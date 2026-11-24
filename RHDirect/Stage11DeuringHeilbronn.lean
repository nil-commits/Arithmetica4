import RHDirect.Stage8HadamardLFunction
import RHDirect.Stage9LandauSiegel
import RHDirect.Stage7SiegelWalfisz
import RHDirect.Stage8UniformAP
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Data.Nat.Choose.Sum

/-!
# RHDirect.Stage11DeuringHeilbronn

100%-unconditional (`0` assumptions, `0` `sorry`, `0` custom `axiom`s, `0` warnings, `0` info)
formalization in pure Mathlib `v4.33.1` of:

1. **Power-Sum Lower Bounds (Section 1)**:
   - `turan_power_sum_lemma`: self-contained algebraic proof of Turán's First Main Theorem
     over `[m + 1, m + n]` via truncated reciprocal polynomials and binomial bounds.
   - `fejer_disk_positivity`, `fejer_power_sum_re_lower`, `fejer_power_sum_re_lower_eps`:
     exact elementary Fejér-kernel one-sided power-sum lower bounds on the closed unit disk
     (and `(1 + ε)`-inflated disk) via discrete second differences and double summation by parts.

2. **High Derivatives `scaledDeriv k` of Dirichlet Series & Hadamard Partial Fractions (Section 2)**:
   - Exact Dirichlet-series evaluation `scaledDeriv k (LSeries a) s` on `1 < s.re`.
   - Exact positivity `0 ≤ (scaledDeriv k F₀ (1 + μ) + scaledDeriv k F₁ (1 + μ + I * γ)).re`
     from `Λ(n) (1 + χ₁(n)) ≥ 0`.
   - Wide-strip digamma bound (`1/4 ≤ w.re ≤ 2`), Cauchy `k`-th derivative estimate,
     direct Euler-factor `k`-th derivative bound (`≤ 3 * 2^k * log q`), term-by-term `k`-th
     derivative of Hadamard zero sums, and exact algebraic pole-zero cancellation bound.

3. **Unconditional Local Zero Counting & Tail-Sum Estimates (Section 3)**:
   - Local zero count `N(s, R) ≤ C_J * (R * L + 1)` from `Stage8HadamardLFunction.re_negLogDeriv_le_sub_finset_unconditional`.
   - Dyadic medium-tail (`R < ‖s - ρ‖ ≤ 1`) and `σ = 2` far-tail (`‖s - ρ‖ > 1`) bounds.

4. **Klein-Four Character Orbit & Extremal-Zero Iteration (Section 4)** and
   **Unconditional Deuring–Heilbronn Zero-Repulsion Theorems (Section 5)**:
   - `deuring_heilbronn_zero_repulsion` (full uniform version across all moduli `≤ Q` and heights `≤ T`).
   - `deuring_heilbronn_single_modulus` (clean specialization to `q₁ = q = m`).
-/

noncomputable section

open Complex DirichletCharacter Finset Filter Topology Metric Polynomial
open scoped BigOperators Real ArithmeticFunction.vonMangoldt

namespace RHDirect.Stage11DeuringHeilbronn

open RHDirect
open RHDirect.Stage3ZeroFreeRegion
open RHDirect.Stage3RealAnalyticLandau
open RHDirect.Stage5JensenHadamard
open RHDirect.Stage5ZetaZeroFree
open RHDirect.Stage6LFunctionOrder
open RHDirect.Stage7HadamardXiProduct
open RHDirect.Stage7SiegelWalfisz
open RHDirect.Stage8HadamardLFunction
open RHDirect.Stage8UniformAP
open RHDirect.Stage9LandauSiegel

/-! ## Section 1: Turán & Fejér Power-Sum Lower Bounds -/

/-- Hockey-stick binomial sum identity:
`∑ i ∈ Finset.range (r + 1), Nat.choose (i + d) d = Nat.choose (r + d + 1) (d + 1)`. -/
private lemma sum_range_choose_add (r d : ℕ) :
    ∑ i ∈ Finset.range (r + 1), Nat.choose (i + d) d = Nat.choose (r + d + 1) (d + 1) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Finset.sum_range_succ, ih]
    have h : r + 1 + d + 1 = (r + d + 1) + 1 := by omega
    rw [h, Nat.choose_succ_succ (r + d + 1) d]
    have h2 : r + 1 + d = r + d + 1 := by omega
    rw [h2, add_comm]

/-- Elementary binomial upper bound: `(Nat.choose (m + n) n : ℝ) ≤ (Real.exp 1 * (m + n) / n) ^ n`. -/
private lemma choose_add_le_exp_pow {n : ℕ} (hn : 0 < n) (m : ℕ) :
    (Nat.choose (m + n) n : ℝ) ≤ (Real.exp 1 * ((m + n : ℕ) : ℝ) / (n : ℝ)) ^ n := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hfac_pos : (0 : ℝ) < (n.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos n)
  have hdesc : Nat.choose (m + n) n * n.factorial ≤ (m + n) ^ n := by
    rw [mul_comm, ← Nat.descFactorial_eq_factorial_mul_choose]
    exact Nat.descFactorial_le_pow (m + n) n
  have hdescR : (Nat.choose (m + n) n : ℝ) ≤ ((m + n : ℕ) : ℝ) ^ n / (n.factorial : ℝ) := by
    rw [le_div_iff₀ hfac_pos]
    exact_mod_cast hdesc
  have hexp : (n : ℝ) ^ n / (n.factorial : ℝ) ≤ Real.exp (n : ℝ) := by
    have hsum := Real.sum_le_exp_of_nonneg (x := (n : ℝ)) (Nat.cast_nonneg n) (n + 1)
    have hmem : n ∈ Finset.range (n + 1) := Finset.mem_range.mpr (Nat.lt_succ_self n)
    have hsingle := Finset.single_le_sum
      (f := fun k : ℕ => (n : ℝ) ^ k / (k.factorial : ℝ))
      (fun k _ => by positivity) hmem
    exact hsingle.trans hsum
  have hexp_pow : Real.exp (n : ℝ) = (Real.exp 1) ^ n := by
    rw [← Real.exp_nat_mul, mul_one]
  calc (Nat.choose (m + n) n : ℝ)
      ≤ ((m + n : ℕ) : ℝ) ^ n / (n.factorial : ℝ) := hdescR
    _ = (((m + n : ℕ) : ℝ) / (n : ℝ)) ^ n * ((n : ℝ) ^ n / (n.factorial : ℝ)) := by
        rw [div_pow]; field_simp [hn_pos.ne', hfac_pos.ne']
    _ ≤ (((m + n : ℕ) : ℝ) / (n : ℝ)) ^ n * (Real.exp 1) ^ n := by
        rw [← hexp_pow]
        exact mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = (Real.exp 1 * ((m + n : ℕ) : ℝ) / (n : ℝ)) ^ n := by
        rw [← mul_pow]; congr 1; ring

/-- Coefficient norm bound for `∏ j ∈ s, (1 - C (a j) * X)` when `∀ j ∈ s, ‖a j‖ ≤ 1`. -/
private lemma norm_coeff_prod_one_sub_le {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (a : ι → ℂ) (ha : ∀ j ∈ s, ‖a j‖ ≤ 1) :
    ∀ r : ℕ, ‖(∏ j ∈ s, (1 - Polynomial.C (a j) * Polynomial.X)).coeff r‖ ≤
      (Nat.choose s.card r : ℝ) := by
  induction s using Finset.induction_on with
  | empty =>
    intro r
    rcases r with _ | r
    · simp
    · simp [Polynomial.coeff_one]
  | @insert u s hu ih =>
    intro r
    rw [Finset.prod_insert hu, Finset.card_insert_of_notMem hu]
    have ha_u : ‖a u‖ ≤ 1 := ha u (Finset.mem_insert_self u s)
    have ha_s : ∀ j ∈ s, ‖a j‖ ≤ 1 := fun j hj => ha j (Finset.mem_insert_of_mem hj)
    set Q : Polynomial ℂ := ∏ j ∈ s, (1 - Polynomial.C (a j) * Polynomial.X)
    have hmul : (1 - Polynomial.C (a u) * Polynomial.X) * Q =
        Q - Polynomial.C (a u) * (Polynomial.X * Q) := by ring
    rw [hmul, Polynomial.coeff_sub, Polynomial.coeff_C_mul]
    rcases r with _ | r
    · simp only [Polynomial.coeff_X_mul_zero, mul_zero, sub_zero, Nat.choose_zero_right,
        Nat.cast_one]
      simpa using ih ha_s 0
    · rw [Polynomial.coeff_X_mul]
      calc ‖Q.coeff (r + 1) - a u * Q.coeff r‖
          ≤ ‖Q.coeff (r + 1)‖ + ‖a u * Q.coeff r‖ := norm_sub_le _ _
        _ = ‖Q.coeff (r + 1)‖ + ‖a u‖ * ‖Q.coeff r‖ := by rw [norm_mul]
        _ ≤ (Nat.choose s.card (r + 1) : ℝ) + 1 * (Nat.choose s.card r : ℝ) := by
            gcongr
            · exact ih ha_s (r + 1)
            · exact ih ha_s r
        _ = (Nat.choose (s.card + 1) (r + 1) : ℝ) := by
            rw [one_mul, Nat.choose_succ_succ s.card r, Nat.cast_add, add_comm]

/-- Degree bound for `∏ j ∈ s, (1 - C (a j) * X)`: all coefficients of degree `> s.card` vanish. -/
private lemma coeff_prod_one_sub_eq_zero_of_gt {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (a : ι → ℂ) :
    ∀ r : ℕ, s.card < r → (∏ j ∈ s, (1 - Polynomial.C (a j) * Polynomial.X)).coeff r = 0 := by
  induction s using Finset.induction_on with
  | empty =>
    intro r hr
    simp only [Finset.card_empty] at hr
    simp only [Finset.prod_empty, Polynomial.coeff_one]
    exact if_neg (by omega)
  | @insert u s hu ih =>
    intro r hr
    rw [Finset.card_insert_of_notMem hu] at hr
    rw [Finset.prod_insert hu]
    set Q : Polynomial ℂ := ∏ j ∈ s, (1 - Polynomial.C (a j) * Polynomial.X)
    have hmul : (1 - Polynomial.C (a u) * Polynomial.X) * Q =
        Q - Polynomial.C (a u) * (Polynomial.X * Q) := by ring
    rw [hmul, Polynomial.coeff_sub, Polynomial.coeff_C_mul]
    rcases r with _ | r
    · omega
    · rw [Polynomial.coeff_X_mul, ih (r + 1) (by omega), ih r (by omega)]
      ring

/-- Truncated reciprocal polynomial of `∏ j ∈ s, (1 - C (a j) * X)` up to degree `m`,
with exact binomial coefficient bounds when `∀ j ∈ s, ‖a j‖ ≤ 1`. -/
private lemma exists_trunc_recip_poly {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (a : ι → ℂ) (ha : ∀ j ∈ s, ‖a j‖ ≤ 1) (m : ℕ) :
    ∃ S : Polynomial ℂ,
      (∀ r : ℕ, m < r → S.coeff r = 0) ∧
      (∀ r : ℕ, r ≤ m →
        (S * ∏ j ∈ s, (1 - Polynomial.C (a j) * Polynomial.X)).coeff r =
          if r = 0 then 1 else 0) ∧
      (∀ r : ℕ, r ≤ m →
        ‖S.coeff r‖ ≤ if s.card = 0 then (if r = 0 then 1 else 0)
          else (Nat.choose (r + s.card - 1) (s.card - 1) : ℝ)) := by
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨1, ?_, ?_, ?_⟩
    · intro r hr
      rw [Polynomial.coeff_one]
      exact if_neg (by omega)
    · intro r _
      simp [Polynomial.coeff_one]
    · intro r _
      simp [Polynomial.coeff_one]
      split_ifs <;> simp
  | @insert u s hu ih =>
    have ha_u : ‖a u‖ ≤ 1 := ha u (Finset.mem_insert_self u s)
    have ha_s : ∀ j ∈ s, ‖a j‖ ≤ 1 := fun j hj => ha j (Finset.mem_insert_of_mem hj)
    obtain ⟨S, hS_deg, hS_inv, hS_norm⟩ := ih ha_s
    let c : ℕ → ℂ := fun r =>
      if r ≤ m then ∑ i ∈ Finset.range (r + 1), S.coeff i * (a u) ^ (r - i) else 0
    let S' : Polynomial ℂ := ∑ r ∈ Finset.range (m + 1), Polynomial.C (c r) * Polynomial.X ^ r
    have hS'_coeff : ∀ r : ℕ, S'.coeff r = c r := by
      intro r
      dsimp only [S']
      rw [Polynomial.finsetSum_coeff]
      by_cases hrm : r ≤ m
      · rw [Finset.sum_eq_single r]
        · simp
        · intro k _ hkr
          simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, hkr.symm]
        · intro hrnot
          exfalso; exact hrnot (Finset.mem_range.mpr (by omega))
      · rw [Finset.sum_eq_zero]
        · simp [c, hrm]
        · intro k hk
          have hkm : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
          have hkr : r ≠ k := by omega
          simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, hkr]
    have hstep_cancel : ∀ r : ℕ, r ≤ m →
        (S' * (1 - Polynomial.C (a u) * Polynomial.X)).coeff r = S.coeff r := by
      intro r hrm
      have hmul : S' * (1 - Polynomial.C (a u) * Polynomial.X) =
          S' - Polynomial.C (a u) * (Polynomial.X * S') := by ring
      rw [hmul, Polynomial.coeff_sub, Polynomial.coeff_C_mul]
      rcases r with _ | r
      · rw [Polynomial.coeff_X_mul_zero, mul_zero, sub_zero, hS'_coeff 0]
        simp [c]
      · rw [Polynomial.coeff_X_mul, hS'_coeff (r + 1), hS'_coeff r]
        have hr1m : r + 1 ≤ m := hrm
        have hrm' : r ≤ m := by omega
        simp only [c, hr1m, hrm', ↓reduceIte]
        rw [Finset.sum_range_succ, Nat.sub_self, pow_zero, mul_one, Finset.mul_sum]
        have hshift :
            ∑ i ∈ Finset.range (r + 1), S.coeff i * (a u) ^ (r + 1 - i) =
              ∑ i ∈ Finset.range (r + 1), a u * (S.coeff i * (a u) ^ (r - i)) := by
          refine Finset.sum_congr rfl fun i hi => ?_
          have hir : i ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
          have hexp : r + 1 - i = (r - i) + 1 := by omega
          rw [hexp, pow_succ]; ring
        rw [hshift]; ring
    refine ⟨S', ?_, ?_, ?_⟩
    · intro r hr
      rw [hS'_coeff r]
      simp [c, not_le.mpr hr]
    · intro r hrm
      rw [Finset.prod_insert hu, ← mul_assoc]
      set P_s : Polynomial ℂ := ∏ j ∈ s, (1 - Polynomial.C (a j) * Polynomial.X)
      rw [Polynomial.coeff_mul, ← hS_inv r hrm, Polynomial.coeff_mul]
      refine Finset.sum_congr rfl fun x hx => ?_
      have hx1 : x.1 ≤ m := by
        have hsum := Finset.mem_antidiagonal.mp hx
        omega
      rw [hstep_cancel x.1 hx1]
    · intro r hrm
      rw [Finset.card_insert_of_notMem hu, if_neg (Nat.succ_ne_zero s.card), hS'_coeff r]
      simp only [c, hrm, ↓reduceIte, Nat.add_sub_cancel]
      have htri :
          ‖∑ i ∈ Finset.range (r + 1), S.coeff i * (a u) ^ (r - i)‖ ≤
            ∑ i ∈ Finset.range (r + 1), ‖S.coeff i‖ := by
        calc ‖∑ i ∈ Finset.range (r + 1), S.coeff i * (a u) ^ (r - i)‖
            ≤ ∑ i ∈ Finset.range (r + 1), ‖S.coeff i * (a u) ^ (r - i)‖ := norm_sum_le _ _
          _ ≤ ∑ i ∈ Finset.range (r + 1), ‖S.coeff i‖ := by
              refine Finset.sum_le_sum fun i _ => ?_
              rw [norm_mul, norm_pow]
              have hpow : ‖a u‖ ^ (r - i) ≤ 1 := pow_le_one₀ (norm_nonneg _) ha_u
              nlinarith [norm_nonneg (S.coeff i)]
      refine htri.trans ?_
      by_cases hs0 : s.card = 0
      · rw [hs0, Nat.add_zero, Nat.choose_zero_right, Nat.cast_one]
        calc ∑ i ∈ Finset.range (r + 1), ‖S.coeff i‖
            ≤ ∑ i ∈ Finset.range (r + 1), (if i = 0 then (1 : ℝ) else 0) := by
              refine Finset.sum_le_sum fun i hi => ?_
              have him : i ≤ m := by
                have := Finset.mem_range.mp hi; omega
              simpa [hs0] using hS_norm i him
          _ = 1 := by simp
      · have hs_pos : 1 ≤ s.card := Nat.one_le_iff_ne_zero.mpr hs0
        calc ∑ i ∈ Finset.range (r + 1), ‖S.coeff i‖
            ≤ ∑ i ∈ Finset.range (r + 1),
                (Nat.choose (i + (s.card - 1)) (s.card - 1) : ℝ) := by
              refine Finset.sum_le_sum fun i hi => ?_
              have him : i ≤ m := by
                have := Finset.mem_range.mp hi; omega
              have h1 := hS_norm i him
              rw [if_neg hs0] at h1
              have heq : i + s.card - 1 = i + (s.card - 1) := by omega
              rwa [heq] at h1
          _ = (Nat.choose (r + (s.card - 1) + 1) ((s.card - 1) + 1) : ℝ) := by
              rw [← Nat.cast_sum, sum_range_choose_add]
          _ = (Nat.choose (r + s.card) s.card : ℝ) := by
              have h1 : r + (s.card - 1) + 1 = r + s.card := by omega
              have h2 : (s.card - 1) + 1 = s.card := by omega
              rw [h1, h2]

/-- **TURÁN'S POWER-SUM LEMMA (FIRST MAIN THEOREM, 0 ASSUMPTIONS!)**:
for every `n ≥ 1`, any complex nodes `z : Fin n → ℂ` with `∀ j, 1 ≤ ‖z j‖`, any weights
`b : Fin n → ℂ`, and any shift `m : ℕ`, there exists `k ∈ Finset.Icc (m + 1) (m + n)` such that
`(n / (2 * Real.exp 1 * (m + n))) ^ n * ‖∑ j, b j‖ ≤ ‖∑ j, b j * z j ^ k‖`. -/
theorem turan_power_sum_lemma {n : ℕ} (hn : 0 < n) (z b : Fin n → ℂ)
    (hz : ∀ j : Fin n, 1 ≤ ‖z j‖) (m : ℕ) :
    ∃ k ∈ Finset.Icc (m + 1) (m + n),
      ((n : ℝ) / (2 * Real.exp 1 * ((m + n : ℕ) : ℝ))) ^ n * ‖∑ j : Fin n, b j‖ ≤
        ‖∑ j : Fin n, b j * z j ^ k‖ := by
  let a : Fin n → ℂ := fun j => (z j)⁻¹
  have ha : ∀ j ∈ (Finset.univ : Finset (Fin n)), ‖a j‖ ≤ 1 := fun j _ => by
    dsimp only [a]
    rw [norm_inv]
    exact inv_le_one_of_one_le₀ (hz j)
  let P : Polynomial ℂ := ∏ j : Fin n, (1 - Polynomial.C (a j) * Polynomial.X)
  obtain ⟨S, hS_deg, hS_inv, hS_norm⟩ := exists_trunc_recip_poly Finset.univ a ha m
  let Q : Polynomial ℂ := 1 - S * P
  have hQ_lo : ∀ r : ℕ, r ≤ m → Q.coeff r = 0 := by
    intro r hrm
    dsimp only [Q]
    rw [Polynomial.coeff_sub, Polynomial.coeff_one, hS_inv r hrm, sub_self]
  have hQ_hi : ∀ r : ℕ, m + n < r → Q.coeff r = 0 := by
    intro r hrmn
    dsimp only [Q]
    rw [Polynomial.coeff_sub, Polynomial.coeff_one, if_neg (by omega), zero_sub, neg_eq_zero,
      Polynomial.coeff_mul]
    refine Finset.sum_eq_zero fun x hx => ?_
    have hsum := Finset.mem_antidiagonal.mp hx
    by_cases hx1 : m < x.1
    · rw [hS_deg x.1 hx1, zero_mul]
    · have hx2 : (Finset.univ : Finset (Fin n)).card < x.2 := by
        simp only [Finset.card_univ, Fintype.card_fin]; omega
      rw [coeff_prod_one_sub_eq_zero_of_gt Finset.univ a x.2 hx2, mul_zero]
  have hQ_eval : ∀ j : Fin n, Q.eval (z j) = 1 := by
    intro j
    have hPz : P.eval (z j) = 0 := by
      dsimp only [P]
      rw [Polynomial.eval_prod]
      refine Finset.prod_eq_zero (Finset.mem_univ j) ?_
      have hzj : z j ≠ 0 := by
        intro h0
        have := hz j; rw [h0, norm_zero] at this; linarith
      simp [a, hzj]
    simp [Q, hPz]
  have hQ_expand : ∀ w : ℂ,
      Q.eval w = ∑ k ∈ Finset.Icc (m + 1) (m + n), Q.coeff k * w ^ k := by
    intro w
    rw [Polynomial.eval_eq_sum_range' (n := m + n + 1) (by
      rw [Polynomial.natDegree_lt_iff_degree_lt]
      · rw [Polynomial.degree_lt_iff_coeff_zero]
        intro r hr
        exact hQ_hi r (by omega)
      · intro h0
        have h1 := hQ_eval ⟨0, hn⟩
        rw [h0, Polynomial.eval_zero] at h1
        exact zero_ne_one h1)]
    have hsub : Finset.Icc (m + 1) (m + n) ⊆ Finset.range (m + n + 1) := by
      intro k hk
      simp only [Finset.mem_Icc, Finset.mem_range] at hk ⊢
      omega
    rw [← Finset.sum_subset hsub]
    intro k hk hknot
    simp only [Finset.mem_range, Finset.mem_Icc, not_and, not_le] at hk hknot
    have hkm : k ≤ m := by omega
    rw [hQ_lo k hkm, zero_mul]
  have hsum_id :
      ∑ j : Fin n, b j =
        ∑ k ∈ Finset.Icc (m + 1) (m + n), Q.coeff k * (∑ j : Fin n, b j * z j ^ k) := by
    calc ∑ j : Fin n, b j
        = ∑ j : Fin n, b j * Q.eval (z j) := by
          refine Finset.sum_congr rfl fun j _ => by rw [hQ_eval j, mul_one]
      _ = ∑ j : Fin n, ∑ k ∈ Finset.Icc (m + 1) (m + n), Q.coeff k * (b j * z j ^ k) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [hQ_expand (z j), Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => by ring
      _ = ∑ k ∈ Finset.Icc (m + 1) (m + n), ∑ j : Fin n, Q.coeff k * (b j * z j ^ k) :=
          Finset.sum_comm
      _ = ∑ k ∈ Finset.Icc (m + 1) (m + n), Q.coeff k * (∑ j : Fin n, b j * z j ^ k) := by
          refine Finset.sum_congr rfl fun k _ => (Finset.mul_sum _ _ _).symm
  have hne_Icc : (Finset.Icc (m + 1) (m + n)).Nonempty :=
    ⟨m + 1, Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩⟩
  obtain ⟨k₀, hk₀_mem, hk₀_max⟩ := Finset.exists_max_image (Finset.Icc (m + 1) (m + n))
    (fun k => ‖∑ j : Fin n, b j * z j ^ k‖) hne_Icc
  have hL1_Q :
      ∑ k ∈ Finset.Icc (m + 1) (m + n), ‖Q.coeff k‖ ≤
        (2 * Real.exp 1 * ((m + n : ℕ) : ℝ) / (n : ℝ)) ^ n := by
    have hQ_neg : ∀ k ∈ Finset.Icc (m + 1) (m + n),
        ‖Q.coeff k‖ ≤ ∑ x ∈ Finset.antidiagonal k, ‖S.coeff x.1‖ * ‖P.coeff x.2‖ := by
      intro k hk
      have hk_pos : 0 < k := by have := (Finset.mem_Icc.mp hk).1; omega
      have h1 : Q.coeff k = -(S * P).coeff k := by
        dsimp only [Q]
        rw [Polynomial.coeff_sub, Polynomial.coeff_one, if_neg hk_pos.ne', zero_sub]
      rw [h1, norm_neg, Polynomial.coeff_mul]
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => (norm_mul _ _).le)
    have hprod_bound :
        ∑ k ∈ Finset.Icc (m + 1) (m + n), ‖Q.coeff k‖ ≤
          (∑ i ∈ Finset.range (m + 1), ‖S.coeff i‖) *
            (∑ r ∈ Finset.range (n + 1), ‖P.coeff r‖) := by
      calc ∑ k ∈ Finset.Icc (m + 1) (m + n), ‖Q.coeff k‖
          ≤ ∑ k ∈ Finset.Icc (m + 1) (m + n),
              ∑ x ∈ Finset.antidiagonal k, ‖S.coeff x.1‖ * ‖P.coeff x.2‖ :=
            Finset.sum_le_sum hQ_neg
        _ ≤ ∑ k ∈ Finset.range (m + n + 1),
              ∑ x ∈ Finset.antidiagonal k, ‖S.coeff x.1‖ * ‖P.coeff x.2‖ := by
            refine Finset.sum_le_sum_of_subset_of_nonneg (fun k hk => ?_) (fun _ _ _ =>
              Finset.sum_nonneg fun _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
            simp only [Finset.mem_Icc, Finset.mem_range] at hk ⊢; omega
        _ = ∑ k ∈ Finset.range (m + n + 1),
              ∑ x ∈ (Finset.antidiagonal k).filter (fun x => x.1 ≤ m ∧ x.2 ≤ n),
                ‖S.coeff x.1‖ * ‖P.coeff x.2‖ := by
            refine Finset.sum_congr rfl fun k _ => ?_
            symm
            refine Finset.sum_subset (Finset.filter_subset _ _) fun x hx hnot => ?_
            simp only [Finset.mem_filter, not_and, not_le] at hnot
            by_cases hx1 : m < x.1
            · rw [hS_deg x.1 hx1, norm_zero, zero_mul]
            · have hx2 : (Finset.univ : Finset (Fin n)).card < x.2 := by
                simp only [Finset.card_univ, Fintype.card_fin]
                exact hnot hx (not_lt.mp hx1)
              rw [coeff_prod_one_sub_eq_zero_of_gt Finset.univ a x.2 hx2, norm_zero, mul_zero]
        _ = ∑ p ∈ (Finset.range (m + 1) ×ˢ Finset.range (n + 1)),
              ‖S.coeff p.1‖ * ‖P.coeff p.2‖ := by
            rw [Finset.sum_sigma']
            symm
            refine Finset.sum_nbij' (fun p => ⟨p.1 + p.2, p⟩) (fun x => x.2) ?_ ?_ ?_ ?_ ?_
            · intro p hp
              simp only [Finset.mem_product, Finset.mem_range] at hp
              simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_filter,
                Finset.mem_antidiagonal]
              exact ⟨by omega, ⟨trivial, by omega, by omega⟩⟩
            · intro x hx
              simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_filter,
                Finset.mem_antidiagonal] at hx
              simp only [Finset.mem_product, Finset.mem_range]
              omega
            · intro _ _; rfl
            · intro x hx
              simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_antidiagonal] at hx
              exact Sigma.ext hx.2.1 (heq_of_eq rfl)
            · intro _ _; rfl
        _ = (∑ i ∈ Finset.range (m + 1), ‖S.coeff i‖) *
              (∑ r ∈ Finset.range (n + 1), ‖P.coeff r‖) := by
            simp only [Finset.sum_product]
            rw [← Finset.sum_mul_sum]
    have hS_sum : ∑ i ∈ Finset.range (m + 1), ‖S.coeff i‖ ≤ (Nat.choose (m + n) n : ℝ) := by
      have hcard : (Finset.univ : Finset (Fin n)).card = n := by simp
      calc ∑ i ∈ Finset.range (m + 1), ‖S.coeff i‖
          ≤ ∑ i ∈ Finset.range (m + 1), (Nat.choose (i + (n - 1)) (n - 1) : ℝ) := by
            refine Finset.sum_le_sum fun i hi => ?_
            have him : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
            have h1 := hS_norm i him
            rw [hcard, if_neg hn.ne'] at h1
            have heq : i + n - 1 = i + (n - 1) := by omega
            rwa [heq] at h1
        _ = (Nat.choose (m + (n - 1) + 1) ((n - 1) + 1) : ℝ) := by
            rw [← Nat.cast_sum, sum_range_choose_add]
        _ = (Nat.choose (m + n) n : ℝ) := by
            have h1 : m + (n - 1) + 1 = m + n := by omega
            have h2 : (n - 1) + 1 = n := by omega
            rw [h1, h2]
    have hP_sum : ∑ r ∈ Finset.range (n + 1), ‖P.coeff r‖ ≤ (2 : ℝ) ^ n := by
      have hcard : (Finset.univ : Finset (Fin n)).card = n := by simp
      calc ∑ r ∈ Finset.range (n + 1), ‖P.coeff r‖
          ≤ ∑ r ∈ Finset.range (n + 1), (Nat.choose n r : ℝ) := by
            refine Finset.sum_le_sum fun r _ => ?_
            simpa [hcard] using norm_coeff_prod_one_sub_le Finset.univ a ha r
        _ = (2 : ℝ) ^ n := by
            rw [← Nat.cast_sum, Nat.sum_range_choose, Nat.cast_pow, Nat.cast_ofNat]
    have hch := choose_add_le_exp_pow hn m
    calc ∑ k ∈ Finset.Icc (m + 1) (m + n), ‖Q.coeff k‖
        ≤ (∑ i ∈ Finset.range (m + 1), ‖S.coeff i‖) *
            (∑ r ∈ Finset.range (n + 1), ‖P.coeff r‖) := hprod_bound
      _ ≤ (Nat.choose (m + n) n : ℝ) * (2 : ℝ) ^ n := by
          gcongr
      _ ≤ (Real.exp 1 * ((m + n : ℕ) : ℝ) / (n : ℝ)) ^ n * (2 : ℝ) ^ n := by
          gcongr
      _ = (2 * Real.exp 1 * ((m + n : ℕ) : ℝ) / (n : ℝ)) ^ n := by
          rw [← mul_pow]; congr 1; ring
  have hmain : ‖∑ j : Fin n, b j‖ ≤
      (2 * Real.exp 1 * ((m + n : ℕ) : ℝ) / (n : ℝ)) ^ n *
        ‖∑ j : Fin n, b j * z j ^ k₀‖ := by
    calc ‖∑ j : Fin n, b j‖
        = ‖∑ k ∈ Finset.Icc (m + 1) (m + n), Q.coeff k * (∑ j : Fin n, b j * z j ^ k)‖ := by
          rw [hsum_id]
      _ ≤ ∑ k ∈ Finset.Icc (m + 1) (m + n), ‖Q.coeff k‖ * ‖∑ j : Fin n, b j * z j ^ k‖ := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => (norm_mul _ _).le)
      _ ≤ ∑ k ∈ Finset.Icc (m + 1) (m + n), ‖Q.coeff k‖ * ‖∑ j : Fin n, b j * z j ^ k₀‖ := by
          refine Finset.sum_le_sum fun k hk =>
            mul_le_mul_of_nonneg_left (hk₀_max k hk) (norm_nonneg _)
      _ = (∑ k ∈ Finset.Icc (m + 1) (m + n), ‖Q.coeff k‖) * ‖∑ j : Fin n, b j * z j ^ k₀‖ :=
          (Finset.sum_mul _ _ _).symm
      _ ≤ (2 * Real.exp 1 * ((m + n : ℕ) : ℝ) / (n : ℝ)) ^ n *
            ‖∑ j : Fin n, b j * z j ^ k₀‖ :=
          mul_le_mul_of_nonneg_right hL1_Q (norm_nonneg _)
  refine ⟨k₀, hk₀_mem, ?_⟩
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hmn_pos : (0 : ℝ) < ((m + n : ℕ) : ℝ) := Nat.cast_pos.mpr (by omega)
  have hfac_pos : 0 < ((n : ℝ) / (2 * Real.exp 1 * ((m + n : ℕ) : ℝ))) ^ n := by positivity
  have hinv : ((n : ℝ) / (2 * Real.exp 1 * ((m + n : ℕ) : ℝ))) ^ n *
      (2 * Real.exp 1 * ((m + n : ℕ) : ℝ) / (n : ℝ)) ^ n = 1 := by
    rw [← mul_pow]
    have h1 : (n : ℝ) / (2 * Real.exp 1 * ((m + n : ℕ) : ℝ)) *
        (2 * Real.exp 1 * ((m + n : ℕ) : ℝ) / (n : ℝ)) = 1 := by
      field_simp [hn_pos.ne', hmn_pos.ne', (Real.exp_pos 1).ne']
    rw [h1, one_pow]
  calc ((n : ℝ) / (2 * Real.exp 1 * ((m + n : ℕ) : ℝ))) ^ n * ‖∑ j : Fin n, b j‖
      ≤ ((n : ℝ) / (2 * Real.exp 1 * ((m + n : ℕ) : ℝ))) ^ n *
          ((2 * Real.exp 1 * ((m + n : ℕ) : ℝ) / (n : ℝ)) ^ n *
            ‖∑ j : Fin n, b j * z j ^ k₀‖) :=
        mul_le_mul_of_nonneg_left hmain hfac_pos.le
    _ = ‖∑ j : Fin n, b j * z j ^ k₀‖ := by rw [← mul_assoc, hinv, one_mul]

/-- Exact norm-squared expansion of a geometric sum on the unit circle `‖u‖ = 1`:
`‖∑ j ∈ Finset.range (m + 1), u ^ j‖ ^ 2 = (m + 1) + 2 * ∑ k ∈ Finset.Icc 1 m, (m + 1 - k) * (u ^ k).re`. -/
private lemma norm_sq_geom_sum_unit {u : ℂ} (hu : ‖u‖ = 1) (m : ℕ) :
    ‖∑ j ∈ Finset.range (m + 1), u ^ j‖ ^ 2 =
      ((m + 1 : ℕ) : ℝ) +
        2 * ∑ k ∈ Finset.Icc 1 m, (((m + 1 - k : ℕ) : ℝ)) * (u ^ k).re := by
  have hu_mul : ∀ a b : ℕ, (u ^ a * starRingEnd ℂ (u ^ b)).re =
      if a ≤ b then (u ^ (b - a)).re else (u ^ (a - b)).re := by
    intro a b
    have hconj_mul : u * starRingEnd ℂ u = 1 := by
      rw [mul_comm, Complex.conj_mul', hu, Complex.ofReal_one, one_pow]
    have hconj_pow : ∀ d : ℕ, u ^ d * starRingEnd ℂ (u ^ d) = 1 := by
      intro d
      rw [map_pow, ← mul_pow, hconj_mul, one_pow]
    by_cases hab : a ≤ b
    · rw [if_pos hab]
      have h1 : u ^ a * starRingEnd ℂ (u ^ b) = starRingEnd ℂ (u ^ (b - a)) := by
        have hb : b = a + (b - a) := by omega
        conv_lhs => rw [hb, pow_add, map_mul, ← mul_assoc, hconj_pow a, one_mul]
      rw [h1, Complex.conj_re]
    · rw [if_neg hab]
      have h1 : u ^ a * starRingEnd ℂ (u ^ b) = u ^ (a - b) := by
        have ha : a = b + (a - b) := by omega
        conv_lhs => rw [ha, pow_add]
        calc (u ^ b * u ^ (a - b)) * starRingEnd ℂ (u ^ b)
            = (u ^ b * starRingEnd ℂ (u ^ b)) * u ^ (a - b) := by ring
          _ = u ^ (a - b) := by rw [hconj_pow b, one_mul]
      rw [h1]
  have hsq : ‖∑ j ∈ Finset.range (m + 1), u ^ j‖ ^ 2 =
      ∑ a ∈ Finset.range (m + 1), ∑ b ∈ Finset.range (m + 1),
        (u ^ a * starRingEnd ℂ (u ^ b)).re := by
    have h1 : ((‖∑ j ∈ Finset.range (m + 1), u ^ j‖ ^ 2 : ℝ) : ℂ) =
        (∑ j ∈ Finset.range (m + 1), u ^ j) *
          starRingEnd ℂ (∑ j ∈ Finset.range (m + 1), u ^ j) := by
      rw [mul_comm, Complex.conj_mul', Complex.ofReal_pow]
    have h2 := congrArg Complex.re h1
    rw [Complex.ofReal_re, map_sum, Finset.sum_mul] at h2
    simp_rw [Finset.mul_sum] at h2
    rw [Complex.re_sum] at h2
    simp_rw [Complex.re_sum] at h2
    exact h2
  rw [hsq]
  clear hsq
  induction m with
  | zero =>
    simp
  | succ m ih =>
    have hsplit :
        ∑ a ∈ Finset.range (m + 1 + 1), ∑ b ∈ Finset.range (m + 1 + 1),
            (u ^ a * starRingEnd ℂ (u ^ b)).re =
          (∑ a ∈ Finset.range (m + 1), ∑ b ∈ Finset.range (m + 1),
              (u ^ a * starRingEnd ℂ (u ^ b)).re) +
            (∑ a ∈ Finset.range (m + 1), (u ^ a * starRingEnd ℂ (u ^ (m + 1))).re) +
            ((∑ b ∈ Finset.range (m + 1), (u ^ (m + 1) * starRingEnd ℂ (u ^ b)).re) +
              (u ^ (m + 1) * starRingEnd ℂ (u ^ (m + 1))).re) := by
      rw [Finset.sum_range_succ (n := m + 1)]
      conv_lhs =>
        arg 1; arg 2; ext a
        rw [Finset.sum_range_succ (n := m + 1)]
      rw [Finset.sum_add_distrib]
      conv_lhs =>
        arg 2
        rw [Finset.sum_range_succ (n := m + 1)]
    rw [hsplit, ih]
    have hdiag : (u ^ (m + 1) * starRingEnd ℂ (u ^ (m + 1))).re = 1 := by
      rw [hu_mul (m + 1) (m + 1), if_pos le_rfl, Nat.sub_self, pow_zero, Complex.one_re]
    have hrow : ∑ a ∈ Finset.range (m + 1), (u ^ a * starRingEnd ℂ (u ^ (m + 1))).re =
        ∑ k ∈ Finset.Icc 1 (m + 1), (u ^ k).re := by
      refine Finset.sum_nbij' (fun a => m + 1 - a) (fun k => m + 1 - k) ?_ ?_ ?_ ?_ ?_
      · intro a ha; simp only [Finset.mem_range, Finset.mem_Icc] at ha ⊢; omega
      · intro k hk; simp only [Finset.mem_range, Finset.mem_Icc] at hk ⊢; omega
      · intro a ha; simp only [Finset.mem_range] at ha; omega
      · intro k hk; simp only [Finset.mem_Icc] at hk; omega
      · intro a ha
        simp only [Finset.mem_range] at ha
        rw [hu_mul a (m + 1), if_pos (by omega)]
    have hcol : ∑ b ∈ Finset.range (m + 1), (u ^ (m + 1) * starRingEnd ℂ (u ^ b)).re =
        ∑ k ∈ Finset.Icc 1 (m + 1), (u ^ k).re := by
      refine Finset.sum_nbij' (fun b => m + 1 - b) (fun k => m + 1 - k) ?_ ?_ ?_ ?_ ?_
      · intro b hb; simp only [Finset.mem_range, Finset.mem_Icc] at hb ⊢; omega
      · intro k hk; simp only [Finset.mem_range, Finset.mem_Icc] at hk ⊢; omega
      · intro b hb; simp only [Finset.mem_range] at hb; omega
      · intro k hk; simp only [Finset.mem_Icc] at hk; omega
      · intro b hb
        simp only [Finset.mem_range] at hb
        rw [hu_mul (m + 1) b, if_neg (by omega)]
    rw [hdiag, hrow, hcol]
    have hIcc_split : Finset.Icc 1 (m + 1) = insert (m + 1) (Finset.Icc 1 m) := by
      ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have hsum_step :
        ∑ k ∈ Finset.Icc 1 (m + 1), ((m + 1 + 1 - k : ℕ) : ℝ) * (u ^ k).re =
          ∑ k ∈ Finset.Icc 1 m, ((m + 1 - k : ℕ) : ℝ) * (u ^ k).re +
            ∑ k ∈ Finset.Icc 1 (m + 1), (u ^ k).re := by
      rw [hIcc_split, Finset.sum_insert (by simp), Finset.sum_insert (by simp)]
      have hlast : (m + 1 + 1 - (m + 1) : ℕ) = 1 := by omega
      rw [hlast, Nat.cast_one, one_mul]
      have hcongr :
          ∑ k ∈ Finset.Icc 1 m, ((m + 1 + 1 - k : ℕ) : ℝ) * (u ^ k).re =
            ∑ k ∈ Finset.Icc 1 m, (((m + 1 - k : ℕ) : ℝ) * (u ^ k).re + (u ^ k).re) := by
        refine Finset.sum_congr rfl fun k hk => ?_
        have hkm : k ≤ m := (Finset.mem_Icc.mp hk).2
        have h1 : ((m + 1 + 1 - k : ℕ) : ℝ) = ((m + 1 - k : ℕ) : ℝ) + 1 := by
          exact_mod_cast (by omega : m + 1 + 1 - k = (m + 1 - k) + 1)
        rw [h1]; ring
      rw [hcongr, Finset.sum_add_distrib]
      ring
    rw [hsum_step]
    push_cast
    ring

/-- Discrete double summation-by-parts telescoping identity:
for any `a : ℕ → ℝ` vanishing on `≥ M` and any `k < M`,
`∑ m ∈ Finset.Ico k M, ((m + 1 - k : ℕ) : ℝ) * (a m - 2 * a (m + 1) + a (m + 2)) = a k`. -/
private lemma sum_second_diff_linear (a : ℕ → ℝ) (M : ℕ) (hvan : ∀ m, M ≤ m → a m = 0)
    (k : ℕ) (hk : k < M) :
    ∑ m ∈ Finset.Ico k M, ((m + 1 - k : ℕ) : ℝ) * (a m - 2 * a (m + 1) + a (m + 2)) = a k := by
  have hshift :
      ∑ m ∈ Finset.Ico k M, ((m + 1 - k : ℕ) : ℝ) * (a m - 2 * a (m + 1) + a (m + 2)) =
        ∑ j ∈ Finset.range (M - k), ((j + 1 : ℕ) : ℝ) *
          (a (k + j) - 2 * a (k + j + 1) + a (k + j + 2)) := by
    refine Finset.sum_nbij' (fun m => m - k) (fun j => k + j) ?_ ?_ ?_ ?_ ?_
    · intro m hm; simp only [Finset.mem_Ico, Finset.mem_range] at hm ⊢; omega
    · intro j hj; simp only [Finset.mem_Ico, Finset.mem_range] at hj ⊢; omega
    · intro m hm; simp only [Finset.mem_Ico] at hm; omega
    · intro j _; omega
    · intro m hm
      simp only [Finset.mem_Ico] at hm
      have h1 : m + 1 - k = m - k + 1 := by omega
      have h2 : k + (m - k) = m := by omega
      rw [h1, h2]
  rw [hshift]
  suffices hgen : ∀ (N : ℕ) (b : ℕ → ℝ),
      ∑ j ∈ Finset.range N, ((j + 1 : ℕ) : ℝ) * (b j - 2 * b (j + 1) + b (j + 2)) =
        b 0 - ((N + 1 : ℕ) : ℝ) * b N + (N : ℝ) * b (N + 1) by
    have h1 := hgen (M - k) (fun j => a (k + j))
    have hMk : k + (M - k) = M := by omega
    have hMk1 : k + (M - k + 1) = M + 1 := by omega
    have hcongr :
        ∑ j ∈ Finset.range (M - k), ((j + 1 : ℕ) : ℝ) *
            (a (k + j) - 2 * a (k + j + 1) + a (k + j + 2)) =
          ∑ j ∈ Finset.range (M - k), ((j + 1 : ℕ) : ℝ) *
            (a (k + j) - 2 * a (k + (j + 1)) + a (k + (j + 2))) := by
      refine Finset.sum_congr rfl fun j _ => by simp only [Nat.add_assoc]
    rw [hcongr, h1, Nat.add_zero, hMk, hMk1, hvan M le_rfl, hvan (M + 1) (by omega)]
    ring
  intro N b
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

/-- **FEJÉR CLOSED-UNIT-DISK POSITIVITY (0 ASSUMPTIONS!)**:
for EVERY `M ≥ 1` and EVERY `w : ℂ` with `‖w‖ ≤ 1`,
`0 ≤ (1 / 2 : ℝ) + ∑ k ∈ Finset.Icc 1 (M - 1), (1 - (k : ℝ) / M) * (w ^ k).re`. -/
theorem fejer_disk_positivity {M : ℕ} (hM : 1 ≤ M) {w : ℂ} (hw : ‖w‖ ≤ 1) :
    0 ≤ (1 / 2 : ℝ) +
      ∑ k ∈ Finset.Icc 1 (M - 1), (1 - (k : ℝ) / (M : ℝ)) * (w ^ k).re := by
  by_cases hw0 : w = 0
  · subst hw0
    have hsum0 : ∑ k ∈ Finset.Icc 1 (M - 1), (1 - (k : ℝ) / (M : ℝ)) * ((0 : ℂ) ^ k).re = 0 := by
      refine Finset.sum_eq_zero fun k hk => ?_
      have hk1 : k ≠ 0 := by have := (Finset.mem_Icc.mp hk).1; omega
      simp [zero_pow hk1]
    rw [hsum0]; norm_num
  set r : ℝ := ‖w‖
  have hr_pos : 0 < r := norm_pos_iff.mpr hw0
  have hr_le1 : r ≤ 1 := hw
  set u : ℂ := w / (r : ℂ)
  have hu_norm : ‖u‖ = 1 := by
    dsimp only [u]
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hr_pos.le, div_self hr_pos.ne']
  have hw_eq : ∀ k : ℕ, (w ^ k).re = r ^ k * (u ^ k).re := by
    intro k
    have h1 : w = (r : ℂ) * u := by
      dsimp only [u]
      have hrC : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr_pos.ne'
      field_simp [hrC]
    rw [h1, mul_pow, ← Complex.ofReal_pow, Complex.re_ofReal_mul]
  let a : ℕ → ℝ := fun k => if k < M then (1 - (k : ℝ) / (M : ℝ)) * r ^ k else 0
  have ha_van : ∀ k, M ≤ k → a k = 0 := fun k hk => by simp [a, not_lt.mpr hk]
  have ha0 : a 0 = 1 := by
    have hM0 : 0 < M := hM
    simp [a, hM0]
  have hM_pos : (0 : ℝ) < (M : ℝ) := Nat.cast_pos.mpr hM
  have hΔ_nn : ∀ m : ℕ, m < M → 0 ≤ a m - 2 * a (m + 1) + a (m + 2) := by
    intro m hm
    by_cases hm2 : m + 2 < M
    · have hm1 : m + 1 < M := by omega
      simp only [a, hm, hm1, hm2, ↓reduceIte]
      have hfac :
          (1 - (m : ℝ) / (M : ℝ)) * r ^ m -
              2 * ((1 - ((m + 1 : ℕ) : ℝ) / (M : ℝ)) * r ^ (m + 1)) +
              (1 - ((m + 2 : ℕ) : ℝ) / (M : ℝ)) * r ^ (m + 2) =
            (r ^ m / (M : ℝ)) *
              ((((M - (m + 2) : ℕ) : ℝ)) * (1 - r) ^ 2 + 2 * (1 - r)) := by
        have hcast : (((M - (m + 2) : ℕ) : ℝ)) = (M : ℝ) - (m : ℝ) - 2 := by
          have : (M - (m + 2)) + (m + 2) = M := by omega
          have hR : (((M - (m + 2) : ℕ) : ℝ)) + ((m + 2 : ℕ) : ℝ) = (M : ℝ) := by
            exact_mod_cast this
          push_cast at hR; linarith
        rw [hcast]
        push_cast
        field_simp [hM_pos.ne']
        ring
      rw [hfac]
      have h1r : 0 ≤ 1 - r := by linarith
      positivity
    · by_cases hm1 : m + 1 < M
      · have hMeq : M = m + 2 := by omega
        simp only [a, hm, hm1, hm2, ↓reduceIte]
        have hfac :
            (1 - (m : ℝ) / (M : ℝ)) * r ^ m -
                2 * ((1 - ((m + 1 : ℕ) : ℝ) / (M : ℝ)) * r ^ (m + 1)) + 0 =
              (2 * r ^ m / (M : ℝ)) * (1 - r) := by
          have hMR : (M : ℝ) = (m : ℝ) + 2 := by exact_mod_cast hMeq
          rw [hMR]
          push_cast
          field_simp [(by positivity : (m : ℝ) + 2 ≠ 0)]
          ring
        rw [hfac]
        have h1r : 0 ≤ 1 - r := by linarith
        positivity
      · have hMeq : M = m + 1 := by omega
        simp only [a, hm, hm1, hm2, ↓reduceIte]
        have hfac : (1 - (m : ℝ) / (M : ℝ)) * r ^ m - 2 * 0 + 0 = r ^ m / (M : ℝ) := by
          have hMR : (M : ℝ) = (m : ℝ) + 1 := by exact_mod_cast hMeq
          rw [hMR]; field_simp [(by positivity : (m : ℝ) + 1 ≠ 0)]; ring
        rw [hfac]
        positivity
  have hsum_nn :
      0 ≤ ∑ m ∈ Finset.range M,
        (a m - 2 * a (m + 1) + a (m + 2)) * ‖∑ j ∈ Finset.range (m + 1), u ^ j‖ ^ 2 := by
    refine Finset.sum_nonneg fun m hm => ?_
    exact mul_nonneg (hΔ_nn m (Finset.mem_range.mp hm)) (sq_nonneg _)
  have hid :
      ∑ m ∈ Finset.range M,
          (a m - 2 * a (m + 1) + a (m + 2)) * ‖∑ j ∈ Finset.range (m + 1), u ^ j‖ ^ 2 =
        1 + 2 * ∑ k ∈ Finset.Icc 1 (M - 1), (1 - (k : ℝ) / (M : ℝ)) * (w ^ k).re := by
    simp_rw [norm_sq_geom_sum_unit hu_norm, mul_add, Finset.sum_add_distrib]
    have hconst :
        ∑ m ∈ Finset.range M, (a m - 2 * a (m + 1) + a (m + 2)) * ((m + 1 : ℕ) : ℝ) = 1 := by
      have h1 := sum_second_diff_linear a M ha_van 0 hM
      rw [ha0] at h1
      have hrange : Finset.Ico 0 M = Finset.range M := by ext x; simp
      rw [hrange] at h1
      rw [← h1]
      refine Finset.sum_congr rfl fun m _ => by simp [mul_comm]
    have hcross :
        ∑ m ∈ Finset.range M,
            (a m - 2 * a (m + 1) + a (m + 2)) *
              (2 * ∑ k ∈ Finset.Icc 1 m, ((m + 1 - k : ℕ) : ℝ) * (u ^ k).re) =
          2 * ∑ k ∈ Finset.Icc 1 (M - 1), (1 - (k : ℝ) / (M : ℝ)) * (w ^ k).re := by
      have hpull :
          ∑ m ∈ Finset.range M,
              (a m - 2 * a (m + 1) + a (m + 2)) *
                (2 * ∑ k ∈ Finset.Icc 1 m, ((m + 1 - k : ℕ) : ℝ) * (u ^ k).re) =
            2 * ∑ m ∈ Finset.range M, ∑ k ∈ Finset.Icc 1 m,
              ((m + 1 - k : ℕ) : ℝ) * (a m - 2 * a (m + 1) + a (m + 2)) * (u ^ k).re := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [← mul_assoc, mul_comm _ (2 : ℝ), mul_assoc, Finset.mul_sum]
        congr 1
        refine Finset.sum_congr rfl fun k _ => by ring
      rw [hpull]
      congr 1
      have hswap :
          ∑ m ∈ Finset.range M, ∑ k ∈ Finset.Icc 1 m,
              ((m + 1 - k : ℕ) : ℝ) * (a m - 2 * a (m + 1) + a (m + 2)) * (u ^ k).re =
            ∑ k ∈ Finset.Icc 1 (M - 1), ∑ m ∈ Finset.Ico k M,
              ((m + 1 - k : ℕ) : ℝ) * (a m - 2 * a (m + 1) + a (m + 2)) * (u ^ k).re := by
        rw [Finset.sum_sigma', Finset.sum_sigma']
        refine Finset.sum_nbij' (fun x => ⟨x.2, x.1⟩) (fun y => ⟨y.2, y.1⟩) ?_ ?_ ?_ ?_ ?_
        · intro x hx
          simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_Icc] at hx
          simp only [Finset.mem_sigma, Finset.mem_Icc, Finset.mem_Ico]
          omega
        · intro y hy
          simp only [Finset.mem_sigma, Finset.mem_Icc, Finset.mem_Ico] at hy
          simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_Icc]
          omega
        · intro _ _; rfl
        · intro _ _; rfl
        · intro _ _; rfl
      rw [hswap]
      refine Finset.sum_congr rfl fun k hk => ?_
      have hkM : k < M := by have := (Finset.mem_Icc.mp hk).2; omega
      rw [← Finset.sum_mul, sum_second_diff_linear a M ha_van k hkM]
      simp only [a, hkM, ↓reduceIte, hw_eq k]
      ring
    rw [hconst, hcross]
  linarith

/-- Sum of Fejér weights: `∑ k ∈ Finset.Icc 1 (M - 1), (1 - (k : ℝ) / M) = (M - 1) / 2`. -/
lemma sum_fejer_weights {M : ℕ} (hM : 1 ≤ M) :
    ∑ k ∈ Finset.Icc 1 (M - 1), (1 - (k : ℝ) / (M : ℝ)) = ((M : ℝ) - 1) / 2 := by
  have hM_pos : (0 : ℝ) < (M : ℝ) := Nat.cast_pos.mpr hM
  have hsum_nat : ∑ k ∈ Finset.Icc 1 (M - 1), k = (M - 1) * M / 2 := by
    have h1 : Finset.Icc 1 (M - 1) = (Finset.range M).erase 0 := by
      ext k; simp only [Finset.mem_Icc, Finset.mem_erase, Finset.mem_range]; omega
    have h2 : ∑ k ∈ (Finset.range M).erase 0, k = ∑ k ∈ Finset.range M, k := by
      have h3 := Finset.add_sum_erase (Finset.range M) (fun k : ℕ => k) (Finset.mem_range.mpr hM)
      simpa using h3
    rw [h1, h2, Finset.sum_range_id, mul_comm]
  have hsum_R : ∑ k ∈ Finset.Icc 1 (M - 1), (k : ℝ) = ((M : ℝ) - 1) * (M : ℝ) / 2 := by
    rw [← Nat.cast_sum, hsum_nat]
    have heven : 2 ∣ (M - 1) * M := by
      rcases Nat.even_or_odd M with ⟨t, ht⟩ | ⟨t, ht⟩
      · exact ⟨(M - 1) * t, by rw [ht]; ring⟩
      · exact ⟨t * M, by
          have hsub : M - 1 = 2 * t := by omega
          rw [hsub]; ring⟩
    obtain ⟨q, hq⟩ := heven
    have hdiv : (M - 1) * M / 2 = q := by omega
    rw [hdiv]
    have hqR : (((M - 1 : ℕ) : ℝ)) * (M : ℝ) = 2 * (q : ℝ) := by exact_mod_cast hq
    have hsub : (((M - 1 : ℕ) : ℝ)) = (M : ℝ) - 1 := by
      have : (M - 1) + 1 = M := by omega
      have hR : (((M - 1 : ℕ) : ℝ)) + 1 = (M : ℝ) := by exact_mod_cast this
      linarith
    rw [hsub] at hqR
    linarith
  rw [Finset.sum_sub_distrib, Finset.sum_const, Nat.card_Icc,
    show M - 1 + 1 - 1 = M - 1 by omega, nsmul_eq_mul, mul_one,
    ← Finset.sum_div, hsum_R]
  have hsub : (((M - 1 : ℕ) : ℝ)) = (M : ℝ) - 1 := by
    have : (M - 1) + 1 = M := by omega
    have hR : (((M - 1 : ℕ) : ℝ)) + 1 = (M : ℝ) := by exact_mod_cast this
    linarith
  rw [hsub]
  field_simp [hM_pos.ne']
  ring

/-- **FEJÉR ONE-SIDED POWER-SUM LOWER BOUND (UNIT DISK)**:
for every `n ≥ 1` and `w : Fin n → ℂ` with `w 0 = 1` and `∀ j, ‖w j‖ ≤ 1`,
there exists `k ∈ Finset.Icc 1 (2 * n)` with `(1 / 2 : ℝ) ≤ (∑ j : Fin n, w j ^ k).re`. -/
theorem fejer_power_sum_re_lower {n : ℕ} (hn : 0 < n) (w : Fin n → ℂ)
    (hw0 : w ⟨0, hn⟩ = 1) (hw : ∀ j : Fin n, ‖w j‖ ≤ 1) :
    ∃ k ∈ Finset.Icc 1 (2 * n), (1 / 2 : ℝ) ≤ (∑ j : Fin n, w j ^ k).re := by
  set M : ℕ := 2 * n + 1
  have hM : 1 ≤ M := by omega
  have hM1 : M - 1 = 2 * n := by omega
  have hsum_ge :
      ((n : ℝ) + 1) / 2 ≤
        ∑ k ∈ Finset.Icc 1 (2 * n), (1 - (k : ℝ) / (M : ℝ)) * (∑ j : Fin n, w j ^ k).re := by
    have hswap :
        ∑ k ∈ Finset.Icc 1 (2 * n), (1 - (k : ℝ) / (M : ℝ)) * (∑ j : Fin n, w j ^ k).re =
          ∑ j : Fin n, ∑ k ∈ Finset.Icc 1 (2 * n), (1 - (k : ℝ) / (M : ℝ)) * (w j ^ k).re := by
      simp_rw [Complex.re_sum, Finset.mul_sum]
      exact Finset.sum_comm
    rw [hswap]
    have h0_mem : (⟨0, hn⟩ : Fin n) ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ _
    rw [← Finset.add_sum_erase _ _ h0_mem]
    have h0_val :
        ∑ k ∈ Finset.Icc 1 (2 * n), (1 - (k : ℝ) / (M : ℝ)) * (w ⟨0, hn⟩ ^ k).re = (n : ℝ) := by
      simp only [hw0, one_pow, Complex.one_re, mul_one, ← hM1, sum_fejer_weights hM]
      dsimp only [M]; push_cast; ring
    have hrest :
        -(((n : ℝ) - 1) / 2) ≤
          ∑ j ∈ Finset.univ.erase ⟨0, hn⟩,
            ∑ k ∈ Finset.Icc 1 (2 * n), (1 - (k : ℝ) / (M : ℝ)) * (w j ^ k).re := by
      have hcard : ((Finset.univ.erase (⟨0, hn⟩ : Fin n)).card : ℝ) = (n : ℝ) - 1 := by
        rw [Finset.card_erase_of_mem h0_mem, Finset.card_univ, Fintype.card_fin]
        have : (n - 1) + 1 = n := by omega
        have hR : (((n - 1 : ℕ) : ℝ)) + 1 = (n : ℝ) := by exact_mod_cast this
        linarith
      calc -(((n : ℝ) - 1) / 2)
          = ∑ _j ∈ Finset.univ.erase (⟨0, hn⟩ : Fin n), (-(1 / 2 : ℝ)) := by
            rw [Finset.sum_const, nsmul_eq_mul, hcard]; ring
        _ ≤ ∑ j ∈ Finset.univ.erase (⟨0, hn⟩ : Fin n),
              ∑ k ∈ Finset.Icc 1 (2 * n), (1 - (k : ℝ) / (M : ℝ)) * (w j ^ k).re := by
            refine Finset.sum_le_sum fun j _ => ?_
            have hpos := fejer_disk_positivity hM (hw j)
            rw [hM1] at hpos
            linarith
    linarith
  have hne : (Finset.Icc 1 (2 * n)).Nonempty := ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩⟩
  obtain ⟨k₀, hk₀_mem, hk₀_max⟩ := Finset.exists_max_image (Finset.Icc 1 (2 * n))
    (fun k => (∑ j : Fin n, w j ^ k).re) hne
  refine ⟨k₀, hk₀_mem, ?_⟩
  have hwt_nn : ∀ k ∈ Finset.Icc 1 (2 * n), 0 ≤ 1 - (k : ℝ) / (M : ℝ) := by
    intro k hk
    have hkM : (k : ℝ) ≤ (M : ℝ) := by
      exact_mod_cast (show k ≤ M by have := (Finset.mem_Icc.mp hk).2; omega)
    have hdiv : (k : ℝ) / (M : ℝ) ≤ 1 := (div_le_one (Nat.cast_pos.mpr hM)).mpr hkM
    linarith
  have hup :
      ∑ k ∈ Finset.Icc 1 (2 * n), (1 - (k : ℝ) / (M : ℝ)) * (∑ j : Fin n, w j ^ k).re ≤
        (n : ℝ) * (∑ j : Fin n, w j ^ k₀).re := by
    calc ∑ k ∈ Finset.Icc 1 (2 * n), (1 - (k : ℝ) / (M : ℝ)) * (∑ j : Fin n, w j ^ k).re
        ≤ ∑ k ∈ Finset.Icc 1 (2 * n),
            (1 - (k : ℝ) / (M : ℝ)) * (∑ j : Fin n, w j ^ k₀).re :=
          Finset.sum_le_sum fun k hk =>
            mul_le_mul_of_nonneg_left (hk₀_max k hk) (hwt_nn k hk)
      _ = (∑ k ∈ Finset.Icc 1 (2 * n), (1 - (k : ℝ) / (M : ℝ))) *
            (∑ j : Fin n, w j ^ k₀).re := (Finset.sum_mul _ _ _).symm
      _ = (n : ℝ) * (∑ j : Fin n, w j ^ k₀).re := by
          rw [← hM1, sum_fejer_weights hM]; dsimp only [M]; push_cast; ring
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  nlinarith

/-- **WEIGHTED FEJÉR SUM LOWER BOUND FOR `(1 - ε)`-SCALED EVEN POWERS**:
used directly in Deuring–Heilbronn! If `z : Fin n → ℂ` has `z 0 = 1` and
`∀ j, (1 - ε) * ‖z j‖ ≤ 1` with `0 ≤ ε`, `2 * M * ε ≤ 1 / 4`, and `M ≥ 1`, then
`∑ m ∈ Finset.Icc 1 (M - 1), (1 - m / M) * (1 - ε) ^ (2 * m) * Re(∑ j, z j ^ (2 * m))
  ≥ (3 / 8) * (M - 1) - (n - 1) / 2`. -/
theorem fejer_even_power_sum_weighted_lower {n : ℕ} (hn : 0 < n) (z : Fin n → ℂ)
    (hz0 : z ⟨0, hn⟩ = 1) {M : ℕ} (hM : 1 ≤ M) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hMε : 2 * (M : ℝ) * ε ≤ 1 / 4) (hz : ∀ j : Fin n, (1 - ε) * ‖z j‖ ≤ 1) :
    (3 / 8 : ℝ) * ((M : ℝ) - 1) - ((n : ℝ) - 1) / 2 ≤
      ∑ m ∈ Finset.Icc 1 (M - 1),
        (1 - (m : ℝ) / (M : ℝ)) * (1 - ε) ^ (2 * m) *
          (∑ j : Fin n, z j ^ (2 * m)).re := by
  have hε_le : ε ≤ 1 / 8 := by
    have hM1 : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
    nlinarith
  have h1ε_nn : 0 ≤ 1 - ε := by linarith
  let u : Fin n → ℂ := fun j => (((1 - ε : ℝ) : ℂ) * z j) ^ 2
  have hu_norm : ∀ j : Fin n, ‖u j‖ ≤ 1 := by
    intro j
    dsimp only [u]
    rw [norm_pow, norm_mul, Complex.norm_real, Real.norm_of_nonneg h1ε_nn]
    have h1 := hz j
    have hnn : 0 ≤ (1 - ε) * ‖z j‖ := mul_nonneg h1ε_nn (norm_nonneg _)
    nlinarith
  have hu_pow_re : ∀ (j : Fin n) (m : ℕ),
      (u j ^ m).re = (1 - ε) ^ (2 * m) * (z j ^ (2 * m)).re := by
    intro j m
    dsimp only [u]
    rw [← pow_mul, mul_pow, ← Complex.ofReal_pow, Complex.re_ofReal_mul]
  have hrewrite :
      ∑ m ∈ Finset.Icc 1 (M - 1),
          (1 - (m : ℝ) / (M : ℝ)) * (1 - ε) ^ (2 * m) * (∑ j : Fin n, z j ^ (2 * m)).re =
        ∑ j : Fin n, ∑ m ∈ Finset.Icc 1 (M - 1),
          (1 - (m : ℝ) / (M : ℝ)) * (u j ^ m).re := by
    trans ∑ m ∈ Finset.Icc 1 (M - 1), ∑ j : Fin n,
        (1 - (m : ℝ) / (M : ℝ)) * (u j ^ m).re
    · refine Finset.sum_congr rfl fun m _ => ?_
      rw [Complex.re_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hu_pow_re j m]; ring
    · exact Finset.sum_comm
  rw [hrewrite]
  have h0_mem : (⟨0, hn⟩ : Fin n) ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ _
  rw [← Finset.add_sum_erase _ _ h0_mem]
  have h0_ge :
      (3 / 8 : ℝ) * ((M : ℝ) - 1) ≤
        ∑ m ∈ Finset.Icc 1 (M - 1), (1 - (m : ℝ) / (M : ℝ)) * (u ⟨0, hn⟩ ^ m).re := by
    have hbern : (3 / 4 : ℝ) ≤ (1 - ε) ^ (2 * M) := by
      have h1 : 1 + ((2 * M : ℕ) : ℝ) * (-ε) ≤ (1 + (-ε)) ^ (2 * M) :=
        one_add_mul_le_pow (by linarith : (-2 : ℝ) ≤ -ε) (2 * M)
      rw [show (1 : ℝ) + -ε = 1 - ε by ring] at h1
      push_cast at h1
      linarith
    have hwt_nn : ∀ m ∈ Finset.Icc 1 (M - 1), 0 ≤ 1 - (m : ℝ) / (M : ℝ) := by
      intro m hm
      have hmM : (m : ℝ) ≤ (M : ℝ) := by
        exact_mod_cast (show m ≤ M by have := (Finset.mem_Icc.mp hm).2; omega)
      have hdiv : (m : ℝ) / (M : ℝ) ≤ 1 := (div_le_one (Nat.cast_pos.mpr hM)).mpr hmM
      linarith
    have hmono : ∀ m ∈ Finset.Icc 1 (M - 1), (3 / 4 : ℝ) ≤ (1 - ε) ^ (2 * m) := by
      intro m hm
      have h2m : 2 * m ≤ 2 * M := by have := (Finset.mem_Icc.mp hm).2; omega
      exact hbern.trans (pow_le_pow_of_le_one h1ε_nn (by linarith) h2m)
    calc (3 / 8 : ℝ) * ((M : ℝ) - 1)
        = (3 / 4 : ℝ) * (((M : ℝ) - 1) / 2) := by ring
      _ = (3 / 4 : ℝ) * ∑ m ∈ Finset.Icc 1 (M - 1), (1 - (m : ℝ) / (M : ℝ)) := by
          rw [sum_fejer_weights hM]
      _ = ∑ m ∈ Finset.Icc 1 (M - 1), (1 - (m : ℝ) / (M : ℝ)) * (3 / 4 : ℝ) := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun m _ => by ring
      _ ≤ ∑ m ∈ Finset.Icc 1 (M - 1), (1 - (m : ℝ) / (M : ℝ)) * (u ⟨0, hn⟩ ^ m).re := by
          refine Finset.sum_le_sum fun m hm => ?_
          rw [hu_pow_re ⟨0, hn⟩ m, hz0, one_pow, Complex.one_re, mul_one]
          exact mul_le_mul_of_nonneg_left (hmono m hm) (hwt_nn m hm)
  have hrest_ge :
      -(((n : ℝ) - 1) / 2) ≤
        ∑ j ∈ Finset.univ.erase ⟨0, hn⟩,
          ∑ m ∈ Finset.Icc 1 (M - 1), (1 - (m : ℝ) / (M : ℝ)) * (u j ^ m).re := by
    have hcard : ((Finset.univ.erase (⟨0, hn⟩ : Fin n)).card : ℝ) = (n : ℝ) - 1 := by
      rw [Finset.card_erase_of_mem h0_mem, Finset.card_univ, Fintype.card_fin]
      have : (n - 1) + 1 = n := by omega
      have hR : (((n - 1 : ℕ) : ℝ)) + 1 = (n : ℝ) := by exact_mod_cast this
      linarith
    calc -(((n : ℝ) - 1) / 2)
        = ∑ _j ∈ Finset.univ.erase (⟨0, hn⟩ : Fin n), (-(1 / 2 : ℝ)) := by
          rw [Finset.sum_const, nsmul_eq_mul, hcard]; ring
      _ ≤ ∑ j ∈ Finset.univ.erase (⟨0, hn⟩ : Fin n),
            ∑ m ∈ Finset.Icc 1 (M - 1), (1 - (m : ℝ) / (M : ℝ)) * (u j ^ m).re := by
          refine Finset.sum_le_sum fun j _ => ?_
          have hpos := fejer_disk_positivity hM (hu_norm j)
          linarith
  linarith

/-! ## Section 2: Scaled High Derivatives `scaledDeriv k`, Positivity & Hadamard Differentiation -/

/-- Scaled alternating `k`-th derivative `((-1)^k / k!) * f^{(k)}(s)`. -/
def scaledDeriv (k : ℕ) (f : ℂ → ℂ) (s : ℂ) : ℂ :=
  ((-1 : ℂ) ^ k / (k.factorial : ℂ)) * iteratedDeriv k f s

lemma scaledDeriv_congr_nhds {k : ℕ} {f g : ℂ → ℂ} {s : ℂ} (h : f =ᶠ[𝓝 s] g) :
    scaledDeriv k f s = scaledDeriv k g s := by
  unfold scaledDeriv
  rw [h.iteratedDeriv_eq k]

lemma scaledDeriv_add {k : ℕ} {f g : ℂ → ℂ} {s : ℂ}
    (hf : ContDiffAt ℂ k f s) (hg : ContDiffAt ℂ k g s) :
    scaledDeriv k (fun z => f z + g z) s = scaledDeriv k f s + scaledDeriv k g s := by
  unfold scaledDeriv
  rw [iteratedDeriv_fun_add hf hg, mul_add]

lemma scaledDeriv_sub {k : ℕ} {f g : ℂ → ℂ} {s : ℂ}
    (hf : ContDiffAt ℂ k f s) (hg : ContDiffAt ℂ k g s) :
    scaledDeriv k (fun z => f z - g z) s = scaledDeriv k f s - scaledDeriv k g s := by
  unfold scaledDeriv
  rw [iteratedDeriv_fun_sub hf hg, mul_sub]

lemma scaledDeriv_const_mul {k : ℕ} (c : ℂ) {f : ℂ → ℂ} {s : ℂ} :
    scaledDeriv k (fun z => c * f z) s = c * scaledDeriv k f s := by
  unfold scaledDeriv
  rw [iteratedDeriv_const_mul_field]; ring

lemma scaledDeriv_const_eq_zero {k : ℕ} (hk : 1 ≤ k) (c s : ℂ) :
    scaledDeriv k (fun _ : ℂ => c) s = 0 := by
  have hiter : ∀ m : ℕ, 1 ≤ m → iteratedDeriv m (fun _ : ℂ => c) = fun _ => 0 := by
    intro m hm
    induction m with
    | zero => omega
    | succ m ih =>
      rcases m with _ | m
      · ext z; simp [iteratedDeriv_one]
      · rw [iteratedDeriv_succ, ih (by omega)]
        ext z; simp
  unfold scaledDeriv
  rw [hiter k hk]
  simp

/-- Exact `k`-th derivative of `(z - w)⁻¹` at any `s ≠ w`. -/
lemma iteratedDeriv_sub_const_inv (w : ℂ) (k : ℕ) :
    ∀ s : ℂ, s ≠ w →
      iteratedDeriv k (fun z : ℂ => (z - w)⁻¹) s =
        (-1 : ℂ) ^ k * (k.factorial : ℂ) * ((s - w)⁻¹) ^ (k + 1) := by
  induction k with
  | zero => intro s _; simp
  | succ k ih =>
    intro s hs
    rw [iteratedDeriv_succ]
    have hopen : IsOpen ({w}ᶜ : Set ℂ) := isClosed_singleton.isOpen_compl
    have hev : iteratedDeriv k (fun z : ℂ => (z - w)⁻¹) =ᶠ[𝓝 s]
        fun z : ℂ => (-1 : ℂ) ^ k * (k.factorial : ℂ) * ((z - w)⁻¹) ^ (k + 1) := by
      filter_upwards [hopen.mem_nhds hs] with z hz
      exact ih z hz
    rw [hev.deriv_eq]
    have hsub_ne : s - w ≠ 0 := sub_ne_zero.mpr hs
    have hd1 : HasDerivAt (fun z : ℂ => (z - w)⁻¹) (-(s - w)⁻¹ ^ 2) s := by
      have h := ((hasDerivAt_id s).sub_const w).inv hsub_ne
      exact h.congr_deriv (by simp only [id]; field_simp [hsub_ne])
    have hd2 : HasDerivAt (fun z : ℂ => ((z - w)⁻¹) ^ (k + 1))
        (((k + 1 : ℕ) : ℂ) * ((s - w)⁻¹) ^ k * (-(s - w)⁻¹ ^ 2)) s :=
      hd1.pow (k + 1)
    have hd3 := hd2.const_mul ((-1 : ℂ) ^ k * (k.factorial : ℂ))
    rw [hd3.deriv, Nat.factorial_succ]
    push_cast
    ring

/-- Exact `scaledDeriv k` of `z ↦ 1 / (z - w)`: equals `1 / (s - w) ^ (k + 1)` at `s ≠ w`. -/
lemma scaledDeriv_inv_sub (w : ℂ) (k : ℕ) {s : ℂ} (hs : s ≠ w) :
    scaledDeriv k (fun z : ℂ => 1 / (z - w)) s = 1 / (s - w) ^ (k + 1) := by
  unfold scaledDeriv
  have hfun : (fun z : ℂ => 1 / (z - w)) = fun z : ℂ => (z - w)⁻¹ := by
    ext z; rw [one_div]
  rw [hfun, iteratedDeriv_sub_const_inv w k s hs]
  have hfac : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
  have hsign : (-1 : ℂ) ^ k * (-1 : ℂ) ^ k = 1 := by rw [← mul_pow]; norm_num
  calc ((-1 : ℂ) ^ k / (k.factorial : ℂ)) *
          ((-1 : ℂ) ^ k * (k.factorial : ℂ) * ((s - w)⁻¹) ^ (k + 1))
      = ((-1 : ℂ) ^ k * (-1 : ℂ) ^ k) * ((k.factorial : ℂ) / (k.factorial : ℂ)) *
          ((s - w)⁻¹) ^ (k + 1) := by ring
    _ = 1 * 1 * ((s - w)⁻¹) ^ (k + 1) := by rw [hsign, div_self hfac]
    _ = 1 / (s - w) ^ (k + 1) := by rw [one_mul, one_mul, inv_pow, one_div]

/-- Summability of the `scaledDeriv k` terms of any Dirichlet series convergent on `Re(s) > 1`. -/
private lemma summable_scaledDeriv_LSeries {a : ℕ → ℂ}
    (hconv : ∀ x : ℝ, 1 < x → LSeriesSummable a (x : ℂ))
    {s : ℂ} (hs : 1 < s.re) (k : ℕ) :
    Summable (fun n : ℕ =>
      if n = 0 then (0 : ℂ)
      else a n * ((((Real.log (n : ℝ)) ^ k / (k.factorial : ℝ) : ℝ) : ℂ)) / (n : ℂ) ^ s) := by
  set ε : ℝ := (s.re - 1) / 2
  have hε_pos : 0 < ε := by dsimp only [ε]; linarith
  set x : ℝ := 1 + ε
  have hx1 : 1 < x := by dsimp only [x]; linarith
  have hbase : Summable (fun n : ℕ => (ε⁻¹) ^ k * ‖LSeries.term a (x : ℂ) n‖) :=
    (hconv x hx1).norm.mul_left ((ε⁻¹) ^ k)
  refine Summable.of_norm_bounded hbase fun n => ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp [LSeries.term_zero]
  · rw [if_neg hn, LSeries.term_of_ne_zero hn]
    have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    have hlog_nn : 0 ≤ Real.log (n : ℝ) := Real.log_natCast_nonneg n
    have hexp : (ε * Real.log (n : ℝ)) ^ k / (k.factorial : ℝ) ≤
        Real.exp (ε * Real.log (n : ℝ)) := by
      have h1 := Real.sum_le_exp_of_nonneg (x := ε * Real.log (n : ℝ)) (by positivity) (k + 1)
      exact (Finset.single_le_sum
        (f := fun j : ℕ => (ε * Real.log (n : ℝ)) ^ j / (j.factorial : ℝ))
        (fun j _ => by positivity) (Finset.mem_range.mpr (Nat.lt_succ_self k))).trans h1
    have hlog_bd : (Real.log (n : ℝ)) ^ k / (k.factorial : ℝ) ≤
        (ε⁻¹) ^ k * (n : ℝ) ^ ε := by
      have hrexp : Real.exp (ε * Real.log (n : ℝ)) = (n : ℝ) ^ ε := by
        rw [Real.rpow_def_of_pos hn_pos, mul_comm]
      rw [hrexp, mul_pow, mul_div_assoc] at hexp
      have hεk : (0 : ℝ) < (ε⁻¹) ^ k := by positivity
      have hmul := mul_le_mul_of_nonneg_left hexp hεk.le
      calc (Real.log (n : ℝ)) ^ k / (k.factorial : ℝ)
          = (ε⁻¹) ^ k * (ε ^ k * ((Real.log (n : ℝ)) ^ k / (k.factorial : ℝ))) := by
            rw [← mul_assoc, ← mul_pow, inv_mul_cancel₀ hε_pos.ne', one_pow, one_mul]
        _ ≤ (ε⁻¹) ^ k * (n : ℝ) ^ ε := hmul
    rw [norm_div, norm_mul, norm_div, Complex.norm_real,
      Real.norm_of_nonneg (by positivity),
      Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn),
      Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn), Complex.ofReal_re]
    have hpow_eq : (n : ℝ) ^ ε / (n : ℝ) ^ s.re = 1 / (n : ℝ) ^ x := by
      have hsx : s.re = ε + x := by dsimp only [x, ε]; ring
      rw [hsx, Real.rpow_add hn_pos]
      have hne1 : (n : ℝ) ^ ε ≠ 0 := (Real.rpow_pos_of_pos hn_pos ε).ne'
      have hne2 : (n : ℝ) ^ x ≠ 0 := (Real.rpow_pos_of_pos hn_pos x).ne'
      field_simp [hne1, hne2]
    calc ‖a n‖ * ((Real.log (n : ℝ)) ^ k / (k.factorial : ℝ)) / (n : ℝ) ^ s.re
        ≤ ‖a n‖ * ((ε⁻¹) ^ k * (n : ℝ) ^ ε) / (n : ℝ) ^ s.re := by gcongr
      _ = (ε⁻¹) ^ k * ‖a n‖ * ((n : ℝ) ^ ε / (n : ℝ) ^ s.re) := by ring
      _ = (ε⁻¹) ^ k * (‖a n‖ / (n : ℝ) ^ x) := by rw [hpow_eq]; ring

private lemma logMul_iterate_apply_local (a : ℕ → ℂ) (k n : ℕ) :
    (LSeries.logMul^[k] a) n = (Complex.log (n : ℂ)) ^ k * a n := by
  induction k generalizing a with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply, ih]
    simp [LSeries.logMul]
    ring

/-- Exact `scaledDeriv k` of a convergent Dirichlet series `LSeries a` on `1 < s.re`. -/
lemma scaledDeriv_LSeries_eq {a : ℕ → ℂ}
    (hconv : ∀ x : ℝ, 1 < x → LSeriesSummable a (x : ℂ))
    {s : ℂ} (hs : 1 < s.re) (k : ℕ) :
    scaledDeriv k (LSeries a) s =
      ∑' n : ℕ, if n = 0 then 0
        else a n * ((((Real.log (n : ℝ)) ^ k / (k.factorial : ℝ) : ℝ) : ℂ)) / (n : ℂ) ^ s := by
  have habs : LSeries.abscissaOfAbsConv a ≤ (1 : EReal) :=
    LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable hconv
  have hlt : LSeries.abscissaOfAbsConv a < (s.re : EReal) :=
    lt_of_le_of_lt habs (EReal.coe_lt_coe_iff.mpr hs)
  unfold scaledDeriv
  rw [LSeries_iteratedDeriv k hlt]
  have hsign : (-1 : ℂ) ^ k * (-1 : ℂ) ^ k = 1 := by rw [← mul_pow]; norm_num
  have hpull : ((-1 : ℂ) ^ k / (k.factorial : ℂ)) *
      ((-1 : ℂ) ^ k * LSeries (LSeries.logMul^[k] a) s) =
      (k.factorial : ℂ)⁻¹ * LSeries (LSeries.logMul^[k] a) s := by
    calc ((-1 : ℂ) ^ k / (k.factorial : ℂ)) *
            ((-1 : ℂ) ^ k * LSeries (LSeries.logMul^[k] a) s)
        = ((-1 : ℂ) ^ k * (-1 : ℂ) ^ k) * (k.factorial : ℂ)⁻¹ *
            LSeries (LSeries.logMul^[k] a) s := by ring
      _ = (k.factorial : ℂ)⁻¹ * LSeries (LSeries.logMul^[k] a) s := by rw [hsign, one_mul]
  rw [hpull, LSeries, ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  by_cases hn : n = 0
  · subst hn; simp [LSeries.term_zero]
  · have hn0 : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    rw [if_neg hn, LSeries.term_of_ne_zero hn, logMul_iterate_apply_local]
    have hlog : Complex.log (n : ℂ) = (Real.log (n : ℝ) : ℂ) := by
      rw [← Complex.ofReal_natCast, Complex.ofReal_log hn0.le]
    rw [hlog]
    push_cast
    ring

/-- **EXACT 4-CHARACTER HIGH-DERIVATIVE POSITIVITY (`0` ASSUMPTIONS!)**:
for every real character `χ₁ mod q₁`, EVERY character `χ mod q`, EVERY `σ > 1`, EVERY `γ : ℝ`,
and EVERY `k : ℕ`:
`0 ≤ (scaledDeriv k (negLogDerivZeta + negLogDerivL χ₁) σ +
      scaledDeriv k (negLogDerivL χ + negLogDerivL (prodChar χ χ₁)) (σ + I * γ)).re`. -/
theorem re_scaledDeriv_four_char_nonneg {q₁ q : ℕ} [NeZero q₁] [NeZero q]
    (χ₁ : DirichletCharacter ℂ q₁) (hreal₁ : IsRealChar χ₁)
    (χ : DirichletCharacter ℂ q) {σ : ℝ} (hσ : 1 < σ) (γ : ℝ) (k : ℕ) :
    0 ≤ (scaledDeriv k (fun z => negLogDerivZeta z + negLogDerivL χ₁ z) (σ : ℂ) +
      scaledDeriv k (fun z => negLogDerivL χ z + negLogDerivL (prodChar χ χ₁) z)
        ((σ : ℂ) + I * (γ : ℂ))).re := by
  let a₀ : ℕ → ℂ := fun n => (Λ n : ℂ) * (1 + χ₁ n)
  let a₁ : ℕ → ℂ := fun n => (Λ n : ℂ) * (1 + χ₁ n) * χ n
  have hconv₀ : ∀ x : ℝ, 1 < x → LSeriesSummable a₀ (x : ℂ) := by
    intro x hx
    have hx' : 1 < (x : ℂ).re := by simpa using hx
    have hZ := ArithmeticFunction.LSeriesSummable_vonMangoldt hx'
    have h1 : LSeriesSummable (fun n => χ₁ n * (Λ n : ℂ)) (x : ℂ) :=
      χ₁.LSeriesSummable_twist_vonMangoldt hx'
    refine (hZ.add h1).congr fun n => ?_
    rcases eq_or_ne n 0 with rfl | hn
    · simp [LSeries.term_zero]
    · simp only [LSeries.term_of_ne_zero hn, a₀, Pi.add_apply]; ring
  have hconv₁ : ∀ x : ℝ, 1 < x → LSeriesSummable a₁ (x : ℂ) := by
    intro x hx
    have hx' : 1 < (x : ℂ).re := by simpa using hx
    have hχ : LSeriesSummable (fun n => χ n * (Λ n : ℂ)) (x : ℂ) :=
      χ.LSeriesSummable_twist_vonMangoldt hx'
    have hprod : LSeriesSummable (fun n => (prodChar χ χ₁) n * (Λ n : ℂ)) (x : ℂ) :=
      (prodChar χ χ₁).LSeriesSummable_twist_vonMangoldt hx'
    refine (hχ.add hprod).congr fun n => ?_
    rcases eq_or_ne n 0 with rfl | hn
    · simp [LSeries.term_zero]
    · simp only [LSeries.term_of_ne_zero hn, a₁, Pi.add_apply, prodChar_apply_nat]; ring
  have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hev₀ : (fun z => negLogDerivZeta z + negLogDerivL χ₁ z) =ᶠ[𝓝 (σ : ℂ)] LSeries a₀ := by
    filter_upwards [hopen.mem_nhds (by simpa using hσ)] with z (hz : 1 < z.re)
    rw [negLogDerivZeta_eq_LSeries hz, negLogDerivL_eq_LSeries χ₁ hz]
    have hZ := ArithmeticFunction.LSeriesSummable_vonMangoldt hz
    have h1 : LSeriesSummable (fun n => χ₁ n * (Λ n : ℂ)) z :=
      χ₁.LSeriesSummable_twist_vonMangoldt hz
    unfold LSeries
    rw [← Summable.tsum_add hZ h1]
    refine tsum_congr fun n => ?_
    rcases eq_or_ne n 0 with rfl | hn
    · simp [LSeries.term_zero]
    · simp only [LSeries.term_of_ne_zero hn, a₀]; ring
  have hev₁ : (fun z => negLogDerivL χ z + negLogDerivL (prodChar χ χ₁) z) =ᶠ[𝓝 ((σ : ℂ) + I * (γ : ℂ))]
      LSeries a₁ := by
    filter_upwards [hopen.mem_nhds (by simp [hσ])] with z (hz : 1 < z.re)
    rw [negLogDerivL_eq_LSeries χ hz, negLogDerivL_eq_LSeries (prodChar χ χ₁) hz]
    have hχ : LSeriesSummable (fun n => χ n * (Λ n : ℂ)) z :=
      χ.LSeriesSummable_twist_vonMangoldt hz
    have hprod : LSeriesSummable (fun n => (prodChar χ χ₁) n * (Λ n : ℂ)) z :=
      (prodChar χ χ₁).LSeriesSummable_twist_vonMangoldt hz
    unfold LSeries
    rw [← Summable.tsum_add hχ hprod]
    refine tsum_congr fun n => ?_
    rcases eq_or_ne n 0 with rfl | hn
    · simp [LSeries.term_zero]
    · simp only [LSeries.term_of_ne_zero hn, a₁, prodChar_apply_nat]; ring
  rw [scaledDeriv_congr_nhds hev₀, scaledDeriv_congr_nhds hev₁,
    scaledDeriv_LSeries_eq hconv₀ (by simpa using hσ) k,
    scaledDeriv_LSeries_eq hconv₁ (by simp [hσ]) k]
  have hsum₀ := summable_scaledDeriv_LSeries hconv₀ (s := (σ : ℂ)) (by simpa using hσ) k
  have hsum₁ := summable_scaledDeriv_LSeries hconv₁ (s := (σ : ℂ) + I * (γ : ℂ)) (by simp [hσ]) k
  rw [← Summable.tsum_add hsum₀ hsum₁, Complex.re_tsum (hsum₀.add hsum₁)]
  refine tsum_nonneg fun n => ?_
  by_cases hn : n = 0
  · simp [hn]
  · simp only [if_neg hn]
    have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    have hcpow_σ : (n : ℂ) ^ (σ : ℂ) = (((n : ℝ) ^ σ : ℝ) : ℂ) := by
      rw [← Complex.ofReal_natCast, Complex.ofReal_cpow hn_pos.le]
    have hcpow_add : (n : ℂ) ^ ((σ : ℂ) + I * (γ : ℂ)) =
        (((n : ℝ) ^ σ : ℝ) : ℂ) * (n : ℂ) ^ (I * (γ : ℂ)) := by
      rw [Complex.cpow_add _ _ hnC, hcpow_σ]
    have hreal_fac : (1 + χ₁ (n : ZMod q₁)) = (((1 + (χ₁ (n : ZMod q₁)).re : ℝ) : ℂ)) := by
      apply Complex.ext
      · simp
      · simp [hreal₁ (n : ZMod q₁)]
    set w : ℂ := χ (n : ZMod q) * (n : ℂ) ^ (-(I * (γ : ℂ)))
    have hw_norm : ‖w‖ ≤ 1 := by
      dsimp only [w]
      rw [norm_mul, Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn)]
      simp only [Complex.neg_re, Complex.mul_re, Complex.I_re, Complex.ofReal_re, zero_mul,
        Complex.I_im, Complex.ofReal_im, mul_zero, sub_self, neg_zero, Real.rpow_zero, mul_one]
      exact χ.norm_le_one _
    have h1w_nn : 0 ≤ 1 + w.re := by
      have h1 := (abs_le.mp ((Complex.abs_re_le_norm w).trans hw_norm)).1
      linarith
    have h1χ₁_nn : 0 ≤ 1 + (χ₁ (n : ZMod q₁)).re := by
      linarith [(isRealChar_apply_re_bounds (χ := χ₁) (n : ZMod q₁)).1]
    set c : ℝ := Λ n * (1 + (χ₁ (n : ZMod q₁)).re) *
        ((Real.log (n : ℝ)) ^ k / (k.factorial : ℝ)) / (n : ℝ) ^ σ
    have hc_nn : 0 ≤ c := by
      dsimp only [c]
      have hlog_nn : 0 ≤ Real.log (n : ℝ) := Real.log_natCast_nonneg n
      have hΛ_nn : 0 ≤ Λ n := ArithmeticFunction.vonMangoldt_nonneg
      positivity
    have hterm_eq :
        a₀ n * ((((Real.log (n : ℝ)) ^ k / (k.factorial : ℝ) : ℝ) : ℂ)) / (n : ℂ) ^ (σ : ℂ) +
          a₁ n * ((((Real.log (n : ℝ)) ^ k / (k.factorial : ℝ) : ℝ) : ℂ)) /
            (n : ℂ) ^ ((σ : ℂ) + I * (γ : ℂ)) =
        (c : ℂ) * (1 + w) := by
      dsimp only [a₀, a₁, c, w]
      rw [hcpow_σ, hcpow_add, hreal_fac, Complex.cpow_neg]
      have hpow_ne : (((n : ℝ) ^ σ : ℝ) : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos hn_pos σ).ne'
      have hpowI_ne : (n : ℂ) ^ (I * (γ : ℂ)) ≠ 0 := by
        rw [Complex.cpow_def_of_ne_zero hnC]; exact Complex.exp_ne_zero _
      push_cast
      field_simp [hpow_ne, hpowI_ne]
    rw [hterm_eq, Complex.re_ofReal_mul, Complex.add_re, Complex.one_re]
    exact mul_nonneg hc_nn h1w_nn

/-- **CAUCHY `k`-TH DERIVATIVE ESTIMATE FOR `scaledDeriv k`**:
if `f` is holomorphic on `closedBall s R` (`R > 0`) and `‖f z‖ ≤ M` on `sphere s R` (`M ≥ 0`),
then `‖scaledDeriv k f s‖ ≤ M / R ^ k`. -/
theorem norm_scaledDeriv_le_of_sphere {f : ℂ → ℂ} {s : ℂ} {R M : ℝ}
    (hR : 0 < R) (_hM : 0 ≤ M)
    (hf : DifferentiableOn ℂ f (Metric.closedBall s R))
    (hbd : ∀ z ∈ Metric.sphere s R, ‖f z‖ ≤ M) (k : ℕ) :
    ‖scaledDeriv k f s‖ ≤ M / R ^ k := by
  set RN : NNReal := ⟨R, hR.le⟩
  have hRN_pos : (0 : NNReal) < RN := by change (0 : ℝ) < R; exact hR
  have hRN_val : (RN : ℝ) = R := rfl
  have hf_RN : DifferentiableOn ℂ f (Metric.closedBall s (RN : ℝ)) := hf
  have hpow : HasFPowerSeriesOnBall f (cauchyPowerSeries f s (RN : ℝ)) s (RN : ENNReal) :=
    hf_RN.hasFPowerSeriesOnBall hRN_pos
  have hfac := hpow.factorial_smul (1 : ℂ) k
  have hmult : (iteratedFDeriv ℂ k f s) (fun _ : Fin k => (1 : ℂ)) = iteratedDeriv k f s := by
    rw [← iteratedDeriv_eq_iteratedFDeriv]
  have hfac_ne : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
  have hnorm_eq : ‖scaledDeriv k f s‖ = ‖cauchyPowerSeries f s (RN : ℝ) k (fun _ => (1 : ℂ))‖ := by
    have h1 : cauchyPowerSeries f s (RN : ℝ) k (fun _ => (1 : ℂ)) =
        iteratedDeriv k f s / (k.factorial : ℂ) := by
      rw [nsmul_eq_mul, hmult] at hfac
      exact (eq_div_iff hfac_ne).mpr (by rw [mul_comm, hfac])
    unfold scaledDeriv
    rw [h1, norm_mul, norm_div, norm_pow, norm_neg, norm_one, one_pow, norm_div]
    ring
  rw [hnorm_eq]
  have hint_le :
      (2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..2 * Real.pi, ‖f (circleMap s (RN : ℝ) θ)‖ ≤ M := by
    have hcont : ContinuousOn (fun θ : ℝ => ‖f (circleMap s (RN : ℝ) θ)‖) (Set.uIcc 0 (2 * Real.pi)) := by
      refine ContinuousOn.norm (hf.continuousOn.comp (continuous_circleMap s (RN : ℝ)).continuousOn ?_)
      intro θ _
      exact Metric.sphere_subset_closedBall (circleMap_mem_sphere s hR.le θ)
    have hmono :
        ∫ θ in (0 : ℝ)..2 * Real.pi, ‖f (circleMap s (RN : ℝ) θ)‖ ≤
          ∫ _θ in (0 : ℝ)..2 * Real.pi, M :=
      intervalIntegral.integral_mono_on (by positivity) hcont.intervalIntegrable
        intervalIntegrable_const fun θ _ => hbd _ (circleMap_mem_sphere s hR.le θ)
    rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hmono
    have h2pi_pos : 0 < 2 * Real.pi := by positivity
    calc (2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..2 * Real.pi, ‖f (circleMap s (RN : ℝ) θ)‖
        ≤ (2 * Real.pi)⁻¹ * (2 * Real.pi * M) :=
          mul_le_mul_of_nonneg_left hmono (inv_nonneg.mpr h2pi_pos.le)
      _ = M := by field_simp [h2pi_pos.ne']
  calc ‖cauchyPowerSeries f s (RN : ℝ) k (fun _ => (1 : ℂ))‖
      ≤ ‖cauchyPowerSeries f s (RN : ℝ) k‖ * ∏ _i : Fin k, ‖(1 : ℂ)‖ :=
        ContinuousMultilinearMap.le_opNorm _ _
    _ = ‖cauchyPowerSeries f s (RN : ℝ) k‖ := by simp
    _ ≤ ((2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..2 * Real.pi, ‖f (circleMap s (RN : ℝ) θ)‖) *
          |(RN : ℝ)|⁻¹ ^ k := norm_cauchyPowerSeries_le f s (RN : ℝ) k
    _ ≤ M * R⁻¹ ^ k := by
        rw [hRN_val, abs_of_pos hR]
        exact mul_le_mul_of_nonneg_right hint_le (by positivity)
    _ = M / R ^ k := by rw [inv_pow, div_eq_mul_inv]

/-- Functional equation of `Complex.digamma`: `digamma (w + 1) = digamma w + 1 / w` on `0 < w.re`. -/
private lemma digamma_add_one {w : ℂ} (hw : 0 < w.re) :
    Complex.digamma (w + 1) = Complex.digamma w + 1 / w := by
  have hw_ne : w ≠ 0 := fun h => by simp [h] at hw
  have hne_neg : ∀ z : ℂ, 0 < z.re → ∀ m : ℕ, z ≠ -(m : ℂ) := by
    intro z hz m h; have := congrArg Complex.re h; simp at this
    linarith [Nat.cast_nonneg (α := ℝ) m]
  have hGw : Complex.Gamma w ≠ 0 := Complex.Gamma_ne_zero (hne_neg w hw)
  have hGw1 : Complex.Gamma (w + 1) ≠ 0 := Complex.Gamma_ne_zero (hne_neg (w + 1) (by simp; linarith))
  have hopen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hev : (fun z : ℂ => Complex.Gamma (z + 1)) =ᶠ[𝓝 w] fun z : ℂ => z * Complex.Gamma z := by
    filter_upwards [hopen.mem_nhds hw] with z (hz : 0 < z.re)
    exact Complex.Gamma_add_one z (fun h => by simp [h] at hz)
  have hG_diff : HasDerivAt Complex.Gamma (deriv Complex.Gamma w) w :=
    (Complex.differentiableAt_Gamma w (hne_neg w hw)).hasDerivAt
  have hmul : HasDerivAt (fun z : ℂ => z * Complex.Gamma z)
      (1 * Complex.Gamma w + w * deriv Complex.Gamma w) w :=
    (hasDerivAt_id w).mul hG_diff
  have hderiv : deriv Complex.Gamma (w + 1) = Complex.Gamma w + w * deriv Complex.Gamma w := by
    have hshift : deriv (fun z : ℂ => Complex.Gamma (z + 1)) w = deriv Complex.Gamma (w + 1) := by
      simpa using deriv_comp_add_const Complex.Gamma (1 : ℂ) w
    rw [← hshift, hev.deriv_eq, hmul.deriv, one_mul]
  rw [Complex.digamma_def, logDeriv_apply, logDeriv_apply, hderiv,
    Complex.Gamma_add_one w hw_ne]
  field_simp [hw_ne, hGw]
  ring

/-- Wide-strip digamma bound: `‖Complex.digamma w‖ ≤ C * Real.log (|w.im| + 2)` on `1/4 ≤ w.re ≤ 2`. -/
theorem norm_digamma_wide_strip_le :
    ∃ C : ℝ, 0 < C ∧ ∀ w : ℂ, 1 / 4 ≤ w.re → w.re ≤ 2 →
      ‖Complex.digamma w‖ ≤ C * Real.log (|w.im| + 2) := by
  obtain ⟨C₀, hC₀_pos, hdig⟩ := Stage8HadamardLFunction.norm_digamma_strip_le
  refine ⟨C₀ + 16, by linarith, fun w hw1 hw2 => ?_⟩
  have hlog_ge : (1 / 2 : ℝ) < Real.log (|w.im| + 2) := by
    have h2 : (2 : ℝ) ≤ |w.im| + 2 := by linarith [abs_nonneg w.im]
    exact lt_of_lt_of_le (by linarith [Real.log_two_gt_d9]) (Real.log_le_log (by norm_num) h2)
  by_cases hlo : w.re < 1 / 2
  · have h1 := digamma_add_one (w := w) (by linarith)
    have hdig1 := hdig (w + 1) (by simp; linarith) (by simp; linarith)
    have him : (w + 1).im = w.im := by simp
    rw [him] at hdig1
    have hnorm_w : 1 / 4 ≤ ‖w‖ := by
      have := (le_abs_self w.re).trans (Complex.abs_re_le_norm w); linarith
    have hinv : ‖(1 : ℂ) / w‖ ≤ 4 := by
      rw [norm_div, norm_one]
      have : (1 : ℝ) / ‖w‖ ≤ 1 / (1 / 4) := one_div_le_one_div_of_le (by norm_num) hnorm_w
      linarith
    have heq : Complex.digamma w = Complex.digamma (w + 1) - 1 / w := by linear_combination -h1
    rw [heq]
    calc ‖Complex.digamma (w + 1) - 1 / w‖
        ≤ ‖Complex.digamma (w + 1)‖ + ‖(1 : ℂ) / w‖ := norm_sub_le _ _
      _ ≤ C₀ * Real.log (|w.im| + 2) + 4 := add_le_add hdig1 hinv
      _ ≤ (C₀ + 16) * Real.log (|w.im| + 2) := by nlinarith
  · push Not at hlo
    by_cases hhi : w.re ≤ 3 / 2
    · exact (hdig w hlo hhi).trans (by nlinarith)
    · push Not at hhi
      have h1 := digamma_add_one (w := w - 1) (by simp; linarith)
      rw [sub_add_cancel] at h1
      have hdig1 := hdig (w - 1) (by simp; linarith) (by simp; linarith)
      have him : (w - 1).im = w.im := by simp
      rw [him] at hdig1
      have hnorm_w1 : 1 / 2 ≤ ‖w - 1‖ := by
        have hre := (le_abs_self (w - 1).re).trans (Complex.abs_re_le_norm (w - 1))
        simp at hre; linarith
      have hinv : ‖(1 : ℂ) / (w - 1)‖ ≤ 2 := by
        rw [norm_div, norm_one]
        have : (1 : ℝ) / ‖w - 1‖ ≤ 1 / (1 / 2) := one_div_le_one_div_of_le (by norm_num) hnorm_w1
        linarith
      rw [h1]
      calc ‖Complex.digamma (w - 1) + 1 / (w - 1)‖
          ≤ ‖Complex.digamma (w - 1)‖ + ‖(1 : ℂ) / (w - 1)‖ := norm_add_le _ _
        _ ≤ C₀ * Real.log (|w.im| + 2) + 2 := add_le_add hdig1 hinv
        _ ≤ (C₀ + 16) * Real.log (|w.im| + 2) := by nlinarith

/-- Holomorphicity of `Complex.digamma` on `Re(w) > 0`. -/
private lemma differentiableOn_digamma_re_pos :
    DifferentiableOn ℂ Complex.digamma {w : ℂ | 0 < w.re} := by
  have hopen : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hne : ∀ w : ℂ, 0 < w.re → ∀ m : ℕ, w ≠ -(m : ℂ) := by
    intro w hw m h; have := congrArg Complex.re h; simp at this
    linarith [Nat.cast_nonneg (α := ℝ) m]
  have hG : DifferentiableOn ℂ Complex.Gamma {w : ℂ | 0 < w.re} := fun w hw =>
    (Complex.differentiableAt_Gamma w (hne w hw)).differentiableWithinAt
  have hG' : DifferentiableOn ℂ (deriv Complex.Gamma) {w : ℂ | 0 < w.re} :=
    hG.deriv hopen
  have hfun : Complex.digamma = fun w => deriv Complex.Gamma w / Complex.Gamma w := by
    ext w; rw [Complex.digamma_def, logDeriv_apply]
  rw [hfun]
  exact hG'.div hG fun w hw => Complex.Gamma_ne_zero (hne w hw)

/-- **CAUCHY HIGH-DERIVATIVE BOUND FOR `digamma((z + a)/2)`** on `1 < s.re ≤ 2` (`a ∈ {0, 1}`):
`‖scaledDeriv k (fun z => Complex.digamma ((z + a) / 2)) s‖ ≤ C * 2 ^ k * Real.log (|s.im| + 2)`. -/
theorem norm_scaledDeriv_digamma_half_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : ℝ), a = 0 ∨ a = 1 →
      ∀ (s : ℂ), 1 < s.re → s.re ≤ 2 → ∀ k : ℕ,
        ‖scaledDeriv k (fun z => Complex.digamma ((z + (a : ℂ)) / 2)) s‖ ≤
          C * (2 : ℝ) ^ k * Real.log (|s.im| + 2) := by
  obtain ⟨C₀, hC₀_pos, hdig⟩ := norm_digamma_wide_strip_le
  refine ⟨2 * C₀, by positivity, fun a ha s hs1 hs2 k => ?_⟩
  have hmap_re : ∀ z ∈ Metric.closedBall s (1 / 2),
      1 / 4 ≤ ((z + (a : ℂ)) / 2).re ∧ ((z + (a : ℂ)) / 2).re ≤ 2 := by
    intro z hz
    rw [Metric.mem_closedBall, dist_eq_norm] at hz
    have hre := abs_le.mp ((Complex.abs_re_le_norm (z - s)).trans hz)
    rw [Complex.sub_re] at hre
    have hwa : ((z + (a : ℂ)) / 2).re = (z.re + a) / 2 := by simp
    rw [hwa]
    rcases ha with rfl | rfl <;> exact ⟨by linarith, by linarith⟩
  have hdiff : DifferentiableOn ℂ (fun z : ℂ => Complex.digamma ((z + (a : ℂ)) / 2))
      (Metric.closedBall s (1 / 2)) := by
    refine differentiableOn_digamma_re_pos.comp
      ((differentiableOn_id.add (differentiableOn_const _)).div_const 2) ?_
    intro z hz
    show 0 < ((z + (a : ℂ)) / 2).re
    linarith [(hmap_re z hz).1]
  have hlog_ge : 0 < Real.log (|s.im| + 2) :=
    Real.log_pos (by linarith [abs_nonneg s.im])
  have hM : ∀ z ∈ Metric.sphere s (1 / 2),
      ‖Complex.digamma ((z + (a : ℂ)) / 2)‖ ≤ 2 * C₀ * Real.log (|s.im| + 2) := by
    intro z hz
    have hcb := Metric.sphere_subset_closedBall hz
    have hre := hmap_re z hcb
    have h1 := hdig ((z + (a : ℂ)) / 2) hre.1 hre.2
    rw [Metric.mem_sphere, dist_eq_norm] at hz
    have him_diff := (Complex.abs_im_le_norm (z - s)).trans_eq hz
    rw [Complex.sub_im] at him_diff
    have him_w : |((z + (a : ℂ)) / 2).im| + 2 ≤ (|s.im| + 2) ^ 2 := by
      have hwim : ((z + (a : ℂ)) / 2).im = z.im / 2 := by simp
      rw [hwim, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      have htri : |z.im| ≤ |z.im - s.im| + |s.im| := by
        simpa [sub_add_cancel] using abs_add_le (z.im - s.im) s.im
      nlinarith [abs_nonneg s.im]
    have hlog_le : Real.log (|((z + (a : ℂ)) / 2).im| + 2) ≤ 2 * Real.log (|s.im| + 2) := by
      calc Real.log (|((z + (a : ℂ)) / 2).im| + 2)
          ≤ Real.log ((|s.im| + 2) ^ 2) :=
            Real.log_le_log (by linarith [abs_nonneg ((z + (a : ℂ)) / 2).im]) him_w
        _ = 2 * Real.log (|s.im| + 2) := by rw [Real.log_pow]; norm_num
    calc ‖Complex.digamma ((z + (a : ℂ)) / 2)‖
        ≤ C₀ * Real.log (|((z + (a : ℂ)) / 2).im| + 2) := h1
      _ ≤ C₀ * (2 * Real.log (|s.im| + 2)) :=
          mul_le_mul_of_nonneg_left hlog_le hC₀_pos.le
      _ = 2 * C₀ * Real.log (|s.im| + 2) := by ring
  have hbd := norm_scaledDeriv_le_of_sphere (R := 1 / 2)
    (M := 2 * C₀ * Real.log (|s.im| + 2)) (by norm_num) (by positivity) hdiff hM k
  have hdiv : (2 * C₀ * Real.log (|s.im| + 2)) / (1 / 2 : ℝ) ^ k =
      2 * C₀ * (2 : ℝ) ^ k * Real.log (|s.im| + 2) := by
    rw [one_div, inv_pow, div_inv_eq_mul]; ring
  rwa [hdiv] at hbd

/-- Helper: geometric series bound `∑ m ∈ Finset.Icc 1 N, ((p : ℝ) ^ m) ^ (-(1 / 2 : ℝ)) ≤ 3`
for every prime `p`. -/
private lemma sum_inv_sqrt_pow_prime_le_three {p : ℕ} (hp : p.Prime) (N : ℕ) :
    ∑ m ∈ Finset.Icc 1 N, ((p : ℝ) ^ (-(1 / 2 : ℝ))) ^ m ≤ 3 := by
  set r : ℝ := (p : ℝ) ^ (-(1 / 2 : ℝ))
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hr_pos : 0 < r := Real.rpow_pos_of_pos (by linarith) _
  have hr_le : r ≤ 3 / 4 := by
    have hsq : r ^ 2 = (p : ℝ)⁻¹ := by
      dsimp only [r]
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
      norm_num
      rw [Real.rpow_neg_one]
    have hpinv : (p : ℝ)⁻¹ ≤ 1 / 2 := by
      rw [inv_eq_one_div]
      exact one_div_le_one_div_of_le (by norm_num) hp2
    nlinarith
  have htel : (1 - r) * ∑ m ∈ Finset.Icc 1 N, r ^ m = r - r ^ (N + 1) := by
    induction N with
    | zero => simp
    | succ N ih =>
      have hIcc : Finset.Icc 1 (N + 1) = insert (N + 1) (Finset.Icc 1 N) := by
        ext m; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      rw [hIcc, Finset.sum_insert (by simp), mul_add, ih, pow_succ]
      ring
  have hle : (1 - r) * ∑ m ∈ Finset.Icc 1 N, r ^ m ≤ r := by
    rw [htel]; linarith [pow_nonneg hr_pos.le (N + 1)]
  nlinarith

/-- **DIRECT EULER-FACTOR HIGH-DERIVATIVE BOUND (`0` ASSUMPTIONS!)**:
for EVERY `q ≥ 1` (`[NeZero q]`), EVERY character `χ : DirichletCharacter ℂ q`,
EVERY `s : ℂ` with `1 < s.re`, and EVERY `k : ℕ`:
`‖scaledDeriv k (fun z => negLogDerivL χ z - negLogDerivL χ.primitiveCharacter z) s‖ ≤ 3 * 2 ^ k * Real.log q`. -/
theorem norm_scaledDeriv_euler_diff_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1 < s.re) (k : ℕ) :
    haveI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
    ‖scaledDeriv k (fun z => negLogDerivL χ z - negLogDerivL χ.primitiveCharacter z) s‖ ≤
      3 * (2 : ℝ) ^ k * Real.log (q : ℝ) := by
  classical
  have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  set ψ : DirichletCharacter ℂ χ.conductor := χ.primitiveCharacter
  let a : ℕ → ℂ := fun n => (χ n - ψ n) * (Λ n : ℂ)
  have hconv : ∀ x : ℝ, 1 < x → LSeriesSummable a (x : ℂ) := by
    intro x hx
    have hx' : 1 < (x : ℂ).re := by simpa using hx
    have hχ : LSeriesSummable (fun n => χ n * (Λ n : ℂ)) (x : ℂ) :=
      χ.LSeriesSummable_twist_vonMangoldt hx'
    have hψ : LSeriesSummable (fun n => ψ n * (Λ n : ℂ)) (x : ℂ) :=
      ψ.LSeriesSummable_twist_vonMangoldt hx'
    refine (hχ.sub hψ).congr fun n => ?_
    rcases eq_or_ne n 0 with rfl | hn
    · simp [LSeries.term_zero]
    · simp only [LSeries.term_of_ne_zero hn, a, Pi.sub_apply]; ring
  have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hev : (fun z => negLogDerivL χ z - negLogDerivL ψ z) =ᶠ[𝓝 s] LSeries a := by
    filter_upwards [hopen.mem_nhds hs] with z (hz : 1 < z.re)
    rw [negLogDerivL_eq_LSeries χ hz, negLogDerivL_eq_LSeries ψ hz]
    have hχ : LSeriesSummable (fun n => χ n * (Λ n : ℂ)) z :=
      χ.LSeriesSummable_twist_vonMangoldt hz
    have hψ : LSeriesSummable (fun n => ψ n * (Λ n : ℂ)) z :=
      ψ.LSeriesSummable_twist_vonMangoldt hz
    unfold LSeries
    rw [← Summable.tsum_sub hχ hψ]
    refine tsum_congr fun n => ?_
    rcases eq_or_ne n 0 with rfl | hn
    · simp [LSeries.term_zero]
    · simp only [LSeries.term_of_ne_zero hn, a]; ring
  rw [scaledDeriv_congr_nhds hev, scaledDeriv_LSeries_eq hconv hs k]
  have hsum := summable_scaledDeriv_LSeries hconv hs k
  refine (norm_tsum_le_tsum_norm hsum.norm).trans ?_
  refine Summable.tsum_le_of_sum_range_le hsum.norm fun N => ?_
  -- Pointwise bound: vanishes if `Coprime n q` or `¬ IsPrimePow n`; otherwise `≤ 2^k * Λ n / √n`!
  have hterm : ∀ n : ℕ,
      ‖if n = 0 then (0 : ℂ)
        else a n * ((((Real.log (n : ℝ)) ^ k / (k.factorial : ℝ) : ℝ) : ℂ)) / (n : ℂ) ^ s‖ ≤
        if ¬ Nat.Coprime n q ∧ IsPrimePow n then
          (2 : ℝ) ^ k * Λ n * (n : ℝ) ^ (-(1 / 2 : ℝ))
        else 0 := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · rw [if_neg hn]
      by_cases hcop : Nat.Coprime n q
      · have hu : IsUnit (n : ZMod q) := (ZMod.isUnit_iff_coprime n q).mpr hcop
        have hχ_eq : χ (n : ZMod q) = ψ (n : ZMod χ.conductor) := by
          obtain ⟨u, hu_eq⟩ := hu
          conv_lhs => rw [← χ.changeLevel_primitiveCharacter]
          rw [← hu_eq, DirichletCharacter.changeLevel_eq_cast_of_dvd χ.primitiveCharacter
            χ.conductor_dvd_level u, hu_eq, ZMod.cast_natCast χ.conductor_dvd_level]
        simp [a, hχ_eq, hcop]
      · by_cases hpp : IsPrimePow n
        · rw [if_pos ⟨hcop, hpp⟩]
          have hnu : ¬ IsUnit (n : ZMod q) := fun hu => hcop ((ZMod.isUnit_iff_coprime n q).mp hu)
          have hχ0 : χ (n : ZMod q) = 0 := MulChar.map_nonunit _ hnu
          have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
          have hn_ge1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
          have hlog_nn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn_ge1
          have hexp : ((1 / 2 : ℝ) * Real.log (n : ℝ)) ^ k / (k.factorial : ℝ) ≤
              Real.exp ((1 / 2 : ℝ) * Real.log (n : ℝ)) := by
            have h1 := Real.sum_le_exp_of_nonneg (x := (1 / 2 : ℝ) * Real.log (n : ℝ))
              (by positivity) (k + 1)
            exact (Finset.single_le_sum
              (f := fun j : ℕ => ((1 / 2 : ℝ) * Real.log (n : ℝ)) ^ j / (j.factorial : ℝ))
              (fun j _ => by positivity) (Finset.mem_range.mpr (Nat.lt_succ_self k))).trans h1
          have hlog_pow : (Real.log (n : ℝ)) ^ k / (k.factorial : ℝ) ≤
              (2 : ℝ) ^ k * (n : ℝ) ^ (1 / 2 : ℝ) := by
            have hrexp : Real.exp ((1 / 2 : ℝ) * Real.log (n : ℝ)) = (n : ℝ) ^ (1 / 2 : ℝ) := by
              rw [Real.rpow_def_of_pos hn_pos, mul_comm]
            have hhalf_pow : (1 / 2 : ℝ) ^ k = ((2 : ℝ) ^ k)⁻¹ := by rw [one_div, inv_pow]
            rw [hrexp, mul_pow, hhalf_pow, mul_div_assoc] at hexp
            have h2k : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
            have hmul := mul_le_mul_of_nonneg_left hexp h2k.le
            calc (Real.log (n : ℝ)) ^ k / (k.factorial : ℝ)
                = (2 : ℝ) ^ k * (((2 : ℝ) ^ k)⁻¹ * ((Real.log (n : ℝ)) ^ k / (k.factorial : ℝ))) := by
                  field_simp [h2k.ne']
              _ ≤ (2 : ℝ) ^ k * (n : ℝ) ^ (1 / 2 : ℝ) := hmul
          have hns_ge : (n : ℝ) ^ (1 : ℝ) ≤ (n : ℝ) ^ s.re :=
            Real.rpow_le_rpow_of_exponent_le hn_ge1 hs.le
          rw [Real.rpow_one] at hns_ge
          have hnorm_a : ‖a n‖ ≤ Λ n := by
            dsimp only [a]
            rw [hχ0, zero_sub, norm_mul, norm_neg, Complex.norm_real,
              Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
            nlinarith [ψ.norm_le_one (n : ZMod χ.conductor),
              ArithmeticFunction.vonMangoldt_nonneg (n := n)]
          rw [norm_div, norm_mul, Complex.norm_real,
            Real.norm_of_nonneg (by positivity),
            Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn)]
          have hrpow_div : (n : ℝ) ^ (1 / 2 : ℝ) / (n : ℝ) ^ s.re ≤ (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
            have h1 : (n : ℝ) ^ (1 / 2 : ℝ) / (n : ℝ) = (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
              rw [div_eq_mul_inv, ← Real.rpow_neg_one (n : ℝ), ← Real.rpow_add hn_pos]
              norm_num
            rw [← h1]
            exact div_le_div_of_nonneg_left (by positivity) hn_pos hns_ge
          calc ‖a n‖ * ((Real.log (n : ℝ)) ^ k / (k.factorial : ℝ)) / (n : ℝ) ^ s.re
              ≤ Λ n * ((2 : ℝ) ^ k * (n : ℝ) ^ (1 / 2 : ℝ)) / (n : ℝ) ^ s.re := by
                gcongr
            _ = (2 : ℝ) ^ k * Λ n * ((n : ℝ) ^ (1 / 2 : ℝ) / (n : ℝ) ^ s.re) := by ring
            _ ≤ (2 : ℝ) ^ k * Λ n * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
                gcongr
        · have h0 : Λ n = 0 := ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hpp
          simp [a, hpp, h0]
  have hsub :
      (Finset.range N).filter (fun n => ¬ Nat.Coprime n q ∧ IsPrimePow n) ⊆
        q.primeFactors.biUnion (fun p => (Finset.Icc 1 N).image (fun m => p ^ m)) := by
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_biUnion, Finset.mem_image,
      Finset.mem_Icc] at hn ⊢
    obtain ⟨hnN, hncop, hpp⟩ := hn
    obtain ⟨p, m, hp, hmpos, rfl⟩ := (isPrimePow_nat_iff n).mp hpp
    have hpq : p ∣ q := by
      by_contra hndvd
      exact hncop ((hp.coprime_iff_not_dvd.mpr hndvd).pow_left m)
    have hm_le : m ≤ N := (le_of_lt (Nat.lt_pow_self hp.one_lt)).trans hnN.le
    exact ⟨p, Nat.mem_primeFactors.mpr ⟨hp, hpq, (NeZero.pos q).ne'⟩, m, ⟨hmpos, hm_le⟩, rfl⟩
  have hterm_nn : ∀ n : ℕ, 0 ≤ (2 : ℝ) ^ k * Λ n * (n : ℝ) ^ (-(1 / 2 : ℝ)) := fun n =>
    mul_nonneg (mul_nonneg (by positivity) ArithmeticFunction.vonMangoldt_nonneg)
      (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  have hbiUnion_le : ∀ (s : Finset ℕ) (t : ℕ → Finset ℕ) (f : ℕ → ℝ), (∀ b, 0 ≤ f b) →
      ∑ b ∈ s.biUnion t, f b ≤ ∑ a ∈ s, ∑ b ∈ t a, f b := by
    intro s t f hf
    induction s using Finset.induction_on with
    | empty => simp
    | insert x s hx ih =>
      rw [Finset.biUnion_insert, Finset.sum_insert hx]
      have hu : ∑ b ∈ t x ∪ s.biUnion t, f b ≤ ∑ b ∈ t x, f b + ∑ b ∈ s.biUnion t, f b := by
        rw [← Finset.sum_union_inter]
        linarith [Finset.sum_nonneg (s := t x ∩ s.biUnion t) (f := f) fun b _ => hf b]
      linarith
  have hper_prime : ∀ p ∈ q.primeFactors,
      ∑ n ∈ (Finset.Icc 1 N).image (fun m => p ^ m),
          (2 : ℝ) ^ k * Λ n * (n : ℝ) ^ (-(1 / 2 : ℝ)) ≤
        3 * (2 : ℝ) ^ k * Real.log (p : ℝ) := by
    intro p hp
    have hpr : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hp_pos : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr hpr.pos
    calc ∑ n ∈ (Finset.Icc 1 N).image (fun m => p ^ m),
            (2 : ℝ) ^ k * Λ n * (n : ℝ) ^ (-(1 / 2 : ℝ))
        ≤ ∑ m ∈ Finset.Icc 1 N,
            (2 : ℝ) ^ k * Λ (p ^ m) * ((p ^ m : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) :=
          Finset.sum_image_le_of_nonneg fun _ _ => hterm_nn _
      _ = (2 : ℝ) ^ k * Real.log (p : ℝ) *
            ∑ m ∈ Finset.Icc 1 N, ((p : ℝ) ^ (-(1 / 2 : ℝ))) ^ m := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun m hm => ?_
          have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
          rw [ArithmeticFunction.vonMangoldt_apply_pow (by omega),
            ArithmeticFunction.vonMangoldt_apply_prime hpr, Nat.cast_pow,
            ← Real.rpow_natCast (p : ℝ) m, ← Real.rpow_mul hp_pos.le,
            ← Real.rpow_natCast ((p : ℝ) ^ (-(1 / 2 : ℝ))) m,
            ← Real.rpow_mul hp_pos.le, mul_comm (m : ℝ)]
      _ ≤ (2 : ℝ) ^ k * Real.log (p : ℝ) * 3 :=
          mul_le_mul_of_nonneg_left (sum_inv_sqrt_pow_prime_le_three hpr N)
            (mul_nonneg (by positivity) (Real.log_natCast_nonneg p))
      _ = 3 * (2 : ℝ) ^ k * Real.log (p : ℝ) := by ring
  have hsum_log : ∑ p ∈ q.primeFactors, Real.log (p : ℝ) ≤ Real.log (q : ℝ) := by
    rw [← Real.log_prod fun p hp => Nat.cast_ne_zero.mpr (Nat.prime_of_mem_primeFactors hp).ne_zero,
      ← Nat.cast_prod]
    have hprod_pos : (0 : ℝ) < ((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) := by
      exact_mod_cast Finset.prod_pos fun p hp => (Nat.prime_of_mem_primeFactors hp).pos
    have hprod_le : ((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) ≤ (q : ℝ) := by
      exact_mod_cast Nat.le_of_dvd (NeZero.pos q) (Nat.prod_primeFactors_dvd q)
    exact Real.log_le_log hprod_pos hprod_le
  calc ∑ n ∈ Finset.range N,
          ‖if n = 0 then (0 : ℂ)
            else a n * ((((Real.log (n : ℝ)) ^ k / (k.factorial : ℝ) : ℝ) : ℂ)) / (n : ℂ) ^ s‖
      ≤ ∑ n ∈ (Finset.range N).filter (fun n => ¬ Nat.Coprime n q ∧ IsPrimePow n),
          (2 : ℝ) ^ k * Λ n * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
        rw [Finset.sum_filter]
        exact Finset.sum_le_sum fun n _ => hterm n
    _ ≤ ∑ n ∈ q.primeFactors.biUnion (fun p => (Finset.Icc 1 N).image (fun m => p ^ m)),
          (2 : ℝ) ^ k * Λ n * (n : ℝ) ^ (-(1 / 2 : ℝ)) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => hterm_nn _
    _ ≤ ∑ p ∈ q.primeFactors,
          ∑ n ∈ (Finset.Icc 1 N).image (fun m => p ^ m),
            (2 : ℝ) ^ k * Λ n * (n : ℝ) ^ (-(1 / 2 : ℝ)) :=
        hbiUnion_le _ _ _ hterm_nn
    _ ≤ ∑ p ∈ q.primeFactors, 3 * (2 : ℝ) ^ k * Real.log (p : ℝ) :=
        Finset.sum_le_sum hper_prime
    _ = 3 * (2 : ℝ) ^ k * ∑ p ∈ q.primeFactors, Real.log (p : ℝ) := (Finset.mul_sum _ _ _).symm
    _ ≤ 3 * (2 : ℝ) ^ k * Real.log (q : ℝ) :=
        mul_le_mul_of_nonneg_left hsum_log (by positivity)

/-- Summability of `1 / (s - ρ n) ^ (k + 1)` for `k ≥ 1`, `1 < s.re`, and any critical-strip
sequence with `∑ (‖ρ n‖ ^ 2)⁻¹ < ∞`. -/
lemma summable_inv_sub_pow_of_strip {ρ : ℕ → ℂ}
    (hstrip : ∀ n, 0 < (ρ n).re ∧ (ρ n).re < 1)
    (hsum : Summable (fun n : ℕ => (‖ρ n‖ ^ 2)⁻¹))
    {s : ℂ} (hs : 1 < s.re) {k : ℕ} (hk : 1 ≤ k) :
    Summable (fun n : ℕ => (1 : ℂ) / (s - ρ n) ^ (k + 1)) := by
  have hnorm_pos : ∀ n : ℕ, s.re - 1 ≤ ‖s - ρ n‖ := fun n => by
    have hre := (le_abs_self (s - ρ n).re).trans (Complex.abs_re_le_norm (s - ρ n))
    rw [Complex.sub_re] at hre
    linarith [(hstrip n).2]
  have hne_zero : ∀ n : ℕ, 0 < ‖ρ n‖ := fun n => by
    have hre := (le_abs_self (ρ n).re).trans (Complex.abs_re_le_norm (ρ n))
    linarith [(hstrip n).1]
  have htend : Tendsto (fun n : ℕ => (‖ρ n‖ ^ 2)⁻¹) atTop (𝓝 0) := hsum.tendsto_atTop_zero
  have hbig : ∀ᶠ n in atTop, 2 * ‖s‖ ≤ ‖ρ n‖ := by
    have hpos : (0 : ℝ) < ((2 * ‖s‖ + 1) ^ 2)⁻¹ := by positivity
    filter_upwards [htend.eventually (gt_mem_nhds hpos)] with n hn
    by_contra hlt; push Not at hlt
    have hsq : ‖ρ n‖ ^ 2 ≤ (2 * ‖s‖ + 1) ^ 2 := by nlinarith [norm_nonneg (ρ n), norm_nonneg s]
    have hinv : ((2 * ‖s‖ + 1) ^ 2)⁻¹ ≤ (‖ρ n‖ ^ 2)⁻¹ :=
      inv_anti₀ (sq_pos_of_pos (hne_zero n)) hsq
    linarith
  have hC : ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ‖(1 : ℂ) / (s - ρ n) ^ (k + 1)‖ ≤ C * (‖ρ n‖ ^ 2)⁻¹ := by
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hbig
    set r : ℝ := s.re - 1
    have hr_pos : 0 < r := by linarith
    let C_fin : ℝ := ∑ n ∈ Finset.range N, ‖ρ n‖ ^ 2 / r ^ (k + 1)
    refine ⟨max C_fin (4 / r ^ (k - 1)), by positivity, fun n => ?_⟩
    rw [norm_div, norm_one, norm_pow]
    by_cases hnN : n < N
    · have h1 : 1 / ‖s - ρ n‖ ^ (k + 1) ≤ 1 / r ^ (k + 1) :=
        one_div_le_one_div_of_le (pow_pos hr_pos _) (pow_le_pow_left₀ hr_pos.le (hnorm_pos n) _)
      have hle_fin : ‖ρ n‖ ^ 2 / r ^ (k + 1) ≤ C_fin :=
        Finset.single_le_sum (f := fun m => ‖ρ m‖ ^ 2 / r ^ (k + 1))
          (fun _ _ => by positivity) (Finset.mem_range.mpr hnN)
      have hρ2_pos : 0 < ‖ρ n‖ ^ 2 := sq_pos_of_pos (hne_zero n)
      calc 1 / ‖s - ρ n‖ ^ (k + 1)
          ≤ 1 / r ^ (k + 1) := h1
        _ = (‖ρ n‖ ^ 2 / r ^ (k + 1)) * (‖ρ n‖ ^ 2)⁻¹ := by
            field_simp [(hne_zero n).ne']
        _ ≤ C_fin * (‖ρ n‖ ^ 2)⁻¹ :=
            mul_le_mul_of_nonneg_right hle_fin (by positivity)
        _ ≤ max C_fin (4 / r ^ (k - 1)) * (‖ρ n‖ ^ 2)⁻¹ :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    · push Not at hnN
      have h2s : 2 * ‖s‖ ≤ ‖ρ n‖ := hN n hnN
      have hsub_ge : ‖ρ n‖ / 2 ≤ ‖s - ρ n‖ := by
        have htri : ‖ρ n‖ ≤ ‖s - ρ n‖ + ‖s‖ := by
          have : ρ n = -(s - ρ n) + s := by ring
          calc ‖ρ n‖ = ‖-(s - ρ n) + s‖ := congrArg norm this
            _ ≤ ‖-(s - ρ n)‖ + ‖s‖ := norm_add_le _ _
            _ = ‖s - ρ n‖ + ‖s‖ := by rw [norm_neg]
        linarith
      have hpow_split : ‖s - ρ n‖ ^ (k + 1) = ‖s - ρ n‖ ^ 2 * ‖s - ρ n‖ ^ (k - 1) := by
        rw [← pow_add]; congr 1; omega
      have hsq_ge : (‖ρ n‖ / 2) ^ 2 ≤ ‖s - ρ n‖ ^ 2 :=
        pow_le_pow_left₀ (by positivity) hsub_ge 2
      have hrem_ge : r ^ (k - 1) ≤ ‖s - ρ n‖ ^ (k - 1) :=
        pow_le_pow_left₀ hr_pos.le (hnorm_pos n) _
      have hden_ge : (‖ρ n‖ / 2) ^ 2 * r ^ (k - 1) ≤ ‖s - ρ n‖ ^ (k + 1) := by
        rw [hpow_split]
        exact mul_le_mul hsq_ge hrem_ge (by positivity) (by positivity)
      have hden_pos : 0 < (‖ρ n‖ / 2) ^ 2 * r ^ (k - 1) :=
        mul_pos (sq_pos_of_pos (by linarith [hne_zero n])) (pow_pos hr_pos _)
      calc 1 / ‖s - ρ n‖ ^ (k + 1)
          ≤ 1 / ((‖ρ n‖ / 2) ^ 2 * r ^ (k - 1)) := one_div_le_one_div_of_le hden_pos hden_ge
        _ = (4 / r ^ (k - 1)) * (‖ρ n‖ ^ 2)⁻¹ := by
            have hρ2_ne : ‖ρ n‖ ^ 2 ≠ 0 := (sq_pos_of_pos (hne_zero n)).ne'
            have hr_ne : r ^ (k - 1) ≠ 0 := (pow_pos hr_pos _).ne'
            field_simp [hρ2_ne, hr_ne]
            ring
        _ ≤ max C_fin (4 / r ^ (k - 1)) * (‖ρ n‖ ^ 2)⁻¹ :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
  obtain ⟨C, _, hCbd⟩ := hC
  exact Summable.of_norm_bounded (hsum.mul_left C) hCbd

/-- **EXACT TERM-BY-TERM `k`-TH DERIVATIVE OF THE HADAMARD ZERO SUM (`k ≥ 1`)**:
for any critical-strip zero sequence `ρ` with `∑ (‖ρ n‖^2)⁻¹ < ∞`, any `s : ℂ` with `1 < s.re`,
and any `k ≥ 1`:
`scaledDeriv k (fun z => ∑' n, (1 / (z - ρ n) + 1 / ρ n)) s = ∑' n, 1 / (s - ρ n) ^ (k + 1)`. -/
theorem scaledDeriv_hadamard_tsum_eq {ρ : ℕ → ℂ}
    (hstrip : ∀ n, 0 < (ρ n).re ∧ (ρ n).re < 1)
    (hsum : Summable (fun n : ℕ => (‖ρ n‖ ^ 2)⁻¹))
    {s : ℂ} (hs : 1 < s.re) {k : ℕ} (hk : 1 ≤ k) :
    scaledDeriv k (fun z : ℂ => ∑' n : ℕ, (1 / (z - ρ n) + 1 / ρ n)) s =
      ∑' n : ℕ, (1 : ℂ) / (s - ρ n) ^ (k + 1) := by
  set r : ℝ := (s.re - 1) / 2
  have hr_pos : 0 < r := by dsimp only [r]; linarith
  have hcb_re : ∀ z ∈ Metric.closedBall s r, 1 + r ≤ z.re := by
    intro z hz
    rw [Metric.mem_closedBall, dist_eq_norm] at hz
    have hre := abs_le.mp ((Complex.abs_re_le_norm (z - s)).trans hz)
    rw [Complex.sub_re] at hre
    dsimp only [r] at *; linarith
  have hcb_dist : ∀ z ∈ Metric.closedBall s r, ∀ n : ℕ, r ≤ ‖z - ρ n‖ := by
    intro z hz n
    have hre := (le_abs_self (z - ρ n).re).trans (Complex.abs_re_le_norm (z - ρ n))
    rw [Complex.sub_re] at hre
    linarith [hcb_re z hz, (hstrip n).2]
  have hne_zero : ∀ n : ℕ, 0 < ‖ρ n‖ := fun n => by
    have hre := (le_abs_self (ρ n).re).trans (Complex.abs_re_le_norm (ρ n))
    linarith [(hstrip n).1]
  -- Uniform M-test on `closedBall s r`
  set M_z : ℝ := ‖s‖ + r
  have hcb_norm : ∀ z ∈ Metric.closedBall s r, ‖z‖ ≤ M_z := by
    intro z hz
    rw [Metric.mem_closedBall, dist_eq_norm] at hz
    have htri : ‖z‖ ≤ ‖z - s‖ + ‖s‖ := by simpa [sub_add_cancel] using norm_add_le (z - s) s
    dsimp only [M_z]; linarith
  have hterm_M : ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ∀ z ∈ Metric.closedBall s r,
      ‖(1 : ℂ) / (z - ρ n) + 1 / ρ n‖ ≤ C * (‖ρ n‖ ^ 2)⁻¹ := by
    have htend : Tendsto (fun n : ℕ => (‖ρ n‖ ^ 2)⁻¹) atTop (𝓝 0) := hsum.tendsto_atTop_zero
    have hbig : ∀ᶠ n in atTop, 2 * M_z ≤ ‖ρ n‖ := by
      have hpos : (0 : ℝ) < ((2 * M_z + 1) ^ 2)⁻¹ := by positivity
      filter_upwards [htend.eventually (gt_mem_nhds hpos)] with n hn
      by_contra hlt; push Not at hlt
      have hsq : ‖ρ n‖ ^ 2 ≤ (2 * M_z + 1) ^ 2 := by
        nlinarith [norm_nonneg (ρ n), norm_nonneg s]
      have hinv : ((2 * M_z + 1) ^ 2)⁻¹ ≤ (‖ρ n‖ ^ 2)⁻¹ :=
        inv_anti₀ (sq_pos_of_pos (hne_zero n)) hsq
      linarith
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hbig
    let C_fin : ℝ := ∑ n ∈ Finset.range N, ‖ρ n‖ * M_z / r
    refine ⟨max C_fin (2 * M_z), by positivity, fun n z hz => ?_⟩
    have hzn : z - ρ n ≠ 0 := by
      intro h0; have := hcb_dist z hz n; rw [h0, norm_zero] at this; linarith
    have hρn : ρ n ≠ 0 := norm_pos_iff.mp (hne_zero n)
    have hcomb : (1 : ℂ) / (z - ρ n) + 1 / ρ n = z / ((z - ρ n) * ρ n) := by
      field_simp [hzn, hρn]
      ring
    rw [hcomb, norm_div, norm_mul]
    by_cases hnN : n < N
    · have hle_fin : ‖ρ n‖ * M_z / r ≤ C_fin :=
        Finset.single_le_sum (f := fun m => ‖ρ m‖ * M_z / r)
          (fun _ _ => by positivity) (Finset.mem_range.mpr hnN)
      have hden_ge : r * ‖ρ n‖ ≤ ‖z - ρ n‖ * ‖ρ n‖ :=
        mul_le_mul_of_nonneg_right (hcb_dist z hz n) (norm_nonneg _)
      have hden_pos : 0 < r * ‖ρ n‖ := mul_pos hr_pos (hne_zero n)
      calc ‖z‖ / (‖z - ρ n‖ * ‖ρ n‖)
          ≤ M_z / (r * ‖ρ n‖) :=
            div_le_div₀ (by positivity) (hcb_norm z hz) hden_pos hden_ge
        _ = (‖ρ n‖ * M_z / r) * (‖ρ n‖ ^ 2)⁻¹ := by
            have hρ_ne : ‖ρ n‖ ≠ 0 := (hne_zero n).ne'
            field_simp [hr_pos.ne', hρ_ne]
        _ ≤ C_fin * (‖ρ n‖ ^ 2)⁻¹ := mul_le_mul_of_nonneg_right hle_fin (by positivity)
        _ ≤ max C_fin (2 * M_z) * (‖ρ n‖ ^ 2)⁻¹ :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    · push Not at hnN
      have h2M : 2 * M_z ≤ ‖ρ n‖ := hN n hnN
      have hsub_ge : ‖ρ n‖ / 2 ≤ ‖z - ρ n‖ := by
        have htri : ‖ρ n‖ ≤ ‖z - ρ n‖ + ‖z‖ := by
          have : ρ n = -(z - ρ n) + z := by ring
          calc ‖ρ n‖ = ‖-(z - ρ n) + z‖ := congrArg norm this
            _ ≤ ‖-(z - ρ n)‖ + ‖z‖ := norm_add_le _ _
            _ = ‖z - ρ n‖ + ‖z‖ := by rw [norm_neg]
        linarith [hcb_norm z hz]
      have hden_ge : ‖ρ n‖ ^ 2 / 2 ≤ ‖z - ρ n‖ * ‖ρ n‖ := by
        have := mul_le_mul_of_nonneg_right hsub_ge (norm_nonneg (ρ n))
        linarith [show ‖ρ n‖ / 2 * ‖ρ n‖ = ‖ρ n‖ ^ 2 / 2 by ring]
      have hden_pos : 0 < ‖ρ n‖ ^ 2 / 2 := by positivity
      calc ‖z‖ / (‖z - ρ n‖ * ‖ρ n‖)
          ≤ M_z / (‖ρ n‖ ^ 2 / 2) :=
            div_le_div₀ (by positivity) (hcb_norm z hz) hden_pos hden_ge
        _ = (2 * M_z) * (‖ρ n‖ ^ 2)⁻¹ := by
            have hρ2_ne : ‖ρ n‖ ^ 2 ≠ 0 := (sq_pos_of_pos (hne_zero n)).ne'
            field_simp [hρ2_ne]
        _ ≤ max C_fin (2 * M_z) * (‖ρ n‖ ^ 2)⁻¹ :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
  obtain ⟨C, hC_nn, hCbd⟩ := hterm_M
  let F : ℂ → ℂ := fun z => ∑' n : ℕ, ((1 : ℂ) / (z - ρ n) + 1 / ρ n)
  let F_N : ℕ → ℂ → ℂ := fun N z => ∑ n ∈ Finset.range N, ((1 : ℂ) / (z - ρ n) + 1 / ρ n)
  -- Each `F_N` is holomorphic on `closedBall s r`, and `F_N → F` uniformly on `closedBall s r`!
  have hFN_diff : ∀ N : ℕ, DifferentiableOn ℂ (F_N N) (Metric.closedBall s r) := by
    intro N
    refine DifferentiableOn.fun_sum fun n _ => ?_
    refine DifferentiableOn.add ?_ (differentiableOn_const _)
    refine (differentiableOn_const _).div (differentiableOn_id.sub (differentiableOn_const _)) ?_
    intro z hz h0
    have := hcb_dist z hz n; rw [h0, norm_zero] at this; linarith
  have hF_unif : TendstoUniformlyOn F_N F atTop (Metric.closedBall s r) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have htail : Tendsto (fun N : ℕ => ∑' n : ℕ, C * (‖ρ (n + N)‖ ^ 2)⁻¹) atTop (𝓝 0) :=
      tendsto_sum_nat_add (fun n => C * (‖ρ n‖ ^ 2)⁻¹) |> fun _ =>
        by
          have h1 := (hsum.mul_left C).hasSum.tendsto_sum_nat
          have h2 : Tendsto (fun N : ℕ => (∑' n, C * (‖ρ n‖ ^ 2)⁻¹) -
              ∑ n ∈ Finset.range N, C * (‖ρ n‖ ^ 2)⁻¹) atTop (𝓝 0) := by
            have h3 := (tendsto_const_nhds (x := ∑' n, C * (‖ρ n‖ ^ 2)⁻¹)).sub h1
            rwa [sub_self] at h3
          refine h2.congr fun N => ?_
          rw [← (hsum.mul_left C).sum_add_tsum_nat_add N]
          ring
    filter_upwards [htail.eventually (gt_mem_nhds hε)] with N hN z hz
    rw [dist_eq_norm, norm_sub_rev]
    have hsum_z : Summable (fun n : ℕ => (1 : ℂ) / (z - ρ n) + 1 / ρ n) :=
      Summable.of_norm_bounded (hsum.mul_left C) fun n => hCbd n z hz
    have hsub_eq : F_N N z - F z = -∑' n : ℕ, ((1 : ℂ) / (z - ρ (n + N)) + 1 / ρ (n + N)) := by
      dsimp only [F, F_N]
      rw [← hsum_z.sum_add_tsum_nat_add N]
      ring
    rw [hsub_eq, norm_neg]
    have hsum_shift : Summable (fun n : ℕ => (1 : ℂ) / (z - ρ (n + N)) + 1 / ρ (n + N)) :=
      (summable_nat_add_iff N).mpr hsum_z
    have hbound_shift : Summable (fun n : ℕ => C * (‖ρ (n + N)‖ ^ 2)⁻¹) :=
      (summable_nat_add_iff N).mpr (hsum.mul_left C)
    calc ‖∑' n : ℕ, ((1 : ℂ) / (z - ρ (n + N)) + 1 / ρ (n + N))‖
        ≤ ∑' n : ℕ, ‖(1 : ℂ) / (z - ρ (n + N)) + 1 / ρ (n + N)‖ :=
          norm_tsum_le_tsum_norm hsum_shift.norm
      _ ≤ ∑' n : ℕ, C * (‖ρ (n + N)‖ ^ 2)⁻¹ :=
          hsum_shift.norm.tsum_le_tsum (fun n => hCbd (n + N) z hz) hbound_shift
      _ < ε := hN
  -- Holomorphicity of `F` on `closedBall s (r / 2)` (via uniform limit on `ball s r`)
  have hF_diff_ball : DifferentiableOn ℂ F (Metric.ball s r) :=
    (hF_unif.mono Metric.ball_subset_closedBall).tendstoLocallyUniformlyOn.differentiableOn
      (Eventually.of_forall fun N => (hFN_diff N).mono Metric.ball_subset_closedBall)
      Metric.isOpen_ball
  have hF_diff_half : DifferentiableOn ℂ F (Metric.closedBall s (r / 2)) :=
    hF_diff_ball.mono (Metric.closedBall_subset_ball (by linarith))
  -- Compute `scaledDeriv k (F_N N) s`
  have hFN_sd : ∀ N : ℕ, scaledDeriv k (F_N N) s =
      ∑ n ∈ Finset.range N, (1 : ℂ) / (s - ρ n) ^ (k + 1) := by
    intro N
    have hterm_cd : ∀ n : ℕ, ContDiffAt ℂ k (fun z : ℂ => (1 : ℂ) / (z - ρ n) + 1 / ρ n) s := by
      intro n
      have hne : s - ρ n ≠ 0 := by
        intro h0; have := hcb_dist s (Metric.mem_closedBall_self hr_pos.le) n
        rw [h0, norm_zero] at this; linarith
      have h1 : ContDiffAt ℂ k (fun z : ℂ => (z - ρ n)⁻¹) s :=
        (contDiffAt_id.sub contDiffAt_const).inv hne
      have hfun : (fun z : ℂ => (1 : ℂ) / (z - ρ n) + 1 / ρ n) =
          fun z : ℂ => (z - ρ n)⁻¹ + 1 / ρ n := by
        ext z; rw [one_div]
      rw [hfun]
      exact h1.add contDiffAt_const
    unfold scaledDeriv F_N
    rw [iteratedDeriv_fun_sum (fun n _ => hterm_cd n), Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    change scaledDeriv k (fun z : ℂ => (1 : ℂ) / (z - ρ n) + 1 / ρ n) s = _
    have hne : s ≠ ρ n := by
      intro h0; have := hcb_dist s (Metric.mem_closedBall_self hr_pos.le) n
      rw [h0, sub_self, norm_zero] at this; linarith
    have h1 : ContDiffAt ℂ k (fun z : ℂ => (1 : ℂ) / (z - ρ n)) s := by
      have hfun : (fun z : ℂ => (1 : ℂ) / (z - ρ n)) = fun z : ℂ => (z - ρ n)⁻¹ := by
        ext z; rw [one_div]
      rw [hfun]
      exact (contDiffAt_id.sub contDiffAt_const).inv (sub_ne_zero.mpr hne)
    rw [scaledDeriv_add h1 contDiffAt_const, scaledDeriv_inv_sub (ρ n) k hne,
      scaledDeriv_const_eq_zero hk, add_zero]
  -- Cauchy bound: `scaledDeriv k (F_N N) s → scaledDeriv k F s`!
  have htend_sd : Tendsto (fun N : ℕ => scaledDeriv k (F_N N) s) atTop (𝓝 (scaledDeriv k F s)) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    have hr2_pos : 0 < r / 2 := by positivity
    have hδ_pos : 0 < ε * (r / 2) ^ k / 2 := by positivity
    rw [Metric.tendstoUniformlyOn_iff] at hF_unif
    obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp (hF_unif (ε * (r / 2) ^ k / 2) hδ_pos)
    refine ⟨N₀, fun N hN => ?_⟩
    rw [dist_eq_norm, norm_sub_rev]
    have hF_cd : ContDiffAt ℂ k F s :=
      (hF_diff_ball.analyticAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr_pos))).contDiffAt.of_le le_top
    have hFN_cd : ContDiffAt ℂ k (F_N N) s :=
      (((hFN_diff N).mono Metric.ball_subset_closedBall).analyticAt
        (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr_pos))).contDiffAt.of_le le_top
    have hsub_sd : scaledDeriv k F s - scaledDeriv k (F_N N) s =
        scaledDeriv k (fun z => F z - F_N N z) s :=
      (scaledDeriv_sub hF_cd hFN_cd).symm
    rw [hsub_sd]
    have hdiff_sub : DifferentiableOn ℂ (fun z => F z - F_N N z) (Metric.closedBall s (r / 2)) :=
      hF_diff_half.sub ((hFN_diff N).mono (Metric.closedBall_subset_closedBall (by linarith)))
    have hbd_sub : ∀ z ∈ Metric.sphere s (r / 2), ‖F z - F_N N z‖ ≤ ε * (r / 2) ^ k / 2 := by
      intro z hz
      have hcb : z ∈ Metric.closedBall s r :=
        Metric.closedBall_subset_closedBall (by linarith) (Metric.sphere_subset_closedBall hz)
      have h1 := hN₀ N hN z hcb
      rw [dist_eq_norm] at h1
      exact h1.le
    have hcauchy := norm_scaledDeriv_le_of_sphere hr2_pos hδ_pos.le hdiff_sub hbd_sub k
    have hsimp : ε * (r / 2) ^ k / 2 / (r / 2) ^ k = ε / 2 := by
      have hne : (r / 2) ^ k ≠ 0 := (pow_pos hr2_pos k).ne'
      field_simp [hne]
    rw [hsimp] at hcauchy
    linarith
  have htend_rhs : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, (1 : ℂ) / (s - ρ n) ^ (k + 1))
      atTop (𝓝 (∑' n : ℕ, (1 : ℂ) / (s - ρ n) ^ (k + 1))) :=
    (summable_inv_sub_pow_of_strip hstrip hsum hs hk).hasSum.tendsto_sum_nat
  simp_rw [hFN_sd] at htend_sd
  exact tendsto_nhds_unique htend_sd htend_rhs

/-- **EXACT ALGEBRAIC POLE-ZERO CANCELLATION BOUND**:
for any `s : ℂ` with `s.re = 1 + μ` (`μ > 0`), any real `β₁ < 1`, and any `k : ℕ`:
`‖1 / (s - 1) ^ (k + 1) - 1 / (s - β₁) ^ (k + 1)‖ ≤ (k + 1) * (1 - β₁) / μ ^ (k + 2)`. -/
theorem norm_inv_pow_sub_inv_pow_le {s : ℂ} {μ β₁ : ℝ} (hμ : 0 < μ) (hs : s.re = 1 + μ)
    (hβ₁ : β₁ < 1) (k : ℕ) :
    ‖(1 : ℂ) / (s - 1) ^ (k + 1) - 1 / (s - (β₁ : ℂ)) ^ (k + 1)‖ ≤
      ((k + 1 : ℕ) : ℝ) * (1 - β₁) / μ ^ (k + 2) := by
  set a : ℂ := (s - 1)⁻¹
  set b : ℂ := (s - (β₁ : ℂ))⁻¹
  have hs1_ge : μ ≤ ‖s - 1‖ := by
    have hre := (le_abs_self (s - 1).re).trans (Complex.abs_re_le_norm (s - 1))
    simp only [Complex.sub_re, hs, Complex.one_re] at hre
    linarith
  have hsβ_ge : μ ≤ ‖s - (β₁ : ℂ)‖ := by
    have hre := (le_abs_self (s - (β₁ : ℂ)).re).trans (Complex.abs_re_le_norm (s - (β₁ : ℂ)))
    simp only [Complex.sub_re, hs, Complex.ofReal_re] at hre
    linarith
  have hs1_ne : s - 1 ≠ 0 := by intro h0; rw [h0, norm_zero] at hs1_ge; linarith
  have hsβ_ne : s - (β₁ : ℂ) ≠ 0 := by intro h0; rw [h0, norm_zero] at hsβ_ge; linarith
  have ha_le : ‖a‖ ≤ μ⁻¹ := by
    dsimp only [a]; rw [norm_inv]; exact inv_anti₀ hμ hs1_ge
  have hb_le : ‖b‖ ≤ μ⁻¹ := by
    dsimp only [b]; rw [norm_inv]; exact inv_anti₀ hμ hsβ_ge
  have hab_diff : a - b = ((1 - β₁ : ℝ) : ℂ) / ((s - 1) * (s - (β₁ : ℂ))) := by
    dsimp only [a, b]
    push_cast
    field_simp [hs1_ne, hsβ_ne]
    ring
  have hab_norm : ‖a - b‖ ≤ (1 - β₁) / μ ^ 2 := by
    rw [hab_diff, norm_div, Complex.norm_real, Real.norm_of_nonneg (by linarith), norm_mul]
    exact div_le_div_of_nonneg_left (by linarith) (sq_pos_of_pos hμ)
      (by rw [sq]; exact mul_le_mul hs1_ge hsβ_ge hμ.le (norm_nonneg _))
  have htel : a ^ (k + 1) - b ^ (k + 1) =
      (a - b) * ∑ j ∈ Finset.range (k + 1), a ^ j * b ^ (k - j) := by
    rw [Finset.mul_sum]
    have h1 : ∀ m : ℕ, (a - b) * ∑ j ∈ Finset.range (m + 1), a ^ j * b ^ (m - j) =
        a ^ (m + 1) - b ^ (m + 1) := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        rw [Finset.sum_range_succ, mul_add]
        have hshift :
            ∑ j ∈ Finset.range (m + 1), a ^ j * b ^ (m + 1 - j) =
              b * ∑ j ∈ Finset.range (m + 1), a ^ j * b ^ (m - j) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j hj => ?_
          have hjm : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
          have hexp : m + 1 - j = (m - j) + 1 := by omega
          rw [hexp, pow_succ]; ring
        rw [hshift, ← mul_assoc, mul_comm (a - b) b, mul_assoc, ih, Nat.sub_self, pow_zero, mul_one]
        ring
    rw [← Finset.mul_sum, h1 k]
  have hrew : (1 : ℂ) / (s - 1) ^ (k + 1) - 1 / (s - (β₁ : ℂ)) ^ (k + 1) =
      a ^ (k + 1) - b ^ (k + 1) := by
    dsimp only [a, b]; rw [inv_pow, inv_pow, one_div, one_div]
  rw [hrew, htel, norm_mul]
  have hsum_le :
      ‖∑ j ∈ Finset.range (k + 1), a ^ j * b ^ (k - j)‖ ≤
        ((k + 1 : ℕ) : ℝ) * (μ⁻¹) ^ k := by
    calc ‖∑ j ∈ Finset.range (k + 1), a ^ j * b ^ (k - j)‖
        ≤ ∑ j ∈ Finset.range (k + 1), ‖a ^ j * b ^ (k - j)‖ := norm_sum_le _ _
      _ ≤ ∑ _j ∈ Finset.range (k + 1), (μ⁻¹) ^ k := by
          refine Finset.sum_le_sum fun j hj => ?_
          have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
          rw [norm_mul, norm_pow, norm_pow]
          calc ‖a‖ ^ j * ‖b‖ ^ (k - j)
              ≤ (μ⁻¹) ^ j * (μ⁻¹) ^ (k - j) :=
                mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) ha_le _)
                  (pow_le_pow_left₀ (norm_nonneg _) hb_le _) (by positivity) (by positivity)
            _ = (μ⁻¹) ^ (j + (k - j)) := (pow_add _ _ _).symm
            _ = (μ⁻¹) ^ k := by rw [Nat.add_sub_of_le hjk]
      _ = ((k + 1 : ℕ) : ℝ) * (μ⁻¹) ^ k := by simp
  calc ‖a - b‖ * ‖∑ j ∈ Finset.range (k + 1), a ^ j * b ^ (k - j)‖
      ≤ ((1 - β₁) / μ ^ 2) * (((k + 1 : ℕ) : ℝ) * (μ⁻¹) ^ k) :=
        mul_le_mul hab_norm hsum_le (norm_nonneg _) (by positivity)
    _ = ((k + 1 : ℕ) : ℝ) * (1 - β₁) / μ ^ (k + 2) := by
        rw [inv_pow, pow_add]; field_simp [hμ.ne']

/-! ## Section 3: Unconditional Local Zero Counting, Tail-Sum Bounds, & High-Derivative Hadamard Expansions -/

/-- Elementary Dirichlet-series norm comparison on `Re(s) > 1`:
`‖negLogDerivL χ (σ + I * t)‖ ≤ (negLogDerivZeta σ).re` and `‖negLogDerivZeta (σ + I * t)‖ ≤ (negLogDerivZeta σ).re`. -/
private lemma norm_negLogDerivL_le_re_negLogDerivZeta {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    ‖negLogDerivL χ ((σ : ℂ) + I * (t : ℂ))‖ ≤ (negLogDerivZeta (σ : ℂ)).re := by
  have hs1 : 1 < ((σ : ℂ) + I * (t : ℂ)).re := by simp [hσ]
  have hs0 : 1 < (σ : ℂ).re := by simpa using hσ
  rw [negLogDerivL_eq_LSeries χ hs1, negLogDerivZeta_eq_LSeries hs0]
  have hsumχ : LSeriesSummable (fun n => χ n * (Λ n : ℂ)) ((σ : ℂ) + I * (t : ℂ)) :=
    χ.LSeriesSummable_twist_vonMangoldt hs1
  have hsumZ : LSeriesSummable (fun n => (Λ n : ℂ)) (σ : ℂ) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt hs0
  unfold LSeries
  rw [Complex.re_tsum hsumZ]
  refine (norm_tsum_le_tsum_norm hsumχ.norm).trans ?_
  refine hsumχ.norm.tsum_le_tsum (fun n => ?_) (Complex.reCLM.summable hsumZ)
  rcases eq_or_ne n 0 with rfl | hn
  · simp [LSeries.term_zero]
  · have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn, norm_div, norm_mul,
      Complex.norm_real, Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
      Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn)]
    have hcpow : (n : ℂ) ^ (σ : ℂ) = (((n : ℝ) ^ σ : ℝ) : ℂ) := by
      rw [← Complex.ofReal_natCast, Complex.ofReal_cpow hn_pos.le]
    rw [hcpow, ← Complex.ofReal_div, Complex.ofReal_re]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, zero_mul,
      Complex.I_im, Complex.ofReal_im, mul_zero, sub_self, add_zero]
    have h1 := χ.norm_le_one (n : ZMod q)
    exact div_le_div_of_nonneg_right
      (by nlinarith [ArithmeticFunction.vonMangoldt_nonneg (n := n)]) (by positivity)

private lemma norm_negLogDerivZeta_le_re_negLogDerivZeta {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    ‖negLogDerivZeta ((σ : ℂ) + I * (t : ℂ))‖ ≤ (negLogDerivZeta (σ : ℂ)).re := by
  have h1 := norm_negLogDerivL_le_re_negLogDerivZeta (1 : DirichletCharacter ℂ 1) hσ t
  have heq : negLogDerivL (1 : DirichletCharacter ℂ 1) ((σ : ℂ) + I * (t : ℂ)) =
      negLogDerivZeta ((σ : ℂ) + I * (t : ℂ)) := by
    unfold negLogDerivL negLogDerivZeta
    rw [DirichletCharacter.LFunction_modOne_eq]
  rwa [heq] at h1

/-- **UNCONDITIONAL UNIFORM FINITE ZERO-SUM REAL-PART UPPER BOUND (`0` ASSUMPTIONS!)**:
there exists an absolute constant `C₁ > 0` such that for all `1 < σ ≤ 2`, `t : ℝ`, and any finite
index set `F : Finset ℕ`:
1. `∑ n ∈ F, (1 / ((σ + I * t) - xiZeroSeq n)).re ≤ C₁ * Real.log (|t| + 2) + 2 / (σ - 1)`,
2. for every primitive `ψ ≠ 1` mod `f`:
   `∑ n ∈ F, (1 / ((σ + I * t) - completedLZeroSeq hprim hψ n)).re ≤ C₁ * Real.log (f * (|t| + 2)) + 2 / (σ - 1)`. -/
theorem re_finset_zero_sum_le_unconditional :
    ∃ C₁ : ℝ, 0 < C₁ ∧
      (∀ (σ t : ℝ), 1 < σ → σ ≤ 2 → ∀ F : Finset ℕ,
        ∑ n ∈ F, ((1 : ℂ) / (((σ : ℂ) + I * (t : ℂ)) - xiZeroSeq n)).re ≤
          C₁ * Real.log (|t| + 2) + 2 / (σ - 1)) ∧
      (∀ (f : ℕ) [NeZero f] (ψ : DirichletCharacter ℂ f) (hprim : ψ.IsPrimitive) (hψ : ψ ≠ 1),
        ∀ (σ t : ℝ), 1 < σ → σ ≤ 2 → ∀ F : Finset ℕ,
          ∑ n ∈ F, ((1 : ℂ) / (((σ : ℂ) + I * (t : ℂ)) - completedLZeroSeq hprim hψ n)).re ≤
            C₁ * Real.log ((f : ℝ) * (|t| + 2)) + 2 / (σ - 1)) := by
  obtain ⟨C, hC_pos, hZ_bd, hL_bd⟩ := Stage8HadamardLFunction.re_negLogDeriv_le_sub_finset_unconditional
  refine ⟨2 * C, by linarith, ?_, ?_⟩
  · intro σ t hσ1 hσ2 F
    have h1 := hZ_bd σ t hσ1 hσ2 F
    have h0 := hZ_bd σ 0 hσ1 hσ2 ∅
    simp only [Finset.sum_empty, sub_zero, abs_zero, zero_add, Complex.ofReal_zero, mul_zero,
      add_zero] at h0
    have hpole0 : ((1 : ℂ) / ((σ : ℂ) - 1)).re = 1 / (σ - 1) := by
      have : (1 : ℂ) / ((σ : ℂ) - 1) = ((1 / (σ - 1) : ℝ) : ℂ) := by push_cast; rfl
      rw [this, Complex.ofReal_re]
    rw [hpole0] at h0
    have hpole_t : ((1 : ℂ) / (((σ : ℂ) + I * (t : ℂ)) - 1)).re ≤ 1 / (σ - 1) := by
      have hre : (((σ : ℂ) + I * (t : ℂ)) - 1).re = σ - 1 := by simp
      have hnorm : σ - 1 ≤ ‖((σ : ℂ) + I * (t : ℂ)) - 1‖ := by
        have := (le_abs_self (((σ : ℂ) + I * (t : ℂ)) - 1).re).trans
          (Complex.abs_re_le_norm _)
        rw [hre] at this; linarith
      calc ((1 : ℂ) / (((σ : ℂ) + I * (t : ℂ)) - 1)).re
          ≤ ‖(1 : ℂ) / (((σ : ℂ) + I * (t : ℂ)) - 1)‖ :=
            (le_abs_self _).trans (Complex.abs_re_le_norm _)
        _ = 1 / ‖((σ : ℂ) + I * (t : ℂ)) - 1‖ := by rw [norm_div, norm_one]
        _ ≤ 1 / (σ - 1) := one_div_le_one_div_of_le (by linarith) hnorm
    have hneg_re : -(negLogDerivZeta ((σ : ℂ) + I * (t : ℂ))).re ≤
        C * Real.log 2 + 1 / (σ - 1) := by
      have h2 : -(negLogDerivZeta ((σ : ℂ) + I * (t : ℂ))).re ≤
          ‖negLogDerivZeta ((σ : ℂ) + I * (t : ℂ))‖ :=
        (neg_le_abs _).trans (Complex.abs_re_le_norm _)
      exact h2.trans ((norm_negLogDerivZeta_le_re_negLogDerivZeta hσ1 t).trans h0)
    have hlog_le : Real.log 2 ≤ Real.log (|t| + 2) :=
      Real.log_le_log (by norm_num) (by linarith [abs_nonneg t])
    have h2div : 2 / (σ - 1) = 1 / (σ - 1) + 1 / (σ - 1) := by ring
    linarith [mul_le_mul_of_nonneg_left hlog_le hC_pos.le]
  · intro f _ ψ hprim hψ σ t hσ1 hσ2 F
    have h1 := hL_bd f ψ hprim hψ σ t hσ1 hσ2 F
    have h0 := hZ_bd σ 0 hσ1 hσ2 ∅
    simp only [Finset.sum_empty, sub_zero, abs_zero, zero_add, Complex.ofReal_zero, mul_zero,
      add_zero] at h0
    have hpole0 : ((1 : ℂ) / ((σ : ℂ) - 1)).re = 1 / (σ - 1) := by
      have : (1 : ℂ) / ((σ : ℂ) - 1) = ((1 / (σ - 1) : ℝ) : ℂ) := by push_cast; rfl
      rw [this, Complex.ofReal_re]
    rw [hpole0] at h0
    have hneg_re : -(negLogDerivL ψ ((σ : ℂ) + I * (t : ℂ))).re ≤
        C * Real.log 2 + 1 / (σ - 1) := by
      have h2 : -(negLogDerivL ψ ((σ : ℂ) + I * (t : ℂ))).re ≤
          ‖negLogDerivL ψ ((σ : ℂ) + I * (t : ℂ))‖ :=
        (neg_le_abs _).trans (Complex.abs_re_le_norm _)
      exact h2.trans ((norm_negLogDerivL_le_re_negLogDerivZeta ψ hσ1 t).trans h0)
    have hf_ge1 : (1 : ℝ) ≤ (f : ℝ) := by exact_mod_cast NeZero.pos f
    have hlog_le : Real.log 2 ≤ Real.log ((f : ℝ) * (|t| + 2)) :=
      Real.log_le_log (by norm_num) (by nlinarith [abs_nonneg t])
    have hσ_pos : 0 < 1 / (σ - 1) := by positivity
    have h2div : 2 / (σ - 1) = 1 / (σ - 1) + 1 / (σ - 1) := by ring
    linarith [mul_le_mul_of_nonneg_left hlog_le hC_pos.le]

/-- **LOCAL ZERO-COUNTING IN ANY DISK OF RADIUS `r ≤ 1`**:
if a critical-strip zero sequence `ρ` satisfies the uniform real-part bound at height `t`, then
for any `0 < μ ≤ r ≤ 1`, `s = (1 + μ) + I * t`, and any `F : Finset ℕ` with `∀ n ∈ F, ‖s - ρ n‖ ≤ r`:
`(F.card : ℝ) ≤ 4 * C₁ * r * L + 8`. -/
theorem finset_card_ball_le_of_re_le {ρ : ℕ → ℂ} {t C₁ L : ℝ}
    (hstrip : ∀ n, 0 < (ρ n).re ∧ (ρ n).re < 1)
    (hre_le : ∀ σ : ℝ, 1 < σ → σ ≤ 2 → ∀ F : Finset ℕ,
      ∑ n ∈ F, ((1 : ℂ) / (((σ : ℂ) + I * (t : ℂ)) - ρ n)).re ≤ C₁ * L + 2 / (σ - 1))
    {μ r : ℝ} (hμ : 0 < μ) (hμr : μ ≤ r) (hr1 : r ≤ 1)
    (F : Finset ℕ) (hF : ∀ n ∈ F, ‖((1 + μ : ℝ) : ℂ) + I * (t : ℂ) - ρ n‖ ≤ r) :
    (F.card : ℝ) ≤ 4 * C₁ * r * L + 8 := by
  have hr_pos : 0 < r := lt_of_lt_of_le hμ hμr
  set s_r : ℂ := ((1 + r : ℝ) : ℂ) + I * (t : ℂ)
  have hterm : ∀ n ∈ F, (1 : ℝ) / (4 * r) ≤ ((1 : ℂ) / (s_r - ρ n)).re := by
    intro n hn
    have hdist_r : ‖s_r - ρ n‖ ≤ 2 * r := by
      have hdiff : s_r - ρ n = (((1 + μ : ℝ) : ℂ) + I * (t : ℂ) - ρ n) + ((r - μ : ℝ) : ℂ) := by
        dsimp only [s_r]; push_cast; ring
      rw [hdiff]
      calc ‖(((1 + μ : ℝ) : ℂ) + I * (t : ℂ) - ρ n) + ((r - μ : ℝ) : ℂ)‖
          ≤ ‖((1 + μ : ℝ) : ℂ) + I * (t : ℂ) - ρ n‖ + ‖((r - μ : ℝ) : ℂ)‖ := norm_add_le _ _
        _ ≤ r + (r - μ) := by
            rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]
            linarith [hF n hn]
        _ ≤ 2 * r := by linarith
    have hre_ge : r ≤ (s_r - ρ n).re := by
      have : (s_r - ρ n).re = 1 + r - (ρ n).re := by simp [s_r]
      rw [this]; linarith [(hstrip n).2]
    have hnorm_pos : 0 < ‖s_r - ρ n‖ := by
      have := (le_abs_self (s_r - ρ n).re).trans (Complex.abs_re_le_norm (s_r - ρ n))
      linarith
    have hinv_re : ((1 : ℂ) / (s_r - ρ n)).re = (s_r - ρ n).re / ‖s_r - ρ n‖ ^ 2 := by
      rw [one_div, Complex.inv_re, Complex.normSq_eq_norm_sq]
    rw [hinv_re]
    have hsq_le : ‖s_r - ρ n‖ ^ 2 ≤ (2 * r) ^ 2 :=
      pow_le_pow_left₀ hnorm_pos.le hdist_r 2
    calc (1 : ℝ) / (4 * r) = r / (2 * r) ^ 2 := by field_simp [hr_pos.ne']; ring
      _ ≤ (s_r - ρ n).re / ‖s_r - ρ n‖ ^ 2 :=
          div_le_div₀ (by linarith) hre_ge (sq_pos_of_pos hnorm_pos) hsq_le
  have hsum_lo : (F.card : ℝ) / (4 * r) ≤ ∑ n ∈ F, ((1 : ℂ) / (s_r - ρ n)).re := by
    calc (F.card : ℝ) / (4 * r)
        = ∑ _n ∈ F, (1 : ℝ) / (4 * r) := by rw [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ ∑ n ∈ F, ((1 : ℂ) / (s_r - ρ n)).re := Finset.sum_le_sum hterm
  have hsum_hi := hre_le (1 + r) (by linarith) (by linarith) F
  rw [show (1 + r : ℝ) - 1 = r by ring] at hsum_hi
  have hcomb : (F.card : ℝ) / (4 * r) ≤ C₁ * L + 2 / r := hsum_lo.trans hsum_hi
  have hmul := mul_le_mul_of_nonneg_right hcomb (by positivity : (0 : ℝ) ≤ 4 * r)
  have h1 : (F.card : ℝ) / (4 * r) * (4 * r) = (F.card : ℝ) := by field_simp [hr_pos.ne']
  have h2 : (C₁ * L + 2 / r) * (4 * r) = 4 * C₁ * r * L + 8 := by field_simp [hr_pos.ne']; ring
  linarith

/-- Finiteness of `{ n : ℕ | ‖s - ρ n‖ ≤ r }` from `hstrip` and `hsum`. -/
lemma finite_ball_zero_indices {ρ : ℕ → ℂ}
    (hstrip : ∀ n, 0 < (ρ n).re ∧ (ρ n).re < 1)
    (hsum : Summable (fun n : ℕ => (‖ρ n‖ ^ 2)⁻¹)) (s : ℂ) (r : ℝ) :
    {n : ℕ | ‖s - ρ n‖ ≤ r}.Finite := by
  have htend : Tendsto (fun n : ℕ => (‖ρ n‖ ^ 2)⁻¹) atTop (𝓝 0) := hsum.tendsto_atTop_zero
  set M : ℝ := ‖s‖ + max r 0 + 1
  have hM_pos : 0 < M := by dsimp only [M]; positivity
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (htend.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < (M ^ 2)⁻¹)))
  refine (Finset.finite_toSet (Finset.range N)).subset fun n hn => ?_
  simp only [Finset.mem_coe, Finset.mem_range]
  by_contra hge; push Not at hge
  have hlt := hN n hge
  have hnorm_le : ‖ρ n‖ ≤ M := by
    have htri : ‖ρ n‖ ≤ ‖s - ρ n‖ + ‖s‖ := by
      have : ρ n = -(s - ρ n) + s := by ring
      calc ‖ρ n‖ = ‖-(s - ρ n) + s‖ := congrArg norm this
        _ ≤ ‖-(s - ρ n)‖ + ‖s‖ := norm_add_le _ _
        _ = ‖s - ρ n‖ + ‖s‖ := by rw [norm_neg]
    have hr_le : r ≤ max r 0 := le_max_left r 0
    dsimp only [M]; linarith [show ‖s - ρ n‖ ≤ r from hn]
  have hρ_pos : 0 < ‖ρ n‖ := by
    have := (le_abs_self (ρ n).re).trans (Complex.abs_re_le_norm (ρ n))
    linarith [(hstrip n).1]
  have hinv : (M ^ 2)⁻¹ ≤ (‖ρ n‖ ^ 2)⁻¹ :=
    inv_anti₀ (sq_pos_of_pos hρ_pos) (pow_le_pow_left₀ hρ_pos.le hnorm_le 2)
  linarith

/-- **DYADIC MEDIUM-TAIL SUM BOUND (`R < ‖s - ρ n‖ ≤ 1`)**:
for any `m ≥ 1`, `A ≥ 4`, `0 < μ`, `R = A * μ ≤ 1 / 2`:
`∑' n, (if R < ‖s - ρ n‖ ∧ ‖s - ρ n‖ ≤ 1 then (2 * μ / ‖s - ρ n‖) ^ (2 * m) else 0)
  ≤ (2 / A) ^ (2 * m) * ((16 * C₁ + 16) * (A * (μ * L) + 1))`. -/
theorem tsum_tail_medium_le_of_re_le {ρ : ℕ → ℂ} {t C₁ L : ℝ}
    (hC₁ : 0 ≤ C₁) (hL : 0 ≤ L)
    (hstrip : ∀ n, 0 < (ρ n).re ∧ (ρ n).re < 1)
    (hsum : Summable (fun n : ℕ => (‖ρ n‖ ^ 2)⁻¹))
    (hre_le : ∀ σ : ℝ, 1 < σ → σ ≤ 2 → ∀ F : Finset ℕ,
      ∑ n ∈ F, ((1 : ℂ) / (((σ : ℂ) + I * (t : ℂ)) - ρ n)).re ≤ C₁ * L + 2 / (σ - 1))
    {μ A : ℝ} (hμ : 0 < μ) (hA : 4 ≤ A) (hR_le : A * μ ≤ 1 / 2)
    {m : ℕ} (hm : 1 ≤ m) :
    let s : ℂ := ((1 + μ : ℝ) : ℂ) + I * (t : ℂ)
    let R : ℝ := A * μ
    ∑' n : ℕ, (if R < ‖s - ρ n‖ ∧ ‖s - ρ n‖ ≤ 1 then (2 * μ / ‖s - ρ n‖) ^ (2 * m) else 0) ≤
      (2 / A) ^ (2 * m) * ((16 * C₁ + 16) * (A * (μ * L) + 1)) := by
  classical
  intro s R
  have hR_pos : 0 < R := by dsimp only [R]; positivity
  have hS_fin : {n : ℕ | ‖s - ρ n‖ ≤ 1}.Finite := finite_ball_zero_indices hstrip hsum s 1
  set S_all : Finset ℕ := hS_fin.toFinset
  have hmem_S : ∀ n : ℕ, n ∈ S_all ↔ ‖s - ρ n‖ ≤ 1 := fun n => hS_fin.mem_toFinset
  have htsum_eq :
      ∑' n : ℕ, (if R < ‖s - ρ n‖ ∧ ‖s - ρ n‖ ≤ 1 then (2 * μ / ‖s - ρ n‖) ^ (2 * m) else 0) =
        ∑ n ∈ S_all.filter (fun n => R < ‖s - ρ n‖), (2 * μ / ‖s - ρ n‖) ^ (2 * m) := by
    rw [tsum_eq_sum (s := S_all) (fun n hn => by
      have hnot : ¬ (‖s - ρ n‖ ≤ 1) := fun h => hn ((hmem_S n).mpr h)
      simp [hnot])]
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun n hn => ?_
    have h1 : ‖s - ρ n‖ ≤ 1 := (hmem_S n).mp hn
    simp [h1]
  rw [htsum_eq]
  -- Choose `J` so that `1 ≤ 2 ^ J * R`
  obtain ⟨J, hJ⟩ : ∃ J : ℕ, 1 ≤ (2 : ℝ) ^ J * R := by
    obtain ⟨J, hJ⟩ := exists_nat_gt (1 / R)
    refine ⟨J, ?_⟩
    have h2J : ∀ k : ℕ, (k : ℝ) ≤ (2 : ℝ) ^ k := by
      intro k
      induction k with
      | zero => norm_num
      | succ k ih =>
        rw [pow_succ]; push_cast
        have hge1 : (1 : ℝ) ≤ (2 : ℝ) ^ k := one_le_pow₀ (by norm_num)
        linarith
    have h1 : 1 / R < (2 : ℝ) ^ J := hJ.trans_le (h2J J)
    exact (div_lt_iff₀ hR_pos).mp h1 |>.le
  let shell : ℕ → Finset ℕ := fun j =>
    S_all.filter (fun n => (2 : ℝ) ^ j * R < ‖s - ρ n‖ ∧ ‖s - ρ n‖ ≤ (2 : ℝ) ^ (j + 1) * R)
  have hcover : S_all.filter (fun n => R < ‖s - ρ n‖) ⊆ (Finset.range J).biUnion shell := by
    intro n hn
    have hnS := (Finset.mem_filter.mp hn).1
    have hlo : R < ‖s - ρ n‖ := (Finset.mem_filter.mp hn).2
    have hhi : ‖s - ρ n‖ ≤ 1 := (hmem_S n).mp hnS
    have hex : ∃ j : ℕ, j < J ∧ (2 : ℝ) ^ j * R < ‖s - ρ n‖ ∧
        ‖s - ρ n‖ ≤ (2 : ℝ) ^ (j + 1) * R := by
      have hset : ∃ k : ℕ, k ≤ J ∧ ‖s - ρ n‖ ≤ (2 : ℝ) ^ k * R := ⟨J, le_rfl, hhi.trans hJ⟩
      let k₀ := Nat.find hset
      have hk₀ : k₀ ≤ J ∧ ‖s - ρ n‖ ≤ (2 : ℝ) ^ k₀ * R := Nat.find_spec hset
      have hk₀_pos : 0 < k₀ := by
        by_contra h0; push Not at h0
        have hk0 : k₀ = 0 := by omega
        rw [hk0, pow_zero, one_mul] at hk₀
        linarith
      refine ⟨k₀ - 1, by omega, ?_, ?_⟩
      · by_contra hle; push Not at hle
        exact Nat.find_min hset (by omega : k₀ - 1 < k₀) ⟨by omega, hle⟩
      · have : k₀ - 1 + 1 = k₀ := by omega
        rw [this]; exact hk₀.2
    obtain ⟨j, hjJ, hjlo, hjhi⟩ := hex
    exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_range.mpr hjJ,
      Finset.mem_filter.mpr ⟨hnS, hjlo, hjhi⟩⟩
  have hbiUnion_le : ∀ (u : Finset ℕ) (t : ℕ → Finset ℕ) (f : ℕ → ℝ), (∀ b, 0 ≤ f b) →
      ∑ b ∈ u.biUnion t, f b ≤ ∑ a ∈ u, ∑ b ∈ t a, f b := by
    intro u t f hf
    induction u using Finset.induction_on with
    | empty => simp
    | insert x u hx ih =>
      rw [Finset.biUnion_insert, Finset.sum_insert hx]
      have hu : ∑ b ∈ t x ∪ u.biUnion t, f b ≤ ∑ b ∈ t x, f b + ∑ b ∈ u.biUnion t, f b := by
        rw [← Finset.sum_union_inter]
        linarith [Finset.sum_nonneg (s := t x ∩ u.biUnion t) (f := f) fun b _ => hf b]
      linarith
  have hshell_bd : ∀ j : ℕ,
      ∑ n ∈ shell j, (2 * μ / ‖s - ρ n‖) ^ (2 * m) ≤
        (2 / A) ^ (2 * m) *
          (8 * C₁ * (A * (μ * L)) * (1 / 2 : ℝ) ^ j + 8 * (1 / 4 : ℝ) ^ j) := by
    intro j
    have hcard : ((shell j).card : ℝ) ≤ 4 * C₁ * ((2 : ℝ) ^ (j + 1) * R) * L + 8 := by
      set r_j : ℝ := min 1 ((2 : ℝ) ^ (j + 1) * R)
      have hrj_le1 : r_j ≤ 1 := min_le_left _ _
      have hrj_geμ : μ ≤ r_j := by
        refine le_min (by nlinarith) ?_
        have h2ge1 : (1 : ℝ) ≤ (2 : ℝ) ^ (j + 1) := one_le_pow₀ (by norm_num)
        dsimp only [R]; nlinarith
      have hcard1 := finset_card_ball_le_of_re_le hstrip hre_le hμ hrj_geμ hrj_le1 (shell j)
        fun n hn => by
          have hmem := Finset.mem_filter.mp hn
          exact le_min ((hmem_S n).mp hmem.1) hmem.2.2
      have hrj_le : r_j ≤ (2 : ℝ) ^ (j + 1) * R := min_le_right _ _
      have h1 : 4 * C₁ * r_j * L ≤ 4 * C₁ * ((2 : ℝ) ^ (j + 1) * R) * L := by
        have : 0 ≤ 4 * C₁ * L := by positivity
        nlinarith
      linarith
    have hterm_j : ∀ n ∈ shell j,
        (2 * μ / ‖s - ρ n‖) ^ (2 * m) ≤ (2 / A) ^ (2 * m) * (1 / 4 : ℝ) ^ j := by
      intro n hn
      have hlo := (Finset.mem_filter.mp hn).2.1
      have hdiv : 2 * μ / ‖s - ρ n‖ ≤ (2 / A) * (1 / 2 : ℝ) ^ j := by
        have hden_pos : 0 < (2 : ℝ) ^ j * R := by positivity
        calc 2 * μ / ‖s - ρ n‖
            ≤ 2 * μ / ((2 : ℝ) ^ j * R) :=
              div_le_div_of_nonneg_left (by positivity) hden_pos hlo.le
          _ = (2 / A) * (1 / 2 : ℝ) ^ j := by
              dsimp only [R]; rw [one_div, inv_pow]
              have hA_ne : A ≠ 0 := by linarith
              have h2j_ne : (2 : ℝ) ^ j ≠ 0 := by positivity
              field_simp [hμ.ne', hA_ne, h2j_ne]
      have hpow_le : ((1 / 2 : ℝ) ^ j) ^ (2 * m) ≤ (1 / 4 : ℝ) ^ j := by
        rw [← pow_mul, mul_comm j (2 * m), pow_mul]
        have hbase : ((1 / 2 : ℝ) ^ (2 * m)) ≤ (1 / 4 : ℝ) := by
          have h2m : 2 ≤ 2 * m := by omega
          calc (1 / 2 : ℝ) ^ (2 * m) ≤ (1 / 2 : ℝ) ^ 2 :=
                pow_le_pow_of_le_one (by norm_num) (by norm_num) h2m
            _ = 1 / 4 := by norm_num
        exact pow_le_pow_left₀ (by positivity) hbase j
      calc (2 * μ / ‖s - ρ n‖) ^ (2 * m)
          ≤ ((2 / A) * (1 / 2 : ℝ) ^ j) ^ (2 * m) :=
            pow_le_pow_left₀ (by positivity) hdiv _
        _ = (2 / A) ^ (2 * m) * ((1 / 2 : ℝ) ^ j) ^ (2 * m) := mul_pow _ _ _
        _ ≤ (2 / A) ^ (2 * m) * (1 / 4 : ℝ) ^ j :=
            mul_le_mul_of_nonneg_left hpow_le (by positivity)
    calc ∑ n ∈ shell j, (2 * μ / ‖s - ρ n‖) ^ (2 * m)
        ≤ ∑ _n ∈ shell j, (2 / A) ^ (2 * m) * (1 / 4 : ℝ) ^ j :=
          Finset.sum_le_sum hterm_j
      _ = ((shell j).card : ℝ) * ((2 / A) ^ (2 * m) * (1 / 4 : ℝ) ^ j) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (4 * C₁ * ((2 : ℝ) ^ (j + 1) * R) * L + 8) *
            ((2 / A) ^ (2 * m) * (1 / 4 : ℝ) ^ j) :=
          mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = (2 / A) ^ (2 * m) *
            (8 * C₁ * (A * (μ * L)) * ((2 : ℝ) ^ j * (1 / 4 : ℝ) ^ j) + 8 * (1 / 4 : ℝ) ^ j) := by
          dsimp only [R]; rw [pow_succ]; ring
      _ = (2 / A) ^ (2 * m) *
            (8 * C₁ * (A * (μ * L)) * (1 / 2 : ℝ) ^ j + 8 * (1 / 4 : ℝ) ^ j) := by
          rw [← mul_pow, show (2 : ℝ) * (1 / 4 : ℝ) = 1 / 2 by norm_num]
  have hgeom2 : ∑ j ∈ Finset.range J, (1 / 2 : ℝ) ^ j ≤ 2 := by
    have h1 := geom_sum_eq (by norm_num : (1 / 2 : ℝ) ≠ 1) J
    rw [h1]
    have hpos : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ J := by positivity
    linarith [show ((1 / 2 : ℝ) ^ J - 1) / (1 / 2 - 1) = 2 * (1 - (1 / 2 : ℝ) ^ J) by ring]
  have hgeom4 : ∑ j ∈ Finset.range J, (1 / 4 : ℝ) ^ j ≤ 2 := by
    have h1 := geom_sum_eq (by norm_num : (1 / 4 : ℝ) ≠ 1) J
    rw [h1]
    have hpos : (0 : ℝ) ≤ (1 / 4 : ℝ) ^ J := by positivity
    linarith [show ((1 / 4 : ℝ) ^ J - 1) / (1 / 4 - 1) = (4 / 3) * (1 - (1 / 4 : ℝ) ^ J) by ring]
  calc ∑ n ∈ S_all.filter (fun n => R < ‖s - ρ n‖), (2 * μ / ‖s - ρ n‖) ^ (2 * m)
      ≤ ∑ n ∈ (Finset.range J).biUnion shell, (2 * μ / ‖s - ρ n‖) ^ (2 * m) :=
        Finset.sum_le_sum_of_subset_of_nonneg hcover fun _ _ _ => by positivity
    _ ≤ ∑ j ∈ Finset.range J, ∑ n ∈ shell j, (2 * μ / ‖s - ρ n‖) ^ (2 * m) :=
        hbiUnion_le _ _ _ fun _ => by positivity
    _ ≤ ∑ j ∈ Finset.range J, (2 / A) ^ (2 * m) *
          (8 * C₁ * (A * (μ * L)) * (1 / 2 : ℝ) ^ j + 8 * (1 / 4 : ℝ) ^ j) :=
        Finset.sum_le_sum fun j _ => hshell_bd j
    _ = (2 / A) ^ (2 * m) *
          (8 * C₁ * (A * (μ * L)) * ∑ j ∈ Finset.range J, (1 / 2 : ℝ) ^ j +
            8 * ∑ j ∈ Finset.range J, (1 / 4 : ℝ) ^ j) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ (2 / A) ^ (2 * m) * (8 * C₁ * (A * (μ * L)) * 2 + 8 * 2) := by
        gcongr
    _ ≤ (2 / A) ^ (2 * m) * ((16 * C₁ + 16) * (A * (μ * L) + 1)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have hnn : 0 ≤ A * (μ * L) := by positivity
        nlinarith

/-- **FAR-TAIL SUM BOUND (`‖s - ρ n‖ > 1`) via `σ = 2`**:
for any `0 < μ ≤ 1 / 2` and `m ≥ 1`:
`∑' n, (if 1 < ‖s - ρ n‖ then (2 * μ / ‖s - ρ n‖) ^ (2 * m) else 0) ≤ 4 * (2 * μ) ^ (2 * m) * (C₁ * L + 2)`. -/
theorem tsum_tail_far_le_of_re_le {ρ : ℕ → ℂ} {t C₁ L : ℝ}
    (hstrip : ∀ n, 0 < (ρ n).re ∧ (ρ n).re < 1)
    (hsum : Summable (fun n : ℕ => (‖ρ n‖ ^ 2)⁻¹))
    (hre_le : ∀ σ : ℝ, 1 < σ → σ ≤ 2 → ∀ F : Finset ℕ,
      ∑ n ∈ F, ((1 : ℂ) / (((σ : ℂ) + I * (t : ℂ)) - ρ n)).re ≤ C₁ * L + 2 / (σ - 1))
    {μ : ℝ} (hμ : 0 < μ) (hμ_le : μ ≤ 1 / 2) {m : ℕ} (hm : 1 ≤ m) :
    let s : ℂ := ((1 + μ : ℝ) : ℂ) + I * (t : ℂ)
    ∑' n : ℕ, (if 1 < ‖s - ρ n‖ then (2 * μ / ‖s - ρ n‖) ^ (2 * m) else 0) ≤
      4 * (2 * μ) ^ (2 * m) * (C₁ * L + 2) := by
  classical
  intro s
  have hsumm_base := summable_inv_sub_pow_of_strip hstrip hsum (s := s) (by simp [s]; linarith)
    (k := 2 * m - 1) (by omega)
  have hsumm_f : Summable (fun n : ℕ =>
      if 1 < ‖s - ρ n‖ then (2 * μ / ‖s - ρ n‖) ^ (2 * m) else 0) := by
    refine Summable.of_nonneg_of_le (fun n => by split_ifs <;> positivity) (fun n => ?_)
      (hsumm_base.norm.mul_left ((2 * μ) ^ (2 * m)))
    split_ifs
    · rw [norm_div, norm_one, norm_pow, show 2 * m - 1 + 1 = 2 * m by omega, div_pow]
      ring_nf; exact le_rfl
    · positivity
  refine Summable.tsum_le_of_sum_range_le hsumm_f fun N => ?_
  set s₂ : ℂ := (2 : ℂ) + I * (t : ℂ)
  have hterm : ∀ n : ℕ,
      (if 1 < ‖s - ρ n‖ then (2 * μ / ‖s - ρ n‖) ^ (2 * m) else 0) ≤
        4 * (2 * μ) ^ (2 * m) * ((1 : ℂ) / (s₂ - ρ n)).re := by
    intro n
    have hre2_pos : 1 ≤ (s₂ - ρ n).re := by
      have : (s₂ - ρ n).re = 2 - (ρ n).re := by simp [s₂]
      rw [this]; linarith [(hstrip n).2]
    have hnorm2_pos : 0 < ‖s₂ - ρ n‖ := by
      have := (le_abs_self (s₂ - ρ n).re).trans (Complex.abs_re_le_norm (s₂ - ρ n))
      linarith
    have hinv_re : ((1 : ℂ) / (s₂ - ρ n)).re = (s₂ - ρ n).re / ‖s₂ - ρ n‖ ^ 2 := by
      rw [one_div, Complex.inv_re, Complex.normSq_eq_norm_sq]
    split_ifs with hgt
    · have hdist2 : ‖s₂ - ρ n‖ ≤ 2 * ‖s - ρ n‖ := by
        have hdiff : s₂ - ρ n = (s - ρ n) + ((1 - μ : ℝ) : ℂ) := by
          dsimp only [s₂, s]; push_cast; ring
        rw [hdiff]
        calc ‖(s - ρ n) + ((1 - μ : ℝ) : ℂ)‖
            ≤ ‖s - ρ n‖ + ‖((1 - μ : ℝ) : ℂ)‖ := norm_add_le _ _
          _ = ‖s - ρ n‖ + (1 - μ) := by rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]
          _ ≤ 2 * ‖s - ρ n‖ := by linarith
      have hpow_ge : ‖s - ρ n‖ ^ 2 ≤ ‖s - ρ n‖ ^ (2 * m) :=
        pow_le_pow_right₀ hgt.le (by omega)
      have hsq_le : ‖s₂ - ρ n‖ ^ 2 ≤ 4 * ‖s - ρ n‖ ^ 2 := by
        have := pow_le_pow_left₀ hnorm2_pos.le hdist2 2
        linarith [show (2 * ‖s - ρ n‖) ^ 2 = 4 * ‖s - ρ n‖ ^ 2 by ring]
      have h1 : 1 / ‖s - ρ n‖ ^ (2 * m) ≤ 4 * ((1 : ℂ) / (s₂ - ρ n)).re := by
        rw [hinv_re]
        calc 1 / ‖s - ρ n‖ ^ (2 * m)
            ≤ 1 / ‖s - ρ n‖ ^ 2 := one_div_le_one_div_of_le (by positivity) hpow_ge
          _ = 4 / (4 * ‖s - ρ n‖ ^ 2) := by field_simp [(by linarith : ‖s - ρ n‖ ≠ 0)]
          _ ≤ 4 * ((s₂ - ρ n).re / ‖s₂ - ρ n‖ ^ 2) := by
              rw [← mul_div_assoc]
              exact div_le_div₀ (by positivity) (by linarith) (sq_pos_of_pos hnorm2_pos) hsq_le
      rw [div_pow, div_eq_mul_inv, ← one_div]
      calc (2 * μ) ^ (2 * m) * (1 / ‖s - ρ n‖ ^ (2 * m))
          ≤ (2 * μ) ^ (2 * m) * (4 * ((1 : ℂ) / (s₂ - ρ n)).re) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = 4 * (2 * μ) ^ (2 * m) * ((1 : ℂ) / (s₂ - ρ n)).re := by ring
    · rw [hinv_re]; positivity
  calc ∑ n ∈ Finset.range N, (if 1 < ‖s - ρ n‖ then (2 * μ / ‖s - ρ n‖) ^ (2 * m) else 0)
      ≤ ∑ n ∈ Finset.range N, 4 * (2 * μ) ^ (2 * m) * ((1 : ℂ) / (s₂ - ρ n)).re :=
        Finset.sum_le_sum fun n _ => hterm n
    _ = 4 * (2 * μ) ^ (2 * m) * ∑ n ∈ Finset.range N, ((1 : ℂ) / (s₂ - ρ n)).re :=
        (Finset.mul_sum _ _ _).symm
    _ ≤ 4 * (2 * μ) ^ (2 * m) * (C₁ * L + 2) := by
        have h2 := hre_le 2 (by norm_num) le_rfl (Finset.range N)
        norm_num at h2
        exact mul_le_mul_of_nonneg_left (by simpa [s₂] using h2) (by positivity)

/-- **UNCONDITIONAL HIGH-DERIVATIVE HADAMARD EXPANSION FOR `negLogDerivZeta` AND EVERY
`negLogDerivL χ` (`k ≥ 1`, `1 < s.re ≤ 2`, `0` ASSUMPTIONS!)**:
1. `scaledDeriv k negLogDerivZeta s = 1 / (s - 1) ^ (k + 1) - ∑' n, 1 / (s - xiZeroSeq n) ^ (k + 1) + E_ζ`,
   with `‖E_ζ‖ ≤ C_E * 2 ^ k * Real.log (|s.im| + 2)`.
2. For any `χ : DirichletCharacter ℂ q` (`[NeZero q]`):
   - if `χ = 1`: `scaledDeriv k (negLogDerivL χ) s = 1 / (s - 1) ^ (k + 1) - ∑' n, 1 / (s - xiZeroSeq n) ^ (k + 1) + E_χ`,
   - if `χ ≠ 1`: `scaledDeriv k (negLogDerivL χ) s = - ∑' n, 1 / (s - completedLZeroSeq ... n) ^ (k + 1) + E_χ`,
   with `‖E_χ‖ ≤ C_E * 2 ^ k * Real.log (q * (|s.im| + 2))`. -/
theorem scaledDeriv_hadamard_expansion_unconditional :
    ∃ C_E : ℝ, 0 < C_E ∧
      (∀ (s : ℂ), 1 < s.re → s.re ≤ 2 → ∀ k : ℕ, 1 ≤ k →
        ‖scaledDeriv k negLogDerivZeta s -
            (1 / (s - 1) ^ (k + 1) - ∑' n : ℕ, (1 : ℂ) / (s - xiZeroSeq n) ^ (k + 1))‖ ≤
          C_E * (2 : ℝ) ^ k * Real.log (|s.im| + 2)) ∧
      (∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ),
        1 < s.re → s.re ≤ 2 → ∀ k : ℕ, 1 ≤ k →
          (χ = 1 →
            ‖scaledDeriv k (negLogDerivL χ) s -
                (1 / (s - 1) ^ (k + 1) - ∑' n : ℕ, (1 : ℂ) / (s - xiZeroSeq n) ^ (k + 1))‖ ≤
              C_E * (2 : ℝ) ^ k * Real.log ((q : ℝ) * (|s.im| + 2))) ∧
          (∀ hχ : χ ≠ 1,
            have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
            have hψ : χ.primitiveCharacter ≠ 1 := fun h1 => hχ (by
              rw [← χ.changeLevel_primitiveCharacter, h1, map_one])
            ‖scaledDeriv k (negLogDerivL χ) s -
                (- ∑' n : ℕ, (1 : ℂ) / (s - completedLZeroSeq χ.primitiveCharacter_isPrimitive hψ n) ^ (k + 1))‖ ≤
              C_E * (2 : ℝ) ^ k * Real.log ((q : ℝ) * (|s.im| + 2)))) := by
  obtain ⟨C_dig, hC_dig_pos, hdig_sd⟩ := norm_scaledDeriv_digamma_half_le
  set C_E : ℝ := C_dig + 8
  have hC_E_pos : 0 < C_E := by dsimp only [C_E]; linarith
  have hlog2_half : (1 / 2 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  -- Helper: `ContDiffAt` for `negLogDerivL` on `1 < s.re`
  have hcd_L : ∀ {m : ℕ} [NeZero m] (φ : DirichletCharacter ℂ m) {s : ℂ} (hs : 1 < s.re) (k : ℕ),
      ContDiffAt ℂ k (negLogDerivL φ) s := by
    intro m _ φ s hs k
    have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    have hdiff : DifferentiableOn ℂ (negLogDerivL φ) {z : ℂ | 1 < z.re} := by
      have habs : LSeries.abscissaOfAbsConv (fun n => φ n * (Λ n : ℂ)) ≤ (1 : EReal) :=
        LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun x hx =>
          φ.LSeriesSummable_twist_vonMangoldt (by simpa using hx)
      intro z hz
      have hlt : LSeries.abscissaOfAbsConv (fun n => φ n * (Λ n : ℂ)) < (z.re : EReal) :=
        lt_of_le_of_lt habs (EReal.coe_lt_coe_iff.mpr hz)
      have hev : negLogDerivL φ =ᶠ[𝓝 z] LSeries (fun n => φ n * (Λ n : ℂ)) := by
        filter_upwards [hopen.mem_nhds hz] with w hw
        exact negLogDerivL_eq_LSeries φ hw
      exact ((LSeries_hasDerivAt hlt).congr_of_eventuallyEq hev).differentiableAt.differentiableWithinAt
    exact (hdiff.analyticAt (hopen.mem_nhds hs)).contDiffAt.of_le le_top
  -- Helper: `ContDiffAt` for Hadamard tsum on `1 < s.re`
  have hcd_tsum : ∀ {ρ : ℕ → ℂ}, (∀ n, 0 < (ρ n).re ∧ (ρ n).re < 1) →
      Summable (fun n : ℕ => (‖ρ n‖ ^ 2)⁻¹) → ∀ {s : ℂ}, 1 < s.re → ∀ k : ℕ,
      ContDiffAt ℂ k (fun z : ℂ => ∑' n : ℕ, ((1 : ℂ) / (z - ρ n) + 1 / ρ n)) s := by
    intro ρ hstrip hsum s hs k
    -- Holomorphic on `1 < z.re` as uniform limit on `closedBall s ((s.re - 1) / 2)`
    -- Use `negLogDerivZeta` / `L`? No, prove directly via `hadamard_canonical_logDeriv_eq` or local ball!
    set r : ℝ := (s.re - 1) / 2
    have hr_pos : 0 < r := by dsimp only [r]; linarith
    have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    have hW_diff : Differentiable ℂ (weierstrassProduct ρ) :=
      Stage5JensenHadamard.differentiable_weierstrassProduct
        (fun n h0 => by have := (hstrip n).1; rw [h0, Complex.zero_re] at this; linarith) hsum
    have hW_nz : ∀ z : ℂ, 1 < z.re → weierstrassProduct ρ z ≠ 0 := by
      intro z hz h0
      rw [Stage5JensenHadamard.weierstrassProduct_eq_zero_iff
        (fun n h => by have := (hstrip n).1; rw [h, Complex.zero_re] at this; linarith) hsum] at h0
      obtain ⟨n, hn⟩ := h0
      have := (hstrip n).2; rw [← hn] at this; linarith
    have hld_diff : DifferentiableOn ℂ (fun z => deriv (weierstrassProduct ρ) z / weierstrassProduct ρ z)
        {z : ℂ | 1 < z.re} :=
      ((hW_diff.differentiableOn.deriv isOpen_univ).mono (Set.subset_univ _)).div
        (hW_diff.differentiableOn.mono (Set.subset_univ _)) (fun z hz => hW_nz z hz)
    have hev : (fun z : ℂ => ∑' n : ℕ, ((1 : ℂ) / (z - ρ n) + 1 / ρ n)) =ᶠ[𝓝 s]
        fun z => deriv (weierstrassProduct ρ) z / weierstrassProduct ρ z := by
      filter_upwards [hopen.mem_nhds hs] with z (hz : 1 < z.re)
      have hz_ne : ∀ n : ℕ, z ≠ ρ n := fun n h => by have := (hstrip n).2; rw [← h] at this; linarith
      exact (Stage5JensenHadamard.logDeriv_weierstrassProduct_eq_tsum
        (fun n h => by have := (hstrip n).1; rw [h, Complex.zero_re] at this; linarith) hsum hz_ne).symm
    exact ((hld_diff.analyticAt (hopen.mem_nhds hs)).congr hev.symm).contDiffAt.of_le le_top
  -- Helper: `ContDiffAt` for `digamma((z + a)/2)` on `1 < s.re`
  have hcd_dig : ∀ (a : ℝ), a = 0 ∨ a = 1 → ∀ {s : ℂ}, 1 < s.re → ∀ k : ℕ,
      ContDiffAt ℂ k (fun z : ℂ => Complex.digamma ((z + (a : ℂ)) / 2)) s := by
    intro a ha s hs k
    have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    have hdiff : DifferentiableOn ℂ (fun z : ℂ => Complex.digamma ((z + (a : ℂ)) / 2))
        {z : ℂ | 1 < z.re} := by
      refine differentiableOn_digamma_re_pos.comp
        ((differentiableOn_id.add (differentiableOn_const _)).div_const 2) ?_
      intro z (hz : 1 < z.re)
      show 0 < ((z + (a : ℂ)) / 2).re
      rcases ha with rfl | rfl <;> simp <;> linarith
    exact (hdiff.analyticAt (hopen.mem_nhds hs)).contDiffAt.of_le le_top
  -- Part 1: `negLogDerivZeta`
  have hzeta_bound : ∀ (s : ℂ), 1 < s.re → s.re ≤ 2 → ∀ k : ℕ, 1 ≤ k →
      ‖scaledDeriv k negLogDerivZeta s -
          (1 / (s - 1) ^ (k + 1) - ∑' n : ℕ, (1 : ℂ) / (s - xiZeroSeq n) ^ (k + 1))‖ ≤
        (C_dig + 4) * (2 : ℝ) ^ k * Real.log (|s.im| + 2) := by
    intro s hs1 hs2 k hk
    have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    have hev : negLogDerivZeta =ᶠ[𝓝 s]
        fun z => (1 / (z - 1) - xiHadamardB) -
          (∑' n : ℕ, (1 / (z - xiZeroSeq n) + 1 / xiZeroSeq n)) +
          ((1 / z - ((Real.log Real.pi / 2 : ℝ) : ℂ)) + (1 / 2 : ℂ) * Complex.digamma (z / 2)) := by
      filter_upwards [hopen.mem_nhds hs1] with z hz
      exact negLogDerivZeta_eq_hadamard_partialFraction hz
    have hs1_ne : s ≠ 1 := fun h => by simp [h] at hs1
    have hs0_ne : s ≠ 0 := fun h => by simp [h] at hs1; linarith
    have hcd1 : ContDiffAt ℂ k (fun z : ℂ => (1 : ℂ) / (z - 1)) s := by
      have : (fun z : ℂ => (1 : ℂ) / (z - 1)) = fun z : ℂ => (z - 1)⁻¹ := by ext z; rw [one_div]
      rw [this]; exact (contDiffAt_id.sub contDiffAt_const).inv (sub_ne_zero.mpr hs1_ne)
    have hcd0 : ContDiffAt ℂ k (fun z : ℂ => (1 : ℂ) / z) s := by
      have : (fun z : ℂ => (1 : ℂ) / z) = fun z : ℂ => z⁻¹ := by ext z; rw [one_div]
      rw [this]; exact contDiffAt_id.inv hs0_ne
    have hcd_sum := hcd_tsum xiZeroSeq_strip xiZeroSeq_summable_inv_sq hs1 k
    have hcd_d0 : ContDiffAt ℂ k (fun z : ℂ => Complex.digamma (z / 2)) s := by
      simpa using hcd_dig 0 (.inl rfl) hs1 k
    rw [scaledDeriv_congr_nhds hev,
      scaledDeriv_add ((hcd1.sub contDiffAt_const).sub hcd_sum)
        ((hcd0.sub contDiffAt_const).add (contDiffAt_const.mul hcd_d0)),
      scaledDeriv_sub (hcd1.sub contDiffAt_const) hcd_sum,
      scaledDeriv_sub hcd1 contDiffAt_const,
      scaledDeriv_add (hcd0.sub contDiffAt_const) (contDiffAt_const.mul hcd_d0),
      scaledDeriv_sub hcd0 contDiffAt_const,
      scaledDeriv_const_mul,
      scaledDeriv_const_eq_zero hk, scaledDeriv_const_eq_zero hk,
      scaledDeriv_inv_sub 1 k hs1_ne,
      scaledDeriv_hadamard_tsum_eq xiZeroSeq_strip xiZeroSeq_summable_inv_sq hs1 hk]
    have hsd0 : scaledDeriv k (fun z : ℂ => (1 : ℂ) / z) s = (1 : ℂ) / s ^ (k + 1) := by
      simpa using scaledDeriv_inv_sub 0 k hs0_ne
    rw [hsd0, sub_zero, sub_zero, add_sub_cancel_left]
    have hnorm_s : 1 ≤ ‖s‖ := by
      have := (le_abs_self s.re).trans (Complex.abs_re_le_norm s); linarith
    have hinv_s : ‖(1 : ℂ) / s ^ (k + 1)‖ ≤ 1 := by
      rw [norm_div, norm_one, norm_pow]
      exact (div_le_one (pow_pos (by linarith) _)).mpr (one_le_pow₀ hnorm_s)
    have hdig_bd := hdig_sd 0 (.inl rfl) s hs1 hs2 k
    simp only [Complex.ofReal_zero, add_zero] at hdig_bd
    have hlog_ge : (1 / 2 : ℝ) < Real.log (|s.im| + 2) :=
      hlog2_half.trans_le (Real.log_le_log (by norm_num) (by linarith [abs_nonneg s.im]))
    have h2k_ge : (1 : ℝ) ≤ (2 : ℝ) ^ k := one_le_pow₀ (by norm_num)
    have hprod_ge : (1 / 2 : ℝ) ≤ (2 : ℝ) ^ k * Real.log (|s.im| + 2) := by nlinarith
    calc ‖(1 : ℂ) / s ^ (k + 1) + (1 / 2 : ℂ) * scaledDeriv k (fun z => Complex.digamma (z / 2)) s‖
        ≤ ‖(1 : ℂ) / s ^ (k + 1)‖ + ‖(1 / 2 : ℂ) * scaledDeriv k (fun z => Complex.digamma (z / 2)) s‖ :=
          norm_add_le _ _
      _ ≤ 1 + (1 / 2 : ℝ) * (C_dig * (2 : ℝ) ^ k * Real.log (|s.im| + 2)) := by
          rw [norm_mul, show ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) by norm_num]
          exact add_le_add hinv_s (mul_le_mul_of_nonneg_left hdig_bd (by norm_num))
      _ ≤ (C_dig + 4) * (2 : ℝ) ^ k * Real.log (|s.im| + 2) := by
          have hmul_eq : (C_dig + 4) * (2 : ℝ) ^ k * Real.log (|s.im| + 2) =
              C_dig * ((2 : ℝ) ^ k * Real.log (|s.im| + 2)) + 4 * ((2 : ℝ) ^ k * Real.log (|s.im| + 2)) := by ring
          have hmul_eq2 : C_dig * (2 : ℝ) ^ k * Real.log (|s.im| + 2) =
              C_dig * ((2 : ℝ) ^ k * Real.log (|s.im| + 2)) := by ring
          rw [hmul_eq, hmul_eq2]; nlinarith
  -- Part 2: primitive `ψ ≠ 1`
  have hprim_bound : ∀ {f : ℕ} [NeZero f] (ψ : DirichletCharacter ℂ f)
      (hprim : ψ.IsPrimitive) (hψ : ψ ≠ 1) (s : ℂ), 1 < s.re → s.re ≤ 2 → ∀ k : ℕ, 1 ≤ k →
      ‖scaledDeriv k (negLogDerivL ψ) s -
          (- ∑' n : ℕ, (1 : ℂ) / (s - completedLZeroSeq hprim hψ n) ^ (k + 1))‖ ≤
        (C_dig + 4) * (2 : ℝ) ^ k * Real.log (|s.im| + 2) := by
    intro f _ ψ hprim hψ s hs1 hs2 k hk
    have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    have hcd_sum := hcd_tsum (completedLZeroSeq_strip hprim hψ)
      (completedLZeroSeq_summable_inv_sq hprim hψ) hs1 k
    rcases ψ.even_or_odd with he | ho
    · have hev : negLogDerivL ψ =ᶠ[𝓝 s]
          fun z => ((0 : ℂ) - symmetricCompletedLHadamardB ψ) -
            (∑' n : ℕ, (1 / (z - completedLZeroSeq hprim hψ n) + 1 / completedLZeroSeq hprim hψ n)) +
            ((((Real.log (f : ℝ) / 2 : ℝ) : ℂ) - ((Real.log Real.pi / 2 : ℝ) : ℂ)) +
              (1 / 2 : ℂ) * Complex.digamma (z / 2)) := by
        filter_upwards [hopen.mem_nhds hs1] with z (hz : 1 < z.re)
        rw [negLogDerivL_prim_eq_hadamard_partialFraction hprim hψ hz,
          logDeriv_gammaFactor_even he (by linarith)]
        ring
      have hcd_d0 : ContDiffAt ℂ k (fun z : ℂ => Complex.digamma (z / 2)) s := by
        simpa using hcd_dig 0 (.inl rfl) hs1 k
      rw [scaledDeriv_congr_nhds hev,
        scaledDeriv_add (contDiffAt_const.sub hcd_sum)
          (contDiffAt_const.add (contDiffAt_const.mul hcd_d0)),
        scaledDeriv_sub contDiffAt_const hcd_sum,
        scaledDeriv_add contDiffAt_const (contDiffAt_const.mul hcd_d0),
        scaledDeriv_const_mul,
        scaledDeriv_const_eq_zero hk, scaledDeriv_const_eq_zero hk,
        scaledDeriv_hadamard_tsum_eq (completedLZeroSeq_strip hprim hψ)
          (completedLZeroSeq_summable_inv_sq hprim hψ) hs1 hk]
      simp only [zero_sub, zero_add, add_sub_cancel_left]
      have hdig_bd := hdig_sd 0 (.inl rfl) s hs1 hs2 k
      simp only [Complex.ofReal_zero, add_zero] at hdig_bd
      rw [norm_mul, show ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) by norm_num]
      have hprod_nn : 0 ≤ (2 : ℝ) ^ k * Real.log (|s.im| + 2) :=
        mul_nonneg (by positivity) (Real.log_nonneg (by linarith [abs_nonneg s.im]))
      linarith [mul_le_mul_of_nonneg_left hdig_bd (by norm_num : (0 : ℝ) ≤ 1 / 2),
        show (C_dig + 4) * (2 : ℝ) ^ k * Real.log (|s.im| + 2) -
          (1 / 2) * (C_dig * (2 : ℝ) ^ k * Real.log (|s.im| + 2)) =
          (C_dig / 2 + 4) * ((2 : ℝ) ^ k * Real.log (|s.im| + 2)) by ring,
        mul_nonneg (by linarith : (0 : ℝ) ≤ C_dig / 2 + 4) hprod_nn]
    · have hev : negLogDerivL ψ =ᶠ[𝓝 s]
          fun z => ((0 : ℂ) - symmetricCompletedLHadamardB ψ) -
            (∑' n : ℕ, (1 / (z - completedLZeroSeq hprim hψ n) + 1 / completedLZeroSeq hprim hψ n)) +
            ((((Real.log (f : ℝ) / 2 : ℝ) : ℂ) - ((Real.log Real.pi / 2 : ℝ) : ℂ)) +
              (1 / 2 : ℂ) * Complex.digamma ((z + (1 : ℝ)) / 2)) := by
        filter_upwards [hopen.mem_nhds hs1] with z (hz : 1 < z.re)
        rw [negLogDerivL_prim_eq_hadamard_partialFraction hprim hψ hz,
          logDeriv_gammaFactor_odd ho (by linarith)]
        push_cast; ring
      have hcd_d1 : ContDiffAt ℂ k (fun z : ℂ => Complex.digamma ((z + (1 : ℝ)) / 2)) s :=
        hcd_dig 1 (.inr rfl) hs1 k
      rw [scaledDeriv_congr_nhds hev,
        scaledDeriv_add (contDiffAt_const.sub hcd_sum)
          (contDiffAt_const.add (contDiffAt_const.mul hcd_d1)),
        scaledDeriv_sub contDiffAt_const hcd_sum,
        scaledDeriv_add contDiffAt_const (contDiffAt_const.mul hcd_d1),
        scaledDeriv_const_mul,
        scaledDeriv_const_eq_zero hk, scaledDeriv_const_eq_zero hk,
        scaledDeriv_hadamard_tsum_eq (completedLZeroSeq_strip hprim hψ)
          (completedLZeroSeq_summable_inv_sq hprim hψ) hs1 hk]
      simp only [zero_sub, zero_add, add_sub_cancel_left]
      have hdig_bd := hdig_sd 1 (.inr rfl) s hs1 hs2 k
      rw [norm_mul, show ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) by norm_num]
      have hprod_nn : 0 ≤ (2 : ℝ) ^ k * Real.log (|s.im| + 2) :=
        mul_nonneg (by positivity) (Real.log_nonneg (by linarith [abs_nonneg s.im]))
      linarith [mul_le_mul_of_nonneg_left hdig_bd (by norm_num : (0 : ℝ) ≤ 1 / 2),
        show (C_dig + 4) * (2 : ℝ) ^ k * Real.log (|s.im| + 2) -
          (1 / 2) * (C_dig * (2 : ℝ) ^ k * Real.log (|s.im| + 2)) =
          (C_dig / 2 + 4) * ((2 : ℝ) ^ k * Real.log (|s.im| + 2)) by ring,
        mul_nonneg (by linarith : (0 : ℝ) ≤ C_dig / 2 + 4) hprod_nn]
  refine ⟨C_E, hC_E_pos, ?_, ?_⟩
  · intro s hs1 hs2 k hk
    have hprod_nn : 0 ≤ (2 : ℝ) ^ k * Real.log (|s.im| + 2) :=
      mul_nonneg (by positivity) (Real.log_nonneg (by linarith [abs_nonneg s.im]))
    exact (hzeta_bound s hs1 hs2 k hk).trans (by
      dsimp only [C_E]
      linarith [show (C_dig + 8) * (2 : ℝ) ^ k * Real.log (|s.im| + 2) -
          (C_dig + 4) * (2 : ℝ) ^ k * Real.log (|s.im| + 2) =
          4 * ((2 : ℝ) ^ k * Real.log (|s.im| + 2)) by ring])
  · intro q _ χ s hs1 hs2 k hk
    have hq_ge1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast NeZero.pos q
    have hq_pos : (0 : ℝ) < (q : ℝ) := by linarith
    have hlog_q : Real.log (q : ℝ) ≤ Real.log ((q : ℝ) * (|s.im| + 2)) :=
      Real.log_le_log hq_pos (by nlinarith [abs_nonneg s.im])
    have hlog_t : Real.log (|s.im| + 2) ≤ Real.log ((q : ℝ) * (|s.im| + 2)) :=
      Real.log_le_log (by linarith [abs_nonneg s.im]) (by nlinarith [abs_nonneg s.im])
    have h2k_nn : (0 : ℝ) ≤ (2 : ℝ) ^ k := by positivity
    have hlog_nn : 0 ≤ Real.log ((q : ℝ) * (|s.im| + 2)) :=
      Real.log_nonneg (by nlinarith [abs_nonneg s.im])
    have h2k_q : (2 : ℝ) ^ k * Real.log (q : ℝ) ≤ (2 : ℝ) ^ k * Real.log ((q : ℝ) * (|s.im| + 2)) :=
      mul_le_mul_of_nonneg_left hlog_q h2k_nn
    have h2k_t : (2 : ℝ) ^ k * Real.log (|s.im| + 2) ≤ (2 : ℝ) ^ k * Real.log ((q : ℝ) * (|s.im| + 2)) :=
      mul_le_mul_of_nonneg_left hlog_t h2k_nn
    have h2k_qt_nn : 0 ≤ (2 : ℝ) ^ k * Real.log ((q : ℝ) * (|s.im| + 2)) := mul_nonneg h2k_nn hlog_nn
    have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
    have heuler := norm_scaledDeriv_euler_diff_le χ hs1 k
    have hsplit_sd : scaledDeriv k (negLogDerivL χ) s =
        scaledDeriv k (negLogDerivL χ.primitiveCharacter) s +
          scaledDeriv k (fun z => negLogDerivL χ z - negLogDerivL χ.primitiveCharacter z) s := by
      rw [scaledDeriv_sub (hcd_L χ hs1 k) (hcd_L χ.primitiveCharacter hs1 k)]; ring
    constructor
    · intro hχ1
      have hprim_eq_zeta : negLogDerivL χ.primitiveCharacter = negLogDerivZeta := by
        have hcond1 : χ.conductor = 1 := by rw [hχ1, DirichletCharacter.conductor_one]
        have hfun : DirichletCharacter.LFunction χ.primitiveCharacter = riemannZeta := by
          have h1 : ∀ (d : ℕ) [NeZero d] (φ : DirichletCharacter ℂ d), d = 1 →
              DirichletCharacter.LFunction φ = riemannZeta := by
            intro d _ φ hd; subst hd
            obtain rfl := DirichletCharacter.level_one φ
            exact DirichletCharacter.LFunction_modOne_eq
          exact h1 χ.conductor χ.primitiveCharacter hcond1
        ext z; unfold negLogDerivL negLogDerivZeta; rw [hfun]
      rw [hprim_eq_zeta] at heuler
      rw [hsplit_sd, hprim_eq_zeta]
      have hrew :
          scaledDeriv k negLogDerivZeta s +
              scaledDeriv k (fun z => negLogDerivL χ z - negLogDerivZeta z) s -
              (1 / (s - 1) ^ (k + 1) - ∑' n : ℕ, (1 : ℂ) / (s - xiZeroSeq n) ^ (k + 1)) =
            (scaledDeriv k negLogDerivZeta s -
                (1 / (s - 1) ^ (k + 1) - ∑' n : ℕ, (1 : ℂ) / (s - xiZeroSeq n) ^ (k + 1))) +
              scaledDeriv k (fun z => negLogDerivL χ z - negLogDerivZeta z) s := by ring
      rw [hrew]
      have htri := norm_add_le
        (scaledDeriv k negLogDerivZeta s -
          (1 / (s - 1) ^ (k + 1) - ∑' n : ℕ, (1 : ℂ) / (s - xiZeroSeq n) ^ (k + 1)))
        (scaledDeriv k (fun z => negLogDerivL χ z - negLogDerivZeta z) s)
      have hzbd := hzeta_bound s hs1 hs2 k hk
      have h1 : (C_dig + 4) * (2 : ℝ) ^ k * Real.log (|s.im| + 2) ≤
          (C_dig + 4) * (2 : ℝ) ^ k * Real.log ((q : ℝ) * (|s.im| + 2)) := by
        rw [mul_assoc, mul_assoc]; exact mul_le_mul_of_nonneg_left h2k_t (by linarith)
      have h2 : 3 * (2 : ℝ) ^ k * Real.log (q : ℝ) ≤
          3 * (2 : ℝ) ^ k * Real.log ((q : ℝ) * (|s.im| + 2)) := by
        rw [mul_assoc, mul_assoc]; exact mul_le_mul_of_nonneg_left h2k_q (by norm_num)
      dsimp only [C_E]
      linarith [show (C_dig + 8) * (2 : ℝ) ^ k * Real.log ((q : ℝ) * (|s.im| + 2)) -
          ((C_dig + 4) * (2 : ℝ) ^ k * Real.log ((q : ℝ) * (|s.im| + 2)) +
            3 * (2 : ℝ) ^ k * Real.log ((q : ℝ) * (|s.im| + 2))) =
          (2 : ℝ) ^ k * Real.log ((q : ℝ) * (|s.im| + 2)) by ring]
    · intro hχne
      dsimp only
      have hψ : χ.primitiveCharacter ≠ 1 := fun h1 => hχne (by
        rw [← χ.changeLevel_primitiveCharacter, h1, map_one])
      rw [hsplit_sd]
      have hrew :
          scaledDeriv k (negLogDerivL χ.primitiveCharacter) s +
              scaledDeriv k (fun z => negLogDerivL χ z - negLogDerivL χ.primitiveCharacter z) s -
              (- ∑' n : ℕ, (1 : ℂ) / (s - completedLZeroSeq χ.primitiveCharacter_isPrimitive hψ n) ^ (k + 1)) =
            (scaledDeriv k (negLogDerivL χ.primitiveCharacter) s -
                (- ∑' n : ℕ, (1 : ℂ) / (s - completedLZeroSeq χ.primitiveCharacter_isPrimitive hψ n) ^ (k + 1))) +
              scaledDeriv k (fun z => negLogDerivL χ z - negLogDerivL χ.primitiveCharacter z) s := by ring
      rw [hrew]
      have htri := norm_add_le
        (scaledDeriv k (negLogDerivL χ.primitiveCharacter) s -
          (- ∑' n : ℕ, (1 : ℂ) / (s - completedLZeroSeq χ.primitiveCharacter_isPrimitive hψ n) ^ (k + 1)))
        (scaledDeriv k (fun z => negLogDerivL χ z - negLogDerivL χ.primitiveCharacter z) s)
      have hpbd := hprim_bound χ.primitiveCharacter χ.primitiveCharacter_isPrimitive hψ s hs1 hs2 k hk
      have h1 : (C_dig + 4) * (2 : ℝ) ^ k * Real.log (|s.im| + 2) ≤
          (C_dig + 4) * (2 : ℝ) ^ k * Real.log ((q : ℝ) * (|s.im| + 2)) := by
        rw [mul_assoc, mul_assoc]; exact mul_le_mul_of_nonneg_left h2k_t (by linarith)
      have h2 : 3 * (2 : ℝ) ^ k * Real.log (q : ℝ) ≤
          3 * (2 : ℝ) ^ k * Real.log ((q : ℝ) * (|s.im| + 2)) := by
        rw [mul_assoc, mul_assoc]; exact mul_le_mul_of_nonneg_left h2k_q (by norm_num)
      dsimp only [C_E]
      linarith [show (C_dig + 8) * (2 : ℝ) ^ k * Real.log ((q : ℝ) * (|s.im| + 2)) -
          ((C_dig + 4) * (2 : ℝ) ^ k * Real.log ((q : ℝ) * (|s.im| + 2)) +
            3 * (2 : ℝ) ^ k * Real.log ((q : ℝ) * (|s.im| + 2))) =
          (2 : ℝ) ^ k * Real.log ((q : ℝ) * (|s.im| + 2)) by ring]

/-! ## Section 4: Unified `PChar` Zero Sequences, Simplicity of Siegel Zeros, Klein-Four Orbit, & Extremal-Zero Iteration -/

open Classical in
/-- Unified multiplicity-counted critical-strip zero sequence for any primitive character `ψ : PChar`
(`xiZeroSeq` when `ψ.χ = 1`, and `completedLZeroSeq ψ.prim hψ` when `ψ.χ ≠ 1`). -/
def pcharZeroSeq (ψ : PChar) : ℕ → ℂ :=
  if h : ψ.χ = 1 then xiZeroSeq else completedLZeroSeq ψ.prim h

lemma pcharZeroSeq_one : pcharZeroSeq PChar.one = xiZeroSeq := by
  unfold pcharZeroSeq; exact dif_pos rfl

lemma pcharZeroSeq_of_ne_one {ψ : PChar} (h : ψ.χ ≠ 1) :
    pcharZeroSeq ψ = completedLZeroSeq ψ.prim h := by
  unfold pcharZeroSeq; exact dif_neg h

lemma pcharZeroSeq_strip (ψ : PChar) (n : ℕ) :
    0 < (pcharZeroSeq ψ n).re ∧ (pcharZeroSeq ψ n).re < 1 := by
  unfold pcharZeroSeq
  split_ifs with h
  · exact xiZeroSeq_strip n
  · exact completedLZeroSeq_strip ψ.prim h n

lemma pcharZeroSeq_summable_inv_sq (ψ : PChar) :
    Summable (fun n : ℕ => (‖pcharZeroSeq ψ n‖ ^ 2)⁻¹) := by
  unfold pcharZeroSeq
  split_ifs with h
  · exact xiZeroSeq_summable_inv_sq
  · exact completedLZeroSeq_summable_inv_sq ψ.prim h

lemma pchar_eq_one_iff_chi_eq_one (ψ : PChar) : ψ = PChar.one ↔ ψ.χ = 1 := by
  constructor
  · rintro rfl; rfl
  · intro h
    have hcond : ψ.N = 1 := by
      have h1 : ψ.χ.conductor = ψ.N := ψ.prim
      rw [h, DirichletCharacter.conductor_one] at h1
      exact h1.symm
    have haux : ∀ (d : ℕ) [NeZero d] (φ : DirichletCharacter ℂ d) (hp : φ.IsPrimitive),
        d = 1 → PChar.mk d φ hp = PChar.one := by
      intro d _ φ hp hd; subst hd
      obtain rfl := DirichletCharacter.level_one φ
      rfl
    cases ψ with | mk N χ prim => exact haux N χ prim hcond

lemma pcharZeroSeq_LFunction_zero (ψ : PChar) (n : ℕ) :
    DirichletCharacter.LFunction ψ.χ (pcharZeroSeq ψ n) = 0 := by
  unfold pcharZeroSeq
  split_ifs with h
  · have h1 : ψ = PChar.one := (pchar_eq_one_iff_chi_eq_one ψ).mpr h
    rw [h1]
    change DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 1) (xiZeroSeq n) = 0
    rw [DirichletCharacter.LFunction_modOne_eq]
    exact xiZeroSeq_riemannZeta_zero n
  · exact completedLZeroSeq_LFunction_zero ψ.prim h n

lemma exists_pcharZeroSeq_eq (ψ : PChar) {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1)
    (hz : DirichletCharacter.LFunction ψ.χ ρ = 0) :
    ∃ n : ℕ, pcharZeroSeq ψ n = ρ := by
  unfold pcharZeroSeq
  split_ifs with h
  · have hψ1 : ψ = PChar.one := (pchar_eq_one_iff_chi_eq_one ψ).mpr h
    rw [hψ1] at hz
    change DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 1) ρ = 0 at hz
    rw [DirichletCharacter.LFunction_modOne_eq] at hz
    exact isMultiplicityZeroSeq_xi.exists_of_eq_zero Stage5StirlingPhragmen.differentiable_xi (by simp)
      ((Stage5StirlingPhragmen.xi_eq_zero_iff_critical_strip_zeta_zero ρ).mpr ⟨h0, h1, hz⟩)
  · exact (isMultiplicityZeroSeq_completedLFunction ψ.prim h).exists_of_eq_zero
      (differentiable_completedLFunction_prim h) (completedLFunction_zero_ne_zero ψ.prim h)
      ((completedLFunction_eq_zero_iff_critical_strip_LFunction_zero ψ.prim h ρ).mpr ⟨h0, h1, hz⟩)

/-- **Simplicity of a Siegel Zero**: if `(1 - β₁) * Real.log (2 * q₁) < 1 / (12 * C_H)`, then
`β₁` occurs at a UNIQUE index `n₁ : ℕ` in `completedLZeroSeq hprim₁ hχ₁`! -/
private lemma siegel_zero_unique_index {C_H : ℝ} (hC_H : 0 < C_H)
    (hZ_bd : ∀ σ t : ℝ, 1 < σ → σ ≤ 2 → ∀ F : Finset ℕ,
      (negLogDerivZeta ((σ : ℂ) + I * (t : ℂ))).re ≤
        C_H * Real.log (|t| + 2) + (1 / (((σ : ℂ) + I * (t : ℂ)) - 1)).re -
          ∑ n ∈ F, (1 / (((σ : ℂ) + I * (t : ℂ)) - xiZeroSeq n)).re)
    (hL_bd : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (hprim : χ.IsPrimitive) (hχ : χ ≠ 1),
      ∀ σ t : ℝ, 1 < σ → σ ≤ 2 → ∀ F : Finset ℕ,
        (negLogDerivL χ ((σ : ℂ) + I * (t : ℂ))).re ≤
          C_H * Real.log ((q : ℝ) * (|t| + 2)) -
            ∑ n ∈ F, (1 / (((σ : ℂ) + I * (t : ℂ)) - completedLZeroSeq hprim hχ n)).re)
    {q₁ : ℕ} [NeZero q₁] {χ₁ : DirichletCharacter ℂ q₁}
    (hprim₁ : χ₁.IsPrimitive) (hχ₁ : χ₁ ≠ 1)
    {β₁ : ℝ} (hβ₁_lo : 1 / 2 < β₁) (hβ₁_hi : β₁ < 1)
    (hsmall : (1 - β₁) * Real.log (2 * (q₁ : ℝ)) < 1 / (12 * C_H))
    {n₁ n₂ : ℕ}
    (hn₁ : completedLZeroSeq hprim₁ hχ₁ n₁ = (β₁ : ℂ))
    (hn₂ : completedLZeroSeq hprim₁ hχ₁ n₂ = (β₁ : ℂ)) :
    n₁ = n₂ := by
  by_contra hne
  set δ : ℝ := 1 - β₁
  have hδ_pos : 0 < δ := by dsimp only [δ]; linarith
  have hδ_lt : δ < 1 / 2 := by dsimp only [δ]; linarith
  set σ : ℝ := 1 + 2 * δ
  have hσ1 : 1 < σ := by dsimp only [σ]; linarith
  have hσ2 : σ ≤ 2 := by dsimp only [σ]; linarith
  have hpos : 0 ≤ (negLogDerivZeta (σ : ℂ) + negLogDerivL χ₁ (σ : ℂ)).re := by
    have hs : 1 < (σ : ℂ).re := by simpa using hσ1
    rw [negLogDerivZeta_eq_LSeries hs, negLogDerivL_eq_LSeries χ₁ hs]
    have hsumZ := ArithmeticFunction.LSeriesSummable_vonMangoldt hs
    have hsum1 : LSeriesSummable (fun n => χ₁ n * (Λ n : ℂ)) (σ : ℂ) :=
      χ₁.LSeriesSummable_twist_vonMangoldt hs
    unfold LSeries
    rw [← Summable.tsum_add hsumZ hsum1, Complex.re_tsum (Summable.add hsumZ hsum1)]
    refine tsum_nonneg fun n => ?_
    rcases eq_or_ne n 0 with rfl | hn
    · simp [LSeries.term_zero]
    · have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
      rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn]
      have hcpow : (n : ℂ) ^ (σ : ℂ) = (((n : ℝ) ^ σ : ℝ) : ℂ) := by
        rw [← Complex.ofReal_natCast, Complex.ofReal_cpow hn_pos.le]
      rw [hcpow, ← add_div, show (Λ n : ℂ) + χ₁ (n : ZMod q₁) * (Λ n : ℂ) =
          (((Λ n : ℝ) : ℂ)) * (1 + χ₁ (n : ZMod q₁)) by ring,
        div_eq_mul_inv, mul_assoc, mul_comm (1 + χ₁ (n : ZMod q₁)), ← mul_assoc,
        ← Complex.ofReal_inv, ← Complex.ofReal_mul, Complex.re_ofReal_mul, Complex.add_re,
        Complex.one_re]
      have h1 := (isRealChar_apply_re_bounds (χ := χ₁) (n : ZMod q₁)).1
      exact mul_nonneg (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity)) (by linarith)
  have hZ := hZ_bd σ 0 hσ1 hσ2 ∅
  have hL := hL_bd q₁ χ₁ hprim₁ hχ₁ σ 0 hσ1 hσ2 {n₁, n₂}
  simp only [Finset.sum_empty, sub_zero, abs_zero, zero_add, Complex.ofReal_zero, mul_zero,
    add_zero] at hZ hL
  rw [Finset.sum_pair hne, hn₁, hn₂] at hL
  have hpole : ((1 : ℂ) / ((σ : ℂ) - 1)).re = 1 / (2 * δ) := by
    have : (1 : ℂ) / ((σ : ℂ) - 1) = ((1 / (2 * δ) : ℝ) : ℂ) := by
      dsimp only [σ]; push_cast; ring_nf
    rw [this, Complex.ofReal_re]
  have hzero_term : ((1 : ℂ) / ((σ : ℂ) - (β₁ : ℂ))).re = 1 / (3 * δ) := by
    have : (1 : ℂ) / ((σ : ℂ) - (β₁ : ℂ)) = ((1 / (3 * δ) : ℝ) : ℂ) := by
      dsimp only [σ, δ]; push_cast; ring_nf
    rw [this, Complex.ofReal_re]
  rw [hpole] at hZ
  rw [hzero_term] at hL
  rw [Complex.add_re] at hpos
  have hq_ge1 : (1 : ℝ) ≤ (q₁ : ℝ) := by exact_mod_cast NeZero.pos q₁
  have hlog_le : Real.log 2 ≤ Real.log (2 * (q₁ : ℝ)) :=
    Real.log_le_log (by norm_num) (by linarith)
  have hqmul : (q₁ : ℝ) * 2 = 2 * (q₁ : ℝ) := by ring
  rw [hqmul] at hL
  have hcomb : 1 / (6 * δ) ≤ 2 * C_H * Real.log (2 * (q₁ : ℝ)) := by
    have hdiff : 1 / (3 * δ) + 1 / (3 * δ) - 1 / (2 * δ) = 1 / (6 * δ) := by
      field_simp [hδ_pos.ne']; ring
    linarith [mul_le_mul_of_nonneg_left hlog_le hC_H.le]
  have hmul := mul_le_mul_of_nonneg_left hcomb hδ_pos.le
  have hleft : δ * (1 / (6 * δ)) = 1 / 6 := by field_simp [hδ_pos.ne']
  rw [hleft] at hmul
  have h12 : δ * (2 * C_H * Real.log (2 * (q₁ : ℝ))) < 1 / 6 := by
    have h1 := mul_lt_mul_of_pos_left hsmall (by positivity : (0 : ℝ) < 2 * C_H)
    have h2 : 2 * C_H * (1 / (12 * C_H)) = 1 / 6 := by field_simp [hC_H.ne']; ring
    linarith
  linarith

/-- Helper: `PChar.of (changeLevel hd χ) = PChar.of χ`. -/
private lemma pchar_of_changeLevel_any {d N : ℕ} [NeZero d] [NeZero N] (hd : d ∣ N)
    (χ : DirichletCharacter ℂ d) :
    PChar.of (DirichletCharacter.changeLevel hd χ) = PChar.of χ := by
  have hdvd : χ.conductor ∣ N := χ.conductor_dvd_level.trans hd
  have hcond : (DirichletCharacter.changeLevel hd χ).conductor = χ.conductor :=
    DirichletCharacter.conductor_changeLevel χ hd
  have hchg : DirichletCharacter.changeLevel hd χ =
      DirichletCharacter.changeLevel hdvd χ.primitiveCharacter := by
    have h1 := (DirichletCharacter.changeLevel_trans χ.primitiveCharacter χ.conductor_dvd_level hd).symm
    rw [χ.changeLevel_primitiveCharacter] at h1
    exact h1
  have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have : NeZero (DirichletCharacter.changeLevel hd χ).conductor :=
    ⟨(DirichletCharacter.changeLevel hd χ).conductor_ne_zero⟩
  have haux : ∀ (e₁ e₂ : ℕ) [NeZero e₁] [NeZero e₂]
      (φ₁ : DirichletCharacter ℂ e₁) (φ₂ : DirichletCharacter ℂ e₂)
      (h1 : e₁ ∣ N) (h2 : e₂ ∣ N) (he : e₁ = e₂)
      (heq : DirichletCharacter.changeLevel h1 φ₁ = DirichletCharacter.changeLevel h2 φ₂)
      (p1 : φ₁.IsPrimitive) (p2 : φ₂.IsPrimitive),
      PChar.mk e₁ φ₁ p1 = PChar.mk e₂ φ₂ p2 := by
    intro e₁ e₂ _ _ φ₁ φ₂ h1 h2 he heq p1 p2
    subst he
    have hφ : φ₁ = φ₂ := DirichletCharacter.changeLevel_injective h1 heq
    subst hφ
    rfl
  exact haux _ _ _ _ (DirichletCharacter.changeLevel hd χ).conductor_dvd_level hdvd hcond
    ((DirichletCharacter.changeLevel hd χ).changeLevel_primitiveCharacter.trans hchg)
    (DirichletCharacter.changeLevel hd χ).primitiveCharacter_isPrimitive
    χ.primitiveCharacter_isPrimitive

/-- Helper: `changeLevel h2 (changeLevel h1 χ) = changeLevel (h1.trans h2) χ`. -/
private lemma changeLevel_comp_apply {a b c : ℕ} [NeZero a] [NeZero b] [NeZero c]
    (h1 : a ∣ b) (h2 : b ∣ c) (χ : DirichletCharacter ℂ a) :
    DirichletCharacter.changeLevel h2 (DirichletCharacter.changeLevel h1 χ) =
      DirichletCharacter.changeLevel (h1.trans h2) χ :=
  (DirichletCharacter.changeLevel_trans χ h1 h2).symm

/-- Helper: `PChar.of (prodChar (PChar.of χ).χ χ₁) = PChar.of (prodChar χ χ₁)`. -/
private lemma pchar_of_prodChar_of_left {q q₁ : ℕ} [NeZero q] [NeZero q₁]
    (χ : DirichletCharacter ℂ q) (χ₁ : DirichletCharacter ℂ q₁) :
    PChar.of (prodChar (PChar.of χ).χ χ₁) = PChar.of (prodChar χ χ₁) := by
  have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hdvd : (PChar.of χ).N * q₁ ∣ q * q₁ := Nat.mul_dvd_mul_right χ.conductor_dvd_level q₁
  have hlift : DirichletCharacter.changeLevel hdvd (prodChar (PChar.of χ).χ χ₁) = prodChar χ χ₁ := by
    unfold prodChar
    rw [map_mul, changeLevel_comp_apply, changeLevel_comp_apply]
    congr 1
    have h1 : DirichletCharacter.changeLevel (dvd_mul_right q q₁) χ =
        DirichletCharacter.changeLevel (χ.conductor_dvd_level.trans (dvd_mul_right q q₁))
          (PChar.of χ).χ := by
      have h2 := changeLevel_comp_apply χ.conductor_dvd_level (dvd_mul_right q q₁) χ.primitiveCharacter
      rw [χ.changeLevel_primitiveCharacter] at h2
      exact h2
    exact h1.symm
  rw [← hlift, pchar_of_changeLevel_any hdvd]

/-- Helper: `PChar.of (prodChar (prodChar χ χ₁) χ₁) = PChar.of χ` whenever `χ₁ ^ 2 = 1`. -/
private lemma pchar_of_prodChar_cancel_right {q q₁ : ℕ} [NeZero q] [NeZero q₁]
    (χ : DirichletCharacter ℂ q) {χ₁ : DirichletCharacter ℂ q₁} (hsq₁ : χ₁ ^ 2 = 1) :
    PChar.of (prodChar (prodChar χ χ₁) χ₁) = PChar.of χ := by
  have hmul_eq : prodChar (prodChar χ χ₁) χ₁ =
      DirichletCharacter.changeLevel ((dvd_mul_right q q₁).trans (dvd_mul_right (q * q₁) q₁)) χ := by
    unfold prodChar
    rw [map_mul, changeLevel_comp_apply, changeLevel_comp_apply]
    have hsq : DirichletCharacter.changeLevel
          ((dvd_mul_left q₁ q).trans (dvd_mul_right (q * q₁) q₁)) χ₁ *
        DirichletCharacter.changeLevel (dvd_mul_left q₁ (q * q₁)) χ₁ = 1 := by
      rw [← map_mul]
      have hmul1 : χ₁ * χ₁ = 1 := by rw [← sq, hsq₁]
      rw [hmul1, map_one]
    calc DirichletCharacter.changeLevel ((dvd_mul_right q q₁).trans (dvd_mul_right (q * q₁) q₁)) χ *
            DirichletCharacter.changeLevel ((dvd_mul_left q₁ q).trans (dvd_mul_right (q * q₁) q₁)) χ₁ *
          DirichletCharacter.changeLevel (dvd_mul_left q₁ (q * q₁)) χ₁
        = DirichletCharacter.changeLevel ((dvd_mul_right q q₁).trans (dvd_mul_right (q * q₁) q₁)) χ *
            (DirichletCharacter.changeLevel ((dvd_mul_left q₁ q).trans (dvd_mul_right (q * q₁) q₁)) χ₁ *
              DirichletCharacter.changeLevel (dvd_mul_left q₁ (q * q₁)) χ₁) := mul_assoc _ _ _
      _ = DirichletCharacter.changeLevel ((dvd_mul_right q q₁).trans (dvd_mul_right (q * q₁) q₁)) χ * 1 := by
            rw [hsq]
      _ = DirichletCharacter.changeLevel ((dvd_mul_right q q₁).trans (dvd_mul_right (q * q₁) q₁)) χ :=
            mul_one _
  rw [hmul_eq, pchar_of_changeLevel_any]

/-- Helper: `PChar.of (prodChar (1 : DirichletCharacter ℂ 1) χ₁) = PChar.of χ₁`. -/
private lemma pchar_of_prodChar_one_left {q₁ : ℕ} [NeZero q₁] (χ₁ : DirichletCharacter ℂ q₁) :
    PChar.of (prodChar (1 : DirichletCharacter ℂ 1) χ₁) = PChar.of χ₁ := by
  have heq : prodChar (1 : DirichletCharacter ℂ 1) χ₁ =
      DirichletCharacter.changeLevel (dvd_mul_left q₁ 1) χ₁ := by
    unfold prodChar
    rw [map_one]
    exact one_mul _
  rw [heq, pchar_of_changeLevel_any]

/-- Helper: `prodChar χ₁ χ₁ = 1` whenever `χ₁ ^ 2 = 1`. -/
private lemma prodChar_self_eq_one {q₁ : ℕ} [NeZero q₁] {χ₁ : DirichletCharacter ℂ q₁}
    (hsq₁ : χ₁ ^ 2 = 1) :
    prodChar χ₁ χ₁ = 1 := by
  unfold prodChar
  rw [← map_mul]
  have hmul1 : χ₁ * χ₁ = 1 := by rw [← sq, hsq₁]
  rw [hmul1, map_one]

/-- Helper: `prodChar ψ.χ χ₁ = 1 ↔ ψ = PChar.of χ₁` for primitive real `χ₁`. -/
private lemma prodChar_eq_one_iff_eq_pchar {q₁ : ℕ} [NeZero q₁] {χ₁ : DirichletCharacter ℂ q₁}
    (hsq₁ : χ₁ ^ 2 = 1) (ψ : PChar) :
    prodChar ψ.χ χ₁ = 1 ↔ ψ = PChar.of χ₁ := by
  constructor
  · intro h1
    have h2 : PChar.of (prodChar (prodChar ψ.χ χ₁) χ₁) = PChar.of ψ.χ :=
      pchar_of_prodChar_cancel_right ψ.χ hsq₁
    rw [h1, PChar.of_self] at h2
    have h3 : prodChar (1 : DirichletCharacter ℂ (ψ.N * q₁)) χ₁ =
        DirichletCharacter.changeLevel (dvd_mul_left q₁ (ψ.N * q₁)) χ₁ := by
      unfold prodChar; rw [map_one]; exact one_mul _
    rw [h3, pchar_of_changeLevel_any] at h2
    exact h2.symm
  · rintro rfl
    have hof1 : PChar.of (prodChar (PChar.of χ₁).χ χ₁) = PChar.one := by
      rw [pchar_of_prodChar_of_left, prodChar_self_eq_one hsq₁, PChar.of_one]
    have hprim1 : (prodChar (PChar.of χ₁).χ χ₁).primitiveCharacter = 1 := by
      have h := (pchar_eq_one_iff_chi_eq_one (PChar.of (prodChar (PChar.of χ₁).χ χ₁))).mp hof1
      exact h
    rw [← (prodChar (PChar.of χ₁).χ χ₁).changeLevel_primitiveCharacter, hprim1, map_one]

/-- **Unified Non-Exceptional Classical Zero-Free Region (`0` ASSUMPTIONS!)**:
there exists `c_cl > 0` such that for any `Q ≥ 2`, `T ≥ 2`, `H ≥ 2`, real primitive `χ₁ mod q₁`
(`q₁ ≤ Q`, `χ₁ ≠ 1`), real zero `β₁ ∈ (1/2, 1)` of `L(χ₁, ·)` with `(1 - β₁) * log(Q * T) ≤ c_cl / 4`,
and ANY `ψ : PChar` with `ψ.N ≤ Q * Q` and critical-strip zero `ρ` of `L(ψ.χ, ·)` with `|ρ.im| ≤ H`
and `(ρ ≠ β₁ ∨ ψ ≠ PChar.of χ₁)`:
`c_cl / Real.log ((Q : ℝ) ^ 2 * (H + 2)) ≤ 1 - ρ.re`. -/
private lemma classical_nonexceptional_zeroFree_orbit :
    ∃ c_cl : ℝ, 0 < c_cl ∧
      ∀ (Q : ℕ) (T H : ℝ), 2 ≤ Q → 2 ≤ T → 2 ≤ H →
      ∀ (q₁ : ℕ) [NeZero q₁] (χ₁ : DirichletCharacter ℂ q₁),
        q₁ ≤ Q → χ₁.IsPrimitive → χ₁ ^ 2 = 1 → χ₁ ≠ 1 →
      ∀ β₁ : ℝ, 1 / 2 < β₁ → β₁ < 1 → DirichletCharacter.LFunction χ₁ (β₁ : ℂ) = 0 →
        (1 - β₁) * Real.log ((Q : ℝ) * T) ≤ c_cl / 4 →
      ∀ (ψ : PChar) (ρ : ℂ), ψ.N ≤ Q * Q → |ρ.im| ≤ H →
        0 < ρ.re → ρ.re < 1 → DirichletCharacter.LFunction ψ.χ ρ = 0 →
        (ρ ≠ (β₁ : ℂ) ∨ ψ ≠ PChar.of χ₁) →
        c_cl / Real.log ((Q : ℝ) ^ 2 * (H + 2)) ≤ 1 - ρ.re := by
  obtain ⟨c_z, hc_z, hzf_z⟩ := Stage5ZetaZeroFree.riemannZeta_deLaValleePoussin_zeroFree
  obtain ⟨c_L, hc_L, hzf_L⟩ := Stage8HadamardLFunction.zeroFreeRegion_nonexceptional_unconditional
  obtain ⟨c_P, hc_P, _, hpage_uniq⟩ := Stage7SiegelWalfisz.page_at_most_one_siegel_zero_unconditional
  set c_cl : ℝ := min c_z (min c_L c_P)
  have hc_pos : 0 < c_cl := lt_min hc_z (lt_min hc_L hc_P)
  refine ⟨c_cl, hc_pos, fun Q T H hQ hT hH q₁ _ χ₁ hq₁ hprim₁ hsq₁ hχ₁ β₁ hβ₁0 hβ₁1 hz₁ hsmall ψ ρ hN hIm hre0 hre1 hzρ hne => ?_⟩
  have hQR : (2 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ
  have hQ2_ge4 : (4 : ℝ) ≤ (Q : ℝ) ^ 2 := by nlinarith
  have hL_pos : 0 < Real.log ((Q : ℝ) ^ 2 * (H + 2)) :=
    Real.log_pos (by nlinarith)
  by_cases hψ1 : ψ.χ = 1
  · have hψ_eq : ψ = PChar.one := (pchar_eq_one_iff_chi_eq_one ψ).mpr hψ1
    rw [hψ_eq] at hzρ
    change DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 1) ρ = 0 at hzρ
    rw [DirichletCharacter.LFunction_modOne_eq] at hzρ
    have hne1 : ρ ≠ 1 := fun h => by rw [h, Complex.one_re] at hre1; linarith
    have hlt : ρ.re < 1 - c_z / Real.log (|ρ.im| + 2) := by
      by_contra hge; push Not at hge
      exact hzf_z ρ hge hne1 hzρ
    have hlog_le : Real.log (|ρ.im| + 2) ≤ Real.log ((Q : ℝ) ^ 2 * (H + 2)) :=
      Real.log_le_log (by linarith [abs_nonneg ρ.im]) (by nlinarith [abs_nonneg ρ.im])
    have hlog_p : 0 < Real.log (|ρ.im| + 2) := Real.log_pos (by linarith [abs_nonneg ρ.im])
    have hdiv : c_cl / Real.log ((Q : ℝ) ^ 2 * (H + 2)) ≤ c_z / Real.log (|ρ.im| + 2) := by
      calc c_cl / Real.log ((Q : ℝ) ^ 2 * (H + 2))
          ≤ c_z / Real.log ((Q : ℝ) ^ 2 * (H + 2)) :=
            div_le_div_of_nonneg_right (min_le_left _ _) hL_pos.le
        _ ≤ c_z / Real.log (|ρ.im| + 2) :=
            div_le_div_of_nonneg_left hc_z.le hlog_p hlog_le
    linarith
  · have hcase := hzf_L ψ.N ψ.χ hψ1 ρ hre0 hre1 hzρ
    rcases hcase with hgood | ⟨_, him0, hreal_exc⟩
    · have hNR : (ψ.N : ℝ) ≤ (Q : ℝ) ^ 2 := by
        have : (ψ.N : ℝ) ≤ ((Q * Q : ℕ) : ℝ) := by exact_mod_cast hN
        push_cast at this; linarith [sq (Q : ℝ)]
      have hN1 : (1 : ℝ) ≤ (ψ.N : ℝ) := by exact_mod_cast NeZero.pos ψ.N
      have hlog_p : 0 < Real.log ((ψ.N : ℝ) * (|ρ.im| + 2)) :=
        Real.log_pos (by nlinarith [abs_nonneg ρ.im])
      have hlog_le : Real.log ((ψ.N : ℝ) * (|ρ.im| + 2)) ≤ Real.log ((Q : ℝ) ^ 2 * (H + 2)) :=
        Real.log_le_log (by nlinarith [abs_nonneg ρ.im]) (by nlinarith [abs_nonneg ρ.im])
      have hdiv : c_cl / Real.log ((Q : ℝ) ^ 2 * (H + 2)) ≤
          c_L / Real.log ((ψ.N : ℝ) * (|ρ.im| + 2)) := by
        calc c_cl / Real.log ((Q : ℝ) ^ 2 * (H + 2))
            ≤ c_L / Real.log ((Q : ℝ) ^ 2 * (H + 2)) :=
              div_le_div_of_nonneg_right ((min_le_right _ _).trans (min_le_left _ _)) hL_pos.le
          _ ≤ c_L / Real.log ((ψ.N : ℝ) * (|ρ.im| + 2)) :=
              div_le_div_of_nonneg_left hc_L.le hlog_p hlog_le
      linarith
    · -- Real zero of `ψ.χ`: if `1 - ρ.re < c_cl / log(Q^2 (H + 2))`, Page's uniqueness forces `(ψ, ρ) = (PChar.of χ₁, β₁)`!
      by_contra hlt; push Not at hlt
      have hρ_eq : ρ = (ρ.re : ℂ) := Complex.ext rfl (by simpa using him0)
      have hzρ_real : DirichletCharacter.LFunction ψ.χ (ρ.re : ℂ) = 0 := by rwa [← hρ_eq]
      have hQ2_ge2 : 2 ≤ Q * Q := by nlinarith
      have hlog2Q2_pos : 0 < Real.log (2 * ((Q * Q : ℕ) : ℝ)) := by
        push_cast; exact Real.log_pos (by nlinarith)
      have hlog2Q2_le : Real.log (2 * ((Q * Q : ℕ) : ℝ)) ≤ Real.log ((Q : ℝ) ^ 2 * (H + 2)) := by
        push_cast; exact Real.log_le_log (by positivity) (by nlinarith)
      have hlog2Q2_le_3L : Real.log (2 * ((Q * Q : ℕ) : ℝ)) ≤ 3 * Real.log ((Q : ℝ) * T) := by
        have h1 : 2 * ((Q * Q : ℕ) : ℝ) ≤ ((Q : ℝ) * T) ^ 3 := by
          have ha : (2 : ℝ) ≤ (Q : ℝ) * T := by nlinarith
          have hb : (Q : ℝ) ^ 2 ≤ ((Q : ℝ) * T) ^ 2 :=
            pow_le_pow_left₀ (by positivity) (by nlinarith) 2
          calc 2 * ((Q * Q : ℕ) : ℝ) = 2 * (Q : ℝ) ^ 2 := by push_cast; ring
            _ ≤ ((Q : ℝ) * T) * ((Q : ℝ) * T) ^ 2 := mul_le_mul ha hb (by positivity) (by positivity)
            _ = ((Q : ℝ) * T) ^ 3 := by ring
        calc Real.log (2 * ((Q * Q : ℕ) : ℝ))
            ≤ Real.log (((Q : ℝ) * T) ^ 3) := Real.log_le_log (by positivity) h1
          _ = 3 * Real.log ((Q : ℝ) * T) := by rw [Real.log_pow]; norm_num
      have hβ₁_gt : 1 - c_P / Real.log (2 * ((Q * Q : ℕ) : ℝ)) < β₁ := by
        have hLQT_pos : 0 < Real.log ((Q : ℝ) * T) := Real.log_pos (by nlinarith)
        have h1 : 1 - β₁ ≤ (c_cl / 4) / Real.log ((Q : ℝ) * T) :=
          (le_div_iff₀ hLQT_pos).mpr hsmall
        have h2 : (c_cl / 4) / Real.log ((Q : ℝ) * T) < c_P / Real.log (2 * ((Q * Q : ℕ) : ℝ)) := by
          have hc_le : c_cl ≤ c_P := (min_le_right _ _).trans (min_le_right _ _)
          have h3 : c_cl * Real.log (2 * ((Q * Q : ℕ) : ℝ)) ≤ 3 * c_cl * Real.log ((Q : ℝ) * T) := by
            nlinarith
          have h4 : (c_cl / 4) * Real.log (2 * ((Q * Q : ℕ) : ℝ)) <
              c_P * Real.log ((Q : ℝ) * T) := by nlinarith
          exact (div_lt_div_iff₀ hLQT_pos hlog2Q2_pos).mpr h4
        linarith
      have hρ_gt : 1 - c_P / Real.log (2 * ((Q * Q : ℕ) : ℝ)) < ρ.re := by
        have hc_le : c_cl ≤ c_P := (min_le_right _ _).trans (min_le_right _ _)
        have hdiv : c_cl / Real.log ((Q : ℝ) ^ 2 * (H + 2)) ≤
            c_P / Real.log (2 * ((Q * Q : ℕ) : ℝ)) := by
          calc c_cl / Real.log ((Q : ℝ) ^ 2 * (H + 2))
              ≤ c_P / Real.log ((Q : ℝ) ^ 2 * (H + 2)) :=
                div_le_div_of_nonneg_right hc_le hL_pos.le
            _ ≤ c_P / Real.log (2 * ((Q * Q : ℕ) : ℝ)) :=
                div_le_div_of_nonneg_left hc_P.le hlog2Q2_pos hlog2Q2_le
        linarith
      have hψ₁_N : (PChar.of χ₁).N ≤ Q * Q := by
        have h1 : (PChar.of χ₁).N = q₁ := hprim₁
        rw [h1]; nlinarith
      have hz₁' : DirichletCharacter.LFunction (PChar.of χ₁).χ (β₁ : ℂ) = 0 := by
        have hof : PChar.of χ₁ = PChar.mk q₁ χ₁ hprim₁ := by
          simpa using PChar.of_self (PChar.mk q₁ χ₁ hprim₁)
        rw [hof]; exact hz₁
      obtain ⟨hψ_eq, hβ_eq⟩ := hpage_uniq (Q * Q) hQ2_ge2 ψ (PChar.of χ₁) ρ.re β₁ hN hψ₁_N
        hzρ_real hz₁' hρ_gt hβ₁_gt
      rcases hne with hρ_ne | hψ_ne
      · exact hρ_ne (by rw [hρ_eq, hβ_eq])
      · exact hψ_ne hψ_eq

/-- Minimum `1 - Re(ρ')` (capped at `1/2`) over all non-exceptional zeros `ρ'` with `|Im(ρ')| ≤ H`
of a finite set `S : Finset PChar`. -/
private lemma exists_min_orbit_zero_gap (S : Finset PChar) (ψ₁ : PChar) (β₁ : ℝ) (H : ℝ) :
    ∃ μ : ℝ, 0 < μ ∧ μ ≤ 1 / 2 ∧
      (∀ ψ ∈ S, ∀ ρ : ℂ, |ρ.im| ≤ H → 0 < ρ.re → ρ.re < 1 →
        DirichletCharacter.LFunction ψ.χ ρ = 0 → (ρ ≠ (β₁ : ℂ) ∨ ψ ≠ ψ₁) →
        μ ≤ 1 - ρ.re) ∧
      (μ < 1 / 2 → ∃ ψ ∈ S, ∃ ρ : ℂ, |ρ.im| ≤ H ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        DirichletCharacter.LFunction ψ.χ ρ = 0 ∧ (ρ ≠ (β₁ : ℂ) ∨ ψ ≠ ψ₁) ∧
        1 - ρ.re = μ) := by
  classical
  -- For each `ψ ∈ S`, every critical-strip zero with `|ρ.im| ≤ H` has `‖0 - ρ‖ ≤ H + 2`!
  let boxFin : PChar → Finset ℕ := fun ψ =>
    (finite_ball_zero_indices (pcharZeroSeq_strip ψ) (pcharZeroSeq_summable_inv_sq ψ) 0 (max H 0 + 2)).toFinset
  let goodPairs : Finset (PChar × ℕ) :=
    S.biUnion fun ψ =>
      ((boxFin ψ).filter fun n =>
        |(pcharZeroSeq ψ n).im| ≤ H ∧ (pcharZeroSeq ψ n ≠ (β₁ : ℂ) ∨ ψ ≠ ψ₁)).image (fun n => (ψ, n))
  let vals : Finset ℝ := insert (1 / 2) (goodPairs.image fun p => 1 - (pcharZeroSeq p.1 p.2).re)
  have hvals_ne : vals.Nonempty := ⟨1 / 2, Finset.mem_insert_self _ _⟩
  let μ : ℝ := vals.min' hvals_ne
  have hμ_le_half : μ ≤ 1 / 2 := Finset.min'_le vals (1 / 2) (Finset.mem_insert_self _ _)
  have hμ_mem : μ ∈ vals := Finset.min'_mem vals hvals_ne
  have hμ_pos : 0 < μ := by
    rcases Finset.mem_insert.mp hμ_mem with hhalf | himg
    · rw [hhalf]; norm_num
    · obtain ⟨⟨ψ, n⟩, _, heq⟩ := Finset.mem_image.mp himg
      rw [← heq]
      linarith [(pcharZeroSeq_strip ψ n).2]
  have hlb : ∀ ψ ∈ S, ∀ ρ : ℂ, |ρ.im| ≤ H → 0 < ρ.re → ρ.re < 1 →
      DirichletCharacter.LFunction ψ.χ ρ = 0 → (ρ ≠ (β₁ : ℂ) ∨ ψ ≠ ψ₁) →
      μ ≤ 1 - ρ.re := by
    intro ψ hψ ρ hIm h0 h1 hz hne
    obtain ⟨n, hn⟩ := exists_pcharZeroSeq_eq ψ h0 h1 hz
    have hnorm : ‖(0 : ℂ) - pcharZeroSeq ψ n‖ ≤ max H 0 + 2 := by
      rw [zero_sub, norm_neg, hn]
      have htri : ‖ρ‖ ≤ |ρ.re| + |ρ.im| := Complex.norm_le_abs_re_add_abs_im ρ
      rw [abs_of_pos h0] at htri
      linarith [le_max_left H 0]
    have hn_box : n ∈ boxFin ψ :=
      (finite_ball_zero_indices (pcharZeroSeq_strip ψ) (pcharZeroSeq_summable_inv_sq ψ) 0 (max H 0 + 2)).mem_toFinset.mpr hnorm
    have hp_mem : (ψ, n) ∈ goodPairs := by
      refine Finset.mem_biUnion.mpr ⟨ψ, hψ, Finset.mem_image.mpr ⟨n, ?_, rfl⟩⟩
      refine Finset.mem_filter.mpr ⟨hn_box, ?_, ?_⟩
      · rwa [hn]
      · rwa [hn]
    have hval_mem : 1 - ρ.re ∈ vals := by
      refine Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨(ψ, n), hp_mem, ?_⟩)
      rw [hn]
    exact Finset.min'_le vals (1 - ρ.re) hval_mem
  refine ⟨μ, hμ_pos, hμ_le_half, hlb, fun hlt => ?_⟩
  rcases Finset.mem_insert.mp hμ_mem with hhalf | himg
  · linarith
  · obtain ⟨⟨ψ, n⟩, hp_mem, heq⟩ := Finset.mem_image.mp himg
    obtain ⟨ψ', hψ'S, himg'⟩ := Finset.mem_biUnion.mp hp_mem
    obtain ⟨n', hn'filt, hpeq⟩ := Finset.mem_image.mp himg'
    rcases Prod.mk.inj hpeq with ⟨rfl, rfl⟩
    obtain ⟨_, hIm, hne⟩ := Finset.mem_filter.mp hn'filt
    refine ⟨ψ', hψ'S, pcharZeroSeq ψ' n', hIm, (pcharZeroSeq_strip ψ' n').1, (pcharZeroSeq_strip ψ' n').2,
      pcharZeroSeq_LFunction_zero ψ' n', hne, heq⟩

/-- Clean real-valued orbit gap function `orbitMinGap S ψ₁ β₁ H`. -/
private def orbitMinGap (S : Finset PChar) (ψ₁ : PChar) (β₁ : ℝ) (H : ℝ) : ℝ :=
  (exists_min_orbit_zero_gap S ψ₁ β₁ H).choose

private lemma orbitMinGap_spec (S : Finset PChar) (ψ₁ : PChar) (β₁ : ℝ) (H : ℝ) :
    let μ := orbitMinGap S ψ₁ β₁ H
    0 < μ ∧ μ ≤ 1 / 2 ∧
      (∀ ψ ∈ S, ∀ ρ : ℂ, |ρ.im| ≤ H → 0 < ρ.re → ρ.re < 1 →
        DirichletCharacter.LFunction ψ.χ ρ = 0 → (ρ ≠ (β₁ : ℂ) ∨ ψ ≠ ψ₁) →
        μ ≤ 1 - ρ.re) ∧
      (μ < 1 / 2 → ∃ ψ ∈ S, ∃ ρ : ℂ, |ρ.im| ≤ H ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        DirichletCharacter.LFunction ψ.χ ρ = 0 ∧ (ρ ≠ (β₁ : ℂ) ∨ ψ ≠ ψ₁) ∧
        1 - ρ.re = μ) :=
  (exists_min_orbit_zero_gap S ψ₁ β₁ H).choose_spec

private lemma orbitMinGap_antitone (S : Finset PChar) (ψ₁ : PChar) (β₁ : ℝ) {H₁ H₂ : ℝ}
    (hH : H₁ ≤ H₂) :
    orbitMinGap S ψ₁ β₁ H₂ ≤ orbitMinGap S ψ₁ β₁ H₁ := by
  have h1 := orbitMinGap_spec S ψ₁ β₁ H₁
  have h2 := orbitMinGap_spec S ψ₁ β₁ H₂
  by_cases hlt : orbitMinGap S ψ₁ β₁ H₁ < 1 / 2
  · obtain ⟨ψ, hψ, ρ, hIm, h0, h1', hz, hne, heq⟩ := h1.2.2.2 hlt
    rw [← heq]
    exact h2.2.2.1 ψ hψ ρ (hIm.trans hH) h0 h1' hz hne
  · push Not at hlt
    linarith [h2.2.1]

/-- **Extremal-Zero Height Stopping Lemma**:
if `orbitMinGap S ψ₁ β₁ H` is bounded below by `c_cl / Real.log (Q^2 * (H + 2))` for all `H ≥ T`,
then for any `ε ∈ (0, 1/4]` and any `J : ℕ` with `Real.exp (-2 * ε * J) * μ₀ < c_cl / Real.log (Q^2 * (T + J + 2))`,
there exists `j < J` with `orbitMinGap S ψ₁ β₁ (T + j + 1) ≥ (1 - 2 * ε) * orbitMinGap S ψ₁ β₁ (T + j)`. -/
private lemma exists_stopping_height (S : Finset PChar) (ψ₁ : PChar) (β₁ T c_cl ε : ℝ)
    (Q J : ℕ) (hε0 : 0 < ε) (hε_le : ε ≤ 1 / 4)
    (hlb : ∀ j : ℕ, j ≤ J →
      c_cl / Real.log ((Q : ℝ) ^ 2 * (T + (j : ℝ) + 2)) ≤ orbitMinGap S ψ₁ β₁ (T + (j : ℝ)))
    (hkill : Real.exp (-2 * ε * (J : ℝ)) * orbitMinGap S ψ₁ β₁ T <
      c_cl / Real.log ((Q : ℝ) ^ 2 * (T + (J : ℝ) + 2))) :
    ∃ j : ℕ, j < J ∧
      (1 - 2 * ε) * orbitMinGap S ψ₁ β₁ (T + (j : ℝ)) ≤
        orbitMinGap S ψ₁ β₁ (T + (j : ℝ) + 1) := by
  by_contra hnone
  push Not at hnone
  have hind : ∀ k : ℕ, k ≤ J →
      orbitMinGap S ψ₁ β₁ (T + (k : ℝ)) ≤
        (1 - 2 * ε) ^ k * orbitMinGap S ψ₁ β₁ T := by
    intro k hk
    induction k with
    | zero => simp
    | succ k ih =>
      have hk_lt : k < J := by omega
      have hstep := hnone k hk_lt
      have hprev := ih (by omega)
      have h12ε_nn : 0 ≤ 1 - 2 * ε := by linarith
      have hcast : T + ((k + 1 : ℕ) : ℝ) = T + (k : ℝ) + 1 := by push_cast; ring
      rw [hcast, pow_succ]
      calc orbitMinGap S ψ₁ β₁ (T + (k : ℝ) + 1)
          ≤ (1 - 2 * ε) * orbitMinGap S ψ₁ β₁ (T + (k : ℝ)) := hstep.le
        _ ≤ (1 - 2 * ε) * ((1 - 2 * ε) ^ k * orbitMinGap S ψ₁ β₁ T) :=
            mul_le_mul_of_nonneg_left hprev h12ε_nn
        _ = (1 - 2 * ε) ^ k * (1 - 2 * ε) * orbitMinGap S ψ₁ β₁ T := by ring
  have h1 := hind J le_rfl
  have hexp_le : (1 - 2 * ε) ^ J ≤ Real.exp (-2 * ε * (J : ℝ)) := by
    have hbase : 1 - 2 * ε ≤ Real.exp (-2 * ε) := by
      have := Real.add_one_le_exp (-2 * ε); linarith
    calc (1 - 2 * ε) ^ J ≤ (Real.exp (-2 * ε)) ^ J :=
          pow_le_pow_left₀ (by linarith) hbase J
      _ = Real.exp (-2 * ε * (J : ℝ)) := by rw [← Real.exp_nat_mul]; ring_nf
  have hμ0_pos : 0 < orbitMinGap S ψ₁ β₁ T := (orbitMinGap_spec S ψ₁ β₁ T).1
  have h2 : orbitMinGap S ψ₁ β₁ (T + (J : ℝ)) ≤
      Real.exp (-2 * ε * (J : ℝ)) * orbitMinGap S ψ₁ β₁ T :=
    h1.trans (mul_le_mul_of_nonneg_right hexp_le hμ0_pos.le)
  linarith [hlb J le_rfl]

/-! ## Section 5: Unconditional Deuring–Heilbronn Zero-Repulsion Theorems (`0` Assumptions!) -/

/-- Helper: splitting an infinite complex sum into inner (`‖s - ρ n‖ ≤ R`), medium (`R < ‖s - ρ n‖ ≤ 1`),
and far (`1 < ‖s - ρ n‖`) parts, and bounding the real part of the tail! -/
private lemma re_tsum_split_inner_tail {ρ : ℕ → ℂ} {t C₁ L μ A : ℝ}
    (hC₁ : 0 ≤ C₁) (hL : 0 ≤ L)
    (hstrip : ∀ n, 0 < (ρ n).re ∧ (ρ n).re < 1)
    (hsum : Summable (fun n : ℕ => (‖ρ n‖ ^ 2)⁻¹))
    (hre_le : ∀ σ : ℝ, 1 < σ → σ ≤ 2 → ∀ F : Finset ℕ,
      ∑ n ∈ F, ((1 : ℂ) / (((σ : ℂ) + I * (t : ℂ)) - ρ n)).re ≤ C₁ * L + 2 / (σ - 1))
    (hμ : 0 < μ) (hA : 4 ≤ A) (hR_le : A * μ ≤ 1 / 2)
    (excl : Option ℕ) {m : ℕ} (hm : 1 ≤ m) :
    let s : ℂ := ((1 + μ : ℝ) : ℂ) + I * (t : ℂ)
    let R : ℝ := A * μ
    let F_in : Finset ℕ := ((finite_ball_zero_indices hstrip hsum s R).toFinset).filter (fun n => excl ≠ some n)
    (∑ n ∈ F_in, (((2 * μ : ℝ) : ℂ) / (s - ρ n)) ^ (2 * m)).re -
      ((2 / A) ^ (2 * m) * ((16 * C₁ + 16) * (A * (μ * L) + 1)) +
        4 * (2 * μ) ^ (2 * m) * (C₁ * L + 2)) ≤
      (∑' n : ℕ, if excl = some n then (0 : ℂ) else (((2 * μ : ℝ) : ℂ) / (s - ρ n)) ^ (2 * m)).re := by
  classical
  intro s R F_in
  have hμ_le : μ ≤ 1 / 2 := by nlinarith
  have hsumm_all : Summable (fun n : ℕ => (((2 * μ : ℝ) : ℂ) / (s - ρ n)) ^ (2 * m)) := by
    have hbase := summable_inv_sub_pow_of_strip hstrip hsum (s := s) (by simp [s]; linarith)
      (k := 2 * m - 1) (by omega)
    refine (hbase.mul_left ((((2 * μ : ℝ) : ℂ)) ^ (2 * m))).congr fun n => ?_
    rw [div_pow, show 2 * m - 1 + 1 = 2 * m by omega]; ring
  have hsumm_excl : Summable (fun n : ℕ =>
      if excl = some n then (0 : ℂ) else (((2 * μ : ℝ) : ℂ) / (s - ρ n)) ^ (2 * m)) :=
    Summable.of_norm_bounded hsumm_all.norm fun n => by
      split_ifs
      · simp; positivity
      · simp
  let f : ℕ → ℂ := fun n => if excl = some n then 0 else (((2 * μ : ℝ) : ℂ) / (s - ρ n)) ^ (2 * m)
  let f_in : ℕ → ℂ := fun n => if n ∈ F_in then f n else 0
  let f_out : ℕ → ℂ := fun n => if n ∈ F_in then 0 else f n
  have hfin_summ : Summable f_in := summable_of_ne_finset_zero (s := F_in) fun n hn => by
    simp [f_in, hn]
  have hfout_summ : Summable f_out :=
    Summable.of_norm_bounded hsumm_excl.norm fun n => by
      dsimp only [f_out, f]
      split_ifs
      · simp
      · simp; positivity
      · simp
      · simp
  have hsplit : ∑' n : ℕ, f n = (∑' n : ℕ, f_in n) + (∑' n : ℕ, f_out n) := by
    rw [← Summable.tsum_add hfin_summ hfout_summ]
    refine tsum_congr fun n => ?_
    dsimp only [f_in, f_out]; split_ifs <;> simp
  have hfin_eq : ∑' n : ℕ, f_in n = ∑ n ∈ F_in, (((2 * μ : ℝ) : ℂ) / (s - ρ n)) ^ (2 * m) := by
    rw [tsum_eq_sum (s := F_in) fun n hn => by simp [f_in, hn]]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hne : excl ≠ some n := (Finset.mem_filter.mp hn).2
    simp [f_in, f, hn, hne]
  have hout_norm : ‖∑' n : ℕ, f_out n‖ ≤
      (2 / A) ^ (2 * m) * ((16 * C₁ + 16) * (A * (μ * L) + 1)) +
        4 * (2 * μ) ^ (2 * m) * (C₁ * L + 2) := by
    have hmed_summ : Summable (fun n : ℕ =>
        if R < ‖s - ρ n‖ ∧ ‖s - ρ n‖ ≤ 1 then (2 * μ / ‖s - ρ n‖) ^ (2 * m) else 0) :=
      summable_of_ne_finset_zero (s := (finite_ball_zero_indices hstrip hsum s 1).toFinset)
        fun n hn => by
          have hnot : ¬ (‖s - ρ n‖ ≤ 1) := fun h =>
            hn ((finite_ball_zero_indices hstrip hsum s 1).mem_toFinset.mpr h)
          simp [hnot]
    have hfar_summ : Summable (fun n : ℕ =>
        if 1 < ‖s - ρ n‖ then (2 * μ / ‖s - ρ n‖) ^ (2 * m) else 0) := by
      refine Summable.of_nonneg_of_le (fun n => by split_ifs <;> positivity) (fun n => ?_)
        hsumm_all.norm
      split_ifs
      · rw [norm_pow, norm_div, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      · exact norm_nonneg _
    have hpt : ∀ n : ℕ, ‖f_out n‖ ≤
        (if R < ‖s - ρ n‖ ∧ ‖s - ρ n‖ ≤ 1 then (2 * μ / ‖s - ρ n‖) ^ (2 * m) else 0) +
          (if 1 < ‖s - ρ n‖ then (2 * μ / ‖s - ρ n‖) ^ (2 * m) else 0) := by
      intro n
      dsimp only [f_out, f]
      by_cases hn_in : n ∈ F_in
      · rw [if_pos hn_in, norm_zero]; split_ifs <;> positivity
      · rw [if_neg hn_in]
        by_cases hex : excl = some n
        · rw [if_pos hex, norm_zero]; split_ifs <;> positivity
        · rw [if_neg hex, norm_pow, norm_div, Complex.norm_real,
            Real.norm_of_nonneg (by positivity)]
          have hR_lt : R < ‖s - ρ n‖ := by
            by_contra hle; push Not at hle
            have hn_mem : n ∈ F_in := Finset.mem_filter.mpr
              ⟨(finite_ball_zero_indices hstrip hsum s R).mem_toFinset.mpr hle, hex⟩
            exact hn_in hn_mem
          by_cases h1 : ‖s - ρ n‖ ≤ 1
          · rw [if_pos ⟨hR_lt, h1⟩, if_neg (not_lt.mpr h1), add_zero]
          · push Not at h1
            rw [if_neg (fun h => not_lt.mpr h.2 h1), if_pos h1, zero_add]
    calc ‖∑' n : ℕ, f_out n‖
        ≤ ∑' n : ℕ, ‖f_out n‖ := norm_tsum_le_tsum_norm hfout_summ.norm
      _ ≤ ∑' n : ℕ, ((if R < ‖s - ρ n‖ ∧ ‖s - ρ n‖ ≤ 1 then (2 * μ / ‖s - ρ n‖) ^ (2 * m) else 0) +
            (if 1 < ‖s - ρ n‖ then (2 * μ / ‖s - ρ n‖) ^ (2 * m) else 0)) :=
          hfout_summ.norm.tsum_le_tsum hpt (hmed_summ.add hfar_summ)
      _ = (∑' n : ℕ, if R < ‖s - ρ n‖ ∧ ‖s - ρ n‖ ≤ 1 then (2 * μ / ‖s - ρ n‖) ^ (2 * m) else 0) +
            (∑' n : ℕ, if 1 < ‖s - ρ n‖ then (2 * μ / ‖s - ρ n‖) ^ (2 * m) else 0) :=
          Summable.tsum_add hmed_summ hfar_summ
      _ ≤ (2 / A) ^ (2 * m) * ((16 * C₁ + 16) * (A * (μ * L) + 1)) +
            4 * (2 * μ) ^ (2 * m) * (C₁ * L + 2) :=
          add_le_add (tsum_tail_medium_le_of_re_le hC₁ hL hstrip hsum hre_le hμ hA hR_le hm)
            (tsum_tail_far_le_of_re_le hstrip hsum hre_le hμ hμ_le hm)
  have hre_out : -(∑' n : ℕ, f_out n).re ≤ ‖∑' n : ℕ, f_out n‖ :=
    (neg_le_abs _).trans (Complex.abs_re_le_norm _)
  change _ ≤ (∑' n : ℕ, f n).re
  rw [hsplit, Complex.add_re, hfin_eq]
  linarith

/-- Helper: elementary log bound `Real.log (x + 2) ≤ x` for `x ≥ 2`, and `(L + 1) * log(L + 2) ≤ 4 * e^L`
for `L ≥ 1`. -/
private lemma log_linear_mul_log_le_exp {L : ℝ} (hL : 1 ≤ L) :
    (L + 1) * Real.log (L + 2) ≤ 4 * Real.exp L := by
  have h1 : Real.log (L + 2) ≤ L + 1 := by
    have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < L + 2); linarith
  have hsq : (L + 1) ^ 2 ≤ 4 * Real.exp L := by
    have hexp := Real.sum_le_exp_of_nonneg (x := L) (by linarith) 3
    have hsum3 : ∑ i ∈ Finset.range 3, L ^ i / (i.factorial : ℝ) = 1 + L + L ^ 2 / 2 := by
      simp [Finset.sum_range_succ, Nat.factorial]
    rw [hsum3] at hexp
    nlinarith
  have hnn : 0 ≤ L + 1 := by linarith
  nlinarith

open Classical in
/-- Helper: per-`m` Hadamard + 4-character positivity upper bound on the sum of inner zeros
across the 4 Klein-four orbit slots `![PChar.one, PChar.of χ₁, ψ_s, PChar.of (prodChar ψ_s.χ χ₁)]`. -/
private lemma per_m_inner_sum_upper_bound
    {C₁ C_E : ℝ} (hC₁_pos : 0 < C₁) (hC_E_pos : 0 < C_E)
    (hsdZ : ∀ s : ℂ, 1 < s.re → s.re ≤ 2 → ∀ k : ℕ, 1 ≤ k →
      ‖scaledDeriv k negLogDerivZeta s -
        (1 / (s - 1) ^ (k + 1) - ∑' n : ℕ, (1 : ℂ) / (s - xiZeroSeq n) ^ (k + 1))‖ ≤
          C_E * (2 : ℝ) ^ k * Real.log (|s.im| + 2))
    (hsdL : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ),
      1 < s.re → s.re ≤ 2 → ∀ k : ℕ, 1 ≤ k →
        (χ = 1 →
          ‖scaledDeriv k (negLogDerivL χ) s -
            (1 / (s - 1) ^ (k + 1) - ∑' n : ℕ, (1 : ℂ) / (s - xiZeroSeq n) ^ (k + 1))‖ ≤
              C_E * (2 : ℝ) ^ k * Real.log ((q : ℝ) * (|s.im| + 2))) ∧
        (∀ hχ : χ ≠ 1,
          have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
          have hψ : χ.primitiveCharacter ≠ 1 := fun h1 => hχ (by
            rw [← χ.changeLevel_primitiveCharacter, h1, map_one])
          ‖scaledDeriv k (negLogDerivL χ) s -
            (- ∑' n : ℕ, (1 : ℂ) / (s - completedLZeroSeq χ.primitiveCharacter_isPrimitive hψ n) ^ (k + 1))‖ ≤
              C_E * (2 : ℝ) ^ k * Real.log ((q : ℝ) * (|s.im| + 2))))
    {Q : ℕ} (hQ : 2 ≤ Q) {T_j : ℝ} (hTj : 2 ≤ T_j)
    {q₁ : ℕ} [NeZero q₁] {χ₁ : DirichletCharacter ℂ q₁}
    (hq₁ : q₁ ≤ Q) (hsq₁ : χ₁ ^ 2 = 1) (hχ₁ : χ₁ ≠ 1)
    {β₁ : ℝ} (hβ₁1 : β₁ < 1) {n₁ : ℕ} (hn₁ : pcharZeroSeq (PChar.of χ₁) n₁ = (β₁ : ℂ))
    {ψ_s : PChar} (hψ_s_N : ψ_s.N ≤ Q * Q) {γ_s : ℝ} (hIm_s : |γ_s| ≤ T_j)
    {μ A : ℝ} (hμ_pos : 0 < μ) (hμ_le1 : μ ≤ 1) (hA_ge4 : 4 ≤ A) (hR_le : A * μ ≤ 1 / 2)
    (hslot_re_le :
      let slotChar : Fin 4 → PChar := ![PChar.one, PChar.of χ₁, ψ_s, PChar.of (prodChar ψ_s.χ χ₁)]
      let slotIm : Fin 4 → ℝ := ![0, 0, γ_s, γ_s]
      ∀ i : Fin 4, ∀ σ : ℝ, 1 < σ → σ ≤ 2 → ∀ F : Finset ℕ,
        ∑ n ∈ F, ((1 : ℂ) / (((σ : ℂ) + I * (slotIm i : ℂ)) - pcharZeroSeq (slotChar i) n)).re ≤
          C₁ * Real.log ((Q : ℝ) ^ 2 * (T_j + 2)) + 2 / (σ - 1))
    {m : ℕ} (hm1 : 1 ≤ m) :
    let ψ₀ := PChar.one
    let ψ₁ := PChar.of χ₁
    let ψ_prod := PChar.of (prodChar ψ_s.χ χ₁)
    let slotChar : Fin 4 → PChar := ![ψ₀, ψ₁, ψ_s, ψ_prod]
    let slotIm : Fin 4 → ℝ := ![0, 0, γ_s, γ_s]
    let slotPt : Fin 4 → ℂ := fun i => ((1 + μ : ℝ) : ℂ) + I * (slotIm i : ℂ)
    let slotExcl : Fin 4 → Option ℕ :=
      ![none, some n₁, if ψ_s = ψ₁ then some n₁ else none, if ψ_s = ψ₀ then some n₁ else none]
    let innerFin : Fin 4 → Finset ℕ := fun i =>
      ((finite_ball_zero_indices (pcharZeroSeq_strip (slotChar i))
        (pcharZeroSeq_summable_inv_sq (slotChar i)) (slotPt i) (A * μ)).toFinset).filter
        (fun n => slotExcl i ≠ some n)
    let L_max : ℝ := Real.log ((Q : ℝ) ^ 2 * (T_j + 2))
    ∑ i : Fin 4, (∑ n ∈ innerFin i, (((2 * μ : ℝ) : ℂ) / (slotPt i - pcharZeroSeq (slotChar i) n)) ^ (2 * m)).re ≤
      4 * (m : ℝ) * ((1 - β₁) / μ) * 2 ^ (2 * m) +
      4 * C_E * (2 * μ) ^ (2 * m) * (2 : ℝ) ^ (2 * m - 1) * L_max +
      4 * ((2 / A) ^ (2 * m) * ((16 * C₁ + 16) * (A * (μ * L_max) + 1)) +
        4 * (2 * μ) ^ (2 * m) * (C₁ * L_max + 2)) := by
  classical
  intro ψ₀ ψ₁ ψ_prod slotChar slotIm slotPt slotExcl innerFin L_max
  have hQR : (2 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ
  have hL_max_pos : 0 < L_max := Real.log_pos (by nlinarith)
  set s₁ : ℂ := ((1 + μ : ℝ) : ℂ) + I * (γ_s : ℂ)
  set k : ℕ := 2 * m - 1
  have hk1 : 1 ≤ k := by omega
  have hk_add1 : k + 1 = 2 * m := by omega
  have hψ₁_ne1 : ψ₁.χ ≠ 1 := by
    intro h1; apply hχ₁
    have h1' : χ₁.primitiveCharacter = 1 := h1
    rw [← χ₁.changeLevel_primitiveCharacter, h1', map_one]
  -- Step 1: 4-character positivity at `σ = 1 + μ`, `γ = γ_s`, order `k`
  have hpos_k := re_scaledDeriv_four_char_nonneg χ₁ (isRealChar_of_sq_eq_one hsq₁) ψ_s.χ
    (by linarith : (1 : ℝ) < 1 + μ) γ_s k
  -- Split `scaledDeriv k (f + g)` via `ContDiffAt`
  have hcd_L_loc : ∀ {q' : ℕ} [NeZero q'] (φ : DirichletCharacter ℂ q') {s : ℂ},
      1 < s.re → ContDiffAt ℂ k (negLogDerivL φ) s := by
    intro q' _ φ s hs
    have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    have hdiff : DifferentiableOn ℂ (negLogDerivL φ) {z : ℂ | 1 < z.re} := by
      have habs : LSeries.abscissaOfAbsConv (fun n => φ n * (Λ n : ℂ)) ≤ (1 : EReal) :=
        LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun x hx =>
          φ.LSeriesSummable_twist_vonMangoldt (by simpa using hx)
      intro z hz
      have hlt : LSeries.abscissaOfAbsConv (fun n => φ n * (Λ n : ℂ)) < (z.re : EReal) :=
        lt_of_le_of_lt habs (EReal.coe_lt_coe_iff.mpr hz)
      have hev : negLogDerivL φ =ᶠ[𝓝 z] LSeries (fun n => φ n * (Λ n : ℂ)) := by
        filter_upwards [hopen.mem_nhds hz] with w hw; exact negLogDerivL_eq_LSeries φ hw
      exact ((LSeries_hasDerivAt hlt).congr_of_eventuallyEq hev).differentiableAt.differentiableWithinAt
    exact (hdiff.analyticAt (hopen.mem_nhds hs)).contDiffAt.of_le le_top
  have hcd_Z_loc : ∀ {s : ℂ}, 1 < s.re → ContDiffAt ℂ k negLogDerivZeta s := by
    intro s hs
    have h1 := hcd_L_loc (1 : DirichletCharacter ℂ 1) hs
    have heq : negLogDerivL (1 : DirichletCharacter ℂ 1) = negLogDerivZeta := by
      ext z; unfold negLogDerivL negLogDerivZeta; rw [DirichletCharacter.LFunction_modOne_eq]
    rwa [heq] at h1
  have hs0_re : (1 : ℝ) < ((1 + μ : ℝ) : ℂ).re := by simp [hμ_pos]
  have hs1_re : (1 : ℝ) < s₁.re := by simp [s₁, hμ_pos]
  have hs0_le2 : ((1 + μ : ℝ) : ℂ).re ≤ 2 := by simp; linarith
  have hs1_le2 : s₁.re ≤ 2 := by simp [s₁]; linarith
  rw [scaledDeriv_add (hcd_Z_loc hs0_re) (hcd_L_loc χ₁ hs0_re),
    scaledDeriv_add (hcd_L_loc ψ_s.χ hs1_re) (hcd_L_loc (prodChar ψ_s.χ χ₁) hs1_re)] at hpos_k
  -- Unified Hadamard error bound for any `φ : DirichletCharacter ℂ q'` at `s`
  have hhad_any : ∀ {q' : ℕ} [NeZero q'] (φ : DirichletCharacter ℂ q') (s : ℂ),
      1 < s.re → s.re ≤ 2 → (q' : ℝ) * (|s.im| + 2) ≤ (Q : ℝ) ^ 2 * (T_j + 2) →
      ‖scaledDeriv k (negLogDerivL φ) s -
          ((if φ = 1 then (1 : ℂ) / (s - 1) ^ (k + 1) else 0) -
            ∑' n : ℕ, (1 : ℂ) / (s - pcharZeroSeq (PChar.of φ) n) ^ (k + 1))‖ ≤
        C_E * (2 : ℝ) ^ k * L_max := by
    intro q' _ φ s hs1 hs2 hqt_le
    have h1 := hsdL q' φ s hs1 hs2 k hk1
    have hlog_le : Real.log ((q' : ℝ) * (|s.im| + 2)) ≤ L_max :=
      Real.log_le_log (by have : (0 : ℝ) < (q' : ℝ) := Nat.cast_pos.mpr (NeZero.pos q'); positivity) hqt_le
    have hCE2k : 0 ≤ C_E * (2 : ℝ) ^ k := by positivity
    by_cases hφ1 : φ = 1
    · have hof1 : PChar.of φ = PChar.one := by rw [hφ1, PChar.of_one]
      have hseq : pcharZeroSeq (PChar.of φ) = xiZeroSeq := by
        rw [hof1]; exact pcharZeroSeq_one
      rw [if_pos hφ1, hseq]
      exact (h1.1 hφ1).trans (mul_le_mul_of_nonneg_left hlog_le hCE2k)
    · have hψ_ne1 : (PChar.of φ).χ ≠ 1 := fun h => hφ1 (by
        have h' : φ.primitiveCharacter = 1 := h
        rw [← φ.changeLevel_primitiveCharacter, h', map_one])
      rw [if_neg hφ1, zero_sub, pcharZeroSeq_of_ne_one hψ_ne1]
      exact (h1.2 hφ1).trans (mul_le_mul_of_nonneg_left hlog_le hCE2k)
  -- Apply Hadamard to all 4 terms!
  have hE1 : ‖scaledDeriv k (negLogDerivL χ₁) ((1 + μ : ℝ) : ℂ) -
      (- ∑' n : ℕ, (1 : ℂ) / (((1 + μ : ℝ) : ℂ) - pcharZeroSeq ψ₁ n) ^ (k + 1))‖ ≤
      C_E * (2 : ℝ) ^ k * L_max := by
    have h1 := hhad_any χ₁ ((1 + μ : ℝ) : ℂ) hs0_re hs0_le2 (by
      simp only [Complex.ofReal_im, abs_zero, zero_add]
      have : (q₁ : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hq₁
      nlinarith)
    simpa [hχ₁, ψ₁] using h1
  have hE2 : ‖scaledDeriv k (negLogDerivL ψ_s.χ) s₁ -
      ((if ψ_s = ψ₀ then (1 : ℂ) / (s₁ - 1) ^ (k + 1) else 0) -
        ∑' n : ℕ, (1 : ℂ) / (s₁ - pcharZeroSeq ψ_s n) ^ (k + 1))‖ ≤
      C_E * (2 : ℝ) ^ k * L_max := by
    have h1 := hhad_any ψ_s.χ s₁ hs1_re hs1_le2 (by
      have hN : (ψ_s.N : ℝ) ≤ (Q : ℝ) ^ 2 := by
        have hR : (ψ_s.N : ℝ) ≤ ((Q * Q : ℕ) : ℝ) := by exact_mod_cast hψ_s_N
        push_cast at hR; linarith [sq (Q : ℝ)]
      have him : s₁.im = γ_s := by simp [s₁]
      rw [him]
      exact mul_le_mul hN (by linarith) (by positivity) (by positivity))
    rw [PChar.of_self] at h1
    have hiff : ψ_s.χ = 1 ↔ ψ_s = ψ₀ := (pchar_eq_one_iff_chi_eq_one ψ_s).symm
    simpa [hiff] using h1
  have hE3 : ‖scaledDeriv k (negLogDerivL (prodChar ψ_s.χ χ₁)) s₁ -
      ((if ψ_s = ψ₁ then (1 : ℂ) / (s₁ - 1) ^ (k + 1) else 0) -
        ∑' n : ℕ, (1 : ℂ) / (s₁ - pcharZeroSeq ψ_prod n) ^ (k + 1))‖ ≤
      (3 / 2 : ℝ) * (C_E * (2 : ℝ) ^ k * L_max) := by
    have h1 := hsdL (ψ_s.N * q₁) (prodChar ψ_s.χ χ₁) s₁ hs1_re hs1_le2 k hk1
    have hN_le : (ψ_s.N : ℝ) ≤ (Q : ℝ) ^ 2 := by
      have hR : (ψ_s.N : ℝ) ≤ ((Q * Q : ℕ) : ℝ) := by exact_mod_cast hψ_s_N
      push_cast at hR; linarith [sq (Q : ℝ)]
    have hq₁_le : (q₁ : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hq₁
    have him : s₁.im = γ_s := by simp [s₁]
    have hlog_le : Real.log (((ψ_s.N * q₁ : ℕ) : ℝ) * (|s₁.im| + 2)) ≤ (3 / 2 : ℝ) * L_max := by
      have hpow : (((ψ_s.N * q₁ : ℕ) : ℝ) * (|s₁.im| + 2)) ^ 2 ≤ ((Q : ℝ) ^ 2 * (T_j + 2)) ^ 3 := by
        push_cast; rw [him]
        have hA1 : (ψ_s.N : ℝ) * (q₁ : ℝ) ≤ (Q : ℝ) ^ 3 := by
          calc (ψ_s.N : ℝ) * (q₁ : ℝ) ≤ (Q : ℝ) ^ 2 * (Q : ℝ) :=
                mul_le_mul hN_le hq₁_le (by positivity) (by positivity)
            _ = (Q : ℝ) ^ 3 := by ring
        have hA2 : |γ_s| + 2 ≤ T_j + 2 := by linarith
        have h1' : ((ψ_s.N : ℝ) * (q₁ : ℝ) * (|γ_s| + 2)) ^ 2 ≤ ((Q : ℝ) ^ 3 * (T_j + 2)) ^ 2 :=
          pow_le_pow_left₀ (by positivity) (mul_le_mul hA1 hA2 (by positivity) (by positivity)) 2
        have h2' : ((Q : ℝ) ^ 3 * (T_j + 2)) ^ 2 ≤ ((Q : ℝ) ^ 2 * (T_j + 2)) ^ 3 := by
          have hT2 : (1 : ℝ) ≤ T_j + 2 := by linarith
          calc ((Q : ℝ) ^ 3 * (T_j + 2)) ^ 2
              = (Q : ℝ) ^ 6 * (T_j + 2) ^ 2 := by ring
            _ ≤ (Q : ℝ) ^ 6 * (T_j + 2) ^ 3 :=
                mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hT2 (by norm_num)) (by positivity)
            _ = ((Q : ℝ) ^ 2 * (T_j + 2)) ^ 3 := by ring
        exact h1'.trans h2'
      have hpos1 : 0 < ((ψ_s.N * q₁ : ℕ) : ℝ) * (|s₁.im| + 2) := by
        have : (0 : ℝ) < ((ψ_s.N * q₁ : ℕ) : ℝ) := Nat.cast_pos.mpr (Nat.mul_pos (NeZero.pos _) (NeZero.pos _))
        positivity
      have hlog2 := Real.log_le_log (pow_pos hpos1 2) hpow
      rw [Real.log_pow, Real.log_pow, Nat.cast_ofNat, Nat.cast_ofNat] at hlog2
      dsimp only [L_max]; linarith
    have hiff : prodChar ψ_s.χ χ₁ = 1 ↔ ψ_s = ψ₁ := prodChar_eq_one_iff_eq_pchar hsq₁ ψ_s
    by_cases hp1 : prodChar ψ_s.χ χ₁ = 1
    · have hψs1 : ψ_s = ψ₁ := hiff.mp hp1
      have hprod1 : ψ_prod = PChar.one := by dsimp only [ψ_prod]; rw [hp1, PChar.of_one]
      have hseq : pcharZeroSeq ψ_prod = xiZeroSeq := by rw [hprod1]; exact pcharZeroSeq_one
      rw [if_pos hψs1, hseq]
      exact (h1.1 hp1).trans (by
        have hnn : 0 ≤ C_E * (2 : ℝ) ^ k := by positivity
        have := mul_le_mul_of_nonneg_left hlog_le hnn
        linarith [show C_E * (2 : ℝ) ^ k * ((3 / 2 : ℝ) * L_max) =
          (3 / 2 : ℝ) * (C_E * (2 : ℝ) ^ k * L_max) by ring])
    · have hψs1 : ψ_s ≠ ψ₁ := fun h => hp1 (hiff.mpr h)
      have hψp_ne1 : ψ_prod.χ ≠ 1 := fun h => hp1 (by
        have h' : (prodChar ψ_s.χ χ₁).primitiveCharacter = 1 := h
        rw [← (prodChar ψ_s.χ χ₁).changeLevel_primitiveCharacter, h', map_one])
      rw [if_neg hψs1, zero_sub, pcharZeroSeq_of_ne_one hψp_ne1]
      exact (h1.2 hp1).trans (by
        have hnn : 0 ≤ C_E * (2 : ℝ) ^ k := by positivity
        have := mul_le_mul_of_nonneg_left hlog_le hnn
        linarith [show C_E * (2 : ℝ) ^ k * ((3 / 2 : ℝ) * L_max) =
          (3 / 2 : ℝ) * (C_E * (2 : ℝ) ^ k * L_max) by ring])
  have hE0_half : ‖scaledDeriv k negLogDerivZeta ((1 + μ : ℝ) : ℂ) -
      ((1 : ℂ) / (((1 + μ : ℝ) : ℂ) - 1) ^ (k + 1) -
        ∑' n : ℕ, (1 : ℂ) / (((1 + μ : ℝ) : ℂ) - pcharZeroSeq ψ₀ n) ^ (k + 1))‖ ≤
      (1 / 2 : ℝ) * (C_E * (2 : ℝ) ^ k * L_max) := by
    have hseq : pcharZeroSeq ψ₀ = xiZeroSeq := pcharZeroSeq_one
    rw [hseq]
    have h1 := hsdZ ((1 + μ : ℝ) : ℂ) hs0_re hs0_le2 k hk1
    have hlog_half : Real.log (|((1 + μ : ℝ) : ℂ).im| + 2) ≤ (1 / 2 : ℝ) * L_max := by
      simp only [Complex.ofReal_im, abs_zero, zero_add]
      have hsq : (2 : ℝ) ^ 2 ≤ (Q : ℝ) ^ 2 * (T_j + 2) := by nlinarith
      have h2 := Real.log_le_log (by norm_num : (0 : ℝ) < (2 : ℝ) ^ 2) hsq
      rw [Real.log_pow] at h2; push_cast at h2; linarith
    have := mul_le_mul_of_nonneg_left hlog_half (by positivity : (0 : ℝ) ≤ C_E * (2 : ℝ) ^ k)
    linarith [show C_E * (2 : ℝ) ^ k * ((1 / 2 : ℝ) * L_max) = (1 / 2 : ℝ) * (C_E * (2 : ℝ) ^ k * L_max) by ring]
  -- Pull out `n₁` from the zero sums where `slotExcl i = some n₁`!
  have hpull_excl : ∀ i : Fin 4,
      (∑' n : ℕ, (1 : ℂ) / (slotPt i - pcharZeroSeq (slotChar i) n) ^ (k + 1)) =
        (if slotExcl i = some n₁ then (1 : ℂ) / (slotPt i - (β₁ : ℂ)) ^ (k + 1) else 0) +
          ∑' n : ℕ, if slotExcl i = some n then (0 : ℂ)
            else (1 : ℂ) / (slotPt i - pcharZeroSeq (slotChar i) n) ^ (k + 1) := by
    intro i
    have hsumm := summable_inv_sub_pow_of_strip (pcharZeroSeq_strip (slotChar i))
      (pcharZeroSeq_summable_inv_sq (slotChar i)) (s := slotPt i) (by simp [slotPt, hμ_pos]) hk1
    by_cases hex : slotExcl i = some n₁
    · rw [if_pos hex]
      have hchar_eq : slotChar i = ψ₁ := by
        fin_cases i
        · simp [slotExcl] at hex
        · rfl
        · simp [slotExcl] at hex
          exact hex
        · simp [slotExcl] at hex
          dsimp only [slotChar, Matrix.cons_val_three, Matrix.tail_cons, Matrix.head_cons, ψ_prod]
          rw [hex]; exact pchar_of_prodChar_one_left χ₁
      have hval_n₁ : pcharZeroSeq (slotChar i) n₁ = (β₁ : ℂ) := by rw [hchar_eq, hn₁]
      rw [← hval_n₁]
      have hsingle : Summable (fun n : ℕ =>
          if n = n₁ then (1 : ℂ) / (slotPt i - pcharZeroSeq (slotChar i) n) ^ (k + 1) else 0) :=
        summable_of_ne_finset_zero (s := {n₁}) fun n hn => by simp [Finset.mem_singleton.not.mp hn]
      have hrest : Summable (fun n : ℕ =>
          if slotExcl i = some n then (0 : ℂ)
          else (1 : ℂ) / (slotPt i - pcharZeroSeq (slotChar i) n) ^ (k + 1)) :=
        Summable.of_norm_bounded hsumm.norm fun n => by
          split_ifs
          · rw [norm_zero]; exact norm_nonneg _
          · exact le_rfl
      have htsum_single :
          ∑' n : ℕ, (if n = n₁ then (1 : ℂ) / (slotPt i - pcharZeroSeq (slotChar i) n) ^ (k + 1) else 0) =
            (1 : ℂ) / (slotPt i - pcharZeroSeq (slotChar i) n₁) ^ (k + 1) := by
        rw [tsum_ite_eq]
      rw [← htsum_single, ← Summable.tsum_add hsingle hrest]
      refine tsum_congr fun n => ?_
      rw [hex]
      by_cases hnn₁ : n = n₁
      · subst hnn₁; simp
      · simp [hnn₁, Ne.symm hnn₁]
    · rw [if_neg hex, zero_add]
      have hnone : slotExcl i = none := by
        fin_cases i
        · rfl
        · simp [slotExcl] at hex
        · change (if ψ_s = ψ₁ then some n₁ else none) = none
          change (if ψ_s = ψ₁ then some n₁ else none) ≠ some n₁ at hex
          split_ifs at hex ⊢ <;> tauto
        · change (if ψ_s = ψ₀ then some n₁ else none) = none
          change (if ψ_s = ψ₀ then some n₁ else none) ≠ some n₁ at hex
          split_ifs at hex ⊢ <;> tauto
      refine tsum_congr fun n => by simp [hnone]
  -- Combine the pole-zero cancellation bounds at `s₀` and `s₁`!
  have hpz0 : ‖(1 : ℂ) / (slotPt 0 - 1) ^ (k + 1) - (1 : ℂ) / (slotPt 0 - (β₁ : ℂ)) ^ (k + 1)‖ ≤
      ((k + 1 : ℕ) : ℝ) * (1 - β₁) / μ ^ (k + 2) :=
    norm_inv_pow_sub_inv_pow_le hμ_pos (by simp [slotPt, slotIm]) hβ₁1 k
  have hpz1 : ‖(1 : ℂ) / (s₁ - 1) ^ (k + 1) - (1 : ℂ) / (s₁ - (β₁ : ℂ)) ^ (k + 1)‖ ≤
      ((k + 1 : ℕ) : ℝ) * (1 - β₁) / μ ^ (k + 2) :=
    norm_inv_pow_sub_inv_pow_le hμ_pos (by simp [s₁]) hβ₁1 k
  have hslot0_pt : slotPt 0 = ((1 + μ : ℝ) : ℂ) := by simp [slotPt, slotIm]
  have hslot1_pt : slotPt 1 = ((1 + μ : ℝ) : ℂ) := by simp [slotPt, slotIm]
  have hslot2_pt : slotPt 2 = s₁ := by simp [slotPt, slotIm, s₁]
  have hslot3_pt : slotPt 3 = s₁ := by simp [slotPt, slotIm, s₁]
  -- Assemble real-part inequality BEFORE scaling by `(2 μ)^(2 m)`!
  have hsum_zero_re :
      (∑ i : Fin 4,
        (∑' n : ℕ, if slotExcl i = some n then (0 : ℂ)
          else (1 : ℂ) / (slotPt i - pcharZeroSeq (slotChar i) n) ^ (k + 1)).re) ≤
        2 * (((k + 1 : ℕ) : ℝ) * (1 - β₁) / μ ^ (k + 2)) +
          4 * (C_E * (2 : ℝ) ^ k * L_max) := by
    set A0 := scaledDeriv k negLogDerivZeta ((1 + μ : ℝ) : ℂ)
    set A1 := scaledDeriv k (negLogDerivL χ₁) ((1 + μ : ℝ) : ℂ)
    set A2 := scaledDeriv k (negLogDerivL ψ_s.χ) s₁
    set A3 := scaledDeriv k (negLogDerivL (prodChar ψ_s.χ χ₁)) s₁
    set Z : Fin 4 → ℂ := fun i =>
      ∑' n : ℕ, if slotExcl i = some n then (0 : ℂ)
        else (1 : ℂ) / (slotPt i - pcharZeroSeq (slotChar i) n) ^ (k + 1)
    set P0 : ℂ := (1 : ℂ) / (((1 + μ : ℝ) : ℂ) - 1) ^ (k + 1) -
      (1 : ℂ) / (((1 + μ : ℝ) : ℂ) - (β₁ : ℂ)) ^ (k + 1)
    set P1 : ℂ := if ψ_s = ψ₀ ∨ ψ_s = ψ₁ then
      (1 : ℂ) / (s₁ - 1) ^ (k + 1) - (1 : ℂ) / (s₁ - (β₁ : ℂ)) ^ (k + 1) else 0
    have hP0_bd : P0.re ≤ ((k + 1 : ℕ) : ℝ) * (1 - β₁) / μ ^ (k + 2) := by
      refine ((le_abs_self _).trans (Complex.abs_re_le_norm _)).trans ?_
      rwa [hslot0_pt] at hpz0
    have hP1_bd : P1.re ≤ ((k + 1 : ℕ) : ℝ) * (1 - β₁) / μ ^ (k + 2) := by
      dsimp only [P1]
      split_ifs
      · exact ((le_abs_self _).trans (Complex.abs_re_le_norm _)).trans hpz1
      · simp; positivity
    have hE0' := ((le_abs_self _).trans (Complex.abs_re_le_norm _)).trans hE0_half
    have hE1' := ((le_abs_self _).trans (Complex.abs_re_le_norm _)).trans hE1
    have hE2' := ((le_abs_self _).trans (Complex.abs_re_le_norm _)).trans hE2
    have hE3' := ((le_abs_self _).trans (Complex.abs_re_le_norm _)).trans hE3
    have hp2' : ∑' n : ℕ, (1 : ℂ) / (s₁ - pcharZeroSeq ψ_s n) ^ (k + 1) =
        (if ψ_s = ψ₁ then (1 : ℂ) / (s₁ - (β₁ : ℂ)) ^ (k + 1) else 0) + Z 2 := by
      have h1 := hpull_excl 2
      rw [hslot2_pt] at h1
      change ∑' n : ℕ, (1 : ℂ) / (s₁ - pcharZeroSeq ψ_s n) ^ (k + 1) =
        (if (if ψ_s = ψ₁ then some n₁ else none) = some n₁ then (1 : ℂ) / (s₁ - (β₁ : ℂ)) ^ (k + 1) else 0) + Z 2 at h1
      by_cases h : ψ_s = ψ₁ <;> simp [h] at h1 ⊢ <;> exact h1
    have hp3' : ∑' n : ℕ, (1 : ℂ) / (s₁ - pcharZeroSeq ψ_prod n) ^ (k + 1) =
        (if ψ_s = ψ₀ then (1 : ℂ) / (s₁ - (β₁ : ℂ)) ^ (k + 1) else 0) + Z 3 := by
      have h1 := hpull_excl 3
      rw [hslot3_pt] at h1
      change ∑' n : ℕ, (1 : ℂ) / (s₁ - pcharZeroSeq ψ_prod n) ^ (k + 1) =
        (if (if ψ_s = ψ₀ then some n₁ else none) = some n₁ then (1 : ℂ) / (s₁ - (β₁ : ℂ)) ^ (k + 1) else 0) + Z 3 at h1
      by_cases h : ψ_s = ψ₀ <;> simp [h] at h1 ⊢ <;> exact h1
    have hψ₀_ne_ψ₁ : ψ₀ ≠ ψ₁ := fun h => hψ₁_ne1 (by rw [← h]; rfl)
    have hP1_eq :
        (if ψ_s = ψ₀ then (1 : ℂ) / (s₁ - 1) ^ (k + 1) else 0) -
            (if ψ_s = ψ₁ then (1 : ℂ) / (s₁ - (β₁ : ℂ)) ^ (k + 1) else 0) +
          ((if ψ_s = ψ₁ then (1 : ℂ) / (s₁ - 1) ^ (k + 1) else 0) -
            (if ψ_s = ψ₀ then (1 : ℂ) / (s₁ - (β₁ : ℂ)) ^ (k + 1) else 0)) = P1 := by
      dsimp only [P1]
      by_cases h0 : ψ_s = ψ₀
      · have h1 : ψ_s ≠ ψ₁ := by rw [h0]; exact hψ₀_ne_ψ₁
        simp_rw [if_pos h0, if_neg h1, if_pos (Or.inl h0)]; ring
      · by_cases h1 : ψ_s = ψ₁
        · simp_rw [if_neg h0, if_pos h1, if_pos (Or.inr h1)]; ring
        · simp_rw [if_neg h0, if_neg h1, if_neg (by tauto : ¬ (ψ_s = ψ₀ ∨ ψ_s = ψ₁))]; ring
    have hZ_sum : ∑ i : Fin 4, (Z i).re = (Z 0 + Z 1 + Z 2 + Z 3).re := by
      rw [Fin.sum_univ_four]; simp
    rw [hZ_sum]
    have hpos_re : 0 ≤ (A0 + A1 + (A2 + A3)).re := hpos_k
    have hre_id :
        (A0 + A1 + (A2 + A3)).re =
          P0.re + P1.re - (Z 0 + Z 1 + Z 2 + Z 3).re +
            (A0 - ((1 : ℂ) / (((1 + μ : ℝ) : ℂ) - 1) ^ (k + 1) -
              ∑' n : ℕ, (1 : ℂ) / (((1 + μ : ℝ) : ℂ) - pcharZeroSeq ψ₀ n) ^ (k + 1))).re +
            (A1 - (- ∑' n : ℕ, (1 : ℂ) / (((1 + μ : ℝ) : ℂ) - pcharZeroSeq ψ₁ n) ^ (k + 1))).re +
            (A2 - ((if ψ_s = ψ₀ then (1 : ℂ) / (s₁ - 1) ^ (k + 1) else 0) -
              ∑' n : ℕ, (1 : ℂ) / (s₁ - pcharZeroSeq ψ_s n) ^ (k + 1))).re +
            (A3 - ((if ψ_s = ψ₁ then (1 : ℂ) / (s₁ - 1) ^ (k + 1) else 0) -
              ∑' n : ℕ, (1 : ℂ) / (s₁ - pcharZeroSeq ψ_prod n) ^ (k + 1))).re := by
      have hC_id :
          A0 + A1 + (A2 + A3) =
            P0 + P1 - (Z 0 + Z 1 + Z 2 + Z 3) +
              (A0 - ((1 : ℂ) / (((1 + μ : ℝ) : ℂ) - 1) ^ (k + 1) -
                ∑' n : ℕ, (1 : ℂ) / (((1 + μ : ℝ) : ℂ) - pcharZeroSeq ψ₀ n) ^ (k + 1))) +
              (A1 - (- ∑' n : ℕ, (1 : ℂ) / (((1 + μ : ℝ) : ℂ) - pcharZeroSeq ψ₁ n) ^ (k + 1))) +
              (A2 - ((if ψ_s = ψ₀ then (1 : ℂ) / (s₁ - 1) ^ (k + 1) else 0) -
                ∑' n : ℕ, (1 : ℂ) / (s₁ - pcharZeroSeq ψ_s n) ^ (k + 1))) +
              (A3 - ((if ψ_s = ψ₁ then (1 : ℂ) / (s₁ - 1) ^ (k + 1) else 0) -
                ∑' n : ℕ, (1 : ℂ) / (s₁ - pcharZeroSeq ψ_prod n) ^ (k + 1))) := by
        have hp0' : ∑' n : ℕ, (1 : ℂ) / (((1 + μ : ℝ) : ℂ) - pcharZeroSeq ψ₀ n) ^ (k + 1) = Z 0 := by
          dsimp only [Z]; rw [← hslot0_pt]; simp [slotExcl, slotChar]
        have hp1' : ∑' n : ℕ, (1 : ℂ) / (((1 + μ : ℝ) : ℂ) - pcharZeroSeq ψ₁ n) ^ (k + 1) =
            (1 : ℂ) / (((1 + μ : ℝ) : ℂ) - (β₁ : ℂ)) ^ (k + 1) + Z 1 := by
          have := hpull_excl 1; dsimp only [Z]; rw [← hslot1_pt]; simpa [slotExcl, slotChar] using this
        rw [hp0', hp1', hp2', hp3', ← hP1_eq]
        dsimp only [P0]; ring
      have := congrArg Complex.re hC_id
      simpa [Complex.add_re, Complex.sub_re] using this
    linarith
  -- Multiply `hsum_zero_re` by `(2 * μ) ^ (2 * m)` and apply `re_tsum_split_inner_tail` to all 4 slots!
  have hmul_scale := mul_le_mul_of_nonneg_left hsum_zero_re (by positivity : (0 : ℝ) ≤ (2 * μ) ^ (2 * m))
  have htsum_scale : ∀ i : Fin 4,
      (2 * μ) ^ (2 * m) *
          (∑' n : ℕ, if slotExcl i = some n then (0 : ℂ)
            else (1 : ℂ) / (slotPt i - pcharZeroSeq (slotChar i) n) ^ (k + 1)).re =
        (∑' n : ℕ, if slotExcl i = some n then (0 : ℂ)
          else (((2 * μ : ℝ) : ℂ) / (slotPt i - pcharZeroSeq (slotChar i) n)) ^ (2 * m)).re := by
    intro i
    rw [← Complex.re_ofReal_mul, Complex.ofReal_pow, ← tsum_mul_left]
    congr 1; refine tsum_congr fun n => ?_
    split_ifs
    · simp
    · rw [hk_add1, div_pow]; ring
  rw [Finset.mul_sum] at hmul_scale
  simp_rw [htsum_scale] at hmul_scale
  have hsplit_all :
      ∑ i : Fin 4,
          ((∑ n ∈ innerFin i, (((2 * μ : ℝ) : ℂ) / (slotPt i - pcharZeroSeq (slotChar i) n)) ^ (2 * m)).re -
            ((2 / A) ^ (2 * m) * ((16 * C₁ + 16) * (A * (μ * L_max) + 1)) +
              4 * (2 * μ) ^ (2 * m) * (C₁ * L_max + 2))) ≤
        ∑ i : Fin 4,
          (∑' n : ℕ, if slotExcl i = some n then (0 : ℂ)
            else (((2 * μ : ℝ) : ℂ) / (slotPt i - pcharZeroSeq (slotChar i) n)) ^ (2 * m)).re := by
    refine Finset.sum_le_sum fun i _ => ?_
    exact re_tsum_split_inner_tail hC₁_pos.le hL_max_pos.le
      (pcharZeroSeq_strip (slotChar i)) (pcharZeroSeq_summable_inv_sq (slotChar i))
      (hslot_re_le i) hμ_pos hA_ge4 hR_le (slotExcl i) hm1
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_ofNat] at hsplit_all
  have hpole_simp :
      (2 * μ) ^ (2 * m) * (2 * (((k + 1 : ℕ) : ℝ) * (1 - β₁) / μ ^ (k + 2))) =
        4 * (m : ℝ) * ((1 - β₁) / μ) * 2 ^ (2 * m) := by
    have hk1R : ((k + 1 : ℕ) : ℝ) = 2 * (m : ℝ) := by exact_mod_cast hk_add1
    have hk2 : k + 2 = 2 * m + 1 := by omega
    rw [hk1R, hk2, mul_pow, pow_succ]
    field_simp [hμ_pos.ne']
    ring
  have herr_simp :
      (2 * μ) ^ (2 * m) * (4 * (C_E * (2 : ℝ) ^ k * L_max)) =
        4 * C_E * (2 * μ) ^ (2 * m) * (2 : ℝ) ^ (2 * m - 1) * L_max := by
    dsimp only [k]; ring
  rw [mul_add, hpole_simp, herr_simp] at hmul_scale
  dsimp only [k]
  linarith

/-- Helper: pure real-algebra extraction of the Deuring–Heilbronn bound from the Fejér-weighted
inner zero sum and per-`m` Hadamard upper bound (keeps all scalar parameters opaque for instant
kernel checking). -/
private lemma deuring_heilbronn_algebraic_extraction
    {C₁ C_E c_cl A C_M C_L c₂ c₁ L δ₁ μ β₁ L_max ε ρ_re : ℝ} {M N : ℕ}
    (hC₁_pos : 0 < C₁) (hC_E_pos : 0 < C_E) (hc_cl_pos : 0 < c_cl)
    (hA_ge4 : 4 ≤ A) (hA_big : 2048 * (16 * C₁ + 16) ≤ A)
    (hC_M_pos : 0 < C_M) (hC_L_pos : 0 < C_L)
    (hc₁_pos : 0 < c₁) (hc₁_le : c₁ ≤ 1 / (3 * C_M * C_L))
    (hc₂_pos : 0 < c₂) (hc₂_le : c₂ ≤ (3 * c_cl / (8 * C_L)) * Real.exp (-(3 * (C_M + 4))))
    (hL_pos : 0 < L) (hδ₁_pos : 0 < δ₁) (hδ₁_eq : δ₁ = (1 - β₁) * L)
    (hβ₁1 : β₁ < 1) (hre1 : ρ_re < 1)
    (hμ_pos : 0 < μ) (hμ_le_ρ : μ ≤ 1 - ρ_re)
    (hμ_C₁ : μ ≤ 1 / (1024 * C₁ + 1024)) (hμ_CE : μ ≤ 1 / (512 * C_E + 32))
    (hL_max_pos : 0 < L_max) (hL_max_le : L_max ≤ C_L * L)
    (hlam_ge_cl : c_cl ≤ μ * L_max)
    (hε_pos : 0 < ε) (hε_le : ε ≤ 1 / 4)
    (hN_pos : 0 < N) (hM_eq : M = 2 * N + 2 * Nat.ceil (μ * L_max) + 1)
    (hM_le_CM : (M : ℝ) ≤ C_M * (μ * L_max + 1) + 4)
    {f : ℕ → ℝ}
    (hfejer : (3 / 4 : ℝ) * (μ * L_max + 1) ≤
      ∑ m ∈ Finset.Icc 1 (M - 1), (1 - (m : ℝ) / (M : ℝ)) * (1 - ε) ^ (2 * m) * f m)
    (hper_m : ∀ m ∈ Finset.Icc 1 (M - 1),
      f m ≤ 4 * (m : ℝ) * ((1 - β₁) / μ) * (2 : ℝ) ^ (2 * m) +
        4 * C_E * (2 * μ) ^ (2 * m) * (2 : ℝ) ^ (2 * m - 1) * L_max +
        4 * ((2 / A) ^ (2 * m) * ((16 * C₁ + 16) * (A * (μ * L_max) + 1)) +
          4 * (2 * μ) ^ (2 * m) * (C₁ * L_max + 2))) :
    c₁ * Real.log (c₂ / δ₁) / L ≤ 1 - ρ_re := by
  have hA_pos : 0 < A := by linarith
  have hlam_pos : 0 < μ * L_max := mul_pos hμ_pos hL_max_pos
  have hM_ge1 : 1 ≤ M := by omega
  have hwt_bounds : ∀ m ∈ Finset.Icc 1 (M - 1),
      0 ≤ (1 - (m : ℝ) / (M : ℝ)) * (1 - ε) ^ (2 * m) ∧
      (1 - (m : ℝ) / (M : ℝ)) * (1 - ε) ^ (2 * m) ≤ 1 := by
    intro m hm
    have hmM : (m : ℝ) ≤ (M : ℝ) := by
      exact_mod_cast (show m ≤ M by have := (Finset.mem_Icc.mp hm).2; omega)
    have hM_pos : (0 : ℝ) < (M : ℝ) := Nat.cast_pos.mpr hM_ge1
    have hdiv_le : (m : ℝ) / (M : ℝ) ≤ 1 := (div_le_one hM_pos).mpr hmM
    have hdiv_nn : 0 ≤ (m : ℝ) / (M : ℝ) := div_nonneg (Nat.cast_nonneg m) hM_pos.le
    have h1ε_nn : 0 ≤ 1 - ε := by linarith
    have h1ε_le1 : 1 - ε ≤ 1 := by linarith
    have hpow_le1 : (1 - ε) ^ (2 * m) ≤ 1 := pow_le_one₀ h1ε_nn h1ε_le1
    refine ⟨mul_nonneg (by linarith) (pow_nonneg h1ε_nn _), ?_⟩
    calc (1 - (m : ℝ) / (M : ℝ)) * (1 - ε) ^ (2 * m)
        ≤ 1 * 1 := mul_le_mul (by linarith) hpow_le1 (pow_nonneg h1ε_nn _) zero_le_one
      _ = 1 := one_mul 1
  have hsum_all :
      (3 / 4 : ℝ) * (μ * L_max + 1) ≤
        (∑ m ∈ Finset.Icc 1 (M - 1), 4 * (m : ℝ) * ((1 - β₁) / μ) * (2 : ℝ) ^ (2 * m)) +
        (∑ m ∈ Finset.Icc 1 (M - 1), 4 * C_E * (2 * μ) ^ (2 * m) * (2 : ℝ) ^ (2 * m - 1) * L_max) +
        (∑ m ∈ Finset.Icc 1 (M - 1), 4 * ((2 / A) ^ (2 * m) * ((16 * C₁ + 16) * (A * (μ * L_max) + 1)))) +
        (∑ m ∈ Finset.Icc 1 (M - 1), 16 * (2 * μ) ^ (2 * m) * (C₁ * L_max + 2)) := by
    refine hfejer.trans ?_
    have hstep1 :
        ∑ m ∈ Finset.Icc 1 (M - 1), (1 - (m : ℝ) / (M : ℝ)) * (1 - ε) ^ (2 * m) * f m ≤
          ∑ m ∈ Finset.Icc 1 (M - 1),
            (4 * (m : ℝ) * ((1 - β₁) / μ) * (2 : ℝ) ^ (2 * m) +
              4 * C_E * (2 * μ) ^ (2 * m) * (2 : ℝ) ^ (2 * m - 1) * L_max +
              4 * ((2 / A) ^ (2 * m) * ((16 * C₁ + 16) * (A * (μ * L_max) + 1))) +
              16 * (2 * μ) ^ (2 * m) * (C₁ * L_max + 2)) := by
      refine Finset.sum_le_sum fun m hm => ?_
      have hwb := hwt_bounds m hm
      have hpm := hper_m m hm
      have hrhs_nn : 0 ≤ 4 * (m : ℝ) * ((1 - β₁) / μ) * (2 : ℝ) ^ (2 * m) +
          4 * C_E * (2 * μ) ^ (2 * m) * (2 : ℝ) ^ (2 * m - 1) * L_max +
          4 * ((2 / A) ^ (2 * m) * ((16 * C₁ + 16) * (A * (μ * L_max) + 1))) +
          16 * (2 * μ) ^ (2 * m) * (C₁ * L_max + 2) := by
        have h1 : 0 ≤ (1 - β₁) / μ := div_nonneg (by linarith) hμ_pos.le
        positivity
      calc (1 - (m : ℝ) / (M : ℝ)) * (1 - ε) ^ (2 * m) * f m
          ≤ (1 - (m : ℝ) / (M : ℝ)) * (1 - ε) ^ (2 * m) *
              (4 * (m : ℝ) * ((1 - β₁) / μ) * (2 : ℝ) ^ (2 * m) +
                4 * C_E * (2 * μ) ^ (2 * m) * (2 : ℝ) ^ (2 * m - 1) * L_max +
                4 * ((2 / A) ^ (2 * m) * ((16 * C₁ + 16) * (A * (μ * L_max) + 1))) +
                16 * (2 * μ) ^ (2 * m) * (C₁ * L_max + 2)) :=
            mul_le_mul_of_nonneg_left (by linarith) hwb.1
        _ ≤ 1 * _ := mul_le_mul_of_nonneg_right hwb.2 hrhs_nn
        _ = _ := one_mul _
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib] at hstep1
    exact hstep1
  have hgeom_le : ∀ (r : ℝ) (K : ℕ), 0 ≤ r → r ≤ 1 / 2 →
      ∑ m ∈ Finset.Icc 1 K, r ^ m ≤ 2 * r := by
    intro r K hr0 hr1
    have hshift : ∑ m ∈ Finset.Icc 1 K, r ^ m = r * ∑ j ∈ Finset.range K, r ^ j := by
      rw [Finset.mul_sum]
      refine Finset.sum_nbij' (fun m => m - 1) (fun j => j + 1) ?_ ?_ ?_ ?_ ?_
      · intro m hm; simp only [Finset.mem_Icc, Finset.mem_range] at hm ⊢; omega
      · intro j hj; simp only [Finset.mem_Icc, Finset.mem_range] at hj ⊢; omega
      · intro m hm; simp only [Finset.mem_Icc] at hm; omega
      · intro j _; omega
      · intro m hm
        have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
        have : m = (m - 1) + 1 := by omega
        conv_lhs => rw [this, pow_succ]
        ring
    rw [hshift, geom_sum_eq (by linarith : r ≠ 1)]
    have h2 : (r ^ K - 1) / (r - 1) ≤ 2 := by
      have hden : r - 1 < 0 := by linarith
      rw [div_le_iff_of_neg hden]
      have hpow : 0 ≤ r ^ K := pow_nonneg hr0 K
      linarith
    exact (mul_le_mul_of_nonneg_left h2 hr0).trans (by ring_nf; exact le_rfl)
  -- Error 1 (digamma + Euler)
  have herr_dig :
      ∑ m ∈ Finset.Icc 1 (M - 1), 4 * C_E * (2 * μ) ^ (2 * m) * (2 : ℝ) ^ (2 * m - 1) * L_max ≤
        (1 / 8 : ℝ) * (μ * L_max + 1) := by
    have hterm : ∀ m ∈ Finset.Icc 1 (M - 1),
        4 * C_E * (2 * μ) ^ (2 * m) * (2 : ℝ) ^ (2 * m - 1) * L_max =
          (2 * C_E * L_max) * ((4 * μ) ^ 2) ^ m := by
      intro m hm
      have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
      have h2m : 2 * m = (2 * m - 1) + 1 := by omega
      rw [← pow_mul, mul_pow, mul_pow]
      have h4pow : (4 : ℝ) ^ (2 * m) = (2 : ℝ) ^ (2 * m) * (2 : ℝ) ^ (2 * m) := by
        rw [← mul_pow]; norm_num
      have h2split : (2 : ℝ) ^ (2 * m) = (2 : ℝ) ^ (2 * m - 1) * 2 := by
        conv_lhs => rw [h2m, pow_succ]
      rw [h4pow, h2split]
      ring
    rw [show ∑ m ∈ Finset.Icc 1 (M - 1), 4 * C_E * (2 * μ) ^ (2 * m) * (2 : ℝ) ^ (2 * m - 1) * L_max =
        (2 * C_E * L_max) * ∑ m ∈ Finset.Icc 1 (M - 1), ((4 * μ) ^ 2) ^ m by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl hterm]
    have h4μ_le : (4 * μ) ^ 2 ≤ 1 / 2 := by
      have h1 : μ ≤ 1 / 32 := hμ_CE.trans (one_div_le_one_div_of_le (by norm_num) (by linarith))
      calc (4 * μ) ^ 2 ≤ (1 / 8 : ℝ) ^ 2 := pow_le_pow_left₀ (by positivity) (by linarith) 2
        _ ≤ 1 / 2 := by norm_num
    have hg := hgeom_le ((4 * μ) ^ 2) (M - 1) (sq_nonneg _) h4μ_le
    calc (2 * C_E * L_max) * ∑ m ∈ Finset.Icc 1 (M - 1), ((4 * μ) ^ 2) ^ m
        ≤ (2 * C_E * L_max) * (2 * (4 * μ) ^ 2) :=
          mul_le_mul_of_nonneg_left hg (by positivity)
      _ = 64 * C_E * μ * (μ * L_max) := by ring
      _ ≤ (1 / 8 : ℝ) * (μ * L_max) := by
          have h1 : 64 * C_E * μ ≤ 1 / 8 := by
            have h2 : 64 * C_E * (1 / (512 * C_E + 32)) ≤ 1 / 8 := by
              rw [mul_one_div, div_le_iff₀ (by positivity)]; linarith
            have h3 := mul_le_mul_of_nonneg_left hμ_CE (by positivity : (0 : ℝ) ≤ 64 * C_E)
            linarith
          exact mul_le_mul_of_nonneg_right h1 hlam_pos.le
      _ ≤ (1 / 8 : ℝ) * (μ * L_max + 1) := by linarith
  -- Error 2 (medium tail)
  have herr_med :
      ∑ m ∈ Finset.Icc 1 (M - 1), 4 * ((2 / A) ^ (2 * m) * ((16 * C₁ + 16) * (A * (μ * L_max) + 1))) ≤
        (1 / 8 : ℝ) * (μ * L_max + 1) := by
    rw [show ∑ m ∈ Finset.Icc 1 (M - 1), 4 * ((2 / A) ^ (2 * m) * ((16 * C₁ + 16) * (A * (μ * L_max) + 1))) =
        (4 * (16 * C₁ + 16) * (A * (μ * L_max) + 1)) * ∑ m ∈ Finset.Icc 1 (M - 1), ((2 / A) ^ 2) ^ m by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun m _ => by rw [← pow_mul]; ring]
    have h2A_le : (2 / A) ^ 2 ≤ 1 / 2 := by
      have h1 : 2 / A ≤ 1 / 2 := by rw [div_le_iff₀ hA_pos]; linarith
      calc (2 / A) ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
        _ ≤ 1 / 2 := by norm_num
    have hg := hgeom_le ((2 / A) ^ 2) (M - 1) (sq_nonneg _) h2A_le
    calc (4 * (16 * C₁ + 16) * (A * (μ * L_max) + 1)) * ∑ m ∈ Finset.Icc 1 (M - 1), ((2 / A) ^ 2) ^ m
        ≤ (4 * (16 * C₁ + 16) * (A * (μ * L_max) + 1)) * (2 * (2 / A) ^ 2) :=
          mul_le_mul_of_nonneg_left hg (by positivity)
      _ ≤ (4 * (16 * C₁ + 16) * (A * (μ * L_max + 1))) * (2 * (2 / A) ^ 2) := by
          have h1 : A * (μ * L_max) + 1 ≤ A * (μ * L_max + 1) := by linarith
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 (by positivity)) (by positivity)
      _ = (32 * (16 * C₁ + 16) / A) * (μ * L_max + 1) := by field_simp [hA_pos.ne']; ring
      _ ≤ (1 / 8 : ℝ) * (μ * L_max + 1) := by
          have h1 : 32 * (16 * C₁ + 16) / A ≤ 1 / 8 := by rw [div_le_iff₀ hA_pos]; linarith
          exact mul_le_mul_of_nonneg_right h1 (by positivity)
  -- Error 3 (far tail)
  have herr_far :
      ∑ m ∈ Finset.Icc 1 (M - 1), 16 * (2 * μ) ^ (2 * m) * (C₁ * L_max + 2) ≤
        (1 / 8 : ℝ) * (μ * L_max + 1) := by
    rw [show ∑ m ∈ Finset.Icc 1 (M - 1), 16 * (2 * μ) ^ (2 * m) * (C₁ * L_max + 2) =
        (16 * (C₁ * L_max + 2)) * ∑ m ∈ Finset.Icc 1 (M - 1), ((2 * μ) ^ 2) ^ m by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun m _ => by rw [← pow_mul]; ring]
    have hμ_le_64 : μ ≤ 1 / 64 := hμ_C₁.trans (one_div_le_one_div_of_le (by norm_num) (by linarith))
    have h2μ_le : (2 * μ) ^ 2 ≤ 1 / 2 := by
      calc (2 * μ) ^ 2 ≤ (1 / 32 : ℝ) ^ 2 := pow_le_pow_left₀ (by positivity) (by linarith) 2
        _ ≤ 1 / 2 := by norm_num
    have hg := hgeom_le ((2 * μ) ^ 2) (M - 1) (sq_nonneg _) h2μ_le
    calc (16 * (C₁ * L_max + 2)) * ∑ m ∈ Finset.Icc 1 (M - 1), ((2 * μ) ^ 2) ^ m
        ≤ (16 * (C₁ * L_max + 2)) * (2 * (2 * μ) ^ 2) :=
          mul_le_mul_of_nonneg_left hg (by positivity)
      _ = 128 * μ * (C₁ * (μ * L_max) + 2 * μ) := by ring
      _ ≤ 128 * μ * ((C₁ + 1) * (μ * L_max + 1)) := by
          have h1 : C₁ * (μ * L_max) + 2 * μ ≤ (C₁ + 1) * (μ * L_max + 1) := by
            have : (C₁ + 1) * (μ * L_max + 1) - (C₁ * (μ * L_max) + 2 * μ) = C₁ + μ * L_max + (1 - 2 * μ) := by ring
            linarith
          exact mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = (128 * (C₁ + 1) * μ) * (μ * L_max + 1) := by ring
      _ ≤ (1 / 8 : ℝ) * (μ * L_max + 1) := by
          have h1 : 128 * (C₁ + 1) * μ ≤ 1 / 8 := by
            have h2 : 128 * (C₁ + 1) * (1 / (1024 * C₁ + 1024)) = 1 / 8 := by
              field_simp [(by positivity : (1024 * C₁ + 1024) ≠ 0)]; ring
            have h3 := mul_le_mul_of_nonneg_left hμ_C₁ (by positivity : (0 : ℝ) ≤ 128 * (C₁ + 1))
            linarith
          exact mul_le_mul_of_nonneg_right h1 (by positivity)
  -- Pole-Zero Sum
  have hpole_sum :
      ∑ m ∈ Finset.Icc 1 (M - 1), 4 * (m : ℝ) * ((1 - β₁) / μ) * (2 : ℝ) ^ (2 * m) ≤
        4 * (M : ℝ) * ((1 - β₁) / μ) * (4 : ℝ) ^ M := by
    have h4geom : ∑ m ∈ Finset.Icc 1 (M - 1), (4 : ℝ) ^ m ≤ (4 : ℝ) ^ M := by
      have h1 : ∑ m ∈ Finset.Icc 1 (M - 1), (4 : ℝ) ^ m ≤ ∑ m ∈ Finset.range M, (4 : ℝ) ^ m := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (fun m hm => ?_) (fun _ _ _ => by positivity)
        simp only [Finset.mem_Icc, Finset.mem_range] at hm ⊢; omega
      rw [geom_sum_eq (by norm_num : (4 : ℝ) ≠ 1) M] at h1
      have : (1 : ℝ) ≤ (4 : ℝ) ^ M := one_le_pow₀ (by norm_num)
      linarith
    calc ∑ m ∈ Finset.Icc 1 (M - 1), 4 * (m : ℝ) * ((1 - β₁) / μ) * (2 : ℝ) ^ (2 * m)
        ≤ ∑ m ∈ Finset.Icc 1 (M - 1), (4 * (M : ℝ) * ((1 - β₁) / μ)) * (4 : ℝ) ^ m := by
          refine Finset.sum_le_sum fun m hm => ?_
          have hmM : (m : ℝ) ≤ (M : ℝ) := by
            exact_mod_cast (show m ≤ M by have := (Finset.mem_Icc.mp hm).2; omega)
          have h24 : (2 : ℝ) ^ (2 * m) = (4 : ℝ) ^ m := by rw [pow_mul]; norm_num
          rw [h24]
          have hnn : 0 ≤ ((1 - β₁) / μ) * (4 : ℝ) ^ m :=
            mul_nonneg (div_nonneg (by linarith) hμ_pos.le) (by positivity)
          have h1 := mul_le_mul_of_nonneg_right (show 4 * (m : ℝ) ≤ 4 * (M : ℝ) by linarith) hnn
          linarith [show 4 * (m : ℝ) * (((1 - β₁) / μ) * (4 : ℝ) ^ m) = 4 * (m : ℝ) * ((1 - β₁) / μ) * (4 : ℝ) ^ m by ring,
            show 4 * (M : ℝ) * (((1 - β₁) / μ) * (4 : ℝ) ^ m) = (4 * (M : ℝ) * ((1 - β₁) / μ)) * (4 : ℝ) ^ m by ring]
      _ = (4 * (M : ℝ) * ((1 - β₁) / μ)) * ∑ m ∈ Finset.Icc 1 (M - 1), (4 : ℝ) ^ m :=
          (Finset.mul_sum _ _ _).symm
      _ ≤ 4 * (M : ℝ) * ((1 - β₁) / μ) * (4 : ℝ) ^ M :=
          mul_le_mul_of_nonneg_left h4geom (mul_nonneg (by positivity) (div_nonneg (by linarith) hμ_pos.le))
  -- Final extraction
  have hmain : (3 / 8 : ℝ) * (μ * L_max + 1) ≤ 4 * (M : ℝ) * ((1 - β₁) / μ) * (4 : ℝ) ^ M := by linarith
  have hmul_lam : (3 / 8 : ℝ) * c_cl ≤ 4 * (M : ℝ) * (4 : ℝ) ^ M * ((1 - β₁) * L_max) := by
    have h1 := mul_le_mul_of_nonneg_right hmain hlam_pos.le
    have hrhs : 4 * (M : ℝ) * ((1 - β₁) / μ) * (4 : ℝ) ^ M * (μ * L_max) =
        4 * (M : ℝ) * (4 : ℝ) ^ M * ((1 - β₁) * L_max) := by
      field_simp [hμ_pos.ne']
    rw [hrhs] at h1
    have hlhs : (3 / 8 : ℝ) * c_cl ≤ (3 / 8 : ℝ) * (μ * L_max + 1) * (μ * L_max) := by
      have hsq : 0 ≤ (3 / 8 : ℝ) * (μ * L_max) * (μ * L_max) := by positivity
      linarith [show (3 / 8 : ℝ) * (μ * L_max + 1) * (μ * L_max) =
        (3 / 8 : ℝ) * (μ * L_max) * (μ * L_max) + (3 / 8 : ℝ) * (μ * L_max) by ring]
    exact hlhs.trans h1
  have h4M_exp : 4 * (M : ℝ) * (4 : ℝ) ^ M ≤ Real.exp (3 * (M : ℝ)) := by
    have h4M_le : 4 * (M : ℝ) ≤ (2 : ℝ) ^ M := by
      have hceil1 : 1 ≤ Nat.ceil (μ * L_max) :=
        Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr hlam_pos).ne'
      have hM5 : 5 ≤ M := by omega
      have hind : ∀ k : ℕ, 5 ≤ k → 4 * (k : ℝ) ≤ (2 : ℝ) ^ k := by
        intro k hk
        induction k with
        | zero => omega
        | succ k ih =>
          rcases eq_or_lt_of_le (show 5 ≤ k + 1 from hk) with h5 | hgt
          · rw [← h5]; norm_num
          · have hk5 : 5 ≤ k := by omega
            have hk5R : (5 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk5
            have hprev := ih hk5
            rw [pow_succ]; push_cast; linarith
      exact hind M hM5
    have h8_le : (8 : ℝ) ^ M ≤ Real.exp (3 * (M : ℝ)) := by
      have h8e3 : (8 : ℝ) ≤ Real.exp 3 := by
        have h1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
        calc (8 : ℝ) = (2 : ℝ) ^ 3 := by norm_num
          _ ≤ (Real.exp 1) ^ 3 := pow_le_pow_left₀ (by norm_num) h1 3
          _ = Real.exp 3 := by rw [← Real.exp_nat_mul]; norm_num
      calc (8 : ℝ) ^ M ≤ (Real.exp 3) ^ M := pow_le_pow_left₀ (by norm_num) h8e3 M
        _ = Real.exp (3 * (M : ℝ)) := by rw [← Real.exp_nat_mul]; ring_nf
    calc 4 * (M : ℝ) * (4 : ℝ) ^ M
        ≤ (2 : ℝ) ^ M * (4 : ℝ) ^ M := mul_le_mul_of_nonneg_right h4M_le (by positivity)
      _ = (8 : ℝ) ^ M := by rw [← mul_pow]; norm_num
      _ ≤ Real.exp (3 * (M : ℝ)) := h8_le
  have h1β₁_L : (1 - β₁) * L_max ≤ C_L * δ₁ := by
    rw [hδ₁_eq]
    calc (1 - β₁) * L_max ≤ (1 - β₁) * (C_L * L) := mul_le_mul_of_nonneg_left hL_max_le (by linarith)
      _ = C_L * ((1 - β₁) * L) := by ring
  have hM_le_ρ : (M : ℝ) ≤ C_M * C_L * ((1 - ρ_re) * L) + C_M + 4 := by
    have hlam_le_ρ : μ * L_max ≤ C_L * ((1 - ρ_re) * L) := by
      calc μ * L_max ≤ (1 - ρ_re) * (C_L * L) :=
            mul_le_mul hμ_le_ρ hL_max_le hL_max_pos.le (by linarith)
        _ = C_L * ((1 - ρ_re) * L) := by ring
    linarith [mul_le_mul_of_nonneg_left (show μ * L_max + 1 ≤ C_L * ((1 - ρ_re) * L) + 1 by linarith) hC_M_pos.le,
      show C_M * (C_L * ((1 - ρ_re) * L) + 1) = C_M * C_L * ((1 - ρ_re) * L) + C_M by ring]
  have hfinal_exp :
      (3 * c_cl / (8 * C_L)) / δ₁ ≤ Real.exp (3 * (C_M * C_L * ((1 - ρ_re) * L) + C_M + 4)) := by
    have h1 : (3 / 8 : ℝ) * c_cl ≤ Real.exp (3 * (M : ℝ)) * (C_L * δ₁) := by
      calc (3 / 8 : ℝ) * c_cl
          ≤ 4 * (M : ℝ) * (4 : ℝ) ^ M * ((1 - β₁) * L_max) := hmul_lam
        _ ≤ Real.exp (3 * (M : ℝ)) * (C_L * δ₁) :=
            mul_le_mul h4M_exp h1β₁_L (mul_nonneg (by linarith) hL_max_pos.le) (Real.exp_pos _).le
    have h2 : Real.exp (3 * (M : ℝ)) ≤ Real.exp (3 * (C_M * C_L * ((1 - ρ_re) * L) + C_M + 4)) :=
      Real.exp_le_exp.mpr (by linarith)
    have h3 : (3 / 8 : ℝ) * c_cl ≤
        Real.exp (3 * (C_M * C_L * ((1 - ρ_re) * L) + C_M + 4)) * (C_L * δ₁) :=
      h1.trans (mul_le_mul_of_nonneg_right h2 (by positivity))
    rw [div_le_iff₀ hδ₁_pos]
    have h4 : (3 * c_cl / (8 * C_L)) = ((3 / 8 : ℝ) * c_cl) / C_L := by field_simp [hC_L_pos.ne']
    rw [h4, div_le_iff₀ hC_L_pos]
    linarith [show Real.exp (3 * (C_M * C_L * ((1 - ρ_re) * L) + C_M + 4)) * δ₁ * C_L =
      Real.exp (3 * (C_M * C_L * ((1 - ρ_re) * L) + C_M + 4)) * (C_L * δ₁) by ring]
  have hlog_final := Real.log_le_log (by positivity) hfinal_exp
  rw [Real.log_exp] at hlog_final
  have hlog_c₂ : Real.log (c₂ / δ₁) ≤ 3 * C_M * C_L * ((1 - ρ_re) * L) := by
    have h1 : c₂ / δ₁ ≤ ((3 * c_cl / (8 * C_L)) / δ₁) * Real.exp (-(3 * (C_M + 4))) := by
      have : ((3 * c_cl / (8 * C_L)) / δ₁) * Real.exp (-(3 * (C_M + 4))) =
          ((3 * c_cl / (8 * C_L)) * Real.exp (-(3 * (C_M + 4)))) / δ₁ := by ring
      rw [this]
      exact div_le_div_of_nonneg_right hc₂_le hδ₁_pos.le
    calc Real.log (c₂ / δ₁)
        ≤ Real.log (((3 * c_cl / (8 * C_L)) / δ₁) * Real.exp (-(3 * (C_M + 4)))) :=
          Real.log_le_log (by positivity) h1
      _ = Real.log ((3 * c_cl / (8 * C_L)) / δ₁) + (-(3 * (C_M + 4))) := by
          rw [Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp]
      _ ≤ 3 * C_M * C_L * ((1 - ρ_re) * L) := by linarith
  have h1 : c₁ * Real.log (c₂ / δ₁) ≤ (1 - ρ_re) * L := by
    by_cases hlog_nn : 0 ≤ Real.log (c₂ / δ₁)
    · calc c₁ * Real.log (c₂ / δ₁)
          ≤ (1 / (3 * C_M * C_L)) * (3 * C_M * C_L * ((1 - ρ_re) * L)) :=
            mul_le_mul hc₁_le hlog_c₂ hlog_nn (by positivity)
        _ = (1 - ρ_re) * L := by field_simp [(by positivity : (3 * C_M * C_L) ≠ 0)]
    · push Not at hlog_nn
      have hneg : c₁ * Real.log (c₂ / δ₁) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hc₁_pos.le hlog_nn.le
      have hpos_r : 0 ≤ (1 - ρ_re) * L := mul_nonneg (by linarith) hL_pos.le
      linarith
  exact (div_le_iff₀ hL_pos).mpr h1

/-- **UNCONDITIONAL DEURING–HEILBRONN ZERO-REPULSION THEOREM (`0` ASSUMPTIONS!)**:
directly on Mathlib's `DirichletCharacter.LFunction`!
If a real primitive non-principal character `χ₁ mod q₁` (`q₁ ≤ Q`) has a real zero `β₁ ∈ (1/2, 1)`
with `(1 - β₁) * Real.log (Q * T) ≤ c₃`, then EVERY other zero `ρ` (`0 < ρ.re < 1`, `|ρ.im| ≤ T`)
of EVERY Dirichlet character `χ mod q` (`q ≤ Q`) with `(ρ ≠ β₁ ∨ PChar.of χ ≠ PChar.of χ₁)`
is repelled from `Re(s) = 1` by:
`1 - ρ.re ≥ c₁ * Real.log (c₂ / ((1 - β₁) * Real.log (Q * T))) / Real.log (Q * T)`. -/
theorem deuring_heilbronn_zero_repulsion :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ c₂ : ℝ, 0 < c₂ ∧ ∃ c₃ : ℝ, 0 < c₃ ∧
      ∀ (Q : ℕ) (T : ℝ), 2 ≤ Q → 2 ≤ T →
      ∀ (q₁ : ℕ) [NeZero q₁] (χ₁ : DirichletCharacter ℂ q₁),
        q₁ ≤ Q → χ₁.IsPrimitive → χ₁ ^ 2 = 1 → χ₁ ≠ 1 →
      ∀ β₁ : ℝ, 1 / 2 < β₁ → β₁ < 1 → DirichletCharacter.LFunction χ₁ (β₁ : ℂ) = 0 →
        (1 - β₁) * Real.log ((Q : ℝ) * T) ≤ c₃ →
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (ρ : ℂ),
        q ≤ Q → |ρ.im| ≤ T → 0 < ρ.re → ρ.re < 1 →
        DirichletCharacter.LFunction χ ρ = 0 →
        (ρ ≠ (β₁ : ℂ) ∨ PChar.of χ ≠ PChar.of χ₁) →
        c₁ * Real.log (c₂ / ((1 - β₁) * Real.log ((Q : ℝ) * T))) / Real.log ((Q : ℝ) * T) ≤
          1 - ρ.re := by
  classical
  -- Unpack all unconditional Stage 7/8/9/11 constants (ZERO assumptions!)
  obtain ⟨C_H, hC_H_pos, hZ_bd, hL_bd⟩ := Stage8HadamardLFunction.re_negLogDeriv_le_sub_finset_unconditional
  obtain ⟨C₁, hC₁_pos, hreZ, hreL⟩ := re_finset_zero_sum_le_unconditional
  obtain ⟨C_E, hC_E_pos, hsdZ, hsdL⟩ := scaledDeriv_hadamard_expansion_unconditional
  obtain ⟨c_cl, hc_cl_pos, hclass⟩ := classical_nonexceptional_zeroFree_orbit
  obtain ⟨C_S, hC_S_pos, hsiegel⟩ := Stage9LandauSiegel.siegel_real_zero_exclusion 1 zero_lt_one
  -- Explicit non-circular absolute constants
  set A : ℝ := max 4 (2048 * (16 * C₁ + 16))
  have hA_ge4 : 4 ≤ A := le_max_left _ _
  have hA_pos : 0 < A := by linarith
  set c_max : ℝ := min (1 / (2 * A)) (min (1 / (1024 * C₁ + 1024)) (min (1 / (512 * C_E + 32)) (1 / 16)))
  have hc_max_pos : 0 < c_max := by positivity
  have hc_max_le_16 : c_max ≤ 1 / 16 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  set C_N : ℝ := 16 * C₁ * A + 32
  have hC_N_pos : 0 < C_N := by positivity
  set C_M : ℝ := 2 * C_N + 4
  have hC_M_pos : 0 < C_M := by positivity
  -- Choose `C_L ≥ 16` large enough so `log(Q^2 (T + J + 2)) ≤ C_L * log(Q * T)`!
  set K_stop : ℝ := 32 * C_M * (1 / c_cl + 2)
  have hK_stop_pos : 0 < K_stop := by positivity
  set C_b : ℝ := 8 * K_stop + 4
  have hC_b_pos : 0 < C_b := by positivity
  set C_L : ℝ := max 16 (2 * (Real.log C_b + 5))
  have hC_L_ge16 : 16 ≤ C_L := le_max_left _ _
  have hC_L_pos : 0 < C_L := by linarith
  have hC_L_self : Real.log C_b + 2 * Real.log C_L + 4 ≤ C_L := by
    have hlogCL : 2 * Real.log C_L ≤ C_L / 2 := by
      have h1 : Real.log (C_L / 8) ≤ C_L / 8 - 1 :=
        Real.log_le_sub_one_of_pos (by linarith)
      rw [Real.log_div hC_L_pos.ne' (by norm_num)] at h1
      have hlog8 : Real.log 8 ≤ 3 * (0.7 : ℝ) := by
        have h8 : (8 : ℝ) = 2 ^ 3 := by norm_num
        rw [h8, Real.log_pow]; norm_num
        linarith [Real.log_two_lt_d9]
      linarith
    have h2 : Real.log C_b + 5 ≤ C_L / 2 := by
      have := le_max_right (16 : ℝ) (2 * (Real.log C_b + 5))
      linarith
    linarith
  -- Final headline constants `(c₁, c₂, c₃)`
  set c₂_raw : ℝ := 3 * c_cl * Real.exp (-(3 * (C_M + 4))) / (8 * C_L)
  set c₂ : ℝ := min c₂_raw C_S
  have hc₂_pos : 0 < c₂ := lt_min (by positivity) hC_S_pos
  set c₁ : ℝ := min (1 / (3 * C_M * C_L)) (c_max / 2)
  have hc₁_pos : 0 < c₁ := lt_min (by positivity) (by positivity)
  set c₃ : ℝ := min (c_cl / 4) (1 / (24 * C_H))
  have hc₃_pos : 0 < c₃ := lt_min (by positivity) (by positivity)
  refine ⟨c₁, hc₁_pos, c₂, hc₂_pos, c₃, hc₃_pos,
    fun Q T hQ hT q₁ _ χ₁ hq₁ hprim₁ hsq₁ hχ₁ β₁ hβ₁0 hβ₁1 hz₁ hsmall q _ χ ρ hq hIm hre0 hre1 hzρ hne => ?_⟩
  have hQR : (2 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ
  have hQT_ge4 : (4 : ℝ) ≤ (Q : ℝ) * T := by nlinarith
  set L : ℝ := Real.log ((Q : ℝ) * T)
  have hL_gt1 : 1 < L := by
    have h1 : Real.exp 1 < 4 := by linarith [Real.exp_one_lt_d9]
    have h2 := Real.log_lt_log (Real.exp_pos 1) (lt_of_lt_of_le h1 hQT_ge4)
    rwa [Real.log_exp] at h2
  have hL_pos : 0 < L := by linarith
  set δ₁ : ℝ := (1 - β₁) * L
  have hδ₁_pos : 0 < δ₁ := mul_pos (by linarith) hL_pos
  -- **EASY CASE (`c_max ≤ 1 - ρ.re`)**: discharged in 8 lines by `siegel_real_zero_exclusion`!
  by_cases hbig : c_max ≤ 1 - ρ.re
  · have hβ₁_siegel : β₁ < 1 - C_S / (q₁ : ℝ) ^ (1 : ℝ) := by
      by_contra hge; push Not at hge
      exact hsiegel q₁ χ₁ hprim₁ hsq₁ hχ₁ β₁ hge hz₁
    rw [Real.rpow_one] at hβ₁_siegel
    have hq₁_pos : (0 : ℝ) < (q₁ : ℝ) := Nat.cast_pos.mpr (NeZero.pos q₁)
    have hq₁_le : (q₁ : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hq₁
    have h1β₁_gt : C_S / (Q : ℝ) < 1 - β₁ := by
      have hdiv : C_S / (Q : ℝ) ≤ C_S / (q₁ : ℝ) := div_le_div_of_nonneg_left hC_S_pos.le hq₁_pos hq₁_le
      linarith
    have hratio_le : c₂ / δ₁ ≤ (Q : ℝ) * T := by
      rw [div_le_iff₀ hδ₁_pos]
      have h2 : C_S < (1 - β₁) * (Q : ℝ) := (div_lt_iff₀ (by linarith)).mp h1β₁_gt
      have h3 : c₂ ≤ C_S := min_le_right _ _
      have h4 : (1 - β₁) * (Q : ℝ) ≤ (Q : ℝ) * T * ((1 - β₁) * L) := by
        have hTL : (1 : ℝ) ≤ T * L := by nlinarith
        have h1' := mul_le_mul_of_nonneg_left hTL (by positivity : (0 : ℝ) ≤ (1 - β₁) * (Q : ℝ))
        linarith [show (1 - β₁) * (Q : ℝ) * (T * L) = (Q : ℝ) * T * ((1 - β₁) * L) by ring]
      dsimp only [δ₁]
      linarith
    have hlog_le : Real.log (c₂ / δ₁) ≤ L := Real.log_le_log (by positivity) hratio_le
    have hc₁_le : c₁ ≤ c_max / 2 := min_le_right _ _
    have hbd : c₁ * Real.log (c₂ / δ₁) / L ≤ c_max := by
      have h1 : c₁ * Real.log (c₂ / δ₁) ≤ (c_max / 2) * L := by
        by_cases hlog_nn : 0 ≤ Real.log (c₂ / δ₁)
        · exact mul_le_mul hc₁_le hlog_le hlog_nn (by positivity)
        · push Not at hlog_nn
          have : c₁ * Real.log (c₂ / δ₁) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hc₁_pos.le hlog_nn.le
          linarith [mul_pos (by positivity : 0 < c_max / 2) hL_pos]
      calc c₁ * Real.log (c₂ / δ₁) / L ≤ ((c_max / 2) * L) / L :=
            div_le_div_of_nonneg_right h1 hL_pos.le
        _ = c_max / 2 := by field_simp [hL_pos.ne']
        _ ≤ c_max := by linarith
    exact hbd.trans hbig
  -- **MAIN CASE (`1 - ρ.re < c_max`)**: Klein-Four Orbit + Extremal Zero + Fejér Power Sum!
  push Not at hbig
  set ψ₀ : PChar := PChar.one
  set ψ₁ : PChar := PChar.of χ₁
  set ψ₂ : PChar := PChar.of χ
  set ψ₃ : PChar := PChar.of (prodChar χ χ₁)
  set S : Finset PChar := {ψ₀, ψ₁, ψ₂, ψ₃}
  -- Orbit properties: conductors `≤ Q^2`, closed under `prodChar · χ₁`
  have hS_N : ∀ ψ ∈ S, ψ.N ≤ Q * Q := by
    intro ψ hψ
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hψ
    rcases hψ with rfl | rfl | rfl | rfl
    · change 1 ≤ Q * Q; nlinarith
    · have : ψ₁.N = q₁ := hprim₁; rw [this]; nlinarith
    · exact (Nat.le_of_dvd (NeZero.pos q) χ.conductor_dvd_level).trans (by nlinarith)
    · have h1 : ψ₃.N ≤ q * q₁ := Nat.le_of_dvd (Nat.mul_pos (NeZero.pos q) (NeZero.pos q₁))
        (prodChar χ χ₁).conductor_dvd_level
      exact h1.trans (Nat.mul_le_mul hq hq₁)
  have hS_closed : ∀ ψ ∈ S, PChar.of (prodChar ψ.χ χ₁) ∈ S := by
    intro ψ hψ
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hψ ⊢
    rcases hψ with rfl | rfl | rfl | rfl
    · right; left; exact pchar_of_prodChar_one_left χ₁
    · left
      have h1 : prodChar ψ₁.χ χ₁ = 1 := (prodChar_eq_one_iff_eq_pchar hsq₁ ψ₁).mpr rfl
      rw [h1, PChar.of_one]
    · right; right; right; exact pchar_of_prodChar_of_left χ χ₁
    · right; right; left
      rw [pchar_of_prodChar_of_left, pchar_of_prodChar_cancel_right χ hsq₁]
  -- Initial zero gap `μ₀ := orbitMinGap S ψ₁ β₁ T ≤ 1 - ρ.re < c_max`
  have hzρ_prim : DirichletCharacter.LFunction ψ₂.χ ρ = 0 :=
    (RHDirect.LFunction_eq_zero_iff_primitive_of_re_pos χ hre0 (by
      by_cases hχ1 : χ = 1
      · right; intro h; rw [h, Complex.one_re] at hre1; linarith
      · left; exact hχ1)).mp hzρ
  set μ₀ : ℝ := orbitMinGap S ψ₁ β₁ T
  have hμ₀_le_ρ : μ₀ ≤ 1 - ρ.re :=
    (orbitMinGap_spec S ψ₁ β₁ T).2.2.1 ψ₂ (by simp [S]) ρ hIm hre0 hre1 hzρ_prim hne
  have hμ₀_lt_max : μ₀ < c_max := lt_of_le_of_lt hμ₀_le_ρ hbig
  have hμ₀_pos : 0 < μ₀ := (orbitMinGap_spec S ψ₁ β₁ T).1
  -- Set stopping parameters `M₀`, `ε`, `J`
  set lam₀ : ℝ := μ₀ * L
  have hlam₀_pos : 0 < lam₀ := mul_pos hμ₀_pos hL_pos
  have hlam₀_le_L : lam₀ ≤ L := by
    have h1 : μ₀ ≤ 1 := hμ₀_lt_max.le.trans (by linarith)
    dsimp only [lam₀]
    linarith [mul_le_mul_of_nonneg_right h1 hL_pos.le]
  set M₀ : ℝ := C_M * (C_L * lam₀ + 1) + 4
  have hM₀_ge4 : 4 ≤ M₀ := by
    dsimp only [M₀]
    linarith [show 0 ≤ C_M * (C_L * lam₀ + 1) by positivity]
  set ε : ℝ := 1 / (8 * M₀)
  have hε_pos : 0 < ε := by positivity
  have hε_le : ε ≤ 1 / 4 := by
    dsimp only [ε]
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 8 * M₀)]
    linarith
  set J : ℕ := Nat.ceil (4 * M₀ * Real.log (2 * C_L * L / c_cl + 2)) + 1
  have hJ_gt : 4 * M₀ * Real.log (2 * C_L * L / c_cl + 2) < (J : ℝ) := by
    dsimp only [J]; push_cast
    linarith [Nat.le_ceil (4 * M₀ * Real.log (2 * C_L * L / c_cl + 2))]
  -- Prove `Real.log (Q^2 * (T + J + 2)) ≤ C_L * L`!
  have hlog_J_le : Real.log ((Q : ℝ) ^ 2 * (T + (J : ℝ) + 2)) ≤ C_L * L := by
    have hM₀_le : M₀ ≤ 2 * C_M * C_L * (L + 1) := by
      dsimp only [M₀]
      have h1 : C_L * lam₀ + 1 ≤ C_L * (L + 1) := by nlinarith
      have h2 : (4 : ℝ) ≤ C_M * C_L * (L + 1) := by nlinarith
      nlinarith
    have hlog_arg : Real.log (2 * C_L * L / c_cl + 2) ≤
        Real.log (2 * C_L * (1 / c_cl + 2)) + Real.log (L + 2) := by
      have h1 : 2 * C_L * L / c_cl + 2 ≤ (2 * C_L * (1 / c_cl + 2)) * (L + 2) := by
        have hdiff : (2 * C_L * (1 / c_cl + 2)) * (L + 2) - (2 * C_L * L / c_cl + 2) =
            4 * C_L / c_cl + 4 * C_L * L + (8 * C_L - 2) := by ring
        have hpos1 : 0 ≤ 4 * C_L / c_cl := by positivity
        have hpos2 : 0 ≤ 4 * C_L * L := by positivity
        linarith
      calc Real.log (2 * C_L * L / c_cl + 2)
          ≤ Real.log ((2 * C_L * (1 / c_cl + 2)) * (L + 2)) :=
            Real.log_le_log (by positivity) h1
        _ = Real.log (2 * C_L * (1 / c_cl + 2)) + Real.log (L + 2) :=
            Real.log_mul (by positivity) (by linarith)
    have hJ_le : (J : ℝ) ≤ 4 * M₀ * Real.log (2 * C_L * L / c_cl + 2) + 2 := by
      dsimp only [J]; push_cast
      have hceil := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ 4 * M₀ * Real.log (2 * C_L * L / c_cl + 2) by
        refine mul_nonneg (by linarith) (Real.log_nonneg ?_)
        have : 0 ≤ 2 * C_L * L / c_cl := by positivity
        linarith)
      linarith
    have hlog_CL_bd : Real.log (2 * C_L * (1 / c_cl + 2)) ≤ 2 * C_L * (1 / c_cl + 2) := by
      have := Real.log_le_sub_one_of_pos (by positivity : 0 < 2 * C_L * (1 / c_cl + 2))
      linarith
    have hJ_exp : (J : ℝ) ≤ 8 * K_stop * C_L ^ 2 * Real.exp L + 2 := by
      have h1 := log_linear_mul_log_le_exp hL_gt1.le
      have h2 : L + 1 ≤ 4 * Real.exp L := by
        have := Real.add_one_le_exp L; linarith
      have hmul1 : 4 * M₀ * Real.log (2 * C_L * L / c_cl + 2) ≤
          (8 * C_M * C_L * (L + 1)) * (2 * C_L * (1 / c_cl + 2) + Real.log (L + 2)) := by
        refine mul_le_mul (by linarith) (by linarith)
          (Real.log_nonneg (by
            have : 0 ≤ 2 * C_L * L / c_cl := by positivity
            linarith))
          (by positivity)
      have hexpand : (8 * C_M * C_L * (L + 1)) * (2 * C_L * (1 / c_cl + 2) + Real.log (L + 2)) =
          16 * C_M * (1 / c_cl + 2) * C_L ^ 2 * (L + 1) +
            8 * C_M * C_L * ((L + 1) * Real.log (L + 2)) := by ring
      rw [hexpand] at hmul1
      have ha : 16 * C_M * (1 / c_cl + 2) * C_L ^ 2 * (L + 1) ≤
          64 * C_M * (1 / c_cl + 2) * C_L ^ 2 * Real.exp L := by
        have hnn : 0 ≤ 16 * C_M * (1 / c_cl + 2) * C_L ^ 2 := by positivity
        have h' := mul_le_mul_of_nonneg_left h2 hnn
        linarith [show 16 * C_M * (1 / c_cl + 2) * C_L ^ 2 * (4 * Real.exp L) =
          64 * C_M * (1 / c_cl + 2) * C_L ^ 2 * Real.exp L by ring]
      have hb : 8 * C_M * C_L * ((L + 1) * Real.log (L + 2)) ≤
          32 * C_M * C_L * Real.exp L := by
        have hnn : 0 ≤ 8 * C_M * C_L := by positivity
        have h' := mul_le_mul_of_nonneg_left h1 hnn
        linarith [show 8 * C_M * C_L * (4 * Real.exp L) = 32 * C_M * C_L * Real.exp L by ring]
      have hc : 32 * C_M * C_L * Real.exp L ≤
          192 * C_M * (1 / c_cl + 2) * C_L ^ 2 * Real.exp L := by
        have hnn : 0 ≤ 32 * C_M * Real.exp L := by positivity
        have hCL1 : C_L ≤ C_L ^ 2 := by
          have := mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ C_L by linarith) hC_L_pos.le
          linarith [sq C_L]
        have hccl : 1 ≤ 6 * (1 / c_cl + 2) := by
          have : 0 < 1 / c_cl := by positivity
          linarith
        have h1' : (1 : ℝ) * C_L ≤ (6 * (1 / c_cl + 2)) * C_L ^ 2 :=
          mul_le_mul hccl hCL1 hC_L_pos.le (by positivity)
        have h2' := mul_le_mul_of_nonneg_left h1' hnn
        linarith [show 32 * C_M * Real.exp L * (1 * C_L) = 32 * C_M * C_L * Real.exp L by ring,
          show 32 * C_M * Real.exp L * (6 * (1 / c_cl + 2) * C_L ^ 2) =
            192 * C_M * (1 / c_cl + 2) * C_L ^ 2 * Real.exp L by ring]
      have htot : 64 * C_M * (1 / c_cl + 2) * C_L ^ 2 * Real.exp L +
          192 * C_M * (1 / c_cl + 2) * C_L ^ 2 * Real.exp L =
          8 * K_stop * C_L ^ 2 * Real.exp L := by dsimp only [K_stop]; ring
      linarith
    have hexpL : Real.exp L = (Q : ℝ) * T := Real.exp_log (by positivity)
    rw [hexpL] at hJ_exp
    have hprod_le : (Q : ℝ) ^ 2 * (T + (J : ℝ) + 2) ≤ C_b * C_L ^ 2 * ((Q : ℝ) * T) ^ 3 := by
      have hT_le : T + 4 ≤ 4 * ((Q : ℝ) * T) := by nlinarith
      have hinner : T + (J : ℝ) + 2 ≤ C_b * C_L ^ 2 * ((Q : ℝ) * T) := by
        have hCL2 : 1 ≤ C_L ^ 2 := by nlinarith
        dsimp only [C_b]
        nlinarith
      have hQ2_le : (Q : ℝ) ^ 2 ≤ ((Q : ℝ) * T) ^ 2 := by
        have : (Q : ℝ) ≤ (Q : ℝ) * T := by nlinarith
        exact pow_le_pow_left₀ (by linarith) this 2
      calc (Q : ℝ) ^ 2 * (T + (J : ℝ) + 2)
          ≤ ((Q : ℝ) * T) ^ 2 * (C_b * C_L ^ 2 * ((Q : ℝ) * T)) :=
            mul_le_mul hQ2_le hinner (by positivity) (by positivity)
        _ = C_b * C_L ^ 2 * ((Q : ℝ) * T) ^ 3 := by ring
    calc Real.log ((Q : ℝ) ^ 2 * (T + (J : ℝ) + 2))
        ≤ Real.log (C_b * C_L ^ 2 * ((Q : ℝ) * T) ^ 3) :=
          Real.log_le_log (by positivity) hprod_le
      _ = Real.log C_b + 2 * Real.log C_L + 3 * L := by
          rw [Real.log_mul (by positivity) (by positivity),
            Real.log_mul hC_b_pos.ne' (by positivity),
            Real.log_pow, Real.log_pow]
          push_cast; rfl
      _ ≤ (Real.log C_b + 2 * Real.log C_L + 4) * L := by
          have hlog_nn : 0 ≤ Real.log C_b + 2 * Real.log C_L := by
            have h1 : 0 ≤ Real.log C_b := Real.log_nonneg (by dsimp only [C_b]; linarith)
            have h2 : 0 ≤ Real.log C_L := Real.log_nonneg (by linarith)
            linarith
          nlinarith
      _ ≤ C_L * L := mul_le_mul_of_nonneg_right hC_L_self hL_pos.le
  -- Apply `exists_stopping_height`!
  have hlb_orbit : ∀ j : ℕ, j ≤ J →
      c_cl / Real.log ((Q : ℝ) ^ 2 * (T + (j : ℝ) + 2)) ≤ orbitMinGap S ψ₁ β₁ (T + (j : ℝ)) := by
    intro j hj
    have hspec := orbitMinGap_spec S ψ₁ β₁ (T + (j : ℝ))
    by_cases hlt : orbitMinGap S ψ₁ β₁ (T + (j : ℝ)) < 1 / 2
    · obtain ⟨ψ, hψS, ρ', hIm', h0', h1', hz', hne', heq'⟩ := hspec.2.2.2 hlt
      rw [← heq']
      exact hclass Q T (T + (j : ℝ)) hQ hT (by linarith [Nat.cast_nonneg (α := ℝ) j])
        q₁ χ₁ hq₁ hprim₁ hsq₁ hχ₁ β₁ hβ₁0 hβ₁1 hz₁ (hsmall.trans (min_le_left _ _))
        ψ ρ' (hS_N ψ hψS) hIm' h0' h1' hz' hne'
    · push Not at hlt
      have hant : orbitMinGap S ψ₁ β₁ (T + (j : ℝ)) ≤ μ₀ :=
        orbitMinGap_antitone S ψ₁ β₁ (by linarith [Nat.cast_nonneg (α := ℝ) j])
      linarith
  have hkill : Real.exp (-2 * ε * (J : ℝ)) * μ₀ <
      c_cl / Real.log ((Q : ℝ) ^ 2 * (T + (J : ℝ) + 2)) := by
    have hlog_pos_J : 0 < Real.log ((Q : ℝ) ^ 2 * (T + (J : ℝ) + 2)) :=
      Real.log_pos (by nlinarith [Nat.cast_nonneg (α := ℝ) J])
    have hexp_lt : Real.exp (-2 * ε * (J : ℝ)) < (2 * C_L * L / c_cl + 2)⁻¹ := by
      have h1 : Real.log (2 * C_L * L / c_cl + 2) < 2 * ε * (J : ℝ) := by
        dsimp only [ε]
        have hM₀_pos : 0 < M₀ := by linarith
        have h2 : 2 * (1 / (8 * M₀)) * (J : ℝ) = (J : ℝ) / (4 * M₀) := by field_simp [hM₀_pos.ne']; ring
        rw [h2, lt_div_iff₀ (by positivity)]
        linarith
      calc Real.exp (-2 * ε * (J : ℝ))
          = (Real.exp (2 * ε * (J : ℝ)))⁻¹ := by rw [← Real.exp_neg]; congr 1; ring
        _ < (Real.exp (Real.log (2 * C_L * L / c_cl + 2)))⁻¹ :=
            inv_strictAnti₀ (Real.exp_pos _) (Real.exp_lt_exp.mpr h1)
        _ = (2 * C_L * L / c_cl + 2)⁻¹ := by rw [Real.exp_log (by positivity)]
    have h2 : (2 * C_L * L / c_cl + 2)⁻¹ * μ₀ ≤ c_cl / (C_L * L) := by
      have hden_pos : 0 < 2 * C_L * L / c_cl + 2 := by positivity
      rw [inv_mul_eq_div, div_le_div_iff₀ hden_pos (by positivity)]
      have hμ₀_le1 : μ₀ ≤ 1 := hμ₀_lt_max.le.trans (by linarith)
      have hmul : c_cl * (2 * C_L * L / c_cl + 2) = 2 * C_L * L + 2 * c_cl := by
        field_simp [hc_cl_pos.ne']
      rw [hmul]
      have h1' : μ₀ * (C_L * L) ≤ 1 * (C_L * L) := mul_le_mul_of_nonneg_right hμ₀_le1 (by positivity)
      linarith [mul_pos hC_L_pos hL_pos]
    have h3 : c_cl / (C_L * L) ≤ c_cl / Real.log ((Q : ℝ) ^ 2 * (T + (J : ℝ) + 2)) :=
      div_le_div_of_nonneg_left hc_cl_pos.le hlog_pos_J hlog_J_le
    calc Real.exp (-2 * ε * (J : ℝ)) * μ₀
        < (2 * C_L * L / c_cl + 2)⁻¹ * μ₀ := mul_lt_mul_of_pos_right hexp_lt hμ₀_pos
      _ ≤ c_cl / (C_L * L) := h2
      _ ≤ c_cl / Real.log ((Q : ℝ) ^ 2 * (T + (J : ℝ) + 2)) := h3
  obtain ⟨j_stop, hj_lt, hj_stop⟩ :=
    exists_stopping_height S ψ₁ β₁ T c_cl ε Q J hε_pos hε_le hlb_orbit hkill
  -- Extract the extremal zero `(ψ_*, ρ_*)` at height `T_j := T + j_stop`!
  set T_j : ℝ := T + (j_stop : ℝ)
  set μ : ℝ := orbitMinGap S ψ₁ β₁ T_j
  have hμ_le_μ₀ : μ ≤ μ₀ := orbitMinGap_antitone S ψ₁ β₁ (by dsimp only [T_j]; linarith [Nat.cast_nonneg (α := ℝ) j_stop])
  have hμ_pos : 0 < μ := (orbitMinGap_spec S ψ₁ β₁ T_j).1
  have hμ_lt_max : μ < c_max := lt_of_le_of_lt hμ_le_μ₀ hμ₀_lt_max
  have hμ_lt_half : μ < 1 / 2 := lt_of_lt_of_le hμ_lt_max ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)) |>.trans (by norm_num))
  obtain ⟨ψ_s, hψ_s_S, ρ_s, hIm_s, hre0_s, hre1_s, hz_s, hne_s, hμ_eq⟩ :=
    (orbitMinGap_spec S ψ₁ β₁ T_j).2.2.2 hμ_lt_half
  -- Log scale `L_max := Real.log (Q^2 * (T_j + 2)) ≤ C_L * L`
  set L_max : ℝ := Real.log ((Q : ℝ) ^ 2 * (T_j + 2))
  have hL_max_le : L_max ≤ C_L * L := by
    have hTj_le : T_j ≤ T + (J : ℝ) := by
      dsimp only [T_j]; linarith [show (j_stop : ℝ) ≤ (J : ℝ) by exact_mod_cast hj_lt.le]
    exact (Real.log_le_log (by positivity) (by nlinarith)).trans hlog_J_le
  have hL_max_ge1 : 1 ≤ L_max := by
    have h1 : (Q : ℝ) * T ≤ (Q : ℝ) ^ 2 * (T_j + 2) := by
      dsimp only [T_j]; nlinarith [Nat.cast_nonneg (α := ℝ) j_stop]
    exact hL_gt1.le.trans (Real.log_le_log (by positivity) h1)
  have hL_max_pos : 0 < L_max := by linarith
  set lam_max : ℝ := μ * L_max
  have hlam_max_pos : 0 < lam_max := mul_pos hμ_pos hL_max_pos
  have hlam_max_ge_cl : c_cl ≤ lam_max := by
    have h1 := hlb_orbit j_stop hj_lt.le
    dsimp only [lam_max, μ, L_max, T_j] at *
    exact (div_le_iff₀ hL_max_pos).mp h1
  -- Simplicity of `β₁` in `completedLZeroSeq hprim₁ hχ₁`
  have hsmall_2q₁ : (1 - β₁) * Real.log (2 * (q₁ : ℝ)) < 1 / (12 * C_H) := by
    have hq₁_pos : (0 : ℝ) < (q₁ : ℝ) := Nat.cast_pos.mpr (NeZero.pos q₁)
    have h2q₁_le : 2 * (q₁ : ℝ) ≤ (Q : ℝ) * T := by
      have : (q₁ : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hq₁
      nlinarith
    have hlog_le : Real.log (2 * (q₁ : ℝ)) ≤ L := Real.log_le_log (by positivity) h2q₁_le
    have h1 : (1 - β₁) * Real.log (2 * (q₁ : ℝ)) ≤ δ₁ :=
      mul_le_mul_of_nonneg_left hlog_le (by linarith)
    have h2 : δ₁ ≤ 1 / (24 * C_H) := hsmall.trans (min_le_right _ _)
    have h3 : 1 / (24 * C_H) < 1 / (12 * C_H) := by
      have : (0 : ℝ) < 12 * C_H := by positivity
      exact one_div_lt_one_div_of_lt this (by linarith)
    linarith
  have hψ₁_ne1 : ψ₁.χ ≠ 1 := by
    intro h1; apply hχ₁
    have h1' : χ₁.primitiveCharacter = 1 := h1
    rw [← χ₁.changeLevel_primitiveCharacter, h1', map_one]
  have hz₁_prim : DirichletCharacter.LFunction ψ₁.χ (β₁ : ℂ) = 0 := by
    have hof : ψ₁ = PChar.mk q₁ χ₁ hprim₁ := by
      simpa [ψ₁] using PChar.of_self (PChar.mk q₁ χ₁ hprim₁)
    rw [hof]; exact hz₁
  obtain ⟨n₁, hn₁⟩ := exists_pcharZeroSeq_eq ψ₁ (by simp; linarith) (by simp; linarith) hz₁_prim
  have hn₁_uniq : ∀ n : ℕ, pcharZeroSeq ψ₁ n = (β₁ : ℂ) → n = n₁ := by
    intro n hn
    have hof : ψ₁ = PChar.mk q₁ χ₁ hprim₁ := by
      simpa [ψ₁] using PChar.of_self (PChar.mk q₁ χ₁ hprim₁)
    have hseq : ∀ k : ℕ, pcharZeroSeq ψ₁ k = completedLZeroSeq hprim₁ hχ₁ k := by
      intro k; rw [hof]; unfold pcharZeroSeq; simp [hχ₁]
    rw [hseq n] at hn
    rw [hseq n₁] at hn₁
    exact siegel_zero_unique_index hC_H_pos hZ_bd hL_bd hprim₁ hχ₁ hβ₁0 hβ₁1 hsmall_2q₁ hn hn₁
  -- Set up the 4 slots `(ψ_i, s_i, excl_i)` for `i : Fin 4`!
  set γ_s : ℝ := ρ_s.im
  set ψ_prod : PChar := PChar.of (prodChar ψ_s.χ χ₁)
  have hψ_prod_S : ψ_prod ∈ S := hS_closed ψ_s hψ_s_S
  let slotChar : Fin 4 → PChar := ![ψ₀, ψ₁, ψ_s, ψ_prod]
  let slotIm : Fin 4 → ℝ := ![0, 0, γ_s, γ_s]
  let slotPt : Fin 4 → ℂ := fun i => ((1 + μ : ℝ) : ℂ) + I * (slotIm i : ℂ)
  let slotExcl : Fin 4 → Option ℕ :=
    ![none, some n₁, if ψ_s = ψ₁ then some n₁ else none, if ψ_s = ψ₀ then some n₁ else none]
  have hslot_S : ∀ i : Fin 4, slotChar i ∈ S := by
    intro i; fin_cases i
    · exact by simp [slotChar, S]
    · exact by simp [slotChar, S]
    · exact hψ_s_S
    · exact hψ_prod_S
  have hslot_Im : ∀ i : Fin 4, |slotIm i| ≤ T_j := by
    intro i; fin_cases i <;> simp [slotIm]
    · dsimp only [T_j]; linarith [Nat.cast_nonneg (α := ℝ) j_stop]
    · dsimp only [T_j]; linarith [Nat.cast_nonneg (α := ℝ) j_stop]
    · exact hIm_s
    · exact hIm_s
  have hslot_re_le : ∀ i : Fin 4, ∀ σ : ℝ, 1 < σ → σ ≤ 2 → ∀ F : Finset ℕ,
      ∑ n ∈ F, ((1 : ℂ) / (((σ : ℂ) + I * (slotIm i : ℂ)) - pcharZeroSeq (slotChar i) n)).re ≤
        C₁ * L_max + 2 / (σ - 1) := by
    intro i σ hσ1 hσ2 F
    set ψ := slotChar i
    have hN_le : ((ψ.N : ℝ) * (|slotIm i| + 2)) ≤ (Q : ℝ) ^ 2 * (T_j + 2) := by
      have h1 : (ψ.N : ℝ) ≤ (Q : ℝ) ^ 2 := by
        have hN := hS_N ψ (hslot_S i)
        have hR : (ψ.N : ℝ) ≤ ((Q * Q : ℕ) : ℝ) := by exact_mod_cast hN
        push_cast at hR; linarith [sq (Q : ℝ)]
      have h2 := hslot_Im i
      nlinarith [abs_nonneg (slotIm i)]
    have hlog_le : Real.log ((ψ.N : ℝ) * (|slotIm i| + 2)) ≤ L_max :=
      Real.log_le_log (by have : (0 : ℝ) < (ψ.N : ℝ) := Nat.cast_pos.mpr (NeZero.pos ψ.N); positivity) hN_le
    unfold pcharZeroSeq
    split_ifs with h1
    · have hbd := hreZ σ (slotIm i) hσ1 hσ2 F
      have hlog_t : Real.log (|slotIm i| + 2) ≤ L_max := by
        have hN1 : (1 : ℝ) ≤ (ψ.N : ℝ) := by exact_mod_cast NeZero.pos ψ.N
        exact (Real.log_le_log (by linarith [abs_nonneg (slotIm i)])
          (by nlinarith [abs_nonneg (slotIm i)])).trans hlog_le
      nlinarith
    · have hbd := hreL ψ.N ψ.χ ψ.prim h1 σ (slotIm i) hσ1 hσ2 F
      nlinarith
  -- Collect all inner zeros (`‖slotPt i - pcharZeroSeq (slotChar i) n‖ ≤ A * μ`, avoiding `slotExcl i`)
  set R : ℝ := A * μ
  have hR_le : R ≤ 1 / 2 := by
    have hc1 : c_max ≤ 1 / (2 * A) := min_le_left _ _
    have h1 : A * μ ≤ A * (1 / (2 * A)) := mul_le_mul_of_nonneg_left (hμ_lt_max.le.trans hc1) hA_pos.le
    have h2 : A * (1 / (2 * A)) = 1 / 2 := by field_simp [hA_pos.ne']
    dsimp only [R]; linarith
  let innerFin : Fin 4 → Finset ℕ := fun i =>
    ((finite_ball_zero_indices (pcharZeroSeq_strip (slotChar i))
      (pcharZeroSeq_summable_inv_sq (slotChar i)) (slotPt i) R).toFinset).filter
      (fun n => slotExcl i ≠ some n)
  -- The distinguished zero `(2, n_s)` is in `innerFin 2` and has value `1`!
  obtain ⟨n_s, hn_s⟩ := exists_pcharZeroSeq_eq ψ_s hre0_s hre1_s hz_s
  have hn_s_excl : slotExcl 2 ≠ some n_s := by
    change (if ψ_s = ψ₁ then some n₁ else none) ≠ some n_s
    split_ifs with hEq
    · intro h2
      have hneq : n₁ = n_s := Option.some.inj h2
      rw [← hneq] at hn_s
      rw [hEq] at hn_s hne_s
      rw [hn₁] at hn_s
      rcases hne_s with hρne | hψne
      · exact hρne hn_s.symm
      · exact hψne rfl
    · simp
  have hn_s_dist : slotPt 2 - pcharZeroSeq (slotChar 2) n_s = ((2 * μ : ℝ) : ℂ) := by
    have hval : pcharZeroSeq (slotChar 2) n_s = ρ_s := hn_s
    rw [hval]
    apply Complex.ext
    · simp only [slotPt, slotIm, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons,
        Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, zero_mul,
        Complex.I_im, Complex.ofReal_im, mul_zero, sub_self, add_zero]
      linarith
    · simp only [slotPt, slotIm, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons,
        Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, zero_mul,
        Complex.I_im, Complex.ofReal_re, one_mul, zero_add, γ_s, sub_self]
  have hn_s_mem : n_s ∈ innerFin 2 := by
    refine Finset.mem_filter.mpr ⟨?_, hn_s_excl⟩
    refine (finite_ball_zero_indices (pcharZeroSeq_strip (slotChar 2))
      (pcharZeroSeq_summable_inv_sq (slotChar 2)) (slotPt 2) R).mem_toFinset.mpr ?_
    show ‖slotPt 2 - pcharZeroSeq (slotChar 2) n_s‖ ≤ R
    rw [hn_s_dist, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    dsimp only [R]
    linarith [mul_le_mul_of_nonneg_right hA_ge4 hμ_pos.le]
  -- Package all inner zeros across the 4 slots into a single `Finset (Σ i : Fin 4, ℕ)`!
  let allIn : Finset (Σ i : Fin 4, ℕ) := Finset.univ.sigma innerFin
  have hstar_mem : (⟨2, n_s⟩ : Σ _ : Fin 4, ℕ) ∈ allIn :=
    Finset.mem_sigma.mpr ⟨Finset.mem_univ 2, hn_s_mem⟩
  set N : ℕ := allIn.card
  have hN_pos : 0 < N := Finset.card_pos.mpr ⟨⟨2, n_s⟩, hstar_mem⟩
  have hN_le : (N : ℝ) ≤ C_N * (lam_max + 1) := by
    have hcard_eq : (N : ℝ) = ∑ i : Fin 4, ((innerFin i).card : ℝ) := by
      dsimp only [N, allIn]; rw [Finset.card_sigma, Nat.cast_sum]
    rw [hcard_eq]
    have hper : ∀ i : Fin 4, ((innerFin i).card : ℝ) ≤ 4 * C₁ * A * lam_max + 8 := by
      intro i
      have h1 := finset_card_ball_le_of_re_le (pcharZeroSeq_strip (slotChar i))
        (hslot_re_le i) hμ_pos (by dsimp only [R]; nlinarith) (by linarith) (innerFin i)
        fun n hn => (finite_ball_zero_indices (pcharZeroSeq_strip (slotChar i))
          (pcharZeroSeq_summable_inv_sq (slotChar i)) (slotPt i) R).mem_toFinset.mp (Finset.mem_filter.mp hn).1
      dsimp only [R, lam_max] at h1 ⊢
      linarith [show 4 * C₁ * (A * μ) * L_max = 4 * C₁ * A * (μ * L_max) by ring]
    calc ∑ i : Fin 4, ((innerFin i).card : ℝ)
        ≤ ∑ _i : Fin 4, (4 * C₁ * A * lam_max + 8) := Finset.sum_le_sum fun i _ => hper i
      _ = 16 * C₁ * A * lam_max + 32 := by simp [Finset.sum_const]; ring
      _ ≤ C_N * (lam_max + 1) := by dsimp only [C_N]; nlinarith
  -- Choose Fejér parameter `M := 2 * N + 2 * ⌈lam_max⌉₊ + 1`!
  set M : ℕ := 2 * N + 2 * Nat.ceil lam_max + 1
  have hM_ge1 : 1 ≤ M := by omega
  have hM_le_CM : (M : ℝ) ≤ C_M * (lam_max + 1) + 4 := by
    have hceil : (Nat.ceil lam_max : ℝ) < lam_max + 1 := Nat.ceil_lt_add_one hlam_max_pos.le
    dsimp only [M, C_M]; push_cast; nlinarith
  have hM_le_M₀ : (M : ℝ) ≤ M₀ := by
    have hlam_le : lam_max ≤ C_L * lam₀ := by
      dsimp only [lam_max, lam₀]
      calc μ * L_max ≤ μ₀ * (C_L * L) := mul_le_mul hμ_le_μ₀ hL_max_le hL_max_pos.le hμ₀_pos.le
        _ = C_L * (μ₀ * L) := by ring
    dsimp only [M₀]
    linarith [mul_le_mul_of_nonneg_left (show lam_max + 1 ≤ C_L * lam₀ + 1 by linarith) hC_M_pos.le]
  have h2Mε : 2 * (M : ℝ) * ε ≤ 1 / 4 := by
    dsimp only [ε]
    have hM₀_pos : 0 < M₀ := by linarith
    have h1 : 2 * (M : ℝ) * (1 / (8 * M₀)) ≤ 2 * M₀ * (1 / (8 * M₀)) := by
      gcongr
    have h2 : 2 * M₀ * (1 / (8 * M₀)) = 1 / 4 := by field_simp [hM₀_pos.ne']; ring
    linarith
  -- Every inner zero `p ∈ allIn` satisfies `(1 - ε) * ‖(2 μ) / (s - ρ')‖ ≤ 1`!
  let zVal : (Σ _ : Fin 4, ℕ) → ℂ := fun p =>
    ((2 * μ : ℝ) : ℂ) / (slotPt p.1 - pcharZeroSeq (slotChar p.1) p.2)
  have hzVal_star : zVal ⟨2, n_s⟩ = 1 := by
    dsimp only [zVal]
    rw [hn_s_dist, div_self (Complex.ofReal_ne_zero.mpr (by positivity))]
  have hzVal_bd : ∀ p ∈ allIn, (1 - ε) * ‖zVal p‖ ≤ 1 := by
    intro p hp
    rcases p with ⟨i, n⟩
    have hn_in : n ∈ innerFin i := (Finset.mem_sigma.mp hp).2
    have hdist : ‖slotPt i - pcharZeroSeq (slotChar i) n‖ ≤ R :=
      (finite_ball_zero_indices (pcharZeroSeq_strip (slotChar i))
        (pcharZeroSeq_summable_inv_sq (slotChar i)) (slotPt i) R).mem_toFinset.mp (Finset.mem_filter.mp hn_in).1
    have hexcl_ne : slotExcl i ≠ some n := (Finset.mem_filter.mp hn_in).2
    set ρ' : ℂ := pcharZeroSeq (slotChar i) n
    -- Check `|ρ'.im| ≤ T_j + 1`
    have hIm' : |ρ'.im| ≤ T_j + 1 := by
      have him_diff := (Complex.abs_im_le_norm (slotPt i - ρ')).trans hdist
      have him_eq : (slotPt i - ρ').im = slotIm i - ρ'.im := by simp [slotPt]
      rw [him_eq] at him_diff
      have htri : |ρ'.im| ≤ |slotIm i - ρ'.im| + |slotIm i| := by
        have : ρ'.im = -(slotIm i - ρ'.im) + slotIm i := by ring
        calc |ρ'.im| = |-(slotIm i - ρ'.im) + slotIm i| := congrArg abs this
          _ ≤ |-(slotIm i - ρ'.im)| + |slotIm i| := abs_add_le _ _
          _ = |slotIm i - ρ'.im| + |slotIm i| := by rw [abs_neg]
      linarith [hslot_Im i, hR_le]
    -- Check `(ρ' ≠ β₁ ∨ slotChar i ≠ ψ₁)` using simplicity `hn₁_uniq`!
    have hne' : ρ' ≠ (β₁ : ℂ) ∨ slotChar i ≠ ψ₁ := by
      by_cases hci : slotChar i = ψ₁
      · left; intro heq
        have hn_eq : n = n₁ := hn₁_uniq n (by rw [← hci]; exact heq)
        -- In every slot where `slotChar i = ψ₁`, `slotExcl i = some n₁`!
        fin_cases i
        · -- `ψ₀ = ψ₁` impossible since `χ₁ ≠ 1`
          have h01 : ψ₀ = ψ₁ := hci
          exact hψ₁_ne1 (by rw [← h01]; rfl)
        · exact hexcl_ne (by simp [slotExcl, hn_eq])
        · have hψs1 : ψ_s = ψ₁ := hci
          exact hexcl_ne (by simp [slotExcl, hψs1, hn_eq])
        · -- `ψ_prod = ψ₁` implies `ψ_s = ψ₀`, so `slotExcl 3 = some n₁`!
          have hψs0 : ψ_s = ψ₀ := by
            have hprod1 : ψ_prod = ψ₁ := hci
            have h1 : PChar.of (prodChar ψ_prod.χ χ₁) = PChar.of (prodChar ψ₁.χ χ₁) := by
              rw [hprod1]
            have h2 : PChar.of (prodChar ψ_prod.χ χ₁) = ψ_s := by
              dsimp only [ψ_prod]
              rw [pchar_of_prodChar_of_left, pchar_of_prodChar_cancel_right ψ_s.χ hsq₁, PChar.of_self]
            have h3 : PChar.of (prodChar ψ₁.χ χ₁) = ψ₀ := by
              have hp1 : prodChar ψ₁.χ χ₁ = 1 := (prodChar_eq_one_iff_eq_pchar hsq₁ ψ₁).mpr rfl
              rw [hp1, PChar.of_one]
            rw [← h2, h1, h3]
          exact hexcl_ne (by simp [slotExcl, hψs0, hn_eq])
      · exact .inr hci
    have hgap : (1 - 2 * ε) * μ ≤ 1 - ρ'.re := by
      have h1 := (orbitMinGap_spec S ψ₁ β₁ (T_j + 1)).2.2.1 (slotChar i) (hslot_S i) ρ' hIm'
        (pcharZeroSeq_strip (slotChar i) n).1 (pcharZeroSeq_strip (slotChar i) n).2
        (pcharZeroSeq_LFunction_zero (slotChar i) n) hne'
      exact hj_stop.trans h1
    have hden_ge : 2 * (1 - ε) * μ ≤ ‖slotPt i - ρ'‖ := by
      have hre := (le_abs_self (slotPt i - ρ').re).trans (Complex.abs_re_le_norm (slotPt i - ρ'))
      have hre_eq : (slotPt i - ρ').re = 1 + μ - ρ'.re := by simp [slotPt]
      rw [hre_eq] at hre
      linarith
    have hden_pos : 0 < 2 * (1 - ε) * μ := by
      have : 0 < 1 - ε := by linarith
      positivity
    dsimp only [zVal]
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    have hdiv : (1 - ε) * (2 * μ / ‖slotPt i - ρ'‖) ≤
        (1 - ε) * (2 * μ / (2 * (1 - ε) * μ)) :=
      mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_left (by positivity) hden_pos hden_ge) (by linarith)
    have hsimp : (1 - ε) * (2 * μ / (2 * (1 - ε) * μ)) = 1 := by
      have h1 : 1 - ε ≠ 0 := by linarith
      field_simp [h1, hμ_pos.ne']
    linarith
  -- Index `allIn` by `Fin N` with index `0` mapped to `⟨2, n_s⟩`!
  have hfejer_inner :
      (3 / 4 : ℝ) * (lam_max + 1) ≤
        ∑ m ∈ Finset.Icc 1 (M - 1),
          (1 - (m : ℝ) / (M : ℝ)) * (1 - ε) ^ (2 * m) *
            ∑ i : Fin 4, (∑ n ∈ innerFin i, (((2 * μ : ℝ) : ℂ) / (slotPt i - pcharZeroSeq (slotChar i) n)) ^ (2 * m)).re := by
    -- Build an equivalence `e : Fin N ≃ allIn` sending `⟨0, hN_pos⟩` to `⟨⟨2, n_s⟩, hstar_mem⟩`
    let e0 : Fin N ≃ {p // p ∈ allIn} := (Fintype.equivFinOfCardEq (by simp [N])).symm
    let idx0 : Fin N := e0.symm ⟨⟨2, n_s⟩, hstar_mem⟩
    let e : Fin N ≃ {p // p ∈ allIn} := (Equiv.swap ⟨0, hN_pos⟩ idx0).trans e0
    have he0 : (e ⟨0, hN_pos⟩).1 = ⟨2, n_s⟩ := by
      simp [e, idx0]
    let zFin : Fin N → ℂ := fun j => zVal (e j).1
    have hzFin0 : zFin ⟨0, hN_pos⟩ = 1 := by dsimp only [zFin]; rw [he0, hzVal_star]
    have hzFin_bd : ∀ j : Fin N, (1 - ε) * ‖zFin j‖ ≤ 1 := fun j => hzVal_bd (e j).1 (e j).2
    have hlow := fejer_even_power_sum_weighted_lower hN_pos zFin hzFin0 hM_ge1 hε_pos.le h2Mε hzFin_bd
    have hmatch : ∀ m : ℕ,
        (∑ j : Fin N, zFin j ^ (2 * m)).re =
          ∑ i : Fin 4, (∑ n ∈ innerFin i, (((2 * μ : ℝ) : ℂ) / (slotPt i - pcharZeroSeq (slotChar i) n)) ^ (2 * m)).re := by
      intro m
      have hsum_eq : ∑ j : Fin N, zFin j ^ (2 * m) = ∑ p ∈ allIn, zVal p ^ (2 * m) := by
        rw [← Finset.sum_attach allIn (fun p => zVal p ^ (2 * m))]
        exact Fintype.sum_equiv e (fun j => zFin j ^ (2 * m)) (fun p => zVal p.1 ^ (2 * m)) fun _ => rfl
      rw [hsum_eq]
      dsimp only [allIn, zVal]
      rw [Finset.sum_sigma, Complex.re_sum]
    simp_rw [hmatch] at hlow
    have hlower_rhs : (3 / 4 : ℝ) * (lam_max + 1) ≤ (3 / 8 : ℝ) * ((M : ℝ) - 1) - ((N : ℝ) - 1) / 2 := by
      have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN_pos
      have hceil : lam_max ≤ (Nat.ceil lam_max : ℝ) := Nat.le_ceil lam_max
      dsimp only [M]; push_cast; linarith
    exact hlower_rhs.trans hlow
  -- Now prove the per-`m` Hadamard inequality from `per_m_inner_sum_upper_bound`!
  have hper_m : ∀ m ∈ Finset.Icc 1 (M - 1),
      ∑ i : Fin 4, (∑ n ∈ innerFin i, (((2 * μ : ℝ) : ℂ) / (slotPt i - pcharZeroSeq (slotChar i) n)) ^ (2 * m)).re ≤
        4 * (m : ℝ) * ((1 - β₁) / μ) * 2 ^ (2 * m) +
        4 * C_E * (2 * μ) ^ (2 * m) * (2 : ℝ) ^ (2 * m - 1) * L_max +
        4 * ((2 / A) ^ (2 * m) * ((16 * C₁ + 16) * (A * lam_max + 1)) +
          4 * (2 * μ) ^ (2 * m) * (C₁ * L_max + 2)) := fun m hm =>
    per_m_inner_sum_upper_bound hC₁_pos hC_E_pos hsdZ hsdL hQ
      (by dsimp only [T_j]; linarith [Nat.cast_nonneg (α := ℝ) j_stop])
      hq₁ hsq₁ hχ₁ hβ₁1 hn₁ (hS_N ψ_s hψ_s_S) hIm_s
      hμ_pos (by linarith) hA_ge4 hR_le hslot_re_le (Finset.mem_Icc.mp hm).1
  -- Extract the final Deuring–Heilbronn bound via pure real algebra (`deuring_heilbronn_algebraic_extraction`)!
  have hc₂_le : c₂ ≤ (3 * c_cl / (8 * C_L)) * Real.exp (-(3 * (C_M + 4))) := by
    have h1 : c₂ ≤ c₂_raw := min_le_left _ _
    dsimp only [c₂_raw] at h1
    linarith [show 3 * c_cl * Real.exp (-(3 * (C_M + 4))) / (8 * C_L) =
      (3 * c_cl / (8 * C_L)) * Real.exp (-(3 * (C_M + 4))) by ring]
  exact deuring_heilbronn_algebraic_extraction
    hC₁_pos hC_E_pos hc_cl_pos hA_ge4 (le_max_right _ _) hC_M_pos hC_L_pos
    hc₁_pos (min_le_left _ _) hc₂_pos hc₂_le hL_pos hδ₁_pos rfl hβ₁1 hre1
    hμ_pos (hμ_le_μ₀.trans hμ₀_le_ρ)
    (hμ_lt_max.le.trans ((min_le_right _ _).trans (min_le_left _ _)))
    (hμ_lt_max.le.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
    hL_max_pos hL_max_le hlam_max_ge_cl hε_pos hε_le hN_pos rfl hM_le_CM
    (f := fun m => ∑ i : Fin 4,
      (∑ n ∈ innerFin i, (((2 * μ : ℝ) : ℂ) / (slotPt i - pcharZeroSeq (slotChar i) n)) ^ (2 * m)).re)
    hfejer_inner hper_m

/-- **UNCONDITIONAL DEURING–HEILBRONN ZERO-REPULSION (SINGLE MODULUS `q₁ = q = m`, `0` ASSUMPTIONS!)**:
clean specialization to a single modulus `m ≥ 2`, ready to plug straight into Linnik's theorem! -/
theorem deuring_heilbronn_single_modulus :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ c₂ : ℝ, 0 < c₂ ∧ ∃ c₃ : ℝ, 0 < c₃ ∧
      ∀ (m : ℕ) [NeZero m] (T : ℝ), 2 ≤ m → 2 ≤ T →
      ∀ (χ₁ : DirichletCharacter ℂ m), χ₁.IsPrimitive → χ₁ ^ 2 = 1 → χ₁ ≠ 1 →
      ∀ β₁ : ℝ, 1 / 2 < β₁ → β₁ < 1 → DirichletCharacter.LFunction χ₁ (β₁ : ℂ) = 0 →
        (1 - β₁) * Real.log ((m : ℝ) * T) ≤ c₃ →
      ∀ (χ : DirichletCharacter ℂ m) (ρ : ℂ),
        |ρ.im| ≤ T → 0 < ρ.re → ρ.re < 1 →
        DirichletCharacter.LFunction χ ρ = 0 →
        (ρ ≠ (β₁ : ℂ) ∨ χ ≠ χ₁) →
        c₁ * Real.log (c₂ / ((1 - β₁) * Real.log ((m : ℝ) * T))) / Real.log ((m : ℝ) * T) ≤
          1 - ρ.re := by
  obtain ⟨c₁, hc₁, c₂, hc₂, c₃, hc₃, hdh⟩ := deuring_heilbronn_zero_repulsion
  refine ⟨c₁, hc₁, c₂, hc₂, c₃, hc₃,
    fun m _ T hm hT χ₁ hprim₁ hsq₁ hχ₁ β₁ hβ₁0 hβ₁1 hz₁ hsmall χ ρ hIm hre0 hre1 hzρ hne => ?_⟩
  refine hdh m T hm hT m χ₁ le_rfl hprim₁ hsq₁ hχ₁ β₁ hβ₁0 hβ₁1 hz₁ hsmall m χ ρ le_rfl hIm hre0 hre1 hzρ ?_
  rcases hne with hρne | hχne
  · exact .inl hρne
  · right
    intro hof
    apply hχne
    have hof₁ : PChar.of χ₁ = PChar.mk m χ₁ hprim₁ := by
      simpa using PChar.of_self (PChar.mk m χ₁ hprim₁)
    rw [hof₁] at hof
    have haux : ∀ (d : ℕ) [NeZero d] (φ : DirichletCharacter ℂ d) (hp : φ.IsPrimitive)
        (hd : d ∣ m) (heq : PChar.mk d φ hp = PChar.mk m χ₁ hprim₁),
        DirichletCharacter.changeLevel hd φ = χ₁ := by
      intro d _ φ hp hd heq
      cases heq
      exact DirichletCharacter.changeLevel_self χ₁
    have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
    have h1 := haux χ.conductor χ.primitiveCharacter χ.primitiveCharacter_isPrimitive
      χ.conductor_dvd_level hof
    rwa [χ.changeLevel_primitiveCharacter] at h1

end RHDirect.Stage11DeuringHeilbronn
