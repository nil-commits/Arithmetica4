import RHDirect.Stage2SiegelReduction
import RHDirect.Stage2WeilMetaplectic
import RHDirect.Stage2ThetaWire
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# RHDirect.Stage3ThetaSiegelBridge

Stage 3 unified **Gaussian Lattice Theta Series – Siegel Reduction – Arakelov Slope – Finite Weil
Seesaw Bridge** in pure Mathlib `v4.33.1` (0 `sorry`, 0 custom `axiom`s).

## Contents

1. **Gaussian Lattice Theta Series `Θ_L(t) = ∑'_{v ∈ L} exp(-π t ‖v‖²)` & Dyadic-Shell Bounds**:
   - Unconditional summability (`summable_gaussianTerm`) over any discrete `ℤ`-lattice `L ⊂ E`
     for all `t > 0`, proved directly from `Stage2SiegelReduction.ncard_lattice_closedBall_le`
     via dyadic shell decomposition `2^k λ₁(L) ≤ ‖v‖ < 2^(k+1) λ₁(L)`.
   - Sharp explicit two-sided bounds:
     * Lower bound (`one_add_two_exp_le_latticeTheta`):
       `1 + 2 exp(-π t λ₁(L)²) ≤ Θ_L(t)` and covolume lower bound
       `1 + 2 exp(-π t r covol(L)^(2/r)) ≤ Θ_L(t)` via Hermite's first-minimum theorem.
     * Upper bound (`latticeTheta_le_dyadic_bound`):
       `Θ_L(t) ≤ 1 + C_r (1 + (√t λ₁(L))^(-r)) exp(-(π/2) t λ₁(L)²)`,
       with explicit constant `C_r = 5^r (2 + 2^(2r + 2) (r + 1)!)`.
     * Rapid decay (`latticeTheta_tendsto_one`, `latticeTheta_rapid_decay`):
       `Θ_L(t) → 1` and `t^m (Θ_L(t) - 1) → 0` as `t → ∞`, plus uniform decay as `λ₁(L) → ∞`.

2. **Banaszczyk-Style Gaussian Tail Inequality & Gram–Schmidt / Covolume / Siegel-Reduced Bounds**:
   - Tilted Banaszczyk Gaussian tail inequality (`banaszczyk_gaussian_tail_tilted`):
     `∑'_{v ∈ L, ‖v‖ ≥ R} exp(-π t ‖v‖²) ≤ exp(-π (t - s) R²) Θ_L(s)` for all `0 < s ≤ t`, `0 ≤ R`.
   - Quantitative super-exponential Banaszczyk tail bound (`banaszczyk_gaussian_tail_explicit`).
   - Shifted 1D Gaussian theta sum bound (`sum_int_exp_shifted_le`: `≤ 6 + 4 / √a`) and inductive
     upper-triangular Gram–Schmidt peeling (`latticeTheta_le_prod_gsVec`), proving the direct
     covolume & basis-norm upper bound:
     `Θ_L(t) ≤ (∏ j, (6 √t ‖b*_j‖ + 4)) / (t^(r/2) covol(L)) ≤ (∏ j, (6 √t ‖b_j‖ + 4)) / (t^(r/2) covol(L))`.
   - Siegel-reduced Gaussian theta upper bound (`latticeTheta_le_of_siegelReduced`) and
     covolume-normalized Banaszczyk tail bound (`banaszczyk_tail_le_covol`).

3. **Hermite–Minkowski Maximal-Slope Equivalence & Gaussian-Theta Siege-Envelope Integrability**:
   - Converse to `Stage2SiegelReduction.neg_log_lambda1_le_muMax`:
     `muMax_le_half_log_rk_sub_log_lambda1`:
     `-log λ₁(L) ≤ μ_max(L) ≤ -log λ₁(L) + (1/2) log (rk L)`.
   - First-minimum recovery from Gaussian theta decay (`lambda1_ge_of_latticeTheta_le`) and
     Siegel-reduced `μ_max` ceiling (`muMax_le_of_siegelReduced`).
   - Full Gaussian-theta Siegel-set integrability (`thetaKernel_integrable_of_gaussian_theta_bound`)
     and all-steps Weil convergence along `ChainRanks` (`chain_gaussianTheta_weil_convergent_all_steps`).

4. **Finite Weil Metaplectic Seesaw Positivity & `Stage2ThetaWire` Unified Pipeline Discharge**:
   - Hilbert adjoint identification (`finiteThetaLift_adjoint`, `finiteThetaLiftAdj_adjoint`),
     automatic Rallis eigenvalue positivity (`finiteTheta_rallis_eigenvalue_pos`) from
     `Stage2WeilMetaplectic.finiteTheta_rallis_criterion`, and restricted `SeesawDualPair`
     from `Stage2WeilMetaplectic.seesaw_intertwiner_identity` (`restrictedSeesawDualPair`).
   - Unified finite Weil seesaw chain bridge (`finiteWeil_seesaw_rallis_chain_bridge`).
   - Unified Siegel-reduced Bost–Arakelov–Theta fiber bridge (`siegelReduced_bost_theta_unified`).
   - Strictly reduced `Stage3ThetaSiegelFiberWitness` & `Stage3ThetaSiegelCoreInputs S` discharging
     `mu_le_max`, `slopes.1`, and `slopes.2` from Siegel-reduced lattice geometry and wiring
     directly into `Stage2ThetaWire.Stage2ThetaCoreInputs S`, `ThetaSlopeContract S`, and
     `AllLevelsWindowBound (3 / 2)`!
-/

open Module Submodule Finset Real MeasureTheory Filter
open scoped BigOperators Matrix ENNReal InnerProductSpace Topology

namespace RHDirect.Stage3ThetaSiegelBridge

noncomputable section

/-! ## Section 1: Elementary Real & Geometric Helpers for Dyadic Shells and 1D Shifted Gaussians -/

section ElemHelpers

/-- Elementary factorial-power upper bound on `exp (-x)`: for `0 < x` and `n : ℕ`,
`exp (-x) ≤ n! / x^n`. -/
lemma exp_neg_le_factorial_div_pow {x : ℝ} (hx : 0 < x) (n : ℕ) :
    Real.exp (-x) ≤ (n.factorial : ℝ) / x ^ n := by
  have hsum : x ^ n / (n.factorial : ℝ) ≤ Real.exp x := by
    have h1 : x ^ n / (n.factorial : ℝ) ≤
        ∑ i ∈ Finset.range (n + 1), x ^ i / (i.factorial : ℝ) :=
      Finset.single_le_sum (fun i _ => div_nonneg (pow_nonneg hx.le i) (Nat.cast_nonneg _))
        (Finset.mem_range.mpr (Nat.lt_succ_self n))
    exact h1.trans (Real.sum_le_exp_of_nonneg hx.le (n + 1))
  rw [Real.exp_neg]
  have hfac_pos : (0 : ℝ) < (n.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos n)
  have hxn_pos : 0 < x ^ n := pow_pos hx n
  have hexp_pos : 0 < Real.exp x := Real.exp_pos x
  rw [inv_eq_one_div, div_le_div_iff₀ hexp_pos hxn_pos, one_mul]
  rwa [div_le_iff₀ hfac_pos, mul_comm] at hsum

/-- Finite geometric sum bound for ratio `q ≥ 2`: `∑ k ∈ range (m + 1), q^k ≤ 2 * q^m`. -/
lemma sum_range_pow_le_two_mul {q : ℝ} (hq : 2 ≤ q) (m : ℕ) :
    ∑ k ∈ Finset.range (m + 1), q ^ k ≤ 2 * q ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, pow_succ]
    have hq0 : 0 ≤ q := by linarith
    have hqm : 0 ≤ q ^ m := pow_nonneg hq0 m
    nlinarith

/-- Finite geometric sum bound for `1 / 2`: `∑ k ∈ range n, (1 / 2 : ℝ)^k ≤ 2`. -/
lemma sum_range_half_pow_le_two (n : ℕ) :
    ∑ k ∈ Finset.range n, ((1 : ℝ) / 2) ^ k ≤ 2 := by
  have h : ∑ k ∈ Finset.range n, ((1 : ℝ) / 2) ^ k = 2 - 2 * ((1 : ℝ) / 2) ^ n := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih, pow_succ]
      ring
  rw [h]
  have hnn : 0 ≤ ((1 : ℝ) / 2) ^ n := pow_nonneg (by norm_num) n
  linarith

/-- Every real `x ≥ 1` lies in a unique dyadic interval `[2^k, 2^(k+1))`. -/
lemma exists_dyadic_shell {x : ℝ} (hx : 1 ≤ x) :
    ∃ k : ℕ, (2 : ℝ) ^ k ≤ x ∧ x < (2 : ℝ) ^ (k + 1) := by
  have hex : ∃ n : ℕ, x < (2 : ℝ) ^ n := by
    refine ⟨⌈x⌉₊ + 1, ?_⟩
    have h1 : x ≤ (⌈x⌉₊ : ℝ) := Nat.le_ceil x
    have h2 : ((⌈x⌉₊ + 1 : ℕ) : ℝ) < (2 : ℝ) ^ (⌈x⌉₊ + 1) := by
      exact_mod_cast Nat.lt_two_pow_self (n := ⌈x⌉₊ + 1)
    push_cast at h2
    linarith
  classical
  let m := Nat.find hex
  have hm_spec : x < (2 : ℝ) ^ m := Nat.find_spec hex
  have hm_pos : 0 < m := by
    by_contra h0
    have hm0 : m = 0 := by omega
    rw [hm0, pow_zero] at hm_spec
    linarith
  refine ⟨m - 1, ?_, ?_⟩
  · have hmin := Nat.find_min hex (Nat.sub_lt hm_pos Nat.zero_lt_one)
    exact not_lt.mp hmin
  · rwa [Nat.sub_add_cancel hm_pos]

/-- For every `α > 0`, there exists a threshold `k₀ : ℕ` with `1 ≤ α * 4^k₀` and
`∀ k < k₀, α * 4^k < 1`. -/
lemma exists_four_pow_threshold {α : ℝ} (hα : 0 < α) :
    ∃ k₀ : ℕ, 1 ≤ α * (4 : ℝ) ^ k₀ ∧ ∀ k < k₀, α * (4 : ℝ) ^ k < 1 := by
  have hex : ∃ n : ℕ, 1 ≤ α * (4 : ℝ) ^ n := by
    refine ⟨⌈α⁻¹⌉₊, ?_⟩
    have h1 : α⁻¹ ≤ (⌈α⁻¹⌉₊ : ℝ) := Nat.le_ceil α⁻¹
    have h2 : (⌈α⁻¹⌉₊ : ℝ) ≤ (2 : ℝ) ^ ⌈α⁻¹⌉₊ := by
      exact_mod_cast (Nat.lt_two_pow_self (n := ⌈α⁻¹⌉₊)).le
    have h3 : (2 : ℝ) ^ ⌈α⁻¹⌉₊ ≤ (4 : ℝ) ^ ⌈α⁻¹⌉₊ :=
      pow_le_pow_left₀ (by norm_num) (by norm_num) _
    have h4 : α⁻¹ ≤ (4 : ℝ) ^ ⌈α⁻¹⌉₊ := h1.trans (h2.trans h3)
    have h5 := mul_le_mul_of_nonneg_left h4 hα.le
    rwa [mul_inv_cancel₀ hα.ne'] at h5
  classical
  exact ⟨Nat.find hex, Nat.find_spec hex, fun k hk => not_le.mp (Nat.find_min hex hk)⟩

/-- Key dyadic-shell constant `C_r = 5^r * (2 + 2^(2*r + 2) * (r + 1)!)` controlling the
Gaussian lattice theta series `Θ_L(t)`. -/
def thetaConst (r : ℕ) : ℝ :=
  (5 : ℝ) ^ r * (2 + (2 : ℝ) ^ (2 * r + 2) * ((r + 1).factorial : ℝ))

lemma thetaConst_pos (r : ℕ) : 0 < thetaConst r := by
  unfold thetaConst
  have hfac : (0 : ℝ) < ((r + 1).factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos _)
  positivity

/-- Core dyadic-series bound: for `r ≥ 1`, `α > 0`, and any `N : ℕ`,
`∑_{k < N} (2^r)^k * exp(-(α / 2) * 4^k) ≤ (2 + 2^(2*r + 2) * (r + 1)!) * (1 + α^(-(r : ℝ)/2))`. -/
lemma dyadic_exp_sum_le {r : ℕ} (hr : 1 ≤ r) {α : ℝ} (hα : 0 < α) (N : ℕ) :
    ∑ k ∈ Finset.range N, ((2 : ℝ) ^ r) ^ k * Real.exp (-(α / 2) * (4 : ℝ) ^ k) ≤
      (2 + (2 : ℝ) ^ (2 * r + 2) * ((r + 1).factorial : ℝ)) *
        (1 + α ^ (-((r : ℝ) / 2))) := by
  obtain ⟨k₀, hk₀_ge, hk₀_lt⟩ := exists_four_pow_threshold hα
  have hsplit : ∑ k ∈ Finset.range N, ((2 : ℝ) ^ r) ^ k * Real.exp (-(α / 2) * (4 : ℝ) ^ k) =
      (∑ k ∈ (Finset.range N).filter (· < k₀),
        ((2 : ℝ) ^ r) ^ k * Real.exp (-(α / 2) * (4 : ℝ) ^ k)) +
      (∑ k ∈ (Finset.range N).filter (fun k => ¬ k < k₀),
        ((2 : ℝ) ^ r) ^ k * Real.exp (-(α / 2) * (4 : ℝ) ^ k)) :=
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  rw [hsplit]
  -- Bound Part 1: k < k₀
  have hpart1 : ∑ k ∈ (Finset.range N).filter (· < k₀),
      ((2 : ℝ) ^ r) ^ k * Real.exp (-(α / 2) * (4 : ℝ) ^ k) ≤
      2 * α ^ (-((r : ℝ) / 2)) := by
    cases k₀ with
    | zero =>
      simp only [Nat.not_lt_zero, Finset.filter_false, Finset.sum_empty]
      exact mul_nonneg (by norm_num) (Real.rpow_nonneg hα.le _)
    | succ m =>
      have hsub : (Finset.range N).filter (· < m + 1) ⊆ Finset.range (m + 1) := fun k hk =>
        Finset.mem_range.mpr (Finset.mem_filter.mp hk).2
      have hle1 : ∑ k ∈ (Finset.range N).filter (· < m + 1),
          ((2 : ℝ) ^ r) ^ k * Real.exp (-(α / 2) * (4 : ℝ) ^ k) ≤
          ∑ k ∈ Finset.range (m + 1), ((2 : ℝ) ^ r) ^ k := by
        calc ∑ k ∈ (Finset.range N).filter (· < m + 1),
              ((2 : ℝ) ^ r) ^ k * Real.exp (-(α / 2) * (4 : ℝ) ^ k)
            ≤ ∑ k ∈ (Finset.range N).filter (· < m + 1), ((2 : ℝ) ^ r) ^ k := by
              refine Finset.sum_le_sum fun k _ => ?_
              have hexp1 : Real.exp (-(α / 2) * (4 : ℝ) ^ k) ≤ 1 :=
                Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity)) (by positivity))
              have hnn : 0 ≤ ((2 : ℝ) ^ r) ^ k := by positivity
              nlinarith
          _ ≤ ∑ k ∈ Finset.range (m + 1), ((2 : ℝ) ^ r) ^ k :=
              Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
      have h2r : (2 : ℝ) ≤ (2 : ℝ) ^ r := by
        calc (2 : ℝ) = (2 : ℝ) ^ 1 := (pow_one 2).symm
          _ ≤ (2 : ℝ) ^ r := pow_le_pow_right₀ (by norm_num) hr
      have hgeom : ∑ k ∈ Finset.range (m + 1), ((2 : ℝ) ^ r) ^ k ≤ 2 * ((2 : ℝ) ^ r) ^ m :=
        sum_range_pow_le_two_mul h2r m
      have hm_lt : α * (4 : ℝ) ^ m < 1 := hk₀_lt m (Nat.lt_succ_self m)
      have h2m_le : (2 : ℝ) ^ m ≤ α ^ (-(1 / 2 : ℝ)) := by
        have h4m : ((2 : ℝ) ^ m) ^ 2 = (4 : ℝ) ^ m := by
          rw [← pow_mul, mul_comm m 2, pow_mul]; norm_num
        have hsq : ((2 : ℝ) ^ m) ^ 2 ≤ α⁻¹ := by
          rw [h4m, ← one_div, le_div_iff₀ hα]
          linarith
        have hinv : α⁻¹ = (α ^ (-(1 / 2 : ℝ))) ^ 2 := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hα.le]
          norm_num
          exact (Real.rpow_neg_one α).symm
        rw [hinv] at hsq
        nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) m, Real.rpow_nonneg hα.le (-(1 / 2 : ℝ))]
      have h2rm : ((2 : ℝ) ^ r) ^ m ≤ α ^ (-((r : ℝ) / 2)) := by
        rw [← pow_mul, mul_comm r m, pow_mul]
        have hp : ((2 : ℝ) ^ m) ^ r ≤ (α ^ (-(1 / 2 : ℝ))) ^ r :=
          pow_le_pow_left₀ (by positivity) h2m_le r
        have heq : (α ^ (-(1 / 2 : ℝ))) ^ r = α ^ (-((r : ℝ) / 2)) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hα.le]
          congr 1; ring
        rwa [heq] at hp
      exact hle1.trans (hgeom.trans (mul_le_mul_of_nonneg_left h2rm (by norm_num)))
  -- Bound Part 2: k₀ ≤ k < N
  have h2k0 : ((2 : ℝ) ^ k₀) ^ r ≤ (2 : ℝ) ^ r * (1 + α ^ (-((r : ℝ) / 2))) := by
    cases k₀ with
    | zero =>
      simp only [pow_zero, one_pow]
      have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ r := one_le_pow₀ (by norm_num)
      have hnn : 0 ≤ α ^ (-((r : ℝ) / 2)) := Real.rpow_nonneg hα.le _
      nlinarith
    | succ m =>
      have hm_lt : α * (4 : ℝ) ^ m < 1 := hk₀_lt m (Nat.lt_succ_self m)
      have h2m_le : (2 : ℝ) ^ m ≤ α ^ (-(1 / 2 : ℝ)) := by
        have h4m : ((2 : ℝ) ^ m) ^ 2 = (4 : ℝ) ^ m := by
          rw [← pow_mul, mul_comm m 2, pow_mul]; norm_num
        have hsq : ((2 : ℝ) ^ m) ^ 2 ≤ α⁻¹ := by
          rw [h4m, ← one_div, le_div_iff₀ hα]
          linarith
        have hinv : α⁻¹ = (α ^ (-(1 / 2 : ℝ))) ^ 2 := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hα.le]; norm_num
          exact (Real.rpow_neg_one α).symm
        rw [hinv] at hsq
        nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) m, Real.rpow_nonneg hα.le (-(1 / 2 : ℝ))]
      have h2mr : ((2 : ℝ) ^ m) ^ r ≤ α ^ (-((r : ℝ) / 2)) := by
        have hp : ((2 : ℝ) ^ m) ^ r ≤ (α ^ (-(1 / 2 : ℝ))) ^ r :=
          pow_le_pow_left₀ (by positivity) h2m_le r
        have heq : (α ^ (-(1 / 2 : ℝ))) ^ r = α ^ (-((r : ℝ) / 2)) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hα.le]; congr 1; ring
        rwa [heq] at hp
      rw [pow_succ, mul_pow, mul_comm (((2 : ℝ) ^ m) ^ r)]
      have h2r_nn : (0 : ℝ) ≤ (2 : ℝ) ^ r := by positivity
      nlinarith
  have hpart2 : ∑ k ∈ (Finset.range N).filter (fun k => ¬ k < k₀),
      ((2 : ℝ) ^ r) ^ k * Real.exp (-(α / 2) * (4 : ℝ) ^ k) ≤
      (2 : ℝ) ^ (2 * r + 2) * ((r + 1).factorial : ℝ) * (1 + α ^ (-((r : ℝ) / 2))) := by
    let term : ℕ → ℝ := fun j =>
      ((2 : ℝ) ^ r) ^ j * Real.exp (-((4 : ℝ) ^ j / 2))
    have hbij : ∑ k ∈ (Finset.range N).filter (fun k => ¬ k < k₀),
        ((2 : ℝ) ^ r) ^ k * Real.exp (-(α / 2) * (4 : ℝ) ^ k) ≤
        ((2 : ℝ) ^ k₀) ^ r * ∑ j ∈ Finset.range (N - k₀), term j := by
      rw [Finset.mul_sum]
      have heq_sum : ∑ k ∈ (Finset.range N).filter (fun k => ¬ k < k₀),
          ((2 : ℝ) ^ r) ^ k * Real.exp (-(α / 2) * (4 : ℝ) ^ k) =
          ∑ j ∈ Finset.range (N - k₀),
            ((2 : ℝ) ^ r) ^ (k₀ + j) * Real.exp (-(α / 2) * (4 : ℝ) ^ (k₀ + j)) := by
        refine Finset.sum_bij (fun k _ => k - k₀) ?_ ?_ ?_ ?_
        · intro k hk
          rcases Finset.mem_filter.mp hk with ⟨hkN, hkge⟩
          exact Finset.mem_range.mpr (by have := Finset.mem_range.mp hkN; omega)
        · intro a ha b hb hab
          have ha' := not_lt.mp (Finset.mem_filter.mp ha).2
          have hb' := not_lt.mp (Finset.mem_filter.mp hb).2
          omega
        · intro j hj
          have hj' := Finset.mem_range.mp hj
          refine ⟨k₀ + j, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), by omega⟩, by omega⟩
        · intro k hk
          have hk' := not_lt.mp (Finset.mem_filter.mp hk).2
          rw [Nat.add_sub_cancel' hk']
      rw [heq_sum]
      refine Finset.sum_le_sum fun j _ => ?_
      have hpow : ((2 : ℝ) ^ r) ^ (k₀ + j) = ((2 : ℝ) ^ k₀) ^ r * ((2 : ℝ) ^ r) ^ j := by
        rw [pow_add, ← pow_mul, mul_comm r k₀, pow_mul]
      have h4ge : (4 : ℝ) ^ j / 2 ≤ (α / 2) * (4 : ℝ) ^ (k₀ + j) := by
        rw [pow_add]
        have h4j : 0 ≤ (4 : ℝ) ^ j := by positivity
        nlinarith [hk₀_ge]
      have hexp : Real.exp (-(α / 2) * (4 : ℝ) ^ (k₀ + j)) ≤ Real.exp (-((4 : ℝ) ^ j / 2)) :=
        Real.exp_le_exp.mpr (by linarith)
      rw [hpow, mul_assoc]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hexp (by positivity)) (by positivity)
    have hterm_le : ∀ j : ℕ, term j ≤
        ((r + 1).factorial : ℝ) * (2 : ℝ) ^ (r + 1) * ((1 : ℝ) / 2) ^ j := by
      intro j
      dsimp only [term]
      have hx : 0 < (4 : ℝ) ^ j / 2 := by positivity
      have h1 := exp_neg_le_factorial_div_pow hx (r + 1)
      have h4_eq : ((4 : ℝ) ^ j / 2) ^ (r + 1) =
          (2 : ℝ) ^ (2 * j * (r + 1)) / (2 : ℝ) ^ (r + 1) := by
        rw [div_pow, ← pow_mul]
        congr 1
        rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, ← pow_mul]
        congr 1; ring
      rw [h4_eq, div_div_eq_mul_div] at h1
      have hmul : ((2 : ℝ) ^ r) ^ j * (((r + 1).factorial : ℝ) * (2 : ℝ) ^ (r + 1) /
          (2 : ℝ) ^ (2 * j * (r + 1))) =
          ((r + 1).factorial : ℝ) * (2 : ℝ) ^ (r + 1) *
            (((2 : ℝ) ^ (r * j)) / (2 : ℝ) ^ (2 * j * (r + 1))) := by
        rw [← pow_mul]; ring
      have hratio : (2 : ℝ) ^ (r * j) / (2 : ℝ) ^ (2 * j * (r + 1)) ≤ ((1 : ℝ) / 2) ^ j := by
        rw [one_div, inv_pow, div_le_iff₀ (by positivity)]
        have hinv : (2 : ℝ) ^ j * (2 : ℝ) ^ (r * j) ≤ (2 : ℝ) ^ (2 * j * (r + 1)) := by
          rw [← pow_add]
          exact pow_le_pow_right₀ (by norm_num) (by nlinarith)
        have hpos : (0 : ℝ) < (2 : ℝ) ^ j := by positivity
        rw [← mul_le_mul_iff_right₀ hpos]
        calc (2 : ℝ) ^ j * (2 : ℝ) ^ (r * j)
            ≤ (2 : ℝ) ^ (2 * j * (r + 1)) := hinv
          _ = (2 : ℝ) ^ j * (((2 : ℝ) ^ j)⁻¹ * (2 : ℝ) ^ (2 * j * (r + 1))) := by
              rw [← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul]
      calc ((2 : ℝ) ^ r) ^ j * Real.exp (-((4 : ℝ) ^ j / 2))
          ≤ ((2 : ℝ) ^ r) ^ j * (((r + 1).factorial : ℝ) * (2 : ℝ) ^ (r + 1) /
              (2 : ℝ) ^ (2 * j * (r + 1))) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = ((r + 1).factorial : ℝ) * (2 : ℝ) ^ (r + 1) *
              ((2 : ℝ) ^ (r * j) / (2 : ℝ) ^ (2 * j * (r + 1))) := hmul
        _ ≤ ((r + 1).factorial : ℝ) * (2 : ℝ) ^ (r + 1) * ((1 : ℝ) / 2) ^ j :=
            mul_le_mul_of_nonneg_left hratio (by positivity)
    have hsum_term : ∑ j ∈ Finset.range (N - k₀), term j ≤
        ((r + 1).factorial : ℝ) * (2 : ℝ) ^ (r + 2) := by
      calc ∑ j ∈ Finset.range (N - k₀), term j
          ≤ ∑ j ∈ Finset.range (N - k₀),
              ((r + 1).factorial : ℝ) * (2 : ℝ) ^ (r + 1) * ((1 : ℝ) / 2) ^ j :=
            Finset.sum_le_sum fun j _ => hterm_le j
        _ = ((r + 1).factorial : ℝ) * (2 : ℝ) ^ (r + 1) *
              ∑ j ∈ Finset.range (N - k₀), ((1 : ℝ) / 2) ^ j := (Finset.mul_sum _ _ _).symm
        _ ≤ ((r + 1).factorial : ℝ) * (2 : ℝ) ^ (r + 1) * 2 :=
            mul_le_mul_of_nonneg_left (sum_range_half_pow_le_two _) (by positivity)
        _ = ((r + 1).factorial : ℝ) * (2 : ℝ) ^ (r + 2) := by rw [pow_succ]; ring
    have hsum_nn : 0 ≤ ∑ j ∈ Finset.range (N - k₀), term j :=
      Finset.sum_nonneg fun j _ => mul_nonneg (by positivity) (Real.exp_pos _).le
    calc ∑ k ∈ (Finset.range N).filter (fun k => ¬ k < k₀),
          ((2 : ℝ) ^ r) ^ k * Real.exp (-(α / 2) * (4 : ℝ) ^ k)
        ≤ ((2 : ℝ) ^ k₀) ^ r * ∑ j ∈ Finset.range (N - k₀), term j := hbij
      _ ≤ ((2 : ℝ) ^ r * (1 + α ^ (-((r : ℝ) / 2)))) *
            (((r + 1).factorial : ℝ) * (2 : ℝ) ^ (r + 2)) :=
          mul_le_mul h2k0 hsum_term hsum_nn (by positivity)
      _ = (2 : ℝ) ^ (2 * r + 2) * ((r + 1).factorial : ℝ) * (1 + α ^ (-((r : ℝ) / 2))) := by
          rw [show 2 * r + 2 = r + (r + 2) by omega, pow_add]; ring
  have hα_nn : 0 ≤ α ^ (-((r : ℝ) / 2)) := Real.rpow_nonneg hα.le _
  linarith

/-- One-dimensional positive integer Gaussian sum bound: for any `a > 0` and `N : ℕ`,
`∑_{k < N} exp(-π * a * (k + 1)²) ≤ 2 + 2 / √a`. -/
lemma sum_nat_succ_exp_le {a : ℝ} (ha : 0 < a) (N : ℕ) :
    ∑ k ∈ Finset.range N, Real.exp (-Real.pi * a * ((k : ℝ) + 1) ^ 2) ≤
      2 + 2 / Real.sqrt a := by
  let B : ℕ := ⌊1 / Real.sqrt a⌋₊ + 1
  have hB_pos : 0 < B := Nat.succ_pos _
  have hsq_pos : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  have hB_gt : 1 / Real.sqrt a < (B : ℝ) := by
    simpa [B] using Nat.lt_floor_add_one (1 / Real.sqrt a)
  have hB_le : (B : ℝ) ≤ 1 / Real.sqrt a + 1 := by
    have h1 : (⌊1 / Real.sqrt a⌋₊ : ℝ) ≤ 1 / Real.sqrt a := Nat.floor_le (by positivity)
    push_cast [B]; linarith
  have hexp_half : Real.exp (-1 : ℝ) ≤ 1 / 2 := by
    rw [Real.exp_neg, inv_eq_one_div, one_div_le_one_div (Real.exp_pos 1) (by norm_num)]
    linarith [Real.exp_one_gt_d9]
  -- Each k ∈ range N maps injectively into (range (N + 1)) ×ˢ (range B) via k ↦ (k / B, k % B)
  have hterm : ∀ k : ℕ,
      Real.exp (-Real.pi * a * ((k : ℝ) + 1) ^ 2) ≤ ((1 : ℝ) / 2) ^ (k / B) := by
    intro k
    by_cases hq : k / B = 0
    · rw [hq, pow_zero]
      exact Real.exp_le_one_iff.mpr (by
        have hpa : 0 ≤ Real.pi * a := by positivity
        have hsq : 0 ≤ ((k : ℝ) + 1) ^ 2 := sq_nonneg _
        nlinarith)
    · have hq_pos : 1 ≤ k / B := Nat.pos_of_ne_zero hq
      have hdiv : (k / B) * B ≤ k := Nat.div_mul_le_self k B
      have hk_ge : ((k / B : ℕ) : ℝ) * (B : ℝ) ≤ (k : ℝ) + 1 := by
        have : ((k / B : ℕ) : ℝ) * (B : ℝ) ≤ (k : ℝ) := by exact_mod_cast hdiv
        linarith
      have hq_div : ((k / B : ℕ) : ℝ) / Real.sqrt a ≤ (k : ℝ) + 1 := by
        have h1 : ((k / B : ℕ) : ℝ) * (1 / Real.sqrt a) ≤ ((k / B : ℕ) : ℝ) * (B : ℝ) :=
          mul_le_mul_of_nonneg_left hB_gt.le (Nat.cast_nonneg _)
        rw [mul_one_div] at h1
        exact h1.trans hk_ge
      have hsq_ge : ((k / B : ℕ) : ℝ) ^ 2 ≤ a * ((k : ℝ) + 1) ^ 2 := by
        have h1 := pow_le_pow_left₀ (by positivity) hq_div 2
        rw [div_pow, Real.sq_sqrt ha.le, div_le_iff₀ ha] at h1
        linarith
      have hq_le_sq : ((k / B : ℕ) : ℝ) ≤ ((k / B : ℕ) : ℝ) ^ 2 := by
        have h1 : (1 : ℝ) ≤ ((k / B : ℕ) : ℝ) := by exact_mod_cast hq_pos
        nlinarith
      have hpi_ge : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
      have hexp_arg : ((k / B : ℕ) : ℝ) ≤ Real.pi * a * ((k : ℝ) + 1) ^ 2 := by
        have h1 : ((k / B : ℕ) : ℝ) ≤ a * ((k : ℝ) + 1) ^ 2 := hq_le_sq.trans hsq_ge
        nlinarith [mul_nonneg ha.le (sq_nonneg ((k : ℝ) + 1))]
      calc Real.exp (-Real.pi * a * ((k : ℝ) + 1) ^ 2)
          ≤ Real.exp (-((k / B : ℕ) : ℝ)) := Real.exp_le_exp.mpr (by linarith)
        _ = (Real.exp (-1 : ℝ)) ^ (k / B) := by
            rw [← Real.exp_nat_mul]; congr 1; ring
        _ ≤ ((1 : ℝ) / 2) ^ (k / B) :=
            pow_le_pow_left₀ (Real.exp_pos _).le hexp_half _
  have hsum_le : ∑ k ∈ Finset.range N, Real.exp (-Real.pi * a * ((k : ℝ) + 1) ^ 2) ≤
      ∑ p ∈ (Finset.range (N + 1)) ×ˢ (Finset.range B), ((1 : ℝ) / 2) ^ p.1 := by
    calc ∑ k ∈ Finset.range N, Real.exp (-Real.pi * a * ((k : ℝ) + 1) ^ 2)
        ≤ ∑ k ∈ Finset.range N, ((1 : ℝ) / 2) ^ (k / B) :=
          Finset.sum_le_sum fun k _ => hterm k
      _ = ∑ p ∈ (Finset.range N).image (fun k => (k / B, k % B)), ((1 : ℝ) / 2) ^ p.1 := by
          rw [Finset.sum_image]
          intro x _ y _ hxy
          have h1 : x / B = y / B := congrArg Prod.fst hxy
          have h2 : x % B = y % B := congrArg Prod.snd hxy
          have hx := (Nat.div_add_mod x B).symm
          have hy := (Nat.div_add_mod y B).symm
          rw [hx, hy, h1, h2]
      _ ≤ ∑ p ∈ (Finset.range (N + 1)) ×ˢ (Finset.range B), ((1 : ℝ) / 2) ^ p.1 := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity)
          intro p hp
          rcases Finset.mem_image.mp hp with ⟨k, hk, rfl⟩
          rw [Finset.mem_product, Finset.mem_range, Finset.mem_range]
          have hkN := Finset.mem_range.mp hk
          exact ⟨lt_of_le_of_lt (Nat.div_le_self k B) (Nat.lt_succ_of_lt hkN), Nat.mod_lt k hB_pos⟩
  have hprod_eval : ∑ p ∈ (Finset.range (N + 1)) ×ˢ (Finset.range B), ((1 : ℝ) / 2) ^ p.1 =
      (B : ℝ) * ∑ q ∈ Finset.range (N + 1), ((1 : ℝ) / 2) ^ q := by
    rw [Finset.sum_product, Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    simp [nsmul_eq_mul, mul_comm]
  calc ∑ k ∈ Finset.range N, Real.exp (-Real.pi * a * ((k : ℝ) + 1) ^ 2)
      ≤ (B : ℝ) * ∑ q ∈ Finset.range (N + 1), ((1 : ℝ) / 2) ^ q := hsum_le.trans_eq hprod_eval
    _ ≤ (B : ℝ) * 2 := mul_le_mul_of_nonneg_left (sum_range_half_pow_le_two _) (Nat.cast_nonneg B)
    _ ≤ (1 / Real.sqrt a + 1) * 2 := mul_le_mul_of_nonneg_right hB_le (by norm_num)
    _ = 2 + 2 / Real.sqrt a := by ring

/-- **Uniform Shifted 1D Gaussian Theta Sum Bound**:
for EVERY `a > 0`, EVERY real shift `α : ℝ`, and EVERY finite set `s : Finset ℤ`,
`∑ n ∈ s, exp(-π * a * (n + α)²) ≤ 6 + 4 / √a`. -/
theorem sum_int_exp_shifted_le {a : ℝ} (ha : 0 < a) (α : ℝ) (s : Finset ℤ) :
    ∑ n ∈ s, Real.exp (-Real.pi * a * ((n : ℝ) + α) ^ 2) ≤ 6 + 4 / Real.sqrt a := by
  let k₀ : ℤ := ⌊α⌋
  let u : ℝ := α - (k₀ : ℝ)
  have hu0 : 0 ≤ u := sub_nonneg.mpr (Int.floor_le α)
  have hu1 : u < 1 := sub_lt_iff_lt_add'.mpr (Int.lt_floor_add_one α)
  let s' : Finset ℤ := s.image (· + k₀)
  have hshift : ∑ n ∈ s, Real.exp (-Real.pi * a * ((n : ℝ) + α) ^ 2) =
      ∑ m ∈ s', Real.exp (-Real.pi * a * ((m : ℝ) + u) ^ 2) := by
    rw [Finset.sum_image (fun x _ y _ h => add_right_cancel h)]
    refine Finset.sum_congr rfl fun n _ => ?_
    congr 2
    push_cast
    dsimp only [u]
    ring
  rw [hshift]
  let s0 := s'.filter (fun m : ℤ => m = 0 ∨ m = -1)
  let sPos := s'.filter (fun m : ℤ => 1 ≤ m)
  let sNeg := s'.filter (fun m : ℤ => m ≤ -2)
  have hpart : ∑ m ∈ s', Real.exp (-Real.pi * a * ((m : ℝ) + u) ^ 2) =
      (∑ m ∈ s0, Real.exp (-Real.pi * a * ((m : ℝ) + u) ^ 2)) +
      (∑ m ∈ sPos, Real.exp (-Real.pi * a * ((m : ℝ) + u) ^ 2)) +
      (∑ m ∈ sNeg, Real.exp (-Real.pi * a * ((m : ℝ) + u) ^ 2)) := by
    have hdisj1 : Disjoint s0 sPos := Finset.disjoint_filter.mpr fun m _ h1 h2 => by omega
    have hdisj2 : Disjoint (s0 ∪ sPos) sNeg := by
      rw [Finset.disjoint_union_left]
      exact ⟨Finset.disjoint_filter.mpr fun m _ h1 h2 => by omega,
             Finset.disjoint_filter.mpr fun m _ h1 h2 => by omega⟩
    have hunion : s0 ∪ sPos ∪ sNeg = s' := by
      ext m
      simp only [s0, sPos, sNeg, Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro ((⟨h, _⟩ | ⟨h, _⟩) | ⟨h, _⟩) <;> exact h
      · intro h
        by_cases h1 : 1 ≤ m
        · exact Or.inl (Or.inr ⟨h, h1⟩)
        · by_cases h2 : m ≤ -2
          · exact Or.inr ⟨h, h2⟩
          · exact Or.inl (Or.inl ⟨h, by omega⟩)
    rw [← Finset.sum_union hdisj1, ← Finset.sum_union hdisj2, hunion]
  rw [hpart]
  -- Bound s0 ≤ 2
  have hs0 : ∑ m ∈ s0, Real.exp (-Real.pi * a * ((m : ℝ) + u) ^ 2) ≤ 2 := by
    have hsub : s0 ⊆ ({0, -1} : Finset ℤ) := by
      intro m hm
      rcases (Finset.mem_filter.mp hm).2 with rfl | rfl <;> simp
    have hcard : s0.card ≤ 2 := (Finset.card_le_card hsub).trans (by decide)
    calc ∑ m ∈ s0, Real.exp (-Real.pi * a * ((m : ℝ) + u) ^ 2)
        ≤ ∑ _m ∈ s0, (1 : ℝ) :=
          Finset.sum_le_sum fun m _ => Real.exp_le_one_iff.mpr (by
            have hpa : 0 ≤ Real.pi * a := by positivity
            have hsq : 0 ≤ ((m : ℝ) + u) ^ 2 := sq_nonneg _
            nlinarith)
      _ = (s0.card : ℝ) := by simp
      _ ≤ 2 := by exact_mod_cast hcard
  -- Bound sPos ≤ 2 + 2 / √a
  have hsPos : ∑ m ∈ sPos, Real.exp (-Real.pi * a * ((m : ℝ) + u) ^ 2) ≤ 2 + 2 / Real.sqrt a := by
    let N : ℕ := (sPos.image (fun m => (m - 1).toNat)).sup id + 1
    calc ∑ m ∈ sPos, Real.exp (-Real.pi * a * ((m : ℝ) + u) ^ 2)
        ≤ ∑ m ∈ sPos, Real.exp (-Real.pi * a * (((m - 1).toNat : ℝ) + 1) ^ 2) := by
          refine Finset.sum_le_sum fun m hm => Real.exp_le_exp.mpr ?_
          have hm1 : 1 ≤ m := (Finset.mem_filter.mp hm).2
          have hcast : (((m - 1).toNat : ℝ) + 1) = (m : ℝ) := by
            have h0 : 0 ≤ m - 1 := by omega
            have h1 : ((m - 1).toNat : ℤ) = m - 1 := Int.toNat_of_nonneg h0
            have h2 : (((m - 1).toNat : ℤ) : ℝ) = ((m - 1 : ℤ) : ℝ) := by exact_mod_cast h1
            push_cast at h2
            linarith
          rw [hcast]
          have hm0 : (0 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (by omega : (0 : ℤ) ≤ m)
          have hsq : (m : ℝ) ^ 2 ≤ ((m : ℝ) + u) ^ 2 :=
            pow_le_pow_left₀ hm0 (by linarith) 2
          have hpa : 0 < Real.pi * a := mul_pos Real.pi_pos ha
          nlinarith
      _ = ∑ k ∈ (sPos.image (fun m : ℤ => (m - 1).toNat) : Finset ℕ),
            Real.exp (-Real.pi * a * ((k : ℝ) + 1) ^ 2) := by
          rw [Finset.sum_image]
          intro x hx y hy hxy
          have hx1 : 1 ≤ x := (Finset.mem_filter.mp hx).2
          have hy1 : 1 ≤ y := (Finset.mem_filter.mp hy).2
          have hx' : ((x - 1).toNat : ℤ) = x - 1 := Int.toNat_of_nonneg (by omega)
          have hy' : ((y - 1).toNat : ℤ) = y - 1 := Int.toNat_of_nonneg (by omega)
          have hxy' : ((x - 1).toNat : ℤ) = ((y - 1).toNat : ℤ) := by exact_mod_cast hxy
          omega
      _ ≤ ∑ k ∈ Finset.range N, Real.exp (-Real.pi * a * ((k : ℝ) + 1) ^ 2) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => (Real.exp_pos _).le)
          intro k hk
          exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup (f := id) hk))
      _ ≤ 2 + 2 / Real.sqrt a := sum_nat_succ_exp_le ha N
  -- Bound sNeg ≤ 2 + 2 / √a
  have hsNeg : ∑ m ∈ sNeg, Real.exp (-Real.pi * a * ((m : ℝ) + u) ^ 2) ≤ 2 + 2 / Real.sqrt a := by
    let N : ℕ := (sNeg.image (fun m => (-m - 2).toNat)).sup id + 1
    calc ∑ m ∈ sNeg, Real.exp (-Real.pi * a * ((m : ℝ) + u) ^ 2)
        ≤ ∑ m ∈ sNeg, Real.exp (-Real.pi * a * (((-m - 2).toNat : ℝ) + 1) ^ 2) := by
          refine Finset.sum_le_sum fun m hm => Real.exp_le_exp.mpr ?_
          have hm2 : m ≤ -2 := (Finset.mem_filter.mp hm).2
          have hcast : (((-m - 2).toNat : ℝ) + 1) = -(m : ℝ) - 1 := by
            have h0 : 0 ≤ -m - 2 := by omega
            have h1 : ((-m - 2).toNat : ℤ) = -m - 2 := Int.toNat_of_nonneg h0
            have h2 : (((-m - 2).toNat : ℤ) : ℝ) = ((-m - 2 : ℤ) : ℝ) := by exact_mod_cast h1
            push_cast at h2
            linarith
          rw [hcast]
          have hpos1 : 0 ≤ -(m : ℝ) - 1 := by
            have : (m : ℝ) ≤ -2 := by exact_mod_cast hm2
            linarith
          have hle : -(m : ℝ) - 1 ≤ -((m : ℝ) + u) := by linarith
          have hsq : (-(m : ℝ) - 1) ^ 2 ≤ ((m : ℝ) + u) ^ 2 := by nlinarith
          have hpa : 0 < Real.pi * a := mul_pos Real.pi_pos ha
          nlinarith
      _ = ∑ k ∈ (sNeg.image (fun m : ℤ => (-m - 2).toNat) : Finset ℕ),
            Real.exp (-Real.pi * a * ((k : ℝ) + 1) ^ 2) := by
          rw [Finset.sum_image]
          intro x hx y hy hxy
          have hx2 : x ≤ -2 := (Finset.mem_filter.mp hx).2
          have hy2 : y ≤ -2 := (Finset.mem_filter.mp hy).2
          have hx' : ((-x - 2).toNat : ℤ) = -x - 2 := Int.toNat_of_nonneg (by omega)
          have hy' : ((-y - 2).toNat : ℤ) = -y - 2 := Int.toNat_of_nonneg (by omega)
          have hxy' : ((-x - 2).toNat : ℤ) = ((-y - 2).toNat : ℤ) := by exact_mod_cast hxy
          omega
      _ ≤ ∑ k ∈ Finset.range N, Real.exp (-Real.pi * a * ((k : ℝ) + 1) ^ 2) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => (Real.exp_pos _).le)
          intro k hk
          exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup (f := id) hk))
      _ ≤ 2 + 2 / Real.sqrt a := sum_nat_succ_exp_le ha N
  have hsum_eq : (2 : ℝ) + (2 + 2 / Real.sqrt a) + (2 + 2 / Real.sqrt a) = 6 + 4 / Real.sqrt a := by
    ring
  linarith

/-- **Inductive Upper-Triangular Gaussian Box Sum Bound**:
peels coordinates `0, 1, ..., n - 1` one by one using `sum_int_exp_shifted_le`, yielding
`∏ i, (6 + 4 / √(a i))` uniformly over every box `[-M, M]^n` and every upper-triangular shift `μ`. -/
lemma sum_box_exp_upperTri_le :
    ∀ {n : ℕ} (M : ℕ) (a : Fin n → ℝ) (_ha : ∀ i, 0 < a i) (μ : Fin n → Fin n → ℝ),
      ∑ c ∈ Fintype.piFinset (fun _ : Fin n => Finset.Icc (-(M : ℤ)) (M : ℤ)),
        Real.exp (-Real.pi * ∑ i : Fin n, a i *
          ((c i : ℝ) + ∑ j ∈ Finset.univ.filter (fun j : Fin n => i < j), μ i j * (c j : ℝ)) ^ 2) ≤
      ∏ i : Fin n, (6 + 4 / Real.sqrt (a i))
  | 0, M, a, _, μ => by
    have hcard : Fintype.piFinset (fun _ : Fin 0 => Finset.Icc (-(M : ℤ)) (M : ℤ)) =
        {Fin.elim0} := by
      ext c
      simp only [Fintype.mem_piFinset, Finset.mem_singleton]
      exact ⟨fun _ => Subsingleton.elim c Fin.elim0, fun _ i => i.elim0⟩
    rw [hcard, Finset.sum_singleton]
    simp
  | n + 1, M, a, ha, μ => by
    let I : Finset ℤ := Finset.Icc (-(M : ℤ)) (M : ℤ)
    let boxN : Finset (Fin n → ℤ) := Fintype.piFinset fun _ : Fin n => I
    let boxS : Finset (Fin (n + 1) → ℤ) := Fintype.piFinset fun _ : Fin (n + 1) => I
    let a' : Fin n → ℝ := fun i => a i.succ
    let μ' : Fin n → Fin n → ℝ := fun i j => μ i.succ j.succ
    have hbij : ∑ c ∈ boxS,
        Real.exp (-Real.pi * ∑ i : Fin (n + 1), a i *
          ((c i : ℝ) + ∑ j ∈ Finset.univ.filter (fun j : Fin (n + 1) => i < j), μ i j * (c j : ℝ)) ^ 2) =
        ∑ p ∈ boxN ×ˢ I,
          Real.exp (-Real.pi * a 0 * ((p.2 : ℝ) + ∑ j : Fin n, μ 0 j.succ * (p.1 j : ℝ)) ^ 2) *
          Real.exp (-Real.pi * ∑ i : Fin n, a' i *
            ((p.1 i : ℝ) + ∑ j ∈ Finset.univ.filter (fun j : Fin n => i < j), μ' i j * (p.1 j : ℝ)) ^ 2) := by
      refine Finset.sum_bij (fun c _ => (fun i => c i.succ, c 0)) ?_ ?_ ?_ ?_
      · intro c hc
        rw [Finset.mem_product, Fintype.mem_piFinset]
        have hc' := Fintype.mem_piFinset.mp hc
        exact ⟨fun i => hc' i.succ, hc' 0⟩
      · intro c₁ _ c₂ _ h
        have h1 : (fun i : Fin n => c₁ i.succ) = (fun i : Fin n => c₂ i.succ) := congrArg Prod.fst h
        have h2 : c₁ 0 = c₂ 0 := congrArg Prod.snd h
        funext i
        refine Fin.cases h2 (fun j => congrFun h1 j) i
      · intro p hp
        rcases Finset.mem_product.mp hp with ⟨hp1, hp2⟩
        have hp1' := Fintype.mem_piFinset.mp hp1
        refine ⟨Fin.cons p.2 p.1, Fintype.mem_piFinset.mpr fun i => Fin.cases hp2 hp1' i, ?_⟩
        ext <;> simp
      · intro c _
        rw [← Real.exp_add, Fin.sum_univ_succ]
        congr 1
        have h0_filter : ∑ j ∈ Finset.univ.filter (fun j : Fin (n + 1) => (0 : Fin (n + 1)) < j),
            μ 0 j * (c j : ℝ) = ∑ j : Fin n, μ 0 j.succ * (c j.succ : ℝ) := by
          refine Finset.sum_bij (fun j hj => j.pred (ne_of_gt (Finset.mem_filter.mp hj).2)) ?_ ?_ ?_ ?_
          · intro _ _; exact Finset.mem_univ _
          · intro x hx y hy hxy
            have hx0 := ne_of_gt (Finset.mem_filter.mp hx).2
            have hy0 := ne_of_gt (Finset.mem_filter.mp hy).2
            rw [← Fin.succ_pred x hx0, ← Fin.succ_pred y hy0, hxy]
          · intro j _
            exact ⟨j.succ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Fin.succ_pos j⟩, Fin.pred_succ j⟩
          · intro j hj
            rw [Fin.succ_pred j (ne_of_gt (Finset.mem_filter.mp hj).2)]
        have hsucc_filter : ∀ i : Fin n,
            ∑ j ∈ Finset.univ.filter (fun j : Fin (n + 1) => i.succ < j), μ i.succ j * (c j : ℝ) =
            ∑ j ∈ Finset.univ.filter (fun j : Fin n => i < j), μ' i j * (c j.succ : ℝ) := by
          intro i
          refine Finset.sum_bij
            (fun j hj => j.pred (ne_of_gt (lt_trans (Fin.succ_pos i) (Finset.mem_filter.mp hj).2)))
            ?_ ?_ ?_ ?_
          · intro j hj
            have hlt : i.succ < j := (Finset.mem_filter.mp hj).2
            have hj0 : j ≠ 0 := ne_of_gt (lt_trans (Fin.succ_pos i) hlt)
            refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
            have h1 : i.succ < (j.pred hj0).succ := by rwa [Fin.succ_pred]
            exact Fin.succ_lt_succ_iff.mp h1
          · intro x hx y hy hxy
            have hx0 := ne_of_gt (lt_trans (Fin.succ_pos i) (Finset.mem_filter.mp hx).2)
            have hy0 := ne_of_gt (lt_trans (Fin.succ_pos i) (Finset.mem_filter.mp hy).2)
            rw [← Fin.succ_pred x hx0, ← Fin.succ_pred y hy0, hxy]
          · intro j hj
            have hij : i < j := (Finset.mem_filter.mp hj).2
            exact ⟨j.succ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Fin.succ_lt_succ_iff.mpr hij⟩,
              Fin.pred_succ j⟩
          · intro j hj
            have hj0 := ne_of_gt (lt_trans (Fin.succ_pos i) (Finset.mem_filter.mp hj).2)
            simp only [μ', Fin.succ_pred j hj0]
        rw [h0_filter]
        simp_rw [hsucc_filter]
        dsimp only [a']
        ring
    rw [hbij, Finset.sum_product]
    have hinner : ∀ c' ∈ boxN,
        ∑ c0 ∈ I,
          Real.exp (-Real.pi * a 0 * ((c0 : ℝ) + ∑ j : Fin n, μ 0 j.succ * (c' j : ℝ)) ^ 2) *
          Real.exp (-Real.pi * ∑ i : Fin n, a' i *
            ((c' i : ℝ) + ∑ j ∈ Finset.univ.filter (fun j : Fin n => i < j), μ' i j * (c' j : ℝ)) ^ 2) ≤
        (6 + 4 / Real.sqrt (a 0)) *
          Real.exp (-Real.pi * ∑ i : Fin n, a' i *
            ((c' i : ℝ) + ∑ j ∈ Finset.univ.filter (fun j : Fin n => i < j), μ' i j * (c' j : ℝ)) ^ 2) := by
      intro c' _
      rw [← Finset.sum_mul]
      exact mul_le_mul_of_nonneg_right
        (sum_int_exp_shifted_le (ha 0) (∑ j : Fin n, μ 0 j.succ * (c' j : ℝ)) I)
        (Real.exp_pos _).le
    have h1 := Finset.sum_le_sum hinner
    rw [← Finset.mul_sum] at h1
    have ih := sum_box_exp_upperTri_le M a' (fun i => ha i.succ) μ'
    rw [Fin.prod_univ_succ]
    exact h1.trans (mul_le_mul_of_nonneg_left ih (by positivity))

end ElemHelpers

/-! ## Section 2: Gaussian Lattice Theta Series `Θ_L(t)` — Summability, Two-Sided Bounds & Rapid Decay -/

section LatticeTheta

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Individual Gaussian lattice summand `v ↦ exp(-π t ‖v‖²)`. -/
def gaussianTerm (t : ℝ) (v : E) : ℝ :=
  Real.exp (-Real.pi * t * ‖v‖ ^ 2)

/-- **Gaussian Lattice Theta Series** `Θ_L(t) = ∑'_{v ∈ L} exp(-π t ‖v‖²)`. -/
def latticeTheta (L : Submodule ℤ E) (t : ℝ) : ℝ :=
  ∑' v : L, gaussianTerm t (v : E)

/-- **Gaussian Lattice Tail Sum Outside Radius `R`**:
`Θ_{L, ≥ R}(t) = ∑'_{v ∈ L, ‖v‖ ≥ R} exp(-π t ‖v‖²)`. -/
def latticeThetaOutside (L : Submodule ℤ E) (t R : ℝ) : ℝ :=
  ∑' v : L, if R ≤ ‖(v : E)‖ then gaussianTerm t (v : E) else 0

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma gaussianTerm_pos (t : ℝ) (v : E) : 0 < gaussianTerm t v :=
  Real.exp_pos _

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma gaussianTerm_nonneg (t : ℝ) (v : E) : 0 ≤ gaussianTerm t v :=
  (gaussianTerm_pos t v).le

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
@[simp]
lemma gaussianTerm_zero (t : ℝ) : gaussianTerm t (0 : E) = 1 := by
  simp [gaussianTerm]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma gaussianTerm_neg (t : ℝ) (v : E) : gaussianTerm t (-v) = gaussianTerm t v := by
  simp [gaussianTerm]

/-- **Finite-Sum Dyadic-Shell Ceiling**:
for any nonzero discrete lattice `L ⊂ E` (`r = rk L`), `t > 0`, and ANY finite subset `F : Finset L`,
`∑ v ∈ F, exp(-π t ‖v‖²) ≤ 1 + thetaConst r * (1 + (√t λ₁(L))^(-r)) * exp(-(π/2) t λ₁(L)²)`.
This simultaneously yields `Summable` AND the sharp upper bound on `Θ_L(t)`! -/
theorem sum_gaussianTerm_le_dyadic (L : Submodule ℤ E) [DiscreteTopology L] (hL0 : L ≠ ⊥)
    {t : ℝ} (ht : 0 < t) (F : Finset L) :
    ∑ v ∈ F, gaussianTerm t (v : E) ≤
      1 + thetaConst (RHDirect.ArakelovCovolume.rk L) *
        (1 + (Real.sqrt t * RHDirect.Stage2SiegelReduction.lambda1 L) ^
          (-(RHDirect.ArakelovCovolume.rk L : ℝ))) *
        Real.exp (-(Real.pi / 2) * t * (RHDirect.Stage2SiegelReduction.lambda1 L) ^ 2) := by
  classical
  let r := RHDirect.ArakelovCovolume.rk L
  let lam := RHDirect.Stage2SiegelReduction.lambda1 L
  have hr : 1 ≤ r := RHDirect.ArakelovCovolume.rk_pos_of_ne_bot L hL0
  have hlam : 0 < lam := RHDirect.Stage2SiegelReduction.lambda1_pos L hL0
  let α : ℝ := Real.pi * t * lam ^ 2
  have hα : 0 < α := by positivity
  -- Separate v = 0 from F' = F.erase 0
  let F' : Finset L := F.erase 0
  have hsplit0 : ∑ v ∈ F, gaussianTerm t (v : E) ≤ 1 + ∑ v ∈ F', gaussianTerm t (v : E) := by
    by_cases h0 : (0 : L) ∈ F
    · rw [← Finset.add_sum_erase F _ h0]
      simp [F']
    · have hF' : F' = F := Finset.erase_eq_of_notMem h0
      rw [hF']
      linarith
  -- Choose a uniform dyadic shell upper bound N covering F'
  let shellIdx : L → ℕ := fun v =>
    if hv : v ≠ 0 then
      Classical.choose (exists_dyadic_shell
        ((one_le_div hlam).mpr (RHDirect.Stage2SiegelReduction.lambda1_le_norm L v.2
          (fun h => hv (Subtype.ext h)))))
    else 0
  have hshell_spec : ∀ v : L, v ≠ 0 →
      (2 : ℝ) ^ (shellIdx v) * lam ≤ ‖(v : E)‖ ∧ ‖(v : E)‖ < (2 : ℝ) ^ (shellIdx v + 1) * lam := by
    intro v hv
    have h1 := Classical.choose_spec (exists_dyadic_shell
      ((one_le_div hlam).mpr (RHDirect.Stage2SiegelReduction.lambda1_le_norm L v.2
        (fun h => hv (Subtype.ext h)))))
    have heq : shellIdx v = Classical.choose (exists_dyadic_shell
      ((one_le_div hlam).mpr (RHDirect.Stage2SiegelReduction.lambda1_le_norm L v.2
        (fun h => hv (Subtype.ext h))))) := dif_pos hv
    rw [heq]
    exact ⟨(le_div_iff₀ hlam).mp h1.1, (div_lt_iff₀ hlam).mp h1.2⟩
  let N : ℕ := F'.sup shellIdx + 1
  have hF'_sum : ∑ v ∈ F', gaussianTerm t (v : E) =
      ∑ k ∈ Finset.range N, ∑ v ∈ F'.filter (fun v => shellIdx v = k), gaussianTerm t (v : E) := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := shellIdx) (t := Finset.range N)]
    intro v hv
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup (f := shellIdx) hv))
  -- Bound each shell k using Stage2SiegelReduction.ncard_lattice_closedBall_le
  have hshell_le : ∀ k : ℕ,
      ∑ v ∈ F'.filter (fun v => shellIdx v = k), gaussianTerm t (v : E) ≤
      (5 : ℝ) ^ r * Real.exp (-(α / 2)) *
        (((2 : ℝ) ^ r) ^ k * Real.exp (-(α / 2) * (4 : ℝ) ^ k)) := by
    intro k
    let Ak : Finset L := F'.filter (fun v => shellIdx v = k)
    have hterm : ∀ v ∈ Ak,
        gaussianTerm t (v : E) ≤ Real.exp (-α * (4 : ℝ) ^ k) := by
      intro v hv
      have hv_ne : v ≠ 0 := (Finset.mem_erase.mp (Finset.mem_filter.mp hv).1).1
      have hidx : shellIdx v = k := (Finset.mem_filter.mp hv).2
      have hge := (hshell_spec v hv_ne).1
      rw [hidx] at hge
      have hsq : ((2 : ℝ) ^ k * lam) ^ 2 ≤ ‖(v : E)‖ ^ 2 :=
        pow_le_pow_left₀ (by positivity) hge 2
      have h4k : ((2 : ℝ) ^ k * lam) ^ 2 = lam ^ 2 * (4 : ℝ) ^ k := by
        rw [mul_pow, ← pow_mul, mul_comm k 2, pow_mul]; norm_num; ring
      rw [h4k] at hsq
      unfold gaussianTerm
      apply Real.exp_le_exp.mpr
      have hpit : 0 < Real.pi * t := by positivity
      dsimp only [α]
      nlinarith
    have hcard_le : (Ak.card : ℝ) ≤ (5 : ℝ) ^ r * ((2 : ℝ) ^ r) ^ k := by
      let Rk : ℝ := (2 : ℝ) ^ (k + 1) * lam
      have hRk : 0 ≤ Rk := by positivity
      have hfin := RHDirect.Stage2SiegelReduction.lattice_inter_closedBall_finite L Rk
      have hsub : (Ak.image (fun v : L => (v : E)) : Set E) ⊆
          (L : Set E) ∩ Metric.closedBall (0 : E) Rk := by
        rintro x hx
        rcases Finset.mem_image.mp (Finset.mem_coe.mp hx) with ⟨v, hv, rfl⟩
        have hv_ne : v ≠ 0 := (Finset.mem_erase.mp (Finset.mem_filter.mp hv).1).1
        have hidx : shellIdx v = k := (Finset.mem_filter.mp hv).2
        have hlt := (hshell_spec v hv_ne).2
        rw [hidx] at hlt
        exact ⟨v.2, mem_closedBall_zero_iff.mpr hlt.le⟩
      have hcard_nat : Ak.card ≤ ((L : Set E) ∩ Metric.closedBall (0 : E) Rk).ncard := by
        have h1 : Ak.card = (Ak.image (fun v : L => (v : E))).card :=
          (Finset.card_image_of_injective Ak Subtype.coe_injective).symm
        rw [h1, ← Set.ncard_coe_finset]
        exact Set.ncard_le_ncard hsub hfin
      have hball := RHDirect.Stage2SiegelReduction.ncard_lattice_closedBall_le L hL0 hRk
      have hratio : 1 + 2 * Rk / lam ≤ 5 * (2 : ℝ) ^ k := by
        dsimp only [Rk]
        rw [mul_div_assoc, mul_div_cancel_right₀ _ hlam.ne', pow_succ]
        have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ k := one_le_pow₀ (by norm_num)
        linarith
      have hpow_le : (1 + 2 * Rk / lam) ^ r ≤ (5 * (2 : ℝ) ^ k) ^ r :=
        pow_le_pow_left₀ (by positivity) hratio r
      calc (Ak.card : ℝ)
          ≤ (((L : Set E) ∩ Metric.closedBall (0 : E) Rk).ncard : ℝ) := by exact_mod_cast hcard_nat
        _ ≤ (1 + 2 * Rk / lam) ^ r := hball
        _ ≤ (5 * (2 : ℝ) ^ k) ^ r := hpow_le
        _ = (5 : ℝ) ^ r * ((2 : ℝ) ^ r) ^ k := by
            rw [mul_pow, ← pow_mul, mul_comm k r, pow_mul]
    have hexp_split : Real.exp (-α * (4 : ℝ) ^ k) ≤
        Real.exp (-(α / 2)) * Real.exp (-(α / 2) * (4 : ℝ) ^ k) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have h4ge : (1 : ℝ) ≤ (4 : ℝ) ^ k := one_le_pow₀ (by norm_num)
      nlinarith
    calc ∑ v ∈ Ak, gaussianTerm t (v : E)
        ≤ ∑ _v ∈ Ak, Real.exp (-α * (4 : ℝ) ^ k) := Finset.sum_le_sum hterm
      _ = (Ak.card : ℝ) * Real.exp (-α * (4 : ℝ) ^ k) := by simp [nsmul_eq_mul]
      _ ≤ ((5 : ℝ) ^ r * ((2 : ℝ) ^ r) ^ k) *
            (Real.exp (-(α / 2)) * Real.exp (-(α / 2) * (4 : ℝ) ^ k)) :=
          mul_le_mul hcard_le hexp_split (Real.exp_pos _).le (by positivity)
      _ = (5 : ℝ) ^ r * Real.exp (-(α / 2)) *
            (((2 : ℝ) ^ r) ^ k * Real.exp (-(α / 2) * (4 : ℝ) ^ k)) := by ring
  -- Sum over k ∈ range N and apply dyadic_exp_sum_le
  have hF'_le : ∑ v ∈ F', gaussianTerm t (v : E) ≤
      thetaConst r * (1 + α ^ (-((r : ℝ) / 2))) * Real.exp (-(α / 2)) := by
    rw [hF'_sum]
    calc ∑ k ∈ Finset.range N, ∑ v ∈ F'.filter (fun v => shellIdx v = k), gaussianTerm t (v : E)
        ≤ ∑ k ∈ Finset.range N, (5 : ℝ) ^ r * Real.exp (-(α / 2)) *
            (((2 : ℝ) ^ r) ^ k * Real.exp (-(α / 2) * (4 : ℝ) ^ k)) :=
          Finset.sum_le_sum fun k _ => hshell_le k
      _ = (5 : ℝ) ^ r * Real.exp (-(α / 2)) *
            ∑ k ∈ Finset.range N, ((2 : ℝ) ^ r) ^ k * Real.exp (-(α / 2) * (4 : ℝ) ^ k) :=
          (Finset.mul_sum _ _ _).symm
      _ ≤ (5 : ℝ) ^ r * Real.exp (-(α / 2)) *
            ((2 + (2 : ℝ) ^ (2 * r + 2) * ((r + 1).factorial : ℝ)) * (1 + α ^ (-((r : ℝ) / 2)))) :=
          mul_le_mul_of_nonneg_left (dyadic_exp_sum_le hr hα N) (by positivity)
      _ = thetaConst r * (1 + α ^ (-((r : ℝ) / 2))) * Real.exp (-(α / 2)) := by
          unfold thetaConst; ring
  -- Compare α^(-(r/2)) = (π t λ₁²)^(-r/2) ≤ (√t λ₁)^(-r) since π ≥ 1
  have hα_rpow : α ^ (-((r : ℝ) / 2)) ≤ (Real.sqrt t * lam) ^ (-(r : ℝ)) := by
    have hsq_eq : (Real.sqrt t * lam) ^ (-(r : ℝ)) = (t * lam ^ 2) ^ (-((r : ℝ) / 2)) := by
      have hpos : 0 < t * lam ^ 2 := by positivity
      have h1 : Real.sqrt t * lam = (t * lam ^ 2) ^ ((1 : ℝ) / 2) := by
        rw [Real.mul_rpow ht.le (sq_nonneg lam), ← Real.sqrt_eq_rpow,
          ← Real.sqrt_eq_rpow, Real.sqrt_sq hlam.le]
      rw [h1, ← Real.rpow_mul hpos.le]
      congr 1; ring
    rw [hsq_eq]
    have hpi : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
    have hbase : t * lam ^ 2 ≤ α := by
      dsimp only [α]
      have hnn : 0 ≤ t * lam ^ 2 := by positivity
      nlinarith
    exact Real.rpow_le_rpow_of_nonpos (by positivity) hbase (neg_nonpos.mpr (by positivity))
  have hexp_eq : Real.exp (-(α / 2)) = Real.exp (-(Real.pi / 2) * t * lam ^ 2) := by
    dsimp only [α]; congr 1; ring
  rw [hexp_eq] at hF'_le
  have hfinal : thetaConst r * (1 + α ^ (-((r : ℝ) / 2))) *
      Real.exp (-(Real.pi / 2) * t * lam ^ 2) ≤
      thetaConst r * (1 + (Real.sqrt t * lam) ^ (-(r : ℝ))) *
      Real.exp (-(Real.pi / 2) * t * lam ^ 2) :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (by linarith) (thetaConst_pos r).le)
      (Real.exp_pos _).le
  linarith

/-- **Unconditional Summability of the Gaussian Lattice Theta Series**:
for EVERY discrete `ℤ`-lattice `L ⊂ E` and EVERY `t > 0`, `v ↦ exp(-π t ‖v‖²)` is `Summable` on `L`. -/
theorem summable_gaussianTerm (L : Submodule ℤ E) [DiscreteTopology L] {t : ℝ} (ht : 0 < t) :
    Summable (fun v : L => gaussianTerm t (v : E)) := by
  by_cases hL0 : L = ⊥
  · subst hL0
    have : Finite (⊥ : Submodule ℤ E) := Finite.of_subsingleton
    exact hasSum_fintype _ |>.summable
  · exact summable_of_sum_le (fun v => gaussianTerm_nonneg t (v : E))
      (sum_gaussianTerm_le_dyadic L hL0 ht)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- For the zero lattice `⊥`, `Θ_⊥(t) = 1`. -/
theorem latticeTheta_bot (t : ℝ) : latticeTheta (⊥ : Submodule ℤ E) t = 1 := by
  unfold latticeTheta
  rw [tsum_eq_single (0 : (⊥ : Submodule ℤ E))]
  · simp [gaussianTerm]
  · intro v hv; exact absurd (Subsingleton.elim v 0) hv

/-- `1 ≤ Θ_L(t)` for every discrete lattice `L` and `t > 0`. -/
theorem one_le_latticeTheta (L : Submodule ℤ E) [DiscreteTopology L] {t : ℝ} (ht : 0 < t) :
    1 ≤ latticeTheta L t := by
  unfold latticeTheta
  have h1 : gaussianTerm t ((0 : L) : E) ≤ ∑' v : L, gaussianTerm t (v : E) :=
    (summable_gaussianTerm L ht).le_tsum (0 : L) (fun v _ => gaussianTerm_nonneg t (v : E))
  simpa [gaussianTerm] using h1

/-- `0 < Θ_L(t)` for every discrete lattice `L` and `t > 0`. -/
theorem latticeTheta_pos (L : Submodule ℤ E) [DiscreteTopology L] {t : ℝ} (ht : 0 < t) :
    0 < latticeTheta L t :=
  lt_of_lt_of_le zero_lt_one (one_le_latticeTheta L ht)

/-- Antitonicity of `Θ_L(t)` in `t > 0`: `t₁ ≤ t₂ → Θ_L(t₂) ≤ Θ_L(t₁)`. -/
theorem latticeTheta_antitone (L : Submodule ℤ E) [DiscreteTopology L]
    {t₁ t₂ : ℝ} (ht₁ : 0 < t₁) (h12 : t₁ ≤ t₂) :
    latticeTheta L t₂ ≤ latticeTheta L t₁ := by
  have ht₂ : 0 < t₂ := lt_of_lt_of_le ht₁ h12
  exact (summable_gaussianTerm L ht₂).tsum_le_tsum
    (fun v => Real.exp_le_exp.mpr (by
      have hnn : 0 ≤ Real.pi * ‖(v : E)‖ ^ 2 := mul_nonneg Real.pi_pos.le (sq_nonneg _)
      nlinarith))
    (summable_gaussianTerm L ht₁)

/-- **Sharp Quantitative Lower Bound on `Θ_L(t)`**:
for any nonzero discrete lattice `L ⊂ E` and `t > 0`,
`1 + 2 exp(-π t λ₁(L)²) ≤ Θ_L(t)`. -/
theorem one_add_two_exp_le_latticeTheta (L : Submodule ℤ E) [DiscreteTopology L] (hL0 : L ≠ ⊥)
    {t : ℝ} (ht : 0 < t) :
    1 + 2 * Real.exp (-Real.pi * t * (RHDirect.Stage2SiegelReduction.lambda1 L) ^ 2) ≤
      latticeTheta L t := by
  classical
  obtain ⟨v₀, hv₀L, hv₀0, hv₀eq⟩ := RHDirect.Stage2SiegelReduction.exists_norm_eq_lambda1 L hL0
  let p : L := ⟨v₀, hv₀L⟩
  have hp0 : p ≠ 0 := fun h => hv₀0 (congrArg Subtype.val h)
  have hnp0 : -p ≠ 0 := neg_ne_zero.mpr hp0
  have hpnp : p ≠ -p := by
    intro h
    have h2 : (2 : ℝ) • v₀ = 0 := by
      have hv : v₀ = -v₀ := congrArg Subtype.val h
      rw [two_smul]
      conv_lhs => rhs; rw [hv]
      exact add_neg_cancel v₀
    exact hv₀0 ((smul_eq_zero.mp h2).resolve_left (by norm_num))
  let S : Finset L := {0, p, -p}
  have hsum : ∑ v ∈ S, gaussianTerm t (v : E) =
      1 + 2 * Real.exp (-Real.pi * t * (RHDirect.Stage2SiegelReduction.lambda1 L) ^ 2) := by
    have h0not : (0 : L) ∉ ({p, -p} : Finset L) := by simp [hp0.symm, hnp0.symm]
    have hpnot : p ∉ ({-p} : Finset L) := by simp [hpnp]
    dsimp only [S]
    rw [Finset.sum_insert h0not, Finset.sum_insert hpnot, Finset.sum_singleton]
    have h1 : gaussianTerm t ((0 : L) : E) = 1 := gaussianTerm_zero t
    have h2 : gaussianTerm t (p : E) =
        Real.exp (-Real.pi * t * (RHDirect.Stage2SiegelReduction.lambda1 L) ^ 2) := by
      simp [gaussianTerm, p, hv₀eq]
    have h3 : gaussianTerm t ((-p : L) : E) =
        Real.exp (-Real.pi * t * (RHDirect.Stage2SiegelReduction.lambda1 L) ^ 2) := by
      change gaussianTerm t (-v₀) = _
      rw [gaussianTerm_neg]
      simp [gaussianTerm, hv₀eq]
    rw [h1, h2, h3]
    ring
  rw [← hsum]
  exact (summable_gaussianTerm L ht).sum_le_tsum S (fun v _ => gaussianTerm_nonneg t (v : E))

/-- **Covolume Lower Bound on `Θ_L(t)`** (via Hermite's first-minimum theorem):
`1 + 2 exp(-π t (rk L) covol(L)^(2 / rk L)) ≤ Θ_L(t)`. -/
theorem latticeTheta_ge_of_covol (L : Submodule ℤ E) [DiscreteTopology L] (hL0 : L ≠ ⊥)
    {t : ℝ} (ht : 0 < t) :
    1 + 2 * Real.exp (-Real.pi * t * (RHDirect.ArakelovCovolume.rk L : ℝ) *
        (RHDirect.ArakelovCovolume.covol L) ^ (2 / (RHDirect.ArakelovCovolume.rk L : ℝ))) ≤
      latticeTheta L t := by
  have hH := RHDirect.Stage2SiegelReduction.lambda1_le_hermite L hL0
  have hlam_nn : 0 ≤ RHDirect.Stage2SiegelReduction.lambda1 L :=
    (RHDirect.Stage2SiegelReduction.lambda1_pos L hL0).le
  have hcov_pos : 0 < RHDirect.ArakelovCovolume.covol L := RHDirect.ArakelovCovolume.covol_pos L
  have hsq : (RHDirect.Stage2SiegelReduction.lambda1 L) ^ 2 ≤
      (RHDirect.ArakelovCovolume.rk L : ℝ) *
        (RHDirect.ArakelovCovolume.covol L) ^ (2 / (RHDirect.ArakelovCovolume.rk L : ℝ)) := by
    have h1 := pow_le_pow_left₀ hlam_nn hH 2
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)] at h1
    have hpow_cov : ((RHDirect.ArakelovCovolume.covol L) ^
        (1 / (RHDirect.ArakelovCovolume.rk L : ℝ))) ^ 2 =
        (RHDirect.ArakelovCovolume.covol L) ^ (2 / (RHDirect.ArakelovCovolume.rk L : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hcov_pos.le]
      congr 1; push_cast; ring
    rwa [hpow_cov] at h1
  have hexp : Real.exp (-Real.pi * t * (RHDirect.ArakelovCovolume.rk L : ℝ) *
        (RHDirect.ArakelovCovolume.covol L) ^ (2 / (RHDirect.ArakelovCovolume.rk L : ℝ))) ≤
      Real.exp (-Real.pi * t * (RHDirect.Stage2SiegelReduction.lambda1 L) ^ 2) := by
    apply Real.exp_le_exp.mpr
    have hpit : 0 < Real.pi * t := by positivity
    nlinarith
  linarith [one_add_two_exp_le_latticeTheta L hL0 ht]

/-- **Sharp Quantitative Upper Bound on `Θ_L(t)`** (from dyadic shell decomposition):
`Θ_L(t) ≤ 1 + thetaConst (rk L) * (1 + (√t λ₁(L))^(-rk L)) * exp(-(π/2) t λ₁(L)²)`. -/
theorem latticeTheta_le_dyadic_bound (L : Submodule ℤ E) [DiscreteTopology L] (hL0 : L ≠ ⊥)
    {t : ℝ} (ht : 0 < t) :
    latticeTheta L t ≤
      1 + thetaConst (RHDirect.ArakelovCovolume.rk L) *
        (1 + (Real.sqrt t * RHDirect.Stage2SiegelReduction.lambda1 L) ^
          (-(RHDirect.ArakelovCovolume.rk L : ℝ))) *
        Real.exp (-(Real.pi / 2) * t * (RHDirect.Stage2SiegelReduction.lambda1 L) ^ 2) :=
  le_of_tendsto (summable_gaussianTerm L ht).hasSum
    (Filter.Eventually.of_forall (sum_gaussianTerm_le_dyadic L hL0 ht))

/-- Simplified large-parameter upper bound: whenever `1 ≤ t * λ₁(L)²`,
`Θ_L(t) - 1 ≤ 2 * thetaConst (rk L) * exp(-(π/2) t λ₁(L)²)`. -/
theorem latticeTheta_sub_one_le_of_one_le (L : Submodule ℤ E) [DiscreteTopology L] (hL0 : L ≠ ⊥)
    {t : ℝ} (ht : 0 < t) (hbig : 1 ≤ t * (RHDirect.Stage2SiegelReduction.lambda1 L) ^ 2) :
    latticeTheta L t - 1 ≤
      2 * thetaConst (RHDirect.ArakelovCovolume.rk L) *
        Real.exp (-(Real.pi / 2) * t * (RHDirect.Stage2SiegelReduction.lambda1 L) ^ 2) := by
  have hlam : 0 < RHDirect.Stage2SiegelReduction.lambda1 L :=
    RHDirect.Stage2SiegelReduction.lambda1_pos L hL0
  have h1 : 1 ≤ Real.sqrt t * RHDirect.Stage2SiegelReduction.lambda1 L := by
    have hsq : (1 : ℝ) ^ 2 ≤ (Real.sqrt t * RHDirect.Stage2SiegelReduction.lambda1 L) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt ht.le]; linarith
    have hnn : 0 ≤ Real.sqrt t * RHDirect.Stage2SiegelReduction.lambda1 L :=
      mul_nonneg (Real.sqrt_nonneg t) hlam.le
    nlinarith
  have hrpow : (Real.sqrt t * RHDirect.Stage2SiegelReduction.lambda1 L) ^
      (-(RHDirect.ArakelovCovolume.rk L : ℝ)) ≤ 1 := by
    calc (Real.sqrt t * RHDirect.Stage2SiegelReduction.lambda1 L) ^
          (-(RHDirect.ArakelovCovolume.rk L : ℝ))
        ≤ (Real.sqrt t * RHDirect.Stage2SiegelReduction.lambda1 L) ^ (0 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le h1 (neg_nonpos.mpr (Nat.cast_nonneg _))
      _ = 1 := Real.rpow_zero _
  have hub := latticeTheta_le_dyadic_bound L hL0 ht
  have hC := (thetaConst_pos (RHDirect.ArakelovCovolume.rk L)).le
  have hexp := (Real.exp_pos (-(Real.pi / 2) * t *
    (RHDirect.Stage2SiegelReduction.lambda1 L) ^ 2)).le
  have hCexp : 0 ≤ thetaConst (RHDirect.ArakelovCovolume.rk L) *
      Real.exp (-(Real.pi / 2) * t * (RHDirect.Stage2SiegelReduction.lambda1 L) ^ 2) :=
    mul_nonneg hC hexp
  nlinarith

/-- **Super-Polynomial Rapid Decay of `Θ_L(t) - 1` as `t → ∞`**:
for every discrete lattice `L ⊂ E` and every polynomial degree `m : ℕ`,
`t^m * (Θ_L(t) - 1) → 0` as `t → ∞`. -/
theorem latticeTheta_rapid_decay (L : Submodule ℤ E) [DiscreteTopology L] (m : ℕ) :
    Tendsto (fun t : ℝ => t ^ m * (latticeTheta L t - 1)) atTop (nhds 0) := by
  by_cases hL0 : L = ⊥
  · subst hL0
    simp_rw [latticeTheta_bot, sub_self, mul_zero]
    exact tendsto_const_nhds
  · let lam := RHDirect.Stage2SiegelReduction.lambda1 L
    let c : ℝ := (Real.pi / 2) * lam ^ 2
    have hlam : 0 < lam := RHDirect.Stage2SiegelReduction.lambda1_pos L hL0
    have hc : 0 < c := by positivity
    let C : ℝ := 2 * thetaConst (RHDirect.ArakelovCovolume.rk L)
    have hC : 0 ≤ C := by
      dsimp only [C]; linarith [thetaConst_pos (RHDirect.ArakelovCovolume.rk L)]
    -- Upper envelope C * (m + 1)! / c^(m + 1) * t⁻¹ → 0
    have htop : Tendsto (fun t : ℝ => C * (((m + 1).factorial : ℝ) / c ^ (m + 1)) * t⁻¹)
        atTop (nhds 0) := by
      simpa using (tendsto_inv_atTop_zero.const_mul (C * (((m + 1).factorial : ℝ) / c ^ (m + 1))))
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds htop ?_ ?_
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
      exact mul_nonneg (pow_nonneg ht.le m) (sub_nonneg.mpr (one_le_latticeTheta L ht))
    · filter_upwards [eventually_ge_atTop (max 1 (lam ^ 2)⁻¹)] with t ht
      have ht1 : 1 ≤ t := (le_max_left _ _).trans ht
      have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht1
      have hbig : 1 ≤ t * lam ^ 2 := by
        have hinv : (lam ^ 2)⁻¹ ≤ t := (le_max_right _ _).trans ht
        exact (inv_le_iff_one_le_mul₀ (pow_pos hlam 2)).mp hinv
      have hsub := latticeTheta_sub_one_le_of_one_le L hL0 ht0 hbig
      have hexp : Real.exp (-c * t) ≤ ((m + 1).factorial : ℝ) / (c * t) ^ (m + 1) := by
        have h1 := exp_neg_le_factorial_div_pow (mul_pos hc ht0) (m + 1)
        simpa [neg_mul] using h1
      have hct : t ^ m * (C * Real.exp (-c * t)) ≤
          C * (((m + 1).factorial : ℝ) / c ^ (m + 1)) * t⁻¹ := by
        calc t ^ m * (C * Real.exp (-c * t))
            ≤ t ^ m * (C * (((m + 1).factorial : ℝ) / (c * t) ^ (m + 1))) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexp hC) (pow_nonneg ht0.le m)
          _ = C * (((m + 1).factorial : ℝ) / c ^ (m + 1)) * t⁻¹ := by
              rw [mul_pow, pow_succ]
              field_simp [hc.ne', ht0.ne']
              rw [pow_succ]; ring
      have harg : -(Real.pi / 2) * t * lam ^ 2 = -c * t := by dsimp only [c]; ring
      rw [harg] at hsub
      exact (mul_le_mul_of_nonneg_left hsub (pow_nonneg ht0.le m)).trans hct

/-- `Θ_L(t) → 1` as `t → ∞` for every discrete lattice `L ⊂ E`. -/
theorem latticeTheta_tendsto_one (L : Submodule ℤ E) [DiscreteTopology L] :
    Tendsto (latticeTheta L) atTop (nhds 1) := by
  have h0 := latticeTheta_rapid_decay L 0
  simp only [pow_zero, one_mul] at h0
  simpa using h0.add_const (1 : ℝ)

/-- **Uniform Rapid Decay in `λ₁(L)`**: for fixed `t > 0` and any family of nonzero lattices
`L : ι → Submodule ℤ E` of constant rank `r`, if `λ₁(L_i) ≥ M ≥ t^(-1/2)`, then
`Θ_{L_i}(t) - 1 ≤ 2 * thetaConst r * exp(-(π/2) t M²)`. -/
theorem latticeTheta_sub_one_le_of_lambda1_ge (L : Submodule ℤ E) [DiscreteTopology L] (hL0 : L ≠ ⊥)
    {t M : ℝ} (ht : 0 < t) (hM : 0 < M) (hbig : 1 ≤ t * M ^ 2)
    (hlam : M ≤ RHDirect.Stage2SiegelReduction.lambda1 L) :
    latticeTheta L t - 1 ≤
      2 * thetaConst (RHDirect.ArakelovCovolume.rk L) * Real.exp (-(Real.pi / 2) * t * M ^ 2) := by
  have hsq : M ^ 2 ≤ (RHDirect.Stage2SiegelReduction.lambda1 L) ^ 2 :=
    pow_le_pow_left₀ hM.le hlam 2
  have h1 := latticeTheta_sub_one_le_of_one_le L hL0 ht (hbig.trans (mul_le_mul_of_nonneg_left hsq ht.le))
  have hexp : Real.exp (-(Real.pi / 2) * t * (RHDirect.Stage2SiegelReduction.lambda1 L) ^ 2) ≤
      Real.exp (-(Real.pi / 2) * t * M ^ 2) :=
    Real.exp_le_exp.mpr (by
      have hpt : 0 < (Real.pi / 2) * t := mul_pos (half_pos Real.pi_pos) ht
      nlinarith)
  exact h1.trans (mul_le_mul_of_nonneg_left hexp (by linarith [thetaConst_pos (RHDirect.ArakelovCovolume.rk L)]))

end LatticeTheta

/-! ## Section 3: Banaszczyk Gaussian Tail Inequality & Gram–Schmidt / Covolume / Siegel-Reduced Bounds -/

section BanaszczykAndSiegelBounds

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Summability of the radius-truncated Gaussian tail sum. -/
theorem summable_gaussianTerm_outside (L : Submodule ℤ E) [DiscreteTopology L]
    {t : ℝ} (ht : 0 < t) (R : ℝ) :
    Summable (fun v : L => if R ≤ ‖(v : E)‖ then gaussianTerm t (v : E) else 0) :=
  (summable_gaussianTerm L ht).of_nonneg_of_le
    (fun v => by split_ifs <;> [exact gaussianTerm_nonneg t (v : E); exact le_rfl])
    (fun v => by split_ifs <;> [exact le_rfl; exact gaussianTerm_nonneg t (v : E)])

/-- **Banaszczyk-Style Tilted Gaussian Tail Inequality on Lattices**:
for any discrete lattice `L ⊂ E`, any `0 < s ≤ t`, and any radius `0 ≤ R`,
`∑'_{v ∈ L, ‖v‖ ≥ R} exp(-π t ‖v‖²) ≤ exp(-π (t - s) R²) * Θ_L(s)`. -/
theorem banaszczyk_gaussian_tail_tilted (L : Submodule ℤ E) [DiscreteTopology L]
    {s t R : ℝ} (hs : 0 < s) (hst : s ≤ t) (hR : 0 ≤ R) :
    latticeThetaOutside L t R ≤ Real.exp (-Real.pi * (t - s) * R ^ 2) * latticeTheta L s := by
  have ht : 0 < t := lt_of_lt_of_le hs hst
  unfold latticeThetaOutside latticeTheta
  rw [← tsum_mul_left]
  refine (summable_gaussianTerm_outside L ht R).tsum_le_tsum ?_
    ((summable_gaussianTerm L hs).mul_left _)
  intro v
  split_ifs with hRv
  · unfold gaussianTerm
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hsq : R ^ 2 ≤ ‖(v : E)‖ ^ 2 := pow_le_pow_left₀ hR hRv 2
    have hts : 0 ≤ t - s := sub_nonneg.mpr hst
    have hpts : 0 ≤ Real.pi * (t - s) := mul_nonneg Real.pi_pos.le hts
    nlinarith
  · exact mul_nonneg (Real.exp_pos _).le (gaussianTerm_nonneg s (v : E))

/-- Normalized Banaszczyk Gaussian tail probability bound:
`Θ_{L, ≥ R}(t) / Θ_L(t) ≤ exp(-π (t - s) R²) * Θ_L(s)`. -/
theorem banaszczyk_gaussian_tail_ratio (L : Submodule ℤ E) [DiscreteTopology L]
    {s t R : ℝ} (hs : 0 < s) (hst : s ≤ t) (hR : 0 ≤ R) :
    latticeThetaOutside L t R / latticeTheta L t ≤
      Real.exp (-Real.pi * (t - s) * R ^ 2) * latticeTheta L s := by
  have ht : 0 < t := lt_of_lt_of_le hs hst
  have h1 : 1 ≤ latticeTheta L t := one_le_latticeTheta L ht
  have hnn : 0 ≤ latticeThetaOutside L t R :=
    tsum_nonneg fun v => by split_ifs <;> [exact gaussianTerm_nonneg t (v : E); exact le_rfl]
  exact (div_le_self hnn h1).trans (banaszczyk_gaussian_tail_tilted L hs hst hR)

/-- **Explicit Super-Exponential Banaszczyk Gaussian Tail Bound**:
taking `s = t / 2` and applying `latticeTheta_le_dyadic_bound` yields a fully explicit tail decay
bound for every nonzero discrete lattice `L ⊂ E`, `t > 0`, and `0 ≤ R`:
`Θ_{L, ≥ R}(t) ≤ (1 + C_r (1 + (√(t/2) λ₁(L))^(-r))) * exp(-(π/2) t R²)`. -/
theorem banaszczyk_gaussian_tail_explicit (L : Submodule ℤ E) [DiscreteTopology L] (hL0 : L ≠ ⊥)
    {t R : ℝ} (ht : 0 < t) (hR : 0 ≤ R) :
    latticeThetaOutside L t R ≤
      (1 + thetaConst (RHDirect.ArakelovCovolume.rk L) *
        (1 + (Real.sqrt (t / 2) * RHDirect.Stage2SiegelReduction.lambda1 L) ^
          (-(RHDirect.ArakelovCovolume.rk L : ℝ)))) *
      Real.exp (-(Real.pi / 2) * t * R ^ 2) := by
  have ht2 : 0 < t / 2 := half_pos ht
  have h1 := banaszczyk_gaussian_tail_tilted L (s := t / 2) (t := t) ht2 (by linarith) hR
  have h2 := latticeTheta_le_dyadic_bound L hL0 ht2
  have hexp1 : Real.exp (-(Real.pi / 2) * (t / 2) *
      (RHDirect.Stage2SiegelReduction.lambda1 L) ^ 2) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by
      have hpt : 0 ≤ (Real.pi / 2) * (t / 2) := by positivity
      nlinarith [sq_nonneg (RHDirect.Stage2SiegelReduction.lambda1 L)])
  have h2' : latticeTheta L (t / 2) ≤
      1 + thetaConst (RHDirect.ArakelovCovolume.rk L) *
        (1 + (Real.sqrt (t / 2) * RHDirect.Stage2SiegelReduction.lambda1 L) ^
          (-(RHDirect.ArakelovCovolume.rk L : ℝ))) := by
    have hCnn : 0 ≤ thetaConst (RHDirect.ArakelovCovolume.rk L) *
        (1 + (Real.sqrt (t / 2) * RHDirect.Stage2SiegelReduction.lambda1 L) ^
          (-(RHDirect.ArakelovCovolume.rk L : ℝ))) :=
      mul_nonneg (thetaConst_pos _).le (add_nonneg zero_le_one
        (Real.rpow_nonneg (mul_nonneg (Real.sqrt_nonneg _)
          (RHDirect.Stage2SiegelReduction.lambda1_pos L hL0).le) _))
    nlinarith
  have harg : -Real.pi * (t - t / 2) * R ^ 2 = -(Real.pi / 2) * t * R ^ 2 := by ring
  rw [harg] at h1
  calc latticeThetaOutside L t R
      ≤ Real.exp (-(Real.pi / 2) * t * R ^ 2) * latticeTheta L (t / 2) := h1
    _ ≤ Real.exp (-(Real.pi / 2) * t * R ^ 2) *
          (1 + thetaConst (RHDirect.ArakelovCovolume.rk L) *
            (1 + (Real.sqrt (t / 2) * RHDirect.Stage2SiegelReduction.lambda1 L) ^
              (-(RHDirect.ArakelovCovolume.rk L : ℝ)))) :=
        mul_le_mul_of_nonneg_left h2' (Real.exp_pos _).le
    _ = _ := mul_comm _ _

omit [FiniteDimensional ℝ E] in
/-- **Gram–Schmidt Norm-Squared Expansion for Arbitrary Lattice Coordinate Combinations**:
`‖∑ j, c_j b_j‖² = ∑ i, (c_i + ∑_{j > i} μ_{i, j} c_j)² * ‖b*_i‖²`. -/
lemma norm_sq_sum_basis_eq_gsVec {r : ℕ} (v : Fin r → E) (c : Fin r → ℝ) :
    ‖∑ j : Fin r, c j • v j‖ ^ 2 =
      ∑ i : Fin r,
        (c i + ∑ j ∈ Finset.univ.filter (fun j : Fin r => i < j),
          RHDirect.Stage2SiegelReduction.gsCoeff v i j * c j) ^ 2 *
        ‖RHDirect.Stage2SiegelReduction.gsVec v i‖ ^ 2 := by
  have hexp : ∑ j : Fin r, c j • v j =
      ∑ i : Fin r,
        (∑ j : Fin r, RHDirect.Stage2SiegelReduction.gsCoeff v i j * c j) •
          RHDirect.Stage2SiegelReduction.gsVec v i := by
    calc ∑ j : Fin r, c j • v j
        = ∑ j : Fin r, c j • ∑ i : Fin r,
            RHDirect.Stage2SiegelReduction.gsCoeff v i j •
              RHDirect.Stage2SiegelReduction.gsVec v i := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [← RHDirect.Stage2SiegelReduction.gs_expansion v j]
      _ = ∑ j : Fin r, ∑ i : Fin r,
            (RHDirect.Stage2SiegelReduction.gsCoeff v i j * c j) •
              RHDirect.Stage2SiegelReduction.gsVec v i := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.smul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [smul_smul, mul_comm]
      _ = ∑ i : Fin r, ∑ j : Fin r,
            (RHDirect.Stage2SiegelReduction.gsCoeff v i j * c j) •
              RHDirect.Stage2SiegelReduction.gsVec v i := Finset.sum_comm
      _ = ∑ i : Fin r,
            (∑ j : Fin r, RHDirect.Stage2SiegelReduction.gsCoeff v i j * c j) •
              RHDirect.Stage2SiegelReduction.gsVec v i := by
          refine Finset.sum_congr rfl fun i _ => Finset.sum_smul.symm
  rw [← real_inner_self_eq_norm_sq, hexp, sum_inner]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_sum, Finset.sum_eq_single i]
  · rw [real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq]
    have hcoeff : ∑ j : Fin r, RHDirect.Stage2SiegelReduction.gsCoeff v i j * c j =
        c i + ∑ j ∈ Finset.univ.filter (fun j : Fin r => i < j),
          RHDirect.Stage2SiegelReduction.gsCoeff v i j * c j := by
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j : Fin r => i < j)]
      rw [add_comm]
      congr 1
      rw [Finset.sum_eq_single i]
      · simp [RHDirect.Stage2SiegelReduction.gsCoeff_self]
      · intro j hj hji
        have hlt : j < i := lt_of_le_of_ne (not_lt.mp (Finset.mem_filter.mp hj).2) hji
        simp [RHDirect.Stage2SiegelReduction.gsCoeff_of_gt v hlt]
      · intro h
        exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ i, lt_irrefl i⟩) h
    rw [hcoeff]
    ring
  · intro k _ hki
    rw [real_inner_smul_left, real_inner_smul_right,
      RHDirect.Stage2SiegelReduction.gsVec_orthogonal v hki.symm, mul_zero, mul_zero]
  · intro h; exact absurd (Finset.mem_univ i) h

/-- **Exact Gram–Schmidt Factorized Upper Bound on `Θ_L(t)`**:
for ANY `ℤ`-basis `b : Basis (Fin r) ℤ L` of a discrete lattice `L ⊂ E` and any `t > 0`,
`Θ_L(t) ≤ ∏ i, (6 + 4 / (√t ‖b*_i‖))`. -/
theorem latticeTheta_le_prod_gsVec {L : Submodule ℤ E} [DiscreteTopology L]
    {r : ℕ} (b : Basis (Fin r) ℤ L) {t : ℝ} (ht : 0 < t) :
    latticeTheta L t ≤
      ∏ i : Fin r, (6 + 4 / (Real.sqrt t *
        ‖RHDirect.Stage2SiegelReduction.gsVec (fun j => (b j : E)) i‖)) := by
  let v : Fin r → E := fun j => (b j : E)
  have hli : LinearIndependent ℝ v := RHDirect.ArakelovCovolume.linearIndependent_coe_basis L b
  have hgs_pos : ∀ i : Fin r, 0 < ‖RHDirect.Stage2SiegelReduction.gsVec v i‖ :=
    fun i => norm_pos_iff.mpr (RHDirect.Stage2SiegelReduction.gsVec_ne_zero_of_linearIndependent hli i)
  let a : Fin r → ℝ := fun i => t * ‖RHDirect.Stage2SiegelReduction.gsVec v i‖ ^ 2
  have ha : ∀ i : Fin r, 0 < a i := fun i => mul_pos ht (pow_pos (hgs_pos i) 2)
  have hsqa : ∀ i : Fin r,
      Real.sqrt (a i) = Real.sqrt t * ‖RHDirect.Stage2SiegelReduction.gsVec v i‖ := fun i => by
    dsimp only [a]
    rw [Real.sqrt_mul ht.le, Real.sqrt_sq (norm_nonneg _)]
  change latticeTheta L t ≤
    ∏ i : Fin r, (6 + 4 / (Real.sqrt t * ‖RHDirect.Stage2SiegelReduction.gsVec v i‖))
  simp_rw [← hsqa]
  refine le_of_tendsto (summable_gaussianTerm L ht).hasSum (Filter.Eventually.of_forall fun F => ?_)
  let M : ℕ := F.sup fun x => Finset.univ.sup fun i : Fin r => (b.repr x i).natAbs
  let box : Finset (Fin r → ℤ) := Fintype.piFinset fun _ : Fin r => Finset.Icc (-(M : ℤ)) (M : ℤ)
  have hrepr : ∀ x : L, (x : E) = ∑ j : Fin r, ((b.repr x j : ℤ) : ℝ) • v j := by
    intro x
    have h1 := congrArg Subtype.val (b.sum_repr x)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h1
    rw [← h1]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Int.cast_smul_eq_zsmul]
  have hF_eq : ∑ x ∈ F, gaussianTerm t (x : E) =
      ∑ c ∈ F.image (fun x => (b.repr x : Fin r → ℤ)),
        Real.exp (-Real.pi * ∑ i : Fin r, a i *
          ((c i : ℝ) + ∑ j ∈ Finset.univ.filter (fun j : Fin r => i < j),
            RHDirect.Stage2SiegelReduction.gsCoeff v i j * (c j : ℝ)) ^ 2) := by
    rw [Finset.sum_image]
    · refine Finset.sum_congr rfl fun x _ => ?_
      unfold gaussianTerm
      rw [hrepr x, norm_sq_sum_basis_eq_gsVec v (fun j => (b.repr x j : ℝ))]
      congr 1
      rw [mul_assoc]
      congr 1
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      dsimp only [a]
      ring
    · intro x _ y _ hxy
      exact b.repr.injective (Finsupp.ext (congrFun hxy))
  have hsub : F.image (fun x => (b.repr x : Fin r → ℤ)) ⊆ box := by
    intro c hc
    rcases Finset.mem_image.mp hc with ⟨x, hx, rfl⟩
    rw [Fintype.mem_piFinset]
    intro i
    rw [Finset.mem_Icc]
    have hnat : (b.repr x i).natAbs ≤ M :=
      (Finset.le_sup (f := fun i : Fin r => (b.repr x i).natAbs) (Finset.mem_univ i)).trans
        (Finset.le_sup (f := fun x => Finset.univ.sup fun i : Fin r => (b.repr x i).natAbs) hx)
    have habs : |b.repr x i| ≤ (M : ℤ) := by
      rw [← Int.natCast_natAbs]; exact_mod_cast hnat
    exact abs_le.mp habs
  rw [hF_eq]
  exact (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => (Real.exp_pos _).le)).trans
    (sum_box_exp_upperTri_le M a ha (RHDirect.Stage2SiegelReduction.gsCoeff v))

/-- **Direct Covolume & Basis-Norm Upper Bound on `Θ_L(t)`**:
for ANY `ℤ`-basis `b : Basis (Fin r) ℤ L` of a discrete lattice `L ⊂ E` and any `t > 0`,
`Θ_L(t) ≤ (∏ i, (6 √t ‖b*_i‖ + 4)) / (t^(r/2) * covol L)`
`≤ (∏ i, (6 √t ‖b_i‖ + 4)) / (t^(r/2) * covol L)`. -/
theorem latticeTheta_le_covol_div {L : Submodule ℤ E} [DiscreteTopology L]
    {r : ℕ} (b : Basis (Fin r) ℤ L) {t : ℝ} (ht : 0 < t) :
    latticeTheta L t ≤
      (∏ i : Fin r, (6 * Real.sqrt t *
        ‖RHDirect.Stage2SiegelReduction.gsVec (fun j => (b j : E)) i‖ + 4)) /
        (t ^ ((r : ℝ) / 2) * RHDirect.ArakelovCovolume.covol L) ∧
    latticeTheta L t ≤
      (∏ i : Fin r, (6 * Real.sqrt t * ‖(b i : E)‖ + 4)) /
        (t ^ ((r : ℝ) / 2) * RHDirect.ArakelovCovolume.covol L) := by
  let v : Fin r → E := fun j => (b j : E)
  have hli : LinearIndependent ℝ v := RHDirect.ArakelovCovolume.linearIndependent_coe_basis L b
  have hgs_pos : ∀ i : Fin r, 0 < ‖RHDirect.Stage2SiegelReduction.gsVec v i‖ :=
    fun i => norm_pos_iff.mpr (RHDirect.Stage2SiegelReduction.gsVec_ne_zero_of_linearIndependent hli i)
  have hsqt_pos : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hprod_eq :
      ∏ i : Fin r, (6 + 4 / (Real.sqrt t * ‖RHDirect.Stage2SiegelReduction.gsVec v i‖)) =
      (∏ i : Fin r, (6 * Real.sqrt t * ‖RHDirect.Stage2SiegelReduction.gsVec v i‖ + 4)) /
        (t ^ ((r : ℝ) / 2) * RHDirect.ArakelovCovolume.covol L) := by
    have hterm : ∀ i : Fin r,
        6 + 4 / (Real.sqrt t * ‖RHDirect.Stage2SiegelReduction.gsVec v i‖) =
        (6 * Real.sqrt t * ‖RHDirect.Stage2SiegelReduction.gsVec v i‖ + 4) /
          (Real.sqrt t * ‖RHDirect.Stage2SiegelReduction.gsVec v i‖) := fun i => by
      have hne1 : Real.sqrt t ≠ 0 := hsqt_pos.ne'
      have hne2 : ‖RHDirect.Stage2SiegelReduction.gsVec v i‖ ≠ 0 := (hgs_pos i).ne'
      field_simp [hne1, hne2]
    simp_rw [hterm, Finset.prod_div_distrib, Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin]
    rw [← RHDirect.Stage2SiegelReduction.covol_eq_prod_gsVec b]
    have hpow : (Real.sqrt t) ^ r = t ^ ((r : ℝ) / 2) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul ht.le]
      congr 1; ring
    rw [hpow]
  have h1 : latticeTheta L t ≤
      (∏ i : Fin r, (6 * Real.sqrt t * ‖RHDirect.Stage2SiegelReduction.gsVec v i‖ + 4)) /
        (t ^ ((r : ℝ) / 2) * RHDirect.ArakelovCovolume.covol L) := by
    rw [← hprod_eq]
    exact latticeTheta_le_prod_gsVec b ht
  have h2 : (∏ i : Fin r, (6 * Real.sqrt t * ‖RHDirect.Stage2SiegelReduction.gsVec v i‖ + 4)) /
        (t ^ ((r : ℝ) / 2) * RHDirect.ArakelovCovolume.covol L) ≤
      (∏ i : Fin r, (6 * Real.sqrt t * ‖v i‖ + 4)) /
        (t ^ ((r : ℝ) / 2) * RHDirect.ArakelovCovolume.covol L) := by
    have hden_pos : 0 < t ^ ((r : ℝ) / 2) * RHDirect.ArakelovCovolume.covol L :=
      mul_pos (Real.rpow_pos_of_pos ht _) (RHDirect.ArakelovCovolume.covol_pos L)
    refine div_le_div_of_nonneg_right ?_ hden_pos.le
    refine Finset.prod_le_prod (fun i _ => by positivity) fun i _ => ?_
    have hle := RHDirect.Stage2SiegelReduction.gsVec_norm_le v i
    nlinarith
  exact ⟨h1, h1.trans h2⟩

omit [FiniteDimensional ℝ E] in
/-- First Gram–Schmidt vector equals the first basis vector: `gsVec v 0 = v 0`. -/
lemma gsVec_zero_eq {r : ℕ} (hr : 0 < r) (v : Fin r → E) :
    RHDirect.Stage2SiegelReduction.gsVec v ⟨0, hr⟩ = v ⟨0, hr⟩ := by
  rw [RHDirect.Stage2SiegelReduction.gsVec]
  simp

/-- **Siegel-Reduced Gaussian Theta Decay Upper Bound**:
for a `(C_diag, C_unip)`-Siegel-reduced basis `b` of a nonzero discrete lattice `L` (`r = rk L > 0`)
and `t > 0`, letting `δ := ‖b_0‖ / C_diag^(r - 1) > 0`, we have `δ ≤ λ₁(L)` and
`Θ_L(t) ≤ 1 + thetaConst r * (1 + (√t δ)^(-r)) * exp(-(π/2) t δ²)`. -/
theorem latticeTheta_le_of_siegelReduced {L : Submodule ℤ E} [DiscreteTopology L] (hL0 : L ≠ ⊥)
    {b : Basis (Fin (RHDirect.ArakelovCovolume.rk L)) ℤ L} {C_diag C_unip : ℝ}
    (hS : RHDirect.Stage2SiegelReduction.IsSiegelReduced b C_diag C_unip)
    {t : ℝ} (ht : 0 < t) :
    let r := RHDirect.ArakelovCovolume.rk L
    let hr : 0 < r := RHDirect.ArakelovCovolume.rk_pos_of_ne_bot L hL0
    let δ : ℝ := ‖(b ⟨0, hr⟩ : E)‖ / C_diag ^ (r - 1)
    0 < δ ∧
    δ ≤ RHDirect.Stage2SiegelReduction.lambda1 L ∧
    latticeTheta L t ≤
      1 + thetaConst r * (1 + (Real.sqrt t * δ) ^ (-(r : ℝ))) *
        Real.exp (-(Real.pi / 2) * t * δ ^ 2) := by
  let r := RHDirect.ArakelovCovolume.rk L
  have hr : 0 < r := RHDirect.ArakelovCovolume.rk_pos_of_ne_bot L hL0
  let δ : ℝ := ‖(b ⟨0, hr⟩ : E)‖ / C_diag ^ (r - 1)
  have hCd_pos : 0 < C_diag := lt_of_lt_of_le zero_lt_one hS.C_diag_ge_one
  have hb0_pos : 0 < ‖(b ⟨0, hr⟩ : E)‖ :=
    norm_pos_iff.mpr ((RHDirect.ArakelovCovolume.linearIndependent_coe_basis L b).ne_zero ⟨0, hr⟩)
  have hδ_pos : 0 < δ := div_pos hb0_pos (pow_pos hCd_pos _)
  have hfirst := hS.first_minimum_ge hr
  rw [gsVec_zero_eq hr] at hfirst
  have hδ_le : δ ≤ RHDirect.Stage2SiegelReduction.lambda1 L :=
    (div_le_iff₀ (pow_pos hCd_pos _)).mpr (by linarith)
  have hub := latticeTheta_le_dyadic_bound L hL0 ht
  have hsqt_pos : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hrpow_le : (Real.sqrt t * RHDirect.Stage2SiegelReduction.lambda1 L) ^ (-(r : ℝ)) ≤
      (Real.sqrt t * δ) ^ (-(r : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos (mul_pos hsqt_pos hδ_pos)
      (mul_le_mul_of_nonneg_left hδ_le hsqt_pos.le) (neg_nonpos.mpr (Nat.cast_nonneg r))
  have hexp_le : Real.exp (-(Real.pi / 2) * t * (RHDirect.Stage2SiegelReduction.lambda1 L) ^ 2) ≤
      Real.exp (-(Real.pi / 2) * t * δ ^ 2) := by
    apply Real.exp_le_exp.mpr
    have hsq : δ ^ 2 ≤ (RHDirect.Stage2SiegelReduction.lambda1 L) ^ 2 :=
      pow_le_pow_left₀ hδ_pos.le hδ_le 2
    have hpt : 0 < (Real.pi / 2) * t := mul_pos (half_pos Real.pi_pos) ht
    nlinarith
  have hmono : thetaConst r *
        (1 + (Real.sqrt t * RHDirect.Stage2SiegelReduction.lambda1 L) ^ (-(r : ℝ))) *
        Real.exp (-(Real.pi / 2) * t * (RHDirect.Stage2SiegelReduction.lambda1 L) ^ 2) ≤
      thetaConst r * (1 + (Real.sqrt t * δ) ^ (-(r : ℝ))) *
        Real.exp (-(Real.pi / 2) * t * δ ^ 2) := by
    refine mul_le_mul ?_ hexp_le (Real.exp_pos _).le ?_
    · exact mul_le_mul_of_nonneg_left (by linarith) (thetaConst_pos r).le
    · exact mul_nonneg (thetaConst_pos r).le (add_nonneg zero_le_one (Real.rpow_nonneg (by positivity) _))
  exact ⟨hδ_pos, hδ_le, hub.trans (by linarith)⟩

/-- **Covolume-Normalized Banaszczyk Tail Inequality**:
combines tilted Banaszczyk tail decay with the Gram–Schmidt covolume bound `latticeTheta_le_covol_div`. -/
theorem banaszczyk_tail_le_covol {L : Submodule ℤ E} [DiscreteTopology L]
    {r : ℕ} (b : Basis (Fin r) ℤ L) {t R : ℝ} (ht : 0 < t) (hR : 0 ≤ R) :
    latticeThetaOutside L t R ≤
      ((∏ i : Fin r, (6 * Real.sqrt (t / 2) * ‖(b i : E)‖ + 4)) /
        ((t / 2) ^ ((r : ℝ) / 2) * RHDirect.ArakelovCovolume.covol L)) *
      Real.exp (-(Real.pi / 2) * t * R ^ 2) := by
  have ht2 : 0 < t / 2 := half_pos ht
  have h1 := banaszczyk_gaussian_tail_tilted L (s := t / 2) (t := t) ht2 (by linarith) hR
  have h2 := (latticeTheta_le_covol_div b ht2).2
  have harg : -Real.pi * (t - t / 2) * R ^ 2 = -(Real.pi / 2) * t * R ^ 2 := by ring
  rw [harg] at h1
  calc latticeThetaOutside L t R
      ≤ Real.exp (-(Real.pi / 2) * t * R ^ 2) * latticeTheta L (t / 2) := h1
    _ ≤ Real.exp (-(Real.pi / 2) * t * R ^ 2) *
          ((∏ i : Fin r, (6 * Real.sqrt (t / 2) * ‖(b i : E)‖ + 4)) /
            ((t / 2) ^ ((r : ℝ) / 2) * RHDirect.ArakelovCovolume.covol L)) :=
        mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
    _ = _ := mul_comm _ _

end BanaszczykAndSiegelBounds

/-! ## Section 4: Hermite–Minkowski Maximal-Slope Equivalence & Gaussian-Theta Siegel-Envelope Integrability -/

section ArakelovThetaAndSiegelIntegrability

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Rank Monotonicity for Discrete Sublattices**: `N ≤ L → rk N ≤ rk L`. -/
lemma rk_le_of_le {L N : Submodule ℤ E} [DiscreteTopology L] (hNL : N ≤ L) :
    RHDirect.ArakelovCovolume.rk N ≤ RHDirect.ArakelovCovolume.rk L := by
  have : DiscreteTopology N := RHDirect.ArakelovCovolume.discreteTopology_of_le hNL
  unfold RHDirect.ArakelovCovolume.rk
  rw [RHDirect.ArakelovCovolume.finrank_int_eq_finrank_real_span N,
      RHDirect.ArakelovCovolume.finrank_int_eq_finrank_real_span L]
  exact Submodule.finrank_mono (Submodule.span_mono (show (N : Set E) ⊆ (L : Set E) from hNL))

/-- **First-Minimum Antitonicity for Sublattices**: `N ≤ L` (`N ≠ ⊥`) implies `λ₁(L) ≤ λ₁(N)`. -/
lemma lambda1_le_of_le {L N : Submodule ℤ E} [DiscreteTopology L] (hNL : N ≤ L) (hN0 : N ≠ ⊥) :
    RHDirect.Stage2SiegelReduction.lambda1 L ≤ RHDirect.Stage2SiegelReduction.lambda1 N := by
  have : DiscreteTopology N := RHDirect.ArakelovCovolume.discreteTopology_of_le hNL
  obtain ⟨v₀, hv₀N, hv₀0, hv₀eq⟩ := RHDirect.Stage2SiegelReduction.exists_norm_eq_lambda1 N hN0
  rw [← hv₀eq]
  exact RHDirect.Stage2SiegelReduction.lambda1_le_norm L (hNL hv₀N) hv₀0

/-- **Hermite–Minkowski Maximal-Slope Upper Bound** (exact converse to `neg_log_lambda1_le_muMax`):
for any nonzero discrete lattice `L ⊂ E`,
`-log λ₁(L) ≤ μ_max(L) ≤ -log λ₁(L) + (1/2) log (rk L)`. -/
theorem muMax_le_half_log_rk_sub_log_lambda1 (L : Submodule ℤ E) [DiscreteTopology L] (hL0 : L ≠ ⊥) :
    -Real.log (RHDirect.Stage2SiegelReduction.lambda1 L) ≤ RHDirect.ArakelovCovolume.muMax L ∧
    RHDirect.ArakelovCovolume.muMax L ≤
      -Real.log (RHDirect.Stage2SiegelReduction.lambda1 L) +
        (1 / 2) * Real.log (RHDirect.ArakelovCovolume.rk L : ℝ) := by
  refine ⟨RHDirect.Stage2SiegelReduction.neg_log_lambda1_le_muMax L hL0, ?_⟩
  unfold RHDirect.ArakelovCovolume.muMax
  have hne : (RHDirect.ArakelovCovolume.slopes L).Nonempty :=
    ⟨RHDirect.ArakelovCovolume.slope L, L, le_rfl, hL0, rfl⟩
  refine csSup_le hne ?_
  rintro _ ⟨N, hNL, hN0, rfl⟩
  have : DiscreteTopology N := RHDirect.ArakelovCovolume.discreteTopology_of_le hNL
  have h1 := RHDirect.Stage2SiegelReduction.slope_sub_half_log_rk_le_neg_log_lambda1 N hN0
  have hlamL : 0 < RHDirect.Stage2SiegelReduction.lambda1 L :=
    RHDirect.Stage2SiegelReduction.lambda1_pos L hL0
  have hlam_le : RHDirect.Stage2SiegelReduction.lambda1 L ≤
      RHDirect.Stage2SiegelReduction.lambda1 N := lambda1_le_of_le hNL hN0
  have hlog_lam : Real.log (RHDirect.Stage2SiegelReduction.lambda1 L) ≤
      Real.log (RHDirect.Stage2SiegelReduction.lambda1 N) :=
    Real.log_le_log hlamL hlam_le
  have hrN_pos : (0 : ℝ) < (RHDirect.ArakelovCovolume.rk N : ℝ) :=
    Nat.cast_pos.mpr (RHDirect.ArakelovCovolume.rk_pos_of_ne_bot N hN0)
  have hlog_rk : Real.log (RHDirect.ArakelovCovolume.rk N : ℝ) ≤
      Real.log (RHDirect.ArakelovCovolume.rk L : ℝ) :=
    Real.log_le_log hrN_pos (by exact_mod_cast rk_le_of_le hNL)
  linarith

/-- **First-Minimum Lower Bound Recovered from Gaussian Theta Decay**:
if `Θ_L(t) ≤ 1 + 2 exp(-π t δ²)` for some `t > 0`, then `δ ≤ λ₁(L)`! -/
theorem lambda1_ge_of_latticeTheta_le (L : Submodule ℤ E) [DiscreteTopology L] (hL0 : L ≠ ⊥)
    {t δ : ℝ} (ht : 0 < t)
    (hθ : latticeTheta L t ≤ 1 + 2 * Real.exp (-Real.pi * t * δ ^ 2)) :
    δ ≤ RHDirect.Stage2SiegelReduction.lambda1 L := by
  have hlo := one_add_two_exp_le_latticeTheta L hL0 ht
  have hexp : Real.exp (-Real.pi * t * (RHDirect.Stage2SiegelReduction.lambda1 L) ^ 2) ≤
      Real.exp (-Real.pi * t * δ ^ 2) := by linarith
  have harg := Real.exp_le_exp.mp hexp
  have hpit : 0 < Real.pi * t := by positivity
  have hsq : δ ^ 2 ≤ (RHDirect.Stage2SiegelReduction.lambda1 L) ^ 2 := by nlinarith
  nlinarith [(RHDirect.Stage2SiegelReduction.lambda1_pos L hL0).le]

/-- **Maximal-Slope Upper Bound Directly from Gaussian Theta Decay**:
if `Θ_L(t) ≤ 1 + 2 exp(-π t δ²)` (`t > 0`, `0 < δ`), then
`μ_max(L) ≤ -log δ + (1/2) log (rk L)`. -/
theorem muMax_le_of_latticeTheta_le (L : Submodule ℤ E) [DiscreteTopology L] (hL0 : L ≠ ⊥)
    {t δ : ℝ} (ht : 0 < t) (hδ : 0 < δ)
    (hθ : latticeTheta L t ≤ 1 + 2 * Real.exp (-Real.pi * t * δ ^ 2)) :
    RHDirect.ArakelovCovolume.muMax L ≤
      -Real.log δ + (1 / 2) * Real.log (RHDirect.ArakelovCovolume.rk L : ℝ) := by
  have hlam_ge := lambda1_ge_of_latticeTheta_le L hL0 ht hθ
  have hlog : Real.log δ ≤ Real.log (RHDirect.Stage2SiegelReduction.lambda1 L) :=
    Real.log_le_log hδ hlam_ge
  linarith [(muMax_le_half_log_rk_sub_log_lambda1 L hL0).2]

/-- **Two-Sided Siegel-Reduced Slope & Maximal-Slope Bounds**:
for any nonzero discrete lattice `L ⊂ E` with a `(C_diag, C_unip)`-Siegel-reduced basis `b`
(`r = rk L > 0`), both the slope lower bound (via Hadamard) and the maximal-slope upper bound
(via Hermite–Minkowski + Siegel reduction) hold unconditionally:
1. `-(1 / r) * log (∏ j, ‖b_j‖) ≤ slope L`,
2. `muMax L ≤ (1 / 2) * log r + (r - 1) * log C_diag - log ‖b_0‖`. -/
theorem slope_and_muMax_bounds_of_siegelReduced (L : Submodule ℤ E) [DiscreteTopology L] (hL0 : L ≠ ⊥)
    {b : Basis (Fin (RHDirect.ArakelovCovolume.rk L)) ℤ L} {C_diag C_unip : ℝ}
    (hS : RHDirect.Stage2SiegelReduction.IsSiegelReduced b C_diag C_unip) :
    let r := RHDirect.ArakelovCovolume.rk L
    let hr : 0 < r := RHDirect.ArakelovCovolume.rk_pos_of_ne_bot L hL0;
    -(Real.log (∏ j : Fin r, ‖(b j : E)‖) / (r : ℝ)) ≤ RHDirect.ArakelovCovolume.slope L ∧
    RHDirect.ArakelovCovolume.muMax L ≤
      (1 / 2) * Real.log (r : ℝ) + ((r - 1 : ℕ) : ℝ) * Real.log C_diag -
        Real.log ‖(b ⟨0, hr⟩ : E)‖ := by
  let r := RHDirect.ArakelovCovolume.rk L
  have hr : 0 < r := RHDirect.ArakelovCovolume.rk_pos_of_ne_bot L hL0
  have hrR : (0 : ℝ) < (r : ℝ) := Nat.cast_pos.mpr hr
  have hcov_pos : 0 < RHDirect.ArakelovCovolume.covol L := RHDirect.ArakelovCovolume.covol_pos L
  have hprod_ge := hS.prod_norm_le_covol.1
  have hlog_cov : Real.log (RHDirect.ArakelovCovolume.covol L) ≤
      Real.log (∏ j : Fin r, ‖(b j : E)‖) := Real.log_le_log hcov_pos hprod_ge
  have hslope_lo : -(Real.log (∏ j : Fin r, ‖(b j : E)‖) / (r : ℝ)) ≤
      RHDirect.ArakelovCovolume.slope L := by
    unfold RHDirect.ArakelovCovolume.slope RHDirect.ArakelovCovolume.degAr
    rw [neg_div, neg_le_neg_iff]
    exact div_le_div_of_nonneg_right hlog_cov hrR.le
  have hCd_pos : 0 < C_diag := lt_of_lt_of_le zero_lt_one hS.C_diag_ge_one
  have hb0_pos : 0 < ‖(b ⟨0, hr⟩ : E)‖ :=
    norm_pos_iff.mpr ((RHDirect.ArakelovCovolume.linearIndependent_coe_basis L b).ne_zero ⟨0, hr⟩)
  have hfirst := hS.first_minimum_ge hr
  rw [gsVec_zero_eq hr] at hfirst
  have hδ_pos : 0 < ‖(b ⟨0, hr⟩ : E)‖ / C_diag ^ (r - 1) := div_pos hb0_pos (pow_pos hCd_pos _)
  have hδ_le : ‖(b ⟨0, hr⟩ : E)‖ / C_diag ^ (r - 1) ≤ RHDirect.Stage2SiegelReduction.lambda1 L :=
    (div_le_iff₀ (pow_pos hCd_pos _)).mpr (by linarith)
  have hlog_lam : Real.log ‖(b ⟨0, hr⟩ : E)‖ - ((r - 1 : ℕ) : ℝ) * Real.log C_diag ≤
      Real.log (RHDirect.Stage2SiegelReduction.lambda1 L) := by
    have h1 := Real.log_le_log hδ_pos hδ_le
    rwa [Real.log_div hb0_pos.ne' (pow_pos hCd_pos _).ne', Real.log_pow] at h1
  have hmu_up : RHDirect.ArakelovCovolume.muMax L ≤
      (1 / 2) * Real.log (r : ℝ) + ((r - 1 : ℕ) : ℝ) * Real.log C_diag -
        Real.log ‖(b ⟨0, hr⟩ : E)‖ := by
    linarith [(muMax_le_half_log_rk_sub_log_lambda1 L hL0).2]
  exact ⟨hslope_lo, hmu_up⟩

/-- **Polynomial Height Bound for the Full Gaussian Lattice Theta Series**:
letting `H(L) = max 1 (λ₁(L))⁻¹`, for every nonzero discrete lattice `L ⊂ E` of rank `r` and `t > 0`,
`Θ_L(t) ≤ (1 + thetaConst r * (1 + (√t)^(-r))) * H(L)^r`. -/
theorem latticeTheta_le_height_pow (L : Submodule ℤ E) [DiscreteTopology L] (hL0 : L ≠ ⊥)
    {t : ℝ} (ht : 0 < t) :
    latticeTheta L t ≤
      (1 + thetaConst (RHDirect.ArakelovCovolume.rk L) *
        (1 + (Real.sqrt t) ^ (-(RHDirect.ArakelovCovolume.rk L : ℝ)))) *
      (max (1 : ℝ) (RHDirect.Stage2SiegelReduction.lambda1 L)⁻¹) ^
        (RHDirect.ArakelovCovolume.rk L) := by
  let r := RHDirect.ArakelovCovolume.rk L
  let lam := RHDirect.Stage2SiegelReduction.lambda1 L
  let H : ℝ := max (1 : ℝ) lam⁻¹
  have hlam : 0 < lam := RHDirect.Stage2SiegelReduction.lambda1_pos L hL0
  have hH1 : 1 ≤ H := le_max_left _ _
  have hHr1 : 1 ≤ H ^ r := one_le_pow₀ hH1
  have hinv_le : lam⁻¹ ≤ H := le_max_right _ _
  have hsqt_pos : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hub := latticeTheta_le_dyadic_bound L hL0 ht
  have hexp1 : Real.exp (-(Real.pi / 2) * t * lam ^ 2) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by
      have hpt : 0 ≤ (Real.pi / 2) * t := by positivity
      nlinarith [sq_nonneg lam])
  have hrpow_split : (Real.sqrt t * lam) ^ (-(r : ℝ)) ≤
      (Real.sqrt t) ^ (-(r : ℝ)) * H ^ r := by
    rw [Real.mul_rpow hsqt_pos.le hlam.le, Real.rpow_neg hlam.le, Real.rpow_natCast, ← inv_pow]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (inv_nonneg.mpr hlam.le) hinv_le r)
      (Real.rpow_nonneg hsqt_pos.le _)
  have hC : 0 ≤ thetaConst r := (thetaConst_pos r).le
  have hprod_nn : 0 ≤ thetaConst r * (1 + (Real.sqrt t * lam) ^ (-(r : ℝ))) :=
    mul_nonneg hC (add_nonneg zero_le_one (Real.rpow_nonneg (by positivity) _))
  have h1 : latticeTheta L t ≤ 1 + thetaConst r * (1 + (Real.sqrt t * lam) ^ (-(r : ℝ))) := by
    nlinarith
  have h2 : 1 + (Real.sqrt t * lam) ^ (-(r : ℝ)) ≤
      (1 + (Real.sqrt t) ^ (-(r : ℝ))) * H ^ r := by
    have hnn : 0 ≤ (Real.sqrt t) ^ (-(r : ℝ)) := Real.rpow_nonneg hsqt_pos.le _
    nlinarith
  nlinarith

/-- **Gaussian-Theta Siegel-Envelope Bochner Integrability & Quantitative `L¹` Bound**:
upgrades `Stage2SiegelReduction.thetaKernel_integrable_of_lattice_ball_bound` from finite balls to
the full infinite Gaussian lattice theta series `Θ_{L(x)}(t)`. If `‖θ x‖ ≤ C * Θ_{L(x)}(t) * H(x)^(-decayExp)`
a.e. with `critExp + r ≤ decayExp`, then `θ` is Bochner integrable on `(X, μ)` with an explicit
`L¹` ceiling! -/
theorem thetaKernel_integrable_of_gaussian_theta_bound {X : Type*} [MeasurableSpace X]
    {μ : Measure X} (L : X → Submodule ℤ E) [∀ x, DiscreteTopology (L x)]
    (hL0 : ∀ x, L x ≠ ⊥) {r : ℕ} (hrk : ∀ x, RHDirect.ArakelovCovolume.rk (L x) = r)
    {t critExp decayExp C : ℝ} (ht : 0 < t) (hC : 0 ≤ C) (hExp : critExp + (r : ℝ) ≤ decayExp)
    (hmeas : AEStronglyMeasurable
      (fun x => max (1 : ℝ) (RHDirect.Stage2SiegelReduction.lambda1 (L x))⁻¹) μ)
    (hint : Integrable
      (fun x => (max (1 : ℝ) (RHDirect.Stage2SiegelReduction.lambda1 (L x))⁻¹) ^ (-critExp)) μ)
    {θ : X → ℂ} (hθm : AEStronglyMeasurable θ μ)
    (hθb : ∀ᵐ x ∂μ, ‖θ x‖ ≤ C * latticeTheta (L x) t *
      (max (1 : ℝ) (RHDirect.Stage2SiegelReduction.lambda1 (L x))⁻¹) ^ (-decayExp)) :
    Integrable θ μ ∧
      ‖∫ x, θ x ∂μ‖ ≤
        (C * (1 + thetaConst r * (1 + (Real.sqrt t) ^ (-(r : ℝ))))) *
          ∫ x, (max (1 : ℝ) (RHDirect.Stage2SiegelReduction.lambda1 (L x))⁻¹) ^ (-critExp) ∂μ := by
  let Env := RHDirect.Stage2SiegelReduction.siegelSetEnvelope_of_lattice_height μ L critExp hmeas hint
  let M_t : ℝ := 1 + thetaConst r * (1 + (Real.sqrt t) ^ (-(r : ℝ)))
  have hMt_nn : 0 ≤ M_t := by
    dsimp only [M_t]
    have h1 := (thetaConst_pos r).le
    have h2 : 0 ≤ (Real.sqrt t) ^ (-(r : ℝ)) := Real.rpow_nonneg (Real.sqrt_nonneg t) _
    positivity
  have hC' : 0 ≤ C * M_t := mul_nonneg hC hMt_nn
  have hExp' : Env.critExp ≤ decayExp - (r : ℝ) := by
    dsimp only [Env, RHDirect.Stage2SiegelReduction.siegelSetEnvelope_of_lattice_height]
    linarith
  have hdom : ∀ᵐ x ∂μ, ‖θ x‖ ≤ (C * M_t) * (Env.H x) ^ (-(decayExp - (r : ℝ))) := by
    filter_upwards [hθb] with x hx
    set Hx : ℝ := max (1 : ℝ) (RHDirect.Stage2SiegelReduction.lambda1 (L x))⁻¹
    have hHx1 : 1 ≤ Hx := le_max_left _ _
    have hHxpos : 0 < Hx := lt_of_lt_of_le zero_lt_one hHx1
    have hθ_le := latticeTheta_le_height_pow (L x) (hL0 x) ht
    rw [hrk x] at hθ_le
    have hpow_combine : Hx ^ r * Hx ^ (-decayExp) = Hx ^ (-(decayExp - (r : ℝ))) := by
      rw [← Real.rpow_natCast Hx r, ← Real.rpow_add hHxpos]
      congr 1; ring
    calc ‖θ x‖
        ≤ C * latticeTheta (L x) t * Hx ^ (-decayExp) := hx
      _ ≤ C * (M_t * Hx ^ r) * Hx ^ (-decayExp) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hθ_le hC)
            (Real.rpow_nonneg hHxpos.le _)
      _ = (C * M_t) * (Hx ^ r * Hx ^ (-decayExp)) := by ring
      _ = (C * M_t) * Hx ^ (-(decayExp - (r : ℝ))) := by rw [hpow_combine]
  have hres := RHDirect.SiegelWeilCore.thetaKernel_integrable_of_siegel_envelope Env hC' hExp' hθm hdom
  exact ⟨hres.1, hres.2.2⟩

/-- **All-Steps Gaussian-Theta Weil Convergence Along `ChainRanks`**:
combines `Stage2ThetaWire.chain_weil_convergent_all_steps` with
`thetaKernel_integrable_of_gaussian_theta_bound`: whenever `R.t + 1 ≤ R.k` and
`r_witt + r_lat ≤ R.t + 1` (with `r_witt < R.t + 1`), every step `j` of the rank-stepped chain
`R.chainRank j → R.chainRank (j + 1)` lies in Weil's convergent range at `s₀ = (R.t + 1) / 2` AND
every Gaussian-theta-dominated kernel `‖θ x‖ ≤ C * Θ_{L(x)}(t) * H(x)^(-P.effRank)` is Bochner
integrable with explicit `L¹` ceiling! -/
theorem chain_gaussianTheta_weil_convergent_all_steps (R : RHDirect.ChainRanks)
    (r_witt r_lat : ℕ) (htk : R.t + 1 ≤ R.k) (hrt : r_witt < R.t + 1)
    (hrsum : r_witt + r_lat ≤ R.t + 1) :
    ∀ j : ℕ,
      let hr : r_witt ≤ R.chainRank (j + 1) := by
        unfold RHDirect.ChainRanks.chainRank; omega
      let P := RHDirect.SiegelWeilCore.DualPairRanks.ofChainStep R j r_witt hr
      P.WeilConvergentRange ∧
      P.sZero = ((R.t : ℝ) + 1) / 2 ∧
      ∀ {X : Type*} [MeasurableSpace X] {μ : Measure X}
        (L : X → Submodule ℤ E) [∀ x, DiscreteTopology (L x)]
        (_hL0 : ∀ x, L x ≠ ⊥) (_hrk : ∀ x, RHDirect.ArakelovCovolume.rk (L x) = r_lat)
        {t C : ℝ} (_ht : 0 < t) (_hC : 0 ≤ C)
        (_hmeas : AEStronglyMeasurable
          (fun x => max (1 : ℝ) (RHDirect.Stage2SiegelReduction.lambda1 (L x))⁻¹) μ)
        (_hint : Integrable
          (fun x => (max (1 : ℝ) (RHDirect.Stage2SiegelReduction.lambda1 (L x))⁻¹) ^ (-(P.n : ℝ))) μ)
        {θ : X → ℂ} (_hθm : AEStronglyMeasurable θ μ)
        (_hθb : ∀ᵐ x ∂μ, ‖θ x‖ ≤ C * latticeTheta (L x) t *
          (max (1 : ℝ) (RHDirect.Stage2SiegelReduction.lambda1 (L x))⁻¹) ^ (-(P.effRank : ℝ))),
        Integrable θ μ ∧
          ‖∫ x, θ x ∂μ‖ ≤
            (C * (1 + thetaConst r_lat * (1 + (Real.sqrt t) ^ (-(r_lat : ℝ))))) *
              ∫ x, (max (1 : ℝ) (RHDirect.Stage2SiegelReduction.lambda1 (L x))⁻¹) ^ (-(P.n : ℝ)) ∂μ := by
  intro j
  have hr : r_witt ≤ R.chainRank (j + 1) := by
    unfold RHDirect.ChainRanks.chainRank; omega
  refine ⟨RHDirect.SiegelWeilCore.DualPairRanks.chainStep_weilRange R j r_witt hr htk hrt,
    RHDirect.SiegelWeilCore.DualPairRanks.chainStep_sZero_eq R j r_witt hr, ?_⟩
  intro X _ μ L _ hL0 hrk t C ht hC hmeas hint θ hθm hθb
  have hExp : ((RHDirect.SiegelWeilCore.DualPairRanks.ofChainStep R j r_witt
      (by unfold RHDirect.ChainRanks.chainRank; omega)).n : ℝ) + (r_lat : ℝ) ≤
      ((RHDirect.SiegelWeilCore.DualPairRanks.ofChainStep R j r_witt
      (by unfold RHDirect.ChainRanks.chainRank; omega)).effRank : ℝ) := by
    unfold RHDirect.SiegelWeilCore.DualPairRanks.ofChainStep
      RHDirect.SiegelWeilCore.DualPairRanks.effRank RHDirect.ChainRanks.chainRank
    have hnat : R.k + j * (R.t + 1) + r_lat ≤ R.k + (j + 1) * (R.t + 1) - r_witt := by
      have : (j + 1) * (R.t + 1) = j * (R.t + 1) + (R.t + 1) := by ring
      omega
    exact_mod_cast hnat
  exact thetaKernel_integrable_of_gaussian_theta_bound L hL0 hrk ht hC hExp hmeas hint hθm hθb

end ArakelovThetaAndSiegelIntegrability

/-! ## Section 5: Finite Weil Metaplectic Seesaw Positivity & Intertwiner Consistency Discharge -/

section WeilMetaplecticSeesawDischarge

/-- Exact Hilbert adjoint identification: `adjoint (finiteThetaLift ω φ₁ φ₂) = finiteThetaLiftAdj ω φ₁ φ₂`. -/
theorem finiteThetaLift_adjoint {G H M : Type*} [Group G] [Fintype G] [Group H] [Fintype H]
    [NormedAddCommGroup M] [InnerProductSpace ℂ M]
    (ω : G × H →* Module.End ℂ M) (φ₁ φ₂ : M) :
    LinearMap.adjoint (RHDirect.Stage2WeilMetaplectic.finiteThetaLift ω φ₁ φ₂) =
      RHDirect.Stage2WeilMetaplectic.finiteThetaLiftAdj ω φ₁ φ₂ := by
  apply LinearMap.ext
  intro u
  refine ext_inner_left ℂ fun f => ?_
  rw [LinearMap.adjoint_inner_right]
  exact (RHDirect.Stage2WeilMetaplectic.finiteThetaSeesawPair ω φ₁ φ₂).adjoint_eq f u

/-- Exact reverse Hilbert adjoint identification:
`adjoint (finiteThetaLiftAdj ω φ₁ φ₂) = finiteThetaLift ω φ₁ φ₂`. -/
theorem finiteThetaLiftAdj_adjoint {G H M : Type*} [Group G] [Fintype G] [Group H] [Fintype H]
    [NormedAddCommGroup M] [InnerProductSpace ℂ M]
    (ω : G × H →* Module.End ℂ M) (φ₁ φ₂ : M) :
    LinearMap.adjoint (RHDirect.Stage2WeilMetaplectic.finiteThetaLiftAdj ω φ₁ φ₂) =
      RHDirect.Stage2WeilMetaplectic.finiteThetaLift ω φ₁ φ₂ := by
  rw [← finiteThetaLift_adjoint ω φ₁ φ₂, LinearMap.adjoint_adjoint]

/-- **Automatic Rallis Eigenvalue Positivity for Finite Weil Theta Lifts**:
whenever `Θ*(Θ f) = c • f` for a nonzero vector `f` whose finite Weil theta lift `Θ f` is nonzero,
the Rallis scalar `c` is automatically a strictly positive real number (`0 < c.re ∧ c.im = 0`)
and equals `‖Θ f‖² / ‖f‖²`! -/
theorem finiteTheta_rallis_eigenvalue_pos {G H M : Type*} [Group G] [Fintype G] [Group H] [Fintype H]
    [NormedAddCommGroup M] [InnerProductSpace ℂ M]
    (ω : G × H →* Module.End ℂ M) (φ₁ φ₂ : M)
    {f : EuclideanSpace ℂ G} {c : ℂ}
    (hf : f ≠ 0) (hΘ : RHDirect.Stage2WeilMetaplectic.finiteThetaLift ω φ₁ φ₂ f ≠ 0)
    (heig : RHDirect.Stage2WeilMetaplectic.finiteThetaLiftAdj ω φ₁ φ₂
      (RHDirect.Stage2WeilMetaplectic.finiteThetaLift ω φ₁ φ₂ f) = c • f) :
    0 < c.re ∧ c.im = 0 ∧
      c.re = ‖RHDirect.Stage2WeilMetaplectic.finiteThetaLift ω φ₁ φ₂ f‖ ^ 2 / ‖f‖ ^ 2 := by
  have hcrit := (RHDirect.Stage2WeilMetaplectic.finiteTheta_rallis_criterion ω φ₁ φ₂ f).1
  rw [heig, inner_smul_right, inner_self_eq_norm_sq_to_K] at hcrit
  have hcast : (RCLike.ofReal ‖f‖ : ℂ) ^ 2 = ((‖f‖ ^ 2 : ℝ) : ℂ) := by simp
  rw [hcast] at hcrit
  have hf_sq : (0 : ℝ) < ‖f‖ ^ 2 := pow_pos (norm_pos_iff.mpr hf) 2
  have hΘ_sq : (0 : ℝ) < ‖RHDirect.Stage2WeilMetaplectic.finiteThetaLift ω φ₁ φ₂ f‖ ^ 2 :=
    pow_pos (norm_pos_iff.mpr hΘ) 2
  have hre : c.re * ‖f‖ ^ 2 = ‖RHDirect.Stage2WeilMetaplectic.finiteThetaLift ω φ₁ φ₂ f‖ ^ 2 := by
    have := congrArg Complex.re hcrit
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.ofReal_re] at this
    linarith
  have him : c.im * ‖f‖ ^ 2 = 0 := by
    have := congrArg Complex.im hcrit
    rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.ofReal_im] at this
    linarith
  have hcre : c.re = ‖RHDirect.Stage2WeilMetaplectic.finiteThetaLift ω φ₁ φ₂ f‖ ^ 2 / ‖f‖ ^ 2 :=
    (eq_div_iff hf_sq.ne').mpr hre
  exact ⟨hcre ▸ div_pos hΘ_sq hf_sq, (mul_eq_zero.mp him).resolve_right hf_sq.ne', hcre⟩

/-- **Explicit Restricted `RallisSeesaw.SeesawDualPair` from `seesaw_intertwiner_identity`**:
packages the Kudla–Rallis seesaw restriction identity on `(ιG : G₂ →* G₁, ιH : H₁ →* H₂)` as a
concrete `RHDirect.RallisSeesaw.SeesawDualPair ℂ (EuclideanSpace ℂ G₂) (EuclideanSpace ℂ H₁)`. -/
def restrictedSeesawDualPair {G₁ G₂ H₁ H₂ M : Type*}
    [Group G₁] [Group G₂] [Fintype G₂]
    [Group H₁] [Fintype H₁] [Group H₂]
    [NormedAddCommGroup M] [InnerProductSpace ℂ M]
    (ιG : G₂ →* G₁) (ιH : H₁ →* H₂)
    (ω₁ : G₁ × H₁ →* Module.End ℂ M) (ω₂ : G₂ × H₂ →* Module.End ℂ M)
    (hseesaw : ∀ (g₂ : G₂) (h₁ : H₁), ω₁ (ιG g₂, h₁) = ω₂ (g₂, ιH h₁))
    (φ₁ φ₂ : M) :
    RHDirect.RallisSeesaw.SeesawDualPair ℂ (EuclideanSpace ℂ G₂) (EuclideanSpace ℂ H₁) where
  θ :=
    { toFun := fun f => WithLp.toLp 2 (fun h₁ : H₁ =>
        RHDirect.Stage2WeilMetaplectic.finiteThetaLift ω₂ φ₁ φ₂ f (ιH h₁))
      map_add' := fun f₁ f₂ => by ext h₁; simp [map_add]
      map_smul' := fun c f => by ext h₁; simp [map_smul] }
  θAdj :=
    { toFun := fun u => WithLp.toLp 2 (fun g₂ : G₂ =>
        RHDirect.Stage2WeilMetaplectic.finiteThetaLiftAdj ω₁ φ₁ φ₂ u (ιG g₂))
      map_add' := fun u₁ u₂ => by ext g₂; simp [map_add]
      map_smul' := fun c u => by ext g₂; simp [map_smul] }
  adjoint_eq := fun f u =>
    RHDirect.Stage2WeilMetaplectic.seesaw_intertwiner_identity ιG ιH ω₁ ω₂ hseesaw φ₁ φ₂ f u

/-- **Finite Weil Metaplectic Tower Datum**:
an `m`-step chain of finite dual-pair Weil representations `(G_j, G_{j+1}, M_j, ω_j, φ₁_j, φ₂_j)`
with stable eigenspaces `S_j` where each step satisfies the Rallis scalar relation
`Θ_j*(Θ_j x) = c_j • x` with nonvanishing theta lift on `S_j \ {0}` (positivity `0 < (c_j).re`
is **discharged automatically**, not assumed!). -/
structure FiniteWeilThetaTower (m : ℕ) : Type 1 where
  G : ℕ → Type
  [grpG : ∀ j, Group (G j)]
  [finG : ∀ j, Fintype (G j)]
  M : ℕ → Type
  [normM : ∀ j, NormedAddCommGroup (M j)]
  [innerM : ∀ j, InnerProductSpace ℂ (M j)]
  ω : ∀ j, (G j × G (j + 1)) →* Module.End ℂ (M j)
  φ₁ : ∀ j, M j
  φ₂ : ∀ j, M j
  S : ∀ j, Submodule ℂ (EuclideanSpace ℂ (G j))
  c : ℕ → ℂ
  hstep : ∀ j, ∀ x ∈ S j,
    RHDirect.Stage2WeilMetaplectic.finiteThetaLiftAdj (ω j) (φ₁ j) (φ₂ j)
      (RHDirect.Stage2WeilMetaplectic.finiteThetaLift (ω j) (φ₁ j) (φ₂ j) x) = c j • x
  hS : ∀ j, ∀ x ∈ S j,
    RHDirect.Stage2WeilMetaplectic.finiteThetaLift (ω j) (φ₁ j) (φ₂ j) x ∈ S (j + 1)
  hnonvan : ∀ j < m, ∃ x ∈ S j, x ≠ 0 ∧
    RHDirect.Stage2WeilMetaplectic.finiteThetaLift (ω j) (φ₁ j) (φ₂ j) x ≠ 0

attribute [instance] FiniteWeilThetaTower.grpG FiniteWeilThetaTower.finG
  FiniteWeilThetaTower.normM FiniteWeilThetaTower.innerM

/-- Step-`j` downward theta operator `Θ_j* : L²(G_{j+1}) →ₗ[ℂ] L²(G_j)` of a `FiniteWeilThetaTower`. -/
def FiniteWeilThetaTower.downOp {m : ℕ} (W : FiniteWeilThetaTower m) (j : ℕ) :
    EuclideanSpace ℂ (W.G (j + 1)) →ₗ[ℂ] EuclideanSpace ℂ (W.G j) :=
  RHDirect.Stage2WeilMetaplectic.finiteThetaLiftAdj (W.ω j) (W.φ₁ j) (W.φ₂ j)

/-- **Unified Finite Weil Seesaw–Rallis Chain Discharge**:
from a `FiniteWeilThetaTower m`, automatically discharges:
1. Strict positivity & reality of EVERY Rallis eigenvalue `0 < (W.c j).re ∧ (W.c j).im = 0` (`j < m`),
2. Nonvanishing & submodule stability along the entire `m`-step adjoint theta tower,
3. Exact additive log-norm-square decomposition along `j = 0, ..., m`,
4. Equal nonzero eigenspace multiplicities (`eigen_swap_finrank`) at every step `j < m`! -/
theorem finiteWeil_seesaw_rallis_chain_bridge {m : ℕ} (W : FiniteWeilThetaTower m)
    {x : EuclideanSpace ℂ (W.G 0)} (hx : x ∈ W.S 0) (hx0 : x ≠ 0) :
    (∀ j < m, 0 < (W.c j).re ∧ (W.c j).im = 0) ∧
    (∀ j ≤ m, LinearMap.adjoint (RHDirect.RallisSeesaw.downChain (E := fun i => EuclideanSpace ℂ (W.G i)) W.downOp j) x ∈ W.S j ∧
      LinearMap.adjoint (RHDirect.RallisSeesaw.downChain (E := fun i => EuclideanSpace ℂ (W.G i)) W.downOp j) x ≠ 0) ∧
    Real.log (‖LinearMap.adjoint (RHDirect.RallisSeesaw.downChain (E := fun i => EuclideanSpace ℂ (W.G i)) W.downOp m) x‖ ^ 2) =
      Real.log (‖x‖ ^ 2) + ∑ j ∈ Finset.range m, Real.log (W.c j).re ∧
    (∀ j < m,
      Module.finrank ℂ (Module.End.eigenspace
          (RHDirect.Stage2WeilMetaplectic.finiteThetaLiftAdj (W.ω j) (W.φ₁ j) (W.φ₂ j) ∘ₗ
            RHDirect.Stage2WeilMetaplectic.finiteThetaLift (W.ω j) (W.φ₁ j) (W.φ₂ j)) (W.c j)) =
      Module.finrank ℂ (Module.End.eigenspace
          (RHDirect.Stage2WeilMetaplectic.finiteThetaLift (W.ω j) (W.φ₁ j) (W.φ₂ j) ∘ₗ
            RHDirect.Stage2WeilMetaplectic.finiteThetaLiftAdj (W.ω j) (W.φ₁ j) (W.φ₂ j)) (W.c j))) := by
  have hadj : ∀ j, LinearMap.adjoint (W.downOp j) =
      RHDirect.Stage2WeilMetaplectic.finiteThetaLift (W.ω j) (W.φ₁ j) (W.φ₂ j) :=
    fun j => finiteThetaLiftAdj_adjoint (W.ω j) (W.φ₁ j) (W.φ₂ j)
  have hc_pos : ∀ j < m, 0 < (W.c j).re ∧ (W.c j).im = 0 := by
    intro j hj
    obtain ⟨v, hvS, hv0, hvΘ⟩ := W.hnonvan j hj
    have h := finiteTheta_rallis_eigenvalue_pos (W.ω j) (W.φ₁ j) (W.φ₂ j) hv0 hvΘ (W.hstep j v hvS)
    exact ⟨h.1, h.2.1⟩
  have hc_ne : ∀ j < m, W.c j ≠ 0 := fun j hj hz => by
    have hpos := (hc_pos j hj).1
    rw [hz, Complex.zero_re] at hpos
    exact lt_irrefl 0 hpos
  have hstepT : ∀ j, ∀ y ∈ W.S j, W.downOp j (LinearMap.adjoint (W.downOp j) y) = W.c j • y := by
    intro j y hy
    rw [hadj j]
    exact W.hstep j y hy
  have hST : ∀ j, ∀ y ∈ W.S j, LinearMap.adjoint (W.downOp j) y ∈ W.S (j + 1) := by
    intro j y hy
    rw [hadj j]
    exact W.hS j y hy
  refine ⟨hc_pos,
    RHDirect.RallisSeesaw.definite_chain_nonvanishing (E := fun i => EuclideanSpace ℂ (W.G i))
      W.downOp W.S W.c hstepT hST m hc_ne hx hx0,
    RHDirect.RallisSeesaw.chain_log_normSq_additive (E := fun i => EuclideanSpace ℂ (W.G i))
      W.downOp W.S W.c hstepT hST m (fun j hj => (hc_pos j hj).1) hx hx0,
    fun j hj => RHDirect.Stage2WeilMetaplectic.finiteTheta_eigen_swap (W.ω j) (W.φ₁ j) (W.φ₂ j)
      (hc_ne j hj)⟩

end WeilMetaplecticSeesawDischarge

/-! ## Section 6: Unified Siegel–Arakelov–Theta Discharge & `Stage2ThetaWire` Pipeline Integration -/

section Stage3UnifiedIntegration

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Unified Siegel-Reduced Bost–Arakelov–Gaussian-Theta Fiber Theorem**:
combines `Stage2ThetaWire.Stage2GramFrameFiber` (discharging `BostSlopeFiber.SlopeIneq`, `0 ≤ η`,
`0 ≤ e ≤ 1/4`), `Stage2SiegelReduction.IsSiegelReduced` (Iwasawa heights & first minimum),
and our Gaussian lattice theta series + Banaszczyk tail bounds into ONE unified certification
theorem on a single fiber! -/
theorem siegelReduced_bost_theta_unified
    {s uF HH muMinCC delBar sgBar deBar e0Bar C_diag C_unip h_min t R : ℝ} {cardW : ℕ}
    (huF0 : 0 ≤ uF) (hHH_ge : s - muMinCC ≤ HH) (hHH_pos : 0 < HH)
    (F : RHDirect.Stage2ThetaWire.Stage2GramFrameFiber s uF HH muMinCC cardW delBar sgBar deBar e0Bar)
    (L : Submodule ℤ E) [DiscreteTopology L] (hL0 : L ≠ ⊥)
    {b : Basis (Fin (RHDirect.ArakelovCovolume.rk L)) ℤ L}
    (hS : RHDirect.Stage2SiegelReduction.IsSiegelReduced b C_diag C_unip)
    (hhpos : 0 < h_min)
    (hh : ∀ j, h_min ≤ ‖RHDirect.Stage2SiegelReduction.gsVec (fun i => (b i : E)) j‖)
    (hmuCC : F.muCC = RHDirect.ArakelovCovolume.slope L)
    (ht : 0 < t) (hR : 0 ≤ R) :
    let B := F.toBostFiber
    let r := RHDirect.ArakelovCovolume.rk L
    let hr : 0 < r := RHDirect.ArakelovCovolume.rk_pos_of_ne_bot L hL0
    let δ : ℝ := ‖(b ⟨0, hr⟩ : E)‖ / C_diag ^ (r - 1)
    B.SlopeIneq ∧
    h_min ^ r ≤ RHDirect.ArakelovCovolume.covol L ∧
    RHDirect.ArakelovCovolume.slope L ≤ -Real.log h_min ∧
    s ≤ -Real.log h_min + Real.log (cardW : ℝ) +
      (1 - B.del)⁻¹ * (4 * B.uF * Real.log (1 + B.HH / B.uF) +
        (B.η + 4 * Real.sqrt B.e) * B.HH) ∧
    RHDirect.Stage2SiegelReduction.lambda1 L ≤ Real.sqrt (r : ℝ) *
      Real.exp (-(s - Real.log (cardW : ℝ) -
        (1 - B.del)⁻¹ * (4 * B.uF * Real.log (1 + B.HH / B.uF) +
          (B.η + 4 * Real.sqrt B.e) * B.HH))) ∧
    (1 + 2 * Real.exp (-Real.pi * t * (r : ℝ) *
        (RHDirect.ArakelovCovolume.covol L) ^ (2 / (r : ℝ))) ≤ latticeTheta L t ∧
      latticeTheta L t ≤ 1 + thetaConst r * (1 + (Real.sqrt t * δ) ^ (-(r : ℝ))) *
        Real.exp (-(Real.pi / 2) * t * δ ^ 2)) ∧
    latticeThetaOutside L t R ≤
      ((∏ i : Fin r, (6 * Real.sqrt (t / 2) * ‖(b i : E)‖ + 4)) /
        ((t / 2) ^ ((r : ℝ) / 2) * RHDirect.ArakelovCovolume.covol L)) *
      Real.exp (-(Real.pi / 2) * t * R ^ 2) := by
  have hSI : F.toBostFiber.SlopeIneq := F.toBostSlopeIneq huF0
  have hδ0 : 0 ≤ F.toBostFiber.del := F.δ_nonneg
  have hδ1 : F.toBostFiber.del < 1 := by
    change F.δ < 1; linarith [F.δ_le_bar, F.delBar_le]
  have hη0 : 0 ≤ F.toBostFiber.η := F.etaVal_bounds.1
  have he0 : 0 ≤ F.toBostFiber.e := F.eVal_bounds.1
  have he4 : F.toBostFiber.e ≤ 1 / 4 := F.eVal_bounds.2.2
  obtain ⟨hcov_ge, hslope_le, hs_le⟩ :=
    RHDirect.Stage2SiegelReduction.bostSlopeFiber_covolume_of_siegelReduced F.toBostFiber L hL0
      hS hhpos hh hSI hδ0 hδ1 hη0 he0 he4 hHH_ge hHH_pos (le_of_eq hmuCC)
  have hlam_up :=
    RHDirect.Stage2SiegelReduction.bostSlopeFiber_lambda1_upper_of_slopeIneq F.toBostFiber L hL0
      hSI hδ0 hδ1 hη0 he0 he4 hHH_ge hHH_pos hmuCC
  have hθ_lo := latticeTheta_ge_of_covol L hL0 ht
  have hθ_up := (latticeTheta_le_of_siegelReduced hL0 hS ht).2.2
  have htail := banaszczyk_tail_le_covol b ht hR
  exact ⟨hSI, hcov_ge, hslope_le, hs_le, hlam_up, ⟨hθ_lo, hθ_up⟩, htail⟩

/-- **Stage 3 Strictly Reduced Fiber Witness (`Stage3ThetaSiegelFiberWitness`)**:
reduces the primitive assumptions of `Stage2ThetaWire.Stage2FiberWitness` even further by
replacing the abstract slope scalars `muN`, `muMaxN`, `muM`, `muMaxM` and the three primitive
hypotheses `mu_le_max`, `slopes.1`, and `slopes.2` with concrete discrete Arakelov lattices
`latN u0 u`, `latM u0 u` equipped with `(C_diag, C_unip)`-Siegel-reduced bases `bM u0 u`:
- `mu_le_max` is **discharged** by `ArakelovCovolume.slope_le_muMax`,
- `slopes.1` is **discharged** from the Siegel-reduced basis norm product via Hadamard,
- `slopes.2` is **discharged** from the first Siegel-reduced basis vector (or Gaussian theta decay)
  via our Hermite–Minkowski `muMax` upper bound `slope_and_muMax_bounds_of_siegelReduced`!
Additionally carries an optional finite Weil seesaw tower `weilTower : FiniteWeilThetaTower R.m`
witnessing Rallis positivity and nonvanishing along the `m`-step theta chain. -/
structure Stage3ThetaSiegelFiberWitness (S : RHDirect.SelmerSystem) (ψ : RHDirect.PChar)
    (eL K cHH eps x : ℝ) (q d_aux e_page : ℕ)
    (hx1 : 1 < x) (heps : 0 < eps) (heps52 : eps < 1 / 52) : Type 1 where
  -- Fiber index spaces & RankVal-constrained unitary chain ranks
  U0 : Type
  [finU0 : Fintype U0]
  [neU0 : Nonempty U0]
  W : U0 → Type
  [finW : ∀ u0, Fintype (W u0)]
  [neW : ∀ u0, Nonempty (W u0)]
  Top : Type
  [finTop : Fintype Top]
  R : RHDirect.ChainRanks
  f_eq : R.f = 2 * R.n
  m_ge_two : 2 ≤ R.m
  mk_le : R.m + 3 ≤ R.k
  r_eq : R.r = R.k + R.m - 1
  rankVal : RHDirect.RankVal (RHDirect.Stage2ThetaWire.stage2ScaleParams x eps hx1 heps heps52) R
  nT2 : ℕ
  nT2_le : nT2 ≤ R.n
  nT_ge_one : 1 ≤ (Fintype.card Top : ℝ)
  nT_ge_rest : x ^ (-(eps / 8)) * (R.n : ℝ) / 2 ≤ (Fintype.card Top : ℝ)
  nT2_ge_rest : x ^ (-eps) ≤ (nT2 : ℝ) / (R.n : ℝ)
  -- Concrete Euclidean inner product spaces & discrete Arakelov lattices (DISCHARGES mu_le_max & slopes!)
  EN : Type
  [normEN : NormedAddCommGroup EN]
  [innerEN : InnerProductSpace ℝ EN]
  [fdEN : FiniteDimensional ℝ EN]
  EM : Type
  [normEM : NormedAddCommGroup EM]
  [innerEM : InnerProductSpace ℝ EM]
  [fdEM : FiniteDimensional ℝ EM]
  latN : ∀ u0, W u0 → Submodule ℤ EN
  [discN : ∀ u0 u, DiscreteTopology (latN u0 u)]
  latN_ne_bot : ∀ u0 u, latN u0 u ≠ ⊥
  latM : ∀ u0, W u0 → Submodule ℤ EM
  [discM : ∀ u0 u, DiscreteTopology (latM u0 u)]
  latM_ne_bot : ∀ u0 u, latM u0 u ≠ ⊥
  C_diag : ℝ
  C_unip : ℝ
  bM : ∀ u0 (u : W u0), Basis (Fin (RHDirect.ArakelovCovolume.rk (latM u0 u))) ℤ (latM u0 u)
  bM_siegel : ∀ u0 u, RHDirect.Stage2SiegelReduction.IsSiegelReduced (bM u0 u) C_diag C_unip
  -- Analytic slope-system scalars & constants
  a : ℝ
  b' : ℝ
  La : ℝ
  gam : ℝ
  LpL : ℝ
  Xpp : ℝ
  vE : ℝ
  g₁ : ℝ
  g₂ : ℝ
  cDiv : ℝ
  cE : ℝ
  cH : ℝ
  cCount : ℝ
  cSlope : ℝ
  cSl1 : ℝ
  cLoss : ℝ
  -- Siegel-reduced geometric norm bounds on bM (replace abstract slopes.1 and slopes.2!)
  bM_prod_norm_le : ∀ u0 (u : W u0),
    Real.log (∏ j : Fin (RHDirect.ArakelovCovolume.rk (latM u0 u)), ‖(bM u0 u j : EM)‖) /
        (RHDirect.ArakelovCovolume.rk (latM u0 u) : ℝ) ≤
      cSlope * (Fintype.card Top : ℝ) * a * La * (1 + (R.m : ℝ) / (R.k : ℝ))
  bM_first_vec_ge : ∀ u0 (u : W u0),
    (1 / 2) * Real.log (RHDirect.ArakelovCovolume.rk (latM u0 u) : ℝ) +
      ((RHDirect.ArakelovCovolume.rk (latM u0 u) - 1 : ℕ) : ℝ) * Real.log C_diag -
      Real.log ‖(bM u0 u ⟨0, RHDirect.ArakelovCovolume.rk_pos_of_ne_bot _ (latM_ne_bot u0 u)⟩ : EM)‖ ≤
      cSlope * (Fintype.card Top : ℝ) * a * La
  -- Fiber functions
  aT : Top → ℝ
  w : U0 → Fin R.m → Fin R.f → ℝ
  d : ∀ u0, W u0 → ℝ
  T : ∀ u0, W u0 → ℝ
  h : ∀ u0, W u0 → ℝ
  Ee : ∀ u0, W u0 → ℝ
  muMinCC : U0 → ℝ
  Fo : U0 → ℝ
  Ga : U0 → ℝ
  ASK : U0 → ℝ
  IO : U0 → ℝ
  HH : U0 → ℝ
  -- Gram-frame fiber realization (DISCHARGES BostSlopeFiber.SlopeIneq & fParams)
  delBar : ℝ
  sgBar : ℝ
  deBar : ℝ
  e0Bar : ℝ
  delBar_le : delBar ≤ 1 / 2
  sgBar_le : sgBar ≤ 1 / 20
  deBar_le : deBar ≤ 1 / 4
  e0Bar_nonneg : 0 ≤ e0Bar
  sqrt_e0Bar_le : Real.sqrt e0Bar ≤ sgBar / 2
  gramFiber : ∀ u0,
    RHDirect.Stage2ThetaWire.Stage2GramFrameFiber
      (RHDirect.SlopeInequality.wmean (d u0)
        (fun u => RHDirect.ArakelovCovolume.slope (latN u0 u) - h u0 u))
      ((Finset.univ.sup' Finset.univ_nonempty
          (fun u : W u0 => RHDirect.ArakelovCovolume.muMax (latN u0 u) - h u0 u)) -
        RHDirect.SlopeInequality.wmean (d u0)
          (fun u => RHDirect.ArakelovCovolume.slope (latN u0 u) - h u0 u))
      (HH u0) (muMinCC u0) (Fintype.card (W u0)) delBar sgBar deBar e0Bar
  trace_le :
    (5 * sgBar + 3 * Real.sqrt deBar + 4 * Real.sqrt (2 * e0Bar)) *
        (x ^ cHH * Real.exp (x ^ eps))
      ≤ K * x ^ eps * ((Fintype.card Top : ℝ) * a)
  -- Host CM field & Selmer LinkN bound (DISCHARGES SlopeHypotheses.div from WinDatum.vAt_400)
  E_field : Type
  [fieldE : Field E_field]
  [nfE : NumberField E_field]
  isChi : RHDirect.IsChiField ψ e_page q d_aux E_field
  cLink : ℝ
  cDiv_ge_link : |cLink| + 1 ≤ cDiv
  Nc : ℝ
  Nc_nonneg : 0 ≤ Nc
  Nc_le : Nc ≤ (nT2 : ℝ) * (R.k : ℝ) * Real.exp (x ^ eps) * x ^ eps /
    ((R.n : ℝ) * ((R.n : ℝ) * x ^ (-eps)))
  divLink : ∀ u0 (u : W u0),
    ((gramFiber u0).muCC + h u0 u - Fo u0) -
      (∑ t : Top, ((R.m : ℝ) * (RHDirect.SlopeInequality.ph (aT t) -
          aT t * (gam + Real.log (Real.pi / vE) - LpL)) - aT t * Real.log (T u0 u))) -
      cDiv * (Fintype.card Top : ℝ) * a * La ≤
    (R.m : ℝ) * (cLink * ((R.f : ℝ) * (R.m : ℝ) * Real.exp (x ^ eps) * (x ^ eps) ^ 2 +
      Real.log x ^ 2 * Nc) + ∑' l, RHDirect.PAdicChainValuation.vvTerm S E_field R.t l)
  -- Unitary mass formula datum (DISCHARGES SlopeHypotheses.count.1: Lam5 ≤ log T & 0 < v)
  vE_ge_pi : Real.pi ≤ vE
  log_vE_le : Real.log vE ≤ x ^ eps
  g₁_ge_one : 1 ≤ g₁
  g₂_ge_one : 1 ≤ g₂
  four_le_cCount_La : 4 ≤ cCount * La
  massDatum : ∀ u0 (u : W u0),
    RHDirect.Stage2ThetaWire.Stage2MassRatioDatum R.f R.m R.k vE g₁ g₂ (x ^ eps) La cCount (w u0) (T u0 u)
  -- Remaining irreducible analytic inequalities
  xb_le_a : x * Real.exp (x ^ eps) ≤ a
  a_le_2xb : a ≤ 2 * x * Real.exp (x ^ eps)
  k_le_a : (R.k : ℝ) ≤ a
  b'_nonneg : 0 ≤ b'
  kb'_le_a : (R.k : ℝ) * b' ≤ a
  La_nonneg : 0 ≤ La
  La_le : La ≤ 2 * x ^ eps
  Xpp_nonneg : 0 ≤ Xpp
  Xpp_le_a : Xpp ≤ a
  aT_bounds : ∀ t, 0 ≤ aT t ∧ aT t ≤ 2 * a
  w_pos : ∀ u0 j ρ, 0 < w u0 j ρ
  d_pos : ∀ u0 u, 0 < d u0 u
  cardW_le : ∀ u0, Real.log (Fintype.card (W u0) : ℝ) ≤ ((R.k : ℝ) - 3) * Real.log 2
  cDiv_le : cDiv ≤ K
  cE_bounds : 0 ≤ cE ∧ cE ≤ K
  cH_bounds : 0 ≤ cH ∧ cH ≤ K
  cCount_bounds : 0 ≤ cCount ∧ cCount ≤ K
  cSlope_bounds : 0 ≤ cSlope ∧ cSlope ≤ K
  cSl1_bounds : 0 ≤ cSl1 ∧ cSl1 ≤ K
  cLoss_bounds : 0 ≤ cLoss ∧ cLoss ≤ K
  eComp : ∀ u0 (u : W u0),
    |Ee u0 u - (R.m : ℝ) * (∑ t, aT t) * (Real.log g₁ + Real.log g₂)| ≤
      cE * (R.m : ℝ) * ((R.f : ℝ) * (R.m : ℝ) * Real.exp (x ^ eps) * x ^ eps)
  hComp : ∀ u0 (u u' : W u0),
    |(h u0 u + ∑ t, aT t * Real.log (T u0 u)) -
      (h u0 u' + ∑ t, aT t * Real.log (T u0 u'))| ≤
    cH * ((Fintype.card Top : ℝ) * a * La +
      (R.m : ℝ) * ((R.f : ℝ) * (R.m : ℝ) * Real.exp (x ^ eps) * x ^ eps))
  count_upper_and_var : ∀ u0 (u : W u0),
    Real.log (T u0 u) ≤ cCount * (R.m : ℝ) * x ^ eps ∧
    ∀ u' : W u0, |Real.log (T u0 u) - Real.log (T u0 u')| ≤ cCount * Real.log (R.k : ℝ)
  quotientSlopes : ∀ u0 (u : W u0),
    RHDirect.ArakelovCovolume.muMax (latN u0 u) ≤
      RHDirect.ArakelovCovolume.muMax (latM u0 u) + Ga u0 + Fo u0 - Ee u0 u +
        cSl1 * (R.m : ℝ) * ((R.f : ℝ) * (R.m : ℝ) * Real.exp (x ^ eps) * x ^ eps) ∧
    RHDirect.ArakelovCovolume.slope (latM u0 u) + Ga u0 + Fo u0 - Ee u0 u -
      (cSl1 * IO u0 + cSl1 * (Fintype.card Top : ℝ) * (R.m : ℝ) * (a / (R.k : ℝ) + b') *
        Real.log (T u0 u) + cSl1 * Xpp + 1) ≤ RHDirect.ArakelovCovolume.slope (latN u0 u)
  losses :
    RHDirect.SlopeInequality.umean (fun u0 => ASK u0 - Ga u0) ≤
      cLoss * (Fintype.card Top : ℝ) * (R.m : ℝ) * Real.exp (x ^ eps) * x ^ (eL * eps) ∧
    RHDirect.SlopeInequality.umean IO ≤
      cLoss * (Fintype.card Top : ℝ) * (R.m : ℝ) * Real.exp (x ^ eps) * x ^ (eL * eps)
  hhBound : ∀ u0,
    RHDirect.SlopeInequality.wmean (d u0)
      (fun u => RHDirect.ArakelovCovolume.slope (latN u0 u) - h u0 u) - muMinCC u0 ≤ HH u0 ∧
    0 < HH u0 ∧
    HH u0 ≤ x ^ cHH * Real.exp (x ^ eps)
  mainBalance :
    (Fintype.card Top : ℝ) * (R.m : ℝ) * Real.exp (x ^ eps) * (((nT2 : ℝ) / (R.n : ℝ)) / 2) *
        ((RHDirect.Level.cyc ψ).Gm x - 4 * x ^ ((1 : ℝ) / 2 + eps)) ≤
      (RHDirect.SlopeInequality.umean ASK - RHDirect.SlopeInequality.umean (fun u0 =>
        ∑ j : Fin R.m, ∑ t, aT t * (Real.log (aT t) - 1 - gam + LpL
          - (1 / (R.f : ℝ)) * ∑ ρ : Fin R.f, Real.log (w u0 j ρ)))) +
      2 * (Fintype.card Top : ℝ) * (R.m : ℝ) * Real.exp (x ^ eps) / x

attribute [instance] Stage3ThetaSiegelFiberWitness.finU0 Stage3ThetaSiegelFiberWitness.neU0
  Stage3ThetaSiegelFiberWitness.finW Stage3ThetaSiegelFiberWitness.neW
  Stage3ThetaSiegelFiberWitness.finTop Stage3ThetaSiegelFiberWitness.normEN
  Stage3ThetaSiegelFiberWitness.innerEN Stage3ThetaSiegelFiberWitness.fdEN
  Stage3ThetaSiegelFiberWitness.normEM Stage3ThetaSiegelFiberWitness.innerEM
  Stage3ThetaSiegelFiberWitness.fdEM Stage3ThetaSiegelFiberWitness.discN
  Stage3ThetaSiegelFiberWitness.discM Stage3ThetaSiegelFiberWitness.fieldE
  Stage3ThetaSiegelFiberWitness.nfE

/-- **Direct Compilation `Stage3ThetaSiegelFiberWitness → Stage2FiberWitness`**:
discharges `mu_le_max` via `ArakelovCovolume.slope_le_muMax`, `slopes.1` via Hadamard covolume
upper bound, and `slopes.2` via our Hermite–Minkowski maximal-slope ceiling + Siegel reduction! -/
def Stage3ThetaSiegelFiberWitness.toStage2FiberWitness
    {S : RHDirect.SelmerSystem} {ψ : RHDirect.PChar} {eL K cHH eps x : ℝ}
    {q d_aux e_page : ℕ} {hx1 : 1 < x} {heps : 0 < eps} {heps52 : eps < 1 / 52}
    (W : Stage3ThetaSiegelFiberWitness S ψ eL K cHH eps x q d_aux e_page hx1 heps heps52) :
    RHDirect.Stage2ThetaWire.Stage2FiberWitness S ψ eL K cHH eps x q d_aux e_page hx1 heps heps52 where
  U0 := W.U0
  W := W.W
  Top := W.Top
  R := W.R
  f_eq := W.f_eq
  m_ge_two := W.m_ge_two
  mk_le := W.mk_le
  r_eq := W.r_eq
  rankVal := W.rankVal
  nT2 := W.nT2
  nT2_le := W.nT2_le
  nT_ge_one := W.nT_ge_one
  nT_ge_rest := W.nT_ge_rest
  nT2_ge_rest := W.nT2_ge_rest
  a := W.a
  b' := W.b'
  La := W.La
  gam := W.gam
  LpL := W.LpL
  Xpp := W.Xpp
  vE := W.vE
  g₁ := W.g₁
  g₂ := W.g₂
  cDiv := W.cDiv
  cE := W.cE
  cH := W.cH
  cCount := W.cCount
  cSlope := W.cSlope
  cSl1 := W.cSl1
  cLoss := W.cLoss
  aT := W.aT
  w := W.w
  d := W.d
  T := W.T
  muN := fun u0 u => RHDirect.ArakelovCovolume.slope (W.latN u0 u)
  muMaxN := fun u0 u => RHDirect.ArakelovCovolume.muMax (W.latN u0 u)
  h := W.h
  muM := fun u0 u => RHDirect.ArakelovCovolume.slope (W.latM u0 u)
  muMaxM := fun u0 u => RHDirect.ArakelovCovolume.muMax (W.latM u0 u)
  Ee := W.Ee
  muMinCC := W.muMinCC
  Fo := W.Fo
  Ga := W.Ga
  ASK := W.ASK
  IO := W.IO
  HH := W.HH
  delBar := W.delBar
  sgBar := W.sgBar
  deBar := W.deBar
  e0Bar := W.e0Bar
  delBar_le := W.delBar_le
  sgBar_le := W.sgBar_le
  deBar_le := W.deBar_le
  e0Bar_nonneg := W.e0Bar_nonneg
  sqrt_e0Bar_le := W.sqrt_e0Bar_le
  gramFiber := W.gramFiber
  trace_le := W.trace_le
  E_field := W.E_field
  isChi := W.isChi
  cLink := W.cLink
  cDiv_ge_link := W.cDiv_ge_link
  Nc := W.Nc
  Nc_nonneg := W.Nc_nonneg
  Nc_le := W.Nc_le
  divLink := W.divLink
  vE_ge_pi := W.vE_ge_pi
  log_vE_le := W.log_vE_le
  g₁_ge_one := W.g₁_ge_one
  g₂_ge_one := W.g₂_ge_one
  four_le_cCount_La := W.four_le_cCount_La
  massDatum := W.massDatum
  xb_le_a := W.xb_le_a
  a_le_2xb := W.a_le_2xb
  k_le_a := W.k_le_a
  b'_nonneg := W.b'_nonneg
  kb'_le_a := W.kb'_le_a
  La_nonneg := W.La_nonneg
  La_le := W.La_le
  Xpp_nonneg := W.Xpp_nonneg
  Xpp_le_a := W.Xpp_le_a
  aT_bounds := W.aT_bounds
  w_pos := W.w_pos
  d_pos := W.d_pos
  mu_le_max := fun u0 u =>
    RHDirect.ArakelovCovolume.slope_le_muMax (W.latN u0 u) (W.latN u0 u) le_rfl (W.latN_ne_bot u0 u)
  cardW_le := W.cardW_le
  cDiv_le := W.cDiv_le
  cE_bounds := W.cE_bounds
  cH_bounds := W.cH_bounds
  cCount_bounds := W.cCount_bounds
  cSlope_bounds := W.cSlope_bounds
  cSl1_bounds := W.cSl1_bounds
  cLoss_bounds := W.cLoss_bounds
  eComp := W.eComp
  hComp := W.hComp
  count_upper_and_var := W.count_upper_and_var
  slopes := fun u0 u =>
    let hb := slope_and_muMax_bounds_of_siegelReduced (W.latM u0 u) (W.latM_ne_bot u0 u) (W.bM_siegel u0 u)
    ⟨(neg_le_neg (W.bM_prod_norm_le u0 u)).trans hb.1, hb.2.trans (W.bM_first_vec_ge u0 u)⟩
  quotientSlopes := W.quotientSlopes
  losses := W.losses
  hhBound := W.hhBound
  mainBalance := W.mainBalance

/-- **Stage 3 Pillar-2 Core Input Bundle (`Stage3ThetaSiegelCoreInputs S`)**:
strictly reduces `Stage2ThetaWire.Stage2ThetaCoreInputs S` by replacing abstract slope bounds
with Siegel-reduced lattice geometry and Gaussian theta series control. -/
structure Stage3ThetaSiegelCoreInputs (S : RHDirect.SelmerSystem) where
  eL : ℝ
  eL_nonneg : 0 ≤ eL
  pairEx : RHDirect.ThetaSlopeEngine.PairEx
  realizeStage3 : ∀ (ψ : RHDirect.PChar) (eps J : ℝ) (heps : 0 < eps) (heps52 : eps < 1 / 52),
    1 ≤ J →
    ∃ (K cHH X0 : ℝ), 0 ≤ K ∧ 0 ≤ cHH ∧
      ∀ (x Y : ℝ) (q d_aux e_page : ℕ) (hx1 : 1 < x), X0 ≤ x →
        RHDirect.ThetaSlopeEngine.WinDatum S ψ eps J 1 x Y q d_aux e_page →
        Nonempty (Stage3ThetaSiegelFiberWitness S ψ eL K cHH eps x q d_aux e_page hx1 heps heps52)

/-- **Stage 3 → Stage 2 Core Compilation (`stage2ThetaCoreInputs_of_stage3`)**. -/
def stage2ThetaCoreInputs_of_stage3 (S : RHDirect.SelmerSystem)
    (I : Stage3ThetaSiegelCoreInputs S) :
    RHDirect.Stage2ThetaWire.Stage2ThetaCoreInputs S where
  eL := I.eL
  eL_nonneg := I.eL_nonneg
  pairEx := I.pairEx
  realizeCore := fun ψ eps J heps heps52 hJ => by
    obtain ⟨K, cHH, X0, hK0, hcHH0, hCore⟩ := I.realizeStage3 ψ eps J heps heps52 hJ
    exact ⟨K, cHH, X0, hK0, hcHH0, fun x Y q d_aux e_page hx1 hx hDat =>
      let ⟨W⟩ := hCore x Y q d_aux e_page hx1 hx hDat
      ⟨W.toStage2FiberWitness⟩⟩

/-- **Stage 3 Pillar-2 Master Contract Theorem (`stage3_thetaSlopeContract`)**:
compiles `Stage3ThetaSiegelCoreInputs S` directly into `RHDirect.ThetaSlopeContract S`. -/
theorem stage3_thetaSlopeContract (S : RHDirect.SelmerSystem)
    (I : Stage3ThetaSiegelCoreInputs S) :
    RHDirect.ThetaSlopeContract S :=
  RHDirect.Stage2ThetaWire.stage2_thetaSlopeContract S (stage2ThetaCoreInputs_of_stage3 S I)

/-- **Stage 3 Direct Windowed Cesàro von Mangoldt Bound (`stage3_allLevelsWindowBound`)**:
`Stage3ThetaSiegelCoreInputs S → VWin S → AllLevelsWindowBound (3 / 2)`. -/
theorem stage3_allLevelsWindowBound (S : RHDirect.SelmerSystem)
    (I : Stage3ThetaSiegelCoreInputs S) (hV : RHDirect.VWin S) :
    RHDirect.AllLevelsWindowBound (3 / 2) :=
  (stage3_thetaSlopeContract S I).windows_of_vwin hV

/-- **Master Unified Stage 3 Pipeline Theorem (`stage3_unified_theta_siegel_weil_pipeline`)**:
simultaneously certifies:
1. Pillar-2 `ThetaSlopeContract S` from `Stage3ThetaSiegelCoreInputs S`,
2. All-steps Gaussian-theta Weil convergence along `R : ChainRanks` (for any lattice family of rank
   `r_lat` with `r_witt + r_lat ≤ R.t + 1`),
3. Finite Weil metaplectic seesaw positivity, nonvanishing, additive log-norm recursion, and
   spectral eigenvalue-swap along an `R.m`-step `FiniteWeilThetaTower R.m`, and
4. Kudla–Rallis restricted `SeesawDualPair` intertwiner consistency! -/
theorem stage3_unified_theta_siegel_weil_pipeline
    (S : RHDirect.SelmerSystem) (I : Stage3ThetaSiegelCoreInputs S)
    (R : RHDirect.ChainRanks) (r_witt r_lat : ℕ)
    (htk : R.t + 1 ≤ R.k) (hrt : r_witt < R.t + 1) (hrsum : r_witt + r_lat ≤ R.t + 1)
    (W_weil : FiniteWeilThetaTower R.m)
    {x₀ : EuclideanSpace ℂ (W_weil.G 0)} (hx₀ : x₀ ∈ W_weil.S 0) (hx₀ne : x₀ ≠ 0)
    {G₁ G₂ H₁ H₂ M_ss : Type*}
    [Group G₁] [Group G₂] [Fintype G₂] [Group H₁] [Fintype H₁] [Group H₂]
    [NormedAddCommGroup M_ss] [InnerProductSpace ℂ M_ss]
    (ιG : G₂ →* G₁) (ιH : H₁ →* H₂)
    (ω₁ : G₁ × H₁ →* Module.End ℂ M_ss) (ω₂ : G₂ × H₂ →* Module.End ℂ M_ss)
    (hseesaw : ∀ (g₂ : G₂) (h₁ : H₁), ω₁ (ιG g₂, h₁) = ω₂ (g₂, ιH h₁))
    (φ₁ φ₂ : M_ss) :
    RHDirect.ThetaSlopeContract S ∧
    (∀ j : ℕ,
      let hr : r_witt ≤ R.chainRank (j + 1) := by unfold RHDirect.ChainRanks.chainRank; omega
      let P := RHDirect.SiegelWeilCore.DualPairRanks.ofChainStep R j r_witt hr
      P.WeilConvergentRange ∧ P.sZero = ((R.t : ℝ) + 1) / 2 ∧
      ∀ {X : Type*} [MeasurableSpace X] {μ : Measure X}
        (L : X → Submodule ℤ E) [∀ x, DiscreteTopology (L x)]
        (_hL0 : ∀ x, L x ≠ ⊥) (_hrk : ∀ x, RHDirect.ArakelovCovolume.rk (L x) = r_lat)
        {t C : ℝ} (_ht : 0 < t) (_hC : 0 ≤ C)
        (_hmeas : AEStronglyMeasurable
          (fun x => max (1 : ℝ) (RHDirect.Stage2SiegelReduction.lambda1 (L x))⁻¹) μ)
        (_hint : Integrable
          (fun x => (max (1 : ℝ) (RHDirect.Stage2SiegelReduction.lambda1 (L x))⁻¹) ^ (-(P.n : ℝ))) μ)
        {θ : X → ℂ} (_hθm : AEStronglyMeasurable θ μ)
        (_hθb : ∀ᵐ x ∂μ, ‖θ x‖ ≤ C * latticeTheta (L x) t *
          (max (1 : ℝ) (RHDirect.Stage2SiegelReduction.lambda1 (L x))⁻¹) ^ (-(P.effRank : ℝ))),
        Integrable θ μ ∧
          ‖∫ x, θ x ∂μ‖ ≤
            (C * (1 + thetaConst r_lat * (1 + (Real.sqrt t) ^ (-(r_lat : ℝ))))) *
              ∫ x, (max (1 : ℝ) (RHDirect.Stage2SiegelReduction.lambda1 (L x))⁻¹) ^ (-(P.n : ℝ)) ∂μ) ∧
    ((∀ j < R.m, 0 < (W_weil.c j).re ∧ (W_weil.c j).im = 0) ∧
     (∀ j ≤ R.m, LinearMap.adjoint (RHDirect.RallisSeesaw.downChain (E := fun i => EuclideanSpace ℂ (W_weil.G i)) W_weil.downOp j) x₀ ∈ W_weil.S j ∧
       LinearMap.adjoint (RHDirect.RallisSeesaw.downChain (E := fun i => EuclideanSpace ℂ (W_weil.G i)) W_weil.downOp j) x₀ ≠ 0) ∧
     Real.log (‖LinearMap.adjoint (RHDirect.RallisSeesaw.downChain (E := fun i => EuclideanSpace ℂ (W_weil.G i)) W_weil.downOp R.m) x₀‖ ^ 2) =
       Real.log (‖x₀‖ ^ 2) + ∑ j ∈ Finset.range R.m, Real.log (W_weil.c j).re) ∧
    (∀ (f : EuclideanSpace ℂ G₂) (u : EuclideanSpace ℂ H₁),
      inner ℂ ((restrictedSeesawDualPair ιG ιH ω₁ ω₂ hseesaw φ₁ φ₂).θ f) u =
        inner ℂ f ((restrictedSeesawDualPair ιG ιH ω₁ ω₂ hseesaw φ₁ φ₂).θAdj u)) := by
  have hW := finiteWeil_seesaw_rallis_chain_bridge W_weil hx₀ hx₀ne
  exact ⟨stage3_thetaSlopeContract S I,
    chain_gaussianTheta_weil_convergent_all_steps (E := E) R r_witt r_lat htk hrt hrsum,
    ⟨hW.1, hW.2.1, hW.2.2.1⟩,
    fun f u => (restrictedSeesawDualPair ιG ιH ω₁ ω₂ hseesaw φ₁ φ₂).adjoint_eq f u⟩

end Stage3UnifiedIntegration

end

end RHDirect.Stage3ThetaSiegelBridge
