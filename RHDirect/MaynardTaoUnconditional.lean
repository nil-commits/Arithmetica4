/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Maynard–Tao Unconditional Bounded Gaps Between Primes (`H ≤ 600` & Arbitrary `m`-Tuples)

This file unconditionally discharges `MaynardTaoReduction.AnalyticCore mtTuple105` and
`MaynardTaoReduction.MAnalyticCore` for arbitrarily large `m`, establishing:
1. **`maynard_tao_bounded_gaps_unconditional`**:
   `∀ N : ℕ, ∃ p q : ℕ, N ≤ p ∧ Nat.Prime p ∧ Nat.Prime q ∧ p < q ∧ q - p ≤ 600`
2. **`maynard_tao_m_tuples_unconditional`**:
   `∀ m ≥ 1, ∃ H : ℕ, ∀ N : ℕ, ∃ S : Finset ℕ, S.card = m ∧ (∀ p ∈ S, N ≤ p ∧ Nat.Prime p) ∧ ∀ p ∈ S, ∀ q ∈ S, p ≤ q + H`

Zero `sorry`, zero custom axioms, zero `native_decide`, zero `import Mathlib`.
-/
import RHDirect.MaynardTaoSieve
import RHDirect.MaynardTaoTuples
import RHDirect.MaynardTaoWTrick
import RHDirect.MaynardTaoReduction
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000
set_option linter.style.haveILetI false

noncomputable section

open Finset Filter Topology MeasureTheory intervalIntegral

namespace RHDirect.MaynardTao

/-! ## Section 1: Exact Simplex Integrals for Symmetric Polynomials -/

/-- Rising-product helper `prodFrom lo len = lo * (lo + 1) * ... * (lo + len - 1)`. -/
def prodFrom : ℕ → ℕ → ℕ
  | _, 0 => 1
  | lo, len + 1 => lo * prodFrom (lo + 1) len

lemma prodFrom_mul_factorial (n m : ℕ) (h : n ≤ m) :
    n.factorial * prodFrom (n + 1) (m - n) = m.factorial := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  clear h
  rw [Nat.add_sub_cancel_left]
  induction d generalizing n with
  | zero => simp [prodFrom]
  | succ d ih =>
    unfold prodFrom
    have h1 : n.factorial * ((n + 1) * prodFrom (n + 1 + 1) d) =
        (n + 1).factorial * prodFrom ((n + 1) + 1) d := by
      rw [Nat.factorial_succ]; ring
    rw [h1, ih (n + 1)]
    congr 1; omega

/-- Computable recursion `polyP k b` giving the exact numerator of
`∫_{Δ_k(s)} (s - ∑ v_i)^a * (∑ v_i^2)^b dv = (a! * polyP k b / (k + a + 2b)!) * s^(k + a + 2b)`. -/
def polyP : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | k + 1, b => ∑ c ∈ Finset.range (b + 1), b.choose c * (2 * c).factorial * polyP k (b - c)

/-- Helper: `IsSimplexLipOn` closure under addition. -/
private lemma IsSimplexLipOn.add {k : ℕ} {s M₁ L₁ M₂ L₂ : ℝ} {G₁ G₂ : (Fin k → ℝ) → ℝ}
    (h1 : IsSimplexLipOn s M₁ L₁ G₁) (h2 : IsSimplexLipOn s M₂ L₂ G₂) :
    IsSimplexLipOn s (M₁ + M₂) (L₁ + L₂) (fun v => G₁ v + G₂ v) := by
  refine ⟨add_nonneg h1.1 h2.1, add_nonneg h1.2.1 h2.2.1, fun v hv => ?_, fun u v hu hv => ?_⟩
  · exact (abs_add_le _ _).trans (add_le_add (h1.2.2.1 v hv) (h2.2.2.1 v hv))
  · have hrew : (G₁ u + G₂ u) - (G₁ v + G₂ v) = (G₁ u - G₁ v) + (G₂ u - G₂ v) := by ring
    rw [hrew]
    calc |(G₁ u - G₁ v) + (G₂ u - G₂ v)|
        ≤ |G₁ u - G₁ v| + |G₂ u - G₂ v| := abs_add_le _ _
      _ ≤ L₁ * ∑ i, |u i - v i| + L₂ * ∑ i, |u i - v i| :=
          add_le_add (h1.2.2.2 u v hu hv) (h2.2.2.2 u v hu hv)
      _ = (L₁ + L₂) * ∑ i, |u i - v i| := by ring

/-- Helper: `IsSimplexLipOn` closure under scalar multiplication. -/
private lemma IsSimplexLipOn.const_mul {k : ℕ} {s M L : ℝ} {G : (Fin k → ℝ) → ℝ}
    (c : ℝ) (h : IsSimplexLipOn s M L G) :
    IsSimplexLipOn s (|c| * M) (|c| * L) (fun v => c * G v) := by
  refine ⟨mul_nonneg (abs_nonneg c) h.1, mul_nonneg (abs_nonneg c) h.2.1, fun v hv => ?_, fun u v hu hv => ?_⟩
  · rw [abs_mul]; exact mul_le_mul_of_nonneg_left (h.2.2.1 v hv) (abs_nonneg c)
  · rw [← mul_sub, abs_mul]
    calc |c| * |G u - G v| ≤ |c| * (L * ∑ i, |u i - v i|) :=
          mul_le_mul_of_nonneg_left (h.2.2.2 u v hu hv) (abs_nonneg c)
      _ = (|c| * L) * ∑ i, |u i - v i| := by ring

/-- Helper: `IsSimplexLipOn` closure under finite sums. -/
private lemma IsSimplexLipOn.finset_sum {k : ℕ} {ι : Type*} (S : Finset ι) {s : ℝ}
    {M L : ι → ℝ} {G : ι → (Fin k → ℝ) → ℝ}
    (h : ∀ j ∈ S, IsSimplexLipOn s (M j) (L j) (G j)) :
    IsSimplexLipOn s (∑ j ∈ S, M j) (∑ j ∈ S, L j) (fun v => ∑ j ∈ S, G j v) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨by simp, by simp, fun _ _ => by simp, fun _ _ _ _ => by simp⟩
  | insert a S ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have hsum : (fun v => ∑ j ∈ insert a S, G j v) = (fun v => G a v + ∑ j ∈ S, G j v) := by
      funext v; exact Finset.sum_insert ha
    rw [hsum]
    exact (h a (Finset.mem_insert_self a S)).add
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

/-- Helper: `IsSimplexLipOn` closure under products. -/
private lemma IsSimplexLipOn.mul {k : ℕ} {s M₁ L₁ M₂ L₂ : ℝ} {G₁ G₂ : (Fin k → ℝ) → ℝ}
    (h1 : IsSimplexLipOn s M₁ L₁ G₁) (h2 : IsSimplexLipOn s M₂ L₂ G₂) :
    IsSimplexLipOn s (M₁ * M₂) (L₁ * M₂ + M₁ * L₂) (fun v => G₁ v * G₂ v) := by
  refine ⟨mul_nonneg h1.1 h2.1, add_nonneg (mul_nonneg h1.2.1 h2.1) (mul_nonneg h1.1 h2.2.1),
    fun v hv => ?_, fun u v hu hv => ?_⟩
  · rw [abs_mul]; exact mul_le_mul (h1.2.2.1 v hv) (h2.2.2.1 v hv) (abs_nonneg _) h1.1
  · have hrew : G₁ u * G₂ u - G₁ v * G₂ v = (G₁ u - G₁ v) * G₂ u + G₁ v * (G₂ u - G₂ v) := by ring
    rw [hrew]
    calc |(G₁ u - G₁ v) * G₂ u + G₁ v * (G₂ u - G₂ v)|
        ≤ |(G₁ u - G₁ v) * G₂ u| + |G₁ v * (G₂ u - G₂ v)| := abs_add_le _ _
      _ = |G₁ u - G₁ v| * |G₂ u| + |G₁ v| * |G₂ u - G₂ v| := by rw [abs_mul, abs_mul]
      _ ≤ (L₁ * ∑ i, |u i - v i|) * M₂ + M₁ * (L₂ * ∑ i, |u i - v i|) :=
          add_le_add (mul_le_mul (h1.2.2.2 u v hu hv) (h2.2.2.1 u hu) (abs_nonneg _) (mul_nonneg h1.2.1 (Finset.sum_nonneg fun _ _ => abs_nonneg _)))
            (mul_le_mul (h1.2.2.1 v hv) (h2.2.2.2 u v hu hv) (abs_nonneg _) h1.1)
      _ = (L₁ * M₂ + M₁ * L₂) * ∑ i, |u i - v i| := by ring

/-- Helper: `|x^n - y^n| ≤ n * |x - y|` for `x, y ∈ [0, 1]`. -/
private lemma abs_pow_sub_pow_le {x y : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) (n : ℕ) :
    |x ^ n - y ^ n| ≤ (n : ℝ) * |x - y| := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hrew : x ^ (n + 1) - y ^ (n + 1) = (x - y) * x ^ n + y * (x ^ n - y ^ n) := by ring
    rw [hrew]
    have hxn : |x ^ n| ≤ 1 := by rw [abs_of_nonneg (pow_nonneg hx0 n)]; exact pow_le_one₀ hx0 hx1
    have hy_le : |y| ≤ 1 := by rw [abs_of_nonneg hy0]; exact hy1
    calc |(x - y) * x ^ n + y * (x ^ n - y ^ n)|
        ≤ |x - y| * |x ^ n| + |y| * |x ^ n - y ^ n| := by
          rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
      _ ≤ |x - y| * 1 + 1 * ((n : ℝ) * |x - y|) :=
          add_le_add (mul_le_mul_of_nonneg_left hxn (abs_nonneg _))
            (mul_le_mul hy_le ih (abs_nonneg _) zero_le_one)
      _ = ((n + 1 : ℕ) : ℝ) * |x - y| := by push_cast; ring

/-- Every basis monomial `(s - ∑ v_i)^a * (∑ v_i^2)^b` is `(1, a + 2*b)`-Lipschitz on `Δ_k(s)` for `0 ≤ s ≤ 1`. -/
private lemma isSimplexLipOn_basis (k a b : ℕ) {s : ℝ} (_hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    IsSimplexLipOn s 1 ((a : ℝ) + 2 * (b : ℝ))
      (fun v : Fin k → ℝ => (s - ∑ i, v i) ^ a * (∑ i, (v i) ^ 2) ^ b) := by
  have h1 : IsSimplexLipOn s 1 (a : ℝ) (fun v : Fin k → ℝ => (s - ∑ i, v i) ^ a) := by
    refine ⟨zero_le_one, Nat.cast_nonneg a, fun v hv => ?_, fun u v hu hv => ?_⟩
    · have h0 : 0 ≤ s - ∑ i, v i := by linarith [hv.2]
      have hle : s - ∑ i, v i ≤ 1 := by linarith [Finset.sum_nonneg (s := Finset.univ) fun i _ => hv.1 i]
      rw [abs_of_nonneg (pow_nonneg h0 a)]; exact pow_le_one₀ h0 hle
    · have hu0 : 0 ≤ s - ∑ i, u i := by linarith [hu.2]
      have hu1 : s - ∑ i, u i ≤ 1 := by linarith [Finset.sum_nonneg (s := Finset.univ) fun i _ => hu.1 i]
      have hv0 : 0 ≤ s - ∑ i, v i := by linarith [hv.2]
      have hv1 : s - ∑ i, v i ≤ 1 := by linarith [Finset.sum_nonneg (s := Finset.univ) fun i _ => hv.1 i]
      calc |(s - ∑ i, u i) ^ a - (s - ∑ i, v i) ^ a|
          ≤ (a : ℝ) * |(s - ∑ i, u i) - (s - ∑ i, v i)| := abs_pow_sub_pow_le hu0 hu1 hv0 hv1 a
        _ = (a : ℝ) * |∑ i, (v i - u i)| := by congr 1; rw [Finset.sum_sub_distrib]; congr 1; ring
        _ ≤ (a : ℝ) * ∑ i, |v i - u i| := mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (Nat.cast_nonneg a)
        _ = (a : ℝ) * ∑ i, |u i - v i| := by congr 1; exact Finset.sum_congr rfl fun i _ => abs_sub_comm _ _
  have h2 : IsSimplexLipOn s 1 (2 * (b : ℝ)) (fun v : Fin k → ℝ => (∑ i, (v i) ^ 2) ^ b) := by
    have hsq_le : ∀ v : Fin k → ℝ, InSimplex s v → 0 ≤ ∑ i, (v i) ^ 2 ∧ ∑ i, (v i) ^ 2 ≤ 1 := by
      intro v hv
      refine ⟨Finset.sum_nonneg fun i _ => sq_nonneg _, ?_⟩
      calc ∑ i, (v i) ^ 2 ≤ ∑ i, v i := by
            refine Finset.sum_le_sum fun i _ => ?_
            have hi0 : 0 ≤ v i := hv.1 i
            have hi1 : v i ≤ 1 := le_trans (Finset.single_le_sum (fun j _ => hv.1 j) (Finset.mem_univ i)) (hv.2.trans hs1)
            nlinarith
        _ ≤ 1 := hv.2.trans hs1
    refine ⟨zero_le_one, by positivity, fun v hv => ?_, fun u v hu hv => ?_⟩
    · rw [abs_of_nonneg (pow_nonneg (hsq_le v hv).1 b)]
      exact pow_le_one₀ (hsq_le v hv).1 (hsq_le v hv).2
    · calc |(∑ i, (u i) ^ 2) ^ b - (∑ i, (v i) ^ 2) ^ b|
          ≤ (b : ℝ) * |(∑ i, (u i) ^ 2) - (∑ i, (v i) ^ 2)| :=
            abs_pow_sub_pow_le (hsq_le u hu).1 (hsq_le u hu).2 (hsq_le v hv).1 (hsq_le v hv).2 b
        _ = (b : ℝ) * |∑ i, ((u i) ^ 2 - (v i) ^ 2)| := by rw [Finset.sum_sub_distrib]
        _ ≤ (b : ℝ) * ∑ i, |(u i) ^ 2 - (v i) ^ 2| :=
            mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (Nat.cast_nonneg b)
        _ ≤ (b : ℝ) * ∑ i, (2 * |u i - v i|) := by
            refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => ?_) (Nat.cast_nonneg b)
            have hui : u i ≤ 1 := le_trans (Finset.single_le_sum (fun j _ => hu.1 j) (Finset.mem_univ i)) (hu.2.trans hs1)
            have hvi : v i ≤ 1 := le_trans (Finset.single_le_sum (fun j _ => hv.1 j) (Finset.mem_univ i)) (hv.2.trans hs1)
            have hrew : (u i) ^ 2 - (v i) ^ 2 = (u i + v i) * (u i - v i) := by ring
            rw [hrew, abs_mul, abs_of_nonneg (add_nonneg (hu.1 i) (hv.1 i))]
            exact mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
        _ = (2 * (b : ℝ)) * ∑ i, |u i - v i| := by rw [← Finset.mul_sum]; ring
  simpa only [one_mul, mul_one] using h1.mul h2

/-- Helper: `simplexIntegral_slice` is `IntervalIntegrable` on `0..s` for any `IsSimplexLipOn` function. -/
private lemma intervalIntegrable_simplex_slice {k : ℕ} {s M L : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    {G : (Fin (k + 1) → ℝ) → ℝ} (hG : IsSimplexLipOn s M L G) :
    IntervalIntegrable (fun t : ℝ => simplexIntegral k (s - t) (fun v => G (Fin.cons t v)))
      MeasureTheory.volume 0 s := by
  have hcont : ContinuousOn (fun t : ℝ => simplexIntegral k (s - t) (fun v => G (Fin.cons t v))) (Set.uIcc 0 s) := by
    rw [Set.uIcc_of_le hs0]
    refine Metric.continuousOn_iff.mpr fun t ht ε hε => ?_
    refine ⟨ε / (L + (k : ℝ) * M + 1), by have := hG.1; have := hG.2.1; positivity, fun t' ht' htt' => ?_⟩
    rw [Real.dist_eq] at htt' ⊢
    have hlip := simplexIntegral_slice_lipschitz hs0 hs1 hG ht' ht
    calc |simplexIntegral k (s - t') (fun v => G (Fin.cons t' v)) -
            simplexIntegral k (s - t) (fun v => G (Fin.cons t v))|
        ≤ (L + (k : ℝ) * M) * |t' - t| := hlip
      _ ≤ (L + (k : ℝ) * M + 1) * |t' - t| := mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
      _ < (L + (k : ℝ) * M + 1) * (ε / (L + (k : ℝ) * M + 1)) :=
          mul_lt_mul_of_pos_left htt' (by have := hG.1; have := hG.2.1; positivity)
      _ = ε := by field_simp [show L + (k : ℝ) * M + 1 ≠ 0 by have := hG.1; have := hG.2.1; positivity]
  exact hcont.intervalIntegrable

/-- Linearity of `simplexIntegral` under addition for `IsSimplexLipOn` functions (`0 ≤ s ≤ 1`). -/
lemma simplexIntegral_add {k : ℕ} {s M₁ L₁ M₂ L₂ : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    {G₁ G₂ : (Fin k → ℝ) → ℝ} (h1 : IsSimplexLipOn s M₁ L₁ G₁) (h2 : IsSimplexLipOn s M₂ L₂ G₂) :
    simplexIntegral k s (fun v => G₁ v + G₂ v) = simplexIntegral k s G₁ + simplexIntegral k s G₂ := by
  induction k generalizing s with
  | zero => simp [simplexIntegral]
  | succ k ih =>
    unfold simplexIntegral
    have hcongr : ∀ t ∈ Set.uIcc (0 : ℝ) s,
        simplexIntegral k (s - t) (fun v => G₁ (Fin.cons t v) + G₂ (Fin.cons t v)) =
        simplexIntegral k (s - t) (fun v => G₁ (Fin.cons t v)) +
          simplexIntegral k (s - t) (fun v => G₂ (Fin.cons t v)) := by
      intro t ht
      rw [Set.uIcc_of_le hs0] at ht
      exact ih (by linarith [ht.2]) (by linarith [ht.1]) (h1.cons ht.1) (h2.cons ht.1)
    rw [intervalIntegral.integral_congr hcongr,
      intervalIntegral.integral_add (intervalIntegrable_simplex_slice hs0 hs1 h1)
        (intervalIntegrable_simplex_slice hs0 hs1 h2)]

/-- Linearity of `simplexIntegral` under scalar multiplication (`0 ≤ s ≤ 1`). -/
lemma simplexIntegral_const_mul {k : ℕ} {s : ℝ} (hs0 : 0 ≤ s) (c : ℝ) (G : (Fin k → ℝ) → ℝ) :
    simplexIntegral k s (fun v => c * G v) = c * simplexIntegral k s G := by
  induction k generalizing s with
  | zero => simp [simplexIntegral]
  | succ k ih =>
    unfold simplexIntegral
    have hcongr : ∀ t ∈ Set.uIcc (0 : ℝ) s,
        simplexIntegral k (s - t) (fun v => c * G (Fin.cons t v)) =
        c * simplexIntegral k (s - t) (fun v => G (Fin.cons t v)) := by
      intro t ht; rw [Set.uIcc_of_le hs0] at ht
      exact ih (by linarith [ht.2]) (fun v => G (Fin.cons t v))
    rw [intervalIntegral.integral_congr hcongr, intervalIntegral.integral_const_mul]

/-- Linearity of `simplexIntegral` under finite sums for `IsSimplexLipOn` functions (`0 ≤ s ≤ 1`). -/
lemma simplexIntegral_finset_sum {k : ℕ} {ι : Type*} (S : Finset ι) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    {M L : ι → ℝ} {G : ι → (Fin k → ℝ) → ℝ}
    (h : ∀ j ∈ S, IsSimplexLipOn s (M j) (L j) (G j)) :
    simplexIntegral k s (fun v => ∑ j ∈ S, G j v) = ∑ j ∈ S, simplexIntegral k s (G j) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    have hzero : ∀ (m : ℕ) (u : ℝ), simplexIntegral m u (fun _ => (0 : ℝ)) = 0 := by
      intro m; induction m with
      | zero => intro u; simp [simplexIntegral]
      | succ m ihm => intro u; unfold simplexIntegral; simp_rw [ihm]; simp
    simpa using hzero k s
  | insert a S ha ih =>
    rw [Finset.sum_insert ha]
    have hsum : (fun v => ∑ j ∈ insert a S, G j v) = (fun v => G a v + ∑ j ∈ S, G j v) := by
      funext v; exact Finset.sum_insert ha
    rw [hsum, simplexIntegral_add hs0 hs1 (h a (Finset.mem_insert_self a S))
      (IsSimplexLipOn.finset_sum S fun j hj => h j (Finset.mem_insert_of_mem hj)),
      ih fun j hj => h j (Finset.mem_insert_of_mem hj)]

/-- Monotonicity of `simplexIntegral` for `IsSimplexLipOn` functions (`0 ≤ s ≤ 1`). -/
lemma simplexIntegral_mono {k : ℕ} {s M₁ L₁ M₂ L₂ : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    {G₁ G₂ : (Fin k → ℝ) → ℝ} (h1 : IsSimplexLipOn s M₁ L₁ G₁) (h2 : IsSimplexLipOn s M₂ L₂ G₂)
    (hle : ∀ v, InSimplex s v → G₁ v ≤ G₂ v) :
    simplexIntegral k s G₁ ≤ simplexIntegral k s G₂ := by
  induction k generalizing s with
  | zero =>
    unfold simplexIntegral; exact hle Fin.elim0 (inSimplex_elim0 hs0)
  | succ k ih =>
    unfold simplexIntegral
    refine intervalIntegral.integral_mono_on hs0
      (intervalIntegrable_simplex_slice hs0 hs1 h1)
      (intervalIntegrable_simplex_slice hs0 hs1 h2) fun t ht => ?_
    exact ih (by linarith [ht.2]) (by linarith [ht.1]) (h1.cons ht.1) (h2.cons ht.1)
      fun v hv => hle (Fin.cons t v) (inSimplex_cons ht.1 hv)

/-- Congruence of `simplexIntegral` on `Δ_k(s)` (`0 ≤ s`). -/
lemma simplexIntegral_congr {k : ℕ} {s : ℝ} (hs0 : 0 ≤ s) {G₁ G₂ : (Fin k → ℝ) → ℝ}
    (heq : ∀ v, InSimplex s v → G₁ v = G₂ v) :
    simplexIntegral k s G₁ = simplexIntegral k s G₂ := by
  induction k generalizing s with
  | zero => unfold simplexIntegral; exact heq Fin.elim0 (inSimplex_elim0 hs0)
  | succ k ih =>
    unfold simplexIntegral
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [Set.uIcc_of_le hs0] at ht
    exact ih (by linarith [ht.2]) fun v hv => heq (Fin.cons t v) (inSimplex_cons ht.1 hv)

/-- Exact 1D Beta integral:
`∫ t in 0..u, (u - t)^a * t^b = (a! * b! / (a + b + 1)!) * u^(a + b + 1)`. -/
lemma integral_sub_pow_mul_pow (u : ℝ) (a b : ℕ) :
    ∫ t in (0 : ℝ)..u, (u - t) ^ a * t ^ b =
      ((a.factorial * b.factorial : ℕ) : ℝ) / (((a + b + 1).factorial : ℕ) : ℝ) * u ^ (a + b + 1) := by
  induction a generalizing b with
  | zero =>
    simp only [pow_zero, one_mul, Nat.factorial_zero, zero_add]
    rw [integral_pow]
    have hfac : (((b + 1).factorial : ℕ) : ℝ) = ((b + 1 : ℕ) : ℝ) * ((b.factorial : ℕ) : ℝ) := by
      rw [Nat.factorial_succ, Nat.cast_mul]
    have hb_ne : ((b.factorial : ℕ) : ℝ) ≠ 0 := by positivity
    have hb1_ne : ((b + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    rw [zero_pow (by omega), sub_zero, hfac]
    push_cast
    field_simp [hb_ne, hb1_ne]
  | succ a ih =>
    have hderiv : ∀ t : ℝ, HasDerivAt
        (fun x : ℝ => (u - x) ^ (a + 1) * x ^ (b + 1) / ((b + 1 : ℕ) : ℝ))
        ((u - t) ^ (a + 1) * t ^ b - ((a + 1 : ℕ) : ℝ) / ((b + 1 : ℕ) : ℝ) * ((u - t) ^ a * t ^ (b + 1))) t := by
      intro t
      have h1 : HasDerivAt (fun x : ℝ => u - x) (-1) t :=
        ((hasDerivAt_const t u).sub (hasDerivAt_id t)).congr_deriv (by ring)
      have h2 : HasDerivAt (fun x : ℝ => (u - x) ^ (a + 1))
          (((a + 1 : ℕ) : ℝ) * (u - t) ^ a * (-1)) t :=
        (h1.pow (a + 1)).congr_deriv (by simp [Nat.cast_add, Nat.cast_one])
      have h3 : HasDerivAt (fun x : ℝ => x ^ (b + 1)) (((b + 1 : ℕ) : ℝ) * t ^ b) t :=
        (hasDerivAt_pow (b + 1) t).congr_deriv (by simp [Nat.cast_add, Nat.cast_one])
      have h4 := (h2.mul h3).div_const ((b + 1 : ℕ) : ℝ)
      have hb1_ne : ((b + 1 : ℕ) : ℝ) ≠ 0 := by positivity
      refine h4.congr_deriv ?_
      field_simp [hb1_ne]
      ring
    have hcont1 : Continuous (fun t : ℝ => (u - t) ^ (a + 1) * t ^ b) := by fun_prop
    have hcont2 : Continuous (fun t : ℝ => ((a + 1 : ℕ) : ℝ) / ((b + 1 : ℕ) : ℝ) * ((u - t) ^ a * t ^ (b + 1))) := by fun_prop
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ => hderiv t) ((hcont1.sub hcont2).intervalIntegrable 0 u)
    rw [intervalIntegral.integral_sub (hcont1.intervalIntegrable 0 u) (hcont2.intervalIntegrable 0 u),
      intervalIntegral.integral_const_mul] at hftc
    simp only [sub_self, zero_pow (Nat.succ_ne_zero _), zero_mul, zero_div, mul_zero, sub_zero] at hftc
    have hibp : ∫ t in (0 : ℝ)..u, (u - t) ^ (a + 1) * t ^ b =
        ((a + 1 : ℕ) : ℝ) / ((b + 1 : ℕ) : ℝ) * ∫ t in (0 : ℝ)..u, (u - t) ^ a * t ^ (b + 1) := by
      linarith
    rw [hibp, ih (b + 1)]
    have h1 : a + 1 + b + 1 = a + (b + 1) + 1 := by omega
    rw [h1]
    have hfa : (((a + 1).factorial : ℕ) : ℝ) = ((a + 1 : ℕ) : ℝ) * ((a.factorial : ℕ) : ℝ) := by
      rw [Nat.factorial_succ, Nat.cast_mul]
    have hfb : (((b + 1).factorial : ℕ) : ℝ) = ((b + 1 : ℕ) : ℝ) * ((b.factorial : ℕ) : ℝ) := by
      rw [Nat.factorial_succ, Nat.cast_mul]
    have hb1_ne : ((b + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    have hden_ne : (((a + (b + 1) + 1).factorial : ℕ) : ℝ) ≠ 0 := by positivity
    push_cast [hfa, hfb]
    field_simp [hb1_ne, hden_ne]

/-- Exact 1D slice integral:
`∫ t in 0..u, (u - t)^a * (Q + t^2)^b = ∑_{j=0}^b (C(b,j) * a! * (2j)! / (a + 2j + 1)!) * u^(a + 2j + 1) * Q^(b - j)`. -/
lemma integral_sub_pow_mul_add_sq_pow (u Q : ℝ) (a b : ℕ) :
    ∫ t in (0 : ℝ)..u, (u - t) ^ a * (Q + t ^ 2) ^ b =
      ∑ j ∈ Finset.range (b + 1),
        (((b.choose j * a.factorial * (2 * j).factorial : ℕ) : ℝ) / (((a + 2 * j + 1).factorial : ℕ) : ℝ)) *
          u ^ (a + 2 * j + 1) * Q ^ (b - j) := by
  have hexp : ∀ t : ℝ, (u - t) ^ a * (Q + t ^ 2) ^ b =
      ∑ j ∈ Finset.range (b + 1), (((b.choose j : ℕ) : ℝ) * Q ^ (b - j)) * ((u - t) ^ a * t ^ (2 * j)) := fun t => by
    rw [add_comm Q (t ^ 2), add_pow (t ^ 2) Q b, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← pow_mul, mul_comm 2 j]; ring
  simp_rw [hexp]
  rw [intervalIntegral.integral_finsetSum fun j _ => (by fun_prop : Continuous (fun t : ℝ =>
    (((b.choose j : ℕ) : ℝ) * Q ^ (b - j)) * ((u - t) ^ a * t ^ (2 * j)))).intervalIntegrable 0 u]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [intervalIntegral.integral_const_mul, integral_sub_pow_mul_pow u a (2 * j)]
  push_cast; ring

/-- **Master Exact Simplex Integral Theorem** for all `k, a, b : ℕ` and `0 ≤ s ≤ 1`:
`simplexIntegral k s (fun v => (s - ∑ i, v i)^a * (∑ i, v i ^ 2)^b) =
  (a! * polyP k b / (k + a + 2b)!) * s^(k + a + 2b)`. -/
theorem simplexIntegral_basis (k a b : ℕ) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    simplexIntegral k s (fun v => (s - ∑ i, v i) ^ a * (∑ i, (v i) ^ 2) ^ b) =
      ((a.factorial * polyP k b : ℕ) : ℝ) / (((k + a + 2 * b).factorial : ℕ) : ℝ) * s ^ (k + a + 2 * b) := by
  induction k generalizing a b s with
  | zero =>
    unfold simplexIntegral
    simp only [Finset.univ_eq_empty, Finset.sum_empty, sub_zero, zero_add]
    cases b with
    | zero =>
      simp only [pow_zero, mul_one, polyP, Nat.mul_zero, add_zero]
      have hne : ((a.factorial : ℕ) : ℝ) ≠ 0 := by positivity
      field_simp [hne]
    | succ b =>
      simp [polyP, zero_pow (Nat.succ_ne_zero b)]
  | succ k ih =>
    unfold simplexIntegral
    have hinner : ∀ t ∈ Set.uIcc (0 : ℝ) s,
        simplexIntegral k (s - t) (fun v => (s - ∑ i : Fin (k + 1), (Fin.cons t v : Fin (k + 1) → ℝ) i) ^ a *
          (∑ i : Fin (k + 1), (Fin.cons t v : Fin (k + 1) → ℝ) i ^ 2) ^ b) =
        ∑ c ∈ Finset.range (b + 1),
          (((b.choose c * a.factorial * polyP k (b - c) : ℕ) : ℝ) /
            (((k + a + 2 * (b - c)).factorial : ℕ) : ℝ)) *
          ((s - t) ^ (k + a + 2 * (b - c)) * t ^ (2 * c)) := by
      intro t ht
      rw [Set.uIcc_of_le hs0] at ht
      have hst0 : 0 ≤ s - t := by linarith [ht.2]
      have hst1 : s - t ≤ 1 := by linarith [ht.1]
      have hexp : (fun v : Fin k → ℝ =>
            (s - ∑ i : Fin (k + 1), (Fin.cons t v : Fin (k + 1) → ℝ) i) ^ a *
              (∑ i : Fin (k + 1), (Fin.cons t v : Fin (k + 1) → ℝ) i ^ 2) ^ b) =
          (fun v : Fin k → ℝ => ∑ c ∈ Finset.range (b + 1),
            (((b.choose c : ℕ) : ℝ) * t ^ (2 * c)) *
              (((s - t) - ∑ i : Fin k, v i) ^ a * (∑ i : Fin k, (v i) ^ 2) ^ (b - c))) := by
        funext v
        have hs1' : s - ∑ i : Fin (k + 1), (Fin.cons t v : Fin (k + 1) → ℝ) i = (s - t) - ∑ i : Fin k, v i := by
          rw [Fin.sum_univ_succ]; simp only [Fin.cons_zero, Fin.cons_succ]; ring
        have hs2' : ∑ i : Fin (k + 1), (Fin.cons t v : Fin (k + 1) → ℝ) i ^ 2 = t ^ 2 + ∑ i : Fin k, (v i) ^ 2 := by
          rw [Fin.sum_univ_succ]; simp only [Fin.cons_zero, Fin.cons_succ]
        rw [hs1', hs2', add_pow (t ^ 2) _ b, Finset.mul_sum]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [← pow_mul, mul_comm 2 c]; ring
      rw [hexp, simplexIntegral_finset_sum (Finset.range (b + 1)) hst0 hst1
        (fun c _ => (isSimplexLipOn_basis k a (b - c) hst0 hst1).const_mul _)]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [simplexIntegral_const_mul hst0, ih a (b - c) hst0 hst1]
      push_cast; ring
    rw [intervalIntegral.integral_congr hinner,
      intervalIntegral.integral_finsetSum fun c _ => (by fun_prop : Continuous (fun t : ℝ =>
        (((b.choose c * a.factorial * polyP k (b - c) : ℕ) : ℝ) /
          (((k + a + 2 * (b - c)).factorial : ℕ) : ℝ)) *
        ((s - t) ^ (k + a + 2 * (b - c)) * t ^ (2 * c)))).intervalIntegrable 0 s]
    have hterm : ∀ c ∈ Finset.range (b + 1),
        ∫ t in (0 : ℝ)..s,
          (((b.choose c * a.factorial * polyP k (b - c) : ℕ) : ℝ) /
            (((k + a + 2 * (b - c)).factorial : ℕ) : ℝ)) *
          ((s - t) ^ (k + a + 2 * (b - c)) * t ^ (2 * c)) =
        (((a.factorial * (b.choose c * (2 * c).factorial * polyP k (b - c)) : ℕ) : ℝ) /
          (((k + 1 + a + 2 * b).factorial : ℕ) : ℝ)) * s ^ (k + 1 + a + 2 * b) := by
      intro c hc
      have hcb : c ≤ b := Nat.lt_succ_iff.mp (Finset.mem_range.mp hc)
      rw [intervalIntegral.integral_const_mul, integral_sub_pow_mul_pow s (k + a + 2 * (b - c)) (2 * c)]
      have hexp_eq : k + a + 2 * (b - c) + 2 * c + 1 = k + 1 + a + 2 * b := by omega
      rw [hexp_eq]
      have hne1 : (((k + a + 2 * (b - c)).factorial : ℕ) : ℝ) ≠ 0 := by positivity
      have hne2 : (((k + 1 + a + 2 * b).factorial : ℕ) : ℝ) ≠ 0 := by positivity
      push_cast; field_simp [hne1, hne2]
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul, ← Finset.sum_div]
    congr 2
    rw [show polyP (k + 1) b = ∑ c ∈ Finset.range (b + 1), b.choose c * (2 * c).factorial * polyP k (b - c) from rfl]
    rw [Finset.mul_sum, Nat.cast_sum]

/-- Symmetric polynomial test function `F(v) = ∑_{p : Fin n} c_p * (1 - ∑ v_i)^(a_p) * (∑ v_i^2)^(b_p)`. -/
def polyFn {n : ℕ} (k : ℕ) (a b : Fin n → ℕ) (c : Fin n → ℤ) (v : Fin k → ℝ) : ℝ :=
  ∑ p : Fin n, (c p : ℝ) * ((1 - ∑ i, v i) ^ (a p) * (∑ i, (v i) ^ 2) ^ (b p))

/-- Package `polyFn` as a `SimplexTestFn k`. -/
def mkPolyTestFn {n : ℕ} (k : ℕ) (a b : Fin n → ℕ) (c : Fin n → ℤ) : SimplexTestFn k where
  F := polyFn k a b c
  bound := ∑ p : Fin n, |(c p : ℝ)| * 1
  lip := ∑ p : Fin n, |(c p : ℝ)| * ((a p : ℝ) + 2 * (b p : ℝ))
  bound_nonneg := Finset.sum_nonneg fun p _ => mul_nonneg (abs_nonneg _) zero_le_one
  lip_nonneg := Finset.sum_nonneg fun p _ => mul_nonneg (abs_nonneg _) (by positivity)
  symm := fun σ v => by
    unfold polyFn
    refine Finset.sum_congr rfl fun p _ => ?_
    have h1 : ∑ i : Fin k, v (σ i) = ∑ i : Fin k, v i := Equiv.sum_comp σ v
    have h2 : ∑ i : Fin k, (v (σ i)) ^ 2 = ∑ i : Fin k, (v i) ^ 2 := Equiv.sum_comp σ (fun i => (v i) ^ 2)
    simp only [Function.comp_apply, h1, h2]
  abs_le := fun v hv0 hvs =>
    (IsSimplexLipOn.finset_sum Finset.univ fun p _ =>
      (isSimplexLipOn_basis k (a p) (b p) zero_le_one le_rfl).const_mul (c p : ℝ)).2.2.1 v ⟨hv0, hvs⟩
  lipschitz := fun u v hu0 hus hv0 hvs =>
    (IsSimplexLipOn.finset_sum Finset.univ fun p _ =>
      (isSimplexLipOn_basis k (a p) (b p) zero_le_one le_rfl).const_mul (c p : ℝ)).2.2.2 u v ⟨hu0, hus⟩ ⟨hv0, hvs⟩

/-- Exact rational bilinear formula for `maynardI k (polyFn k a b c)`. -/
theorem maynardI_poly {n : ℕ} (k : ℕ) (a b : Fin n → ℕ) (c : Fin n → ℤ) :
    maynardI k (polyFn k a b c) =
      ∑ p : Fin n, ∑ q : Fin n, (c p : ℝ) * (c q : ℝ) *
        ((((a p + a q).factorial * polyP k (b p + b q) : ℕ) : ℝ) /
          (((k + (a p + a q) + 2 * (b p + b q)).factorial : ℕ) : ℝ)) := by
  unfold maynardI polyFn
  have hexp : (fun v : Fin k → ℝ => (∑ p : Fin n, (c p : ℝ) * ((1 - ∑ i, v i) ^ (a p) * (∑ i, (v i) ^ 2) ^ (b p))) ^ 2) =
      (fun v : Fin k → ℝ => ∑ p : Fin n, ∑ q : Fin n, ((c p : ℝ) * (c q : ℝ)) *
        ((1 - ∑ i, v i) ^ (a p + a q) * (∑ i, (v i) ^ 2) ^ (b p + b q))) := by
    funext v; rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    rw [pow_add, pow_add]; ring
  rw [hexp, simplexIntegral_finset_sum Finset.univ zero_le_one le_rfl (fun p _ =>
    IsSimplexLipOn.finset_sum Finset.univ fun q _ =>
      (isSimplexLipOn_basis k (a p + a q) (b p + b q) zero_le_one le_rfl).const_mul _)]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [simplexIntegral_finset_sum Finset.univ zero_le_one le_rfl (fun q _ =>
    (isSimplexLipOn_basis k (a p + a q) (b p + b q) zero_le_one le_rfl).const_mul _)]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [simplexIntegral_const_mul zero_le_one, simplexIntegral_basis k (a p + a q) (b p + b q) zero_le_one le_rfl,
    one_pow, mul_one]

/-- Exact rational bilinear formula for `maynardJ0 k (polyFn (k + 1) a b c)`. -/
theorem maynardJ0_poly {n : ℕ} (k : ℕ) (a b : Fin n → ℕ) (c : Fin n → ℤ) :
    maynardJ0 k (polyFn (k + 1) a b c) =
      ∑ p : Fin n, ∑ q : Fin n, (c p : ℝ) * (c q : ℝ) *
        ∑ j₁ ∈ Finset.range (b p + 1), ∑ j₂ ∈ Finset.range (b q + 1),
          (((b p).choose j₁ * (a p).factorial * (2 * j₁).factorial : ℕ) : ℝ) / (((a p + 2 * j₁ + 1).factorial : ℕ) : ℝ) *
          ((((b q).choose j₂ * (a q).factorial * (2 * j₂).factorial : ℕ) : ℝ) / (((a q + 2 * j₂ + 1).factorial : ℕ) : ℝ)) *
          ((((a p + 2 * j₁ + 1 + (a q + 2 * j₂ + 1)).factorial * polyP k (b p - j₁ + (b q - j₂)) : ℕ) : ℝ) /
            (((k + (a p + 2 * j₁ + 1 + (a q + 2 * j₂ + 1)) + 2 * (b p - j₁ + (b q - j₂))).factorial : ℕ) : ℝ)) := by
  unfold maynardJ0
  -- Evaluate the inner 1D integral `∫ t in 0..(1 - ∑ v_i), polyFn (k + 1) a b c (Fin.cons t v)`
  have hinner : ∀ v : Fin k → ℝ,
      ∫ t in (0 : ℝ)..(1 - ∑ i, v i), polyFn (k + 1) a b c (Fin.cons t v) =
      ∑ p : Fin n, ∑ j₁ ∈ Finset.range (b p + 1),
        ((c p : ℝ) * (((b p).choose j₁ * (a p).factorial * (2 * j₁).factorial : ℕ) : ℝ) /
          (((a p + 2 * j₁ + 1).factorial : ℕ) : ℝ)) *
        ((1 - ∑ i, v i) ^ (a p + 2 * j₁ + 1) * (∑ i, (v i) ^ 2) ^ (b p - j₁)) := by
    intro v
    unfold polyFn
    have hpt : ∀ t : ℝ, ∑ p : Fin n, (c p : ℝ) *
          ((1 - ∑ i : Fin (k + 1), (Fin.cons t v : Fin (k + 1) → ℝ) i) ^ (a p) *
            (∑ i : Fin (k + 1), (Fin.cons t v : Fin (k + 1) → ℝ) i ^ 2) ^ (b p)) =
        ∑ p : Fin n, (c p : ℝ) *
          (((1 - ∑ i, v i) - t) ^ (a p) * ((∑ i, (v i) ^ 2) + t ^ 2) ^ (b p)) := fun t => by
      refine Finset.sum_congr rfl fun p _ => ?_
      have h1 : 1 - ∑ i : Fin (k + 1), (Fin.cons t v : Fin (k + 1) → ℝ) i = (1 - ∑ i, v i) - t := by
        rw [Fin.sum_univ_succ]; simp only [Fin.cons_zero, Fin.cons_succ]; ring
      have h2 : ∑ i : Fin (k + 1), (Fin.cons t v : Fin (k + 1) → ℝ) i ^ 2 = (∑ i, (v i) ^ 2) + t ^ 2 := by
        rw [Fin.sum_univ_succ]; simp only [Fin.cons_zero, Fin.cons_succ]; ring
      rw [h1, h2]
    simp_rw [hpt]
    rw [intervalIntegral.integral_finsetSum fun p _ => (by fun_prop : Continuous (fun t : ℝ =>
      (c p : ℝ) * (((1 - ∑ i, v i) - t) ^ (a p) * ((∑ i, (v i) ^ 2) + t ^ 2) ^ (b p)))).intervalIntegrable _ _]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [intervalIntegral.integral_const_mul, integral_sub_pow_mul_add_sq_pow, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j₁ _ => by ring
  simp_rw [hinner]
  have hsq : (fun v : Fin k → ℝ =>
        (∑ p : Fin n, ∑ j₁ ∈ Finset.range (b p + 1),
          ((c p : ℝ) * (((b p).choose j₁ * (a p).factorial * (2 * j₁).factorial : ℕ) : ℝ) /
            (((a p + 2 * j₁ + 1).factorial : ℕ) : ℝ)) *
          ((1 - ∑ i, v i) ^ (a p + 2 * j₁ + 1) * (∑ i, (v i) ^ 2) ^ (b p - j₁))) ^ 2) =
      (fun v : Fin k → ℝ =>
        ∑ p : Fin n, ∑ q : Fin n, ∑ j₁ ∈ Finset.range (b p + 1), ∑ j₂ ∈ Finset.range (b q + 1),
          (((c p : ℝ) * (c q : ℝ)) *
            ((((b p).choose j₁ * (a p).factorial * (2 * j₁).factorial : ℕ) : ℝ) / (((a p + 2 * j₁ + 1).factorial : ℕ) : ℝ)) *
            ((((b q).choose j₂ * (a q).factorial * (2 * j₂).factorial : ℕ) : ℝ) / (((a q + 2 * j₂ + 1).factorial : ℕ) : ℝ))) *
          ((1 - ∑ i, v i) ^ (a p + 2 * j₁ + 1 + (a q + 2 * j₂ + 1)) * (∑ i, (v i) ^ 2) ^ (b p - j₁ + (b q - j₂)))) := by
    funext v
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun j₁ _ => Finset.sum_congr rfl fun j₂ _ => ?_
    rw [pow_add, pow_add]; ring
  rw [hsq,
    simplexIntegral_finset_sum Finset.univ zero_le_one le_rfl (fun p _ =>
      IsSimplexLipOn.finset_sum Finset.univ fun q _ =>
        IsSimplexLipOn.finset_sum (Finset.range (b p + 1)) fun j₁ _ =>
          IsSimplexLipOn.finset_sum (Finset.range (b q + 1)) fun j₂ _ =>
            (isSimplexLipOn_basis k _ _ zero_le_one le_rfl).const_mul _)]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [simplexIntegral_finset_sum Finset.univ zero_le_one le_rfl (fun q _ =>
    IsSimplexLipOn.finset_sum (Finset.range (b p + 1)) fun j₁ _ =>
      IsSimplexLipOn.finset_sum (Finset.range (b q + 1)) fun j₂ _ =>
        (isSimplexLipOn_basis k _ _ zero_le_one le_rfl).const_mul _)]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [simplexIntegral_finset_sum (Finset.range (b p + 1)) zero_le_one le_rfl (fun j₁ _ =>
    IsSimplexLipOn.finset_sum (Finset.range (b q + 1)) fun j₂ _ =>
      (isSimplexLipOn_basis k _ _ zero_le_one le_rfl).const_mul _), Finset.mul_sum]
  refine Finset.sum_congr rfl fun j₁ _ => ?_
  rw [simplexIntegral_finset_sum (Finset.range (b q + 1)) zero_le_one le_rfl (fun j₂ _ =>
    (isSimplexLipOn_basis k _ _ zero_le_one le_rfl).const_mul _), Finset.mul_sum]
  refine Finset.sum_congr rfl fun j₂ _ => ?_
  rw [simplexIntegral_const_mul zero_le_one, simplexIntegral_basis k _ _ zero_le_one le_rfl, one_pow, mul_one]
  ring

/-! ## Section 2: Explicit `k = 105` Polynomial Witness (`M_{105} = 4.0019797... > 4`) -/

/-- The 42 basis pairs `(a, b)` with `a + 2*b ≤ 11` for Maynard's `k = 105` symmetric polynomial. -/
private def basis105 : Fin 42 → ℕ × ℕ :=
  ![(0, 0), (1, 0), (2, 0), (3, 0), (4, 0), (5, 0), (6, 0), (7, 0), (8, 0), (9, 0), (10, 0), (11, 0),
    (0, 1), (1, 1), (2, 1), (3, 1), (4, 1), (5, 1), (6, 1), (7, 1), (8, 1), (9, 1),
    (0, 2), (1, 2), (2, 2), (3, 2), (4, 2), (5, 2), (6, 2), (7, 2),
    (0, 3), (1, 3), (2, 3), (3, 3), (4, 3), (5, 3),
    (0, 4), (1, 4), (2, 4), (3, 4),
    (0, 5), (1, 5)]

private def a105 (p : Fin 42) : ℕ := (basis105 p).1
private def b105 (p : Fin 42) : ℕ := (basis105 p).2

/-- Exact integer coefficients giving `M_{105} = 4.0019797... > 4`. -/
private def c105 : Fin 42 → ℤ :=
  ![-10, -5267, -55918, -374640, 166481439, -440995343, -21849340910, 58540882525, 450251191613,
    2002480109127, -24945401815038, 45962083256530,
    2403, 1222360, 17011648, -219304156, -31513500435, 149321083388, 3015213382068,
    -7442466799133, -96279325539765, 294250860896069,
    -235661, -114117778, -1789906537, 46390669593, 2034044550516, -14062073024736,
    -130879945575872, 672130134948540,
    11927504, 5413147229, 80304319307, -2924692938982, -46238572062721, 470983140908692,
    -315049261, -132266212212, -1333008757686, 62060752208682,
    3494487459, 1353887139930]

/-- Precomputed `polyP 105 b` for `0 ≤ b ≤ 10` (kernel-verified below). -/
private def tableP105 : Fin 11 → ℕ :=
  ![1, 210, 46200, 10646160, 2569472640, 649565763840, 172039896806400, 47758733442201600,
    13906217329385472000, 4251952625998204108800, 1367542144912926611865600]

/-- Precomputed `polyP 104 b` for `0 ≤ b ≤ 10` (kernel-verified below). -/
private def tableP104 : Fin 11 → ℕ :=
  ![1, 208, 45344, 10358400, 2479436544, 621913344000, 163502746767360, 45074911052021760,
    13040192296300216320, 3963497946537236889600, 1267924969103825829888000]

/-- Fast computable row update for `polyP` (so kernel `decide` verifies all 11 entries instantaneously). -/
private def polyPRow : ℕ → List ℕ
  | 0 => [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  | k + 1 =>
    let prev := polyPRow k
    List.ofFn fun b : Fin 11 =>
      ∑ c ∈ Finset.range (b.1 + 1), b.1.choose c * (2 * c).factorial * prev.getD (b.1 - c) 0

private lemma polyPRow_len (k : ℕ) : (polyPRow k).length = 11 := by
  cases k <;> simp [polyPRow]

private lemma polyPRow_getD_eq (k : ℕ) : ∀ b : Fin 11, (polyPRow k).getD b.1 0 = polyP k b.1 := by
  induction k with
  | zero =>
    intro b; fin_cases b <;> rfl
  | succ k ih =>
    intro b
    have hlt : b.1 < (polyPRow (k + 1)).length := by rw [polyPRow_len]; exact b.2
    simp only [polyPRow, List.getD_eq_getElem?_getD, List.getElem?_ofFn, b.2, ↓reduceDIte, Option.getD_some]
    unfold polyP
    refine Finset.sum_congr rfl fun c hc => ?_
    have hbc : b.1 - c < 11 := by omega
    have hih := ih ⟨b.1 - c, hbc⟩
    rw [List.getD_eq_getElem?_getD] at hih
    rw [hih]

private lemma tableP105_eq : ∀ b : Fin 11, polyP 105 b.1 = tableP105 b := by
  have hcheck : ∀ b : Fin 11, (polyPRow 105).getD b.1 0 = tableP105 b := by decide
  intro b; rw [← polyPRow_getD_eq 105 b, hcheck b]

private lemma tableP104_eq : ∀ b : Fin 11, polyP 104 b.1 = tableP104 b := by
  have hcheck : ∀ b : Fin 11, (polyPRow 104).getD b.1 0 = tableP104 b := by decide
  intro b; rw [← polyPRow_getD_eq 104 b, hcheck b]

private lemma deg_basis105 : ∀ p : Fin 42, a105 p + 2 * b105 p ≤ 11 := by decide
private lemma b_basis105 : ∀ p : Fin 42, b105 p ≤ 5 := by decide

/-- Exact integer scaling factor `D_common = (128! / 105!) * (12!)^2`. -/
private def D105 : ℕ := prodFrom 106 23 * ((12).factorial) ^ 2

private lemma D105_pos : 0 < D105 := by decide

/-- Exact scaled integer `I_int_105 = 105! * D105 * maynardI 105 (polyFn 105 a105 b105 c105)`. -/
private def I_int_105 : ℤ :=
  ∑ p : Fin 42, ∑ q : Fin 42,
    c105 p * c105 q *
      (((a105 p + a105 q).factorial * tableP105 ⟨b105 p + b105 q, by have := b_basis105 p; have := b_basis105 q; omega⟩ *
        prodFrom (106 + (a105 p + a105 q + 2 * (b105 p + b105 q))) (23 - (a105 p + a105 q + 2 * (b105 p + b105 q))) *
        ((12).factorial) ^ 2 : ℕ) : ℤ)

/-- Exact scaled integer `J_int_105 = 105! * D105 * maynardJ0 104 (polyFn 105 a105 b105 c105)`. -/
private def J_int_105 : ℤ :=
  ∑ p : Fin 42, ∑ q : Fin 42,
    c105 p * c105 q *
      ∑ j₁ ∈ Finset.range (b105 p + 1), ∑ j₂ ∈ Finset.range (b105 q + 1),
        let f1 : ℕ := (b105 p).choose j₁ * (a105 p).factorial * (2 * j₁).factorial *
          prodFrom (a105 p + 2 * j₁ + 2) (11 - (a105 p + 2 * j₁))
        let f2 : ℕ := (b105 q).choose j₂ * (a105 q).factorial * (2 * j₂).factorial *
          prodFrom (a105 q + 2 * j₂ + 2) (11 - (a105 q + 2 * j₂))
        let AA : ℕ := a105 p + 2 * j₁ + 1 + (a105 q + 2 * j₂ + 1)
        let BB : ℕ := b105 p - j₁ + (b105 q - j₂)
        let d : ℕ := a105 p + a105 q + 2 * (b105 p + b105 q)
        ((f1 * f2 * AA.factorial *
          tableP104 ⟨BB, by have := b_basis105 p; have := b_basis105 q; omega⟩ *
          prodFrom (107 + d) (22 - d) : ℕ) : ℤ)

/-- Kernel verification: `I_int_105 > 0` (ZERO `native_decide`!). -/
private lemma I_int_105_pos : (0 : ℤ) < I_int_105 := by decide

/-- Kernel verification: `105 * J_int_105 > 4 * I_int_105` (i.e. `M_{105} = 4.0019797... > 4`, ZERO `native_decide`!). -/
private lemma J_int_105_gt : 4 * I_int_105 < 105 * J_int_105 := by decide

/-- Maynard's explicit symmetric polynomial test function on the 105-simplex. -/
def T105 : SimplexTestFn 105 := mkPolyTestFn 105 a105 b105 c105

/-- **Unconditional Exact `k = 105` Variational Ratio `M_{105} > 4`** (Maynard 2015 §7). -/
theorem maynard_105_ratio_gt_four :
    0 < maynardI 105 T105.F ∧
      4 * (1 : ℝ) * maynardI 105 T105.F < ((105 : ℕ) : ℝ) * maynardJ0 104 T105.F := by
  have hscale_pos : (0 : ℝ) < ((105).factorial : ℝ) * (D105 : ℝ) :=
    mul_pos (by positivity) (Nat.cast_pos.mpr D105_pos)
  have h128_eq : (105).factorial * prodFrom 106 23 = (128).factorial :=
    prodFrom_mul_factorial 105 128 (by omega)
  have hI_eq : ((105).factorial : ℝ) * (D105 : ℝ) * maynardI 105 T105.F = (I_int_105 : ℝ) := by
    dsimp only [T105, mkPolyTestFn]
    rw [maynardI_poly 105 a105 b105 c105]
    unfold I_int_105
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    set d := a105 p + a105 q + 2 * (b105 p + b105 q)
    have hd22 : d ≤ 22 := by have := deg_basis105 p; have := deg_basis105 q; omega
    have hb10 : b105 p + b105 q < 11 := by have := b_basis105 p; have := b_basis105 q; omega
    rw [← tableP105_eq ⟨b105 p + b105 q, hb10⟩]
    have hfac_d : (105 + d).factorial * prodFrom (106 + d) (23 - d) = (128).factorial := by
      have h1 := prodFrom_mul_factorial (105 + d) 128 (by omega)
      rwa [show 105 + d + 1 = 106 + d by omega, show 128 - (105 + d) = 23 - d by omega] at h1
    have hden_ne : (((105 + (a105 p + a105 q) + 2 * (b105 p + b105 q)).factorial : ℕ) : ℝ) ≠ 0 := by positivity
    have hd_eq : 105 + (a105 p + a105 q) + 2 * (b105 p + b105 q) = 105 + d := by dsimp only [d]; omega
    rw [hd_eq] at hden_ne ⊢
    dsimp only [D105]; push_cast
    have hfac_eqR : (((105).factorial : ℝ) * (prodFrom 106 23 : ℝ)) =
        (((105 + d).factorial : ℝ) * (prodFrom (106 + d) (23 - d) : ℝ)) := by
      exact_mod_cast (h128_eq.trans hfac_d.symm)
    field_simp [hden_ne]
    rw [hfac_eqR]; ring
  have hJ_eq : ((105).factorial : ℝ) * (D105 : ℝ) * maynardJ0 104 T105.F = (J_int_105 : ℝ) := by
    dsimp only [T105, mkPolyTestFn]
    rw [maynardJ0_poly 104 a105 b105 c105]
    unfold J_int_105
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [← mul_assoc, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j₁ hj₁ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j₂ hj₂ => ?_
    have hj1_le : j₁ ≤ b105 p := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj₁)
    have hj2_le : j₂ ≤ b105 q := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj₂)
    have hdeg_p : a105 p + 2 * j₁ ≤ 11 := by have := deg_basis105 p; omega
    have hdeg_q : a105 q + 2 * j₂ ≤ 11 := by have := deg_basis105 q; omega
    set d := a105 p + a105 q + 2 * (b105 p + b105 q)
    have hd22 : d ≤ 22 := by have := deg_basis105 p; have := deg_basis105 q; omega
    set AA := a105 p + 2 * j₁ + 1 + (a105 q + 2 * j₂ + 1)
    set BB := b105 p - j₁ + (b105 q - j₂)
    have hBB10 : BB < 11 := by have := b_basis105 p; have := b_basis105 q; omega
    have h106d : 104 + AA + 2 * BB = 106 + d := by dsimp only [AA, BB, d]; omega
    rw [← tableP104_eq ⟨BB, hBB10⟩]
    have hfac1 : (a105 p + 2 * j₁ + 1).factorial * prodFrom (a105 p + 2 * j₁ + 2) (11 - (a105 p + 2 * j₁)) = (12).factorial := by
      have h1 := prodFrom_mul_factorial (a105 p + 2 * j₁ + 1) 12 (by omega)
      rwa [show a105 p + 2 * j₁ + 1 + 1 = a105 p + 2 * j₁ + 2 by omega,
        show 12 - (a105 p + 2 * j₁ + 1) = 11 - (a105 p + 2 * j₁) by omega] at h1
    have hfac2 : (a105 q + 2 * j₂ + 1).factorial * prodFrom (a105 q + 2 * j₂ + 2) (11 - (a105 q + 2 * j₂)) = (12).factorial := by
      have h1 := prodFrom_mul_factorial (a105 q + 2 * j₂ + 1) 12 (by omega)
      rwa [show a105 q + 2 * j₂ + 1 + 1 = a105 q + 2 * j₂ + 2 by omega,
        show 12 - (a105 q + 2 * j₂ + 1) = 11 - (a105 q + 2 * j₂) by omega] at h1
    have hfac_d : (106 + d).factorial * prodFrom (107 + d) (22 - d) = (128).factorial := by
      have h1 := prodFrom_mul_factorial (106 + d) 128 (by omega)
      rwa [show 106 + d + 1 = 107 + d by omega, show 128 - (106 + d) = 22 - d by omega] at h1
    have hfac1R : ((12).factorial : ℝ) =
        ((a105 p + 2 * j₁ + 1).factorial : ℝ) * (prodFrom (a105 p + 2 * j₁ + 2) (11 - (a105 p + 2 * j₁)) : ℝ) := by
      exact_mod_cast hfac1.symm
    have hfac2R : ((12).factorial : ℝ) =
        ((a105 q + 2 * j₂ + 1).factorial : ℝ) * (prodFrom (a105 q + 2 * j₂ + 2) (11 - (a105 q + 2 * j₂)) : ℝ) := by
      exact_mod_cast hfac2.symm
    have hfac_dR : ((105).factorial : ℝ) * (prodFrom 106 23 : ℝ) =
        ((106 + d).factorial : ℝ) * (prodFrom (107 + d) (22 - d) : ℝ) := by
      exact_mod_cast (h128_eq.trans hfac_d.symm)
    rw [h106d]
    have hne1 : (((a105 p + 2 * j₁ + 1).factorial : ℕ) : ℝ) ≠ 0 := by positivity
    have hne2 : (((a105 q + 2 * j₂ + 1).factorial : ℕ) : ℝ) ≠ 0 := by positivity
    have hne3 : (((106 + d).factorial : ℕ) : ℝ) ≠ 0 := by positivity
    dsimp only [D105]
    push_cast
    have hcomb : ((105).factorial : ℝ) * ((prodFrom 106 23 : ℝ) * ((12).factorial : ℝ) ^ 2) =
        (((106 + d).factorial : ℝ) * (prodFrom (107 + d) (22 - d) : ℝ)) *
        ((((a105 p + 2 * j₁ + 1).factorial : ℝ) * (prodFrom (a105 p + 2 * j₁ + 2) (11 - (a105 p + 2 * j₁)) : ℝ)) *
         (((a105 q + 2 * j₂ + 1).factorial : ℝ) * (prodFrom (a105 q + 2 * j₂ + 2) (11 - (a105 q + 2 * j₂)) : ℝ))) := by
      rw [← mul_assoc, hfac_dR, pow_two]
      congr 1
      rw [← hfac1R, ← hfac2R]
    rw [hcomb]
    field_simp [hne1, hne2, hne3]
    ring
  have hI_int_posR : (0 : ℝ) < (I_int_105 : ℝ) := by exact_mod_cast I_int_105_pos
  have hJ_int_gtR : 4 * (I_int_105 : ℝ) < 105 * (J_int_105 : ℝ) := by exact_mod_cast J_int_105_gt
  constructor
  · exact pos_of_mul_pos_right (hI_eq.symm ▸ hI_int_posR) hscale_pos.le
  · have hmul : ((105).factorial : ℝ) * (D105 : ℝ) * (4 * (1 : ℝ) * maynardI 105 T105.F) <
        ((105).factorial : ℝ) * (D105 : ℝ) * (((105 : ℕ) : ℝ) * maynardJ0 104 T105.F) := by
      have h1 : ((105).factorial : ℝ) * (D105 : ℝ) * (4 * (1 : ℝ) * maynardI 105 T105.F) = 4 * (I_int_105 : ℝ) := by
        rw [← hI_eq]; ring
      have h2 : ((105).factorial : ℝ) * (D105 : ℝ) * (((105 : ℕ) : ℝ) * maynardJ0 104 T105.F) = 105 * (J_int_105 : ℝ) := by
        rw [← hJ_eq]; push_cast; ring
      rw [h1, h2]; exact hJ_int_gtR
    exact lt_of_mul_lt_mul_left hmul hscale_pos.le

/-! ## Section 3: Large-`k` Variational Ratio `M_{k+1} ≥ Real.log (k + 1) / 32` (`99 ≤ k`) -/

/-- Helper: `IsSimplexLipOn` for a product `∏ i, h (v i)` of bounded Lipschitz functions on `[0, 1]`. -/
private lemma isSimplexLipOn_prod (m : ℕ) {s M L : ℝ} (_hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    {h : ℝ → ℝ} (_hM : 0 ≤ M) (hL : 0 ≤ L) (hM1 : M ≤ 1)
    (hbd : ∀ t ∈ Set.Icc (0 : ℝ) 1, |h t| ≤ M)
    (hlip : ∀ t₁ ∈ Set.Icc (0 : ℝ) 1, ∀ t₂ ∈ Set.Icc (0 : ℝ) 1, |h t₁ - h t₂| ≤ L * |t₁ - t₂|) :
    IsSimplexLipOn s 1 L (fun v : Fin m → ℝ => ∏ i, h (v i)) := by
  induction m with
  | zero =>
    refine ⟨zero_le_one, hL, fun _ _ => by simp, fun _ _ _ _ => by simp⟩
  | succ m ih =>
    refine ⟨zero_le_one, hL, fun v hv => ?_, fun u v hu hv => ?_⟩
    · rw [Finset.abs_prod]
      refine Finset.prod_le_one (fun _ _ => abs_nonneg _) fun i _ => ?_
      have hi1 : v i ≤ 1 := le_trans (Finset.single_le_sum (fun j _ => hv.1 j) (Finset.mem_univ i)) (hv.2.trans hs1)
      exact (hbd (v i) ⟨hv.1 i, hi1⟩).trans hM1
    · dsimp only
      rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
      have hu0 : u 0 ∈ Set.Icc (0 : ℝ) 1 := ⟨hu.1 0, le_trans (Finset.single_le_sum (fun j _ => hu.1 j) (Finset.mem_univ 0)) (hu.2.trans hs1)⟩
      have hv0 : v 0 ∈ Set.Icc (0 : ℝ) 1 := ⟨hv.1 0, le_trans (Finset.single_le_sum (fun j _ => hv.1 j) (Finset.mem_univ 0)) (hv.2.trans hs1)⟩
      have hut : InSimplex s (Fin.tail u) := ⟨fun j => hu.1 j.succ, by
        have := hu.2; rw [Fin.sum_univ_succ] at this; dsimp only [Fin.tail]; linarith [hu.1 0]⟩
      have hvt : InSimplex s (Fin.tail v) := ⟨fun j => hv.1 j.succ, by
        have := hv.2; rw [Fin.sum_univ_succ] at this; dsimp only [Fin.tail]; linarith [hv.1 0]⟩
      have hrew : h (u 0) * ∏ i : Fin m, h (u i.succ) - h (v 0) * ∏ i : Fin m, h (v i.succ) =
          (h (u 0) - h (v 0)) * (∏ i : Fin m, h (u i.succ)) +
            h (v 0) * ((∏ i : Fin m, h (u i.succ)) - (∏ i : Fin m, h (v i.succ))) := by ring
      rw [hrew, Fin.sum_univ_succ]
      calc |(h (u 0) - h (v 0)) * (∏ i : Fin m, h (u i.succ)) +
              h (v 0) * ((∏ i : Fin m, h (u i.succ)) - (∏ i : Fin m, h (v i.succ)))|
          ≤ |h (u 0) - h (v 0)| * |∏ i : Fin m, h (u i.succ)| +
            |h (v 0)| * |(∏ i : Fin m, h (u i.succ)) - (∏ i : Fin m, h (v i.succ))| := by
            rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
        _ ≤ (L * |u 0 - v 0|) * 1 + 1 * (L * ∑ i : Fin m, |u i.succ - v i.succ|) :=
            add_le_add (mul_le_mul (hlip _ hu0 _ hv0) (ih.2.2.1 (Fin.tail u) hut) (abs_nonneg _) (mul_nonneg hL (abs_nonneg _)))
              (mul_le_mul ((hbd _ hv0).trans hM1) (ih.2.2.2 (Fin.tail u) (Fin.tail v) hut hvt) (abs_nonneg _) zero_le_one)
        _ = L * (|u 0 - v 0| + ∑ i : Fin m, |u i.succ - v i.succ|) := by ring

/-- Upper bound for a product simplex integral:
`simplexIntegral m s (fun v => ∏ i, h (v i)) ≤ (∫ t in 0..1, h t)^m` for `0 ≤ s ≤ 1`, `h ≥ 0`. -/
private lemma simplexIntegral_prod_le_pow (m : ℕ) {h : ℝ → ℝ}
    (hh_cont : ContinuousOn h (Set.Icc 0 1)) (hh_nn : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ h t)
    {M L : ℝ} (hM : 0 ≤ M) (hL : 0 ≤ L) (hM1 : M ≤ 1)
    (hbd : ∀ t ∈ Set.Icc (0 : ℝ) 1, |h t| ≤ M)
    (hlip : ∀ t₁ ∈ Set.Icc (0 : ℝ) 1, ∀ t₂ ∈ Set.Icc (0 : ℝ) 1, |h t₁ - h t₂| ≤ L * |t₁ - t₂|) :
    ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
      simplexIntegral m s (fun v : Fin m → ℝ => ∏ i, h (v i)) ≤ (∫ t in (0 : ℝ)..1, h t) ^ m := by
  induction m with
  | zero => intro s _ _; simp [simplexIntegral]
  | succ m ih =>
    intro s hs0 hs1
    unfold simplexIntegral
    have hI_nn : 0 ≤ ∫ t in (0 : ℝ)..1, h t :=
      intervalIntegral.integral_nonneg zero_le_one fun t ht => hh_nn t ht
    have hcongr : ∀ t ∈ Set.uIcc (0 : ℝ) s,
        simplexIntegral m (s - t) (fun v => ∏ i : Fin (m + 1), h ((Fin.cons t v : Fin (m + 1) → ℝ) i)) =
        h t * simplexIntegral m (s - t) (fun v => ∏ i : Fin m, h (v i)) := by
      intro t ht; rw [Set.uIcc_of_le hs0] at ht
      have hfn : (fun v : Fin m → ℝ => ∏ i : Fin (m + 1), h ((Fin.cons t v : Fin (m + 1) → ℝ) i)) =
          (fun v : Fin m → ℝ => h t * ∏ i : Fin m, h (v i)) := by
        funext v; rw [Fin.prod_univ_succ]; simp
      rw [hfn, simplexIntegral_const_mul (by linarith [ht.2])]
    rw [intervalIntegral.integral_congr hcongr]
    have hint_lhs : IntervalIntegrable (fun t => h t * simplexIntegral m (s - t) (fun v => ∏ i : Fin m, h (v i)))
        MeasureTheory.volume 0 s := by
      have hlip_all := isSimplexLipOn_prod (m + 1) hs0 hs1 hM hL hM1 hbd hlip
      exact (intervalIntegrable_simplex_slice hs0 hs1 hlip_all).congr fun t ht => hcongr t (Set.uIoc_subset_uIcc ht)
    have hint_h_s : IntervalIntegrable h MeasureTheory.volume 0 s :=
      (hh_cont.mono (by rw [Set.uIcc_of_le hs0]; exact Set.Icc_subset_Icc_right hs1)).intervalIntegrable
    have hint_h_1 : IntervalIntegrable h MeasureTheory.volume s 1 :=
      (hh_cont.mono (by rw [Set.uIcc_of_le hs1]; exact Set.Icc_subset_Icc_left hs0)).intervalIntegrable
    calc ∫ t in (0 : ℝ)..s, h t * simplexIntegral m (s - t) (fun v => ∏ i : Fin m, h (v i))
        ≤ ∫ t in (0 : ℝ)..s, h t * (∫ x in (0 : ℝ)..1, h x) ^ m := by
          refine intervalIntegral.integral_mono_on hs0 hint_lhs (hint_h_s.mul_const _) fun t ht => ?_
          exact mul_le_mul_of_nonneg_left (ih (s - t) (by linarith [ht.2]) (by linarith [ht.1]))
            (hh_nn t ⟨ht.1, ht.2.trans hs1⟩)
      _ = (∫ t in (0 : ℝ)..s, h t) * (∫ x in (0 : ℝ)..1, h x) ^ m := intervalIntegral.integral_mul_const _ _
      _ ≤ (∫ t in (0 : ℝ)..1, h t) * (∫ x in (0 : ℝ)..1, h x) ^ m := by
          refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg hI_nn m)
          have hadd := intervalIntegral.integral_add_adjacent_intervals hint_h_s hint_h_1
          have htail : 0 ≤ ∫ t in s..1, h t :=
            intervalIntegral.integral_nonneg hs1 fun t ht => hh_nn t ⟨hs0.trans ht.1, ht.2⟩
          linarith
      _ = (∫ x in (0 : ℝ)..1, h x) ^ (m + 1) := (pow_succ' _ m).symm

/-- **Continuous Markov Lower Bound for Product Simplex Integrals**:
for any bounded Lipschitz `h ≥ 0` on `[0, 1]` and `0 < s ≤ 1`:
`(∫_0^1 h)^m - (m / s) * (∫_0^1 t * h t) * (∫_0^1 h)^(m - 1) ≤ simplexIntegral m s (fun v => ∏ i, h (v i))`. -/
private lemma simplexIntegral_prod_markov (m : ℕ) {h : ℝ → ℝ}
    (hh_cont : ContinuousOn h (Set.Icc 0 1)) (hh_nn : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ h t)
    {M L : ℝ} (hM : 0 ≤ M) (hL : 0 ≤ L) (hM1 : M ≤ 1)
    (hbd : ∀ t ∈ Set.Icc (0 : ℝ) 1, |h t| ≤ M)
    (hlip : ∀ t₁ ∈ Set.Icc (0 : ℝ) 1, ∀ t₂ ∈ Set.Icc (0 : ℝ) 1, |h t₁ - h t₂| ≤ L * |t₁ - t₂|)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) :
    (∫ t in (0 : ℝ)..1, h t) ^ m -
      ((m : ℝ) / s) * (∫ t in (0 : ℝ)..1, t * h t) * (∫ t in (0 : ℝ)..1, h t) ^ (m - 1) ≤
    simplexIntegral m s (fun v : Fin m → ℝ => ∏ i, h (v i)) := by
  set Ih : ℝ := ∫ t in (0 : ℝ)..1, h t
  set Jh : ℝ := ∫ t in (0 : ℝ)..1, t * h t
  have hIh_nn : 0 ≤ Ih := intervalIntegral.integral_nonneg zero_le_one fun t ht => hh_nn t ht
  have hJh_nn : 0 ≤ Jh := intervalIntegral.integral_nonneg zero_le_one fun t ht => mul_nonneg ht.1 (hh_nn t ht)
  -- Define `R n u := if 0 ≤ u then simplexIntegral n u (fun v => (u - ∑ i, v i) * ∏ i, h (v i)) else 0`
  let R : ℕ → ℝ → ℝ := fun n u =>
    if 0 ≤ u then simplexIntegral n u (fun v => (u - ∑ i, v i) * ∏ i, h (v i)) else 0
  have hR_zero : ∀ n : ℕ, R n 0 = 0 := fun n => by
    dsimp only [R]; rw [if_pos le_rfl]
    cases n with
    | zero => simp [simplexIntegral]
    | succ n => unfold simplexIntegral; simp
  -- Show `R n u` is continuous on `(-∞, 1]` (hence `u - t ↦ R n (u - t)` is continuous on `[0, 1]`)
  have hR_cont : ∀ (n : ℕ) (u : ℝ), 0 ≤ u → u ≤ 1 →
      ContinuousOn (fun t : ℝ => R n (u - t)) (Set.Icc 0 1) := by
    intro n u hu0 hu1
    -- Split into `[0, u]` (where `u - t ≥ 0`, Lipschitz) and `[u, 1]` (where `u - t ≤ 0`, identically `0`)
    have hlip_left : ContinuousOn (fun t : ℝ => R n (u - t)) (Set.Icc 0 u) := by
      have hG : IsSimplexLipOn u 1 (1 + L) (fun v : Fin (n + 1) → ℝ =>
          (u - ∑ i, v i) * (∏ i : Fin n, h (v i.succ))) := by
        have h1 : IsSimplexLipOn u 1 1 (fun v : Fin (n + 1) → ℝ => u - ∑ i, v i) := by
          simpa using isSimplexLipOn_basis (n + 1) 1 0 hu0 hu1
        have h2 : IsSimplexLipOn u 1 L (fun v : Fin (n + 1) → ℝ => ∏ i : Fin n, h (v i.succ)) := by
          have hp := isSimplexLipOn_prod n hu0 hu1 hM hL hM1 hbd hlip
          refine ⟨zero_le_one, hL, fun v hv => hp.2.2.1 (Fin.tail v) ⟨fun j => hv.1 j.succ, ?_⟩,
            fun v₁ v₂ hv₁ hv₂ => ?_⟩
          · have := hv.2; rw [Fin.sum_univ_succ] at this; dsimp only [Fin.tail]; linarith [hv.1 0]
          · have h1' : InSimplex u (Fin.tail v₁) := ⟨fun j => hv₁.1 j.succ, by
              have := hv₁.2; rw [Fin.sum_univ_succ] at this; dsimp only [Fin.tail]; linarith [hv₁.1 0]⟩
            have h2' : InSimplex u (Fin.tail v₂) := ⟨fun j => hv₂.1 j.succ, by
              have := hv₂.2; rw [Fin.sum_univ_succ] at this; dsimp only [Fin.tail]; linarith [hv₂.1 0]⟩
            calc |(∏ i : Fin n, h (v₁ i.succ)) - (∏ i : Fin n, h (v₂ i.succ))|
                ≤ L * ∑ i : Fin n, |v₁ i.succ - v₂ i.succ| := hp.2.2.2 _ _ h1' h2'
              _ ≤ L * (|v₁ 0 - v₂ 0| + ∑ i : Fin n, |v₁ i.succ - v₂ i.succ|) :=
                  mul_le_mul_of_nonneg_left (by linarith [abs_nonneg (v₁ 0 - v₂ 0)]) hL
              _ = L * ∑ i : Fin (n + 1), |v₁ i - v₂ i| := by rw [Fin.sum_univ_succ]
        simpa only [one_mul, mul_one] using h1.mul h2
      have hcongr : Set.EqOn (fun t : ℝ => R n (u - t))
          (fun t : ℝ => simplexIntegral n (u - t) (fun v => (u - ∑ i, (Fin.cons t v : Fin (n + 1) → ℝ) i) * ∏ i, h (v i)))
          (Set.Icc 0 u) := fun t ht => by
        dsimp only [R]; rw [if_pos (by linarith [ht.2])]
        refine simplexIntegral_congr (by linarith [ht.2]) fun v _ => ?_
        congr 1; rw [Fin.sum_univ_succ]; simp only [Fin.cons_zero, Fin.cons_succ]; ring
      refine ContinuousOn.congr ?_ hcongr
      refine Metric.continuousOn_iff.mpr fun t ht ε hε => ?_
      refine ⟨ε / (1 + L + (n : ℝ) * 1 + 1), by positivity, fun t' ht' htt' => ?_⟩
      rw [Real.dist_eq] at htt' ⊢
      have hlip := simplexIntegral_slice_lipschitz hu0 hu1 hG ht' ht
      calc _ ≤ (1 + L + (n : ℝ) * 1) * |t' - t| := hlip
        _ ≤ (1 + L + (n : ℝ) * 1 + 1) * |t' - t| := mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
        _ < (1 + L + (n : ℝ) * 1 + 1) * (ε / (1 + L + (n : ℝ) * 1 + 1)) := mul_lt_mul_of_pos_left htt' (by positivity)
        _ = ε := by field_simp [show 1 + L + (n : ℝ) * 1 + 1 ≠ 0 by positivity]
    have hconst_right : ContinuousOn (fun t : ℝ => R n (u - t)) (Set.Icc u 1) := by
      refine ContinuousOn.congr (continuousOn_const (c := (0 : ℝ))) fun t ht => ?_
      rcases lt_or_eq_of_le ht.1 with hlt | rfl
      · dsimp only [R]; rw [if_neg (by linarith)]
      · rw [sub_self, hR_zero n]
    have hunion : Set.Icc (0 : ℝ) 1 = Set.Icc 0 u ∪ Set.Icc u 1 :=
      (Set.Icc_union_Icc_eq_Icc hu0 hu1).symm
    rw [hunion]
    exact ContinuousOn.union_of_isClosed hlip_left hconst_right isClosed_Icc isClosed_Icc
  -- Inductive Markov inequality on `R n u` for ALL `u ≤ 1`!
  have hgen : ∀ (n : ℕ) (u : ℝ), u ≤ 1 →
      u * Ih ^ n - (n : ℝ) * Jh * Ih ^ (n - 1) ≤ R n u := by
    intro n
    induction n with
    | zero =>
      intro u _
      dsimp only [R, simplexIntegral]
      simp only [pow_zero, mul_one, Nat.cast_zero, zero_mul, sub_zero, Finset.univ_eq_empty, Finset.sum_empty,
        Finset.prod_empty]
      split_ifs with hu <;> linarith
    | succ n ih =>
      intro u hu1
      by_cases hu0 : 0 ≤ u
      · dsimp only [R]; rw [if_pos hu0]
        unfold simplexIntegral
        have hcongr_u : ∀ t ∈ Set.uIcc (0 : ℝ) u,
            simplexIntegral n (u - t) (fun v => (u - ∑ i : Fin (n + 1), (Fin.cons t v : Fin (n + 1) → ℝ) i) *
              ∏ i : Fin (n + 1), h ((Fin.cons t v : Fin (n + 1) → ℝ) i)) =
            h t * R n (u - t) := by
          intro t ht; rw [Set.uIcc_of_le hu0] at ht
          have hfn : (fun v : Fin n → ℝ => (u - ∑ i : Fin (n + 1), (Fin.cons t v : Fin (n + 1) → ℝ) i) *
                ∏ i : Fin (n + 1), h ((Fin.cons t v : Fin (n + 1) → ℝ) i)) =
              (fun v : Fin n → ℝ => h t * (((u - t) - ∑ i : Fin n, v i) * ∏ i : Fin n, h (v i))) := by
            funext v; rw [Fin.sum_univ_succ, Fin.prod_univ_succ]; simp only [Fin.cons_zero, Fin.cons_succ]; ring
          rw [hfn, simplexIntegral_const_mul (by linarith [ht.2])]
          dsimp only [R]; rw [if_pos (by linarith [ht.2])]
        rw [intervalIntegral.integral_congr hcongr_u]
        have hcont_hR : ContinuousOn (fun t : ℝ => h t * R n (u - t)) (Set.Icc 0 1) :=
          hh_cont.mul (hR_cont n u hu0 hu1)
        have hint1 : IntervalIntegrable (fun t => h t * R n (u - t)) MeasureTheory.volume 0 u :=
          (hcont_hR.mono (by rw [Set.uIcc_of_le hu0]; exact Set.Icc_subset_Icc_right hu1)).intervalIntegrable
        have hint2 : IntervalIntegrable (fun t => h t * R n (u - t)) MeasureTheory.volume u 1 :=
          (hcont_hR.mono (by rw [Set.uIcc_of_le hu1]; exact Set.Icc_subset_Icc_left hu0)).intervalIntegrable
        have hzero_tail : ∫ t in u..1, h t * R n (u - t) = 0 := by
          have hcongr_0 : ∀ t ∈ Set.uIcc u 1, h t * R n (u - t) = 0 := by
            intro t ht; rw [Set.uIcc_of_le hu1] at ht
            rcases lt_or_eq_of_le ht.1 with hlt | rfl
            · dsimp only [R]; rw [if_neg (by linarith), mul_zero]
            · rw [sub_self, hR_zero n, mul_zero]
          rw [intervalIntegral.integral_congr hcongr_0, intervalIntegral.integral_zero]
        have heq_01 : ∫ t in (0 : ℝ)..u, h t * R n (u - t) = ∫ t in (0 : ℝ)..1, h t * R n (u - t) := by
          have := intervalIntegral.integral_add_adjacent_intervals hint1 hint2
          linarith
        rw [heq_01]
        have hcont_lo : ContinuousOn (fun t : ℝ => h t * ((u - t) * Ih ^ n - (n : ℝ) * Jh * Ih ^ (n - 1))) (Set.Icc 0 1) :=
          hh_cont.mul (by fun_prop : Continuous (fun t : ℝ => (u - t) * Ih ^ n - (n : ℝ) * Jh * Ih ^ (n - 1))).continuousOn
        have hmono : ∫ t in (0 : ℝ)..1, h t * ((u - t) * Ih ^ n - (n : ℝ) * Jh * Ih ^ (n - 1)) ≤
            ∫ t in (0 : ℝ)..1, h t * R n (u - t) :=
          intervalIntegral.integral_mono_on zero_le_one
            (hcont_lo.mono (by rw [Set.uIcc_of_le zero_le_one])).intervalIntegrable
            (hcont_hR.mono (by rw [Set.uIcc_of_le zero_le_one])).intervalIntegrable
            fun t ht => mul_le_mul_of_nonneg_left (ih (u - t) (by linarith [ht.1])) (hh_nn t ht)
        have hint_h : IntervalIntegrable h MeasureTheory.volume 0 1 :=
          (hh_cont.mono (by rw [Set.uIcc_of_le zero_le_one])).intervalIntegrable
        have hint_th : IntervalIntegrable (fun t => t * h t) MeasureTheory.volume 0 1 :=
          ((continuous_id.continuousOn.mul hh_cont).mono (by rw [Set.uIcc_of_le zero_le_one])).intervalIntegrable
        have heval : ∫ t in (0 : ℝ)..1, h t * ((u - t) * Ih ^ n - (n : ℝ) * Jh * Ih ^ (n - 1)) =
            u * Ih ^ (n + 1) - ((n + 1 : ℕ) : ℝ) * Jh * Ih ^ n := by
          have hrew : (fun t : ℝ => h t * ((u - t) * Ih ^ n - (n : ℝ) * Jh * Ih ^ (n - 1))) =
              (fun t : ℝ => (u * Ih ^ n - (n : ℝ) * Jh * Ih ^ (n - 1)) * h t - (Ih ^ n) * (t * h t)) := by
            funext t; ring
          rw [hrew, intervalIntegral.integral_sub (hint_h.const_mul _) (hint_th.const_mul _),
            intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
          dsimp only [Ih, Jh]
          rcases n with _ | n'
          · simp
          · simp only [Nat.add_sub_cancel]
            rw [pow_succ _ (n' + 1), pow_succ _ n']; push_cast; ring
        simp only [Nat.add_sub_cancel]
        linarith
      · dsimp only [R]; rw [if_neg hu0]
        push Not at hu0
        have h1 : u * Ih ^ (n + 1) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hu0.le (pow_nonneg hIh_nn _)
        have h2 : 0 ≤ ((n + 1 : ℕ) : ℝ) * Jh * Ih ^ n := by positivity
        simp only [Nat.add_sub_cancel]; linarith
  -- Apply `hgen m s hs1` and bound `R m s ≤ s * simplexIntegral m s (∏ h)`!
  have hm_lo := hgen m s hs1
  dsimp only [R] at hm_lo; rw [if_pos hs0.le] at hm_lo
  have hR_le : simplexIntegral m s (fun v => (s - ∑ i, v i) * ∏ i, h (v i)) ≤
      s * simplexIntegral m s (fun v => ∏ i, h (v i)) := by
    rw [← simplexIntegral_const_mul hs0.le]
    have hlip_p := isSimplexLipOn_prod m hs0.le hs1 hM hL hM1 hbd hlip
    have hlip_s : IsSimplexLipOn s 1 1 (fun v : Fin m → ℝ => s - ∑ i, v i) := by
      simpa using isSimplexLipOn_basis m 1 0 hs0.le hs1
    refine simplexIntegral_mono hs0.le hs1 (hlip_s.mul hlip_p) (hlip_p.const_mul s) fun v hv => ?_
    refine mul_le_mul_of_nonneg_right ?_ (Finset.prod_nonneg fun i _ =>
      hh_nn (v i) ⟨hv.1 i, le_trans (Finset.single_le_sum (fun j _ => hv.1 j) (Finset.mem_univ i)) (hv.2.trans hs1)⟩)
    linarith [Finset.sum_nonneg (s := Finset.univ) fun i _ => hv.1 i]
  have hdiv := div_le_div_of_nonneg_right (hm_lo.trans hR_le) hs0.le
  rw [mul_div_cancel_left₀ _ hs0.ne', sub_div, mul_div_cancel_left₀ _ hs0.ne'] at hdiv
  calc Ih ^ m - ((m : ℝ) / s) * Jh * Ih ^ (m - 1)
      = Ih ^ m - (m : ℝ) * Jh * Ih ^ (m - 1) / s := by ring
    _ ≤ simplexIntegral m s (fun v => ∏ i, h (v i)) := hdiv

/-- Explicit large-`k` test function `F(v) = ∏ i, (1 + 16 * (k + 1) * log (k + 1) * v i)⁻¹` on `Δ_{k+1}`. -/
def TLarge (k : ℕ) (hk : 99 ≤ k) : SimplexTestFn (k + 1) :=
  let lam : ℝ := 16 * ((k + 1 : ℕ) : ℝ) * Real.log ((k + 1 : ℕ) : ℝ)
  let g : ℝ → ℝ := fun t => (1 + lam * t)⁻¹
  have hlam_nn : 0 ≤ lam := by
    dsimp only [lam]
    have hk1 : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ k + 1 by omega)
    exact mul_nonneg (by positivity) (Real.log_nonneg hk1)
  have hg_bd : ∀ t ∈ Set.Icc (0 : ℝ) 1, |g t| ≤ 1 := fun t ht => by
    dsimp only [g]
    have h1 : 1 ≤ 1 + lam * t := by nlinarith [ht.1]
    rw [abs_of_nonneg (inv_nonneg.mpr (by linarith))]
    exact inv_le_one_of_one_le₀ h1
  have hg_lip : ∀ t₁ ∈ Set.Icc (0 : ℝ) 1, ∀ t₂ ∈ Set.Icc (0 : ℝ) 1, |g t₁ - g t₂| ≤ lam * |t₁ - t₂| := by
    intro t₁ ht₁ t₂ ht₂
    dsimp only [g]
    have h1 : 1 ≤ 1 + lam * t₁ := by nlinarith [ht₁.1]
    have h2 : 1 ≤ 1 + lam * t₂ := by nlinarith [ht₂.1]
    have hdiff : (1 + lam * t₁)⁻¹ - (1 + lam * t₂)⁻¹ = lam * (t₂ - t₁) / ((1 + lam * t₁) * (1 + lam * t₂)) := by
      field_simp [show 1 + lam * t₁ ≠ 0 by linarith, show 1 + lam * t₂ ≠ 0 by linarith]; ring
    rw [hdiff, abs_div, abs_mul, abs_of_nonneg hlam_nn, abs_sub_comm t₂ t₁,
      abs_of_nonneg (show 0 ≤ (1 + lam * t₁) * (1 + lam * t₂) by nlinarith)]
    exact div_le_self (mul_nonneg hlam_nn (abs_nonneg _)) (by nlinarith)
  have hlip := isSimplexLipOn_prod (k + 1) zero_le_one le_rfl zero_le_one hlam_nn le_rfl hg_bd hg_lip
  { F := fun v => ∏ i, g (v i)
    bound := 1
    lip := lam
    bound_nonneg := zero_le_one
    lip_nonneg := hlam_nn
    symm := fun σ v => Equiv.prod_comp σ (fun i => g (v i))
    abs_le := fun v hv0 hvs => hlip.2.2.1 v ⟨hv0, hvs⟩
    lipschitz := fun u v hu0 hus hv0 hvs => hlip.2.2.2 u v ⟨hu0, hus⟩ ⟨hv0, hvs⟩ }

/-- **Large-`k` Variational Ratio `M_{k+1} ≥ Real.log (k + 1) / 32`** for all `k ≥ 99`:
`0 < I_{k+1}(TLarge k)` and `(log (k + 1) / 32) * I_{k+1}(TLarge k) ≤ (k + 1) * J_k^{(0)}(TLarge k)`. -/
theorem maynard_large_k_ratio (k : ℕ) (hk : 99 ≤ k) :
    0 < maynardI (k + 1) (TLarge k hk).F ∧
      (Real.log ((k + 1 : ℕ) : ℝ) / 32) * maynardI (k + 1) (TLarge k hk).F ≤
        ((k + 1 : ℕ) : ℝ) * maynardJ0 k (TLarge k hk).F := by
  set K : ℝ := ((k + 1 : ℕ) : ℝ)
  have hK100 : (100 : ℝ) ≤ K := by dsimp only [K]; exact_mod_cast (show 100 ≤ k + 1 by omega)
  have hK_pos : 0 < K := by linarith
  have hlogK_ge4 : 4 ≤ Real.log K := by
    have h1 : Real.exp 4 ≤ (100 : ℝ) := by
      have he : Real.exp 1 ≤ 3 := by linarith [Real.exp_one_lt_d9]
      calc Real.exp 4 = (Real.exp 1) ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
        _ ≤ 3 ^ 4 := pow_le_pow_left₀ (Real.exp_pos 1).le he 4
        _ ≤ 100 := by norm_num
    have h2 := Real.log_le_log (Real.exp_pos 4) (h1.trans hK100)
    rwa [Real.log_exp] at h2
  have hlogK_pos : 0 < Real.log K := by linarith
  set lam : ℝ := 16 * K * Real.log K
  have hlam_pos : 0 < lam := by positivity
  have hlam_ge : 6400 ≤ lam := by dsimp only [lam]; nlinarith
  let g : ℝ → ℝ := fun t => (1 + lam * t)⁻¹
  let h : ℝ → ℝ := fun t => (1 + lam * t) ^ (-2 : ℤ)
  have hhg : ∀ t : ℝ, (g t) ^ 2 = h t := fun t => by
    dsimp only [g, h]; rw [zpow_neg, zpow_two, inv_pow, sq]
  have hh_nn : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ h t := fun t ht => by
    rw [← hhg t]; exact sq_nonneg _
  have hh_cont : ContinuousOn h (Set.Icc 0 1) := by
    have h1 : ContinuousOn (fun t : ℝ => (g t) ^ 2) (Set.Icc 0 1) := by
      refine ContinuousOn.pow (ContinuousOn.inv₀ (by fun_prop) fun t ht => ?_) 2
      have : 0 ≤ lam * t := mul_nonneg hlam_pos.le ht.1
      linarith
    exact h1.congr fun t _ => (hhg t).symm
  have hh_bd : ∀ t ∈ Set.Icc (0 : ℝ) 1, |h t| ≤ 1 := fun t ht => by
    rw [← hhg t, abs_of_nonneg (sq_nonneg _)]
    have h1 : 1 ≤ 1 + lam * t := by nlinarith [ht.1]
    have h2 : g t ≤ 1 := inv_le_one_of_one_le₀ h1
    nlinarith [inv_nonneg.mpr (by linarith : 0 ≤ 1 + lam * t)]
  have hh_lip : ∀ t₁ ∈ Set.Icc (0 : ℝ) 1, ∀ t₂ ∈ Set.Icc (0 : ℝ) 1, |h t₁ - h t₂| ≤ (2 * lam) * |t₁ - t₂| := by
    intro t₁ ht₁ t₂ ht₂
    rw [← hhg t₁, ← hhg t₂]
    have h1 : 1 ≤ 1 + lam * t₁ := by nlinarith [ht₁.1]
    have h2 : 1 ≤ 1 + lam * t₂ := by nlinarith [ht₂.1]
    have hg1 : 0 ≤ g t₁ ∧ g t₁ ≤ 1 := ⟨inv_nonneg.mpr (by linarith), inv_le_one_of_one_le₀ h1⟩
    have hg2 : 0 ≤ g t₂ ∧ g t₂ ≤ 1 := ⟨inv_nonneg.mpr (by linarith), inv_le_one_of_one_le₀ h2⟩
    have hdiff : g t₁ - g t₂ = lam * (t₂ - t₁) / ((1 + lam * t₁) * (1 + lam * t₂)) := by
      dsimp only [g]; field_simp [show 1 + lam * t₁ ≠ 0 by linarith, show 1 + lam * t₂ ≠ 0 by linarith]; ring
    have hdg : |g t₁ - g t₂| ≤ lam * |t₁ - t₂| := by
      rw [hdiff, abs_div, abs_mul, abs_of_nonneg hlam_pos.le, abs_sub_comm t₂ t₁,
        abs_of_nonneg (show 0 ≤ (1 + lam * t₁) * (1 + lam * t₂) by nlinarith)]
      exact div_le_self (mul_nonneg hlam_pos.le (abs_nonneg _)) (by nlinarith)
    have hrew : (g t₁) ^ 2 - (g t₂) ^ 2 = (g t₁ + g t₂) * (g t₁ - g t₂) := by ring
    rw [hrew, abs_mul, abs_of_nonneg (add_nonneg hg1.1 hg2.1)]
    calc (g t₁ + g t₂) * |g t₁ - g t₂| ≤ 2 * (lam * |t₁ - t₂|) :=
          mul_le_mul (by linarith) hdg (abs_nonneg _) (by norm_num)
      _ = (2 * lam) * |t₁ - t₂| := by ring
  -- Exact 1D integrals of `g` and `h = g^2`
  have hint_g : ∀ u : ℝ, 0 ≤ u → ∫ t in (0 : ℝ)..u, g t = Real.log (1 + lam * u) / lam := by
    intro u hu
    have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) u, HasDerivAt (fun x : ℝ => Real.log (1 + lam * x) / lam) (g t) t := by
      intro t ht; rw [Set.uIcc_of_le hu] at ht
      have hpos : 0 < 1 + lam * t := by nlinarith [ht.1]
      have h1 : HasDerivAt (fun x : ℝ => 1 + lam * x) lam t :=
        ((hasDerivAt_const t (1 : ℝ)).add ((hasDerivAt_id t).const_mul lam)).congr_deriv (by ring)
      have h2 := (h1.log hpos.ne').div_const lam
      refine h2.congr_deriv ?_
      dsimp only [g]; field_simp [hlam_pos.ne', hpos.ne']
    have hcont : ContinuousOn g (Set.uIcc 0 u) := by
      rw [Set.uIcc_of_le hu]
      refine ContinuousOn.inv₀ (by fun_prop) fun t ht => ?_
      have : 0 ≤ lam * t := mul_nonneg hlam_pos.le ht.1; linarith
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable]
    simp
  have hint_h : ∫ t in (0 : ℝ)..1, h t = (1 + lam)⁻¹ := by
    have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt (fun x : ℝ => -(lam * (1 + lam * x))⁻¹) (h t) t := by
      intro t ht; rw [Set.uIcc_of_le zero_le_one] at ht
      have hpos : 0 < 1 + lam * t := by nlinarith [ht.1]
      have h1 : HasDerivAt (fun x : ℝ => lam * (1 + lam * x)) (lam * lam) t := by
        have hlin : HasDerivAt (fun x : ℝ => 1 + lam * x) lam t :=
          ((hasDerivAt_const t (1 : ℝ)).add ((hasDerivAt_id t).const_mul lam)).congr_deriv (by ring)
        exact hlin.const_mul lam
      have h2 := (h1.inv (mul_pos hlam_pos hpos).ne').neg
      refine h2.congr_deriv ?_
      rw [← hhg t]; dsimp only [g]
      field_simp [hlam_pos.ne', hpos.ne']
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
      (hh_cont.mono (by rw [Set.uIcc_of_le zero_le_one])).intervalIntegrable]
    field_simp [hlam_pos.ne', show 1 + lam ≠ 0 by linarith]; ring
  have hint_th : ∫ t in (0 : ℝ)..1, t * h t ≤ Real.log (1 + lam) / lam ^ 2 := by
    have hcont_th : ContinuousOn (fun t : ℝ => t * h t) (Set.Icc 0 1) := continuous_id.continuousOn.mul hh_cont
    have hcont_g : ContinuousOn g (Set.Icc 0 1) := by
      refine ContinuousOn.inv₀ (by fun_prop) fun t ht => ?_
      have : 0 ≤ lam * t := mul_nonneg hlam_pos.le ht.1; linarith
    have hmono : ∫ t in (0 : ℝ)..1, t * h t ≤ ∫ t in (0 : ℝ)..1, lam⁻¹ * g t := by
      refine intervalIntegral.integral_mono_on zero_le_one
        (hcont_th.mono (by rw [Set.uIcc_of_le zero_le_one])).intervalIntegrable
        ((continuousOn_const.mul hcont_g).mono (by rw [Set.uIcc_of_le zero_le_one])).intervalIntegrable
        fun t ht => ?_
      rw [← hhg t]; dsimp only [g]
      have hpos : 0 < 1 + lam * t := by nlinarith [ht.1]
      have hstep : t * (1 + lam * t)⁻¹ ≤ lam⁻¹ := by
        rw [← div_eq_mul_inv, div_le_iff₀ hpos]
        calc t = lam⁻¹ * (lam * t) := by field_simp [hlam_pos.ne']
          _ ≤ lam⁻¹ * (1 + lam * t) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      calc t * ((1 + lam * t)⁻¹) ^ 2 = (t * (1 + lam * t)⁻¹) * (1 + lam * t)⁻¹ := by ring
        _ ≤ lam⁻¹ * (1 + lam * t)⁻¹ := mul_le_mul_of_nonneg_right hstep (by positivity)
    rw [intervalIntegral.integral_const_mul, hint_g 1 zero_le_one, mul_one] at hmono
    calc ∫ t in (0 : ℝ)..1, t * h t ≤ lam⁻¹ * (Real.log (1 + lam) / lam) := hmono
      _ = Real.log (1 + lam) / lam ^ 2 := by rw [sq]; ring
  -- Key log bound: `Real.log (1 + lam) ≤ 2 * Real.log K` (since `1 + 16 * K * log K ≤ K^2` for `K ≥ 100`!)
  have hlog_lam_le : Real.log (1 + lam) ≤ 2 * Real.log K := by
    have hlog_le_sqrt : Real.log K ≤ K / 20 := by
      have hlog100 : Real.log 100 ≤ 5 := by
        have he5 : (100 : ℝ) ≤ Real.exp 5 := by
          have he : (8 : ℝ) / 3 ≤ Real.exp 1 := by
            have := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 1 by norm_num) 4
            simp [Finset.sum_range_succ, Nat.factorial] at this; linarith
          calc (100 : ℝ) ≤ (8 / 3) ^ 5 := by norm_num
            _ ≤ (Real.exp 1) ^ 5 := pow_le_pow_left₀ (by norm_num) he 5
            _ = Real.exp 5 := by rw [← Real.exp_nat_mul]; norm_num
        have h1 := Real.log_le_log (by norm_num) he5
        rwa [Real.log_exp] at h1
      have hdiv : Real.log K = Real.log (K / 100) + Real.log 100 := by
        rw [Real.log_div hK_pos.ne' (by norm_num)]; ring
      have hle1 : Real.log (K / 100) ≤ K / 100 - 1 := Real.log_le_sub_one_of_pos (by positivity)
      linarith
    have h1 : 1 + lam ≤ K ^ 2 := by dsimp only [lam]; nlinarith
    calc Real.log (1 + lam) ≤ Real.log (K ^ 2) := Real.log_le_log (by linarith) h1
      _ = 2 * Real.log K := by rw [Real.log_pow]; ring
  -- (1) Upper bound `I_{k+1} ≤ (1 + lam)^(-(k+1))` and lower bound `I_{k+1} > 0`
  have hF_sq : (fun v : Fin (k + 1) → ℝ => ((TLarge k hk).F v) ^ 2) = (fun v => ∏ i, h (v i)) := by
    funext v; dsimp only [TLarge]; rw [← Finset.prod_pow]; exact Finset.prod_congr rfl fun i _ => hhg _
  have hI_up : maynardI (k + 1) (TLarge k hk).F ≤ ((1 + lam)⁻¹) ^ (k + 1) := by
    unfold maynardI; rw [hF_sq]
    have h1 := simplexIntegral_prod_le_pow (k + 1) hh_cont hh_nn zero_le_one (by positivity) le_rfl hh_bd hh_lip 1 zero_le_one le_rfl
    rwa [hint_h] at h1
  have hI_pos : 0 < maynardI (k + 1) (TLarge k hk).F := by
    unfold maynardI; rw [hF_sq]
    have hm := simplexIntegral_prod_markov (k + 1) hh_cont hh_nn zero_le_one (by positivity) le_rfl hh_bd hh_lip zero_lt_one le_rfl
    rw [hint_h, div_one] at hm
    have hsub : ((k + 1 : ℕ) : ℝ) * (∫ t in (0 : ℝ)..1, t * h t) * ((1 + lam)⁻¹) ^ k ≤
        (1 / 2) * ((1 + lam)⁻¹) ^ (k + 1) := by
      have h1 : K * (Real.log (1 + lam) / lam ^ 2) ≤ (1 / 2) * (1 + lam)⁻¹ := by
        have hkey : K * (Real.log (1 + lam) / lam ^ 2) * (2 * (1 + lam)) ≤ 1 := by
          have h1' : K * Real.log (1 + lam) * (2 * (1 + lam)) ≤ lam ^ 2 := by
            have ha : K * Real.log (1 + lam) * (2 * (1 + lam)) ≤ K * (2 * Real.log K) * (4 * lam) := by
              refine mul_le_mul (mul_le_mul_of_nonneg_left hlog_lam_le hK_pos.le) (by linarith) (by linarith) (by positivity)
            have hb : K * (2 * Real.log K) * (4 * lam) = lam ^ 2 / 2 := by dsimp only [lam]; ring
            nlinarith [sq_nonneg lam]
          calc K * (Real.log (1 + lam) / lam ^ 2) * (2 * (1 + lam))
              = (K * Real.log (1 + lam) * (2 * (1 + lam))) / lam ^ 2 := by ring
            _ ≤ lam ^ 2 / lam ^ 2 := div_le_div_of_nonneg_right h1' (sq_nonneg lam)
            _ = 1 := div_self (sq_pos_of_pos hlam_pos).ne'
        have hpos2 : 0 < 2 * (1 + lam) := by linarith
        calc K * (Real.log (1 + lam) / lam ^ 2)
            ≤ 1 / (2 * (1 + lam)) := (le_div_iff₀ hpos2).mpr hkey
          _ = (1 / 2) * (1 + lam)⁻¹ := by field_simp [show 1 + lam ≠ 0 by linarith]
      calc K * (∫ t in (0 : ℝ)..1, t * h t) * ((1 + lam)⁻¹) ^ k
          ≤ K * (Real.log (1 + lam) / lam ^ 2) * ((1 + lam)⁻¹) ^ k :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hint_th hK_pos.le) (by positivity)
        _ ≤ ((1 / 2) * (1 + lam)⁻¹) * ((1 + lam)⁻¹) ^ k :=
            mul_le_mul_of_nonneg_right h1 (by positivity)
        _ = (1 / 2) * ((1 + lam)⁻¹) ^ (k + 1) := by rw [pow_succ']; ring
    simp only [Nat.add_sub_cancel] at hm
    have hpos_pow : 0 < ((1 + lam)⁻¹) ^ (k + 1) := by positivity
    linarith
  -- (2) Lower bound `J_k^{(0)} ≥ (log (1 + lam / 2) / lam)^2 * (1/2) * (1 + lam)^(-k)`!
  have hJ_lo : (Real.log (1 + lam / 2) / lam) ^ 2 * ((1 / 2) * ((1 + lam)⁻¹) ^ k) ≤
      maynardJ0 k (TLarge k hk).F := by
    unfold maynardJ0
    -- Restrict outer simplex integral from `Δ_k(1)` to `Δ_k(1/2)` (monotone in `s` for nonnegative integrands!)
    have hmono_s : ∀ (m : ℕ) {G : (Fin m → ℝ) → ℝ} {sTop M L : ℝ}, sTop ≤ 1 →
        IsSimplexLipOn sTop M L G → (∀ v, InSimplex sTop v → 0 ≤ G v) →
        ∀ s₁ s₂ : ℝ, 0 ≤ s₁ → s₁ ≤ s₂ → s₂ ≤ sTop → simplexIntegral m s₁ G ≤ simplexIntegral m s₂ G := by
      intro m
      induction m with
      | zero => intro G sTop M L _ _ _ s₁ s₂ _ _ _; simp [simplexIntegral]
      | succ m ihm =>
        intro G sTop M L hsTop hG hGnn s₁ s₂ hs1 hs12 hs2
        unfold simplexIntegral
        have hI1 := intervalIntegrable_simplex_slice hs1 ((hs12.trans hs2).trans hsTop) (hG.mono (hs12.trans hs2))
        have hI2 := intervalIntegrable_simplex_slice (hs1.trans hs12) (hs2.trans hsTop) (hG.mono hs2)
        have hI2a : IntervalIntegrable (fun t => simplexIntegral m (s₂ - t) (fun v => G (Fin.cons t v)))
            MeasureTheory.volume 0 s₁ :=
          hI2.mono_set (by rw [Set.uIcc_of_le hs1, Set.uIcc_of_le (hs1.trans hs12)]; exact Set.Icc_subset_Icc_right hs12)
        have hI2b : IntervalIntegrable (fun t => simplexIntegral m (s₂ - t) (fun v => G (Fin.cons t v)))
            MeasureTheory.volume s₁ s₂ :=
          hI2.mono_set (by rw [Set.uIcc_of_le hs12, Set.uIcc_of_le (hs1.trans hs12)]; exact Set.Icc_subset_Icc_left hs1)
        have hpart1 : ∫ t in (0 : ℝ)..s₁, simplexIntegral m (s₁ - t) (fun v => G (Fin.cons t v)) ≤
            ∫ t in (0 : ℝ)..s₁, simplexIntegral m (s₂ - t) (fun v => G (Fin.cons t v)) :=
          intervalIntegral.integral_mono_on hs1 hI1 hI2a fun t ht =>
            ihm (by linarith [ht.1]) (hG.cons ht.1)
              (fun v hv => hGnn _ (inSimplex_cons ht.1 hv))
              (s₁ - t) (s₂ - t) (by linarith [ht.2]) (by linarith) (by linarith)
        have hpart2 : 0 ≤ ∫ t in s₁..s₂, simplexIntegral m (s₂ - t) (fun v => G (Fin.cons t v)) :=
          intervalIntegral.integral_nonneg hs12 fun t ht =>
            simplexIntegral_nonneg (by linarith [ht.2])
              (fun v hv => hGnn _ (inSimplex_cons (hs1.trans ht.1) (inSimplex_mono (by linarith) hv)))
        have hadd := intervalIntegral.integral_add_adjacent_intervals hI2a hI2b
        linarith
    have hGe_half : simplexIntegral k (1 / 2) (fun v => (∫ t in (0 : ℝ)..(1 - ∑ i, v i), (TLarge k hk).F (Fin.cons t v)) ^ 2) ≤
        simplexIntegral k 1 (fun v => (∫ t in (0 : ℝ)..(1 - ∑ i, v i), (TLarge k hk).F (Fin.cons t v)) ^ 2) :=
      hmono_s k le_rfl (TLarge k hk).isSimplexLipOn.innerIntegral.sq (fun _ _ => sq_nonneg _) (1 / 2) 1 (by norm_num) (by norm_num) le_rfl
    -- On `Δ_k(1/2)`, `1 - ∑ v_i ≥ 1/2`, so the inner integral is `≥ (log (1 + lam / 2) / lam) * ∏ g (v i)`!
    have hpt_half : ∀ v : Fin k → ℝ, InSimplex (1 / 2) v →
        (Real.log (1 + lam / 2) / lam) ^ 2 * ∏ i, h (v i) ≤
        (∫ t in (0 : ℝ)..(1 - ∑ i, v i), (TLarge k hk).F (Fin.cons t v)) ^ 2 := by
      intro v hv
      have hu : (1 / 2 : ℝ) ≤ 1 - ∑ i, v i := by linarith [hv.2]
      have hfactor : ∫ t in (0 : ℝ)..(1 - ∑ i, v i), (TLarge k hk).F (Fin.cons t v) =
          (∏ i : Fin k, g (v i)) * ∫ t in (0 : ℝ)..(1 - ∑ i, v i), g t := by
        have hfn : (fun t : ℝ => (TLarge k hk).F (Fin.cons t v)) =
            (fun t : ℝ => (∏ i : Fin k, g (v i)) * g t) := by
          funext t; dsimp only [TLarge]; rw [Fin.prod_univ_succ]; simp only [Fin.cons_zero, Fin.cons_succ]; ring
        rw [hfn, intervalIntegral.integral_const_mul]
      rw [hfactor, hint_g (1 - ∑ i, v i) (by linarith), mul_pow, ← Finset.prod_pow,
        Finset.prod_congr rfl fun i _ => hhg (v i), mul_comm]
      refine mul_le_mul_of_nonneg_left ?_ (Finset.prod_nonneg fun i _ => hh_nn (v i)
        ⟨hv.1 i, le_trans (Finset.single_le_sum (fun j _ => hv.1 j) (Finset.mem_univ i)) (by linarith [hv.2])⟩)
      have hlog_mono : Real.log (1 + lam / 2) ≤ Real.log (1 + lam * (1 - ∑ i, v i)) :=
        Real.log_le_log (by linarith) (by nlinarith)
      have hlog_nn : 0 ≤ Real.log (1 + lam / 2) := Real.log_nonneg (by linarith)
      exact pow_le_pow_left₀ (div_nonneg hlog_nn hlam_pos.le)
        (div_le_div_of_nonneg_right hlog_mono hlam_pos.le) 2
    have hmono_pt : (Real.log (1 + lam / 2) / lam) ^ 2 * simplexIntegral k (1 / 2) (fun v => ∏ i, h (v i)) ≤
        simplexIntegral k (1 / 2) (fun v => (∫ t in (0 : ℝ)..(1 - ∑ i, v i), (TLarge k hk).F (Fin.cons t v)) ^ 2) := by
      rw [← simplexIntegral_const_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      exact simplexIntegral_mono (by norm_num) (by norm_num)
        ((isSimplexLipOn_prod k (by norm_num) (by norm_num) zero_le_one (by positivity) le_rfl hh_bd hh_lip).const_mul _)
        ((TLarge k hk).isSimplexLipOn.innerIntegral.sq.mono (by norm_num)) hpt_half
    -- Apply `simplexIntegral_prod_markov` at `m = k`, `s = 1 / 2`!
    have hmark := simplexIntegral_prod_markov k hh_cont hh_nn zero_le_one (by positivity) le_rfl hh_bd hh_lip
      (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
    rw [hint_h] at hmark
    have hsub_half : ((k : ℝ) / (1 / 2)) * (∫ t in (0 : ℝ)..1, t * h t) * ((1 + lam)⁻¹) ^ (k - 1) ≤
        (1 / 2) * ((1 + lam)⁻¹) ^ k := by
      have hk1 : 1 ≤ k := by omega
      have h1 : (2 * (k : ℝ)) * (Real.log (1 + lam) / lam ^ 2) ≤ (1 / 2) * (1 + lam)⁻¹ := by
        have hpos2 : 0 < 2 * (1 + lam) := by linarith
        have hkey : (2 * (k : ℝ)) * (Real.log (1 + lam) / lam ^ 2) * (2 * (1 + lam)) ≤ 1 := by
          have hkK : (k : ℝ) ≤ K := by dsimp only [K]; exact_mod_cast Nat.le_succ k
          have h1' : (2 * (k : ℝ)) * Real.log (1 + lam) * (2 * (1 + lam)) ≤ lam ^ 2 := by
            have ha : (2 * (k : ℝ)) * Real.log (1 + lam) * (2 * (1 + lam)) ≤ (2 * K) * (2 * Real.log K) * (4 * lam) := by
              refine mul_le_mul (mul_le_mul (by linarith) hlog_lam_le (Real.log_nonneg (by linarith)) (by positivity))
                (by linarith) (by linarith) (by positivity)
            have hb : (2 * K) * (2 * Real.log K) * (4 * lam) = lam ^ 2 := by dsimp only [lam]; ring
            linarith
          calc (2 * (k : ℝ)) * (Real.log (1 + lam) / lam ^ 2) * (2 * (1 + lam))
              = ((2 * (k : ℝ)) * Real.log (1 + lam) * (2 * (1 + lam))) / lam ^ 2 := by ring
            _ ≤ lam ^ 2 / lam ^ 2 := div_le_div_of_nonneg_right h1' (sq_nonneg lam)
            _ = 1 := div_self (sq_pos_of_pos hlam_pos).ne'
        calc (2 * (k : ℝ)) * (Real.log (1 + lam) / lam ^ 2)
            ≤ 1 / (2 * (1 + lam)) := (le_div_iff₀ hpos2).mpr hkey
          _ = (1 / 2) * (1 + lam)⁻¹ := by field_simp [show 1 + lam ≠ 0 by linarith]
      calc ((k : ℝ) / (1 / 2)) * (∫ t in (0 : ℝ)..1, t * h t) * ((1 + lam)⁻¹) ^ (k - 1)
          = (2 * (k : ℝ)) * (∫ t in (0 : ℝ)..1, t * h t) * ((1 + lam)⁻¹) ^ (k - 1) := by ring
        _ ≤ (2 * (k : ℝ)) * (Real.log (1 + lam) / lam ^ 2) * ((1 + lam)⁻¹) ^ (k - 1) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hint_th (by positivity)) (by positivity)
        _ ≤ ((1 / 2) * (1 + lam)⁻¹) * ((1 + lam)⁻¹) ^ (k - 1) :=
            mul_le_mul_of_nonneg_right h1 (by positivity)
        _ = (1 / 2) * ((1 + lam)⁻¹) ^ k := by rw [mul_assoc, ← pow_succ', Nat.sub_add_cancel hk1]
    have hsimp_lo : (1 / 2) * ((1 + lam)⁻¹) ^ k ≤ simplexIntegral k (1 / 2) (fun v => ∏ i, h (v i)) := by linarith
    have hmul := mul_le_mul_of_nonneg_left hsimp_lo (sq_nonneg (Real.log (1 + lam / 2) / lam))
    linarith
  -- (3) Combine `hI_up` and `hJ_lo`: `(log K / 32) * I_{k+1} ≤ K * J_k^{(0)}`!
  have hlog_half_ge : Real.log K ≤ Real.log (1 + lam / 2) :=
    Real.log_le_log hK_pos (by dsimp only [lam]; nlinarith)
  have hratio_step : (Real.log K / 32) * ((1 + lam)⁻¹) ^ (k + 1) ≤
      K * ((Real.log (1 + lam / 2) / lam) ^ 2 * ((1 / 2) * ((1 + lam)⁻¹) ^ k)) := by
    have h1 : (Real.log K / 32) * (1 + lam)⁻¹ ≤ K * ((Real.log (1 + lam / 2) / lam) ^ 2 * (1 / 2)) := by
      have hsq : (Real.log K) ^ 2 ≤ (Real.log (1 + lam / 2)) ^ 2 :=
        pow_le_pow_left₀ hlogK_pos.le hlog_half_ge 2
      have hlam_inv : (1 + lam)⁻¹ ≤ lam⁻¹ := inv_anti₀ hlam_pos (by linarith)
      calc (Real.log K / 32) * (1 + lam)⁻¹
          ≤ (Real.log K / 32) * lam⁻¹ := mul_le_mul_of_nonneg_left hlam_inv (by positivity)
        _ = K * (((Real.log K) ^ 2 / lam ^ 2) * (1 / 2)) := by
            dsimp only [lam]; field_simp [hK_pos.ne', hlogK_pos.ne']; ring
        _ ≤ K * (((Real.log (1 + lam / 2)) ^ 2 / lam ^ 2) * (1 / 2)) := by gcongr
        _ = K * ((Real.log (1 + lam / 2) / lam) ^ 2 * (1 / 2)) := by rw [div_pow]
    calc (Real.log K / 32) * ((1 + lam)⁻¹) ^ (k + 1)
        = ((Real.log K / 32) * (1 + lam)⁻¹) * ((1 + lam)⁻¹) ^ k := by rw [pow_succ']; ring
      _ ≤ (K * ((Real.log (1 + lam / 2) / lam) ^ 2 * (1 / 2))) * ((1 + lam)⁻¹) ^ k :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = K * ((Real.log (1 + lam / 2) / lam) ^ 2 * ((1 / 2) * ((1 + lam)⁻¹) ^ k)) := by ring
  refine ⟨hI_pos, ?_⟩
  calc (Real.log K / 32) * maynardI (k + 1) (TLarge k hk).F
      ≤ (Real.log K / 32) * ((1 + lam)⁻¹) ^ (k + 1) :=
        mul_le_mul_of_nonneg_left hI_up (by positivity)
    _ ≤ K * ((Real.log (1 + lam / 2) / lam) ^ 2 * ((1 / 2) * ((1 + lam)⁻¹) ^ k)) := hratio_step
    _ ≤ K * maynardJ0 k (TLarge k hk).F := mul_le_mul_of_nonneg_left hJ_lo hK_pos.le

/-! ## Section 4: Unconditional Crown Theorems (H ≤ 600 & Arbitrary m-Tuples!) -/

/-- **UNCONDITIONAL DISCHARGE OF `AnalyticCore mtTuple105` (0 assumptions, 0 sorry)**. -/
def maynard_tao_analyticCore_105 : AnalyticCore mtTuple105 :=
  analyticCore_of_mAnalyticCore_two
    (maynard_tao_sieve_core mtTuple105_admissible mtTuple105_card 1 T105
      maynard_105_ratio_gt_four.1 (by simpa using maynard_105_ratio_gt_four.2))

/-- **UNCONDITIONAL MAYNARD–TAO THEOREM (`H ≤ 600`, Maynard 2015 Theorem 1.1)**:
discharging `MaynardTaoReduction.maynard_tao_600_of_core` unconditionally! -/
theorem maynard_tao_600_unconditional :
    ∃ H : ℕ, H ≤ 600 ∧
      ∀ N : ℕ, ∃ p q : ℕ, N ≤ p ∧ p < q ∧ Nat.Prime p ∧ Nat.Prime q ∧ q - p ≤ H :=
  maynard_tao_600_of_core maynard_tao_analyticCore_105

/-- **CROWN THEOREM 1 — UNCONDITIONAL BOUNDED GAPS BETWEEN PRIMES (`q - p ≤ 600`)**:
for every `N : ℕ`, there exist primes `N ≤ p < q` with `q - p ≤ 600`. -/
theorem maynard_tao_bounded_gaps_unconditional :
    ∀ N : ℕ, ∃ p q : ℕ, N ≤ p ∧ Nat.Prime p ∧ Nat.Prime q ∧ p < q ∧ q - p ≤ 600 := by
  obtain ⟨H, hH600, hbound⟩ := maynard_tao_600_unconditional
  intro N
  obtain ⟨p, q, hpN, hpq, hp, hq, hgap⟩ := hbound N
  exact ⟨p, q, hpN, hp, hq, hpq, hgap.trans hH600⟩

/-- **CROWN THEOREM 2 — UNCONDITIONAL ARBITRARY `m`-TUPLES OF PRIMES IN BOUNDED INTERVALS**
(Maynard 2015 Theorem 1.2 / Tao 2013):
for every `m ≥ 1`, there exists `H : ℕ` such that for every `N : ℕ`, there is a set `S` of `m`
primes `≥ N` all within diameter `H` (`∀ p ∈ S, ∀ q ∈ S, p ≤ q + H`). -/
theorem maynard_tao_m_tuples_unconditional (m : ℕ) (hm : 1 ≤ m) :
    ∃ H : ℕ, ∀ N : ℕ, ∃ S : Finset ℕ, S.card = m ∧ (∀ p ∈ S, N ≤ p ∧ Nat.Prime p) ∧
      ∀ p ∈ S, ∀ q ∈ S, p ≤ q + H := by
  -- Choose `k ≥ 99` large enough that `log (k + 1) / 32 > 4 * (m - 1)`, i.e. `k + 1 > exp (128 * m + 1)`!
  set k : ℕ := max 99 (Nat.ceil (Real.exp (128 * (m : ℝ) + 1)))
  have hk99 : 99 ≤ k := le_max_left _ _
  have hK_gt : Real.exp (128 * (m : ℝ) + 1) < ((k + 1 : ℕ) : ℝ) := by
    have h1 : Real.exp (128 * (m : ℝ) + 1) ≤ (k : ℝ) :=
      (Nat.le_ceil _).trans (by dsimp only [k]; exact_mod_cast le_max_right 99 (Nat.ceil (Real.exp (128 * (m : ℝ) + 1))))
    push_cast; linarith
  have hlogK_gt : 128 * (m : ℝ) + 1 < Real.log ((k + 1 : ℕ) : ℝ) := by
    have h1 := Real.log_lt_log (Real.exp_pos _) hK_gt
    rwa [Real.log_exp] at h1
  obtain ⟨H_tup, hH_card, hH_adm⟩ := exists_admissible_card (k + 1) (by omega)
  have hH_ne : H_tup.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨hI_pos, hratio_ge⟩ := maynard_large_k_ratio k hk99
  have hratio_strict : 4 * ((m - 1 : ℕ) : ℝ) * maynardI (k + 1) (TLarge k hk99).F <
      ((k + 1 : ℕ) : ℝ) * maynardJ0 k (TLarge k hk99).F := by
    have hlt : 4 * ((m - 1 : ℕ) : ℝ) < Real.log ((k + 1 : ℕ) : ℝ) / 32 := by
      have hm1 : ((m - 1 : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast Nat.sub_le m 1
      linarith
    exact (mul_lt_mul_of_pos_right hlt hI_pos).trans_le hratio_ge
  let hcore_m : MAnalyticCore H_tup m :=
    Nat.sub_add_cancel hm ▸ maynard_tao_sieve_core hH_adm hH_card (m - 1) (TLarge k hk99) hI_pos hratio_strict
  obtain ⟨H', _, hH'⟩ := bounded_m_tuples_of_analyticCore hH_ne hm hcore_m
  refine ⟨H', fun N => ?_⟩
  obtain ⟨L, hNL, P, hPcard, hPprime, hPbd⟩ := hH' N
  refine ⟨P, hPcard, fun p hp => ⟨hNL.trans (hPbd p hp).1, hPprime p hp⟩, fun p hp q hq => ?_⟩
  have hp_bd := hPbd p hp
  have hq_bd := hPbd q hq
  omega

end RHDirect.MaynardTao
