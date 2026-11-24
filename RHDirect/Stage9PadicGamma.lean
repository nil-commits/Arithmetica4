import RHDirect.Stage7PadicLFunction
import RHDirect.Stage2DworkExp
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.NumberTheory.Padics.MahlerBasis
import Mathlib.Data.ZMod.Units
import Mathlib.Topology.UniformSpace.UniformConvergence

/-!
# RHDirect.Stage9PadicGamma

Unconditional Lean 4 formalization (zero `sorry`, zero custom `axiom`s) of:

1. **Mahler's 1958 Expansion Theorem on `C(ℤ_[p], ℚ_[p])`**:
   - Forward difference operator `mahlerDiff f n = ∑_{k=0}^n (-1)^(n-k) C(n, k) f(k)`.
   - Exact Newton interpolation identity `f(m) = ∑_{k=0}^m (mahlerDiff f k) * C(m, k)`.
   - Mahler's coefficient decay theorem `tendsto_mahlerDiff_zero_of_continuous`:
     for every continuous `f : ℤ_[p] → ℚ_[p]`, `mahlerDiff f n → 0` as `n → ∞`.
   - Unconditional Mahler expansion `mahler_expansion_eq`:
     `HasSum (fun n => mahlerDiff f n * (mahlerBinom n x : ℚ_[p])) (f x)` for all `x : ℤ_[p]`.
   - Exact ultrametric isometry `supNorm_eq_sup_mahlerDiff`:
     `⨆ x : ℤ_[p], ‖f x‖ = ⨆ n : ℕ, ‖mahlerDiff f n‖`.

2. **Morita's 1975 $p$-adic Gamma Function `Γ_p : ℤ_[p] → ℤ_[p]`**:
   - Integer formula `moritaGammaNat p n = (-1)^n * ∏_{1 ≤ k < n, p ∤ k} k`.
   - Gauss–Wilson product of units modulo prime powers `p^r` (both odd `p` with `r ≥ 1` and
     `p = 2` with `r ≥ 3`).
   - Morita's fundamental congruence `moritaGammaNat_congr_mod_pow` (for odd `p`, all `r`) and
     `moritaGammaNat_congr_mod_two_pow` (for `p = 2`, `r ≥ 3`).
   - Concrete continuous extension `padicGamma p : ℤ_[p] → ℤ_[p]` with:
     - `continuous_padicGamma` & 1-Lipschitz bound `norm_padicGamma_sub_le` (for odd `p`).
     - `padicGamma_nat`, `padicGamma_zero`, `padicGamma_one`, `padicGamma_two`.
     - `padicGamma_unit` (`∀ x, ‖padicGamma p x‖ = 1`).
     - Morita's functional equation `padicGamma_add_one`.
     - Morita's reflection formula `padicGamma_mul_one_sub` for odd `p`.
     - Exact value at `1/2`: `padicGamma_half_sq` (`(Γ_p(1/2))^2 = (-1)^((p+1)/2)`).
-/

noncomputable section

open scoped BigOperators Topology
open Finset Filter Topology RHDirect.Stage2IwasawaTwoTower RHDirect.Stage7PadicLFunction RHDirect.Stage2DworkExp

namespace RHDirect.Stage9PadicGamma

/-! ## Section 1: Unconditional Mahler's 1958 Expansion Theorem on `C(ℤ_[p], ℚ_[p])` -/

section MahlerExpansion

variable {p : ℕ} [Fact p.Prime]

/-- One-step forward difference operator `(Δ f)(x) = f(x + 1) - f(x)` on `ℤ_[p] → ℚ_[p]`. -/
def forwardDiff (f : ℤ_[p] → ℚ_[p]) : ℤ_[p] → ℚ_[p] :=
  fun x => f (x + 1) - f x

/-- The `n`-th Mahler forward-difference coefficient
`Δ^n f(0) = ∑_{k=0}^n (-1)^(n - k) * C(n, k) * f(k)`. -/
def mahlerDiff (f : ℤ_[p] → ℚ_[p]) (n : ℕ) : ℚ_[p] :=
  ∑ k ∈ Finset.range (n + 1),
    (-1 : ℚ_[p]) ^ (n - k) * (n.choose k : ℚ_[p]) * f (k : ℤ_[p])

/-- Explicit binomial formula for the `n`-th iterated forward difference `(Δ^n f)(x)`. -/
theorem iter_forwardDiff_eq (f : ℤ_[p] → ℚ_[p]) (n : ℕ) (x : ℤ_[p]) :
    (forwardDiff^[n] f) x =
      ∑ k ∈ Finset.range (n + 1),
        (-1 : ℚ_[p]) ^ (n - k) * (n.choose k : ℚ_[p]) * f (x + (k : ℤ_[p])) := by
  induction n generalizing x with
  | zero =>
    simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', forwardDiff, ih (x + 1), ih x]
    have hshift :
        ∑ k ∈ Finset.range (n + 1),
          (-1 : ℚ_[p]) ^ (n - k) * (n.choose k : ℚ_[p]) * f (x + 1 + (k : ℤ_[p])) =
        ∑ k ∈ Finset.range (n + 1),
          (-1 : ℚ_[p]) ^ (n - k) * (n.choose k : ℚ_[p]) * f (x + ((k + 1 : ℕ) : ℤ_[p])) := by
      refine Finset.sum_congr rfl fun k _ => ?_
      congr 2
      push_cast
      ring
    rw [hshift]
    conv_rhs => rw [Finset.sum_range_succ, Finset.sum_range_succ']
    have hsplit_left :
        ∑ k ∈ Finset.range (n + 1),
          (-1 : ℚ_[p]) ^ (n - k) * (n.choose k : ℚ_[p]) * f (x + ((k + 1 : ℕ) : ℤ_[p])) =
        (∑ k ∈ Finset.range n,
          (-1 : ℚ_[p]) ^ (n - k) * (n.choose k : ℚ_[p]) * f (x + ((k + 1 : ℕ) : ℤ_[p]))) +
        f (x + ((n + 1 : ℕ) : ℤ_[p])) := by
      rw [Finset.sum_range_succ]
      simp
    have hsplit_right :
        ∑ k ∈ Finset.range (n + 1),
          (-1 : ℚ_[p]) ^ (n - k) * (n.choose k : ℚ_[p]) * f (x + (k : ℤ_[p])) =
        (∑ k ∈ Finset.range n,
          (-1 : ℚ_[p]) ^ (n - (k + 1)) * (n.choose (k + 1) : ℚ_[p]) *
            f (x + ((k + 1 : ℕ) : ℤ_[p]))) +
        (-1 : ℚ_[p]) ^ n * f x := by
      rw [Finset.sum_range_succ']
      simp
    rw [hsplit_left, hsplit_right]
    have hmid :
        (∑ k ∈ Finset.range n,
          (-1 : ℚ_[p]) ^ (n - k) * (n.choose k : ℚ_[p]) * f (x + ((k + 1 : ℕ) : ℤ_[p]))) -
        (∑ k ∈ Finset.range n,
          (-1 : ℚ_[p]) ^ (n - (k + 1)) * (n.choose (k + 1) : ℚ_[p]) *
            f (x + ((k + 1 : ℕ) : ℤ_[p]))) =
        ∑ k ∈ Finset.range n,
          (-1 : ℚ_[p]) ^ (n + 1 - (k + 1)) * ((n + 1).choose (k + 1) : ℚ_[p]) *
            f (x + ((k + 1 : ℕ) : ℤ_[p])) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun k hk => ?_
      have hkn : k < n := Finset.mem_range.mp hk
      have hsub : n - k = (n - (k + 1)) + 1 := by omega
      have hsub2 : n + 1 - (k + 1) = n - k := by omega
      have hch : (((n + 1).choose (k + 1) : ℕ) : ℚ_[p]) =
          (n.choose k : ℚ_[p]) + (n.choose (k + 1) : ℚ_[p]) := by
        rw [Nat.choose_succ_succ, Nat.succ_eq_add_one, Nat.cast_add]
      rw [hsub2, hch, hsub, pow_succ]
      ring
    have hgoal_mid :
        ∑ k ∈ Finset.range n,
          (-1 : ℚ_[p]) ^ (n + 1 - (k + 1)) * ((n + 1).choose (k + 1) : ℚ_[p]) *
            f (x + ((k + 1 : ℕ) : ℤ_[p])) =
        ∑ k ∈ Finset.range n,
          (-1 : ℚ_[p]) ^ (n - k) * (n.choose k : ℚ_[p]) * f (x + ((k + 1 : ℕ) : ℤ_[p])) -
        ∑ k ∈ Finset.range n,
          (-1 : ℚ_[p]) ^ (n - (k + 1)) * (n.choose (k + 1) : ℚ_[p]) *
            f (x + ((k + 1 : ℕ) : ℤ_[p])) := hmid.symm
    rw [hgoal_mid]
    simp only [Nat.sub_self, pow_zero, Nat.choose_self, Nat.cast_one, one_mul,
      Nat.sub_zero, Nat.choose_zero_right, Nat.cast_zero, add_zero, mul_one, pow_succ]
    ring

lemma iter_forwardDiff_zero_eq_mahlerDiff (f : ℤ_[p] → ℚ_[p]) (n : ℕ) :
    (forwardDiff^[n] f) 0 = mahlerDiff f n := by
  rw [iter_forwardDiff_eq]
  simp [mahlerDiff]

/-- Shifted Newton interpolation identity:
`f(x + m) = ∑_{k=0}^m (Δ^k f)(x) * C(m, k)`. -/
theorem newton_interpolation_shift (f : ℤ_[p] → ℚ_[p]) (m : ℕ) (x : ℤ_[p]) :
    f (x + (m : ℤ_[p])) =
      ∑ k ∈ Finset.range (m + 1), (forwardDiff^[k] f) x * (m.choose k : ℚ_[p]) := by
  induction m generalizing f with
  | zero =>
    simp
  | succ m ih =>
    have hstep : f (x + ((m + 1 : ℕ) : ℤ_[p])) =
        f (x + (m : ℤ_[p])) + forwardDiff f (x + (m : ℤ_[p])) := by
      unfold forwardDiff
      have heq : x + ((m + 1 : ℕ) : ℤ_[p]) = x + (m : ℤ_[p]) + 1 := by push_cast; ring
      rw [heq]
      ring
    rw [hstep, ih f, ih (forwardDiff f)]
    have hiter : ∀ k : ℕ, (forwardDiff^[k] (forwardDiff f)) x = (forwardDiff^[k + 1] f) x := by
      intro k
      rw [← Function.iterate_succ_apply]
    simp_rw [hiter]
    conv_rhs => rw [Finset.sum_range_succ, Finset.sum_range_succ']
    have hleft :
        ∑ k ∈ Finset.range (m + 1), (forwardDiff^[k] f) x * (m.choose k : ℚ_[p]) =
        (∑ k ∈ Finset.range m, (forwardDiff^[k + 1] f) x * (m.choose (k + 1) : ℚ_[p])) +
          f x := by
      rw [Finset.sum_range_succ']
      simp
    have hright :
        ∑ k ∈ Finset.range (m + 1), (forwardDiff^[k + 1] f) x * (m.choose k : ℚ_[p]) =
        (∑ k ∈ Finset.range m, (forwardDiff^[k + 1] f) x * (m.choose k : ℚ_[p])) +
          (forwardDiff^[m + 1] f) x := by
      rw [Finset.sum_range_succ]
      simp
    rw [hleft, hright]
    have hcomb :
        (∑ k ∈ Finset.range m, (forwardDiff^[k + 1] f) x * (m.choose (k + 1) : ℚ_[p])) +
        (∑ k ∈ Finset.range m, (forwardDiff^[k + 1] f) x * (m.choose k : ℚ_[p])) =
        ∑ k ∈ Finset.range m, (forwardDiff^[k + 1] f) x * ((m + 1).choose (k + 1) : ℚ_[p]) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Nat.choose_succ_succ, Nat.cast_add]
      ring
    rw [← hcomb]
    simp only [Nat.choose_self, Nat.choose_zero_right, Nat.cast_one, mul_one,
      Function.iterate_zero_apply]
    ring

/-- **Exact Newton Interpolation Identity**:
for every function `f : ℤ_[p] → ℚ_[p]` and every `m : ℕ`,
`f(m) = ∑_{k=0}^m (mahlerDiff f k) * C(m, k)`. -/
theorem newton_interpolation (f : ℤ_[p] → ℚ_[p]) (m : ℕ) :
    f (m : ℤ_[p]) = ∑ k ∈ Finset.range (m + 1), mahlerDiff f k * (m.choose k : ℚ_[p]) := by
  have h := newton_interpolation_shift f m 0
  rw [zero_add] at h
  rw [h]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [iter_forwardDiff_zero_eq_mahlerDiff]

lemma norm_forwardDiff_le {f : ℤ_[p] → ℚ_[p]} {B : ℝ}
    (hf : ∀ x : ℤ_[p], ‖f x‖ ≤ B) (x : ℤ_[p]) :
    ‖forwardDiff f x‖ ≤ B := by
  unfold forwardDiff
  rw [sub_eq_add_neg]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans
    (max_le (hf (x + 1)) (by simpa [norm_neg] using hf x))

lemma norm_iter_forwardDiff_le {f : ℤ_[p] → ℚ_[p]} {B : ℝ}
    (hf : ∀ x : ℤ_[p], ‖f x‖ ≤ B) (n : ℕ) (x : ℤ_[p]) :
    ‖(forwardDiff^[n] f) x‖ ≤ B := by
  induction n generalizing x with
  | zero => exact hf x
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact norm_forwardDiff_le ih x

lemma iter_forwardDiff_shift_sub (f : ℤ_[p] → ℚ_[p]) (a : ℤ_[p]) (n : ℕ) (x : ℤ_[p]) :
    (forwardDiff^[n] (fun y => f (y + a) - f y)) x =
      (forwardDiff^[n] f) (x + a) - (forwardDiff^[n] f) x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    simp only [Function.iterate_succ_apply', forwardDiff]
    rw [ih (x + 1), ih x]
    have h1 : x + 1 + a = x + a + 1 := by ring
    rw [h1]
    ring

lemma padic_norm_intCast_le_one (z : ℤ) : ‖(z : ℚ_[p])‖ ≤ 1 := by
  have hcast : (z : ℚ_[p]) = ((z : ℤ_[p]) : ℚ_[p]) := by simp
  rw [hcast]
  exact PadicInt.norm_le_one (z : ℤ_[p])

lemma padic_norm_natCast_le_one (m : ℕ) : ‖(m : ℚ_[p])‖ ≤ 1 := by
  simpa using padic_norm_intCast_le_one (p := p) (m : ℤ)

lemma padic_norm_intCast_le_inv_of_dvd {z : ℤ} (h : (p : ℤ) ∣ z) :
    ‖(z : ℚ_[p])‖ ≤ (p : ℝ)⁻¹ := by
  obtain ⟨q, rfl⟩ := h
  rw [Int.cast_mul, Int.cast_natCast, norm_mul, Padic.norm_p]
  exact (mul_le_mul_of_nonneg_left (padic_norm_intCast_le_one q) (by positivity)).trans (mul_one _).le

lemma padic_norm_natCast_le_inv_of_dvd {m : ℕ} (h : p ∣ m) :
    ‖(m : ℚ_[p])‖ ≤ (p : ℝ)⁻¹ := by
  have hz : (p : ℤ) ∣ (m : ℤ) := Int.natCast_dvd_natCast.mpr h
  simpa using padic_norm_intCast_le_inv_of_dvd (p := p) hz

/-- Key one-step $p$-adic contraction for `Δ^(p^r)`:
if `‖g‖_∞ ≤ B` and `‖g(x + p^r) - g(x)‖ ≤ ε` for all `x`, then `‖Δ^(p^r) g‖_∞ ≤ max ε (p⁻¹ * B)`. -/
lemma norm_iter_forwardDiff_prime_pow_le {g : ℤ_[p] → ℚ_[p]} {r : ℕ} (hr : 1 ≤ r)
    {B ε : ℝ} (hε : 0 ≤ ε)
    (hbd : ∀ x : ℤ_[p], ‖g x‖ ≤ B)
    (hper : ∀ x : ℤ_[p], ‖g (x + ((p ^ r : ℕ) : ℤ_[p])) - g x‖ ≤ ε)
    (x : ℤ_[p]) :
    ‖(forwardDiff^[p ^ r] g) x‖ ≤ max ε ((p : ℝ)⁻¹ * B) := by
  have hp : p.Prime := Fact.out
  have hM : 0 ≤ max ε ((p : ℝ)⁻¹ * B) := le_max_of_le_left hε
  let N := p ^ r
  have hNpos : 0 < N := pow_pos hp.pos r
  have hN1 : 1 ≤ N := hNpos
  rw [iter_forwardDiff_eq, Finset.sum_range_succ]
  have hsplit :
      (∑ k ∈ Finset.range (N - 1),
        (-1 : ℚ_[p]) ^ (N - (k + 1)) * (N.choose (k + 1) : ℚ_[p]) *
          g (x + ((k + 1 : ℕ) : ℤ_[p]))) +
        (-1 : ℚ_[p]) ^ (N - 0) * (N.choose 0 : ℚ_[p]) * g (x + (0 : ℕ)) +
        (-1 : ℚ_[p]) ^ (N - N) * (N.choose N : ℚ_[p]) * g (x + (N : ℤ_[p])) =
      (∑ k ∈ Finset.range (N - 1),
        (-1 : ℚ_[p]) ^ (N - (k + 1)) * (N.choose (k + 1) : ℚ_[p]) *
          g (x + ((k + 1 : ℕ) : ℤ_[p]))) +
        ((g (x + (N : ℤ_[p])) - g x) +
          ((((1 : ℤ) + (-1 : ℤ) ^ N : ℤ) : ℚ_[p]) * g x)) := by
    simp only [Nat.sub_zero, Nat.choose_zero_right, Nat.cast_one, mul_one, Nat.cast_zero, add_zero,
      Nat.sub_self, pow_zero, Nat.choose_self, one_mul, Int.cast_add, Int.cast_one, Int.cast_pow,
      Int.cast_neg]
    ring
  have hrange : N - 1 + 1 = N := Nat.sub_add_cancel hN1
  have hsum_eq :
      (∑ k ∈ Finset.range (N - 1),
        (-1 : ℚ_[p]) ^ (N - (k + 1)) * (N.choose (k + 1) : ℚ_[p]) *
          g (x + ((k + 1 : ℕ) : ℤ_[p]))) +
        (-1 : ℚ_[p]) ^ (N - 0) * (N.choose 0 : ℚ_[p]) * g (x + (0 : ℕ)) +
        (-1 : ℚ_[p]) ^ (N - N) * (N.choose N : ℚ_[p]) * g (x + (N : ℤ_[p])) =
      (∑ k ∈ Finset.range N,
        (-1 : ℚ_[p]) ^ (N - k) * (N.choose k : ℚ_[p]) * g (x + (k : ℤ_[p]))) +
        (-1 : ℚ_[p]) ^ (N - N) * (N.choose N : ℚ_[p]) * g (x + (N : ℤ_[p])) := by
    congr 1
    have h := Finset.sum_range_succ'
      (fun k => (-1 : ℚ_[p]) ^ (N - k) * (N.choose k : ℚ_[p]) * g (x + (k : ℤ_[p]))) (N - 1)
    rw [hrange] at h
    exact h.symm
  rw [← hsum_eq, hsplit]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hM fun k hk => ?_
    have hklt : k + 1 < N := by
      have := Finset.mem_range.mp hk
      omega
    have hdvd : p ∣ N.choose (k + 1) :=
      prime_dvd_choose_prime_pow (p := p) (n := r) (Nat.succ_pos k) hklt
    rw [norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    calc ‖(N.choose (k + 1) : ℚ_[p])‖ * ‖g (x + ((k + 1 : ℕ) : ℤ_[p]))‖
        ≤ (p : ℝ)⁻¹ * B :=
          mul_le_mul (padic_norm_natCast_le_inv_of_dvd hdvd) (hbd _) (norm_nonneg _) (by positivity)
      _ ≤ max ε ((p : ℝ)⁻¹ * B) := le_max_right _ _
  · refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · exact (hper x).trans (le_max_left _ _)
    · have hdvd : (p : ℤ) ∣ (1 + (-1 : ℤ) ^ N) := by
        rcases hp.eq_two_or_odd with rfl | hodd
        · have heven : Even (2 ^ r) := Even.pow_of_ne_zero even_two (by omega)
          rw [Even.neg_one_pow heven]
          norm_num
        · have hNodd : Odd N := Odd.pow (Nat.odd_iff.mpr hodd)
          rw [Odd.neg_one_pow hNodd]
          norm_num
      rw [norm_mul]
      calc ‖(((1 : ℤ) + (-1 : ℤ) ^ N : ℤ) : ℚ_[p])‖ * ‖g x‖
          ≤ (p : ℝ)⁻¹ * B :=
            mul_le_mul (padic_norm_intCast_le_inv_of_dvd hdvd) (hbd x) (norm_nonneg _) (by positivity)
        _ ≤ max ε ((p : ℝ)⁻¹ * B) := le_max_right _ _

/-- Iterated `k`-fold contraction for `Δ^(k * p^r)`. -/
lemma norm_iter_forwardDiff_mul_prime_pow_le {f : ℤ_[p] → ℚ_[p]} {r : ℕ} (hr : 1 ≤ r)
    {B ε : ℝ} (hε : 0 ≤ ε)
    (hbd : ∀ x : ℤ_[p], ‖f x‖ ≤ B)
    (hper : ∀ x : ℤ_[p], ‖f (x + ((p ^ r : ℕ) : ℤ_[p])) - f x‖ ≤ ε)
    (k : ℕ) (x : ℤ_[p]) :
    ‖(forwardDiff^[k * p ^ r] f) x‖ ≤ max ε ((p : ℝ)⁻¹ ^ k * B) := by
  have hp : p.Prime := Fact.out
  have hpinv0 : (0 : ℝ) ≤ (p : ℝ)⁻¹ := by positivity
  have hpinv1 : (p : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast hp.one_le)
  induction k generalizing x with
  | zero =>
    simp only [zero_mul, Function.iterate_zero_apply, pow_zero, one_mul]
    exact (hbd x).trans (le_max_right _ _)
  | succ k ih =>
    have heq : (k + 1) * p ^ r = p ^ r + k * p ^ r := by ring
    rw [heq, Function.iterate_add_apply]
    have hper_k : ∀ y : ℤ_[p],
        ‖(forwardDiff^[k * p ^ r] f) (y + ((p ^ r : ℕ) : ℤ_[p])) -
          (forwardDiff^[k * p ^ r] f) y‖ ≤ ε := by
      intro y
      rw [← iter_forwardDiff_shift_sub]
      exact norm_iter_forwardDiff_le hper (k * p ^ r) y
    have hstep := norm_iter_forwardDiff_prime_pow_le (p := p) hr
      hε ih hper_k x
    refine hstep.trans (max_le (le_max_left _ _) ?_)
    rw [mul_max_of_nonneg _ _ hpinv0]
    refine max_le ?_ ?_
    · calc (p : ℝ)⁻¹ * ε ≤ 1 * ε := mul_le_mul_of_nonneg_right hpinv1 hε
        _ = ε := one_mul ε
        _ ≤ max ε ((p : ℝ)⁻¹ ^ (k + 1) * B) := le_max_left _ _
    · have hpow : (p : ℝ)⁻¹ * ((p : ℝ)⁻¹ ^ k * B) = (p : ℝ)⁻¹ ^ (k + 1) * B := by
        rw [pow_succ']; ring
      rw [hpow]
      exact le_max_right _ _

/-- **Mahler's Coefficient Decay Theorem (1958)**:
for every continuous function `f : ℤ_[p] → ℚ_[p]`, its Mahler coefficients converge to `0`:
`mahlerDiff f n → 0` as `n → ∞`. -/
theorem tendsto_mahlerDiff_zero_of_continuous {f : ℤ_[p] → ℚ_[p]} (hf : Continuous f) :
    Tendsto (fun n => mahlerDiff f n) atTop (nhds 0) := by
  have hp : p.Prime := Fact.out
  -- Step 1: `f` is bounded on compact `ℤ_[p]`.
  have hbdd : BddAbove ((fun x : ℤ_[p] => ‖f x‖) '' Set.univ) :=
    isCompact_univ.bddAbove_image hf.norm.continuousOn
  obtain ⟨B₀, hB₀⟩ := hbdd
  let B : ℝ := max B₀ 0
  have hbd : ∀ x : ℤ_[p], ‖f x‖ ≤ B := fun x =>
    (hB₀ ⟨x, Set.mem_univ x, rfl⟩).trans (le_max_left _ _)
  -- Step 2: Prove convergence via uniform continuity on compact `ℤ_[p]`.
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hε2 : 0 < ε / 2 := half_pos hε
  have huc : UniformContinuous f := CompactSpace.uniformContinuous_of_continuous hf
  obtain ⟨δ, hδ, hdist⟩ := Metric.uniformContinuous_iff.mp huc (ε / 2) hε2
  obtain ⟨r₀, hr₀⟩ := PadicInt.exists_pow_neg_lt p hδ
  let r : ℕ := r₀ + 1
  have hr1 : 1 ≤ r := Nat.succ_le_succ (Nat.zero_le r₀)
  have hper : ∀ x : ℤ_[p], ‖f (x + ((p ^ r : ℕ) : ℤ_[p])) - f x‖ ≤ ε / 2 := by
    intro x
    have hxd : dist (x + ((p ^ r : ℕ) : ℤ_[p])) x < δ := by
      rw [dist_eq_norm, add_sub_cancel_left]
      have hnp : ‖((p ^ r : ℕ) : ℤ_[p])‖ = (p : ℝ) ^ (-(r : ℤ)) := by
        change ‖((p ^ r : ℕ) : ℚ_[p])‖ = _
        rw [Nat.cast_pow, norm_pow, Padic.norm_p, ← zpow_neg_one, ← zpow_natCast, ← zpow_mul]
        congr 1; ring
      rw [hnp]
      have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.one_le
      have hmono : (p : ℝ) ^ (-(r : ℤ)) ≤ (p : ℝ) ^ (-(r₀ : ℤ)) :=
        zpow_le_zpow_right₀ hp1 (by omega)
      exact hmono.trans_lt hr₀
    have hfl := hdist hxd
    rw [dist_eq_norm] at hfl
    exact hfl.le
  -- Step 3: Choose `k` with `(p⁻¹)^k * B ≤ ε / 2`.
  have hpinv_lt : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)
  have hgeom : Tendsto (fun k : ℕ => (p : ℝ)⁻¹ ^ k * B) atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) hpinv_lt).mul_const B
  obtain ⟨k, hk⟩ := eventually_atTop.mp (hgeom.eventually (Iio_mem_nhds hε2))
  have hkB : (p : ℝ)⁻¹ ^ k * B ≤ ε / 2 := (hk k le_rfl).le
  refine ⟨k * p ^ r, fun n hn => ?_⟩
  rw [dist_zero_right, ← iter_forwardDiff_zero_eq_mahlerDiff]
  have hsplit_n : n = (n - k * p ^ r) + k * p ^ r := (Nat.sub_add_cancel hn).symm
  rw [hsplit_n, Function.iterate_add_apply]
  have hbound_k : ∀ y : ℤ_[p], ‖(forwardDiff^[k * p ^ r] f) y‖ ≤ ε / 2 := by
    intro y
    exact (norm_iter_forwardDiff_mul_prime_pow_le hr1 hε2.le hbd hper k y).trans
      (max_le le_rfl hkB)
  have hle : ‖(forwardDiff^[n - k * p ^ r] (forwardDiff^[k * p ^ r] f)) 0‖ ≤ ε / 2 :=
    norm_iter_forwardDiff_le hbound_k (n - k * p ^ r) 0
  exact hle.trans_lt (half_lt_self hε)

/-- In the complete ultrametric field `ℚ_[p]`, any sequence tending to `0` is `Summable`. -/
lemma padic_summable_of_tendsto_zero {u : ℕ → ℚ_[p]} (hu : Tendsto u atTop (nhds 0)) :
    Summable u := by
  rw [summable_iff_cauchySeq_finset, cauchySeq_finset_iff_vanishing_norm]
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hu (ε / 2) (half_pos hε)
  refine ⟨Finset.range N, fun t ht => ?_⟩
  have hle : ‖∑ i ∈ t, u i‖ ≤ ε / 2 := by
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (half_pos hε).le fun i hi => ?_
    have hge : N ≤ i := by
      by_contra hlt
      exact Finset.disjoint_left.mp ht hi (Finset.mem_range.mpr (not_le.mp hlt))
    simpa [dist_zero_right] using (hN i hge).le
  exact hle.trans_lt (half_lt_self hε)

/-- For every continuous `f : ℤ_[p] → ℚ_[p]` and every `x : ℤ_[p]`, the Mahler series is
summable in `ℚ_[p]`. -/
theorem summable_mahler_term {f : ℤ_[p] → ℚ_[p]} (hf : Continuous f) (x : ℤ_[p]) :
    Summable (fun n => mahlerDiff f n * (mahlerBinom n x : ℚ_[p])) := by
  refine padic_summable_of_tendsto_zero ?_
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h0 : Tendsto (fun n => ‖mahlerDiff f n‖) atTop (nhds 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mp (tendsto_mahlerDiff_zero_of_continuous hf)
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) h0
  rw [norm_mul]
  have h1 : ‖(mahlerBinom n x : ℚ_[p])‖ ≤ 1 := PadicInt.norm_le_one (mahlerBinom n x)
  exact (mul_le_mul_of_nonneg_left h1 (norm_nonneg _)).trans (mul_one _).le

/-- The Mahler partial sums converge uniformly on `ℤ_[p]` to the Mahler series. -/
theorem tendstoUniformly_mahlerPartialSum {f : ℤ_[p] → ℚ_[p]} (hf : Continuous f) :
    TendstoUniformly
      (fun N (x : ℤ_[p]) => ∑ n ∈ Finset.range N, mahlerDiff f n * (mahlerBinom n x : ℚ_[p]))
      (fun x : ℤ_[p] => ∑' n, mahlerDiff f n * (mahlerBinom n x : ℚ_[p]))
      atTop := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (tendsto_mahlerDiff_zero_of_continuous hf)
    (ε / 2) (half_pos hε)
  filter_upwards [eventually_ge_atTop N] with M hM x
  rw [dist_eq_norm]
  have hs := summable_mahler_term hf x
  have htail :
      (∑' n, mahlerDiff f n * (mahlerBinom n x : ℚ_[p])) -
        (∑ n ∈ Finset.range M, mahlerDiff f n * (mahlerBinom n x : ℚ_[p])) =
      ∑' k, mahlerDiff f (k + M) * (mahlerBinom (k + M) x : ℚ_[p]) := by
    have hsplit := hs.sum_add_tsum_nat_add M
    rw [← hsplit]
    ring
  rw [htail]
  have hs_tail : Summable (fun k => mahlerDiff f (k + M) * (mahlerBinom (k + M) x : ℚ_[p])) :=
    (summable_nat_add_iff M).mpr hs
  have hle : ‖∑' k, mahlerDiff f (k + M) * (mahlerBinom (k + M) x : ℚ_[p])‖ ≤ ε / 2 := by
    refine ultrametric_norm_tsum_le (half_pos hε).le hs_tail fun k => ?_
    rw [norm_mul]
    have hge : N ≤ k + M := hM.trans (Nat.le_add_left M k)
    have ha : ‖mahlerDiff f (k + M)‖ ≤ ε / 2 := by
      simpa [dist_zero_right] using (hN (k + M) hge).le
    have hb : ‖(mahlerBinom (k + M) x : ℚ_[p])‖ ≤ 1 :=
      PadicInt.norm_le_one (mahlerBinom (k + M) x)
    exact (mul_le_mul ha hb (norm_nonneg _) (half_pos hε).le).trans (mul_one _).le
  exact hle.trans_lt (half_lt_self hε)

/-- **UNCONDITIONAL MAHLER EXPANSION THEOREM (1958)**:
for EVERY continuous function `f : ℤ_[p] → ℚ_[p]` and EVERY `x : ℤ_[p]`,
`f(x) = ∑'_{n=0}^∞ (mahlerDiff f n) * C(x, n)` in `ℚ_[p]`. -/
theorem mahler_expansion_eq {f : ℤ_[p] → ℚ_[p]} (hf : Continuous f) (x : ℤ_[p]) :
    HasSum (fun n => mahlerDiff f n * (mahlerBinom n x : ℚ_[p])) (f x) := by
  let g : ℤ_[p] → ℚ_[p] := fun y => ∑' n, mahlerDiff f n * (mahlerBinom n y : ℚ_[p])
  have hg_cont : Continuous g := by
    refine (tendstoUniformly_mahlerPartialSum hf).continuous ?_
    refine Eventually.frequently (Eventually.of_forall fun N => ?_)
    refine continuous_finsetSum _ fun n _ => ?_
    exact continuous_const.mul (continuous_subtype_val.comp (continuous_mahlerBinom n))
  have hgf : g = f := by
    refine PadicInt.denseRange_natCast.equalizer hg_cont hf ?_
    ext m
    dsimp only [Function.comp_apply, g]
    have hfin : (∑' n, mahlerDiff f n * (mahlerBinom n (m : ℤ_[p]) : ℚ_[p])) =
        ∑ n ∈ Finset.range (m + 1), mahlerDiff f n * (mahlerBinom n (m : ℤ_[p]) : ℚ_[p]) := by
      refine tsum_eq_sum fun n hn => ?_
      have hgt : m < n := by
        simp only [Finset.mem_range, not_lt] at hn
        omega
      rw [mahlerBinom_natCast, Nat.choose_eq_zero_of_lt hgt]
      simp
    rw [hfin, newton_interpolation f m]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [mahlerBinom_natCast]
    simp
  have hgx : g x = f x := congrFun hgf x
  rw [← hgx]
  exact (summable_mahler_term hf x).hasSum

/-- `tsum` form of Mahler's expansion theorem. -/
theorem mahler_expansion_tsum {f : ℤ_[p] → ℚ_[p]} (hf : Continuous f) (x : ℤ_[p]) :
    (∑' n, mahlerDiff f n * (mahlerBinom n x : ℚ_[p])) = f x :=
  (mahler_expansion_eq hf x).tsum_eq

/-- Continuous-map version of Mahler's expansion theorem for `f : C(ℤ_[p], ℚ_[p])`. -/
theorem mahler_expansion_continuousMap (f : C(ℤ_[p], ℚ_[p])) (x : ℤ_[p]) :
    HasSum (fun n => mahlerDiff f n * (mahlerBinom n x : ℚ_[p])) (f x) :=
  mahler_expansion_eq f.continuous x

/-- **Exact Mahler Ultrametric Isometry**:
for every continuous `f : ℤ_[p] → ℚ_[p]`,
`⨆ x : ℤ_[p], ‖f x‖ = ⨆ n : ℕ, ‖mahlerDiff f n‖`. -/
theorem supNorm_eq_sup_mahlerDiff {f : ℤ_[p] → ℚ_[p]} (hf : Continuous f) :
    (⨆ x : ℤ_[p], ‖f x‖) = ⨆ n : ℕ, ‖mahlerDiff f n‖ := by
  have hbdd_f : BddAbove (Set.range (fun x : ℤ_[p] => ‖f x‖)) := by
    have := isCompact_univ.bddAbove_image hf.norm.continuousOn
    simpa [Set.image_univ] using this
  have hsup_nonneg : 0 ≤ ⨆ x : ℤ_[p], ‖f x‖ :=
    le_ciSup_of_le hbdd_f (0 : ℤ_[p]) (norm_nonneg _)
  have hcoeff_le : ∀ n : ℕ, ‖mahlerDiff f n‖ ≤ ⨆ x : ℤ_[p], ‖f x‖ := by
    intro n
    unfold mahlerDiff
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hsup_nonneg fun k _ => ?_
    rw [norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    have hch : ‖(n.choose k : ℚ_[p])‖ ≤ 1 := padic_norm_natCast_le_one (n.choose k)
    calc ‖(n.choose k : ℚ_[p])‖ * ‖f (k : ℤ_[p])‖
        ≤ 1 * ‖f (k : ℤ_[p])‖ := mul_le_mul_of_nonneg_right hch (norm_nonneg _)
      _ = ‖f (k : ℤ_[p])‖ := one_mul _
      _ ≤ ⨆ x : ℤ_[p], ‖f x‖ := le_ciSup hbdd_f (k : ℤ_[p])
  have hbdd_a : BddAbove (Set.range (fun n : ℕ => ‖mahlerDiff f n‖)) :=
    ⟨⨆ x : ℤ_[p], ‖f x‖, by rintro _ ⟨n, rfl⟩; exact hcoeff_le n⟩
  have hsup_a_nonneg : 0 ≤ ⨆ n : ℕ, ‖mahlerDiff f n‖ :=
    le_ciSup_of_le hbdd_a 0 (norm_nonneg _)
  refine le_antisymm ?_ (ciSup_le hcoeff_le)
  refine ciSup_le fun x => ?_
  rw [← mahler_expansion_tsum hf x]
  refine ultrametric_norm_tsum_le hsup_a_nonneg (summable_mahler_term hf x) fun n => ?_
  rw [norm_mul]
  have hb : ‖(mahlerBinom n x : ℚ_[p])‖ ≤ 1 := PadicInt.norm_le_one (mahlerBinom n x)
  calc ‖mahlerDiff f n‖ * ‖(mahlerBinom n x : ℚ_[p])‖
      ≤ ‖mahlerDiff f n‖ * 1 := mul_le_mul_of_nonneg_left hb (norm_nonneg _)
    _ = ‖mahlerDiff f n‖ := mul_one _
    _ ≤ ⨆ m : ℕ, ‖mahlerDiff f m‖ := le_ciSup hbdd_a n

end MahlerExpansion

/-! ## Section 2: Unconditional Morita's 1975 $p$-adic Gamma Function `Γ_p : ℤ_[p] → ℤ_[p]` -/

section MoritaPadicGamma

variable {p : ℕ} [Fact p.Prime]

/-- Morita's $p$-adic Gamma function on natural numbers:
`moritaGammaNat p n = (-1)^n * ∏_{1 ≤ k < n, p ∤ k} k`. -/
def moritaGammaNat (p : ℕ) (n : ℕ) : ℤ :=
  (-1 : ℤ) ^ n * ∏ k ∈ (Finset.Ico 1 n).filter (fun k => ¬ p ∣ k), (k : ℤ)

@[simp] lemma moritaGammaNat_zero (p : ℕ) : moritaGammaNat p 0 = 1 := by
  simp [moritaGammaNat]

@[simp] lemma moritaGammaNat_one (p : ℕ) : moritaGammaNat p 1 = -1 := by
  simp [moritaGammaNat]

@[simp] lemma moritaGammaNat_two {p : ℕ} (hp : p.Prime) : moritaGammaNat p 2 = 1 := by
  unfold moritaGammaNat
  have hIco : Finset.Ico 1 2 = {1} := by decide
  rw [hIco]
  have h1 : ¬ p ∣ 1 := by
    intro hd
    exact hp.not_dvd_one hd
  simp [Finset.filter_singleton, h1]

/-- Replacing `Finset.Ico 1 n` by `Finset.range n` leaves the `¬ p ∣ k` filter unchanged
(since `p ∣ 0`). -/
lemma filter_Ico_one_eq_filter_range (p n : ℕ) :
    (Finset.Ico 1 n).filter (fun k => ¬ p ∣ k) = (Finset.range n).filter (fun k => ¬ p ∣ k) := by
  ext k
  simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_range]
  constructor
  · rintro ⟨⟨_, hlt⟩, hnd⟩
    exact ⟨hlt, hnd⟩
  · rintro ⟨hlt, hnd⟩
    refine ⟨⟨?_, hlt⟩, hnd⟩
    by_contra h0
    have hk0 : k = 0 := by omega
    exact hnd (hk0 ▸ dvd_zero p)

lemma moritaGammaNat_eq_range (p n : ℕ) :
    moritaGammaNat p n =
      (-1 : ℤ) ^ n * ∏ k ∈ (Finset.range n).filter (fun k => ¬ p ∣ k), (k : ℤ) := by
  rw [moritaGammaNat, filter_Ico_one_eq_filter_range]

/-- Exact one-step recurrence for `moritaGammaNat`:
`moritaGammaNat p (n + 1) = (if ¬ p ∣ n then -n else -1) * moritaGammaNat p n`. -/
lemma moritaGammaNat_succ (p n : ℕ) :
    moritaGammaNat p (n + 1) = (if ¬ p ∣ n then -(n : ℤ) else -1) * moritaGammaNat p n := by
  rw [moritaGammaNat_eq_range, moritaGammaNat_eq_range, Finset.range_add_one,
    Finset.filter_insert]
  have hnotin : n ∉ (Finset.range n).filter (fun k => ¬ p ∣ k) := by
    simp
  by_cases hnd : ¬ p ∣ n
  · rw [if_pos hnd, if_pos hnd, Finset.prod_insert hnotin, pow_succ]
    ring
  · rw [if_neg hnd, if_neg hnd, pow_succ]
    ring

/-- For every prime `p` and every `n : ℕ`, `p` does not divide `moritaGammaNat p n`. -/
lemma not_dvd_moritaGammaNat (n : ℕ) : ¬ (p : ℤ) ∣ moritaGammaNat p n := by
  have hp : p.Prime := Fact.out
  have hpI : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  unfold moritaGammaNat
  intro hd
  rcases hpI.dvd_or_dvd hd with h1 | h2
  · have hunit : IsUnit ((-1 : ℤ) ^ n) := isUnit_one.neg.pow n
    exact hpI.not_isUnit (isUnit_of_dvd_unit h1 hunit)
  · rw [hpI.dvd_finsetProd_iff] at h2
    obtain ⟨k, hk, hdk⟩ := h2
    simp only [Finset.mem_filter] at hk
    exact hk.2 (Int.natCast_dvd_natCast.mp hdk)

/-- Every `moritaGammaNat p n` is a unit in `ℤ_[p]`, i.e. has norm `1`. -/
lemma norm_moritaGammaNat_eq_one (n : ℕ) : ‖(moritaGammaNat p n : ℤ_[p])‖ = 1 := by
  have hle : ‖(moritaGammaNat p n : ℤ_[p])‖ ≤ 1 := PadicInt.norm_le_one _
  refine le_antisymm hle (le_of_not_gt fun hlt => ?_)
  have hd : (p : ℤ_[p]) ∣ (moritaGammaNat p n : ℤ_[p]) :=
    (PadicInt.norm_lt_one_iff_dvd _).mp hlt
  have hmod : PadicInt.toZMod (moritaGammaNat p n : ℤ_[p]) = 0 := by
    obtain ⟨q, hq⟩ := hd
    rw [hq, map_mul, map_natCast, ZMod.natCast_self, zero_mul]
  rw [map_intCast] at hmod
  exact not_dvd_moritaGammaNat (p := p) n ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hmod)

/-! ### Gauss–Wilson Theorem Modulo Prime Powers `p^r` -/

/-- Pairing inverse elements in any finite commutative group:
for any inverse-closed `s : Finset G`, `∏ x ∈ s, x = ∏ x ∈ s.filter (fun x => x⁻¹ = x), x`. -/
lemma prod_eq_prod_inv_eq_self {G : Type*} [CommGroup G] [DecidableEq G] :
    ∀ (N : ℕ) (s : Finset G), s.card ≤ N → (∀ x ∈ s, x⁻¹ ∈ s) →
      ∏ x ∈ s, x = ∏ x ∈ s.filter (fun x => x⁻¹ = x), x
  | 0, s, hcard, _ => by
    have hs : s = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)
    simp [hs]
  | N + 1, s, hcard, hinv => by
    by_cases hall : ∀ x ∈ s, x⁻¹ = x
    · have hf : s.filter (fun x => x⁻¹ = x) = s := Finset.filter_true_of_mem hall
      rw [hf]
    · push Not at hall
      obtain ⟨a, ha, hne⟩ := hall
      have hainv : a⁻¹ ∈ s := hinv a ha
      let s' : Finset G := (s.erase a).erase a⁻¹
      have hainv_er : a⁻¹ ∈ s.erase a := Finset.mem_erase.mpr ⟨hne, hainv⟩
      have hcard' : s'.card ≤ N := by
        have h1 : (s.erase a).card = s.card - 1 := Finset.card_erase_of_mem ha
        have h2 : s'.card = (s.erase a).card - 1 := Finset.card_erase_of_mem hainv_er
        have hpos : 2 ≤ s.card := by
          have hsub : ({a, a⁻¹} : Finset G) ⊆ s := by
            intro x hx
            simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            rcases hx with rfl | rfl <;> assumption
          have hc := Finset.card_le_card hsub
          rw [Finset.card_pair hne.symm] at hc
          exact hc
        omega
      have hinv' : ∀ x ∈ s', x⁻¹ ∈ s' := by
        intro x hx
        simp only [s', Finset.mem_erase] at hx ⊢
        refine ⟨?_, ?_, hinv x hx.2.2⟩
        · intro heq
          exact hx.2.1 (inv_inj.mp heq)
        · intro heq
          have : x = a⁻¹ := by rw [← inv_inv x, heq]
          exact hx.1 this
      have hprod_s : ∏ x ∈ s, x = a * (a⁻¹ * ∏ x ∈ s', x) := by
        rw [← Finset.mul_prod_erase s (fun x => x) ha]
        congr 1
        exact (Finset.mul_prod_erase (s.erase a) (fun x => x) hainv_er).symm
      have hfilt : s'.filter (fun x => x⁻¹ = x) = s.filter (fun x => x⁻¹ = x) := by
        ext x
        simp only [s', Finset.mem_filter, Finset.mem_erase]
        constructor
        · rintro ⟨⟨_, _, hxs⟩, hfx⟩
          exact ⟨hxs, hfx⟩
        · rintro ⟨hxs, hfx⟩
          refine ⟨⟨?_, ?_, hxs⟩, hfx⟩
          · rintro rfl
            exact hne ((inv_inv a).symm.trans hfx).symm
          · rintro rfl
            exact hne hfx
      rw [hprod_s, ← mul_assoc, mul_inv_cancel, one_mul,
        prod_eq_prod_inv_eq_self N s' hcard' hinv', hfilt]

/-- Helper: in `ℤ`, if `p` is prime, `¬ (p : ℤ) ∣ b`, and `(p : ℤ) ^ r ∣ a * b`, then `(p : ℤ) ^ r ∣ a`. -/
lemma prime_pow_dvd_of_dvd_mul_of_not_dvd {a b : ℤ} {r : ℕ}
    (hnd : ¬ (p : ℤ) ∣ b) (hd : ((p : ℤ) ^ r) ∣ a * b) : ((p : ℤ) ^ r) ∣ a := by
  have hp : p.Prime := Fact.out
  have hpI : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hcop : IsCoprime (p : ℤ) b := hpI.coprime_iff_not_dvd.mpr hnd
  exact (hcop.pow_left (m := r)).dvd_of_dvd_mul_right hd

/-- **Gauss–Wilson Theorem for Odd Prime Powers**:
for any odd prime `p` and `r ≥ 1`, `∏ u : (ZMod (p ^ r))ˣ, (u : ZMod (p ^ r)) = -1`. -/
theorem prod_units_zmod_odd_prime_pow (hp2 : p ≠ 2) {r : ℕ} (hr : 1 ≤ r) :
    ∏ u : (ZMod (p ^ r))ˣ, (u : ZMod (p ^ r)) = -1 := by
  have hp : p.Prime := Fact.out
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have hpr3 : 3 ≤ p ^ r :=
    hp3.trans (Nat.le_self_pow (by omega) p)
  have : NeZero (p ^ r) := ⟨pow_ne_zero r hp.ne_zero⟩
  have hgrp : (∏ u : (ZMod (p ^ r))ˣ, u) = -1 := by
    rw [prod_eq_prod_inv_eq_self (Fintype.card (ZMod (p ^ r))ˣ) Finset.univ
      (by simp) (fun _ _ => Finset.mem_univ _)]
    have hfilt : Finset.univ.filter (fun u : (ZMod (p ^ r))ˣ => u⁻¹ = u) = {1, -1} := by
      ext u
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton]
      constructor
      · intro hu
        have hsq : (u : ZMod (p ^ r)) * (u : ZMod (p ^ r)) = 1 := by
          have h1 : u * u = 1 := by
            nth_rw 1 [← hu]
            exact inv_mul_cancel u
          simpa [Units.val_mul] using congrArg Units.val h1
        let a : ℤ := ((u : ZMod (p ^ r)).val : ℤ)
        have ha : (a : ZMod (p ^ r)) = (u : ZMod (p ^ r)) := by
          simp [a]
        have hzero : ((a - 1) * (a + 1) : ZMod (p ^ r)) = 0 := by
          rw [ha]
          linear_combination hsq
        have hdvd : ((p : ℤ) ^ r) ∣ (a - 1) * (a + 1) := by
          have h1 := (ZMod.intCast_zmod_eq_zero_iff_dvd ((a - 1) * (a + 1)) (p ^ r)).mp (by
            simpa using hzero)
          simpa using h1
        by_cases hpa : (p : ℤ) ∣ (a + 1)
        · have hnd : ¬ (p : ℤ) ∣ (a - 1) := by
            intro hpm
            have hd2 : (p : ℤ) ∣ ((a + 1) - (a - 1)) := dvd_sub hpa hpm
            have h2 : (a + 1) - (a - 1) = 2 := by ring
            rw [h2] at hd2
            have h2nat : p ∣ 2 := Int.natCast_dvd_natCast.mp hd2
            have := Nat.le_of_dvd (by decide) h2nat
            omega
          have hpr_dvd : ((p : ℤ) ^ r) ∣ (a + 1) := by
            rw [mul_comm] at hdvd
            exact prime_pow_dvd_of_dvd_mul_of_not_dvd hnd hdvd
          right
          ext
          have hz : ((a + 1 : ℤ) : ZMod (p ^ r)) = 0 :=
            (ZMod.intCast_zmod_eq_zero_iff_dvd (a + 1) (p ^ r)).mpr (by simpa using hpr_dvd)
          push_cast at hz
          rw [ha] at hz
          simpa [Units.val_neg] using eq_neg_of_add_eq_zero_left hz
        · have hpr_dvd : ((p : ℤ) ^ r) ∣ (a - 1) :=
            prime_pow_dvd_of_dvd_mul_of_not_dvd hpa hdvd
          left
          ext
          have hz : ((a - 1 : ℤ) : ZMod (p ^ r)) = 0 :=
            (ZMod.intCast_zmod_eq_zero_iff_dvd (a - 1) (p ^ r)).mpr (by simpa using hpr_dvd)
          push_cast at hz
          rw [ha] at hz
          simpa using sub_eq_zero.mp hz
      · rintro (rfl | rfl) <;> simp
    rw [hfilt]
    have hne : (1 : (ZMod (p ^ r))ˣ) ≠ -1 := by
      intro heq
      have hval : (1 : ZMod (p ^ r)) = -1 := congrArg Units.val heq
      have h20 : ((2 : ℕ) : ZMod (p ^ r)) = 0 := by
        have : (1 : ZMod (p ^ r)) + 1 = 0 := by
          calc (1 : ZMod (p ^ r)) + 1 = (1 : ZMod (p ^ r)) + -1 := by rw [← hval]
            _ = 0 := add_neg_cancel _
        simpa [one_add_one_eq_two] using this
      have hd2 : p ^ r ∣ 2 := (ZMod.natCast_eq_zero_iff 2 (p ^ r)).mp h20
      have := Nat.le_of_dvd (by decide) hd2
      omega
    rw [Finset.prod_pair hne, one_mul]
  have hmap := congrArg (Units.coeHom (ZMod (p ^ r))) hgrp
  simpa using hmap

/-- **Gauss–Wilson Theorem for Powers of `2` (`r ≥ 3`)**:
for every `r ≥ 3`, `∏ u : (ZMod (2 ^ r))ˣ, (u : ZMod (2 ^ r)) = 1`. -/
theorem prod_units_zmod_two_pow {r : ℕ} (hr : 3 ≤ r) :
    ∏ u : (ZMod (2 ^ r))ˣ, (u : ZMod (2 ^ r)) = 1 := by
  have : NeZero (2 ^ r) := ⟨pow_ne_zero r (by decide)⟩
  let h : ZMod (2 ^ r) := ((2 ^ (r - 1) : ℕ) : ZMod (2 ^ r))
  have hh_sq : h * h = 0 := by
    have heq : (2 ^ (r - 1) * 2 ^ (r - 1) : ℕ) = 2 ^ r * 2 ^ (r - 2) := by
      rw [← pow_add, ← pow_add]
      congr 1; omega
    have hz : ((2 ^ (r - 1) * 2 ^ (r - 1) : ℕ) : ZMod (2 ^ r)) = 0 := by
      rw [heq, Nat.cast_mul, ZMod.natCast_self, zero_mul]
    simpa [h, Nat.cast_mul] using hz
  have hh_two : (2 : ZMod (2 ^ r)) * h = 0 := by
    have heq : 2 * 2 ^ (r - 1) = 2 ^ r := by
      rw [← pow_succ']; congr 1; omega
    have hz : ((2 * 2 ^ (r - 1) : ℕ) : ZMod (2 ^ r)) = 0 := by
      rw [heq, ZMod.natCast_self]
    simpa [h, Nat.cast_mul] using hz
  have h1h_sq : (1 + h) * (1 + h) = 1 := by
    calc (1 + h) * (1 + h) = 1 + 2 * h + h * h := by ring
      _ = 1 + 0 + 0 := by rw [hh_two, hh_sq]
      _ = 1 := by ring
  let u3 : (ZMod (2 ^ r))ˣ := ⟨1 + h, 1 + h, h1h_sq, h1h_sq⟩
  let u4 : (ZMod (2 ^ r))ˣ := -u3
  have hgrp : (∏ u : (ZMod (2 ^ r))ˣ, u) = 1 := by
    rw [prod_eq_prod_inv_eq_self (Fintype.card (ZMod (2 ^ r))ˣ) Finset.univ
      (by simp) (fun _ _ => Finset.mem_univ _)]
    have hfilt : Finset.univ.filter (fun u : (ZMod (2 ^ r))ˣ => u⁻¹ = u) = {1, -1, u3, u4} := by
      ext u
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton]
      constructor
      · intro hu
        have hsq : (u : ZMod (2 ^ r)) * (u : ZMod (2 ^ r)) = 1 := by
          have h1 : u * u = 1 := by
            nth_rw 1 [← hu]
            exact inv_mul_cancel u
          simpa [Units.val_mul] using congrArg Units.val h1
        let a : ℤ := ((u : ZMod (2 ^ r)).val : ℤ)
        have ha : (a : ZMod (2 ^ r)) = (u : ZMod (2 ^ r)) := by simp [a]
        have hzero : ((a - 1) * (a + 1) : ZMod (2 ^ r)) = 0 := by
          rw [ha]; linear_combination hsq
        have hdvd : ((2 : ℤ) ^ r) ∣ (a - 1) * (a + 1) := by
          have h1 := (ZMod.intCast_zmod_eq_zero_iff_dvd ((a - 1) * (a + 1)) (2 ^ r)).mp (by
            simpa using hzero)
          simpa using h1
        have ha_odd : (2 : ℤ) ∣ (a - 1) := by
          have h2dvd : (2 : ℤ) ∣ (a - 1) * (a + 1) :=
            (dvd_pow_self (2 : ℤ) (by omega : r ≠ 0)).trans hdvd
          have h2p : Prime (2 : ℤ) := Nat.prime_iff_prime_int.mp Nat.prime_two
          rcases h2p.dvd_or_dvd h2dvd with h1 | h2
          · exact h1
          · obtain ⟨t, ht⟩ := h2
            exact ⟨t - 1, by linarith⟩
        obtain ⟨b, hb⟩ := ha_odd
        have hab : a + 1 = 2 * (b + 1) := by linarith
        have h4 : ((2 : ℤ) ^ r) = 4 * (2 : ℤ) ^ (r - 2) := by
          have : (4 : ℤ) = 2 ^ 2 := by norm_num
          rw [this, ← pow_add]; congr 1; omega
        have hdvd_b : ((2 : ℤ) ^ (r - 2)) ∣ b * (b + 1) := by
          rw [hb, hab, h4] at hdvd
          have hmul : (2 * b) * (2 * (b + 1)) = 4 * (b * (b + 1)) := by ring
          rw [hmul] at hdvd
          exact (mul_dvd_mul_iff_left (by norm_num : (4 : ℤ) ≠ 0)).mp hdvd
        have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        have hsplit : ((2 : ℤ) ^ (r - 2) ∣ b) ∨ ((2 : ℤ) ^ (r - 2) ∣ (b + 1)) := by
          by_cases h2b : (2 : ℤ) ∣ b
          · left
            have hnd : ¬ (2 : ℤ) ∣ (b + 1) := by
              intro h2b1
              have h1 := dvd_sub h2b1 h2b
              have : (b + 1) - b = 1 := by ring
              rw [this] at h1
              omega
            exact prime_pow_dvd_of_dvd_mul_of_not_dvd (p := 2) hnd hdvd_b
          · right
            rw [mul_comm] at hdvd_b
            exact prime_pow_dvd_of_dvd_mul_of_not_dvd (p := 2) h2b hdvd_b
        rcases hsplit with ⟨q, hq⟩ | ⟨q, hq⟩
        · have ha_eq : a - 1 = (2 : ℤ) ^ (r - 1) * q := by
            rw [hb, hq]
            have hpow : (2 : ℤ) * (2 : ℤ) ^ (r - 2) = (2 : ℤ) ^ (r - 1) := by
              rw [← pow_succ']; congr 1; omega
            linear_combination q * hpow
          rcases Int.even_or_odd q with ⟨t, ht⟩ | ⟨t, ht⟩
          · left
            ext
            have hdiv : ((2 : ℤ) ^ r) ∣ (a - 1) := by
              refine ⟨t, ?_⟩
              rw [ha_eq, ht]
              have hpow : (2 : ℤ) ^ (r - 1) * 2 = (2 : ℤ) ^ r := by
                rw [← pow_succ]; congr 1; omega
              linear_combination t * hpow
            have hz : ((a - 1 : ℤ) : ZMod (2 ^ r)) = 0 :=
              (ZMod.intCast_zmod_eq_zero_iff_dvd (a - 1) (2 ^ r)).mpr (by simpa using hdiv)
            push_cast at hz; rw [ha] at hz
            simpa using sub_eq_zero.mp hz
          · right; right; left
            ext
            have hdiv : ((2 : ℤ) ^ r) ∣ (a - 1 - (2 : ℤ) ^ (r - 1)) := by
              refine ⟨t, ?_⟩
              rw [ha_eq, ht]
              have hpow : (2 : ℤ) ^ (r - 1) * 2 = (2 : ℤ) ^ r := by
                rw [← pow_succ]; congr 1; omega
              linear_combination t * hpow
            have hz : ((a - 1 - (2 : ℤ) ^ (r - 1) : ℤ) : ZMod (2 ^ r)) = 0 :=
              (ZMod.intCast_zmod_eq_zero_iff_dvd _ (2 ^ r)).mpr (by simpa using hdiv)
            push_cast at hz; rw [ha] at hz
            change (u : ZMod (2 ^ r)) = 1 + h
            have hh_eq : (2 : ZMod (2 ^ r)) ^ (r - 1) = h := by simp [h]
            rw [hh_eq] at hz
            linear_combination hz
        · have ha_eq : a + 1 = (2 : ℤ) ^ (r - 1) * q := by
            rw [hab, hq]
            have hpow : (2 : ℤ) * (2 : ℤ) ^ (r - 2) = (2 : ℤ) ^ (r - 1) := by
              rw [← pow_succ']; congr 1; omega
            linear_combination q * hpow
          rcases Int.even_or_odd q with ⟨t, ht⟩ | ⟨t, ht⟩
          · right; left
            ext
            have hdiv : ((2 : ℤ) ^ r) ∣ (a + 1) := by
              refine ⟨t, ?_⟩
              rw [ha_eq, ht]
              have hpow : (2 : ℤ) ^ (r - 1) * 2 = (2 : ℤ) ^ r := by
                rw [← pow_succ]; congr 1; omega
              linear_combination t * hpow
            have hz : ((a + 1 : ℤ) : ZMod (2 ^ r)) = 0 :=
              (ZMod.intCast_zmod_eq_zero_iff_dvd (a + 1) (2 ^ r)).mpr (by simpa using hdiv)
            push_cast at hz; rw [ha] at hz
            simpa [Units.val_neg] using eq_neg_of_add_eq_zero_left hz
          · right; right; right
            ext
            have hdiv : ((2 : ℤ) ^ r) ∣ (a + 1 + (2 : ℤ) ^ (r - 1)) := by
              refine ⟨t + 1, ?_⟩
              rw [ha_eq, ht]
              have hpow : (2 : ℤ) ^ (r - 1) * 2 = (2 : ℤ) ^ r := by
                rw [← pow_succ]; congr 1; omega
              linear_combination (t + 1) * hpow
            have hz : ((a + 1 + (2 : ℤ) ^ (r - 1) : ℤ) : ZMod (2 ^ r)) = 0 :=
              (ZMod.intCast_zmod_eq_zero_iff_dvd _ (2 ^ r)).mpr (by simpa using hdiv)
            push_cast at hz; rw [ha] at hz
            change (u : ZMod (2 ^ r)) = -(1 + h)
            have hh_eq : (2 : ZMod (2 ^ r)) ^ (r - 1) = h := by simp [h]
            rw [hh_eq] at hz
            linear_combination hz
      · rintro (rfl | rfl | rfl | rfl)
        · simp
        · simp
        · ext; rfl
        · ext
          simp only [u4, u3, Units.val_neg]
          have : (-u3)⁻¹ = -(u3⁻¹) := by simp
          have hu3 : u3⁻¹ = u3 := by ext; rfl
          change (((-u3)⁻¹ : (ZMod (2 ^ r))ˣ) : ZMod (2 ^ r)) = -(1 + h)
          rw [this, hu3]
          rfl
    rw [hfilt]
    -- All four elements `1, -1, u3, u4` are pairwise distinct for `r ≥ 3`.
    have h2r_ge : 8 ≤ 2 ^ r := by
      have : 2 ^ 3 ≤ 2 ^ r := Nat.pow_le_pow_right (by decide) hr
      omega
    have hhalf_lt : 2 ^ (r - 1) < 2 ^ r := Nat.pow_lt_pow_right (by decide) (by omega)
    have hhalf_ge4 : 4 ≤ 2 ^ (r - 1) := by
      have : 2 ^ 2 ≤ 2 ^ (r - 1) := Nat.pow_le_pow_right (by decide) (by omega)
      omega
    have h2_ne : (2 : ZMod (2 ^ r)) ≠ 0 := by
      intro h0
      have hd : 2 ^ r ∣ 2 := (ZMod.natCast_eq_zero_iff 2 (2 ^ r)).mp (by simpa using h0)
      have := Nat.le_of_dvd (by decide) hd
      omega
    have hh_ne : h ≠ 0 := by
      intro h0
      have hd : 2 ^ r ∣ 2 ^ (r - 1) := (ZMod.natCast_eq_zero_iff _ (2 ^ r)).mp h0
      have := Nat.le_of_dvd (pow_pos (by decide) _) hd
      omega
    have hh_ne_two : h + 2 ≠ 0 := by
      intro h0
      have hcast : ((2 ^ (r - 1) + 2 : ℕ) : ZMod (2 ^ r)) = 0 := by simpa [h] using h0
      have hd : 2 ^ r ∣ (2 ^ (r - 1) + 2) := (ZMod.natCast_eq_zero_iff _ (2 ^ r)).mp hcast
      have hle := Nat.le_of_dvd (by omega) hd
      have h2eq : 2 ^ r = 2 * 2 ^ (r - 1) := by rw [← pow_succ']; congr 1; omega
      omega
    have h1_m1 : (1 : (ZMod (2 ^ r))ˣ) ≠ -1 := fun heq => h2_ne (by
      have hv : (1 : ZMod (2 ^ r)) = -1 := congrArg Units.val heq
      linear_combination hv)
    have h1_u3 : (1 : (ZMod (2 ^ r))ˣ) ≠ u3 := fun heq => hh_ne (by
      have hv : (1 : ZMod (2 ^ r)) = 1 + h := congrArg Units.val heq
      linear_combination -hv)
    have h1_u4 : (1 : (ZMod (2 ^ r))ˣ) ≠ u4 := fun heq => hh_ne_two (by
      have hv : (1 : ZMod (2 ^ r)) = -(1 + h) := congrArg Units.val heq
      linear_combination hv)
    have hm1_u3 : (-1 : (ZMod (2 ^ r))ˣ) ≠ u3 := fun heq => hh_ne_two (by
      have hv : (-1 : ZMod (2 ^ r)) = 1 + h := congrArg Units.val heq
      linear_combination -hv)
    have hm1_u4 : (-1 : (ZMod (2 ^ r))ˣ) ≠ u4 := fun heq => hh_ne (by
      have hv : (-1 : ZMod (2 ^ r)) = -(1 + h) := congrArg Units.val heq
      linear_combination hv)
    have hu3_u4 : u3 ≠ u4 := fun heq => h2_ne (by
      have hv : (1 + h : ZMod (2 ^ r)) = -(1 + h) := congrArg Units.val heq
      linear_combination hv - hh_two)
    rw [Finset.prod_insert (by simp [h1_m1, h1_u3, h1_u4]),
      Finset.prod_insert (by simp [hm1_u3, hm1_u4]),
      Finset.prod_pair hu3_u4]
    ext
    simp only [u4, u3, Units.val_mul, Units.val_one, Units.val_neg]
    calc 1 * (-1 * ((1 + h) * -(1 + h))) = (1 + h) * (1 + h) := by ring
      _ = 1 := h1h_sq
  have hmap := congrArg (Units.coeHom (ZMod (2 ^ r))) hgrp
  simpa using hmap

/-- The product of all integers `k ∈ [m, m + p^r)` coprime to `p` equals the product of all units
in `ZMod (p ^ r)`. -/
lemma prod_Ico_not_dvd_eq_prod_units {r : ℕ} (hr : 1 ≤ r) (m : ℕ) :
    (∏ k ∈ (Finset.Ico m (m + p ^ r)).filter (fun k => ¬ p ∣ k), (k : ZMod (p ^ r))) =
      ∏ u : (ZMod (p ^ r))ˣ, (u : ZMod (p ^ r)) := by
  have hp : p.Prime := Fact.out
  have : NeZero (p ^ r) := ⟨pow_ne_zero r hp.ne_zero⟩
  refine Finset.prod_bij
    (fun k hk =>
      ZMod.unitOfCoprime k
        (Nat.Coprime.pow_right r (hp.coprime_iff_not_dvd.mpr (Finset.mem_filter.mp hk).2).symm))
    (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
  · intro k₁ hk₁ k₂ hk₂ heq
    have hval : (k₁ : ZMod (p ^ r)) = (k₂ : ZMod (p ^ r)) := by
      have := congrArg Units.val heq
      simpa [ZMod.coe_unitOfCoprime] using this
    have hmod : k₁ ≡ k₂ [MOD p ^ r] := (ZMod.natCast_eq_natCast_iff k₁ k₂ (p ^ r)).mp hval
    have h1 := Finset.mem_Ico.mp (Finset.mem_filter.mp hk₁).1
    have h2 := Finset.mem_Ico.mp (Finset.mem_filter.mp hk₂).1
    have hsub : k₁ - m ≡ k₂ - m [MOD p ^ r] := by
      have h' : (k₁ - m) + m ≡ (k₂ - m) + m [MOD p ^ r] := by
        rwa [Nat.sub_add_cancel h1.1, Nat.sub_add_cancel h2.1]
      exact Nat.ModEq.add_right_cancel' m h'
    have hlt1 : k₁ - m < p ^ r := by omega
    have hlt2 : k₂ - m < p ^ r := by omega
    have hsub_eq : k₁ - m = k₂ - m := by
      rw [Nat.ModEq, Nat.mod_eq_of_lt hlt1, Nat.mod_eq_of_lt hlt2] at hsub
      exact hsub
    omega
  · intro u _
    let a : ℕ := ((u : ZMod (p ^ r)) - (m : ZMod (p ^ r))).val
    have ha_lt : a < p ^ r := ZMod.val_lt _
    let k : ℕ := m + a
    have hk_cast : (k : ZMod (p ^ r)) = (u : ZMod (p ^ r)) := by
      simp [k, a]
    have hk_ndvd : ¬ p ∣ k := by
      intro hd
      obtain ⟨q, hq⟩ := hd
      have h1 : (p : ZMod (p ^ r)) * ((q : ZMod (p ^ r)) * (u⁻¹ : (ZMod (p ^ r))ˣ)) = 1 := by
        have hku : (k : ZMod (p ^ r)) * (u⁻¹ : (ZMod (p ^ r))ˣ) = 1 := by
          rw [hk_cast]
          exact_mod_cast Units.mul_inv u
        rw [hq, Nat.cast_mul, mul_assoc] at hku
        exact hku
      have hmul := congrArg (fun z : ZMod (p ^ r) => ((p ^ (r - 1) : ℕ) : ZMod (p ^ r)) * z) h1
      rw [mul_one, ← mul_assoc, ← Nat.cast_mul] at hmul
      have hpeq : p ^ (r - 1) * p = p ^ r := by
        rw [← pow_succ]; congr 1; omega
      rw [hpeq, ZMod.natCast_self, zero_mul] at hmul
      have hdvd : p ^ r ∣ p ^ (r - 1) :=
        (ZMod.natCast_eq_zero_iff (p ^ (r - 1)) (p ^ r)).mp hmul.symm
      have hle := Nat.le_of_dvd (pow_pos hp.pos _) hdvd
      have hlt : p ^ (r - 1) < p ^ r := Nat.pow_lt_pow_right hp.one_lt (by omega)
      omega
    refine ⟨k, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_Ico]
      exact ⟨⟨Nat.le_add_right m a, by omega⟩, hk_ndvd⟩
    · ext
      simpa [ZMod.coe_unitOfCoprime] using hk_cast
  · intro k hk
    simp [ZMod.coe_unitOfCoprime]

/-- One-step prime-power periodicity of `moritaGammaNat`:
for odd `p` (and any `r ≥ 1`), or `p = 2` with `r ≥ 3`,
`moritaGammaNat p (m + p ^ r) ≡ moritaGammaNat p m [ZMOD (p ^ r : ℕ)]`. -/
lemma moritaGammaNat_add_prime_pow_modEq {r : ℕ} (hpr : (p ≠ 2 ∧ 1 ≤ r) ∨ (p = 2 ∧ 3 ≤ r))
    (m : ℕ) :
    moritaGammaNat p (m + p ^ r) ≡ moritaGammaNat p m [ZMOD (p ^ r : ℕ)] := by
  have hp : p.Prime := Fact.out
  have hr1 : 1 ≤ r := by rcases hpr with ⟨_, h⟩ | ⟨_, h⟩ <;> omega
  rw [← ZMod.intCast_eq_intCast_iff]
  rw [moritaGammaNat_eq_range, moritaGammaNat_eq_range]
  have hrange_split :
      (Finset.range (m + p ^ r)).filter (fun k => ¬ p ∣ k) =
        (Finset.range m).filter (fun k => ¬ p ∣ k) ∪
          (Finset.Ico m (m + p ^ r)).filter (fun k => ¬ p ∣ k) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_union, Finset.mem_Ico]
    omega
  have hdisj : Disjoint
      ((Finset.range m).filter (fun k => ¬ p ∣ k))
      ((Finset.Ico m (m + p ^ r)).filter (fun k => ¬ p ∣ k)) := by
    rw [Finset.disjoint_left]
    intro k h1 h2
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico] at h1 h2
    omega
  rw [hrange_split, Finset.prod_union hdisj, pow_add]
  push_cast
  have hblk :
      (∏ k ∈ (Finset.Ico m (m + p ^ r)).filter (fun k => ¬ p ∣ k), (k : ZMod (p ^ r))) =
        ∏ u : (ZMod (p ^ r))ˣ, (u : ZMod (p ^ r)) :=
    prod_Ico_not_dvd_eq_prod_units hr1 m
  have hfac : ((-1 : ZMod (p ^ r)) ^ (p ^ r)) *
      (∏ k ∈ (Finset.Ico m (m + p ^ r)).filter (fun k => ¬ p ∣ k), (k : ZMod (p ^ r))) = 1 := by
    rw [hblk]
    rcases hpr with ⟨hp2, hr⟩ | ⟨rfl, hr⟩
    · rw [prod_units_zmod_odd_prime_pow hp2 hr]
      have hodd : Odd (p ^ r) := Odd.pow (hp.odd_of_ne_two hp2)
      rw [Odd.neg_one_pow hodd]
      ring
    · rw [prod_units_zmod_two_pow hr]
      have heven : Even (2 ^ r) := Even.pow_of_ne_zero even_two (by omega)
      rw [Even.neg_one_pow heven]
      ring
  calc (-1 : ZMod (p ^ r)) ^ m * (-1) ^ (p ^ r) *
        ((∏ x ∈ (Finset.range m).filter (fun k => ¬ p ∣ k), (x : ZMod (p ^ r))) *
          ∏ x ∈ (Finset.Ico m (m + p ^ r)).filter (fun k => ¬ p ∣ k), (x : ZMod (p ^ r)))
      = (-1 : ZMod (p ^ r)) ^ m *
          (∏ x ∈ (Finset.range m).filter (fun k => ¬ p ∣ k), (x : ZMod (p ^ r))) *
          ((-1 : ZMod (p ^ r)) ^ (p ^ r) *
            ∏ x ∈ (Finset.Ico m (m + p ^ r)).filter (fun k => ¬ p ∣ k), (x : ZMod (p ^ r))) := by
        ring
    _ = (-1 : ZMod (p ^ r)) ^ m *
          ∏ x ∈ (Finset.range m).filter (fun k => ¬ p ∣ k), (x : ZMod (p ^ r)) := by
        rw [hfac, mul_one]

/-- Unified Morita fundamental congruence:
for any prime `p` and `r : ℕ` with `p ≠ 2 ∨ 3 ≤ r`,
`m ≡ n [MOD p ^ r] → moritaGammaNat p m ≡ moritaGammaNat p n [ZMOD p ^ r]`. -/
theorem moritaGammaNat_congr_mod_pow_any {r : ℕ} (hpr : p ≠ 2 ∨ 3 ≤ r) {m n : ℕ}
    (hmn : m ≡ n [MOD p ^ r]) :
    moritaGammaNat p m ≡ moritaGammaNat p n [ZMOD (p ^ r : ℕ)] := by
  rcases Nat.eq_zero_or_pos r with rfl | hrpos
  · simp [Int.ModEq]
  have hpr' : (p ≠ 2 ∧ 1 ≤ r) ∨ (p = 2 ∧ 3 ≤ r) := by
    rcases hpr with hp2 | hr3
    · exact Or.inl ⟨hp2, hrpos⟩
    · by_cases hp2 : p = 2
      · exact Or.inr ⟨hp2, hr3⟩
      · exact Or.inl ⟨hp2, hrpos⟩
  have hstep : ∀ (a t : ℕ),
      moritaGammaNat p (a + t * p ^ r) ≡ moritaGammaNat p a [ZMOD (p ^ r : ℕ)] := by
    intro a t
    induction t with
    | zero => simp
    | succ t ih =>
      have heq : a + (t + 1) * p ^ r = (a + t * p ^ r) + p ^ r := by ring
      rw [heq]
      exact (moritaGammaNat_add_prime_pow_modEq hpr' (a + t * p ^ r)).trans ih
  rcases le_total m n with hle | hle
  · have hdvd : p ^ r ∣ (n - m) := (Nat.modEq_iff_dvd' hle).mp hmn
    obtain ⟨t, ht⟩ := hdvd
    have hn : n = m + t * p ^ r := by rw [mul_comm, ← ht, Nat.add_sub_cancel' hle]
    rw [hn]
    exact (hstep m t).symm
  · have hdvd : p ^ r ∣ (m - n) := (Nat.modEq_iff_dvd' hle).mp hmn.symm
    obtain ⟨t, ht⟩ := hdvd
    have hm : m = n + t * p ^ r := by rw [mul_comm, ← ht, Nat.add_sub_cancel' hle]
    rw [hm]
    exact hstep n t

/-- **Morita's Fundamental Congruence (Odd Primes)**:
for every odd prime `p`, every `r : ℕ`, and all `m n : ℕ`,
`m ≡ n [MOD p ^ r] → moritaGammaNat p m ≡ moritaGammaNat p n [ZMOD p ^ r]`. -/
theorem moritaGammaNat_congr_mod_pow (hp2 : p ≠ 2) (r : ℕ) {m n : ℕ}
    (hmn : m ≡ n [MOD p ^ r]) :
    moritaGammaNat p m ≡ moritaGammaNat p n [ZMOD (p ^ r : ℕ)] :=
  moritaGammaNat_congr_mod_pow_any (Or.inl hp2) hmn

/-- **Morita's Fundamental Congruence (`p = 2`, `r ≥ 3`)**:
for every `r ≥ 3` and all `m n : ℕ`,
`m ≡ n [MOD 2 ^ r] → moritaGammaNat 2 m ≡ moritaGammaNat 2 n [ZMOD 2 ^ r]`. -/
theorem moritaGammaNat_congr_mod_two_pow {r : ℕ} (hr : 3 ≤ r) {m n : ℕ}
    (hmn : m ≡ n [MOD 2 ^ r]) :
    moritaGammaNat 2 m ≡ moritaGammaNat 2 n [ZMOD (2 ^ r : ℕ)] := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact moritaGammaNat_congr_mod_pow_any (p := 2) (Or.inr hr) hmn

/-! ### Construction and Properties of Morita's $p$-adic Gamma Function `padicGamma` -/

/-- Level-`n` approximating sequence for `padicGamma p x`. -/
def padicGammaSeq (p : ℕ) [Fact p.Prime] (x : ℤ_[p]) (n : ℕ) : ℤ_[p] :=
  (moritaGammaNat p (PadicInt.toZModPow n x).val : ℤ_[p])

lemma norm_padicGammaSeq_sub_le_of_le (x : ℤ_[p]) {m n : ℕ} (hmn : m ≤ n)
    (hm : p ≠ 2 ∨ 3 ≤ m) :
    ‖padicGammaSeq p x n - padicGammaSeq p x m‖ ≤ (p : ℝ) ^ (-(m : ℤ)) := by
  have hmod : (PadicInt.toZModPow n x).val ≡ (PadicInt.toZModPow m x).val [MOD p ^ m] := by
    have h1 := zmodPowCast_val_modEq (p := p) hmn (PadicInt.toZModPow n x)
    rwa [zmodPowCast_toZModPow hmn x] at h1
  have hzmod : moritaGammaNat p (PadicInt.toZModPow n x).val ≡
      moritaGammaNat p (PadicInt.toZModPow m x).val [ZMOD (p ^ m : ℕ)] :=
    moritaGammaNat_congr_mod_pow_any hm hmod
  refine padicInt_norm_le_pow_of_toZModPow_eq ?_
  unfold padicGammaSeq
  rw [map_intCast, map_intCast]
  exact (ZMod.intCast_eq_intCast_iff _ _ _).mpr hzmod

/-- For every `x : ℤ_[p]`, `padicGammaSeq p x` is a Cauchy sequence in `ℤ_[p]`. -/
theorem cauchySeq_padicGammaSeq (x : ℤ_[p]) : CauchySeq (padicGammaSeq p x) := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨N₀, hN₀⟩ := PadicInt.exists_pow_neg_lt p hε
  let N : ℕ := max N₀ 3
  refine ⟨N, fun m hm n hn => ?_⟩
  rw [dist_eq_norm]
  have hN3 : 3 ≤ N := le_max_right N₀ 3
  have h1 : ‖padicGammaSeq p x m - padicGammaSeq p x N‖ ≤ (p : ℝ) ^ (-(N : ℤ)) :=
    norm_padicGammaSeq_sub_le_of_le x hm (Or.inr hN3)
  have h2 : ‖padicGammaSeq p x n - padicGammaSeq p x N‖ ≤ (p : ℝ) ^ (-(N : ℤ)) :=
    norm_padicGammaSeq_sub_le_of_le x hn (Or.inr hN3)
  have hsub : padicGammaSeq p x m - padicGammaSeq p x n =
      (padicGammaSeq p x m - padicGammaSeq p x N) -
        (padicGammaSeq p x n - padicGammaSeq p x N) := by ring
  rw [hsub]
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).one_le
  have hmono : (p : ℝ) ^ (-(N : ℤ)) ≤ (p : ℝ) ^ (-(N₀ : ℤ)) :=
    zpow_le_zpow_right₀ hp1 (by have : N₀ ≤ N := le_max_left _ _; omega)
  exact ((padicInt_norm_sub_le_max _ _).trans (max_le h1 h2)).trans_lt (hmono.trans_lt hN₀)

/-- **Morita's 1975 $p$-adic Gamma Function** `Γ_p : ℤ_[p] → ℤ_[p]`, defined as the
$p$-adic limit of `moritaGammaNat p ((PadicInt.toZModPow n x).val)`. -/
def padicGamma (p : ℕ) [Fact p.Prime] (x : ℤ_[p]) : ℤ_[p] :=
  limUnder atTop (padicGammaSeq p x)

theorem tendsto_padicGammaSeq (x : ℤ_[p]) :
    Tendsto (padicGammaSeq p x) atTop (nhds (padicGamma p x)) :=
  let ⟨L, hL⟩ := cauchySeq_tendsto_of_complete (cauchySeq_padicGammaSeq (p := p) x)
  tendsto_nhds_limUnder ⟨L, hL⟩

theorem padicGamma_eq_of_tendsto {x L : ℤ_[p]}
    (hL : Tendsto (padicGammaSeq p x) atTop (nhds L)) :
    padicGamma p x = L :=
  tendsto_nhds_unique (tendsto_padicGammaSeq x) hL

lemma norm_padicGamma_sub_seq_le (x : ℤ_[p]) {r : ℕ} (hr : p ≠ 2 ∨ 3 ≤ r) :
    ‖padicGamma p x - padicGammaSeq p x r‖ ≤ (p : ℝ) ^ (-(r : ℤ)) := by
  have hlim : Tendsto (fun n => ‖padicGammaSeq p x n - padicGammaSeq p x r‖) atTop
      (nhds ‖padicGamma p x - padicGammaSeq p x r‖) :=
    ((tendsto_padicGammaSeq x).sub_const _).norm
  refine le_of_tendsto hlim ?_
  filter_upwards [eventually_ge_atTop r] with n hn
  exact norm_padicGammaSeq_sub_le_of_le x hn hr

/-- Congruence preservation for `padicGamma`:
if `x ≡ y (mod p^r)` (with `p ≠ 2 ∨ 3 ≤ r`), then `‖Γ_p(x) - Γ_p(y)‖ ≤ p^(-r)`. -/
theorem norm_padicGamma_sub_le_of_toZModPow_eq {r : ℕ} (hr : p ≠ 2 ∨ 3 ≤ r) {x y : ℤ_[p]}
    (hxy : PadicInt.toZModPow r x = PadicInt.toZModPow r y) :
    ‖padicGamma p x - padicGamma p y‖ ≤ (p : ℝ) ^ (-(r : ℤ)) := by
  have hseq : padicGammaSeq p x r = padicGammaSeq p y r := by
    unfold padicGammaSeq
    rw [hxy]
  have hdecomp : padicGamma p x - padicGamma p y =
      (padicGamma p x - padicGammaSeq p x r) - (padicGamma p y - padicGammaSeq p y r) := by
    rw [hseq]; ring
  rw [hdecomp]
  exact (padicInt_norm_sub_le_max _ _).trans
    (max_le (norm_padicGamma_sub_seq_le x hr) (norm_padicGamma_sub_seq_le y hr))

/-- **Uniform Continuity of `padicGamma p`** on all of `ℤ_[p]` (for every prime `p`, including `p = 2`). -/
theorem uniformContinuous_padicGamma : UniformContinuous (padicGamma p) := by
  rw [Metric.uniformContinuous_iff]
  intro ε hε
  obtain ⟨r₀, hr₀⟩ := PadicInt.exists_pow_neg_lt p hε
  let r : ℕ := max r₀ 3
  have hr_pos : (0 : ℝ) < (p : ℝ) ^ (-(r : ℤ)) :=
    zpow_pos (by exact_mod_cast (Fact.out : p.Prime).pos) _
  refine ⟨(p : ℝ) ^ (-(r : ℤ)), hr_pos, fun {x y} hxy => ?_⟩
  rw [dist_eq_norm] at hxy ⊢
  have hmod : PadicInt.toZModPow r x = PadicInt.toZModPow r y :=
    padicInt_toZModPow_eq_of_norm_le_pow hxy.le
  have hle := norm_padicGamma_sub_le_of_toZModPow_eq (p := p) (Or.inr (le_max_right r₀ 3)) hmod
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).one_le
  have hmono : (p : ℝ) ^ (-(r : ℤ)) ≤ (p : ℝ) ^ (-(r₀ : ℤ)) :=
    zpow_le_zpow_right₀ hp1 (by have : r₀ ≤ r := le_max_left _ _; omega)
  exact hle.trans_lt (hmono.trans_lt hr₀)

/-- **Continuity of Morita's $p$-adic Gamma Function** on all of `ℤ_[p]`. -/
theorem continuous_padicGamma : Continuous (padicGamma p) :=
  uniformContinuous_padicGamma.continuous

/-- **1-Lipschitz Bound for Odd Primes**:
for every odd prime `p` and all `x y : ℤ_[p]`, `‖Γ_p(x) - Γ_p(y)‖ ≤ ‖x - y‖`. -/
theorem norm_padicGamma_sub_le (hp2 : p ≠ 2) (x y : ℤ_[p]) :
    ‖padicGamma p x - padicGamma p y‖ ≤ ‖x - y‖ := by
  by_cases hxy : x = y
  · simp [hxy]
  have hne : x - y ≠ 0 := sub_ne_zero.mpr hxy
  have hnorm_eq : ‖x - y‖ = (p : ℝ) ^ (-((x - y).valuation : ℤ)) :=
    PadicInt.norm_eq_zpow_neg_valuation hne
  have hmod : PadicInt.toZModPow (x - y).valuation x = PadicInt.toZModPow (x - y).valuation y :=
    padicInt_toZModPow_eq_of_norm_le_pow hnorm_eq.le
  rw [hnorm_eq]
  exact norm_padicGamma_sub_le_of_toZModPow_eq (Or.inl hp2) hmod

/-- **Interpolation on Natural Numbers**:
for every `n : ℕ` (including `n = 0, 1, 2, ...`), `Γ_p(n) = moritaGammaNat p n`. -/
theorem padicGamma_nat (n : ℕ) : padicGamma p (n : ℤ_[p]) = (moritaGammaNat p n : ℤ_[p]) := by
  have hp : p.Prime := Fact.out
  refine padicGamma_eq_of_tendsto ?_
  refine tendsto_atTop_of_eventually_const (i₀ := n) fun k hk => ?_
  unfold padicGammaSeq
  have hlt : n < p ^ k :=
    lt_of_le_of_lt hk (Nat.lt_pow_self hp.one_lt)
  have hval : (PadicInt.toZModPow k (n : ℤ_[p])).val = n := by
    rw [map_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt hlt]
  rw [hval]

@[simp] theorem padicGamma_zero : padicGamma p 0 = 1 := by
  have h := padicGamma_nat (p := p) 0
  simpa using h

@[simp] theorem padicGamma_one : padicGamma p 1 = -1 := by
  have h := padicGamma_nat (p := p) 1
  simpa using h

@[simp] theorem padicGamma_two : padicGamma p 2 = 1 := by
  have h := padicGamma_nat (p := p) 2
  simpa [moritaGammaNat_two (Fact.out : p.Prime)] using h

/-- **Unit Norm of `padicGamma`**: `‖Γ_p(x)‖ = 1` for EVERY `x : ℤ_[p]`. -/
theorem padicGamma_unit (x : ℤ_[p]) : ‖padicGamma p x‖ = 1 := by
  have hlim : Tendsto (fun n => ‖padicGammaSeq p x n‖) atTop (nhds ‖padicGamma p x‖) :=
    (tendsto_padicGammaSeq x).norm
  have hconst : (fun n => ‖padicGammaSeq p x n‖) = fun _ => (1 : ℝ) := by
    ext n
    exact norm_moritaGammaNat_eq_one (p := p) _
  rw [hconst] at hlim
  exact tendsto_nhds_unique hlim tendsto_const_nhds

/-- Every value `Γ_p(x)` is a unit in `ℤ_[p]`. -/
theorem isUnit_padicGamma (x : ℤ_[p]) : IsUnit (padicGamma p x) :=
  PadicInt.isUnit_iff.mpr (padicGamma_unit x)

/-- Characterization of unit norm in `ℤ_[p]` via reduction mod `p`. -/
lemma padicInt_norm_eq_one_iff_toZMod_ne_zero (x : ℤ_[p]) :
    ‖x‖ = 1 ↔ PadicInt.toZMod x ≠ 0 := by
  constructor
  · intro h1 h0
    have hker : x ∈ Ideal.span ({(p : ℤ_[p])} : Set ℤ_[p]) := by
      rw [← padicInt_ker_toZMod_eq_span_p, RingHom.mem_ker]
      exact h0
    have hpow : PadicInt.toZModPow 1 x = 0 := by
      rw [← RingHom.mem_ker, PadicInt.ker_toZModPow, pow_one]
      exact hker
    have hle : ‖x - 0‖ ≤ (p : ℝ) ^ (-(1 : ℤ)) :=
      padicInt_norm_le_pow_of_toZModPow_eq (by simpa using hpow)
    rw [sub_zero, h1, zpow_neg_one] at hle
    have hlt : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt)
    linarith
  · intro hne
    refine le_antisymm (PadicInt.norm_le_one x) (le_of_not_gt fun hlt => ?_)
    have hd : (p : ℤ_[p]) ∣ x := (PadicInt.norm_lt_one_iff_dvd x).mp hlt
    obtain ⟨q, rfl⟩ := hd
    apply hne
    rw [map_mul, map_natCast, ZMod.natCast_self, zero_mul]

/-- **Morita's Functional Equation**:
for EVERY `x : ℤ_[p]`,
`Γ_p(x + 1) = (if ‖x‖ = 1 then -x else -1) * Γ_p(x)`. -/
theorem padicGamma_add_one (x : ℤ_[p]) :
    padicGamma p (x + 1) = (if ‖x‖ = 1 then -x else -1) * padicGamma p x := by
  have hfactor : ∀ y : ℤ_[p], (if ‖y‖ = 1 then -y else -1) = -1 + unitIndicator y * (1 - y) := by
    intro y
    unfold unitIndicator
    simp only [padicInt_norm_eq_one_iff_toZMod_ne_zero]
    split_ifs <;> ring
  have hL : Continuous (fun y : ℤ_[p] => padicGamma p (y + 1)) :=
    continuous_padicGamma.comp (continuous_id.add continuous_const)
  have hR : Continuous (fun y : ℤ_[p] => (if ‖y‖ = 1 then -y else -1) * padicGamma p y) := by
    have hfun : (fun y : ℤ_[p] => (if ‖y‖ = 1 then -y else -1) * padicGamma p y) =
        (fun y : ℤ_[p] => (-1 + unitIndicator y * (1 - y)) * padicGamma p y) := by
      ext y; rw [hfactor]
    rw [hfun]
    exact (continuous_const.add
      (continuous_unitIndicator.mul (continuous_const.sub continuous_id))).mul continuous_padicGamma
  have heq : (fun y : ℤ_[p] => padicGamma p (y + 1)) =
      (fun y : ℤ_[p] => (if ‖y‖ = 1 then -y else -1) * padicGamma p y) := by
    refine PadicInt.denseRange_natCast.equalizer hL hR ?_
    ext n
    dsimp only [Function.comp_apply]
    rw [← Nat.cast_succ, padicGamma_nat, padicGamma_nat, moritaGammaNat_succ]
    have hcond : (‖(n : ℤ_[p])‖ = 1) ↔ ¬ p ∣ n := by
      rw [padicInt_norm_eq_one_iff_toZMod_ne_zero, map_natCast, ne_eq, ZMod.natCast_eq_zero_iff]
    by_cases hnd : ¬ p ∣ n
    · rw [if_pos hnd, if_pos (hcond.mpr hnd)]
      push_cast
      ring
    · rw [if_neg hnd, if_neg (fun h => hnd (hcond.mp h))]
      push_cast
      ring
  exact congrFun heq x

/-! ### Morita's Reflection Formula & Exact Value at `1/2` -/

/-- The unique representative `padicGammaResidue p x ∈ {1, ..., p}` of `x mod p`. -/
def padicGammaResidue (p : ℕ) [Fact p.Prime] (x : ℤ_[p]) : ℕ :=
  if (PadicInt.toZMod x).val = 0 then p else (PadicInt.toZMod x).val

lemma one_le_padicGammaResidue (x : ℤ_[p]) : 1 ≤ padicGammaResidue p x := by
  have hp : p.Prime := Fact.out
  unfold padicGammaResidue
  split_ifs with h
  · exact hp.one_le
  · omega

lemma padicGammaResidue_le (x : ℤ_[p]) : padicGammaResidue p x ≤ p := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  unfold padicGammaResidue
  split_ifs with h
  · exact le_rfl
  · exact (ZMod.val_lt _).le

lemma padicGammaResidue_cast_zmod (x : ℤ_[p]) :
    (padicGammaResidue p x : ZMod p) = PadicInt.toZMod x := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  unfold padicGammaResidue
  split_ifs with h
  · rw [ZMod.natCast_self]
    exact ((ZMod.val_eq_zero _).mp h).symm
  · exact ZMod.natCast_zmod_val _

lemma continuous_neg_one_pow_padicGammaResidue :
    Continuous (fun x : ℤ_[p] => (-1 : ℤ_[p]) ^ padicGammaResidue p x) := by
  rw [Metric.continuous_iff]
  intro x ε hε
  refine ⟨(p : ℝ) ^ (-(1 : ℤ)), zpow_pos (by exact_mod_cast (Fact.out : p.Prime).pos) _,
    fun y hy => ?_⟩
  have hmod1 : PadicInt.toZModPow 1 y = PadicInt.toZModPow 1 x :=
    padicInt_toZModPow_eq_of_norm_le_pow (by rw [dist_eq_norm] at hy; exact hy.le)
  have hmod : PadicInt.toZMod y = PadicInt.toZMod x := by
    have hsub : y - x ∈ Ideal.span ({(p : ℤ_[p])} : Set ℤ_[p]) := by
      have : y - x ∈ RingHom.ker (PadicInt.toZModPow 1) := by
        rw [RingHom.mem_ker, map_sub, hmod1, sub_self]
      rw [PadicInt.ker_toZModPow, pow_one] at this
      exact this
    rw [← padicInt_ker_toZMod_eq_span_p, RingHom.mem_ker, map_sub, sub_eq_zero] at hsub
    exact hsub
  simp [padicGammaResidue, hmod, hε]

/-- One-step sign recurrence for `(-1)^(padicGammaResidue p x)` (odd primes `p`). -/
lemma neg_one_pow_padicGammaResidue_add_one (hp2 : p ≠ 2) (x : ℤ_[p]) :
    (-1 : ℤ_[p]) ^ padicGammaResidue p (x + 1) =
      (if ‖x‖ = 1 then -1 else 1) * (-1 : ℤ_[p]) ^ padicGammaResidue p x := by
  have hp : p.Prime := Fact.out
  have : NeZero p := ⟨hp.ne_zero⟩
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  simp only [padicInt_norm_eq_one_iff_toZMod_ne_zero]
  let r : ℕ := (PadicInt.toZMod x).val
  have hrlt : r < p := ZMod.val_lt _
  have hzx : PadicInt.toZMod x = (r : ZMod p) := (ZMod.natCast_zmod_val _).symm
  have hzx1 : PadicInt.toZMod (x + 1) = ((r + 1 : ℕ) : ZMod p) := by
    rw [map_add, map_one, hzx, Nat.cast_add, Nat.cast_one]
  by_cases hr0 : r = 0
  · have hx0 : PadicInt.toZMod x = 0 := by rw [hzx, hr0, Nat.cast_zero]
    rw [if_neg (not_not.mpr hx0), one_mul]
    have hres_x : padicGammaResidue p x = p := by
      unfold padicGammaResidue
      exact if_pos hr0
    have hval1 : (PadicInt.toZMod (x + 1)).val = 1 := by
      rw [hzx1, hr0, zero_add, Nat.cast_one, ZMod.val_one]
    have hres_x1 : padicGammaResidue p (x + 1) = 1 := by
      unfold padicGammaResidue
      rw [hval1]
      exact if_neg one_ne_zero
    rw [hres_x, hres_x1, pow_one, Odd.neg_one_pow hpodd]
  · have hxne : PadicInt.toZMod x ≠ 0 := fun h0 => hr0 (by dsimp only [r]; rw [h0, ZMod.val_zero])
    rw [if_pos hxne]
    have hres_x : padicGammaResidue p x = r := by
      unfold padicGammaResidue
      exact if_neg hr0
    by_cases htop : r + 1 = p
    · have hzx1_0 : PadicInt.toZMod (x + 1) = 0 := by
        rw [hzx1, htop, ZMod.natCast_self]
      have hres_x1 : padicGammaResidue p (x + 1) = p := by
        unfold padicGammaResidue
        rw [hzx1_0, ZMod.val_zero, if_pos rfl]
      rw [hres_x, hres_x1]
      have hpow : (-1 : ℤ_[p]) ^ p = (-1 : ℤ_[p]) ^ (r + 1) :=
        congrArg (fun k => (-1 : ℤ_[p]) ^ k) htop.symm
      rw [hpow, pow_succ]
      ring
    · have hlt1 : r + 1 < p := by omega
      have hval1 : (PadicInt.toZMod (x + 1)).val = r + 1 := by
        rw [hzx1, ZMod.val_natCast, Nat.mod_eq_of_lt hlt1]
      have hres_x1 : padicGammaResidue p (x + 1) = r + 1 := by
        unfold padicGammaResidue
        rw [hval1]
        exact if_neg (Nat.succ_ne_zero r)
      rw [hres_x, hres_x1, pow_succ]
      ring

/-- One-step sign recurrence for the reflection product `Γ_p(x) * Γ_p(1 - x)`. -/
lemma padicGamma_reflection_step (x : ℤ_[p]) :
    padicGamma p (x + 1) * padicGamma p (1 - (x + 1)) =
      (if ‖x‖ = 1 then -1 else 1) * (padicGamma p x * padicGamma p (1 - x)) := by
  have h1 : 1 - (x + 1) = -x := by ring
  have h2 : 1 - x = -x + 1 := by ring
  rw [h1, h2, padicGamma_add_one x, padicGamma_add_one (-x), norm_neg, neg_neg]
  split_ifs <;> ring

/-- **Morita's Reflection Formula (1975)**:
for every odd prime `p` and EVERY `x : ℤ_[p]`,
`Γ_p(x) * Γ_p(1 - x) = (-1) ^ (padicGammaResidue p x)`. -/
theorem padicGamma_mul_one_sub (hp2 : p ≠ 2) (x : ℤ_[p]) :
    padicGamma p x * padicGamma p (1 - x) = (-1 : ℤ_[p]) ^ padicGammaResidue p x := by
  have hL : Continuous (fun y : ℤ_[p] => padicGamma p y * padicGamma p (1 - y)) :=
    continuous_padicGamma.mul (continuous_padicGamma.comp (continuous_const.sub continuous_id))
  have hR : Continuous (fun y : ℤ_[p] => (-1 : ℤ_[p]) ^ padicGammaResidue p y) :=
    continuous_neg_one_pow_padicGammaResidue
  have heq : (fun y : ℤ_[p] => padicGamma p y * padicGamma p (1 - y)) =
      (fun y : ℤ_[p] => (-1 : ℤ_[p]) ^ padicGammaResidue p y) := by
    refine PadicInt.denseRange_natCast.equalizer hL hR ?_
    ext n
    dsimp only [Function.comp_apply]
    induction n with
    | zero =>
      have hpodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp2
      have hres0 : padicGammaResidue p 0 = p := by simp [padicGammaResidue]
      simp [hres0, Odd.neg_one_pow hpodd]
    | succ n ih =>
      rw [Nat.cast_succ, padicGamma_reflection_step, neg_one_pow_padicGammaResidue_add_one hp2, ih]
  exact congrFun heq x

/-- **Exact Value of `Γ_p(1/2)²`** for any `h : ℤ_[p]` satisfying `2 * h = 1` (odd prime `p`):
`(Γ_p(h)) ^ 2 = (-1) ^ ((p + 1) / 2)`. -/
theorem padicGamma_half_sq_of_two_mul (hp2 : p ≠ 2) {h : ℤ_[p]} (hh : 2 * h = 1) :
    (padicGamma p h) ^ 2 = (-1 : ℤ_[p]) ^ ((p + 1) / 2) := by
  have hp : p.Prime := Fact.out
  have : NeZero p := ⟨hp.ne_zero⟩
  have h1sub : 1 - h = h := by linear_combination -hh
  have hmod2 : (2 : ZMod p) * PadicInt.toZMod h = 1 := by
    have := congrArg PadicInt.toZMod hh
    simpa [map_mul, map_ofNat, map_one] using this
  have h2_ne : (2 : ZMod p) ≠ 0 := by
    intro h0
    have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp (by simpa using h0)
    have := Nat.le_of_dvd (by decide) hd
    have := hp.two_le
    omega
  have h2half : 2 * ((p + 1) / 2) = p + 1 := by
    have hodd : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two hp2)
    omega
  have hmod_half : (2 : ZMod p) * (((p + 1) / 2 : ℕ) : ZMod p) = 1 := by
    have : ((2 * ((p + 1) / 2) : ℕ) : ZMod p) = 1 := by
      rw [h2half, Nat.cast_add, ZMod.natCast_self, zero_add, Nat.cast_one]
    simpa [Nat.cast_mul] using this
  have hzmod_h : PadicInt.toZMod h = (((p + 1) / 2 : ℕ) : ZMod p) :=
    mul_left_cancel₀ h2_ne (hmod2.trans hmod_half.symm)
  have hlt : (p + 1) / 2 < p := by
    have := hp.two_le
    omega
  have hpos : (p + 1) / 2 ≠ 0 := by
    have := hp.two_le
    omega
  have hres : padicGammaResidue p h = (p + 1) / 2 := by
    unfold padicGammaResidue
    rw [hzmod_h, ZMod.val_natCast, Nat.mod_eq_of_lt hlt, if_neg hpos]
  calc (padicGamma p h) ^ 2 = padicGamma p h * padicGamma p h := sq _
    _ = padicGamma p h * padicGamma p (1 - h) := by rw [h1sub]
    _ = (-1 : ℤ_[p]) ^ padicGammaResidue p h := padicGamma_mul_one_sub hp2 h
    _ = (-1 : ℤ_[p]) ^ ((p + 1) / 2) := by rw [hres]

/-- **Exact Value of `Γ_p(1/2)²` via `PadicInt.inv 2`** (odd prime `p`):
`(Γ_p(PadicInt.inv 2)) ^ 2 = (-1) ^ ((p + 1) / 2)`. -/
theorem padicGamma_half_sq (hp2 : p ≠ 2) :
    (padicGamma p (PadicInt.inv (2 : ℤ_[p]))) ^ 2 = (-1 : ℤ_[p]) ^ ((p + 1) / 2) := by
  have hp : p.Prime := Fact.out
  have hnorm2 : ‖(2 : ℤ_[p])‖ = 1 := by
    rw [padicInt_norm_eq_one_iff_toZMod_ne_zero]
    intro h0
    have h2 : ((2 : ℕ) : ZMod p) = 0 := by
      rw [← map_natCast PadicInt.toZMod]
      simpa using h0
    have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h2
    have := Nat.le_of_dvd (by decide) hd
    have := hp.two_le
    omega
  exact padicGamma_half_sq_of_two_mul hp2 (PadicInt.mul_inv hnorm2)

end MoritaPadicGamma

end RHDirect.Stage9PadicGamma
