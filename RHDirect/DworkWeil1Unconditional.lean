/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Dwork's Rationality Theorem (Weil Conjecture I) — 100% Unconditional

Proves **Dwork's Rationality Theorem (1960) — Weil Conjecture I — 100% unconditionally**
for ANY finite system of multivariate polynomials `fs : Finset (MvPolynomial (Fin n) (GaloisField p r))`
over ANY finite field `𝔽_q` (`q = p^r`, `p` prime, `r > 0`) in ANY dimension `n : ℕ`:

```lean
theorem dwork_rationality_unconditional
    (p r n : ℕ) [Fact p.Prime] (hr : 0 < r)
    (fs : Finset (MvPolynomial (Fin n) (GaloisField p r))) :
    ∃ P Q : Polynomial ℚ, Q.coeff 0 = 1 ∧
      hasseWeilZeta (affinePointCount p r fs) * (Q : PowerSeries ℚ) = (P : PowerSeries ℚ)
```

Architecture:
1. Generalized Borel–Dwork rationality criterion `borel_dwork_rationality_of_field` over any
   ultrametric normed field `K` of characteristic `0` with `‖(p : K)‖ = p⁻¹` (using
   `DworkRat.padic_hankel_decay`, `DworkRat.hankelDet_natAbs_le`, `DworkRat.kronecker_recurrence`).
2. `p`-adic entire infinite Fredholm determinant `dworkFredholmSeries` as the coefficientwise limit
   of finite truncations `det(1 - T · M_N)`, proving `p`-adic entireness (via the elementary
   `M₀ |S| - M₀ |B_{M₀}|` degree-sum lower bound) and passing `DworkRat.expSeries_traceLog_mul_detOneSubMul`
   to the limit `N → ∞`: `expSeries (infTraceLog) * dworkFredholmSeries = 1`.
3. Frobenius-orbit Euler-product integrality & archimedean bound `0 ≤ coeff k Z ≤ (q^n)^k`
   for torus hypersurfaces, combined with `DworkTraceFormula.dwork_trace_formula` and
   `borel_dwork_rationality_of_field` to prove rationality of every torus hypersurface.
4. Coordinate-support torus stratification (`𝔸^n = ⨆_{S ⊆ Fin n} 𝔾_m^{|S|}`), inclusion–exclusion
   reduction from arbitrary `fs : Finset (MvPolynomial (Fin n) (GaloisField p r))` to single
   polynomials, exact canonical equivalence `affinePointCount_eq_galoisField` to `Fintype.card`
   over `GaloisField p (r * m)`, and the unconditional crown theorem `dwork_rationality_unconditional`.
-/
import RHDirect.DworkTraceFormula
import RHDirect.DworkRatMain
import RHDirect.DworkRatZeta
import RHDirect.DworkRatFredholmComplete
import RHDirect.Stage3DworkFrobenius
import Mathlib.FieldTheory.SplittingField.IsSplittingField
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.GroupTheory.Perm.Support
import Mathlib.Tactic

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000
set_option linter.unusedSectionVars false

noncomputable section

open Real Finset Filter Topology BigOperators PowerSeries Matrix
open scoped Classical
open RHDirect.PAdicChainValuation
open RHDirect.Stage2DworkExp
open RHDirect.Stage3DworkFrobenius
open RHDirect.Stage14M5_WittFrobeniusDwork
open RHDirect.DworkRat

namespace RHDirect.DworkWeil1

instance dworkField_charZero_inst (p : ℕ) [Fact p.Prime] : CharZero (DworkField p) :=
  dworkField_charZero p

/-! ## Section 1: Generalized Borel–Dwork Criterion & Rational Power-Series Algebra -/

section BorelDworkGeneral

/-- **Ultrametric Borel Integrality over any `p`-adic field `K`**:
if `‖(p : K)‖ = p⁻¹` and `(z.natAbs : ℝ) * ‖(z : K)‖ < 1`, then `z = 0`. -/
lemma eq_zero_of_natAbs_mul_norm_lt_one_of_field {p : ℕ} [hp : Fact p.Prime]
    {K : Type*} [NormedField K] [IsUltrametricDist K] [CharZero K]
    (hnp : ‖(p : K)‖ = (p : ℝ)⁻¹) {z : ℤ}
    (hlt : (z.natAbs : ℝ) * ‖(z : K)‖ < 1) : z = 0 := by
  by_contra hz
  have hna_ne : z.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hz
  have hlt1 : ‖(p : K)‖ < 1 := by
    rw [hnp]; exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.out.one_lt)
  have hnorm_z : ‖(z : K)‖ = ‖(z.natAbs : K)‖ := by
    rcases Int.natAbs_eq z with h | h
    · conv_lhs => rw [h]
      rw [Int.cast_natCast]
    · conv_lhs => rw [h]
      rw [Int.cast_neg, norm_neg, Int.cast_natCast]
  rw [hnorm_z, norm_natCast_eq_pow_padicValNat hp.out hlt1 hna_ne, hnp] at hlt
  set v := padicValNat p z.natAbs
  obtain ⟨u, hu⟩ := pow_padicValNat_dvd (p := p) (n := z.natAbs)
  have hu_pos : 1 ≤ u := by
    by_contra h0
    have hu0 : u = 0 := by omega
    rw [hu0, mul_zero] at hu
    exact hna_ne hu
  have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.out.pos
  have hprod : (z.natAbs : ℝ) * ((p : ℝ)⁻¹) ^ v = (u : ℝ) := by
    rw [hu, Nat.cast_mul, Nat.cast_pow, inv_pow]
    change ((p : ℝ) ^ v * (u : ℝ)) * ((p : ℝ) ^ v)⁻¹ = (u : ℝ)
    field_simp [pow_ne_zero v hp_pos.ne']
  rw [hprod] at hlt
  have hu_ge : (1 : ℝ) ≤ (u : ℝ) := by exact_mod_cast hu_pos
  linarith

/-- **Generalized Borel–Dwork Rationality Criterion over any `p`-adic field `K`**:
an integer power series with archimedean exponential growth and `p`-adic meromorphic continuation
over ANY ultrametric field `K` with `‖(p : K)‖ = p⁻¹` is rational over `ℚ`! -/
theorem borel_dwork_rationality_of_field {p : ℕ} [hp : Fact p.Prime]
    {K : Type*} [NormedField K] [IsUltrametricDist K] [CharZero K]
    (hnp : ‖(p : K)‖ = (p : ℝ)⁻¹) (a : ℕ → ℤ)
    (h_arch : ∃ C₀ A : ℕ, ∀ n, (a n).natAbs ≤ C₀ * A ^ n)
    (h_mero : ∃ (g h : PowerSeries K),
      (PowerSeries.mk fun n => (a n : K)) * h = g ∧ PowerSeries.coeff 0 h = 1 ∧
      (∀ r : ℝ, 0 < r → ∃ C : ℝ, ∀ n,
        ‖PowerSeries.coeff n g‖ ≤ C * r ^ (-(n : ℤ)) ∧
        ‖PowerSeries.coeff n h‖ ≤ C * r ^ (-(n : ℤ)))) :
    IsRationalPS (PowerSeries.mk fun n => (a n : ℚ)) := by
  obtain ⟨C₀, A, hA⟩ := h_arch
  obtain ⟨g, h, hgh, hh0, h_entire⟩ := h_mero
  let r : ℝ := 16 * (max A 1 : ℝ) ^ 8 + 1
  have hr1 : 1 < r := by
    dsimp [r]
    have hmax : 1 ≤ (max A 1 : ℝ) := by exact_mod_cast le_max_right A 1
    have hp8 : 0 < (max A 1 : ℝ) ^ 8 := pow_pos (by linarith) 8
    linarith [mul_pos (by norm_num : (0 : ℝ) < 16) hp8]
  have hr0 : 0 ≤ r := by linarith
  have hrpos' : 0 < r ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos (by linarith : 0 < r) _
  have hrA : (2 * (max A 1 : ℝ) ^ 2) ^ 4 < r := by
    dsimp [r]
    have : (2 * (max A 1 : ℝ) ^ 2) ^ 4 = 16 * (max A 1 : ℝ) ^ 8 := by ring
    linarith
  obtain ⟨C, hC⟩ := h_entire r (by linarith)
  let C' : ℝ := max C 1
  have hC'1 : 1 ≤ C' := le_max_right _ _
  have hC'0 : 0 ≤ C' := by linarith
  have hg : ∀ n, ‖PowerSeries.coeff n g‖ ≤ C' * r ^ (-(n : ℤ)) := fun n =>
    (hC n).1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (zpow_nonneg hr0 _))
  have hh : ∀ n, ‖PowerSeries.coeff n h‖ ≤ C' * r ^ (-(n : ℤ)) := fun n =>
    (hC n).2.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (zpow_nonneg hr0 _))
  have hpadic : ∀ m, ‖(hankelDet a 0 m : K)‖ ≤
      (C' * r ^ (-((m / 2 : ℕ) : ℤ))) ^ (m + 1 - m / 2) := fun m =>
    padic_hankel_decay a g h hgh hh0 hr1 hC'1 hg hh m
  have harch : ∀ m, (hankelDet a 0 m).natAbs ≤
      Nat.factorial (m + 1) * (C₀ * (max A 1) ^ (2 * m)) ^ (m + 1) := fun m => by
    have hbound : ∀ n, (a n).natAbs ≤ C₀ * (max A 1) ^ n := fun n =>
      (hA n).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (le_max_left _ _) n))
    simpa using hankelDet_natAbs_le (show 1 ≤ max A 1 by omega) hbound 0 m
  set q : ℝ := 2 * (max A 1 : ℝ) ^ 2 / r ^ (1 / 4 : ℝ)
  have hq0 : 0 ≤ q := div_nonneg (mul_nonneg (by norm_num) (pow_two_nonneg _)) hrpos'.le
  have hq1 : q < 1 := by
    dsimp [q]
    rw [div_lt_one hrpos']
    by_contra hge
    push Not at hge
    have hpow : (r ^ (1 / 4 : ℝ)) ^ 4 ≤ (2 * (max A 1 : ℝ) ^ 2) ^ 4 := by gcongr
    have hy : (r ^ (1 / 4 : ℝ)) ^ 4 = r := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hr0,
        show (1 / 4 : ℝ) * ((4 : ℕ) : ℝ) = 1 by norm_num, Real.rpow_one]
    rw [hy] at hpow
    linarith [hrA]
  set D : ℝ := 2 * (max A 1 : ℝ) ^ 2 * (C₀ : ℝ) * C'
  have hD0 : 0 ≤ D := mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (pow_two_nonneg _))
    (Nat.cast_nonneg _)) hC'0
  have hprod : ∀ m, ((hankelDet a 0 m).natAbs : ℝ) * ‖(hankelDet a 0 m : K)‖ ≤
      ((C₀ : ℝ) * C' + 1) * r ^ (1 / 4 : ℝ) * D ^ m * q ^ (m * m) := by
    intro m
    have h1 : ((hankelDet a 0 m).natAbs : ℝ) ≤
        (Nat.factorial (m + 1) : ℝ) * ((C₀ : ℝ) * (max A 1 : ℝ) ^ (2 * m)) ^ (m + 1) := by
      exact_mod_cast harch m
    have hfact : (Nat.factorial (m + 1) : ℝ) ≤ (2 : ℝ) ^ (m * (m + 1)) := by
      have hf : (Nat.factorial (m + 1) : ℝ) ≤ ((m + 1) : ℝ) ^ (m + 1) := by
        exact_mod_cast Nat.factorial_le_pow (m + 1)
      have h2nat : ∀ n : ℕ, n + 1 ≤ 2 ^ n := fun n => by
        induction n with
        | zero => norm_num
        | succ n ih => have := Nat.one_le_pow n 2 (by norm_num); rw [pow_succ]; omega
      have h2 : ((m + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ m := by exact_mod_cast h2nat m
      calc (Nat.factorial (m + 1) : ℝ) ≤ ((m + 1 : ℕ) : ℝ) ^ (m + 1) := by simpa using hf
        _ ≤ ((2 : ℝ) ^ m) ^ (m + 1) := by gcongr
        _ = (2 : ℝ) ^ (m * (m + 1)) := by rw [← pow_mul]
    have hd : ((m / 2 : ℕ) : ℝ) * ((m : ℝ) + 1 - ((m / 2 : ℕ) : ℝ)) ≥
        ((m : ℝ) * (m : ℝ) - 1) / 4 := by
      have hpar : m % 2 = 0 ∨ m % 2 = 1 := by omega
      rcases hpar with hpar | hpar
      · have hm : (m : ℝ) = 2 * ((m / 2 : ℕ) : ℝ) := by
          have := congrArg (fun k : ℕ => (k : ℝ)) (show m = 2 * (m / 2) by omega)
          push_cast at this; linarith
        rw [hm]; nlinarith [Nat.cast_nonneg (α := ℝ) (m / 2)]
      · have hm : (m : ℝ) = 2 * ((m / 2 : ℕ) : ℝ) + 1 := by
          have := congrArg (fun k : ℕ => (k : ℝ)) (show m = 2 * (m / 2) + 1 by omega)
          push_cast at this; linarith
        rw [hm]; nlinarith [Nat.cast_nonneg (α := ℝ) (m / 2)]
    have hC'pow : C' ^ (m + 1 - m / 2) ≤ C' ^ (m + 1) := by gcongr; omega
    have hrpow : r ^ (-((m / 2 : ℕ) : ℤ) * ((m + 1 - m / 2 : ℕ) : ℤ)) ≤
        (r ^ (1 / 4 : ℝ)) ^ (-(m * m : ℝ)) * r ^ (1 / 4 : ℝ) := by
      have hL : r ^ (-((m / 2 : ℕ) : ℤ) * ((m + 1 - m / 2 : ℕ) : ℤ)) =
          r ^ (-(((m / 2 : ℕ) * (m + 1 - m / 2) : ℕ) : ℝ)) := by
        have heq : -((m / 2 : ℕ) : ℤ) * ((m + 1 - m / 2 : ℕ) : ℤ) =
            -(((m / 2 : ℕ) * (m + 1 - m / 2) : ℕ) : ℤ) := by rw [neg_mul, ← Nat.cast_mul]
        rw [heq, ← Real.rpow_intCast]
        simp only [Int.cast_neg, Int.cast_natCast]
      have hR : (r ^ (1 / 4 : ℝ)) ^ (-(m * m : ℝ)) * r ^ (1 / 4 : ℝ) =
          r ^ (-(((m : ℝ) * (m : ℝ) - 1) / 4)) := by
        rw [← Real.rpow_mul hr0, ← Real.rpow_add (by linarith : 0 < r)]; ring_nf
      rw [hL, hR]
      refine Real.rpow_le_rpow_of_exponent_le hr1.le ?_
      have hcast : (((m / 2 : ℕ) * (m + 1 - m / 2) : ℕ) : ℝ) =
          ((m / 2 : ℕ) : ℝ) * ((m : ℝ) + 1 - ((m / 2 : ℕ) : ℝ)) := by
        rw [Nat.cast_mul, Nat.cast_sub (by omega : m / 2 ≤ m + 1)]; push_cast; ring
      linarith
    set B : ℝ := (max A 1 : ℝ)
    have e1 : ((C₀ : ℝ) * B ^ (2 * m)) ^ (m + 1) =
        (C₀ : ℝ) ^ (m + 1) * (B ^ 2) ^ (m * (m + 1)) := by
      rw [mul_pow, ← pow_mul, show 2 * m * (m + 1) = 2 * (m * (m + 1)) by ring, pow_mul]
    have e2 : (C' * r ^ (-((m / 2 : ℕ) : ℤ))) ^ (m + 1 - m / 2) =
        C' ^ (m + 1 - m / 2) * r ^ (-((m / 2 : ℕ) : ℤ) * ((m + 1 - m / 2 : ℕ) : ℤ)) := by
      rw [mul_pow, ← zpow_natCast (r ^ (-((m / 2 : ℕ) : ℤ))), ← _root_.zpow_mul]
    calc ((hankelDet a 0 m).natAbs : ℝ) * ‖(hankelDet a 0 m : K)‖
        ≤ ((Nat.factorial (m + 1) : ℝ) * ((C₀ : ℝ) * B ^ (2 * m)) ^ (m + 1)) *
            (C' * r ^ (-((m / 2 : ℕ) : ℤ))) ^ (m + 1 - m / 2) :=
          mul_le_mul h1 (hpadic m) (norm_nonneg _) (by positivity)
      _ ≤ (2 : ℝ) ^ (m * (m + 1)) * ((C₀ : ℝ) * B ^ (2 * m)) ^ (m + 1) *
            (C' * r ^ (-((m / 2 : ℕ) : ℤ))) ^ (m + 1 - m / 2) := by gcongr
      _ = (2 * B ^ 2) ^ (m * (m + 1)) * ((C₀ : ℝ) ^ (m + 1) * C' ^ (m + 1 - m / 2)) *
            r ^ (-((m / 2 : ℕ) : ℤ) * ((m + 1 - m / 2 : ℕ) : ℤ)) := by
          rw [e1, e2, mul_pow]; ring
      _ ≤ (2 * B ^ 2) ^ (m * (m + 1)) * ((C₀ : ℝ) ^ (m + 1) * C' ^ (m + 1)) *
            r ^ (-((m / 2 : ℕ) : ℤ) * ((m + 1 - m / 2 : ℕ) : ℤ)) := by gcongr
      _ ≤ (2 * B ^ 2) ^ (m * (m + 1)) * ((C₀ : ℝ) ^ (m + 1) * C' ^ (m + 1)) *
            ((r ^ (1 / 4 : ℝ)) ^ (-(m * m : ℝ)) * r ^ (1 / 4 : ℝ)) := by gcongr
      _ = ((C₀ : ℝ) * C') * r ^ (1 / 4 : ℝ) * D ^ m * q ^ (m * m) := by
          have hpow : (2 * B ^ 2) ^ (m * (m + 1)) =
              (2 * B ^ 2) ^ (m * m) * (2 * B ^ 2) ^ m := by
            rw [show m * (m + 1) = m * m + m by ring, pow_add]
          have hDpow : D ^ m = (2 * B ^ 2) ^ m * (C₀ : ℝ) ^ m * C' ^ m := by
            dsimp [D, B]; rw [mul_pow, mul_pow]
          have hqpow : q ^ (m * m) = (2 * B ^ 2) ^ (m * m) * (r ^ (1 / 4 : ℝ)) ^ (-(m * m : ℝ)) := by
            dsimp [q, B]
            rw [div_pow, Real.rpow_neg hrpos'.le,
              show (m : ℝ) * (m : ℝ) = ((m * m : ℕ) : ℝ) by rw [Nat.cast_mul],
              Real.rpow_natCast, div_eq_mul_inv]
          rw [hpow, hDpow, hqpow, pow_succ, pow_succ]; ring
      _ ≤ ((C₀ : ℝ) * C' + 1) * r ^ (1 / 4 : ℝ) * D ^ m * q ^ (m * m) := by
          have : (C₀ : ℝ) * C' ≤ (C₀ : ℝ) * C' + 1 := by linarith
          gcongr
  have hN0 : ∃ M, ∀ m ≥ M, hankelDet a 0 m = 0 := by
    have hKpos : 0 < ((C₀ : ℝ) * C' + 1) * r ^ (1 / 4 : ℝ) :=
      mul_pos (by linarith [mul_nonneg (Nat.cast_nonneg C₀) hC'0]) hrpos'
    have hε : 0 < (1 : ℝ) / (((C₀ : ℝ) * C' + 1) * r ^ (1 / 4 : ℝ)) := div_pos one_pos hKpos
    obtain ⟨M, hM⟩ := exists_pow_mul_pow_sq_lt hq0 hq1 hD0 hε
    refine ⟨M, fun m hm => eq_zero_of_natAbs_mul_norm_lt_one_of_field hnp ?_⟩
    refine lt_of_le_of_lt (hprod m) ?_
    have := hM m hm
    calc ((C₀ : ℝ) * C' + 1) * r ^ (1 / 4 : ℝ) * D ^ m * q ^ (m * m)
        = (((C₀ : ℝ) * C' + 1) * r ^ (1 / 4 : ℝ)) * (D ^ m * q ^ (m * m)) := by ring
      _ < (((C₀ : ℝ) * C' + 1) * r ^ (1 / 4 : ℝ)) *
          (1 / (((C₀ : ℝ) * C' + 1) * r ^ (1 / 4 : ℝ))) := by gcongr
      _ = 1 := by field_simp
  obtain ⟨M, hM⟩ := hN0
  have hkronecker : ∃ (d : ℕ) (c : ℕ → ℚ), c d = 1 ∧ (∀ j > d, c j = 0) ∧
      ∀ n, ∑ j ∈ range (d + 1), c j * (a (n + j) : ℚ) = 0 := by
    apply kronecker_recurrence (fun n => (a n : ℚ))
    refine ⟨M, fun m hm => ?_⟩
    rw [hankel0_cast_det (K := ℚ) a m]
    exact_mod_cast hM m hm
  obtain ⟨d, c, hc1, _, hrec⟩ := hkronecker
  let qcoef : ℕ → ℚ := fun i => if i ≤ d then c (d - i) else 0
  have hrecPS : HasRecurrencePS (PowerSeries.mk fun n => (a n : ℚ)) := by
    refine ⟨d, qcoef, d, le_rfl, ⟨0, by omega, by simp [qcoef, hc1]⟩,
      fun i hi => by simp [qcoef, show ¬(i ≤ d) by omega], fun n hn => ?_⟩
    simp only [PowerSeries.coeff_mk]
    have hsum : ∑ i ∈ range (d + 1), qcoef i * (a (n - i) : ℚ) =
        ∑ j ∈ range (d + 1), c j * (a (n - d + j) : ℚ) := by
      refine Finset.sum_bij (fun (i : ℕ) _ => d - i)
        (fun i hi => Finset.mem_range.mpr (by rw [Finset.mem_range] at hi; omega))
        (fun i₁ hi₁ i₂ hi₂ h => by rw [Finset.mem_range] at hi₁ hi₂; omega)
        (fun j hj => ⟨d - j, Finset.mem_range.mpr (by rw [Finset.mem_range] at hj; omega),
          by rw [Finset.mem_range] at hj; omega⟩)
        (fun i hi => by
          rw [Finset.mem_range] at hi
          simp only [qcoef, if_pos (show i ≤ d by omega)]
          rw [show n - i = n - d + (d - i) by omega])
    rw [hsum]
    exact hrec (n - d)
  exact rational_of_recurrence hrecPS

/-! ### Closure Properties of `IsRationalPS` and `Q.coeff 0 = 1` Normalization -/

lemma isRationalPS_one {K : Type*} [Field K] : IsRationalPS (1 : PowerSeries K) :=
  ⟨1, 1, one_ne_zero, by simp⟩

lemma isRationalPS_mul {K : Type*} [Field K] {f g : PowerSeries K}
    (hf : IsRationalPS f) (hg : IsRationalPS g) : IsRationalPS (f * g) := by
  obtain ⟨P₁, Q₁, hQ₁, h1⟩ := hf
  obtain ⟨P₂, Q₂, hQ₂, h2⟩ := hg
  refine ⟨P₁ * P₂, Q₁ * Q₂, mul_ne_zero hQ₁ hQ₂, ?_⟩
  push_cast
  calc (Q₁ : PowerSeries K) * (Q₂ : PowerSeries K) * (f * g)
      = ((Q₁ : PowerSeries K) * f) * ((Q₂ : PowerSeries K) * g) := by ring
    _ = (P₁ : PowerSeries K) * (P₂ : PowerSeries K) := by rw [h1, h2]

lemma isRationalPS_inv_of_mul_eq_one {K : Type*} [Field K] {f g : PowerSeries K}
    (hf : IsRationalPS f) (hf0 : PowerSeries.constantCoeff f ≠ 0) (hfg : g * f = 1) :
    IsRationalPS g := by
  obtain ⟨P, Q, hQ, hQf⟩ := hf
  have hPne : P ≠ 0 := by
    intro hP0
    rw [hP0, Polynomial.coe_zero] at hQf
    have hf_zero : f = 0 := (mul_eq_zero.mp hQf).resolve_left (by
      intro hQ0
      apply hQ
      ext n
      have hc := congrArg (PowerSeries.coeff n) hQ0
      simpa [coeff_coe_poly] using hc)
    rw [hf_zero, map_zero] at hf0
    exact hf0 rfl
  refine ⟨Q, P, hPne, ?_⟩
  calc (P : PowerSeries K) * g
      = ((Q : PowerSeries K) * f) * g := by rw [hQf]
    _ = (Q : PowerSeries K) * (g * f) := by ring
    _ = (Q : PowerSeries K) := by rw [hfg, mul_one]

lemma isRationalPS_prod {K : Type*} [Field K] {ι : Type*} (s : Finset ι)
    (f : ι → PowerSeries K) (hf : ∀ i ∈ s, IsRationalPS (f i)) :
    IsRationalPS (∏ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty => simpa using isRationalPS_one
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact isRationalPS_mul (hf a (Finset.mem_insert_self a s))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

lemma scalePS_poly {K : Type*} [Field K] (α : K) (P : Polynomial K) :
    scalePS α (P : PowerSeries K) =
      ((∑ i ∈ Finset.range (P.natDegree + 1),
        Polynomial.monomial i (P.coeff i * α ^ i) : Polynomial K) : PowerSeries K) := by
  ext n
  rw [coeff_scalePS, coeff_coe_poly, coeff_coe_poly, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_monomial]
  by_cases hn : n < P.natDegree + 1
  · rw [Finset.sum_ite_eq', if_pos (Finset.mem_range.mpr hn)]
  · rw [Finset.sum_ite_eq', if_neg (by simpa [Finset.mem_range] using hn)]
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), zero_mul]

lemma isRationalPS_of_scalePS {K : Type*} [Field K] {α : K} (hα : α ≠ 0) {f : PowerSeries K}
    (hf : IsRationalPS (scalePS α f)) : IsRationalPS f := by
  obtain ⟨P, Q, hQ, hQf⟩ := hf
  have hback : scalePS α⁻¹ (scalePS α f) = f := by
    ext n; rw [coeff_scalePS, coeff_scalePS, mul_assoc, ← mul_pow, mul_inv_cancel₀ hα, one_pow, mul_one]
  let P' : Polynomial K := ∑ i ∈ Finset.range (P.natDegree + 1),
    Polynomial.monomial i (P.coeff i * α⁻¹ ^ i)
  let Q' : Polynomial K := ∑ i ∈ Finset.range (Q.natDegree + 1),
    Polynomial.monomial i (Q.coeff i * α⁻¹ ^ i)
  have hQ'ne : Q' ≠ 0 := by
    intro h0
    have hc := congrArg (fun R : Polynomial K => R.coeff Q.natDegree) h0
    simp only [Q', Polynomial.finsetSum_coeff, Polynomial.coeff_monomial, Polynomial.coeff_zero] at hc
    rw [Finset.sum_ite_eq', if_pos (Finset.mem_range.mpr (Nat.lt_succ_self _))] at hc
    exact mul_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hQ) (pow_ne_zero _ (inv_ne_zero hα)) hc
  refine ⟨P', Q', hQ'ne, ?_⟩
  have hmap := congrArg (scalePS α⁻¹) hQf
  rw [map_mul, hback, scalePS_poly, scalePS_poly] at hmap
  exact hmap

/-- Normalize `IsRationalPS f` (when `constantCoeff f = 1`) to `∃ P Q, Q.coeff 0 = 1 ∧ f * Q = P`. -/
theorem isRationalPS_normalized_of_const_one {K : Type*} [Field K] {f : PowerSeries K}
    (hf : IsRationalPS f) (_hf0 : PowerSeries.constantCoeff f = 1) :
    ∃ P Q : Polynomial K, Q.coeff 0 = 1 ∧ f * (Q : PowerSeries K) = (P : PowerSeries K) := by
  obtain ⟨P₀, Q₀, hQ₀, hQ₀f⟩ := hf
  -- Let `k` be the smallest index with `Q₀.coeff k ≠ 0`
  have hex : ∃ k : ℕ, Q₀.coeff k ≠ 0 := ⟨Q₀.natDegree, Polynomial.leadingCoeff_ne_zero.mpr hQ₀⟩
  let k := Nat.find hex
  have hk_ne : Q₀.coeff k ≠ 0 := Nat.find_spec hex
  have hk_lt : ∀ j < k, Q₀.coeff j = 0 := fun j hj => by
    by_contra hne; exact Nat.find_min hex hj hne
  have hk_le : k ≤ Q₀.natDegree := by
    by_contra hgt
    exact hk_ne (Polynomial.coeff_eq_zero_of_natDegree_lt (by omega))
  -- Also `P₀.coeff j = 0` for all `j < k`
  have hP₀_lt : ∀ j < k, P₀.coeff j = 0 := by
    intro j hj
    have hcoeff := congrArg (PowerSeries.coeff j) hQ₀f
    rw [PowerSeries.coeff_mul, coeff_coe_poly] at hcoeff
    rw [← hcoeff]
    refine Finset.sum_eq_zero fun ab hab => ?_
    rw [Finset.mem_antidiagonal] at hab
    rw [coeff_coe_poly, hk_lt ab.1 (by omega), zero_mul]
  let Q₁ : Polynomial K := ∑ i ∈ Finset.range (Q₀.natDegree + 1 - k),
    Polynomial.monomial i (Q₀.coeff (i + k))
  let P₁ : Polynomial K := ∑ i ∈ Finset.range (P₀.natDegree + 1),
    Polynomial.monomial i (P₀.coeff (i + k))
  have hQ₁_shift : (Q₀ : PowerSeries K) = PowerSeries.X ^ k * (Q₁ : PowerSeries K) := by
    ext n
    rw [coeff_coe_poly, PowerSeries.coeff_X_pow_mul']
    by_cases hkn : k ≤ n
    · rw [if_pos hkn, coeff_coe_poly, Polynomial.finsetSum_coeff]
      simp only [Polynomial.coeff_monomial]
      by_cases hlt : n - k < Q₀.natDegree + 1 - k
      · rw [Finset.sum_ite_eq', if_pos (Finset.mem_range.mpr hlt), Nat.sub_add_cancel hkn]
      · rw [Finset.sum_ite_eq', if_neg (by simpa [Finset.mem_range] using hlt)]
        exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    · rw [if_neg hkn]; exact hk_lt n (by omega)
  have hP₁_shift : (P₀ : PowerSeries K) = PowerSeries.X ^ k * (P₁ : PowerSeries K) := by
    ext n
    rw [coeff_coe_poly, PowerSeries.coeff_X_pow_mul']
    by_cases hkn : k ≤ n
    · rw [if_pos hkn, coeff_coe_poly, Polynomial.finsetSum_coeff]
      simp only [Polynomial.coeff_monomial]
      by_cases hlt : n - k < P₀.natDegree + 1
      · rw [Finset.sum_ite_eq', if_pos (Finset.mem_range.mpr hlt), Nat.sub_add_cancel hkn]
      · rw [Finset.sum_ite_eq', if_neg (by simpa [Finset.mem_range] using hlt)]
        exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    · rw [if_neg hkn]; exact hP₀_lt n (by omega)
  have hXne : (PowerSeries.X : PowerSeries K) ^ k ≠ 0 := pow_ne_zero k PowerSeries.X_ne_zero
  have hQ₁f : (Q₁ : PowerSeries K) * f = (P₁ : PowerSeries K) := by
    rw [hQ₁_shift, hP₁_shift, mul_assoc] at hQ₀f
    exact mul_left_cancel₀ hXne hQ₀f
  have hQ₁0 : Q₁.coeff 0 = Q₀.coeff k := by
    simp only [Q₁, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
    rw [Finset.sum_ite_eq', if_pos (Finset.mem_range.mpr (by omega)), zero_add]
  let c : K := (Q₀.coeff k)⁻¹
  refine ⟨Polynomial.C c * P₁, Polynomial.C c * Q₁, ?_, ?_⟩
  · rw [Polynomial.coeff_C_mul, hQ₁0, inv_mul_cancel₀ hk_ne]
  · push_cast
    rw [mul_comm f, mul_assoc, hQ₁f]

/-- Coefficient formula for `DworkRat.expSeries f`:
`coeff n (expSeries f) = ∑ j ∈ range (n + 1), (j! : K)⁻¹ * coeff n (f ^ j)`. -/
lemma coeff_expSeries_eq_sum {K : Type*} [Field K] [Algebra ℚ K] [CharZero K]
    {f : PowerSeries K} (hf : PowerSeries.constantCoeff f = 0) (n : ℕ) :
    PowerSeries.coeff n (expSeries f) =
      ∑ j ∈ Finset.range (n + 1), ((j.factorial : K))⁻¹ * PowerSeries.coeff n (f ^ j) := by
  have heq : expSeries f = expPS f := by
    ext m
    unfold expSeries
    change MvPowerSeries.coeff (Finsupp.single () m) (PowerSeries.subst f (PowerSeries.exp K)) = _
    rw [PowerSeries.coeff_subst (hasSubst_of_constantCoeff_zero hf)]
    rw [finsum_eq_sum_of_support_subset _ (s := Finset.range (m + 1))]
    · rw [coeff_expPS_eq_sum hf m]
      refine Finset.sum_congr rfl fun j _ => ?_
      change PowerSeries.coeff j (PowerSeries.exp K) • PowerSeries.coeff m (f ^ j) = _
      rw [PowerSeries.coeff_exp, smul_eq_mul, one_div, map_inv₀, map_natCast]
    · intro j hj
      rw [Function.mem_support] at hj
      rw [Finset.mem_coe, Finset.mem_range]
      by_contra hge
      have hgt : m < j := by omega
      have h0 : MvPowerSeries.coeff (Finsupp.single () m) (f ^ j) = 0 := by
        change PowerSeries.coeff m (f ^ j) = 0
        clear hj hge
        induction j generalizing m with
        | zero => omega
        | succ j ih =>
          rw [pow_succ, PowerSeries.coeff_mul]
          refine Finset.sum_eq_zero fun ab hab => ?_
          rw [Finset.mem_antidiagonal] at hab
          by_cases hb : ab.2 = 0
          · rw [hb, PowerSeries.coeff_zero_eq_constantCoeff, hf, mul_zero]
          · rw [ih ab.1 (by omega), zero_mul]
      rw [h0, smul_zero] at hj
      exact hj rfl
  rw [heq, coeff_expPS_eq_sum hf n]

lemma scalePS_expSeries {K : Type*} [Field K] [Algebra ℚ K] [CharZero K]
    (α : K) {f : PowerSeries K} (hf : PowerSeries.constantCoeff f = 0) :
    scalePS α (expSeries f) = expSeries (scalePS α f) := by
  have hsf : PowerSeries.constantCoeff (scalePS α f) = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff, coeff_scalePS, pow_zero, mul_one,
      PowerSeries.coeff_zero_eq_constantCoeff, hf]
  ext n
  rw [coeff_scalePS, coeff_expSeries_eq_sum hf n, coeff_expSeries_eq_sum hsf n, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← map_pow, coeff_scalePS]; ring

lemma scalePS_zetaOfCounts {K : Type*} [Field K] [Algebra ℚ K] [CharZero K]
    (α : K) (N : ℕ → K) :
    scalePS α (zetaOfCounts N) = zetaOfCounts (fun m => α ^ m * N m) := by
  rw [zetaOfCounts_eq_expSeries_zetaLog, zetaOfCounts_eq_expSeries_zetaLog,
    scalePS_expSeries α (constantCoeff_zetaLog N)]
  congr 1
  ext r
  rw [coeff_scalePS, zetaLog, zetaLog, PowerSeries.coeff_mk, PowerSeries.coeff_mk]
  split_ifs <;> ring

end BorelDworkGeneral

/-! ## Section 2: `p`-Adic Entire Infinite Fredholm Determinant & Limit Jacobi Identity -/

section InfiniteFredholm

variable (p : ℕ) [hp : Fact p.Prime]

/-- A power series `f ∈ (DworkField p)[[T]]` is `p`-adically entire if `∀ r > 0, ∃ C, ∀ n, ‖f_n‖ ≤ C r^{-n}`. -/
def IsPadicEntire (f : PowerSeries (DworkField p)) : Prop :=
  ∀ r : ℝ, 0 < r → ∃ C : ℝ, ∀ n : ℕ,
    (letI := dworkNormedField p; ‖PowerSeries.coeff n f‖ ≤ C * r ^ (-(n : ℤ)))

lemma isPadicEntire_one : IsPadicEntire p (1 : PowerSeries (DworkField p)) := by
  let _ : NormedField (DworkField p) := dworkNormedField p
  intro r hr
  refine ⟨1, fun n => ?_⟩
  rw [PowerSeries.coeff_one]
  split_ifs with h
  · subst h; simp
  · rw [norm_zero]; exact mul_nonneg zero_le_one (zpow_nonneg hr.le _)

lemma isPadicEntire_mul {f g : PowerSeries (DworkField p)}
    (hf : IsPadicEntire p f) (hg : IsPadicEntire p g) :
    IsPadicEntire p (f * g) := by
  let _ : NormedField (DworkField p) := dworkNormedField p
  have _ : IsUltrametricDist (DworkField p) := dworkField_ultra p
  intro r hr
  obtain ⟨Cf, hCf⟩ := hf r hr
  obtain ⟨Cg, hCg⟩ := hg r hr
  have hCf0 : 0 ≤ Cf := by
    have := hCf 0; simp at this; exact le_trans (norm_nonneg _) this
  have hCg0 : 0 ≤ Cg := by
    have := hCg 0; simp at this; exact le_trans (norm_nonneg _) this
  refine ⟨Cf * Cg, fun n => ?_⟩
  rw [PowerSeries.coeff_mul]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
    (mul_nonneg (mul_nonneg hCf0 hCg0) (zpow_nonneg hr.le _)) fun ab hab => ?_
  rw [Finset.mem_antidiagonal] at hab
  rw [norm_mul]
  calc ‖PowerSeries.coeff ab.1 f‖ * ‖PowerSeries.coeff ab.2 g‖
      ≤ (Cf * r ^ (-(ab.1 : ℤ))) * (Cg * r ^ (-(ab.2 : ℤ))) :=
        mul_le_mul (hCf ab.1) (hCg ab.2) (norm_nonneg _) (mul_nonneg hCf0 (zpow_nonneg hr.le _))
    _ = Cf * Cg * (r ^ (-(ab.1 : ℤ)) * r ^ (-(ab.2 : ℤ))) := by ring
    _ = Cf * Cg * r ^ (-(n : ℤ)) := by
        rw [← zpow_add₀ hr.ne']
        congr 2
        omega

lemma isPadicEntire_pow {f : PowerSeries (DworkField p)} (hf : IsPadicEntire p f) (m : ℕ) :
    IsPadicEntire p (f ^ m) := by
  induction m with
  | zero => simpa using isPadicEntire_one p
  | succ m ih => rw [pow_succ]; exact isPadicEntire_mul p ih hf

lemma isPadicEntire_prod {ι : Type*} (s : Finset ι) (f : ι → PowerSeries (DworkField p))
    (hf : ∀ i ∈ s, IsPadicEntire p (f i)) :
    IsPadicEntire p (∏ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty => simpa using isPadicEntire_one p
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact isPadicEntire_mul p (hf a (Finset.mem_insert_self a s))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

lemma isPadicEntire_one_sub_C_mul_X (α : DworkField p) :
    IsPadicEntire p (1 - PowerSeries.C α * PowerSeries.X) := by
  let _ : NormedField (DworkField p) := dworkNormedField p
  intro r hr
  refine ⟨max 1 (‖α‖ * r), fun n => ?_⟩
  rcases n with _ | _ | n
  · simp
  · simp only [map_sub, PowerSeries.coeff_one, ↓reduceIte,
      PowerSeries.coeff_C_mul, PowerSeries.coeff_X, mul_one]
    have h1 : ‖α‖ * r ≤ max 1 (‖α‖ * r) := le_max_right _ _
    have hmul := mul_le_mul_of_nonneg_right h1 (inv_nonneg.mpr hr.le)
    rw [mul_assoc, mul_inv_cancel₀ hr.ne', mul_one] at hmul
    simpa [_root_.zpow_neg_one] using hmul
  · simp only [map_sub, PowerSeries.coeff_one, Nat.succ_ne_zero, ↓reduceIte,
      PowerSeries.coeff_C_mul, PowerSeries.coeff_X, show n + 2 ≠ 1 by omega, mul_zero,
      sub_self, norm_zero]
    exact mul_nonneg (le_trans zero_le_one (le_max_left _ _)) (zpow_nonneg hr.le _)

lemma isPadicEntire_scalePS_of_norm_le_one {α : DworkField p}
    (hα : (letI := dworkNormedField p; ‖α‖ ≤ 1)) {f : PowerSeries (DworkField p)}
    (hf : IsPadicEntire p f) :
    IsPadicEntire p (scalePS α f) := by
  let _ : NormedField (DworkField p) := dworkNormedField p
  intro r hr
  obtain ⟨C, hC⟩ := hf r hr
  refine ⟨C, fun n => ?_⟩
  rw [coeff_scalePS, norm_mul, norm_pow]
  exact le_trans (mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg α) hα)) (hC n)

/-- Principal-minor expansion of `det(1 - T · A)` for any finite-indexed square matrix `A`:
`coeff k (det(1 - T · A)) = (-1)^k * ∑_{S ⊆ univ, |S|=k} det(A|_{S × S})`. -/
lemma coeff_detOneSub_eq_sum_minors {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R : Type*} [CommRing R] (A : Matrix ι ι R) (k : ℕ) :
    PowerSeries.coeff k
        (Matrix.det ((1 : Matrix ι ι (PowerSeries R)) -
          (PowerSeries.X : PowerSeries R) • A.map (fun x : R => PowerSeries.C x))) =
      (-1 : R) ^ k * ∑ S ∈ (Finset.univ : Finset ι).powersetCard k,
        (A.submatrix (Subtype.val : S → ι) Subtype.val).det := by
  -- Reindex `ι ≃ Fin (Fintype.card ι)` to invoke `Stage3DworkFrobenius.coeff_fredholmDet`
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let A' : Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) R := Matrix.reindex e e A
  have hdet_eq : Matrix.det ((1 : Matrix ι ι (PowerSeries R)) -
      (PowerSeries.X : PowerSeries R) • A.map (fun x : R => PowerSeries.C x)) =
      ((fredholmDet A' : Polynomial R) : PowerSeries R) := by
    have hpoly : ((fredholmDet A' : Polynomial R) : PowerSeries R) =
        Matrix.det ((1 : Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) (PowerSeries R)) -
          (PowerSeries.X : PowerSeries R) • A'.map (fun x : R => PowerSeries.C x)) := by
      change Polynomial.coeToPowerSeries.ringHom
        (Matrix.det ((1 : Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) (Polynomial R)) -
          (Polynomial.X : Polynomial R) • A'.map Polynomial.C)) = _
      rw [RingHom.map_det]
      congr 1; ext i j
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.sub_apply, Matrix.one_apply,
        Matrix.smul_apply, smul_eq_mul, map_sub, map_mul, Polynomial.coeToPowerSeries.ringHom_apply]
      split_ifs <;> simp
    rw [hpoly]
    have hmat : ((1 : Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) (PowerSeries R)) -
        (PowerSeries.X : PowerSeries R) • A'.map (fun x : R => PowerSeries.C x)) =
        Matrix.reindex e e ((1 : Matrix ι ι (PowerSeries R)) -
          (PowerSeries.X : PowerSeries R) • A.map (fun x : R => PowerSeries.C x)) := by
      ext i j
      simp only [A', Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.sub_apply,
        Matrix.one_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
      by_cases hij : i = j
      · subst hij; simp
      · have hne : e.symm i ≠ e.symm j := fun h => hij (e.symm.injective h)
        simp [hij, hne]
    rw [hmat, Matrix.det_reindex_self]
  have hcoeff_coe : PowerSeries.coeff k (fredholmDet A' : PowerSeries R) = (fredholmDet A').coeff k := by
    simp
  rw [hdet_eq, hcoeff_coe, coeff_fredholmDet]
  congr 1
  -- Swap `∑ σ` and `∑ S`, then identify `{σ : Perm (Fin N) | ∀ i ∉ S, σ i = i}` with `Perm S`
  have hpush : ∑ σ : Equiv.Perm (Fin (Fintype.card ι)), Equiv.Perm.sign σ •
      ∑ S ∈ (Finset.univ : Finset (Fin (Fintype.card ι))).powersetCard k,
        (if ∀ i ∉ S, σ i = i then ∏ i ∈ S, A' (σ i) i else 0) =
      ∑ S ∈ (Finset.univ : Finset (Fin (Fintype.card ι))).powersetCard k,
        ∑ σ : Equiv.Perm (Fin (Fintype.card ι)),
          if ∀ i ∉ S, σ i = i then Equiv.Perm.sign σ • ∏ i ∈ S, A' (σ i) i else 0 := by
    simp_rw [Finset.smul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun S _ => Finset.sum_congr rfl fun σ _ => ?_
    split_ifs <;> simp
  rw [hpush]
  -- Match each `S' : Finset (Fin (Fintype.card ι))` to `S = S'.map e.symm.toEmbedding`
  have hinner : ∀ S' : Finset (Fin (Fintype.card ι)),
      ∑ σ : Equiv.Perm (Fin (Fintype.card ι)),
        (if ∀ i ∉ S', σ i = i then Equiv.Perm.sign σ • ∏ i ∈ S', A' (σ i) i else 0) =
      (A'.submatrix (Subtype.val : S' → Fin (Fintype.card ι)) Subtype.val).det := by
    intro S'
    rw [Matrix.det_apply]
    have hfilt : ∑ σ : Equiv.Perm (Fin (Fintype.card ι)),
        (if ∀ i ∉ S', σ i = i then Equiv.Perm.sign σ • ∏ i ∈ S', A' (σ i) i else 0) =
        ∑ σ ∈ (Finset.univ : Finset (Equiv.Perm (Fin (Fintype.card ι)))).filter
          (fun σ => ∀ i ∉ S', σ i = i),
          Equiv.Perm.sign σ • ∏ i ∈ S', A' (σ i) i := by
      rw [← Finset.sum_subset (Finset.filter_subset
        (fun σ : Equiv.Perm (Fin (Fintype.card ι)) => ∀ i ∉ S', σ i = i) Finset.univ)]
      · refine Finset.sum_congr rfl fun σ hσ => if_pos (Finset.mem_filter.mp hσ).2
      · intro σ _ hnot
        rw [Finset.mem_filter] at hnot
        exact if_neg fun h => hnot ⟨Finset.mem_univ σ, h⟩
    rw [hfilt]
    symm
    refine Finset.sum_bij (fun (τ : Equiv.Perm S') _ => Equiv.Perm.ofSubtype τ) ?_ ?_ ?_ ?_
    · intro τ _
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, fun i hi => Equiv.Perm.ofSubtype_apply_of_not_mem τ hi⟩
    · intro τ₁ _ τ₂ _ h
      ext x
      have hx := congrArg (fun σ : Equiv.Perm (Fin (Fintype.card ι)) => σ x.1) h
      simp only [Equiv.Perm.ofSubtype_apply_of_mem _ x.2] at hx
      exact congrArg Fin.val hx
    · intro σ hσ
      rw [Finset.mem_filter] at hσ
      have hmem : ∀ x : S', σ x.1 ∈ S' := fun x => by
        by_contra hnot
        have hfix := hσ.2 (σ x.1) hnot
        have heq : σ x.1 = x.1 := σ.injective hfix
        exact hnot (heq.symm ▸ x.2)
      have hmem_inv : ∀ x : S', σ.symm x.1 ∈ S' := fun x => by
        by_contra hnot
        have hfix := hσ.2 (σ.symm x.1) hnot
        rw [σ.apply_symm_apply] at hfix
        exact hnot (hfix ▸ x.2)
      let τ : Equiv.Perm S' :=
        { toFun := fun x => ⟨σ x.1, hmem x⟩
          invFun := fun x => ⟨σ.symm x.1, hmem_inv x⟩
          left_inv := fun x => Subtype.ext (σ.symm_apply_apply x.1)
          right_inv := fun x => Subtype.ext (σ.apply_symm_apply x.1) }
      refine ⟨τ, Finset.mem_univ τ, ?_⟩
      apply Equiv.ext
      intro i
      by_cases hi : i ∈ S'
      · exact Equiv.Perm.ofSubtype_apply_of_mem τ hi
      · rw [Equiv.Perm.ofSubtype_apply_of_not_mem τ hi, hσ.2 i hi]
    · intro τ _
      rw [Equiv.Perm.sign_ofSubtype]
      congr 1
      rw [← Finset.prod_attach S']
      refine Finset.prod_congr rfl fun x _ => ?_
      simp [Matrix.submatrix_apply, Equiv.Perm.ofSubtype_apply_of_mem τ x.2]
  simp_rw [hinner]
  refine Finset.sum_bij (fun S' _ => S'.map e.symm.toEmbedding) ?_ ?_ ?_ ?_
  · intro S' hS'
    rw [Finset.mem_powersetCard] at hS' ⊢
    exact ⟨Finset.subset_univ _, by rw [Finset.card_map, hS'.2]⟩
  · intro S₁ _ S₂ _ h
    ext x
    have := congrArg (fun T : Finset ι => e.symm x ∈ T) h
    simpa [Finset.mem_map] using this
  · intro S hS
    rw [Finset.mem_powersetCard] at hS
    refine ⟨S.map e.toEmbedding, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, by
      rw [Finset.card_map, hS.2]⟩, ?_⟩
    ext x; simp
  · intro S' _
    let T' : Finset ι := S'.map e.symm.toEmbedding
    let eS : S' ≃ T' :=
      { toFun := fun x => ⟨e.symm x.1, Finset.mem_map.mpr ⟨x.1, x.2, rfl⟩⟩
        invFun := fun y => ⟨e y.1, by
          obtain ⟨a, ha, hay⟩ := Finset.mem_map.mp y.2
          have : e y.1 = a := by rw [← hay]; exact e.apply_symm_apply a
          rw [this]; exact ha⟩
        left_inv := fun x => Subtype.ext (e.apply_symm_apply x.1)
        right_inv := fun y => Subtype.ext (e.symm_apply_apply y.1) }
    have hsub : (A'.submatrix (Subtype.val : S' → Fin (Fintype.card ι)) Subtype.val) =
        Matrix.reindex eS.symm eS.symm
          (A.submatrix (Subtype.val : T' → ι) Subtype.val) := by
      ext x y
      simp [A', eS, Matrix.reindex_apply, Matrix.submatrix_apply]
    rw [hsub, Matrix.det_reindex_self]

/-- Ultrametric bound on EVERY principal minor `det(M|_{S × S})` of `dworkInfMat`:
exact permutation cancellation `∑_{u ∈ S} |τ u| = ∑_{u ∈ S} |u|` yields
`‖det(M|_{S × S})‖ ≤ p^{-c (q - 1) ∑_{u ∈ S} u.degree}`! -/
lemma norm_det_submatrix_dworkInfMat_le {d q : ℕ} {c : ℝ}
    {F : MvPowerSeries (Fin d) (DworkField p)}
    (hF : ∀ u, (letI := dworkNormedField p; ‖MvPowerSeries.coeff u F‖ ≤ (p : ℝ) ^ (-c * (u.degree : ℝ))))
    (S : Finset (Fin d →₀ ℕ)) :
    letI := dworkNormedField p
    ‖(Matrix.of fun u v : S => dworkInfMat p q F u.1 v.1).det‖ ≤
      (p : ℝ) ^ (-c * ((q : ℝ) - 1) * ∑ u ∈ S, (u.degree : ℝ)) := by
  let _ : NormedField (DworkField p) := dworkNormedField p
  have _ : IsUltrametricDist (DworkField p) := dworkField_ultra p
  have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.out.pos
  rw [Matrix.det_apply]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (Real.rpow_nonneg hppos.le _) fun τ _ => ?_
  simp only [Matrix.of_apply]
  have hunit : ‖Equiv.Perm.sign τ • ∏ i : S, dworkInfMat p q F (τ i).1 i.1‖ =
      ‖∏ i : S, dworkInfMat p q F (τ i).1 i.1‖ := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign τ) with h | h <;> simp [h]
  rw [hunit, norm_prod]
  calc ∏ i : S, ‖dworkInfMat p q F (τ i).1 i.1‖
      ≤ ∏ i : S, (p : ℝ) ^ (-c * ((q : ℝ) * ((τ i).1.degree : ℝ) - (i.1.degree : ℝ))) :=
        Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun i _ =>
          norm_dworkInfMat_le p hF (τ i).1 i.1
    _ = (p : ℝ) ^ (∑ i : S, -c * ((q : ℝ) * ((τ i).1.degree : ℝ) - (i.1.degree : ℝ))) :=
        (Real.rpow_sum_of_pos hppos _ _).symm
    _ = (p : ℝ) ^ (-c * ((q : ℝ) - 1) * ∑ u ∈ S, (u.degree : ℝ)) := by
        congr 1
        have hperm : ∑ i : S, ((τ i).1.degree : ℝ) = ∑ i : S, (i.1.degree : ℝ) :=
          Equiv.sum_comp τ (fun x : S => (x.1.degree : ℝ))
        have hsub : ∑ i : S, (i.1.degree : ℝ) = ∑ u ∈ S, (u.degree : ℝ) := by
          rw [Finset.sum_coe_sort S (fun u => (u.degree : ℝ))]
        rw [← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.mul_sum, hperm, hsub]
        ring

/-- **5-line elementary super-linear degree-sum lower bound**:
for any `M₀ : ℕ` and any `S : Finset (Fin d →₀ ℕ)`,
`M₀ * |S| - M₀ * |dworkBox d M₀| ≤ ∑_{u ∈ S} u.degree`! -/
lemma linear_le_sum_degree {d : ℕ} (M₀ : ℕ) (S : Finset (Fin d →₀ ℕ)) :
    (M₀ : ℝ) * (S.card : ℝ) - (M₀ : ℝ) * ((dworkBox d M₀).card : ℝ) ≤
      ∑ u ∈ S, (u.degree : ℝ) := by
  let B := dworkBox d M₀
  have h1 : (M₀ : ℝ) * ((S \ B).card : ℝ) ≤ ∑ u ∈ S \ B, (u.degree : ℝ) := by
    calc (M₀ : ℝ) * ((S \ B).card : ℝ)
        = ∑ _u ∈ S \ B, (M₀ : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
      _ ≤ ∑ u ∈ S \ B, (u.degree : ℝ) := Finset.sum_le_sum fun u hu => by
          have hnot : u ∉ B := (Finset.mem_sdiff.mp hu).2
          rw [mem_dworkBox] at hnot
          exact_mod_cast (show M₀ ≤ u.degree by omega)
  have h2 : ∑ u ∈ S \ B, (u.degree : ℝ) ≤ ∑ u ∈ S, (u.degree : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset fun _ _ _ => Nat.cast_nonneg _
  have hcard : S.card ≤ (S \ B).card + B.card := by
    have hsub : S ⊆ (S \ B) ∪ B := fun x hx => by
      by_cases h : x ∈ B
      · exact Finset.mem_union_right _ h
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hx, h⟩)
    exact le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)
  have hcardR : (S.card : ℝ) ≤ ((S \ B).card : ℝ) + (B.card : ℝ) := by exact_mod_cast hcard
  have hM0 : (0 : ℝ) ≤ (M₀ : ℝ) := Nat.cast_nonneg M₀
  nlinarith

/-- Truncated Fredholm determinant `det(1 - T · M_N) ∈ (DworkField p)[[T]]`. -/
def dworkTruncDet {d : ℕ} (q : ℕ) (F : MvPowerSeries (Fin d) (DworkField p)) (N : ℕ) :
    PowerSeries (DworkField p) :=
  Matrix.det ((1 : Matrix (dworkBox d N) (dworkBox d N) (PowerSeries (DworkField p))) -
    (PowerSeries.X : PowerSeries (DworkField p)) •
      (dworkTruncMat p q F N).map (fun x => PowerSeries.C x))

/-- Exact `coeff k (dworkTruncDet p q F N)` in terms of `Finset.powersetCard k` of `dworkBox d N`. -/
lemma coeff_dworkTruncDet_eq {d : ℕ} (q : ℕ) (F : MvPowerSeries (Fin d) (DworkField p)) (N k : ℕ) :
    PowerSeries.coeff k (dworkTruncDet p q F N) =
      (-1 : DworkField p) ^ k * ∑ S ∈ (dworkBox d N).powersetCard k,
        (Matrix.of fun u v : S => dworkInfMat p q F u.1 v.1).det := by
  unfold dworkTruncDet
  rw [coeff_detOneSub_eq_sum_minors]
  congr 1
  refine Finset.sum_bij (fun (T : Finset (dworkBox d N)) _ => T.map ⟨Subtype.val, Subtype.val_injective⟩)
    ?_ ?_ ?_ ?_
  · intro T hT
    rw [Finset.mem_powersetCard] at hT ⊢
    refine ⟨fun u hu => ?_, by rw [Finset.card_map, hT.2]⟩
    obtain ⟨v, _, rfl⟩ := Finset.mem_map.mp hu
    exact v.2
  · intro T₁ _ T₂ _ h
    ext v
    have := congrArg (fun S : Finset (Fin d →₀ ℕ) => v.1 ∈ S) h
    simpa [Finset.mem_map] using this
  · intro S hS
    rw [Finset.mem_powersetCard] at hS
    let T : Finset (dworkBox d N) := S.attach.map
      ⟨fun u : S => (⟨u.1, hS.1 u.2⟩ : dworkBox d N),
        fun a b h => Subtype.ext (show a.1 = b.1 from congrArg (Subtype.val : dworkBox d N → Fin d →₀ ℕ) h)⟩
    refine ⟨T, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, by
      simp [T, hS.2]⟩, ?_⟩
    ext u
    simp only [T, Finset.mem_map, Finset.mem_attach, Function.Embedding.coeFn_mk, true_and]
    constructor
    · rintro ⟨_, ⟨a, rfl⟩, rfl⟩; exact a.2
    · intro hu; exact ⟨⟨u, hS.1 hu⟩, ⟨⟨u, hu⟩, rfl⟩, rfl⟩
  · intro T _
    let eT : T ≃ (T.map ⟨Subtype.val, Subtype.val_injective⟩ : Finset (Fin d →₀ ℕ)) :=
      { toFun := fun x => ⟨x.1.1, Finset.mem_map.mpr ⟨x.1, x.2, rfl⟩⟩
        invFun := fun y =>
          have hy_mem : y.1 ∈ dworkBox d N := by
            obtain ⟨v, _, hvy⟩ := Finset.mem_map.mp y.2; exact hvy ▸ v.2
          ⟨⟨y.1, hy_mem⟩, by
            obtain ⟨v, hv, hvy⟩ := Finset.mem_map.mp y.2
            have heq : (⟨y.1, hy_mem⟩ : dworkBox d N) = v := Subtype.ext (show y.1 = v.1 from hvy.symm)
            rw [heq]; exact hv⟩
        left_inv := fun _ => Subtype.ext (Subtype.ext rfl)
        right_inv := fun _ => Subtype.ext rfl }
    have hmat : ((dworkTruncMat p q F N).submatrix (Subtype.val : T → dworkBox d N) Subtype.val) =
        Matrix.reindex eT.symm eT.symm
          (Matrix.of fun u v : (T.map ⟨Subtype.val, Subtype.val_injective⟩ : Finset (Fin d →₀ ℕ)) =>
            dworkInfMat p q F u.1 v.1) := by
      ext x y; rfl
    rw [hmat, Matrix.det_reindex_self]

/-- **Uniform `p`-adic entire bound on `dworkTruncDet p q F N` (INDEPENDENT OF `N`!)**. -/
lemma norm_coeff_dworkTruncDet_uniform {d q : ℕ} (hq : 2 ≤ q) {c : ℝ} (hc : 0 < c)
    {F : MvPowerSeries (Fin d) (DworkField p)}
    (hF : ∀ u, (letI := dworkNormedField p; ‖MvPowerSeries.coeff u F‖ ≤ (p : ℝ) ^ (-c * (u.degree : ℝ))))
    {r : ℝ} (hr : 0 < r) :
    ∃ C : ℝ, ∀ N k : ℕ,
      (letI := dworkNormedField p; ‖PowerSeries.coeff k (dworkTruncDet p q F N)‖ ≤ C * r ^ (-(k : ℤ))) := by
  let _ : NormedField (DworkField p) := dworkNormedField p
  have _ : IsUltrametricDist (DworkField p) := dworkField_ultra p
  have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.out.pos
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.out.one_lt
  have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hα : 0 < c * ((q : ℝ) - 1) := mul_pos hc (by linarith)
  -- Pick `M₀ : ℕ` large enough that `p^{α * M₀} ≥ r`
  have htend : Filter.Tendsto (fun m : ℕ => ((p : ℝ) ^ (c * ((q : ℝ) - 1))) ^ m) Filter.atTop Filter.atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (Real.one_lt_rpow hp1 hα)
  obtain ⟨M₀, hM₀⟩ := (Filter.tendsto_atTop.mp htend r).exists
  have hM₀_pow : r ≤ (p : ℝ) ^ (c * ((q : ℝ) - 1) * (M₀ : ℝ)) := by
    rw [Real.rpow_mul hppos.le, Real.rpow_natCast]; exact hM₀
  let B := dworkBox d M₀
  refine ⟨(p : ℝ) ^ (c * ((q : ℝ) - 1) * (M₀ : ℝ) * (B.card : ℝ)), fun N k => ?_⟩
  rw [coeff_dworkTruncDet_eq, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
    (mul_nonneg (Real.rpow_nonneg hppos.le _) (zpow_nonneg hr.le _)) fun S hS => ?_
  rw [Finset.mem_powersetCard] at hS
  have hdet := norm_det_submatrix_dworkInfMat_le p (q := q) hF S
  have hdeg := linear_le_sum_degree M₀ S
  rw [hS.2] at hdeg
  calc ‖(Matrix.of fun u v : S => dworkInfMat p q F u.1 v.1).det‖
      ≤ (p : ℝ) ^ (-c * ((q : ℝ) - 1) * ∑ u ∈ S, (u.degree : ℝ)) := hdet
    _ ≤ (p : ℝ) ^ (-c * ((q : ℝ) - 1) * ((M₀ : ℝ) * (k : ℝ) - (M₀ : ℝ) * (B.card : ℝ))) := by
        refine Real.rpow_le_rpow_of_exponent_le hp1.le ?_
        have hneg : -c * ((q : ℝ) - 1) = -(c * ((q : ℝ) - 1)) := by ring
        rw [hneg]; nlinarith
    _ = (p : ℝ) ^ (c * ((q : ℝ) - 1) * (M₀ : ℝ) * (B.card : ℝ)) *
        ((p : ℝ) ^ (c * ((q : ℝ) - 1) * (M₀ : ℝ))) ^ (-(k : ℤ)) := by
        rw [← Real.rpow_intCast, ← Real.rpow_mul hppos.le, ← Real.rpow_add hppos]
        congr 1; push_cast; ring
    _ ≤ (p : ℝ) ^ (c * ((q : ℝ) - 1) * (M₀ : ℝ) * (B.card : ℝ)) * r ^ (-(k : ℤ)) := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hppos.le _)
        rw [_root_.zpow_neg, _root_.zpow_neg, zpow_natCast, zpow_natCast]
        exact inv_anti₀ (pow_pos hr k) (pow_le_pow_left₀ hr.le hM₀_pow k)

/-- **Uniform Cauchy difference bound for `coeff k (dworkTruncDet p q F N)`**:
for `N₁ ≤ N₂`, `‖coeff k D_{N₂} - coeff k D_{N₁}‖ ≤ p^{-c (q - 1) N₁}`! -/
lemma norm_coeff_dworkTruncDet_sub_le {d q : ℕ} (hq : 2 ≤ q) {c : ℝ} (hc : 0 < c)
    {F : MvPowerSeries (Fin d) (DworkField p)}
    (hF : ∀ u, (letI := dworkNormedField p; ‖MvPowerSeries.coeff u F‖ ≤ (p : ℝ) ^ (-c * (u.degree : ℝ))))
    {N₁ N₂ : ℕ} (hN : N₁ ≤ N₂) (k : ℕ) :
    letI := dworkNormedField p
    ‖PowerSeries.coeff k (dworkTruncDet p q F N₂) -
      PowerSeries.coeff k (dworkTruncDet p q F N₁)‖ ≤
      (p : ℝ) ^ (-c * ((q : ℝ) - 1) * (N₁ : ℝ)) := by
  let _ : NormedField (DworkField p) := dworkNormedField p
  have _ : IsUltrametricDist (DworkField p) := dworkField_ultra p
  have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.out.pos
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.out.one_le
  have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  rw [coeff_dworkTruncDet_eq, coeff_dworkTruncDet_eq, ← mul_sub]
  have hsub_pow : (dworkBox d N₁).powersetCard k ⊆ (dworkBox d N₂).powersetCard k :=
    Finset.powersetCard_mono (dworkBox_mono hN)
  rw [← Finset.sum_sdiff hsub_pow, add_sub_cancel_right, norm_mul, norm_pow, norm_neg,
    norm_one, one_pow, one_mul]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (Real.rpow_nonneg hppos.le _) fun S hS => ?_
  rw [Finset.mem_sdiff, Finset.mem_powersetCard, Finset.mem_powersetCard] at hS
  have hnot_sub : ¬ S ⊆ dworkBox d N₁ := fun hsub => hS.2 ⟨hsub, hS.1.2⟩
  rw [Finset.not_subset] at hnot_sub
  obtain ⟨u₀, hu₀S, hu₀not⟩ := hnot_sub
  rw [mem_dworkBox] at hu₀not
  have hsum_ge : (N₁ : ℝ) ≤ ∑ u ∈ S, (u.degree : ℝ) := by
    have h1 : (N₁ : ℝ) ≤ (u₀.degree : ℝ) := by exact_mod_cast (show N₁ ≤ u₀.degree by omega)
    have h2 : (u₀.degree : ℝ) ≤ ∑ u ∈ S, (u.degree : ℝ) :=
      Finset.single_le_sum (f := fun u : Fin d →₀ ℕ => (u.degree : ℝ))
        (fun _ _ => Nat.cast_nonneg _) hu₀S
    linarith
  refine (norm_det_submatrix_dworkInfMat_le p (q := q) hF S).trans ?_
  refine Real.rpow_le_rpow_of_exponent_le hp1 ?_
  have hα : 0 ≤ c * ((q : ℝ) - 1) := mul_nonneg hc.le (by linarith)
  have hneg : -c * ((q : ℝ) - 1) = -(c * ((q : ℝ) - 1)) := by ring
  rw [hneg]; nlinarith

/-- The infinite Fredholm determinant `dworkFredholmSeries p q F := lim_{N → ∞} det(1 - T · M_N)`
in `(DworkField p)[[T]]`. -/
def dworkFredholmSeries {d : ℕ} (q : ℕ) (F : MvPowerSeries (Fin d) (DworkField p)) :
    PowerSeries (DworkField p) :=
  letI := dworkNormedField p
  PowerSeries.mk fun k => limUnder Filter.atTop (fun N => PowerSeries.coeff k (dworkTruncDet p q F N))

lemma tendsto_coeff_dworkTruncDet {d q : ℕ} (hq : 2 ≤ q) {c : ℝ} (hc : 0 < c)
    {F : MvPowerSeries (Fin d) (DworkField p)}
    (hF : ∀ u, (letI := dworkNormedField p; ‖MvPowerSeries.coeff u F‖ ≤ (p : ℝ) ^ (-c * (u.degree : ℝ))))
    (k : ℕ) :
    letI := dworkNormedField p
    Filter.Tendsto (fun N => PowerSeries.coeff k (dworkTruncDet p q F N))
      Filter.atTop (nhds (PowerSeries.coeff k (dworkFredholmSeries p q F))) := by
  let _ : NormedField (DworkField p) := dworkNormedField p
  have _ : CompleteSpace (DworkField p) := dworkField_complete p
  have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.out.pos
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.out.one_lt
  have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hα : 0 < c * ((q : ℝ) - 1) := mul_pos hc (by linarith)
  have hcauchy : CauchySeq (fun N => PowerSeries.coeff k (dworkTruncDet p q F N)) := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    have htend : Filter.Tendsto (fun N : ℕ => ((p : ℝ) ^ (-c * ((q : ℝ) - 1))) ^ N)
        Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (Real.rpow_nonneg hppos.le _)
        (Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith))
    obtain ⟨N₀, hN₀⟩ := Metric.tendsto_atTop.mp htend ε hε
    refine ⟨N₀, fun m hm n hn => ?_⟩
    wlog hmn : m ≤ n generalizing m n
    · rw [dist_comm]; exact this n hn m hm (le_of_not_ge hmn)
    rw [dist_comm, dist_eq_norm]
    have hbd := norm_coeff_dworkTruncDet_sub_le p hq hc hF hmn k
    have hlt := hN₀ m hm
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (pow_nonneg (Real.rpow_nonneg hppos.le _) m)] at hlt
    rw [← Real.rpow_natCast ((p : ℝ) ^ _), ← Real.rpow_mul hppos.le] at hlt
    exact lt_of_le_of_lt hbd hlt
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hlim : PowerSeries.coeff k (dworkFredholmSeries p q F) = L := by
    unfold dworkFredholmSeries
    rw [PowerSeries.coeff_mk]
    exact hL.limUnder_eq
  rw [hlim]
  exact hL

theorem constantCoeff_dworkFredholmSeries {d q : ℕ} (hq : 2 ≤ q) {c : ℝ} (hc : 0 < c)
    {F : MvPowerSeries (Fin d) (DworkField p)}
    (hF : ∀ u, (letI := dworkNormedField p; ‖MvPowerSeries.coeff u F‖ ≤ (p : ℝ) ^ (-c * (u.degree : ℝ)))) :
    PowerSeries.constantCoeff (dworkFredholmSeries p q F) = 1 := by
  let _ : NormedField (DworkField p) := dworkNormedField p
  rw [← PowerSeries.coeff_zero_eq_constantCoeff]
  have ht := tendsto_coeff_dworkTruncDet p hq hc hF 0
  have hconst : (fun N => PowerSeries.coeff 0 (dworkTruncDet p q F N)) = fun _ => (1 : DworkField p) := by
    ext N
    rw [coeff_dworkTruncDet_eq, pow_zero, one_mul, Finset.powersetCard_zero, Finset.sum_singleton]
    exact Matrix.det_isEmpty
  rw [hconst] at ht
  exact tendsto_nhds_unique ht tendsto_const_nhds

/-- **`p`-Adic Entireness of the Infinite Fredholm Determinant `dworkFredholmSeries`**! -/
theorem isPadicEntire_dworkFredholmSeries {d q : ℕ} (hq : 2 ≤ q) {c : ℝ} (hc : 0 < c)
    {F : MvPowerSeries (Fin d) (DworkField p)}
    (hF : ∀ u, (letI := dworkNormedField p; ‖MvPowerSeries.coeff u F‖ ≤ (p : ℝ) ^ (-c * (u.degree : ℝ)))) :
    IsPadicEntire p (dworkFredholmSeries p q F) := by
  let _ : NormedField (DworkField p) := dworkNormedField p
  intro r hr
  obtain ⟨C, hC⟩ := norm_coeff_dworkTruncDet_uniform p hq hc hF hr
  refine ⟨C, fun k => ?_⟩
  exact le_of_tendsto (tendsto_coeff_dworkTruncDet p hq hc hF k).norm
    (Filter.Eventually.of_forall fun N => hC N k)

/-- Continuity of `coeff k (expSeries (f N))` under coefficientwise convergence `coeff n (f N) → coeff n f`. -/
lemma tendsto_coeff_expSeries {K : Type*} [NormedField K] [Algebra ℚ K] [CharZero K]
    (fSeq : ℕ → PowerSeries K) (f : PowerSeries K)
    (hfSeq0 : ∀ N, PowerSeries.constantCoeff (fSeq N) = 0)
    (hf0 : PowerSeries.constantCoeff f = 0)
    (htend : ∀ n : ℕ, Filter.Tendsto (fun N => PowerSeries.coeff n (fSeq N))
      Filter.atTop (nhds (PowerSeries.coeff n f))) (k : ℕ) :
    Filter.Tendsto (fun N => PowerSeries.coeff k (expSeries (fSeq N)))
      Filter.atTop (nhds (PowerSeries.coeff k (expSeries f))) := by
  have hpow : ∀ j n : ℕ, Filter.Tendsto (fun N => PowerSeries.coeff n ((fSeq N) ^ j))
      Filter.atTop (nhds (PowerSeries.coeff n (f ^ j))) := by
    intro j
    induction j with
    | zero => intro n; exact tendsto_const_nhds
    | succ j ih =>
      intro n
      simp_rw [pow_succ, PowerSeries.coeff_mul]
      exact tendsto_finsetSum _ fun ab _ => (ih ab.1).mul (htend ab.2)
  simp_rw [coeff_expSeries_eq_sum (hfSeq0 _), coeff_expSeries_eq_sum hf0]
  exact tendsto_finsetSum _ fun j _ => tendsto_const_nhds.mul (hpow j k)

/-- Infinite trace logarithm series `infTraceLog p q F = ∑_{m ≥ 1} Tr(M^m) T^m / m`. -/
def infTraceLog {d : ℕ} (q : ℕ) (F : MvPowerSeries (Fin d) (DworkField p)) :
    PowerSeries (DworkField p) :=
  PowerSeries.mk fun m => if m = 0 then 0 else dworkInfTrace p q F m / (m : DworkField p)

lemma constantCoeff_infTraceLog {d : ℕ} (q : ℕ) (F : MvPowerSeries (Fin d) (DworkField p)) :
    PowerSeries.constantCoeff (infTraceLog p q F) = 0 := by
  simp [infTraceLog]

/-- **Infinite Nuclear Jacobi Identity**:
`expSeries (infTraceLog p q F) * dworkFredholmSeries p q F = 1` in `(DworkField p)[[T]]`! -/
theorem expSeries_infTraceLog_mul_dworkFredholmSeries {d q : ℕ} (hq : 2 ≤ q) {c : ℝ} (hc : 0 < c)
    {F : MvPowerSeries (Fin d) (DworkField p)}
    (hF : ∀ u, (letI := dworkNormedField p; ‖MvPowerSeries.coeff u F‖ ≤ (p : ℝ) ^ (-c * (u.degree : ℝ)))) :
    expSeries (infTraceLog p q F) * dworkFredholmSeries p q F = 1 := by
  let _ : NormedField (DworkField p) := dworkNormedField p
  have _ : CharZero (DworkField p) := dworkField_charZero p
  have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.out.pos
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.out.one_lt
  have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hα : 0 < c * ((q : ℝ) - 1) := mul_pos hc (by linarith)
  -- For each `N`, reindex `dworkTruncMat p q F N` to `Fin (dworkBox d N).card` and apply `DworkRat.expSeries_traceLog_mul_detOneSubMul`
  let A_fin (N : ℕ) : Matrix (Fin (dworkBox d N).card) (Fin (dworkBox d N).card) (DworkField p) :=
    Matrix.reindex (Finset.equivFin (dworkBox d N)) (Finset.equivFin (dworkBox d N))
      (dworkTruncMat p q F N)
  have hdet_eq : ∀ N, detOneSubMul (A_fin N) = dworkTruncDet p q F N := by
    intro N
    unfold detOneSubMul dworkTruncDet A_fin
    have hmat : ((1 : Matrix (Fin (dworkBox d N).card) (Fin (dworkBox d N).card) (PowerSeries (DworkField p))) -
        (PowerSeries.X : PowerSeries (DworkField p)) •
          (Matrix.reindex (Finset.equivFin (dworkBox d N)) (Finset.equivFin (dworkBox d N))
            (dworkTruncMat p q F N)).map (fun x => PowerSeries.C x)) =
        Matrix.reindex (Finset.equivFin (dworkBox d N)) (Finset.equivFin (dworkBox d N))
          ((1 : Matrix (dworkBox d N) (dworkBox d N) (PowerSeries (DworkField p))) -
            (PowerSeries.X : PowerSeries (DworkField p)) •
              (dworkTruncMat p q F N).map (fun x => PowerSeries.C x)) := by
      ext i j
      simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.sub_apply, Matrix.one_apply,
        Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
      by_cases hij : i = j
      · subst hij; simp
      · have hne : (Finset.equivFin (dworkBox d N)).symm i ≠ (Finset.equivFin (dworkBox d N)).symm j :=
          fun h => hij ((Finset.equivFin (dworkBox d N)).symm.injective h)
        simp [hij, hne]
    rw [hmat, Matrix.det_reindex_self]
  have htrace_eq : ∀ N m, ((A_fin N) ^ m).trace = ((dworkTruncMat p q F N) ^ m).trace := by
    intro N m
    have hpow : (A_fin N) ^ m =
        Matrix.reindex (Finset.equivFin (dworkBox d N)) (Finset.equivFin (dworkBox d N))
          ((dworkTruncMat p q F N) ^ m) := by
      unfold A_fin
      induction m with
      | zero => simp [Matrix.reindex_apply]
      | succ m ih =>
        rw [pow_succ, pow_succ, ih]
        ext i j
        simp only [Matrix.mul_apply, Matrix.reindex_apply, Matrix.submatrix_apply]
        exact Equiv.sum_comp (Finset.equivFin (dworkBox d N)).symm
          (fun k => ((dworkTruncMat p q F N) ^ m) ((Finset.equivFin (dworkBox d N)).symm i) k *
            dworkTruncMat p q F N k ((Finset.equivFin (dworkBox d N)).symm j))
    rw [hpow]
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.reindex_apply, Matrix.submatrix_apply]
    exact Equiv.sum_comp (Finset.equivFin (dworkBox d N)).symm
      (fun u => ((dworkTruncMat p q F N) ^ m) u u)
  have hfin_jacobi : ∀ N, expSeries (traceLog (A_fin N)) * dworkTruncDet p q F N = 1 := fun N => by
    rw [← hdet_eq N]
    exact expSeries_traceLog_mul_detOneSubMul (A_fin N)
  -- Coefficientwise convergence `coeff m (traceLog (A_fin N)) → coeff m (infTraceLog p q F)`
  have htrace_tend : ∀ m : ℕ,
      Filter.Tendsto (fun N => PowerSeries.coeff m (traceLog (A_fin N)))
        Filter.atTop (nhds (PowerSeries.coeff m (infTraceLog p q F))) := by
    intro m
    rcases m with _ | m
    · simp only [traceLog, infTraceLog, PowerSeries.coeff_mk, ↓reduceIte]
      exact tendsto_const_nhds
    · simp only [traceLog, infTraceLog, PowerSeries.coeff_mk, Nat.succ_ne_zero, ↓reduceIte,
        htrace_eq]
      refine Filter.Tendsto.div_const ?_ ((m + 1 : ℕ) : DworkField p)
      rw [tendsto_iff_norm_sub_tendsto_zero]
      have hdecay : Filter.Tendsto (fun N : ℕ => ((p : ℝ) ^ (-c * ((q : ℝ) - 1))) ^ N)
          Filter.atTop (nhds 0) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one (Real.rpow_nonneg hppos.le _)
          (Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith))
      refine squeeze_zero (fun _ => norm_nonneg _) (fun N => ?_) hdecay
      rw [norm_sub_rev]
      have hbd := norm_dworkInfTrace_sub_trunc_le p hq hc hF (Nat.succ_pos m) N
      refine hbd.trans_eq ?_
      rw [← Real.rpow_natCast ((p : ℝ) ^ _), ← Real.rpow_mul hppos.le]
      congr 1; ring
  ext k
  have hprod_tend : Filter.Tendsto
      (fun N => PowerSeries.coeff k (expSeries (traceLog (A_fin N)) * dworkTruncDet p q F N))
      Filter.atTop (nhds (PowerSeries.coeff k (expSeries (infTraceLog p q F) * dworkFredholmSeries p q F))) := by
    simp_rw [PowerSeries.coeff_mul]
    refine tendsto_finsetSum _ fun ab _ => ?_
    exact (tendsto_coeff_expSeries (fun N => traceLog (A_fin N)) (infTraceLog p q F)
      (fun N => constantCoeff_traceLog (A_fin N)) (constantCoeff_infTraceLog p q F)
      htrace_tend ab.1).mul (tendsto_coeff_dworkTruncDet p hq hc hF ab.2)
  have hconst_tend : Filter.Tendsto
      (fun N => PowerSeries.coeff k (expSeries (traceLog (A_fin N)) * dworkTruncDet p q F N))
      Filter.atTop (nhds (PowerSeries.coeff k (1 : PowerSeries (DworkField p)))) := by
    simp_rw [hfin_jacobi]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique hprod_tend hconst_tend

end InfiniteFredholm

/-! ## Section 3: Frobenius-Orbit Integrality, Archimedean Bound & Torus Hypersurface Rationality -/

section TorusRationality

variable (p : ℕ) [hp : Fact p.Prime]

/-- Torus point count `N_m^*(g) = #{x ∈ (𝔽_{(p^r)^m}ˣ)^n : g(x) = 0}` for a single polynomial
`g : MvPolynomial (Fin n) (kb p)`. -/
def torusPointCount {n : ℕ} (r : ℕ) (g : MvPolynomial (Fin n) (kb p)) (m : ℕ) : ℕ :=
  ((Fintype.piFinset fun _ : Fin n => finFieldUnits p (r * m)).filter
    (fun x => MvPolynomial.eval x g = 0)).card

/-- Frobenius linearity over `kb p = AlgebraicClosure (ZMod p)` for `p^k`-th powers. -/
lemma kb_sum_pow_prime_pow {ι : Type*} (s : Finset ι) (f : ι → kb p) (k : ℕ) :
    (∑ i ∈ s, f i) ^ (p ^ k) = ∑ i ∈ s, (f i) ^ (p ^ k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, pow_mul, ih]
    have hfr : (∑ i ∈ s, f i ^ p ^ k) ^ p = ∑ i ∈ s, (f i ^ p ^ k) ^ p := by
      change frobenius (kb p) p (∑ i ∈ s, f i ^ p ^ k) = _
      rw [map_sum]; rfl
    rw [hfr]
    exact Finset.sum_congr rfl fun i _ => by rw [← pow_mul, ← pow_succ]

lemma torusPointCount_le {n : ℕ} (r : ℕ) (g : MvPolynomial (Fin n) (kb p)) {m : ℕ}
    (hr : 1 ≤ r) (hm : 1 ≤ m) :
    torusPointCount p r g m ≤ ((p ^ r) ^ n) ^ m := by
  unfold torusPointCount
  have hrm : 1 ≤ r * m := Nat.mul_pos hr hm
  calc ((Fintype.piFinset fun _ : Fin n => finFieldUnits p (r * m)).filter _).card
      ≤ (Fintype.piFinset fun _ : Fin n => finFieldUnits p (r * m)).card := Finset.card_filter_le _ _
    _ = (p ^ (r * m) - 1) ^ n := by
        rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_fin, card_finFieldUnits p hrm]
    _ ≤ (p ^ (r * m)) ^ n := Nat.pow_le_pow_left (Nat.sub_le _ 1) n
    _ = ((p ^ r) ^ n) ^ m := by rw [← pow_mul, ← pow_mul, ← pow_mul]; congr 1; ring

/-- Coefficient of `expSeries (logSeries α)` equals `α ^ n`. -/
lemma coeff_expSeries_logSeries {K : Type*} [Field K] [Algebra ℚ K] [CharZero K] (α : K) (n : ℕ) :
    PowerSeries.coeff n (expSeries (logSeries α)) = α ^ n := by
  have h := one_sub_C_mul_X_mul_expSeries_logSeries α
  induction n with
  | zero =>
    rw [PowerSeries.coeff_zero_eq_constantCoeff, constantCoeff_expSeries (constantCoeff_logSeries α),
      pow_zero]
  | succ n ih =>
    have hc := congrArg (PowerSeries.coeff (n + 1)) h
    rw [sub_mul, one_mul, map_sub, mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_X_mul,
      PowerSeries.coeff_one, if_neg (Nat.succ_ne_zero n), ih] at hc
    rw [sub_eq_zero.mp hc, pow_succ']

/-- **Frobenius-Orbit Integrality & Archimedean Bound for `zetaOfCounts (torusPointCount p r g)`**:
there exists `a : ℕ → ℕ` such that `coeff k (zetaOfCounts N) = (a k : ℚ)` and `a k ≤ ((p^r)^n)^k`! -/
theorem torusPointCount_zeta_int_and_arch {n : ℕ} {r : ℕ} (hr : 1 ≤ r)
    (g : MvPolynomial (Fin n) (kb p))
    (hg : ∀ w ∈ g.support, (g.coeff w) ^ (p ^ r) = g.coeff w) :
    ∃ a : ℕ → ℕ,
      (∀ k, PowerSeries.coeff k (zetaOfCounts (fun m => (torusPointCount p r g m : ℚ))) = (a k : ℚ)) ∧
      (∀ k, a k ≤ ((p ^ r) ^ n) ^ k) := by
  -- Step 1: Frobenius map `φ x = fun i => (x i) ^ (p^r)` on `Fin n → kb p`
  let q := p ^ r
  let φ : (Fin n → kb p) → (Fin n → kb p) := fun x i => (x i) ^ q
  have hφ_inj : Function.Injective φ := fun x y hxy => by
    ext i
    have hi : (x i) ^ (p ^ r) = (y i) ^ (p ^ r) := congrFun hxy i
    have hpow : ∀ k (u v : kb p), u ^ (p ^ k) = v ^ (p ^ k) → u = v := fun k => by
      induction k with
      | zero => intro u v h; simpa using h
      | succ k ih =>
        intro u v h
        rw [pow_succ, pow_mul, pow_mul] at h
        have hsub : (u ^ (p ^ k) - v ^ (p ^ k)) ^ p = 0 := by
          rw [sub_pow_char, h, sub_self]
        exact ih u v (sub_eq_zero.mp (eq_zero_of_pow_eq_zero hsub))
    exact hpow r (x i) (y i) hi
  have hφ_iter : ∀ k (x : Fin n → kb p) (i : Fin n), (φ^[k] x) i = (x i) ^ (q ^ k) := fun k => by
    induction k with
    | zero => intro x i; simp
    | succ k ih =>
      intro x i
      rw [Function.iterate_succ_apply', pow_succ, pow_mul]
      change ((φ^[k] x) i) ^ q = _
      rw [ih]
  -- Fixed points of `φ^m` in `V^*(g)` are precisely the elements counted by `torusPointCount p r g m`
  let S_m (m : ℕ) : Finset (Fin n → kb p) :=
    (Fintype.piFinset fun _ : Fin n => finFieldUnits p (r * m)).filter
      (fun x => MvPolynomial.eval x g = 0)
  have hmem_Sm : ∀ {m : ℕ} (hm : 1 ≤ m) {x : Fin n → kb p},
      x ∈ S_m m ↔ (∀ i, x i ≠ 0) ∧ φ^[m] x = x ∧ MvPolynomial.eval x g = 0 := by
    intro m hm x
    have hrm : 1 ≤ r * m := Nat.mul_pos hr hm
    simp only [S_m, Finset.mem_filter, Fintype.mem_piFinset, mem_finFieldUnits p hrm]
    constructor
    · rintro ⟨hx, hev⟩
      refine ⟨fun i => (hx i).1, ?_, hev⟩
      ext i; rw [hφ_iter]; dsimp only [q]; rw [← pow_mul]; exact (hx i).2
    · rintro ⟨hne, hfix, hev⟩
      refine ⟨fun i => ⟨hne i, ?_⟩, hev⟩
      have hi := congrFun hfix i
      rw [hφ_iter] at hi; dsimp only [q] at hi; rw [← pow_mul] at hi
      exact hi
  -- `φ` preserves `S_m m` (since `g` has coefficients in `𝔽_q`)
  have hφ_eval : ∀ x : Fin n → kb p, MvPolynomial.eval (φ x) g = (MvPolynomial.eval x g) ^ q := by
    intro x
    dsimp only [q]
    rw [MvPolynomial.eval_eq', MvPolynomial.eval_eq', kb_sum_pow_prime_pow p]
    refine Finset.sum_congr rfl fun w hw => ?_
    rw [mul_pow, hg w hw, ← Finset.prod_pow]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    change ((x i) ^ (p ^ r)) ^ (w i) = ((x i) ^ (w i)) ^ (p ^ r)
    rw [← pow_mul, mul_comm, pow_mul]
  -- For every `k : ℕ`, prove `coeff k (zetaOfCounts N)` is a natural number `≤ ((p^r)^n)^k`!
  have hpointwise : ∀ k : ℕ, ∃ a : ℕ,
      PowerSeries.coeff k (zetaOfCounts (fun m => (torusPointCount p r g m : ℚ))) = (a : ℚ) ∧
      a ≤ ((p ^ r) ^ n) ^ k := by
    intro k
    -- Minimal period subsets `P_d` for `1 ≤ d ≤ k`
    let P (d : ℕ) : Finset (Fin n → kb p) :=
      (S_m d).filter (fun x => ∀ e ∈ Finset.Ico 1 d, φ^[e] x ≠ x)
    let orb (d : ℕ) (x : Fin n → kb p) : Finset (Fin n → kb p) :=
      (Finset.range d).image (fun j => φ^[j] x)
    let c (d : ℕ) : ℕ := ((P d).image (orb d)).card
    -- `d * c d = (P d).card` for `1 ≤ d`
    have hP_card : ∀ d : ℕ, 1 ≤ d → (P d).card = d * c d := by
      intro d hd
      have horb_mem : ∀ x ∈ P d, ∀ j < d, φ^[j] x ∈ P d := by
        intro x hx j _
        simp only [P, Finset.mem_filter, hmem_Sm hd] at hx ⊢
        obtain ⟨⟨hne, hfix, hev⟩, hmin⟩ := hx
        refine ⟨⟨fun i => by rw [hφ_iter]; exact pow_ne_zero _ (hne i), ?_, ?_⟩, fun e he heq => ?_⟩
        · rw [← Function.iterate_add_apply, add_comm, Function.iterate_add_apply, hfix]
        · have hevj : ∀ t, MvPolynomial.eval (φ^[t] x) g = (MvPolynomial.eval x g) ^ (q ^ t) := fun t => by
            induction t with
            | zero => simp
            | succ t iht =>
              rw [Function.iterate_succ_apply', hφ_eval, iht, ← pow_mul, ← pow_succ]
          rw [hevj j, hev, zero_pow (pow_ne_zero j (pow_ne_zero r hp.out.ne_zero))]
        · rw [← Function.iterate_add_apply, add_comm, Function.iterate_add_apply] at heq
          exact hmin e he ((Function.Injective.iterate hφ_inj j) heq)
      have horb_card : ∀ x ∈ P d, (orb d x).card = d := by
        intro x hx
        simp only [P, Finset.mem_filter] at hx
        rw [Finset.card_image_of_injOn]
        · exact Finset.card_range d
        · intro a ha b hb hab
          rw [Finset.mem_coe, Finset.mem_range] at ha hb
          by_contra hne
          wlog hlt : a < b generalizing a b
          · exact this hb ha hab.symm (Ne.symm hne) (by omega)
          have hdiff : φ^[b - a] x = x := by
            apply Function.Injective.iterate hφ_inj a
            rw [← Function.iterate_add_apply, Nat.add_sub_cancel' hlt.le]
            exact hab.symm
          exact hx.2 (b - a) (Finset.mem_Ico.mpr ⟨by omega, by omega⟩) hdiff
      have horb_eq_or_disj : ∀ x ∈ P d, ∀ y ∈ P d, orb d x = orb d y ∨ Disjoint (orb d x) (orb d y) := by
        intro x hx y hy
        by_cases hdisj : Disjoint (orb d x) (orb d y)
        · exact Or.inr hdisj
        · left
          rw [Finset.not_disjoint_iff] at hdisj
          obtain ⟨z, hzx, hzy⟩ := hdisj
          obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hzx
          obtain ⟨b, hb, hby⟩ := Finset.mem_image.mp hzy
          simp only [P, Finset.mem_filter] at hx hy
          have hxfix : φ^[d] x = x := ((hmem_Sm hd).mp hx.1).2.1
          have hyfix : φ^[d] y = y := ((hmem_Sm hd).mp hy.1).2.1
          have hiter_mod : ∀ (u : Fin n → kb p), φ^[d] u = u → ∀ t, φ^[t] u = φ^[t % d] u := by
            intro u hu t
            have hmul : ∀ s, φ^[d * s] u = u := fun s => by
              induction s with
              | zero => simp
              | succ s ihs =>
                rw [Nat.mul_succ, add_comm, Function.iterate_add_apply, ihs, hu]
            have hdiv2 : d * (t / d) + t % d = t := Nat.div_add_mod t d
            conv_lhs => rw [← hdiv2, add_comm, Function.iterate_add_apply, hmul]
          -- Show `orb d x ⊆ orb d y` and compare cardinalities!
          have hsub : orb d x ⊆ orb d y := by
            intro w hw
            obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hw
            have hmod : (j + d - a + b) % d < d := Nat.mod_lt _ hd
            refine Finset.mem_image.mpr ⟨(j + d - a + b) % d, Finset.mem_range.mpr hmod, ?_⟩
            rw [← hiter_mod y hyfix, Function.iterate_add_apply, hby,
              ← Function.iterate_add_apply, hiter_mod x hxfix]
            have ha_lt : a < d := Finset.mem_range.mp ha
            have heq_mod : (j + d - a + a) % d = j % d := by
              rw [Nat.sub_add_cancel (by omega), Nat.add_mod_right]
            rw [heq_mod, Nat.mod_eq_of_lt (Finset.mem_range.mp hj)]
          have hxP : x ∈ P d := by simp only [P, Finset.mem_filter]; exact hx
          have hyP : y ∈ P d := by simp only [P, Finset.mem_filter]; exact hy
          exact Finset.eq_of_subset_of_card_le hsub (by rw [horb_card x hxP, horb_card y hyP])
      have hbi : P d = ((P d).image (orb d)).biUnion id := by
        ext z
        simp only [Finset.mem_biUnion, Finset.mem_image, id_eq]
        constructor
        · intro hz
          exact ⟨orb d z, ⟨z, hz, rfl⟩, Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr hd, rfl⟩⟩
        · rintro ⟨_, ⟨x, hx, rfl⟩, hzx⟩
          obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hzx
          exact horb_mem x hx j (Finset.mem_range.mp hj)
      have hpw : ((P d).image (orb d) : Set (Finset (Fin n → kb p))).PairwiseDisjoint id := by
        intro O₁ hO₁ O₂ hO₂ hne
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hO₁
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hO₂
        exact (horb_eq_or_disj x hx y hy).resolve_left hne
      rw [hbi, Finset.card_biUnion hpw]
      have hsum_const : ∑ O ∈ (P d).image (orb d), O.card = ∑ _O ∈ (P d).image (orb d), d := by
        refine Finset.sum_congr rfl fun O hO => ?_
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hO
        exact horb_card x hx
      simp only [id_eq]
      rw [hsum_const, Finset.sum_const, smul_eq_mul, mul_comm]
    -- Partition `S_m m` by minimal period `d ∣ m` (for `1 ≤ m ≤ k`)
    have hSm_eq : ∀ m : ℕ, 1 ≤ m → m ≤ k →
        (S_m m).card = ∑ d ∈ Finset.Icc 1 k, if d ∣ m then d * c d else 0 := by
      intro m hm hmk
      have hpart : S_m m = ((Finset.Icc 1 k).filter (· ∣ m)).biUnion P := by
        ext x
        simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_Icc]
        constructor
        · intro hx
          have hx_m := (hmem_Sm hm).mp hx
          have hex : ∃ d : ℕ, 1 ≤ d ∧ φ^[d] x = x := ⟨m, hm, hx_m.2.1⟩
          let d := Nat.find hex
          have hd_spec : 1 ≤ d ∧ φ^[d] x = x := Nat.find_spec hex
          have hd_le_m : d ≤ m := Nat.find_min' hex ⟨hm, hx_m.2.1⟩
          have hd_dvd : d ∣ m := by
            by_contra hnd
            have hrem_pos : 0 < m % d := Nat.pos_of_ne_zero fun h0 => hnd (Nat.dvd_of_mod_eq_zero h0)
            have hrem_lt : m % d < d := Nat.mod_lt m hd_spec.1
            have hmul : ∀ s, φ^[d * s] x = x := fun s => by
              induction s with
              | zero => simp
              | succ s ihs => rw [Nat.mul_succ, add_comm, Function.iterate_add_apply, ihs, hd_spec.2]
            have hrem_fix : φ^[m % d] x = x := by
              have hdiv : d * (m / d) + m % d = m := Nat.div_add_mod m d
              have h1 : φ^[d * (m / d) + m % d] x = x := by rw [hdiv]; exact hx_m.2.1
              rw [add_comm, Function.iterate_add_apply, hmul] at h1
              exact h1
            exact Nat.find_min hex hrem_lt ⟨hrem_pos, hrem_fix⟩
          refine ⟨d, ⟨⟨hd_spec.1, le_trans hd_le_m hmk⟩, hd_dvd⟩, ?_⟩
          simp only [P, Finset.mem_filter, hmem_Sm hd_spec.1]
          exact ⟨⟨hx_m.1, hd_spec.2, hx_m.2.2⟩, fun e he heq => by
            rw [Finset.mem_Ico] at he
            exact Nat.find_min hex he.2 ⟨he.1, heq⟩⟩
        · rintro ⟨d, ⟨⟨hd1, _⟩, ⟨s, rfl⟩⟩, hxP⟩
          simp only [P, Finset.mem_filter, hmem_Sm hd1] at hxP
          rw [hmem_Sm hm]
          refine ⟨hxP.1.1, ?_, hxP.1.2.2⟩
          have hmul : ∀ t, φ^[d * t] x = x := fun t => by
            induction t with
            | zero => simp
            | succ t iht => rw [Nat.mul_succ, add_comm, Function.iterate_add_apply, iht, hxP.1.2.1]
          exact hmul s
      have hpw : (((Finset.Icc 1 k).filter (· ∣ m)) : Set ℕ).PairwiseDisjoint P := by
        intro d₁ hd₁ d₂ hd₂ hne
        rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at hd₁ hd₂
        change Disjoint (P d₁) (P d₂)
        rw [Finset.disjoint_left]
        intro x hx₁ hx₂
        simp only [P, Finset.mem_filter, hmem_Sm hd₁.1.1] at hx₁
        simp only [P, Finset.mem_filter, hmem_Sm hd₂.1.1] at hx₂
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · exact hx₂.2 d₁ (Finset.mem_Ico.mpr ⟨hd₁.1.1, hlt⟩) hx₁.1.2.1
        · exact hx₁.2 d₂ (Finset.mem_Ico.mpr ⟨hd₂.1.1, hgt⟩) hx₂.1.2.1
      rw [hpart, Finset.card_biUnion hpw, Finset.sum_filter]
      refine Finset.sum_congr rfl fun d hd => ?_
      split_ifs
      · exact hP_card d (Finset.mem_Icc.mp hd).1
      · rfl
    -- Define the truncated periodic sequence `N_trunc m = ∑_{d ∈ Icc 1 k, d ∣ m} d * c d`
    let N_trunc : ℕ → ℚ := fun m => ∑ d ∈ Finset.Icc 1 k, if d ∣ m then ((d * c d : ℕ) : ℚ) else 0
    have hcoeff_eq : PowerSeries.coeff k (zetaOfCounts (fun m => (torusPointCount p r g m : ℚ))) =
        PowerSeries.coeff k (zetaOfCounts N_trunc) := by
      -- Two `zetaLog`s agreeing on `0..k` have the same `k`-th coefficient in `expSeries`!
      have hlog_eq : ∀ j ≤ k, PowerSeries.coeff j (zetaLog (fun m => (torusPointCount p r g m : ℚ))) =
          PowerSeries.coeff j (zetaLog N_trunc) := by
        intro j hjk
        rcases j with _ | j
        · simp [zetaLog]
        · simp only [zetaLog, PowerSeries.coeff_mk, Nat.succ_ne_zero, ↓reduceIte]
          congr 1
          change ((S_m (j + 1)).card : ℚ) = N_trunc (j + 1)
          rw [hSm_eq (j + 1) (Nat.succ_pos j) hjk, Nat.cast_sum]
          refine Finset.sum_congr rfl fun d _ => by split_ifs <;> simp
      have hpow_eq : ∀ s j, j ≤ k →
          PowerSeries.coeff j ((zetaLog (fun m => (torusPointCount p r g m : ℚ))) ^ s) =
            PowerSeries.coeff j ((zetaLog N_trunc) ^ s) := fun s => by
        induction s with
        | zero => intro j _; simp
        | succ s ih =>
          intro j hjk
          rw [pow_succ, pow_succ, PowerSeries.coeff_mul, PowerSeries.coeff_mul]
          refine Finset.sum_congr rfl fun ab hab => ?_
          rw [Finset.mem_antidiagonal] at hab
          rw [ih ab.1 (by omega), hlog_eq ab.2 (by omega)]
      rw [zetaOfCounts_eq_expSeries_zetaLog, zetaOfCounts_eq_expSeries_zetaLog,
        coeff_expSeries_eq_sum (constantCoeff_zetaLog _),
        coeff_expSeries_eq_sum (constantCoeff_zetaLog _)]
      exact Finset.sum_congr rfl fun s _ => by rw [hpow_eq s k le_rfl]
    -- Show `zetaOfCounts N_trunc = ∏ d ∈ Icc 1 k, (substPow d (expSeries (logSeries 1))) ^ (c d)`!
    have hlog_trunc : zetaLog N_trunc =
        ∑ d ∈ Finset.Icc 1 k, ((c d : ℕ) : ℚ) • substPow d (logSeries (1 : ℚ)) := by
      ext m
      rw [zetaLog, PowerSeries.coeff_mk, map_sum]
      rcases m with _ | m
      · simp [coeff_substPow, logSeries]
      · simp only [Nat.succ_ne_zero, ↓reduceIte, N_trunc, Finset.sum_div]
        refine Finset.sum_congr rfl fun d hd => ?_
        have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
        rw [PowerSeries.coeff_smul, coeff_substPow, coeff_logSeries, smul_eq_mul]
        split_ifs with hdvd hdiv0
        · exfalso
          obtain ⟨t, ht⟩ := hdvd
          rw [ht, Nat.mul_div_cancel_left t hd1] at hdiv0
          subst hdiv0; simp at ht
        · obtain ⟨t, ht⟩ := hdvd
          have ht_ne : (t : ℚ) ≠ 0 := by
            intro ht0; have : t = 0 := by exact_mod_cast ht0
            rw [this, mul_zero] at ht; exact Nat.succ_ne_zero m ht
          have hd_ne : (d : ℚ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
          rw [ht, Nat.mul_div_cancel_left t hd1, one_pow, Nat.cast_mul, Nat.cast_mul]
          field_simp [hd_ne, ht_ne]
        · simp
    have hzeta_prod : zetaOfCounts N_trunc =
        ∏ d ∈ Finset.Icc 1 k, (substPow d (expSeries (logSeries (1 : ℚ)))) ^ (c d) := by
      rw [zetaOfCounts_eq_expSeries_zetaLog, hlog_trunc, expSeries_sum]
      · refine Finset.prod_congr rfl fun d hd => ?_
        have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
        have hcc_sub : PowerSeries.constantCoeff (substPow d (logSeries (1 : ℚ))) = 0 := by
          rw [constantCoeff_substPow, constantCoeff_logSeries]
        have hsmul_exp : ∀ t : ℕ, expSeries ((t : ℚ) • substPow d (logSeries (1 : ℚ))) =
            (expSeries (substPow d (logSeries (1 : ℚ)))) ^ t := fun t => by
          induction t with
          | zero => simp [expSeries_zero]
          | succ t iht =>
            have hadd : ((t + 1 : ℕ) : ℚ) • substPow d (logSeries (1 : ℚ)) =
                (t : ℚ) • substPow d (logSeries (1 : ℚ)) + substPow d (logSeries (1 : ℚ)) := by
              ext j; simp only [PowerSeries.coeff_smul, smul_eq_mul, map_add]; push_cast; ring
            have h0t : PowerSeries.constantCoeff ((t : ℚ) • substPow d (logSeries (1 : ℚ))) = 0 := by
              rw [← PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.coeff_smul,
                PowerSeries.coeff_zero_eq_constantCoeff, hcc_sub, smul_zero]
            rw [hadd, expSeries_add h0t hcc_sub, iht, pow_succ]
        rw [hsmul_exp (c d)]
        congr 1
        have heq_sub : expSeries (substPow d (logSeries (1 : ℚ))) =
            substPow d (expSeries (logSeries (1 : ℚ))) := by
          ext j
          rw [coeff_expSeries_eq_sum hcc_sub j, coeff_substPow,
            coeff_expSeries_eq_sum (constantCoeff_logSeries 1)]
          -- Use `substPow_expPS` via `expSeries = expPS`!
          have h1 : expSeries (substPow d (logSeries (1 : ℚ))) = expPS (substPow d (logSeries (1 : ℚ))) := by
            ext n; rw [coeff_expSeries_eq_sum hcc_sub, coeff_expPS_eq_sum hcc_sub]
          have h2 : expSeries (logSeries (1 : ℚ)) = expPS (logSeries (1 : ℚ)) := by
            ext n; rw [coeff_expSeries_eq_sum (constantCoeff_logSeries 1),
              coeff_expPS_eq_sum (constantCoeff_logSeries 1)]
          have h3 := congrArg (PowerSeries.coeff j) (substPow_expPS hd1 (constantCoeff_logSeries (1 : ℚ)))
          rw [← h1, ← h2] at h3
          rw [coeff_expSeries_eq_sum hcc_sub j] at h3
          rw [← h3, coeff_substPow, coeff_expSeries_eq_sum (constantCoeff_logSeries 1)]
        exact heq_sub
      · intro d _
        rw [← PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.coeff_smul,
          PowerSeries.coeff_zero_eq_constantCoeff, constantCoeff_substPow,
          constantCoeff_logSeries, smul_zero]
    -- Every factor `substPow d (expSeries (logSeries 1))` has `ℕ`-cast coefficients, hence so does the product!
    have hisNat_factor : ∀ d ∈ Finset.Icc 1 k, ∀ j : ℕ,
        ∃ b : ℕ, PowerSeries.coeff j (substPow d (expSeries (logSeries (1 : ℚ)))) = (b : ℚ) := by
      intro d _ j
      rw [coeff_substPow, coeff_expSeries_logSeries, one_pow]
      by_cases hd : d ∣ j
      · exact ⟨1, by simp [hd]⟩
      · exact ⟨0, by simp [hd]⟩
    have hisNat_mul : ∀ f g : PowerSeries ℚ,
        (∀ j, ∃ b : ℕ, PowerSeries.coeff j f = (b : ℚ)) →
        (∀ j, ∃ b : ℕ, PowerSeries.coeff j g = (b : ℚ)) →
        (∀ j, ∃ b : ℕ, PowerSeries.coeff j (f * g) = (b : ℚ)) := by
      intro f g hf hg j
      choose bf hbf using hf
      choose bg hbg using hg
      refine ⟨∑ ab ∈ Finset.antidiagonal j, bf ab.1 * bg ab.2, ?_⟩
      rw [PowerSeries.coeff_mul, Nat.cast_sum]
      refine Finset.sum_congr rfl fun ab _ => by rw [hbf ab.1, hbg ab.2, Nat.cast_mul]
    have hisNat_pow : ∀ (f : PowerSeries ℚ) (t : ℕ),
        (∀ j, ∃ b : ℕ, PowerSeries.coeff j f = (b : ℚ)) →
        (∀ j, ∃ b : ℕ, PowerSeries.coeff j (f ^ t) = (b : ℚ)) := by
      intro f t hf
      induction t with
      | zero => intro j; rw [pow_zero, PowerSeries.coeff_one]; split_ifs <;> [exact ⟨1, by simp⟩; exact ⟨0, by simp⟩]
      | succ t iht => rw [pow_succ]; exact hisNat_mul _ _ iht hf
    have hisNat_prod : ∀ s : Finset ℕ,
        (∀ d ∈ s, ∀ j, ∃ b : ℕ, PowerSeries.coeff j ((substPow d (expSeries (logSeries (1 : ℚ)))) ^ (c d)) = (b : ℚ)) →
        ∀ j, ∃ b : ℕ, PowerSeries.coeff j (∏ d ∈ s, (substPow d (expSeries (logSeries (1 : ℚ)))) ^ (c d)) = (b : ℚ) := by
      intro s
      induction s using Finset.induction_on with
      | empty => intro _ j; rw [Finset.prod_empty, PowerSeries.coeff_one]; split_ifs <;> [exact ⟨1, by simp⟩; exact ⟨0, by simp⟩]
      | insert a s ha ih =>
        intro hs
        rw [Finset.prod_insert ha]
        exact hisNat_mul _ _ (hs a (Finset.mem_insert_self a s))
          (ih fun d hd => hs d (Finset.mem_insert_of_mem hd))
    obtain ⟨ak, hak⟩ := hisNat_prod (Finset.Icc 1 k)
      (fun d hd => hisNat_pow _ (c d) (hisNat_factor d hd)) k
    rw [← hzeta_prod, ← hcoeff_eq] at hak
    -- Step 2: Archimedean upper bound `ak ≤ ((p^r)^n)^k` by termwise comparison with `expSeries (logSeries B)`!
    let B : ℕ := (p ^ r) ^ n
    have hlog_le : ∀ j : ℕ, 0 ≤ PowerSeries.coeff j (zetaLog (fun m => (torusPointCount p r g m : ℚ))) ∧
        PowerSeries.coeff j (zetaLog (fun m => (torusPointCount p r g m : ℚ))) ≤
          PowerSeries.coeff j (logSeries (B : ℚ)) := by
      intro j
      rcases j with _ | j
      · simp [zetaLog, logSeries]
      · simp only [zetaLog, logSeries, PowerSeries.coeff_mk, Nat.succ_ne_zero, ↓reduceIte]
        have hjpos : (0 : ℚ) < ((j + 1 : ℕ) : ℚ) := by positivity
        refine ⟨div_nonneg (Nat.cast_nonneg _) hjpos.le,
          div_le_div_of_nonneg_right ?_ hjpos.le⟩
        have hle := torusPointCount_le p r g hr (Nat.succ_pos j)
        exact_mod_cast hle
    have hpow_le : ∀ s j : ℕ, 0 ≤ PowerSeries.coeff j ((zetaLog (fun m => (torusPointCount p r g m : ℚ))) ^ s) ∧
        PowerSeries.coeff j ((zetaLog (fun m => (torusPointCount p r g m : ℚ))) ^ s) ≤
          PowerSeries.coeff j ((logSeries (B : ℚ)) ^ s) := by
      intro s
      induction s with
      | zero =>
        intro j; rw [pow_zero, pow_zero, PowerSeries.coeff_one]; split_ifs <;> simp
      | succ s ih =>
        intro j
        rw [pow_succ, pow_succ, PowerSeries.coeff_mul, PowerSeries.coeff_mul]
        refine ⟨Finset.sum_nonneg fun ab _ => mul_nonneg (ih ab.1).1 (hlog_le ab.2).1,
          Finset.sum_le_sum fun ab _ => mul_le_mul (ih ab.1).2 (hlog_le ab.2).2 (hlog_le ab.2).1
            (le_trans (ih ab.1).1 (ih ab.1).2)⟩
    have harch_q : (ak : ℚ) ≤ ((B ^ k : ℕ) : ℚ) := by
      rw [← hak, zetaOfCounts_eq_expSeries_zetaLog, coeff_expSeries_eq_sum (constantCoeff_zetaLog _),
        Nat.cast_pow, ← coeff_expSeries_logSeries (B : ℚ) k,
        coeff_expSeries_eq_sum (constantCoeff_logSeries (B : ℚ)) k]
      exact Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (hpow_le s k).2 (by positivity)
    exact ⟨ak, hak, by exact_mod_cast harch_q⟩
  choose a ha using hpointwise
  exact ⟨a, fun k => (ha k).1, fun k => (ha k).2⟩

/-- **Unified Binomial-Expansion Exponential Lemma**:
if `expSeries f * D = 1` (with `constantCoeff f = 0`), then for any `q : K` and `d : ℕ`:
`expSeries (∑_{j ≤ d} ((-1)^{d-j} * C(d, j)) • scalePS (q^j) f) * Den = Num`
where `Den = ∏_{j ≤ d, Even (d - j)} (scalePS (q^j) D)^{C(d, j)}` and
`Num = ∏_{j ≤ d, ¬ Even (d - j)} (scalePS (q^j) D)^{C(d, j)}`. -/
lemma expSeries_binomial_scale_mul {K : Type*} [Field K] [Algebra ℚ K] [CharZero K]
    {f D : PowerSeries K} (hf0 : PowerSeries.constantCoeff f = 0)
    (hinv : expSeries f * D = 1) (q : K) (d : ℕ) :
    expSeries (∑ j ∈ Finset.range (d + 1),
        ((-1 : K) ^ (d - j) * (Nat.choose d j : K)) • scalePS (q ^ j) f) *
      (∏ j ∈ (Finset.range (d + 1)).filter (fun j => Even (d - j)),
        (scalePS (q ^ j) D) ^ (Nat.choose d j)) =
      (∏ j ∈ (Finset.range (d + 1)).filter (fun j => ¬ Even (d - j)),
        (scalePS (q ^ j) D) ^ (Nat.choose d j)) := by
  have hsf0 : ∀ j : ℕ, PowerSeries.constantCoeff (scalePS (q ^ j) f) = 0 := fun j => by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff, coeff_scalePS, pow_zero, mul_one,
      PowerSeries.coeff_zero_eq_constantCoeff, hf0]
  have hterm0 : ∀ j ∈ Finset.range (d + 1),
      PowerSeries.constantCoeff (((-1 : K) ^ (d - j) * (Nat.choose d j : K)) • scalePS (q ^ j) f) = 0 := by
    intro j _
    rw [← PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.coeff_smul,
      PowerSeries.coeff_zero_eq_constantCoeff, hsf0 j, smul_zero]
  rw [expSeries_sum _ _ hterm0]
  have hscale_inv : ∀ j : ℕ, expSeries (scalePS (q ^ j) f) * scalePS (q ^ j) D = 1 := fun j => by
    rw [← scalePS_expSeries (q ^ j) hf0, ← map_mul, hinv, map_one]
  have hneg_exp : ∀ j : ℕ, expSeries (-scalePS (q ^ j) f) = scalePS (q ^ j) D := fun j => by
    calc expSeries (-scalePS (q ^ j) f)
        = expSeries (-scalePS (q ^ j) f) * 1 := (mul_one _).symm
      _ = expSeries (-scalePS (q ^ j) f) * (expSeries (scalePS (q ^ j) f) * scalePS (q ^ j) D) := by
          rw [hscale_inv j]
      _ = (expSeries (scalePS (q ^ j) f) * expSeries (-scalePS (q ^ j) f)) * scalePS (q ^ j) D := by ring
      _ = 1 * scalePS (q ^ j) D := by rw [expSeries_mul_expSeries_neg (hsf0 j)]
      _ = scalePS (q ^ j) D := one_mul _
  have hnat_exp : ∀ (g : PowerSeries K) (_hg0 : PowerSeries.constantCoeff g = 0) (t : ℕ),
      expSeries ((t : K) • g) = (expSeries g) ^ t := fun g hg0 t => by
    induction t with
    | zero => simp [expSeries_zero]
    | succ t iht =>
      have hadd : ((t + 1 : ℕ) : K) • g = (t : K) • g + g := by
        ext m; simp only [PowerSeries.coeff_smul, smul_eq_mul, map_add]; push_cast; ring
      have ht0 : PowerSeries.constantCoeff ((t : K) • g) = 0 := by
        rw [← PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.coeff_smul,
          PowerSeries.coeff_zero_eq_constantCoeff, hg0, smul_zero]
      rw [hadd, expSeries_add ht0 hg0, iht, pow_succ]
  -- Split `Finset.range (d + 1)` into `Even (d - j)` and `¬ Even (d - j)`
  rw [← Finset.prod_filter_mul_prod_filter_not (Finset.range (d + 1)) (fun j => Even (d - j))]
  have heven : (∏ j ∈ (Finset.range (d + 1)).filter (fun j => Even (d - j)),
        expSeries (((-1 : K) ^ (d - j) * (Nat.choose d j : K)) • scalePS (q ^ j) f)) *
      (∏ j ∈ (Finset.range (d + 1)).filter (fun j => Even (d - j)),
        (scalePS (q ^ j) D) ^ (Nat.choose d j)) = 1 := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun j hj => ?_
    have hev : Even (d - j) := (Finset.mem_filter.mp hj).2
    rw [hev.neg_one_pow, one_mul, hnat_exp _ (hsf0 j), ← mul_pow, hscale_inv j, one_pow]
  have hodd : ∏ j ∈ (Finset.range (d + 1)).filter (fun j => ¬ Even (d - j)),
        expSeries (((-1 : K) ^ (d - j) * (Nat.choose d j : K)) • scalePS (q ^ j) f) =
      ∏ j ∈ (Finset.range (d + 1)).filter (fun j => ¬ Even (d - j)),
        (scalePS (q ^ j) D) ^ (Nat.choose d j) := by
    refine Finset.prod_congr rfl fun j hj => ?_
    have hnot : ¬ Even (d - j) := (Finset.mem_filter.mp hj).2
    have hodd_j : Odd (d - j) := Nat.not_even_iff_odd.mp hnot
    rw [hodd_j.neg_one_pow, neg_one_mul]
    have hneg_smul : (-(Nat.choose d j : K)) • scalePS (q ^ j) f =
        (Nat.choose d j : K) • (-scalePS (q ^ j) f) := by
      ext m; simp [smul_eq_mul]
    have hneg0 : PowerSeries.constantCoeff (-scalePS (q ^ j) f) = 0 := by
      rw [map_neg, hsf0 j, neg_zero]
    rw [hneg_smul, hnat_exp _ hneg0, hneg_exp j]
  calc (∏ j ∈ (Finset.range (d + 1)).filter (fun j => Even (d - j)),
          expSeries (((-1 : K) ^ (d - j) * (Nat.choose d j : K)) • scalePS (q ^ j) f)) *
        (∏ j ∈ (Finset.range (d + 1)).filter (fun j => ¬ Even (d - j)),
          expSeries (((-1 : K) ^ (d - j) * (Nat.choose d j : K)) • scalePS (q ^ j) f)) *
        (∏ j ∈ (Finset.range (d + 1)).filter (fun j => Even (d - j)),
          (scalePS (q ^ j) D) ^ (Nat.choose d j))
      = ((∏ j ∈ (Finset.range (d + 1)).filter (fun j => Even (d - j)),
            expSeries (((-1 : K) ^ (d - j) * (Nat.choose d j : K)) • scalePS (q ^ j) f)) *
          (∏ j ∈ (Finset.range (d + 1)).filter (fun j => Even (d - j)),
            (scalePS (q ^ j) D) ^ (Nat.choose d j))) *
        (∏ j ∈ (Finset.range (d + 1)).filter (fun j => ¬ Even (d - j)),
          expSeries (((-1 : K) ^ (d - j) * (Nat.choose d j : K)) • scalePS (q ^ j) f)) := by ring
    _ = 1 * _ := by rw [heven]
    _ = _ := by rw [one_mul, hodd]

/-- Binomial log identity: `zetaLog (fun m => (q^m - 1)^d * T m) = ∑_{j ≤ d} ((-1)^{d-j} C(d,j)) • scalePS (q^j) (zetaLog T)`. -/
lemma zetaLog_pow_sub_one_mul {K : Type*} [Field K] [Algebra ℚ K] [CharZero K]
    (q : K) (d : ℕ) (T : ℕ → K) :
    zetaLog (fun m => (q ^ m - 1) ^ d * T m) =
      ∑ j ∈ Finset.range (d + 1),
        ((-1 : K) ^ (d - j) * (Nat.choose d j : K)) • scalePS (q ^ j) (zetaLog T) := by
  ext m
  rw [zetaLog, PowerSeries.coeff_mk, map_sum]
  rcases m with _ | m
  · simp [zetaLog]
  · simp only [Nat.succ_ne_zero, ↓reduceIte, PowerSeries.coeff_smul, coeff_scalePS, zetaLog,
      PowerSeries.coeff_mk, smul_eq_mul]
    rw [sub_eq_add_neg, add_pow, Finset.sum_mul, Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← pow_mul, mul_comm (m + 1) j, pow_mul]
    ring

/-- **Torus Hypersurface Rationality (Unconditional via Dwork Trace Formula + Fredholm Determinant + Borel–Dwork)**:
for any `r ≥ 1`, `n : ℕ`, and polynomial `g : MvPolynomial (Fin n) (kb p)` with coefficients in `𝔽_{p^r}`,
`zetaOfCounts (fun m => (torusPointCount p r g m : ℚ))` is a rational power series over `ℚ`! -/
theorem torus_hypersurface_rational {n r : ℕ} (hr : 1 ≤ r)
    (g : MvPolynomial (Fin n) (kb p))
    (hg : ∀ w ∈ g.support, (g.coeff w) ^ (p ^ r) = g.coeff w) :
    IsRationalPS (zetaOfCounts (fun m => (torusPointCount p r g m : ℚ))) := by
  let _ : NormedField (DworkField p) := dworkNormedField p
  have _ : IsUltrametricDist (DworkField p) := dworkField_ultra p
  have _ : CharZero (DworkField p) := dworkField_charZero p
  have hq_nat_ge2 : 2 ≤ p ^ r := by
    have h1 : p ^ 1 ≤ p ^ r := Nat.pow_le_pow_right hp.out.pos hr
    have h2 : 2 ≤ p := hp.out.two_le
    rw [pow_one] at h1; omega
  set q : ℕ := p ^ r
  have hq_ne : (q : ℚ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  -- Step 1: Auxiliary `(n+1)`-variable polynomial `G(X_0, X_1, ..., X_n) = X_0 * g(X_1, ..., X_n)`
  let G : MvPolynomial (Fin (n + 1)) (kb p) :=
    MvPolynomial.X 0 * MvPolynomial.rename Fin.succ g
  have hG_eval : ∀ x : Fin (n + 1) → kb p,
      MvPolynomial.eval x G = x 0 * MvPolynomial.eval (fun i : Fin n => x i.succ) g := by
    intro x
    simp only [G, map_mul, MvPolynomial.eval_X, MvPolynomial.eval_rename]
    rfl
  have hG0 : ∀ w ∈ G.support, w ≠ 0 := by
    intro w hw h0
    subst h0
    rw [MvPolynomial.mem_support_iff] at hw
    apply hw
    rw [← MvPolynomial.constantCoeff_eq]
    simp [G]
  have hGcoeff : ∀ w ∈ G.support, (G.coeff w) ^ (p ^ r) = G.coeff w := by
    have hcoeff_all : ∀ w : Fin (n + 1) →₀ ℕ, (G.coeff w) ^ (p ^ r) = G.coeff w := by
      intro w
      -- Express `G` as `∑ u ∈ g.support, monomial (single 0 1 + mapDomain Fin.succ u) (g.coeff u)`
      have hG_sum : G = ∑ u ∈ g.support,
          MvPolynomial.monomial (Finsupp.single (0 : Fin (n + 1)) 1 + Finsupp.mapDomain Fin.succ u)
            (g.coeff u) := by
        dsimp only [G]
        conv_lhs => rw [MvPolynomial.as_sum g]
        rw [map_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [MvPolynomial.rename_monomial, MvPolynomial.X, MvPolynomial.monomial_mul, one_mul]
      rw [hG_sum, MvPolynomial.coeff_sum, kb_sum_pow_prime_pow p]
      refine Finset.sum_congr rfl fun u hu => ?_
      rw [MvPolynomial.coeff_monomial]
      split_ifs
      · exact hg u hu
      · exact zero_pow (pow_ne_zero r hp.out.ne_zero)
    exact fun w _ => hcoeff_all w
  -- Step 2: Exponential sum identity via `sum_finFieldUnits_dworkChar` + `dwork_trace_formula`!
  let F_r := dworkPolySeries p r G
  have hcount_eq : ∀ m : ℕ, 1 ≤ m →
      ((q : DworkField p) ^ m) * (torusPointCount p r g m : DworkField p) =
        ((q : DworkField p) ^ m - 1) ^ n +
        ((q : DworkField p) ^ m - 1) ^ (n + 1) * dworkInfTrace p q F_r m := by
    intro m hm
    have hrm : 1 ≤ r * m := Nat.mul_pos hr hm
    have hqrm : q ^ m = p ^ (r * m) := (pow_mul p r m).symm
    have htrace := dwork_trace_formula p hr hm G hG0 hGcoeff
    have hq_sub_cast : ((((p ^ r) ^ m - 1 : ℕ) : DworkField p)) = (q : DworkField p) ^ m - 1 := by
      have h1 : 1 ≤ (p ^ r) ^ m := Nat.one_le_pow m (p ^ r) (pow_pos hp.out.pos r)
      rw [Nat.cast_sub h1, Nat.cast_pow, Nat.cast_one]
    rw [hq_sub_cast] at htrace
    -- Split the `(n+1)`-fold torus sum into `(x_0, x') ∈ finFieldUnits × (finFieldUnits)^n`
    let e_pi : (Fin (n + 1) → kb p) ≃ kb p × (Fin n → kb p) :=
      { toFun := fun x => (x 0, fun i => x i.succ)
        invFun := fun y => Fin.cons y.1 y.2
        left_inv := fun x => by ext i; refine Fin.cases rfl (fun _ => rfl) i
        right_inv := fun ⟨a, y⟩ => by ext <;> simp }
    have hsplit : ∑ x ∈ Fintype.piFinset (fun _ : Fin (n + 1) => finFieldUnits p (r * m)),
          dworkChar p (r * m) (MvPolynomial.eval x G) =
        ∑ x' ∈ Fintype.piFinset (fun _ : Fin n => finFieldUnits p (r * m)),
          ∑ x₀ ∈ finFieldUnits p (r * m),
            dworkChar p (r * m) (x₀ * MvPolynomial.eval x' g) := by
      rw [← Finset.sum_product']
      refine Finset.sum_bij (fun x _ => (fun i => x i.succ, x 0)) ?_ ?_ ?_ ?_
      · intro x hx
        rw [Fintype.mem_piFinset] at hx
        rw [Finset.mem_product, Fintype.mem_piFinset]
        exact ⟨fun i => hx i.succ, hx 0⟩
      · intro x₁ _ x₂ _ h
        ext i
        refine Fin.cases (congrArg Prod.snd h) (fun j => congrFun (congrArg Prod.fst h) j) i
      · intro y hy
        rw [Finset.mem_product, Fintype.mem_piFinset] at hy
        refine ⟨Fin.cons y.2 y.1, ?_, by ext <;> simp⟩
        rw [Fintype.mem_piFinset]
        intro i
        refine Fin.cases hy.2 (fun j => hy.1 j) i
      · intro x _; rw [hG_eval]
    -- Apply `sum_finFieldUnits_dworkChar` to the inner sum over `x₀`
    have hinner : ∀ x' ∈ Fintype.piFinset (fun _ : Fin n => finFieldUnits p (r * m)),
        ∑ x₀ ∈ finFieldUnits p (r * m),
          dworkChar p (r * m) (x₀ * MvPolynomial.eval x' g) =
        if MvPolynomial.eval x' g = 0 then (q : DworkField p) ^ m - 1 else -1 := by
      intro x' hx'
      rw [Fintype.mem_piFinset] at hx'
      have hev_mem : MvPolynomial.eval x' g ∈ finFieldSet p (r * m) := by
        rw [mem_finFieldSet p hrm]
        have hpow_rm : ∀ k (u : kb p), u ^ (p ^ r) = u → u ^ (p ^ (r * k)) = u := fun k u hu => by
          induction k with
          | zero => simp
          | succ k ihk => rw [Nat.mul_succ, pow_add, pow_mul, ihk, hu]
        rw [MvPolynomial.eval_eq', kb_sum_pow_prime_pow p]
        refine Finset.sum_congr rfl fun w hw => ?_
        rw [mul_pow, hpow_rm m _ (hg w hw), ← Finset.prod_pow]
        congr 1
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [← pow_mul, mul_comm, pow_mul, ((mem_finFieldUnits p hrm).mp (hx' i)).2]
      rw [sum_finFieldUnits_dworkChar p hrm hev_mem, ← hqrm, Nat.cast_pow]
    rw [hsplit, Finset.sum_congr rfl hinner] at htrace
    -- Evaluate `∑_{x' ∈ (𝔽_{q^m}ˣ)^n} (if g(x') = 0 then q^m - 1 else -1)`
    let U := Fintype.piFinset (fun _ : Fin n => finFieldUnits p (r * m))
    have hsum_eval : ∑ x' ∈ U, (if MvPolynomial.eval x' g = 0 then (q : DworkField p) ^ m - 1 else -1) =
        (q : DworkField p) ^ m * (torusPointCount p r g m : DworkField p) -
        ((q : DworkField p) ^ m - 1) ^ n := by
      have hrew : ∀ x' ∈ U,
          (if MvPolynomial.eval x' g = 0 then (q : DworkField p) ^ m - 1 else -1) =
          (if MvPolynomial.eval x' g = 0 then (q : DworkField p) ^ m else 0) + (-1) := fun x' _ => by
        split_ifs <;> ring
      rw [Finset.sum_congr rfl hrew, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
        Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
      have hUcard : (U.card : DworkField p) = ((q : DworkField p) ^ m - 1) ^ n := by
        have hc : U.card = (q ^ m - 1) ^ n := by
          dsimp only [U]
          rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_fin, card_finFieldUnits p hrm,
            hqrm]
        rw [hc, Nat.cast_pow, hq_sub_cast]
      rw [hUcard]
      change (torusPointCount p r g m : DworkField p) * (q : DworkField p) ^ m +
          ((q : DworkField p) ^ m - 1) ^ n * (-1) = _
      ring
    rw [hsum_eval] at htrace
    linear_combination -htrace
  -- Step 3: `p`-adic meromorphic continuation of `zetaOfCounts (fun m => q^m * torusPointCount m)` in `(DworkField p)[[T]]`!
  set D_deg : ℕ := max 1 G.totalDegree
  have hDpos : 0 < D_deg := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hD : ∀ w ∈ G.support, w.degree ≤ D_deg := fun w hw => by
    have hle : w.degree ≤ G.totalDegree := by
      rw [MvPolynomial.totalDegree, finsupp_degree_eq_sum]
      exact Finset.le_sup (f := fun s : Fin (n + 1) →₀ ℕ => s.sum fun _ e => e) hw
        |> le_trans (by
          rw [Finsupp.sum]
          exact (Finset.sum_subset (Finset.subset_univ _) fun i _ hi =>
            Finsupp.notMem_support_iff.mp hi).symm.le)
    exact le_trans hle (le_max_right _ _)
  have hF_decay := norm_coeff_dworkPolySeries_le p r G hG0 hDpos hD
  have hc_pos : 0 < dworkDecayConst p r D_deg := dworkDecayConst_pos p r hDpos
  let DF := dworkFredholmSeries p q F_r
  have hDF_entire : IsPadicEntire p DF := isPadicEntire_dworkFredholmSeries p hq_nat_ge2 hc_pos hF_decay
  have hDF_cc : PowerSeries.constantCoeff DF = 1 :=
    constantCoeff_dworkFredholmSeries p hq_nat_ge2 hc_pos hF_decay
  have hDF_jacobi : expSeries (infTraceLog p q F_r) * DF = 1 :=
    expSeries_infTraceLog_mul_dworkFredholmSeries p hq_nat_ge2 hc_pos hF_decay
  -- Build `Num₀, Den₀` for `(q^m - 1)^n` and `Num₁, Den₁` for `(q^m - 1)^{n+1} * Tr(M^m)`
  let Den₀ : PowerSeries (DworkField p) :=
    ∏ j ∈ (Finset.range (n + 1)).filter (fun j => Even (n - j)),
      (scalePS ((q : DworkField p) ^ j) (1 - PowerSeries.X)) ^ (Nat.choose n j)
  let Num₀ : PowerSeries (DworkField p) :=
    ∏ j ∈ (Finset.range (n + 1)).filter (fun j => ¬ Even (n - j)),
      (scalePS ((q : DworkField p) ^ j) (1 - PowerSeries.X)) ^ (Nat.choose n j)
  let Den₁ : PowerSeries (DworkField p) :=
    ∏ j ∈ (Finset.range (n + 2)).filter (fun j => Even (n + 1 - j)),
      (scalePS ((q : DworkField p) ^ j) DF) ^ (Nat.choose (n + 1) j)
  let Num₁ : PowerSeries (DworkField p) :=
    ∏ j ∈ (Finset.range (n + 2)).filter (fun j => ¬ Even (n + 1 - j)),
      (scalePS ((q : DworkField p) ^ j) DF) ^ (Nat.choose (n + 1) j)
  have hZ0 : zetaOfCounts (fun m => ((q : DworkField p) ^ m - 1) ^ n) * Den₀ = Num₀ := by
    have hinv1 : expSeries (logSeries (1 : DworkField p)) * (1 - PowerSeries.X) = 1 := by
      rw [mul_comm]; simpa using one_sub_C_mul_X_mul_expSeries_logSeries (1 : DworkField p)
    have hlog1 : zetaLog (fun m => ((q : DworkField p) ^ m - 1) ^ n) =
        ∑ j ∈ Finset.range (n + 1),
          ((-1 : DworkField p) ^ (n - j) * (Nat.choose n j : DworkField p)) •
            scalePS ((q : DworkField p) ^ j) (logSeries (1 : DworkField p)) := by
      have h := zetaLog_pow_sub_one_mul (q : DworkField p) n (fun _ => (1 : DworkField p))
      have h1 : zetaLog (fun _ => (1 : DworkField p)) = logSeries (1 : DworkField p) := by
        ext m; simp [zetaLog, logSeries]
      simpa [h1] using h
    rw [zetaOfCounts_eq_expSeries_zetaLog, hlog1]
    exact expSeries_binomial_scale_mul (constantCoeff_logSeries 1) hinv1 (q : DworkField p) n
  have hZ1 : zetaOfCounts (fun m => ((q : DworkField p) ^ m - 1) ^ (n + 1) * dworkInfTrace p q F_r m) *
      Den₁ = Num₁ := by
    have hinf_eq : infTraceLog p q F_r = zetaLog (dworkInfTrace p q F_r) := by
      ext m; simp [infTraceLog, zetaLog]
    have hlog2 : zetaLog (fun m => ((q : DworkField p) ^ m - 1) ^ (n + 1) * dworkInfTrace p q F_r m) =
        ∑ j ∈ Finset.range (n + 2),
          ((-1 : DworkField p) ^ (n + 1 - j) * (Nat.choose (n + 1) j : DworkField p)) •
            scalePS ((q : DworkField p) ^ j) (infTraceLog p q F_r) := by
      rw [hinf_eq]
      exact zetaLog_pow_sub_one_mul (q : DworkField p) (n + 1) (dworkInfTrace p q F_r)
    rw [zetaOfCounts_eq_expSeries_zetaLog, hlog2]
    exact expSeries_binomial_scale_mul (constantCoeff_infTraceLog p q F_r) hDF_jacobi
      (q : DworkField p) (n + 1)
  have hZ_split : zetaOfCounts (fun m => (q : DworkField p) ^ m * (torusPointCount p r g m : DworkField p)) =
      zetaOfCounts (fun m => ((q : DworkField p) ^ m - 1) ^ n) *
      zetaOfCounts (fun m => ((q : DworkField p) ^ m - 1) ^ (n + 1) * dworkInfTrace p q F_r m) := by
    rw [← zetaOfCounts_add]
    rw [zetaOfCounts_eq_expSeries_zetaLog, zetaOfCounts_eq_expSeries_zetaLog]
    congr 1
    ext m
    rcases m with _ | m
    · simp [zetaLog]
    · simp only [zetaLog, PowerSeries.coeff_mk, Nat.succ_ne_zero, ↓reduceIte]
      rw [hcount_eq (m + 1) (Nat.succ_pos m)]
  have hmero_eq : zetaOfCounts (fun m => (q : DworkField p) ^ m * (torusPointCount p r g m : DworkField p)) *
      (Den₀ * Den₁) = Num₀ * Num₁ := by
    rw [hZ_split]
    calc zetaOfCounts (fun m => ((q : DworkField p) ^ m - 1) ^ n) *
          zetaOfCounts (fun m => ((q : DworkField p) ^ m - 1) ^ (n + 1) * dworkInfTrace p q F_r m) *
          (Den₀ * Den₁)
        = (zetaOfCounts (fun m => ((q : DworkField p) ^ m - 1) ^ n) * Den₀) *
          (zetaOfCounts (fun m => ((q : DworkField p) ^ m - 1) ^ (n + 1) * dworkInfTrace p q F_r m) * Den₁) := by ring
      _ = Num₀ * Num₁ := by rw [hZ0, hZ1]
  -- Check `‖(q : DworkField p)^j‖ ≤ 1`, `IsPadicEntire` for `Num₀*Num₁` and `Den₀*Den₁`, and `coeff 0 (Den₀*Den₁) = 1`
  have hq_norm_le : ∀ j : ℕ, ‖((q : DworkField p) ^ j)‖ ≤ 1 := fun j => by
    have hq_le : ‖(q : DworkField p)‖ ≤ 1 := by
      dsimp only [q]
      rw [Nat.cast_pow, norm_pow, dworkField_norm_p p]
      exact pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ (by exact_mod_cast hp.out.one_le))
    rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hq_le
  have h1X_entire : IsPadicEntire p (1 - PowerSeries.X : PowerSeries (DworkField p)) := by
    simpa using isPadicEntire_one_sub_C_mul_X p (1 : DworkField p)
  have hNum_entire : IsPadicEntire p (Num₀ * Num₁) :=
    isPadicEntire_mul p
      (isPadicEntire_prod p _ _ fun j _ => isPadicEntire_pow p
        (isPadicEntire_scalePS_of_norm_le_one p (hq_norm_le j) h1X_entire) _)
      (isPadicEntire_prod p _ _ fun j _ => isPadicEntire_pow p
        (isPadicEntire_scalePS_of_norm_le_one p (hq_norm_le j) hDF_entire) _)
  have hDen_entire : IsPadicEntire p (Den₀ * Den₁) :=
    isPadicEntire_mul p
      (isPadicEntire_prod p _ _ fun j _ => isPadicEntire_pow p
        (isPadicEntire_scalePS_of_norm_le_one p (hq_norm_le j) h1X_entire) _)
      (isPadicEntire_prod p _ _ fun j _ => isPadicEntire_pow p
        (isPadicEntire_scalePS_of_norm_le_one p (hq_norm_le j) hDF_entire) _)
  have hDen_cc : PowerSeries.coeff 0 (Den₀ * Den₁) = 1 := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff, map_mul]
    have hD0_cc : PowerSeries.constantCoeff Den₀ = 1 := by
      dsimp only [Den₀]
      rw [map_prod]
      refine Finset.prod_eq_one fun j _ => ?_
      rw [map_pow, ← PowerSeries.coeff_zero_eq_constantCoeff, coeff_scalePS, pow_zero, mul_one,
        PowerSeries.coeff_zero_eq_constantCoeff, map_sub, map_one, PowerSeries.constantCoeff_X,
        sub_zero, one_pow]
    have hD1_cc : PowerSeries.constantCoeff Den₁ = 1 := by
      dsimp only [Den₁]
      rw [map_prod]
      refine Finset.prod_eq_one fun j _ => ?_
      rw [map_pow, ← PowerSeries.coeff_zero_eq_constantCoeff, coeff_scalePS, pow_zero, mul_one,
        PowerSeries.coeff_zero_eq_constantCoeff, hDF_cc, one_pow]
    rw [hD0_cc, hD1_cc, mul_one]
  -- Step 4: Invoke `torusPointCount_zeta_int_and_arch` + `borel_dwork_rationality_of_field`!
  obtain ⟨a, ha_coeff, ha_arch⟩ := torusPointCount_zeta_int_and_arch p hr g hg
  let b : ℕ → ℤ := fun k => ((a k * q ^ k : ℕ) : ℤ)
  have hb_arch : ∃ C₀ A : ℕ, ∀ k, (b k).natAbs ≤ C₀ * A ^ k := by
    refine ⟨1, q ^ n * q, fun k => ?_⟩
    simp only [b, Int.natAbs_natCast, one_mul, mul_pow]
    exact Nat.mul_le_mul_right (q ^ k) (ha_arch k)
  have hb_q_eq : scalePS (q : ℚ) (zetaOfCounts (fun m => (torusPointCount p r g m : ℚ))) =
      PowerSeries.mk fun k => (b k : ℚ) := by
    ext k
    rw [coeff_scalePS, ha_coeff k, PowerSeries.coeff_mk]
    simp [b]
  have hb_K_eq : zetaOfCounts (fun m => (q : DworkField p) ^ m * (torusPointCount p r g m : DworkField p)) =
      PowerSeries.mk fun k => (b k : DworkField p) := by
    have hmap := map_zetaOfCounts (L := DworkField p)
      (fun m => (q : ℚ) ^ m * (torusPointCount p r g m : ℚ))
    have hscale_q : zetaOfCounts (fun m => (q : ℚ) ^ m * (torusPointCount p r g m : ℚ)) =
        PowerSeries.mk fun k => (b k : ℚ) := by
      rw [← scalePS_zetaOfCounts, hb_q_eq]
    rw [hscale_q] at hmap
    have hfun : (fun m => algebraMap ℚ (DworkField p) ((q : ℚ) ^ m * (torusPointCount p r g m : ℚ))) =
        fun m => (q : DworkField p) ^ m * (torusPointCount p r g m : DworkField p) := by
      funext m; simp [map_mul, map_pow]
    rw [hfun] at hmap
    ext k
    have hc := congrArg (PowerSeries.coeff k) hmap
    rw [PowerSeries.coeff_map, PowerSeries.coeff_mk] at hc
    rw [PowerSeries.coeff_mk, ← hc]
    simp
  have hrat_scaled : IsRationalPS (scalePS (q : ℚ) (zetaOfCounts (fun m => (torusPointCount p r g m : ℚ)))) := by
    rw [hb_q_eq]
    refine borel_dwork_rationality_of_field (p := p) (K := DworkField p) (dworkField_norm_p p) b hb_arch ?_
    refine ⟨Num₀ * Num₁, Den₀ * Den₁, ?_, hDen_cc, fun r' hr' => ?_⟩
    · rw [← hb_K_eq]; exact hmero_eq
    · obtain ⟨C₁, hC₁⟩ := hNum_entire r' hr'
      obtain ⟨C₂, hC₂⟩ := hDen_entire r' hr'
      refine ⟨max C₁ C₂, fun k => ⟨?_, ?_⟩⟩
      · exact (hC₁ k).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (zpow_nonneg hr'.le _))
      · exact (hC₂ k).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (zpow_nonneg hr'.le _))
  exact isRationalPS_of_scalePS hq_ne hrat_scaled

end TorusRationality

/-! ## Section 4: Stratification, Inclusion–Exclusion, `GaloisField` Equivalence & Dwork's Rationality Theorem -/

section CrownTheorem

/-- Canonical embedding `GaloisField p r →+* AlgebraicClosure (ZMod p)`. -/
def gfEmbed (p r : ℕ) [Fact p.Prime] : GaloisField p r →+* kb p :=
  (IsAlgClosed.lift (R := ZMod p) (S := GaloisField p r) (M := kb p)).toRingHom

lemma gfEmbed_pow_card {p r : ℕ} [Fact p.Prime] (hr : 0 < r) (a : GaloisField p r) :
    (gfEmbed p r a) ^ (p ^ r) = gfEmbed p r a := by
  have : Fintype (GaloisField p r) := Fintype.ofFinite _
  have hcard : Fintype.card (GaloisField p r) = p ^ r := by
    rw [← Nat.card_eq_fintype_card]; exact GaloisField.card p r hr.ne'
  have ha : a ^ (p ^ r) = a := by
    rw [← hcard]; exact FiniteField.pow_card a
  rw [← map_pow, ha]

/-- **Genuine Affine Point Count over `𝔽_{q^m}` (`q = p^r`)**:
for any finite system of polynomials `fs : Finset (MvPolynomial (Fin n) (GaloisField p r))`,
`affinePointCount p r fs m` is the exact number of `𝔽_{q^m}`-rational solutions `x ∈ (𝔽_{q^m})^n`
to `∀ f ∈ fs, f(x) = 0`. -/
def affinePointCount (p r : ℕ) [Fact p.Prime] {n : ℕ}
    (fs : Finset (MvPolynomial (Fin n) (GaloisField p r))) (m : ℕ) : ℕ :=
  Nat.card {x : Fin n → kb p // (∀ i : Fin n, (x i) ^ ((p ^ r) ^ m) = x i) ∧
    ∀ f ∈ fs, MvPolynomial.eval₂ (gfEmbed p r) x f = 0}

/-- **Genuine Hasse–Weil Zeta Function** `Z(V, T) = exp(∑_{m ≥ 1} N_m T^m / m) ∈ ℚ[[T]]`. -/
def hasseWeilZeta (N : ℕ → ℕ) : PowerSeries ℚ :=
  zetaOfCounts (fun m => (N m : ℚ))

/-- The finite subfield `𝔽_{p^s} ⊆ kb p` as a `Subfield (kb p)`. -/
def finSubfield (p s : ℕ) [Fact p.Prime] (hs : 1 ≤ s) : Subfield (kb p) where
  carrier := (finFieldSet p s : Set (kb p))
  mul_mem' ha hb := mul_mem_finFieldSet p hs ha hb
  one_mem' := by simp [mem_finFieldSet p hs]
  add_mem' ha hb := add_mem_finFieldSet p hs ha hb
  zero_mem' := zero_mem_finFieldSet p hs
  neg_mem' ha := neg_mem_finFieldSet p hs ha
  inv_mem' _ ha := inv_mem_finFieldSet p hs ha

/-- Any finite field `L` of cardinality `N` over `K` is a splitting field of `X^N - X` over `K`. -/
lemma isSplittingField_X_pow_card_sub_X {K : Type*} [Field K]
    (L : Type*) [Field L] [Fintype L] [Algebra K L] {N : ℕ} (hcard : Fintype.card L = N) :
    Polynomial.IsSplittingField K L (Polynomial.X ^ N - Polynomial.X) := by
  let P : Polynomial K := Polynomial.X ^ N - Polynomial.X
  have hPmap : Polynomial.map (algebraMap K L) P =
      Polynomial.X ^ (Fintype.card L) - Polynomial.X := by
    simp [P, hcard]
  have hprod_eq : Polynomial.X ^ (Fintype.card L) - Polynomial.X =
      ∏ a : L, (Polynomial.X - Polynomial.C a) := by
    have hcard_gt1 : 1 < Fintype.card L := Fintype.one_lt_card
    let Q : Polynomial L :=
      (Polynomial.X ^ (Fintype.card L) - Polynomial.X) - ∏ a : L, (Polynomial.X - Polynomial.C a)
    suffices hQ : Q = 0 from sub_eq_zero.mp hQ
    by_contra hQne
    have hlead1 : (Polynomial.X ^ (Fintype.card L) - Polynomial.X : Polynomial L).Monic := by
      apply Polynomial.monic_X_pow_sub
      rw [Polynomial.degree_X]
      exact_mod_cast hcard_gt1
    have hdeg1 : (Polynomial.X ^ (Fintype.card L) - Polynomial.X : Polynomial L).natDegree =
        Fintype.card L := by
      rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt]
      · exact Polynomial.natDegree_X_pow _
      · rw [Polynomial.natDegree_X, Polynomial.natDegree_X_pow]; exact hcard_gt1
    have hlead2 : (∏ a : L, (Polynomial.X - Polynomial.C a)).Monic :=
      Polynomial.monic_prod_of_monic _ _ fun a _ => Polynomial.monic_X_sub_C a
    have hdeg2 : (∏ a : L, (Polynomial.X - Polynomial.C a)).natDegree = Fintype.card L := by
      rw [Polynomial.natDegree_prod_of_monic _ _ fun a _ => Polynomial.monic_X_sub_C a]
      simp
    have hdegQ : Q.natDegree < Fintype.card L := by
      by_contra hge
      push Not at hge
      have hne_lead : Q.coeff Q.natDegree ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hQne
      apply hne_lead
      dsimp only [Q]
      rw [Polynomial.coeff_sub]
      rcases eq_or_lt_of_le hge with heq | hgt
      · rw [← heq]
        have hc1 : (Polynomial.X ^ (Fintype.card L) - Polynomial.X : Polynomial L).coeff (Fintype.card L) = 1 := by
          rw [← hlead1.leadingCoeff, Polynomial.leadingCoeff, hdeg1]
        have hc2 : (∏ a : L, (Polynomial.X - Polynomial.C a)).coeff (Fintype.card L) = 1 := by
          rw [← hlead2.leadingCoeff, Polynomial.leadingCoeff, hdeg2]
        rw [hc1, hc2, sub_self]
      · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (hdeg1.symm ▸ hgt),
            Polynomial.coeff_eq_zero_of_natDegree_lt (hdeg2.symm ▸ hgt), sub_self]
    have hroots : ∀ a : L, a ∈ Q.roots := fun a => by
      rw [Polynomial.mem_roots hQne, Polynomial.IsRoot.def]
      simp only [Q, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
        FiniteField.pow_card, sub_self, Polynomial.eval_prod, Polynomial.eval_C]
      rw [Finset.prod_eq_zero (Finset.mem_univ a) (sub_self a), sub_zero]
    have hle : Fintype.card L ≤ Q.roots.card := by
      have hsub : (Finset.univ : Finset L).val ⊆ Q.roots := fun a _ => hroots a
      have hnodup : (Finset.univ : Finset L).val.Nodup := (Finset.univ : Finset L).nodup
      have hle_ms : (Finset.univ : Finset L).val ≤ Q.roots := (Multiset.le_iff_subset hnodup).mpr hsub
      exact Multiset.card_le_card hle_ms
    have hcard_roots : Q.roots.card ≤ Q.natDegree := Polynomial.card_roots' Q
    omega
  have hprod_splits : ∀ (s : Finset L), (∏ a ∈ s, (Polynomial.X - Polynomial.C a)).Splits := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      rw [Finset.prod_empty, ← Polynomial.C_1]
      exact Polynomial.Splits.C (1 : L)
    | insert a s ha ih =>
      rw [Finset.prod_insert ha]
      exact (Polynomial.Splits.X_sub_C a).mul ih
  have hsplits : (Polynomial.map (algebraMap K L) P).Splits := by
    rw [hPmap, hprod_eq]
    exact hprod_splits Finset.univ
  refine ⟨hsplits, ?_⟩
  rw [eq_top_iff]
  intro a _
  refine Algebra.subset_adjoin ?_
  rw [Polynomial.mem_rootSet_of_ne]
  · rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
    change Polynomial.eval a (Polynomial.map (algebraMap K L) P) = 0
    rw [hPmap, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
      FiniteField.pow_card, sub_self]
  · intro h0
    have hmap0 : Polynomial.map (algebraMap K L) P = 0 := by
      change Polynomial.map (algebraMap K L) (Polynomial.X ^ N - Polynomial.X) = 0
      rw [h0, Polynomial.map_zero]
    rw [hPmap, hprod_eq] at hmap0
    have hne : (∏ x : L, (Polynomial.X - Polynomial.C x)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun x _ => Polynomial.X_sub_C_ne_zero x
    exact hne hmap0

/-- **Canonical `GaloisField p (r * m)` Equivalence**:
for EVERY `m ≥ 1`, EVERY finite field `F` with `Fintype.card F = (p ^ r) ^ m` (in particular
`F = GaloisField p (r * m)`!), and EVERY ring hom `φ : GaloisField p r →+* F`,
`affinePointCount p r fs m` equals the native `Fintype.card` of solutions in `Fin n → F`! -/
theorem affinePointCount_eq_finiteField {p r n : ℕ} [hp : Fact p.Prime] (hr : 0 < r)
    (fs : Finset (MvPolynomial (Fin n) (GaloisField p r))) {m : ℕ} (hm : 1 ≤ m)
    (F : Type*) [Field F] [Fintype F] (hFcard : Fintype.card F = (p ^ r) ^ m)
    (φ : GaloisField p r →+* F) :
    affinePointCount p r fs m =
      Fintype.card {x : Fin n → F // ∀ f ∈ fs, MvPolynomial.eval₂ φ x f = 0} := by
  have hrm : 1 ≤ r * m := Nat.mul_pos hr hm
  have hqrm : (p ^ r) ^ m = p ^ (r * m) := (pow_mul p r m).symm
  let E := finSubfield p (r * m) hrm
  have : Fintype E := Fintype.ofEquiv (finFieldSet p (r * m))
    { toFun := fun a => ⟨a.1, Finset.mem_coe.mpr a.2⟩
      invFun := fun a => ⟨a.1, Finset.mem_coe.mp a.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hEcard : Fintype.card E = (p ^ r) ^ m := by
    rw [Fintype.card_congr (show E ≃ finFieldSet p (r * m) from
      { toFun := fun a => ⟨a.1, Finset.mem_coe.mp a.2⟩
        invFun := fun a => ⟨a.1, Finset.mem_coe.mpr a.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }), Fintype.card_coe, card_finFieldSet p hrm, hqrm]
  -- Embed `GaloisField p r →+* E` via `gfEmbed p r`
  have hgf_mem : ∀ c : GaloisField p r, gfEmbed p r c ∈ E := fun c => by
    refine Finset.mem_coe.mpr ?_
    rw [mem_finFieldSet p hrm]
    have hpow : ∀ k, (gfEmbed p r c) ^ (p ^ (r * k)) = gfEmbed p r c := fun k => by
      induction k with
      | zero => simp
      | succ k ihk => rw [Nat.mul_succ, pow_add, pow_mul, ihk, gfEmbed_pow_card hr c]
    exact hpow m
  let ι_E : GaloisField p r →+* E :=
    { toFun := fun c => ⟨gfEmbed p r c, hgf_mem c⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun a b => Subtype.ext (map_mul _ a b)
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun a b => Subtype.ext (map_add _ a b) }
  -- Both `F` and `E` are splitting fields of `X ^ ((p^r)^m) - X` over `GaloisField p r`!
  let _ : Algebra (GaloisField p r) F := φ.toAlgebra
  let _ : Algebra (GaloisField p r) E := ι_E.toAlgebra
  let P : Polynomial (GaloisField p r) := Polynomial.X ^ ((p ^ r) ^ m) - Polynomial.X
  have : Polynomial.IsSplittingField (GaloisField p r) F P :=
    isSplittingField_X_pow_card_sub_X F hFcard
  have : Polynomial.IsSplittingField (GaloisField p r) E P :=
    isSplittingField_X_pow_card_sub_X E hEcard
  let e : F ≃ₐ[GaloisField p r] E :=
    (Polynomial.IsSplittingField.algEquiv F P).trans (Polynomial.IsSplittingField.algEquiv E P).symm
  have he_comm : ∀ c : GaloisField p r, (e (φ c) : kb p) = gfEmbed p r c := fun c => by
    have h1 : e (algebraMap (GaloisField p r) F c) = algebraMap (GaloisField p r) E c := e.commutes c
    exact congrArg Subtype.val h1
  -- Coordinatewise bijection between solutions in `F^n` and solutions in `kb^n` with `x_i^{q^m} = x_i`!
  let equiv_sol :
      {x : Fin n → F // ∀ f ∈ fs, MvPolynomial.eval₂ φ x f = 0} ≃
      {x : Fin n → kb p // (∀ i : Fin n, (x i) ^ ((p ^ r) ^ m) = x i) ∧
        ∀ f ∈ fs, MvPolynomial.eval₂ (gfEmbed p r) x f = 0} :=
    { toFun := fun ⟨x, hx⟩ =>
        ⟨fun i => (e (x i) : kb p),
          ⟨fun i => by
            rw [hqrm]; exact (mem_finFieldSet p hrm).mp (Finset.mem_coe.mp (e (x i)).2),
           fun f hf => by
            have hhom : (E.subtype.comp e.toRingHom).comp φ = gfEmbed p r := by
              ext c; exact he_comm c
            have hev := MvPolynomial.hom_eval₂ f φ (E.subtype.comp e.toRingHom) x
            rw [hhom, hx f hf, map_zero] at hev
            exact hev.symm⟩⟩
      invFun := fun ⟨y, hy⟩ =>
        ⟨fun i => e.symm ⟨y i, Finset.mem_coe.mpr ((mem_finFieldSet p hrm).mpr (by rw [← hqrm]; exact hy.1 i))⟩,
          fun f hf => by
            have hinv_comm : ∀ c : GaloisField p r, e.symm (ι_E c) = φ c := fun c =>
              e.injective (by rw [e.apply_symm_apply]; exact Subtype.ext (he_comm c).symm)
            have hhom : (e.symm.toRingHom.comp ι_E) = φ := by ext c; exact hinv_comm c
            let yE : Fin n → E := fun i =>
              ⟨y i, Finset.mem_coe.mpr ((mem_finFieldSet p hrm).mpr (by rw [← hqrm]; exact hy.1 i))⟩
            have h1 : MvPolynomial.eval₂ (E.subtype.comp ι_E) (fun i => (yE i).1) f = 0 :=
              hy.2 f hf
            have h2 := MvPolynomial.hom_eval₂ f ι_E E.subtype yE
            change E.subtype (MvPolynomial.eval₂ ι_E yE f) =
              MvPolynomial.eval₂ (E.subtype.comp ι_E) (fun i => (yE i).1) f at h2
            rw [h1] at h2
            have hE0 : MvPolynomial.eval₂ ι_E yE f = 0 :=
              E.subtype.injective (h2.trans (map_zero _).symm)
            have h3 := MvPolynomial.hom_eval₂ f ι_E e.symm.toRingHom yE
            rw [hE0, map_zero, hhom] at h3
            exact h3.symm⟩
      left_inv := fun ⟨x, _⟩ => by
        ext i
        change e.symm (e (x i)) = x i
        exact e.symm_apply_apply (x i)
      right_inv := fun ⟨y, _⟩ => by ext i; simp }
  unfold affinePointCount
  rw [← Nat.card_congr equiv_sol, Nat.card_eq_fintype_card]

/-- Corollary: `affinePointCount` matches `Nat.card` over `GaloisField p (r * m)` directly! -/
theorem affinePointCount_eq_galoisField {p r n : ℕ} [Fact p.Prime] (hr : 0 < r)
    (fs : Finset (MvPolynomial (Fin n) (GaloisField p r))) {m : ℕ} (hm : 1 ≤ m)
    (φ : GaloisField p r →+* GaloisField p (r * m)) :
    affinePointCount p r fs m =
      Nat.card {x : Fin n → GaloisField p (r * m) // ∀ f ∈ fs, MvPolynomial.eval₂ φ x f = 0} := by
  have : Fintype (GaloisField p (r * m)) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card]
  refine affinePointCount_eq_finiteField hr fs hm (GaloisField p (r * m)) ?_ φ
  rw [← Nat.card_eq_fintype_card, GaloisField.card p (r * m) (Nat.mul_pos hr hm).ne', pow_mul]

/-- Helper: `affinePointCount` as a `Finset.card` inside `Fintype.piFinset (fun _ => finFieldSet p (r * m))`. -/
lemma affinePointCount_eq_finset_card {p r n : ℕ} [Fact p.Prime] (hr : 0 < r)
    (fs : Finset (MvPolynomial (Fin n) (GaloisField p r))) {m : ℕ} (hm : 1 ≤ m) :
    affinePointCount p r fs m =
      ((Fintype.piFinset fun _ : Fin n => finFieldSet p (r * m)).filter
        (fun x => ∀ f ∈ fs, MvPolynomial.eval₂ (gfEmbed p r) x f = 0)).card := by
  have hrm : 1 ≤ r * m := Nat.mul_pos hr hm
  have hqrm : (p ^ r) ^ m = p ^ (r * m) := (pow_mul p r m).symm
  let S := (Fintype.piFinset fun _ : Fin n => finFieldSet p (r * m)).filter
    (fun x => ∀ f ∈ fs, MvPolynomial.eval₂ (gfEmbed p r) x f = 0)
  let e : {x : Fin n → kb p // (∀ i : Fin n, (x i) ^ ((p ^ r) ^ m) = x i) ∧
      ∀ f ∈ fs, MvPolynomial.eval₂ (gfEmbed p r) x f = 0} ≃ S :=
    { toFun := fun ⟨x, hx⟩ => ⟨x, Finset.mem_filter.mpr
        ⟨Fintype.mem_piFinset.mpr fun i => (mem_finFieldSet p hrm).mpr (by rw [← hqrm]; exact hx.1 i), hx.2⟩⟩
      invFun := fun ⟨x, hx⟩ => ⟨x, ⟨fun i => by
        rw [hqrm]; exact (mem_finFieldSet p hrm).mp (Fintype.mem_piFinset.mp (Finset.mem_filter.mp hx).1 i),
        (Finset.mem_filter.mp hx).2⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  unfold affinePointCount
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe]

/-- **Coordinate-Support Torus Stratification**:
for any single polynomial `f : MvPolynomial (Fin n) (GaloisField p r)`,
`hasseWeilZeta (affinePointCount p r {f})` is rational over `ℚ`! -/
theorem affine_single_poly_rational {p r n : ℕ} [Fact p.Prime] (hr : 0 < r)
    (f : MvPolynomial (Fin n) (GaloisField p r)) :
    IsRationalPS (hasseWeilZeta (affinePointCount p r {f})) := by
  -- Map `f` into `MvPolynomial (Fin n) (kb p)` via `gfEmbed p r`
  let g : MvPolynomial (Fin n) (kb p) := MvPolynomial.map (gfEmbed p r) f
  -- For each support `S : Finset (Fin n)`, define the restricted `S.card`-variable polynomial `g_S`
  let restrictPoly (S : Finset (Fin n)) : MvPolynomial (Fin S.card) (kb p) :=
    let eS : S ≃ Fin S.card := Finset.equivFin S
    MvPolynomial.aeval (fun i : Fin n => if h : i ∈ S then MvPolynomial.X (eS ⟨i, h⟩) else 0) g
  have hrestrict_eval : ∀ (S : Finset (Fin n)) (y : Fin S.card → kb p),
      let eS : S ≃ Fin S.card := Finset.equivFin S
      MvPolynomial.eval y (restrictPoly S) =
        MvPolynomial.eval₂ (gfEmbed p r) (fun i => if h : i ∈ S then y (eS ⟨i, h⟩) else 0) f := by
    intro S y eS
    dsimp only [restrictPoly, g]
    change MvPolynomial.eval y
        (MvPolynomial.eval₂ MvPolynomial.C
          (fun i : Fin n => if h : i ∈ S then MvPolynomial.X (eS ⟨i, h⟩) else 0)
          (MvPolynomial.map (gfEmbed p r) f)) = _
    rw [MvPolynomial.eval₂_map, MvPolynomial.hom_eval₂]
    have hhom : (MvPolynomial.eval y).comp (MvPolynomial.C.comp (gfEmbed p r)) = gfEmbed p r := by
      ext c; simp
    have hvar : (fun i : Fin n => MvPolynomial.eval y
        (if h : i ∈ S then MvPolynomial.X (eS ⟨i, h⟩) else 0)) =
        (fun i : Fin n => if h : i ∈ S then y (eS ⟨i, h⟩) else 0) := by
      funext i; split_ifs <;> simp
    rw [hhom, hvar]
  have hrestrict_frob : ∀ (S : Finset (Fin n)) (w : Fin S.card →₀ ℕ),
      w ∈ (restrictPoly S).support → ((restrictPoly S).coeff w) ^ (p ^ r) = (restrictPoly S).coeff w := by
    intro S w _
    -- `restrictPoly S` is in the image of `MvPolynomial.map (gfEmbed p r)`!
    let eS : S ≃ Fin S.card := Finset.equivFin S
    let f_S : MvPolynomial (Fin S.card) (GaloisField p r) :=
      MvPolynomial.aeval (fun i : Fin n => if h : i ∈ S then MvPolynomial.X (eS ⟨i, h⟩) else 0) f
    have hmap_eq : restrictPoly S = MvPolynomial.map (gfEmbed p r) f_S := by
      dsimp only [restrictPoly, f_S, g]
      change MvPolynomial.eval₂ MvPolynomial.C _ (MvPolynomial.map (gfEmbed p r) f) =
        MvPolynomial.map (gfEmbed p r) (MvPolynomial.eval₂ MvPolynomial.C _ f)
      rw [MvPolynomial.eval₂_map, MvPolynomial.hom_eval₂]
      have hhom : (MvPolynomial.C (σ := Fin S.card)).comp (gfEmbed p r) =
          (MvPolynomial.map (gfEmbed p r)).comp (MvPolynomial.C (σ := Fin S.card)) := by
        ext c; simp
      have hvar : (fun i : Fin n => if h : i ∈ S then (MvPolynomial.X (eS ⟨i, h⟩) : MvPolynomial (Fin S.card) (kb p)) else 0) =
          (fun i : Fin n => MvPolynomial.map (gfEmbed p r)
            (if h : i ∈ S then MvPolynomial.X (eS ⟨i, h⟩) else 0)) := by
        funext i; split_ifs <;> simp
      rw [hhom, hvar]
    rw [hmap_eq, MvPolynomial.coeff_map]
    exact gfEmbed_pow_card hr _
  -- Stratify `affinePointCount p r {f} m = ∑ S : Finset (Fin n), torusPointCount p r (restrictPoly S) m`!
  have hstrat : ∀ m : ℕ, 1 ≤ m →
      affinePointCount p r {f} m =
        ∑ S : Finset (Fin n), torusPointCount p r (restrictPoly S) m := by
    intro m hm
    have hrm : 1 ≤ r * m := Nat.mul_pos hr hm
    rw [affinePointCount_eq_finset_card hr {f} hm]
    let A := (Fintype.piFinset fun _ : Fin n => finFieldSet p (r * m)).filter
      (fun x => ∀ f' ∈ ({f} : Finset _), MvPolynomial.eval₂ (gfEmbed p r) x f' = 0)
    -- Partition `A` by support `supp x = Finset.univ.filter (fun i => x i ≠ 0)`
    let supp : (Fin n → kb p) → Finset (Fin n) := fun x => Finset.univ.filter (fun i => x i ≠ 0)
    have hcard_fiber : A.card = ∑ S : Finset (Fin n), (A.filter (fun x => supp x = S)).card :=
      Finset.card_eq_sum_card_fiberwise (fun x _ => Finset.mem_univ (supp x))
    rw [hcard_fiber]
    refine Finset.sum_congr rfl fun S _ => ?_
    let eS : S ≃ Fin S.card := Finset.equivFin S
    unfold torusPointCount
    refine Finset.card_bij (fun x _ j => x (eS.symm j).1) ?_ ?_ ?_
    · intro x hx
      rw [Finset.mem_filter] at hx
      obtain ⟨hxA, hsupp⟩ := hx
      rw [Finset.mem_filter, Fintype.mem_piFinset] at hxA
      rw [Finset.mem_filter, Fintype.mem_piFinset]
      refine ⟨fun j => ?_, ?_⟩
      · have hmemS : (eS.symm j).1 ∈ supp x := by rw [hsupp]; exact (eS.symm j).2
        have hne : x (eS.symm j).1 ≠ 0 := (Finset.mem_filter.mp hmemS).2
        exact (mem_finFieldUnits p hrm).mpr ⟨hne, (mem_finFieldSet p hrm).mp (hxA.1 _)⟩
      · rw [hrestrict_eval S]
        have hx_eq : (fun i : Fin n => if h : i ∈ S then x (eS.symm (eS ⟨i, h⟩)).1 else 0) = x := by
          ext i
          by_cases hi : i ∈ S
          · rw [dif_pos hi, eS.symm_apply_apply]
          · rw [dif_neg hi]
            by_contra hne
            have : i ∈ supp x := Finset.mem_filter.mpr ⟨Finset.mem_univ i, Ne.symm hne⟩
            rw [hsupp] at this
            exact hi this
        rw [hx_eq]
        exact hxA.2 f (Finset.mem_singleton_self f)
    · intro x₁ hx₁ x₂ hx₂ heq
      rw [Finset.mem_filter] at hx₁ hx₂
      ext i
      by_cases hi : i ∈ S
      · have h := congrFun heq (eS ⟨i, hi⟩)
        simpa [eS.symm_apply_apply] using h
      · have h1 : x₁ i = 0 := by
          by_contra hne; exact hi (hx₁.2 ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ i, hne⟩)
        have h2 : x₂ i = 0 := by
          by_contra hne; exact hi (hx₂.2 ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ i, hne⟩)
        rw [h1, h2]
    · intro y hy
      rw [Finset.mem_filter, Fintype.mem_piFinset] at hy
      let x : Fin n → kb p := fun i => if h : i ∈ S then y (eS ⟨i, h⟩) else 0
      refine ⟨x, ?_, by ext j; simp [x, (eS.symm j).2, eS.apply_symm_apply]⟩
      rw [Finset.mem_filter, Finset.mem_filter, Fintype.mem_piFinset]
      refine ⟨⟨fun i => ?_, fun f' hf' => ?_⟩, ?_⟩
      · dsimp only [x]
        split_ifs with hi
        · exact (mem_finFieldSet p hrm).mpr ((mem_finFieldUnits p hrm).mp (hy.1 _)).2
        · exact zero_mem_finFieldSet p hrm
      · rw [Finset.mem_singleton.mp hf', ← hrestrict_eval S y]
        exact hy.2
      · ext i
        simp only [supp, x, Finset.mem_filter, Finset.mem_univ, true_and]
        split_ifs with hi
        · exact iff_of_true ((mem_finFieldUnits p hrm).mp (hy.1 _)).1 hi
        · exact iff_of_false (not_not.mpr rfl) hi
  -- Zeta function of a finite sum of sequences is the product of their zeta functions!
  have hzeta_eq : hasseWeilZeta (affinePointCount p r {f}) =
      ∏ S : Finset (Fin n), zetaOfCounts (fun m => (torusPointCount p r (restrictPoly S) m : ℚ)) := by
    have hsum_zeta : ∀ (T : Finset (Finset (Fin n))),
        zetaOfCounts (fun m => ∑ S ∈ T, (torusPointCount p r (restrictPoly S) m : ℚ)) =
          ∏ S ∈ T, zetaOfCounts (fun m => (torusPointCount p r (restrictPoly S) m : ℚ)) := by
      intro T
      induction T using Finset.induction_on with
      | empty => simp [zetaOfCounts_zero]
      | insert a T ha ih =>
        have hadd : (fun m => ∑ S ∈ insert a T, (torusPointCount p r (restrictPoly S) m : ℚ)) =
            fun m => (torusPointCount p r (restrictPoly a) m : ℚ) +
              ∑ S ∈ T, (torusPointCount p r (restrictPoly S) m : ℚ) := by
          ext m; exact Finset.sum_insert ha
        rw [hadd, zetaOfCounts_add, ih, Finset.prod_insert ha]
    rw [← hsum_zeta Finset.univ]
    unfold hasseWeilZeta
    rw [zetaOfCounts_eq_expSeries_zetaLog, zetaOfCounts_eq_expSeries_zetaLog]
    congr 1
    ext m
    rcases m with _ | m
    · simp [zetaLog]
    · simp only [zetaLog, PowerSeries.coeff_mk, Nat.succ_ne_zero, ↓reduceIte]
      rw [hstrat (m + 1) (Nat.succ_pos m), Nat.cast_sum]
  rw [hzeta_eq]
  exact isRationalPS_prod Finset.univ _ fun S _ =>
    torus_hypersurface_rational p hr (restrictPoly S) (hrestrict_frob S)

/-- **Inclusion–Exclusion Reduction to Single Polynomials**:
for any finite system `fs : Finset (MvPolynomial (Fin n) (GaloisField p r))`,
`hasseWeilZeta (affinePointCount p r fs)` is rational over `ℚ`! -/
theorem affine_finset_rational {p r n : ℕ} [Fact p.Prime] (hr : 0 < r)
    (fs : Finset (MvPolynomial (Fin n) (GaloisField p r))) :
    IsRationalPS (hasseWeilZeta (affinePointCount p r fs)) := by
  -- Inclusion–exclusion identity for every `m ≥ 1`:
  -- `N_m(V(fs)) = ∑_{I ⊆ fs} (-1)^{|I|} * (q^{n m} - N_m(V(∏_{f ∈ I} f)))`!
  have hie : ∀ m : ℕ, 1 ≤ m →
      (affinePointCount p r fs m : ℚ) =
        ∑ I ∈ fs.powerset, (-1 : ℚ) ^ I.card *
          ((((p ^ r) ^ n : ℚ) ^ m) - (affinePointCount p r {∏ f ∈ I, f} m : ℚ)) := by
    intro m hm
    have hrm : 1 ≤ r * m := Nat.mul_pos hr hm
    have hqrm : (p ^ r) ^ m = p ^ (r * m) := (pow_mul p r m).symm
    let U := Fintype.piFinset (fun _ : Fin n => finFieldSet p (r * m))
    have hUcard : (U.card : ℚ) = ((p ^ r) ^ n : ℚ) ^ m := by
      have hc : U.card = ((p ^ r) ^ n) ^ m := by
        dsimp only [U]
        rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_fin, card_finFieldSet p hrm,
          ← hqrm, ← pow_mul, mul_comm m n, pow_mul]
      exact_mod_cast hc
    rw [affinePointCount_eq_finset_card hr fs hm]
    have hterm_I : ∀ I ∈ fs.powerset,
        (((p ^ r) ^ n : ℚ) ^ m - (affinePointCount p r {∏ f ∈ I, f} m : ℚ)) =
          ∑ x ∈ U, ∏ f ∈ I, if MvPolynomial.eval₂ (gfEmbed p r) x f = 0 then (0 : ℚ) else 1 := by
      intro I _
      rw [affinePointCount_eq_finset_card hr {∏ f ∈ I, f} hm, ← hUcard]
      have hcard_eq : (U.card : ℚ) - ((U.filter (fun x => ∀ g ∈ ({∏ f ∈ I, f} : Finset _),
            MvPolynomial.eval₂ (gfEmbed p r) x g = 0)).card : ℚ) =
          ∑ x ∈ U, if MvPolynomial.eval₂ (gfEmbed p r) x (∏ f ∈ I, f) = 0 then (0 : ℚ) else 1 := by
        have h1 : (U.card : ℚ) = ∑ _x ∈ U, (1 : ℚ) := by simp
        have h2 : ((U.filter (fun x => ∀ g ∈ ({∏ f ∈ I, f} : Finset _),
            MvPolynomial.eval₂ (gfEmbed p r) x g = 0)).card : ℚ) =
            ∑ x ∈ U, if MvPolynomial.eval₂ (gfEmbed p r) x (∏ f ∈ I, f) = 0 then (1 : ℚ) else 0 := by
          rw [Finset.sum_boole]
          congr 2; ext x; simp
        rw [h1, h2, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun x _ => by split_ifs <;> norm_num
      rw [hcard_eq]
      refine Finset.sum_congr rfl fun x _ => ?_
      have hprod : MvPolynomial.eval₂ (gfEmbed p r) x (∏ f ∈ I, f) =
          ∏ f ∈ I, MvPolynomial.eval₂ (gfEmbed p r) x f :=
        map_prod (MvPolynomial.eval₂Hom (gfEmbed p r) x) id I
      rw [hprod]
      by_cases hall : ∀ f ∈ I, MvPolynomial.eval₂ (gfEmbed p r) x f ≠ 0
      · have hne : ∏ f ∈ I, MvPolynomial.eval₂ (gfEmbed p r) x f ≠ 0 :=
          Finset.prod_ne_zero_iff.mpr hall
        rw [if_neg hne]
        symm
        exact Finset.prod_eq_one fun f hf => if_neg (hall f hf)
      · push Not at hall
        obtain ⟨f₀, hf₀, hf₀0⟩ := hall
        have h0 : ∏ f ∈ I, MvPolynomial.eval₂ (gfEmbed p r) x f = 0 :=
          Finset.prod_eq_zero hf₀ hf₀0
        rw [if_pos h0]
        symm
        exact Finset.prod_eq_zero hf₀ (if_pos hf₀0)
    rw [Finset.sum_congr rfl fun I hI => by rw [hterm_I I hI, Finset.mul_sum]]
    rw [Finset.sum_comm]
    have hpt : ∀ x ∈ U,
        (∑ I ∈ fs.powerset, (-1 : ℚ) ^ I.card *
          ∏ f ∈ I, if MvPolynomial.eval₂ (gfEmbed p r) x f = 0 then (0 : ℚ) else 1) =
        if ∀ f ∈ fs, MvPolynomial.eval₂ (gfEmbed p r) x f = 0 then (1 : ℚ) else 0 := by
      intro x _
      let ind : MvPolynomial (Fin n) (GaloisField p r) → ℚ :=
        fun f => if MvPolynomial.eval₂ (gfEmbed p r) x f = 0 then 0 else 1
      have hprod_one_sub : ∏ f ∈ fs, (1 - ind f) =
          ∑ I ∈ fs.powerset, (-1 : ℚ) ^ I.card * ∏ f ∈ I, ind f := by
        have hrew : ∀ f ∈ fs, (1 : ℚ) - ind f = (-ind f) + 1 := fun _ _ => by ring
        rw [Finset.prod_congr rfl hrew, Finset.prod_add]
        refine Finset.sum_congr rfl fun I _ => ?_
        rw [Finset.prod_const_one, mul_one, Finset.prod_neg]
      rw [← hprod_one_sub]
      by_cases hall : ∀ f ∈ fs, MvPolynomial.eval₂ (gfEmbed p r) x f = 0
      · rw [if_pos hall]
        refine Finset.prod_eq_one fun f hf => by simp [ind, hall f hf]
      · rw [if_neg hall]
        push Not at hall
        obtain ⟨f₀, hf₀, hf₀ne⟩ := hall
        exact Finset.prod_eq_zero hf₀ (by simp [ind, hf₀ne])
    rw [Finset.sum_congr rfl hpt, Finset.sum_boole]
  -- Convert the inclusion–exclusion sum into a finite product of rational zeta functions!
  have hfactor_rat : ∀ I ∈ fs.powerset,
      IsRationalPS (zetaOfCounts (fun m => (-1 : ℚ) ^ I.card *
        ((((p ^ r) ^ n : ℚ) ^ m) - (affinePointCount p r {∏ f ∈ I, f} m : ℚ)))) := by
    intro I _
    have hgeom_rat : IsRationalPS (zetaOfCounts (fun m => (((p ^ r) ^ n : ℚ)) ^ m)) :=
      ⟨1, 1 - Polynomial.C (((p ^ r) ^ n : ℚ)) * Polynomial.X, by
        intro h0
        have hc := congrArg (fun Q : Polynomial ℚ => Q.coeff 0) h0
        simp at hc, by
        push_cast
        rw [mul_comm]
        exact zetaOfCounts_geometric (((p ^ r) ^ n : ℚ))⟩
    have hsingle_rat : IsRationalPS (zetaOfCounts (fun m => (affinePointCount p r {∏ f ∈ I, f} m : ℚ))) :=
      affine_single_poly_rational hr (∏ f ∈ I, f)
    have hneg_single_rat : IsRationalPS (zetaOfCounts (fun m => -(affinePointCount p r {∏ f ∈ I, f} m : ℚ))) :=
      isRationalPS_inv_of_mul_eq_one hsingle_rat
        (by rw [constantCoeff_zetaOfCounts]; exact one_ne_zero)
        (zetaOfCounts_neg_mul _)
    have hdiff_rat : IsRationalPS (zetaOfCounts (fun m =>
        (((p ^ r) ^ n : ℚ) ^ m) - (affinePointCount p r {∏ f ∈ I, f} m : ℚ))) := by
      have hsub : (fun m => (((p ^ r) ^ n : ℚ) ^ m) - (affinePointCount p r {∏ f ∈ I, f} m : ℚ)) =
          fun m => (((p ^ r) ^ n : ℚ) ^ m) + -(affinePointCount p r {∏ f ∈ I, f} m : ℚ) := by
        ext m; ring
      rw [hsub, zetaOfCounts_add]
      exact isRationalPS_mul hgeom_rat hneg_single_rat
    rcases Nat.even_or_odd I.card with hev | hodd
    · have hsign : ∀ m, (-1 : ℚ) ^ I.card *
          ((((p ^ r) ^ n : ℚ) ^ m) - (affinePointCount p r {∏ f ∈ I, f} m : ℚ)) =
          (((p ^ r) ^ n : ℚ) ^ m) - (affinePointCount p r {∏ f ∈ I, f} m : ℚ) := fun m => by
        rw [hev.neg_one_pow, one_mul]
      simpa [hsign] using hdiff_rat
    · have hsign : ∀ m, (-1 : ℚ) ^ I.card *
          ((((p ^ r) ^ n : ℚ) ^ m) - (affinePointCount p r {∏ f ∈ I, f} m : ℚ)) =
          -((((p ^ r) ^ n : ℚ) ^ m) - (affinePointCount p r {∏ f ∈ I, f} m : ℚ)) := fun m => by
        rw [hodd.neg_one_pow, neg_one_mul]
      simp_rw [hsign]
      exact isRationalPS_inv_of_mul_eq_one hdiff_rat
        (by rw [constantCoeff_zetaOfCounts]; exact one_ne_zero)
        (zetaOfCounts_neg_mul _)
  have hzeta_prod : hasseWeilZeta (affinePointCount p r fs) =
      ∏ I ∈ fs.powerset, zetaOfCounts (fun m => (-1 : ℚ) ^ I.card *
        ((((p ^ r) ^ n : ℚ) ^ m) - (affinePointCount p r {∏ f ∈ I, f} m : ℚ))) := by
    have hsum_zeta : ∀ (T : Finset (Finset (MvPolynomial (Fin n) (GaloisField p r)))),
        zetaOfCounts (fun m => ∑ I ∈ T, (-1 : ℚ) ^ I.card *
          ((((p ^ r) ^ n : ℚ) ^ m) - (affinePointCount p r {∏ f ∈ I, f} m : ℚ))) =
        ∏ I ∈ T, zetaOfCounts (fun m => (-1 : ℚ) ^ I.card *
          ((((p ^ r) ^ n : ℚ) ^ m) - (affinePointCount p r {∏ f ∈ I, f} m : ℚ))) := by
      intro T
      induction T using Finset.induction_on with
      | empty => simp [zetaOfCounts_zero]
      | insert a T ha ih =>
        have hadd : (fun m => ∑ I ∈ insert a T, (-1 : ℚ) ^ I.card *
            ((((p ^ r) ^ n : ℚ) ^ m) - (affinePointCount p r {∏ f ∈ I, f} m : ℚ))) =
          fun m => ((-1 : ℚ) ^ a.card *
            ((((p ^ r) ^ n : ℚ) ^ m) - (affinePointCount p r {∏ f ∈ a, f} m : ℚ))) +
            ∑ I ∈ T, (-1 : ℚ) ^ I.card *
              ((((p ^ r) ^ n : ℚ) ^ m) - (affinePointCount p r {∏ f ∈ I, f} m : ℚ)) := by
          ext m; exact Finset.sum_insert ha
        rw [hadd, zetaOfCounts_add, ih, Finset.prod_insert ha]
    rw [← hsum_zeta fs.powerset]
    unfold hasseWeilZeta
    rw [zetaOfCounts_eq_expSeries_zetaLog, zetaOfCounts_eq_expSeries_zetaLog]
    congr 1
    ext m
    rcases m with _ | m
    · simp [zetaLog]
    · simp only [zetaLog, PowerSeries.coeff_mk, Nat.succ_ne_zero, ↓reduceIte]
      rw [hie (m + 1) (Nat.succ_pos m)]
  rw [hzeta_prod]
  exact isRationalPS_prod fs.powerset _ hfactor_rat

/-- **DWORK'S RATIONALITY THEOREM (1960) — WEIL CONJECTURE I — 100% UNCONDITIONAL**:
For ANY prime `p`, ANY `r > 0` (`q = p^r`), ANY dimension `n : ℕ`, and ANY finite system of
polynomials `fs : Finset (MvPolynomial (Fin n) (GaloisField p r))` defining an arbitrary affine
algebraic set `V(fs) ⊆ 𝔸^n` over `𝔽_q`, the Hasse–Weil zeta function
`Z(V(fs), T) = exp(∑_{m ≥ 1} #V(𝔽_{q^m}) T^m / m) ∈ ℚ[[T]]`
is a **rational function of `T` over `ℚ`** with normalized denominator `Q(0) = 1`! -/
theorem dwork_rationality_unconditional
    (p r n : ℕ) [Fact p.Prime] (hr : 0 < r)
    (fs : Finset (MvPolynomial (Fin n) (GaloisField p r))) :
    ∃ P Q : Polynomial ℚ, Q.coeff 0 = 1 ∧
      hasseWeilZeta (affinePointCount p r fs) * (Q : PowerSeries ℚ) = (P : PowerSeries ℚ) :=
  isRationalPS_normalized_of_const_one (affine_finset_rational hr fs)
    (constantCoeff_zetaOfCounts _)

end CrownTheorem

end RHDirect.DworkWeil1

