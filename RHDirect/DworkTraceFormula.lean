/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Dwork's Trace Formula over `𝔽_q` (Unconditional Weil Conjecture I, Part 1)

This file constructs:
1. The complete ultrametric field `DworkField p = K0(p)[ϖ]/(ϖ^{p-1} + p)` extending
   `K0 p = FractionRing (WittVector p (AlgebraicClosure (ZMod p)))` with normalized `p`-adic
   norm `‖p‖ = p⁻¹`, Dwork uniformizer `ϖ^{p-1} = -p`, and Teichmüller multiplicative lift
   `teich : AlgebraicClosure (ZMod p) →*₀ DworkField p`.
2. Analytic evaluation of Dwork's splitting function `θ(T) = exp(ϖ (T - T^p))`, proof that
   `θ(1)` is a primitive `p`-th root of unity (`θ(1)^p = 1`, `‖θ(1) - 1‖ = ‖ϖ‖ > 0`), and the
   nontrivial additive character `dworkChar p s a = ∏_{j < s} θ(teich(a)^{p^j}) = θ(1)^{Tr(a)}`
   on `𝔽_{p^s} ⊆ AlgebraicClosure (ZMod p)`.
3. The multivariate Dwork splitting series `F_r`, the row-finite infinite Dwork matrix `M`,
   exact matrix powers `(M^m)_{u, v} = coeff_{q^m u - v}(F_{r, m})`, truncation trace
   convergence `‖Tr(M^m) - Tr(M_N^m)‖ ≤ p^{-c (q - 1) N}`, and **Dwork's Trace Formula**:
     `(q^m - 1)^d * Tr(M^m) = ∑_{x ∈ (𝔽_{q^m}ˣ)^d} ψ_{r m}(G(x))`.
-/
import RHDirect.Stage2DworkExp
import RHDirect.Stage14M5_WittFrobeniusDwork
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000
set_option linter.unusedSectionVars false

noncomputable section

open Real Finset Filter Topology BigOperators
open scoped Classical
open RHDirect.PAdicChainValuation
open RHDirect.Stage2DworkExp
open RHDirect.Stage14M5_WittFrobeniusDwork

namespace RHDirect.DworkWeil1

/-! ## Section 1: The Complete Ultrametric Dwork Field `DworkField p = K0(p)(ϖ)` -/

section DworkFieldConstruction

variable (p : ℕ) [hp : Fact p.Prime]

/-- The Eisenstein Dwork polynomial `X^(p-1) + p ∈ K0(p)[X]`. -/
def dworkPoly : Polynomial (K0 p) :=
  Polynomial.X ^ (p - 1) + Polynomial.C (p : K0 p)

lemma dworkPoly_monic : (dworkPoly p).Monic := by
  have hp2 : 2 ≤ p := hp.out.two_le
  have hpos : 0 < p - 1 := by omega
  unfold dworkPoly
  apply Polynomial.Monic.add_of_left (Polynomial.monic_X_pow (p - 1))
  rw [Polynomial.degree_X_pow]
  exact lt_of_le_of_lt Polynomial.degree_C_le (by exact_mod_cast hpos)

lemma dworkPoly_ne_zero : dworkPoly p ≠ 0 :=
  (dworkPoly_monic p).ne_zero

lemma dworkPoly_natDegree : (dworkPoly p).natDegree = p - 1 := by
  have hp2 : 2 ≤ p := hp.out.two_le
  have hpos : 0 < p - 1 := by omega
  unfold dworkPoly
  rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt]
  · exact Polynomial.natDegree_X_pow (p - 1)
  · rw [Polynomial.natDegree_X_pow, Polynomial.natDegree_C]
    exact hpos

/-- The ramified Dwork field `DworkField p := K0(p)[ϖ]/(ϖ^{p-1} + p)`. -/
abbrev DworkField : Type := AdjoinRoot (dworkPoly p)

/-- The Dwork uniformizer `ϖ ∈ DworkField p` satisfying `ϖ^(p - 1) = -p`. -/
def dworkPi : DworkField p := AdjoinRoot.root (dworkPoly p)

lemma dworkPi_pow : (dworkPi p) ^ (p - 1) = -(p : DworkField p) := by
  have hroot : Polynomial.aeval (dworkPi p) (dworkPoly p) = 0 := by
    rw [dworkPi, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  simp only [dworkPoly, map_add, map_pow, Polynomial.aeval_X, map_natCast] at hroot
  exact eq_neg_of_add_eq_zero_left hroot

/-- The power basis `{1, ϖ, ..., ϖ^{p-2}}` of `DworkField p` over `K0 p`. -/
def dworkPowerBasis : PowerBasis (K0 p) (DworkField p) :=
  AdjoinRoot.powerBasis (dworkPoly_ne_zero p)

lemma dworkPowerBasis_dim : (dworkPowerBasis p).dim = p - 1 := by
  change (dworkPoly p).natDegree = p - 1
  exact dworkPoly_natDegree p

lemma dworkPowerBasis_gen : (dworkPowerBasis p).gen = dworkPi p := rfl

/-- The `j`-th coordinate (`0 ≤ j < p - 1`) of `x ∈ DworkField p` in the `ϖ`-power basis. -/
def dworkCoord (x : DworkField p) (j : Fin (p - 1)) : K0 p :=
  (dworkPowerBasis p).basis.repr x ⟨j.val, by rw [dworkPowerBasis_dim]; exact j.isLt⟩

lemma dworkCoord_zero (j : Fin (p - 1)) : dworkCoord p 0 j = 0 := by
  simp [dworkCoord]

lemma dworkCoord_add (x y : DworkField p) (j : Fin (p - 1)) :
    dworkCoord p (x + y) j = dworkCoord p x j + dworkCoord p y j := by
  simp [dworkCoord]

lemma dworkCoord_neg (x : DworkField p) (j : Fin (p - 1)) :
    dworkCoord p (-x) j = -dworkCoord p x j := by
  simp [dworkCoord]

lemma dworkCoord_sub (x y : DworkField p) (j : Fin (p - 1)) :
    dworkCoord p (x - y) j = dworkCoord p x j - dworkCoord p y j := by
  simp [dworkCoord]

lemma dworkCoord_smul (c : K0 p) (x : DworkField p) (j : Fin (p - 1)) :
    dworkCoord p (c • x) j = c * dworkCoord p x j := by
  simp [dworkCoord, smul_eq_mul]

lemma dworkField_eq_sum_coords (x : DworkField p) :
    x = ∑ j : Fin (p - 1), algebraMap (K0 p) (DworkField p) (dworkCoord p x j) *
      (dworkPi p) ^ j.val := by
  conv_lhs => rw [← (dworkPowerBasis p).basis.sum_repr x]
  refine Finset.sum_bij (fun i _ => (⟨i.val, by rw [← dworkPowerBasis_dim p]; exact i.isLt⟩ : Fin (p - 1)))
    (fun _ _ => Finset.mem_univ _)
    (fun i₁ _ i₂ _ h => Fin.ext (by simpa using congrArg Fin.val h))
    (fun j _ => ⟨⟨j.val, by rw [dworkPowerBasis_dim p]; exact j.isLt⟩, Finset.mem_univ _, by ext; rfl⟩)
    ?_
  intro i _
  simp only [dworkCoord, PowerBasis.coe_basis, dworkPowerBasis_gen, Algebra.smul_def, Fin.eta]

lemma dworkCoord_sum_basis (c : Fin (p - 1) → K0 p) (j : Fin (p - 1)) :
    dworkCoord p (∑ i : Fin (p - 1), algebraMap (K0 p) (DworkField p) (c i) * (dworkPi p) ^ i.val) j =
      c j := by
  have hlin : ∑ i : Fin (p - 1), algebraMap (K0 p) (DworkField p) (c i) * (dworkPi p) ^ i.val =
      ∑ i : Fin (dworkPowerBasis p).dim,
        c ⟨i.val, by rw [← dworkPowerBasis_dim p]; exact i.isLt⟩ • (dworkPowerBasis p).basis i := by
    refine Finset.sum_bij (fun i _ => (⟨i.val, by rw [dworkPowerBasis_dim p]; exact i.isLt⟩ : Fin (dworkPowerBasis p).dim))
      (fun _ _ => Finset.mem_univ _)
      (fun i₁ _ i₂ _ h => Fin.ext (by simpa using congrArg Fin.val h))
      (fun i _ => ⟨⟨i.val, by rw [← dworkPowerBasis_dim p]; exact i.isLt⟩, Finset.mem_univ _, by ext; rfl⟩)
      ?_
    intro i _
    simp [PowerBasis.coe_basis, dworkPowerBasis_gen, Algebra.smul_def]
  rw [hlin]
  unfold dworkCoord
  rw [map_sum]
  simp only [map_smul, Module.Basis.repr_self, Finsupp.coe_finsetSum, Finsupp.coe_smul,
    Finset.sum_apply, Pi.smul_apply, Finsupp.single_apply, smul_eq_mul]
  rw [Finset.sum_eq_single ⟨j.val, by rw [dworkPowerBasis_dim p]; exact j.isLt⟩]
  · simp
  · intro b _ hb
    simp [hb]
  · intro h; exact (h (Finset.mem_univ _)).elim

lemma dworkCoord_algebraMap (c : K0 p) (j : Fin (p - 1)) :
    dworkCoord p (algebraMap (K0 p) (DworkField p) c) j = if j.val = 0 then c else 0 := by
  have hp1 : 0 < p - 1 := by have := hp.out.two_le; omega
  have hrepr : algebraMap (K0 p) (DworkField p) c =
      ∑ i : Fin (p - 1), algebraMap (K0 p) (DworkField p) (if i.val = 0 then c else 0) *
        (dworkPi p) ^ i.val := by
    rw [Finset.sum_eq_single ⟨0, hp1⟩]
    · simp
    · intro b _ hb
      have hb0 : b.val ≠ 0 := fun h => hb (Fin.ext h)
      simp [hb0]
    · intro h; exact (h (Finset.mem_univ _)).elim
  rw [hrepr, dworkCoord_sum_basis]

lemma dworkCoord_eq_zero_iff (x : DworkField p) :
    (∀ j : Fin (p - 1), dworkCoord p x j = 0) ↔ x = 0 := by
  constructor
  · intro h
    rw [dworkField_eq_sum_coords p x]
    simp [h]
  · rintro rfl j
    exact dworkCoord_zero p j

/-- Weight factor `p^{-j/(p-1)}` for the `j`-th `ϖ`-power basis coordinate. -/
def dworkWt (j : Fin (p - 1)) : ℝ :=
  (p : ℝ) ^ (-(j.val : ℝ) / ((p : ℝ) - 1))

lemma dworkWt_pos (j : Fin (p - 1)) : 0 < dworkWt p j :=
  Real.rpow_pos_of_pos (by exact_mod_cast hp.out.pos) _

lemma dworkWt_le_one (j : Fin (p - 1)) : dworkWt p j ≤ 1 := by
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.out.one_le
  have hpm1 : (0 : ℝ) < (p : ℝ) - 1 := by
    have h2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.out.two_le
    linarith
  have hexp : -(j.val : ℝ) / ((p : ℝ) - 1) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg _)) hpm1.le
  calc dworkWt p j = (p : ℝ) ^ (-(j.val : ℝ) / ((p : ℝ) - 1)) := rfl
    _ ≤ (p : ℝ) ^ (0 : ℝ) := Real.rpow_le_rpow_of_exponent_le hp1 hexp
    _ = 1 := Real.rpow_zero _

/-- Weighted sup-norm `‖∑ c_j ϖ^j‖ := max_j (wittAbv p c_j * p^{-j/(p-1)})` on `DworkField p`. -/
def dworkNorm (x : DworkField p) : ℝ :=
  have : Nonempty (Fin (p - 1)) := ⟨⟨0, by have := hp.out.two_le; omega⟩⟩
  Finset.univ.sup' Finset.univ_nonempty (fun j : Fin (p - 1) => wittAbv p (dworkCoord p x j) * dworkWt p j)

lemma dworkTerm_le_dworkNorm (x : DworkField p) (j : Fin (p - 1)) :
    wittAbv p (dworkCoord p x j) * dworkWt p j ≤ dworkNorm p x := by
  unfold dworkNorm
  exact Finset.le_sup' (f := fun j : Fin (p - 1) => wittAbv p (dworkCoord p x j) * dworkWt p j)
    (Finset.mem_univ j)

lemma dworkNorm_le_iff (x : DworkField p) {r : ℝ} :
    dworkNorm p x ≤ r ↔ ∀ j : Fin (p - 1), wittAbv p (dworkCoord p x j) * dworkWt p j ≤ r := by
  unfold dworkNorm
  simp [Finset.sup'_le_iff]

lemma dworkNorm_nonneg (x : DworkField p) : 0 ≤ dworkNorm p x := by
  have hp1 : 0 < p - 1 := by have := hp.out.two_le; omega
  exact le_trans (mul_nonneg (AbsoluteValue.nonneg _ _) (dworkWt_pos p ⟨0, hp1⟩).le)
    (dworkTerm_le_dworkNorm p x ⟨0, hp1⟩)

lemma dworkNorm_zero : dworkNorm p 0 = 0 := by
  apply le_antisymm
  · rw [dworkNorm_le_iff]
    intro j
    rw [dworkCoord_zero, map_zero, zero_mul]
  · exact dworkNorm_nonneg p 0

lemma dworkNorm_eq_zero_iff (x : DworkField p) : dworkNorm p x = 0 ↔ x = 0 := by
  constructor
  · intro h
    rw [← dworkCoord_eq_zero_iff p]
    intro j
    have hle : wittAbv p (dworkCoord p x j) * dworkWt p j ≤ 0 := by
      rw [← h]; exact dworkTerm_le_dworkNorm p x j
    have hge : 0 ≤ wittAbv p (dworkCoord p x j) := AbsoluteValue.nonneg _ _
    have h0 : wittAbv p (dworkCoord p x j) = 0 := by
      nlinarith [dworkWt_pos p j]
    exact (AbsoluteValue.eq_zero _).mp h0
  · rintro rfl
    exact dworkNorm_zero p

lemma dworkNorm_nonarch (x y : DworkField p) :
    dworkNorm p (x + y) ≤ max (dworkNorm p x) (dworkNorm p y) := by
  rw [dworkNorm_le_iff]
  intro j
  rw [dworkCoord_add]
  calc wittAbv p (dworkCoord p x j + dworkCoord p y j) * dworkWt p j
      ≤ max (wittAbv p (dworkCoord p x j)) (wittAbv p (dworkCoord p y j)) * dworkWt p j :=
        mul_le_mul_of_nonneg_right (wittAbv_nonarch p _ _) (dworkWt_pos p j).le
    _ = max (wittAbv p (dworkCoord p x j) * dworkWt p j)
            (wittAbv p (dworkCoord p y j) * dworkWt p j) :=
        max_mul_of_nonneg _ _ (dworkWt_pos p j).le
    _ ≤ max (dworkNorm p x) (dworkNorm p y) :=
        max_le_max (dworkTerm_le_dworkNorm p x j) (dworkTerm_le_dworkNorm p y j)

lemma dworkNorm_neg (x : DworkField p) : dworkNorm p (-x) = dworkNorm p x := by
  apply le_antisymm
  · rw [dworkNorm_le_iff]
    intro j
    rw [dworkCoord_neg, AbsoluteValue.map_neg]
    exact dworkTerm_le_dworkNorm p x j
  · rw [dworkNorm_le_iff]
    intro j
    have h := dworkTerm_le_dworkNorm p (-x) j
    rwa [dworkCoord_neg, AbsoluteValue.map_neg] at h

lemma dworkNorm_algebraMap (c : K0 p) :
    dworkNorm p (algebraMap (K0 p) (DworkField p) c) = wittAbv p c := by
  have hp1 : 0 < p - 1 := by have := hp.out.two_le; omega
  apply le_antisymm
  · rw [dworkNorm_le_iff]
    intro j
    rw [dworkCoord_algebraMap]
    split_ifs with h
    · have hw : dworkWt p j = 1 := by simp [dworkWt, h]
      rw [hw, mul_one]
    · simp
  · have h0 := dworkTerm_le_dworkNorm p (algebraMap (K0 p) (DworkField p) c) ⟨0, hp1⟩
    rw [dworkCoord_algebraMap] at h0
    have hw : dworkWt p ⟨0, hp1⟩ = 1 := by simp [dworkWt]
    simpa [hw] using h0

/-- For any nonzero `x : DworkField p`, there is a UNIQUE coordinate `j₀ : Fin (p - 1)` attaining
the maximum `dworkNorm p x`, and every other coordinate has strictly smaller weighted norm! -/
lemma dworkNorm_exists_unique_max {x : DworkField p} (hx : x ≠ 0) :
    ∃ j₀ : Fin (p - 1),
      wittAbv p (dworkCoord p x j₀) * dworkWt p j₀ = dworkNorm p x ∧
      ∀ j : Fin (p - 1), j ≠ j₀ → wittAbv p (dworkCoord p x j) * dworkWt p j < dworkNorm p x := by
  have : Nonempty (Fin (p - 1)) := ⟨⟨0, by have := hp.out.two_le; omega⟩⟩
  obtain ⟨j₀, _, hj₀⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
    (fun j : Fin (p - 1) => wittAbv p (dworkCoord p x j) * dworkWt p j)
  have hj₀_norm : wittAbv p (dworkCoord p x j₀) * dworkWt p j₀ = dworkNorm p x := hj₀.symm
  refine ⟨j₀, hj₀_norm, fun j hjne => ?_⟩
  have hle : wittAbv p (dworkCoord p x j) * dworkWt p j ≤ dworkNorm p x :=
    dworkTerm_le_dworkNorm p x j
  refine lt_of_le_of_ne hle fun heq => ?_
  have hpos : 0 < dworkNorm p x :=
    lt_of_le_of_ne (dworkNorm_nonneg p x) (Ne.symm (mt (dworkNorm_eq_zero_iff p x).mp hx))
  have hc0 : dworkCoord p x j₀ ≠ 0 := by
    intro h0; rw [h0, map_zero, zero_mul] at hj₀_norm; linarith
  have hc : dworkCoord p x j ≠ 0 := by
    intro h0; rw [h0, map_zero, zero_mul] at heq; linarith
  obtain ⟨m₀, hm₀⟩ := wittAbvOn_value p (kb p) (dworkCoord p x j₀) hc0
  obtain ⟨m, hm⟩ := wittAbvOn_value p (kb p) (dworkCoord p x j) hc
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.out.one_lt
  have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.out.pos
  have hpm1 : (0 : ℝ) < (p : ℝ) - 1 := by
    have h2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.out.two_le
    linarith
  have heq_pow : (p : ℝ) ^ ((m : ℝ) + -(j.val : ℝ) / ((p : ℝ) - 1)) =
      (p : ℝ) ^ ((m₀ : ℝ) + -(j₀.val : ℝ) / ((p : ℝ) - 1)) := by
    rw [Real.rpow_add hppos, Real.rpow_add hppos, Real.rpow_intCast, Real.rpow_intCast]
    change (p : ℝ) ^ m * dworkWt p j = (p : ℝ) ^ m₀ * dworkWt p j₀
    rw [← hm, ← hm₀]
    exact heq.trans hj₀_norm.symm
  have hexp : (m : ℝ) + -(j.val : ℝ) / ((p : ℝ) - 1) =
      (m₀ : ℝ) + -(j₀.val : ℝ) / ((p : ℝ) - 1) :=
    (Real.rpow_right_inj hppos hp1.ne').mp heq_pow
  have hmul : ((m : ℝ) - (m₀ : ℝ)) * ((p : ℝ) - 1) = (j.val : ℝ) - (j₀.val : ℝ) := by
    field_simp [hpm1.ne'] at hexp
    linarith
  have hint : (m - m₀) * ((p - 1 : ℕ) : ℤ) = (j.val : ℤ) - (j₀.val : ℤ) := by
    have hcast : (((m - m₀) * ((p - 1 : ℕ) : ℤ) : ℤ) : ℝ) = (((j.val : ℤ) - (j₀.val : ℤ) : ℤ) : ℝ) := by
      push_cast [Nat.cast_sub hp.out.one_le]
      exact hmul
    exact_mod_cast hcast
  have hdvd : ((p - 1 : ℕ) : ℤ) ∣ ((j.val : ℤ) - (j₀.val : ℤ)) := ⟨m - m₀, by linarith⟩
  obtain ⟨k, hk⟩ := hdvd
  have hjlt : (j.val : ℤ) < (p - 1 : ℕ) := by exact_mod_cast j.isLt
  have hj0lt : (j₀.val : ℤ) < (p - 1 : ℕ) := by exact_mod_cast j₀.isLt
  have hk0 : k = 0 := by nlinarith
  rw [hk0, mul_zero] at hk
  have hval : j.val = j₀.val := by omega
  exact hjne (Fin.ext hval)

/-- Explicit convolution formula for the `k`-th coordinate of a product `x * y` in `DworkField p`:
terms with `a + b = k` enter with `+1`, terms with `a + b = k + (p - 1)` enter with `-p`. -/
lemma dworkCoord_mul (x y : DworkField p) (k : Fin (p - 1)) :
    dworkCoord p (x * y) k =
      ∑ a : Fin (p - 1), ∑ b : Fin (p - 1),
        if a.val + b.val = k.val then dworkCoord p x a * dworkCoord p y b
        else if a.val + b.val = k.val + (p - 1) then -(p : K0 p) * (dworkCoord p x a * dworkCoord p y b)
        else 0 := by
  have hxy : x * y =
      ∑ k' : Fin (p - 1),
        algebraMap (K0 p) (DworkField p)
          (∑ a : Fin (p - 1), ∑ b : Fin (p - 1),
            if a.val + b.val = k'.val then dworkCoord p x a * dworkCoord p y b
            else if a.val + b.val = k'.val + (p - 1) then -(p : K0 p) * (dworkCoord p x a * dworkCoord p y b)
            else 0) * (dworkPi p) ^ k'.val := by
    conv_lhs => rw [dworkField_eq_sum_coords p x, dworkField_eq_sum_coords p y]
    rw [Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    have hterm : ∀ a b : Fin (p - 1),
        (algebraMap (K0 p) (DworkField p) (dworkCoord p x a) * (dworkPi p) ^ a.val) *
        (algebraMap (K0 p) (DworkField p) (dworkCoord p y b) * (dworkPi p) ^ b.val) =
        ∑ k' : Fin (p - 1),
          algebraMap (K0 p) (DworkField p)
            (if a.val + b.val = k'.val then dworkCoord p x a * dworkCoord p y b
             else if a.val + b.val = k'.val + (p - 1) then -(p : K0 p) * (dworkCoord p x a * dworkCoord p y b)
             else 0) * (dworkPi p) ^ k'.val := by
      intro a b
      by_cases hlt : a.val + b.val < p - 1
      · rw [Finset.sum_eq_single ⟨a.val + b.val, hlt⟩]
        · simp [map_mul, pow_add]; ring
        · intro k' _ hk'
          have hne1 : a.val + b.val ≠ k'.val := fun h => hk' (Fin.ext h.symm)
          have hne2 : a.val + b.val ≠ k'.val + (p - 1) := by omega
          simp [hne1, hne2]
        · intro h; exact (h (Finset.mem_univ _)).elim
      · have hge : p - 1 ≤ a.val + b.val := Nat.le_of_not_lt hlt
        have hsub_lt : a.val + b.val - (p - 1) < p - 1 := by omega
        rw [Finset.sum_eq_single ⟨a.val + b.val - (p - 1), hsub_lt⟩]
        · have hne1 : a.val + b.val ≠ a.val + b.val - (p - 1) := by
            have := hp.out.two_le; omega
          have heq2 : a.val + b.val = a.val + b.val - (p - 1) + (p - 1) := by omega
          simp only [if_neg hne1, if_pos heq2, map_mul, map_neg, map_natCast]
          have hpow : (dworkPi p) ^ a.val * (dworkPi p) ^ b.val =
              -(p : DworkField p) * (dworkPi p) ^ (a.val + b.val - (p - 1)) := by
            rw [← pow_add, ← dworkPi_pow p, ← pow_add, Nat.add_sub_cancel' hge]
          calc (algebraMap (K0 p) (DworkField p) (dworkCoord p x a) * (dworkPi p) ^ a.val) *
                (algebraMap (K0 p) (DworkField p) (dworkCoord p y b) * (dworkPi p) ^ b.val)
              = algebraMap (K0 p) (DworkField p) (dworkCoord p x a) *
                algebraMap (K0 p) (DworkField p) (dworkCoord p y b) *
                ((dworkPi p) ^ a.val * (dworkPi p) ^ b.val) := by ring
            _ = _ := by rw [hpow]; ring
        · intro k' _ hk'
          have hne1 : a.val + b.val ≠ k'.val := by omega
          have hne2 : a.val + b.val ≠ k'.val + (p - 1) := fun h =>
            hk' (Fin.ext (show k'.val = a.val + b.val - (p - 1) by omega))
          simp [hne1, hne2]
        · intro h; exact (h (Finset.mem_univ _)).elim
    simp_rw [hterm]
    conv_lhs =>
      arg 2
      ext a
      rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k' _ => ?_
    simp_rw [map_sum, Finset.sum_mul]
  rw [hxy, dworkCoord_sum_basis]

/-- Helper: ultrametric bound for a finite sum under `wittAbv p`. -/
lemma wittAbv_sum_le {ι : Type*} (s : Finset ι) (f : ι → K0 p) {B : ℝ} (hB : 0 ≤ B)
    (hf : ∀ i ∈ s, wittAbv p (f i) ≤ B) :
    wittAbv p (∑ i ∈ s, f i) ≤ B := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hB]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact le_trans (wittAbv_nonarch p _ _)
      (max_le (hf a (Finset.mem_insert_self a s))
        (ih fun i hi => hf i (Finset.mem_insert_of_mem hi)))

/-- Helper: strict ultrametric bound for a finite sum under `wittAbv p`. -/
lemma wittAbv_sum_lt {ι : Type*} (s : Finset ι) (f : ι → K0 p) {B : ℝ} (hB : 0 < B)
    (hf : ∀ i ∈ s, wittAbv p (f i) < B) :
    wittAbv p (∑ i ∈ s, f i) < B := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hB]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact lt_of_le_of_lt (wittAbv_nonarch p _ _)
      (max_lt (hf a (Finset.mem_insert_self a s))
        (ih fun i hi => hf i (Finset.mem_insert_of_mem hi)))

/-- Helper: ultrametric strict dominance `wittAbv p (u + v) = wittAbv p u` when `wittAbv p v < wittAbv p u`. -/
lemma wittAbv_add_eq_left_of_lt {u v : K0 p} (h : wittAbv p v < wittAbv p u) :
    wittAbv p (u + v) = wittAbv p u := by
  apply le_antisymm
  · exact le_trans (wittAbv_nonarch p u v) (max_le le_rfl h.le)
  · by_contra hlt
    push Not at hlt
    have hu : u = (u + v) + (-v) := by ring
    have hle : wittAbv p u ≤ max (wittAbv p (u + v)) (wittAbv p (-v)) := by
      conv_lhs => rw [hu]
      exact wittAbv_nonarch p (u + v) (-v)
    rw [AbsoluteValue.map_neg] at hle
    exact lt_irrefl _ (lt_of_le_of_lt hle (max_lt hlt h))

/-- **Exact Multiplicativity of `dworkNorm` on `DworkField p`**:
`dworkNorm p (x * y) = dworkNorm p x * dworkNorm p y` for all `x, y : DworkField p`! -/
theorem dworkNorm_mul (x y : DworkField p) :
    dworkNorm p (x * y) = dworkNorm p x * dworkNorm p y := by
  by_cases hx : x = 0
  · subst hx; simp [dworkNorm_zero]
  by_cases hy : y = 0
  · subst hy; simp [dworkNorm_zero]
  obtain ⟨j₁, hj₁_eq, hj₁_lt⟩ := dworkNorm_exists_unique_max p hx
  obtain ⟨j₂, hj₂_eq, hj₂_lt⟩ := dworkNorm_exists_unique_max p hy
  have hxpos : 0 < dworkNorm p x :=
    lt_of_le_of_ne (dworkNorm_nonneg p x) (Ne.symm (mt (dworkNorm_eq_zero_iff p x).mp hx))
  have hypos : 0 < dworkNorm p y :=
    lt_of_le_of_ne (dworkNorm_nonneg p y) (Ne.symm (mt (dworkNorm_eq_zero_iff p y).mp hy))
  have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.out.pos
  have hpm1 : (0 : ℝ) < (p : ℝ) - 1 := by
    have h2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.out.two_le
    linarith
  let T (k : Fin (p - 1)) (ab : Fin (p - 1) × Fin (p - 1)) : K0 p :=
    if ab.1.val + ab.2.val = k.val then dworkCoord p x ab.1 * dworkCoord p y ab.2
    else if ab.1.val + ab.2.val = k.val + (p - 1) then
      -(p : K0 p) * (dworkCoord p x ab.1 * dworkCoord p y ab.2)
    else 0
  have hT_wt_eq1 : ∀ (k a b : Fin (p - 1)), a.val + b.val = k.val →
      wittAbv p (dworkCoord p x a * dworkCoord p y b) * dworkWt p k =
        (wittAbv p (dworkCoord p x a) * dworkWt p a) *
        (wittAbv p (dworkCoord p y b) * dworkWt p b) := by
    intro k a b hab
    rw [map_mul]
    have hwt : dworkWt p k = dworkWt p a * dworkWt p b := by
      unfold dworkWt
      rw [← Real.rpow_add hppos]
      congr 1
      have : (k.val : ℝ) = (a.val : ℝ) + (b.val : ℝ) := by exact_mod_cast hab.symm
      rw [this]; ring
    rw [hwt]; ring
  have hT_wt_eq2 : ∀ (k a b : Fin (p - 1)), a.val + b.val = k.val + (p - 1) →
      wittAbv p (-(p : K0 p) * (dworkCoord p x a * dworkCoord p y b)) * dworkWt p k =
        (wittAbv p (dworkCoord p x a) * dworkWt p a) *
        (wittAbv p (dworkCoord p y b) * dworkWt p b) := by
    intro k a b hab
    rw [map_mul, AbsoluteValue.map_neg, wittAbv_p, map_mul]
    have hwt : (p : ℝ)⁻¹ * dworkWt p k = dworkWt p a * dworkWt p b := by
      unfold dworkWt
      rw [← Real.rpow_neg_one (p : ℝ), ← Real.rpow_add hppos, ← Real.rpow_add hppos]
      congr 1
      have hk : (a.val : ℝ) + (b.val : ℝ) = (k.val : ℝ) + ((p : ℝ) - 1) := by
        have hcast : ((a.val + b.val : ℕ) : ℝ) = ((k.val + (p - 1) : ℕ) : ℝ) := by exact_mod_cast hab
        push_cast [Nat.cast_sub hp.out.one_le] at hcast
        exact hcast
      field_simp [hpm1.ne']
      linarith
    calc (p : ℝ)⁻¹ * (wittAbv p (dworkCoord p x a) * wittAbv p (dworkCoord p y b)) * dworkWt p k
        = wittAbv p (dworkCoord p x a) * wittAbv p (dworkCoord p y b) * ((p : ℝ)⁻¹ * dworkWt p k) := by ring
      _ = _ := by rw [hwt]; ring
  have hT_le : ∀ k ab, wittAbv p (T k ab) * dworkWt p k ≤ dworkNorm p x * dworkNorm p y := by
    intro k ⟨a, b⟩
    dsimp only [T]
    split_ifs with h1 h2
    · rw [hT_wt_eq1 k a b h1]
      exact mul_le_mul (dworkTerm_le_dworkNorm p x a) (dworkTerm_le_dworkNorm p y b)
        (mul_nonneg (AbsoluteValue.nonneg _ _) (dworkWt_pos p b).le) (dworkNorm_nonneg p x)
    · rw [hT_wt_eq2 k a b h2]
      exact mul_le_mul (dworkTerm_le_dworkNorm p x a) (dworkTerm_le_dworkNorm p y b)
        (mul_nonneg (AbsoluteValue.nonneg _ _) (dworkWt_pos p b).le) (dworkNorm_nonneg p x)
    · rw [map_zero, zero_mul]
      exact mul_nonneg (dworkNorm_nonneg p x) (dworkNorm_nonneg p y)
  have hT_lt : ∀ k ab, ab ≠ (j₁, j₂) →
      wittAbv p (T k ab) * dworkWt p k < dworkNorm p x * dworkNorm p y := by
    intro k ⟨a, b⟩ hne
    have hprod_lt : (wittAbv p (dworkCoord p x a) * dworkWt p a) *
        (wittAbv p (dworkCoord p y b) * dworkWt p b) < dworkNorm p x * dworkNorm p y := by
      by_cases ha : a = j₁
      · have hb : b ≠ j₂ := fun hb' => hne (Prod.ext ha hb')
        rw [ha, hj₁_eq]
        exact mul_lt_mul_of_pos_left (hj₂_lt b hb) hxpos
      · have h1 := hj₁_lt a ha
        have h2 := dworkTerm_le_dworkNorm p y b
        have h1_nn : 0 ≤ wittAbv p (dworkCoord p x a) * dworkWt p a :=
          mul_nonneg (AbsoluteValue.nonneg _ _) (dworkWt_pos p a).le
        have h2_nn : 0 ≤ wittAbv p (dworkCoord p y b) * dworkWt p b :=
          mul_nonneg (AbsoluteValue.nonneg _ _) (dworkWt_pos p b).le
        nlinarith
    dsimp only [T]
    split_ifs with h1 h2
    · rw [hT_wt_eq1 k a b h1]; exact hprod_lt
    · rw [hT_wt_eq2 k a b h2]; exact hprod_lt
    · rw [map_zero, zero_mul]; exact mul_pos hxpos hypos
  have hcoord_eq : ∀ k : Fin (p - 1),
      dworkCoord p (x * y) k = ∑ ab : Fin (p - 1) × Fin (p - 1), T k ab := by
    intro k
    rw [dworkCoord_mul, Fintype.sum_prod_type]
  apply le_antisymm
  · rw [dworkNorm_le_iff]
    intro k
    rw [hcoord_eq k]
    have hsum : wittAbv p (∑ ab : Fin (p - 1) × Fin (p - 1), T k ab) ≤
        dworkNorm p x * dworkNorm p y / dworkWt p k := by
      refine wittAbv_sum_le p _ _ (div_nonneg (mul_nonneg (dworkNorm_nonneg p x)
        (dworkNorm_nonneg p y)) (dworkWt_pos p k).le) fun ab _ => ?_
      exact (le_div_iff₀ (dworkWt_pos p k)).mpr (hT_le k ab)
    exact (le_div_iff₀ (dworkWt_pos p k)).mp hsum
  · have hk₀_lt : (j₁.val + j₂.val) % (p - 1) < p - 1 :=
      Nat.mod_lt _ (by have := hp.out.two_le; omega)
    let k₀ : Fin (p - 1) := ⟨(j₁.val + j₂.val) % (p - 1), hk₀_lt⟩
    have hdom_eq : wittAbv p (T k₀ (j₁, j₂)) * dworkWt p k₀ = dworkNorm p x * dworkNorm p y := by
      by_cases hlt : j₁.val + j₂.val < p - 1
      · have h1 : j₁.val + j₂.val = k₀.val := (Nat.mod_eq_of_lt hlt).symm
        dsimp only [T]
        rw [if_pos h1, hT_wt_eq1 k₀ j₁ j₂ h1, hj₁_eq, hj₂_eq]
      · have hge : p - 1 ≤ j₁.val + j₂.val := Nat.le_of_not_lt hlt
        have hk0val : k₀.val = j₁.val + j₂.val - (p - 1) := by
          change (j₁.val + j₂.val) % (p - 1) = j₁.val + j₂.val - (p - 1)
          have hsub : j₁.val + j₂.val - (p - 1) < p - 1 := by omega
          conv_lhs => rw [← Nat.sub_add_cancel hge]
          rw [Nat.add_mod_right, Nat.mod_eq_of_lt hsub]
        have hne1 : j₁.val + j₂.val ≠ k₀.val := by
          have := hp.out.two_le; omega
        have h2 : j₁.val + j₂.val = k₀.val + (p - 1) := by omega
        dsimp only [T]
        rw [if_neg hne1, if_pos h2, hT_wt_eq2 k₀ j₁ j₂ h2, hj₁_eq, hj₂_eq]
    have hsplit : dworkCoord p (x * y) k₀ =
        T k₀ (j₁, j₂) + ∑ ab ∈ Finset.univ.erase (j₁, j₂), T k₀ ab := by
      rw [hcoord_eq k₀, Finset.add_sum_erase _ _ (Finset.mem_univ _)]
    have hrest_lt : wittAbv p (∑ ab ∈ Finset.univ.erase (j₁, j₂), T k₀ ab) <
        wittAbv p (T k₀ (j₁, j₂)) := by
      have hpos_dom : 0 < wittAbv p (T k₀ (j₁, j₂)) := by
        have : 0 < wittAbv p (T k₀ (j₁, j₂)) * dworkWt p k₀ := by
          rw [hdom_eq]; exact mul_pos hxpos hypos
        exact pos_of_mul_pos_left this (dworkWt_pos p k₀).le
      refine wittAbv_sum_lt p _ _ hpos_dom fun ab hab => ?_
      have hne : ab ≠ (j₁, j₂) := (Finset.mem_erase.mp hab).1
      have hlt := hT_lt k₀ ab hne
      rw [← hdom_eq] at hlt
      exact lt_of_mul_lt_mul_right hlt (dworkWt_pos p k₀).le
    have hle := dworkTerm_le_dworkNorm p (x * y) k₀
    rw [hsplit, wittAbv_add_eq_left_of_lt p hrest_lt, hdom_eq] at hle
    exact hle

/-- `DworkField p` has no zero divisors, hence is an integral domain. -/
theorem dworkField_isDomain : IsDomain (DworkField p) := by
  have hnz : NoZeroDivisors (DworkField p) := ⟨fun {x y} hxy => by
    have h0 : dworkNorm p x * dworkNorm p y = 0 := by
      rw [← dworkNorm_mul, hxy, dworkNorm_zero]
    rcases mul_eq_zero.mp h0 with hx | hy
    · exact Or.inl ((dworkNorm_eq_zero_iff p x).mp hx)
    · exact Or.inr ((dworkNorm_eq_zero_iff p y).mp hy)⟩
  have hnt : Nontrivial (DworkField p) := by
    refine ⟨⟨0, 1, fun h01 => ?_⟩⟩
    have h1 : dworkNorm p 1 = 1 := by
      rw [show (1 : DworkField p) = algebraMap (K0 p) (DworkField p) 1 by simp,
        dworkNorm_algebraMap, map_one]
    rw [← h01, dworkNorm_zero] at h1
    norm_num at h1
  exact NoZeroDivisors.to_isDomain _

/-- `dworkPoly p = X^(p-1) + p` is irreducible over `K0 p` (immediate from `IsDomain (AdjoinRoot _)`!). -/
theorem dworkPoly_irreducible : Irreducible (dworkPoly p) := by
  have : IsDomain (AdjoinRoot (dworkPoly p)) := dworkField_isDomain p
  have hprime_ideal : (Ideal.span {dworkPoly p}).IsPrime :=
    (Ideal.Quotient.isDomain_iff_prime (Ideal.span {dworkPoly p})).mp this
  have hprime : Prime (dworkPoly p) :=
    (Ideal.span_singleton_prime (dworkPoly_ne_zero p)).mp hprime_ideal
  exact hprime.irreducible

instance dworkPoly_irreducible_fact : Fact (Irreducible (dworkPoly p)) :=
  ⟨dworkPoly_irreducible p⟩

/-- Normalized `p`-adic absolute value on `DworkField p`. -/
def dworkAbv : AbsoluteValue (DworkField p) ℝ where
  toFun := dworkNorm p
  map_mul' := dworkNorm_mul p
  nonneg' := dworkNorm_nonneg p
  eq_zero' := dworkNorm_eq_zero_iff p
  add_le' x y := le_trans (dworkNorm_nonarch p x y)
    (max_le (le_add_of_nonneg_right (dworkNorm_nonneg p y))
      (le_add_of_nonneg_left (dworkNorm_nonneg p x)))

/-- Local `NormedField (DworkField p)` (diamond-free via `normedFieldOfAbv`). -/
@[instance_reducible]
def dworkNormedField : NormedField (DworkField p) :=
  normedFieldOfAbv (dworkAbv p)

theorem dworkField_ultra :
    letI := dworkNormedField p
    IsUltrametricDist (DworkField p) := by
  let _ : NormedField (DworkField p) := dworkNormedField p
  exact IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm fun x y =>
    dworkNorm_nonarch p x y

theorem dworkField_charZero : CharZero (DworkField p) := by
  have : CharZero (K0 p) := (concreteWittRingLift p).charZeroK
  exact charZero_of_injective_algebraMap (algebraMap (K0 p) (DworkField p)).injective

theorem dworkField_norm_p :
    letI := dworkNormedField p
    ‖(p : DworkField p)‖ = (p : ℝ)⁻¹ := by
  let _ : NormedField (DworkField p) := dworkNormedField p
  change dworkNorm p (p : DworkField p) = (p : ℝ)⁻¹
  rw [show (p : DworkField p) = algebraMap (K0 p) (DworkField p) (p : K0 p) by simp,
    dworkNorm_algebraMap, wittAbv_p]

theorem dworkField_norm_p_lt_one :
    letI := dworkNormedField p
    ‖(p : DworkField p)‖ < 1 := by
  let _ : NormedField (DworkField p) := dworkNormedField p
  rw [dworkField_norm_p p]
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.out.one_lt)

/-- Completeness of `DworkField p` (from `witt_complete` on each `ϖ`-basis coordinate). -/
theorem dworkField_complete :
    letI := dworkNormedField p
    CompleteSpace (DworkField p) := by
  let _ : NormedField (DworkField p) := dworkNormedField p
  let _ : NormedField (K0 p) := wittNormedField p
  have _ : CompleteSpace (K0 p) := witt_complete p
  refine Metric.complete_of_cauchySeq_tendsto fun u hu => ?_
  have hcoord_cauchy : ∀ j : Fin (p - 1), CauchySeq (fun n => dworkCoord p (u n) j) := by
    intro j
    rw [Metric.cauchySeq_iff] at hu ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := hu (ε * dworkWt p j) (mul_pos hε (dworkWt_pos p j))
    refine ⟨N, fun m hm n hn => ?_⟩
    have hdist : dworkNorm p (u m - u n) < ε * dworkWt p j := hN m hm n hn
    have hterm : wittAbv p (dworkCoord p (u m) j - dworkCoord p (u n) j) * dworkWt p j ≤
        dworkNorm p (u m - u n) := by
      rw [← dworkCoord_sub]
      exact dworkTerm_le_dworkNorm p (u m - u n) j
    have hlt : wittAbv p (dworkCoord p (u m) j - dworkCoord p (u n) j) * dworkWt p j <
        ε * dworkWt p j := lt_of_le_of_lt hterm hdist
    exact lt_of_mul_lt_mul_right hlt (dworkWt_pos p j).le
  choose L hL using fun j => cauchySeq_tendsto_of_complete (hcoord_cauchy j)
  let x : DworkField p :=
    ∑ j : Fin (p - 1), algebraMap (K0 p) (DworkField p) (L j) * (dworkPi p) ^ j.val
  refine ⟨x, ?_⟩
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hLj : ∀ j : Fin (p - 1), ∃ N, ∀ n ≥ N, wittAbv p (dworkCoord p (u n) j - L j) < ε := by
    intro j
    exact (Metric.tendsto_atTop.mp (hL j)) ε hε
  choose Nj hNj using hLj
  refine ⟨Finset.univ.sup Nj, fun n hn => ?_⟩
  change dworkNorm p (u n - x) < ε
  have hne : (Finset.univ : Finset (Fin (p - 1))).Nonempty :=
    ⟨⟨0, by have := hp.out.two_le; omega⟩, Finset.mem_univ _⟩
  have hle : dworkNorm p (u n - x) ≤ Finset.univ.sup' hne
      (fun j : Fin (p - 1) => wittAbv p (dworkCoord p (u n) j - L j)) := by
    rw [dworkNorm_le_iff]
    intro j
    rw [dworkCoord_sub, dworkCoord_sum_basis]
    calc wittAbv p (dworkCoord p (u n) j - L j) * dworkWt p j
        ≤ wittAbv p (dworkCoord p (u n) j - L j) * 1 :=
          mul_le_mul_of_nonneg_left (dworkWt_le_one p j) (AbsoluteValue.nonneg _ _)
      _ = wittAbv p (dworkCoord p (u n) j - L j) := mul_one _
      _ ≤ _ := Finset.le_sup' (f := fun j : Fin (p - 1) => wittAbv p (dworkCoord p (u n) j - L j))
          (Finset.mem_univ j)
  refine lt_of_le_of_lt hle ?_
  rw [Finset.sup'_lt_iff]
  intro j _
  exact hNj j n (le_trans (Finset.le_sup (f := Nj) (Finset.mem_univ j)) hn)

/-- Teichmüller multiplicative lift `teich : kb p →*₀ DworkField p` (where `kb p = AlgebraicClosure (ZMod p)`). -/
def teich : kb p →*₀ DworkField p where
  toFun a := algebraMap (K0 p) (DworkField p)
    (algebraMap (WW p) (K0 p) (WittVector.teichmuller p a))
  map_zero' := by simp
  map_one' := by simp
  map_mul' a b := by simp [map_mul]

lemma teich_norm_le_one (a : kb p) :
    letI := dworkNormedField p
    ‖teich p a‖ ≤ 1 := by
  let _ : NormedField (DworkField p) := dworkNormedField p
  change dworkNorm p (algebraMap (K0 p) (DworkField p)
    (algebraMap (WW p) (K0 p) (WittVector.teichmuller p a))) ≤ 1
  rw [dworkNorm_algebraMap]
  exact wittAbvOn_coe_le_one p (kb p) _

lemma teich_injective : Function.Injective (teich p) := by
  intro a b hab
  have h1 : algebraMap (WW p) (K0 p) (WittVector.teichmuller p a) =
      algebraMap (WW p) (K0 p) (WittVector.teichmuller p b) :=
    (algebraMap (K0 p) (DworkField p)).injective hab
  have h2 : WittVector.teichmuller p a = WittVector.teichmuller p b :=
    IsFractionRing.injective (WW p) (K0 p) h1
  have h3 := congrArg (fun w : WW p => w.coeff 0) h2
  simpa [WittVector.teichmuller_coeff_zero] using h3

lemma teich_ne_zero_iff (a : kb p) : teich p a ≠ 0 ↔ a ≠ 0 := by
  constructor
  · intro h ha; exact h (by rw [ha, map_zero])
  · intro ha h0; exact ha (teich_injective p (h0.trans (map_zero _).symm))

lemma teich_norm_eq_one {a : kb p} (ha : a ≠ 0) :
    letI := dworkNormedField p
    ‖teich p a‖ = 1 := by
  let _ : NormedField (DworkField p) := dworkNormedField p
  have h1 : ‖teich p a‖ ≤ 1 := teich_norm_le_one p a
  have h2 : ‖teich p a⁻¹‖ ≤ 1 := teich_norm_le_one p a⁻¹
  have hmul : teich p a * teich p a⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ ha, map_one]
  have h1eq : ‖teich p a‖ * ‖teich p a⁻¹‖ = 1 := by
    rw [← norm_mul, hmul, norm_one]
  nlinarith [norm_nonneg (teich p a), norm_nonneg (teich p a⁻¹)]

end DworkFieldConstruction

/-! ## Section 2: Power-Series Evaluation, `θ(1)` Primitivity, and Dwork's Additive Character -/

section DworkCharacter

variable {K : Type*}

/-- Analytic evaluation of a formal power series `f ∈ K[[X]]` at `x ∈ K`: `∑' n, coeff n f * x ^ n`. -/
def evalPS [NormedField K] (x : K) (f : PowerSeries K) : K :=
  ∑' n : ℕ, PowerSeries.coeff n f * x ^ n

/-- Substitution `f(X^k)` for `k ≥ 1`. -/
def substPow {R : Type*} [CommSemiring R] (k : ℕ) (f : PowerSeries R) : PowerSeries R :=
  PowerSeries.mk fun n => if k ∣ n then PowerSeries.coeff (n / k) f else 0

lemma coeff_substPow {R : Type*} [CommSemiring R] (k : ℕ) (f : PowerSeries R) (n : ℕ) :
    PowerSeries.coeff n (substPow k f) = if k ∣ n then PowerSeries.coeff (n / k) f else 0 := by
  simp [substPow]

lemma substPow_one {R : Type*} [CommSemiring R] {k : ℕ} (hk : 0 < k) :
    substPow k (1 : PowerSeries R) = 1 := by
  ext n
  rw [coeff_substPow]
  by_cases hn : n = 0
  · subst hn; simp
  · conv_rhs => rw [PowerSeries.coeff_one, if_neg hn]
    split_ifs with hd
    · rw [PowerSeries.coeff_one, if_neg]
      intro hdiv
      obtain ⟨m, rfl⟩ := hd
      rw [Nat.mul_div_cancel_left m hk] at hdiv
      subst hdiv
      exact hn (mul_zero k)
    · rfl

lemma substPow_add {R : Type*} [CommSemiring R] (k : ℕ) (f g : PowerSeries R) :
    substPow k (f + g) = substPow k f + substPow k g := by
  ext n
  simp only [coeff_substPow, map_add]
  split_ifs <;> simp

lemma substPow_mul {R : Type*} [CommSemiring R] {k : ℕ} (hk : 0 < k) (f g : PowerSeries R) :
    substPow k (f * g) = substPow k f * substPow k g := by
  ext n
  rw [coeff_substPow]
  conv_rhs => rw [PowerSeries.coeff_mul]
  by_cases hd : k ∣ n
  · obtain ⟨m, rfl⟩ := hd
    rw [if_pos ⟨m, rfl⟩, Nat.mul_div_cancel_left m hk, PowerSeries.coeff_mul]
    symm
    have hfilt : ∑ x ∈ Finset.antidiagonal (k * m),
        PowerSeries.coeff x.1 (substPow k f) * PowerSeries.coeff x.2 (substPow k g) =
      ∑ x ∈ (Finset.antidiagonal (k * m)).filter (fun x : ℕ × ℕ => k ∣ x.1 ∧ k ∣ x.2),
        PowerSeries.coeff (x.1 / k) f * PowerSeries.coeff (x.2 / k) g := by
      rw [← Finset.sum_subset (Finset.filter_subset (fun x : ℕ × ℕ => k ∣ x.1 ∧ k ∣ x.2)
          (Finset.antidiagonal (k * m)))]
      · refine Finset.sum_congr rfl fun x hx => ?_
        have hdiv := (Finset.mem_filter.mp hx).2
        rw [coeff_substPow, coeff_substPow, if_pos hdiv.1, if_pos hdiv.2]
      · intro x hx hnot
        simp only [Finset.mem_filter, hx, true_and, not_and_or] at hnot
        rw [coeff_substPow, coeff_substPow]
        rcases hnot with h1 | h2
        · rw [if_neg h1, zero_mul]
        · rw [if_neg h2, mul_zero]
    rw [hfilt]
    refine Finset.sum_bij (fun (x : ℕ × ℕ) _ => (x.1 / k, x.2 / k)) ?_ ?_ ?_ ?_
    · intro x hx
      rw [Finset.mem_filter, Finset.mem_antidiagonal] at hx
      rw [Finset.mem_antidiagonal]
      obtain ⟨a, ha⟩ := hx.2.1
      obtain ⟨b, hb⟩ := hx.2.2
      rw [ha, hb, Nat.mul_div_cancel_left a hk, Nat.mul_div_cancel_left b hk]
      have hkm : k * (a + b) = k * m := by rw [mul_add, ← ha, ← hb, hx.1]
      exact Nat.eq_of_mul_eq_mul_left hk hkm
    · intro x₁ hx₁ x₂ hx₂ heq
      rw [Finset.mem_filter] at hx₁ hx₂
      have h1 : x₁.1 / k = x₂.1 / k := congrArg Prod.fst heq
      have h2 : x₁.2 / k = x₂.2 / k := congrArg Prod.snd heq
      ext
      · rw [← Nat.mul_div_cancel' hx₁.2.1, ← Nat.mul_div_cancel' hx₂.2.1, h1]
      · rw [← Nat.mul_div_cancel' hx₁.2.2, ← Nat.mul_div_cancel' hx₂.2.2, h2]
    · intro ab hab
      rw [Finset.mem_antidiagonal] at hab
      refine ⟨(k * ab.1, k * ab.2), ?_, ?_⟩
      · rw [Finset.mem_filter, Finset.mem_antidiagonal]
        exact ⟨by rw [← mul_add, hab], ⟨ab.1, rfl⟩, ⟨ab.2, rfl⟩⟩
      · ext <;> simp [Nat.mul_div_cancel_left _ hk]
    · intro _ _; rfl
  · rw [if_neg hd]
    symm
    refine Finset.sum_eq_zero fun x hx => ?_
    rw [Finset.mem_antidiagonal] at hx
    rw [coeff_substPow, coeff_substPow]
    by_cases h1 : k ∣ x.1
    · have h2 : ¬ k ∣ x.2 := fun h2 => hd (hx ▸ dvd_add h1 h2)
      rw [if_neg h2, mul_zero]
    · rw [if_neg h1, zero_mul]

lemma substPow_pow {R : Type*} [CommSemiring R] {k : ℕ} (hk : 0 < k) (f : PowerSeries R) (m : ℕ) :
    substPow k (f ^ m) = (substPow k f) ^ m := by
  induction m with
  | zero => simp [substPow_one hk]
  | succ m ih => rw [pow_succ, pow_succ, substPow_mul hk, ih]

lemma substPow_C_mul_X_pow {R : Type*} [CommSemiring R] {k : ℕ} (hk : 0 < k) (c : R) (m : ℕ) :
    substPow k (PowerSeries.C c * PowerSeries.X ^ m) =
      PowerSeries.C c * PowerSeries.X ^ (k * m) := by
  ext n
  rw [coeff_substPow, PowerSeries.coeff_C_mul_X_pow, PowerSeries.coeff_C_mul_X_pow]
  by_cases h : n = k * m
  · subst h
    rw [if_pos ⟨m, rfl⟩, Nat.mul_div_cancel_left m hk, if_pos rfl, if_pos rfl]
  · rw [if_neg h]
    split_ifs with hd hdiv
    · exfalso; apply h
      rw [← hdiv, Nat.mul_div_cancel' hd]
    · rfl
    · rfl

lemma substPow_C_mul {R : Type*} [CommSemiring R] (k : ℕ) (c : R) (f : PowerSeries R) :
    substPow k (PowerSeries.C c * f) = PowerSeries.C c * substPow k f := by
  ext n
  rw [coeff_substPow, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul, coeff_substPow]
  split_ifs <;> simp

lemma substPow_sub {R : Type*} [CommRing R] (k : ℕ) (f g : PowerSeries R) :
    substPow k (f - g) = substPow k f - substPow k g := by
  ext n
  simp only [coeff_substPow, map_sub]
  split_ifs <;> simp

lemma constantCoeff_substPow {R : Type*} [CommSemiring R] (k : ℕ) (f : PowerSeries R) :
    PowerSeries.constantCoeff (substPow k f) = PowerSeries.constantCoeff f := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff, coeff_substPow, if_pos (dvd_zero k),
    Nat.zero_div, PowerSeries.coeff_zero_eq_constantCoeff]

private lemma coeff_pow_eq_zero_of_lt_const_zero {R : Type*} [CommSemiring R]
    {A : PowerSeries R} (hA : PowerSeries.constantCoeff A = 0) :
    ∀ {j n : ℕ}, n < j → PowerSeries.coeff n (A ^ j) = 0 := by
  intro j
  induction j with
  | zero => intro n hn; omega
  | succ j ih =>
    intro n hn
    rw [pow_succ, PowerSeries.coeff_mul]
    refine Finset.sum_eq_zero fun ab hab => ?_
    rw [Finset.mem_antidiagonal] at hab
    by_cases hb : ab.2 = 0
    · rw [hb, PowerSeries.coeff_zero_eq_constantCoeff, hA, mul_zero]
    · rw [ih (by omega), zero_mul]

lemma substPow_expPS {R : Type*} [Field R] [CharZero R] {k : ℕ} (hk : 0 < k)
    {A : PowerSeries R} (hA : PowerSeries.constantCoeff A = 0) :
    substPow k (expPS A) = expPS (substPow k A) := by
  have hsA : PowerSeries.constantCoeff (substPow k A) = 0 := by
    rw [constantCoeff_substPow, hA]
  ext n
  rw [coeff_substPow, coeff_expPS_eq_sum hsA n]
  by_cases hd : k ∣ n
  · obtain ⟨m, rfl⟩ := hd
    rw [if_pos ⟨m, rfl⟩, Nat.mul_div_cancel_left m hk, coeff_expPS_eq_sum hA m]
    have hsub : Finset.range (m + 1) ⊆ Finset.range (k * m + 1) := by
      intro j hj
      rw [Finset.mem_range] at hj ⊢
      have : m ≤ k * m := Nat.le_mul_of_pos_left m hk
      omega
    rw [← Finset.sum_subset hsub]
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [← substPow_pow hk, coeff_substPow, if_pos ⟨m, rfl⟩, Nat.mul_div_cancel_left m hk]
    · intro j hj hnot
      rw [Finset.mem_range] at hj hnot
      have hgt : m < j := by omega
      rw [← substPow_pow hk, coeff_substPow, if_pos ⟨m, rfl⟩, Nat.mul_div_cancel_left m hk]
      have h0 : PowerSeries.coeff m (A ^ j) = 0 := coeff_pow_eq_zero_of_lt_const_zero hA hgt
      rw [h0, mul_zero]
  · rw [if_neg hd]
    symm
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [← substPow_pow hk, coeff_substPow, if_neg hd, mul_zero]

lemma evalPS_substPow [NormedField K] {k : ℕ} (hk : 0 < k) (x : K) (f : PowerSeries K) :
    evalPS x (substPow k f) = evalPS (x ^ k) f := by
  unfold evalPS
  refine tsum_eq_tsum_of_ne_zero_bij (fun n => k * n.1) ?_ ?_ ?_
  · intro a b hab
    exact Subtype.ext (Nat.eq_of_mul_eq_mul_left hk hab)
  · intro n hn
    rw [Function.mem_support, coeff_substPow] at hn
    have hd : k ∣ n := by
      by_contra hnd
      rw [if_neg hnd, zero_mul] at hn
      exact hn rfl
    obtain ⟨m, rfl⟩ := hd
    refine ⟨⟨m, ?_⟩, rfl⟩
    rw [Function.mem_support]
    rw [if_pos (dvd_mul_right k m), Nat.mul_div_cancel_left m hk, pow_mul] at hn
    exact hn
  · intro a
    rw [coeff_substPow, if_pos ⟨a.1, rfl⟩, Nat.mul_div_cancel_left a.1 hk, pow_mul]

lemma summable_norm_substPow [NormedField K] {k : ℕ} (hk : 0 < k) {x : K} {f : PowerSeries K}
    (hf : Summable fun n => ‖PowerSeries.coeff n f * (x ^ k) ^ n‖) :
    Summable fun n => ‖PowerSeries.coeff n (substPow k f) * x ^ n‖ := by
  have hmul : Summable ((fun n => ‖PowerSeries.coeff n (substPow k f) * x ^ n‖) ∘ (fun n => k * n)) := by
    refine hf.congr fun n => ?_
    simp only [Function.comp_apply, coeff_substPow, dvd_mul_right, ↓reduceIte,
      Nat.mul_div_cancel_left n hk, pow_mul]
  exact (Function.Injective.summable_iff (fun a b h => Nat.eq_of_mul_eq_mul_left hk h) fun n hn => by
    rw [coeff_substPow, if_neg, zero_mul, norm_zero]
    rintro ⟨m, rfl⟩
    exact hn ⟨m, rfl⟩).mp hmul

/-- Helper: Cauchy product summability for norm-summable power series. -/
lemma summable_norm_mul_evalPS [NormedField K] {x : K} {f g : PowerSeries K}
    (hf : Summable fun n => ‖PowerSeries.coeff n f * x ^ n‖)
    (hg : Summable fun n => ‖PowerSeries.coeff n g * x ^ n‖) :
    Summable fun n => ‖PowerSeries.coeff n (f * g) * x ^ n‖ := by
  have hprod : Summable fun p : ℕ × ℕ =>
      ‖PowerSeries.coeff p.1 f * x ^ p.1‖ * ‖PowerSeries.coeff p.2 g * x ^ p.2‖ :=
    Summable.mul_of_nonneg hf hg (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  let e := Equiv.sigmaFiberEquiv (fun p : ℕ × ℕ => p.1 + p.2)
  have hsig : Summable fun q : Σ n : ℕ, {p : ℕ × ℕ // p.1 + p.2 = n} =>
      ‖PowerSeries.coeff q.2.1.1 f * x ^ q.2.1.1‖ * ‖PowerSeries.coeff q.2.1.2 g * x ^ q.2.1.2‖ :=
    (e.summable_iff (f := fun p : ℕ × ℕ =>
      ‖PowerSeries.coeff p.1 f * x ^ p.1‖ * ‖PowerSeries.coeff p.2 g * x ^ p.2‖)).mpr hprod
  have hfib : Summable fun n : ℕ =>
      ∑' p : {p : ℕ × ℕ // p.1 + p.2 = n},
        ‖PowerSeries.coeff p.1.1 f * x ^ p.1.1‖ * ‖PowerSeries.coeff p.1.2 g * x ^ p.1.2‖ :=
    hsig.sigma
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_) hfib
  have htsum_eq : ∑' p : {p : ℕ × ℕ // p.1 + p.2 = n},
      ‖PowerSeries.coeff p.1.1 f * x ^ p.1.1‖ * ‖PowerSeries.coeff p.1.2 g * x ^ p.1.2‖ =
      ∑ p ∈ Finset.antidiagonal n,
        ‖PowerSeries.coeff p.1 f * x ^ p.1‖ * ‖PowerSeries.coeff p.2 g * x ^ p.2‖ := by
    have : Fintype {p : ℕ × ℕ // p.1 + p.2 = n} :=
      Fintype.ofEquiv (Finset.antidiagonal n)
        { toFun := fun p => ⟨p.1, Finset.mem_antidiagonal.mp p.2⟩
          invFun := fun p => ⟨p.1, Finset.mem_antidiagonal.mpr p.2⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
    rw [tsum_fintype]
    refine Finset.sum_bij (fun p _ => p.1)
      (fun p _ => Finset.mem_antidiagonal.mpr p.2)
      (fun _ _ _ _ h => Subtype.ext h)
      (fun p hp => ⟨⟨p, Finset.mem_antidiagonal.mp hp⟩, Finset.mem_univ _, rfl⟩)
      (fun _ _ => rfl)
  rw [htsum_eq, PowerSeries.coeff_mul, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p hp => ?_)
  rw [Finset.mem_antidiagonal] at hp
  have hrew : PowerSeries.coeff p.1 f * PowerSeries.coeff p.2 g * x ^ n =
      (PowerSeries.coeff p.1 f * x ^ p.1) * (PowerSeries.coeff p.2 g * x ^ p.2) := by
    rw [← hp, pow_add]; ring
  rw [hrew, norm_mul]

/-- Cauchy product for power-series evaluation: if `f` and `g` are norm-summable at `x`,
then `evalPS x (f * g) = evalPS x f * evalPS x g`. -/
lemma evalPS_mul [NormedField K] [CompleteSpace K] {x : K} {f g : PowerSeries K}
    (hf : Summable fun n => ‖PowerSeries.coeff n f * x ^ n‖)
    (hg : Summable fun n => ‖PowerSeries.coeff n g * x ^ n‖) :
    evalPS x (f * g) = evalPS x f * evalPS x g := by
  unfold evalPS
  have hprod_norm : Summable fun p : ℕ × ℕ =>
      ‖(PowerSeries.coeff p.1 f * x ^ p.1) * (PowerSeries.coeff p.2 g * x ^ p.2)‖ := by
    simpa [norm_mul] using
      Summable.mul_of_nonneg hf hg (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  have hprod : Summable fun p : ℕ × ℕ =>
      (PowerSeries.coeff p.1 f * x ^ p.1) * (PowerSeries.coeff p.2 g * x ^ p.2) :=
    hprod_norm.of_norm
  let e := Equiv.sigmaFiberEquiv (fun p : ℕ × ℕ => p.1 + p.2)
  have hsig : Summable fun q : Σ n : ℕ, {p : ℕ × ℕ // p.1 + p.2 = n} =>
      (PowerSeries.coeff q.2.1.1 f * x ^ q.2.1.1) * (PowerSeries.coeff q.2.1.2 g * x ^ q.2.1.2) :=
    (e.summable_iff (f := fun p : ℕ × ℕ =>
      (PowerSeries.coeff p.1 f * x ^ p.1) * (PowerSeries.coeff p.2 g * x ^ p.2))).mpr hprod
  have he : (fun c : (y : ℕ) × {p : ℕ × ℕ // p.1 + p.2 = y} =>
      (PowerSeries.coeff (e c).1 f * x ^ (e c).1) * (PowerSeries.coeff (e c).2 g * x ^ (e c).2)) =
      (fun q => (PowerSeries.coeff q.2.1.1 f * x ^ q.2.1.1) *
        (PowerSeries.coeff q.2.1.2 g * x ^ q.2.1.2)) := rfl
  rw [tsum_mul_tsum_of_summable_norm hf hg, ← e.tsum_eq, he,
    hsig.tsum_sigma' (fun n => hsig.sigma_factor n)]
  congr 1
  ext n
  have : Fintype {p : ℕ × ℕ // p.1 + p.2 = n} :=
    Fintype.ofEquiv (Finset.antidiagonal n)
      { toFun := fun p => ⟨p.1, Finset.mem_antidiagonal.mp p.2⟩
        invFun := fun p => ⟨p.1, Finset.mem_antidiagonal.mpr p.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  rw [tsum_fintype, PowerSeries.coeff_mul, Finset.sum_mul]
  symm
  refine Finset.sum_bij (fun p _ => p.1)
    (fun p _ => Finset.mem_antidiagonal.mpr p.2)
    (fun _ _ _ _ h => Subtype.ext h)
    (fun p hp => ⟨⟨p, Finset.mem_antidiagonal.mp hp⟩, Finset.mem_univ _, rfl⟩)
    (fun p _ => ?_)
  have hpow : x ^ n = x ^ p.1.1 * x ^ p.1.2 := by
    rw [← pow_add]
    exact congrArg (x ^ ·) p.2.symm
  dsimp only
  rw [hpow]; ring

lemma evalPS_one [NormedField K] (x : K) : evalPS x (1 : PowerSeries K) = 1 := by
  unfold evalPS
  rw [tsum_eq_single 0]
  · simp
  · intro n hn; simp [PowerSeries.coeff_one, hn]

lemma summable_norm_one_evalPS [NormedField K] (x : K) :
    Summable fun n => ‖PowerSeries.coeff n (1 : PowerSeries K) * x ^ n‖ := by
  refine summable_of_ne_finset_zero (s := {0}) fun n hn => ?_
  have hn0 : n ≠ 0 := by simpa using hn
  simp [PowerSeries.coeff_one, hn0]

lemma summable_norm_pow_evalPS [NormedField K] {x : K} {f : PowerSeries K}
    (hf : Summable fun n => ‖PowerSeries.coeff n f * x ^ n‖) (m : ℕ) :
    Summable fun n => ‖PowerSeries.coeff n (f ^ m) * x ^ n‖ := by
  induction m with
  | zero => simpa using summable_norm_one_evalPS x
  | succ m ih => rw [pow_succ]; exact summable_norm_mul_evalPS ih hf

lemma evalPS_pow [NormedField K] [CompleteSpace K] {x : K} {f : PowerSeries K}
    (hf : Summable fun n => ‖PowerSeries.coeff n f * x ^ n‖) (m : ℕ) :
    evalPS x (f ^ m) = (evalPS x f) ^ m := by
  induction m with
  | zero => simp [evalPS_one]
  | succ m ih =>
    rw [pow_succ, pow_succ, evalPS_mul (summable_norm_pow_evalPS hf m) hf, ih]

lemma summable_norm_prod_evalPS [NormedField K] {ι : Type*} (s : Finset ι) (x : K)
    (f : ι → PowerSeries K) (hf : ∀ i ∈ s, Summable fun n => ‖PowerSeries.coeff n (f i) * x ^ n‖) :
    Summable fun n => ‖PowerSeries.coeff n (∏ i ∈ s, f i) * x ^ n‖ := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using summable_norm_one_evalPS x
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact summable_norm_mul_evalPS (hf a (Finset.mem_insert_self a s))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

lemma evalPS_prod [NormedField K] [CompleteSpace K] {ι : Type*} (s : Finset ι) (x : K)
    (f : ι → PowerSeries K) (hf : ∀ i ∈ s, Summable fun n => ‖PowerSeries.coeff n (f i) * x ^ n‖) :
    evalPS x (∏ i ∈ s, f i) = ∏ i ∈ s, evalPS x (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [evalPS_one]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha,
      evalPS_mul (hf a (Finset.mem_insert_self a s))
        (summable_norm_prod_evalPS s x f fun i hi => hf i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]

/-- Helper: ultrametric bound for an infinite sum `∑' i, u i` in an ultrametric normed field. -/
lemma ultrametric_norm_tsum_le [NormedField K] [IsUltrametricDist K]
    {ι : Type*} {u : ι → K} {B : ℝ} (hB : 0 ≤ B)
    (hu : Summable u) (hb : ∀ i, ‖u i‖ ≤ B) :
    ‖∑' i, u i‖ ≤ B := by
  have hlim : Filter.Tendsto (fun s : Finset ι => ‖∑ i ∈ s, u i‖) Filter.atTop (nhds ‖∑' i, u i‖) :=
    hu.hasSum.norm
  exact le_of_tendsto hlim (Filter.Eventually.of_forall fun s =>
    IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hB fun i _ => hb i)

/-- Coefficient formula for `expPS (C c * X^k)` when `k > 0`. -/
lemma coeff_expPS_C_mul_X_pow [Field K] [CharZero K] (c : K) {k : ℕ} (hk : 0 < k) (n : ℕ) :
    PowerSeries.coeff n (expPS (PowerSeries.C c * PowerSeries.X ^ k)) =
      if k ∣ n then ((n / k).factorial : K)⁻¹ * c ^ (n / k) else 0 := by
  have h0 : PowerSeries.constantCoeff (PowerSeries.C c * PowerSeries.X ^ k) = 0 := by
    rw [map_mul, map_pow, PowerSeries.constantCoeff_X, zero_pow hk.ne', mul_zero]
  rw [coeff_expPS_eq_sum h0 n]
  have hpow : ∀ j : ℕ, (PowerSeries.C c * PowerSeries.X ^ k) ^ j =
      PowerSeries.C (c ^ j) * PowerSeries.X ^ (k * j) := fun j => by
    rw [mul_pow, ← map_pow, ← pow_mul]
  simp_rw [hpow, PowerSeries.coeff_C_mul_X_pow]
  by_cases hd : k ∣ n
  · obtain ⟨m, rfl⟩ := hd
    rw [if_pos ⟨m, rfl⟩, Nat.mul_div_cancel_left m hk]
    have hm : m ∈ Finset.range (k * m + 1) := by
      rw [Finset.mem_range]
      have : m ≤ k * m := Nat.le_mul_of_pos_left m hk
      omega
    rw [Finset.sum_eq_single m]
    · simp
    · intro j _ hjm
      have hne : k * m ≠ k * j := fun h => hjm (Nat.eq_of_mul_eq_mul_left hk h).symm
      rw [if_neg hne, mul_zero]
    · intro h; exact (h hm).elim
  · rw [if_neg hd]
    refine Finset.sum_eq_zero fun j _ => ?_
    have hne : n ≠ k * j := fun h => hd ⟨j, h⟩
    rw [if_neg hne, mul_zero]

lemma summable_norm_expPS_monomial [NormedField K] [IsUltrametricDist K] [CharZero K]
    {p : ℕ} (hp : p.Prime) (hlt : ‖(p : K)‖ < 1) {c x : K} {k : ℕ} (hk : 0 < k)
    (hcx : ‖c * x ^ k‖ < expRadius K p) :
    Summable fun n => ‖PowerSeries.coeff n (expPS (PowerSeries.C c * PowerSeries.X ^ k)) * x ^ n‖ := by
  have hexp : Summable fun m => ‖expTerm (c * x ^ k) m‖ := by
    have hpi0 : 0 < ‖(p : K)‖ := norm_pos_iff.mpr (Nat.cast_ne_zero.mpr hp.ne_zero)
    have hrpos : 0 < expRadius K p := expRadius_pos hp
    have hq0 : 0 ≤ ‖c * x ^ k‖ / expRadius K p := div_nonneg (norm_nonneg _) hrpos.le
    have hq1 : ‖c * x ^ k‖ / expRadius K p < 1 := (div_lt_one hrpos).mpr hcx
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun m => ?_)
      (summable_geometric_of_lt_one hq0 hq1)
    rw [norm_expTerm hp hlt]
    have hbd : (p - 1) * padicValNat p m.factorial ≤ m := by
      have : Fact p.Prime := ⟨hp⟩
      have hleg := sub_one_mul_padicValNat_factorial (p := p) m
      omega
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
    have hpm1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    have hv : (padicValNat p m.factorial : ℝ) ≤ (m : ℝ) / ((p : ℝ) - 1) := by
      have hcast : (((p - 1) * padicValNat p m.factorial : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast hbd
      rw [Nat.cast_mul, Nat.cast_sub hp.one_le, Nat.cast_one] at hcast
      rw [le_div_iff₀ hpm1, mul_comm]
      exact hcast
    rw [div_pow, div_eq_mul_inv, mul_comm]
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg (norm_nonneg (c * x ^ k)) m)
    unfold expRadius
    rw [← Real.rpow_natCast (‖(p : K)‖ ^ _), ← Real.rpow_mul hpi0.le, ← Real.rpow_neg hpi0.le]
    refine Real.rpow_le_rpow_of_exponent_ge hpi0 hlt.le ?_
    have : -(1 / ((p : ℝ) - 1) * (m : ℝ)) = -((m : ℝ) / ((p : ℝ) - 1)) := by ring
    linarith
  have hmul : Summable ((fun n => ‖PowerSeries.coeff n (expPS (PowerSeries.C c * PowerSeries.X ^ k)) * x ^ n‖) ∘
      (fun m => k * m)) := by
    refine hexp.congr fun m => ?_
    simp only [Function.comp_apply, coeff_expPS_C_mul_X_pow c hk, dvd_mul_right, ↓reduceIte,
      Nat.mul_div_cancel_left m hk]
    unfold expTerm
    rw [mul_pow, pow_mul, mul_assoc]
  have hinj : Function.Injective (fun m : ℕ => k * m) := fun a b h => Nat.eq_of_mul_eq_mul_left hk h
  refine (hinj.summable_iff (f := fun n =>
    ‖PowerSeries.coeff n (expPS (PowerSeries.C c * PowerSeries.X ^ k)) * x ^ n‖) fun n hn => ?_).mp hmul
  rw [coeff_expPS_C_mul_X_pow c hk, if_neg, zero_mul, norm_zero]
  rintro ⟨m, rfl⟩
  exact hn ⟨m, rfl⟩

lemma evalPS_expPS_monomial [NormedField K] [IsUltrametricDist K] [CharZero K]
    (c x : K) {k : ℕ} (hk : 0 < k) :
    evalPS x (expPS (PowerSeries.C c * PowerSeries.X ^ k)) = expP (c * x ^ k) := by
  unfold evalPS expP
  refine tsum_eq_tsum_of_ne_zero_bij (fun m => k * m.1) ?_ ?_ ?_
  · intro a b hab
    exact Subtype.ext (Nat.eq_of_mul_eq_mul_left hk hab)
  · intro n hn
    rw [Function.mem_support, coeff_expPS_C_mul_X_pow c hk] at hn
    have hd : k ∣ n := by
      by_contra hnd; rw [if_neg hnd, zero_mul] at hn; exact hn rfl
    obtain ⟨m, rfl⟩ := hd
    refine ⟨⟨m, ?_⟩, rfl⟩
    rw [Function.mem_support]
    rw [if_pos ⟨m, rfl⟩, Nat.mul_div_cancel_left m hk, pow_mul] at hn
    unfold expTerm
    rw [mul_pow, ← mul_assoc]
    exact hn
  · intro a
    rw [coeff_expPS_C_mul_X_pow c hk, if_pos ⟨a.1, rfl⟩, Nat.mul_div_cancel_left a.1 hk]
    unfold expTerm
    rw [mul_pow, pow_mul, mul_assoc]

/-! ### Dwork Splitting Evaluation & Additive Character on `𝔽_{p^s} ⊆ kb p` -/

section ConcreteDworkChar

variable (p : ℕ) [hp : Fact p.Prime]

/-- Evaluation of Dwork's splitting function `θ(T) = exp(ϖ (T - T^p))` in `DworkField p`. -/
def evalTheta (x : DworkField p) : DworkField p :=
  letI := dworkNormedField p
  haveI := dworkField_ultra p
  haveI := dworkField_charZero p
  evalPS x (dworkSplitting (dworkPi p) p)

lemma evalTheta_summable_norm {x : DworkField p}
    (hx : (letI := dworkNormedField p; ‖x‖ ≤ 1)) :
    letI := dworkNormedField p
    haveI := dworkField_ultra p
    haveI := dworkField_charZero p
    Summable fun n => ‖PowerSeries.coeff n (dworkSplitting (dworkPi p) p) * x ^ n‖ := by
  let _ : NormedField (DworkField p) := dworkNormedField p
  have _ : IsUltrametricDist (DworkField p) := dworkField_ultra p
  have _ : CharZero (DworkField p) := dworkField_charZero p
  have hlt : ‖(p : DworkField p)‖ < 1 := dworkField_norm_p_lt_one p
  have hxlt : ‖x‖ < dworkOverconvRadius (DworkField p) p :=
    lt_of_le_of_lt hx (one_lt_dworkOverconvRadius hp.out hlt)
  exact wtGe_implies_summable_norm hp.out (dworkSplitting_wtGe hp.out hlt (dworkPi_pow p)) hxlt

lemma evalTheta_summable_norm_pow {x : DworkField p}
    (hx : (letI := dworkNormedField p; ‖x‖ ≤ 1)) (k : ℕ) :
    letI := dworkNormedField p
    haveI := dworkField_ultra p
    haveI := dworkField_charZero p
    Summable fun n => ‖PowerSeries.coeff n (dworkSplitting (dworkPi p) p) * (x ^ k) ^ n‖ := by
  let _ : NormedField (DworkField p) := dworkNormedField p
  have _ : IsUltrametricDist (DworkField p) := dworkField_ultra p
  have _ : CharZero (DworkField p) := dworkField_charZero p
  exact evalTheta_summable_norm p (by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg x) hx)

/-- Formal telescoping product: `∏_{j < s} θ(X^{p^j}) = exp(ϖ (X - X^{p^s}))`. -/
lemma prod_substPow_dworkSplitting (s : ℕ) :
    letI := dworkNormedField p
    haveI := dworkField_ultra p
    haveI := dworkField_charZero p
    ∏ j ∈ Finset.range s, substPow (p ^ j) (dworkSplitting (dworkPi p) p) =
      expPS (PowerSeries.C (dworkPi p) * (PowerSeries.X - PowerSeries.X ^ (p ^ s))) := by
  let _ : NormedField (DworkField p) := dworkNormedField p
  have _ : IsUltrametricDist (DworkField p) := dworkField_ultra p
  have _ : CharZero (DworkField p) := dworkField_charZero p
  have hterm : ∀ j : ℕ, substPow (p ^ j) (dworkSplitting (dworkPi p) p) =
      expPS (PowerSeries.C (dworkPi p) * (PowerSeries.X ^ (p ^ j) - PowerSeries.X ^ (p ^ (j + 1)))) := by
    intro j
    have hpos : 0 < p ^ j := pow_pos hp.out.pos j
    have hA0 : PowerSeries.constantCoeff
        (PowerSeries.C (dworkPi p) * (PowerSeries.X - PowerSeries.X ^ p)) = 0 := by
      simp [zero_pow hp.out.ne_zero]
    unfold dworkSplitting
    rw [substPow_expPS hpos hA0, substPow_C_mul (p ^ j), substPow_sub]
    have h1 : substPow (p ^ j) (PowerSeries.X : PowerSeries (DworkField p)) =
        PowerSeries.X ^ (p ^ j) := by
      have := substPow_C_mul_X_pow (R := DworkField p) hpos 1 1
      simpa using this
    have h2 : substPow (p ^ j) ((PowerSeries.X : PowerSeries (DworkField p)) ^ p) =
        PowerSeries.X ^ (p ^ (j + 1)) := by
      have := substPow_C_mul_X_pow (R := DworkField p) hpos 1 p
      simpa [pow_succ] using this
    rw [h1, h2]
  simp_rw [hterm]
  induction s with
  | zero =>
    simp [expPS_zero]
  | succ s ih =>
    rw [Finset.prod_range_succ, ih]
    have h0a : PowerSeries.constantCoeff
        (PowerSeries.C (dworkPi p) * (PowerSeries.X - PowerSeries.X ^ (p ^ s))) = 0 := by
      simp [zero_pow (pow_ne_zero s hp.out.ne_zero)]
    have h0b : PowerSeries.constantCoeff
        (PowerSeries.C (dworkPi p) * (PowerSeries.X ^ (p ^ s) - PowerSeries.X ^ (p ^ (s + 1)))) = 0 := by
      simp [zero_pow (pow_ne_zero s hp.out.ne_zero), zero_pow (pow_ne_zero (s + 1) hp.out.ne_zero)]
    rw [← expPS_add h0a h0b]
    congr 1
    ring

/-- **Dwork's Additive Character** `dworkChar p s a := ∏_{j < s} θ(teich(a)^{p^j})`. -/
def dworkChar (s : ℕ) (a : kb p) : DworkField p :=
  ∏ j ∈ Finset.range s, evalTheta p ((teich p a) ^ (p ^ j))

/-- For any `a ∈ 𝔽_{p^s}` (`a^{p^s} = a`), `(dworkChar p s a) ^ p = 1`! -/
theorem dworkChar_pow_p {s : ℕ} (_hs : 1 ≤ s) {a : kb p} (ha : a ^ (p ^ s) = a) :
    (dworkChar p s a) ^ p = 1 := by
  let _ : NormedField (DworkField p) := dworkNormedField p
  have _ : IsUltrametricDist (DworkField p) := dworkField_ultra p
  have _ : CharZero (DworkField p) := dworkField_charZero p
  have _ : CompleteSpace (DworkField p) := dworkField_complete p
  have hlt : ‖(p : DworkField p)‖ < 1 := dworkField_norm_p_lt_one p
  set t : DworkField p := teich p a
  have ht_le : ‖t‖ ≤ 1 := teich_norm_le_one p a
  have ht_pow : t ^ (p ^ s) = t := by
    change (teich p a) ^ (p ^ s) = teich p a
    rw [← map_pow, ha]
  have hsumm : ∀ j ∈ Finset.range s,
      Summable fun n =>
        ‖PowerSeries.coeff n (substPow (p ^ j) (dworkSplitting (dworkPi p) p)) * t ^ n‖ := by
    intro j _
    exact summable_norm_substPow (pow_pos hp.out.pos j) (evalTheta_summable_norm_pow p ht_le (p ^ j))
  have hchar_eq : dworkChar p s a =
      evalPS t (∏ j ∈ Finset.range s, substPow (p ^ j) (dworkSplitting (dworkPi p) p)) := by
    rw [evalPS_prod (Finset.range s) t _ hsumm]
    unfold dworkChar
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [evalPS_substPow (pow_pos hp.out.pos j)]
    rfl
  rw [hchar_eq, ← evalPS_pow (summable_norm_prod_evalPS _ _ _ hsumm) p,
    prod_substPow_dworkSplitting p s]
  have hA0 : PowerSeries.constantCoeff
      (PowerSeries.C (dworkPi p) * (PowerSeries.X - PowerSeries.X ^ (p ^ s))) = 0 := by
    simp [zero_pow (pow_ne_zero s hp.out.ne_zero)]
  have hpow_exp : (expPS (PowerSeries.C (dworkPi p) * (PowerSeries.X - PowerSeries.X ^ (p ^ s)))) ^ p =
      expPS (PowerSeries.C ((p : DworkField p) * dworkPi p) * PowerSeries.X ^ 1) *
      expPS (PowerSeries.C (-((p : DworkField p) * dworkPi p)) * PowerSeries.X ^ (p ^ s)) := by
    rw [← expPS_nsmul hA0 p]
    have h1 : PowerSeries.constantCoeff
        (PowerSeries.C ((p : DworkField p) * dworkPi p) * PowerSeries.X ^ 1) = 0 := by simp
    have h2 : PowerSeries.constantCoeff
        (PowerSeries.C (-((p : DworkField p) * dworkPi p)) * PowerSeries.X ^ (p ^ s)) = 0 := by
      simp [zero_pow (pow_ne_zero s hp.out.ne_zero)]
    rw [← expPS_add h1 h2]
    congr 1
    rw [Algebra.smul_def, map_neg, map_mul, map_natCast]
    change (p : PowerSeries (DworkField p)) *
        (PowerSeries.C (dworkPi p) * (PowerSeries.X - PowerSeries.X ^ p ^ s)) = _
    rw [← map_natCast PowerSeries.C p]
    ring
  rw [hpow_exp]
  have hnorm_p_pi : ‖(p : DworkField p) * dworkPi p‖ < expRadius (DworkField p) p := by
    rw [norm_mul, norm_dworkPi hp.out (dworkPi_pow p)]
    exact mul_lt_of_lt_one_left (expRadius_pos hp.out) hlt
  have hrad1 : ‖((p : DworkField p) * dworkPi p) * t ^ 1‖ < expRadius (DworkField p) p := by
    rw [norm_mul, pow_one]
    exact lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) ht_le) hnorm_p_pi
  have hrad2 : ‖(-((p : DworkField p) * dworkPi p)) * t ^ (p ^ s)‖ < expRadius (DworkField p) p := by
    rw [norm_mul, norm_neg, ht_pow]
    exact lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) ht_le) hnorm_p_pi
  rw [evalPS_mul (summable_norm_expPS_monomial hp.out hlt one_pos hrad1)
      (summable_norm_expPS_monomial hp.out hlt (pow_pos hp.out.pos s) hrad2),
    evalPS_expPS_monomial _ _ one_pos,
    evalPS_expPS_monomial _ _ (pow_pos hp.out.pos s),
    ← expP_add hp.out hlt hrad1 hrad2, pow_one, ht_pow]
  have hzero : (p : DworkField p) * dworkPi p * t + -((p : DworkField p) * dworkPi p) * t = 0 := by ring
  rw [hzero, expP_zero]

lemma evalTheta_one_pow_p : (evalTheta p 1) ^ p = 1 := by
  have h := dworkChar_pow_p p (s := 1) le_rfl (a := (1 : kb p)) (by simp)
  simpa [dworkChar] using h

/-- Arithmetic inequality: `m * (p - 1) + 2 ≤ p ^ m` for all `p ≥ 2` and `m ≥ 2`. -/
lemma tail_exp_ineq_two {p : ℕ} (hp2 : 2 ≤ p) {m : ℕ} (hm : 2 ≤ m) :
    m * (p - 1) + 2 ≤ p ^ m := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  induction k with
  | zero =>
    simp only [add_zero, pow_two]
    have h1 : 2 * (p - 1) + 2 = 2 * p := by omega
    rw [h1]
    exact Nat.mul_le_mul_right p hp2
  | succ k ih =>
    have hih := ih (by omega)
    rw [show 2 + (k + 1) = (2 + k) + 1 by omega, pow_succ]
    have hstep : (2 + k + 1) * (p - 1) + 2 = ((2 + k) * (p - 1) + 2) + (p - 1) := by ring
    rw [hstep]
    have h2 : p ^ (2 + k) * 2 ≤ p ^ (2 + k) * p := Nat.mul_le_mul_left _ hp2
    have h3 : p - 1 ≤ p ^ (2 + k) := by
      have : p ^ 1 ≤ p ^ (2 + k) := Nat.pow_le_pow_right (by omega) (by omega)
      rw [pow_one] at this; omega
    omega

/-- Uniform `‖ϖ‖^2` bound on EVERY positive coefficient of `exp(B_p(X))`, valid for ALL primes `p ≥ 2`! -/
lemma norm_coeff_expPS_dworkTailArg_le (n : ℕ) (hn : 1 ≤ n) :
    letI := dworkNormedField p
    haveI := dworkField_ultra p
    haveI := dworkField_charZero p
    ‖PowerSeries.coeff n (expPS (dworkTailArg (dworkPi p) p))‖ ≤ ‖dworkPi p‖ ^ 2 := by
  let _ : NormedField (DworkField p) := dworkNormedField p
  have _ : IsUltrametricDist (DworkField p) := dworkField_ultra p
  have _ : CharZero (DworkField p) := dworkField_charZero p
  have hlt : ‖(p : DworkField p)‖ < 1 := dworkField_norm_p_lt_one p
  have hpi0 : 0 < ‖(p : DworkField p)‖ := norm_pos_iff.mpr (Nat.cast_ne_zero.mpr hp.out.ne_zero)
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.out.two_le
  have hpm1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hnorm_pi_sq : ‖dworkPi p‖ ^ 2 = ‖(p : DworkField p)‖ ^ ((2 : ℝ) / ((p : ℝ) - 1)) := by
    rw [norm_dworkPi hp.out (dworkPi_pow p), expRadius, ← Real.rpow_natCast,
      ← Real.rpow_mul hpi0.le]
    congr 1; push_cast; ring
  have hB_coeff : ∀ k : ℕ, ‖PowerSeries.coeff k (dworkTailArg (dworkPi p) p)‖ ≤ ‖dworkPi p‖ ^ 2 := by
    intro k
    classical
    simp only [dworkTailArg, PowerSeries.coeff_mk]
    split_ifs with hex
    · obtain ⟨m, hm2, rfl⟩ := hex
      conv_rhs => rw [hnorm_pi_sq]
      rw [norm_neg, norm_mul, norm_inv, norm_pow, norm_dworkPi hp.out (dworkPi_pow p),
        norm_natCast_eq_pow_padicValNat hp.out hlt (pow_ne_zero m hp.out.ne_zero)]
      have hval : padicValNat p (p ^ m) = m := padicValNat.prime_pow m
      rw [hval]
      unfold expRadius
      rw [← Real.rpow_natCast ‖(p : DworkField p)‖ m, ← Real.rpow_neg hpi0.le,
        ← Real.rpow_natCast (‖(p : DworkField p)‖ ^ _) (p ^ m), ← Real.rpow_mul hpi0.le,
        ← Real.rpow_add hpi0]
      refine Real.rpow_le_rpow_of_exponent_ge hpi0 hlt.le ?_
      have hineq : ((m * (p - 1) + 2 : ℕ) : ℝ) ≤ ((p ^ m : ℕ) : ℝ) := by
        exact_mod_cast tail_exp_ineq_two hp.out.two_le hm2
      push_cast [Nat.cast_sub hp.out.one_le] at hineq
      rw [div_le_iff₀ hpm1]
      have hmul : (-(m : ℝ) + 1 / ((p : ℝ) - 1) * (p : ℝ) ^ m) * ((p : ℝ) - 1) =
          (p : ℝ) ^ m - (m : ℝ) * ((p : ℝ) - 1) := by field_simp [hpm1.ne']; ring
      rw [Nat.cast_pow]
      linarith
    · rw [norm_zero]; exact sq_nonneg _
  have hB_pow : ∀ j k : ℕ, ‖PowerSeries.coeff k ((dworkTailArg (dworkPi p) p) ^ j)‖ ≤
      (‖dworkPi p‖ ^ 2) ^ j := by
    intro j
    induction j with
    | zero =>
      intro k
      rw [pow_zero, pow_zero, PowerSeries.coeff_one]
      split_ifs <;> simp
    | succ j ih =>
      intro k
      rw [pow_succ, pow_succ, PowerSeries.coeff_mul]
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun ab _ => ?_
      rw [norm_mul]
      exact mul_le_mul (ih ab.1) (hB_coeff ab.2) (norm_nonneg _) (by positivity)
  have hB0 := constantCoeff_dworkTailArg hp.out (dworkPi p)
  rw [coeff_expPS_eq_sum hB0 n]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (sq_nonneg _) fun j _ => ?_
  rcases j with _ | j
  · rw [pow_zero, PowerSeries.coeff_one, if_neg (by omega : n ≠ 0), mul_zero, norm_zero]
    exact sq_nonneg _
  · set m := j + 1
    have hm1 : 1 ≤ m := Nat.succ_pos j
    rw [norm_mul, norm_inv,
      norm_natCast_eq_pow_padicValNat hp.out hlt (Nat.factorial_ne_zero m)]
    calc (‖(p : DworkField p)‖ ^ padicValNat p m.factorial)⁻¹ *
          ‖PowerSeries.coeff n ((dworkTailArg (dworkPi p) p) ^ m)‖
        ≤ (‖(p : DworkField p)‖ ^ padicValNat p m.factorial)⁻¹ * (‖dworkPi p‖ ^ 2) ^ m :=
          mul_le_mul_of_nonneg_left (hB_pow m n) (by positivity)
      _ = ‖(p : DworkField p)‖ ^ (-(padicValNat p m.factorial : ℝ) +
            (2 : ℝ) / ((p : ℝ) - 1) * (m : ℝ)) := by
          rw [hnorm_pi_sq, ← Real.rpow_natCast ‖(p : DworkField p)‖, ← Real.rpow_neg hpi0.le,
            ← Real.rpow_natCast (‖(p : DworkField p)‖ ^ _), ← Real.rpow_mul hpi0.le,
            ← Real.rpow_add hpi0]
      _ ≤ ‖(p : DworkField p)‖ ^ ((2 : ℝ) / ((p : ℝ) - 1)) := by
          refine Real.rpow_le_rpow_of_exponent_ge hpi0 hlt.le ?_
          -- `(p - 1) * v_p(m!) ≤ m - 1` (since `digits` sum `≥ 1` for `m ≥ 1`)
          have hdig : 1 ≤ (p.digits m).sum := by
            have hne : p.digits m ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr (by omega)
            have hlast : (p.digits m).getLast hne ≠ 0 := Nat.getLast_digit_ne_zero p (by omega)
            have hmem : (p.digits m).getLast hne ∈ p.digits m := List.getLast_mem hne
            have hle : (p.digits m).getLast hne ≤ (p.digits m).sum := List.le_sum_of_mem hmem
            omega
          have hleg := sub_one_mul_padicValNat_factorial (p := p) m
          have hv_nat : (p - 1) * padicValNat p m.factorial + 1 ≤ m := by omega
          have hv_real : ((p : ℝ) - 1) * (padicValNat p m.factorial : ℝ) + 1 ≤ (m : ℝ) := by
            have hcast : (((p - 1) * padicValNat p m.factorial + 1 : ℕ) : ℝ) ≤ (m : ℝ) := by
              exact_mod_cast hv_nat
            push_cast [Nat.cast_sub hp.out.one_le] at hcast
            exact hcast
          have hm_real : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
          rw [div_le_iff₀ hpm1]
          have hmul : (-(padicValNat p m.factorial : ℝ) + 2 / ((p : ℝ) - 1) * (m : ℝ)) * ((p : ℝ) - 1) =
              2 * (m : ℝ) - ((p : ℝ) - 1) * (padicValNat p m.factorial : ℝ) := by
            field_simp [hpm1.ne']; ring
          linarith
      _ = ‖dworkPi p‖ ^ 2 := hnorm_pi_sq.symm

/-- **First-order `ϖ`-expansion of `evalTheta p x`**: for every `x ∈ DworkField p` with `‖x‖ ≤ 1`,
`‖evalTheta p x - (1 + ϖ * x)‖ ≤ ‖ϖ‖ ^ 2` (valid for ALL primes `p ≥ 2`!). -/
theorem norm_evalTheta_sub_one_add_pi_le {x : DworkField p}
    (hx : (letI := dworkNormedField p; ‖x‖ ≤ 1)) :
    letI := dworkNormedField p
    ‖evalTheta p x - (1 + dworkPi p * x)‖ ≤ ‖dworkPi p‖ ^ 2 := by
  let _ : NormedField (DworkField p) := dworkNormedField p
  have _ : IsUltrametricDist (DworkField p) := dworkField_ultra p
  have _ : CharZero (DworkField p) := dworkField_charZero p
  have _ : CompleteSpace (DworkField p) := dworkField_complete p
  have hlt : ‖(p : DworkField p)‖ < 1 := dworkField_norm_p_lt_one p
  have hpi_lt_one : ‖dworkPi p‖ < 1 := by
    rw [norm_dworkPi hp.out (dworkPi_pow p)]
    exact expRadius_lt_one hp.out hlt
  have hAH_summ : Summable fun n =>
      ‖PowerSeries.coeff n (scalePS (dworkPi p) (artinHasseExp (DworkField p) p)) * x ^ n‖ :=
    wtGe_implies_summable_norm hp.out (scalePS_artinHasseExp_wtGe hp.out hlt (dworkPi_pow p))
      (lt_of_le_of_lt hx (one_lt_dworkOverconvRadius hp.out hlt))
  have hB_exp_wt : WtGe ‖(p : DworkField p)‖
      (fun _ : Unit => -(((p : ℝ) - 1) / (p : ℝ) ^ 2)) 0
      (expPS (dworkTailArg (dworkPi p) p) : MvPowerSeries Unit (DworkField p)) := fun κ =>
    dwork_exp_weight_le hp.out hlt (constantCoeff_dworkTailArg hp.out (dworkPi p))
      (fun m _ => dworkTailArg_wtGe hp.out hlt (dworkPi_pow p) m) κ le_rfl
  have hB_summ : Summable fun n =>
      ‖PowerSeries.coeff n (expPS (dworkTailArg (dworkPi p) p)) * x ^ n‖ :=
    wtGe_implies_summable_norm hp.out hB_exp_wt
      (lt_of_le_of_lt hx (one_lt_dworkOverconvRadius hp.out hlt))
  -- Factor `evalTheta p x = A * B`
  set A := evalPS x (scalePS (dworkPi p) (artinHasseExp (DworkField p) p))
  set B := evalPS x (expPS (dworkTailArg (dworkPi p) p))
  have hfac : evalTheta p x = A * B := by
    unfold evalTheta A B
    rw [dworkSplitting_eq_artinHasse_mul_tail hp.out (dworkPi_pow p),
      evalPS_mul hAH_summ hB_summ]
  -- Bound 1: `‖A - (1 + ϖ x)‖ ≤ ‖ϖ‖^2`
  have hA_coeff0 : PowerSeries.coeff 0 (scalePS (dworkPi p) (artinHasseExp (DworkField p) p)) = 1 := by
    rw [coeff_scalePS, pow_zero, mul_one, PowerSeries.coeff_zero_eq_constantCoeff]
    exact constantCoeff_expPS (constantCoeff_artinHasseArg hp.out)
  have hA_coeff1 : PowerSeries.coeff 1 (scalePS (dworkPi p) (artinHasseExp (DworkField p) p)) = dworkPi p := by
    rw [coeff_scalePS, pow_one]
    have hc1 : PowerSeries.coeff 1 (artinHasseExp (DworkField p) p) = 1 := by
      unfold artinHasseExp
      rw [coeff_expPS_eq_sum (constantCoeff_artinHasseArg hp.out) 1]
      rw [Finset.sum_range_succ, Finset.sum_range_one]
      simp only [pow_zero, PowerSeries.coeff_one, one_ne_zero, ↓reduceIte, mul_zero, zero_add,
        Nat.factorial_one, Nat.cast_one, inv_one, pow_one, one_mul, artinHasseArg, PowerSeries.coeff_mk]
      rw [if_pos ⟨0, (pow_zero p).symm⟩]
    rw [hc1, one_mul]
  have hA_sub : ‖A - (1 + dworkPi p * x)‖ ≤ ‖dworkPi p‖ ^ 2 := by
    have htsum_split : A = (1 + dworkPi p * x) +
        ∑' n : ℕ, if 2 ≤ n then
          PowerSeries.coeff n (scalePS (dworkPi p) (artinHasseExp (DworkField p) p)) * x ^ n else 0 := by
      unfold A evalPS
      have h01 : ∑' n : ℕ, PowerSeries.coeff n (scalePS (dworkPi p) (artinHasseExp (DworkField p) p)) * x ^ n =
          (PowerSeries.coeff 0 (scalePS (dworkPi p) (artinHasseExp (DworkField p) p)) * x ^ 0 +
           PowerSeries.coeff 1 (scalePS (dworkPi p) (artinHasseExp (DworkField p) p)) * x ^ 1) +
          ∑' n : ℕ, if 2 ≤ n then
            PowerSeries.coeff n (scalePS (dworkPi p) (artinHasseExp (DworkField p) p)) * x ^ n else 0 := by
        have htail : Summable fun n : ℕ => if 2 ≤ n then
            PowerSeries.coeff n (scalePS (dworkPi p) (artinHasseExp (DworkField p) p)) * x ^ n else 0 :=
          (hAH_summ.of_norm).indicator {n : ℕ | 2 ≤ n} |>.congr fun n => by
            simp [Set.indicator]
        have hhead : Summable fun n : ℕ => if n < 2 then
            PowerSeries.coeff n (scalePS (dworkPi p) (artinHasseExp (DworkField p) p)) * x ^ n else 0 :=
          summable_of_ne_finset_zero (s := Finset.range 2) fun n hn => by
            rw [Finset.mem_range, not_lt] at hn; exact if_neg (not_lt.mpr hn)
        have hadd := hhead.tsum_add htail
        have hsum_eq : (fun n : ℕ =>
            (if n < 2 then PowerSeries.coeff n (scalePS (dworkPi p) (artinHasseExp (DworkField p) p)) * x ^ n else 0) +
            (if 2 ≤ n then PowerSeries.coeff n (scalePS (dworkPi p) (artinHasseExp (DworkField p) p)) * x ^ n else 0)) =
            fun n => PowerSeries.coeff n (scalePS (dworkPi p) (artinHasseExp (DworkField p) p)) * x ^ n := by
          ext n; by_cases hn : n < 2
          · rw [if_pos hn, if_neg (by omega), add_zero]
          · rw [if_neg hn, if_pos (by omega), zero_add]
        rw [hsum_eq] at hadd
        rw [hadd]
        congr 1
        rw [tsum_eq_sum (s := Finset.range 2) (fun n hn => by
          rw [Finset.mem_range, not_lt] at hn; exact if_neg (not_lt.mpr hn))]
        rw [Finset.sum_range_succ, Finset.sum_range_one]
        simp
      rw [h01, hA_coeff0, hA_coeff1, pow_zero, mul_one, pow_one]
    rw [htsum_split, add_sub_cancel_left]
    have htail : Summable fun n : ℕ => if 2 ≤ n then
        PowerSeries.coeff n (scalePS (dworkPi p) (artinHasseExp (DworkField p) p)) * x ^ n else 0 :=
      (hAH_summ.of_norm).indicator {n : ℕ | 2 ≤ n} |>.congr fun n => by simp [Set.indicator]
    refine ultrametric_norm_tsum_le (sq_nonneg _) htail fun n => ?_
    split_ifs with hn
    · rw [coeff_scalePS, norm_mul, norm_mul, norm_pow, norm_pow]
      calc ‖PowerSeries.coeff n (artinHasseExp (DworkField p) p)‖ * ‖dworkPi p‖ ^ n * ‖x‖ ^ n
          ≤ 1 * ‖dworkPi p‖ ^ n * 1 := by
            refine mul_le_mul (mul_le_mul (artinHasseExp_isIntegral hp.out hlt n) le_rfl
              (pow_nonneg (norm_nonneg _) _) zero_le_one)
              (pow_le_one₀ (norm_nonneg x) hx) (pow_nonneg (norm_nonneg x) _) (by positivity)
        _ = ‖dworkPi p‖ ^ n := by ring
        _ ≤ ‖dworkPi p‖ ^ 2 := pow_le_pow_of_le_one (norm_nonneg _) hpi_lt_one.le hn
    · rw [norm_zero]; exact sq_nonneg _
  -- Bound 2: `‖B - 1‖ ≤ ‖ϖ‖^2`
  have hB_coeff0 : PowerSeries.coeff 0 (expPS (dworkTailArg (dworkPi p) p)) = 1 := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff]
    exact constantCoeff_expPS (constantCoeff_dworkTailArg hp.out (dworkPi p))
  have hB_sub : ‖B - 1‖ ≤ ‖dworkPi p‖ ^ 2 := by
    have htsum_split : B = 1 +
        ∑' n : ℕ, if 1 ≤ n then
          PowerSeries.coeff n (expPS (dworkTailArg (dworkPi p) p)) * x ^ n else 0 := by
      unfold B evalPS
      have htail : Summable fun n : ℕ => if 1 ≤ n then
          PowerSeries.coeff n (expPS (dworkTailArg (dworkPi p) p)) * x ^ n else 0 :=
        (hB_summ.of_norm).indicator {n : ℕ | 1 ≤ n} |>.congr fun n => by simp [Set.indicator]
      have hhead : Summable fun n : ℕ => if n = 0 then
          PowerSeries.coeff n (expPS (dworkTailArg (dworkPi p) p)) * x ^ n else 0 :=
        summable_of_ne_finset_zero (s := {0}) fun n hn => by
          have : n ≠ 0 := by simpa using hn
          exact if_neg this
      have hadd := hhead.tsum_add htail
      have hsum_eq : (fun n : ℕ =>
          (if n = 0 then PowerSeries.coeff n (expPS (dworkTailArg (dworkPi p) p)) * x ^ n else 0) +
          (if 1 ≤ n then PowerSeries.coeff n (expPS (dworkTailArg (dworkPi p) p)) * x ^ n else 0)) =
          fun n => PowerSeries.coeff n (expPS (dworkTailArg (dworkPi p) p)) * x ^ n := by
        ext n; rcases n with _ | n
        · simp
        · simp
      rw [hsum_eq] at hadd
      rw [hadd]
      congr 1
      rw [tsum_eq_single 0]
      · simp [hB_coeff0]
      · intro n hn; exact if_neg hn
    rw [htsum_split, add_sub_cancel_left]
    have htail : Summable fun n : ℕ => if 1 ≤ n then
        PowerSeries.coeff n (expPS (dworkTailArg (dworkPi p) p)) * x ^ n else 0 :=
      (hB_summ.of_norm).indicator {n : ℕ | 1 ≤ n} |>.congr fun n => by simp [Set.indicator]
    refine ultrametric_norm_tsum_le (sq_nonneg _) htail fun n => ?_
    split_ifs with hn
    · rw [norm_mul, norm_pow]
      calc ‖PowerSeries.coeff n (expPS (dworkTailArg (dworkPi p) p))‖ * ‖x‖ ^ n
          ≤ ‖dworkPi p‖ ^ 2 * 1 :=
            mul_le_mul (norm_coeff_expPS_dworkTailArg_le p n hn)
              (pow_le_one₀ (norm_nonneg x) hx) (pow_nonneg (norm_nonneg x) _) (sq_nonneg _)
        _ = ‖dworkPi p‖ ^ 2 := mul_one _
    · rw [norm_zero]; exact sq_nonneg _
  -- Combine `A * B - (1 + ϖ x) = (A - (1 + ϖ x)) * B + (1 + ϖ x) * (B - 1)`
  have hB_le : ‖B‖ ≤ 1 := by
    have : B = 1 + (B - 1) := by ring
    rw [this]
    refine le_trans (IsUltrametricDist.norm_add_le_max _ _) (max_le (by simp) ?_)
    exact le_trans hB_sub (by nlinarith [norm_nonneg (dworkPi p)])
  have h1px_le : ‖(1 : DworkField p) + dworkPi p * x‖ ≤ 1 := by
    refine le_trans (IsUltrametricDist.norm_add_le_max _ _) (max_le (by simp) ?_)
    rw [norm_mul]
    exact le_trans (mul_le_of_le_one_right (norm_nonneg _) hx) hpi_lt_one.le
  rw [hfac, show A * B - (1 + dworkPi p * x) =
      (A - (1 + dworkPi p * x)) * B + (1 + dworkPi p * x) * (B - 1) by ring]
  refine le_trans (IsUltrametricDist.norm_add_le_max _ _) (max_le ?_ ?_)
  · rw [norm_mul]
    exact le_trans (mul_le_of_le_one_right (norm_nonneg _) hB_le) hA_sub
  · rw [norm_mul]
    exact le_trans (mul_le_of_le_one_left (norm_nonneg _) h1px_le) hB_sub

/-- Product of `1 + ϖ x_i + O(ϖ^2)` factors equals `1 + ϖ (∑ x_i) + O(ϖ^2)`. -/
lemma norm_prod_sub_one_add_pi_sum_le {ι : Type*} (s : Finset ι)
    (f g : ι → DworkField p)
    (hf : ∀ i ∈ s, (letI := dworkNormedField p; ‖f i‖ ≤ 1))
    (hg : ∀ i ∈ s, (letI := dworkNormedField p; ‖g i - (1 + dworkPi p * f i)‖ ≤ ‖dworkPi p‖ ^ 2)) :
    letI := dworkNormedField p
    ‖(∏ i ∈ s, g i) - (1 + dworkPi p * ∑ i ∈ s, f i)‖ ≤ ‖dworkPi p‖ ^ 2 := by
  let _ : NormedField (DworkField p) := dworkNormedField p
  have _ : IsUltrametricDist (DworkField p) := dworkField_ultra p
  have _ : CharZero (DworkField p) := dworkField_charZero p
  have hpi_le : ‖dworkPi p‖ ≤ 1 := by
    rw [norm_dworkPi hp.out (dworkPi_pow p)]
    exact (expRadius_lt_one hp.out (dworkField_norm_p_lt_one p)).le
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    have hfa : ‖f a‖ ≤ 1 := hf a (Finset.mem_insert_self a s)
    have hga : ‖g a - (1 + dworkPi p * f a)‖ ≤ ‖dworkPi p‖ ^ 2 := hg a (Finset.mem_insert_self a s)
    have hih := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
      (fun i hi => hg i (Finset.mem_insert_of_mem hi))
    have hsum_le : ‖∑ i ∈ s, f i‖ ≤ 1 :=
      IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i hi =>
        hf i (Finset.mem_insert_of_mem hi)
    have hga_le : ‖g a‖ ≤ 1 := by
      have : g a = (1 + dworkPi p * f a) + (g a - (1 + dworkPi p * f a)) := by ring
      rw [this]
      refine le_trans (IsUltrametricDist.norm_add_le_max _ _) (max_le ?_ ?_)
      · refine le_trans (IsUltrametricDist.norm_add_le_max _ _) (max_le (by simp) ?_)
        rw [norm_mul]; exact le_trans (mul_le_of_le_one_right (norm_nonneg _) hfa) hpi_le
      · exact le_trans hga (by nlinarith [norm_nonneg (dworkPi p)])
    have h1s_le : ‖(1 : DworkField p) + dworkPi p * ∑ i ∈ s, f i‖ ≤ 1 := by
      refine le_trans (IsUltrametricDist.norm_add_le_max _ _) (max_le (by simp) ?_)
      rw [norm_mul]; exact le_trans (mul_le_of_le_one_right (norm_nonneg _) hsum_le) hpi_le
    set P := ∏ i ∈ s, g i
    set S := ∑ i ∈ s, f i
    have hdecomp : g a * P - (1 + dworkPi p * (f a + S)) =
        g a * (P - (1 + dworkPi p * S)) +
        ((g a - (1 + dworkPi p * f a)) * (1 + dworkPi p * S) +
         (dworkPi p * f a) * (dworkPi p * S)) := by ring
    rw [hdecomp]
    refine le_trans (IsUltrametricDist.norm_add_le_max _ _) (max_le ?_ ?_)
    · rw [norm_mul]; exact le_trans (mul_le_of_le_one_left (norm_nonneg _) hga_le) hih
    · refine le_trans (IsUltrametricDist.norm_add_le_max _ _) (max_le ?_ ?_)
      · rw [norm_mul]; exact le_trans (mul_le_of_le_one_right (norm_nonneg _) h1s_le) hga
      · rw [norm_mul, norm_mul, norm_mul]
        calc (‖dworkPi p‖ * ‖f a‖) * (‖dworkPi p‖ * ‖S‖)
            ≤ (‖dworkPi p‖ * 1) * (‖dworkPi p‖ * 1) :=
              mul_le_mul (mul_le_mul_of_nonneg_left hfa (norm_nonneg _))
                (mul_le_mul_of_nonneg_left hsum_le (norm_nonneg _)) (by positivity) (by positivity)
          _ = ‖dworkPi p‖ ^ 2 := by ring

/-- For every `1 ≤ k < p`, `‖θ(1)^k - 1‖ = ‖ϖ‖` (in particular, `θ(1)^k ≠ 1`). -/
theorem norm_evalTheta_one_pow_sub_one {k : ℕ} (hk1 : 1 ≤ k) (hkp : k < p) :
    letI := dworkNormedField p
    ‖(evalTheta p 1) ^ k - 1‖ = ‖dworkPi p‖ := by
  let _ : NormedField (DworkField p) := dworkNormedField p
  have _ : IsUltrametricDist (DworkField p) := dworkField_ultra p
  have _ : CharZero (DworkField p) := dworkField_charZero p
  have hlt : ‖(p : DworkField p)‖ < 1 := dworkField_norm_p_lt_one p
  have hpi_lt_one : ‖dworkPi p‖ < 1 := by
    rw [norm_dworkPi hp.out (dworkPi_pow p)]
    exact expRadius_lt_one hp.out hlt
  have hpi_pos : 0 < ‖dworkPi p‖ := by
    rw [norm_dworkPi hp.out (dworkPi_pow p)]
    exact expRadius_pos hp.out
  have hprod := norm_prod_sub_one_add_pi_sum_le p (Finset.range k)
    (fun _ => (1 : DworkField p)) (fun _ => evalTheta p 1)
    (fun _ _ => by simp)
    (fun _ _ => norm_evalTheta_sub_one_add_pi_le p (by simp))
  simp only [Finset.prod_const, Finset.card_range, Finset.sum_const, nsmul_eq_mul, mul_one] at hprod
  have hndvd : ¬ p ∣ k := Nat.not_dvd_of_pos_of_lt hk1 hkp
  have hk_norm : ‖(k : DworkField p)‖ = 1 :=
    norm_natCast_eq_one_of_not_dvd hp.out hlt hndvd
  have hmain : ‖dworkPi p * (k : DworkField p)‖ = ‖dworkPi p‖ := by
    rw [norm_mul, hk_norm, mul_one]
  have hsmall : ‖(evalTheta p 1) ^ k - (1 + dworkPi p * (k : DworkField p))‖ <
      ‖dworkPi p * (k : DworkField p)‖ := by
    rw [hmain]
    exact lt_of_le_of_lt hprod (by nlinarith)
  rw [show (evalTheta p 1) ^ k - 1 =
      (dworkPi p * (k : DworkField p)) + ((evalTheta p 1) ^ k - (1 + dworkPi p * (k : DworkField p))) by ring]
  rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (ne_of_gt hsmall),
    max_eq_left hsmall.le, hmain]

/-- Every `p`-th root of unity `ζ ∈ DworkField p` is a power `(evalTheta p 1) ^ k` for some `k < p`. -/
lemma eq_evalTheta_one_pow_of_pow_p_eq_one {ζ : DworkField p} (hζ : ζ ^ p = 1) :
    ∃ k < p, ζ = (evalTheta p 1) ^ k := by
  let _ : NormedField (DworkField p) := dworkNormedField p
  have _ : IsUltrametricDist (DworkField p) := dworkField_ultra p
  have _ : CharZero (DworkField p) := dworkField_charZero p
  have hpi_pos : 0 < ‖dworkPi p‖ := by
    rw [norm_dworkPi hp.out (dworkPi_pow p)]
    exact expRadius_pos hp.out
  let P : Polynomial (DworkField p) := Polynomial.X ^ p - 1
  have hPne : P ≠ 0 := by
    intro h0
    have hcoeff := congrArg (fun Q : Polynomial (DworkField p) => Q.coeff p) h0
    simp [P, Polynomial.coeff_one, hp.out.ne_zero] at hcoeff
  have hPdeg : P.natDegree = p := by
    have hpos : 0 < p := hp.out.pos
    unfold P
    rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt]
    · exact Polynomial.natDegree_X_pow p
    · rw [Polynomial.natDegree_X_pow, Polynomial.natDegree_one]; exact hpos
  let S : Finset (DworkField p) := (Finset.range p).image (fun k => (evalTheta p 1) ^ k)
  have hScard : S.card = p := by
    rw [Finset.card_image_of_injOn]
    · exact Finset.card_range p
    · intro a ha b hb hab
      rw [Finset.mem_coe, Finset.mem_range] at ha hb
      by_contra hne
      wlog hlt : a < b generalizing a b
      · exact this hb ha hab.symm (Ne.symm hne) (by omega)
      have hne0 : (evalTheta p 1) ^ a ≠ 0 := by
        intro h0
        have hp0 : ((evalTheta p 1) ^ p) ^ a = 0 := by
          rw [← pow_mul, mul_comm, pow_mul, h0, zero_pow hp.out.ne_zero]
        rw [evalTheta_one_pow_p, one_pow] at hp0
        exact one_ne_zero hp0
      have hpow1 : (evalTheta p 1) ^ (b - a) = 1 := by
        dsimp only at hab
        have hmul : (evalTheta p 1) ^ a * (evalTheta p 1) ^ (b - a) = (evalTheta p 1) ^ a * 1 := by
          rw [← pow_add, Nat.add_sub_cancel' hlt.le, mul_one, hab]
        exact mul_left_cancel₀ hne0 hmul
      have hnorm := norm_evalTheta_one_pow_sub_one p (by omega : 1 ≤ b - a) (by omega : b - a < p)
      rw [hpow1, sub_self, norm_zero] at hnorm
      linarith
  have hSsub : ∀ z ∈ S, z ∈ P.roots.toFinset := by
    intro z hz
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hPne]
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hz
    simp only [P, Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_one]
    rw [← pow_mul, mul_comm, pow_mul, evalTheta_one_pow_p, one_pow, sub_self]
  have hroots_card : P.roots.toFinset.card ≤ p := by
    calc P.roots.toFinset.card ≤ P.roots.card := Multiset.toFinset_card_le _
      _ ≤ P.natDegree := Polynomial.card_roots' P
      _ = p := hPdeg
  have hSeq : S = P.roots.toFinset :=
    Finset.eq_of_subset_of_card_le hSsub (by rw [hScard]; exact hroots_card)
  have hζmem : ζ ∈ S := by
    rw [hSeq, Multiset.mem_toFinset, Polynomial.mem_roots hPne]
    simp [P, Polynomial.IsRoot, hζ]
  obtain ⟨k, hk, heq⟩ := Finset.mem_image.mp hζmem
  exact ⟨k, Finset.mem_range.mp hk, heq.symm⟩

/-- Finite-field trace `Tr_{𝔽_{p^s}/𝔽_p}(a) = ∑_{j < s} a^{p^j}` inside `kb p`. -/
def finTrace (s : ℕ) (a : kb p) : kb p :=
  ∑ j ∈ Finset.range s, a ^ (p ^ j)

lemma finTrace_pow_p {s : ℕ} (hs : 1 ≤ s) {a : kb p} (ha : a ^ (p ^ s) = a) :
    (finTrace p s a) ^ p = finTrace p s a := by
  unfold finTrace
  have h1 : (∑ j ∈ Finset.range s, a ^ (p ^ j)) ^ p =
      ∑ j ∈ Finset.range s, (a ^ (p ^ j)) ^ p := by
    change frobenius (kb p) p (∑ j ∈ Finset.range s, a ^ (p ^ j)) = _
    rw [map_sum]
    rfl
  rw [h1]
  have hpow : ∀ j, (a ^ (p ^ j)) ^ p = a ^ (p ^ (j + 1)) := fun j => by
    rw [← pow_mul, ← pow_succ]
  simp_rw [hpow]
  obtain ⟨s', rfl⟩ := Nat.exists_eq_add_of_le' hs
  rw [Finset.sum_range_succ, Finset.sum_range_succ', pow_zero, pow_one, ha, add_comm]

lemma finTrace_add (s : ℕ) (a b : kb p) :
    finTrace p s (a + b) = finTrace p s a + finTrace p s b := by
  unfold finTrace
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hpow : ∀ k : ℕ, (a + b) ^ (p ^ k) = a ^ (p ^ k) + b ^ (p ^ k) := fun k => by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, pow_mul, ih, add_pow_char, ← pow_mul, ← pow_mul, ← pow_succ]
  exact hpow j

/-- Every `t ∈ kb p` with `t ^ p = t` is a natural number cast `(m : kb p)` for some `m < p`. -/
lemma exists_nat_lt_of_pow_p_eq {t : kb p} (ht : t ^ p = t) :
    ∃ m < p, (m : kb p) = t := by
  let P : Polynomial (kb p) := Polynomial.X ^ p - Polynomial.X
  have hPne : P ≠ 0 := by
    intro h0
    have hc := congrArg (fun Q : Polynomial (kb p) => Q.coeff p) h0
    simp only [P, Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_X,
      Polynomial.coeff_zero] at hc
    have h1ne : (1 : ℕ) ≠ p := by have := hp.out.two_le; omega
    rw [if_neg h1ne, sub_zero] at hc
    exact one_ne_zero hc
  have hPdeg : P.natDegree = p := by
    have hlt : 1 < p := hp.out.one_lt
    unfold P
    rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt]
    · exact Polynomial.natDegree_X_pow p
    · rw [Polynomial.natDegree_X_pow, Polynomial.natDegree_X]; exact hlt
  let S : Finset (kb p) := (Finset.range p).image (fun m : ℕ => (m : kb p))
  have hScard : S.card = p := by
    rw [Finset.card_image_of_injOn]
    · exact Finset.card_range p
    · intro a ha b hb hab
      rw [Finset.mem_coe, Finset.mem_range] at ha hb
      have hcast : (a : ZMod p) = (b : ZMod p) := by
        have hinj := (algebraMap (ZMod p) (kb p)).injective
        apply hinj
        simpa using hab
      have hmod : a % p = b % p := by
        simpa [ZMod.val_natCast] using congrArg ZMod.val hcast
      rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at hmod
      exact hmod
  have hSsub : ∀ z ∈ S, z ∈ P.roots.toFinset := by
    intro z hz
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hPne]
    obtain ⟨m, _, rfl⟩ := Finset.mem_image.mp hz
    simp only [P, Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X]
    have hzm : ((m : ZMod p) ^ p) = (m : ZMod p) := ZMod.pow_card (m : ZMod p)
    have hmap := congrArg (algebraMap (ZMod p) (kb p)) hzm
    simp only [map_pow, map_natCast] at hmap
    rw [hmap, sub_self]
  have hroots_card : P.roots.toFinset.card ≤ p := by
    calc P.roots.toFinset.card ≤ P.roots.card := Multiset.toFinset_card_le _
      _ ≤ P.natDegree := Polynomial.card_roots' P
      _ = p := hPdeg
  have hSeq : S = P.roots.toFinset :=
    Finset.eq_of_subset_of_card_le hSsub (by rw [hScard]; exact hroots_card)
  have htmem : t ∈ S := by
    rw [hSeq, Multiset.mem_toFinset, Polynomial.mem_roots hPne]
    simp [P, Polynomial.IsRoot, ht]
  obtain ⟨m, hm, heq⟩ := Finset.mem_image.mp htmem
  exact ⟨m, Finset.mem_range.mp hm, heq⟩

/-- **Exact Character-Trace Identity**: for any `s ≥ 1`, `a ∈ kb p` with `a^{p^s} = a`, and
`m : ℕ` with `(m : kb p) = finTrace p s a`, we have `dworkChar p s a = (evalTheta p 1) ^ m`! -/
theorem dworkChar_eq_pow_of_trace {s : ℕ} (hs : 1 ≤ s) {a : kb p} (ha : a ^ (p ^ s) = a)
    {m : ℕ} (hm : (m : kb p) = finTrace p s a) :
    dworkChar p s a = (evalTheta p 1) ^ m := by
  let _ : NormedField (DworkField p) := dworkNormedField p
  have _ : IsUltrametricDist (DworkField p) := dworkField_ultra p
  have _ : CharZero (DworkField p) := dworkField_charZero p
  have hlt : ‖(p : DworkField p)‖ < 1 := dworkField_norm_p_lt_one p
  have hpi_lt_one : ‖dworkPi p‖ < 1 := by
    rw [norm_dworkPi hp.out (dworkPi_pow p)]
    exact expRadius_lt_one hp.out hlt
  have hpi_pos : 0 < ‖dworkPi p‖ := by
    rw [norm_dworkPi hp.out (dworkPi_pow p)]
    exact expRadius_pos hp.out
  -- Step 1: First-order approximation of `dworkChar p s a`
  set y : DworkField p := ∑ j ∈ Finset.range s, (teich p a) ^ (p ^ j)
  have hchar_approx : ‖dworkChar p s a - (1 + dworkPi p * y)‖ ≤ ‖dworkPi p‖ ^ 2 := by
    unfold dworkChar y
    refine norm_prod_sub_one_add_pi_sum_le p (Finset.range s)
      (fun j => (teich p a) ^ (p ^ j)) (fun j => evalTheta p ((teich p a) ^ (p ^ j)))
      (fun j _ => by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) (teich_norm_le_one p a))
      (fun j _ => norm_evalTheta_sub_one_add_pi_le p (by
        rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) (teich_norm_le_one p a)))
  -- Step 2: First-order approximation of `(evalTheta p 1) ^ m`
  have hpow_approx : ‖(evalTheta p 1) ^ m - (1 + dworkPi p * (m : DworkField p))‖ ≤ ‖dworkPi p‖ ^ 2 := by
    have h := norm_prod_sub_one_add_pi_sum_le p (Finset.range m)
      (fun _ => (1 : DworkField p)) (fun _ => evalTheta p 1)
      (fun _ _ => by simp)
      (fun _ _ => norm_evalTheta_sub_one_add_pi_le p (by simp))
    simpa [Finset.prod_const, Finset.sum_const] using h
  -- Step 3: `‖y - m‖ ≤ ‖p‖ ≤ ‖ϖ‖` (since `y` and `m` have the same Witt constant coeff `Tr(a)`)
  have hy_sub_m : ‖y - (m : DworkField p)‖ ≤ ‖dworkPi p‖ := by
    let yW : WW p := ∑ j ∈ Finset.range s, (WittVector.teichmuller p a) ^ (p ^ j)
    have hyW_coe : algebraMap (K0 p) (DworkField p) (algebraMap (WW p) (K0 p) yW) = y := by
      simp [yW, y, teich, map_sum, map_pow]
    have hcc : WittVector.constantCoeff (yW - (m : WW p)) = 0 := by
      rw [map_sub, map_natCast, map_sum]
      have hterm : ∀ j : ℕ, WittVector.constantCoeff ((WittVector.teichmuller p a) ^ (p ^ j)) = a ^ (p ^ j) := by
        intro j
        rw [map_pow]
        change (WittVector.teichmuller p a).coeff 0 ^ (p ^ j) = a ^ (p ^ j)
        rw [WittVector.teichmuller_coeff_zero]
      simp_rw [hterm]
      change finTrace p s a - (m : kb p) = 0
      rw [hm, sub_self]
    have hmem : yW - (m : WW p) ∈ Ideal.span {(p : WW p)} :=
      (WittVector.mem_span_p_iff_coeff_zero_eq_zero _).mpr hcc
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton.mp hmem
    have hdiff : y - (m : DworkField p) =
        (p : DworkField p) * algebraMap (K0 p) (DworkField p) (algebraMap (WW p) (K0 p) w) := by
      rw [← hyW_coe, show (m : DworkField p) =
        algebraMap (K0 p) (DworkField p) (algebraMap (WW p) (K0 p) (m : WW p)) by simp,
        ← map_sub, ← map_sub, hw, map_mul, map_mul, map_natCast, map_natCast]
    rw [hdiff, norm_mul]
    have hw_le : ‖algebraMap (K0 p) (DworkField p) (algebraMap (WW p) (K0 p) w)‖ ≤ 1 := by
      change dworkNorm p (algebraMap (K0 p) (DworkField p) (algebraMap (WW p) (K0 p) w)) ≤ 1
      rw [dworkNorm_algebraMap]
      exact wittAbvOn_coe_le_one p (kb p) w
    have hp_le_pi : ‖(p : DworkField p)‖ ≤ ‖dworkPi p‖ := by
      have hpow : ‖(p : DworkField p)‖ = ‖dworkPi p‖ ^ (p - 1) := by
        rw [← norm_neg, ← dworkPi_pow p, norm_pow]
      rw [hpow]
      have h1 : 1 ≤ p - 1 := by have := hp.out.two_le; omega
      calc ‖dworkPi p‖ ^ (p - 1) ≤ ‖dworkPi p‖ ^ 1 := pow_le_pow_of_le_one (norm_nonneg _) hpi_lt_one.le h1
        _ = ‖dworkPi p‖ := pow_one _
    exact le_trans (mul_le_of_le_one_right (norm_nonneg _) hw_le) hp_le_pi
  -- Step 4: `‖dworkChar p s a - (evalTheta p 1) ^ m‖ ≤ ‖ϖ‖^2 < ‖ϖ‖`
  have hdiff_le : ‖dworkChar p s a - (evalTheta p 1) ^ m‖ ≤ ‖dworkPi p‖ ^ 2 := by
    have hdecomp : dworkChar p s a - (evalTheta p 1) ^ m =
        (dworkChar p s a - (1 + dworkPi p * y)) +
        (dworkPi p * (y - (m : DworkField p)) -
         ((evalTheta p 1) ^ m - (1 + dworkPi p * (m : DworkField p)))) := by ring
    rw [hdecomp]
    refine le_trans (IsUltrametricDist.norm_add_le_max _ _) (max_le hchar_approx ?_)
    rw [sub_eq_add_neg]
    refine le_trans (IsUltrametricDist.norm_add_le_max _ _) (max_le ?_ (by rw [norm_neg]; exact hpow_approx))
    rw [norm_mul, pow_two]
    exact mul_le_mul_of_nonneg_left hy_sub_m (norm_nonneg _)
  -- Step 5: Quotient `ζ = dworkChar / θ(1)^m` is a `p`-th root of unity with `‖ζ - 1‖ < ‖ϖ‖`, hence `ζ = 1`!
  have hth_norm : ‖evalTheta p 1‖ = 1 := by
    have hpow1 : ‖evalTheta p 1‖ ^ p = 1 := by
      rw [← norm_pow, evalTheta_one_pow_p, norm_one]
    have hnn : 0 ≤ ‖evalTheta p 1‖ := norm_nonneg _
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt1 | hgt1
    · have : ‖evalTheta p 1‖ ^ p < 1 := pow_lt_one₀ hnn hlt1 hp.out.ne_zero
      linarith
    · have : 1 < ‖evalTheta p 1‖ ^ p := one_lt_pow₀ hgt1 hp.out.ne_zero
      linarith
  have hthm_ne : (evalTheta p 1) ^ m ≠ 0 := by
    intro h0
    have : ‖(evalTheta p 1) ^ m‖ = 0 := by rw [h0, norm_zero]
    rw [norm_pow, hth_norm, one_pow] at this
    norm_num at this
  set ζ : DworkField p := dworkChar p s a * ((evalTheta p 1) ^ m)⁻¹
  have hζ_pow : ζ ^ p = 1 := by
    dsimp only [ζ]
    rw [mul_pow, inv_pow, ← pow_mul, mul_comm m p, pow_mul,
      dworkChar_pow_p p hs ha, evalTheta_one_pow_p, one_pow, inv_one, mul_one]
  obtain ⟨k, hkp, hζk⟩ := eq_evalTheta_one_pow_of_pow_p_eq_one p hζ_pow
  have hζ_sub_lt : ‖ζ - 1‖ < ‖dworkPi p‖ := by
    have hrew : ζ - 1 = (dworkChar p s a - (evalTheta p 1) ^ m) * ((evalTheta p 1) ^ m)⁻¹ := by
      dsimp only [ζ]; field_simp [hthm_ne]
    rw [hrew, norm_mul, norm_inv, norm_pow, hth_norm, one_pow, inv_one, mul_one]
    exact lt_of_le_of_lt hdiff_le (by nlinarith)
  have hk0 : k = 0 := by
    by_contra hkne
    have hk1 : 1 ≤ k := Nat.pos_of_ne_zero hkne
    have heq := norm_evalTheta_one_pow_sub_one p hk1 hkp
    rw [← hζk] at heq
    linarith
  rw [hk0, pow_zero] at hζk
  have hmul : dworkChar p s a * ((evalTheta p 1) ^ m)⁻¹ * (evalTheta p 1) ^ m =
      1 * (evalTheta p 1) ^ m := congrArg (· * (evalTheta p 1) ^ m) hζk
  simpa [mul_assoc, inv_mul_cancel₀ hthm_ne] using hmul

/-- **Additivity of Dwork's Character on `𝔽_{p^s}`**:
for all `a, b ∈ kb p` with `a^{p^s} = a` and `b^{p^s} = b`,
`dworkChar p s (a + b) = dworkChar p s a * dworkChar p s b`. -/
theorem dworkChar_add {s : ℕ} (hs : 1 ≤ s) {a b : kb p}
    (ha : a ^ (p ^ s) = a) (hb : b ^ (p ^ s) = b) :
    dworkChar p s (a + b) = dworkChar p s a * dworkChar p s b := by
  obtain ⟨ma, _, hma⟩ := exists_nat_lt_of_pow_p_eq p (finTrace_pow_p p hs ha)
  obtain ⟨mb, _, hmb⟩ := exists_nat_lt_of_pow_p_eq p (finTrace_pow_p p hs hb)
  have hab_pow : (a + b) ^ (p ^ s) = a + b := by
    have hadd : ∀ k : ℕ, (a + b) ^ (p ^ k) = a ^ (p ^ k) + b ^ (p ^ k) := fun k => by
      induction k with
      | zero => simp
      | succ k ih =>
        rw [pow_succ, pow_mul, ih, add_pow_char, ← pow_mul, ← pow_mul, ← pow_succ]
    rw [hadd s, ha, hb]
  have hmab : ((ma + mb : ℕ) : kb p) = finTrace p s (a + b) := by
    rw [Nat.cast_add, hma, hmb, finTrace_add]
  rw [dworkChar_eq_pow_of_trace p hs ha hma,
    dworkChar_eq_pow_of_trace p hs hb hmb,
    dworkChar_eq_pow_of_trace p hs hab_pow hmab, pow_add]

lemma dworkChar_zero (s : ℕ) : dworkChar p s 0 = 1 := by
  let _ : NormedField (DworkField p) := dworkNormedField p
  have _ : CharZero (DworkField p) := dworkField_charZero p
  unfold dworkChar
  refine Finset.prod_eq_one fun j _ => ?_
  rw [map_zero, zero_pow (pow_ne_zero j hp.out.ne_zero)]
  unfold evalTheta evalPS
  rw [tsum_eq_single 0]
  · rw [pow_zero, mul_one, PowerSeries.coeff_zero_eq_constantCoeff, dworkSplitting]
    exact constantCoeff_expPS (by simp [zero_pow hp.out.ne_zero])
  · intro n hn; simp [zero_pow hn]

/-- The finite subfield `𝔽_{p^s} = {a : kb p | a^{p^s} = a}` as a canonical `Finset (kb p)`. -/
def finFieldSet (s : ℕ) : Finset (kb p) :=
  (Polynomial.X ^ (p ^ s) - Polynomial.X : Polynomial (kb p)).roots.toFinset

lemma finFieldPoly_ne_zero {s : ℕ} (hs : 1 ≤ s) :
    (Polynomial.X ^ (p ^ s) - Polynomial.X : Polynomial (kb p)) ≠ 0 := by
  have hq_gt : 1 < p ^ s := one_lt_pow₀ hp.out.one_lt (by omega)
  intro h0
  have hc := congrArg (fun Q : Polynomial (kb p) => Q.coeff (p ^ s)) h0
  simp only [Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_X,
    Polynomial.coeff_zero] at hc
  rw [if_neg (by omega : 1 ≠ p ^ s), sub_zero] at hc
  exact one_ne_zero hc

lemma mem_finFieldSet {s : ℕ} (hs : 1 ≤ s) {a : kb p} :
    a ∈ finFieldSet p s ↔ a ^ (p ^ s) = a := by
  unfold finFieldSet
  rw [Multiset.mem_toFinset, Polynomial.mem_roots (finFieldPoly_ne_zero p hs)]
  simp only [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
    sub_eq_zero]

lemma card_finFieldSet {s : ℕ} (hs : 1 ≤ s) : (finFieldSet p s).card = p ^ s := by
  set P : Polynomial (kb p) := Polynomial.X ^ (p ^ s) - Polynomial.X
  have hq_gt : 1 < p ^ s := one_lt_pow₀ hp.out.one_lt (by omega)
  have hPdeg : P.natDegree = p ^ s := by
    unfold P
    rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt]
    · exact Polynomial.natDegree_X_pow (p ^ s)
    · rw [Polynomial.natDegree_X_pow, Polynomial.natDegree_X]; exact hq_gt
  have hderiv : Polynomial.derivative P = -1 := by
    unfold P
    rw [map_sub, Polynomial.derivative_X_pow, Polynomial.derivative_X]
    have hdvd : p ∣ p ^ s := dvd_pow_self p (by omega)
    have hcast : ((p ^ s : ℕ) : kb p) = 0 := (CharP.cast_eq_zero_iff (kb p) p (p ^ s)).mpr hdvd
    rw [hcast, map_zero, zero_mul, zero_sub]
  have hPsep : P.Separable := ⟨0, -1, by simp [hderiv]⟩
  have hnodup : P.roots.Nodup := Polynomial.nodup_roots hPsep
  have hsplits : P.Splits := IsAlgClosed.splits P
  unfold finFieldSet
  change P.roots.toFinset.card = p ^ s
  rw [Multiset.toFinset_card_of_nodup hnodup, ← hPdeg]
  exact (Polynomial.Splits.natDegree_eq_card_roots hsplits).symm

/-- The multiplicative group `𝔽_{p^s}ˣ` as a canonical `Finset (kb p)`. -/
def finFieldUnits (s : ℕ) : Finset (kb p) :=
  (finFieldSet p s).erase 0

lemma mem_finFieldUnits {s : ℕ} (hs : 1 ≤ s) {a : kb p} :
    a ∈ finFieldUnits p s ↔ a ≠ 0 ∧ a ^ (p ^ s) = a := by
  rw [finFieldUnits, Finset.mem_erase, mem_finFieldSet p hs]

lemma zero_mem_finFieldSet {s : ℕ} (hs : 1 ≤ s) : (0 : kb p) ∈ finFieldSet p s := by
  rw [mem_finFieldSet p hs, zero_pow (pow_ne_zero s hp.out.ne_zero)]

lemma card_finFieldUnits {s : ℕ} (hs : 1 ≤ s) : (finFieldUnits p s).card = p ^ s - 1 := by
  rw [finFieldUnits, Finset.card_erase_of_mem (zero_mem_finFieldSet p hs), card_finFieldSet p hs]

lemma add_mem_finFieldSet {s : ℕ} (hs : 1 ≤ s) {a b : kb p}
    (ha : a ∈ finFieldSet p s) (hb : b ∈ finFieldSet p s) :
    a + b ∈ finFieldSet p s := by
  rw [mem_finFieldSet p hs] at ha hb ⊢
  have hadd : ∀ k : ℕ, (a + b) ^ (p ^ k) = a ^ (p ^ k) + b ^ (p ^ k) := fun k => by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, pow_mul, ih, add_pow_char, ← pow_mul, ← pow_mul, ← pow_succ]
  rw [hadd s, ha, hb]

lemma mul_mem_finFieldSet {s : ℕ} (hs : 1 ≤ s) {a b : kb p}
    (ha : a ∈ finFieldSet p s) (hb : b ∈ finFieldSet p s) :
    a * b ∈ finFieldSet p s := by
  rw [mem_finFieldSet p hs] at ha hb ⊢
  rw [mul_pow, ha, hb]

lemma neg_mem_finFieldSet {s : ℕ} (hs : 1 ≤ s) {a : kb p} (ha : a ∈ finFieldSet p s) :
    -a ∈ finFieldSet p s := by
  rw [mem_finFieldSet p hs] at ha ⊢
  by_cases hp2 : p = 2
  · subst hp2
    have h2 : (-a : kb 2) = a := by
      have hchar : (2 : kb 2) = 0 := CharP.cast_eq_zero (kb 2) 2
      have : a + a = 0 := by rw [← two_mul, hchar, zero_mul]
      exact eq_of_sub_eq_zero (by rw [sub_eq_add_neg]; linear_combination -this)
    rw [h2, ha]
  · have hodd : Odd (p ^ s) := Odd.pow (hp.out.odd_of_ne_two hp2)
    rw [hodd.neg_pow, ha]

lemma inv_mem_finFieldSet {s : ℕ} (hs : 1 ≤ s) {a : kb p} (ha : a ∈ finFieldSet p s) :
    a⁻¹ ∈ finFieldSet p s := by
  rw [mem_finFieldSet p hs] at ha ⊢
  rw [inv_pow, ha]

/-- **Nontriviality of `dworkChar p s` on `𝔽_{p^s}`**: for every `s ≥ 1`, there exists
`a ∈ finFieldSet p s` with `dworkChar p s a ≠ 1`. -/
theorem dworkChar_nontrivial {s : ℕ} (hs : 1 ≤ s) :
    ∃ a ∈ finFieldSet p s, dworkChar p s a ≠ 1 := by
  let _ : NormedField (DworkField p) := dworkNormedField p
  have _ : IsUltrametricDist (DworkField p) := dworkField_ultra p
  have _ : CharZero (DworkField p) := dworkField_charZero p
  let Tpoly : Polynomial (kb p) := ∑ j ∈ Finset.range s, Polynomial.X ^ (p ^ j)
  have hTdeg : Tpoly.natDegree ≤ p ^ (s - 1) := by
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun j hj => ?_
    rw [Polynomial.natDegree_X_pow]
    exact Nat.pow_le_pow_right hp.out.pos (by rw [Finset.mem_range] at hj; omega)
  have hTne : Tpoly ≠ 0 := by
    intro h0
    have hc := congrArg (fun Q : Polynomial (kb p) => Q.coeff 1) h0
    simp only [Tpoly, Polynomial.finsetSum_coeff, Polynomial.coeff_X_pow, Polynomial.coeff_zero] at hc
    rw [Finset.sum_eq_single 0] at hc
    · simp at hc
    · intro j _ hj0
      have hgt : 1 < p ^ j := one_lt_pow₀ hp.out.one_lt hj0
      rw [if_neg (by omega)]
    · intro h; exact (h (Finset.mem_range.mpr (by omega))).elim
  have hlt_card : Tpoly.roots.toFinset.card < (finFieldSet p s).card := by
    calc Tpoly.roots.toFinset.card ≤ Tpoly.roots.card := Multiset.toFinset_card_le _
      _ ≤ Tpoly.natDegree := Polynomial.card_roots' Tpoly
      _ ≤ p ^ (s - 1) := hTdeg
      _ < p ^ s := Nat.pow_lt_pow_right hp.out.one_lt (by omega)
      _ = (finFieldSet p s).card := (card_finFieldSet p hs).symm
  obtain ⟨a, ha_mem, ha_not⟩ : ∃ a ∈ finFieldSet p s, a ∉ Tpoly.roots.toFinset := by
    by_contra hall
    push Not at hall
    have := Finset.card_le_card hall
    omega
  refine ⟨a, ha_mem, ?_⟩
  have htr_ne : finTrace p s a ≠ 0 := by
    intro h0
    apply ha_not
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hTne]
    simp only [Tpoly, Polynomial.IsRoot, Polynomial.eval_finsetSum, Polynomial.eval_pow,
      Polynomial.eval_X]
    exact h0
  have ha_pow : a ^ (p ^ s) = a := (mem_finFieldSet p hs).mp ha_mem
  obtain ⟨m, hmp, hm⟩ := exists_nat_lt_of_pow_p_eq p (finTrace_pow_p p hs ha_pow)
  have hm_pos : 1 ≤ m := by
    by_contra hm0
    have hm' : m = 0 := by omega
    rw [hm', Nat.cast_zero] at hm
    exact htr_ne hm.symm
  rw [dworkChar_eq_pow_of_trace p hs ha_pow hm]
  intro h1
  have hnorm := norm_evalTheta_one_pow_sub_one p hm_pos hmp
  rw [h1, sub_self, norm_zero] at hnorm
  have hpi_pos : 0 < ‖dworkPi p‖ := by
    rw [norm_dworkPi hp.out (dworkPi_pow p)]
    exact expRadius_pos hp.out
  linarith

/-- **Additive Character Orthogonality on `𝔽_{p^s}`**:
`∑_{x ∈ 𝔽_{p^s}} dworkChar p s (x * y) = if y = 0 then p^s else 0`. -/
theorem sum_finFieldSet_dworkChar {s : ℕ} (hs : 1 ≤ s) {y : kb p} (hy : y ∈ finFieldSet p s) :
    ∑ x ∈ finFieldSet p s, dworkChar p s (x * y) =
      if y = 0 then ((p ^ s : ℕ) : DworkField p) else 0 := by
  split_ifs with hy0
  · subst hy0
    simp only [mul_zero, dworkChar_zero p s, Finset.sum_const, nsmul_eq_mul, mul_one,
      card_finFieldSet p hs]
  · obtain ⟨a, ha_mem, ha_ne⟩ := dworkChar_nontrivial p hs
    let c : kb p := a * y⁻¹
    have hc_mem : c ∈ finFieldSet p s :=
      mul_mem_finFieldSet p hs ha_mem (inv_mem_finFieldSet p hs hy)
    have hcy : c * y = a := by dsimp [c]; field_simp [hy0]
    have hshift : ∑ x ∈ finFieldSet p s, dworkChar p s (x * y) =
        ∑ x ∈ finFieldSet p s, dworkChar p s ((x + c) * y) := by
      symm
      refine Finset.sum_bij (fun x _ => x + c) ?_ ?_ ?_ ?_
      · intro x hx; exact add_mem_finFieldSet p hs hx hc_mem
      · intro x₁ _ x₂ _ h; exact add_right_cancel h
      · intro z hz
        refine ⟨z + -c, add_mem_finFieldSet p hs hz (neg_mem_finFieldSet p hs hc_mem), by ring⟩
      · intro _ _; rfl
    have hmul : ∑ x ∈ finFieldSet p s, dworkChar p s ((x + c) * y) =
        dworkChar p s a * ∑ x ∈ finFieldSet p s, dworkChar p s (x * y) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun x hx => ?_
      rw [add_mul, hcy,
        dworkChar_add p hs ((mem_finFieldSet p hs).mp (mul_mem_finFieldSet p hs hx hy))
          ((mem_finFieldSet p hs).mp ha_mem),
        mul_comm]
    have heq : (dworkChar p s a - 1) * ∑ x ∈ finFieldSet p s, dworkChar p s (x * y) = 0 := by
      rw [sub_mul, one_mul, ← hmul, ← hshift, sub_self]
    exact (mul_eq_zero.mp heq).resolve_left (sub_ne_zero.mpr ha_ne)

/-- **Units-Form Character Orthogonality**:
`∑_{x ∈ 𝔽_{p^s}ˣ} dworkChar p s (x * y) = if y = 0 then p^s - 1 else -1`. -/
theorem sum_finFieldUnits_dworkChar {s : ℕ} (hs : 1 ≤ s) {y : kb p} (hy : y ∈ finFieldSet p s) :
    ∑ x ∈ finFieldUnits p s, dworkChar p s (x * y) =
      if y = 0 then ((p ^ s : ℕ) : DworkField p) - 1 else -1 := by
  have hsplit := Finset.add_sum_erase (finFieldSet p s) (fun x => dworkChar p s (x * y))
    (zero_mem_finFieldSet p hs)
  rw [zero_mul, dworkChar_zero p s, sum_finFieldSet_dworkChar p hs hy] at hsplit
  change 1 + ∑ x ∈ finFieldUnits p s, dworkChar p s (x * y) = _ at hsplit
  split_ifs at hsplit ⊢ <;> linear_combination hsplit

end ConcreteDworkChar

end DworkCharacter

/-! ## Section 3: Multivariate Dwork Splitting Series, Infinite Matrix `M`, and Dwork's Trace Formula -/

section MultivariateDworkTrace

variable (p : ℕ) [hp : Fact p.Prime]

/-- Helper: `Finsupp.degree` of a `Fin d →₀ ℕ` equals `∑ i : Fin d, u i`. -/
lemma finsupp_degree_eq_sum {d : ℕ} (u : Fin d →₀ ℕ) :
    u.degree = ∑ i : Fin d, u i := by
  rw [Finsupp.degree_apply]
  exact Finset.sum_subset (Finset.subset_univ _) fun i _ hi =>
    Finsupp.notMem_support_iff.mp hi

/-- Helper: finite set of all `v : Fin d →₀ ℕ` with `v ≤ b`. -/
def leFinset {d : ℕ} (b : Fin d →₀ ℕ) : Finset (Fin d →₀ ℕ) :=
  (Fintype.piFinset fun i : Fin d => Finset.range (b i + 1)).image Finsupp.equivFunOnFinite.symm

lemma mem_leFinset {d : ℕ} {b v : Fin d →₀ ℕ} :
    v ∈ leFinset b ↔ v ≤ b := by
  unfold leFinset
  rw [Finset.mem_image]
  constructor
  · rintro ⟨f, hf, rfl⟩ i
    rw [Fintype.mem_piFinset] at hf
    have hi := Finset.mem_range.mp (hf i)
    have hval : (Finsupp.equivFunOnFinite.symm f) i = f i := rfl
    rw [hval]
    omega
  · intro hv
    refine ⟨Finsupp.equivFunOnFinite v, ?_, Finsupp.equivFunOnFinite.symm_apply_apply v⟩
    rw [Fintype.mem_piFinset]
    intro i
    rw [Finset.mem_range]
    have hi := hv i
    simp only [Finsupp.equivFunOnFinite_apply]
    omega

/-- Finite degree box `{u : Fin d →₀ ℕ | u.degree ≤ N}`. -/
def dworkBox (d N : ℕ) : Finset (Fin d →₀ ℕ) :=
  ((Fintype.piFinset fun _ : Fin d => Finset.range (N + 1)).image
    Finsupp.equivFunOnFinite.symm).filter (fun u => u.degree ≤ N)

lemma mem_dworkBox {d N : ℕ} {u : Fin d →₀ ℕ} :
    u ∈ dworkBox d N ↔ u.degree ≤ N := by
  unfold dworkBox
  rw [Finset.mem_filter, Finset.mem_image]
  constructor
  · exact fun h => h.2
  · intro hdeg
    refine ⟨⟨Finsupp.equivFunOnFinite u, ?_, Finsupp.equivFunOnFinite.symm_apply_apply u⟩, hdeg⟩
    rw [Fintype.mem_piFinset]
    intro i
    rw [Finset.mem_range]
    have hi : u i ≤ u.degree := by
      rw [finsupp_degree_eq_sum]
      exact Finset.single_le_sum (f := fun j => u j) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    simp only [Finsupp.equivFunOnFinite_apply]
    omega

lemma dworkBox_mono {d N₁ N₂ : ℕ} (h : N₁ ≤ N₂) :
    dworkBox d N₁ ⊆ dworkBox d N₂ := fun _ hu =>
  mem_dworkBox.mpr (le_trans (mem_dworkBox.mp hu) h)

/-- Exponential decay `u ↦ ρ^{u.degree}` is summable over `Fin d →₀ ℕ` whenever `0 ≤ ρ < 1`. -/
lemma summable_pow_degree {d : ℕ} {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    Summable fun u : Fin d →₀ ℕ => ρ ^ u.degree := by
  have hfun : ∀ d : ℕ, Summable fun f : Fin d → ℕ => ρ ^ (∑ i : Fin d, f i) := by
    intro d
    induction d with
    | zero =>
      exact summable_of_hasFiniteSupport (Set.toFinite _)
    | succ d ih =>
      let e : (Fin (d + 1) → ℕ) ≃ ℕ × (Fin d → ℕ) :=
        { toFun := fun f => (f 0, fun i => f i.succ)
          invFun := fun p => Fin.cons p.1 p.2
          left_inv := fun f => by ext i; refine Fin.cases rfl (fun _ => rfl) i
          right_inv := fun ⟨a, g⟩ => by ext <;> simp }
      rw [← e.symm.summable_iff]
      have hgeom : Summable fun n : ℕ => ρ ^ n := summable_geometric_of_lt_one hρ0 hρ1
      have hprod := Summable.mul_of_nonneg hgeom ih (fun _ => pow_nonneg hρ0 _) (fun _ => pow_nonneg hρ0 _)
      refine hprod.congr fun ⟨a, g⟩ => ?_
      change ρ ^ a * ρ ^ (∑ i : Fin d, g i) = ρ ^ (∑ i : Fin (d + 1), Fin.cons a g i)
      rw [Fin.sum_univ_succ, Fin.cons_zero]
      simp only [Fin.cons_succ, pow_add]
  have heq : (fun u : Fin d →₀ ℕ => ρ ^ u.degree) =
      (fun f : Fin d → ℕ => ρ ^ (∑ i : Fin d, f i)) ∘ Finsupp.equivFunOnFinite := by
    ext u
    simp [finsupp_degree_eq_sum]
  rw [heq]
  exact (Finsupp.equivFunOnFinite.summable_iff).mpr (hfun d)

lemma summable_rpow_neg_degree {d : ℕ} {c : ℝ} (hc : 0 < c) :
    Summable fun u : Fin d →₀ ℕ => (p : ℝ) ^ (-c * (u.degree : ℝ)) := by
  have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.out.pos
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.out.one_lt
  set ρ : ℝ := (p : ℝ) ^ (-c)
  have hρ0 : 0 ≤ ρ := Real.rpow_nonneg hppos.le _
  have hρ1 : ρ < 1 := Real.rpow_lt_one_of_one_lt_of_neg hp1 (neg_lt_zero.mpr hc)
  refine (summable_pow_degree hρ0 hρ1).congr fun u => ?_
  dsimp only [ρ]
  rw [← Real.rpow_natCast ((p : ℝ) ^ (-c)), ← Real.rpow_mul hppos.le]

/-- Exponential decay `‖coeff u F‖ ≤ p^{-c * u.degree}` is preserved under multiplication of `MvPowerSeries`. -/
lemma norm_coeff_mvMul_le {d : ℕ} {c : ℝ} {F G : MvPowerSeries (Fin d) (DworkField p)}
    (hF : ∀ u, (letI := dworkNormedField p; ‖MvPowerSeries.coeff u F‖ ≤ (p : ℝ) ^ (-c * (u.degree : ℝ))))
    (hG : ∀ u, (letI := dworkNormedField p; ‖MvPowerSeries.coeff u G‖ ≤ (p : ℝ) ^ (-c * (u.degree : ℝ))))
    (u : Fin d →₀ ℕ) :
    letI := dworkNormedField p
    ‖MvPowerSeries.coeff u (F * G)‖ ≤ (p : ℝ) ^ (-c * (u.degree : ℝ)) := by
  let _ : NormedField (DworkField p) := dworkNormedField p
  have _ : IsUltrametricDist (DworkField p) := dworkField_ultra p
  have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.out.pos
  rw [MvPowerSeries.coeff_mul]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (Real.rpow_nonneg hppos.le _) fun ab hab => ?_
  rw [Finset.mem_antidiagonal] at hab
  rw [norm_mul]
  calc ‖MvPowerSeries.coeff ab.1 F‖ * ‖MvPowerSeries.coeff ab.2 G‖
      ≤ (p : ℝ) ^ (-c * (ab.1.degree : ℝ)) * (p : ℝ) ^ (-c * (ab.2.degree : ℝ)) :=
        mul_le_mul (hF ab.1) (hG ab.2) (norm_nonneg _) (Real.rpow_nonneg hppos.le _)
    _ = (p : ℝ) ^ (-c * (ab.1.degree : ℝ) + -c * (ab.2.degree : ℝ)) := (Real.rpow_add hppos _ _).symm
    _ = (p : ℝ) ^ (-c * (u.degree : ℝ)) := by
        congr 1
        have hdeg : (u.degree : ℝ) = (ab.1.degree : ℝ) + (ab.2.degree : ℝ) := by
          rw [← hab, map_add, Nat.cast_add]
        rw [hdeg]; ring

lemma norm_coeff_mvProd_le {d : ℕ} {ι : Type*} (s : Finset ι) {c : ℝ}
    (F : ι → MvPowerSeries (Fin d) (DworkField p))
    (hF : ∀ i ∈ s, ∀ u, (letI := dworkNormedField p;
      ‖MvPowerSeries.coeff u (F i)‖ ≤ (p : ℝ) ^ (-c * (u.degree : ℝ)))) (u : Fin d →₀ ℕ) :
    letI := dworkNormedField p
    ‖MvPowerSeries.coeff u (∏ i ∈ s, F i)‖ ≤ (p : ℝ) ^ (-c * (u.degree : ℝ)) := by
  let _ : NormedField (DworkField p) := dworkNormedField p
  have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.out.pos
  induction s using Finset.induction_on generalizing u with
  | empty =>
    rw [Finset.prod_empty, MvPowerSeries.coeff_one]
    split_ifs with hu
    · subst hu; simp
    · rw [norm_zero]; exact Real.rpow_nonneg hppos.le _
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact norm_coeff_mvMul_le p (hF a (Finset.mem_insert_self a s))
      (fun v => ih (fun i hi => hF i (Finset.mem_insert_of_mem hi)) v) u

/-- Analytic evaluation of a multivariate power series `F ∈ MvPowerSeries (Fin d) K` at `t : Fin d → K`. -/
def mvEval {d : ℕ} (t : Fin d → DworkField p) (F : MvPowerSeries (Fin d) (DworkField p)) :
    DworkField p :=
  letI := dworkNormedField p
  ∑' u : Fin d →₀ ℕ, MvPowerSeries.coeff u F * ∏ i : Fin d, (t i) ^ (u i)

lemma mvEval_summable_norm_of_decay {d : ℕ} {c : ℝ} (hc : 0 < c)
    {F : MvPowerSeries (Fin d) (DworkField p)}
    (hF : ∀ u, (letI := dworkNormedField p; ‖MvPowerSeries.coeff u F‖ ≤ (p : ℝ) ^ (-c * (u.degree : ℝ))))
    {t : Fin d → DworkField p} (ht : ∀ i, (letI := dworkNormedField p; ‖t i‖ ≤ 1)) :
    letI := dworkNormedField p
    Summable fun u : Fin d →₀ ℕ => ‖MvPowerSeries.coeff u F * ∏ i : Fin d, (t i) ^ (u i)‖ := by
  let _ : NormedField (DworkField p) := dworkNormedField p
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun u => ?_)
    (summable_rpow_neg_degree p hc)
  rw [norm_mul, norm_prod]
  have hprod_le : ∏ i : Fin d, ‖(t i) ^ (u i)‖ ≤ 1 :=
    Finset.prod_le_one (fun _ _ => norm_nonneg _) fun i _ => by
      rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) (ht i)
  exact le_trans (mul_le_of_le_one_right (norm_nonneg _) hprod_le) (hF u)

lemma mvEval_one {d : ℕ} (t : Fin d → DworkField p) :
    mvEval p t (1 : MvPowerSeries (Fin d) (DworkField p)) = 1 := by
  let _ : NormedField (DworkField p) := dworkNormedField p
  unfold mvEval
  rw [tsum_eq_single (0 : Fin d →₀ ℕ)]
  · simp
  · intro u hu; simp [MvPowerSeries.coeff_one, hu]

lemma mvEval_mul {d : ℕ} {t : Fin d → DworkField p} {F G : MvPowerSeries (Fin d) (DworkField p)}
    (hF : (letI := dworkNormedField p; Summable fun u : Fin d →₀ ℕ =>
      ‖MvPowerSeries.coeff u F * ∏ i : Fin d, (t i) ^ (u i)‖))
    (hG : (letI := dworkNormedField p; Summable fun u : Fin d →₀ ℕ =>
      ‖MvPowerSeries.coeff u G * ∏ i : Fin d, (t i) ^ (u i)‖)) :
    mvEval p t (F * G) = mvEval p t F * mvEval p t G := by
  let _ : NormedField (DworkField p) := dworkNormedField p
  have _ : CompleteSpace (DworkField p) := dworkField_complete p
  unfold mvEval
  have hprod_norm : Summable fun q : (Fin d →₀ ℕ) × (Fin d →₀ ℕ) =>
      ‖(MvPowerSeries.coeff q.1 F * ∏ i : Fin d, (t i) ^ (q.1 i)) *
       (MvPowerSeries.coeff q.2 G * ∏ i : Fin d, (t i) ^ (q.2 i))‖ := by
    simpa [norm_mul] using
      Summable.mul_of_nonneg hF hG (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  have hprod := hprod_norm.of_norm
  let e := Equiv.sigmaFiberEquiv (fun q : (Fin d →₀ ℕ) × (Fin d →₀ ℕ) => q.1 + q.2)
  have hsig : Summable fun s : Σ u : Fin d →₀ ℕ, {q : (Fin d →₀ ℕ) × (Fin d →₀ ℕ) // q.1 + q.2 = u} =>
      (MvPowerSeries.coeff s.2.1.1 F * ∏ i : Fin d, (t i) ^ (s.2.1.1 i)) *
      (MvPowerSeries.coeff s.2.1.2 G * ∏ i : Fin d, (t i) ^ (s.2.1.2 i)) :=
    (e.summable_iff (f := fun q : (Fin d →₀ ℕ) × (Fin d →₀ ℕ) =>
      (MvPowerSeries.coeff q.1 F * ∏ i : Fin d, (t i) ^ (q.1 i)) *
      (MvPowerSeries.coeff q.2 G * ∏ i : Fin d, (t i) ^ (q.2 i)))).mpr hprod
  have he : (fun c : (y : Fin d →₀ ℕ) × {q : (Fin d →₀ ℕ) × (Fin d →₀ ℕ) // q.1 + q.2 = y} =>
      (MvPowerSeries.coeff (e c).1 F * ∏ i : Fin d, (t i) ^ ((e c).1 i)) *
      (MvPowerSeries.coeff (e c).2 G * ∏ i : Fin d, (t i) ^ ((e c).2 i))) =
      (fun s => (MvPowerSeries.coeff s.2.1.1 F * ∏ i : Fin d, (t i) ^ (s.2.1.1 i)) *
        (MvPowerSeries.coeff s.2.1.2 G * ∏ i : Fin d, (t i) ^ (s.2.1.2 i))) := rfl
  rw [tsum_mul_tsum_of_summable_norm hF hG, ← e.tsum_eq, he,
    hsig.tsum_sigma' (fun u => hsig.sigma_factor u)]
  congr 1
  ext u
  have : Fintype {q : (Fin d →₀ ℕ) × (Fin d →₀ ℕ) // q.1 + q.2 = u} :=
    Fintype.ofEquiv (Finset.antidiagonal u)
      { toFun := fun q => ⟨q.1, Finset.mem_antidiagonal.mp q.2⟩
        invFun := fun q => ⟨q.1, Finset.mem_antidiagonal.mpr q.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  rw [tsum_fintype, MvPowerSeries.coeff_mul, Finset.sum_mul]
  symm
  refine Finset.sum_bij (fun q _ => q.1)
    (fun q _ => Finset.mem_antidiagonal.mpr q.2)
    (fun _ _ _ _ h => Subtype.ext h)
    (fun q hq => ⟨⟨q, Finset.mem_antidiagonal.mp hq⟩, Finset.mem_univ _, rfl⟩)
    (fun q _ => ?_)
  have hq := q.2
  have hpow : ∏ i : Fin d, (t i) ^ (u i) =
      (∏ i : Fin d, (t i) ^ (q.1.1 i)) * (∏ i : Fin d, (t i) ^ (q.1.2 i)) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    have hqi : u i = q.1.1 i + q.1.2 i := by
      have := congrArg (fun a : Fin d →₀ ℕ => a i) q.2
      simpa using this.symm
    rw [hqi, pow_add]
  dsimp only
  rw [hpow]; ring

lemma mvEval_prod_of_decay {d : ℕ} {ι : Type*} (s : Finset ι) {c : ℝ} (hc : 0 < c)
    (F : ι → MvPowerSeries (Fin d) (DworkField p))
    (hF : ∀ i ∈ s, ∀ u, (letI := dworkNormedField p;
      ‖MvPowerSeries.coeff u (F i)‖ ≤ (p : ℝ) ^ (-c * (u.degree : ℝ))))
    {t : Fin d → DworkField p} (ht : ∀ i, (letI := dworkNormedField p; ‖t i‖ ≤ 1)) :
    mvEval p t (∏ i ∈ s, F i) = ∏ i ∈ s, mvEval p t (F i) := by
  induction s using Finset.induction_on with
  | empty => simp [mvEval_one]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha,
      mvEval_mul p
        (mvEval_summable_norm_of_decay p hc (hF a (Finset.mem_insert_self a s)) ht)
        (mvEval_summable_norm_of_decay p hc
          (norm_coeff_mvProd_le p s F fun i hi => hF i (Finset.mem_insert_of_mem hi)) ht),
      ih fun i hi => hF i (Finset.mem_insert_of_mem hi)]

/-- Multivariate Frobenius power substitution `F(X^k)` for `k ≥ 1`. -/
def mvSubstPow {d : ℕ} (k : ℕ) (F : MvPowerSeries (Fin d) (DworkField p)) :
    MvPowerSeries (Fin d) (DworkField p) :=
  fun u => if ∀ i : Fin d, k ∣ u i then
    MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm fun i => u i / k) F
  else 0

lemma coeff_mvSubstPow {d : ℕ} (k : ℕ) (F : MvPowerSeries (Fin d) (DworkField p)) (u : Fin d →₀ ℕ) :
    MvPowerSeries.coeff u (mvSubstPow p k F) =
      if ∀ i : Fin d, k ∣ u i then
        MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm fun i => u i / k) F
      else 0 := rfl

lemma coeff_mvSubstPow_smul {d : ℕ} {k : ℕ} (hk : 0 < k)
    (F : MvPowerSeries (Fin d) (DworkField p)) (v : Fin d →₀ ℕ) :
    MvPowerSeries.coeff (k • v) (mvSubstPow p k F) = MvPowerSeries.coeff v F := by
  rw [coeff_mvSubstPow, if_pos (fun i => by simp [dvd_mul_right])]
  congr 1
  ext i
  simp [Nat.mul_div_cancel_left _ hk]

lemma mvEval_mvSubstPow {d : ℕ} {k : ℕ} (hk : 0 < k) (t : Fin d → DworkField p)
    (F : MvPowerSeries (Fin d) (DworkField p)) :
    mvEval p t (mvSubstPow p k F) = mvEval p (fun i => (t i) ^ k) F := by
  let _ : NormedField (DworkField p) := dworkNormedField p
  unfold mvEval
  refine tsum_eq_tsum_of_ne_zero_bij (fun v => k • v.1) ?_ ?_ ?_
  · intro a b hab
    apply Subtype.ext
    ext i
    have hi := congrArg (fun u : Fin d →₀ ℕ => u i) hab
    simp only [Finsupp.smul_apply, smul_eq_mul] at hi
    exact Nat.eq_of_mul_eq_mul_left hk hi
  · intro u hu
    rw [Function.mem_support, coeff_mvSubstPow] at hu
    have hdiv : ∀ i : Fin d, k ∣ u i := by
      by_contra hnd
      rw [if_neg hnd, zero_mul] at hu
      exact hu rfl
    let v : Fin d →₀ ℕ := Finsupp.equivFunOnFinite.symm fun i => u i / k
    have huv : k • v = u := by
      ext i
      change k * (u i / k) = u i
      exact Nat.mul_div_cancel' (hdiv i)
    refine ⟨⟨v, ?_⟩, huv⟩
    rw [Function.mem_support]
    rw [if_pos hdiv] at hu
    have hprod : ∏ i : Fin d, (t i) ^ (u i) = ∏ i : Fin d, ((t i) ^ k) ^ (v i) := by
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [← pow_mul, ← huv, Finsupp.smul_apply, smul_eq_mul]
    rw [hprod] at hu
    exact hu
  · intro a
    rw [coeff_mvSubstPow_smul p hk]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Finsupp.smul_apply, smul_eq_mul, pow_mul]

lemma norm_coeff_mvSubstPow_le {d : ℕ} {k : ℕ} (hk : 0 < k) {c : ℝ}
    {F : MvPowerSeries (Fin d) (DworkField p)}
    (hF : ∀ u, (letI := dworkNormedField p; ‖MvPowerSeries.coeff u F‖ ≤ (p : ℝ) ^ (-c * (u.degree : ℝ))))
    (u : Fin d →₀ ℕ) :
    letI := dworkNormedField p
    ‖MvPowerSeries.coeff u (mvSubstPow p k F)‖ ≤ (p : ℝ) ^ (-(c / (k : ℝ)) * (u.degree : ℝ)) := by
  let _ : NormedField (DworkField p) := dworkNormedField p
  have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.out.pos
  rw [coeff_mvSubstPow]
  split_ifs with hdiv
  · set v : Fin d →₀ ℕ := Finsupp.equivFunOnFinite.symm fun i => u i / k
    have huv : k • v = u := by
      ext i
      change k * (u i / k) = u i
      exact Nat.mul_div_cancel' (hdiv i)
    have hdeg : u.degree = k * v.degree := by
      rw [← huv, finsupp_degree_eq_sum, finsupp_degree_eq_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => by simp
    refine (hF v).trans_eq ?_
    congr 1
    have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
    rw [hdeg, Nat.cast_mul]
    field_simp [hk0]
  · rw [norm_zero]; exact Real.rpow_nonneg hppos.le _

/-- Monomial Dwork splitting series `θ(c X^w)` for a nonzero exponent `w : Fin d →₀ ℕ`. -/
def mvThetaMonom {d : ℕ} (c : DworkField p) (w : Fin d →₀ ℕ) :
    MvPowerSeries (Fin d) (DworkField p) :=
  letI := dworkNormedField p
  haveI := dworkField_ultra p
  haveI := dworkField_charZero p
  fun u => if h : ∃ k : ℕ, u = k • w then
    PowerSeries.coeff h.choose (dworkSplitting (dworkPi p) p) * c ^ h.choose
  else 0

lemma smul_eq_smul_of_ne_zero {d : ℕ} {w : Fin d →₀ ℕ} (hw : w ≠ 0) {k₁ k₂ : ℕ}
    (h : k₁ • w = k₂ • w) : k₁ = k₂ := by
  have hdeg : w.degree ≠ 0 := fun hd => hw ((finsupp_degree_eq_zero_iff w).mp hd)
  have hmul : k₁ * w.degree = k₂ * w.degree := by
    have := congrArg Finsupp.degree h
    simpa [finsupp_degree_eq_sum, ← Finset.mul_sum] using this
  exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hdeg) hmul

lemma coeff_mvThetaMonom_smul {d : ℕ} (c : DworkField p) {w : Fin d →₀ ℕ} (hw : w ≠ 0) (k : ℕ) :
    letI := dworkNormedField p
    haveI := dworkField_ultra p
    haveI := dworkField_charZero p
    MvPowerSeries.coeff (k • w) (mvThetaMonom p c w) =
      PowerSeries.coeff k (dworkSplitting (dworkPi p) p) * c ^ k := by
  let _ : NormedField (DworkField p) := dworkNormedField p
  have _ : IsUltrametricDist (DworkField p) := dworkField_ultra p
  have _ : CharZero (DworkField p) := dworkField_charZero p
  change (if h : ∃ m : ℕ, k • w = m • w then _ else 0) = _
  rw [dif_pos ⟨k, rfl⟩]
  have heq : (⟨k, rfl⟩ : ∃ m : ℕ, k • w = m • w).choose = k :=
    (smul_eq_smul_of_ne_zero hw (⟨k, rfl⟩ : ∃ m : ℕ, k • w = m • w).choose_spec.symm)
  rw [heq]

lemma mvEval_mvThetaMonom {d : ℕ} (c : DworkField p) {w : Fin d →₀ ℕ} (hw : w ≠ 0)
    (t : Fin d → DworkField p) :
    mvEval p t (mvThetaMonom p c w) = evalTheta p (c * ∏ i : Fin d, (t i) ^ (w i)) := by
  let _ : NormedField (DworkField p) := dworkNormedField p
  have _ : IsUltrametricDist (DworkField p) := dworkField_ultra p
  have _ : CharZero (DworkField p) := dworkField_charZero p
  unfold mvEval evalTheta evalPS
  refine tsum_eq_tsum_of_ne_zero_bij (fun k => k.1 • w) ?_ ?_ ?_
  · intro a b hab
    exact Subtype.ext (smul_eq_smul_of_ne_zero hw hab)
  · intro u hu
    rw [Function.mem_support] at hu
    have hex : ∃ k : ℕ, u = k • w := by
      by_contra hnot
      have h0 : MvPowerSeries.coeff u (mvThetaMonom p c w) = 0 := dif_neg hnot
      rw [h0, zero_mul] at hu
      exact hu rfl
    obtain ⟨k, rfl⟩ := hex
    refine ⟨⟨k, ?_⟩, rfl⟩
    rw [Function.mem_support]
    rw [coeff_mvThetaMonom_smul p c hw k] at hu
    have hpow : (c * ∏ i : Fin d, (t i) ^ (w i)) ^ k =
        c ^ k * ∏ i : Fin d, (t i) ^ ((k • w) i) := by
      rw [mul_pow, ← Finset.prod_pow]
      congr 1
      refine Finset.prod_congr rfl fun i _ => by
        rw [Finsupp.smul_apply, smul_eq_mul, mul_comm, pow_mul]
    rw [hpow, ← mul_assoc]
    exact hu
  · intro k
    rw [coeff_mvThetaMonom_smul p c hw k.1, mul_pow, ← Finset.prod_pow, mul_assoc]
    congr 2
    refine Finset.prod_congr rfl fun i _ => by
      rw [Finsupp.smul_apply, smul_eq_mul, mul_comm, pow_mul]

lemma norm_coeff_mvThetaMonom_le {d : ℕ} {c : DworkField p}
    (hc : (letI := dworkNormedField p; ‖c‖ ≤ 1))
    {w : Fin d →₀ ℕ} (_hw : w ≠ 0) {D : ℕ} (hD : w.degree ≤ D) (hDpos : 0 < D) (u : Fin d →₀ ℕ) :
    letI := dworkNormedField p
    ‖MvPowerSeries.coeff u (mvThetaMonom p c w)‖ ≤
      (p : ℝ) ^ (-((((p : ℝ) - 1) / ((p : ℝ) ^ 2 * (D : ℝ))) * (u.degree : ℝ))) := by
  let _ : NormedField (DworkField p) := dworkNormedField p
  have _ : IsUltrametricDist (DworkField p) := dworkField_ultra p
  have _ : CharZero (DworkField p) := dworkField_charZero p
  have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.out.pos
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.out.one_le
  have hlt : ‖(p : DworkField p)‖ < 1 := dworkField_norm_p_lt_one p
  change ‖if h : ∃ k : ℕ, u = k • w then _ else 0‖ ≤ _
  split_ifs with hex
  · set k := hex.choose
    have hu : u = k • w := hex.choose_spec
    rw [norm_mul, norm_pow]
    calc ‖PowerSeries.coeff k (dworkSplitting (dworkPi p) p)‖ * ‖c‖ ^ k
        ≤ ‖PowerSeries.coeff k (dworkSplitting (dworkPi p) p)‖ * 1 :=
          mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg c) hc) (norm_nonneg _)
      _ = ‖PowerSeries.coeff k (dworkSplitting (dworkPi p) p)‖ := mul_one _
      _ ≤ ‖(p : DworkField p)‖ ^ ((k : ℝ) * (((p : ℝ) - 1) / (p : ℝ) ^ 2)) :=
          norm_coeff_dworkSplitting_le hp.out hlt (dworkPi_pow p) k
      _ = (p : ℝ) ^ (-((k : ℝ) * (((p : ℝ) - 1) / (p : ℝ) ^ 2))) := by
          rw [dworkField_norm_p p, Real.inv_rpow hppos.le, ← Real.rpow_neg hppos.le]
      _ ≤ (p : ℝ) ^ (-((((p : ℝ) - 1) / ((p : ℝ) ^ 2 * (D : ℝ))) * (u.degree : ℝ))) := by
          refine Real.rpow_le_rpow_of_exponent_le hp1 ?_
          have hdeg : u.degree = k * w.degree := by
            rw [hu, finsupp_degree_eq_sum, finsupp_degree_eq_sum, Finset.mul_sum]
            refine Finset.sum_congr rfl fun i _ => by simp
          have hdeg_le : (u.degree : ℝ) ≤ (k : ℝ) * (D : ℝ) := by
            rw [hdeg, Nat.cast_mul]
            exact mul_le_mul_of_nonneg_left (by exact_mod_cast hD) (Nat.cast_nonneg k)
          have hD0 : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hDpos
          have hp2 : (0 : ℝ) < (p : ℝ) ^ 2 := sq_pos_of_pos hppos
          have hpm1 : (0 : ℝ) ≤ (p : ℝ) - 1 := by
            have : (1 : ℝ) ≤ (p : ℝ) := hp1; linarith
          have hcoef : 0 ≤ ((p : ℝ) - 1) / ((p : ℝ) ^ 2 * (D : ℝ)) := by positivity
          have hmul := mul_le_mul_of_nonneg_left hdeg_le hcoef
          have heq : ((p : ℝ) - 1) / ((p : ℝ) ^ 2 * (D : ℝ)) * ((k : ℝ) * (D : ℝ)) =
              (k : ℝ) * (((p : ℝ) - 1) / (p : ℝ) ^ 2) := by
            field_simp [hp2.ne', hD0.ne']
          linarith
  · rw [norm_zero]; exact Real.rpow_nonneg hppos.le _

/-! ### Row-Finite Infinite Dwork Matrix `dworkInfMat` & Exact Powers -/

/-- The infinite Dwork matrix `M_{u, v} = coeff_{q u - v}(F)` (0 unless `v ≤ q • u`). -/
def dworkInfMat {d : ℕ} (q : ℕ) (F : MvPowerSeries (Fin d) (DworkField p))
    (u v : Fin d →₀ ℕ) : DworkField p :=
  if v ≤ q • u then MvPowerSeries.coeff (q • u - v) F else 0

/-- Iterated Dwork splitting series `F_{m}(X) = ∏_{l < m} F(X^{q^l})`. -/
def dworkIterSeries {d : ℕ} (q : ℕ) (F : MvPowerSeries (Fin d) (DworkField p)) (m : ℕ) :
    MvPowerSeries (Fin d) (DworkField p) :=
  ∏ l ∈ Finset.range m, mvSubstPow p (q ^ l) F

/-- Exact row-finite `m`-th matrix power of `dworkInfMat q F`. -/
def dworkInfMatPow {d : ℕ} (q : ℕ) (F : MvPowerSeries (Fin d) (DworkField p)) :
    ℕ → (Fin d →₀ ℕ) → (Fin d →₀ ℕ) → DworkField p
  | 0, u, v => if u = v then 1 else 0
  | m + 1, u, v =>
      ∑ w ∈ leFinset (q • u), dworkInfMat p q F u w * dworkInfMatPow q F m w v

/-- **Exact Matrix-Power Identity**:
`(M^m)_{u, v} = coeff_{q^m u - v}(∏_{l < m} F(X^{q^l}))` when `v ≤ q^m • u`, else `0`. -/
theorem dworkInfMatPow_eq {d : ℕ} {q : ℕ} (hq : 0 < q)
    (F : MvPowerSeries (Fin d) (DworkField p)) (m : ℕ) (u v : Fin d →₀ ℕ) :
    dworkInfMatPow p q F m u v =
      if v ≤ q ^ m • u then
        MvPowerSeries.coeff (q ^ m • u - v) (dworkIterSeries p q F m)
      else 0 := by
  induction m generalizing u v with
  | zero =>
    simp only [dworkInfMatPow, dworkIterSeries, Finset.range_zero, Finset.prod_empty,
      pow_zero, one_smul]
    by_cases hle : v ≤ u
    · rw [if_pos hle, MvPowerSeries.coeff_one]
      have heq : u - v = 0 ↔ u = v := by
        constructor
        · intro h
          ext i
          have h1 := congrArg (fun a : Fin d →₀ ℕ => a i) h
          have h2 : v i ≤ u i := hle i
          simp only [Finsupp.tsub_apply, Finsupp.coe_zero, Pi.zero_apply] at h1
          omega
        · rintro rfl; simp
      by_cases huv : u = v
      · rw [if_pos huv, if_pos (heq.mpr huv)]
      · rw [if_neg huv, if_neg (mt heq.mp huv)]
    · rw [if_neg hle, if_neg]
      rintro rfl
      exact hle le_rfl
  | succ m ih =>
    simp only [dworkInfMatPow, dworkIterSeries, Finset.prod_range_succ]
    simp_rw [ih]
    by_cases hv : v ≤ q ^ (m + 1) • u
    · rw [if_pos hv, MvPowerSeries.coeff_mul]
      have hqm : 0 < q ^ m := pow_pos hq m
      -- Filter the antidiagonal to pairs `(b, a)` where `q^m ∣ a`
      have hfilt_lhs : ∑ w ∈ leFinset (q • u),
          dworkInfMat p q F u w *
            (if v ≤ q ^ m • w then
              MvPowerSeries.coeff (q ^ m • w - v) (dworkIterSeries p q F m) else 0) =
          ∑ w ∈ (leFinset (q • u)).filter (fun w => v ≤ q ^ m • w),
            MvPowerSeries.coeff (q • u - w) F *
              MvPowerSeries.coeff (q ^ m • w - v) (dworkIterSeries p q F m) := by
        rw [← Finset.sum_subset (Finset.filter_subset (fun w => v ≤ q ^ m • w) (leFinset (q • u)))]
        · refine Finset.sum_congr rfl fun w hw => ?_
          rw [Finset.mem_filter, mem_leFinset] at hw
          rw [dworkInfMat, if_pos hw.1, if_pos hw.2]
        · intro w hw hnot
          rw [Finset.mem_filter] at hnot
          have hnv : ¬ v ≤ q ^ m • w := fun h => hnot ⟨hw, h⟩
          rw [if_neg hnv, mul_zero]
      have hfilt_rhs : ∑ ab ∈ Finset.antidiagonal (q ^ (m + 1) • u - v),
          MvPowerSeries.coeff ab.1 (dworkIterSeries p q F m) *
            MvPowerSeries.coeff ab.2 (mvSubstPow p (q ^ m) F) =
          ∑ ab ∈ (Finset.antidiagonal (q ^ (m + 1) • u - v)).filter
              (fun ab => ∀ i : Fin d, q ^ m ∣ ab.2 i),
            MvPowerSeries.coeff ab.1 (dworkIterSeries p q F m) *
              MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm fun i => ab.2 i / q ^ m) F := by
        rw [← Finset.sum_subset (Finset.filter_subset
          (fun ab : (Fin d →₀ ℕ) × (Fin d →₀ ℕ) => ∀ i : Fin d, q ^ m ∣ ab.2 i)
          (Finset.antidiagonal (q ^ (m + 1) • u - v)))]
        · refine Finset.sum_congr rfl fun ab hab => ?_
          rw [Finset.mem_filter] at hab
          rw [coeff_mvSubstPow, if_pos hab.2]
        · intro ab hab hnot
          rw [Finset.mem_filter] at hnot
          have hnd : ¬ ∀ i : Fin d, q ^ m ∣ ab.2 i := fun h => hnot ⟨hab, h⟩
          rw [coeff_mvSubstPow, if_neg hnd, mul_zero]
      rw [hfilt_lhs]
      change _ = ∑ ab ∈ Finset.antidiagonal (q ^ (m + 1) • u - v),
          MvPowerSeries.coeff ab.1 (dworkIterSeries p q F m) *
            MvPowerSeries.coeff ab.2 (mvSubstPow p (q ^ m) F)
      rw [hfilt_rhs]
      refine Finset.sum_bij
        (fun w _ => (q ^ m • w - v, q ^ m • (q • u - w))) ?_ ?_ ?_ ?_
      · intro w hw
        rw [Finset.mem_filter, mem_leFinset] at hw
        rw [Finset.mem_filter, Finset.mem_antidiagonal]
        refine ⟨?_, fun i => by simp [dvd_mul_right]⟩
        ext i
        have h1 : w i ≤ q * u i := hw.1 i
        have h2 : v i ≤ q ^ m * w i := hw.2 i
        simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.smul_apply, smul_eq_mul]
        have hmul : q ^ m * (q * u i - w i) = q ^ (m + 1) * u i - q ^ m * w i := by
          rw [Nat.mul_sub_left_distrib, pow_succ, mul_assoc]
        have hle_qm : q ^ m * w i ≤ q ^ (m + 1) * u i := by
          rw [pow_succ, mul_assoc]
          exact Nat.mul_le_mul_left (q ^ m) h1
        omega
      · intro w₁ hw₁ w₂ hw₂ heq
        rw [Finset.mem_filter, mem_leFinset] at hw₁ hw₂
        have h2 := congrArg Prod.snd heq
        ext i
        have hi := congrArg (fun a : Fin d →₀ ℕ => a i) h2
        simp only [Finsupp.smul_apply, Finsupp.tsub_apply, smul_eq_mul] at hi
        have hsub := Nat.eq_of_mul_eq_mul_left hqm hi
        have hle1 : w₁ i ≤ q * u i := hw₁.1 i
        have hle2 : w₂ i ≤ q * u i := hw₂.1 i
        omega
      · intro ab hab
        rw [Finset.mem_filter, Finset.mem_antidiagonal] at hab
        let a' : Fin d →₀ ℕ := Finsupp.equivFunOnFinite.symm fun i => ab.2 i / q ^ m
        have ha'_mul : ∀ i, q ^ m * a' i = ab.2 i := fun i => by
          change q ^ m * (ab.2 i / q ^ m) = ab.2 i
          exact Nat.mul_div_cancel' (hab.2 i)
        have ha'_le : a' ≤ q • u := by
          intro i
          have hsum_i : ab.1 i + ab.2 i = q ^ (m + 1) * u i - v i := by
            have := congrArg (fun z : Fin d →₀ ℕ => z i) hab.1
            simpa [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.smul_apply, smul_eq_mul] using this
          have hle_i : q ^ m * a' i ≤ q ^ m * (q * u i) := by
            rw [ha'_mul i, ← mul_assoc, ← pow_succ]
            omega
          exact Nat.le_of_mul_le_mul_left hle_i hqm
        let w : Fin d →₀ ℕ := q • u - a'
        have hw_le : w ≤ q • u := fun i => Nat.sub_le _ _
        have hv_le : v ≤ q ^ m • w := by
          intro i
          have hsum_i : ab.1 i + ab.2 i = q ^ (m + 1) * u i - v i := by
            have := congrArg (fun z : Fin d →₀ ℕ => z i) hab.1
            simpa [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.smul_apply, smul_eq_mul] using this
          have hv_i : v i ≤ q ^ (m + 1) * u i := hv i
          have hmul_w : q ^ m * w i = q ^ (m + 1) * u i - ab.2 i := by
            simp only [w, Finsupp.tsub_apply, Finsupp.smul_apply, smul_eq_mul]
            rw [Nat.mul_sub_left_distrib, pow_succ, mul_assoc, ha'_mul i]
          simp only [Finsupp.smul_apply, smul_eq_mul]
          omega
        refine ⟨w, Finset.mem_filter.mpr ⟨mem_leFinset.mpr hw_le, hv_le⟩, ?_⟩
        ext i
        · have hsum_i : ab.1 i + ab.2 i = q ^ (m + 1) * u i - v i := by
            have := congrArg (fun z : Fin d →₀ ℕ => z i) hab.1
            simpa [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.smul_apply, smul_eq_mul] using this
          have hv_i : v i ≤ q ^ (m + 1) * u i := hv i
          have hmul_w : q ^ m * w i = q ^ (m + 1) * u i - ab.2 i := by
            simp only [w, Finsupp.tsub_apply, Finsupp.smul_apply, smul_eq_mul]
            rw [Nat.mul_sub_left_distrib, pow_succ, mul_assoc, ha'_mul i]
          simp only [Finsupp.tsub_apply, Finsupp.smul_apply, smul_eq_mul]
          omega
        · simp only [w, Finsupp.smul_apply, Finsupp.tsub_apply, smul_eq_mul]
          have hle_i : a' i ≤ q * u i := ha'_le i
          rw [Nat.sub_sub_self hle_i, ha'_mul i]
      · intro w _
        rw [mul_comm]
        congr 1
        refine congrArg (fun z : Fin d →₀ ℕ => MvPowerSeries.coeff z F) ?_
        ext i
        change (q • u - w) i = q ^ m * (q * u i - w i) / q ^ m
        rw [Nat.mul_div_cancel_left _ hqm]
        rfl
    · rw [if_neg hv]
      refine Finset.sum_eq_zero fun w hw => ?_
      rw [mem_leFinset] at hw
      have hnv : ¬ v ≤ q ^ m • w := by
        intro hvw
        apply hv
        intro i
        have h1 : v i ≤ q ^ m * w i := hvw i
        have h2 : w i ≤ q * u i := hw i
        calc v i ≤ q ^ m * w i := h1
          _ ≤ q ^ m * (q * u i) := Nat.mul_le_mul_left _ h2
          _ = q ^ (m + 1) * u i := by rw [pow_succ]; ring
      rw [if_neg hnv, mul_zero]

lemma dworkInfMatPow_diag {d : ℕ} {q : ℕ} (hq : 2 ≤ q)
    (F : MvPowerSeries (Fin d) (DworkField p)) {m : ℕ} (_hm : 1 ≤ m) (u : Fin d →₀ ℕ) :
    dworkInfMatPow p q F m u u =
      MvPowerSeries.coeff ((q ^ m - 1) • u) (dworkIterSeries p q F m) := by
  have hqm1 : 1 ≤ q ^ m := Nat.one_le_pow m q (by omega)
  have hle : u ≤ q ^ m • u := fun i => by
    simp only [Finsupp.smul_apply, smul_eq_mul]
    exact Nat.le_mul_of_pos_left (u i) hqm1
  rw [dworkInfMatPow_eq p (by omega) F m u u, if_pos hle]
  refine congrArg (fun z : Fin d →₀ ℕ => MvPowerSeries.coeff z (dworkIterSeries p q F m)) ?_
  ext i
  change q ^ m * u i - u i = (q ^ m - 1) * u i
  rw [Nat.sub_mul, one_mul]

/-- Entrywise `p`-adic norm decay of `dworkInfMat q F`. -/
lemma norm_dworkInfMat_le {d : ℕ} {q : ℕ} {c : ℝ} {F : MvPowerSeries (Fin d) (DworkField p)}
    (hF : ∀ u, (letI := dworkNormedField p; ‖MvPowerSeries.coeff u F‖ ≤ (p : ℝ) ^ (-c * (u.degree : ℝ))))
    (u v : Fin d →₀ ℕ) :
    letI := dworkNormedField p
    ‖dworkInfMat p q F u v‖ ≤ (p : ℝ) ^ (-c * ((q : ℝ) * (u.degree : ℝ) - (v.degree : ℝ))) := by
  let _ : NormedField (DworkField p) := dworkNormedField p
  have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.out.pos
  unfold dworkInfMat
  split_ifs with hle
  · refine (hF (q • u - v)).trans_eq ?_
    congr 1
    have hdeg : ((q • u - v).degree : ℝ) = (q : ℝ) * (u.degree : ℝ) - (v.degree : ℝ) := by
      have hadd : (q • u - v) + v = q • u := by
        ext i; simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.smul_apply, smul_eq_mul]
        exact Nat.sub_add_cancel (hle i)
      have hdeg_add : (q • u - v).degree + v.degree = q * u.degree := by
        rw [← map_add, hadd, finsupp_degree_eq_sum, finsupp_degree_eq_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => by simp
      have hcast : (((q • u - v).degree : ℕ) : ℝ) + (v.degree : ℝ) = (q : ℝ) * (u.degree : ℝ) := by
        exact_mod_cast hdeg_add
      linarith
    rw [hdeg]
  · rw [norm_zero]; exact Real.rpow_nonneg hppos.le _

/-- Finite `N`-truncation of `dworkInfMat q F` on `dworkBox d N`. -/
def dworkTruncMat {d : ℕ} (q : ℕ) (F : MvPowerSeries (Fin d) (DworkField p)) (N : ℕ) :
    Matrix (dworkBox d N) (dworkBox d N) (DworkField p) :=
  fun u v => dworkInfMat p q F u.1 v.1

/-- Inductive helper for comparing `dworkInfMatPow` and `dworkTruncMat ^ m`:
for any `m`, `u, v`,
1. `‖(M^m)_{u, v}‖ ≤ p^{-c (q u - v) - c (q - 1) ...}` — more cleanly,
   `‖(M^m)_{u, v}‖ ≤ p^{-c (q |u| - |v|)}` (for `m ≥ 1`), and
2. `‖(M^m)_{u, v} - (M_N^m)_{u, v}‖ ≤ p^{-c ((q - 1) N + |u| - |v|)}`! -/
lemma norm_dworkInfMatPow_le {d : ℕ} {q : ℕ} (hq : 2 ≤ q) {c : ℝ} (hc : 0 < c)
    {F : MvPowerSeries (Fin d) (DworkField p)}
    (hF : ∀ u, (letI := dworkNormedField p; ‖MvPowerSeries.coeff u F‖ ≤ (p : ℝ) ^ (-c * (u.degree : ℝ))))
    (m : ℕ) (u v : Fin d →₀ ℕ) :
    letI := dworkNormedField p
    ‖dworkInfMatPow p q F m u v‖ ≤
      (p : ℝ) ^ (-c * ((if m = 0 then (0 : ℝ) else ((q : ℝ) - 1) * (u.degree : ℝ)) +
        ((u.degree : ℝ) - (v.degree : ℝ)))) := by
  let _ : NormedField (DworkField p) := dworkNormedField p
  have _ : IsUltrametricDist (DworkField p) := dworkField_ultra p
  have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.out.pos
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.out.one_le
  have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  induction m generalizing u v with
  | zero =>
    simp only [dworkInfMatPow, ↓reduceIte, zero_add]
    split_ifs with huv
    · subst huv; simp
    · rw [norm_zero]; exact Real.rpow_nonneg hppos.le _
  | succ m ih =>
    simp only [dworkInfMatPow, Nat.succ_ne_zero, ↓reduceIte]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (Real.rpow_nonneg hppos.le _) fun w _ => ?_
    rw [norm_mul]
    calc ‖dworkInfMat p q F u w‖ * ‖dworkInfMatPow p q F m w v‖
        ≤ (p : ℝ) ^ (-c * ((q : ℝ) * (u.degree : ℝ) - (w.degree : ℝ))) *
          (p : ℝ) ^ (-c * ((if m = 0 then (0 : ℝ) else ((q : ℝ) - 1) * (w.degree : ℝ)) +
            ((w.degree : ℝ) - (v.degree : ℝ)))) :=
          mul_le_mul (norm_dworkInfMat_le p hF u w) (ih w v) (norm_nonneg _)
            (Real.rpow_nonneg hppos.le _)
      _ = (p : ℝ) ^ (-c * ((q : ℝ) * (u.degree : ℝ) - (w.degree : ℝ)) +
            -c * ((if m = 0 then (0 : ℝ) else ((q : ℝ) - 1) * (w.degree : ℝ)) +
              ((w.degree : ℝ) - (v.degree : ℝ)))) := (Real.rpow_add hppos _ _).symm
      _ ≤ (p : ℝ) ^ (-c * (((q : ℝ) - 1) * (u.degree : ℝ) + ((u.degree : ℝ) - (v.degree : ℝ)))) := by
          refine Real.rpow_le_rpow_of_exponent_le hp1 ?_
          have hnn : (0 : ℝ) ≤ if m = 0 then (0 : ℝ) else ((q : ℝ) - 1) * (w.degree : ℝ) := by
            split_ifs
            · exact le_rfl
            · exact mul_nonneg (by linarith) (Nat.cast_nonneg _)
          nlinarith

/-- Key truncation bound: for `u, v ∈ dworkBox d N`,
`‖(M^m)_{u, v} - (M_N^m)_{u, v}‖ ≤ p^{-c * ((q - 1) * N + |u| - |v|)}`! -/
lemma norm_dworkInfMatPow_sub_trunc_le {d : ℕ} {q : ℕ} (hq : 2 ≤ q) {c : ℝ} (hc : 0 < c)
    {F : MvPowerSeries (Fin d) (DworkField p)}
    (hF : ∀ u, (letI := dworkNormedField p; ‖MvPowerSeries.coeff u F‖ ≤ (p : ℝ) ^ (-c * (u.degree : ℝ))))
    (N m : ℕ) (u v : dworkBox d N) :
    letI := dworkNormedField p
    ‖dworkInfMatPow p q F m u.1 v.1 - ((dworkTruncMat p q F N) ^ m) u v‖ ≤
      (p : ℝ) ^ (-c * (((q : ℝ) - 1) * (N : ℝ) + ((u.1.degree : ℝ) - (v.1.degree : ℝ)))) := by
  let _ : NormedField (DworkField p) := dworkNormedField p
  have _ : IsUltrametricDist (DworkField p) := dworkField_ultra p
  have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.out.pos
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.out.one_le
  have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  induction m generalizing u v with
  | zero =>
    simp only [dworkInfMatPow, pow_zero, Matrix.one_apply]
    have heq : (if u.1 = v.1 then (1 : DworkField p) else 0) = (if u = v then 1 else 0) := by
      by_cases h : u = v
      · subst h; simp
      · have h1 : u.1 ≠ v.1 := fun heq => h (Subtype.ext heq)
        simp [h, h1]
    rw [heq, sub_self, norm_zero]
    exact Real.rpow_nonneg hppos.le _
  | succ m ih =>
    rw [pow_succ', Matrix.mul_apply]
    simp only [dworkInfMatPow]
    -- Split the sum over `w ∈ leFinset (q • u.1)` into `w ∈ dworkBox d N` and `w ∉ dworkBox d N`
    let S_in := (leFinset (q • u.1)).filter (fun w => w ∈ dworkBox d N)
    let S_out := (leFinset (q • u.1)).filter (fun w => w ∉ dworkBox d N)
    have hsplit : ∑ w ∈ leFinset (q • u.1), dworkInfMat p q F u.1 w * dworkInfMatPow p q F m w v.1 =
        (∑ w ∈ S_in, dworkInfMat p q F u.1 w * dworkInfMatPow p q F m w v.1) +
        (∑ w ∈ S_out, dworkInfMat p q F u.1 w * dworkInfMatPow p q F m w v.1) := by
      exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm
    have htrunc_eq : ∑ w : dworkBox d N, dworkTruncMat p q F N u w * ((dworkTruncMat p q F N) ^ m) w v =
        ∑ w ∈ S_in, dworkInfMat p q F u.1 w *
          (if hw : w ∈ dworkBox d N then ((dworkTruncMat p q F N) ^ m) ⟨w, hw⟩ v else 0) := by
      -- Only terms with `w.1 ≤ q • u.1` are nonzero in `dworkTruncMat u w`
      have hsub : ∑ w : dworkBox d N, dworkTruncMat p q F N u w * ((dworkTruncMat p q F N) ^ m) w v =
          ∑ w ∈ (Finset.univ : Finset (dworkBox d N)).filter (fun w => w.1 ≤ q • u.1),
            dworkInfMat p q F u.1 w.1 * ((dworkTruncMat p q F N) ^ m) w v := by
        rw [← Finset.sum_subset (Finset.filter_subset (fun w : dworkBox d N => w.1 ≤ q • u.1)
          (Finset.univ : Finset (dworkBox d N)))]
        · rfl
        · intro w _ hnot
          rw [Finset.mem_filter] at hnot
          have hnl : ¬ w.1 ≤ q • u.1 := fun h => hnot ⟨Finset.mem_univ w, h⟩
          simp [dworkTruncMat, dworkInfMat, hnl]
      rw [hsub]
      refine Finset.sum_bij (fun w _ => w.1) ?_ ?_ ?_ ?_
      · intro w hw
        rw [Finset.mem_filter] at hw
        exact Finset.mem_filter.mpr ⟨mem_leFinset.mpr hw.2, w.2⟩
      · intro w₁ _ w₂ _ h; exact Subtype.ext h
      · intro w hw
        rw [Finset.mem_filter, mem_leFinset] at hw
        exact ⟨⟨w, hw.2⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw.1⟩, rfl⟩
      · intro w _; rw [dif_pos w.2]
    rw [hsplit, htrunc_eq, show (∑ w ∈ S_in, dworkInfMat p q F u.1 w * dworkInfMatPow p q F m w v.1) +
        (∑ w ∈ S_out, dworkInfMat p q F u.1 w * dworkInfMatPow p q F m w v.1) -
        ∑ w ∈ S_in, dworkInfMat p q F u.1 w *
          (if hw : w ∈ dworkBox d N then ((dworkTruncMat p q F N) ^ m) ⟨w, hw⟩ v else 0) =
        (∑ w ∈ S_in, dworkInfMat p q F u.1 w *
          (dworkInfMatPow p q F m w v.1 -
            if hw : w ∈ dworkBox d N then ((dworkTruncMat p q F N) ^ m) ⟨w, hw⟩ v else 0)) +
        (∑ w ∈ S_out, dworkInfMat p q F u.1 w * dworkInfMatPow p q F m w v.1) by
          simp_rw [mul_sub, Finset.sum_sub_distrib]; ring]
    refine le_trans (IsUltrametricDist.norm_add_le_max _ _) (max_le ?_ ?_)
    · -- Inside `S_in`: apply IH
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (Real.rpow_nonneg hppos.le _) fun w hw => ?_
      have hw_box : w ∈ dworkBox d N := (Finset.mem_filter.mp hw).2
      rw [dif_pos hw_box, norm_mul]
      calc ‖dworkInfMat p q F u.1 w‖ * ‖dworkInfMatPow p q F m w v.1 - ((dworkTruncMat p q F N) ^ m) ⟨w, hw_box⟩ v‖
          ≤ (p : ℝ) ^ (-c * ((q : ℝ) * (u.1.degree : ℝ) - (w.degree : ℝ))) *
            (p : ℝ) ^ (-c * (((q : ℝ) - 1) * (N : ℝ) + ((w.degree : ℝ) - (v.1.degree : ℝ)))) :=
            mul_le_mul (norm_dworkInfMat_le p hF u.1 w) (ih ⟨w, hw_box⟩ v) (norm_nonneg _)
              (Real.rpow_nonneg hppos.le _)
        _ = (p : ℝ) ^ (-c * ((q : ℝ) * (u.1.degree : ℝ) - (w.degree : ℝ)) +
              -c * (((q : ℝ) - 1) * (N : ℝ) + ((w.degree : ℝ) - (v.1.degree : ℝ)))) :=
            (Real.rpow_add hppos _ _).symm
        _ ≤ (p : ℝ) ^ (-c * (((q : ℝ) - 1) * (N : ℝ) + ((u.1.degree : ℝ) - (v.1.degree : ℝ)))) := by
            refine Real.rpow_le_rpow_of_exponent_le hp1 ?_
            have hq1 : (0 : ℝ) ≤ (q : ℝ) - 1 := by linarith
            have hu_nn : (0 : ℝ) ≤ (u.1.degree : ℝ) := Nat.cast_nonneg _
            have hterm : 0 ≤ c * ((q : ℝ) - 1) * (u.1.degree : ℝ) := by positivity
            linarith
    · -- Outside `S_out`: `w ∉ dworkBox d N` means `w.degree > N`!
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (Real.rpow_nonneg hppos.le _) fun w hw => ?_
      have hw_not : w ∉ dworkBox d N := (Finset.mem_filter.mp hw).2
      have hw_gt : (N : ℝ) ≤ (w.degree : ℝ) := by
        have hlt : N < w.degree := by
          rw [mem_dworkBox] at hw_not; omega
        exact_mod_cast hlt.le
      rcases m with _ | m'
      · -- `m = 0`: `dworkInfMatPow 0 w v.1 = 0` since `w ∉ dworkBox` and `v.1 ∈ dworkBox`!
        have hne : w ≠ v.1 := fun h => hw_not (h ▸ v.2)
        simp only [dworkInfMatPow, if_neg hne, mul_zero, norm_zero]
        exact Real.rpow_nonneg hppos.le _
      · rw [norm_mul]
        have hpow := norm_dworkInfMatPow_le p hq hc hF (m' + 1) w v.1
        simp only [Nat.succ_ne_zero, ↓reduceIte] at hpow
        calc ‖dworkInfMat p q F u.1 w‖ * ‖dworkInfMatPow p q F (m' + 1) w v.1‖
            ≤ (p : ℝ) ^ (-c * ((q : ℝ) * (u.1.degree : ℝ) - (w.degree : ℝ))) *
              (p : ℝ) ^ (-c * (((q : ℝ) - 1) * (w.degree : ℝ) + ((w.degree : ℝ) - (v.1.degree : ℝ)))) :=
              mul_le_mul (norm_dworkInfMat_le p hF u.1 w) hpow (norm_nonneg _)
                (Real.rpow_nonneg hppos.le _)
          _ = (p : ℝ) ^ (-c * ((q : ℝ) * (u.1.degree : ℝ) - (w.degree : ℝ)) +
                -c * (((q : ℝ) - 1) * (w.degree : ℝ) + ((w.degree : ℝ) - (v.1.degree : ℝ)))) :=
              (Real.rpow_add hppos _ _).symm
          _ ≤ (p : ℝ) ^ (-c * (((q : ℝ) - 1) * (N : ℝ) + ((u.1.degree : ℝ) - (v.1.degree : ℝ)))) := by
              refine Real.rpow_le_rpow_of_exponent_le hp1 ?_
              have hq1 : (0 : ℝ) ≤ (q : ℝ) - 1 := by linarith
              have hu_nn : (0 : ℝ) ≤ (u.1.degree : ℝ) := Nat.cast_nonneg _
              have hwN : (0 : ℝ) ≤ (w.degree : ℝ) - (N : ℝ) := by linarith
              have hterm1 : 0 ≤ c * ((q : ℝ) - 1) * (u.1.degree : ℝ) := by positivity
              have hterm2 : 0 ≤ c * ((q : ℝ) - 1) * ((w.degree : ℝ) - (N : ℝ)) := by positivity
              linarith

/-- Infinite nuclear trace `Tr(M^m) = ∑'_u (M^m)_{u, u}` of the Dwork operator. -/
def dworkInfTrace {d : ℕ} (q : ℕ) (F : MvPowerSeries (Fin d) (DworkField p)) (m : ℕ) :
    DworkField p :=
  letI := dworkNormedField p
  ∑' u : Fin d →₀ ℕ, dworkInfMatPow p q F m u u

lemma dworkInfTrace_summable_norm {d : ℕ} {q : ℕ} (hq : 2 ≤ q) {c : ℝ} (hc : 0 < c)
    {F : MvPowerSeries (Fin d) (DworkField p)}
    (hF : ∀ u, (letI := dworkNormedField p; ‖MvPowerSeries.coeff u F‖ ≤ (p : ℝ) ^ (-c * (u.degree : ℝ))))
    {m : ℕ} (hm : 1 ≤ m) :
    letI := dworkNormedField p
    Summable fun u : Fin d →₀ ℕ => ‖dworkInfMatPow p q F m u u‖ := by
  let _ : NormedField (DworkField p) := dworkNormedField p
  have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hc' : 0 < c * ((q : ℝ) - 1) := mul_pos hc (by linarith)
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun u => ?_)
    (summable_rpow_neg_degree p hc')
  have h := norm_dworkInfMatPow_le p hq hc hF m u u
  rw [if_neg (by omega : m ≠ 0)] at h
  refine h.trans_eq ?_
  congr 1; ring

/-- **Ultrametric Trace Truncation Convergence**:
for every `m ≥ 1` and `N : ℕ`,
`‖dworkInfTrace p q F m - ((dworkTruncMat p q F N) ^ m).trace‖ ≤ p^{-c (q - 1) N}`! -/
theorem norm_dworkInfTrace_sub_trunc_le {d : ℕ} {q : ℕ} (hq : 2 ≤ q) {c : ℝ} (hc : 0 < c)
    {F : MvPowerSeries (Fin d) (DworkField p)}
    (hF : ∀ u, (letI := dworkNormedField p; ‖MvPowerSeries.coeff u F‖ ≤ (p : ℝ) ^ (-c * (u.degree : ℝ))))
    {m : ℕ} (hm : 1 ≤ m) (N : ℕ) :
    letI := dworkNormedField p
    ‖dworkInfTrace p q F m - ((dworkTruncMat p q F N) ^ m).trace‖ ≤
      (p : ℝ) ^ (-c * (((q : ℝ) - 1) * (N : ℝ))) := by
  let _ : NormedField (DworkField p) := dworkNormedField p
  have _ : IsUltrametricDist (DworkField p) := dworkField_ultra p
  have _ : CompleteSpace (DworkField p) := dworkField_complete p
  have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.out.pos
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.out.one_le
  have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hsumm : Summable fun u : Fin d →₀ ℕ => dworkInfMatPow p q F m u u :=
    (dworkInfTrace_summable_norm p hq hc hF hm).of_norm
  have hhead : Summable fun u : Fin d →₀ ℕ => if u ∈ dworkBox d N then dworkInfMatPow p q F m u u else 0 :=
    summable_of_ne_finset_zero (s := dworkBox d N) fun u hu => if_neg hu
  have htail : Summable fun u : Fin d →₀ ℕ => if u ∉ dworkBox d N then dworkInfMatPow p q F m u u else 0 :=
    (hsumm.indicator {u | u ∉ dworkBox d N}).congr fun u => by simp [Set.indicator]
  have hsplit : dworkInfTrace p q F m =
      (∑ u ∈ dworkBox d N, dworkInfMatPow p q F m u u) +
      (∑' u : Fin d →₀ ℕ, if u ∉ dworkBox d N then dworkInfMatPow p q F m u u else 0) := by
    unfold dworkInfTrace
    have hadd := hhead.tsum_add htail
    have heq : (fun u : Fin d →₀ ℕ =>
        (if u ∈ dworkBox d N then dworkInfMatPow p q F m u u else 0) +
        (if u ∉ dworkBox d N then dworkInfMatPow p q F m u u else 0)) =
        fun u => dworkInfMatPow p q F m u u := by
      ext u; by_cases hu : u ∈ dworkBox d N <;> simp [hu]
    rw [heq] at hadd
    rw [hadd]
    congr 1
    rw [tsum_eq_sum (s := dworkBox d N) (fun u hu => if_neg hu)]
    exact Finset.sum_congr rfl fun u hu => if_pos hu
  have htrace_eq : ((dworkTruncMat p q F N) ^ m).trace =
      ∑ u ∈ dworkBox d N, if hu : u ∈ dworkBox d N then ((dworkTruncMat p q F N) ^ m) ⟨u, hu⟩ ⟨u, hu⟩ else 0 := by
    rw [Matrix.trace]
    simp only [Matrix.diag_apply]
    symm
    refine Finset.sum_bij (fun (u : Fin d →₀ ℕ) hu => (⟨u, hu⟩ : dworkBox d N))
      (fun _ _ => Finset.mem_univ _)
      (fun _ _ _ _ h => congrArg Subtype.val h)
      (fun u _ => ⟨u.1, u.2, rfl⟩)
      (fun u hu => by rw [dif_pos hu])
  rw [hsplit, htrace_eq,
    show (∑ u ∈ dworkBox d N, dworkInfMatPow p q F m u u) +
        (∑' u : Fin d →₀ ℕ, if u ∉ dworkBox d N then dworkInfMatPow p q F m u u else 0) -
        (∑ u ∈ dworkBox d N, if hu : u ∈ dworkBox d N then ((dworkTruncMat p q F N) ^ m) ⟨u, hu⟩ ⟨u, hu⟩ else 0) =
      (∑ u ∈ dworkBox d N, (dworkInfMatPow p q F m u u -
        if hu : u ∈ dworkBox d N then ((dworkTruncMat p q F N) ^ m) ⟨u, hu⟩ ⟨u, hu⟩ else 0)) +
      (∑' u : Fin d →₀ ℕ, if u ∉ dworkBox d N then dworkInfMatPow p q F m u u else 0) by
        rw [Finset.sum_sub_distrib]; ring]
  refine le_trans (IsUltrametricDist.norm_add_le_max _ _) (max_le ?_ ?_)
  · refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (Real.rpow_nonneg hppos.le _) fun u hu => ?_
    rw [dif_pos hu]
    have hbd := norm_dworkInfMatPow_sub_trunc_le p hq hc hF N m ⟨u, hu⟩ ⟨u, hu⟩
    simpa [sub_self, add_zero] using hbd
  · refine ultrametric_norm_tsum_le (Real.rpow_nonneg hppos.le _) htail fun u => ?_
    by_cases hu : u ∉ dworkBox d N
    · rw [if_pos hu]
      have hbd := norm_dworkInfMatPow_le p hq hc hF m u u
      rw [if_neg (by omega : m ≠ 0)] at hbd
      have hgt : (N : ℝ) ≤ (u.degree : ℝ) := by
        rw [mem_dworkBox] at hu
        exact_mod_cast (show N ≤ u.degree by omega)
      refine hbd.trans ?_
      refine Real.rpow_le_rpow_of_exponent_le hp1 ?_
      have hq1 : (0 : ℝ) ≤ (q : ℝ) - 1 := by linarith
      have hdiff : (0 : ℝ) ≤ (u.degree : ℝ) - (N : ℝ) := by linarith
      have hterm : 0 ≤ c * ((q : ℝ) - 1) * ((u.degree : ℝ) - (N : ℝ)) := by positivity
      linarith
    · rw [if_neg hu, norm_zero]; exact Real.rpow_nonneg hppos.le _

/-! ### Multiplicative Character Orthogonality on `𝔽_{p^s}ˣ` & Dwork's Trace Formula -/

/-- Multiplicative orthogonality of Teichmüller lifts on `finFieldUnits p s`:
`∑_{x ∈ 𝔽_{p^s}ˣ} (teich p x)^k = if (p^s - 1) ∣ k then p^s - 1 else 0`. -/
theorem sum_finFieldUnits_teich_pow {s : ℕ} (hs : 1 ≤ s) (k : ℕ) :
    ∑ x ∈ finFieldUnits p s, (teich p x) ^ k =
      if (p ^ s - 1) ∣ k then ((p ^ s - 1 : ℕ) : DworkField p) else 0 := by
  have hqs_gt : 1 < p ^ s := one_lt_pow₀ hp.out.one_lt (by omega)
  have hqs_sub_pos : 0 < p ^ s - 1 := by omega
  split_ifs with hdvd
  · -- `(p^s - 1) ∣ k`: every `x ∈ finFieldUnits p s` has `x^{p^s - 1} = 1`, hence `(teich x)^k = 1`
    have hterm : ∀ x ∈ finFieldUnits p s, (teich p x) ^ k = 1 := by
      intro x hx
      rw [mem_finFieldUnits p hs] at hx
      have hxp : x ^ (p ^ s - 1) = 1 := by
        have hmul : x * x ^ (p ^ s - 1) = x * 1 := by
          rw [← pow_succ', Nat.sub_add_cancel (by omega), mul_one, hx.2]
        exact mul_left_cancel₀ hx.1 hmul
      obtain ⟨m, rfl⟩ := hdvd
      rw [← map_pow, pow_mul, hxp, one_pow, map_one]
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, card_finFieldUnits p hs, nsmul_eq_mul, mul_one]
  · -- `¬ (p^s - 1) ∣ k`: there exists `g ∈ finFieldUnits p s` with `g^k ≠ 1`!
    have hex_g : ∃ g ∈ finFieldUnits p s, g ^ k ≠ 1 := by
      -- Because `X^{k % (p^s - 1)} - 1` has at most `k % (p^s - 1) < p^s - 1` roots in `kb p`!
      set r := k % (p ^ s - 1)
      have hr_pos : 0 < r := Nat.pos_of_ne_zero (fun h0 => hdvd (Nat.dvd_of_mod_eq_zero h0))
      have hr_lt : r < p ^ s - 1 := Nat.mod_lt k hqs_sub_pos
      let P : Polynomial (kb p) := Polynomial.X ^ r - 1
      have hPne : P ≠ 0 := by
        intro h0
        have hc := congrArg (fun Q : Polynomial (kb p) => Q.coeff r) h0
        simp [P, Polynomial.coeff_one, hr_pos.ne'] at hc
      have hPdeg : P.natDegree = r := by
        unfold P
        rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt]
        · exact Polynomial.natDegree_X_pow r
        · rw [Polynomial.natDegree_X_pow, Polynomial.natDegree_one]; exact hr_pos
      have hlt_card : P.roots.toFinset.card < (finFieldUnits p s).card := by
        calc P.roots.toFinset.card ≤ P.roots.card := Multiset.toFinset_card_le _
          _ ≤ P.natDegree := Polynomial.card_roots' P
          _ = r := hPdeg
          _ < p ^ s - 1 := hr_lt
          _ = (finFieldUnits p s).card := (card_finFieldUnits p hs).symm
      obtain ⟨g, hg_mem, hg_not⟩ : ∃ g ∈ finFieldUnits p s, g ∉ P.roots.toFinset := by
        by_contra hall
        push Not at hall
        have := Finset.card_le_card hall
        omega
      refine ⟨g, hg_mem, fun hgk => ?_⟩
      apply hg_not
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hPne]
      simp only [P, Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow,
        Polynomial.eval_X, Polynomial.eval_one, sub_eq_zero]
      have hg_u := (mem_finFieldUnits p hs).mp hg_mem
      have hgp : g ^ (p ^ s - 1) = 1 := by
        have hmul : g * g ^ (p ^ s - 1) = g * 1 := by
          rw [← pow_succ', Nat.sub_add_cancel (by omega), mul_one, hg_u.2]
        exact mul_left_cancel₀ hg_u.1 hmul
      have hdiv_mod : k = (p ^ s - 1) * (k / (p ^ s - 1)) + r := (Nat.div_add_mod k (p ^ s - 1)).symm
      rw [hdiv_mod, pow_add, pow_mul, hgp, one_pow, one_mul] at hgk
      exact hgk
    obtain ⟨g, hg_mem, hgk_ne⟩ := hex_g
    have hg_u := (mem_finFieldUnits p hs).mp hg_mem
    have htg_ne : (teich p g) ^ k ≠ 1 := by
      rw [← map_pow]
      intro h1
      exact hgk_ne (teich_injective p (h1.trans (map_one _).symm))
    have hshift : ∑ x ∈ finFieldUnits p s, (teich p x) ^ k =
        ∑ x ∈ finFieldUnits p s, (teich p (g * x)) ^ k := by
      symm
      refine Finset.sum_bij (fun x _ => g * x) ?_ ?_ ?_ ?_
      · intro x hx
        rw [mem_finFieldUnits p hs] at hx ⊢
        exact ⟨mul_ne_zero hg_u.1 hx.1, by rw [mul_pow, hg_u.2, hx.2]⟩
      · intro x₁ _ x₂ _ h; exact mul_left_cancel₀ hg_u.1 h
      · intro z hz
        rw [mem_finFieldUnits p hs] at hz
        refine ⟨g⁻¹ * z, ?_, by field_simp [hg_u.1]⟩
        rw [mem_finFieldUnits p hs]
        exact ⟨mul_ne_zero (inv_ne_zero hg_u.1) hz.1, by rw [mul_pow, inv_pow, hg_u.2, hz.2]⟩
      · intro _ _; rfl
    have hmul : ∑ x ∈ finFieldUnits p s, (teich p (g * x)) ^ k =
        (teich p g) ^ k * ∑ x ∈ finFieldUnits p s, (teich p x) ^ k := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => by rw [map_mul, mul_pow]
    have heq : ((teich p g) ^ k - 1) * ∑ x ∈ finFieldUnits p s, (teich p x) ^ k = 0 := by
      rw [sub_mul, one_mul, ← hmul, ← hshift, sub_self]
    exact (mul_eq_zero.mp heq).resolve_left (sub_ne_zero.mpr htg_ne)

/-- Dwork splitting series `F_r(X) = ∏_{j < r} ∏_{w ∈ G.support} θ((teich (ι (coeff w G)))^{p^j} X^{p^j w})`
associated to a polynomial `G : MvPolynomial (Fin d) (kb p)` whose coefficients lie in `𝔽_{p^r}`
and whose constant term is `0` (`∀ w ∈ G.support, w ≠ 0`). -/
def dworkPolySeries {d : ℕ} (r : ℕ) (G : MvPolynomial (Fin d) (kb p)) :
    MvPowerSeries (Fin d) (DworkField p) :=
  ∏ j ∈ Finset.range r,
    mvSubstPow p (p ^ j)
      (∏ w ∈ G.support, mvThetaMonom p ((teich p (G.coeff w)) ^ (p ^ j)) w)

/-- Positive decay constant `c_Dwork(p, r, D) = (p - 1) / (p^2 * D * p^r) > 0` for `dworkPolySeries`. -/
def dworkDecayConst (r D : ℕ) : ℝ :=
  ((p : ℝ) - 1) / ((p : ℝ) ^ 2 * (D : ℝ) * (p : ℝ) ^ r)

lemma dworkDecayConst_pos (r : ℕ) {D : ℕ} (hD : 0 < D) : 0 < dworkDecayConst p r D := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.out.two_le
  have hppos : (0 : ℝ) < (p : ℝ) := by linarith
  have hpm1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hDpos : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
  unfold dworkDecayConst
  positivity

/-- Uniform exponential coefficient decay of `dworkPolySeries p r G`:
for `D = max 1 (G.totalDegree)` and `c = dworkDecayConst p r D > 0`,
`‖coeff u (dworkPolySeries p r G)‖ ≤ p^{-c * u.degree}` for all `u : Fin d →₀ ℕ`. -/
theorem norm_coeff_dworkPolySeries_le {d : ℕ} (r : ℕ) (G : MvPolynomial (Fin d) (kb p))
    (hG0 : ∀ w ∈ G.support, w ≠ 0) {D : ℕ} (hDpos : 0 < D)
    (hD : ∀ w ∈ G.support, w.degree ≤ D) (u : Fin d →₀ ℕ) :
    letI := dworkNormedField p
    ‖MvPowerSeries.coeff u (dworkPolySeries p r G)‖ ≤
      (p : ℝ) ^ (-dworkDecayConst p r D * (u.degree : ℝ)) := by
  let _ : NormedField (DworkField p) := dworkNormedField p
  have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.out.pos
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.out.one_le
  unfold dworkPolySeries
  refine norm_coeff_mvProd_le p (Finset.range r) _ (fun j hj v => ?_) u
  rw [Finset.mem_range] at hj
  set c₀ : ℝ := ((p : ℝ) - 1) / ((p : ℝ) ^ 2 * (D : ℝ))
  have hinner : ∀ a : Fin d →₀ ℕ,
      ‖MvPowerSeries.coeff a (∏ w ∈ G.support, mvThetaMonom p ((teich p (G.coeff w)) ^ (p ^ j)) w)‖ ≤
        (p : ℝ) ^ (-c₀ * (a.degree : ℝ)) := by
    intro a
    refine norm_coeff_mvProd_le p G.support _ (fun w hw b => ?_) a
    have hnorm_c : ‖(teich p (G.coeff w)) ^ (p ^ j)‖ ≤ 1 := by
      rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) (teich_norm_le_one p _)
    simpa [c₀, neg_mul] using norm_coeff_mvThetaMonom_le p hnorm_c (hG0 w hw) (hD w hw) hDpos b
  have hsubst := norm_coeff_mvSubstPow_le p (pow_pos hp.out.pos j) hinner v
  refine hsubst.trans ?_
  refine Real.rpow_le_rpow_of_exponent_le hp1 ?_
  have hjp : (p : ℝ) ^ j ≤ (p : ℝ) ^ r := by
    exact_mod_cast Nat.pow_le_pow_right hp.out.pos (le_of_lt hj)
  have hc0_nn : 0 ≤ c₀ := by
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.out.two_le
    have hD0 : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hDpos
    dsimp only [c₀]; positivity
  have hdiv_le : dworkDecayConst p r D ≤ c₀ / ((p ^ j : ℕ) : ℝ) := by
    have heq : dworkDecayConst p r D = c₀ / (p : ℝ) ^ r := by
      unfold dworkDecayConst; dsimp only [c₀]; ring
    rw [heq, Nat.cast_pow]
    exact div_le_div_of_nonneg_left hc0_nn (pow_pos hppos j) hjp
  have hdeg_nn : (0 : ℝ) ≤ (v.degree : ℝ) := Nat.cast_nonneg _
  nlinarith

/-- Pointwise evaluation of `dworkIterSeries (p^r) (dworkPolySeries p r G) m` at Teichmüller lifts
recovers `dworkChar p (r * m) (G(x))`! -/
theorem mvEval_dworkIterSeries_eq_dworkChar {d : ℕ} {r m : ℕ} (hr : 1 ≤ r) (hm : 1 ≤ m)
    (G : MvPolynomial (Fin d) (kb p))
    (hG0 : ∀ w ∈ G.support, w ≠ 0)
    (hGcoeff : ∀ w ∈ G.support, (G.coeff w) ^ (p ^ r) = G.coeff w)
    (x : Fin d → kb p) (hx : ∀ i, x i ∈ finFieldSet p (r * m)) :
    mvEval p (fun i => teich p (x i))
        (dworkIterSeries p (p ^ r) (dworkPolySeries p r G) m) =
      dworkChar p (r * m) (MvPolynomial.eval x G) := by
  let _ : NormedField (DworkField p) := dworkNormedField p
  have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.out.pos
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.out.one_le
  set D : ℕ := max 1 (G.totalDegree)
  have hDpos : 0 < D := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hD : ∀ w ∈ G.support, w.degree ≤ D := fun w hw => by
    have hle : w.degree ≤ G.totalDegree := by
      rw [MvPolynomial.totalDegree, finsupp_degree_eq_sum]
      exact Finset.le_sup (f := fun s : Fin d →₀ ℕ => s.sum fun _ e => e) hw
        |> le_trans (by
          rw [Finsupp.sum]
          exact (Finset.sum_subset (Finset.subset_univ _) fun i _ hi =>
            Finsupp.notMem_support_iff.mp hi).symm.le)
    exact le_trans hle (le_max_right _ _)
  set c := dworkDecayConst p r D
  have hc : 0 < c := dworkDecayConst_pos p r hDpos
  have hF_decay := norm_coeff_dworkPolySeries_le p r G hG0 hDpos hD
  have ht_le : ∀ i : Fin d, ‖teich p (x i)‖ ≤ 1 := fun i => teich_norm_le_one p (x i)
  -- Decay of each factor `mvSubstPow ((p^r)^l) (dworkPolySeries p r G)` with uniform `c_m = c / (p^r)^m`
  set cm : ℝ := c / ((p ^ r) ^ m : ℝ)
  have hcm : 0 < cm := div_pos hc (pow_pos (pow_pos hppos r) m)
  have hfactor_decay : ∀ l ∈ Finset.range m, ∀ u : Fin d →₀ ℕ,
      ‖MvPowerSeries.coeff u (mvSubstPow p ((p ^ r) ^ l) (dworkPolySeries p r G))‖ ≤
        (p : ℝ) ^ (-cm * (u.degree : ℝ)) := by
    intro l hl u
    rw [Finset.mem_range] at hl
    have hsub := norm_coeff_mvSubstPow_le p (pow_pos (pow_pos hp.out.pos r) l) hF_decay u
    refine hsub.trans ?_
    refine Real.rpow_le_rpow_of_exponent_le hp1 ?_
    have hle_pow : (((p ^ r) ^ l : ℕ) : ℝ) ≤ ((p ^ r) ^ m : ℝ) := by
      exact_mod_cast Nat.pow_le_pow_right (pow_pos hp.out.pos r) (le_of_lt hl)
    have hdiv : cm ≤ c / (((p ^ r) ^ l : ℕ) : ℝ) :=
      div_le_div_of_nonneg_left hc.le (by exact_mod_cast pow_pos (pow_pos hp.out.pos r) l) hle_pow
    nlinarith [Nat.cast_nonneg (α := ℝ) u.degree]
  -- Evaluate `dworkIterSeries` as product over `l < m`, then `j < r`, then `w ∈ G.support`
  unfold dworkIterSeries
  rw [mvEval_prod_of_decay p (Finset.range m) hcm _ hfactor_decay ht_le]
  have hstep_l : ∀ l ∈ Finset.range m,
      mvEval p (fun i => teich p (x i)) (mvSubstPow p ((p ^ r) ^ l) (dworkPolySeries p r G)) =
        ∏ j ∈ Finset.range r, ∏ w ∈ G.support,
          evalTheta p ((teich p (G.coeff w * ∏ i : Fin d, (x i) ^ (w i))) ^ (p ^ (r * l + j))) := by
    intro l _
    rw [mvEval_mvSubstPow p (pow_pos (pow_pos hp.out.pos r) l)]
    unfold dworkPolySeries
    have ht_pow : ∀ i : Fin d, ‖(teich p (x i)) ^ ((p ^ r) ^ l)‖ ≤ 1 := fun i => by
      rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) (ht_le i)
    -- Uniform decay for `j < r`
    have hj_decay : ∀ j ∈ Finset.range r, ∀ u : Fin d →₀ ℕ,
        ‖MvPowerSeries.coeff u (mvSubstPow p (p ^ j)
          (∏ w ∈ G.support, mvThetaMonom p ((teich p (G.coeff w)) ^ (p ^ j)) w))‖ ≤
          (p : ℝ) ^ (-c * (u.degree : ℝ)) := by
      intro j hj u
      rw [Finset.mem_range] at hj
      set c₀ : ℝ := ((p : ℝ) - 1) / ((p : ℝ) ^ 2 * (D : ℝ))
      have hinner : ∀ a : Fin d →₀ ℕ,
          ‖MvPowerSeries.coeff a (∏ w ∈ G.support, mvThetaMonom p ((teich p (G.coeff w)) ^ (p ^ j)) w)‖ ≤
            (p : ℝ) ^ (-c₀ * (a.degree : ℝ)) := fun a =>
        norm_coeff_mvProd_le p G.support _ (fun w hw b => by
          have hnc : ‖(teich p (G.coeff w)) ^ (p ^ j)‖ ≤ 1 := by
            rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) (teich_norm_le_one p _)
          simpa [c₀, neg_mul] using norm_coeff_mvThetaMonom_le p hnc (hG0 w hw) (hD w hw) hDpos b) a
      have hsub := norm_coeff_mvSubstPow_le p (pow_pos hp.out.pos j) hinner u
      refine hsub.trans ?_
      refine Real.rpow_le_rpow_of_exponent_le hp1 ?_
      have hjp : (p : ℝ) ^ j ≤ (p : ℝ) ^ r := by
        exact_mod_cast Nat.pow_le_pow_right hp.out.pos (le_of_lt hj)
      have hc0_nn : 0 ≤ c₀ := by
        have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.out.two_le
        have hD0 : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hDpos
        dsimp only [c₀]; positivity
      have hdiv : c ≤ c₀ / ((p ^ j : ℕ) : ℝ) := by
        have heq : c = c₀ / (p : ℝ) ^ r := by unfold c dworkDecayConst; dsimp only [c₀]; ring
        rw [heq, Nat.cast_pow]
        exact div_le_div_of_nonneg_left hc0_nn (pow_pos hppos j) hjp
      nlinarith [Nat.cast_nonneg (α := ℝ) u.degree]
    rw [mvEval_prod_of_decay p (Finset.range r) hc _ hj_decay ht_pow]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [mvEval_mvSubstPow p (pow_pos hp.out.pos j)]
    set c₀ : ℝ := ((p : ℝ) - 1) / ((p : ℝ) ^ 2 * (D : ℝ))
    have hc0 : 0 < c₀ := by
      have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.out.two_le
      have hpm1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
      have hD0 : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hDpos
      dsimp only [c₀]; positivity
    have ht_pow2 : ∀ i : Fin d, ‖((teich p (x i)) ^ ((p ^ r) ^ l)) ^ (p ^ j)‖ ≤ 1 := fun i => by
      rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) (ht_pow i)
    rw [mvEval_prod_of_decay p G.support hc0 _ (fun w hw a => by
      have hnc : ‖(teich p (G.coeff w)) ^ (p ^ j)‖ ≤ 1 := by
        rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) (teich_norm_le_one p _)
      simpa [c₀, neg_mul] using norm_coeff_mvThetaMonom_le p hnc (hG0 w hw) (hD w hw) hDpos a) ht_pow2]
    refine Finset.prod_congr rfl fun w hw => ?_
    rw [mvEval_mvThetaMonom p _ (hG0 w hw)]
    congr 1
    -- Show `teich(a_w)^{p^j} * ∏_i ((teich(x_i)^{(p^r)^l})^{p^j})^{w i} = teich(a_w * ∏ x_i^{w i})^{p^{r*l+j}}`
    have haw_pow : ∀ k : ℕ, (teich p (G.coeff w)) ^ ((p ^ r) ^ k) = teich p (G.coeff w) := fun k => by
      induction k with
      | zero => simp
      | succ k ihk =>
        rw [pow_succ, pow_mul, ihk, ← map_pow, hGcoeff w hw]
    have hl_pow : (p ^ r) ^ l * p ^ j = p ^ (r * l + j) := by
      rw [← pow_mul, ← pow_add]
    rw [map_mul, map_prod, mul_pow, ← Finset.prod_pow, ← hl_pow, pow_mul, haw_pow l]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [map_pow, ← pow_mul, ← pow_mul, ← pow_mul, ← pow_mul, mul_comm (w i), mul_assoc]
  rw [Finset.prod_congr rfl hstep_l]
  -- Swap `∏ w ∈ G.support` to the outside and collapse `∏_{l < m} ∏_{j < r}` into `∏_{k < r * m}`!
  have hswap : ∏ l ∈ Finset.range m, ∏ j ∈ Finset.range r, ∏ w ∈ G.support,
        evalTheta p ((teich p (G.coeff w * ∏ i : Fin d, (x i) ^ (w i))) ^ (p ^ (r * l + j))) =
      ∏ w ∈ G.support, ∏ l ∈ Finset.range m, ∏ j ∈ Finset.range r,
        evalTheta p ((teich p (G.coeff w * ∏ i : Fin d, (x i) ^ (w i))) ^ (p ^ (r * l + j))) := by
    simp_rw [Finset.prod_comm (s := Finset.range r) (t := G.support)]
    rw [Finset.prod_comm]
  rw [hswap]
  have hcollapse : ∀ w ∈ G.support,
      ∏ l ∈ Finset.range m, ∏ j ∈ Finset.range r,
        evalTheta p ((teich p (G.coeff w * ∏ i : Fin d, (x i) ^ (w i))) ^ (p ^ (r * l + j))) =
      dworkChar p (r * m) (G.coeff w * ∏ i : Fin d, (x i) ^ (w i)) := by
    intro w _
    unfold dworkChar
    rw [← Finset.prod_product']
    refine Finset.prod_bij (fun (lj : ℕ × ℕ) _ => r * lj.1 + lj.2) ?_ ?_ ?_ ?_
    · intro lj hlj
      rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hlj
      rw [Finset.mem_range]
      nlinarith
    · intro a ha b hb heq
      rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at ha hb
      have hdiv : a.1 = b.1 := by
        have h1 : (r * a.1 + a.2) / r = a.1 := by
          rw [Nat.mul_add_div (by omega), Nat.div_eq_of_lt ha.2, add_zero]
        have h2 : (r * b.1 + b.2) / r = b.1 := by
          rw [Nat.mul_add_div (by omega), Nat.div_eq_of_lt hb.2, add_zero]
        rw [← h1, ← h2, heq]
      ext
      · exact hdiv
      · rw [hdiv] at heq; omega
    · intro k hk
      rw [Finset.mem_range] at hk
      refine ⟨(k / r, k % r), ?_, Nat.div_add_mod k r⟩
      rw [Finset.mem_product, Finset.mem_range, Finset.mem_range]
      exact ⟨Nat.div_lt_of_lt_mul hk, Nat.mod_lt k (by omega)⟩
    · intro _ _; rfl
  rw [Finset.prod_congr rfl hcollapse]
  -- Now use additivity of `dworkChar p (r * m)` on `finFieldSet p (r * m)`!
  have hrm : 1 ≤ r * m := Nat.mul_pos hr hm
  have hterm_mem : ∀ w ∈ G.support, G.coeff w * ∏ i : Fin d, (x i) ^ (w i) ∈ finFieldSet p (r * m) := by
    intro w hw
    have ha_mem : G.coeff w ∈ finFieldSet p (r * m) := by
      rw [mem_finFieldSet p hrm]
      have hpow_rm : ∀ k : ℕ, (G.coeff w) ^ (p ^ (r * k)) = G.coeff w := fun k => by
        induction k with
        | zero => simp
        | succ k ihk =>
          rw [Nat.mul_succ, pow_add, pow_mul, ihk, hGcoeff w hw]
      exact hpow_rm m
    refine mul_mem_finFieldSet p hrm ha_mem ?_
    rw [mem_finFieldSet p hrm, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← pow_mul, mul_comm, pow_mul, (mem_finFieldSet p hrm).mp (hx i)]
  have hsum_mem : ∀ t : Finset (Fin d →₀ ℕ),
      (∀ w ∈ t, G.coeff w * ∏ i : Fin d, (x i) ^ (w i) ∈ finFieldSet p (r * m)) →
      ∑ w ∈ t, G.coeff w * ∏ i : Fin d, (x i) ^ (w i) ∈ finFieldSet p (r * m) := by
    intro t
    induction t using Finset.induction_on with
    | empty => intro _; simpa using zero_mem_finFieldSet p hrm
    | insert b t hb iht =>
      intro ht
      rw [Finset.sum_insert hb]
      exact add_mem_finFieldSet p hrm (ht b (Finset.mem_insert_self b t))
        (iht fun w hw => ht w (Finset.mem_insert_of_mem hw))
  have hprod_char : ∀ s : Finset (Fin d →₀ ℕ),
      (∀ w ∈ s, G.coeff w * ∏ i : Fin d, (x i) ^ (w i) ∈ finFieldSet p (r * m)) →
      ∏ w ∈ s, dworkChar p (r * m) (G.coeff w * ∏ i : Fin d, (x i) ^ (w i)) =
        dworkChar p (r * m) (∑ w ∈ s, G.coeff w * ∏ i : Fin d, (x i) ^ (w i)) := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro _; simp [dworkChar_zero]
    | insert a s ha ih =>
      intro hs
      rw [Finset.prod_insert ha, Finset.sum_insert ha,
        ih fun w hw => hs w (Finset.mem_insert_of_mem hw)]
      have ha_m := hs a (Finset.mem_insert_self a s)
      have hs_m := hsum_mem s fun w hw => hs w (Finset.mem_insert_of_mem hw)
      exact (dworkChar_add p hrm ((mem_finFieldSet p hrm).mp ha_m)
        ((mem_finFieldSet p hrm).mp hs_m)).symm
  rw [hprod_char G.support hterm_mem]
  congr 1
  rw [MvPolynomial.eval_eq']

/-- **DWORK'S TRACE FORMULA (UNCONDITIONAL, ARBITRARY DIMENSION `d`, ARBITRARY `q = p^r`)**:
For any `r ≥ 1`, `m ≥ 1`, and polynomial `G : MvPolynomial (Fin d) (kb p)` with zero constant term
and coefficients in `𝔽_{p^r}`,
`((p^r)^m - 1)^d * Tr(M^m) = ∑_{x ∈ (𝔽_{(p^r)^m}ˣ)^d} dworkChar p (r * m) (G(x))`! -/
theorem dwork_trace_formula {d : ℕ} {r m : ℕ} (hr : 1 ≤ r) (hm : 1 ≤ m)
    (G : MvPolynomial (Fin d) (kb p))
    (hG0 : ∀ w ∈ G.support, w ≠ 0)
    (hGcoeff : ∀ w ∈ G.support, (G.coeff w) ^ (p ^ r) = G.coeff w) :
    ((((p ^ r) ^ m - 1 : ℕ) : DworkField p) ^ d) *
        dworkInfTrace p (p ^ r) (dworkPolySeries p r G) m =
      ∑ x ∈ Fintype.piFinset (fun _ : Fin d => finFieldUnits p (r * m)),
        dworkChar p (r * m) (MvPolynomial.eval x G) := by
  let _ : NormedField (DworkField p) := dworkNormedField p
  have _ : CompleteSpace (DworkField p) := dworkField_complete p
  have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.out.pos
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.out.one_le
  have hrm : 1 ≤ r * m := Nat.mul_pos hr hm
  have hq2 : 2 ≤ p ^ r := by
    have h1 : p ^ 1 ≤ p ^ r := Nat.pow_le_pow_right hp.out.pos hr
    have h2 : 2 ≤ p := hp.out.two_le
    rw [pow_one] at h1; omega
  have hqrm : (p ^ r) ^ m = p ^ (r * m) := (pow_mul p r m).symm
  set H := dworkIterSeries p (p ^ r) (dworkPolySeries p r G) m
  -- Step 1: Decay of `H` so `∑'_w coeff w H * ∏ (teich (x i))^{w i}` is summable for every `x`
  set D : ℕ := max 1 (G.totalDegree)
  have hDpos : 0 < D := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hD : ∀ w ∈ G.support, w.degree ≤ D := fun w hw => by
    have hle : w.degree ≤ G.totalDegree := by
      rw [MvPolynomial.totalDegree, finsupp_degree_eq_sum]
      exact Finset.le_sup (f := fun s : Fin d →₀ ℕ => s.sum fun _ e => e) hw
        |> le_trans (by
          rw [Finsupp.sum]
          exact (Finset.sum_subset (Finset.subset_univ _) fun i _ hi =>
            Finsupp.notMem_support_iff.mp hi).symm.le)
    exact le_trans hle (le_max_right _ _)
  set c := dworkDecayConst p r D
  have hc : 0 < c := dworkDecayConst_pos p r hDpos
  set cm : ℝ := c / ((p ^ r) ^ m : ℝ)
  have hcm : 0 < cm := div_pos hc (pow_pos (pow_pos hppos r) m)
  have hH_decay : ∀ u : Fin d →₀ ℕ,
      ‖MvPowerSeries.coeff u H‖ ≤ (p : ℝ) ^ (-cm * (u.degree : ℝ)) := by
    unfold H dworkIterSeries
    refine norm_coeff_mvProd_le p (Finset.range m) _ (fun l hl u => ?_)
    rw [Finset.mem_range] at hl
    have hsub := norm_coeff_mvSubstPow_le p (pow_pos (pow_pos hp.out.pos r) l)
      (norm_coeff_dworkPolySeries_le p r G hG0 hDpos hD) u
    refine hsub.trans ?_
    refine Real.rpow_le_rpow_of_exponent_le hp1 ?_
    have hle_pow : (((p ^ r) ^ l : ℕ) : ℝ) ≤ ((p ^ r) ^ m : ℝ) := by
      exact_mod_cast Nat.pow_le_pow_right (pow_pos hp.out.pos r) (le_of_lt hl)
    have hdiv : cm ≤ c / (((p ^ r) ^ l : ℕ) : ℝ) :=
      div_le_div_of_nonneg_left hc.le (by exact_mod_cast pow_pos (pow_pos hp.out.pos r) l) hle_pow
    nlinarith [Nat.cast_nonneg (α := ℝ) u.degree]
  -- Step 2: Replace `dworkChar` with `mvEval H` on RHS, then swap finite sum and `tsum`
  have hrhs_eval : ∑ x ∈ Fintype.piFinset (fun _ : Fin d => finFieldUnits p (r * m)),
      dworkChar p (r * m) (MvPolynomial.eval x G) =
      ∑ x ∈ Fintype.piFinset (fun _ : Fin d => finFieldUnits p (r * m)),
        mvEval p (fun i => teich p (x i)) H := by
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [Fintype.mem_piFinset] at hx
    exact (mvEval_dworkIterSeries_eq_dworkChar p hr hm G hG0 hGcoeff x
      fun i => (mem_finFieldSet p hrm).mpr ((mem_finFieldUnits p hrm).mp (hx i)).2).symm
  rw [hrhs_eval]
  unfold mvEval
  have hsumm_x : ∀ x ∈ Fintype.piFinset (fun _ : Fin d => finFieldUnits p (r * m)),
      Summable fun w : Fin d →₀ ℕ =>
        MvPowerSeries.coeff w H * ∏ i : Fin d, (teich p (x i)) ^ (w i) := fun x _ =>
    (mvEval_summable_norm_of_decay p hcm hH_decay fun i => teich_norm_le_one p (x i)).of_norm
  rw [← Summable.tsum_finsetSum hsumm_x]
  -- Step 3: Factor the inner finite sum over `i : Fin d` and apply `sum_finFieldUnits_teich_pow`
  have hinner : ∀ w : Fin d →₀ ℕ,
      ∑ x ∈ Fintype.piFinset (fun _ : Fin d => finFieldUnits p (r * m)),
        MvPowerSeries.coeff w H * ∏ i : Fin d, (teich p (x i)) ^ (w i) =
      if ∀ i : Fin d, ((p ^ r) ^ m - 1) ∣ w i then
        (((p ^ r) ^ m - 1 : ℕ) : DworkField p) ^ d * MvPowerSeries.coeff w H
      else 0 := by
    intro w
    rw [← Finset.mul_sum]
    have hpi : ∑ x ∈ Fintype.piFinset (fun _ : Fin d => finFieldUnits p (r * m)),
        ∏ i : Fin d, (teich p (x i)) ^ (w i) =
        ∏ i : Fin d, ∑ y ∈ finFieldUnits p (r * m), (teich p y) ^ (w i) := by
      exact (Finset.prod_univ_sum (t := fun _ : Fin d => finFieldUnits p (r * m))
        (f := fun i y => (teich p y) ^ (w i))).symm
    rw [hpi]
    simp_rw [sum_finFieldUnits_teich_pow p hrm, ← hqrm]
    by_cases hall : ∀ i : Fin d, ((p ^ r) ^ m - 1) ∣ w i
    · rw [if_pos hall]
      have hprod_const : ∏ i : Fin d,
          (if ((p ^ r) ^ m - 1) ∣ w i then (((p ^ r) ^ m - 1 : ℕ) : DworkField p) else 0) =
          (((p ^ r) ^ m - 1 : ℕ) : DworkField p) ^ d := by
        rw [Finset.prod_congr rfl (fun i _ => if_pos (hall i)), Finset.prod_const, Finset.card_fin]
      rw [hprod_const, mul_comm]
    · rw [if_neg hall]
      push Not at hall
      obtain ⟨i₀, hi₀⟩ := hall
      have hprod0 : ∏ i : Fin d,
          (if ((p ^ r) ^ m - 1) ∣ w i then (((p ^ r) ^ m - 1 : ℕ) : DworkField p) else 0) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ i₀) (if_neg hi₀)
      rw [hprod0, mul_zero]
  simp_rw [hinner]
  -- Step 4: Reindex `w = ((p^r)^m - 1) • u` to match `((p^r)^m - 1)^d * dworkInfTrace`!
  unfold dworkInfTrace
  rw [← tsum_mul_left]
  have hqm_pos : 0 < (p ^ r) ^ m - 1 := by
    have : 2 ≤ (p ^ r) ^ m := by
      calc 2 ≤ p ^ r := hq2
        _ = (p ^ r) ^ 1 := (pow_one _).symm
        _ ≤ (p ^ r) ^ m := Nat.pow_le_pow_right (by omega) hm
    omega
  symm
  refine tsum_eq_tsum_of_ne_zero_bij (fun u => ((p ^ r) ^ m - 1) • u.1) ?_ ?_ ?_
  · intro a b hab
    apply Subtype.ext
    ext i
    have hi := congrArg (fun z : Fin d →₀ ℕ => z i) hab
    simp only [Finsupp.smul_apply, smul_eq_mul] at hi
    exact Nat.eq_of_mul_eq_mul_left hqm_pos hi
  · intro w hw
    rw [Function.mem_support] at hw
    have hall : ∀ i : Fin d, ((p ^ r) ^ m - 1) ∣ w i := by
      by_contra hnot
      rw [if_neg hnot] at hw
      exact hw rfl
    let u : Fin d →₀ ℕ := Finsupp.equivFunOnFinite.symm fun i => w i / ((p ^ r) ^ m - 1)
    have hwu : ((p ^ r) ^ m - 1) • u = w := by
      ext i
      change ((p ^ r) ^ m - 1) * (w i / ((p ^ r) ^ m - 1)) = w i
      exact Nat.mul_div_cancel' (hall i)
    refine ⟨⟨u, ?_⟩, hwu⟩
    rw [Function.mem_support]
    rw [if_pos hall] at hw
    rw [dworkInfMatPow_diag p hq2 _ hm u, hwu]
    exact hw
  · intro u
    rw [if_pos (fun i => by simp [dvd_mul_right]), dworkInfMatPow_diag p hq2 _ hm u.1]

end MultivariateDworkTrace

end RHDirect.DworkWeil1

