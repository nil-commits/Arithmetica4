/-
Copyright: reference implementation for the ORACLE P3 (Dwork / Hasse–Weil) campaign.
Wave 1: full dimension-0 rationality for a finite permutation, fixed points included.
-/
import RHDirect.DworkZeta0D
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.Data.Fintype.Card
import Mathlib.GroupTheory.Perm.Cycle.Factors

/-!
# `RHDirect.DworkZetaW1`

Wave 1 of the P3 campaign: the `dim 0` Dwork rationality theorem **with no residual hypothesis**,
for an arbitrary permutation of a finite type.

The previously open arithmetic input (the point-count identity) is discharged in
`fixedCount_eq_sum`, and the geometric factors are handled uniformly with `PowerSeries.expand`
so that fixed points (orbits of length `1`) need no special treatment.

Nothing here is conditional.
-/

namespace RHDirect
namespace HasseWeil

open PowerSeries

noncomputable section

/-! ## 1.  Product rule and the derivative of `1 - T^d` -/

/-- Product rule for a finite product of power series. -/
theorem derivative_prod {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f : ι → PowerSeries ℚ) :
    (d⁄dX ℚ) (∏ i ∈ s, f i)
      = ∑ j ∈ s, (∏ i ∈ s.erase j, f i) * (d⁄dX ℚ) (f j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Derivation.leibniz, ih]
    simp only [smul_eq_mul]
    rw [Finset.erase_insert ha, Finset.mul_sum]
    have hstep : ∀ j ∈ s, (∏ i ∈ (insert a s).erase j, f i) * (d⁄dX ℚ) (f j)
        = f a * ((∏ i ∈ s.erase j, f i) * (d⁄dX ℚ) (f j)) := by
      intro j hj
      have hne : a ≠ j := by rintro rfl; exact ha hj
      have hmem : a ∉ s.erase j := fun h => ha (Finset.mem_of_mem_erase h)
      rw [Finset.erase_insert_of_ne hne, Finset.prod_insert (a := a) (s := s.erase j) hmem]
      ring
    rw [Finset.sum_congr rfl hstep, ← Finset.mul_sum]
    ring

theorem derivative_one_sub_X_pow (d : ℕ) :
    (d⁄dX ℚ) (1 - PowerSeries.X ^ d : PowerSeries ℚ)
      = -((d : PowerSeries ℚ) * PowerSeries.X ^ (d - 1)) := by
  rw [map_sub, PowerSeries.derivative_one, zero_sub, PowerSeries.derivative_pow,
    PowerSeries.derivative_X]
  ring

theorem derivative_neg_logOf_one_sub_X_pow (d : ℕ) (hd : 1 ≤ d) :
    (d⁄dX ℚ) (-(PowerSeries.logOf (1 - PowerSeries.X ^ d : PowerSeries ℚ)))
      = (d : PowerSeries ℚ) * PowerSeries.X ^ (d - 1)
          * (1 - PowerSeries.X ^ d)⁻¹ := by
  rw [map_neg, deriv_logOf (by simp [show d ≠ 0 by omega]),
    derivative_one_sub_X_pow]
  ring

/-! ## 2.  Uniqueness for `y' = y * S'` and the `exp = F⁻¹` criterion -/

theorem eq_C_constantCoeff_of_derivative_eq_zero {f : PowerSeries ℚ}
    (h : (d⁄dX ℚ) f = 0) : f = PowerSeries.C (constantCoeff f) := by
  refine PowerSeries.derivative.ext ?_ ?_
  · rw [h, PowerSeries.derivative_C]
  · rw [PowerSeries.constantCoeff_C]

theorem eq_of_derivative_eq_mul_derivative {S y₁ y₂ : PowerSeries ℚ}
    (h1 : (d⁄dX ℚ) y₁ = y₁ * (d⁄dX ℚ) S)
    (h2 : (d⁄dX ℚ) y₂ = y₂ * (d⁄dX ℚ) S)
    (hy₂ : constantCoeff y₂ ≠ 0)
    (h0 : constantCoeff y₁ = constantCoeff y₂) : y₁ = y₂ := by
  have hderiv : (d⁄dX ℚ) (y₁ * y₂⁻¹) = 0 := by
    have hcancel : y₂⁻¹ * y₂ = 1 := PowerSeries.inv_mul_cancel y₂ hy₂
    have h2' : y₂⁻¹ ^ 2 * y₂ = y₂⁻¹ := by
      calc y₂⁻¹ ^ 2 * y₂ = y₂⁻¹ * (y₂⁻¹ * y₂) := by ring
        _ = y₂⁻¹ := by rw [hcancel, mul_one]
    rw [Derivation.leibniz, PowerSeries.derivative_inv', h2, h1]
    simp only [smul_eq_mul]
    have hexp : y₁ * (-y₂⁻¹ ^ 2 * (y₂ * (d⁄dX ℚ) S))
        = -(y₁ * ((y₂⁻¹ ^ 2 * y₂) * (d⁄dX ℚ) S)) := by ring
    rw [hexp, h2']
    ring
  have hconst : y₁ * y₂⁻¹ = PowerSeries.C (constantCoeff (y₁ * y₂⁻¹)) :=
    eq_C_constantCoeff_of_derivative_eq_zero hderiv
  have hc : constantCoeff (y₁ * y₂⁻¹) = 1 := by
    rw [map_mul, PowerSeries.constantCoeff_inv, h0]
    exact mul_inv_cancel₀ hy₂
  have hone : y₁ * y₂⁻¹ = 1 := by rw [hconst, hc]; simp
  calc y₁ = y₁ * 1 := by rw [mul_one]
    _ = y₁ * (y₂ * y₂⁻¹) := by rw [PowerSeries.mul_inv_cancel y₂ hy₂]
    _ = (y₁ * y₂⁻¹) * y₂ := by ring
    _ = 1 * y₂ := by rw [hone]
    _ = y₂ := by rw [one_mul]

/-- **`exp` criterion.**  If `F(0) = 1` and `F' = -(F · S')` then `exp S = F⁻¹`. -/
theorem expSeries_eq_inv_of_derivative {S F : PowerSeries ℚ} (hS : constantCoeff S = 0)
    (hF : constantCoeff F = 1)
    (h : (d⁄dX ℚ) F = -(F * (d⁄dX ℚ) S)) : expSeries S = F⁻¹ := by
  have hFne : constantCoeff F ≠ 0 := by rw [hF]; exact one_ne_zero
  have hinv : (d⁄dX ℚ) F⁻¹ = F⁻¹ * (d⁄dX ℚ) S := by
    have hFF : F * F⁻¹ = 1 := PowerSeries.mul_inv_cancel F hFne
    rw [PowerSeries.derivative_inv', h]
    rw [show -F⁻¹ ^ 2 * -(F * (d⁄dX ℚ) S) = F⁻¹ * (F * F⁻¹) * (d⁄dX ℚ) S by ring]
    rw [hFF]
    ring
  have hcc : constantCoeff F⁻¹ = 1 := by
    rw [PowerSeries.constantCoeff_inv, hF]
    simp
  exact eq_of_derivative_eq_mul_derivative (derivative_expSeries hS) hinv
    (by rw [hcc]; exact one_ne_zero) (by rw [constantCoeff_expSeries hS, hcc])

/-! ## 3.  The geometric factor `(1 - T^d)⁻¹` via `expand` -/

theorem subst_one' (h : PowerSeries ℚ) (hh : HasSubst h) :
    PowerSeries.subst h (1 : PowerSeries ℚ) = 1 := by
  rw [← PowerSeries.coe_substAlgHom hh]
  exact map_one (PowerSeries.substAlgHom hh)

theorem inv_one_sub_X_pow_eq_expand (d : ℕ) (hd : d ≠ 0) :
    (1 - PowerSeries.X ^ d : PowerSeries ℚ)⁻¹ = (PowerSeries.mk 1).expand d hd := by
  have hXd : HasSubst (PowerSeries.X ^ d : PowerSeries ℚ) := by
    apply HasSubst.of_constantCoeff_zero'
    rw [map_pow, PowerSeries.constantCoeff_X]
    exact zero_pow hd
  have hone : PowerSeries.subst (PowerSeries.X ^ d : PowerSeries ℚ) (1 : PowerSeries ℚ) = 1 :=
    subst_one' _ hXd
  have hkey : PowerSeries.subst (PowerSeries.X ^ d : PowerSeries ℚ)
      ((1 : PowerSeries ℚ) - PowerSeries.X) = 1 - PowerSeries.X ^ d := by
    rw [PowerSeries.subst_sub hXd, PowerSeries.subst_X hXd, hone]
  have h := congrArg (PowerSeries.subst (PowerSeries.X ^ d : PowerSeries ℚ))
    (PowerSeries.mk_one_mul_one_sub_eq_one (S := ℚ))
  rw [PowerSeries.subst_mul hXd, hkey, hone] at h
  rw [PowerSeries.expand_apply, eq_comm,
    PowerSeries.eq_inv_iff_mul_eq_one (by simp [hd])]
  exact h

/-- Coefficient of `(1 - T^d)⁻¹`: `1` exactly on multiples of `d`. -/
theorem coeff_inv_one_sub_X_pow (d : ℕ) (hd : d ≠ 0) (j : ℕ) :
    (coeff j) ((1 - PowerSeries.X ^ d)⁻¹ : PowerSeries ℚ) = if d ∣ j then 1 else 0 := by
  rw [inv_one_sub_X_pow_eq_expand d hd, PowerSeries.coeff_expand]
  split_ifs with h
  · simp
  · rfl

/-- Coefficient of one geometric orbit term. -/
theorem coeff_orbitTerm (d : ℕ) (hd : 1 ≤ d) (k : ℕ) :
    (coeff k) ((d : PowerSeries ℚ) * PowerSeries.X ^ (d - 1)
        * (1 - PowerSeries.X ^ d)⁻¹)
      = if d ∣ k + 1 then (d : ℚ) else 0 := by
  have hd0 : d ≠ 0 := by omega
  have hiff : (d - 1 ≤ k ∧ d ∣ (k - (d - 1))) ↔ d ∣ k + 1 := by
    constructor
    · rintro ⟨h1, h2⟩
      have hk : k + 1 = (k - (d - 1)) + d := by omega
      rw [hk]
      exact Nat.dvd_add h2 (dvd_refl d)
    · intro h
      have hle : d ≤ k + 1 := Nat.le_of_dvd (by omega) h
      refine ⟨by omega, ?_⟩
      have hk : k + 1 = (k - (d - 1)) + d := by omega
      rw [hk] at h
      rw [Nat.add_comm (k - (d - 1)) d] at h
      exact (Nat.dvd_add_iff_right (dvd_refl d)).mpr h
  rw [show (d : PowerSeries ℚ) = PowerSeries.C (d : ℚ) by simp]
  rw [mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul',
    coeff_inv_one_sub_X_pow d hd0]
  by_cases hmain : d ∣ k + 1
  · rw [if_pos (by omega : d - 1 ≤ k), if_pos hmain, if_pos ((hiff.mpr hmain).2)]
    ring
  · rw [if_neg hmain]
    by_cases hle : d - 1 ≤ k
    · rw [if_pos hle]
      have h2 : ¬ d ∣ (k - (d - 1)) := fun h => hmain (hiff.mp ⟨hle, h⟩)
      rw [if_neg h2, mul_zero]
    · rw [if_neg hle, mul_zero]

/-! ## 4.  The point-count identity (fixed points separated out) -/

theorem fixed_point_iterate {V : Type*} (σ : Equiv.Perm V) {v : V} (h : σ v = v) (m : ℕ) :
    (σ ^ m) v = v := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ]
    simp only [Equiv.Perm.mul_apply]
    rw [h, ih]

/-- **Point counts of a finite permutation.**  The fixed points of `σ^m` are the fixed points of `σ`
together with the points lying on a cycle whose length divides `m`. -/
theorem fixedCount_eq_sum {V : Type*} [Fintype V] [DecidableEq V]
    (σ : Equiv.Perm V) (m : ℕ) :
    fixedCount σ m = Nat.card {v : V // σ v = v}
      + ∑ c ∈ σ.cycleFactorsFinset, (if c.support.card ∣ m then c.support.card else 0) := by
  classical
  have h1 : fixedCount σ m = (Finset.univ.filter (fun v : V => (σ ^ m) v = v)).card := by
    rw [fixedCount, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have h2 : Nat.card {v : V // σ v = v}
      = (Finset.univ.filter (fun v : V => σ v = v)).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [h1, h2]
  have hsplit : (Finset.univ.filter (fun v : V => (σ ^ m) v = v))
      = (Finset.univ.filter (fun v : V => σ v = v))
        ∪ (Finset.univ.filter (fun v : V => (σ ^ m) v = v ∧ ¬ σ v = v)) := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    constructor
    · intro h
      by_cases hq : σ v = v
      · exact Or.inl hq
      · exact Or.inr ⟨h, hq⟩
    · rintro (h | ⟨h, _⟩)
      · exact fixed_point_iterate σ h m
      · exact h
  have hdisj : Disjoint (Finset.univ.filter (fun v : V => σ v = v))
      (Finset.univ.filter (fun v : V => (σ ^ m) v = v ∧ ¬ σ v = v)) := by
    rw [Finset.disjoint_left]
    intro v hv hv'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv hv'
    exact hv'.2 hv
  rw [hsplit, Finset.card_union_of_disjoint hdisj]
  congr 1
  have hC : (Finset.univ.filter (fun v : V => (σ ^ m) v = v ∧ ¬ σ v = v))
      = σ.cycleFactorsFinset.biUnion
          (fun c => Finset.univ.filter (fun v : V => v ∈ c.support ∧ (σ ^ m) v = v)) := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion]
    constructor
    · rintro ⟨hP, hQ⟩
      have hsupp : v ∈ σ.support := by
        rw [Equiv.Perm.mem_support]; exact hQ
      obtain ⟨c, hc, hvc⟩ :=
        Equiv.Perm.mem_support_iff_mem_support_of_mem_cycleFactorsFinset.mp hsupp
      exact ⟨c, hc, hvc, hP⟩
    · rintro ⟨c, hc, hvc, hP⟩
      refine ⟨hP, ?_⟩
      intro hQ
      have hmem : v ∈ σ.support :=
        Equiv.Perm.mem_cycleFactorsFinset_support_le hc hvc
      rw [Equiv.Perm.mem_support] at hmem
      exact hmem hQ
  rw [hC, Finset.card_biUnion]
  · refine Finset.sum_congr rfl (fun c hc => ?_)
    have hcyc : σ.IsCycleOn ↑c.support :=
      Equiv.Perm.isCycleOn_support_of_mem_cycleFactorsFinset hc
    by_cases hdvd : c.support.card ∣ m
    · rw [if_pos hdvd]
      have hfill : (Finset.univ.filter (fun v : V => v ∈ c.support ∧ (σ ^ m) v = v))
          = c.support := by
        ext v
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨fun h => h.1, fun hv => ⟨hv, (hcyc.pow_apply_eq hv).mpr hdvd⟩⟩
      rw [hfill]
    · rw [if_neg hdvd]
      have hempty : (Finset.univ.filter (fun v : V => v ∈ c.support ∧ (σ ^ m) v = v)) = ∅ := by
        ext v
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty]
        exact ⟨fun hv => absurd ((hcyc.pow_apply_eq hv.1).mp hv.2) hdvd, False.elim⟩
      rw [hempty, Finset.card_empty]
  · intro c hc d hd hne
    have hdisj' : Equiv.Perm.Disjoint c d :=
      Equiv.Perm.cycleFactorsFinset_pairwise_disjoint σ hc hd hne
    have hsupp : Disjoint c.support d.support :=
      Equiv.Perm.Disjoint.disjoint_support hdisj'
    show Disjoint (Finset.univ.filter (fun v : V => v ∈ c.support ∧ (σ ^ m) v = v))
      (Finset.univ.filter (fun v : V => v ∈ d.support ∧ (σ ^ m) v = v))
    rw [Finset.disjoint_left]
    intro v hv hv'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv hv'
    exact ((Finset.disjoint_left.mp hsupp) hv.1) hv'.1

/-! ## 5.  The derivative of `zetaLog` -/

theorem coeff_derivative_zetaLog {V : Type*} [Fintype V] (σ : Equiv.Perm V) (k : ℕ) :
    (coeff k) ((d⁄dX ℚ) (zetaLog σ)) = (fixedCount σ (k + 1) : ℚ) := by
  rw [PowerSeries.coeff_derivative]
  have h : ((k : ℚ) + 1) ≠ 0 := by positivity
  rw [zetaLog, PowerSeries.coeff_mk]
  have hcast : ((k : ℚ) + 1) = ((k + 1 : ℕ) : ℚ) := by push_cast; ring
  rw [hcast]
  have hb : ((k + 1 : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k)
  field_simp

/-- **Closed form of `S'`.** -/
theorem derivative_zetaLog_eq_sum {V : Type*} [Fintype V] {ι : Type*} [Fintype ι]
    (σ : Equiv.Perm V) (d : ι → ℕ) (hd : ∀ i, 1 ≤ d i)
    (hcount : ∀ m, fixedCount σ m = ∑ i, (if d i ∣ m then d i else 0)) :
    (d⁄dX ℚ) (zetaLog σ)
      = ∑ i, (d i : PowerSeries ℚ) * PowerSeries.X ^ (d i - 1)
          * (1 - PowerSeries.X ^ (d i))⁻¹ := by
  ext k
  have hcast : ((∑ i, (if d i ∣ k + 1 then d i else 0) : ℕ) : ℚ)
      = ∑ i, (if d i ∣ k + 1 then (d i : ℚ) else 0) := by
    rw [Nat.cast_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    split_ifs <;> simp
  rw [map_sum, coeff_derivative_zetaLog, hcount (k + 1), hcast]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [coeff_orbitTerm (d i) (hd i) k]

/-! ## 6.  Dwork rationality in dimension `0`, unconditional -/

/-- **Dwork rationality, `dim 0`, for arbitrary orbit data.** -/
theorem zetaFinite_eq_inv_prod {V : Type*} [Fintype V] {ι : Type*} [Fintype ι]
    [DecidableEq ι] (σ : Equiv.Perm V) (d : ι → ℕ) (hd : ∀ i, 1 ≤ d i)
    (hcount : ∀ m, fixedCount σ m = ∑ i, (if d i ∣ m then d i else 0)) :
    zetaFinite σ = (∏ i : ι, (1 - PowerSeries.X ^ (d i) : PowerSeries ℚ))⁻¹ := by
  have hS : constantCoeff (zetaLog σ) = 0 := constantCoeff_zetaLog σ
  have hF : constantCoeff (∏ i : ι, (1 - PowerSeries.X ^ (d i) : PowerSeries ℚ)) = 1 := by
    rw [map_prod]
    refine Finset.prod_eq_one (fun i _ => ?_)
    rw [map_sub, map_one, map_pow, PowerSeries.constantCoeff_X,
      zero_pow (by have := hd i; omega), sub_zero]
  refine expSeries_eq_inv_of_derivative hS hF ?_
  rw [derivative_zetaLog_eq_sum σ d hd hcount, derivative_prod]
  simp only [derivative_one_sub_X_pow]
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have hfj : constantCoeff (1 - PowerSeries.X ^ d j : PowerSeries ℚ) ≠ 0 := by
    rw [constantCoeff_one_sub_X_pow (hd j)]; exact one_ne_zero
  have hcancel : (1 - PowerSeries.X ^ d j : PowerSeries ℚ)
      * (1 - PowerSeries.X ^ d j)⁻¹ = 1 := PowerSeries.mul_inv_cancel _ hfj
  have hprod : (∏ i ∈ Finset.univ.erase j, (1 - PowerSeries.X ^ d i : PowerSeries ℚ))
      * (1 - PowerSeries.X ^ d j) = ∏ i, (1 - PowerSeries.X ^ d i : PowerSeries ℚ) :=
    Finset.prod_erase_mul (Finset.univ)
      (fun i => (1 - PowerSeries.X ^ d i : PowerSeries ℚ)) (Finset.mem_univ j)
  calc (∏ i ∈ Finset.univ.erase j, (1 - PowerSeries.X ^ d i : PowerSeries ℚ))
        * (-((d j : PowerSeries ℚ) * PowerSeries.X ^ (d j - 1)))
      = -((∏ i ∈ Finset.univ.erase j, (1 - PowerSeries.X ^ d i : PowerSeries ℚ))
          * ((d j : PowerSeries ℚ) * PowerSeries.X ^ (d j - 1))) := by ring
    _ = -((∏ i ∈ Finset.univ.erase j, (1 - PowerSeries.X ^ d i : PowerSeries ℚ))
          * ((d j : PowerSeries ℚ) * PowerSeries.X ^ (d j - 1))
          * ((1 - PowerSeries.X ^ d j) * (1 - PowerSeries.X ^ d j)⁻¹)) := by
          rw [hcancel, mul_one]
    _ = -((∏ i, (1 - PowerSeries.X ^ d i : PowerSeries ℚ))
          * ((d j : PowerSeries ℚ) * PowerSeries.X ^ (d j - 1)
            * (1 - PowerSeries.X ^ d j)⁻¹)) := by
          rw [← hprod]; ring

/-! ## 7.  Explicit orbit data and the unconditional headline -/

/-- Orbit index of a permutation: fixed points (orbits of length `1`) together with the
non-trivial cycles. -/
abbrev OrbitIndex {V : Type*} [Fintype V] [DecidableEq V] (σ : Equiv.Perm V) : Type _ :=
  {v : V // σ v = v} ⊕ {c : Equiv.Perm V // c ∈ σ.cycleFactorsFinset}

/-- Orbit length: `1` on fixed points, the support size on non-trivial cycles. -/
def orbitLen {V : Type*} [Fintype V] [DecidableEq V] (σ : Equiv.Perm V) : OrbitIndex σ → ℕ
  | Sum.inl _ => 1
  | Sum.inr c => c.val.support.card

theorem orbitLen_pos {V : Type*} [Fintype V] [DecidableEq V] (σ : Equiv.Perm V)
    (i : OrbitIndex σ) : 1 ≤ orbitLen σ i := by
  rcases i with v | c
  · simp [orbitLen]
  · simp only [orbitLen]
    have hcyc : c.val.IsCycle := (Equiv.Perm.mem_cycleFactorsFinset_iff.mp c.prop).1
    exact Nat.one_le_iff_ne_zero.mpr (Finset.card_ne_zero.mpr hcyc.nonempty_support)

/-- The point-count identity, indexed by the orbit data. -/
theorem fixedCount_eq_orbitSum {V : Type*} [Fintype V] [DecidableEq V]
    (σ : Equiv.Perm V) (m : ℕ) :
    fixedCount σ m = ∑ i : OrbitIndex σ, (if orbitLen σ i ∣ m then orbitLen σ i else 0) := by
  rw [Fintype.sum_sum_type]
  have hleft : (∑ v : {v : V // σ v = v},
      (if orbitLen σ (Sum.inl v) ∣ m then orbitLen σ (Sum.inl v) else 0))
      = Nat.card {v : V // σ v = v} := by
    simp [orbitLen]
  have hright : (∑ c : {c : Equiv.Perm V // c ∈ σ.cycleFactorsFinset},
      (if orbitLen σ (Sum.inr c) ∣ m then orbitLen σ (Sum.inr c) else 0))
      = ∑ c ∈ σ.cycleFactorsFinset, (if c.support.card ∣ m then c.support.card else 0) := by
    have h := Finset.sum_coe_sort (σ.cycleFactorsFinset)
      (fun c : Equiv.Perm V => (if c.support.card ∣ m then c.support.card else 0))
    rw [← h]
    refine Finset.sum_congr rfl
      (fun (c : {c : Equiv.Perm V // c ∈ σ.cycleFactorsFinset}) _ => ?_)
    rfl
  rw [hleft, hright, fixedCount_eq_sum]

/-- **Dwork rationality in dimension `0`, unconditional.**
For every permutation `σ` of a finite type, the Hasse–Weil zeta function is the reciprocal of
`(1 - T)^{#Fix σ} · ∏_{c} (1 - T^{|c|})`, a rational function of `T`. -/
theorem zetaFinite_eq_prod_inv_fixed {V : Type*} [Fintype V] [DecidableEq V]
    (σ : Equiv.Perm V) :
    zetaFinite σ
      = (((1 - PowerSeries.X) ^ Nat.card {v : V // σ v = v})
          * ∏ c ∈ σ.cycleFactorsFinset, (1 - PowerSeries.X ^ c.support.card)
            : PowerSeries ℚ)⁻¹ := by
  rw [zetaFinite_eq_inv_prod σ (orbitLen σ) (orbitLen_pos σ) (fixedCount_eq_orbitSum σ)]
  congr 1
  rw [Fintype.prod_sum_type]
  congr 1
  · simp only [orbitLen]
    rw [Finset.prod_const, pow_one]
    congr 1
    rw [Finset.card_univ, Nat.card_eq_fintype_card]
  · have h := Finset.prod_coe_sort (σ.cycleFactorsFinset)
      (fun c : Equiv.Perm V => (1 - PowerSeries.X ^ c.support.card : PowerSeries ℚ))
    rw [← h]
    refine Finset.prod_congr rfl (fun c _ => ?_)
    simp [orbitLen]

/-- Multiplicative form of the headline: `Z(T) · (1 - T)^{#Fix} · ∏ (1 - T^{|c|}) = 1`. -/
theorem zetaFinite_mul_prod_fixed_eq_one {V : Type*} [Fintype V] [DecidableEq V]
    (σ : Equiv.Perm V) :
    zetaFinite σ
      * (((1 - PowerSeries.X) ^ Nat.card {v : V // σ v = v})
          * ∏ c ∈ σ.cycleFactorsFinset, (1 - PowerSeries.X ^ c.support.card)) = 1 := by
  rw [zetaFinite_eq_prod_inv_fixed]
  exact PowerSeries.inv_mul_cancel _ (by
    have hf : constantCoeff ((1 - PowerSeries.X) ^ Nat.card {v : V // σ v = v}
        : PowerSeries ℚ) = 1 := by
      rw [map_pow, map_sub, map_one, PowerSeries.constantCoeff_X, sub_zero, one_pow]
    have hp : constantCoeff (∏ c ∈ σ.cycleFactorsFinset,
        (1 - PowerSeries.X ^ c.support.card) : PowerSeries ℚ) = 1 := by
      rw [map_prod]
      refine Finset.prod_eq_one (fun c hc => ?_)
      have hcyc : c.IsCycle := (Equiv.Perm.mem_cycleFactorsFinset_iff.mp hc).1
      have hpos : 0 < c.support.card := Finset.card_pos.mpr hcyc.nonempty_support
      rw [map_sub, map_one, map_pow, PowerSeries.constantCoeff_X,
        zero_pow (by omega), sub_zero]
    rw [map_mul, hf, hp, one_mul]
    exact one_ne_zero)

end

end HasseWeil
end RHDirect