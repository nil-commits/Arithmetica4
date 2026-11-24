/-
Copyright: reference implementation for the ORACLE P3 (Dwork / Hasse–Weil) campaign.
Wave 3: multiplicativity of the Hasse–Weil zeta function under disjoint union.
-/
import RHDirect.DworkZetaW2

/-!
# `RHDirect.DworkZetaW3`

Waves 1–2 produced a rational Hasse–Weil zeta function `Z(V, T)` for a single finite `F_q`-scheme
`V` (a finite type with a Frobenius permutation).  This file proves the property that makes `Z` a
*zeta function of varieties* rather than of one finite set:

`Z(V ⊔ W, T) = Z(V, T) · Z(W, T)`.

The proof is structural: point counts add under disjoint union, so `zetaLog` is additive, and
`exp` turns sums into products (`expSeries_add`, proved in `DworkZetaCore`).
-/

namespace RHDirect
namespace HasseWeil

open PowerSeries

noncomputable section

/-! ## 1.  Fixed points as a sum of indicators -/

lemma natCard_fixedPoints {α : Type*} [Fintype α] [DecidableEq α] (σ : Equiv.Perm α) (m : ℕ) :
    Nat.card {x : α // (σ ^ m) x = x} = ∑ x : α, if (σ ^ m) x = x then 1 else 0 := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter]

/-! ## 2.  Iterates of `sumCongr` act componentwise -/

theorem sumCongr_apply_inl {V W : Type*} (σ₁ : Equiv.Perm V) (σ₂ : Equiv.Perm W) (v : V) :
    (Equiv.Perm.sumCongr σ₁ σ₂) (Sum.inl v) = Sum.inl (σ₁ v) := rfl

theorem sumCongr_apply_inr {V W : Type*} (σ₁ : Equiv.Perm V) (σ₂ : Equiv.Perm W) (w : W) :
    (Equiv.Perm.sumCongr σ₁ σ₂) (Sum.inr w) = Sum.inr (σ₂ w) := rfl

theorem sumCongr_pow_apply_inl {V W : Type*} (σ₁ : Equiv.Perm V) (σ₂ : Equiv.Perm W)
    (m : ℕ) :
    ∀ v : V, ((Equiv.Perm.sumCongr σ₁ σ₂ ^ m) (Sum.inl v)) = Sum.inl ((σ₁ ^ m) v) := by
  induction m with
  | zero => intro v; rfl
  | succ m ih =>
    intro v
    rw [pow_succ, Equiv.Perm.mul_apply, sumCongr_apply_inl, ih, pow_succ,
      Equiv.Perm.mul_apply]

theorem sumCongr_pow_apply_inr {V W : Type*} (σ₁ : Equiv.Perm V) (σ₂ : Equiv.Perm W)
    (m : ℕ) :
    ∀ w : W, ((Equiv.Perm.sumCongr σ₁ σ₂ ^ m) (Sum.inr w)) = Sum.inr ((σ₂ ^ m) w) := by
  induction m with
  | zero => intro w; rfl
  | succ m ih =>
    intro w
    rw [pow_succ, Equiv.Perm.mul_apply, sumCongr_apply_inr, ih, pow_succ,
      Equiv.Perm.mul_apply]

/-! ## 3.  Point counts are additive -/

theorem fixedCount_sumCongr {V W : Type*} [Fintype V] [Fintype W]
    (σ₁ : Equiv.Perm V) (σ₂ : Equiv.Perm W) (m : ℕ) :
    fixedCount (Equiv.Perm.sumCongr σ₁ σ₂) m = fixedCount σ₁ m + fixedCount σ₂ m := by
  classical
  rw [fixedCount, fixedCount, fixedCount, natCard_fixedPoints, natCard_fixedPoints,
    natCard_fixedPoints, Fintype.sum_sum_type]
  simp only [sumCongr_pow_apply_inl, sumCongr_pow_apply_inr, Sum.inl.injEq, Sum.inr.injEq]

/-! ## 4.  `zetaLog` is additive -/

theorem zetaLog_sumCongr {V W : Type*} [Fintype V] [Fintype W]
    (σ₁ : Equiv.Perm V) (σ₂ : Equiv.Perm W) :
    zetaLog (Equiv.Perm.sumCongr σ₁ σ₂) = zetaLog σ₁ + zetaLog σ₂ := by
  ext n
  simp only [zetaLog, PowerSeries.coeff_mk, map_add]
  rw [fixedCount_sumCongr]
  push_cast
  ring

/-! ## 5.  Multiplicativity of the zeta function -/

/-- **W3 headline.**  The Hasse–Weil zeta function is multiplicative under disjoint union. -/
theorem zetaFinite_sumCongr {V W : Type*} [Fintype V] [Fintype W]
    (σ₁ : Equiv.Perm V) (σ₂ : Equiv.Perm W) :
    zetaFinite (Equiv.Perm.sumCongr σ₁ σ₂) = zetaFinite σ₁ * zetaFinite σ₂ := by
  rw [zetaFinite, zetaFinite, zetaFinite, zetaLog_sumCongr,
    expSeries_add (constantCoeff_zetaLog σ₁) (constantCoeff_zetaLog σ₂)]

/-- Iterated multiplicativity over an explicit disjoint decomposition. -/
theorem zetaFinite_sumCongr_three {U V W : Type*} [Fintype U] [Fintype V] [Fintype W]
    (σ₁ : Equiv.Perm U) (σ₂ : Equiv.Perm V) (σ₃ : Equiv.Perm W) :
    zetaFinite (Equiv.Perm.sumCongr (Equiv.Perm.sumCongr σ₁ σ₂) σ₃)
      = zetaFinite σ₁ * zetaFinite σ₂ * zetaFinite σ₃ := by
  rw [zetaFinite_sumCongr, zetaFinite_sumCongr]

end

end HasseWeil
end RHDirect
