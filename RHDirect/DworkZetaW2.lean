/-
Copyright: reference implementation for the ORACLE P3 (Dwork / Hasse–Weil) campaign.
Wave 2: from permutations to varieties — Frobenius acting on a zero locus over a finite field.
-/
import RHDirect.DworkZetaW1
import Mathlib.RingTheory.Polynomial.Basic

/-!
# `RHDirect.DworkZetaW2`

Wave 2 makes the `dim 0` theorem *geometric*.

Let `K` be a field and `φ : K ≃+* K` a field automorphism — the model for the Frobenius
`x ↦ x ^ q` of `𝔽_q`.  Let `p : K[X]` be a polynomial whose coefficients are fixed by `φ`,
i.e. `p.map φ = p` — the model for a polynomial defined over `𝔽_q`.

Then `φ` carries roots of `p` to roots of `p`, so it acts as a permutation `rootPerm φ p hp` of the
zero locus `V = {x : K // p.eval x = 0}`.  When `K` is finite, Wave 1 gives

`Z(V, T) = (1 - T)^{-#Fix} · ∏_{c} (1 - T^{|c|})^{-1}`,

a rational function of `T`.  This is the Hasse–Weil zeta function of the `dim 0` variety `V`
under Frobenius, and the fixed points of `rootPerm ^ m` are exactly the roots fixed by `φ ^ m`
— the model for "`V(𝔽_{q^m})`".
-/

namespace RHDirect
namespace HasseWeil

open PowerSeries

noncomputable section

section Polynomial

variable {K : Type*} [Field K]

/-- A field automorphism commutes with polynomial evaluation against the moved coefficients. -/
theorem eval_map_apply (φ : K ≃+* K) (p : Polynomial K) (x : K) :
    (p.map (φ : K →+* K)).eval (φ x) = φ (p.eval x) := by
  rw [Polynomial.eval_map]
  exact Polynomial.eval₂_at_apply (φ : K →+* K) x

/-- **Frobenius acts on the zero locus of a polynomial defined over the fixed field.** -/
def rootPerm (φ : K ≃+* K) (p : Polynomial K) (hp : p.map (φ : K →+* K) = p) :
    Equiv.Perm {x : K // p.eval x = 0} where
  toFun x := ⟨φ x.1, by
    have h := eval_map_apply φ p x.1
    rw [hp] at h
    rw [h, x.2, map_zero]⟩
  invFun y := ⟨φ.symm y.1, by
    have h := eval_map_apply φ p (φ.symm y.1)
    rw [hp] at h
    simp only [RingEquiv.apply_symm_apply] at h
    have h2 : φ (p.eval (φ.symm y.1)) = 0 := by rw [← h, y.2]
    exact (map_eq_zero_iff φ φ.injective).mp h2⟩
  left_inv x := by
    ext
    simp
  right_inv y := by
    ext
    simp

/-- The underlying map of `rootPerm`. -/
@[simp] theorem rootPerm_apply (φ : K ≃+* K) (p : Polynomial K)
    (hp : p.map (φ : K →+* K) = p) (x : {x : K // p.eval x = 0}) :
    (rootPerm φ p hp x).1 = φ x.1 := rfl

/-- **Fixed points of the induced permutation are roots fixed by the automorphism.** -/
theorem rootPerm_fixed_iff (φ : K ≃+* K) (p : Polynomial K)
    (hp : p.map (φ : K →+* K) = p) (x : {x : K // p.eval x = 0}) :
    rootPerm φ p hp x = x ↔ φ x.1 = x.1 := by
  constructor
  · intro h
    exact congrArg Subtype.val h
  · intro h
    ext
    exact h

/-- The iterates of `rootPerm` are the iterates of `φ`. -/
theorem rootPerm_pow_apply (φ : K ≃+* K) (p : Polynomial K)
    (hp : p.map (φ : K →+* K) = p) (m : ℕ) :
    ∀ x : {x : K // p.eval x = 0}, ((rootPerm φ p hp ^ m) x).1 = (φ ^ m) x.1 := by
  induction m with
  | zero => intro x; rfl
  | succ m ih =>
    intro x
    rw [pow_succ, pow_succ, Equiv.Perm.mul_apply, ih, rootPerm_apply]
    rfl

end Polynomial

section Finite

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

/-- **Point counts of the induced permutation are counts of roots fixed by `φ ^ m`.** -/
theorem fixedCount_rootPerm (φ : K ≃+* K) (p : Polynomial K)
    (hp : p.map (φ : K →+* K) = p) (m : ℕ) :
    fixedCount (rootPerm φ p hp) m
      = Nat.card {x : K // p.eval x = 0 ∧ (φ ^ m) x = x} := by
  refine Nat.card_congr ?_
  refine
    { toFun := fun y => ⟨y.1.1, y.1.2, ?_⟩
      invFun := fun x => ⟨⟨x.1, x.2.1⟩, ?_⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  · rw [← rootPerm_pow_apply φ p hp m y.1]
    exact congrArg Subtype.val y.2
  · apply Subtype.ext
    rw [rootPerm_pow_apply]
    exact x.2.2

/-- **W2 headline.**  The Hasse–Weil zeta function of the `dim 0` variety `{x | p(x) = 0}` under
the automorphism `φ` is rational, with explicit denominator. -/
theorem zetaFinite_rootPerm_eq (φ : K ≃+* K) (p : Polynomial K)
    (hp : p.map (φ : K →+* K) = p) :
    zetaFinite (rootPerm φ p hp)
      = (((1 - PowerSeries.X) ^ Nat.card {x : {x : K // p.eval x = 0} //
            rootPerm φ p hp x = x})
          * ∏ c ∈ (rootPerm φ p hp).cycleFactorsFinset,
              (1 - PowerSeries.X ^ c.support.card) : PowerSeries ℚ)⁻¹ :=
  zetaFinite_eq_prod_inv_fixed _

/-- Multiplicative form of the W2 headline. -/
theorem zetaFinite_rootPerm_mul_eq_one (φ : K ≃+* K) (p : Polynomial K)
    (hp : p.map (φ : K →+* K) = p) :
    zetaFinite (rootPerm φ p hp)
      * (((1 - PowerSeries.X) ^ Nat.card {x : {x : K // p.eval x = 0} //
            rootPerm φ p hp x = x})
          * ∏ c ∈ (rootPerm φ p hp).cycleFactorsFinset,
              (1 - PowerSeries.X ^ c.support.card)) = 1 :=
  zetaFinite_mul_prod_fixed_eq_one _

end Finite

end

end HasseWeil
end RHDirect
