/-
Copyright: reference implementation for the ORACLE P3 (Dwork / Hasse–Weil) campaign.
Wave 3a/3b: the actual Frobenius of a finite field, and its fixed points as roots of X^(q^m) - X.
-/
import RHDirect.DworkZetaW3
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.Separable

/-!
# `RHDirect.DworkZetaW3ab`

Wave 2 used an *arbitrary* automorphism `φ : K ≃+* K` as a stand-in for Frobenius.  This file
supplies the real thing and identifies its fixed points.

* **W3a** — on a finite field `K` of characteristic `p`, the Frobenius endomorphism
  `frobenius K p : x ↦ x ^ p` is bijective, hence an automorphism `frobeniusAut K p`.  Polynomials
  with coefficients in the prime field `𝔽_p` are fixed by it.
* **W3b** — the fixed points of `frobeniusAut K p ^ m` are exactly the roots of
  `X ^ (p ^ m) - X`, i.e. the solutions of `x ^ (p ^ m) = x`: the model for `𝔽_{p^m}`.
-/

namespace RHDirect
namespace HasseWeil

open Polynomial

noncomputable section

/-- **W3a.**  On a finite field the Frobenius endomorphism is bijective. -/
theorem frobenius_bijective (K : Type*) [Field K] [Fintype K] (p : ℕ) [ExpChar K p] :
    Function.Bijective (frobenius K p) :=
  ⟨frobenius_inj K p, Finite.injective_iff_surjective.mp (frobenius_inj K p)⟩

/-- **W3a.**  The Frobenius of a finite field, as a field automorphism. -/
def frobeniusAut (K : Type*) [Field K] [Fintype K] (p : ℕ) [ExpChar K p] : K ≃+* K :=
  RingEquiv.ofBijective (frobenius K p) (frobenius_bijective K p)

@[simp] theorem frobeniusAut_apply (K : Type*) [Field K] [Fintype K] (p : ℕ) [ExpChar K p]
    (x : K) : frobeniusAut K p x = x ^ p :=
  frobenius_def p x

/-- The iterates of Frobenius are `x ↦ x ^ (p ^ m)`. -/
theorem frobeniusAut_pow_apply (K : Type*) [Field K] [Fintype K] (p : ℕ) [ExpChar K p]
    (m : ℕ) :
    ∀ x : K, ((frobeniusAut K p) ^ m) x = x ^ (p ^ m) := by
  induction m with
  | zero => intro x; simp
  | succ m ih =>
    intro x
    rw [pow_succ]
    show ((frobeniusAut K p) ^ m) ((frobeniusAut K p) x) = x ^ (p ^ (m + 1))
    rw [ih, frobeniusAut_apply, ← pow_mul, pow_succ']

/-- **W3a.**  The Frobenius fixes the prime field. -/
theorem frobeniusAut_algebraMap_zmod (K : Type*) [Field K] [Fintype K] (p : ℕ) [ExpChar K p]
    [Algebra (ZMod p) K] [Fact (Nat.Prime p)] (x : ZMod p) :
    frobeniusAut K p (algebraMap (ZMod p) K x) = algebraMap (ZMod p) K x := by
  rw [frobeniusAut_apply, ← map_pow, ZMod.pow_card]

/-- **W3a.**  Polynomials with coefficients in `𝔽_p` are fixed by Frobenius. -/
theorem map_frobeniusAut_map_algebraMap (K : Type*) [Field K] [Fintype K] (p : ℕ)
    [ExpChar K p] [Algebra (ZMod p) K] [Fact (Nat.Prime p)] (f : (ZMod p)[X]) :
    (f.map (algebraMap (ZMod p) K)).map (frobeniusAut K p : K →+* K)
      = f.map (algebraMap (ZMod p) K) := by
  rw [Polynomial.map_map]
  congr 1
  exact RingHom.ext (frobeniusAut_algebraMap_zmod K p)

/-- **W3b.**  The fixed points of `φ ^ m` are the roots of `X ^ (p ^ m) - X`. -/
theorem frobeniusAut_pow_fixed_iff_isRoot (K : Type*) [Field K] [Fintype K] [DecidableEq K]
    (p : ℕ) [ExpChar K p] (m : ℕ) (x : K) :
    ((frobeniusAut K p) ^ m) x = x
      ↔ (Polynomial.X ^ (p ^ m) - Polynomial.X : Polynomial K).IsRoot x := by
  rw [frobeniusAut_pow_apply K p m]
  simp [Polynomial.IsRoot, sub_eq_zero]

/-- **W3b.**  The fixed points of `φ ^ m` are exactly the solutions of `x ^ (p ^ m) = x` —
the model for `𝔽_{p^m}`. -/
theorem natCard_fixed_eq (K : Type*) [Field K] [Fintype K] [DecidableEq K]
    (p : ℕ) [ExpChar K p] (m : ℕ) :
    Nat.card {x : K // ((frobeniusAut K p) ^ m) x = x}
      = Nat.card {x : K // x ^ (p ^ m) = x} := by
  refine Nat.card_congr (Equiv.subtypeEquiv (Equiv.refl K) (fun x => ?_))
  rw [Equiv.refl_apply, frobeniusAut_pow_apply K p m]

end

end HasseWeil
end RHDirect
