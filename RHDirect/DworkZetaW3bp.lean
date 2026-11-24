/-
Copyright: reference implementation for the ORACLE P3 (Dwork / Hasse–Weil) campaign.
Wave 3b': the fixed-point count `N_m = p ^ m` on the field with `p ^ m` elements.
-/
import RHDirect.DworkZetaW3ab
import Mathlib.FieldTheory.Finite.GaloisField

/-!
# `RHDirect.DworkZetaW3bp`

Wave 3b identified `#Fix(φ ^ m)` with the solutions of `x ^ (p ^ m) = x`.  This file closes the
count in the case that matters for the model: when the field *is* `𝔽_{p^m}` (i.e. `Nat.card K = p^m`),
every element is fixed, so `N_m = p ^ m`.

The engine is `FiniteField.pow_card`, the statement that `a ^ #K = a` in a finite field — the
group-theoretic content of `𝔽_q^×` having order `q - 1`.
-/

namespace RHDirect
namespace HasseWeil

noncomputable section

/-- `𝔽_{p^m}` carries a `Fintype` structure (it is `Finite`, and the choice is irrelevant). -/
instance galoisFieldFintype (p m : ℕ) [Fact (Nat.Prime p)] [NeZero m] :
    Fintype (GaloisField p m) :=
  Fintype.ofFinite _

/-- On a field with `p ^ m` elements, `φ ^ m` is the identity. -/
theorem frobeniusAut_pow_card_eq_id (K : Type*) [Field K] [Fintype K] (p m : ℕ) [ExpChar K p]
    (h : Nat.card K = p ^ m) (x : K) :
    ((frobeniusAut K p) ^ m) x = x := by
  rw [frobeniusAut_pow_apply K p m]
  have h2 : p ^ m = Fintype.card K := by rw [← h, Nat.card_eq_fintype_card]
  rw [h2]
  exact FiniteField.pow_card x

/-- **W3b′.**  On a field with `p ^ m` elements every point is fixed by `φ ^ m`, so `N_m = p ^ m`. -/
theorem natCard_fixed_eq_pow_of_card (K : Type*) [Field K] [Fintype K]
    (p m : ℕ) [ExpChar K p] (h : Nat.card K = p ^ m) :
    Nat.card {x : K // ((frobeniusAut K p) ^ m) x = x} = p ^ m := by
  rw [Nat.card_congr (Equiv.subtypeUnivEquiv (frobeniusAut_pow_card_eq_id K p m h)), h]

/-- **W3b′.**  Concrete instance: Frobenius `^ m` fixes every element of `𝔽_{p^m}`. -/
theorem galoisField_frobeniusAut_pow (p m : ℕ) [Fact (Nat.Prime p)] [NeZero m] :
    ∀ x : GaloisField p m, ((frobeniusAut (GaloisField p m) p) ^ m) x = x := by
  intro x
  exact frobeniusAut_pow_card_eq_id (GaloisField p m) p m (GaloisField.card p m (NeZero.ne m)) x

/-- **W3b′.**  `N_m = p ^ m` on `𝔽_{p^m}`. -/
theorem galoisField_natCard_fixed (p m : ℕ) [Fact (Nat.Prime p)] [NeZero m] :
    Nat.card {x : GaloisField p m // ((frobeniusAut (GaloisField p m) p) ^ m) x = x}
      = p ^ m :=
  natCard_fixed_eq_pow_of_card (GaloisField p m) p m (GaloisField.card p m (NeZero.ne m))

end

end HasseWeil
end RHDirect
