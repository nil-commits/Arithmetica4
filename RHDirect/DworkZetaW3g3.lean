/-
Copyright: reference implementation for the ORACLE P3 (Dwork / Hasse–Weil) campaign.
Wave 3b'-general, step 3: `X ^ (p ^ m) - X` is separable in characteristic `p`.
-/
import RHDirect.DworkZetaW3g1

/-!
# `RHDirect.DworkZetaW3g3`

Step 3 of route B (§17.4).  In a field of characteristic `p`, the polynomial `X ^ (p ^ m) - X`
has derivative `-1`, hence is separable.
-/

namespace RHDirect
namespace HasseWeil

open Polynomial

/-- **Step 3.**  `X ^ (p ^ m) - X` is separable over a field of characteristic `p`, for `m > 0`. -/
theorem separable_X_pow_pow_sub_X {K : Type*} [Field K] (p m : ℕ) [CharP K p] (hm : 0 < m) :
    (Polynomial.X ^ (p ^ m) - Polynomial.X : Polynomial K).Separable := by
  have hcast : ((p ^ m : ℕ) : K) = 0 := by
    rw [Nat.cast_pow, CharP.cast_eq_zero]
    exact zero_pow (by omega)
  have hderiv : (Polynomial.X ^ (p ^ m) - Polynomial.X : Polynomial K).derivative = -1 := by
    rw [map_sub, Polynomial.derivative_X_pow, Polynomial.derivative_X, hcast]
    simp
  rw [Polynomial.separable_def, hderiv]
  exact ⟨0, -1, by ring⟩

end HasseWeil
end RHDirect
