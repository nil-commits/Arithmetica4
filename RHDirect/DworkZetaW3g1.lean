/-
Copyright: reference implementation for the ORACLE P3 (Dwork / Hasse–Weil) campaign.
Wave 3b'-general, step 1: `X ^ q - X` divides `X ^ (q ^ k) - X`.
-/
import RHDirect.DworkZetaW3bp

/-!
# `RHDirect.DworkZetaW3g1`

Step 1 of route B (§17.4).  For every `q`, the polynomial `X ^ q - X` divides `X ^ (q ^ k) - X`
for every `k`.

The induction uses only `A - B ∣ A ^ n - B ^ n` and the fact that `X ^ q ≡ X` modulo
`X ^ q - X`.
-/

namespace RHDirect
namespace HasseWeil

open Polynomial

/-- **Step 1.**  `X ^ q - X ∣ X ^ (q ^ k) - X` for `q > 0`. -/
theorem X_pow_sub_X_dvd_X_pow_pow_sub_X {R : Type*} [CommRing R] (q : ℕ) (k : ℕ) :
    (Polynomial.X ^ q - Polynomial.X : Polynomial R) ∣
      Polynomial.X ^ (q ^ k) - Polynomial.X := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, pow_mul]
    have h2 : (Polynomial.X ^ q - Polynomial.X : Polynomial R) ∣
        (Polynomial.X ^ (q ^ k)) ^ q - Polynomial.X ^ q :=
      dvd_trans ih (sub_dvd_pow_sub_pow _ _ q)
    have h3 : (Polynomial.X ^ q - Polynomial.X : Polynomial R) ∣
        Polynomial.X ^ q - Polynomial.X := dvd_refl _
    have h4 : (Polynomial.X ^ q - Polynomial.X : Polynomial R) ∣
        ((Polynomial.X ^ (q ^ k)) ^ q - Polynomial.X ^ q)
          + (Polynomial.X ^ q - Polynomial.X) :=
      dvd_add h2 h3
    have h5 : ((((Polynomial.X ^ (q ^ k)) ^ q : Polynomial R) - Polynomial.X ^ q)
          + (Polynomial.X ^ q - Polynomial.X))
        = ((Polynomial.X ^ (q ^ k)) ^ q : Polynomial R) - Polynomial.X := by ring
    rwa [h5] at h4

end HasseWeil
end RHDirect
