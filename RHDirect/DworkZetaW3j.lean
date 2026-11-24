/-
Copyright: reference implementation for the ORACLE P3 (Dwork / Hasse–Weil) campaign.
Wave 3j: the Lefschetz shape — what Dwork's trace formula produces.
-/
import RHDirect.DworkZetaW3i

/-!
# `RHDirect.DworkZetaW3j`

Dwork's trace formula says that the point counts of a variety over `𝔽_q` have the shape

`N_m = ∑_i c_i · α_i ^ m`   (`c_i ∈ ℤ`, `α_i` algebraic numbers),

an alternating sum of traces of Frobenius.  Given that shape, rationality of `Z` is immediate:

`Z(V, T) = ∏_i (1 - α_i T) ^ (-c_i)`.

This file proves the implication, in the alternating form (positive and negative parts separated so
that no `zpow` on power series is needed), and instantiates it at the elliptic-curve shape
`N_m = q^m + 1 - α^m - β^m`, which gives the classical
`Z(E, T) = (1 - aT + qT²) / ((1 - T)(1 - qT))`.

**What this is not.**  Dwork's theorem is the statement that *every* variety has this shape.  That is
the trace formula, and it is not proved here.  This file proves the `trace formula ⇒ rationality`
half.
-/

namespace RHDirect
namespace HasseWeil

open PowerSeries

noncomputable section

/-- `(∑ q^n T^n)⁻¹ = 1 - qT`. -/
theorem geomSeq_inv (r : ℚ) : (geomSeq r)⁻¹ = (1 - PowerSeries.C r * PowerSeries.X) := by
  rw [geomSeq_eq_inv, eq_comm, PowerSeries.eq_inv_iff_mul_eq_one]
  · exact PowerSeries.mul_inv_cancel _ (by
      rw [show constantCoeff (1 - PowerSeries.C r * PowerSeries.X : PowerSeries ℚ) = 1 from by
        rw [map_sub, map_one, map_mul, PowerSeries.constantCoeff_C,
          PowerSeries.constantCoeff_X, mul_zero, sub_zero]]
      exact one_ne_zero)
  · rw [PowerSeries.constantCoeff_inv]
    simp

/-! ## The Lefschetz shape -/

set_option maxHeartbeats 1000000 in
/-- **Trace formula ⇒ rationality.**  If `N_m = ∑_i c_i α_i^m - ∑_j d_j β_j^m`, then

`Z = (∏_i (1 - α_i T)⁻¹ ^ c_i) · (∏_j (1 - β_j T)⁻¹ ^ d_j)⁻¹`. -/
theorem zetaSeq_lefschetz {ι κ : Type*} (spos : Finset ι) (sneg : Finset κ)
    (cp : ι → ℕ) (cn : κ → ℕ) (α : ι → ℚ) (β : κ → ℚ) :
    zetaSeq (fun m => (∑ i ∈ spos, (cp i : ℚ) * α i ^ m)
        - (∑ j ∈ sneg, (cn j : ℚ) * β j ^ m))
      = (∏ i ∈ spos, (geomSeq (α i)) ^ (cp i))
        * (∏ j ∈ sneg, (geomSeq (β j)) ^ (cn j))⁻¹ := by
  have hfun : (fun m => (∑ i ∈ spos, (cp i : ℚ) * α i ^ m)
        - (∑ j ∈ sneg, (cn j : ℚ) * β j ^ m))
      = ((fun m => ∑ i ∈ spos, (cp i : ℚ) * α i ^ m)
        - (fun m => ∑ j ∈ sneg, (cn j : ℚ) * β j ^ m)) := rfl
  rw [hfun, zetaSeq_sub, zetaSeq_sum, zetaSeq_sum]

/-! ## The elliptic-curve shape -/

/-- **`N_m = q^m + 1 - α^m - β^m`** (the Hasse trace formula for an elliptic curve). -/
theorem zeta_elliptic_shape (q α β : ℚ) :
    zetaSeq (fun m => q ^ m + 1 - α ^ m - β ^ m)
      = geomSeq q * geomSeq 1 * (geomSeq α)⁻¹ * (geomSeq β)⁻¹ := by
  have h : (fun m => q ^ m + 1 - α ^ m - β ^ m)
      = (fun m => q ^ m + 1) - (fun m => α ^ m) - (fun m => β ^ m) := rfl
  rw [h]
  rw [show (fun m => q ^ m + 1) = (fun m => q ^ m) + (fun _ => (1 : ℚ)) from rfl]
  rw [zetaSeq_sub, zetaSeq_sub, zetaSeq_add, zeta_affine_line, zetaSeq_one,
    zeta_affine_line, zeta_affine_line]

/-- **The classical elliptic-curve zeta function**, in explicit rational form:
`Z(E,T) · (1 - T)(1 - qT) = (1 - αT)(1 - βT)`.  With `α + β = a` and `αβ = q` this is
`(1 - aT + qT²) / ((1 - T)(1 - qT))`. -/
theorem zeta_elliptic_den (q α β : ℚ) :
    zetaSeq (fun m => q ^ m + 1 - α ^ m - β ^ m)
        * ((1 - PowerSeries.C q * PowerSeries.X) * (1 - PowerSeries.X))
      = (1 - PowerSeries.C α * PowerSeries.X) * (1 - PowerSeries.C β * PowerSeries.X) := by
  rw [zeta_elliptic_shape, geomSeq_inv, geomSeq_inv]
  have hq : geomSeq q * (1 - PowerSeries.C q * PowerSeries.X) = 1 := geomSeq_mul_one_sub q
  have h1 : geomSeq (1 : ℚ) * (1 - PowerSeries.X) = 1 := by
    rw [← one_sub_C_one_mul_X]; exact geomSeq_mul_one_sub 1
  calc geomSeq q * geomSeq 1 * (1 - PowerSeries.C α * PowerSeries.X)
        * (1 - PowerSeries.C β * PowerSeries.X)
        * ((1 - PowerSeries.C q * PowerSeries.X) * (1 - PowerSeries.X))
      = (1 - PowerSeries.C α * PowerSeries.X) * (1 - PowerSeries.C β * PowerSeries.X)
        * ((geomSeq q * (1 - PowerSeries.C q * PowerSeries.X))
          * (geomSeq (1 : ℚ) * (1 - PowerSeries.X))) := by ring
    _ = (1 - PowerSeries.C α * PowerSeries.X) * (1 - PowerSeries.C β * PowerSeries.X)
        * (1 * 1) := by rw [hq, h1]
    _ = (1 - PowerSeries.C α * PowerSeries.X) * (1 - PowerSeries.C β * PowerSeries.X) := by ring

end

end HasseWeil
end RHDirect
