/-
Copyright: reference implementation for the ORACLE P3 (Dwork / Hasse–Weil) campaign.
-/
import RHDirect.DworkZetaLog

/-!
# `RHDirect.DworkZeta0D`

**Dwork rationality in dimension `0`.**

For a finite type `V` with a permutation `σ` (the Frobenius on the `\bar F_q`-points of a finite
`F_q`-scheme), the Hasse–Weil zeta function is `Z(T) = exp (∑_{m ≥ 1} N_m T^m / m)` with
`N_m = #Fix(σ^m)`.

`zetaFinite_eq_prod_inv` proves that **if** the point counts are those of a disjoint union of
cycles of lengths `d i` — i.e. `N_m = ∑_{i} d i · [d i ∣ m]` — **then**

`Z(T) = ∏_i (1 - T^{d i})⁻¹`,

which is a rational function of `T`.  This is the `dim 0` case of Dwork's theorem / Weil I, and the
only input it leaves open is the combinatorial point-count identity, stated explicitly as `h`.

The assembly itself is unconditional: it rests on `expSeries_add`, `expSeries_neg`,
`expSeries_logOf` (proved in `DworkZetaLog`) and nothing else.
-/

namespace RHDirect
namespace HasseWeil

open PowerSeries

noncomputable section

lemma constantCoeff_one_sub_X_pow {n : ℕ} (hn : 1 ≤ n) :
    constantCoeff (1 - PowerSeries.X ^ n : PowerSeries ℚ) = 1 := by
  rw [map_sub, map_one, map_pow, PowerSeries.constantCoeff_X, zero_pow (by omega), sub_zero]

/-- `exp (-log f) * f = 1` for `f` with constant term `1`. -/
theorem expSeries_neg_logOf_mul {f : PowerSeries ℚ} (h1 : constantCoeff f = 1) :
    expSeries (- PowerSeries.logOf f) * f = 1 := by
  have h0 : constantCoeff (PowerSeries.logOf f) = 0 := PowerSeries.constantCoeff_logOf h1
  rw [expSeries_neg h0, expSeries_logOf h1]
  exact PowerSeries.inv_mul_cancel f (by rw [h1]; exact one_ne_zero)

/-- `exp (-log f) = f⁻¹` for `f` with constant term `1`. -/
theorem expSeries_neg_logOf {f : PowerSeries ℚ} (h1 : constantCoeff f = 1) :
    expSeries (- PowerSeries.logOf f) = f⁻¹ := by
  have h0 : constantCoeff (PowerSeries.logOf f) = 0 := PowerSeries.constantCoeff_logOf h1
  rw [expSeries_neg h0, expSeries_logOf h1]

/-- **Dwork rationality, `dim 0`, product form.**

If the logarithmic point-count series of `σ` decomposes over a finite index set `s` into the
contributions `-log (1 - T^{d i})` of cycles of lengths `d i ≥ 1`, then the Hasse–Weil zeta
function is the finite product `∏_i (1 - T^{d i})⁻¹`. -/
theorem zetaFinite_eq_prod_inv {V : Type*} [Fintype V] {ι : Type*} [DecidableEq ι]
    (σ : Equiv.Perm V) (s : Finset ι) (d : ι → ℕ) (hd : ∀ i ∈ s, 1 ≤ d i)
    (h : zetaLog σ
      = ∑ i ∈ s, - PowerSeries.logOf (1 - PowerSeries.X ^ d i)) :
    zetaFinite σ = ∏ i ∈ s, (1 - PowerSeries.X ^ d i)⁻¹ := by
  have hc : ∀ i ∈ s,
      constantCoeff (- PowerSeries.logOf (1 - PowerSeries.X ^ d i : PowerSeries ℚ)) = 0 := by
    intro i hi
    rw [map_neg, PowerSeries.constantCoeff_logOf (constantCoeff_one_sub_X_pow (hd i hi)), neg_zero]
  rw [zetaFinite, h,
    expSeries_sum s (fun i => - PowerSeries.logOf (1 - PowerSeries.X ^ d i : PowerSeries ℚ)) hc]
  exact Finset.prod_congr rfl fun i hi =>
    expSeries_neg_logOf (constantCoeff_one_sub_X_pow (hd i hi))

/-- **Dwork rationality, `dim 0`, denominator form.**

`Z(T) · ∏_i (1 - T^{d i}) = 1`: the zeta function is the reciprocal of an explicit polynomial,
hence a rational function of `T`. -/
theorem zetaFinite_mul_prod_eq_one {V : Type*} [Fintype V] {ι : Type*} [DecidableEq ι]
    (σ : Equiv.Perm V) (s : Finset ι) (d : ι → ℕ) (hd : ∀ i ∈ s, 1 ≤ d i)
    (h : zetaLog σ
      = ∑ i ∈ s, - PowerSeries.logOf (1 - PowerSeries.X ^ d i)) :
    zetaFinite σ * ∏ i ∈ s, (1 - PowerSeries.X ^ d i) = 1 := by
  rw [zetaFinite_eq_prod_inv σ s d hd h]
  have hterm : ∀ i ∈ s, (1 - PowerSeries.X ^ d i : PowerSeries ℚ)⁻¹
      * (1 - PowerSeries.X ^ d i) = 1 := fun i hi =>
    PowerSeries.inv_mul_cancel _ (by
      rw [constantCoeff_one_sub_X_pow (hd i hi)]
      exact one_ne_zero)
  calc (∏ i ∈ s, (1 - PowerSeries.X ^ d i : PowerSeries ℚ)⁻¹) * ∏ i ∈ s, (1 - PowerSeries.X ^ d i)
      = ∏ i ∈ s, ((1 - PowerSeries.X ^ d i : PowerSeries ℚ)⁻¹ * (1 - PowerSeries.X ^ d i)) :=
        Finset.prod_mul_distrib.symm
    _ = ∏ i ∈ s, (1 : PowerSeries ℚ) := Finset.prod_congr rfl hterm
    _ = 1 := Finset.prod_const_one

end

end HasseWeil
end RHDirect
