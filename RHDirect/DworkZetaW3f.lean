/-
Copyright: reference implementation for the ORACLE P3 (Dwork / Hasse–Weil) campaign.
Wave 3f: cell-decomposition rationality, and `ℙ^n`.
-/
import RHDirect.DworkZetaW3e
import Mathlib.LinearAlgebra.Projectivization.Cardinality

/-!
# `RHDirect.DworkZetaW3f`

The mechanism that actually proves rationality for toric and projective varieties is a *cell
decomposition*: if the point counts have the shape `N_m = ∑_i c_i · α_i ^ m` with `c_i ∈ ℕ`, then

`Z(V, T) = ∏_i (1 - α_i T) ^ (-c_i)`,

a rational function.  This file proves that, and gets `ℙ^n` as the main instance:

* `zetaSeq_sum`            : `Z` of `m ↦ ∑_i c_i α_i^m` is `∏_i geomSeq (α_i) ^ (c_i)`
* `card_projSpace`         : `#ℙ^n(K) = ∑_{i<n+1} #K ^ i`
* `zeta_projectiveSpace`   : `Z(ℙ^n/𝔽_q, T) = ∏_{i=0}^{n} (1 - q^i T)⁻¹`
-/

namespace RHDirect
namespace HasseWeil

open PowerSeries
open scoped LinearAlgebra.Projectivization

noncomputable section

/-! ## The cell-decomposition theorem -/

theorem zetaSeq_zero : zetaSeq (fun _ => (0 : ℚ)) = 1 := by
  unfold zetaSeq
  have hzero : (PowerSeries.mk fun n => (0 : ℚ) / n) = (0 : PowerSeries ℚ) := by
    ext n
    simp
  rw [hzero, expSeries_zero]

theorem zetaSeq_pow (α : ℚ) : zetaSeq (fun m => α ^ m) = geomSeq α :=
  zeta_affine_line α

/-- `Z` of a single cell `m ↦ c · α ^ m` is `geomSeq α ^ c`. -/
theorem zetaSeq_const_mul_pow (c : ℕ) (α : ℚ) :
    zetaSeq (fun m => (c : ℚ) * α ^ m) = (geomSeq α) ^ c := by
  induction c with
  | zero => simpa using zetaSeq_zero
  | succ c ih =>
    have h : (fun m => ((c + 1 : ℕ) : ℚ) * α ^ m)
        = (fun m => (c : ℚ) * α ^ m) + (fun m => α ^ m) := by
      funext m
      simp only [Pi.add_apply]
      push_cast
      ring
    rw [h, zetaSeq_add, ih, zetaSeq_pow, pow_succ]

/-- **Cell decomposition.**  If `N_m = ∑_i c_i · α_i ^ m` with `c_i ∈ ℕ`, then
`Z = ∏_i (1 - α_i T) ^ (-c_i)`; in particular it is rational. -/
theorem zetaSeq_sum {ι : Type*} (s : Finset ι) (c : ι → ℕ) (α : ι → ℚ) :
    zetaSeq (fun m => ∑ i ∈ s, (c i : ℚ) * α i ^ m)
      = ∏ i ∈ s, (geomSeq (α i)) ^ (c i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty, Finset.prod_empty]
    exact zetaSeq_zero
  | insert a s ha ih =>
    have hsplit : (fun m => ∑ i ∈ insert a s, (c i : ℚ) * α i ^ m)
        = (fun m => (c a : ℚ) * α a ^ m)
          + (fun m => ∑ i ∈ s, (c i : ℚ) * α i ^ m) := by
      funext m
      rw [Finset.sum_insert ha]
      rfl
    rw [hsplit, zetaSeq_add, zetaSeq_const_mul_pow, ih, Finset.prod_insert ha]

/-! ## The projective space `ℙ^n` -/

/-- `ℙ^n` over `K`, as the projectivisation of `K^(n+1)`. -/
abbrev ProjSpace (n : ℕ) (K : Type*) [DivisionRing K] : Type _ := ℙ K (Fin (n + 1) → K)

/-- **`#ℙ^n(K) = ∑_{i<n+1} #K ^ i`.** -/
theorem card_projSpace (n : ℕ) (K : Type*) [Field K] [Fintype K] :
    Nat.card (ProjSpace n K) = ∑ i ∈ Finset.range (n + 1), Nat.card K ^ i := by
  have hfr : Module.finrank K (Fin (n + 1) → K) = n + 1 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  exact Projectivization.card_of_finrank K (Fin (n + 1) → K) hfr

/-- **`N_m(ℙ^n) = ∑_{i<n+1} q^{im}`**: apply at a field with `q ^ m` elements. -/
theorem pointCount_projSpace (n : ℕ) (K : Type*) [Field K] [Fintype K] (q m : ℕ)
    (hK : Nat.card K = q ^ m) :
    Nat.card (ProjSpace n K) = ∑ i ∈ Finset.range (n + 1), (q ^ i) ^ m := by
  rw [card_projSpace]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [hK, ← pow_mul, ← pow_mul, Nat.mul_comm]

/-- **`Z(ℙ^n/𝔽_q, T) = ∏_{i=0}^{n} (1 - q^i T)⁻¹`.** -/
theorem zeta_projectiveSpace (n : ℕ) (q : ℚ) :
    zetaSeq (fun m => ∑ i ∈ Finset.range (n + 1), (q ^ i) ^ m)
      = ∏ i ∈ Finset.range (n + 1), geomSeq (q ^ i) := by
  have h := zetaSeq_sum (Finset.range (n + 1)) (fun _ => 1) (fun i => q ^ i)
  simpa using h

/-- The same, with the denominator made explicit. -/
theorem zeta_projectiveSpace_den (n : ℕ) (q : ℚ) :
    zetaSeq (fun m => ∑ i ∈ Finset.range (n + 1), (q ^ i) ^ m)
      * ∏ i ∈ Finset.range (n + 1), (1 - PowerSeries.C (q ^ i) * PowerSeries.X) = 1 := by
  rw [zeta_projectiveSpace]
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_eq_one (fun i _ => geomSeq_mul_one_sub (q ^ i))

end

end HasseWeil
end RHDirect
