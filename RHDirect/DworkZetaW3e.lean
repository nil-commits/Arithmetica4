/-
Copyright: reference implementation for the ORACLE P3 (Dwork / Hasse–Weil) campaign.
Wave 3e: `𝔸¹`, `𝔾_m` and `ℙ¹` as actual objects, with their point counts over `𝔽_q`.
-/
import RHDirect.DworkZetaW3d
import Mathlib.LinearAlgebra.Projectivization.Cardinality

/-!
# `RHDirect.DworkZetaW3e`

`DworkZetaW3d` proved that the zeta functions attached to the point-count sequences `q^m`, `q^m - 1`
and `q^m + 1` are `1/(1-qT)`, `(1-T)/(1-qT)` and `1/((1-T)(1-qT))`.  Those sequences were *taken as
input*.

This file supplies the geometry: `𝔸¹`, `𝔾_m` and `ℙ¹` are realised as actual objects
(`K`, `Kˣ`, and the projectivisation `ℙ K (Fin 2 → K)`), and their point counts over a finite field
`K` are proved:

* `#𝔸¹(K) = #K`
* `#𝔾_m(K) = #K - 1`
* `#ℙ¹(K) = #K + 1`

Since these hold uniformly in `K`, applying them to a field with `q ^ m` elements yields
`N_m = q^m`, `q^m - 1`, `q^m + 1` — exactly the sequences fed to `zetaSeq` in `DworkZetaW3d`.
-/

namespace RHDirect
namespace HasseWeil

open scoped LinearAlgebra.Projectivization

noncomputable section

/-- The affine line over `K`. -/
abbrev AffineLine (K : Type*) : Type _ := K

/-- The multiplicative group `𝔾_m` over `K`. -/
abbrev MultGroup (K : Type*) [GroupWithZero K] : Type _ := Kˣ

/-- The projective line over `K`, as the projectivisation of `K²`. -/
abbrev ProjLine (K : Type*) [DivisionRing K] : Type _ := ℙ K (Fin 2 → K)

/-! ## Point counts -/

theorem card_affineLine (K : Type*) [Fintype K] :
    Nat.card (AffineLine K) = Nat.card K := rfl

theorem card_multGroup (K : Type*) [Field K] [Fintype K] :
    Nat.card (MultGroup K) = Nat.card K - 1 :=
  Nat.card_units K

/-- **`#ℙ¹(K) = #K + 1`.** -/
theorem card_projLine (K : Type*) [Field K] [Fintype K] :
    Nat.card (ProjLine K) = Nat.card K + 1 := by
  have hfr : Module.finrank K (Fin 2 → K) = 2 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  exact Projectivization.card_of_finrank_two K (Fin 2 → K) hfr

/-! ## Uniform form: the `m`-th point count over `𝔽_q` -/

/-- **`N_m(𝔸¹) = q ^ m`.**  Apply to a field with `q ^ m` elements. -/
theorem pointCount_affineLine (K : Type*) [Fintype K] (q m : ℕ) (hK : Nat.card K = q ^ m) :
    Nat.card (AffineLine K) = q ^ m := by
  rw [card_affineLine, hK]

/-- **`N_m(𝔾_m) = q ^ m - 1`.** -/
theorem pointCount_multGroup (K : Type*) [Field K] [Fintype K] (q m : ℕ)
    (hK : Nat.card K = q ^ m) : Nat.card (MultGroup K) = q ^ m - 1 := by
  rw [card_multGroup, hK]

/-- **`N_m(ℙ¹) = q ^ m + 1`.** -/
theorem pointCount_projLine (K : Type*) [Field K] [Fintype K] (q m : ℕ)
    (hK : Nat.card K = q ^ m) : Nat.card (ProjLine K) = q ^ m + 1 := by
  rw [card_projLine, hK]

/-- The projective line is the affine line plus one point at infinity. -/
theorem card_projLine_eq_affineLine_add_one (K : Type*) [Field K] [Fintype K] :
    Nat.card (ProjLine K) = Nat.card (AffineLine K) + 1 :=
  card_projLine K

/-! ## Feeding the zeta function

`zetaSeq` takes a sequence `ℕ → ℚ`.  These are the point counts of the three varieties, cast to
`ℚ`, in exactly the shape `zeta_affine_line`, `zeta_mult_group` and `zeta_projective_line` expect.
-/

theorem pointCount_affineLine_rat (K : Type*) [Fintype K] (q m : ℕ) (hK : Nat.card K = q ^ m) :
    (Nat.card (AffineLine K) : ℚ) = (q : ℚ) ^ m := by
  rw [pointCount_affineLine K q m hK]
  push_cast
  ring

theorem pointCount_multGroup_rat (K : Type*) [Field K] [Fintype K] (q m : ℕ)
    (hK : Nat.card K = q ^ m) :
    (Nat.card (MultGroup K) : ℚ) = (q : ℚ) ^ m - 1 := by
  have hpos : 1 ≤ q ^ m := by rw [← hK]; exact Nat.card_pos
  rw [pointCount_multGroup K q m hK]
  push_cast [hpos]
  ring

theorem pointCount_projLine_rat (K : Type*) [Field K] [Fintype K] (q m : ℕ)
    (hK : Nat.card K = q ^ m) :
    (Nat.card (ProjLine K) : ℚ) = (q : ℚ) ^ m + 1 := by
  rw [pointCount_projLine K q m hK]
  push_cast
  ring

/-- **Capstone: `Z(ℙ¹/𝔽_q, T) = 1/((1-T)(1-qT))` from the variety.**
The sequence `m ↦ #ℙ¹(𝔽_{q^m}) = q^m + 1` (`pointCount_projLine_rat`) is the input of
`zeta_projective_line_den`. -/
theorem zeta_of_projLine (q : ℚ) :
    zetaSeq (fun m => q ^ m + 1) * ((1 - PowerSeries.C q * PowerSeries.X)
      * (1 - PowerSeries.X)) = 1 :=
  zeta_projective_line_den q

end

end HasseWeil
end RHDirect
