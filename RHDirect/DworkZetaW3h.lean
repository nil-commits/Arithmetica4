/-
Copyright: reference implementation for the ORACLE P3 (Dwork / Hasse–Weil) campaign.
Wave 3h: `ℙ^n_K` as a scheme (structure sheaf included), with its structure morphism.
-/
import RHDirect.DworkZetaW3g
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic

/-!
# `RHDirect.DworkZetaW3h`

Waves 3e/3f realised `ℙ^n` as a *finite type* (the `K`-rational points) and counted them.  This
file adds the scheme: `ℙ^n_K` is `Proj` of the homogeneous coordinate ring `K[X₀,…,Xₙ]`.

A `Scheme` is by definition a locally ringed space, so this supplies the structure sheaf.  The
morphism `Proj.toSpecZero` records the structure map to `Spec` of the degree-zero part (the
constants), i.e. the `K`-scheme structure.

**What is not here:** base change, and the comparison between `Scheme`-points of `ℙ^n_K` and
`ProjSpace n K`.  Mathlib has no functor-of-points bridge between `Proj` and
`Projectivization`, and building one is a project, not a lemma.
-/

namespace RHDirect
namespace HasseWeil

noncomputable section

open AlgebraicGeometry

/-- **`ℙ^n_K` as a scheme**: `Proj` of the homogeneous coordinate ring `K[X₀,…,Xₙ]`. -/
def projSpaceScheme (n : ℕ) (K : Type*) [Field K] : Scheme :=
  letI := MvPolynomial.gradedAlgebra (σ := Fin (n + 1)) (R := K)
  AlgebraicGeometry.Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K)

/-- The structure morphism of `ℙ^n_K`, to `Spec` of the degree-zero part. -/
def projSpaceSchemeStruct (n : ℕ) (K : Type*) [Field K] :
    projSpaceScheme n K ⟶
      AlgebraicGeometry.Spec (CommRingCat.of ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K 0)) :=
  letI := MvPolynomial.gradedAlgebra (σ := Fin (n + 1)) (R := K)
  AlgebraicGeometry.Proj.toSpecZero (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K)

/-- `ℙ¹_K` as a scheme. -/
def projLineScheme (K : Type*) [Field K] : Scheme := projSpaceScheme 1 K

end

end HasseWeil
end RHDirect
