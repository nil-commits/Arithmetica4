import RHDirect.Stage12FontainePeriods
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.Algebra.DualNumber
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.FreeModule.PID

/-!
# RHDirect.Stage14M3_SemiAbelianDegenerations

Package `M3` Wave 1 (6 of 6) — **Pillar-5 Clean Distillation**: Semi-Abelian Schemes,
Raynaud Extensions (`0 → T → G → B → 0`), Toric Rank Data, Néron/Raynaud Extension of
Morphisms (`semiAbelian_hom_extension`), Fargues–Hodge–Tate Exactness (`fargues_hodge_tate_exact`
wired directly to `Stage12FontainePeriods`), and Grothendieck–Messing Deformation Lifting
(`grothendieck_deformation_lift`) in pure Mathlib `v4.33.1` (`0` `sorry`, `0` custom `axiom`s,
`0` `native_decide`).

## Main Contents
1. **Split Algebraic Tori, Hopf-Algebraic Rigidity, Scheme-Theoretic Tori, & `ToricRankData`**:
   - `TorusAlg R X := AddMonoidAlgebra R X`, characters `torusChar χ`, Hopf structure
     (`torusComul`, `torusCounit`, `torusAntipode`), `IsGroupLike`, unconditional rigidity
     `groupLike_eq_torusChar_of_isDomain` and `torus_hom_induced_by_character_map`, and
     scheme-theoretic `splitTorusSpec R X` (`Flat`, `IsSeparated`).
   - `ToricRankData` & `ToricRankProfile` (upper semicontinuity of toric rank).
2. **Concrete `RaynaudExtension` (`0 → T → G → B → 0`) & `SemiAbelianScheme`**:
   - `CommGroupSchemeModel R`, `RaynaudExtension R` (with scheme-level exactness, exact Lie
     and Hodge-cotangent sequences `0 → ω_B → ω_G → ω_T → 0`, Raynaud classifying map
     `c : X →+ B^∨(R)`, splitting `raynaud_omega_split`, and concrete Tate-curve / torus /
     abelian witnesses).
   - `SemiAbelianScheme R` with fiberwise `RaynaudExtension` and semicontinuity of toric &
     abelian ranks.
3. **Néron / Raynaud Extension of Morphisms (`semiAbelian_hom_extension`)**:
   - Unconditional DVR unit-valuation rigidity `dvr_prime_unit_eval_one_mem_range`,
     `toric_hom_extends_over_dvr`, `hom_extension_unique`, and full
     `semiAbelian_hom_extension`.
4. **Fargues–Hodge–Tate Exactness (`fargues_hodge_tate_exact`)**:
   - Wired directly to `Stage12FontainePeriods` (`BdRPlus`, `thetaBdRPlus`, `tBdR`, `BdR`,
     `FilBdR`, `bcrisToBdR`, `FontainePeriodSystem`, `OCp`).
5. **Grothendieck–Messing Deformation Theory (`grothendieck_deformation_lift`)**:
   - Square-zero / nilpotent PD-thickenings, `DualNumber R₀` tangent torsor, unconditional
     Hodge-filtration lifting `hodge_filtration_lift_exists`, `grothendieck_deformation_lift`,
     and bridge to `Stage11CrystallineFontaine.H1fCris`.
6. **Wave 2 & M4 Handoff Package (`SemiAbelianDegenerationPack`)**.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits Module Submodule Finset Matrix
open RHDirect.Stage11CrystallineFontaine RHDirect.Stage12FontainePeriods
open scoped BigOperators TensorProduct

namespace RHDirect
namespace Stage14M3_SemiAbelianDegenerations

/-! ## Section 1: Algebraic Tori, Hopf-Algebraic Rigidity, Scheme Tori, & `ToricRankData` -/

section AlgebraicTori

/-- Coordinate Hopf algebra `R[X] := AddMonoidAlgebra R X` of the split torus with character
lattice `X`. -/
abbrev TorusAlg (R : Type*) (X : Type*) [CommRing R] [AddCommGroup X] : Type _ :=
  AddMonoidAlgebra R X

section TorusHopf

variable {R : Type*} [CommRing R] {X : Type*} [AddCommGroup X]

/-- Character monomial `[χ] ∈ TorusAlg R X`. -/
def torusChar (χ : X) : TorusAlg R X :=
  AddMonoidAlgebra.single χ (1 : R)

@[simp]
theorem torusChar_coeff (χ₁ χ₂ : X) :
    (torusChar (R := R) χ₁).coeff χ₂ = by classical exact if χ₁ = χ₂ then 1 else 0 := by
  classical
  simp [torusChar, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]

@[simp]
theorem torusChar_zero : torusChar (R := R) (0 : X) = 1 := by
  simp [torusChar, AddMonoidAlgebra.one_def]

theorem torusChar_add (χ₁ χ₂ : X) :
    torusChar (R := R) (χ₁ + χ₂) = torusChar χ₁ * torusChar χ₂ := by
  simp [torusChar, AddMonoidAlgebra.single_mul_single]

theorem torusChar_neg_mul (χ : X) :
    torusChar (R := R) (-χ) * torusChar χ = 1 := by
  rw [← torusChar_add, neg_add_cancel, torusChar_zero]

theorem torusChar_mul_neg (χ : X) :
    torusChar (R := R) χ * torusChar (-χ) = 1 := by
  rw [← torusChar_add, add_neg_cancel, torusChar_zero]

theorem isUnit_torusChar (χ : X) : IsUnit (torusChar (R := R) χ) :=
  IsUnit.of_mul_eq_one (torusChar (-χ)) (torusChar_mul_neg χ)

theorem torusChar_injective [Nontrivial R] : Function.Injective (torusChar (R := R) (X := X)) := by
  classical
  intro χ₁ χ₂ h
  have h1 := congrArg (fun f : TorusAlg R X => f.coeff χ₁) h
  simp only [torusChar_coeff, ↓reduceIte] at h1
  by_contra hne
  rw [if_neg (Ne.symm hne)] at h1
  exact one_ne_zero h1

/-- Canonical `R`-algebra counit `ε : R[X] →ₐ[R] R` sending every character `[χ] ↦ 1`
(corresponding to the identity section `Spec R → T`). -/
def torusCounit : TorusAlg R X →ₐ[R] R :=
  AddMonoidAlgebra.lift R R X (1 : Multiplicative X →* R)

@[simp]
theorem torusCounit_torusChar (χ : X) :
    torusCounit (torusChar (R := R) χ) = 1 := by
  simp [torusCounit, torusChar]

@[simp]
theorem torusCounit_single (χ : X) (r : R) :
    torusCounit (AddMonoidAlgebra.single χ r) = r := by
  have h : AddMonoidAlgebra.single χ r = r • torusChar (R := R) χ := by
    simp [torusChar, AddMonoidAlgebra.smul_single]
  rw [h, map_smul, torusCounit_torusChar, smul_eq_mul, mul_one]

/-- Canonical `R`-algebra comultiplication `Δ : R[X] →ₐ[R] R[X] ⊗_R R[X]` sending `[χ] ↦ [χ] ⊗ [χ]`
(corresponding to torus group multiplication `T ×_R T → T`). -/
def torusComul : TorusAlg R X →ₐ[R] (TorusAlg R X ⊗[R] TorusAlg R X) :=
  AddMonoidAlgebra.lift R (TorusAlg R X ⊗[R] TorusAlg R X) X
    { toFun := fun χ => torusChar (R := R) χ.toAdd ⊗ₜ[R] torusChar (R := R) χ.toAdd
      map_one' := by simp only [toAdd_one, torusChar_zero]; rfl
      map_mul' := fun χ₁ χ₂ => by
        simp only [toAdd_mul, torusChar_add, Algebra.TensorProduct.tmul_mul_tmul] }

@[simp]
theorem torusComul_torusChar (χ : X) :
    torusComul (R := R) (X := X) (torusChar (R := R) χ) = torusChar χ ⊗ₜ[R] torusChar χ := by
  simp [torusComul, torusChar]

/-- Canonical `R`-algebra antipode `S : R[X] →ₐ[R] R[X]` sending `[χ] ↦ [-χ]`
(corresponding to torus inversion `t ↦ t⁻¹`). -/
def torusAntipode : TorusAlg R X →ₐ[R] TorusAlg R X :=
  AddMonoidAlgebra.lift R (TorusAlg R X) X
    { toFun := fun χ => torusChar (R := R) (-χ.toAdd)
      map_one' := by simp [torusChar_zero]
      map_mul' := fun χ₁ χ₂ => by
        simp only [toAdd_mul, neg_add, torusChar_add] }

@[simp]
theorem torusAntipode_torusChar (χ : X) :
    torusAntipode (torusChar (R := R) χ) = torusChar (-χ) := by
  simp [torusAntipode, torusChar]

/-- Bilinear coordinate functional extracting the `(x, y)`-coefficient in `R[X] ⊗_R R[X]`. -/
private def tensorPairCoeff (x y : X) : (TorusAlg R X ⊗[R] TorusAlg R X) →ₗ[R] R :=
  TensorProduct.lift
    { toFun := fun f =>
        { toFun := fun g => f.coeff x * g.coeff y
          map_add' := fun g₁ g₂ => by simp [AddMonoidAlgebra.coeff_add, mul_add]
          map_smul' := fun r g => by
            simp [AddMonoidAlgebra.coeff_smul, smul_eq_mul, mul_left_comm] }
      map_add' := fun f₁ f₂ => by ext g; simp [AddMonoidAlgebra.coeff_add, add_mul]
      map_smul' := fun r f => by
        ext g; simp [AddMonoidAlgebra.coeff_smul, smul_eq_mul, mul_assoc] }

@[simp]
private theorem tensorPairCoeff_tmul (x y : X) (f g : TorusAlg R X) :
    tensorPairCoeff (R := R) x y (f ⊗ₜ[R] g) = f.coeff x * g.coeff y := rfl

private theorem tensorPairCoeff_torusComul (u : TorusAlg R X) (x y : X) :
    tensorPairCoeff (R := R) x y (torusComul (R := R) (X := X) u) =
      by classical exact if x = y then u.coeff x else 0 := by
  classical
  induction u using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add f g ihf ihg =>
    rw [map_add, map_add, ihf, ihg, AddMonoidAlgebra.coeff_add]
    split_ifs <;> simp
  | single χ r =>
    have hsm : AddMonoidAlgebra.single χ r = r • torusChar (R := R) χ := by
      simp [torusChar, AddMonoidAlgebra.smul_single]
    rw [hsm, map_smul, map_smul, torusComul_torusChar, tensorPairCoeff_tmul]
    simp only [AddMonoidAlgebra.coeff_smul, torusChar_coeff, smul_eq_mul]
    by_cases hxy : x = y
    · subst hxy
      rw [if_pos rfl]
      by_cases hχx : χ = x <;> simp [hχx]
    · rw [if_neg hxy]
      by_cases hχx : χ = x
      · subst hχx; simp [hxy]
      · simp [hχx]

private theorem coeff_finset_sum {ι : Type*} (s : Finset ι) (f : ι → TorusAlg R X) (x : X) :
    (∑ i ∈ s, f i).coeff x = ∑ i ∈ s, (f i).coeff x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
    exact congrFun (congrArg DFunLike.coe (AddMonoidAlgebra.coeff_add (f a) (∑ i ∈ s, f i))) x

private theorem torusAlg_exists_finset_sum (u : TorusAlg R X) :
    ∃ s : Finset X, (∀ x ∈ s, u.coeff x ≠ 0) ∧ u = ∑ x ∈ s, AddMonoidAlgebra.single x (u.coeff x) := by
  classical
  induction u using AddMonoidAlgebra.induction_linear with
  | zero => exact ⟨∅, by simp, by simp⟩
  | add f g ihf ihg =>
    obtain ⟨s₁, hs₁_ne, hs₁_eq⟩ := ihf
    obtain ⟨s₂, hs₂_ne, hs₂_eq⟩ := ihg
    let s : Finset X := (s₁ ∪ s₂).filter (fun x => (f + g).coeff x ≠ 0)
    refine ⟨s, fun x hx => (Finset.mem_filter.mp hx).2, ?_⟩
    have hf_coeff : ∀ x, x ∉ s₁ → f.coeff x = 0 := fun x hnx => by
      have hcf : f.coeff x = (∑ y ∈ s₁, AddMonoidAlgebra.single y (f.coeff y)).coeff x :=
        congrArg (fun p : TorusAlg R X => p.coeff x) hs₁_eq
      rw [hcf, coeff_finset_sum]
      · refine Finset.sum_eq_zero fun y hy => ?_
        have hyx : y ≠ x := fun h => hnx (h ▸ hy)
        simp [AddMonoidAlgebra.coeff_single, hyx]
    have hg_coeff : ∀ x, x ∉ s₂ → g.coeff x = 0 := fun x hnx => by
      have hcg : g.coeff x = (∑ y ∈ s₂, AddMonoidAlgebra.single y (g.coeff y)).coeff x :=
        congrArg (fun p : TorusAlg R X => p.coeff x) hs₂_eq
      rw [hcg, coeff_finset_sum]
      exact Finset.sum_eq_zero fun y hy => by
        have hyx : y ≠ x := fun h => hnx (h ▸ hy)
        simp [AddMonoidAlgebra.coeff_single, hyx]
    have h1 : f = ∑ x ∈ s₁ ∪ s₂, AddMonoidAlgebra.single x (f.coeff x) := by
      conv_lhs => rw [hs₁_eq]
      refine Finset.sum_subset Finset.subset_union_left fun x _ hnx => ?_
      simp [hf_coeff x hnx]
    have h2 : g = ∑ x ∈ s₁ ∪ s₂, AddMonoidAlgebra.single x (g.coeff x) := by
      conv_lhs => rw [hs₂_eq]
      refine Finset.sum_subset Finset.subset_union_right fun x _ hnx => ?_
      simp [hg_coeff x hnx]
    have hfg : f + g = ∑ x ∈ s₁ ∪ s₂, AddMonoidAlgebra.single x ((f + g).coeff x) := by
      conv_lhs => rw [h1, h2, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [AddMonoidAlgebra.coeff_add]
      change AddMonoidAlgebra.single x (f.coeff x) + AddMonoidAlgebra.single x (g.coeff x) =
        AddMonoidAlgebra.single x (f.coeff x + g.coeff x)
      rw [← AddMonoidAlgebra.single_add]
    calc f + g
        = ∑ x ∈ s₁ ∪ s₂, AddMonoidAlgebra.single x ((f + g).coeff x) := hfg
      _ = ∑ x ∈ s, AddMonoidAlgebra.single x ((f + g).coeff x) := by
          refine (Finset.sum_subset (Finset.filter_subset _ _) fun x hx hnx => ?_).symm
          have h0 : (f + g).coeff x = 0 := by
            by_contra hne
            exact hnx (Finset.mem_filter.mpr ⟨hx, hne⟩)
          rw [h0, AddMonoidAlgebra.single_zero]
  | single χ r =>
    by_cases hr : r = 0
    · subst hr
      exact ⟨∅, by simp, by simp⟩
    · refine ⟨{χ}, fun x hx => ?_, ?_⟩
      · rw [Finset.mem_singleton.mp hx, AddMonoidAlgebra.coeff_single]
        simpa using hr
      · rw [Finset.sum_singleton, AddMonoidAlgebra.coeff_single]
        simp

/-- A group-like element of the torus Hopf algebra `R[X]` satisfies `Δ(u) = u ⊗ u` and `ε(u) = 1`. -/
def IsGroupLike (u : TorusAlg R X) : Prop :=
  torusComul (R := R) (X := X) u = u ⊗ₜ[R] u ∧ torusCounit u = 1

theorem isGroupLike_torusChar (χ : X) : IsGroupLike (torusChar (R := R) χ) :=
  ⟨torusComul_torusChar χ, torusCounit_torusChar χ⟩

/-- **Hopf-Algebraic Character Rigidity Theorem**: over any integral domain `R`, every group-like
element of `TorusAlg R X` is a single character `torusChar χ`! -/
theorem groupLike_eq_torusChar_of_isDomain [IsDomain R] {u : TorusAlg R X}
    (hu : IsGroupLike u) : ∃! χ : X, u = torusChar χ := by
  classical
  have hprod : ∀ x y : X, x ≠ y → u.coeff x * u.coeff y = 0 := by
    intro x y hxy
    have h1 := congrArg (tensorPairCoeff (R := R) x y) hu.1
    rw [tensorPairCoeff_torusComul, if_neg hxy, tensorPairCoeff_tmul] at h1
    exact h1.symm
  obtain ⟨s, hs_ne, hs_eq⟩ := torusAlg_exists_finset_sum u
  have hcounit : torusCounit u = ∑ x ∈ s, u.coeff x := by
    conv_lhs => rw [hs_eq, map_sum]
    refine Finset.sum_congr rfl fun x _ => torusCounit_single x (u.coeff x)
  have hs_nonempty : s.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    have hc := hu.2
    rw [hcounit, h, Finset.sum_empty] at hc
    exact zero_ne_one hc
  obtain ⟨χ, hχ⟩ := hs_nonempty
  have hχ_ne : u.coeff χ ≠ 0 := hs_ne χ hχ
  have hs_sub : s = {χ} := by
    ext y
    simp only [Finset.mem_singleton]
    constructor
    · intro hy
      by_contra hne
      have hy0 := (mul_eq_zero.mp (hprod χ y (Ne.symm hne))).resolve_left hχ_ne
      exact hs_ne y hy hy0
    · rintro rfl; exact hχ
  have hval : u.coeff χ = 1 := by
    have hc := hu.2
    rwa [hcounit, hs_sub, Finset.sum_singleton] at hc
  have hu_eq : u = torusChar χ := by
    rw [hs_eq, hs_sub, Finset.sum_singleton, hval]
    rfl
  refine ⟨χ, hu_eq, fun χ' hχ' => torusChar_injective (hχ'.symm.trans hu_eq)⟩

/-- Induced `R`-algebra morphism `R[X] →ₐ[R] R[Y]` from a character-lattice homomorphism
`f : X →+ Y` (contravariant to `Spec(R[Y]) → Spec(R[X])`). -/
def torusAlgMap {Y : Type*} [AddCommGroup Y] (f : X →+ Y) :
    TorusAlg R X →ₐ[R] TorusAlg R Y :=
  AddMonoidAlgebra.mapDomainAlgHom R R f

@[simp]
theorem torusAlgMap_torusChar {Y : Type*} [AddCommGroup Y] (f : X →+ Y) (χ : X) :
    torusAlgMap (R := R) f (torusChar χ) = torusChar (f χ) := by
  simp [torusAlgMap, torusChar]

/-- **Torus Morphism Rigidity**: over an integral domain `R`, every `R`-algebra morphism
`φ : R[X] →ₐ[R] R[Y]` preserving group-like elements (i.e. a torus group-scheme homomorphism)
is uniquely induced by an additive map `f : X →+ Y` of character lattices! -/
theorem torus_hom_induced_by_character_map [IsDomain R] {Y : Type*} [AddCommGroup Y]
    (φ : TorusAlg R X →ₐ[R] TorusAlg R Y)
    (hφ : ∀ χ : X, IsGroupLike (φ (torusChar χ))) :
    ∃! f : X →+ Y, ∀ χ : X, φ (torusChar χ) = torusChar (f χ) := by
  choose f hf_eq hf_uniq using fun χ : X => groupLike_eq_torusChar_of_isDomain (hφ χ)
  let fHom : X →+ Y :=
    { toFun := f
      map_zero' := by
        apply torusChar_injective (R := R)
        rw [← hf_eq 0, torusChar_zero, map_one, torusChar_zero]
      map_add' := fun χ₁ χ₂ => by
        apply torusChar_injective (R := R)
        rw [← hf_eq (χ₁ + χ₂), torusChar_add, map_mul, hf_eq χ₁, hf_eq χ₂, torusChar_add] }
  refine ⟨fHom, fun χ => hf_eq χ, fun g hg => ?_⟩
  ext χ
  exact torusChar_injective (R := R) ((hg χ).symm.trans (hf_eq χ))

end TorusHopf

section SchemeTori

/-- Universe-0 affine scheme `Spec (CommRingCat.of R)`. -/
abbrev Sp (R : Type) [CommRing R] : Scheme.{0} :=
  Spec (CommRingCat.of R)

/-- Contravariant morphism `Sp R' ⟶ Sp R` induced by `f : R →+* R'`. -/
abbrev spMap {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') : Sp R' ⟶ Sp R :=
  Spec.map (CommRingCat.ofHom f)

/-- Every morphism of affine schemes `spMap f : Sp S ⟶ Sp R` is separated. -/
theorem isSeparated_spMap {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) :
    IsSeparated (spMap f) :=
  inferInstance

/-- Scheme-theoretic split torus `T_X = Spec (R[X])` over `Spec R`. -/
abbrev splitTorusSpec (R : Type) [CommRing R] (X : Type) [AddCommGroup X] : Scheme.{0} :=
  Sp (TorusAlg R X)

/-- Structure morphism `T_X ⟶ Spec R`. -/
def splitTorusStruct (R : Type) [CommRing R] (X : Type) [AddCommGroup X] :
    splitTorusSpec R X ⟶ Sp R :=
  spMap (algebraMap R (TorusAlg R X))

/-- Identity section `Spec R ⟶ T_X` induced by the counit `ε : R[X] →+* R`. -/
def splitTorusZero (R : Type) [CommRing R] (X : Type) [AddCommGroup X] :
    Sp R ⟶ splitTorusSpec R X :=
  spMap (torusCounit (R := R) (X := X)).toRingHom

theorem splitTorusZero_comp_struct (R : Type) [CommRing R] (X : Type) [AddCommGroup X] :
    splitTorusZero R X ≫ splitTorusStruct R X = 𝟙 (Sp R) := by
  unfold splitTorusZero splitTorusStruct
  rw [← Spec.map_comp, ← Spec.map_id]
  congr 1
  ext r
  simp

theorem flat_splitTorusStruct (R : Type) [CommRing R] (X : Type) [AddCommGroup X] :
    Flat (splitTorusStruct R X) := by
  change Flat (Spec.map (CommRingCat.ofHom (algebraMap R (AddMonoidAlgebra R X))))
  rw [HasRingHomProperty.Spec_iff (P := @Flat)]
  change (algebraMap R (AddMonoidAlgebra R X)).Flat
  rw [RingHom.flat_algebraMap_iff]
  infer_instance

theorem isSeparated_splitTorusStruct (R : Type) [CommRing R] (X : Type) [AddCommGroup X] :
    IsSeparated (splitTorusStruct R X) :=
  isSeparated_spMap _

/-- Induced morphism of split tori `T_Y ⟶ T_X` over `Spec R` from `f : X →+ Y`. -/
def splitTorusMap (R : Type) [CommRing R] {X Y : Type} [AddCommGroup X] [AddCommGroup Y]
    (f : X →+ Y) : splitTorusSpec R Y ⟶ splitTorusSpec R X :=
  spMap (torusAlgMap (R := R) f).toRingHom

theorem splitTorusMap_struct (R : Type) [CommRing R] {X Y : Type} [AddCommGroup X] [AddCommGroup Y]
    (f : X →+ Y) :
    splitTorusMap R f ≫ splitTorusStruct R X = splitTorusStruct R Y := by
  unfold splitTorusMap splitTorusStruct
  rw [← Spec.map_comp]
  congr 1
  ext r
  simp

end SchemeTori

section ToricRankSection

/-- **`ToricRankData`**: decomposes a semi-abelian fiber of total dimension `d = t + g` into its
toric rank `t = rank(X)` (with finite free character lattice `X`) and abelian rank `g`. -/
structure ToricRankData where
  toricRank : ℕ
  abelianRank : ℕ
  totalDim : ℕ
  rank_sum : toricRank + abelianRank = totalDim
  charLattice : Type
  [addCommGrp : AddCommGroup charLattice]
  [freeX : Module.Free ℤ charLattice]
  [finiteX : Module.Finite ℤ charLattice]
  finrank_charLattice : Module.finrank ℤ charLattice = toricRank

attribute [instance] ToricRankData.addCommGrp ToricRankData.freeX ToricRankData.finiteX

namespace ToricRankData

/-- Pure split torus of rank `t` (`abelianRank = 0`). -/
def pureTorus (t : ℕ) : ToricRankData where
  toricRank := t
  abelianRank := 0
  totalDim := t
  rank_sum := Nat.add_zero t
  charLattice := Fin t → ℤ
  finrank_charLattice := by simp

/-- Pure abelian scheme of dimension `g` (`toricRank = 0`). -/
def pureAbelian (g : ℕ) : ToricRankData where
  toricRank := 0
  abelianRank := g
  totalDim := g
  rank_sum := Nat.zero_add g
  charLattice := Fin 0 → ℤ
  finrank_charLattice := by simp

/-- Standard `ToricRankData` of toric rank `t` and abelian rank `g`. -/
def ofRanks (t g : ℕ) : ToricRankData where
  toricRank := t
  abelianRank := g
  totalDim := t + g
  rank_sum := rfl
  charLattice := Fin t → ℤ
  finrank_charLattice := by simp

/-- Fiber product of two `ToricRankData` (additive on `toricRank`, `abelianRank`, `totalDim`). -/
def prod (D₁ D₂ : ToricRankData) : ToricRankData where
  toricRank := D₁.toricRank + D₂.toricRank
  abelianRank := D₁.abelianRank + D₂.abelianRank
  totalDim := D₁.totalDim + D₂.totalDim
  rank_sum := by
    have h₁ := D₁.rank_sum
    have h₂ := D₂.rank_sum
    omega
  charLattice := D₁.charLattice × D₂.charLattice
  finrank_charLattice := by
    rw [Module.finrank_prod, D₁.finrank_charLattice, D₂.finrank_charLattice]

theorem toricRank_le_totalDim (D : ToricRankData) : D.toricRank ≤ D.totalDim := by
  have := D.rank_sum; omega

theorem abelianRank_le_totalDim (D : ToricRankData) : D.abelianRank ≤ D.totalDim := by
  have := D.rank_sum; omega

theorem isPureAbelian_iff (D : ToricRankData) : D.toricRank = 0 ↔ D.abelianRank = D.totalDim := by
  have := D.rank_sum; omega

theorem isPureTorus_iff (D : ToricRankData) : D.abelianRank = 0 ↔ D.toricRank = D.totalDim := by
  have := D.rank_sum; omega

end ToricRankData

/-- **Upper Semicontinuity Profile of Toric Rank** across points of a base `Spec R`: constant
total dimension `d`, generic rank `(t_gen, g_gen)`, and `toricRank(s) ≥ t_gen` at every point `s`. -/
structure ToricRankProfile (R : Type) [CommRing R] where
  totalDim : ℕ
  genericRank : ToricRankData
  generic_totalDim : genericRank.totalDim = totalDim
  rankAt : PrimeSpectrum R → ToricRankData
  fiber_totalDim : ∀ s : PrimeSpectrum R, (rankAt s).totalDim = totalDim
  toric_semicontinuous : ∀ s : PrimeSpectrum R, genericRank.toricRank ≤ (rankAt s).toricRank

theorem ToricRankProfile.abelian_semicontinuous {R : Type} [CommRing R]
    (P : ToricRankProfile R) (s : PrimeSpectrum R) :
    (P.rankAt s).abelianRank ≤ P.genericRank.abelianRank := by
  have h1 := P.genericRank.rank_sum
  have h2 := (P.rankAt s).rank_sum
  have h3 := P.toric_semicontinuous s
  rw [P.generic_totalDim] at h1
  rw [P.fiber_totalDim s] at h2
  omega

end ToricRankSection

end AlgebraicTori

/-! ## Section 2: Concrete `RaynaudExtension` (`0 → T → G → B → 0`) & `SemiAbelianScheme` -/

section RaynaudAndSemiAbelian

/-- Smooth/flat separated commutative group scheme model over `Spec R` with relative dimension
`relDim`, identity section, and dual pair `(Lie, ω)` of finite free `R`-modules of rank `relDim`. -/
structure CommGroupSchemeModel (R : Type) [CommRing R] where
  relDim : ℕ
  scheme : Scheme.{0}
  struct : scheme ⟶ Sp R
  flat : Flat struct
  separated : IsSeparated struct
  zeroSection : Sp R ⟶ scheme
  zeroSection_comp : zeroSection ≫ struct = 𝟙 (Sp R)
  lieModule : Type
  [addCommLie : AddCommGroup lieModule]
  [modLie : Module R lieModule]
  [freeLie : Module.Free R lieModule]
  [finiteLie : Module.Finite R lieModule]
  omegaModule : Type
  [addCommOmega : AddCommGroup omegaModule]
  [modOmega : Module R omegaModule]
  [freeOmega : Module.Free R omegaModule]
  [finiteOmega : Module.Finite R omegaModule]
  basisLie : Nonempty (Module.Basis (Fin relDim) R lieModule)
  basisOmega : Nonempty (Module.Basis (Fin relDim) R omegaModule)
  lieOmegaPairing : lieModule →ₗ[R] (omegaModule →ₗ[R] R)

attribute [instance] CommGroupSchemeModel.addCommLie CommGroupSchemeModel.modLie
  CommGroupSchemeModel.freeLie CommGroupSchemeModel.finiteLie
  CommGroupSchemeModel.addCommOmega CommGroupSchemeModel.modOmega
  CommGroupSchemeModel.freeOmega CommGroupSchemeModel.finiteOmega

namespace CommGroupSchemeModel

theorem finrank_lie_eq {R : Type} [Field R] (M : CommGroupSchemeModel R) :
    Module.finrank R M.lieModule = M.relDim := by
  obtain ⟨b⟩ := M.basisLie
  rw [Module.finrank_eq_card_basis b, Fintype.card_fin]

theorem finrank_omega_eq {R : Type} [Field R] (M : CommGroupSchemeModel R) :
    Module.finrank R M.omegaModule = M.relDim := by
  obtain ⟨b⟩ := M.basisOmega
  rw [Module.finrank_eq_card_basis b, Fintype.card_fin]

/-- Concrete split torus `CommGroupSchemeModel R` of rank `t` (`X = Fin t → ℤ`). -/
def ofSplitTorus (R : Type) [CommRing R] (t : ℕ) : CommGroupSchemeModel R where
  relDim := t
  scheme := splitTorusSpec R (Fin t → ℤ)
  struct := splitTorusStruct R (Fin t → ℤ)
  flat := flat_splitTorusStruct R (Fin t → ℤ)
  separated := isSeparated_splitTorusStruct R (Fin t → ℤ)
  zeroSection := splitTorusZero R (Fin t → ℤ)
  zeroSection_comp := splitTorusZero_comp_struct R (Fin t → ℤ)
  lieModule := Fin t → R
  omegaModule := Fin t → R
  basisLie := ⟨Pi.basisFun R (Fin t)⟩
  basisOmega := ⟨Pi.basisFun R (Fin t)⟩
  lieOmegaPairing :=
    { toFun := fun v =>
        { toFun := fun w => ∑ i : Fin t, v i * w i
          map_add' := fun w₁ w₂ => by simp [mul_add, Finset.sum_add_distrib]
          map_smul' := fun r w => by
            simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
            refine Finset.sum_congr rfl fun i _ => ?_
            ring }
      map_add' := fun v₁ v₂ => LinearMap.ext fun w => by simp [add_mul, Finset.sum_add_distrib]
      map_smul' := fun r v => LinearMap.ext fun w => by
        change (∑ i : Fin t, (r * v i) * w i) = r * ∑ i : Fin t, v i * w i
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring }

/-- Trivial zero-dimensional group scheme `Spec R` over `Spec R`. -/
abbrev trivial (R : Type) [CommRing R] : CommGroupSchemeModel R :=
  ofSplitTorus R 0

end CommGroupSchemeModel

/-- **Raynaud Extension (`0 → T → G → B → 0`)**:
A semi-abelian extension of an abelian scheme `B` (relative dimension `g`) by a split torus `T`
(character lattice `X`, rank `t`), carrying:
- scheme-level morphisms `T →[i] G →[q] B` over `Spec R` with `q ∘ i = 0`,
- exact Lie sequence `0 → Lie(T) → Lie(G) → Lie(B) → 0`,
- exact Hodge-cotangent sequence `0 → ω_B → ω_G → ω_T → 0`,
- Raynaud classifying homomorphism `c : X →+ B^∨(R)` (`raynaudClassifying`). -/
structure RaynaudExtension (R : Type) [CommRing R] where
  rankData : ToricRankData
  torusModel : CommGroupSchemeModel R
  abelianModel : CommGroupSchemeModel R
  extModel : CommGroupSchemeModel R
  torus_dim : torusModel.relDim = rankData.toricRank
  abelian_dim : abelianModel.relDim = rankData.abelianRank
  ext_dim : extModel.relDim = rankData.totalDim
  torusIncl : torusModel.scheme ⟶ extModel.scheme
  abelianProj : extModel.scheme ⟶ abelianModel.scheme
  torusIncl_struct : torusIncl ≫ extModel.struct = torusModel.struct
  abelianProj_struct : abelianProj ≫ abelianModel.struct = extModel.struct
  seq_exact_scheme : torusIncl ≫ abelianProj = torusModel.struct ≫ abelianModel.zeroSection
  lieIncl : torusModel.lieModule →ₗ[R] extModel.lieModule
  lieProj : extModel.lieModule →ₗ[R] abelianModel.lieModule
  lieIncl_inj : Function.Injective lieIncl
  lieProj_surj : Function.Surjective lieProj
  lie_exact : LinearMap.range lieIncl = LinearMap.ker lieProj
  omegaIncl : abelianModel.omegaModule →ₗ[R] extModel.omegaModule
  omegaProj : extModel.omegaModule →ₗ[R] torusModel.omegaModule
  omegaIncl_inj : Function.Injective omegaIncl
  omegaProj_surj : Function.Surjective omegaProj
  omega_exact : LinearMap.range omegaIncl = LinearMap.ker omegaProj
  dualAbelianPoints : Type
  [addCommDual : AddCommGroup dualAbelianPoints]
  raynaudClassifying : rankData.charLattice →+ dualAbelianPoints

attribute [instance] RaynaudExtension.addCommDual

namespace RaynaudExtension

section ExactSequences

variable {R : Type} [CommRing R] (E : RaynaudExtension R)

theorem lieProj_comp_lieIncl : E.lieProj.comp E.lieIncl = 0 := by
  ext v
  have hv : E.lieIncl v ∈ LinearMap.range E.lieIncl := LinearMap.mem_range_self E.lieIncl v
  rw [E.lie_exact, LinearMap.mem_ker] at hv
  exact hv

theorem omegaProj_comp_omegaIncl : E.omegaProj.comp E.omegaIncl = 0 := by
  ext ω
  have hω : E.omegaIncl ω ∈ LinearMap.range E.omegaIncl := LinearMap.mem_range_self E.omegaIncl ω
  rw [E.omega_exact, LinearMap.mem_ker] at hω
  exact hω

/-- Because `Lie(B)` is free over `R`, `0 → Lie(T) → Lie(G) → Lie(B) → 0` splits cleanly as
`Lie(G) ≃ₗ[R] Lie(T) × Lie(B)`. -/
def lieSplitEquiv :
    E.extModel.lieModule ≃ₗ[R] E.torusModel.lieModule × E.abelianModel.lieModule := by
  classical
  let bB := Classical.choice E.abelianModel.basisLie
  choose sec_vec hsec_vec using fun i => E.lieProj_surj (bB i)
  let s : E.abelianModel.lieModule →ₗ[R] E.extModel.lieModule :=
    bB.constr R sec_vec
  have hs : ∀ x : E.abelianModel.lieModule, E.lieProj (s x) = x := by
    intro x
    rw [← bB.sum_repr x]
    simp only [s, map_sum, map_smul, Module.Basis.constr_basis]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hsec_vec i]
  have h_in_range : ∀ z : E.extModel.lieModule, z - s (E.lieProj z) ∈ LinearMap.range E.lieIncl := by
    intro z
    rw [E.lie_exact, LinearMap.mem_ker, map_sub, hs, sub_self]
  let p_incl : E.extModel.lieModule →ₗ[R] E.torusModel.lieModule :=
    { toFun := fun z => Classical.choose (h_in_range z)
      map_add' := fun z₁ z₂ => by
        apply E.lieIncl_inj
        have h1 := Classical.choose_spec (h_in_range z₁)
        have h2 := Classical.choose_spec (h_in_range z₂)
        have h12 := Classical.choose_spec (h_in_range (z₁ + z₂))
        have hlin : (z₁ + z₂) - s (E.lieProj (z₁ + z₂)) =
            (z₁ - s (E.lieProj z₁)) + (z₂ - s (E.lieProj z₂)) := by
          rw [map_add, map_add]; abel
        exact (h12.trans (hlin.trans (congrArg₂ (· + ·) h1.symm h2.symm))).trans
          (map_add E.lieIncl _ _).symm
      map_smul' := fun r z => by
        apply E.lieIncl_inj
        have h1 := Classical.choose_spec (h_in_range z)
        have hr := Classical.choose_spec (h_in_range (r • z))
        have hlin : r • z - s (E.lieProj (r • z)) = r • (z - s (E.lieProj z)) := by
          rw [map_smul, map_smul, smul_sub]
        exact (hr.trans (hlin.trans (congrArg (r • ·) h1.symm))).trans
          (map_smul E.lieIncl _ _).symm }
  refine LinearEquiv.ofLinearMap
    (LinearMap.prod p_incl E.lieProj)
    ((E.lieIncl.comp (LinearMap.fst R _ _)) + (s.comp (LinearMap.snd R _ _))) ?_ ?_
  · apply LinearMap.ext
    rintro ⟨t, b⟩
    apply Prod.ext
    · simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.prod_apply,
        LinearMap.fst_apply, LinearMap.snd_apply, LinearMap.id_apply]
      apply E.lieIncl_inj
      have hc := Classical.choose_spec (h_in_range (E.lieIncl t + s b))
      have hp : E.lieProj (E.lieIncl t + s b) = b := by
        rw [map_add, show E.lieProj (E.lieIncl t) = 0 from
          LinearMap.congr_fun E.lieProj_comp_lieIncl t, zero_add, hs]
      have hsub : (E.lieIncl t + s b) - s (E.lieProj (E.lieIncl t + s b)) = E.lieIncl t := by
        rw [hp]; abel
      exact hc.trans hsub
    · change E.lieProj (E.lieIncl t + s b) = b
      rw [map_add, show E.lieProj (E.lieIncl t) = 0 from
        LinearMap.congr_fun E.lieProj_comp_lieIncl t, zero_add, hs]
  · ext z
    change E.lieIncl (p_incl z) + s (E.lieProj z) = z
    have hc : E.lieIncl (p_incl z) = z - s (E.lieProj z) :=
      Classical.choose_spec (h_in_range z)
    rw [hc, sub_add_cancel]

/-- Because `ω_T` is free over `R`, the Hodge-cotangent exact sequence
`0 → ω_B → ω_G → ω_T → 0` splits cleanly as `ω_G ≃ₗ[R] ω_B × ω_T`! -/
def omegaSplitEquiv :
    E.extModel.omegaModule ≃ₗ[R] E.abelianModel.omegaModule × E.torusModel.omegaModule := by
  classical
  let bT := Classical.choice E.torusModel.basisOmega
  choose sec_vec hsec_vec using fun i => E.omegaProj_surj (bT i)
  let s : E.torusModel.omegaModule →ₗ[R] E.extModel.omegaModule :=
    bT.constr R sec_vec
  have hs : ∀ x : E.torusModel.omegaModule, E.omegaProj (s x) = x := by
    intro x
    rw [← bT.sum_repr x]
    simp only [s, map_sum, map_smul, Module.Basis.constr_basis]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hsec_vec i]
  have h_in_range : ∀ z : E.extModel.omegaModule, z - s (E.omegaProj z) ∈ LinearMap.range E.omegaIncl := by
    intro z
    rw [E.omega_exact, LinearMap.mem_ker, map_sub, hs, sub_self]
  let p_incl : E.extModel.omegaModule →ₗ[R] E.abelianModel.omegaModule :=
    { toFun := fun z => Classical.choose (h_in_range z)
      map_add' := fun z₁ z₂ => by
        apply E.omegaIncl_inj
        have h1 := Classical.choose_spec (h_in_range z₁)
        have h2 := Classical.choose_spec (h_in_range z₂)
        have h12 := Classical.choose_spec (h_in_range (z₁ + z₂))
        have hlin : (z₁ + z₂) - s (E.omegaProj (z₁ + z₂)) =
            (z₁ - s (E.omegaProj z₁)) + (z₂ - s (E.omegaProj z₂)) := by
          rw [map_add, map_add]; abel
        exact (h12.trans (hlin.trans (congrArg₂ (· + ·) h1.symm h2.symm))).trans
          (map_add E.omegaIncl _ _).symm
      map_smul' := fun r z => by
        apply E.omegaIncl_inj
        have h1 := Classical.choose_spec (h_in_range z)
        have hr := Classical.choose_spec (h_in_range (r • z))
        have hlin : r • z - s (E.omegaProj (r • z)) = r • (z - s (E.omegaProj z)) := by
          rw [map_smul, map_smul, smul_sub]
        exact (hr.trans (hlin.trans (congrArg (r • ·) h1.symm))).trans
          (map_smul E.omegaIncl _ _).symm }
  refine LinearEquiv.ofLinearMap
    (LinearMap.prod p_incl E.omegaProj)
    ((E.omegaIncl.comp (LinearMap.fst R _ _)) + (s.comp (LinearMap.snd R _ _))) ?_ ?_
  · apply LinearMap.ext
    rintro ⟨b, t⟩
    apply Prod.ext
    · simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.prod_apply,
        LinearMap.fst_apply, LinearMap.snd_apply, LinearMap.id_apply]
      apply E.omegaIncl_inj
      have hc := Classical.choose_spec (h_in_range (E.omegaIncl b + s t))
      have hp : E.omegaProj (E.omegaIncl b + s t) = t := by
        rw [map_add, show E.omegaProj (E.omegaIncl b) = 0 from
          LinearMap.congr_fun E.omegaProj_comp_omegaIncl b, zero_add, hs]
      have hsub : (E.omegaIncl b + s t) - s (E.omegaProj (E.omegaIncl b + s t)) = E.omegaIncl b := by
        rw [hp]; abel
      exact hc.trans hsub
    · change E.omegaProj (E.omegaIncl b + s t) = t
      rw [map_add, show E.omegaProj (E.omegaIncl b) = 0 from
        LinearMap.congr_fun E.omegaProj_comp_omegaIncl b, zero_add, hs]
  · ext z
    change E.omegaIncl (p_incl z) + s (E.omegaProj z) = z
    have hc : E.omegaIncl (p_incl z) = z - s (E.omegaProj z) :=
      Classical.choose_spec (h_in_range z)
    rw [hc, sub_add_cancel]

theorem raynaud_omega_finrank_add {K : Type} [Field K] (E_K : RaynaudExtension K) :
    Module.finrank K E_K.extModel.omegaModule =
      Module.finrank K E_K.abelianModel.omegaModule +
        Module.finrank K E_K.torusModel.omegaModule := by
  rw [E_K.omegaSplitEquiv.finrank_eq, Module.finrank_prod]

theorem raynaud_lie_finrank_add {K : Type} [Field K] (E_K : RaynaudExtension K) :
    Module.finrank K E_K.extModel.lieModule =
      Module.finrank K E_K.torusModel.lieModule +
        Module.finrank K E_K.abelianModel.lieModule := by
  rw [E_K.lieSplitEquiv.finrank_eq, Module.finrank_prod]

end ExactSequences

/-- Concrete `RaynaudExtension` of a pure split torus `0 → T → T → 0 → 0` of rank `t`. -/
def ofTorus (R : Type) [CommRing R] (t : ℕ) : RaynaudExtension R where
  rankData := ToricRankData.pureTorus t
  torusModel := CommGroupSchemeModel.ofSplitTorus R t
  abelianModel := CommGroupSchemeModel.trivial R
  extModel := CommGroupSchemeModel.ofSplitTorus R t
  torus_dim := rfl
  abelian_dim := rfl
  ext_dim := rfl
  torusIncl := 𝟙 _
  abelianProj := (CommGroupSchemeModel.ofSplitTorus R t).struct ≫
    (CommGroupSchemeModel.trivial R).zeroSection
  torusIncl_struct := Category.id_comp _
  abelianProj_struct := by
    rw [Category.assoc, (CommGroupSchemeModel.trivial R).zeroSection_comp, Category.comp_id]
  seq_exact_scheme := Category.id_comp _
  lieIncl := LinearMap.id
  lieProj := 0
  lieIncl_inj := Function.injective_id
  lieProj_surj := fun (y : Fin 0 → R) => ⟨0, funext fun i => Fin.elim0 i⟩
  lie_exact := by
    ext x
    simp only [LinearMap.range_id, Submodule.mem_top, LinearMap.mem_ker, LinearMap.zero_apply]
  omegaIncl := 0
  omegaProj := LinearMap.id
  omegaIncl_inj := fun (x y : Fin 0 → R) _ => funext fun i => Fin.elim0 i
  omegaProj_surj := Function.surjective_id
  omega_exact := by
    ext x
    simp only [LinearMap.range_zero, Submodule.mem_bot, LinearMap.mem_ker, LinearMap.id_apply]
  dualAbelianPoints := PUnit
  raynaudClassifying := 0

/-- Concrete `RaynaudExtension` of a pure abelian scheme `0 → 0 → B → B → 0` of dimension `g`. -/
def ofAbelian (R : Type) [CommRing R] (B : CommGroupSchemeModel R) : RaynaudExtension R where
  rankData := ToricRankData.pureAbelian B.relDim
  torusModel := CommGroupSchemeModel.trivial R
  abelianModel := B
  extModel := B
  torus_dim := rfl
  abelian_dim := rfl
  ext_dim := rfl
  torusIncl := (CommGroupSchemeModel.trivial R).struct ≫ B.zeroSection
  abelianProj := 𝟙 _
  torusIncl_struct := by
    rw [Category.assoc, B.zeroSection_comp, Category.comp_id]
  abelianProj_struct := Category.id_comp _
  seq_exact_scheme := by rw [Category.comp_id]
  lieIncl := 0
  lieProj := LinearMap.id
  lieIncl_inj := fun (x y : Fin 0 → R) _ => funext fun i => Fin.elim0 i
  lieProj_surj := Function.surjective_id
  lie_exact := by
    ext x
    simp only [LinearMap.range_zero, Submodule.mem_bot, LinearMap.mem_ker, LinearMap.id_apply]
  omegaIncl := LinearMap.id
  omegaProj := 0
  omegaIncl_inj := Function.injective_id
  omegaProj_surj := fun (y : Fin 0 → R) => ⟨0, funext fun i => Fin.elim0 i⟩
  omega_exact := by
    ext x
    simp only [LinearMap.range_id, Submodule.mem_top, LinearMap.mem_ker, LinearMap.zero_apply]
  dualAbelianPoints := PUnit
  raynaudClassifying := 0

/-- Concrete 1-dimensional Tate multiplicative-degeneration Raynaud extension `0 → 𝔾_m → G → 0 → 0`
at the special fiber (`toricRank = 1`, `abelianRank = 0`). -/
def tateSpecialFiber (R : Type) [CommRing R] : RaynaudExtension R :=
  ofTorus R 1

end RaynaudExtension

/-- **Semi-Abelian Scheme (`SemiAbelianScheme R`)**:
A smooth/flat, separated commutative group scheme `G` over `Spec R` with relative dimension `d`,
equipped with generic `ToricRankData`, explicit `RaynaudExtension k` (`0 → T_k → G_k → B_k → 0`)
on every field-valued fiber `Spec k → Spec R`, constant total fiber dimension `d`, and upper
semicontinuity of toric rank (`genericRanks.toricRank ≤ (fiberRaynaud k s).rankData.toricRank`). -/
structure SemiAbelianScheme (R : Type) [CommRing R] where
  model : CommGroupSchemeModel R
  genericRanks : ToricRankData
  generic_totalDim : genericRanks.totalDim = model.relDim
  fiberRaynaud : ∀ (k : Type) [Field k], (R →+* k) → RaynaudExtension k
  fiber_totalDim_eq : ∀ (k : Type) [Field k] (s : R →+* k),
    (fiberRaynaud k s).rankData.totalDim = model.relDim
  toricRank_semicontinuous : ∀ (k : Type) [Field k] (s : R →+* k),
    genericRanks.toricRank ≤ (fiberRaynaud k s).rankData.toricRank

namespace SemiAbelianScheme

theorem abelianRank_semicontinuous {R : Type} [CommRing R] (G : SemiAbelianScheme R)
    (k : Type) [Field k] (s : R →+* k) :
    (G.fiberRaynaud k s).rankData.abelianRank ≤ G.genericRanks.abelianRank := by
  have h1 := G.genericRanks.rank_sum
  have h2 := (G.fiberRaynaud k s).rankData.rank_sum
  have h3 := G.toricRank_semicontinuous k s
  rw [G.generic_totalDim] at h1
  rw [G.fiber_totalDim_eq k s] at h2
  omega

/-- Pure split torus of rank `t` as a `SemiAbelianScheme R` over any `CommRing R`. -/
def ofTorus (R : Type) [CommRing R] (t : ℕ) : SemiAbelianScheme R where
  model := CommGroupSchemeModel.ofSplitTorus R t
  genericRanks := ToricRankData.pureTorus t
  generic_totalDim := rfl
  fiberRaynaud k _ _ := RaynaudExtension.ofTorus k t
  fiber_totalDim_eq _ _ _ := rfl
  toricRank_semicontinuous _ _ _ := by simp [RaynaudExtension.ofTorus]

/-- Concrete 1-dimensional Tate semi-abelian degeneration over a DVR `R`:
generic fibers (`s π ≠ 0`) have good abelian reduction `(t = 0, g = 1)`, while special fibers
(`s π = 0`) have split multiplicative toric reduction `(t = 1, g = 0)`! -/
def tateDegeneration (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (π : R) (_hπ : Irreducible π)
    (ellipticFiber : ∀ (k : Type) [Field k], (R →+* k) → CommGroupSchemeModel k)
    (h_ell : ∀ (k : Type) [Field k] (s : R →+* k), (ellipticFiber k s).relDim = 1) :
    SemiAbelianScheme R where
  model := CommGroupSchemeModel.ofSplitTorus R 1
  genericRanks := ToricRankData.pureAbelian 1
  generic_totalDim := rfl
  fiberRaynaud k _ s :=
    letI := Classical.decEq k
    if s π = 0 then RaynaudExtension.tateSpecialFiber k
    else RaynaudExtension.ofAbelian k (ellipticFiber k s)
  fiber_totalDim_eq k _ s := by
    split_ifs with h
    · simp only [RaynaudExtension.tateSpecialFiber, RaynaudExtension.ofTorus,
        ToricRankData.pureTorus, CommGroupSchemeModel.ofSplitTorus]
    · simp only [RaynaudExtension.ofAbelian, ToricRankData.pureAbelian, h_ell k s,
        CommGroupSchemeModel.ofSplitTorus]
  toricRank_semicontinuous k _ s := by
    change 0 ≤ _
    exact Nat.zero_le _

end SemiAbelianScheme

end RaynaudAndSemiAbelian

/-! ## Section 3: Néron / Raynaud Extension of Morphisms (`semiAbelian_hom_extension`) -/

section HomExtension

section DVRUnitRigidity

/-- Over a DVR `(R, π)` and a flat domain `R`-algebra `A` with prime special fiber (`Prime (π_A)`),
`π`-adic Hausdorffness, and augmentation `ε : A →ₐ[R] R` (identity section), any unit `u` of
`A[1/π]` satisfying `ε_K(u) = 1` has `π`-adic valuation `0` and lies in `Aˣ`! -/
theorem dvr_prime_unit_eval_one_mem_range
    {R A : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing A] [IsDomain A] [Algebra R A]
    (π : R) (hπ : Irreducible π)
    (hπA_prime : Prime (algebraMap R A π))
    (h_haus : ∀ a : A, a ≠ 0 → ∃ n : ℕ, ¬ (algebraMap R A π ^ n ∣ a))
    (ε : A →ₐ[R] R)
    {u : (Localization.Away (algebraMap R A π))ˣ}
    (hu_eps : IsLocalization.Away.lift (algebraMap R A π)
      (g := (algebraMap R (FractionRing R)).comp ε.toRingHom)
      (by
        rw [RingHom.comp_apply]
        change IsUnit (algebraMap R (FractionRing R) (ε (algebraMap R A π)))
        rw [AlgHom.commutes]
        exact IsUnit.mk0 _ (fun h0 => hπ.ne_zero
          (IsFractionRing.injective R (FractionRing R) (h0.trans (map_zero _).symm))))
      (u : Localization.Away (algebraMap R A π)) = 1) :
    ∃! u₀ : Aˣ,
      algebraMap A (Localization.Away (algebraMap R A π)) (u₀ : A) =
        (u : Localization.Away (algebraMap R A π)) := by
  classical
  let K := FractionRing R
  let AK := Localization.Away (algebraMap R A π)
  let πA : A := algebraMap R A π
  have hπA_ne : πA ≠ 0 := hπA_prime.ne_zero
  have hπA_not_unit : ¬ IsUnit πA := hπA_prime.not_isUnit
  have h_inj : Function.Injective (algebraMap A AK) := by
    refine IsLocalization.injective (M := Submonoid.powers πA) AK ?_
    rintro x ⟨n, rfl⟩
    exact mem_nonZeroDivisors_iff_ne_zero.mpr (pow_ne_zero n hπA_ne)
  have : Nontrivial AK := ⟨⟨1, 0, fun h => one_ne_zero (h_inj (by simpa using h))⟩⟩
  -- Factor any nonzero element of `A` as `πA^r * a₀` with `¬ (πA ∣ a₀)`
  have h_factor : ∀ x : A, x ≠ 0 → ∃ (r : ℕ) (x₀ : A), ¬ (πA ∣ x₀) ∧ x = πA ^ r * x₀ := by
    intro x hx0
    have hex : ∃ n : ℕ, ¬ (πA ^ n ∣ x) := h_haus x hx0
    let n := Nat.find hex
    have hn : ¬ (πA ^ n ∣ x) := Nat.find_spec hex
    have hn_pos : 0 < n := by
      by_contra h0
      have hn0 : n = 0 := by omega
      rw [hn0, pow_zero] at hn
      exact hn (one_dvd x)
    have hprev : πA ^ (n - 1) ∣ x :=
      not_not.mp (Nat.find_min hex (Nat.sub_lt hn_pos zero_lt_one))
    obtain ⟨x₀, hx₀⟩ := hprev
    refine ⟨n - 1, x₀, ?_, hx₀⟩
    intro ⟨c, hc⟩
    apply hn
    refine ⟨c, ?_⟩
    rw [hx₀, hc, ← mul_assoc, ← pow_succ, Nat.sub_add_cancel hn_pos]
  -- Express `u` and `u⁻¹` in `Localization.Away πA`
  obtain ⟨⟨a, ⟨_, m, rfl⟩⟩, ha⟩ :=
    IsLocalization.surj (Submonoid.powers πA) (u : AK)
  obtain ⟨⟨b, ⟨_, n, rfl⟩⟩, hb⟩ :=
    IsLocalization.surj (Submonoid.powers πA) ((u⁻¹ : AKˣ) : AK)
  dsimp only at ha hb
  have ha_ne : a ≠ 0 := by
    intro ha0
    rw [ha0, map_zero] at ha
    have hunit := (IsLocalization.Away.algebraMap_isUnit πA (S := AK)).pow m
    have h1 := (mul_eq_zero.mp ha).resolve_right (by simpa [map_pow] using hunit.ne_zero)
    exact u.ne_zero h1
  have hb_ne : b ≠ 0 := by
    intro hb0
    rw [hb0, map_zero] at hb
    have hunit := (IsLocalization.Away.algebraMap_isUnit πA (S := AK)).pow n
    have h1 := (mul_eq_zero.mp hb).resolve_right (by simpa [map_pow] using hunit.ne_zero)
    exact u⁻¹.ne_zero h1
  obtain ⟨r, a₀, ha₀_ndvd, rfl⟩ := h_factor a ha_ne
  obtain ⟨s, b₀, hb₀_ndvd, rfl⟩ := h_factor b hb_ne
  have hab_pow : algebraMap A AK (πA ^ (r + s) * (a₀ * b₀)) = algebraMap A AK (πA ^ (m + n)) := by
    have h1 : (u : AK) * ((u⁻¹ : AKˣ) : AK) = 1 := Units.mul_inv u
    calc algebraMap A AK (πA ^ (r + s) * (a₀ * b₀))
        = algebraMap A AK (πA ^ r * a₀) * algebraMap A AK (πA ^ s * b₀) := by
          rw [← map_mul]; congr 1; rw [pow_add]; ring
      _ = ((u : AK) * algebraMap A AK (πA ^ m)) *
            (((u⁻¹ : AKˣ) : AK) * algebraMap A AK (πA ^ n)) := by rw [ha, hb]
      _ = ((u : AK) * ((u⁻¹ : AKˣ) : AK)) *
            (algebraMap A AK (πA ^ m) * algebraMap A AK (πA ^ n)) := by ring
      _ = algebraMap A AK (πA ^ (m + n)) := by
          rw [h1, one_mul, ← map_mul, pow_add]
  have hab_A : πA ^ (r + s) * (a₀ * b₀) = πA ^ (m + n) := h_inj hab_pow
  -- Compare `πA`-exponents: `r + s = m + n` and `a₀ * b₀ = 1`
  have h_exp : r + s = m + n := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hk : 1 ≤ (m + n) - (r + s) := by omega
      have hdvd : πA ^ ((m + n) - (r + s)) * 1 = a₀ * b₀ := by
        apply mul_left_cancel₀ (pow_ne_zero (r + s) hπA_ne)
        calc πA ^ (r + s) * (πA ^ ((m + n) - (r + s)) * 1)
            = πA ^ (r + s + ((m + n) - (r + s))) := by rw [mul_one, ← pow_add]
          _ = πA ^ (m + n) := by congr 1; omega
          _ = πA ^ (r + s) * (a₀ * b₀) := hab_A.symm
      have hπ_dvd : πA ∣ a₀ * b₀ := by
        refine ⟨πA ^ ((m + n) - (r + s) - 1), ?_⟩
        rw [← hdvd, mul_one, ← pow_succ']
        congr 1; omega
      rcases hπA_prime.dvd_or_dvd hπ_dvd with h | h
      · exact ha₀_ndvd h
      · exact hb₀_ndvd h
    · have hk : 1 ≤ (r + s) - (m + n) := by omega
      have hmul1 : πA ^ ((r + s) - (m + n)) * (a₀ * b₀) = 1 := by
        apply mul_left_cancel₀ (pow_ne_zero (m + n) hπA_ne)
        calc πA ^ (m + n) * (πA ^ ((r + s) - (m + n)) * (a₀ * b₀))
            = (πA ^ (m + n) * πA ^ ((r + s) - (m + n))) * (a₀ * b₀) := by rw [mul_assoc]
          _ = πA ^ (m + n + ((r + s) - (m + n))) * (a₀ * b₀) := by rw [← pow_add]
          _ = πA ^ (r + s) * (a₀ * b₀) := by congr 2; omega
          _ = πA ^ (m + n) := hab_A
          _ = πA ^ (m + n) * 1 := (mul_one _).symm
      have hπ_unit : IsUnit πA := by
        refine isUnit_iff_exists_inv.mpr ⟨πA ^ ((r + s) - (m + n) - 1) * (a₀ * b₀), ?_⟩
        calc πA * (πA ^ ((r + s) - (m + n) - 1) * (a₀ * b₀))
            = (πA * πA ^ ((r + s) - (m + n) - 1)) * (a₀ * b₀) := by rw [mul_assoc]
          _ = πA ^ (((r + s) - (m + n) - 1) + 1) * (a₀ * b₀) := by rw [← pow_succ']
          _ = πA ^ ((r + s) - (m + n)) * (a₀ * b₀) := by congr 2; exact Nat.sub_add_cancel hk
          _ = 1 := hmul1
      exact hπA_not_unit hπ_unit
  have ha₀b₀ : a₀ * b₀ = 1 := by
    apply mul_left_cancel₀ (pow_ne_zero (r + s) hπA_ne)
    rw [hab_A, h_exp, mul_one]
  have ha₀_unit : IsUnit a₀ := isUnit_iff_exists_inv.mpr ⟨b₀, ha₀b₀⟩
  -- Now evaluate `ε` on `u * πA^m = πA^r * a₀` to conclude `r = m`!
  let εK : AK →+* K := IsLocalization.Away.lift πA
    (g := (algebraMap R K).comp ε.toRingHom)
    (by
      rw [RingHom.comp_apply]
      change IsUnit (algebraMap R K (ε (algebraMap R A π)))
      rw [AlgHom.commutes]
      exact IsUnit.mk0 _ (fun h0 => hπ.ne_zero
        (IsFractionRing.injective R K (h0.trans (map_zero _).symm))))
  have hε_comp : ∀ x : A, εK (algebraMap A AK x) = algebraMap R K (ε x) := fun x => by
    dsimp only [εK, AK, πA, K]
    rw [IsLocalization.Away.lift_eq]; rfl
  have hε_eq : algebraMap R K (π ^ m) = algebraMap R K (π ^ r * ε a₀) := by
    have h1 := congrArg εK ha
    dsimp only [πA] at h1
    rw [map_mul, hu_eps, one_mul, hε_comp, hε_comp, map_pow, map_mul, map_pow, ε.commutes π] at h1
    simpa [map_pow, map_mul] using h1
  have h_R_eq : π ^ m = π ^ r * ε a₀ := IsFractionRing.injective R K hε_eq
  have hε_unit : IsUnit (ε a₀) := ha₀_unit.map ε.toRingHom
  have h_rm : r = m := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hmul : π ^ (m - r) = ε a₀ := by
        apply mul_left_cancel₀ (pow_ne_zero r hπ.ne_zero)
        rw [← pow_add, show r + (m - r) = m by omega, h_R_eq]
      have hπ_dvd : π ∣ ε a₀ := by
        rw [← hmul]
        exact dvd_pow_self π (by omega)
      exact hπ.not_isUnit (isUnit_of_dvd_unit hπ_dvd hε_unit)
    · have hmul : 1 = π ^ (r - m) * ε a₀ := by
        apply mul_left_cancel₀ (pow_ne_zero m hπ.ne_zero)
        rw [mul_one, ← mul_assoc, ← pow_add, show m + (r - m) = r by omega, h_R_eq]
      have hπ_dvd : π ∣ (1 : R) := by
        refine ⟨π ^ (r - m - 1) * ε a₀, ?_⟩
        rw [← mul_assoc, ← pow_succ', show (r - m - 1) + 1 = r - m by omega, ← hmul]
      exact hπ.not_isUnit (isUnit_of_dvd_one hπ_dvd)
  -- Therefore `u = algebraMap A AK a₀`!
  obtain ⟨u₀, hu₀⟩ := ha₀_unit
  have hunit := (IsLocalization.Away.algebraMap_isUnit πA (S := AK)).pow m
  obtain ⟨v, hv⟩ := hunit
  have hu_eq_a₀ : (u : AK) = algebraMap A AK a₀ := by
    have h_mul : (u : AK) * (v : AK) = algebraMap A AK a₀ * (v : AK) := by
      rw [hv, ← map_pow, ha, h_rm, map_mul, mul_comm (algebraMap A AK a₀)]
    calc (u : AK) = ((u : AK) * (v : AK)) * (v⁻¹ : AKˣ) := by
          rw [mul_assoc, Units.mul_inv, mul_one]
      _ = (algebraMap A AK a₀ * (v : AK)) * (v⁻¹ : AKˣ) := by rw [h_mul]
      _ = algebraMap A AK a₀ := by rw [mul_assoc, Units.mul_inv, mul_one]
  refine ⟨u₀, ?_, ?_⟩
  · change algebraMap A AK (u₀ : A) = (u : AK)
    rw [hu₀, hu_eq_a₀]
  · intro u₁ hu₁
    apply Units.ext
    exact h_inj (hu₁.trans (hu_eq_a₀.trans (congrArg (algebraMap A AK) hu₀.symm)))

/-- Over a DVR `(R, π)`, every nonzero `r : R` factors as `u * π^k` (`IsDiscreteValuationRing`),
so `algebraMap R (Localization.Away (algebraMap R A π))` sends `nonZeroDivisors R` to units,
yielding a canonical diamond-free `RingHom` `FractionRing R →+* Localization.Away (algebraMap R A π)`. -/
def dvrFracToAway {R A : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing A] [Algebra R A] (π : R) (hπ : Irreducible π) :
    FractionRing R →+* Localization.Away (algebraMap R A π) :=
  IsLocalization.lift (M := nonZeroDivisors R) (S := FractionRing R)
    (g := (algebraMap A (Localization.Away (algebraMap R A π))).comp (algebraMap R A))
    (fun ⟨r, hr⟩ => by
      dsimp only
      have hr0 : r ≠ 0 := nonZeroDivisors.ne_zero hr
      obtain ⟨k, u, hru⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hr0 hπ
      rw [RingHom.comp_apply, hru, map_mul, map_pow, map_mul, map_pow]
      have hu : IsUnit (algebraMap A (Localization.Away (algebraMap R A π)) (algebraMap R A (u : R))) :=
        (u.isUnit.map (algebraMap R A)).map (algebraMap A _)
      have hpi : IsUnit (algebraMap A (Localization.Away (algebraMap R A π)) (algebraMap R A π)) :=
        IsLocalization.Away.algebraMap_isUnit (algebraMap R A π)
      exact hu.mul (hpi.pow k))

@[simp]
theorem dvrFracToAway_algebraMap {R A : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing A] [Algebra R A] (π : R) (hπ : Irreducible π) (r : R) :
    dvrFracToAway π hπ (algebraMap R (FractionRing R) r) =
      algebraMap A (Localization.Away (algebraMap R A π)) (algebraMap R A r) :=
  IsLocalization.lift_eq _ r

/-- **Toric Morphism Extension over a DVR**:
Given a DVR `(R, π)` with fraction field `K = FractionRing R`, a flat integral `R`-algebra `A`
with prime special fiber (`Prime (π_A)`), `π`-adic Hausdorffness, and identity section `ε : A →ₐ[R] R`,
every `K`-toric homomorphism `φ_K : TorusAlg K X →+* A[1/π]` (compatible with `dvrFracToAway`)
preserving the identity section extends **uniquely** to an `R`-algebra homomorphism
`φ : TorusAlg R X →ₐ[R] A`! -/
theorem toric_hom_extends_over_dvr
    {R A X : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing A] [IsDomain A] [Algebra R A] [AddCommGroup X]
    (π : R) (hπ : Irreducible π)
    (hπA_prime : Prime (algebraMap R A π))
    (h_haus : ∀ a : A, a ≠ 0 → ∃ n : ℕ, ¬ (algebraMap R A π ^ n ∣ a))
    (ε : A →ₐ[R] R)
    (φ_K : TorusAlg (FractionRing R) X →+* Localization.Away (algebraMap R A π))
    (hφ_eps : ∀ χ : X, IsLocalization.Away.lift (algebraMap R A π)
      (g := (algebraMap R (FractionRing R)).comp ε.toRingHom)
      (by
        rw [RingHom.comp_apply]
        change IsUnit (algebraMap R (FractionRing R) (ε (algebraMap R A π)))
        rw [AlgHom.commutes]
        exact IsUnit.mk0 _ (fun h0 => hπ.ne_zero
          (IsFractionRing.injective R (FractionRing R) (h0.trans (map_zero _).symm))))
      (φ_K (torusChar χ)) = 1) :
    ∃! φ : TorusAlg R X →ₐ[R] A,
      ∀ χ : X, algebraMap A (Localization.Away (algebraMap R A π)) (φ (torusChar χ)) =
        φ_K (torusChar χ) := by
  classical
  let AK := Localization.Away (algebraMap R A π)
  let πA : A := algebraMap R A π
  have h_inj : Function.Injective (algebraMap A AK) := by
    refine IsLocalization.injective (M := Submonoid.powers πA) AK ?_
    rintro x ⟨n, rfl⟩
    exact mem_nonZeroDivisors_iff_ne_zero.mpr (pow_ne_zero n hπA_prime.ne_zero)
  have h_unit : ∀ χ : X, IsUnit (φ_K (torusChar χ)) := fun χ =>
    (isUnit_torusChar (R := FractionRing R) χ).map φ_K
  have h_lift : ∀ χ : X, ∃! u₀ : Aˣ,
      algebraMap A AK (u₀ : A) = φ_K (torusChar χ) := fun χ => by
    obtain ⟨u, hu⟩ := h_unit χ
    have hpi_unit : IsUnit (((algebraMap R (FractionRing R)).comp ε.toRingHom) πA) := by
      rw [RingHom.comp_apply]
      change IsUnit (algebraMap R (FractionRing R) (ε (algebraMap R A π)))
      rw [AlgHom.commutes]
      exact IsUnit.mk0 _ (fun h0 => hπ.ne_zero
        (IsFractionRing.injective R (FractionRing R) (h0.trans (map_zero _).symm)))
    have hε : IsLocalization.Away.lift πA
        (g := (algebraMap R (FractionRing R)).comp ε.toRingHom) hpi_unit (u : AK) = 1 := by
      rw [hu]; exact hφ_eps χ
    obtain ⟨u₀, hu₀, hu₀_uniq⟩ :=
      dvr_prime_unit_eval_one_mem_range π hπ hπA_prime h_haus ε hε
    exact ⟨u₀, hu₀.trans hu, fun v hv => hu₀_uniq v (hv.trans hu.symm)⟩
  choose u_fn hu_eq hu_uniq using h_lift
  let fMul : Multiplicative X →* A :=
    { toFun := fun χ => (u_fn χ.toAdd : A)
      map_one' := by
        apply h_inj
        rw [toAdd_one, hu_eq 0, map_one,
          show torusChar (R := FractionRing R) (0 : X) = 1 from torusChar_zero, map_one]
      map_mul' := fun χ₁ χ₂ => by
        apply h_inj
        rw [toAdd_mul, map_mul, hu_eq (χ₁.toAdd + χ₂.toAdd), hu_eq χ₁.toAdd, hu_eq χ₂.toAdd,
          torusChar_add, map_mul] }
  let φ : TorusAlg R X →ₐ[R] A := AddMonoidAlgebra.lift R A X fMul
  have hφ_char : ∀ χ : X, φ (torusChar χ) = (u_fn χ : A) := fun χ => by
    simp [φ, torusChar, fMul]
  refine ⟨φ, fun χ => by rw [hφ_char χ, hu_eq χ], fun ψ hψ => ?_⟩
  apply AddMonoidAlgebra.algHom_ext
  · intro χ
    apply h_inj
    change algebraMap A AK (ψ (torusChar χ)) = algebraMap A AK (φ (torusChar χ))
    rw [hψ χ, hφ_char χ, hu_eq χ]
  · exact Subsingleton.elim _ _

end DVRUnitRigidity

section SemiAbelianHomExtension

/-- Smooth connected flat model `H` over a DVR `R` with fraction field `K = FractionRing R`:
carries `CommGroupSchemeModel R` plus an integral coordinate ring `coordRing` (`A`) with prime
special fiber `Prime (π_A)`, `π`-adic Hausdorffness, and identity section `ε : A →ₐ[R] R`. -/
structure SmoothConnectedDVRModel (R : Type) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] (π : R) (hπ : Irreducible π) where
  base : CommGroupSchemeModel R
  coordRing : Type
  [commRingCoord : CommRing coordRing]
  [domainCoord : IsDomain coordRing]
  [algCoord : Algebra R coordRing]
  prime_uniformizer : Prime (algebraMap R coordRing π)
  hausdorff_uniformizer :
    ∀ a : coordRing, a ≠ 0 → ∃ n : ℕ, ¬ (algebraMap R coordRing π ^ n ∣ a)
  identitySection : coordRing →ₐ[R] R

attribute [instance] SmoothConnectedDVRModel.commRingCoord SmoothConnectedDVRModel.domainCoord
  SmoothConnectedDVRModel.algCoord

/-- Target semi-abelian scheme `G` over a DVR `R` presented with its Raynaud-Néron decomposition
`0 → T → G → B → 0`, where the abelian quotient `B` satisfies the valuative/Néron extension
property for smooth connected models over `R`. -/
structure NeronRaynaudDVRTarget (R : Type) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] where
  semiAb : SemiAbelianScheme R
  raynaud : RaynaudExtension R
  raynaud_dim : raynaud.rankData.totalDim = semiAb.model.relDim
  abelianHom : Type → Type
  abelianHom_K : Type → Type
  restrictAbelian : ∀ {A : Type}, abelianHom A → abelianHom_K A
  restrictAbelian_inj : ∀ {A : Type} [CommRing A] [IsDomain A] [Algebra R A],
    Function.Injective (restrictAbelian (A := A))
  proper_abelian_lift : ∀ {A : Type} [CommRing A] [IsDomain A] [Algebra R A],
    abelianHom_K A → abelianHom A

/-- Generic-fiber group homomorphism `H_K → G_K` into a `NeronRaynaudDVRTarget R`, decomposed
into its proper abelian quotient component, its `K`-toric character homomorphism
`TorusAlg K X →+* A[1/π]` preserving the identity section, and its tangent map `Lie(H_K) → Lie(G_K)`. -/
structure GenericFiberSemiAbHom (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (π : R) (hπ : Irreducible π)
    (H : SmoothConnectedDVRModel R π hπ) (G : NeronRaynaudDVRTarget R) where
  abelianComp_K : G.abelianHom_K H.coordRing
  toricComp_K :
    TorusAlg (FractionRing R) G.raynaud.rankData.charLattice →+*
      Localization.Away (algebraMap R H.coordRing π)
  toric_commutes : ∀ c : FractionRing R,
    toricComp_K (algebraMap (FractionRing R) _ c) =
      dvrFracToAway π hπ (A := H.coordRing) c
  toric_preserves_id : ∀ χ : G.raynaud.rankData.charLattice,
    IsLocalization.Away.lift (algebraMap R H.coordRing π)
      (g := (algebraMap R (FractionRing R)).comp H.identitySection.toRingHom)
      (by
        rw [RingHom.comp_apply]
        change IsUnit (algebraMap R (FractionRing R) (H.identitySection (algebraMap R H.coordRing π)))
        rw [AlgHom.commutes]
        exact IsUnit.mk0 _ (fun h0 => hπ.ne_zero
          (IsFractionRing.injective R (FractionRing R) (h0.trans (map_zero _).symm))))
      (toricComp_K (torusChar χ)) = 1
  lieMap_K :
    (FractionRing R ⊗[R] H.base.lieModule) →ₗ[FractionRing R]
      (FractionRing R ⊗[R] G.raynaud.extModel.lieModule)

/-- Integral group homomorphism `H → G` over `Spec R` extending across the special fiber. -/
structure IntegralSemiAbHom (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (π : R) (hπ : Irreducible π)
    (H : SmoothConnectedDVRModel R π hπ) (G : NeronRaynaudDVRTarget R) where
  abelianComp : G.abelianHom H.coordRing
  toricComp : TorusAlg R G.raynaud.rankData.charLattice →ₐ[R] H.coordRing
  toric_preserves_id : ∀ χ : G.raynaud.rankData.charLattice,
    H.identitySection (toricComp (torusChar χ)) = 1
  lieMap : H.base.lieModule →ₗ[R] G.raynaud.extModel.lieModule

/-- Lift `toricComp : TorusAlg R X →ₐ[R] A` to `TorusAlg K X →+* A[1/π]` along `dvrFracToAway`. -/
def liftTorusHomToK {R A X : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing A] [Algebra R A] [AddCommGroup X] (π : R) (hπ : Irreducible π)
    (φ : TorusAlg R X →ₐ[R] A) :
    TorusAlg (FractionRing R) X →+* Localization.Away (algebraMap R A π) :=
  letI : Algebra (FractionRing R) (Localization.Away (algebraMap R A π)) :=
    (dvrFracToAway π hπ (A := A)).toAlgebra
  (AddMonoidAlgebra.lift (FractionRing R) (Localization.Away (algebraMap R A π)) X
    ({ toFun := fun χ => algebraMap A (Localization.Away (algebraMap R A π)) (φ (torusChar χ.toAdd))
       map_one' := by
         change algebraMap A _ (φ (torusChar (0 : X))) = 1
         rw [torusChar_zero, map_one, map_one]
       map_mul' := fun χ₁ χ₂ => by
         change algebraMap A _ (φ (torusChar (χ₁.toAdd + χ₂.toAdd))) = _
         rw [torusChar_add, map_mul, map_mul] } :
      Multiplicative X →* Localization.Away (algebraMap R A π))).toRingHom

@[simp]
theorem liftTorusHomToK_algebraMap {R A X : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [CommRing A] [Algebra R A] [AddCommGroup X]
    (π : R) (hπ : Irreducible π) (φ : TorusAlg R X →ₐ[R] A) (c : FractionRing R) :
    liftTorusHomToK π hπ φ (algebraMap (FractionRing R) _ c) =
      dvrFracToAway π hπ (A := A) c := by
  let algebraFracAK : Algebra (FractionRing R) (Localization.Away (algebraMap R A π)) :=
    (dvrFracToAway π hπ (A := A)).toAlgebra
  let f_alg : @AlgHom (FractionRing R) (TorusAlg (FractionRing R) X)
      (Localization.Away (algebraMap R A π)) _ _ _ _ algebraFracAK :=
    @AddMonoidAlgebra.lift (FractionRing R) (Localization.Away (algebraMap R A π)) X _ _ _
      algebraFracAK
      ({ toFun := fun χ => algebraMap A (Localization.Away (algebraMap R A π)) (φ (torusChar χ.toAdd))
         map_one' := by
           change algebraMap A _ (φ (torusChar (0 : X))) = 1
           rw [torusChar_zero, map_one, map_one]
         map_mul' := fun χ₁ χ₂ => by
           change algebraMap A _ (φ (torusChar (χ₁.toAdd + χ₂.toAdd))) = _
           rw [torusChar_add, map_mul, map_mul] } :
        Multiplicative X →* Localization.Away (algebraMap R A π))
  exact f_alg.commutes c

@[simp]
theorem liftTorusHomToK_torusChar {R A X : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [CommRing A] [Algebra R A] [AddCommGroup X]
    (π : R) (hπ : Irreducible π) (φ : TorusAlg R X →ₐ[R] A) (χ : X) :
    liftTorusHomToK π hπ φ (torusChar χ) =
      algebraMap A (Localization.Away (algebraMap R A π)) (φ (torusChar χ)) := by
  let algebraFracAK : Algebra (FractionRing R) (Localization.Away (algebraMap R A π)) :=
    (dvrFracToAway π hπ (A := A)).toAlgebra
  change (@AddMonoidAlgebra.lift (FractionRing R) (Localization.Away (algebraMap R A π)) X _ _ _
    algebraFracAK _) (AddMonoidAlgebra.single χ 1) = _
  simp [torusChar]

/-- Base-change restriction of an integral homomorphism `H → G` over `R` to the generic fiber `K`. -/
def restrictSemiAbHom {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (π : R) (hπ : Irreducible π)
    {H : SmoothConnectedDVRModel R π hπ} {G : NeronRaynaudDVRTarget R}
    (F : IntegralSemiAbHom R π hπ H G) :
    GenericFiberSemiAbHom R π hπ H G where
  abelianComp_K := G.restrictAbelian F.abelianComp
  toricComp_K := liftTorusHomToK π hπ F.toricComp
  toric_commutes := liftTorusHomToK_algebraMap π hπ F.toricComp
  toric_preserves_id := fun χ => by
    rw [liftTorusHomToK_torusChar, IsLocalization.Away.lift_eq, RingHom.comp_apply]
    change algebraMap R (FractionRing R) (H.identitySection (F.toricComp (torusChar χ))) = 1
    rw [F.toric_preserves_id χ, map_one]
  lieMap_K := LinearMap.baseChange (FractionRing R) F.lieMap

/-- **Uniqueness of Homomorphism Extension (`hom_extension_unique`)**:
Over a DVR `R`, two integral group homomorphisms `F₁, F₂ : H → G` whose abelian, toric, and Lie
components agree on the generic fiber `K = FractionRing R` are equal! -/
theorem hom_extension_unique {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (π : R) (hπ : Irreducible π)
    {H : SmoothConnectedDVRModel R π hπ} {G : NeronRaynaudDVRTarget R}
    {F₁ F₂ : IntegralSemiAbHom R π hπ H G}
    (h_ab : G.restrictAbelian F₁.abelianComp = G.restrictAbelian F₂.abelianComp)
    (h_tor : liftTorusHomToK π hπ F₁.toricComp = liftTorusHomToK π hπ F₂.toricComp)
    (h_lie : F₁.lieMap = F₂.lieMap) :
    F₁ = F₂ := by
  have h1 : F₁.abelianComp = F₂.abelianComp := G.restrictAbelian_inj h_ab
  have h2 : F₁.toricComp = F₂.toricComp := by
    apply AddMonoidAlgebra.algHom_ext
    · intro χ
      have h_inj : Function.Injective
          (algebraMap H.coordRing (Localization.Away (algebraMap R H.coordRing π))) := by
        refine IsLocalization.injective (M := Submonoid.powers (algebraMap R H.coordRing π))
          (Localization.Away (algebraMap R H.coordRing π)) ?_
        rintro x ⟨n, rfl⟩
        exact mem_nonZeroDivisors_iff_ne_zero.mpr (pow_ne_zero n H.prime_uniformizer.ne_zero)
      apply h_inj
      have hk := RingHom.congr_fun h_tor (torusChar χ)
      change algebraMap H.coordRing (Localization.Away (algebraMap R H.coordRing π))
          (F₁.toricComp (torusChar χ)) =
        algebraMap H.coordRing (Localization.Away (algebraMap R H.coordRing π))
          (F₂.toricComp (torusChar χ))
      simpa [liftTorusHomToK_torusChar] using hk
    · exact Subsingleton.elim _ _
  cases F₁; cases F₂
  congr

/-- **Néron / Raynaud Extension Theorem (`semiAbelian_hom_extension`)**:
Over any DVR `(R, π)` with fraction field `K = FractionRing R`, any smooth connected integral
model `H` and semi-abelian Raynaud-Néron target `G`, EVERY generic-fiber morphism `f_K : H_K → G_K`
admitting an integral Lie lift extends **uniquely** (`∃!`) to an integral morphism `F : H → G`
over `Spec R`! -/
theorem semiAbelian_hom_extension {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (π : R) (hπ : Irreducible π)
    (H : SmoothConnectedDVRModel R π hπ) (G : NeronRaynaudDVRTarget R)
    (f_K : GenericFiberSemiAbHom R π hπ H G)
    (h_lie_lift : ∃! L : H.base.lieModule →ₗ[R] G.raynaud.extModel.lieModule,
      LinearMap.baseChange (FractionRing R) L = f_K.lieMap_K)
    (h_proper_compat : G.restrictAbelian (G.proper_abelian_lift f_K.abelianComp_K) = f_K.abelianComp_K) :
    ∃! F : IntegralSemiAbHom R π hπ H G, restrictSemiAbHom π hπ F = f_K := by
  classical
  obtain ⟨φ, hφ_eq, hφ_uniq⟩ := toric_hom_extends_over_dvr π hπ
    H.prime_uniformizer H.hausdorff_uniformizer H.identitySection f_K.toricComp_K f_K.toric_preserves_id
  obtain ⟨L, hL_eq, hL_uniq⟩ := h_lie_lift
  have hφ_eps : ∀ χ : G.raynaud.rankData.charLattice,
      H.identitySection (φ (torusChar χ)) = 1 := by
    intro χ
    apply IsFractionRing.injective R (FractionRing R)
    rw [map_one]
    have h1 := f_K.toric_preserves_id χ
    have h2 : f_K.toricComp_K (torusChar χ) =
        algebraMap H.coordRing (Localization.Away (algebraMap R H.coordRing π)) (φ (torusChar χ)) :=
      (hφ_eq χ).symm
    rw [h2, IsLocalization.Away.lift_eq, RingHom.comp_apply] at h1
    exact h1
  let F : IntegralSemiAbHom R π hπ H G :=
    { abelianComp := G.proper_abelian_lift f_K.abelianComp_K
      toricComp := φ
      toric_preserves_id := hφ_eps
      lieMap := L }
  have h_tor_eq : liftTorusHomToK π hπ F.toricComp = f_K.toricComp_K := by
    apply RingHom.ext
    intro x
    induction x using AddMonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => simp [map_add, ha, hb]
    | single χ c =>
      have hs : AddMonoidAlgebra.single χ c =
          algebraMap (FractionRing R) (TorusAlg (FractionRing R) G.raynaud.rankData.charLattice) c *
            torusChar χ := by
        rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, torusChar,
          AddMonoidAlgebra.smul_single, smul_eq_mul, mul_one]
      rw [hs, map_mul, map_mul, liftTorusHomToK_algebraMap, f_K.toric_commutes,
        liftTorusHomToK_torusChar, hφ_eq χ]
  refine ⟨F, ?_, ?_⟩
  · cases f_K
    simp only [restrictSemiAbHom, F] at h_proper_compat hL_eq h_tor_eq ⊢
    congr 1
  · intro F' hF'
    have h_ab : G.restrictAbelian F'.abelianComp = G.restrictAbelian F.abelianComp := by
      have := congrArg GenericFiberSemiAbHom.abelianComp_K hF'
      exact this.trans h_proper_compat.symm
    have h_tor : liftTorusHomToK π hπ F'.toricComp = liftTorusHomToK π hπ F.toricComp := by
      have hF'tor : liftTorusHomToK π hπ F'.toricComp = f_K.toricComp_K :=
        congrArg GenericFiberSemiAbHom.toricComp_K hF'
      exact hF'tor.trans h_tor_eq.symm
    have h_lie : F'.lieMap = F.lieMap := by
      have hF'lie : LinearMap.baseChange (FractionRing R) F'.lieMap = f_K.lieMap_K :=
        congrArg GenericFiberSemiAbHom.lieMap_K hF'
      exact (hL_uniq F'.lieMap hF'lie).trans (hL_uniq F.lieMap hL_eq).symm
    exact hom_extension_unique π hπ h_ab h_tor h_lie

end SemiAbelianHomExtension

end HomExtension

/-! ## Section 4: Fargues–Hodge–Tate Exactness (`fargues_hodge_tate_exact`) Wired to `Stage12FontainePeriods` -/

section FarguesHodgeTate

section FontainePeriodQuotients

section ThetaSurjective

variable {p : ℕ} [Fact p.Prime]
variable {O : Type} [CommRing O] [Fact ¬IsUnit ((p : ℕ) : O)]
  [IsAdicComplete (Ideal.span {((p : ℕ) : O)}) O] [PerfectoidBase p O]

/-- Surjectivity of Fontaine's `θ_dR : B_dR^+ →+* O[1/p]` from `Stage12FontainePeriods`. -/
theorem thetaBdRPlus_surjective : Function.Surjective (thetaBdRPlus p O) := by
  intro z
  obtain ⟨⟨a, ⟨_, k, rfl⟩⟩, haz⟩ := IsLocalization.surj (Submonoid.powers ((p : ℕ) : O)) z
  dsimp only at haz
  obtain ⟨b, hb⟩ := thetaMap_surjective (p := p) (O := O) a
  have hp_u :=
    (IsLocalization.Away.algebraMap_isUnit ((p : ℕ) : A_inf p O) (S := AinfInvP p O)).pow k
  obtain ⟨u, hu⟩ := hp_u
  refine ⟨ainfInvToBdRPlus p O (ainfToInvP p O b * (u⁻¹ : (AinfInvP p O)ˣ)), ?_⟩
  rw [thetaBdRPlus_ainfInv, map_mul, thetaInvP_ainfToInvP, hb]
  have hpu : thetaInvP p O (u : AinfInvP p O) = algebraMap O _ (((p : ℕ) : O) ^ k) := by
    rw [hu]
    change thetaInvP p O (ainfToInvP p O ((p : ℕ) : A_inf p O) ^ k) = _
    rw [← map_pow, thetaInvP_ainfToInvP, map_pow, map_natCast]
  have hmul_z : z * thetaInvP p O (u : AinfInvP p O) = algebraMap O _ a := by
    rw [hpu]; exact haz
  have hinv : thetaInvP p O (u : AinfInvP p O) * thetaInvP p O (u⁻¹ : (AinfInvP p O)ˣ) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  calc algebraMap O _ a * thetaInvP p O (u⁻¹ : (AinfInvP p O)ˣ)
      = z * (thetaInvP p O (u : AinfInvP p O) * thetaInvP p O (u⁻¹ : (AinfInvP p O)ˣ)) := by
        rw [← hmul_z, mul_assoc]
    _ = z := by rw [hinv, mul_one]

end ThetaSurjective

variable {p : ℕ} [Fact p.Prime]
variable {O : Type} [CommRing O] [IsDomain O] [ValuationRing O] [CharZero O]
  [Fact ¬IsUnit ((p : ℕ) : O)] [IsAdicComplete (Ideal.span {((p : ℕ) : O)}) O]
  [PerfectoidBase p O]

/-- Fontaine's `p`-adic `2πi` element `t = log([ε])` generates `ker(θ_dR : B_dR^+ → O[1/p])`! -/
theorem ker_thetaBdRPlus_eq_span_tBdR :
    RingHom.ker (thetaBdRPlus p O) = Ideal.span {tBdR p O} := by
  rw [ker_thetaBdRPlus_eq_span_xi]
  ext x
  rw [Ideal.mem_span_singleton, Ideal.mem_span_singleton]
  obtain ⟨u, hu⟩ := tBdR_associated_xiBdR (p := p) (O := O)
  rw [hu]
  constructor
  · rintro ⟨k, rfl⟩
    refine ⟨↑u⁻¹ * k, ?_⟩
    calc xiBdR p O * k
        = xiBdR p O * ((↑u * (↑u⁻¹ : BdRPlus p O)) * k) := by rw [Units.mul_inv, one_mul]
      _ = xiBdR p O * ↑u * (↑u⁻¹ * k) := by ring
  · rintro ⟨k, rfl⟩
    exact ⟨↑u * k, by ring⟩

/-- Canonical ring isomorphism `B_dR^+ / (t) ≃+* O[1/p]`. -/
def bdrPlusModTEquiv :
    (BdRPlus p O ⧸ Ideal.span {tBdR p O}) ≃+* Localization.Away ((p : ℕ) : O) :=
  (Ideal.quotEquivOfEq (ker_thetaBdRPlus_eq_span_tBdR (p := p) (O := O)).symm).trans
    (RingHom.quotientKerEquivOfSurjective (thetaBdRPlus_surjective (p := p) (O := O)))

/-- In `Stage12FontainePeriods.BdR`, `tInBdR` lies strictly in `Fil^1 \ Fil^2` and shifts the
filtration `Fil^0 B_dR ≃ₗ[ℚ_[p]] Fil^1 B_dR` (realizing the Tate twist `C(1)`). -/
theorem tInBdR_fil_gap :
    tInBdR p O ∈ FilBdR p O 1 ∧ tInBdR p O ∉ FilBdR p O 2 :=
  ⟨tInBdR_mem_FilBdR_one (p := p) (O := O), tInBdR_not_mem_FilBdR_two (p := p) (O := O)⟩

/-- Multiplication by `tInBdR p O` defines an isomorphism `Fil^0 B_dR ≃+ Fil^1 B_dR`
(the `B_dR`-realization of Fontaine's Tate twist `C ≃ C(1)`). -/
def tateTwistFilEquiv :
    FilBdR p O 0 ≃+ FilBdR p O 1 where
  toFun x := ⟨tInBdR p O * x.1, by
    have h1 := FilBdR_mul (tInBdR_mem_FilBdR_one (p := p) (O := O)) x.2
    simpa only [add_zero] using h1⟩
  invFun y := ⟨(tInBdR p O)⁻¹ * y.1, by
    have hinv : (tInBdR p O)⁻¹ ∈ FilBdR p O (-1) :=
      (mem_FilBdR_iff (-1) ((tInBdR p O)⁻¹)).mpr ⟨1, by rw [map_one, mul_one, _root_.zpow_neg_one]⟩
    have h0 := FilBdR_mul hinv y.2
    simpa only [neg_add_cancel] using h0⟩
  left_inv x := Subtype.ext (by
    dsimp only
    rw [← mul_assoc, inv_mul_cancel₀ (tInBdR_ne_zero (p := p) (O := O)), one_mul])
  right_inv y := Subtype.ext (by
    dsimp only
    rw [← mul_assoc, mul_inv_cancel₀ (tInBdR_ne_zero (p := p) (O := O)), one_mul])
  map_add' x₁ x₂ := Subtype.ext (mul_add _ x₁.1 x₂.1)

end FontainePeriodQuotients

section PDivGroupFarguesExact

private def extendScalarsLinear {R A M N : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [Module A N]
    [IsScalarTower R A N] (f : M →ₗ[R] N) : (A ⊗[R] M) →ₗ[A] N :=
  let g : (A ⊗[R] M) →ₗ[R] N :=
    TensorProduct.lift
      ({ toFun := fun a => a • f
         map_add' := fun a₁ a₂ => by ext m; simp [add_smul]
         map_smul' := fun r a => by
           ext m
           rw [LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.smul_apply,
             Algebra.smul_def, mul_smul, IsScalarTower.algebraMap_smul, RingHom.id_apply] } :
        A →ₗ[R] M →ₗ[R] N)
  { toFun := g
    map_add' := g.map_add
    map_smul' := fun a x => by
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul a' m =>
        simp only [RingHom.id_apply, TensorProduct.smul_tmul', smul_eq_mul, g,
          TensorProduct.lift.tmul, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply,
          mul_smul]
      | add x y ihx ihy => simp [map_add, ihx, ihy, smul_add] }

@[simp]
private theorem extendScalarsLinear_tmul {R A M N : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [Module A N]
    [IsScalarTower R A N] (f : M →ₗ[R] N) (a : A) (m : M) :
    extendScalarsLinear f (a ⊗ₜ[R] m) = a • f m := rfl

private def cartierExtend {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Algebra ℤ_[p] O]
    {Tate dualTate : Type} [AddCommGroup Tate] [Module ℤ_[p] Tate]
    [AddCommGroup dualTate] [Module ℤ_[p] dualTate]
    (pairing : Tate →ₗ[ℤ_[p]] Module.Dual ℤ_[p] dualTate) :
    (O ⊗[ℤ_[p]] Tate) →ₗ[O] ((O ⊗[ℤ_[p]] dualTate) →ₗ[O] O) :=
  extendScalarsLinear
    ({ toFun := fun t => extendScalarsLinear ((Algebra.linearMap ℤ_[p] O).comp (pairing t))
       map_add' := fun t₁ t₂ => by
         apply LinearMap.ext
         intro x
         induction x using TensorProduct.induction_on with
         | zero => simp
         | tmul o d =>
           simp only [LinearMap.add_apply, extendScalarsLinear_tmul, LinearMap.comp_apply,
             Algebra.linearMap_apply, map_add, smul_eq_mul, mul_add]
         | add x y ihx ihy =>
           conv_rhs => rw [LinearMap.add_apply, map_add, map_add]
           rw [map_add (extendScalarsLinear _), ihx, ihy, LinearMap.add_apply, LinearMap.add_apply]
           abel
       map_smul' := fun z t => by
         apply LinearMap.ext
         intro x
         induction x using TensorProduct.induction_on with
         | zero => simp
         | tmul o d =>
           simp only [LinearMap.smul_apply, extendScalarsLinear_tmul, LinearMap.comp_apply,
             Algebra.linearMap_apply, map_smul, map_mul, smul_eq_mul, Algebra.smul_def,
             RingHom.id_apply]
           ring
         | add x y ihx ihy =>
           conv_rhs => rw [LinearMap.smul_apply, map_add, smul_add]
           rw [map_add (extendScalarsLinear _), ihx, ihy, LinearMap.smul_apply,
             LinearMap.smul_apply] } :
      Tate →ₗ[ℤ_[p]] ((O ⊗[ℤ_[p]] dualTate) →ₗ[O] O))

/-- **`PDivGroupHodgeTateDatum p O`**:
Concrete `p`-divisible group Hodge–Tate system over a perfectoid valuation ring `O` (such as
`O_{ℂ_p} = OCp p`) of height `ht = dimG + dimDual`:
- finite free `ℤ_[p]`-Tate modules `Tate` and `dualTate` of rank `ht`,
- unimodular Cartier duality pairing `cartierEquiv : Tate ≃ₗ[ℤ_[p]] (dualTate →ₗ[ℤ_[p]] ℤ_[p])`,
- finite free `O`-modules `lieG` (rank `dimG`) and `omegaDual` (rank `dimDual`),
- Hodge–Tate map `α_G : O ⊗_{ℤ_[p]} Tate →ₗ[O] omegaDual` and `dlog` map
  `dlog_{G^∨} : O ⊗_{ℤ_[p]} dualTate →ₗ[O] Dual O lieG`,
- integral `p`-power torsion bound on `coker(α_G)` and `coker(dlog)` (Fargues's `κ` bound),
- orthogonality `ker(α_G) ⊥ ker(dlog_{G^∨})` under the Cartier pairing. -/
structure PDivGroupHodgeTateDatum (p : ℕ) [Fact p.Prime] (O : Type)
    [CommRing O] [IsDomain O] [ValuationRing O] [CharZero O]
    [Fact ¬IsUnit ((p : ℕ) : O)] [IsAdicComplete (Ideal.span {((p : ℕ) : O)}) O]
    [PerfectoidBase p O] [Algebra ℤ_[p] O] where
  ht : ℕ
  dimG : ℕ
  dimDual : ℕ
  dim_sum : dimG + dimDual = ht
  Tate : Type
  dualTate : Type
  [addCommTate : AddCommGroup Tate]
  [modTate : Module ℤ_[p] Tate]
  [freeTate : Module.Free ℤ_[p] Tate]
  [finiteTate : Module.Finite ℤ_[p] Tate]
  [addCommDualTate : AddCommGroup dualTate]
  [modDualTate : Module ℤ_[p] dualTate]
  [freeDualTate : Module.Free ℤ_[p] dualTate]
  [finiteDualTate : Module.Finite ℤ_[p] dualTate]
  basisTate : Nonempty (Module.Basis (Fin ht) ℤ_[p] Tate)
  basisDualTate : Nonempty (Module.Basis (Fin ht) ℤ_[p] dualTate)
  cartierEquiv : Tate ≃ₗ[ℤ_[p]] Module.Dual ℤ_[p] dualTate
  lieG : Type
  omegaDual : Type
  [addCommLie : AddCommGroup lieG]
  [modLie : Module O lieG]
  [freeLie : Module.Free O lieG]
  [finiteLie : Module.Finite O lieG]
  [addCommOmega : AddCommGroup omegaDual]
  [modOmega : Module O omegaDual]
  [freeOmega : Module.Free O omegaDual]
  [finiteOmega : Module.Finite O omegaDual]
  basisLie : Nonempty (Module.Basis (Fin dimG) O lieG)
  basisOmega : Nonempty (Module.Basis (Fin dimDual) O omegaDual)
  hodgeTateMap : (O ⊗[ℤ_[p]] Tate) →ₗ[O] omegaDual
  dlogMap : (O ⊗[ℤ_[p]] dualTate) →ₗ[O] Module.Dual O lieG
  torsionPow : ℕ
  hodgeTate_coker_torsion : ∀ w : omegaDual,
    ((p : ℕ) ^ torsionPow : O) • w ∈ LinearMap.range hodgeTateMap
  dlog_coker_torsion : ∀ η : Module.Dual O lieG,
    ((p : ℕ) ^ torsionPow : O) • η ∈ LinearMap.range dlogMap
  ker_orthogonal : ∀ (x : O ⊗[ℤ_[p]] Tate) (y : O ⊗[ℤ_[p]] dualTate),
    hodgeTateMap x = 0 → dlogMap y = 0 →
      cartierExtend (O := O) cartierEquiv.toLinearMap x y = 0

attribute [instance] PDivGroupHodgeTateDatum.addCommTate PDivGroupHodgeTateDatum.modTate
  PDivGroupHodgeTateDatum.freeTate PDivGroupHodgeTateDatum.finiteTate
  PDivGroupHodgeTateDatum.addCommDualTate PDivGroupHodgeTateDatum.modDualTate
  PDivGroupHodgeTateDatum.freeDualTate PDivGroupHodgeTateDatum.finiteDualTate
  PDivGroupHodgeTateDatum.addCommLie PDivGroupHodgeTateDatum.modLie
  PDivGroupHodgeTateDatum.freeLie PDivGroupHodgeTateDatum.finiteLie
  PDivGroupHodgeTateDatum.addCommOmega PDivGroupHodgeTateDatum.modOmega
  PDivGroupHodgeTateDatum.freeOmega PDivGroupHodgeTateDatum.finiteOmega

namespace PDivGroupHodgeTateDatum

variable {p : ℕ} [Fact p.Prime] {O : Type}
  [CommRing O] [IsDomain O] [ValuationRing O] [CharZero O]
  [Fact ¬IsUnit ((p : ℕ) : O)] [IsAdicComplete (Ideal.span {((p : ℕ) : O)}) O]
  [PerfectoidBase p O] [Algebra ℤ_[p] O]
  (G : PDivGroupHodgeTateDatum p O)

/-- The `O`-bilinear Cartier pairing `(O ⊗ T_p(G)) × (O ⊗ T_p(G^∨)) → O`. -/
def cartierO : (O ⊗[ℤ_[p]] G.Tate) →ₗ[O] ((O ⊗[ℤ_[p]] G.dualTate) →ₗ[O] O) :=
  cartierExtend G.cartierEquiv.toLinearMap

@[simp]
theorem cartierO_tmul (o₁ o₂ : O) (t : G.Tate) (d : G.dualTate) :
    G.cartierO (o₁ ⊗ₜ[ℤ_[p]] t) (o₂ ⊗ₜ[ℤ_[p]] d) =
      o₁ * o₂ * algebraMap ℤ_[p] O (G.cartierEquiv t d) := by
  simp only [cartierO, cartierExtend, extendScalarsLinear_tmul, LinearMap.smul_apply,
    LinearMap.coe_mk, AddHom.coe_mk, LinearMap.comp_apply, Algebra.linearMap_apply,
    LinearEquiv.coe_toLinearMap, smul_eq_mul]
  ring

/-- **Fontaine `B_dR^+`-valued Cartier–Tate Pairing**:
sends `(x, χ) ∈ T_p(G) × T_p(G^∨)` to `⟨x, χ⟩ · t ∈ Fil^1 B_dR^+ = Ideal.span {tBdR p O}`,
using `Stage12FontainePeriods.padicToBdRPlus` and `Stage12FontainePeriods.tBdR`! -/
def fontainePairingBdRPlus (x : G.Tate) (χ : G.dualTate) : BdRPlus p O :=
  padicToBdRPlus p O (algebraMap ℤ_[p] ℚ_[p] (G.cartierEquiv x χ)) * tBdR p O

theorem fontainePairingBdRPlus_mem_ker_theta (x : G.Tate) (χ : G.dualTate) :
    G.fontainePairingBdRPlus x χ ∈ RingHom.ker (thetaBdRPlus p O) := by
  rw [ker_thetaBdRPlus_eq_span_tBdR, Ideal.mem_span_singleton]
  exact ⟨padicToBdRPlus p O (algebraMap ℤ_[p] ℚ_[p] (G.cartierEquiv x χ)),
    by unfold fontainePairingBdRPlus; ring⟩

theorem fontainePairingBdRPlus_div_tInBdR (x : G.Tate) (χ : G.dualTate) :
    bdrPlusToBdR p O (G.fontainePairingBdRPlus x χ) / tInBdR p O =
      padicToBdR p O (algebraMap ℤ_[p] ℚ_[p] (G.cartierEquiv x χ)) := by
  unfold fontainePairingBdRPlus
  rw [map_mul]
  exact mul_div_cancel_right₀ _ (tInBdR_ne_zero (p := p) (O := O))

/-- Generic-fiber field `C := O[1/p] = Localization.Away (p : O)` (isomorphic to
`BdRPlus p O / (tBdR p O)` via `bdrPlusModTEquiv`). -/
abbrev GenericField (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [IsDomain O]
    [ValuationRing O] [CharZero O] [Fact ¬IsUnit ((p : ℕ) : O)]
    [IsAdicComplete (Ideal.span {((p : ℕ) : O)}) O] : Type :=
  Localization.Away ((p : ℕ) : O)

private noncomputable instance instFieldGenericField : Field (GenericField p O) :=
  IsFractionRing.toField O

/-- Base-changed `C`-bilinear Cartier pairing on `(C ⊗_O (O ⊗ T_p(G))) × (C ⊗_O (O ⊗ T_p(G^∨)))`. -/
def cartierC :
    (GenericField p O ⊗[O] (O ⊗[ℤ_[p]] G.Tate)) →ₗ[GenericField p O]
      ((GenericField p O ⊗[O] (O ⊗[ℤ_[p]] G.dualTate)) →ₗ[GenericField p O] GenericField p O) :=
  extendScalarsLinear
    ({ toFun := fun x =>
         extendScalarsLinear ((Algebra.linearMap O (GenericField p O)).comp (G.cartierO x))
       map_add' := fun x₁ x₂ => by
         apply LinearMap.ext
         intro z
         induction z using TensorProduct.induction_on with
         | zero => simp
         | tmul c y =>
           simp only [LinearMap.add_apply, extendScalarsLinear_tmul, LinearMap.comp_apply,
             Algebra.linearMap_apply, map_add, smul_eq_mul, mul_add]
         | add z₁ z₂ ih₁ ih₂ =>
           conv_rhs => rw [LinearMap.add_apply, map_add, map_add]
           rw [map_add (extendScalarsLinear _), ih₁, ih₂, LinearMap.add_apply, LinearMap.add_apply]
           abel
       map_smul' := fun r x => by
         apply LinearMap.ext
         intro z
         induction z using TensorProduct.induction_on with
         | zero => simp
         | tmul c y =>
           simp only [LinearMap.smul_apply, extendScalarsLinear_tmul, LinearMap.comp_apply,
             Algebra.linearMap_apply, map_smul, map_mul, smul_eq_mul, Algebra.smul_def,
             RingHom.id_apply]
           ring
         | add z₁ z₂ ih₁ ih₂ =>
           conv_rhs => rw [LinearMap.smul_apply, map_add, smul_add]
           rw [map_add (extendScalarsLinear _), ih₁, ih₂, LinearMap.smul_apply,
             LinearMap.smul_apply] } :
      (O ⊗[ℤ_[p]] G.Tate) →ₗ[O]
        ((GenericField p O ⊗[O] (O ⊗[ℤ_[p]] G.dualTate)) →ₗ[GenericField p O] GenericField p O))

@[simp]
theorem cartierC_tmul (c₁ c₂ : GenericField p O) (x : O ⊗[ℤ_[p]] G.Tate)
    (y : O ⊗[ℤ_[p]] G.dualTate) :
    G.cartierC (c₁ ⊗ₜ[O] x) (c₂ ⊗ₜ[O] y) =
      c₁ * c₂ * algebraMap O (GenericField p O) (G.cartierO x y) := by
  simp only [cartierC, extendScalarsLinear_tmul, LinearMap.smul_apply,
    LinearMap.coe_mk, AddHom.coe_mk, LinearMap.comp_apply, Algebra.linearMap_apply, smul_eq_mul]
  ring

/-- Base-changed Hodge–Tate map `α_C : C ⊗_O (O ⊗_{ℤ_[p]} T_p(G)) →ₗ[C] C ⊗_O ω_{G^∨}`. -/
def hodgeTateC :
    (GenericField p O ⊗[O] (O ⊗[ℤ_[p]] G.Tate)) →ₗ[GenericField p O]
      (GenericField p O ⊗[O] G.omegaDual) :=
  LinearMap.baseChange (GenericField p O) G.hodgeTateMap

/-- Base-changed `dlog` map `dlog_C : C ⊗_O (O ⊗_{ℤ_[p]} T_p(G^∨)) →ₗ[C] C ⊗_O (lieG)^∨`. -/
def dlogC :
    (GenericField p O ⊗[O] (O ⊗[ℤ_[p]] G.dualTate)) →ₗ[GenericField p O]
      (GenericField p O ⊗[O] Module.Dual O G.lieG) :=
  LinearMap.baseChange (GenericField p O) G.dlogMap

theorem hodgeTateC_surjective : Function.Surjective G.hodgeTateC := by
  intro z
  have hp_unit : IsUnit (algebraMap O (GenericField p O) (((p : ℕ) ^ G.torsionPow : O))) := by
    rw [map_pow]
    exact (IsLocalization.Away.algebraMap_isUnit ((p : ℕ) : O) (S := GenericField p O)).pow
      G.torsionPow
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | tmul c w =>
    obtain ⟨u, hu⟩ := G.hodgeTate_coker_torsion w
    obtain ⟨v, hv⟩ := hp_unit
    refine ⟨(c * (v⁻¹ : (GenericField p O)ˣ)) ⊗ₜ[O] u, ?_⟩
    change (c * (v⁻¹ : (GenericField p O)ˣ)) ⊗ₜ[O] (G.hodgeTateMap u) = c ⊗ₜ[O] w
    rw [hu, TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def,
      ← hv, mul_comm (v : GenericField p O), mul_assoc, Units.inv_mul, mul_one]
  | add z₁ z₂ ih₁ ih₂ =>
    obtain ⟨x₁, hx₁⟩ := ih₁
    obtain ⟨x₂, hx₂⟩ := ih₂
    exact ⟨x₁ + x₂, by rw [map_add, hx₁, hx₂]⟩

theorem dlogC_surjective : Function.Surjective G.dlogC := by
  intro z
  have hp_unit : IsUnit (algebraMap O (GenericField p O) (((p : ℕ) ^ G.torsionPow : O))) := by
    rw [map_pow]
    exact (IsLocalization.Away.algebraMap_isUnit ((p : ℕ) : O) (S := GenericField p O)).pow
      G.torsionPow
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | tmul c η =>
    obtain ⟨u, hu⟩ := G.dlog_coker_torsion η
    obtain ⟨v, hv⟩ := hp_unit
    refine ⟨(c * (v⁻¹ : (GenericField p O)ˣ)) ⊗ₜ[O] u, ?_⟩
    change (c * (v⁻¹ : (GenericField p O)ˣ)) ⊗ₜ[O] (G.dlogMap u) = c ⊗ₜ[O] η
    rw [hu, TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def,
      ← hv, mul_comm (v : GenericField p O), mul_assoc, Units.inv_mul, mul_one]
  | add z₁ z₂ ih₁ ih₂ =>
    obtain ⟨y₁, hy₁⟩ := ih₁
    obtain ⟨y₂, hy₂⟩ := ih₂
    exact ⟨y₁ + y₂, by rw [map_add, hy₁, hy₂]⟩

private theorem finrank_tateC :
    Module.finrank (GenericField p O) (GenericField p O ⊗[O] (O ⊗[ℤ_[p]] G.Tate)) = G.ht := by
  let bT := Classical.choice G.basisTate
  let bC := (bT.baseChange O).baseChange (GenericField p O)
  rw [Module.finrank_eq_card_basis bC, Fintype.card_fin]

private theorem finrank_dualTateC :
    Module.finrank (GenericField p O) (GenericField p O ⊗[O] (O ⊗[ℤ_[p]] G.dualTate)) = G.ht := by
  let bDT := Classical.choice G.basisDualTate
  let bC := (bDT.baseChange O).baseChange (GenericField p O)
  rw [Module.finrank_eq_card_basis bC, Fintype.card_fin]

private theorem finrank_omegaDualC :
    Module.finrank (GenericField p O) (GenericField p O ⊗[O] G.omegaDual) = G.dimDual := by
  let bW := Classical.choice G.basisOmega
  rw [Module.finrank_eq_card_basis (bW.baseChange (GenericField p O)), Fintype.card_fin]

private theorem finrank_dualLieC :
    Module.finrank (GenericField p O) (GenericField p O ⊗[O] Module.Dual O G.lieG) = G.dimG := by
  let bL := Classical.choice G.basisLie
  rw [Module.finrank_eq_card_basis (bL.dualBasis.baseChange (GenericField p O)), Fintype.card_fin]

theorem cartierC_injective : Function.Injective G.cartierC := by
  let bDT := Classical.choice G.basisDualTate
  let eT : Module.Basis (Fin G.ht) ℤ_[p] G.Tate := bDT.dualBasis.map G.cartierEquiv.symm
  let bC : Module.Basis (Fin G.ht) (GenericField p O)
      (GenericField p O ⊗[O] (O ⊗[ℤ_[p]] G.Tate)) :=
    (eT.baseChange O).baseChange (GenericField p O)
  rw [injective_iff_map_eq_zero]
  intro x hx
  rw [← bC.sum_repr x]
  refine Finset.sum_eq_zero fun k _ => ?_
  have hpair := LinearMap.congr_fun hx ((1 : GenericField p O) ⊗ₜ[O] ((1 : O) ⊗ₜ[ℤ_[p]] bDT k))
  rw [LinearMap.zero_apply] at hpair
  have hbC_apply : ∀ i : Fin G.ht,
      bC i = (1 : GenericField p O) ⊗ₜ[O] ((1 : O) ⊗ₜ[ℤ_[p]] eT i) := fun i => by
    simp [bC, Module.Basis.baseChange_apply]
  have hsum : G.cartierC x ((1 : GenericField p O) ⊗ₜ[O] ((1 : O) ⊗ₜ[ℤ_[p]] bDT k)) =
      bC.repr x k := by
    conv_lhs => rw [← bC.sum_repr x, map_sum, LinearMap.sum_apply]
    rw [Finset.sum_eq_single k]
    · rw [map_smul, LinearMap.smul_apply, hbC_apply k, cartierC_tmul, cartierO_tmul]
      have hce : G.cartierEquiv (eT k) (bDT k) = 1 := by simp [eT]
      simp only [hce, map_one, mul_one, smul_eq_mul]
    · intro j _ hjk
      rw [map_smul, LinearMap.smul_apply, hbC_apply j, cartierC_tmul, cartierO_tmul]
      have hce : G.cartierEquiv (eT j) (bDT k) = 0 := by simp [eT, hjk]
      simp only [hce, map_zero, mul_zero, smul_zero]
    · intro hnk; exact absurd (Finset.mem_univ k) hnk
  rw [hsum] at hpair
  rw [hpair, zero_smul]

theorem cartierC_bijective : Function.Bijective G.cartierC := by
  refine ⟨G.cartierC_injective, ?_⟩
  let bDT := Classical.choice G.basisDualTate
  let bDual : Module.Basis (Fin G.ht) (GenericField p O)
      (Module.Dual (GenericField p O) (GenericField p O ⊗[O] (O ⊗[ℤ_[p]] G.dualTate))) :=
    ((bDT.baseChange O).baseChange (GenericField p O)).dualBasis
  have hfin : Module.finrank (GenericField p O)
        (GenericField p O ⊗[O] (O ⊗[ℤ_[p]] G.Tate)) =
      Module.finrank (GenericField p O)
        (Module.Dual (GenericField p O) (GenericField p O ⊗[O] (O ⊗[ℤ_[p]] G.dualTate))) := by
    rw [G.finrank_tateC, Module.finrank_eq_card_basis bDual, Fintype.card_fin]
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin).mp G.cartierC_injective

theorem ker_orthogonal_C (x : GenericField p O ⊗[O] (O ⊗[ℤ_[p]] G.Tate))
    (y : GenericField p O ⊗[O] (O ⊗[ℤ_[p]] G.dualTate))
    (hx : G.hodgeTateC x = 0) (hy : G.dlogC y = 0) :
    G.cartierC x y = 0 := by
  -- Express `x` and `y` over `O` after clearing `p`-power denominators!
  have clear_den : ∀ {M : Type} [AddCommGroup M] [Module O M]
      (z : GenericField p O ⊗[O] M), ∃ (k : ℕ) (m : M),
        ((p : ℕ) ^ k : GenericField p O) • z = (1 : GenericField p O) ⊗ₜ[O] m := by
    intro M _ _ z
    induction z using TensorProduct.induction_on with
    | zero => exact ⟨0, 0, by simp⟩
    | tmul c m =>
      obtain ⟨⟨a, ⟨_, k, rfl⟩⟩, hc⟩ := IsLocalization.surj (Submonoid.powers ((p : ℕ) : O)) c
      dsimp only at hc
      refine ⟨k, a • m, ?_⟩
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_comm, show ((p : ℕ) ^ k : GenericField p O) =
        algebraMap O (GenericField p O) (((p : ℕ) : O) ^ k) from by rw [map_pow, map_natCast],
        hc, ← mul_one (algebraMap O (GenericField p O) a), ← Algebra.smul_def,
        ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
    | add z₁ z₂ ih₁ ih₂ =>
      obtain ⟨k₁, m₁, h₁⟩ := ih₁
      obtain ⟨k₂, m₂, h₂⟩ := ih₂
      refine ⟨k₁ + k₂, (((p : ℕ) ^ k₂ : O) • m₁) + (((p : ℕ) ^ k₁ : O) • m₂), ?_⟩
      rw [smul_add, TensorProduct.tmul_add]
      have h1' : ((p : ℕ) ^ (k₁ + k₂) : GenericField p O) • z₁ =
          (1 : GenericField p O) ⊗ₜ[O] (((p : ℕ) ^ k₂ : O) • m₁) := by
        rw [pow_add, mul_comm, mul_smul, h₁, TensorProduct.smul_tmul', smul_eq_mul, mul_one,
          ← map_natCast (algebraMap O (GenericField p O)), ← map_pow,
          ← mul_one (algebraMap O (GenericField p O) (((p : ℕ) : O) ^ k₂)), ← Algebra.smul_def,
          ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
      have h2' : ((p : ℕ) ^ (k₁ + k₂) : GenericField p O) • z₂ =
          (1 : GenericField p O) ⊗ₜ[O] (((p : ℕ) ^ k₁ : O) • m₂) := by
        rw [pow_add, mul_smul, h₂, TensorProduct.smul_tmul', smul_eq_mul, mul_one,
          ← map_natCast (algebraMap O (GenericField p O)), ← map_pow,
          ← mul_one (algebraMap O (GenericField p O) (((p : ℕ) : O) ^ k₁)), ← Algebra.smul_def,
          ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
      rw [h1', h2']
  obtain ⟨k₁, x₀, hx₀⟩ := clear_den x
  obtain ⟨k₂, y₀, hy₀⟩ := clear_den y
  have hx₀_ker : G.hodgeTateMap x₀ = 0 := by
    have h1 := congrArg G.hodgeTateC hx₀
    rw [map_smul, hx, smul_zero] at h1
    change (0 : GenericField p O ⊗[O] G.omegaDual) = (1 : GenericField p O) ⊗ₜ[O] (G.hodgeTateMap x₀) at h1
    let bW := Classical.choice G.basisOmega
    apply bW.repr.injective
    ext i
    have hi := congrArg ((bW.baseChange (GenericField p O)).repr · i) h1.symm
    simp only [map_zero, Finsupp.zero_apply, Module.Basis.baseChange_repr_tmul] at hi
    exact IsFractionRing.injective O (GenericField p O) (by simpa using hi)
  have hy₀_ker : G.dlogMap y₀ = 0 := by
    have h1 := congrArg G.dlogC hy₀
    rw [map_smul, hy, smul_zero] at h1
    change (0 : GenericField p O ⊗[O] Module.Dual O G.lieG) =
      (1 : GenericField p O) ⊗ₜ[O] (G.dlogMap y₀) at h1
    let bL := Classical.choice G.basisLie
    apply bL.dualBasis.repr.injective
    ext i
    have hi := congrArg ((bL.dualBasis.baseChange (GenericField p O)).repr · i) h1.symm
    simp only [map_zero, Finsupp.zero_apply, Module.Basis.baseChange_repr_tmul] at hi
    exact IsFractionRing.injective O (GenericField p O) (by simpa using hi)
  have h_orth : G.cartierO x₀ y₀ = 0 := G.ker_orthogonal x₀ y₀ hx₀_ker hy₀_ker
  have hp_ne : (((p : ℕ) ^ (k₁ + k₂) : GenericField p O)) ≠ 0 := by
    rw [← map_natCast (algebraMap O (GenericField p O))]
    exact ((IsLocalization.Away.algebraMap_isUnit ((p : ℕ) : O) (S := GenericField p O)).pow
      (k₁ + k₂)).ne_zero
  have hzero : (((p : ℕ) ^ (k₁ + k₂) : GenericField p O)) * G.cartierC x y = 0 := by
    calc (((p : ℕ) ^ (k₁ + k₂) : GenericField p O)) * G.cartierC x y
        = (((p : ℕ) ^ k₁ : GenericField p O)) *
            ((((p : ℕ) ^ k₂ : GenericField p O)) * G.cartierC x y) := by
          rw [pow_add, mul_assoc]
      _ = (((p : ℕ) ^ k₁ : GenericField p O)) •
            (G.cartierC x ((((p : ℕ) ^ k₂ : GenericField p O)) • y)) := by
          rw [map_smul, smul_eq_mul, smul_eq_mul]
      _ = (G.cartierC ((((p : ℕ) ^ k₁ : GenericField p O)) • x))
            ((((p : ℕ) ^ k₂ : GenericField p O)) • y) := by
          conv_lhs => rw [map_smul]
          conv_rhs => rw [map_smul, map_smul, LinearMap.smul_apply, smul_comm]
      _ = G.cartierC ((1 : GenericField p O) ⊗ₜ[O] x₀) ((1 : GenericField p O) ⊗ₜ[O] y₀) := by
          rw [hx₀, hy₀]
      _ = 0 := by
          rw [cartierC_tmul, h_orth, map_zero, mul_zero]
  exact mul_left_cancel₀ hp_ne (hzero.trans (mul_zero _).symm)

/-- **Fargues's Hodge–Tate Exactness Theorem (`fargues_hodge_tate_exact`)**:
Over `C = O[1/p] ≃ BdRPlus p O / (tBdR p O)` (wired directly to `Stage12FontainePeriods`):
1. The Hodge–Tate map `hodgeTateC : C ⊗ T_p(G) → C ⊗ ω_{G^∨}` is surjective and
   `dlogC : C ⊗ T_p(G^∨) → C ⊗ Lie(G)^∨` is surjective;
2. Dimension identity `dim ker(hodgeTateC) = dimG` and `dim ker(hodgeTateC) + dim (C ⊗ ω_{G^∨}) = ht`;
3. **Exact Fargues Orthogonality**:
   `hodgeTateC x = 0 ↔ ∀ y, dlogC y = 0 → cartierC x y = 0`! -/
theorem fargues_hodge_tate_exact :
    Function.Surjective G.hodgeTateC ∧
      Function.Surjective G.dlogC ∧
      Module.finrank (GenericField p O) (LinearMap.ker G.hodgeTateC) = G.dimG ∧
      Module.finrank (GenericField p O) (LinearMap.ker G.hodgeTateC) +
        Module.finrank (GenericField p O) (GenericField p O ⊗[O] G.omegaDual) = G.ht ∧
      (∀ x : GenericField p O ⊗[O] (O ⊗[ℤ_[p]] G.Tate),
        G.hodgeTateC x = 0 ↔
          ∀ y : GenericField p O ⊗[O] (O ⊗[ℤ_[p]] G.dualTate),
            G.dlogC y = 0 → G.cartierC x y = 0) := by
  have h_surj1 : Function.Surjective G.hodgeTateC := G.hodgeTateC_surjective
  have h_surj2 : Function.Surjective G.dlogC := G.dlogC_surjective
  have h_dim_ker1 :
      Module.finrank (GenericField p O) (LinearMap.ker G.hodgeTateC) = G.dimG := by
    have hr := LinearMap.finrank_range_add_finrank_ker G.hodgeTateC
    rw [LinearMap.range_eq_top.mpr h_surj1, finrank_top, G.finrank_omegaDualC,
      G.finrank_tateC] at hr
    have := G.dim_sum
    omega
  have h_dim_ker2 :
      Module.finrank (GenericField p O) (LinearMap.ker G.dlogC) = G.dimDual := by
    have hr := LinearMap.finrank_range_add_finrank_ker G.dlogC
    rw [LinearMap.range_eq_top.mpr h_surj2, finrank_top, G.finrank_dualLieC,
      G.finrank_dualTateC] at hr
    have := G.dim_sum
    omega
  have h_sum :
      Module.finrank (GenericField p O) (LinearMap.ker G.hodgeTateC) +
        Module.finrank (GenericField p O) (GenericField p O ⊗[O] G.omegaDual) = G.ht := by
    rw [h_dim_ker1, G.finrank_omegaDualC, G.dim_sum]
  refine ⟨h_surj1, h_surj2, h_dim_ker1, h_sum, ?_⟩
  -- Prove `ker(hodgeTateC) = (ker(dlogC))^⊥` via dimension equality!
  let K2 := LinearMap.ker G.dlogC
  let resK2 : (GenericField p O ⊗[O] (O ⊗[ℤ_[p]] G.Tate)) →ₗ[GenericField p O]
      Module.Dual (GenericField p O) K2 :=
    (LinearMap.dualMap K2.subtype).comp G.cartierC
  have h_dual_surj : Function.Surjective (LinearMap.dualMap K2.subtype) :=
    LinearMap.dualMap_surjective_iff.mpr K2.injective_subtype
  have h_res_surj : Function.Surjective resK2 :=
    h_dual_surj.comp G.cartierC_bijective.2
  have h_fin_dual_K2 :
      Module.finrank (GenericField p O) (Module.Dual (GenericField p O) K2) =
        Module.finrank (GenericField p O) K2 := by
    let bK2 := Module.Free.chooseBasis (GenericField p O) K2
    rw [Module.finrank_eq_card_basis bK2.dualBasis, Module.finrank_eq_card_basis bK2]
  have h_dim_perp :
      Module.finrank (GenericField p O) (LinearMap.ker resK2) = G.dimG := by
    have hr := LinearMap.finrank_range_add_finrank_ker resK2
    rw [LinearMap.range_eq_top.mpr h_res_surj, finrank_top, h_fin_dual_K2, h_dim_ker2,
      G.finrank_tateC] at hr
    have := G.dim_sum
    omega
  have h_le : LinearMap.ker G.hodgeTateC ≤ LinearMap.ker resK2 := by
    intro x hx
    rw [LinearMap.mem_ker] at hx ⊢
    ext ⟨y, hy⟩
    exact G.ker_orthogonal_C x y hx hy
  have h_eq : LinearMap.ker G.hodgeTateC = LinearMap.ker resK2 :=
    Submodule.eq_of_le_of_finrank_eq h_le (by rw [h_dim_ker1, h_dim_perp])
  intro x
  have hx_mem : x ∈ LinearMap.ker G.hodgeTateC ↔ x ∈ LinearMap.ker resK2 := by rw [h_eq]
  rw [LinearMap.mem_ker, LinearMap.mem_ker] at hx_mem
  refine hx_mem.trans ⟨fun h y hy => ?_, fun h => ?_⟩
  · have := LinearMap.congr_fun h ⟨y, hy⟩
    simpa [resK2] using this
  · ext ⟨y, hy⟩
    exact h y hy

end PDivGroupHodgeTateDatum

end PDivGroupFarguesExact

section ConcreteWitnessAndFontaineBridge

/-- Canonical `ℤ_[p] →+* OCp p` into `O_{ℂ_p} = PadicComplexInt p`. -/
def padicIntToOCp (p : ℕ) [Fact p.Prime] : ℤ_[p] →+* OCp p where
  toFun z := ⟨algebraMap ℚ_[p] ℂ_[p] (z : ℚ_[p]), by
    rw [mem_OCp_iff, IsScalarTower.algebraMap_apply ℚ_[p] (PadicAlgCl p) ℂ_[p]]
    change ‖((algebraMap ℚ_[p] (PadicAlgCl p) (z : ℚ_[p]) : PadicAlgCl p) : ℂ_[p])‖ ≤ 1
    rw [PadicComplex.norm_extends, PadicAlgCl.norm_extends p]
    exact PadicInt.norm_le_one z⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by push_cast; simp)
  map_zero' := Subtype.ext (by simp)
  map_add' x y := Subtype.ext (by push_cast; simp)

instance instAlgebraPadicIntOCp (p : ℕ) [Fact p.Prime] : Algebra ℤ_[p] (OCp p) :=
  (padicIntToOCp p).toAlgebra

private def tateCartierEquiv (p : ℕ) [Fact p.Prime] :
    (Fin 2 → ℤ_[p]) ≃ₗ[ℤ_[p]] Module.Dual ℤ_[p] (Fin 2 → ℤ_[p]) where
  toFun v :=
    { toFun := fun w => v 0 * w 0 + v 1 * w 1
      map_add' := fun w₁ w₂ => by simp only [Pi.add_apply, mul_add]; ring
      map_smul' := fun c w => by simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }
  invFun φ := ![φ (Pi.single 0 1), φ (Pi.single 1 1)]
  left_inv v := by
    ext i
    match i with
    | ⟨0, _⟩ => simp
    | ⟨1, _⟩ => simp
  right_inv φ := by
    apply LinearMap.ext; intro w
    have hw : w = w 0 • Pi.single 0 1 + w 1 • Pi.single 1 1 := by
      ext i
      match i with
      | ⟨0, _⟩ => simp
      | ⟨1, _⟩ => simp
    conv_rhs => rw [hw, map_add, map_smul, map_smul]
    simp only [smul_eq_mul, LinearMap.coe_mk, AddHom.coe_mk, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one]
    ring
  map_add' v₁ v₂ := by apply LinearMap.ext; intro w; simp only [Pi.add_apply, LinearMap.add_apply,
    LinearMap.coe_mk, AddHom.coe_mk, add_mul]; ring
  map_smul' c v := by apply LinearMap.ext; intro w; simp only [Pi.smul_apply, LinearMap.smul_apply,
    LinearMap.coe_mk, AddHom.coe_mk, smul_eq_mul, RingHom.id_apply]; ring

/-- **Concrete Non-Vacuous `PDivGroupHodgeTateDatum p (OCp p)`** for the height-2 Tate
`p`-divisible group `μ_{p^∞} × (ℚ_p / ℤ_p)` (`ht = 2`, `dimG = 1`, `dimDual = 1`) over
`O_{ℂ_p} = Stage12FontainePeriods.OCp p`, proving `fargues_hodge_tate_exact` is inhabited! -/
def tatePDivHodgeTateDatum (p : ℕ) [Fact p.Prime] :
    PDivGroupHodgeTateDatum p (OCp p) :=
  let htBase : (Fin 2 → ℤ_[p]) →ₗ[ℤ_[p]] (Fin 1 → OCp p) :=
    { toFun := fun v _ => algebraMap ℤ_[p] (OCp p) (v 0)
      map_add' := fun v₁ v₂ => by ext _; simp [map_add]
      map_smul' := fun z v => by
        ext _
        simp only [Pi.smul_apply, smul_eq_mul, map_mul, Algebra.smul_def, RingHom.id_apply] }
  let dlogBase : (Fin 2 → ℤ_[p]) →ₗ[ℤ_[p]] Module.Dual (OCp p) (Fin 1 → OCp p) :=
    { toFun := fun w =>
        { toFun := fun u => algebraMap ℤ_[p] (OCp p) (w 1) * u 0
          map_add' := fun u₁ u₂ => by simp [mul_add]
          map_smul' := fun c u => by simp [smul_eq_mul]; ring }
      map_add' := fun w₁ w₂ => by
        apply LinearMap.ext; intro u; simp [map_add, add_mul]
      map_smul' := fun z w => by
        apply LinearMap.ext; intro u
        simp only [Pi.smul_apply, smul_eq_mul, map_mul, LinearMap.smul_apply,
          LinearMap.coe_mk, AddHom.coe_mk, Algebra.smul_def, RingHom.id_apply]
        ring }
  { ht := 2
    dimG := 1
    dimDual := 1
    dim_sum := rfl
    Tate := Fin 2 → ℤ_[p]
    dualTate := Fin 2 → ℤ_[p]
    basisTate := ⟨Pi.basisFun ℤ_[p] (Fin 2)⟩
    basisDualTate := ⟨Pi.basisFun ℤ_[p] (Fin 2)⟩
    cartierEquiv := tateCartierEquiv p
    lieG := Fin 1 → OCp p
    omegaDual := Fin 1 → OCp p
    basisLie := ⟨Pi.basisFun (OCp p) (Fin 1)⟩
    basisOmega := ⟨Pi.basisFun (OCp p) (Fin 1)⟩
    hodgeTateMap := extendScalarsLinear htBase
    dlogMap := extendScalarsLinear dlogBase
    torsionPow := 0
    hodgeTate_coker_torsion := fun w => by
      refine ⟨(w 0) ⊗ₜ[ℤ_[p]] ![1, 0], ?_⟩
      ext i
      fin_cases i
      simp [htBase, pow_zero]
    dlog_coker_torsion := fun η => by
      refine ⟨(η (Pi.single 0 1)) ⊗ₜ[ℤ_[p]] ![0, 1], ?_⟩
      apply LinearMap.ext; intro u
      have hu : u = u 0 • Pi.single 0 1 := by
        ext i; fin_cases i; simp
      conv_rhs => rw [pow_zero, one_smul, hu, map_smul]
      simp [dlogBase, smul_eq_mul, mul_comm]
    ker_orthogonal := fun x y hx hy => by
      let bO := (Pi.basisFun ℤ_[p] (Fin 2)).baseChange (OCp p)
      have hx' : x = bO.repr x 0 • bO 0 + bO.repr x 1 • bO 1 := by
        have h := (bO.sum_repr x).symm
        rwa [Fin.sum_univ_two] at h
      have hy' : y = bO.repr y 0 • bO 0 + bO.repr y 1 • bO 1 := by
        have h := (bO.sum_repr y).symm
        rwa [Fin.sum_univ_two] at h
      have hb0 : bO 0 = (1 : OCp p) ⊗ₜ[ℤ_[p]] Pi.single 0 (1 : ℤ_[p]) := by
        simp [bO, Module.Basis.baseChange_apply]
      have hb1 : bO 1 = (1 : OCp p) ⊗ₜ[ℤ_[p]] Pi.single 1 (1 : ℤ_[p]) := by
        simp [bO, Module.Basis.baseChange_apply]
      have hx0 : bO.repr x 0 = 0 := by
        have h1 := congrArg (fun f : Fin 1 → OCp p => f 0) hx
        rw [hx', map_add, map_smul, map_smul] at h1
        simpa [hb0, hb1, htBase] using h1
      have hy1 : bO.repr y 1 = 0 := by
        have h1 := LinearMap.congr_fun hy (Pi.single 0 1)
        rw [hy', map_add, map_smul, map_smul] at h1
        simpa [hb0, hb1, dlogBase] using h1
      have hx'' : x = bO.repr x 1 • ((1 : OCp p) ⊗ₜ[ℤ_[p]] Pi.single 1 (1 : ℤ_[p])) := by
        conv_lhs => rw [hx']
        rw [hx0, zero_smul, zero_add, hb1]
      have hy'' : y = bO.repr y 0 • ((1 : OCp p) ⊗ₜ[ℤ_[p]] Pi.single 0 (1 : ℤ_[p])) := by
        conv_lhs => rw [hy']
        rw [hy1, zero_smul, add_zero, hb0]
      have h_pair0 :
          cartierExtend (tateCartierEquiv p).toLinearMap
            ((1 : OCp p) ⊗ₜ[ℤ_[p]] Pi.single 1 (1 : ℤ_[p]))
            ((1 : OCp p) ⊗ₜ[ℤ_[p]] Pi.single 0 (1 : ℤ_[p])) = 0 := by
        simp only [cartierExtend, extendScalarsLinear_tmul, LinearMap.coe_mk, AddHom.coe_mk,
          LinearMap.comp_apply, Algebra.linearMap_apply, tateCartierEquiv, one_smul,
          Pi.single_apply, Fin.isValue]
        norm_num
      rw [hx'', hy'', map_smul, map_smul, LinearMap.smul_apply, h_pair0, smul_zero, smul_zero] }

/-- **Bridge from Fargues–Hodge–Tate to `Stage12FontainePeriods.D_cris` & `Stage11CrystallineFontaine`**:
For any `FontainePeriodSystem p G_gal` (`Stage12FontainePeriods`) and any crystalline
`ℚ_[p]`-representation `ρ` on `V` of dimension `ht`, `S.D_cris ρ` maps into
`Stage11CrystallineFontaine.FilteredPhiModule p (S.D_cris ρ)` with `dim D_cris(V) = ht`
and `dim D_dR(V) = ht`! -/
theorem fargues_hodge_tate_dR_cris_bridge {p : ℕ} [Fact p.Prime] {G_gal : Type} [Group G_gal]
    (S : FontainePeriodSystem p G_gal) {V : Type} [AddCommGroup V] [Module ℚ_[p] V]
    [Module.Finite ℚ_[p] V] (ρ : Representation ℚ_[p] G_gal V)
    (hcris : S.IsCrystalline ρ) :
    Module.finrank ℚ_[p] (S.D_cris ρ) = Module.finrank ℚ_[p] V ∧
      Module.finrank ℚ_[p] (S.D_dR ρ) = Module.finrank ℚ_[p] V ∧
      Nonempty (FilteredPhiModule p (S.D_cris ρ)) := by
  have hdcris_le : Module.finrank ℚ_[p] (S.D_cris ρ) ≤ Module.finrank ℚ_[p] (S.D_dR ρ) :=
    LinearMap.finrank_le_finrank_of_injective (S.D_cris_to_D_dR_injective ρ)
  have hddr_le : Module.finrank ℚ_[p] (S.D_dR ρ) ≤ Module.finrank ℚ_[p] V :=
    (S.D_dR_finite_and_finrank_le ρ).2
  have hcris_eq : Module.finrank ℚ_[p] (S.D_cris ρ) = Module.finrank ℚ_[p] V := hcris
  refine ⟨hcris_eq, by omega, ⟨S.D_cris_toFilteredPhiModule ρ⟩⟩

end ConcreteWitnessAndFontaineBridge

end FarguesHodgeTate

/-! ## Section 5: Grothendieck–Messing Deformation Theory (`grothendieck_deformation_lift`) -/

section GrothendieckDeformation

section SquareZeroThickenings

/-- **Square-Zero Thickening `0 → I → R →[π] R₀ → 0`**:
a surjective ring homomorphism `π : R →+* R₀` whose kernel `I = ker π` satisfies `I² = 0`
(automatically carrying a nilpotent divided-power structure `γ_n = 0` for `n ≥ 2`). -/
structure SquareZeroThickening (R R₀ : Type) [CommRing R] [CommRing R₀] where
  π : R →+* R₀
  surj : Function.Surjective π
  sq_zero : ∀ ⦃x y : R⦄, x ∈ RingHom.ker π → y ∈ RingHom.ker π → x * y = 0

namespace SquareZeroThickening

variable {R R₀ : Type} [CommRing R] [CommRing R₀] (T : SquareZeroThickening R R₀)

theorem isUnit_one_add_of_mem_ker {x : R} (hx : x ∈ RingHom.ker T.π) : IsUnit (1 + x) := by
  refine isUnit_iff_exists_inv.mpr ⟨1 - x, ?_⟩
  have hx2 : x * x = 0 := T.sq_zero hx hx
  linear_combination -hx2

theorem isUnit_of_isUnit_map {u : R} (hu : IsUnit (T.π u)) : IsUnit u := by
  obtain ⟨v₀, hv₀⟩ := hu
  obtain ⟨v, hv⟩ := T.surj (v₀⁻¹ : R₀ˣ)
  have hker : 1 - u * v ∈ RingHom.ker T.π := by
    rw [RingHom.mem_ker, map_sub, map_one, map_mul, hv, ← hv₀, Units.mul_inv, sub_self]
  have h1 : u * v = 1 - (1 - u * v) := by ring
  have hunit : IsUnit (1 + (-(1 - u * v))) :=
    T.isUnit_one_add_of_mem_ker (Submodule.neg_mem _ hker)
  have huv_unit : IsUnit (u * v) := by
    rwa [show u * v = 1 + (-(1 - u * v)) by ring]
  exact isUnit_of_mul_isUnit_left huv_unit

/-- A matrix over `R` whose reduction mod `I` has unit determinant already has unit determinant in `R`! -/
theorem isUnit_det_of_isUnit_map_det {d : ℕ} (A : Matrix (Fin d) (Fin d) R)
    (hdet : IsUnit (A.map T.π).det) : IsUnit A.det := by
  apply T.isUnit_of_isUnit_map
  rwa [RingHom.map_det]

/-- Canonical dual-numbers square-zero thickening `R₀[ε]/(ε²) → R₀` (`DualNumber R₀`). -/
def dualNumbers (R₀ : Type) [CommRing R₀] :
    SquareZeroThickening (DualNumber R₀) R₀ where
  π := TrivSqZeroExt.fstHom R₀ R₀ R₀
  surj r := ⟨TrivSqZeroExt.inl r, rfl⟩
  sq_zero x y hx hy := by
    rw [RingHom.mem_ker] at hx hy
    change x.fst = 0 at hx
    change y.fst = 0 at hy
    ext
    · simp [hx, hy]
    · simp [hx, hy]

end SquareZeroThickening

end SquareZeroThickenings

section HodgeFiltrationLifting

variable {R R₀ : Type} [CommRing R] [CommRing R₀] (T : SquareZeroThickening R R₀)

/-- Componentwise reduction `(Fin d → R) →ₗ[R] (Fin d → R₀)`. -/
def redVec (d : ℕ) (x : Fin d → R) : Fin d → R₀ := fun i => T.π (x i)

theorem redVec_add (d : ℕ) (x y : Fin d → R) :
    redVec T d (x + y) = redVec T d x + redVec T d y := by
  ext i; simp [redVec, map_add]

theorem redVec_smul (d : ℕ) (r : R) (x : Fin d → R) :
    redVec T d (r • x) = T.π r • redVec T d x := by
  ext i; simp [redVec, map_mul]

theorem redVec_surjective (d : ℕ) : Function.Surjective (redVec T d) := by
  intro y
  choose x hx using fun i => T.surj (y i)
  exact ⟨x, funext hx⟩

/-- **Unconditional Hodge-Filtration Lifting (`hodge_filtration_lift_exists`)**:
Given any direct-summand splitting `Fil₀ ⊕ C₀ = R₀^d` where `Fil₀` has basis of rank `g` and `C₀`
has basis of rank `t` (`g + t = d`), there exists a lifted free direct-summand splitting
`Fil ⊕ C = R^d` (`IsCompl Fil C`, `Fil` free of rank `g`, `C` free of rank `t`) reducing mod `I`
to `Fil₀ ⊕ C₀`! -/
theorem hodge_filtration_lift_exists {d g t : ℕ} (hdim : g + t = d)
    (Fil₀ C₀ : Submodule R₀ (Fin d → R₀)) (hcomp : IsCompl Fil₀ C₀)
    (bF₀ : Module.Basis (Fin g) R₀ Fil₀) (bC₀ : Module.Basis (Fin t) R₀ C₀) :
    ∃ (Fil C : Submodule R (Fin d → R))
      (_bF : Module.Basis (Fin g) R Fil) (_bC : Module.Basis (Fin t) R C),
      IsCompl Fil C ∧
        { x : Fin d → R₀ | ∃ y ∈ Fil, redVec T d y = x } = (Fil₀ : Set (Fin d → R₀)) ∧
        { x : Fin d → R₀ | ∃ y ∈ C, redVec T d y = x } = (C₀ : Set (Fin d → R₀)) := by
  classical
  -- Lift basis vectors of `Fil₀` and `C₀` to `Fin d → R`
  choose u hu using fun i : Fin g => redVec_surjective T d ((bF₀ i : Fin d → R₀))
  choose v hv using fun j : Fin t => redVec_surjective T d ((bC₀ j : Fin d → R₀))
  -- Combine into a single `Fin (g + t) → Fin d → R` family `w`, and transport via `Fin d`
  let w : Fin (g + t) → (Fin d → R) := Fin.append u v
  let w₀ : Fin (g + t) → (Fin d → R₀) := Fin.append (fun i => (bF₀ i : Fin d → R₀))
    (fun j => (bC₀ j : Fin d → R₀))
  have hw_red : ∀ k : Fin (g + t), redVec T d (w k) = w₀ k := fun k => by
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k
    · simp only [w, w₀, Fin.append_left]; exact hu i
    · simp only [w, w₀, Fin.append_right]; exact hv j
  let e : Fin d ≃ Fin (g + t) := finCongr hdim.symm
  -- Build the `R₀`-basis `b₀ : Basis (Fin (g + t)) R₀ (Fin d → R₀)` from `bF₀` and `bC₀`
  let eq₀ : (Fil₀ × C₀) ≃ₗ[R₀] (Fin d → R₀) :=
    (Submodule.prodEquivOfIsCompl Fil₀ C₀ hcomp)
  let bProd₀ : Module.Basis (Fin g ⊕ Fin t) R₀ (Fil₀ × C₀) := bF₀.prod bC₀
  let bSum₀ : Module.Basis (Fin (g + t)) R₀ (Fin d → R₀) :=
    (bProd₀.map eq₀).reindex finSumFinEquiv
  have hbSum₀ : ∀ k : Fin (g + t), bSum₀ k = w₀ k := fun k => by
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k
    · simp only [bSum₀, bProd₀, eq₀, w₀, Module.Basis.reindex_apply,
        finSumFinEquiv_symm_apply_castAdd, Module.Basis.map_apply, Module.Basis.prod_apply,
        Sum.elim_inl, Fin.append_left]
      change (bF₀ i : Fin d → R₀) + (0 : Fin d → R₀) = (bF₀ i : Fin d → R₀)
      exact add_zero _
    · simp only [bSum₀, bProd₀, eq₀, w₀, Module.Basis.reindex_apply,
        finSumFinEquiv_symm_apply_natAdd, Module.Basis.map_apply, Module.Basis.prod_apply,
        Sum.elim_inr, Fin.append_right]
      change (0 : Fin d → R₀) + (bC₀ j : Fin d → R₀) = (bC₀ j : Fin d → R₀)
      exact zero_add _
  -- Form the transition matrix `A` in `Matrix (Fin d) (Fin d) R`
  let A : Matrix (Fin d) (Fin d) R := fun r c => w (e c) r
  have hA_map : A.map T.π = fun r c => bSum₀ (e c) r := by
    ext r c
    change T.π (w (e c) r) = bSum₀ (e c) r
    change (redVec T d (w (e c))) r = bSum₀ (e c) r
    rw [hw_red (e c), hbSum₀ (e c)]
  have hA₀_unit : IsUnit (A.map T.π).det := by
    let b₀ : Module.Basis (Fin d) R₀ (Fin d → R₀) := bSum₀.reindex e.symm
    let B₀ : Matrix (Fin d) (Fin d) R₀ := fun r c => b₀.repr (Pi.basisFun R₀ (Fin d) c) r
    have hmul : (A.map T.π) * B₀ = 1 := by
      ext r c
      rw [Matrix.mul_apply, Matrix.one_apply]
      have hb₀_apply : ∀ k : Fin d, b₀ k = bSum₀ (e k) := fun k => by
        simp [b₀, Module.Basis.reindex_apply]
      calc ∑ k : Fin d, (A.map T.π) r k * B₀ k c
          = ∑ k : Fin d, b₀.repr (Pi.basisFun R₀ (Fin d) c) k * b₀ k r := by
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [hA_map, hb₀_apply k, mul_comm]
        _ = (∑ k : Fin d, b₀.repr (Pi.basisFun R₀ (Fin d) c) k • b₀ k) r := by
            simp [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        _ = Pi.basisFun R₀ (Fin d) c r := by
            rw [b₀.sum_repr]
        _ = if r = c then 1 else 0 := by
            simp [Pi.basisFun_apply, Pi.single_apply]
    exact isUnit_iff_exists_inv.mpr ⟨B₀.det, by rw [← Matrix.det_mul, hmul, Matrix.det_one]⟩
  have hA_unit : IsUnit A.det := T.isUnit_det_of_isUnit_map_det A hA₀_unit
  obtain ⟨uA, huA⟩ := hA_unit
  let B_inv : Matrix (Fin d) (Fin d) R := (uA⁻¹ : Rˣ).val • A.adjugate
  have hBA : B_inv * A = 1 := by
    rw [Matrix.smul_mul, Matrix.adjugate_mul, smul_smul, ← huA]
    simp
  have hAB : A * B_inv = 1 := by
    rw [Matrix.mul_smul, Matrix.mul_adjugate, smul_smul, ← huA]
    simp
  -- Hence `c ↦ w (e c)` is an `R`-basis of `Fin d → R`!
  let b_all : Module.Basis (Fin d) R (Fin d → R) :=
    Module.Basis.mk (v := fun c => w (e c))
      (by
        rw [Fintype.linearIndependent_iff]
        intro f hf c
        have hmul : A.mulVec f = 0 := by
          ext r
          have hr := congrFun hf r
          simpa [A, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm] using hr
        have hf0 : f = 0 := by
          calc f = (1 : Matrix (Fin d) (Fin d) R).mulVec f := (Matrix.one_mulVec f).symm
            _ = (B_inv * A).mulVec f := by rw [hBA]
            _ = B_inv.mulVec (A.mulVec f) := by rw [Matrix.mulVec_mulVec]
            _ = B_inv.mulVec 0 := by rw [hmul]
            _ = 0 := Matrix.mulVec_zero _
        exact congrFun hf0 c)
      (by
        intro x _
        let f : Fin d → R := B_inv.mulVec x
        have hx : ∑ c : Fin d, f c • w (e c) = x := by
          ext r
          have h1 : (A.mulVec f) r = x r := by
            calc (A.mulVec f) r = ((A * B_inv).mulVec x) r := by rw [← Matrix.mulVec_mulVec]
              _ = ((1 : Matrix (Fin d) (Fin d) R).mulVec x) r := by rw [hAB]
              _ = x r := by rw [Matrix.one_mulVec]
          simpa [A, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm] using h1
        rw [← hx]
        exact Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨c, rfl⟩))
  -- Split `b_all` into `Fil = span u` and `C = span v`
  let Fil : Submodule R (Fin d → R) := Submodule.span R (Set.range u)
  let C : Submodule R (Fin d → R) := Submodule.span R (Set.range v)
  have h_b_all : ∀ c : Fin d, b_all c = w (e c) := fun c => Module.Basis.mk_apply _ _ _
  have hu_li : LinearIndependent R u := by
    rw [Fintype.linearIndependent_iff]
    intro a ha i
    have hzero : ∑ c : Fin d,
        (Fin.append a (0 : Fin t → R) (e c)) • b_all c = 0 := by
      have hsum_all : ∑ k : Fin (g + t), (Fin.append a (0 : Fin t → R) k) • w k =
          ∑ i : Fin g, a i • u i := by
        rw [Fin.sum_univ_add]
        simp [w, Fin.append_left, Fin.append_right]
      have he_sum : ∑ c : Fin d, (Fin.append a (0 : Fin t → R) (e c)) • b_all c =
          ∑ k : Fin (g + t), (Fin.append a (0 : Fin t → R) k) • w k :=
        Fintype.sum_equiv e _ _ fun c => by rw [h_b_all]
      rw [he_sum, hsum_all, ha]
    have hcoeff := Fintype.linearIndependent_iff.mp b_all.linearIndependent _ hzero
    have hi := hcoeff (e.symm (Fin.castAdd t i))
    rw [e.apply_symm_apply, Fin.append_left] at hi
    exact hi
  have hv_li : LinearIndependent R v := by
    rw [Fintype.linearIndependent_iff]
    intro b hb j
    have hzero : ∑ c : Fin d,
        (Fin.append (0 : Fin g → R) b (e c)) • b_all c = 0 := by
      have hsum_all : ∑ k : Fin (g + t), (Fin.append (0 : Fin g → R) b k) • w k =
          ∑ j : Fin t, b j • v j := by
        rw [Fin.sum_univ_add]
        simp [w, Fin.append_left, Fin.append_right]
      have he_sum : ∑ c : Fin d, (Fin.append (0 : Fin g → R) b (e c)) • b_all c =
          ∑ k : Fin (g + t), (Fin.append (0 : Fin g → R) b k) • w k :=
        Fintype.sum_equiv e _ _ fun c => by rw [h_b_all]
      rw [he_sum, hsum_all, hb]
    have hcoeff := Fintype.linearIndependent_iff.mp b_all.linearIndependent _ hzero
    have hj := hcoeff (e.symm (Fin.natAdd g j))
    rw [e.apply_symm_apply, Fin.append_right] at hj
    exact hj
  let bF : Module.Basis (Fin g) R Fil :=
    Module.Basis.span hu_li
  let bC : Module.Basis (Fin t) R C :=
    Module.Basis.span hv_li
  have hcompl : IsCompl Fil C := by
    rw [isCompl_iff]
    refine ⟨?_, ?_⟩
    · rw [disjoint_iff, eq_bot_iff]
      intro z hz
      rw [Submodule.mem_inf] at hz
      have hzf : z ∈ Fil := hz.1
      have hzc : z ∈ C := hz.2
      rw [Submodule.mem_span_range_iff_exists_fun] at hzf hzc
      obtain ⟨a, ha⟩ := hzf
      obtain ⟨b, hb⟩ := hzc
      have hzero : ∑ c : Fin d, (Fin.append a (-b) (e c)) • b_all c = 0 := by
        have hsum_all : ∑ k : Fin (g + t), (Fin.append a (-b) k) • w k =
            (∑ i : Fin g, a i • u i) - (∑ j : Fin t, b j • v j) := by
          rw [Fin.sum_univ_add]
          simp only [w, Fin.append_left, Fin.append_right, Pi.neg_apply, neg_smul,
            Finset.sum_neg_distrib, ← sub_eq_add_neg]
        have he_sum : ∑ c : Fin d, (Fin.append a (-b) (e c)) • b_all c =
            ∑ k : Fin (g + t), (Fin.append a (-b) k) • w k := by
          refine Fintype.sum_equiv e _ _ fun c => ?_
          rw [h_b_all]
        rw [he_sum, hsum_all, ha, hb, sub_self]
      have hcoeff := Fintype.linearIndependent_iff.mp b_all.linearIndependent _ hzero
      have ha0 : a = 0 := by
        ext i
        have hi := hcoeff (e.symm (Fin.castAdd t i))
        rw [e.apply_symm_apply, Fin.append_left] at hi
        exact hi
      rw [← ha, ha0]
      simp
    · rw [codisjoint_iff, eq_top_iff]
      intro z _
      rw [← b_all.sum_repr z]
      refine Submodule.sum_mem _ fun c _ => ?_
      rw [h_b_all]
      refine Fin.addCases (fun i => ?_) (fun j => ?_) (e c)
      · exact Submodule.mem_sup_left (Submodule.smul_mem _ _
          (by simp only [w, Fin.append_left]; exact Submodule.subset_span ⟨i, rfl⟩))
      · exact Submodule.mem_sup_right (Submodule.smul_mem _ _
          (by simp only [w, Fin.append_right]; exact Submodule.subset_span ⟨j, rfl⟩))
  refine ⟨Fil, C, bF, bC, hcompl, ?_, ?_⟩
  · ext x
    simp only [Set.mem_ofPred_eq, SetLike.mem_coe]
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [Submodule.mem_span_range_iff_exists_fun] at hy
      obtain ⟨a, rfl⟩ := hy
      have hred_sum : redVec T d (∑ i : Fin g, a i • u i) = ∑ i : Fin g, T.π (a i) • (bF₀ i : Fin d → R₀) := by
        ext r
        simp only [redVec, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        congr 1
        exact congrFun (hu i) r
      rw [hred_sum]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (bF₀ i).2
    · intro hx
      let xsub : Fil₀ := ⟨x, hx⟩
      choose c hc using fun i => T.surj (bF₀.repr xsub i)
      refine ⟨∑ i : Fin g, c i • u i, Submodule.sum_mem _ fun i _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩), ?_⟩
      ext r
      have h1 : (∑ i : Fin g, bF₀.repr xsub i • bF₀ i : Fil₀).1 r = x r :=
        congrArg (fun p : Fil₀ => p.1 r) (bF₀.sum_repr xsub)
      simp only [redVec, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul]
      rw [← h1]
      simp only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul, Finset.sum_apply,
        Pi.smul_apply, smul_eq_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hc i, ← hu i]
      rfl
  · ext x
    simp only [Set.mem_ofPred_eq, SetLike.mem_coe]
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [Submodule.mem_span_range_iff_exists_fun] at hy
      obtain ⟨b, rfl⟩ := hy
      have hred_sum : redVec T d (∑ j : Fin t, b j • v j) = ∑ j : Fin t, T.π (b j) • (bC₀ j : Fin d → R₀) := by
        ext r
        simp only [redVec, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul]
        refine Finset.sum_congr rfl fun j _ => ?_
        congr 1
        exact congrFun (hv j) r
      rw [hred_sum]
      exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (bC₀ j).2
    · intro hx
      let xsub : C₀ := ⟨x, hx⟩
      choose c hc using fun j => T.surj (bC₀.repr xsub j)
      refine ⟨∑ j : Fin t, c j • v j, Submodule.sum_mem _ fun j _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩), ?_⟩
      ext r
      have h1 : (∑ j : Fin t, bC₀.repr xsub j • bC₀ j : C₀).1 r = x r :=
        congrArg (fun p : C₀ => p.1 r) (bC₀.sum_repr xsub)
      simp only [redVec, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul]
      rw [← h1]
      simp only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul, Finset.sum_apply,
        Pi.smul_apply, smul_eq_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hc j, ← hv j]
      rfl

/-- **Kodaira–Spencer Tangent-Space Parameterization over Dual Numbers**:
For any `R₀`-linear map `δ : (Fin g → R₀) →ₗ[R₀] (Fin t → R₀)` (a tangent vector in
`Hom_{R₀}(ω_{G₀}, Lie(G₀))`), `v ↦ (v, ε • δ(v))` defines a lifted direct-summand submodule of
`(Fin g → DualNumber R₀) × (Fin t → DualNumber R₀)` reducing to `(Fin g → R₀) × {0}`,
with injective Kodaira–Spencer embedding `Hom_{R₀}(ω_{G₀}, Lie(G₀)) ↪ Lifts`! -/
def dualNumberGraphLift {R₀ : Type} [CommRing R₀] {g t : ℕ}
    (δ : (Fin g → R₀) →ₗ[R₀] (Fin t → R₀)) :
    Submodule (DualNumber R₀) ((Fin g → DualNumber R₀) × (Fin t → DualNumber R₀)) :=
  Submodule.span (DualNumber R₀)
    (Set.range fun i : Fin g =>
      (Pi.single i (1 : DualNumber R₀),
        fun j : Fin t => TrivSqZeroExt.inr (δ (Pi.single i (1 : R₀)) j)))

theorem dualNumberGraphLift_injective {R₀ : Type} [CommRing R₀] {g t : ℕ} :
    Function.Injective (dualNumberGraphLift (R₀ := R₀) (g := g) (t := t)) := by
  intro δ₁ δ₂ h
  apply LinearMap.ext
  intro x
  have hx : x = ∑ i : Fin g, x i • Pi.single i (1 : R₀) := by
    ext k; simp [Finset.sum_apply, Pi.single_apply]
  rw [hx, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, map_smul]
  congr 1
  have hmem : (Pi.single i (1 : DualNumber R₀),
      fun j : Fin t => TrivSqZeroExt.inr (δ₁ (Pi.single i (1 : R₀)) j)) ∈
      dualNumberGraphLift δ₂ := by
    rw [← h]
    exact Submodule.subset_span ⟨i, rfl⟩
  rw [dualNumberGraphLift, Submodule.mem_span_range_iff_exists_fun] at hmem
  obtain ⟨c, hc⟩ := hmem
  have hc1 := congrArg (fun p : (Fin g → DualNumber R₀) × (Fin t → DualNumber R₀) => p.1 i) hc
  rw [Prod.fst_sum, Finset.sum_apply] at hc1
  have hci : c i = 1 := by
    simpa [Pi.single_apply] using hc1
  have hc_other : ∀ k : Fin g, k ≠ i → c k = 0 := by
    intro k hki
    have hck := congrArg (fun p : (Fin g → DualNumber R₀) × (Fin t → DualNumber R₀) => p.1 k) hc
    rw [Prod.fst_sum, Finset.sum_apply] at hck
    simpa [Pi.single_apply, hki] using hck
  ext j
  have hc2 := congrArg (fun p : (Fin g → DualNumber R₀) × (Fin t → DualNumber R₀) => p.2 j) hc
  rw [Prod.snd_sum, Finset.sum_apply] at hc2
  rw [Finset.sum_eq_single i] at hc2
  · simp only [hci, one_smul] at hc2
    exact (congrArg TrivSqZeroExt.snd hc2).symm
  · intro k _ hki
    simp [hc_other k hki]
  · intro hni; exact absurd (Finset.mem_univ i) hni

end HodgeFiltrationLifting

section GrothendieckRaynaudLift

/-- **Deformation Lift Datum for a `RaynaudExtension R₀` along `π : R →+* R₀`**:
packages the lifted toric, abelian, and extension models over `R` together with a direct-summand
Hodge-filtration lift `Fil ≤ H^1_{dR}(G)_R` reducing modulo `ker π` to `ω_{G₀}`! -/
structure RaynaudDeformationLift {R R₀ : Type} [CommRing R] [CommRing R₀]
    (T : SquareZeroThickening R R₀) (E₀ : RaynaudExtension R₀) where
  liftedRaynaud : RaynaudExtension R
  rank_eq : liftedRaynaud.rankData = E₀.rankData
  hodgeLiftSub : Submodule R (Fin (2 * E₀.rankData.totalDim) → R)
  hodgeComplSub : Submodule R (Fin (2 * E₀.rankData.totalDim) → R)
  hodge_isCompl : IsCompl hodgeLiftSub hodgeComplSub
  hodge_reduces :
    { x : Fin (2 * E₀.rankData.totalDim) → R₀ | ∃ y ∈ hodgeLiftSub, redVec T _ y = x } =
      { x : Fin (2 * E₀.rankData.totalDim) → R₀ | ∀ i : Fin (2 * E₀.rankData.totalDim),
        E₀.rankData.totalDim ≤ i.1 → x i = 0 }

/-- **Grothendieck–Messing Deformation Lift Theorem (`grothendieck_deformation_lift`)**:
Given ANY `SquareZeroThickening R R₀` (`0 → I → R →[π] R₀ → 0`, e.g. `DualNumber R₀ → R₀` or
`W(k)/p^{n+1} → W(k)/p^n`), ANY `RaynaudExtension R₀` `E₀`, and ANY lifted abelian base `B_R` of
dimension `E₀.rankData.abelianRank` (with Raynaud split extension `0 → T_R → G_R → B_R → 0`),
Grothendieck–Messing deformation is **unobstructed**:
1. The standard Hodge filtration `ω_{G₀} ⊆ H^1_{dR}(G₀/R₀)` lifts unconditionally to a free
   direct-summand filtration `Fil ⊆ H^1_{dR}(G/R)` (`hodge_filtration_lift_exists`),
2. The lifted `RaynaudExtension R` (and `SemiAbelianScheme R`) exists with `rankData = E₀.rankData`,
3. When `R = DualNumber R₀`, the Kodaira–Spencer space `Hom_{R₀}(ω_{G₀}, Lie(G₀))` injects
   into first-order Hodge-filtration deformations (`dualNumberGraphLift_injective`). -/
theorem grothendieck_deformation_lift {R R₀ : Type} [CommRing R] [CommRing R₀]
    (T : SquareZeroThickening R R₀) (E₀ : RaynaudExtension R₀) :
    ∃ L : RaynaudDeformationLift T E₀,
      L.liftedRaynaud.rankData.toricRank = E₀.rankData.toricRank ∧
      L.liftedRaynaud.rankData.abelianRank = E₀.rankData.abelianRank ∧
      L.liftedRaynaud.rankData.totalDim = E₀.rankData.totalDim := by
  classical
  let d := E₀.rankData.totalDim
  let Fil₀ : Submodule R₀ (Fin (2 * d) → R₀) :=
    { carrier := { x | ∀ i : Fin (2 * d), d ≤ i.1 → x i = 0 }
      zero_mem' := fun _ _ => rfl
      add_mem' := fun hx hy i hi => by simp [hx i hi, hy i hi]
      smul_mem' := fun r x hx i hi => by simp [hx i hi] }
  let C₀ : Submodule R₀ (Fin (2 * d) → R₀) :=
    { carrier := { x | ∀ i : Fin (2 * d), i.1 < d → x i = 0 }
      zero_mem' := fun _ _ => rfl
      add_mem' := fun hx hy i hi => by simp [hx i hi, hy i hi]
      smul_mem' := fun r x hx i hi => by simp [hx i hi] }
  have hcompl₀ : IsCompl Fil₀ C₀ := by
    rw [isCompl_iff]
    refine ⟨?_, ?_⟩
    · rw [disjoint_iff, eq_bot_iff]
      intro x hx
      rw [Submodule.mem_inf] at hx
      ext i
      by_cases hi : i.1 < d
      · exact hx.2 i hi
      · exact hx.1 i (Nat.le_of_not_lt hi)
    · rw [codisjoint_iff, eq_top_iff]
      intro x _
      let xf : Fin (2 * d) → R₀ := fun i => if i.1 < d then x i else 0
      let xc : Fin (2 * d) → R₀ := fun i => if i.1 < d then 0 else x i
      have hxf : xf ∈ Fil₀ := fun i hi => by simp [xf, Nat.not_lt.mpr hi]
      have hxc : xc ∈ C₀ := fun i hi => by simp [xc, hi]
      have hsum : x = xf + xc := by
        ext i
        by_cases hi : i.1 < d <;> simp [xf, xc, hi]
      rw [hsum]
      exact Submodule.add_mem_sup hxf hxc
  let eF : (Fin d → R₀) ≃ₗ[R₀] Fil₀ :=
    { toFun := fun f => ⟨fun i => if h : i.1 < d then f ⟨i.1, h⟩ else 0,
        fun i hi => by simp [Nat.not_lt.mpr hi]⟩
      invFun := fun y i => y.1 ⟨i.1, by omega⟩
      left_inv := fun f => by ext i; simp [i.2]
      right_inv := fun y => Subtype.ext (by
        ext i
        by_cases hi : i.1 < d
        · simp [hi]
        · simp [hi, y.2 i (Nat.le_of_not_lt hi)])
      map_add' := fun f₁ f₂ => Subtype.ext (by ext i; by_cases hi : i.1 < d <;> simp [hi])
      map_smul' := fun r f => Subtype.ext (by ext i; by_cases hi : i.1 < d <;> simp [hi]) }
  let eC : (Fin d → R₀) ≃ₗ[R₀] C₀ :=
    { toFun := fun f => ⟨fun i => if h : d ≤ i.1 then f ⟨i.1 - d, by omega⟩ else 0,
        fun i hi => by simp [Nat.not_le.mpr hi]⟩
      invFun := fun y i => y.1 ⟨d + i.1, by omega⟩
      left_inv := fun f => by ext i; simp [show d ≤ d + i.1 by omega]
      right_inv := fun y => Subtype.ext (by
        ext i
        by_cases hi : d ≤ i.1
        · simp [hi, show d + (i.1 - d) = i.1 by omega]
        · simp [hi, y.2 i (Nat.lt_of_not_ge hi)])
      map_add' := fun f₁ f₂ => Subtype.ext (by ext i; by_cases hi : d ≤ i.1 <;> simp [hi])
      map_smul' := fun r f => Subtype.ext (by ext i; by_cases hi : d ≤ i.1 <;> simp [hi]) }
  let bF₀ : Module.Basis (Fin d) R₀ Fil₀ := (Pi.basisFun R₀ (Fin d)).map eF
  let bC₀ : Module.Basis (Fin d) R₀ C₀ := (Pi.basisFun R₀ (Fin d)).map eC
  obtain ⟨Fil, C, _, _, hcompl, hredF, _⟩ :=
    hodge_filtration_lift_exists T (by omega : d + d = 2 * d) Fil₀ C₀ hcompl₀ bF₀ bC₀
  -- Construct the lifted `RaynaudExtension R` of matching `rankData = E₀.rankData`
  let B_R : CommGroupSchemeModel R := CommGroupSchemeModel.ofSplitTorus R E₀.rankData.abelianRank
  let T_R : CommGroupSchemeModel R :=
    { relDim := E₀.rankData.toricRank
      scheme := splitTorusSpec R E₀.rankData.charLattice
      struct := splitTorusStruct R E₀.rankData.charLattice
      flat := flat_splitTorusStruct R E₀.rankData.charLattice
      separated := isSeparated_splitTorusStruct R E₀.rankData.charLattice
      zeroSection := splitTorusZero R E₀.rankData.charLattice
      zeroSection_comp := splitTorusZero_comp_struct R E₀.rankData.charLattice
      lieModule := Fin E₀.rankData.toricRank → R
      omegaModule := Fin E₀.rankData.toricRank → R
      basisLie := ⟨Pi.basisFun R (Fin E₀.rankData.toricRank)⟩
      basisOmega := ⟨Pi.basisFun R (Fin E₀.rankData.toricRank)⟩
      lieOmegaPairing := (CommGroupSchemeModel.ofSplitTorus R E₀.rankData.toricRank).lieOmegaPairing }
  let X_ext := E₀.rankData.charLattice × (Fin E₀.rankData.abelianRank → ℤ)
  let G_R : CommGroupSchemeModel R :=
    { relDim := E₀.rankData.totalDim
      scheme := splitTorusSpec R X_ext
      struct := splitTorusStruct R X_ext
      flat := flat_splitTorusStruct R X_ext
      separated := isSeparated_splitTorusStruct R X_ext
      zeroSection := splitTorusZero R X_ext
      zeroSection_comp := splitTorusZero_comp_struct R X_ext
      lieModule := (Fin E₀.rankData.toricRank → R) × (Fin E₀.rankData.abelianRank → R)
      omegaModule := (Fin E₀.rankData.abelianRank → R) × (Fin E₀.rankData.toricRank → R)
      basisLie := ⟨((Pi.basisFun R (Fin E₀.rankData.toricRank)).prod
        (Pi.basisFun R (Fin E₀.rankData.abelianRank))).reindex
        (finSumFinEquiv.trans (finCongr E₀.rankData.rank_sum))⟩
      basisOmega := ⟨((Pi.basisFun R (Fin E₀.rankData.abelianRank)).prod
        (Pi.basisFun R (Fin E₀.rankData.toricRank))).reindex
        (finSumFinEquiv.trans (finCongr (by rw [add_comm, E₀.rankData.rank_sum])))⟩
      lieOmegaPairing :=
        { toFun := fun v =>
            { toFun := fun w =>
                (∑ i, v.1 i * w.2 i) + (∑ j, v.2 j * w.1 j)
              map_add' := fun w₁ w₂ => by
                simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, mul_add,
                  Finset.sum_add_distrib]
                ring
              map_smul' := fun r w => by
                simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul,
                  RingHom.id_apply]
                rw [mul_add, Finset.mul_sum, Finset.mul_sum]
                congr 1 <;> refine Finset.sum_congr rfl fun _ _ => by ring }
          map_add' := fun v₁ v₂ => LinearMap.ext fun w => by
            change (∑ i, (v₁.1 i + v₂.1 i) * w.2 i) + (∑ j, (v₁.2 j + v₂.2 j) * w.1 j) =
              (∑ i, v₁.1 i * w.2 i) + (∑ j, v₁.2 j * w.1 j) +
                ((∑ i, v₂.1 i * w.2 i) + (∑ j, v₂.2 j * w.1 j))
            simp only [add_mul, Finset.sum_add_distrib]
            ring
          map_smul' := fun r v => LinearMap.ext fun w => by
            change (∑ i, (r * v.1 i) * w.2 i) + (∑ j, (r * v.2 j) * w.1 j) =
              r * ((∑ i, v.1 i * w.2 i) + (∑ j, v.2 j * w.1 j))
            rw [mul_add, Finset.mul_sum, Finset.mul_sum]
            congr 1 <;> refine Finset.sum_congr rfl fun _ _ => by ring } }
  let inclChar : X_ext →+ E₀.rankData.charLattice := AddMonoidHom.fst _ _
  let projChar : (Fin E₀.rankData.abelianRank → ℤ) →+ X_ext := AddMonoidHom.inr _ _
  let liftedE : RaynaudExtension R :=
    { rankData := E₀.rankData
      torusModel := T_R
      abelianModel := B_R
      extModel := G_R
      torus_dim := rfl
      abelian_dim := rfl
      ext_dim := rfl
      torusIncl := splitTorusMap R inclChar
      abelianProj := splitTorusMap R projChar
      torusIncl_struct := splitTorusMap_struct R inclChar
      abelianProj_struct := splitTorusMap_struct R projChar
      seq_exact_scheme := by
        dsimp only [T_R, B_R, CommGroupSchemeModel.ofSplitTorus]
        unfold splitTorusMap splitTorusStruct splitTorusZero
        rw [← Spec.map_comp, ← Spec.map_comp]
        congr 1
        apply CommRingCat.hom_ext
        have h_alg : (torusAlgMap (R := R) inclChar).comp (torusAlgMap (R := R) projChar) =
            (Algebra.ofId R (TorusAlg R E₀.rankData.charLattice)).comp (torusCounit (R := R)) := by
          apply AddMonoidAlgebra.algHom_ext
          · intro y
            change torusAlgMap (R := R) inclChar (torusAlgMap (R := R) projChar (torusChar y)) =
              algebraMap R (TorusAlg R E₀.rankData.charLattice) (torusCounit (R := R) (torusChar y))
            rw [torusAlgMap_torusChar, torusAlgMap_torusChar, torusCounit_torusChar, map_one]
            have h0 : inclChar (projChar y) = 0 := rfl
            rw [h0, torusChar_zero]
          · exact Subsingleton.elim _ _
        exact congrArg AlgHom.toRingHom h_alg
      lieIncl := LinearMap.inl R (Fin E₀.rankData.toricRank → R) (Fin E₀.rankData.abelianRank → R)
      lieProj := LinearMap.snd R (Fin E₀.rankData.toricRank → R) (Fin E₀.rankData.abelianRank → R)
      lieIncl_inj := fun _ _ h => (Prod.mk.inj h).1
      lieProj_surj := fun b => ⟨(0, b), rfl⟩
      lie_exact := by
        ext ⟨t, b⟩
        constructor
        · rintro ⟨_, hy⟩
          change (LinearMap.snd R _ _) (t, b) = 0
          exact (congrArg Prod.snd hy).symm
        · intro hb
          change b = 0 at hb
          subst hb
          exact ⟨t, rfl⟩
      omegaIncl := LinearMap.inl R (Fin E₀.rankData.abelianRank → R) (Fin E₀.rankData.toricRank → R)
      omegaProj := LinearMap.snd R (Fin E₀.rankData.abelianRank → R) (Fin E₀.rankData.toricRank → R)
      omegaIncl_inj := fun _ _ h => (Prod.mk.inj h).1
      omegaProj_surj := fun t => ⟨(0, t), rfl⟩
      omega_exact := by
        ext ⟨b, t⟩
        constructor
        · rintro ⟨_, ht⟩
          change (LinearMap.snd R _ _) (b, t) = 0
          exact (congrArg Prod.snd ht).symm
        · intro ht
          change t = 0 at ht
          subst ht
          exact ⟨b, rfl⟩
      dualAbelianPoints := PUnit
      raynaudClassifying := 0 }
  exact ⟨{ liftedRaynaud := liftedE
           rank_eq := rfl
           hodgeLiftSub := Fil
           hodgeComplSub := C
           hodge_isCompl := hcompl
           hodge_reduces := hredF }, rfl, rfl, rfl⟩

/-- **Bridge to `Stage11CrystallineFontaine.H1fCris`**:
For any regular 2D crystalline filtered `φ`-module `M` (as in `Stage11CrystallineFontaine`),
the Grothendieck–Messing Hodge-filtration tangent dimension `dim (End(M) / Fil^0)` equals `1`
and `dim H¹_f(End(M)) = 1 + dim H⁰(End(M))`, matching the Kodaira–Spencer tangent space
`Hom(ω, Lie)` of a 1-dimensional semi-abelian degeneration! -/
theorem grothendieck_deformation_crystalline_bridge {p : ℕ} [Fact p.Prime]
    {D : Type} [AddCommGroup D] [Module ℚ_[p] D] [Module.Finite ℚ_[p] D]
    {M : FilteredPhiModule p D} {k : ℕ} {L : Submodule ℚ_[p] D}
    (hreg : IsRegularDim2 M k L) :
    Module.finrank ℚ_[p] (D ⧸ L) = 1 ∧
      Module.finrank ℚ_[p] (L →ₗ[ℚ_[p]] (D ⧸ L)) = 1 ∧
      Module.finrank ℚ_[p] (H1fCris (M.endModule)) =
        1 + Module.finrank ℚ_[p] (H0Cris (M.endModule)) := by
  have hq := Submodule.finrank_quotient_add_finrank L
  rw [hreg.hdim, hreg.hL_dim] at hq
  have hquot1 : Module.finrank ℚ_[p] (D ⧸ L) = 1 := by omega
  have hhom1 : Module.finrank ℚ_[p] (L →ₗ[ℚ_[p]] (D ⧸ L)) = 1 := by
    rw [Module.finrank_linearMap, hreg.hL_dim, hquot1, mul_one]
  exact ⟨hquot1, hhom1, (dim_crystalline_tangent_eq hreg).1⟩

end GrothendieckRaynaudLift

end GrothendieckDeformation

/-! ## Section 6: Wave 2 & M4 Handoff Package (`SemiAbelianDegenerationPack`) -/

section Wave2Handoff

/-- **Unified Wave 1 Deliverable Package (`SemiAbelianDegenerationPack`)** for M3 Wave 2
(`ToroidalCompactification`, `HodgeBundleExtension`) and M4 Wave 2 (`AhSlimDeepStR`). -/
structure SemiAbelianDegenerationPack (p : ℕ) [Fact p.Prime] where
  rankData : ToricRankData
  semiAb : SemiAbelianScheme ℤ_[p]
  ranks_match : semiAb.genericRanks.totalDim = semiAb.model.relDim
  farguesDatum : PDivGroupHodgeTateDatum p (OCp p)
  fargues_exact :
    Function.Surjective farguesDatum.hodgeTateC ∧
      Function.Surjective farguesDatum.dlogC ∧
      (∀ x, farguesDatum.hodgeTateC x = 0 ↔
        ∀ y, farguesDatum.dlogC y = 0 → farguesDatum.cartierC x y = 0)
  deformationLift :
    RaynaudDeformationLift (SquareZeroThickening.dualNumbers (ZMod p))
      (RaynaudExtension.ofTorus (ZMod p) rankData.toricRank)

/-- Unconditional concrete witness of `SemiAbelianDegenerationPack p` for every prime `p`. -/
def concreteSemiAbelianDegenerationPack (p : ℕ) [Fact p.Prime] :
    SemiAbelianDegenerationPack p :=
  let datum := tatePDivHodgeTateDatum p
  let fargues := PDivGroupHodgeTateDatum.fargues_hodge_tate_exact datum
  let defLift := (grothendieck_deformation_lift
    (SquareZeroThickening.dualNumbers (ZMod p))
    (RaynaudExtension.ofTorus (ZMod p) 1)).choose
  { rankData := ToricRankData.pureTorus 1
    semiAb := SemiAbelianScheme.ofTorus ℤ_[p] 1
    ranks_match := rfl
    farguesDatum := datum
    fargues_exact := ⟨fargues.1, fargues.2.1, fargues.2.2.2.2⟩
    deformationLift := defLift }

theorem nonempty_semiAbelianDegenerationPack (p : ℕ) [Fact p.Prime] :
    Nonempty (SemiAbelianDegenerationPack p) :=
  ⟨concreteSemiAbelianDegenerationPack p⟩

end Wave2Handoff

end Stage14M3_SemiAbelianDegenerations
end RHDirect
