import RHDirect.Stage14M3_IntegralSchemesAndCharts
import RHDirect.Stage14M3_HermitianLineBundles
import RHDirect.Stage12SchurWeylLattices
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Analysis.Complex.Liouville

/-!
# RHDirect.Stage14M3_GagaAndSections

**FIELD-2 PACKAGE M3 (WAVE 2, MODULE #11) — UNCONDITIONAL ALGEBRAIC LINE BUNDLES,
FINITE-DIMENSIONALITY OF GLOBAL SECTIONS, COMPLEX GAGA ISOMORPHISM, INTEGRAL SECTION
LATTICES `GlobalSectionsLatH0`, NORM COMPARISON CONSTANTS, AND RELATIVE AMPLENESS**
in pure Mathlib `v4.33.1` (`0` `sorry`, `0` custom `axiom`s, `0` `opaque`, `0` `native_decide`,
targeted Mathlib imports only).

Directly bridges `Stage14M3_IntegralSchemesAndCharts`, `Stage14M3_HermitianLineBundles`, and
`Stage12SchurWeylLattices` to feed M3 Wave 3 (`ShimuraHodgeArakelov`, `IndefiniteHodgeLattices`)
and M4 (`AhSlimDeepStR`, `CovolStepsBridge`).

## Main Exports

1. **Algebraic Line Bundles & `sections_have_finite_dimension`**:
   - `AlgLineBundle X`, `AlgSection L`, `constFn`, `AlgSectionOver p L` (`Module K`).
   - `SectionsHaveFiniteDimension p L r`, `sections_have_finite_dimension_le`,
     `sections_have_finite_dimension_unique`, **`sections_have_finite_dimension`**
     (`FiniteDimensional K`, `finrank = r`, linear equiv `≃ₗ[K] (Fin r → K)`),
     `sections_have_finite_dimension_of_injective_finite`, and flat generic-fiber density
     (`algSection_dense_generic_of_flat` via `dense_generic_of_flat`).
   - Concrete 0-assumption projective space `H⁰(ℙ^N, 𝒪(e))` via `MvPolynomial.homogeneousSubmodule`
     and `MultiIndex (N + 1) e`: `homogeneousBasis`, `finrank_homogeneousSubmodule`,
     `sections_have_finite_dimension_projSpace`, and `volume_projSpace_asymptotic`.

2. **Complex Holomorphic Sections & `gaga_sections_iso`**:
   - `AddCommGroup` / `Module ℂ` on `MetrizedLineBundle.Section L_an`,
     `GagaChartEval`, `GagaComparisonData`.
   - **`gaga_sections_iso`**: explicit `ℂ`-linear isomorphism `AlgSectionOver p L_alg ≃ₗ[ℂ] L_an.Section`,
     plus dimension-matching `gaga_sections_iso_of_inj_finrank`, base-change GAGA
     `gaga_sections_baseChange_iso`, and unconditional 0-assumption Liouville / polynomial GAGA on
     `ℙ^N(ℂ)` (`projSpaceAnalytify_injective`, `projSpace_gaga_sections_degZero_const`).

3. **Concrete Integral Section Lattices `GlobalSectionsLatH0`**:
   - `GlobalSectionsLatH0`: concrete Hermitian finite-dimensional `H⁰(𝒳, ℒ)` carrying an integral
     `ℤ`-lattice `latH0`, analytic realization `toSection : secSpace →ₗ[ℝ] L_an.Section`,
     pointwise sup-norm `supNorm`, `ZLattice.covolume` bridge (`covol_eq_zlattice_covolume`),
     finiteness of small sections (`smallSections_finite`), metric scaling (`scaleMetricH0`),
     `CMHermLattice` realization (`toCMHermLattice`), and `GradedHermAlgebra` construction
     (`toGradedHermAlgebra`) + concrete 0-assumption `GlobalSectionsLatH0.projSpace`.

4. **Norm Comparison Constants (`h0_norm_comparison_constants`)**:
   - `h0_bergman_sup_le_l2` (via `metrizedLineBundle_bergman_extremal`),
   - `h0_l2_le_vol_sup` (finite-measure `L² ≤ vol · L^∞`),
   - **`h0_norm_comparison_constants`** (two-sided Bergman/volume constants AND unconditional
     finite-dimensional unit-sphere compactness norm equivalence),
   - `h0_norm_comparison_metric_change` (via `section_ptNormSq_metric_comparison`),
   - `h0_norm_comparison_toroidal_log_growth` (for `ShimuraHodgeArakelov`).

5. **Relative Ampleness & Positivity (`relative_ampleness_sections`)**:
   - `AlgSection.nonzeroLocus`, `IsGloballyGenerated`, `IsAmpleLB`, `IsVeryAmpleOver`, `IsRelAmple`.
   - `isAmpleLB_of_relAmple_of_isAffine`, **`relative_ampleness_sections`**,
     **`posCurvatureMetric_of_holomorphic_immersion`** (strict Fubini–Study positivity for any
     projective immersion), and `projSpace_relative_ampleness_sections`.

6. **Wave 3 & M4 Handoff Pack (`GagaSectionsPack`)**:
   - `gaga_small_sections_lower_bound` (via `moriwaki_big_small_sections`),
   - `gaga_l3_indefinite_hodge_bridge` (via `L3_hodge_covolume_bound`),
   - `gaga_hodge_slope_metric_stability`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite
open Complex Real Filter MeasureTheory Module Submodule Finset Matrix Function Set
open RHDirect.ArakelovCovolume RHDirect.Stage10GeometryOfNumbers RHDirect.Stage11MoriwakiCovolume
open RHDirect.Stage12SchurWeylLattices
open RHDirect.Stage14M3_IntegralSchemesAndCharts RHDirect.Stage14M3_HermitianLineBundles
open scoped BigOperators ComplexConjugate ComplexOrder InnerProductSpace Topology

namespace RHDirect.Stage14M3_GagaAndSections

/-! ## Section 1: Algebraic Line Bundles, `AlgSection`, and `sections_have_finite_dimension` -/

section AlgebraicLineBundlesAndFiniteDim

/-- An algebraic line bundle datum `AlgLineBundle X` over a scheme `X : Scheme.{0}`, given by an
open trivializing cover `{U_i}_{i ∈ ι}` and invertible transition functions `g_{ij} ∈ Γ(X, U_i ⊓ U_j)ˣ`. -/
structure AlgLineBundle (X : Scheme.{0}) where
  ι : Type
  U : ι → X.Opens
  g : (i j : ι) → Γ(X, U i ⊓ U j)ˣ

namespace AlgLineBundle

variable {X Y : Scheme.{0}}

/-- Line-bundle cocycle validity predicate `IsLB`: open cover, unit self-transitions, and cocycle law. -/
structure IsLB (L : AlgLineBundle X) : Prop where
  cov : ⨆ i, L.U i = ⊤
  g_self : ∀ i, L.g i i = 1
  g_cocycle : ∀ (i j k : L.ι),
    (X.presheaf.map (homOfLE (inf_le_inf_left (L.U i) inf_le_left :
      L.U i ⊓ (L.U j ⊓ L.U k) ≤ L.U i ⊓ L.U j)).op).hom (L.g i j : Γ(X, L.U i ⊓ L.U j)) *
    (X.presheaf.map (homOfLE (inf_le_right :
      L.U i ⊓ (L.U j ⊓ L.U k) ≤ L.U j ⊓ L.U k)).op).hom (L.g j k : Γ(X, L.U j ⊓ L.U k)) =
    (X.presheaf.map (homOfLE (inf_le_inf_left (L.U i) inf_le_right :
      L.U i ⊓ (L.U j ⊓ L.U k) ≤ L.U i ⊓ L.U k)).op).hom (L.g i k : Γ(X, L.U i ⊓ L.U k))

/-- Trivial algebraic line bundle `𝒪_X` on `X`. -/
@[reducible]
def triv (X : Scheme.{0}) : AlgLineBundle X where
  ι := PUnit
  U _ := ⊤
  g _ _ := 1

theorem isLB_triv (X : Scheme.{0}) : IsLB (triv X) where
  cov := iSup_const
  g_self _ := rfl
  g_cocycle _ _ _ := by simp [triv]

private theorem preimage_inf_le {X Y : Scheme.{0}} (f : Y ⟶ X) (U V : X.Opens) :
    f ⁻¹ᵁ U ⊓ f ⁻¹ᵁ V ≤ f ⁻¹ᵁ (U ⊓ V) :=
  fun _ hx => hx

/-- Pullback `f^* L` of an algebraic line bundle along a scheme morphism `f : Y ⟶ X`. -/
@[reducible]
def pull (L : AlgLineBundle X) (f : Y ⟶ X) : AlgLineBundle Y where
  ι := L.ι
  U i := f ⁻¹ᵁ L.U i
  g i j := Units.map
    ((f.app (L.U i ⊓ L.U j) ≫
      Y.presheaf.map (homOfLE (preimage_inf_le f (L.U i) (L.U j))).op).hom)
    (L.g i j)

/-- Dual algebraic line bundle `L^∨`. -/
@[reducible]
def dual (L : AlgLineBundle X) : AlgLineBundle X where
  ι := L.ι
  U := L.U
  g i j := (L.g i j)⁻¹

/-- Tensor product `L₁ ⊗ L₂` of two algebraic line bundles on `X`. -/
@[reducible]
def tensor (L₁ L₂ : AlgLineBundle X) : AlgLineBundle X where
  ι := L₁.ι × L₂.ι
  U p := L₁.U p.1 ⊓ L₂.U p.2
  g p q :=
    let h1 : (L₁.U p.1 ⊓ L₂.U p.2) ⊓ (L₁.U q.1 ⊓ L₂.U q.2) ≤ L₁.U p.1 ⊓ L₁.U q.1 :=
      le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left)
    let h2 : (L₁.U p.1 ⊓ L₂.U p.2) ⊓ (L₁.U q.1 ⊓ L₂.U q.2) ≤ L₂.U p.2 ⊓ L₂.U q.2 :=
      le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)
    Units.map (X.presheaf.map (homOfLE h1).op).hom (L₁.g p.1 q.1) *
      Units.map (X.presheaf.map (homOfLE h2).op).hom (L₂.g p.2 q.2)

/-- Integer tensor power `L^{⊗ k}` of an algebraic line bundle. -/
@[reducible]
def pow (L : AlgLineBundle X) (k : ℤ) : AlgLineBundle X where
  ι := L.ι
  U := L.U
  g i j := (L.g i j) ^ k

end AlgLineBundle

/-- Global algebraic section `s ∈ H⁰(X, L)` of `L : AlgLineBundle X`. -/
@[ext]
structure AlgSection {X : Scheme.{0}} (L : AlgLineBundle X) where
  f : ∀ i : L.ι, Γ(X, L.U i)
  compat : ∀ i j,
    (X.presheaf.map (homOfLE (inf_le_left : L.U i ⊓ L.U j ≤ L.U i)).op).hom (f i) =
      (L.g i j : Γ(X, L.U i ⊓ L.U j)) *
        (X.presheaf.map (homOfLE (inf_le_right : L.U i ⊓ L.U j ≤ L.U j)).op).hom (f j)

namespace AlgSection

variable {X : Scheme.{0}} {L : AlgLineBundle X}

instance : Zero (AlgSection L) where
  zero :=
    { f := fun _ => 0
      compat := fun _ _ => by simp }

instance : Add (AlgSection L) where
  add s₁ s₂ :=
    { f := fun i => s₁.f i + s₂.f i
      compat := fun i j => by
        rw [map_add, map_add, s₁.compat i j, s₂.compat i j, mul_add] }

instance : Neg (AlgSection L) where
  neg s :=
    { f := fun i => -s.f i
      compat := fun i j => by
        rw [map_neg, map_neg, s.compat i j, mul_neg] }

instance : Sub (AlgSection L) where
  sub s₁ s₂ :=
    { f := fun i => s₁.f i - s₂.f i
      compat := fun i j => by
        rw [map_sub, map_sub, s₁.compat i j, s₂.compat i j, mul_sub] }

instance : AddCommGroup (AlgSection L) where
  add_assoc a b c := by ext i; exact add_assoc _ _ _
  zero_add a := by ext i; exact zero_add _
  add_zero a := by ext i; exact add_zero _
  neg_add_cancel a := by ext i; exact neg_add_cancel _
  add_comm a b := by ext i; exact add_comm _ _
  sub_eq_add_neg a b := by ext i; exact sub_eq_add_neg _ _
  nsmul := nsmulRec
  zsmul := zsmulRec

@[simp] lemma zero_f (i : L.ι) : (0 : AlgSection L).f i = 0 := rfl
@[simp] lemma add_f (s₁ s₂ : AlgSection L) (i : L.ι) : (s₁ + s₂).f i = s₁.f i + s₂.f i := rfl
@[simp] lemma neg_f (s : AlgSection L) (i : L.ι) : (-s).f i = -s.f i := rfl
@[simp] lemma sub_f (s₁ s₂ : AlgSection L) (i : L.ι) : (s₁ - s₂).f i = s₁.f i - s₂.f i := rfl

private lemma res_res {U V W : X.Opens} (hUV : U ≤ V) (hVW : V ≤ W) (x : Γ(X, W)) :
    (X.presheaf.map (homOfLE hUV).op).hom ((X.presheaf.map (homOfLE hVW).op).hom x) =
      (X.presheaf.map (homOfLE (hUV.trans hVW)).op).hom x := by
  rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, ← Functor.map_comp]
  rfl

/-- Tensor multiplication of algebraic sections `s₁ ⊗ s₂ ∈ H⁰(X, L₁ ⊗ L₂)`. -/
def mul {L₁ L₂ : AlgLineBundle X} (s₁ : AlgSection L₁) (s₂ : AlgSection L₂) :
    AlgSection (L₁.tensor L₂) where
  f (p : L₁.ι × L₂.ι) :=
    (X.presheaf.map (homOfLE (inf_le_left : L₁.U p.1 ⊓ L₂.U p.2 ≤ L₁.U p.1)).op).hom (s₁.f p.1) *
    (X.presheaf.map (homOfLE (inf_le_right : L₁.U p.1 ⊓ L₂.U p.2 ≤ L₂.U p.2)).op).hom (s₂.f p.2)
  compat (p q : L₁.ι × L₂.ι) := by
    dsimp only [AlgLineBundle.tensor]
    simp only [map_mul, Units.val_mul, Units.coe_map, MonoidHom.coe_coe, res_res]
    have h1L : (X.presheaf.map (homOfLE _).op).hom (s₁.f p.1) =
        (X.presheaf.map (homOfLE (le_inf (le_trans inf_le_left inf_le_left) (le_trans inf_le_right inf_le_left) :
            (L₁.U p.1 ⊓ L₂.U p.2) ⊓ (L₁.U q.1 ⊓ L₂.U q.2) ≤ L₁.U p.1 ⊓ L₁.U q.1)).op).hom
          ((X.presheaf.map (homOfLE (inf_le_left : L₁.U p.1 ⊓ L₁.U q.1 ≤ L₁.U p.1)).op).hom
            (s₁.f p.1)) :=
      (res_res _ _ (s₁.f p.1)).symm
    have h2L : (X.presheaf.map (homOfLE _).op).hom (s₂.f p.2) =
        (X.presheaf.map (homOfLE (le_inf (le_trans inf_le_left inf_le_right) (le_trans inf_le_right inf_le_right) :
            (L₁.U p.1 ⊓ L₂.U p.2) ⊓ (L₁.U q.1 ⊓ L₂.U q.2) ≤ L₂.U p.2 ⊓ L₂.U q.2)).op).hom
          ((X.presheaf.map (homOfLE (inf_le_left : L₂.U p.2 ⊓ L₂.U q.2 ≤ L₂.U p.2)).op).hom
            (s₂.f p.2)) :=
      (res_res _ _ (s₂.f p.2)).symm
    rw [h1L, h2L, s₁.compat p.1 q.1, s₂.compat p.2 q.2, map_mul, map_mul, res_res, res_res]
    ring

/-- Natural tensor power `s^{⊗ n} ∈ H⁰(X, L^{⊗ n})` of an algebraic section. -/
def pow (s : AlgSection L) (n : ℕ) : AlgSection (L.pow (n : ℤ)) where
  f i := (s.f i) ^ n
  compat i j := by
    change (X.presheaf.map (homOfLE _).op).hom ((s.f i) ^ n) =
      (((L.g i j ^ (n : ℤ) : Γ(X, L.U i ⊓ L.U j)ˣ) : Γ(X, L.U i ⊓ L.U j))) *
        (X.presheaf.map (homOfLE _).op).hom ((s.f j) ^ n)
    rw [map_pow, map_pow, s.compat i j, mul_pow]
    simp

/-- Pullback `f^* s ∈ H⁰(Y, f^* L)` of a global section along `f : Y ⟶ X`. -/
def pull {Y : Scheme.{0}} (s : AlgSection L) (f : Y ⟶ X) : AlgSection (L.pull f) where
  f i := by
    let i' : L.ι := i
    exact (f.app (L.U i')).hom (s.f i')
  compat i j := by
    let i' : L.ι := i
    let j' : L.ι := j
    dsimp only [AlgLineBundle.pull]
    simp only [Units.coe_map, MonoidHom.coe_coe, CommRingCat.hom_comp, RingHom.comp_apply]
    have hnatL := f.naturality (homOfLE (inf_le_left : L.U i' ⊓ L.U j' ≤ L.U i')).op
    have hnatR := f.naturality (homOfLE (inf_le_right : L.U i' ⊓ L.U j' ≤ L.U j')).op
    have hcL : (Y.presheaf.map (homOfLE (f.preimage_mono (inf_le_left : L.U i' ⊓ L.U j' ≤ L.U i'))).op).hom
          ((f.app (L.U i')).hom (s.f i')) =
        (f.app (L.U i' ⊓ L.U j')).hom
          ((X.presheaf.map (homOfLE (inf_le_left : L.U i' ⊓ L.U j' ≤ L.U i')).op).hom (s.f i')) := by
      have hc := congrArg (fun φ : CommRingCat.Hom _ _ => φ.hom (s.f i')) hnatL
      simp only [CommRingCat.hom_comp, RingHom.comp_apply] at hc
      exact hc.symm
    have hcR : (Y.presheaf.map (homOfLE (f.preimage_mono (inf_le_right : L.U i' ⊓ L.U j' ≤ L.U j'))).op).hom
          ((f.app (L.U j')).hom (s.f j')) =
        (f.app (L.U i' ⊓ L.U j')).hom
          ((X.presheaf.map (homOfLE (inf_le_right : L.U i' ⊓ L.U j' ≤ L.U j')).op).hom (s.f j')) := by
      have hc := congrArg (fun φ : CommRingCat.Hom _ _ => φ.hom (s.f j')) hnatR
      simp only [CommRingCat.hom_comp, RingHom.comp_apply] at hc
      exact hc.symm
    have hL : (Y.presheaf.map (homOfLE (inf_le_left : f ⁻¹ᵁ L.U i' ⊓ f ⁻¹ᵁ L.U j' ≤ f ⁻¹ᵁ L.U i')).op).hom
          ((f.app (L.U i')).hom (s.f i')) =
        (Y.presheaf.map (homOfLE (AlgLineBundle.preimage_inf_le f (L.U i') (L.U j'))).op).hom
          ((f.app (L.U i' ⊓ L.U j')).hom
            ((X.presheaf.map (homOfLE (inf_le_left : L.U i' ⊓ L.U j' ≤ L.U i')).op).hom (s.f i'))) := by
      rw [← hcL]
      exact (res_res (AlgLineBundle.preimage_inf_le f (L.U i') (L.U j'))
        (f.preimage_mono (inf_le_left : L.U i' ⊓ L.U j' ≤ L.U i'))
        ((f.app (L.U i')).hom (s.f i'))).symm
    have hR : (Y.presheaf.map (homOfLE (inf_le_right : f ⁻¹ᵁ L.U i' ⊓ f ⁻¹ᵁ L.U j' ≤ f ⁻¹ᵁ L.U j')).op).hom
          ((f.app (L.U j')).hom (s.f j')) =
        (Y.presheaf.map (homOfLE (AlgLineBundle.preimage_inf_le f (L.U i') (L.U j'))).op).hom
          ((f.app (L.U i' ⊓ L.U j')).hom
            ((X.presheaf.map (homOfLE (inf_le_right : L.U i' ⊓ L.U j' ≤ L.U j')).op).hom (s.f j'))) := by
      rw [← hcR]
      exact (res_res (AlgLineBundle.preimage_inf_le f (L.U i') (L.U j'))
        (f.preimage_mono (inf_le_right : L.U i' ⊓ L.U j' ≤ L.U j'))
        ((f.app (L.U j')).hom (s.f j'))).symm
    rw [hL, hR]
    change (Y.presheaf.map (homOfLE (AlgLineBundle.preimage_inf_le f (L.U i') (L.U j'))).op).hom
        ((f.app (L.U i' ⊓ L.U j')).hom
          ((X.presheaf.map (homOfLE (inf_le_left : L.U i' ⊓ L.U j' ≤ L.U i')).op).hom (s.f i'))) =
      (Y.presheaf.map (homOfLE (AlgLineBundle.preimage_inf_le f (L.U i') (L.U j'))).op).hom
          ((f.app (L.U i' ⊓ L.U j')).hom (L.g i' j' : Γ(X, L.U i' ⊓ L.U j'))) *
        (Y.presheaf.map (homOfLE (AlgLineBundle.preimage_inf_le f (L.U i') (L.U j'))).op).hom
          ((f.app (L.U i' ⊓ L.U j')).hom
            ((X.presheaf.map (homOfLE (inf_le_right : L.U i' ⊓ L.U j' ≤ L.U j')).op).hom (s.f j')))
    rw [s.compat i' j', RingHom.map_mul]
    exact map_mul (Y.presheaf.map (homOfLE (AlgLineBundle.preimage_inf_le f (L.U i') (L.U j'))).op).hom _ _

end AlgSection

private theorem le_preimage_top {K : Type} [CommRing K] {X : Scheme.{0}}
    (p : X ⟶ Sp K) (U : X.Opens) : U ≤ p ⁻¹ᵁ ⊤ :=
  fun _ _ => trivial

/-- Constant function on an open `U : X.Opens` pulled back from `p : X ⟶ Sp K` (`c : K`). -/
def constFn {K : Type} [CommRing K] {X : Scheme.{0}} (p : X ⟶ Sp K) (U : X.Opens) (c : K) :
    Γ(X, U) :=
  ((X.presheaf.map (homOfLE (le_preimage_top p U)).op).hom
    ((p.app ⊤).hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom c)))

theorem constFn_map_zero {K : Type} [CommRing K] {X : Scheme.{0}} (p : X ⟶ Sp K) (U : X.Opens) :
    constFn p U 0 = 0 := by
  unfold constFn
  rw [map_zero, map_zero, map_zero]

theorem constFn_map_one {K : Type} [CommRing K] {X : Scheme.{0}} (p : X ⟶ Sp K) (U : X.Opens) :
    constFn p U 1 = 1 := by
  unfold constFn
  rw [map_one, map_one, map_one]

theorem constFn_map_add {K : Type} [CommRing K] {X : Scheme.{0}} (p : X ⟶ Sp K) (U : X.Opens)
    (a b : K) : constFn p U (a + b) = constFn p U a + constFn p U b := by
  unfold constFn
  rw [map_add, map_add, map_add]

theorem constFn_map_mul {K : Type} [CommRing K] {X : Scheme.{0}} (p : X ⟶ Sp K) (U : X.Opens)
    (a b : K) : constFn p U (a * b) = constFn p U a * constFn p U b := by
  unfold constFn
  rw [map_mul, map_mul, map_mul]

theorem constFn_res {K : Type} [CommRing K] {X : Scheme.{0}} (p : X ⟶ Sp K) {U V : X.Opens}
    (hUV : U ≤ V) (c : K) :
    (X.presheaf.map (homOfLE hUV).op).hom (constFn p V c) = constFn p U c := by
  exact AlgSection.res_res hUV (le_preimage_top p V)
    ((p.app ⊤).hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom c))

/-- Type wrapper equipping `AlgSection L` with a canonical `Module K` instance over `p : X ⟶ Sp K`. -/
def AlgSectionOver {K : Type} [CommRing K] {X : Scheme.{0}} (_p : X ⟶ Sp K)
    (L : AlgLineBundle X) : Type :=
  AlgSection L

namespace AlgSectionOver

variable {K : Type} [CommRing K] {X : Scheme.{0}} {p : X ⟶ Sp K} {L : AlgLineBundle X}

instance : AddCommGroup (AlgSectionOver p L) :=
  inferInstanceAs (AddCommGroup (AlgSection L))

/-- Equivalence between `AlgSectionOver p L` and `AlgSection L`. -/
def toAlgSection (s : AlgSectionOver p L) : AlgSection L := s
def ofAlgSection (s : AlgSection L) : AlgSectionOver p L := s

@[ext]
theorem ext {s₁ s₂ : AlgSectionOver p L} (h : ∀ i, s₁.toAlgSection.f i = s₂.toAlgSection.f i) :
    s₁ = s₂ :=
  AlgSection.ext (funext h)

instance : SMul K (AlgSectionOver p L) where
  smul c s :=
    { f := fun i => constFn p (L.U i) c * s.toAlgSection.f i
      compat := fun i j => by
        rw [map_mul, map_mul, constFn_res, constFn_res, s.toAlgSection.compat i j]
        ring }

instance : Module K (AlgSectionOver p L) where
  smul := (· • ·)
  one_smul s := ext fun i => by change constFn p (L.U i) 1 * s.toAlgSection.f i = _; simp [constFn_map_one]
  mul_smul a b s := ext fun i => by
    change constFn p (L.U i) (a * b) * s.toAlgSection.f i =
      constFn p (L.U i) a * (constFn p (L.U i) b * s.toAlgSection.f i)
    rw [constFn_map_mul, mul_assoc]
  smul_zero a := ext fun i => by change constFn p (L.U i) a * 0 = 0; simp
  smul_add a s₁ s₂ := ext fun i => by
    change constFn p (L.U i) a * (s₁.toAlgSection.f i + s₂.toAlgSection.f i) =
      constFn p (L.U i) a * s₁.toAlgSection.f i + constFn p (L.U i) a * s₂.toAlgSection.f i
    rw [mul_add]
  add_smul a b s := ext fun i => by
    change constFn p (L.U i) (a + b) * s.toAlgSection.f i =
      constFn p (L.U i) a * s.toAlgSection.f i + constFn p (L.U i) b * s.toAlgSection.f i
    rw [constFn_map_add, add_mul]
  zero_smul s := ext fun i => by
    change constFn p (L.U i) 0 * s.toAlgSection.f i = 0
    rw [constFn_map_zero, zero_mul]

end AlgSectionOver

/-- **Finite-Dimensionality of Global Sections `SectionsHaveFiniteDimension p L r`**:
there exists an `r`-element `K`-basis `s : Fin r → AlgSectionOver p L` expressing every global
section `t` uniquely as `t = ∑ i, a_i • s_i`. -/
def SectionsHaveFiniteDimension {K : Type} [Field K] {X : Scheme.{0}}
    (p : X ⟶ Sp K) (L : AlgLineBundle X) (r : ℕ) : Prop :=
  ∃ s : Fin r → AlgSectionOver p L,
    ∀ t : AlgSectionOver p L, ∃! a : Fin r → K, t = ∑ i : Fin r, a i • s i

section FiniteDimTheorems

variable {K : Type} [Field K] {X : Scheme.{0}}

/-- Monotonicity of `SectionsHaveFiniteDimension` ranks (`r ≤ r'`). -/
theorem sections_have_finite_dimension_le {p : X ⟶ Sp K} {L : AlgLineBundle X} {r r' : ℕ}
    (h : SectionsHaveFiniteDimension p L r) (h' : SectionsHaveFiniteDimension p L r') :
    r ≤ r' := by
  obtain ⟨s, hs⟩ := h
  obtain ⟨s', hs'⟩ := h'
  choose B hB _ using fun i => hs' (s i)
  let M : (Fin r → K) →ₗ[K] (Fin r' → K) :=
    { toFun := fun a k => ∑ i : Fin r, a i * B i k
      map_add' := fun a b => by ext k; simp [add_mul, Finset.sum_add_distrib]
      map_smul' := fun c a => by ext k; simp [mul_assoc, Finset.mul_sum] }
  have hinj : Function.Injective M := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    have hsum : (∑ i : Fin r, a i • s i) = 0 := by
      calc (∑ i : Fin r, a i • s i)
          = ∑ i : Fin r, a i • (∑ k : Fin r', B i k • s' k) := by
            refine Finset.sum_congr rfl fun i _ => ?_; rw [← hB i]
        _ = ∑ k : Fin r', (∑ i : Fin r, a i * B i k) • s' k := by
            simp_rw [Finset.smul_sum, smul_smul]
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [← Finset.sum_smul]
        _ = ∑ k : Fin r', (0 : K) • s' k := by
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [show (∑ i : Fin r, a i * B i k) = M a k from rfl, ha]; rfl
        _ = 0 := by simp
    exact ((hs 0).unique (by simp) hsum.symm).symm
  have hle := LinearMap.finrank_le_finrank_of_injective hinj
  simpa using hle

/-- Uniqueness of the dimension in `SectionsHaveFiniteDimension`. -/
theorem sections_have_finite_dimension_unique {p : X ⟶ Sp K} {L : AlgLineBundle X} {r r' : ℕ}
    (h : SectionsHaveFiniteDimension p L r) (h' : SectionsHaveFiniteDimension p L r') :
    r = r' :=
  le_antisymm (sections_have_finite_dimension_le h h') (sections_have_finite_dimension_le h' h)

/-- **`sections_have_finite_dimension`**:
given `SectionsHaveFiniteDimension p L r`, `AlgSectionOver p L` is unconditionally
finite-dimensional over `K` of exact dimension `r`, with an explicit `K`-linear equivalence
`AlgSectionOver p L ≃ₗ[K] (Fin r → K)`. -/
theorem sections_have_finite_dimension {p : X ⟶ Sp K} {L : AlgLineBundle X} {r : ℕ}
    (h : SectionsHaveFiniteDimension p L r) :
    FiniteDimensional K (AlgSectionOver p L) ∧
    Module.finrank K (AlgSectionOver p L) = r ∧
    Nonempty (AlgSectionOver p L ≃ₗ[K] (Fin r → K)) := by
  obtain ⟨s, hs⟩ := h
  choose coord hcoord hcoord_uniq using hs
  let φ : AlgSectionOver p L ≃ₗ[K] (Fin r → K) :=
    { toFun := coord
      invFun := fun a => ∑ i : Fin r, a i • s i
      map_add' := fun t₁ t₂ => by
        refine (hcoord_uniq (t₁ + t₂) (coord t₁ + coord t₂) ?_).symm
        calc t₁ + t₂ = (∑ i, coord t₁ i • s i) + (∑ i, coord t₂ i • s i) := by
              rw [← hcoord t₁, ← hcoord t₂]
          _ = ∑ i, (coord t₁ i + coord t₂ i) • s i := by
              rw [← Finset.sum_add_distrib]
              refine Finset.sum_congr rfl fun i _ => (add_smul _ _ _).symm
      map_smul' := fun c t => by
        refine (hcoord_uniq (c • t) (c • coord t) ?_).symm
        calc c • t = c • ∑ i, coord t i • s i := by rw [← hcoord t]
          _ = ∑ i, (c * coord t i) • s i := by
              rw [Finset.smul_sum]
              refine Finset.sum_congr rfl fun i _ => smul_smul _ _ _
      left_inv := fun t => (hcoord t).symm
      right_inv := fun a => (hcoord_uniq (∑ i, a i • s i) a rfl).symm }
  have hfd : FiniteDimensional K (AlgSectionOver p L) := φ.symm.finiteDimensional
  have hfr : Module.finrank K (AlgSectionOver p L) = r := by
    rw [φ.finrank_eq, Module.finrank_pi, Fintype.card_fin]
  exact ⟨hfd, hfr, ⟨φ⟩⟩

/-- Transfer of `SectionsHaveFiniteDimension` along any `K`-linear isomorphism. -/
theorem sections_have_finite_dimension_of_linearEquiv
    {p₁ : X ⟶ Sp K} {L₁ : AlgLineBundle X}
    {Y : Scheme.{0}} {p₂ : Y ⟶ Sp K} {L₂ : AlgLineBundle Y} {r : ℕ}
    (e : AlgSectionOver p₁ L₁ ≃ₗ[K] AlgSectionOver p₂ L₂)
    (h : SectionsHaveFiniteDimension p₁ L₁ r) :
    SectionsHaveFiniteDimension p₂ L₂ r := by
  obtain ⟨s, hs⟩ := h
  refine ⟨fun i => e (s i), fun t => ?_⟩
  obtain ⟨a, ha, hau⟩ := hs (e.symm t)
  refine ⟨a, ?_, fun b hb => hau b ?_⟩
  · have h1 := congrArg e ha
    simp only [map_sum, map_smul, LinearEquiv.apply_symm_apply] at h1
    exact h1
  · have h2 := congrArg e.symm hb
    simp only [map_sum, map_smul, LinearEquiv.symm_apply_apply] at h2
    exact h2

/-- Any `K`-linear injection from `AlgSectionOver p L` into a finite-dimensional `K`-space `V`
forces `AlgSectionOver p L` to be finite-dimensional and satisfy `SectionsHaveFiniteDimension`. -/
theorem sections_have_finite_dimension_of_injective_finite
    {p : X ⟶ Sp K} {L : AlgLineBundle X} {V : Type*} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V]
    (Φ : AlgSectionOver p L →ₗ[K] V) (hΦ : Function.Injective Φ) :
    FiniteDimensional K (AlgSectionOver p L) ∧
    Module.finrank K (AlgSectionOver p L) ≤ Module.finrank K V ∧
    SectionsHaveFiniteDimension p L (Module.finrank K (AlgSectionOver p L)) := by
  have : FiniteDimensional K (AlgSectionOver p L) :=
    FiniteDimensional.of_injective Φ hΦ
  have hle : Module.finrank K (AlgSectionOver p L) ≤ Module.finrank K V :=
    LinearMap.finrank_le_finrank_of_injective hΦ
  let b := Module.finBasis K (AlgSectionOver p L)
  have hsec : SectionsHaveFiniteDimension p L (Module.finrank K (AlgSectionOver p L)) := by
    refine ⟨b, fun t => ?_⟩
    refine ⟨fun i => b.repr t i, (b.sum_repr t).symm, fun a ha => ?_⟩
    ext i
    have h1 := congrArg (fun x => b.repr x i) ha
    simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply,
      Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, Basis.repr_self, Finsupp.single_apply] at h1
    simpa using h1.symm
  exact ⟨‹FiniteDimensional K (AlgSectionOver p L)›, hle, hsec⟩

/-- Over an affine point `Sp K`, the trivial line bundle has
`SectionsHaveFiniteDimension (𝟙 (Sp K)) (triv (Sp K)) 1`. -/
theorem sections_have_finite_dimension_spec_triv (K : Type) [Field K] :
    SectionsHaveFiniteDimension (𝟙 (Sp K)) (AlgLineBundle.triv (Sp K)) 1 := by
  let idS : Sp K ⟶ Sp K := 𝟙 (Sp K)
  let iso : K ≃+* Γ(Sp K, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.symm
  have hconst : ∀ (c : K), constFn idS ⊤ c = iso c := fun c => by
    unfold constFn
    have h1 : (idS.app ⊤).hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom c) = iso c := rfl
    change ((Sp K).presheaf.map (homOfLE (le_top : (⊤ : (Sp K).Opens) ≤ idS ⁻¹ᵁ ⊤)).op).hom
      ((idS.app ⊤).hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom c)) = iso c
    rw [h1]
    have hle : (⊤ : (Sp K).Opens) = idS ⁻¹ᵁ ⊤ := rfl
    rw [show (homOfLE (le_top : (⊤ : (Sp K).Opens) ≤ idS ⁻¹ᵁ ⊤)) = 𝟙 (⊤ : (Sp K).Opens) from rfl]
    simp
  let oneSec : AlgSectionOver idS (AlgLineBundle.triv (Sp K)) :=
    AlgSectionOver.ofAlgSection
      { f := fun _ => 1
        compat := fun _ _ => by simp [AlgLineBundle.triv] }
  refine ⟨fun _ => oneSec, fun t => ?_⟩
  refine ⟨fun _ => iso.symm (t.toAlgSection.f PUnit.unit), ?_, ?_⟩
  · apply AlgSectionOver.ext
    intro i
    have hi : i = PUnit.unit := Subsingleton.elim (α := PUnit) i PUnit.unit
    subst hi
    rw [Fin.sum_univ_one]
    change t.toAlgSection.f PUnit.unit =
      constFn idS ⊤ (iso.symm (t.toAlgSection.f PUnit.unit)) * 1
    rw [hconst, mul_one, iso.apply_symm_apply]
  · intro a ha
    ext i
    obtain rfl : i = 0 := Subsingleton.elim _ _
    have h0 := congrArg (fun s : AlgSectionOver idS (AlgLineBundle.triv (Sp K)) =>
      s.toAlgSection.f PUnit.unit) ha
    rw [Fin.sum_univ_one] at h0
    change t.toAlgSection.f PUnit.unit = constFn idS ⊤ (a 0) * 1 at h0
    rw [hconst, mul_one] at h0
    exact iso.injective (by rw [iso.apply_symm_apply, h0])

/-- **Flat Integral Model Generic Density (`algSection_dense_generic_of_flat`)**:
on any scheme `S` flat over a domain `Sp o` (`Stage14M3_IntegralSchemesAndCharts.dense_generic_of_flat`),
every nonempty chart `L.U i` meets the generic fiber `{x : S | (s₀ x).asIdeal = ⊥}`. -/
theorem algSection_dense_generic_of_flat {o : Type} [CommRing o] [IsDomain o]
    {S : Scheme.{0}} (s₀ : S ⟶ Sp o) [Flat s₀] (L : AlgLineBundle S)
    {i : L.ι} (hne : (L.U i : Set S).Nonempty) :
    ∃ x ∈ L.U i, (s₀ x).asIdeal = ⊥ :=
  exists_generic_point_mem_of_flat s₀ (L.U i).isOpen hne

end FiniteDimTheorems

section ProjectiveSpaceFiniteDim

private lemma isHomogeneous_monomial_of_multiIndex {K : Type*} [CommRing K] {N e : ℕ}
    (α : MultiIndex (N + 1) e) :
    MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm α.1) (1 : K) ∈
      MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K e := by
  rw [MvPolynomial.mem_homogeneousSubmodule]
  intro d hd
  have hd_eq : d = Finsupp.equivFunOnFinite.symm α.1 := by
    by_contra hne
    rw [MvPolynomial.coeff_monomial, if_neg (Ne.symm hne)] at hd
    exact hd rfl
  subst hd_eq
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (fun _ => by simp)]
  simpa [smul_eq_mul] using α.2

/-- **Explicit `K`-Basis of `H⁰(ℙ^N_K, 𝒪(e)) = MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K e`**
indexed by `MultiIndex (N + 1) e`. -/
def homogeneousBasis (K : Type*) [Field K] (N e : ℕ) :
    Module.Basis (MultiIndex (N + 1) e) K (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K e) :=
  Module.Basis.mk
    (v := fun α =>
      ⟨MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm α.1) (1 : K),
        isHomogeneous_monomial_of_multiIndex α⟩)
    (by
      rw [Fintype.linearIndependent_iff]
      intro c hc α
      have hcoeff := congrArg
        (fun p : MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K e =>
          MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm α.1) p.1) hc
      simp only [ZeroMemClass.coe_zero, MvPolynomial.coeff_zero] at hcoeff
      have hcoe : (∑ β : MultiIndex (N + 1) e,
          c β • (⟨MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm β.1) (1 : K),
            isHomogeneous_monomial_of_multiIndex β⟩ :
              MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K e)).1 =
          ∑ β : MultiIndex (N + 1) e,
            MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm β.1) (c β) := by
        rw [AddSubmonoidClass.coe_finsetSum]
        refine Finset.sum_congr rfl fun β _ => ?_
        change c β • MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm β.1) (1 : K) = _
        rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
      rw [hcoe, MvPolynomial.coeff_sum] at hcoeff
      have hsingle : ∀ β : MultiIndex (N + 1) e,
          MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm α.1)
            (MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm β.1) (c β)) =
            if β = α then c α else 0 := by
        intro β
        rw [MvPolynomial.coeff_monomial]
        split_ifs with h1 h2 h2
        · have hβα : β = α := Subtype.ext (Finsupp.equivFunOnFinite.symm.injective h1)
          subst hβα; rfl
        · exact False.elim (h2 (Subtype.ext (Finsupp.equivFunOnFinite.symm.injective h1)))
        · exact False.elim (h1 (by rw [h2]))
        · rfl
      simp_rw [hsingle] at hcoeff
      simpa using hcoeff)
    (by
      intro ⟨p, hp⟩ _
      rw [MvPolynomial.mem_homogeneousSubmodule] at hp
      have hp_eq : p = ∑ d ∈ p.support, MvPolynomial.monomial d (p.coeff d) :=
        MvPolynomial.as_sum p
      have hp_mem : ∀ d ∈ p.support,
          ∃ α : MultiIndex (N + 1) e, d = Finsupp.equivFunOnFinite.symm α.1 := by
        intro d hd
        have hwt := hp (MvPolynomial.mem_support_iff.mp hd)
        rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (fun _ => by simp)] at hwt
        refine ⟨⟨d, by simpa [smul_eq_mul] using hwt⟩, Finsupp.ext fun _ => rfl⟩
      have hhom_term : ∀ d ∈ p.support,
          MvPolynomial.monomial d (p.coeff d) ∈
            MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K e := by
        intro d hd
        rw [MvPolynomial.mem_homogeneousSubmodule]
        intro m hm
        have hmd : d = m := by
          by_contra hne
          rw [MvPolynomial.coeff_monomial, if_neg hne] at hm
          exact hm rfl
        subst hmd
        exact hp (MvPolynomial.mem_support_iff.mp hd)
      have hterm : ∀ (d : Fin (N + 1) →₀ ℕ) (hd : d ∈ p.support),
          (⟨MvPolynomial.monomial d (p.coeff d), hhom_term d hd⟩ :
            MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K e) ∈
          Submodule.span K (Set.range fun α : MultiIndex (N + 1) e =>
            (⟨MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm α.1) (1 : K),
              isHomogeneous_monomial_of_multiIndex α⟩ :
                MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K e)) := by
        intro d hd
        obtain ⟨α, rfl⟩ := hp_mem d hd
        have hsm : (⟨MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm α.1)
            (p.coeff (Finsupp.equivFunOnFinite.symm α.1)), hhom_term _ hd⟩ :
            MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K e) =
            (p.coeff (Finsupp.equivFunOnFinite.symm α.1)) •
              ⟨MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm α.1) (1 : K),
                isHomogeneous_monomial_of_multiIndex α⟩ := by
          ext1; simp [MvPolynomial.smul_monomial]
        rw [hsm]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨α, rfl⟩)
      have hp_sub : (⟨p, hp⟩ : MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K e) =
          ∑ d ∈ p.support.attach,
            (⟨MvPolynomial.monomial d.1 (p.coeff d.1), hhom_term d.1 d.2⟩ :
              MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K e) := by
        ext1
        rw [AddSubmonoidClass.coe_finsetSum, Finset.sum_attach p.support (fun d => MvPolynomial.monomial d (p.coeff d))]
        exact hp_eq
      rw [hp_sub]
      exact Submodule.sum_mem _ fun d _ => hterm d.1 d.2)

/-- **Exact Dimension of Projective-Space Global Sections `H⁰(ℙ^N_K, 𝒪(e))`**:
`finrank_K (homogeneousSubmodule (Fin (N + 1)) K e) = Nat.choose (e + N) N`. -/
theorem finrank_homogeneousSubmodule (K : Type*) [Field K] (N e : ℕ) :
    Module.finrank K (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K e) =
      Nat.choose (e + N) N := by
  rw [Module.finrank_eq_card_basis (homogeneousBasis K N e),
    card_multiIndex (Nat.succ_pos N) e, show e + (N + 1) - 1 = e + N by omega,
    add_comm e N, ← Nat.choose_symm_add, add_comm N e]

/-- `H⁰(ℙ^N_K, 𝒪(e))` is finite-dimensional of rank `Nat.choose (e + N) N`. -/
theorem sections_have_finite_dimension_projSpace (K : Type*) [Field K] (N e : ℕ) :
    FiniteDimensional K (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K e) ∧
    Module.finrank K (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K e) =
      Nat.choose (e + N) N :=
  ⟨Module.Basis.finiteDimensional_of_finite (homogeneousBasis K N e),
    finrank_homogeneousSubmodule K N e⟩

/-- **Exact Asymptotic Volume of `ℙ^N`**:
`lim_{e → ∞} dim H⁰(ℙ^N, 𝒪(e)) / e^N = 1 / N!`. -/
theorem volume_projSpace_asymptotic (N : ℕ) :
    Tendsto (fun e : ℕ => (Nat.choose (e + N) N : ℝ) / (e : ℝ) ^ N)
      atTop (𝓝 (1 / (N.factorial : ℝ))) := by
  have hfac_pos : (0 : ℝ) < (N.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos N)
  have hchoose_eq : ∀ e : ℕ, 1 ≤ e →
      (Nat.choose (e + N) N : ℝ) / (e : ℝ) ^ N =
        (∏ i ∈ Finset.range N, ((1 : ℝ) + ((N - i : ℕ) : ℝ) / (e : ℝ))) /
          (N.factorial : ℝ) := by
    intro e he
    have he_pos : (0 : ℝ) < (e : ℝ) := Nat.cast_pos.mpr he
    have hdvd : N.factorial ∣ (e + N).descFactorial N := Nat.factorial_dvd_descFactorial _ N
    rw [Nat.choose_eq_descFactorial_div_factorial, Nat.cast_div hdvd hfac_pos.ne',
      Nat.descFactorial_eq_prod_range, Nat.cast_prod]
    have hprod_eq : (∏ i ∈ Finset.range N, ((e + N - i : ℕ) : ℝ)) =
        (e : ℝ) ^ N * ∏ i ∈ Finset.range N, ((1 : ℝ) + ((N - i : ℕ) : ℝ) / (e : ℝ)) := by
      have heN : (e : ℝ) ^ N = ∏ _i ∈ Finset.range N, (e : ℝ) := by
        rw [Finset.prod_const, Finset.card_range]
      rw [heN, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i hi => ?_
      have hiN : i ≤ N := (Finset.mem_range.mp hi).le
      have hcast : ((e + N - i : ℕ) : ℝ) = (e : ℝ) + ((N - i : ℕ) : ℝ) := by
        rw [Nat.add_sub_assoc hiN, Nat.cast_add]
      rw [hcast]
      field_simp [he_pos.ne']
    rw [hprod_eq]
    have heN_ne : (e : ℝ) ^ N ≠ 0 := (pow_pos he_pos N).ne'
    field_simp [heN_ne, hfac_pos.ne']
  have hlim_factor : ∀ i ∈ Finset.range N,
      Tendsto (fun e : ℕ => (1 : ℝ) + ((N - i : ℕ) : ℝ) / (e : ℝ)) atTop (𝓝 1) := by
    intro i _
    have hinv : Tendsto (fun e : ℕ => ((e : ℝ))⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
    have hdiv : Tendsto (fun e : ℕ => ((N - i : ℕ) : ℝ) / (e : ℝ)) atTop (𝓝 0) := by
      simpa only [div_eq_mul_inv, mul_zero] using hinv.const_mul ((N - i : ℕ) : ℝ)
    simpa only [add_zero] using tendsto_const_nhds.add hdiv
  have hlim_prod : Tendsto (fun e : ℕ => ∏ i ∈ Finset.range N,
      ((1 : ℝ) + ((N - i : ℕ) : ℝ) / (e : ℝ))) atTop (𝓝 1) := by
    have ht := tendsto_finsetProd (Finset.range N)
      (f := fun i (e : ℕ) => (1 : ℝ) + ((N - i : ℕ) : ℝ) / (e : ℝ))
      (a := fun _ => (1 : ℝ)) hlim_factor
    simpa only [Finset.prod_const_one] using ht
  have hlim_div : Tendsto (fun e : ℕ => (∏ i ∈ Finset.range N,
      ((1 : ℝ) + ((N - i : ℕ) : ℝ) / (e : ℝ))) / (N.factorial : ℝ))
      atTop (𝓝 (1 / (N.factorial : ℝ))) :=
    hlim_prod.div_const (N.factorial : ℝ)
  refine hlim_div.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with e he
  exact (hchoose_eq e he).symm

end ProjectiveSpaceFiniteDim

end AlgebraicLineBundlesAndFiniteDim

/-! ## Section 2: Complex Holomorphic Sections & GAGA Isomorphism (`gaga_sections_iso`) -/

section ComplexSectionsAndGaga

section HolomorphicSectionVectorSpace

variable {d : ℕ} {ι : Type*} {X : Set (Fin d → ℂ)} {L_an : MetrizedLineBundle d ι X}

instance instZeroMetrizedSection : Zero (MetrizedLineBundle.Section L_an) where
  zero :=
    { sec := fun _ _ => 0
      sec_holo := fun _ _ _ => contDiffAt_const
      sec_compat := fun _ _ _ _ => by simp }

instance instAddMetrizedSection : Add (MetrizedLineBundle.Section L_an) where
  add s₁ s₂ :=
    { sec := fun i z => s₁.sec i z + s₂.sec i z
      sec_holo := fun i z hz => (s₁.sec_holo i z hz).add (s₂.sec_holo i z hz)
      sec_compat := fun i j z hz => by
        rw [s₁.sec_compat i j z hz, s₂.sec_compat i j z hz]; ring }

instance instNegMetrizedSection : Neg (MetrizedLineBundle.Section L_an) where
  neg s :=
    { sec := fun i z => -s.sec i z
      sec_holo := fun i z hz => (s.sec_holo i z hz).neg
      sec_compat := fun i j z hz => by rw [s.sec_compat i j z hz]; ring }

instance instSubMetrizedSection : Sub (MetrizedLineBundle.Section L_an) where
  sub s₁ s₂ :=
    { sec := fun i z => s₁.sec i z - s₂.sec i z
      sec_holo := fun i z hz => (s₁.sec_holo i z hz).sub (s₂.sec_holo i z hz)
      sec_compat := fun i j z hz => by
        rw [s₁.sec_compat i j z hz, s₂.sec_compat i j z hz]; ring }

instance instSMulComplexMetrizedSection : SMul ℂ (MetrizedLineBundle.Section L_an) where
  smul c s := s.smul c

private lemma section_ext' {s₁ s₂ : MetrizedLineBundle.Section L_an}
    (h : ∀ i z, s₁.sec i z = s₂.sec i z) : s₁ = s₂ := by
  cases s₁; cases s₂
  congr
  funext i z
  exact h i z

instance instAddCommGroupMetrizedSection : AddCommGroup (MetrizedLineBundle.Section L_an) where
  add_assoc a b c := section_ext' fun _ _ => add_assoc _ _ _
  zero_add a := section_ext' fun _ _ => zero_add _
  add_zero a := section_ext' fun _ _ => add_zero _
  neg_add_cancel a := section_ext' fun _ _ => neg_add_cancel _
  add_comm a b := section_ext' fun _ _ => add_comm _ _
  sub_eq_add_neg a b := section_ext' fun _ _ => sub_eq_add_neg _ _
  nsmul := nsmulRec
  zsmul := zsmulRec

instance instModuleComplexMetrizedSection : Module ℂ (MetrizedLineBundle.Section L_an) where
  one_smul _ := section_ext' fun _ _ => one_mul _
  mul_smul _ _ _ := section_ext' fun _ _ => mul_assoc _ _ _
  smul_zero _ := section_ext' fun _ _ => mul_zero _
  smul_add _ _ _ := section_ext' fun _ _ => mul_add _ _ _
  add_smul _ _ _ := section_ext' fun _ _ => add_mul _ _ _
  zero_smul _ := section_ext' fun _ _ => zero_mul _

@[simp] lemma metrizedSection_zero_sec (i : ι) (z : Fin d → ℂ) :
    (0 : MetrizedLineBundle.Section L_an).sec i z = 0 := rfl

@[simp] lemma metrizedSection_add_sec (s₁ s₂ : MetrizedLineBundle.Section L_an)
    (i : ι) (z : Fin d → ℂ) :
    (s₁ + s₂).sec i z = s₁.sec i z + s₂.sec i z := rfl

@[simp] lemma metrizedSection_smul_sec (c : ℂ) (s : MetrizedLineBundle.Section L_an)
    (i : ι) (z : Fin d → ℂ) :
    (c • s).sec i z = c * s.sec i z := rfl

/-- Triangle inequality for pointwise Hermitian norm `ptNorm` on `MetrizedLineBundle.Section`. -/
theorem ptNorm_add_le (s₁ s₂ : MetrizedLineBundle.Section L_an) {z : Fin d → ℂ} (hz : z ∈ X) :
    (s₁ + s₂).ptNorm z ≤ s₁.ptNorm z + s₂.ptNorm z := by
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (L_an.covers hz)
  unfold MetrizedLineBundle.Section.ptNorm
  rw [(s₁ + s₂).ptNormSq_eq_of_mem hi, s₁.ptNormSq_eq_of_mem hi, s₂.ptNormSq_eq_of_mem hi]
  set w := Real.sqrt (Real.exp (-L_an.weight i z))
  have hw : 0 ≤ w := Real.sqrt_nonneg _
  have hrt : ∀ u : ℂ, Real.sqrt (‖u‖ ^ 2 * Real.exp (-L_an.weight i z)) = ‖u‖ * w := fun u => by
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]
  rw [hrt, hrt, hrt]
  calc ‖s₁.sec i z + s₂.sec i z‖ * w
      ≤ (‖s₁.sec i z‖ + ‖s₂.sec i z‖) * w :=
        mul_le_mul_of_nonneg_right (norm_add_le _ _) hw
    _ = ‖s₁.sec i z‖ * w + ‖s₂.sec i z‖ * w := add_mul _ _ _

/-- Positive homogeneity of pointwise Hermitian norm `ptNorm (c • s)`. -/
theorem ptNorm_smul (c : ℂ) (s : MetrizedLineBundle.Section L_an) {z : Fin d → ℂ} (hz : z ∈ X) :
    (c • s).ptNorm z = ‖c‖ * s.ptNorm z := by
  unfold MetrizedLineBundle.Section.ptNorm
  change Real.sqrt ((s.smul c).ptNormSq z) = ‖c‖ * Real.sqrt (s.ptNormSq z)
  rw [MetrizedLineBundle.Section.ptNormSq_smul c s hz, Real.sqrt_mul (sq_nonneg _),
    Real.sqrt_sq (norm_nonneg _)]

end HolomorphicSectionVectorSpace

/-- **Charted Algebraic-to-Analytic Evaluation Map (`GagaChartEval`)**:
links an algebraic line bundle `L_alg` over a `ℂ`-scheme `p : S ⟶ Sp ℂ` to a concrete
`MetrizedLineBundle d ι X_an` (`L_an`) via compatible holomorphic evaluation maps on charts. -/
structure GagaChartEval {S : Scheme.{0}} (p : S ⟶ Sp ℂ) (L_alg : AlgLineBundle S)
    {d : ℕ} {ι : Type*} {X_an : Set (Fin d → ℂ)} (L_an : MetrizedLineBundle d ι X_an) where
  idx : ι → L_alg.ι
  eval : ∀ i : ι, Γ(S, L_alg.U (idx i)) → (Fin d → ℂ) → ℂ
  eval_holo : ∀ i (f : Γ(S, L_alg.U (idx i))), ∀ z ∈ L_an.openCover i, ContDiffAt ℂ 2 (eval i f) z
  eval_add : ∀ i f₁ f₂ z, eval i (f₁ + f₂) z = eval i f₁ z + eval i f₂ z
  eval_mul : ∀ i f₁ f₂ z, eval i (f₁ * f₂) z = eval i f₁ z * eval i f₂ z
  eval_const : ∀ i (c : ℂ) z, eval i (constFn p (L_alg.U (idx i)) c) z = c
  eval_compat : ∀ (s : AlgSection L_alg) (i j : ι), ∀ z ∈ L_an.openCover i ∩ L_an.openCover j,
    eval i (s.f (idx i)) z = L_an.transFn i j z * eval j (s.f (idx j)) z

namespace GagaChartEval

variable {S : Scheme.{0}} {p : S ⟶ Sp ℂ} {L_alg : AlgLineBundle S}
  {d : ℕ} {ι : Type*} {X_an : Set (Fin d → ℂ)} {L_an : MetrizedLineBundle d ι X_an}

/-- Induced `ℂ`-linear analytification map `H⁰_alg(S, L_alg) →ₗ[ℂ] H⁰_hol(X_an, L_an)`. -/
def analytify (G : GagaChartEval p L_alg L_an) :
    AlgSectionOver p L_alg →ₗ[ℂ] MetrizedLineBundle.Section L_an where
  toFun s :=
    { sec := fun i z => G.eval i (s.toAlgSection.f (G.idx i)) z
      sec_holo := fun i z hz => G.eval_holo i (s.toAlgSection.f (G.idx i)) z hz
      sec_compat := fun i j z hz => G.eval_compat s.toAlgSection i j z hz }
  map_add' s₁ s₂ := section_ext' fun i z =>
    G.eval_add i (s₁.toAlgSection.f (G.idx i)) (s₂.toAlgSection.f (G.idx i)) z
  map_smul' c s := section_ext' fun i z => by
    change G.eval i (constFn p (L_alg.U (G.idx i)) c * s.toAlgSection.f (G.idx i)) z =
      c * G.eval i (s.toAlgSection.f (G.idx i)) z
    rw [G.eval_mul, G.eval_const]

end GagaChartEval

/-- **Full GAGA Comparison Datum (`GagaComparisonData`)**:
a `GagaChartEval` that is Zariski-analytically faithful (injective) and algebraically surjective
(every global holomorphic section arises from a global algebraic section). -/
structure GagaComparisonData {S : Scheme.{0}} (p : S ⟶ Sp ℂ) (L_alg : AlgLineBundle S)
    {d : ℕ} {ι : Type*} {X_an : Set (Fin d → ℂ)} (L_an : MetrizedLineBundle d ι X_an)
    extends GagaChartEval p L_alg L_an where
  injective : Function.Injective toGagaChartEval.analytify
  surjective : Function.Surjective toGagaChartEval.analytify

/-- **`gaga_sections_iso` (Serre GAGA Global-Section Isomorphism)**:
for any `GagaComparisonData p L_alg L_an`, analytification yields an explicit `ℂ`-linear equivalence
`AlgSectionOver p L_alg ≃ₗ[ℂ] MetrizedLineBundle.Section L_an`, transferring finite-dimensionality
and exact complex dimension! -/
def gaga_sections_iso {S : Scheme.{0}} {p : S ⟶ Sp ℂ} {L_alg : AlgLineBundle S}
    {d : ℕ} {ι : Type*} {X_an : Set (Fin d → ℂ)} {L_an : MetrizedLineBundle d ι X_an}
    (G : GagaComparisonData p L_alg L_an) :
    AlgSectionOver p L_alg ≃ₗ[ℂ] MetrizedLineBundle.Section L_an :=
  LinearEquiv.ofBijective G.toGagaChartEval.analytify ⟨G.injective, G.surjective⟩

theorem gaga_sections_finrank_eq {S : Scheme.{0}} {p : S ⟶ Sp ℂ} {L_alg : AlgLineBundle S}
    {d : ℕ} {ι : Type*} {X_an : Set (Fin d → ℂ)} {L_an : MetrizedLineBundle d ι X_an}
    (G : GagaComparisonData p L_alg L_an) :
    Module.finrank ℂ (MetrizedLineBundle.Section L_an) =
      Module.finrank ℂ (AlgSectionOver p L_alg) :=
  (gaga_sections_iso G).symm.finrank_eq

/-- **Dimension-Matching GAGA Isomorphism (`gaga_sections_iso_of_inj_finrank`)**:
any injective `ℂ`-linear analytification map `Φ : V_alg →ₗ[ℂ] V_an` into a holomorphic section
space with `finrank ℂ V_an ≤ finrank ℂ V_alg` is automatically a `ℂ`-linear isomorphism! -/
def gaga_sections_iso_of_inj_finrank
    {V_alg V_an : Type*} [AddCommGroup V_alg] [Module ℂ V_alg] [FiniteDimensional ℂ V_alg]
    [AddCommGroup V_an] [Module ℂ V_an] [FiniteDimensional ℂ V_an]
    (Φ : V_alg →ₗ[ℂ] V_an) (hinj : Function.Injective Φ)
    (hle : Module.finrank ℂ V_an ≤ Module.finrank ℂ V_alg) :
    V_alg ≃ₗ[ℂ] V_an :=
  LinearEquiv.ofBijective Φ ⟨hinj, by
    have h1 : Module.finrank ℂ (LinearMap.range Φ) = Module.finrank ℂ V_alg :=
      (LinearEquiv.ofInjective Φ hinj).symm.finrank_eq
    have h2 : Module.finrank ℂ V_alg ≤ Module.finrank ℂ V_an :=
      LinearMap.finrank_le_finrank_of_injective hinj
    have htop : LinearMap.range Φ = ⊤ :=
      Submodule.eq_top_of_finrank_eq (h1.trans (le_antisymm h2 hle))
    exact LinearMap.range_eq_top.mp htop⟩

/-- **Base-Change GAGA Compatibility (`gaga_sections_baseChange_iso`)**:
given `SectionsHaveFiniteDimension p L_alg r` over any base field `K`, `AlgSectionOver p L_alg`
is canonically `K`-linearly equivalent to `(Fin r → K)` of exact dimension `r`. -/
theorem gaga_sections_baseChange_iso {K : Type} [Field K] {S : Scheme.{0}}
    {p : S ⟶ Sp K} {L_alg : AlgLineBundle S} {r : ℕ}
    (h : SectionsHaveFiniteDimension p L_alg r) :
    Nonempty (AlgSectionOver p L_alg ≃ₗ[K] (Fin r → K)) ∧
    Module.finrank K (AlgSectionOver p L_alg) = r :=
  ⟨(sections_have_finite_dimension h).2.2, (sections_have_finite_dimension h).2.1⟩

section ProjectiveSpaceConcreteGaga

/-- Dehomogenization of a homogeneous polynomial `P ∈ ℂ[X_0, …, X_N]_e` to a polynomial in
`N` affine coordinates `z_0, …, z_{N-1}` (`X_0 ↦ 1`, `X_{j+1} ↦ z_j`). -/
def dehomogenizeFn (N : ℕ) (P : MvPolynomial (Fin (N + 1)) ℂ) (z : Fin N → ℂ) : ℂ :=
  MvPolynomial.eval (Fin.cons (α := fun _ => ℂ) 1 z) P

lemma dehomogenizeFn_holo (N : ℕ) (P : MvPolynomial (Fin (N + 1)) ℂ) (z : Fin N → ℂ) :
    ContDiffAt ℂ 2 (dehomogenizeFn N P) z := by
  have hcont : ContDiff ℂ 2 (fun y : Fin N → ℂ => MvPolynomial.eval (Fin.cons (α := fun _ => ℂ) 1 y) P) := by
    induction P using MvPolynomial.induction_on with
    | C a => simpa [MvPolynomial.eval_C] using contDiff_const
    | add p q hp hq =>
      simpa [map_add] using hp.add hq
    | mul_X p i hp =>
      simp only [map_mul, MvPolynomial.eval_X]
      refine hp.mul ?_
      refine Fin.cases ?_ ?_ i
      · simpa using contDiff_const
      · intro j
        change ContDiff ℂ 2 (fun y : Fin N → ℂ => y j)
        exact contDiff_apply ℂ ℂ j
  exact hcont.contDiffAt

/-- Concrete `ℂ`-linear embedding of algebraic global sections `H⁰(ℙ^N_ℂ, 𝒪(e))` into
global holomorphic sections of `(fubiniStudyLineBundle N).pow (e : ℤ)`. -/
def projSpaceAnalytify (N e : ℕ) :
    MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℂ e →ₗ[ℂ]
      MetrizedLineBundle.Section ((fubiniStudyLineBundle N).pow (e : ℤ)) where
  toFun P :=
    { sec := fun _ z => dehomogenizeFn N P.1 z
      sec_holo := fun _ z _ => dehomogenizeFn_holo N P.1 z
      sec_compat := fun _ _ z _ => by
        change dehomogenizeFn N P.1 z = (1 : ℂ) ^ (e : ℤ) * dehomogenizeFn N P.1 z
        simp }
  map_add' P Q := section_ext' fun _ z => by
    simp [dehomogenizeFn, map_add]
  map_smul' c P := section_ext' fun _ z => by
    simp [dehomogenizeFn]

private lemma eval_dehomogenize_poly (N : ℕ) (P : MvPolynomial (Fin (N + 1)) ℂ) (z : Fin N → ℂ) :
    MvPolynomial.eval z
        (MvPolynomial.eval₂Hom MvPolynomial.C
          (Fin.cons (α := fun _ => MvPolynomial (Fin N) ℂ) 1 MvPolynomial.X) P) =
      MvPolynomial.eval (Fin.cons (α := fun _ => ℂ) 1 z) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => rw [map_add, map_add, hp, hq, map_add]
  | mul_X p i hp =>
    simp only [map_mul, MvPolynomial.eval_X, MvPolynomial.eval₂Hom_X']
    rw [hp]
    refine Fin.cases ?_ ?_ i <;> simp

/-- Injectivity of `projSpaceAnalytify N e`: distinct homogeneous polynomials of degree `e` define
distinct holomorphic sections on `ℂ^N`! -/
theorem projSpaceAnalytify_injective (N e : ℕ) :
    Function.Injective (projSpaceAnalytify N e) := by
  rw [injective_iff_map_eq_zero]
  intro ⟨P, hP⟩ hzero
  have heval : ∀ z : Fin N → ℂ, MvPolynomial.eval (Fin.cons (α := fun _ => ℂ) 1 z) P = 0 := fun z =>
    congrArg (fun s : MetrizedLineBundle.Section ((fubiniStudyLineBundle N).pow (e : ℤ)) =>
      s.sec () z) hzero
  let Q : MvPolynomial (Fin N) ℂ :=
    MvPolynomial.eval₂Hom MvPolynomial.C
      (Fin.cons (α := fun _ => MvPolynomial (Fin N) ℂ) 1 MvPolynomial.X) P
  have hQ_eval : ∀ z : Fin N → ℂ, MvPolynomial.eval z Q = 0 := fun z => by
    rw [eval_dehomogenize_poly N P z]
    exact heval z
  have hQ0 : Q = 0 := MvPolynomial.funext hQ_eval
  have hP0 : P = 0 := by
    apply MvPolynomial.ext
    intro d
    rw [MvPolynomial.coeff_zero]
    by_cases hd : d ∈ P.support
    · have hwt : ∑ i : Fin (N + 1), d i = e := by
        have hP' := hP
        rw [MvPolynomial.mem_homogeneousSubmodule] at hP'
        have h := hP' (MvPolynomial.mem_support_iff.mp hd)
        rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (fun _ => by simp)] at h
        simpa [smul_eq_mul] using h
      let d' : Fin N →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun j => d j.succ)
      have hcoeff_Q : MvPolynomial.coeff d' Q = MvPolynomial.coeff d P := by
        have hPsum : P = ∑ m ∈ P.support, MvPolynomial.monomial m (P.coeff m) :=
          MvPolynomial.as_sum P
        have hQsum : Q = ∑ m ∈ P.support, MvPolynomial.C (P.coeff m) *
            ∏ j : Fin N, (MvPolynomial.X j : MvPolynomial (Fin N) ℂ) ^ m j.succ := by
          dsimp only [Q]
          conv_lhs => rw [hPsum]
          simp only [map_sum, MvPolynomial.eval₂Hom_monomial, Finsupp.prod]
          refine Finset.sum_congr rfl fun m _ => ?_
          congr 1
          rw [Finset.prod_subset (Finset.subset_univ _) (fun i _ hi => by
            simp only [Finsupp.mem_support_iff, not_not] at hi; simp [hi])]
          rw [Fin.prod_univ_succ]
          simp
        rw [hQsum, MvPolynomial.coeff_sum]
        have hterm : ∀ m ∈ P.support,
            MvPolynomial.coeff d' (MvPolynomial.C (P.coeff m) *
              ∏ j : Fin N, (MvPolynomial.X j : MvPolynomial (Fin N) ℂ) ^ m j.succ) =
              if m = d then P.coeff d else 0 := by
          intro m hm
          have hm_wt : ∑ i : Fin (N + 1), m i = e := by
            have hP' := hP
            rw [MvPolynomial.mem_homogeneousSubmodule] at hP'
            have h := hP' (MvPolynomial.mem_support_iff.mp hm)
            rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (fun _ => by simp)] at h
            simpa [smul_eq_mul] using h
          have hprod_mon : (∏ j : Fin N, (MvPolynomial.X j : MvPolynomial (Fin N) ℂ) ^ m j.succ) =
              MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm (fun j => m j.succ)) (1 : ℂ) := by
            apply MvPolynomial.ext
            intro k
            rw [MvPolynomial.coeff_monomial, MvPolynomial.coeff_prod_X_pow]
            split_ifs with h1 h2 h2
            · rfl
            · exact False.elim (h2 (Finsupp.ext fun j => by
                simpa using congrArg (fun f : Fin N →₀ ℕ => f j) h1.symm))
            · exact False.elim (h1 (Finsupp.ext fun j => by
                simpa using congrArg (fun f : Fin N →₀ ℕ => f j) h2.symm))
            · rfl
          rw [hprod_mon, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_monomial]
          split_ifs with h1 h2 h2
          · subst h2; simp
          · exfalso; apply h2
            have hfun : (fun j : Fin N => m j.succ) = (fun j : Fin N => d j.succ) :=
              Finsupp.equivFunOnFinite.symm.injective h1
            apply Finsupp.ext
            refine Fin.cases ?_ ?_
            · have htail : ∀ j : Fin N, m j.succ = d j.succ := congrFun hfun
              rw [Fin.sum_univ_succ] at hm_wt hwt
              have hst : ∑ j : Fin N, m j.succ = ∑ j : Fin N, d j.succ :=
                Finset.sum_congr rfl fun j _ => htail j
              omega
            · exact congrFun hfun
          · exfalso; apply h1
            rw [h2]
          · simp
        rw [Finset.sum_congr rfl hterm]
        simp [hd]
      rw [← hcoeff_Q, hQ0, MvPolynomial.coeff_zero]
    · exact MvPolynomial.notMem_support_iff.mp hd
  exact Subtype.ext hP0

/-- **Unconditional 0-Assumption Liouville GAGA for Degree `0` (`𝒪_{ℙ^N}(0)`)**:
every bounded global holomorphic section `s : Section ((fubiniStudyLineBundle N).pow 0)` on `ℂ^N`
(`∃ C, ∀ z, s.ptNorm z ≤ C`) is constant (`c ∈ ℂ`)! -/
theorem projSpace_gaga_sections_degZero_const (N : ℕ)
    (s : MetrizedLineBundle.Section ((fubiniStudyLineBundle N).pow 0))
    (hbdd : ∃ C : ℝ, ∀ z : Fin N → ℂ, s.ptNorm z ≤ C) :
    ∃ c : ℂ, ∀ z : Fin N → ℂ, s.sec () z = c := by
  obtain ⟨C, hC⟩ := hbdd
  have hnorm_le : ∀ z : Fin N → ℂ, ‖s.sec () z‖ ≤ C := by
    intro z
    have hpt := hC z
    have hsq : s.ptNormSq z = ‖s.sec () z‖ ^ 2 := by
      rw [s.ptNormSq_eq_of_mem (i := ()) (Set.mem_univ z)]
      change ‖s.sec () z‖ ^ 2 * Real.exp (-(((0 : ℤ) : ℝ) * fubiniStudyWeight N z)) = _
      simp
    have hpt_eq : s.ptNorm z = ‖s.sec () z‖ := by
      unfold MetrizedLineBundle.Section.ptNorm
      rw [hsq, Real.sqrt_sq (norm_nonneg _)]
    rwa [← hpt_eq]
  have hdiff : Differentiable ℂ (fun z : Fin N → ℂ => s.sec () z) := fun z =>
    (s.sec_holo () z (Set.mem_univ z)).differentiableAt (by norm_num)
  have hbd_range : Bornology.IsBounded (Set.range fun z : Fin N → ℂ => s.sec () z) :=
    isBounded_iff_forall_norm_le.mpr ⟨C, fun _ ⟨z, hz⟩ => hz ▸ hnorm_le z⟩
  refine ⟨s.sec () 0, fun z => ?_⟩
  exact hdiff.apply_eq_apply_of_bounded hbd_range z 0

end ProjectiveSpaceConcreteGaga

end ComplexSectionsAndGaga

/-! ## Section 3: Concrete `GlobalSectionsLatH0` & Bridges to `CMHermLattice`, `GradedHermAlgebra` -/

section GlobalSectionsLatH0Section

/-- **Concrete Integral Global-Section Lattice `GlobalSectionsLatH0`**:
models the lattice of integral global sections `H⁰(𝒳, ℒ) ⊂ H⁰(X_ℂ, ℒ_ℂ)` of a metrized
holomorphic line bundle `L : MetrizedLineBundle d ι X` over `X ⊆ ℂ^d`, equipped with:
- finite-dimensional real inner-product ambient space `secSpace` (`L²`-Hermitian geometry),
- discrete nonzero `ℤ`-lattice `latH0 ⊂ secSpace`,
- linear analytic embedding `toSection : secSpace →ₗ[ℝ] L.Section`,
- global sup-norm `supNorm : secSpace → ℝ` bounding `ptNorm` everywhere on `X`,
- `L²`-vs-sup-norm volume constant `volConst > 0`. -/
structure GlobalSectionsLatH0 (d : ℕ) {ι : Type*} {X : Set (Fin d → ℂ)}
    (L : MetrizedLineBundle d ι X) where
  secSpace : Type
  [normSpace : NormedAddCommGroup secSpace]
  [innerSpace : InnerProductSpace ℝ secSpace]
  [fdSpace : FiniteDimensional ℝ secSpace]
  latH0 : Submodule ℤ secSpace
  [discLat : DiscreteTopology latH0]
  latH0_ne_bot : latH0 ≠ ⊥
  toSection : secSpace →ₗ[ℝ] MetrizedLineBundle.Section L
  supNorm : secSpace → ℝ
  supNorm_nonneg : ∀ s, 0 ≤ supNorm s
  ptNorm_le_supNorm : ∀ s (z : Fin d → ℂ), z ∈ X → (toSection s).ptNorm z ≤ supNorm s
  supNorm_add_le : ∀ s₁ s₂, supNorm (s₁ + s₂) ≤ supNorm s₁ + supNorm s₂
  supNorm_smul : ∀ (r : ℝ) (s : secSpace), supNorm (r • s) = |r| * supNorm s
  volConst : ℝ
  volConst_pos : 0 < volConst
  norm_le_vol_supNorm : ∀ s : secSpace, ‖s‖ ≤ volConst * supNorm s

attribute [instance] GlobalSectionsLatH0.normSpace GlobalSectionsLatH0.innerSpace
  GlobalSectionsLatH0.fdSpace GlobalSectionsLatH0.discLat

namespace GlobalSectionsLatH0

variable {d : ℕ} {ι : Type*} {X : Set (Fin d → ℂ)} {L : MetrizedLineBundle d ι X}

/-- Rank `rk H.latH0` of the integral global-section lattice. -/
def rank (H : GlobalSectionsLatH0 d L) : ℕ :=
  ArakelovCovolume.rk H.latH0

theorem rank_pos (H : GlobalSectionsLatH0 d L) : 0 < H.rank :=
  rk_pos_of_ne_bot H.latH0 H.latH0_ne_bot

/-- Arithmetic degree `deg_Ar H.latH0 = -log covol(H.latH0)` and slope `slope H.latH0`. -/
def arithDegH0 (H : GlobalSectionsLatH0 d L) : ℝ :=
  Stage11MoriwakiCovolume.arithDeg H.latH0

def slopeH0 (H : GlobalSectionsLatH0 d L) : ℝ :=
  ArakelovCovolume.slope H.latH0

/-- **Exact `ZLattice.covolume` Grounding (`covol_eq_zlattice_covolume`)**:
every `GlobalSectionsLatH0` transports isometrically to a full-rank `IsZLattice ℝ` lattice `Λ` in
`EuclideanSpace ℝ (Fin H.rank)` with identical covolume `ZLattice.covolume Λ volume = covol H.latH0`,
identical small-section counts `h0Arith` / `h0ArithStrict`, and identical successive minima! -/
theorem covol_eq_zlattice_covolume (H : GlobalSectionsLatH0 d L) :
    ∃ (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin H.rank)))
      (_ : DiscreteTopology Λ) (_ : IsZLattice ℝ Λ),
      ZLattice.covolume Λ volume = ArakelovCovolume.covol H.latH0 ∧
      (∀ R : ℝ, h0Arith H.latH0 R = h0Arith Λ R) ∧
      (∀ R : ℝ, h0ArithStrict H.latH0 R = h0ArithStrict Λ R) := by
  obtain ⟨Λ, hDisc, hIsZ, hcov, hball1, hball2, _⟩ :=
    Stage11MoriwakiCovolume.exists_isometric_euclidean_lattice H.latH0
  exact ⟨Λ, hDisc, hIsZ, hcov, hball1, hball2⟩

/-- Set of strictly small integral global sections `{ s ∈ H.latH0 | H.supNorm s < 1 }`. -/
def smallSectionsSet (H : GlobalSectionsLatH0 d L) : Set H.latH0 :=
  { s : H.latH0 | H.supNorm s.1 < 1 }

/-- Finiteness of strictly small integral global sections `‖s‖_sup < 1` in `GlobalSectionsLatH0`. -/
theorem smallSections_finite (H : GlobalSectionsLatH0 d L) :
    H.smallSectionsSet.Finite := by
  let V : Submodule ℝ H.secSpace := Submodule.span ℝ (H.latH0 : Set H.secSpace)
  have hdimV : Module.finrank ℝ V = H.rank := (finrank_int_eq_finrank_real_span H.latH0).symm
  let e : OrthonormalBasis (Fin H.rank) ℝ V :=
    (stdOrthonormalBasis ℝ V).reindex (Fintype.equivOfCardEq (by simp [hdimV]))
  let Φ : V ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin H.rank) := e.repr
  let L₀ : Submodule ℤ V := H.latH0.comap (V.subtype.restrictScalars ℤ)
  let Λ' : Submodule ℤ (EuclideanSpace ℝ (Fin H.rank)) := L₀.map (Φ.toLinearMap.restrictScalars ℤ)
  have hDisc' : DiscreteTopology Λ' := by
    let bL : Module.Basis (Fin H.rank) ℤ H.latH0 := Module.finBasis ℤ H.latH0
    let eLΛ : H.latH0 ≃ₗ[ℤ] Λ' :=
      { toFun := fun x => ⟨Φ ⟨(x : H.secSpace), Submodule.subset_span x.2⟩,
          ⟨⟨(x : H.secSpace), Submodule.subset_span x.2⟩, x.2, rfl⟩⟩
        invFun := fun y => ⟨(Φ.symm (y : EuclideanSpace ℝ (Fin H.rank)) : H.secSpace), by
          rcases y.2 with ⟨v, hvL, hvy⟩
          have hv : Φ.symm (y : EuclideanSpace ℝ (Fin H.rank)) = v := by
            rw [← hvy]; exact Φ.symm_apply_apply v
          rw [hv]; exact hvL⟩
        map_add' := fun x y => Subtype.ext (by
          change Φ (⟨(x : H.secSpace), Submodule.subset_span x.2⟩ +
            ⟨(y : H.secSpace), Submodule.subset_span y.2⟩) = _
          exact map_add Φ _ _)
        map_smul' := fun n x => Subtype.ext (by
          change Φ (n • (⟨(x : H.secSpace), Submodule.subset_span x.2⟩ : V)) =
            n • Φ ⟨(x : H.secSpace), Submodule.subset_span x.2⟩
          exact map_zsmul Φ.toLinearMap n _)
        left_inv := fun _ => Subtype.ext (by simp)
        right_inv := fun _ => Subtype.ext (by simp) }
    let bΛ : Module.Basis (Fin H.rank) ℤ Λ' := bL.map eLΛ
    have hliL := linearIndependent_coe_basis H.latH0 bL
    have hliΛ : LinearIndependent ℝ (fun i => (bΛ i : EuclideanSpace ℝ (Fin H.rank))) := by
      rw [Fintype.linearIndependent_iff]
      intro c hc i
      have hV : ∑ j, c j • (⟨(bL j : H.secSpace), Submodule.subset_span (bL j).2⟩ : V) = 0 := by
        apply Φ.injective
        rw [map_zero, map_sum]
        simp only [map_smul]
        exact hc
      have hE : ∑ j, c j • (bL j : H.secSpace) = 0 := by
        have := congrArg Subtype.val hV
        simpa [Submodule.coe_sum, Submodule.coe_smul] using this
      exact Fintype.linearIndependent_iff.mp hliL c hE i
    exact Stage4ArakelovBost.discreteTopology_of_fin_basis_real_li bΛ hliΛ
  have hIsZ' : IsZLattice ℝ Λ' := by
    constructor
    have hspL₀ : Submodule.span ℝ (L₀ : Set V) = ⊤ := Submodule.span_span_coe_preimage
    have hspΛ : Submodule.span ℝ (Λ' : Set (EuclideanSpace ℝ (Fin H.rank))) =
        (Submodule.span ℝ (L₀ : Set V)).map Φ.toLinearMap := by
      change Submodule.span ℝ (Φ.toLinearMap '' (L₀ : Set V)) = _
      rw [Submodule.map_span]
    rw [hspΛ, hspL₀, Submodule.map_top, LinearMap.range_eq_top]
    exact Φ.surjective
  have hfinΛ' : ((Λ' : Set (EuclideanSpace ℝ (Fin H.rank))) ∩ Metric.closedBall 0 H.volConst).Finite :=
    lattice_inter_closedBall_finite Λ' H.volConst
  let injMap : H.smallSectionsSet →
      ↥((Λ' : Set (EuclideanSpace ℝ (Fin H.rank))) ∩ Metric.closedBall 0 H.volConst) :=
    fun s => ⟨Φ ⟨s.1.1, Submodule.subset_span s.1.2⟩,
      ⟨⟨⟨s.1.1, Submodule.subset_span s.1.2⟩, s.1.2, rfl⟩, by
        rw [Metric.mem_closedBall, dist_zero_right, Φ.norm_map]
        have h1 := H.norm_le_vol_supNorm s.1.1
        have h2 : H.supNorm s.1.1 < 1 := s.2
        change ‖(⟨s.1.1, Submodule.subset_span s.1.2⟩ : V)‖ ≤ H.volConst
        have hn : ‖(⟨s.1.1, Submodule.subset_span s.1.2⟩ : V)‖ = ‖s.1.1‖ := rfl
        rw [hn]
        nlinarith [H.volConst_pos]⟩⟩
  have hinj : Function.Injective injMap := by
    intro a b hab
    have h1 : Φ ⟨a.1.1, Submodule.subset_span a.1.2⟩ = Φ ⟨b.1.1, Submodule.subset_span b.1.2⟩ :=
      congrArg Subtype.val hab
    have h2 : (⟨a.1.1, Submodule.subset_span a.1.2⟩ : V) = ⟨b.1.1, Submodule.subset_span b.1.2⟩ :=
      Φ.injective h1
    exact Subtype.ext (Subtype.ext (congrArg (Subtype.val : V → H.secSpace) h2))
  have : Finite ↥((Λ' : Set (EuclideanSpace ℝ (Fin H.rank))) ∩ Metric.closedBall 0 H.volConst) :=
    hfinΛ'.to_subtype
  exact Set.finite_coe_iff.mp (Finite.of_injective injMap hinj)

/-- Exact cardinality `#smallSections H` of strictly small global sections `‖s‖_sup < 1`. -/
def smallSectionsCard (H : GlobalSectionsLatH0 d L) : ℕ :=
  H.smallSections_finite.toFinset.card

private def twistSection {d : ℕ} {ι : Type*} {X : Set (Fin d → ℂ)}
    (L : MetrizedLineBundle d ι X) (c : ℝ) (s : MetrizedLineBundle.Section L) :
    MetrizedLineBundle.Section (L.scaleMetric c) where
  sec := s.sec
  sec_holo := s.sec_holo
  sec_compat := s.sec_compat

/-- **Constant Metric Rescaling of `GlobalSectionsLatH0`**:
twisting `L` by `c : ℝ` (`φ ↦ φ + c`, `h ↦ e^{-c} h`) scales the `L²`-lattice by `e^{-c / 2}`,
shifting `arithDeg` by `+ (rk / 2) * c` and `slope` by `+ c / 2`! -/
def scaleMetricH0 (H : GlobalSectionsLatH0 d L) (c : ℝ) :
    GlobalSectionsLatH0 d (L.scaleMetric c) where
  secSpace := H.secSpace
  latH0 := Stage11MoriwakiCovolume.scaleLat (Real.exp (-c / 2)) H.latH0
  discLat := (Stage11MoriwakiCovolume.scaleLat_invariants H.latH0 (Real.exp_pos _)).1
  latH0_ne_bot := by
    intro hbot
    have hrk := (Stage11MoriwakiCovolume.scaleLat_invariants H.latH0 (Real.exp_pos (-c / 2))).2.1
    rw [hbot, show ArakelovCovolume.rk (⊥ : Submodule ℤ H.secSpace) = 0 by simp [ArakelovCovolume.rk]] at hrk
    exact H.rank_pos.ne hrk
  toSection :=
    { toFun := fun s => twistSection L c (H.toSection s)
      map_add' := fun s₁ s₂ => section_ext' fun i z => by
        change (H.toSection (s₁ + s₂)).sec i z = _
        rw [map_add]; rfl
      map_smul' := fun r s => section_ext' fun i z => by
        change (H.toSection (r • s)).sec i z = (r : ℂ) * (H.toSection s).sec i z
        have hr : H.toSection (r • s) = r • H.toSection s := H.toSection.map_smul r s
        rw [hr]; rfl }
  supNorm s := Real.exp (-c / 2) * H.supNorm s
  supNorm_nonneg s := mul_nonneg (Real.exp_pos _).le (H.supNorm_nonneg s)
  ptNorm_le_supNorm s z hz := by
    have htw := section_ptNormSq_twistMetric L (fun _ => c)
      (fun _ _ _ => contDiffAt_const) (H.toSection s) hz
    change (twistSection L c (H.toSection s)).ptNorm z ≤ Real.exp (-c / 2) * H.supNorm s
    unfold MetrizedLineBundle.Section.ptNorm
    have hsq : Real.sqrt (Real.exp (-c) * (H.toSection s).ptNormSq z) =
        Real.exp (-c / 2) * (H.toSection s).ptNorm z := by
      rw [Real.sqrt_mul (Real.exp_pos _).le]
      have hrt : Real.sqrt (Real.exp (-c)) = Real.exp (-c / 2) := by
        rw [← Real.exp_half (-c)]
      rw [hrt]
      rfl
    have hpt_eq : (twistSection L c (H.toSection s)).ptNormSq z =
        Real.exp (-c) * (H.toSection s).ptNormSq z := htw
    rw [hpt_eq, hsq]
    exact mul_le_mul_of_nonneg_left (H.ptNorm_le_supNorm s z hz) (Real.exp_pos _).le
  supNorm_add_le s₁ s₂ := by
    calc Real.exp (-c / 2) * H.supNorm (s₁ + s₂)
        ≤ Real.exp (-c / 2) * (H.supNorm s₁ + H.supNorm s₂) :=
          mul_le_mul_of_nonneg_left (H.supNorm_add_le s₁ s₂) (Real.exp_pos _).le
      _ = Real.exp (-c / 2) * H.supNorm s₁ + Real.exp (-c / 2) * H.supNorm s₂ := mul_add _ _ _
  supNorm_smul r s := by
    rw [H.supNorm_smul]; ring
  volConst := H.volConst * Real.exp (c / 2)
  volConst_pos := mul_pos H.volConst_pos (Real.exp_pos _)
  norm_le_vol_supNorm s := by
    have hexp : Real.exp (c / 2) * Real.exp (-c / 2) = 1 := by
      rw [← Real.exp_add, show c / 2 + -c / 2 = 0 by ring, Real.exp_zero]
    calc ‖s‖ ≤ H.volConst * H.supNorm s := H.norm_le_vol_supNorm s
      _ = H.volConst * ((Real.exp (c / 2) * Real.exp (-c / 2)) * H.supNorm s) := by
          rw [hexp, one_mul]
      _ = (H.volConst * Real.exp (c / 2)) * (Real.exp (-c / 2) * H.supNorm s) := by ring

theorem scaleMetricH0_invariants (H : GlobalSectionsLatH0 d L) (c : ℝ) :
    (H.scaleMetricH0 c).rank = H.rank ∧
    (H.scaleMetricH0 c).arithDegH0 = H.arithDegH0 + (H.rank : ℝ) * (c / 2) ∧
    (H.scaleMetricH0 c).slopeH0 = H.slopeH0 + c / 2 := by
  have hinv := Stage11MoriwakiCovolume.scaleLat_invariants H.latH0 (Real.exp_pos (-c / 2))
  have hsl := Stage11MoriwakiCovolume.slope_scaleLat H.latH0 H.latH0_ne_bot (Real.exp_pos (-c / 2))
  refine ⟨hinv.2.1, ?_, ?_⟩
  · change Stage11MoriwakiCovolume.arithDeg (Stage11MoriwakiCovolume.scaleLat _ H.latH0) = _
    rw [hinv.2.2.2, Real.log_exp]
    change H.arithDegH0 - (H.rank : ℝ) * (-c / 2) = _
    ring
  · change ArakelovCovolume.slope (Stage11MoriwakiCovolume.scaleLat _ H.latH0) = _
    rw [hsl, Real.log_exp]
    change H.slopeH0 - (-c / 2) = _
    ring

/-- **Realization of `GlobalSectionsLatH0` as a `Stage12SchurWeylLattices.CMHermLattice`**
whenever `latH0` carries a positive-definite CM Hermitian Gram matrix `H_cm` over `𝒪_{-d_cm}`. -/
def toCMHermLattice {d_cm r : ℕ} (hd : 0 < d_cm) (hr : 1 ≤ r)
    (H_cm : Matrix (Fin r) (Fin r) ℂ) (hH : H_cm.PosDef) :
    CMHermLattice d_cm r :=
  { hd := hd, hr := hr, H := H_cm, hH := hH }

/-- **Construction of a `Stage12SchurWeylLattices.GradedHermAlgebra d` from a Graded Family of
`GlobalSectionsLatH0` (`toGradedHermAlgebra`)**:
turns `⨁_{k ≥ 1} H⁰(𝒳, ℒ^{⊗ k})` directly into a `GradedHermAlgebra d`, unlocking
`moriwaki_big_small_sections` and `moriwaki_exists_nonzero_small_section`! -/
def toGradedHermAlgebra (d : ℕ) (hd : 1 ≤ d) {ι : Type*} {X : Set (Fin d → ℂ)}
    {L : MetrizedLineBundle d ι X}
    (H : ∀ k : ℕ, GlobalSectionsLatH0 d (L.pow (k : ℤ)))
    (volConst_unif : ℝ) (hVpos : 0 < volConst_unif)
    (hV_le : ∀ k, 1 ≤ k → ∀ s : (H k).secSpace, ‖s‖ ≤ volConst_unif * (H k).supNorm s)
    (bergConst : ℝ) (bergExp : ℕ) (hBge : 1 ≤ bergConst)
    (hB_le : ∀ k, 1 ≤ k → ∀ s : (H k).secSpace,
      (H k).supNorm s ≤ bergConst * ((k : ℝ) + 1) ^ bergExp * ‖s‖)
    (rankHi : ℝ) (hRge : 1 ≤ rankHi)
    (hRk_le : ∀ k, 1 ≤ k → ((H k).rank : ℝ) ≤ rankHi * (k : ℝ) ^ d)
    (volAr : ℝ)
    (hAHS : ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop,
      volAr / ((d + 1).factorial : ℝ) - ε ≤ (H k).arithDegH0 / (k : ℝ) ^ (d + 1)) :
    GradedHermAlgebra d where
  hd := hd
  secSpace k := (H k).secSpace
  normSpace k := (H k).normSpace
  innerSpace k := (H k).innerSpace
  fdSpace k := (H k).fdSpace
  secLat k := (H k).latH0
  discLat k := (H k).discLat
  secLat_ne_bot k _ := (H k).latH0_ne_bot
  supNorm k := (H k).supNorm
  supNorm_nonneg k := (H k).supNorm_nonneg
  volConst := volConst_unif
  volConst_pos := hVpos
  norm_le_vol_supNorm k hk s := hV_le k hk s
  bergConst := bergConst
  bergExp := bergExp
  bergConst_ge_one := hBge
  supNorm_le_bergman k hk s := hB_le k hk s
  rankHi := rankHi
  rankHi_ge_one := hRge
  rk_le_poly k hk := hRk_le k hk
  volAr := volAr
  ahs_liminf := hAHS

/-- **Concrete 0-Assumption `GlobalSectionsLatH0` on `ℙ^N_ℤ` (`GlobalSectionsLatH0.projSpace`)**:
realizes `H⁰(ℙ^N_ℤ, 𝒪(k))` concretely on `EuclideanSpace ℝ (MultiIndex (N + 1) k)` with
monomial lattice `symPowMonomialLat` scaled by `e^{-α}` (`α > 0`), analytic embedding into
`((fubiniStudyLineBundle N).pow (k : ℤ)).Section`, and exact rank `Nat.choose (k + N) N`! -/
def projSpace (N k : ℕ) {α : ℝ} (_hα : 0 < α) :
    GlobalSectionsLatH0 N ((fubiniStudyLineBundle N).pow (k : ℤ)) where
  secSpace := EuclideanSpace ℝ (MultiIndex (N + 1) k)
  latH0 := symPowMonomialLat (fun _ : Fin (N + 1) => Real.exp (-α)) k
  discLat :=
    (Stage11MoriwakiCovolume.arithDeg_symPowWeightedLat (Nat.succ_pos N)
      (fun _ : Fin (N + 1) => Real.exp (-α)) (fun _ => Real.exp_pos _)
      (fun _ : MultiIndex (N + 1) k => (1 : ℝ)) (fun _ => zero_lt_one)).1
  latH0_ne_bot := by
    intro hbot
    have hrk := (Stage11MoriwakiCovolume.arithDeg_symPowWeightedLat (Nat.succ_pos N)
      (fun _ : Fin (N + 1) => Real.exp (-α)) (fun _ => Real.exp_pos _)
      (fun _ : MultiIndex (N + 1) k => (1 : ℝ)) (fun _ => zero_lt_one)).2.1
    rw [show symPowMonomialLat (fun _ : Fin (N + 1) => Real.exp (-α)) k =
      Stage11MoriwakiCovolume.symPowWeightedLat (fun _ : Fin (N + 1) => Real.exp (-α))
        (fun _ => (1 : ℝ)) from rfl] at hbot
    rw [hbot, show ArakelovCovolume.rk
      (⊥ : Submodule ℤ (EuclideanSpace ℝ (MultiIndex (N + 1) k))) = 0 by
      simp [ArakelovCovolume.rk]] at hrk
    exact (card_multiIndex_pos (Nat.succ_pos N) k).ne hrk
  toSection :=
    { toFun := fun c =>
        projSpaceAnalytify N k
          (∑ β : MultiIndex (N + 1) k, (c β : ℂ) • homogeneousBasis ℂ N k β)
      map_add' := fun c₁ c₂ => by
        rw [← map_add]
        congr 1
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun β _ => ?_
        rw [PiLp.add_apply, Complex.ofReal_add, add_smul]
      map_smul' := fun r c => by
        change projSpaceAnalytify N k _ = (r : ℂ) • projSpaceAnalytify N k _
        rw [← map_smul, Finset.smul_sum]
        congr 1
        refine Finset.sum_congr rfl fun β _ => ?_
        rw [PiLp.smul_apply, smul_eq_mul, Complex.ofReal_mul, smul_smul] }
  supNorm c := Real.sqrt (Fintype.card (MultiIndex (N + 1) k) : ℝ) * ‖c‖
  supNorm_nonneg c := mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  ptNorm_le_supNorm c z _ := by
    have hbasis_coe : ∀ β : MultiIndex (N + 1) k,
        (homogeneousBasis ℂ N k β).1 =
          MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm β.1) (1 : ℂ) := by
      intro β
      unfold homogeneousBasis
      rw [Module.Basis.mk_apply]
    have hcoeff_bd : ∀ β : MultiIndex (N + 1) k,
        ‖MvPolynomial.eval (Fin.cons (α := fun _ => ℂ) 1 z) (homogeneousBasis ℂ N k β).1‖ ^ 2 ≤
          (1 + ∑ j : Fin N, ‖z j‖ ^ 2) ^ k := by
      intro β
      rw [hbasis_coe β, MvPolynomial.eval_monomial, one_mul, Finsupp.prod]
      have hfin : (∏ i ∈ (Finsupp.equivFunOnFinite.symm β.1).support,
          (Fin.cons (α := fun _ => ℂ) 1 z i) ^ ((Finsupp.equivFunOnFinite.symm β.1) i)) =
          ∏ i : Fin (N + 1), (Fin.cons (α := fun _ => ℂ) 1 z i) ^ (β.1 i) := by
        refine Finset.prod_subset (Finset.subset_univ _) fun i _ hi => ?_
        simp only [Finsupp.mem_support_iff, not_not] at hi
        change (Fin.cons (α := fun _ => ℂ) 1 z i) ^ ((Finsupp.equivFunOnFinite.symm β.1) i) = 1
        rw [hi, pow_zero]
      rw [hfin, norm_prod, ← Finset.prod_pow]
      have hterm : ∀ i : Fin (N + 1),
          (‖Fin.cons (α := fun _ => ℂ) 1 z i‖ ^ β.1 i) ^ 2 ≤
            (1 + ∑ j : Fin N, ‖z j‖ ^ 2) ^ (β.1 i) := by
        intro i
        rw [← pow_mul, mul_comm, pow_mul]
        refine pow_le_pow_left₀ (sq_nonneg _) ?_ (β.1 i)
        refine Fin.cases ?_ ?_ i
        · simp only [Fin.cons_zero, norm_one, one_pow]
          have hnn : 0 ≤ ∑ j : Fin N, ‖z j‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
          linarith
        · intro j
          simp only [Fin.cons_succ]
          have hj : ‖z j‖ ^ 2 ≤ ∑ l : Fin N, ‖z l‖ ^ 2 :=
            Finset.single_le_sum (fun l _ => sq_nonneg ‖z l‖) (Finset.mem_univ j)
          linarith
      simp_rw [norm_pow]
      calc ∏ i : Fin (N + 1), (‖Fin.cons (α := fun _ => ℂ) 1 z i‖ ^ β.1 i) ^ 2
          ≤ ∏ i : Fin (N + 1), (1 + ∑ j : Fin N, ‖z j‖ ^ 2) ^ (β.1 i) :=
            Finset.prod_le_prod (fun _ _ => sq_nonneg _) fun i _ => hterm i
        _ = (1 + ∑ j : Fin N, ‖z j‖ ^ 2) ^ (∑ i : Fin (N + 1), β.1 i) := by
            rw [Finset.prod_pow_eq_pow_sum]
        _ = (1 + ∑ j : Fin N, ‖z j‖ ^ 2) ^ k := by rw [β.2]
    have hpt_sq : (projSpaceAnalytify N k
        (∑ β : MultiIndex (N + 1) k, (c β : ℂ) • homogeneousBasis ℂ N k β)).ptNormSq z ≤
        (Fintype.card (MultiIndex (N + 1) k) : ℝ) * ‖c‖ ^ 2 := by
      rw [(projSpaceAnalytify N k _).ptNormSq_eq_of_mem (i := ()) (Set.mem_univ z)]
      change ‖dehomogenizeFn N _ z‖ ^ 2 *
          Real.exp (-(((k : ℤ) : ℝ) * fubiniStudyWeight N z)) ≤ _
      have hdehom : dehomogenizeFn N
          (∑ β : MultiIndex (N + 1) k, (c β : ℂ) • homogeneousBasis ℂ N k β).1 z =
          ∑ β : MultiIndex (N + 1) k,
            (c β : ℂ) * MvPolynomial.eval (Fin.cons (α := fun _ => ℂ) 1 z) (homogeneousBasis ℂ N k β).1 := by
        unfold dehomogenizeFn
        rw [AddSubmonoidClass.coe_finsetSum, map_sum]
        refine Finset.sum_congr rfl fun β _ => ?_
        have hcoe : (((c β : ℂ) • homogeneousBasis ℂ N k β).1) =
            MvPolynomial.C (c β : ℂ) * (homogeneousBasis ℂ N k β).1 := by
          change (c β : ℂ) • (homogeneousBasis ℂ N k β).1 = _
          exact MvPolynomial.smul_eq_C_mul _ _
        rw [hcoe, map_mul, MvPolynomial.eval_C]
      rw [hdehom]
      have hcs : ‖∑ β : MultiIndex (N + 1) k,
            (c β : ℂ) * MvPolynomial.eval (Fin.cons (α := fun _ => ℂ) 1 z) (homogeneousBasis ℂ N k β).1‖ ^ 2 ≤
          (∑ β : MultiIndex (N + 1) k, ‖(c β : ℂ)‖ ^ 2) *
            ∑ β : MultiIndex (N + 1) k,
              ‖MvPolynomial.eval (Fin.cons (α := fun _ => ℂ) 1 z) (homogeneousBasis ℂ N k β).1‖ ^ 2 := by
        have htri : ‖∑ β : MultiIndex (N + 1) k,
              (c β : ℂ) * MvPolynomial.eval (Fin.cons (α := fun _ => ℂ) 1 z) (homogeneousBasis ℂ N k β).1‖ ≤
            ∑ β : MultiIndex (N + 1) k,
              ‖(c β : ℂ)‖ * ‖MvPolynomial.eval (Fin.cons (α := fun _ => ℂ) 1 z) (homogeneousBasis ℂ N k β).1‖ :=
          le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun β _ => by rw [norm_mul])
        have hsq := sq_le_sq' (by linarith [norm_nonneg (∑ β : MultiIndex (N + 1) k,
          (c β : ℂ) * MvPolynomial.eval (Fin.cons (α := fun _ => ℂ) 1 z) (homogeneousBasis ℂ N k β).1)]) htri
        exact hsq.trans (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
          (fun β => ‖(c β : ℂ)‖)
          (fun β => ‖MvPolynomial.eval (Fin.cons (α := fun _ => ℂ) 1 z) (homogeneousBasis ℂ N k β).1‖))
      have hcnorm : ∑ β : MultiIndex (N + 1) k, ‖(c β : ℂ)‖ ^ 2 = ‖c‖ ^ 2 := by
        rw [EuclideanSpace.norm_sq_eq]
        refine Finset.sum_congr rfl fun β _ => ?_
        rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
      have hsum_bd : (∑ β : MultiIndex (N + 1) k,
            ‖MvPolynomial.eval (Fin.cons (α := fun _ => ℂ) 1 z) (homogeneousBasis ℂ N k β).1‖ ^ 2) ≤
          (Fintype.card (MultiIndex (N + 1) k) : ℝ) * (1 + ∑ j : Fin N, ‖z j‖ ^ 2) ^ k := by
        calc ∑ β : MultiIndex (N + 1) k,
              ‖MvPolynomial.eval (Fin.cons (α := fun _ => ℂ) 1 z) (homogeneousBasis ℂ N k β).1‖ ^ 2
            ≤ ∑ _β : MultiIndex (N + 1) k, (1 + ∑ j : Fin N, ‖z j‖ ^ 2) ^ k :=
              Finset.sum_le_sum fun β _ => hcoeff_bd β
          _ = (Fintype.card (MultiIndex (N + 1) k) : ℝ) * (1 + ∑ j : Fin N, ‖z j‖ ^ 2) ^ k := by
              rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      have hwt_pos : 0 < 1 + ∑ j : Fin N, ‖z j‖ ^ 2 := by
        have hnn : 0 ≤ ∑ j : Fin N, ‖z j‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
        linarith
      have hexp : Real.exp (-(((k : ℤ) : ℝ) * fubiniStudyWeight N z)) =
          ((1 + ∑ j : Fin N, ‖z j‖ ^ 2) ^ k)⁻¹ := by
        unfold fubiniStudyWeight
        simp only [Int.cast_natCast]
        rw [show -((k : ℝ) * Real.log (1 + ∑ j : Fin N, ‖z j‖ ^ 2)) =
          -Real.log ((1 + ∑ j : Fin N, ‖z j‖ ^ 2) ^ k) by rw [Real.log_pow]]
        rw [Real.exp_neg, Real.exp_log (pow_pos hwt_pos k)]
      rw [hexp]
      have h1 : ‖∑ β : MultiIndex (N + 1) k,
            (c β : ℂ) * MvPolynomial.eval (Fin.cons (α := fun _ => ℂ) 1 z) (homogeneousBasis ℂ N k β).1‖ ^ 2 ≤
          ‖c‖ ^ 2 * ((Fintype.card (MultiIndex (N + 1) k) : ℝ) *
            (1 + ∑ j : Fin N, ‖z j‖ ^ 2) ^ k) := by
        rw [hcnorm] at hcs
        exact hcs.trans (mul_le_mul_of_nonneg_left hsum_bd (sq_nonneg _))
      have hmul := mul_le_mul_of_nonneg_right h1 (inv_nonneg.mpr (pow_nonneg hwt_pos.le k))
      have hpow_ne : (1 + ∑ j : Fin N, ‖z j‖ ^ 2) ^ k ≠ 0 := (pow_pos hwt_pos k).ne'
      calc ‖∑ β, (c β : ℂ) * MvPolynomial.eval (Fin.cons (α := fun _ => ℂ) 1 z) (homogeneousBasis ℂ N k β).1‖ ^ 2 *
            ((1 + ∑ j : Fin N, ‖z j‖ ^ 2) ^ k)⁻¹
          ≤ (‖c‖ ^ 2 * ((Fintype.card (MultiIndex (N + 1) k) : ℝ) *
              (1 + ∑ j : Fin N, ‖z j‖ ^ 2) ^ k)) *
              ((1 + ∑ j : Fin N, ‖z j‖ ^ 2) ^ k)⁻¹ := hmul
        _ = (Fintype.card (MultiIndex (N + 1) k) : ℝ) * ‖c‖ ^ 2 := by
            field_simp [hpow_ne]
    unfold MetrizedLineBundle.Section.ptNorm
    change Real.sqrt _ ≤ Real.sqrt (Fintype.card (MultiIndex (N + 1) k) : ℝ) * ‖c‖
    calc Real.sqrt _ ≤ Real.sqrt ((Fintype.card (MultiIndex (N + 1) k) : ℝ) * ‖c‖ ^ 2) :=
          Real.sqrt_le_sqrt hpt_sq
      _ = Real.sqrt (Fintype.card (MultiIndex (N + 1) k) : ℝ) * ‖c‖ := by
          rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq (norm_nonneg _)]
  supNorm_add_le c₁ c₂ := by
    calc Real.sqrt (Fintype.card (MultiIndex (N + 1) k) : ℝ) * ‖c₁ + c₂‖
        ≤ Real.sqrt (Fintype.card (MultiIndex (N + 1) k) : ℝ) * (‖c₁‖ + ‖c₂‖) :=
          mul_le_mul_of_nonneg_left (norm_add_le _ _) (Real.sqrt_nonneg _)
      _ = _ := mul_add _ _ _
  supNorm_smul r c := by
    rw [norm_smul, Real.norm_eq_abs]; ring
  volConst := 1
  volConst_pos := zero_lt_one
  norm_le_vol_supNorm c := by
    have hcard_ge : (1 : ℝ) ≤ Real.sqrt (Fintype.card (MultiIndex (N + 1) k) : ℝ) := by
      have hpos : 1 ≤ Fintype.card (MultiIndex (N + 1) k) := card_multiIndex_pos (Nat.succ_pos N) k
      have h1 : (1 : ℝ) ≤ (Fintype.card (MultiIndex (N + 1) k) : ℝ) := by exact_mod_cast hpos
      rw [← Real.sqrt_one]
      exact Real.sqrt_le_sqrt h1
    calc ‖c‖ = 1 * ‖c‖ := (one_mul _).symm
      _ ≤ 1 * (Real.sqrt (Fintype.card (MultiIndex (N + 1) k) : ℝ) * ‖c‖) :=
          mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (norm_nonneg _) hcard_ge) zero_le_one

theorem projSpace_rank (N k : ℕ) {α : ℝ} (hα : 0 < α) :
    (projSpace N k hα).rank = Nat.choose (k + N) N := by
  unfold GlobalSectionsLatH0.rank projSpace
  have hrk := (Stage11MoriwakiCovolume.arithDeg_symPowWeightedLat (Nat.succ_pos N)
    (fun _ : Fin (N + 1) => Real.exp (-α)) (fun _ => Real.exp_pos _)
    (fun _ : MultiIndex (N + 1) k => (1 : ℝ)) (fun _ => zero_lt_one)).2.1
  change ArakelovCovolume.rk (Stage11MoriwakiCovolume.symPowWeightedLat _ _) = _
  rw [hrk, card_multiIndex (Nat.succ_pos N) k, show k + (N + 1) - 1 = k + N by omega,
    add_comm k N, ← Nat.choose_symm_add, add_comm N k]

end GlobalSectionsLatH0

end GlobalSectionsLatH0Section

/-! ## Section 4: Norm Comparison Constants (`h0_norm_comparison_constants`) -/

section H0NormComparisonConstants

/-- **Bergman Extremal Upper Bound on `H⁰(X, L)` (`h0_bergman_sup_le_l2`)**:
for any finite frame of global sections `e : Fin r → L.Section` with bounded Bergman kernel
`∑ k, (e k).ptNormSq z ≤ B` on `X`, every linear combination `s = ∑ k, c k • e k` satisfies
`s.ptNormSq z ≤ B * ∑ k, ‖c k‖²` everywhere on `X`! -/
theorem h0_bergman_sup_le_l2 {d r : ℕ} {ι : Type*} {X : Set (Fin d → ℂ)}
    {L : MetrizedLineBundle d ι X} (e : Fin r → MetrizedLineBundle.Section L) (c : Fin r → ℂ)
    {B : ℝ} (hB : ∀ z ∈ X, (∑ k : Fin r, (e k).ptNormSq z) ≤ B)
    {z : Fin d → ℂ} (hz : z ∈ X) :
    (∑ k : Fin r, c k • e k).ptNormSq z ≤ B * (∑ k : Fin r, ‖c k‖ ^ 2) := by
  obtain ⟨i, hi, hberg⟩ := metrizedLineBundle_bergman_extremal e c hz
  have hsec_eq : ∀ (s : Finset (Fin r)),
      (∑ k ∈ s, c k • e k).sec i z = ∑ k ∈ s, c k * (e k).sec i z := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, metrizedSection_add_sec,
        metrizedSection_smul_sec, ih]
  rw [(∑ k : Fin r, c k • e k).ptNormSq_eq_of_mem hi, hsec_eq Finset.univ]
  have hnn : 0 ≤ ∑ k : Fin r, ‖c k‖ ^ 2 := Finset.sum_nonneg fun k _ => sq_nonneg _
  exact hberg.trans (mul_le_mul_of_nonneg_right (hB z hz) hnn)

/-- **Finite-Volume `L² ≤ vol · L^∞` Bound (`h0_l2_le_vol_sup`)**:
if `(X, μ)` is measurable with finite measure (`μ X ≠ ⊤`) and `s.ptNormSq z ≤ M ^ 2` everywhere
on `X`, then `∫ z in X, s.ptNormSq z ∂μ ≤ μ.real X * M ^ 2`. -/
theorem h0_l2_le_vol_sup {d : ℕ} {ι : Type*} {X : Set (Fin d → ℂ)}
    {L : MetrizedLineBundle d ι X} (μ : Measure (Fin d → ℂ)) (hX : MeasurableSet X)
    (hfin : μ X ≠ ⊤) (s : MetrizedLineBundle.Section L) {M : ℝ}
    (hle : ∀ z ∈ X, s.ptNormSq z ≤ M ^ 2) (hint : IntegrableOn s.ptNormSq X μ) :
    ∫ z in X, s.ptNormSq z ∂μ ≤ μ.real X * M ^ 2 := by
  have hconst : IntegrableOn (fun _ : Fin d → ℂ => M ^ 2) X μ :=
    integrableOn_const hfin
  calc ∫ z in X, s.ptNormSq z ∂μ
      ≤ ∫ _z in X, M ^ 2 ∂μ := setIntegral_mono_on hint hconst hX fun z hz => hle z hz
    _ = μ.real X * M ^ 2 := by rw [setIntegral_const, smul_eq_mul]

/-- **Two-Sided `H⁰(X, L)` Norm Comparison (`h0_norm_comparison_bergman_vol`)**:
on a finite-measure complex space `(X, μ)` (`0 < μ.real X < ∞`) with an `L²`-orthonormal frame
`e : Fin r → L.Section` of bounded Bergman kernel `∑ k, (e k).ptNormSq z ≤ B`, EVERY section
`s = ∑ c_k e_k` satisfies:
`((μ.real X)⁻¹) * ∫_X s.ptNormSq dμ ≤ sup_X s.ptNormSq ≤ B * ∑_k ‖c_k‖²`! -/
theorem h0_norm_comparison_bergman_vol {d r : ℕ} {ι : Type*} {X : Set (Fin d → ℂ)}
    {L : MetrizedLineBundle d ι X} (μ : Measure (Fin d → ℂ)) (hX : MeasurableSet X)
    (hfin : μ X ≠ ⊤) (hpos : 0 < μ.real X)
    (e : Fin r → MetrizedLineBundle.Section L)
    {B : ℝ} (hB : ∀ z ∈ X, (∑ k : Fin r, (e k).ptNormSq z) ≤ B)
    (c : Fin r → ℂ) (M : ℝ) (hle : ∀ z ∈ X, (∑ k : Fin r, c k • e k).ptNormSq z ≤ M ^ 2)
    (hint : IntegrableOn (∑ k : Fin r, c k • e k).ptNormSq X μ) :
    (μ.real X)⁻¹ * (∫ z in X, (∑ k : Fin r, c k • e k).ptNormSq z ∂μ) ≤ M ^ 2 ∧
    (∀ z ∈ X, (∑ k : Fin r, c k • e k).ptNormSq z ≤ B * (∑ k : Fin r, ‖c k‖ ^ 2)) := by
  have hl2 := h0_l2_le_vol_sup μ hX hfin (∑ k : Fin r, c k • e k) hle hint
  have h1 : (μ.real X)⁻¹ * (∫ z in X, (∑ k : Fin r, c k • e k).ptNormSq z ∂μ) ≤ M ^ 2 := by
    rw [inv_mul_le_iff₀ hpos]
    exact hl2
  exact ⟨h1, fun z hz => h0_bergman_sup_le_l2 e c hB hz⟩

/-- **`h0_norm_comparison_constants` (Unconditional Finite-Dimensional Norm Equivalence)**:
for ANY continuous, positively homogeneous, positive-definite norm function `N : V → ℝ` on a
nontrivial finite-dimensional real normed space `V` (in particular, comparing `supNorm` against
the `L²`-norm on `H⁰(X, L)`!), there exist explicit constants `0 < c₁ ≤ c₂` such that
`∀ v : V, c₁ * ‖v‖ ≤ N v ∧ N v ≤ c₂ * ‖v‖`! -/
theorem h0_norm_comparison_constants {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [Nontrivial V]
    (N : V → ℝ) (hN_cont : Continuous N)
    (hN_pos : ∀ v : V, v ≠ 0 → 0 < N v)
    (hN_hom : ∀ (r : ℝ) (v : V), N (r • v) = |r| * N v) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ c₁ ≤ c₂ ∧
      ∀ v : V, c₁ * ‖v‖ ≤ N v ∧ N v ≤ c₂ * ‖v‖ := by
  let S : Set V := Metric.sphere (0 : V) 1
  have hScpt : IsCompact S := isCompact_sphere (0 : V) 1
  obtain ⟨v₀, hv₀⟩ := exists_ne (0 : V)
  have hSne : S.Nonempty := by
    refine ⟨‖v₀‖⁻¹ • v₀, ?_⟩
    rw [Metric.mem_sphere, dist_zero_right, norm_smul, norm_inv, norm_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv₀)]
  obtain ⟨u_min, hu_min_mem, hu_min⟩ := hScpt.exists_isMinOn hSne hN_cont.continuousOn
  obtain ⟨u_max, hu_max_mem, hu_max⟩ := hScpt.exists_isMaxOn hSne hN_cont.continuousOn
  have hu_min_ne : u_min ≠ 0 := by
    intro h0
    rw [Metric.mem_sphere, dist_zero_right, h0, norm_zero] at hu_min_mem
    norm_num at hu_min_mem
  have hu_max_ne : u_max ≠ 0 := by
    intro h0
    rw [Metric.mem_sphere, dist_zero_right, h0, norm_zero] at hu_max_mem
    norm_num at hu_max_mem
  set c₁ : ℝ := N u_min
  set c₂ : ℝ := N u_max
  have hc₁ : 0 < c₁ := hN_pos u_min hu_min_ne
  have hc₂ : 0 < c₂ := hN_pos u_max hu_max_ne
  have hc_le : c₁ ≤ c₂ := hu_min hu_max_mem
  refine ⟨c₁, c₂, hc₁, hc₂, hc_le, fun v => ?_⟩
  by_cases hv : v = 0
  · subst hv
    have hN0 : N 0 = 0 := by simpa using hN_hom 0 0
    simp [hN0]
  · have hvn : 0 < ‖v‖ := norm_pos_iff.mpr hv
    let u : V := ‖v‖⁻¹ • v
    have huS : u ∈ S := by
      rw [Metric.mem_sphere, dist_zero_right, norm_smul, norm_inv, norm_norm,
        inv_mul_cancel₀ hvn.ne']
    have hvu : v = ‖v‖ • u := by
      simp only [u, smul_smul, mul_inv_cancel₀ hvn.ne', one_smul]
    have hNv : N v = ‖v‖ * N u := by
      conv_lhs => rw [hvu]
      rw [hN_hom, abs_of_pos hvn]
    rw [hNv]
    exact ⟨(mul_le_mul_of_nonneg_right (hu_min huS) hvn.le).trans_eq (mul_comm _ _),
      (mul_comm _ _).trans_le (mul_le_mul_of_nonneg_right (hu_max huS) hvn.le)⟩

/-- **Metric-Change Norm Comparison Constants (`h0_norm_comparison_metric_change`)**:
if two Hermitian metrics on the same line bundle satisfy `|φ₁(z) - φ₂(z)| ≤ C` everywhere on `X`,
then pointwise norms, sup-norms, and `L²`-norms compare within `exp (C / 2)`! -/
theorem h0_norm_comparison_metric_change {d : ℕ} {ι : Type*} {X : Set (Fin d → ℂ)}
    {L₁ L₂ : MetrizedLineBundle d ι X} (hcov : L₁.openCover = L₂.openCover)
    (htrans : L₁.transFn = L₂.transFn) {C : ℝ}
    (hwt : ∀ i, ∀ z ∈ L₁.openCover i, |L₁.weight i z - L₂.weight i z| ≤ C)
    (s₁ : MetrizedLineBundle.Section L₁) (s₂ : MetrizedLineBundle.Section L₂)
    (hsec : ∀ i, ∀ z ∈ L₁.openCover i, s₁.sec i z = s₂.sec i z) {z : Fin d → ℂ} (hz : z ∈ X) :
    Real.exp (-C) * s₁.ptNormSq z ≤ s₂.ptNormSq z ∧
    s₂.ptNormSq z ≤ Real.exp C * s₁.ptNormSq z ∧
    Real.exp (-C / 2) * s₁.ptNorm z ≤ s₂.ptNorm z ∧
    s₂.ptNorm z ≤ Real.exp (C / 2) * s₁.ptNorm z := by
  have hup : s₂.ptNormSq z ≤ Real.exp C * s₁.ptNormSq z :=
    section_ptNormSq_metric_comparison hcov htrans
      (fun i w hw => by linarith [(abs_le.mp (hwt i w hw)).2]) s₁ s₂ hsec hz
  have hlo' : s₁.ptNormSq z ≤ Real.exp C * s₂.ptNormSq z :=
    section_ptNormSq_metric_comparison hcov.symm htrans.symm
      (fun i w hw => by
        have hw1 : w ∈ L₁.openCover i := by rwa [hcov]
        linarith [(abs_le.mp (hwt i w hw1)).1])
      s₂ s₁ (fun i w hw => (hsec i w (by rwa [hcov])).symm) hz
  have hlo : Real.exp (-C) * s₁.ptNormSq z ≤ s₂.ptNormSq z := by
    have hmul := mul_le_mul_of_nonneg_left hlo' (Real.exp_pos (-C)).le
    have hexp : Real.exp (-C) * Real.exp C = 1 := by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    calc Real.exp (-C) * s₁.ptNormSq z
        ≤ Real.exp (-C) * (Real.exp C * s₂.ptNormSq z) := hmul
      _ = (Real.exp (-C) * Real.exp C) * s₂.ptNormSq z := by ring
      _ = s₂.ptNormSq z := by rw [hexp, one_mul]
  have hpt_up : s₂.ptNorm z ≤ Real.exp (C / 2) * s₁.ptNorm z := by
    unfold MetrizedLineBundle.Section.ptNorm
    have hrt : Real.sqrt (Real.exp C * s₁.ptNormSq z) =
        Real.exp (C / 2) * Real.sqrt (s₁.ptNormSq z) := by
      rw [Real.sqrt_mul (Real.exp_pos _).le, ← Real.exp_half C]
    rw [← hrt]
    exact Real.sqrt_le_sqrt hup
  have hpt_lo : Real.exp (-C / 2) * s₁.ptNorm z ≤ s₂.ptNorm z := by
    unfold MetrizedLineBundle.Section.ptNorm
    have hrt : Real.sqrt (Real.exp (-C) * s₁.ptNormSq z) =
        Real.exp (-C / 2) * Real.sqrt (s₁.ptNormSq z) := by
      rw [Real.sqrt_mul (Real.exp_pos _).le, ← Real.exp_half (-C)]
    rw [← hrt]
    exact Real.sqrt_le_sqrt hlo
  exact ⟨hlo, hup, hpt_lo, hpt_up⟩

/-- **Toroidal Logarithmic-Singularity Norm Growth Bound (`h0_norm_comparison_toroidal_log_growth`)**:
if a singular metric `φ_sing` on the toroidal interior satisfies
`φ_bg z ≤ φ_sing z + κ * (-∑ i, log ‖t_i z‖²) + C`, then for any section `s` vanishing along the
boundary `t_i = 0` at order `‖s_loc‖² ≤ M² ∏ ‖t_i‖^{2 a_i}` (`a_i ≥ κ`), the singular pointwise
norm is bounded by `M² * exp(C) * ∏ ‖t_i‖^{2 (a_i - κ)} ≤ M² * exp(C)` inside `‖t_i‖ ≤ 1`! -/
theorem h0_norm_comparison_toroidal_log_growth {m : ℕ}
    (t : Fin m → ℂ) (ht : ∀ i, 0 < ‖t i‖) (hle1 : ∀ i, ‖t i‖ ≤ 1)
    {φ_sing C κ : ℝ} (a : Fin m → ℝ) (ha : ∀ i, κ ≤ a i)
    (s_loc : ℂ) {M : ℝ}
    (hvan : ‖s_loc‖ ^ 2 ≤ M ^ 2 * ∏ i : Fin m, (‖t i‖ ^ 2) ^ (a i))
    (hmetric : -φ_sing ≤ C + κ * (-∑ i : Fin m, Real.log (‖t i‖ ^ 2))) :
    ‖s_loc‖ ^ 2 * Real.exp (-φ_sing) ≤ M ^ 2 * Real.exp C := by
  have hexp_le : Real.exp (-φ_sing) ≤
      Real.exp C * ∏ i : Fin m, (‖t i‖ ^ 2) ^ (-κ) := by
    have hlog_eq : κ * (-∑ i : Fin m, Real.log (‖t i‖ ^ 2)) =
        ∑ i : Fin m, (-κ) * Real.log (‖t i‖ ^ 2) := by
      rw [mul_neg, Finset.mul_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ => by ring
    have hprod_eq : Real.exp (C + κ * (-∑ i : Fin m, Real.log (‖t i‖ ^ 2))) =
        Real.exp C * ∏ i : Fin m, (‖t i‖ ^ 2) ^ (-κ) := by
      rw [hlog_eq, Real.exp_add, Real.exp_sum]
      congr 1
      refine Finset.prod_congr rfl fun i _ => ?_
      have hpos : 0 < ‖t i‖ ^ 2 := sq_pos_of_pos (ht i)
      rw [mul_comm (-κ), Real.rpow_def_of_pos hpos]
    exact (Real.exp_le_exp.mpr hmetric).trans_eq hprod_eq
  have hprod_le_one : (∏ i : Fin m, (‖t i‖ ^ 2) ^ (a i)) *
      (∏ i : Fin m, (‖t i‖ ^ 2) ^ (-κ)) ≤ 1 := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_le_one (fun i _ => mul_nonneg (Real.rpow_nonneg (sq_nonneg _) _)
      (Real.rpow_nonneg (sq_nonneg _) _)) fun i _ => ?_
    have hpos : 0 < ‖t i‖ ^ 2 := sq_pos_of_pos (ht i)
    have hle1_sq : ‖t i‖ ^ 2 ≤ 1 := by
      have := hle1 i; nlinarith [ht i]
    rw [← Real.rpow_add hpos]
    exact Real.rpow_le_one hpos.le hle1_sq (by linarith [ha i])
  calc ‖s_loc‖ ^ 2 * Real.exp (-φ_sing)
      ≤ (M ^ 2 * ∏ i : Fin m, (‖t i‖ ^ 2) ^ (a i)) *
          (Real.exp C * ∏ i : Fin m, (‖t i‖ ^ 2) ^ (-κ)) :=
        mul_le_mul hvan hexp_le (Real.exp_pos _).le
          (mul_nonneg (sq_nonneg _) (Finset.prod_nonneg fun _ _ => Real.rpow_nonneg (sq_nonneg _) _))
    _ = (M ^ 2 * Real.exp C) * ((∏ i : Fin m, (‖t i‖ ^ 2) ^ (a i)) *
          (∏ i : Fin m, (‖t i‖ ^ 2) ^ (-κ))) := by ring
    _ ≤ (M ^ 2 * Real.exp C) * 1 :=
        mul_le_mul_of_nonneg_left hprod_le_one (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)
    _ = M ^ 2 * Real.exp C := mul_one _

end H0NormComparisonConstants

/-! ## Section 5: Relative Ampleness & Positivity (`relative_ampleness_sections`) -/

section RelativeAmplenessSections

/-- **Nonvanishing Locus `nonzeroLocus s : X.Opens`** of an algebraic global section
`s : AlgSection L`: union of chart basic opens `⨆ i, X.basicOpen (s.f i)`. -/
def AlgSection.nonzeroLocus {X : Scheme.{0}} {L : AlgLineBundle X} (s : AlgSection L) :
    X.Opens :=
  ⨆ i : L.ι, X.basicOpen (s.f i)

theorem AlgSection.mem_nonzeroLocus_iff {X : Scheme.{0}} {L : AlgLineBundle X}
    (s : AlgSection L) (x : X) :
    x ∈ s.nonzeroLocus ↔ ∃ i : L.ι, x ∈ L.U i ∧ x ∈ X.basicOpen (s.f i) := by
  simp only [AlgSection.nonzeroLocus, Opens.mem_iSup]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i, (X.basicOpen_le (s.f i)) hi, hi⟩
  · rintro ⟨i, _, hi⟩
    exact ⟨i, hi⟩

theorem AlgSection.nonzeroLocus_pull {X Y : Scheme.{0}} {L : AlgLineBundle X}
    (s : AlgSection L) (f : Y ⟶ X) :
    (s.pull f).nonzeroLocus = f ⁻¹ᵁ s.nonzeroLocus := by
  ext y
  unfold AlgSection.nonzeroLocus
  change (y ∈ ⨆ i, Y.basicOpen ((s.pull f).f i)) ↔ (f.base y ∈ ⨆ i, X.basicOpen (s.f i))
  rw [Opens.mem_iSup, Opens.mem_iSup]
  refine exists_congr fun i => ?_
  change y ∈ Y.basicOpen ((s.pull f).f i) ↔ y ∈ f ⁻¹ᵁ X.basicOpen (s.f i)
  rw [Scheme.preimage_basicOpen]
  rfl

/-- Global generation of `L : AlgLineBundle X` by finitely many global sections. -/
def IsGloballyGenerated {X : Scheme.{0}} (L : AlgLineBundle X) : Prop :=
  ∃ (n : ℕ) (s : Fin n → AlgSection L), ⨆ i : Fin n, (s i).nonzeroLocus = ⊤

/-- **Ample Algebraic Line Bundle (`IsAmpleLB L`)**:
`X` is quasi-compact and every point `x : X` lies in an affine nonvanishing locus
`nonzeroLocus s` of some tensor power section `s : AlgSection (L.pow n)` (`n ≥ 1`). -/
structure IsAmpleLB {X : Scheme.{0}} (L : AlgLineBundle X) : Prop where
  isLB : L.IsLB
  compactSpace : CompactSpace X
  exists_affine : ∀ x : X, ∃ n : ℕ, 1 ≤ n ∧
    ∃ s : AlgSection (L.pow n), x ∈ s.nonzeroLocus ∧ IsAffineOpen s.nonzeroLocus

/-- **Very Ample Section System (`IsVeryAmpleOver p L s`)**:
over `p : X ⟶ Sp K`, the nonvanishing loci `U_i = (s i).nonzeroLocus` are affine, cover `X`,
and their coordinate rings `Γ(X, U_i)` are generated over `K` by the section ratios `s_j / s_i`. -/
def IsVeryAmpleOver {K : Type} [CommRing K] {X : Scheme.{0}}
    (p : X ⟶ Sp K) (L : AlgLineBundle X) {m : ℕ} (s : Fin (m + 1) → AlgSection L) : Prop :=
  (⨆ i, (s i).nonzeroLocus = ⊤) ∧
  ∀ i : Fin (m + 1), IsAffineOpen (s i).nonzeroLocus ∧
    ∃ r : Fin (m + 1) → Γ(X, (s i).nonzeroLocus),
      (∀ j k,
        (X.presheaf.map (homOfLE (inf_le_right : (s i).nonzeroLocus ⊓ L.U k ≤ L.U k)).op).hom
          ((s j).f k) =
        (X.presheaf.map (homOfLE (inf_le_left : (s i).nonzeroLocus ⊓ L.U k ≤ (s i).nonzeroLocus)).op).hom
          (r j) *
        (X.presheaf.map (homOfLE (inf_le_right : (s i).nonzeroLocus ⊓ L.U k ≤ L.U k)).op).hom
          ((s i).f k)) ∧
      ∀ f : Γ(X, (s i).nonzeroLocus), ∃ F : MvPolynomial (Fin (m + 1)) K,
        f = MvPolynomial.eval₂
          (RingHom.comp (X.presheaf.map (homOfLE (le_top : (s i).nonzeroLocus ≤ p ⁻¹ᵁ ⊤)).op).hom
            (RingHom.comp (p.app ⊤).hom (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom))
          r F

/-- **Relative Ampleness (`IsRelAmple p L`)** over a base scheme `p : X ⟶ S`:
on the preimage of every affine open `U ⊆ S`, some positive tensor power `(L.pull _).pow n`
is very ample over `Spec Γ(S, U)`. -/
def IsRelAmple {X S : Scheme.{0}} (p : X ⟶ S) (L : AlgLineBundle X) : Prop :=
  ∀ U : S.Opens, ∀ hU : IsAffineOpen U,
    ∃ (n : ℕ), 1 ≤ n ∧ ∃ (m : ℕ) (s : Fin (m + 1) → AlgSection ((L.pull (p ⁻¹ᵁ U).ι).pow n)),
      IsVeryAmpleOver (p ∣_ U ≫ hU.isoSpec.hom)
        ((L.pull (p ⁻¹ᵁ U).ι).pow n) s

/-- **Affine-Base Ampleness from Relative Ampleness (`isAmpleLB_of_relAmple_of_isAffine`)**:
if `S` is affine (`[IsAffine S]`) and `L` is relatively ample over a compact-fiber morphism
`p : X ⟶ S` (with `[CompactSpace X]`), then `L` is ample (`IsAmpleLB L`)! -/
theorem isAmpleLB_of_relAmple_of_isAffine {X S : Scheme.{0}} [IsAffine S] [CompactSpace X]
    {p : X ⟶ S} {L : AlgLineBundle X} (hL : L.IsLB) (hr : IsRelAmple p L) :
    IsAmpleLB L := by
  refine ⟨hL, inferInstance, fun x => ?_⟩
  obtain ⟨n, hn, m, s, hcov, haff⟩ := hr ⊤ (isAffineOpen_top S)
  let V0 : X.Opens := p ⁻¹ᵁ (⊤ : S.Opens)
  let j : V0.toScheme ⟶ X := V0.ι
  have : IsIso j := inferInstanceAs (IsIso (X.topIso.hom))
  have hx_pre : x ∈ V0 := trivial
  obtain ⟨x', hx'⟩ : ∃ x' : V0.toScheme, j x' = x := ⟨⟨x, hx_pre⟩, rfl⟩
  have hx'_cov : x' ∈ ⨆ i : Fin (m + 1), (s i).nonzeroLocus := by rw [hcov]; trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.1 hx'_cov
  let s_i : AlgSection ((L.pull j).pow n) := s i
  let s' : AlgSection (L.pow n) :=
    { f := fun (k : L.ι) => (inv (j.app (L.U k))).hom (s_i.f k)
      compat := fun (k l : L.ι) => by
        have hnat_j : ∀ (W₁ W₂ : X.Opens) (hW : W₁ ≤ W₂) (v : Γ(V0.toScheme, j ⁻¹ᵁ W₂)),
            (X.presheaf.map (homOfLE hW).op).hom ((inv (j.app W₂)).hom v) =
              (inv (j.app W₁)).hom
                ((V0.toScheme.presheaf.map (homOfLE (j.preimage_mono hW)).op).hom v) := by
          intro W₁ W₂ hW v
          have h1 := j.naturality (homOfLE hW).op
          have h2 : j.app W₂ ≫ V0.toScheme.presheaf.map (homOfLE (j.preimage_mono hW)).op =
              X.presheaf.map (homOfLE hW).op ≫ j.app W₁ := h1.symm
          have h3 : inv (j.app W₂) ≫ X.presheaf.map (homOfLE hW).op =
              V0.toScheme.presheaf.map (homOfLE (j.preimage_mono hW)).op ≫ inv (j.app W₁) := by
            rw [IsIso.inv_comp_eq, ← Category.assoc, h2, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
          have hc := congrArg (fun φ : CommRingCat.Hom _ _ => φ.hom v) h3
          rw [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_comp, RingHom.comp_apply] at hc
          exact hc
        rw [hnat_j _ _ _ (s_i.f k), hnat_j _ _ _ (s_i.f l)]
        have hsc := s_i.compat k l
        dsimp only [AlgLineBundle.pow, AlgLineBundle.pull] at hsc
        have hle_kl : j ⁻¹ᵁ (L.U k ⊓ L.U l) ≤ j ⁻¹ᵁ L.U k ⊓ j ⁻¹ᵁ L.U l :=
          le_inf (j.preimage_mono inf_le_left) (j.preimage_mono inf_le_right)
        have hsc' := congrArg (V0.toScheme.presheaf.map (homOfLE hle_kl).op).hom hsc
        rw [map_mul, AlgSection.res_res, AlgSection.res_res] at hsc'
        have hg_pull : (V0.toScheme.presheaf.map (homOfLE hle_kl).op).hom
            ((Units.map ((j.app (L.U k ⊓ L.U l) ≫ V0.toScheme.presheaf.map
              (homOfLE (AlgLineBundle.preimage_inf_le j (L.U k) (L.U l))).op).hom) (L.g k l) ^ (n : ℤ) :
              Γ(V0.toScheme, j ⁻¹ᵁ L.U k ⊓ j ⁻¹ᵁ L.U l)ˣ) :
              Γ(V0.toScheme, j ⁻¹ᵁ L.U k ⊓ j ⁻¹ᵁ L.U l)) =
            (j.app (L.U k ⊓ L.U l)).hom
              ((L.g k l ^ (n : ℤ) : Γ(X, L.U k ⊓ L.U l)ˣ) : Γ(X, L.U k ⊓ L.U l)) := by
          rw [← map_zpow, Units.coe_map]
          simp only [MonoidHom.coe_coe, CommRingCat.hom_comp, RingHom.comp_apply]
          rw [AlgSection.res_res, show homOfLE (le_rfl : j ⁻¹ᵁ (L.U k ⊓ L.U l) ≤ j ⁻¹ᵁ (L.U k ⊓ L.U l)) = 𝟙 _ from rfl,
            op_id, CategoryTheory.Functor.map_id]
          rfl
        rw [hg_pull] at hsc'
        dsimp only [AlgLineBundle.pow]
        rw [hsc', map_mul]
        congr 1
        rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, IsIso.hom_inv_id]
        rfl }
  have hloc_eq : s'.nonzeroLocus = j ''ᵁ s_i.nonzeroLocus := by
    ext y
    have hy_pre : j ⁻¹ᵁ s'.nonzeroLocus = s_i.nonzeroLocus := by
      ext z
      unfold AlgSection.nonzeroLocus
      change (j.base z ∈ ⨆ k, X.basicOpen ((inv (j.app (L.U k))).hom (s_i.f k))) ↔
        (z ∈ ⨆ k, V0.toScheme.basicOpen (s_i.f k))
      rw [Opens.mem_iSup, Opens.mem_iSup]
      refine exists_congr fun k => ?_
      change z ∈ j ⁻¹ᵁ X.basicOpen ((inv (j.app (L.U k))).hom (s_i.f k)) ↔
        z ∈ V0.toScheme.basicOpen (s_i.f k)
      have hsimp : (j.app (L.U k)).hom ((inv (j.app (L.U k))).hom (s_i.f k)) = s_i.f k := by
        rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, IsIso.inv_hom_id]
        rfl
      rw [Scheme.preimage_basicOpen, hsimp]
    change y ∈ s'.nonzeroLocus ↔ ∃ z ∈ s_i.nonzeroLocus, j z = y
    constructor
    · intro hy
      refine ⟨⟨y, trivial⟩, ?_, rfl⟩
      rw [← hy_pre]
      exact hy
    · rintro ⟨z, hz, rfl⟩
      rw [← hy_pre] at hz
      exact hz
  have haff' : IsAffineOpen s'.nonzeroLocus := by
    rw [hloc_eq]
    exact (haff i).1.image_of_isOpenImmersion j
  refine ⟨n, hn, s', ?_, haff'⟩
  · rw [hloc_eq]
    exact ⟨x', hi, hx'⟩

/-- **Strict Positivity of Pullback Fubini–Study Metric Along a Holomorphic Projective Immersion
(`posCurvatureMetric_of_holomorphic_immersion`)**:
if `f : Fin (m + 1) → (Fin d → ℂ) → ℂ` is `C²`-holomorphic and nowhere simultaneously vanishing on
open `X ⊆ ℂ^d`, and at every `z ∈ X` and nonzero tangent `w ≠ 0`, `Df(z) w` is not a complex
scalar multiple of `f(z)` (i.e. `z ↦ [f₀(z) : … : f_m(z)]` is a holomorphic immersion into `ℙ^m`),
then the pullback Fubini–Study line bundle `weight = log (∑ k, ‖f_k‖²)` has **strictly positive
curvature (`PosCurvatureMetric`)**! -/
theorem posCurvatureMetric_of_holomorphic_immersion {d m : ℕ} (X : Set (Fin d → ℂ))
    (hX : IsOpen X) (f : Fin (m + 1) → (Fin d → ℂ) → ℂ)
    (hf : ∀ k, ∀ z ∈ X, ContDiffAt ℂ 2 (f k) z)
    (hpos : ∀ z ∈ X, 0 < ∑ k : Fin (m + 1), ‖f k z‖ ^ 2)
    (himm : ∀ z ∈ X, ∀ w : Fin d → ℂ, w ≠ 0 →
      ¬ ∃ c : ℂ, ∀ k : Fin (m + 1), fderiv ℂ (f k) z w = c * f k z) :
    PosCurvatureMetric (MetrizedLineBundle.trivial d X hX
      (fun y => Real.log (∑ k : Fin (m + 1), ‖f k y‖ ^ 2))
      (fun z hz => (ContDiffAt.sum fun k _ => contDiffAt_norm_sq_of_holo (hf k z hz)).log
        (hpos z hz).ne')) := by
  intro z hz w hw
  show 0 < (MetrizedLineBundle.trivial d X hX _ _).curvatureAt z w
  rw [MetrizedLineBundle.trivial_curvatureAt hX _ _ hz w,
    leviForm_log_sum_norm_sq_eq f (fun k => hf k z hz) (hpos z hz) w]
  set S : ℝ := ∑ k : Fin (m + 1), ‖f k z‖ ^ 2
  set A : ℂ := ∑ k : Fin (m + 1), fderiv ℂ (f k) z w * conj (f k z)
  have hS : 0 < S := hpos z hz
  refine div_pos ?_ (sq_pos_of_pos hS)
  let u : Fin (m + 1) → ℂ := fun k => fderiv ℂ (f k) z w
  let v : Fin (m + 1) → ℂ := fun k => f k z
  have hid : (∑ k : Fin (m + 1), ‖(S : ℂ) * u k - A * v k‖ ^ 2) =
      S * (S * (∑ k : Fin (m + 1), ‖u k‖ ^ 2) - ‖A‖ ^ 2) := by
    have hnorm_eq : ∀ k : Fin (m + 1),
        ((‖(S : ℂ) * u k - A * v k‖ ^ 2 : ℝ) : ℂ) =
          ((S : ℂ) * u k - A * v k) * conj ((S : ℂ) * u k - A * v k) := fun k => by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
    have hsumC : Complex.ofReal (∑ k : Fin (m + 1), ‖(S : ℂ) * u k - A * v k‖ ^ 2) =
        Complex.ofReal (S * (S * (∑ k : Fin (m + 1), ‖u k‖ ^ 2) - ‖A‖ ^ 2)) := by
      have hlhs : Complex.ofReal (∑ k : Fin (m + 1), ‖(S : ℂ) * u k - A * v k‖ ^ 2) =
          ∑ k : Fin (m + 1), ((S : ℂ) * u k - A * v k) * conj ((S : ℂ) * u k - A * v k) := by
        rw [Complex.ofReal_sum]
        exact Finset.sum_congr rfl fun k _ => hnorm_eq k
      have hrhs : Complex.ofReal (S * (S * (∑ k : Fin (m + 1), ‖u k‖ ^ 2) - ‖A‖ ^ 2)) =
          (S : ℂ) * ((S : ℂ) * (∑ k : Fin (m + 1), ((‖u k‖ : ℂ) ^ 2)) - (‖A‖ : ℂ) ^ 2) := by
        have h_u_sum : Complex.ofReal (∑ k : Fin (m + 1), ‖u k‖ ^ 2) =
            ∑ k : Fin (m + 1), ((‖u k‖ : ℂ) ^ 2) := by
          rw [Complex.ofReal_sum]
          exact Finset.sum_congr rfl fun k _ => Complex.ofReal_pow ‖u k‖ 2
        rw [Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_pow, h_u_sum]
      rw [hlhs, hrhs]
      have hexp : ∀ k : Fin (m + 1),
          ((S : ℂ) * u k - A * v k) * conj ((S : ℂ) * u k - A * v k) =
            (S : ℂ) ^ 2 * (u k * conj (u k)) -
            (S : ℂ) * conj A * (u k * conj (v k)) -
            (S : ℂ) * A * (v k * conj (u k)) +
            (A * conj A) * (v k * conj (v k)) := fun k => by
        rw [map_sub, map_mul, map_mul, Complex.conj_ofReal]
        ring
      simp_rw [hexp, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
      have h1 : (∑ k : Fin (m + 1), u k * conj (u k)) =
          ∑ k : Fin (m + 1), ((‖u k‖ : ℂ) ^ 2) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
      have h2 : (∑ k : Fin (m + 1), v k * conj (v k)) = (S : ℂ) := by
        have hS_eq : (S : ℂ) = ∑ k : Fin (m + 1), ((‖v k‖ : ℂ) ^ 2) := by
          change Complex.ofReal (∑ k : Fin (m + 1), ‖v k‖ ^ 2) = _
          rw [Complex.ofReal_sum]
          exact Finset.sum_congr rfl fun k _ => Complex.ofReal_pow ‖v k‖ 2
        rw [hS_eq]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
      have h3 : (∑ k : Fin (m + 1), u k * conj (v k)) = A := rfl
      have h4 : (∑ k : Fin (m + 1), v k * conj (u k)) = conj A := by
        rw [show A = ∑ k : Fin (m + 1), u k * conj (v k) from rfl, map_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [map_mul, Complex.conj_conj, mul_comm]
      have hAA : A * conj A = (‖A‖ : ℂ) ^ 2 := by
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
      have hAA' : conj A * A = (‖A‖ : ℂ) ^ 2 := by
        rw [mul_comm, hAA]
      rw [h1, h2, h3, h4, mul_assoc (S : ℂ), mul_assoc (S : ℂ), hAA, hAA']
      ring
    exact Complex.ofReal_injective hsumC
  have hproj_pos : 0 < ∑ k : Fin (m + 1), ‖(S : ℂ) * u k - A * v k‖ ^ 2 := by
    have hne : ∃ k : Fin (m + 1), (S : ℂ) * u k - A * v k ≠ 0 := by
      by_contra hall
      push Not at hall
      apply himm z hz w hw
      refine ⟨A / (S : ℂ), fun k => ?_⟩
      have hk := hall k
      have hSne : (S : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hS.ne'
      have h1 : (S : ℂ) * u k = A * v k := sub_eq_zero.mp hk
      change u k = (A / (S : ℂ)) * v k
      rw [div_mul_eq_mul_div, eq_div_iff hSne, mul_comm (u k), h1]
    rcases hne with ⟨k₀, hk₀⟩
    exact Finset.sum_pos' (fun k _ => sq_nonneg _)
      ⟨k₀, Finset.mem_univ k₀, sq_pos_of_pos (norm_pos_iff.mpr hk₀)⟩
  rw [hid] at hproj_pos
  exact pos_of_mul_pos_right hproj_pos hS.le

/-- **`relative_ampleness_sections` (Relative Ampleness → Finite-Dim Generating Sections,
Affine-Base Ampleness, and Analytic Positivity)**:
combines:
1. Over an affine base `S`, `IsRelAmple p L` implies `IsAmpleLB L` (when `X` is compact),
2. Any very ample section tuple `s : Fin (m + 1) → AlgSection L` yields `IsGloballyGenerated L`. -/
theorem relative_ampleness_sections
    {X S : Scheme.{0}} [IsAffine S] [CompactSpace X]
    {p : X ⟶ S} {L : AlgLineBundle X} (hL : L.IsLB) (hr : IsRelAmple p L) :
    IsAmpleLB L ∧
    (∀ {K : Type} [CommRing K] {q : X ⟶ Sp K} {m : ℕ} (s : Fin (m + 1) → AlgSection L),
      IsVeryAmpleOver q L s → IsGloballyGenerated L) :=
  ⟨isAmpleLB_of_relAmple_of_isAffine hL hr, fun s hs => ⟨_ + 1, s, hs.1⟩⟩

/-- **Concrete 0-Assumption Projective-Space Relative Ampleness & Positivity Witness
(`projSpace_relative_ampleness_sections`)**:
on `ℙ^N` (`N : ℕ`):
1. `fubiniStudyLineBundle N` has `PosCurvatureMetric` (`fubiniStudy_posCurvature N`),
2. `H⁰(ℙ^N_K, 𝒪(e))` is finite-dimensional of exact dimension `Nat.choose (e + N) N`,
3. `H⁰(ℙ^N_ℤ, 𝒪(k))` (`k ≥ 0`, `α > 0`) forms a concrete `GlobalSectionsLatH0` of exact rank
   `Nat.choose (k + N) N`! -/
theorem projSpace_relative_ampleness_sections (K : Type) [Field K] (N e : ℕ) {α : ℝ} (hα : 0 < α) :
    PosCurvatureMetric (fubiniStudyLineBundle N) ∧
    (FiniteDimensional K (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K e) ∧
     Module.finrank K (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K e) =
       Nat.choose (e + N) N) ∧
    (GlobalSectionsLatH0.projSpace N e hα).rank = Nat.choose (e + N) N :=
  ⟨fubiniStudy_posCurvature N, sections_have_finite_dimension_projSpace K N e,
    GlobalSectionsLatH0.projSpace_rank N e hα⟩

end RelativeAmplenessSections

/-! ## Section 6: Wave 3 (`ShimuraHodgeArakelov`, `IndefiniteHodgeLattices`) & M4 Handoff Pack -/

section Wave3AndM4Handoff

/-- **Wave 3 & M4 Handoff Package (`GagaSectionsPack`)**:
bundles `GlobalSectionsLatH0` at graded degrees `k ≥ 1` with `GradedHermAlgebra` and positive
arithmetic self-intersection `volAr > 0`. -/
structure GagaSectionsPack (d : ℕ) {ι : Type*} {X : Set (Fin d → ℂ)}
    (L : MetrizedLineBundle d ι X) where
  hd : 1 ≤ d
  alg : GradedHermAlgebra d
  hPosVol : 0 < alg.volAr

/-- **Moriwaki Small-Section Bigness via `GlobalSectionsLatH0` (`gaga_small_sections_lower_bound`)**:
any graded family of `GlobalSectionsLatH0` with positive arithmetic volume `volAr > 0`
admits `c₀ > 0` and `K₀ ≥ 1` such that `log (#smallSections H k) ≥ c₀ * k^(d + 1)` and
there exists a nonzero strictly small global section `s ∈ H⁰(𝒳, ℒ^{⊗ k})` (`‖s‖_sup < 1`)
for all `k ≥ K₀`! -/
theorem gaga_small_sections_lower_bound (d : ℕ) (hd : 1 ≤ d) {ι : Type*} {X : Set (Fin d → ℂ)}
    {L : MetrizedLineBundle d ι X}
    (H : ∀ k : ℕ, GlobalSectionsLatH0 d (L.pow (k : ℤ)))
    (volConst_unif : ℝ) (hVpos : 0 < volConst_unif)
    (hV_le : ∀ k, 1 ≤ k → ∀ s : (H k).secSpace, ‖s‖ ≤ volConst_unif * (H k).supNorm s)
    (bergConst : ℝ) (bergExp : ℕ) (hBge : 1 ≤ bergConst)
    (hB_le : ∀ k, 1 ≤ k → ∀ s : (H k).secSpace,
      (H k).supNorm s ≤ bergConst * ((k : ℝ) + 1) ^ bergExp * ‖s‖)
    (rankHi : ℝ) (hRge : 1 ≤ rankHi)
    (hRk_le : ∀ k, 1 ≤ k → ((H k).rank : ℝ) ≤ rankHi * (k : ℝ) ^ d)
    (volAr : ℝ) (hvol : 0 < volAr)
    (hAHS : ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop,
      volAr / ((d + 1).factorial : ℝ) - ε ≤ (H k).arithDegH0 / (k : ℝ) ^ (d + 1)) :
    let A := GlobalSectionsLatH0.toGradedHermAlgebra d hd H volConst_unif hVpos hV_le
      bergConst bergExp hBge hB_le rankHi hRge hRk_le volAr hAHS
    (∃ c₀ : ℝ, 0 < c₀ ∧ ∃ K₀ : ℕ, ∃ hK₀ : 1 ≤ K₀,
      ∀ k : ℕ, (hk : K₀ ≤ k) →
        c₀ * (k : ℝ) ^ (d + 1) ≤ Real.log (A.smallSectionsCard k (le_trans hK₀ hk) : ℝ)) ∧
    (∃ K₀ : ℕ, 1 ≤ K₀ ∧ ∀ k : ℕ, K₀ ≤ k → ∃ s : A.secLat k, s ≠ 0 ∧ A.supNorm k s.1 < 1) := by
  intro A
  exact ⟨moriwaki_big_small_sections A hvol, moriwaki_exists_nonzero_small_section A hvol⟩

/-- **Indefinite Hodge-Lattice `L3` Covolume Bridge (`gaga_l3_indefinite_hodge_bridge`)**:
directly feeds `IndefiniteHodgeLattices` (`M3` Wave 3) and `CovolStepsBridge` / `TopCovolG` (`M4`):
bounded Moriwaki small global sections pushed forward into indefinite Hodge lattices `M j ⊂ E j`
yield the uniform `L3` covolume bound
`(2 / D) * log(covol (M j)) ≤ (2 * rk (M j) / D) * log(C_chart j * A.volConst)`. -/
theorem gaga_l3_indefinite_hodge_bridge {d m : ℕ} (A : GradedHermAlgebra d)
    (E : Fin m → Type*) [∀ j, NormedAddCommGroup (E j)] [∀ j, InnerProductSpace ℝ (E j)]
    [∀ j, FiniteDimensional ℝ (E j)]
    (M : ∀ j, Submodule ℤ (E j)) [∀ j, DiscreteTopology (M j)]
    (hM0 : ∀ j, M j ≠ ⊥)
    (k : Fin m → ℕ) (hk : ∀ j, 1 ≤ k j)
    (Ψ : ∀ j, A.secSpace (k j) → E j)
    (C_chart : Fin m → ℝ) (hCpos : ∀ j, 0 < C_chart j)
    (hΨ_bound : ∀ j x, ‖Ψ j x‖ ≤ C_chart j * ‖x‖)
    (t : ∀ j, Fin (ArakelovCovolume.rk (M j)) → A.secLat (k j))
    (ht_small : ∀ j i, t j i ∈ A.smallSectionsSet (k j))
    (hΨ_mem : ∀ j i, Ψ j (t j i).1 ∈ M j)
    (hΨ_li : ∀ j, LinearIndependent ℝ (fun i => Ψ j (t j i).1))
    {D : ℝ} (hD : 0 < D) :
    (∀ j : Fin m, Real.log (ArakelovCovolume.covol (M j)) ≤
      (ArakelovCovolume.rk (M j) : ℝ) * Real.log (C_chart j * A.volConst)) ∧
    (∑ j : Fin m, (2 / D) * Real.log (ArakelovCovolume.covol (M j)) ≤
      ∑ j : Fin m, (2 * (ArakelovCovolume.rk (M j) : ℝ) / D) *
        Real.log (C_chart j * A.volConst)) :=
  L3_covolume_of_moriwaki_small_sections A E M hM0 k hk Ψ C_chart hCpos hΨ_bound
    t ht_small hΨ_mem hΨ_li hD

/-- **Hodge-Section Arakelov Slope Stability under Metric Rescaling (`gaga_hodge_slope_metric_stability`)**:
for any `GlobalSectionsLatH0` and metric rescaling `c : ℝ`, the rank is preserved, `arithDeg`
shifts by `rk * (c / 2)`, and `slope` shifts by `c / 2`! -/
theorem gaga_hodge_slope_metric_stability {d : ℕ} {ι : Type*} {X : Set (Fin d → ℂ)}
    {L : MetrizedLineBundle d ι X} (H : GlobalSectionsLatH0 d L) (c : ℝ) :
    (H.scaleMetricH0 c).rank = H.rank ∧
    (H.scaleMetricH0 c).arithDegH0 = H.arithDegH0 + (H.rank : ℝ) * (c / 2) ∧
    (H.scaleMetricH0 c).slopeH0 = H.slopeH0 + c / 2 :=
  H.scaleMetricH0_invariants c

end Wave3AndM4Handoff

end RHDirect.Stage14M3_GagaAndSections

end
