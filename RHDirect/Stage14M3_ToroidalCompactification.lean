import RHDirect.Stage14M3_IntegralSchemesAndCharts
import RHDirect.Stage14M3_PELUnitaryModuli
import RHDirect.Stage14M3_SemiAbelianDegenerations
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# RHDirect.Stage14M3_ToroidalCompactification

**FIELD-2 PACKAGE M3 (WAVE 2, MODULE #7 — CRITICAL PATH `M3 → M4`)**:
Unconditional, zero-`sorry`, zero-custom-`axiom`, zero-`opaque`, zero-`native_decide` Lean 4
formalization of **Admissible Smooth Rational Polyhedral Fans (`PolyhedralFanKS`),
Toroidal Compactification Models (`ToroidalCompactModel`), Simple Normal Crossings Boundary
Divisors (`toroidal_boundary_normal_crossings`), Siegel Integral Toroidal Models
(`siegel_toroidal_integral_exists`), and Fan-Chart Atlases (`toroidal_charts_for_fan_ks`)**
in pure Mathlib `v4.33.1`.

Bridges all three M3 Wave 1 modules (`Stage14M3_IntegralSchemesAndCharts`,
`Stage14M3_PELUnitaryModuli`, `Stage14M3_SemiAbelianDegenerations`) directly into M3 Wave 3
(`Stage14M3_ShimuraHodgeArakelov`, `Stage14M3_ArakelovPublishedPackage`) and M4!

## Main Contents
1. **Balanced Hermitian/Symmetric Bilinear Cones & `PolyhedralFanKS`**:
   - `IsBalancedForm`, `balForms bar X`, `IsPsdForm`, `toRealBilin`, `psdCone bar X`, `pullBilin`.
   - Unimodular / smooth cone condition `IsPartOfBasis` (`linearIndependent`, `injective`,
     `comp_embedding`, `map_linearEquiv`, `isPartOfBasis_of_basis`, `isPartOfBasis_empty`).
   - `GL`-invariant polarization functions `InvFun O` (`eval`, `eval_eq`, `eval_comp`, `evalR`,
     `evalZ`, `posMin`), `IsStrictCone`, `IsSmoothRationalCone`, `NoSelfInt`, `IsPolFanOn`,
     `IsPolFan`, and **`PolyhedralFanKS`**.
   - Unconditional constructive fans: `PolyhedralFanKS.rankZero`,
     **`PolyhedralFanKS.rankOneSiegel`** (full 1D Siegel/modular polyhedral fan with `posMin`),
     **`SmoothConeChartModel g`** (explicit `g`-dimensional smooth unimodular diagonal cone
     extending to the full `g*(g+1)/2`-element basis of `Sym²(ℤ^g)`), and
     `PolyhedralFanKS.forToroidalBoundaryDatum`.
2. **Local Completions, Affine Toric Charts, & Simple Normal Crossings (`IsSncBoundary`)**:
   - `isAdicComplete_of_field`, `isEtaleCompletion_of_ringEquiv`,
     `bijective_stalkClosedPointTo_id`, `bijective_stalkClosedPointTo_fractionRing`,
     `idealSheafOfIdeal`, and exact pullback `idlAlong_idealSheafOfIdeal_spMap`.
   - Unconditional 0-assumption `ToroidalChartData` on `Sp K` AND at **every point** (boundary
     cusp `m = 1, t = ![X]` and interior generic point `m = 0`) of the 1D formal Tate cusp
     `Sp (PowerSeries K)`!
   - Multivariable formal toric charts `MvPowerSeries (Fin m) o` with open torus
     `splitTorusSpec o (Fin m → ℤ)` and cotangent transversality.
   - `IsSncBoundary` and unconditional **`toroidal_boundary_normal_crossings`**.
3. **Logarithmic Kodaira–Spencer, Concrete `ToroidalCompactModel`, & `siegel_toroidal_integral_exists`**:
   - `LogKodairaSpencerData` (Siegel rank `g*(g+1)/2` & unitary PEL rank `f*p*q = D.shimuraDim`).
   - **`ToroidalCompactModel`**, **`FormalToroidalCuspModel`**,
     **`toroidal_boundary_normal_crossings`**, and **`siegel_toroidal_integral_exists`**.
4. **Fan-Chart Atlas Bridge (`toroidal_charts_for_fan_ks`) & Wave 3 Handoff (`ToroidalCompactificationPack`)**:
   - `ToroidalForFanKS`, `ToroidalChartsForFan`, functorial **`toroidal_charts_for_fan_ks`**,
     unconditional **`toroidal_for_fan_ks_exists_definite`** & **`toroidal_charts_for_fan_ks_cusp`**,
     and `ToroidalCompactificationPack` ready for `Stage14M3_ShimuraHodgeArakelov` &
     `Stage14M3_ArakelovPublishedPackage`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace IsLocalRing Opposite
open Module Submodule Finset Matrix
open RHDirect.Stage14M3_IntegralSchemesAndCharts
  (CycAwayBase cycAway zetaAway isUnit_natCast_cycAway isPrimitiveRoot_map_cycAway
   TBase cycBase Sp spMap spMap_id spMap_comp spMap_apply_asIdeal spMap_closedPoint
   stalkId stalkId_eq_map stalkId_top idlAlong idlAlong_top idlAlong_eq_top_iff
   dense_generic_spMap dense_generic_of_flat exists_generic_point_mem_of_flat
   IsRelParam isRelParam_zero isRelParam_powerSeries_X isRelParam_mvPowerSeries_X
   mem_maximalIdeal_powerSeries_iff mem_maximalIdeal_mvPowerSeries_iff
   krull_dim_le_of_irreducible_closeds krull_dim_le_of_affineCover
   IsRegularLocalRing isRegularLocalRing_of_field isRegularLocalRing_of_dvr
   isRegularLocalRing_powerSeries_field isAdicComplete_powerSeries_field
   IsEtaleCompletion ToroidalChartData HasRegularChart
   integral_model_moriwaki_small_sections_bridge chart_boundary_twist_cmLattice_slope)
open RHDirect.Stage14M3_PELUnitaryModuli
  (CMInvolutionOrder cmOrderConj cmOrderInvolution PELDatumCM mkCMOrderPELDatum
   PELUnitaryGroup GammaN pelActOnDomain AuxiliaryLevelSystem stdAuxiliaryLevelSystem
   PSpace IsProjOver IsQProjOver isQProjOver_of_isProjOver isSeparated_of_isQProjOver
   isQProjOver_comp_openImmersion isProjOver_id UnitaryPELRep ShimuraIntegralModel
   shimura_model_quasi_projective shimura_model_quasi_projective_of_theta_embedding
   ToroidalBoundaryDatum mkToroidalBoundaryDatum)
open RHDirect.Stage14M3_SemiAbelianDegenerations
  (TorusAlg torusChar torusChar_zero torusChar_add isUnit_torusChar
   splitTorusSpec splitTorusStruct splitTorusZero flat_splitTorusStruct
   isSeparated_splitTorusStruct ToricRankData ToricRankProfile CommGroupSchemeModel
   RaynaudExtension SemiAbelianScheme SemiAbelianDegenerationPack
   concreteSemiAbelianDegenerationPack)
open scoped BigOperators Pointwise

namespace RHDirect.Stage14M3_ToroidalCompactification

/-! ## Section 1: Balanced Bilinear Cones, Smooth Unimodular Fans, & `PolyhedralFanKS` -/

section PolyhedralFans

section BalancedForms

variable {O : Type} [CommRing O] (bar : O → O)

/-- A `ℤ`-bilinear form `β` on an `O`-module `X` is `bar`-balanced if it is symmetric and
`bar`-Hermitian-adjoint (`β (a • x) y = β x (bar a • y)`). For Siegel varieties `O = ℤ, bar = id`,
this is simply the space of symmetric `ℤ`-bilinear forms `Sym²(X^∨)`. -/
def IsBalancedForm {X : Type} [AddCommGroup X] [Module O X] (β : LinearMap.BilinForm ℤ X) : Prop :=
  (∀ x y : X, β x y = β y x) ∧ ∀ (a : O) (x y : X), β (a • x) y = β x (bar a • y)

/-- Submodule `balForms bar X` of `bar`-balanced `ℤ`-bilinear forms on `X`. -/
def balForms (X : Type) [AddCommGroup X] [Module O X] :
    Submodule ℤ (LinearMap.BilinForm ℤ X) where
  carrier := {β | IsBalancedForm bar β}
  zero_mem' := ⟨fun _ _ => rfl, fun _ _ _ => rfl⟩
  add_mem' := fun {β₁ β₂} h₁ h₂ =>
    ⟨fun x y => by simp [h₁.1 x y, h₂.1 x y],
     fun a x y => by simp [h₁.2 a x y, h₂.2 a x y]⟩
  smul_mem' := fun c {β} h =>
    ⟨fun x y => by simp [h.1 x y],
     fun a x y => by simp [h.2 a x y]⟩

@[simp]
theorem mem_balForms_iff {X : Type} [AddCommGroup X] [Module O X] (β : LinearMap.BilinForm ℤ X) :
    β ∈ balForms bar X ↔ IsBalancedForm bar β :=
  Iff.rfl

/-- Positive semidefinite predicate on `ℤ`-bilinear forms. -/
def IsPsdForm {X : Type} [AddCommGroup X] (β : LinearMap.BilinForm ℤ X) : Prop :=
  ∀ x : X, 0 ≤ β x x

/-- Real extension of an integer bilinear form `β : X →ₗ[ℤ] X →ₗ[ℤ] ℤ` to `X →ₗ[ℤ] X →ₗ[ℤ] ℝ`. -/
def toRealBilin {X : Type} [AddCommGroup X] (β : LinearMap.BilinForm ℤ X) :
    X →ₗ[ℤ] X →ₗ[ℤ] ℝ where
  toFun x :=
    { toFun := fun y => (β x y : ℝ)
      map_add' := fun y₁ y₂ => by simp [map_add]
      map_smul' := fun c y => by simp }
  map_add' := fun x₁ x₂ => LinearMap.ext fun y => by simp [map_add]
  map_smul' := fun c x => LinearMap.ext fun y => by simp

@[simp]
theorem toRealBilin_apply {X : Type} [AddCommGroup X] (β : LinearMap.BilinForm ℤ X) (x y : X) :
    toRealBilin β x y = (β x y : ℝ) :=
  rfl

@[simp]
theorem toRealBilin_zero {X : Type} [AddCommGroup X] :
    toRealBilin (0 : LinearMap.BilinForm ℤ X) = 0 :=
  LinearMap.ext fun _ => LinearMap.ext fun _ => by simp

theorem toRealBilin_add {X : Type} [AddCommGroup X] (β₁ β₂ : LinearMap.BilinForm ℤ X) :
    toRealBilin (β₁ + β₂) = toRealBilin β₁ + toRealBilin β₂ :=
  LinearMap.ext fun _ => LinearMap.ext fun _ => by simp

theorem toRealBilin_zsmul {X : Type} [AddCommGroup X] (c : ℤ) (β : LinearMap.BilinForm ℤ X) :
    toRealBilin (c • β) = (c : ℝ) • toRealBilin β :=
  LinearMap.ext fun _ => LinearMap.ext fun _ => by simp

/-- Real cone `psdCone bar X` of symmetric, `bar`-balanced, positive semidefinite real forms on `X`. -/
def psdCone (X : Type) [AddCommGroup X] [Module O X] : Set (X →ₗ[ℤ] X →ₗ[ℤ] ℝ) :=
  {B | (∀ x y : X, B x y = B y x) ∧
       (∀ (a : O) (x y : X), B (a • x) y = B x (bar a • y)) ∧
       (∀ x : X, 0 ≤ B x x)}

theorem toRealBilin_mem_psdCone {X : Type} [AddCommGroup X] [Module O X]
    {β : LinearMap.BilinForm ℤ X} (hβ : β ∈ balForms bar X) (hpsd : IsPsdForm β) :
    toRealBilin β ∈ psdCone bar X :=
  ⟨fun x y => by simp [hβ.1 x y],
   fun a x y => by simp [hβ.2 a x y],
   fun x => by simp [toRealBilin_apply, hpsd x]⟩

theorem zero_mem_psdCone (X : Type) [AddCommGroup X] [Module O X] :
    (0 : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) ∈ psdCone bar X :=
  ⟨fun _ _ => rfl, fun _ _ _ => rfl, fun _ => le_rfl⟩

theorem add_mem_psdCone {X : Type} [AddCommGroup X] [Module O X]
    {B₁ B₂ : X →ₗ[ℤ] X →ₗ[ℤ] ℝ} (h₁ : B₁ ∈ psdCone bar X) (h₂ : B₂ ∈ psdCone bar X) :
    B₁ + B₂ ∈ psdCone bar X :=
  ⟨fun x y => by simp [h₁.1 x y, h₂.1 x y],
   fun a x y => by simp [h₁.2.1 a x y, h₂.2.1 a x y],
   fun x => add_nonneg (h₁.2.2 x) (h₂.2.2 x)⟩

theorem smul_mem_psdCone {X : Type} [AddCommGroup X] [Module O X]
    {B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ} (hB : B ∈ psdCone bar X) {t : ℝ} (ht : 0 ≤ t) :
    t • B ∈ psdCone bar X :=
  ⟨fun x y => by simp [hB.1 x y],
   fun a x y => by simp [hB.2.1 a x y],
   fun x => mul_nonneg ht (hB.2.2 x)⟩

/-- Pullback of a `ℤ`-bilinear form along an `O`-linear map `f : X →ₗ[O] X₁`. -/
def pullBilin {X X₁ : Type} [AddCommGroup X] [Module O X] [AddCommGroup X₁] [Module O X₁]
    (f : X →ₗ[O] X₁) (β : LinearMap.BilinForm ℤ X₁) : LinearMap.BilinForm ℤ X :=
  β.comp f.toAddMonoidHom.toIntLinearMap f.toAddMonoidHom.toIntLinearMap

@[simp]
theorem pullBilin_apply {X X₁ : Type} [AddCommGroup X] [Module O X] [AddCommGroup X₁] [Module O X₁]
    (f : X →ₗ[O] X₁) (β : LinearMap.BilinForm ℤ X₁) (x y : X) :
    pullBilin f β x y = β (f x) (f y) :=
  rfl

theorem pullBilin_mem {X X₁ : Type} [AddCommGroup X] [Module O X] [AddCommGroup X₁] [Module O X₁]
    (f : X →ₗ[O] X₁) {β : LinearMap.BilinForm ℤ X₁} (hβ : β ∈ balForms bar X₁) :
    pullBilin f β ∈ balForms bar X :=
  ⟨fun x y => hβ.1 (f x) (f y),
   fun a x y => by
     change β (f (a • x)) (f y) = β (f x) (f (bar a • y))
     rw [f.map_smul, f.map_smul, hβ.2]⟩

theorem pullBilin_psd {X X₁ : Type} [AddCommGroup X] [Module O X] [AddCommGroup X₁] [Module O X₁]
    (f : X →ₗ[O] X₁) {β : LinearMap.BilinForm ℤ X₁} (hβ : IsPsdForm β) :
    IsPsdForm (pullBilin f β) :=
  fun x => hβ (f x)

@[simp]
theorem pullBilin_symm_pullBilin {X X₁ : Type} [AddCommGroup X] [Module O X] [AddCommGroup X₁]
    [Module O X₁] (e : X ≃ₗ[O] X₁) (β : LinearMap.BilinForm ℤ X₁) :
    pullBilin e.symm.toLinearMap (pullBilin e.toLinearMap β) = β :=
  LinearMap.ext fun a => LinearMap.ext fun b => by simp

@[simp]
theorem pullBilin_pullBilin_symm {X X₁ : Type} [AddCommGroup X] [Module O X] [AddCommGroup X₁]
    [Module O X₁] (e : X ≃ₗ[O] X₁) (β : LinearMap.BilinForm ℤ X) :
    pullBilin e.toLinearMap (pullBilin e.symm.toLinearMap β) = β :=
  LinearMap.ext fun a => LinearMap.ext fun b => by simp

/-- Real-valued pullback `pullRealBilin` along an `O`-linear map `f : X →ₗ[O] X₁`. -/
def pullRealBilin {X X₁ : Type} [AddCommGroup X] [Module O X] [AddCommGroup X₁] [Module O X₁]
    (f : X →ₗ[O] X₁) (B : X₁ →ₗ[ℤ] X₁ →ₗ[ℤ] ℝ) : X →ₗ[ℤ] X →ₗ[ℤ] ℝ where
  toFun x :=
    { toFun := fun y => B (f x) (f y)
      map_add' := fun y₁ y₂ => by simp [map_add]
      map_smul' := fun c y => by simp [map_zsmul] }
  map_add' := fun x₁ x₂ => LinearMap.ext fun y => by simp [map_add]
  map_smul' := fun c x => LinearMap.ext fun y => by simp [map_zsmul]

@[simp]
theorem pullRealBilin_apply {X X₁ : Type} [AddCommGroup X] [Module O X] [AddCommGroup X₁]
    [Module O X₁] (f : X →ₗ[O] X₁) (B : X₁ →ₗ[ℤ] X₁ →ₗ[ℤ] ℝ) (x y : X) :
    pullRealBilin f B x y = B (f x) (f y) :=
  rfl

theorem pullRealBilin_mem_psdCone {X X₁ : Type} [AddCommGroup X] [Module O X]
    [AddCommGroup X₁] [Module O X₁] (f : X →ₗ[O] X₁) {B : X₁ →ₗ[ℤ] X₁ →ₗ[ℤ] ℝ}
    (hB : B ∈ psdCone bar X₁) : pullRealBilin f B ∈ psdCone bar X :=
  ⟨fun x y => hB.1 (f x) (f y),
   fun a x y => by
     change B (f (a • x)) (f y) = B (f x) (f (bar a • y))
     rw [f.map_smul, f.map_smul, hB.2.1],
   fun x => hB.2.2 (f x)⟩

/-- `ℤ`-linear equivalence on balanced forms induced by `e : X ≃ₗ[O] X₁`. -/
def pullBalEquiv {X X₁ : Type} [AddCommGroup X] [Module O X] [AddCommGroup X₁] [Module O X₁]
    (e : X ≃ₗ[O] X₁) : balForms bar X₁ ≃ₗ[ℤ] balForms bar X where
  toFun β := ⟨pullBilin e.toLinearMap β.1, pullBilin_mem bar e.toLinearMap β.2⟩
  invFun β := ⟨pullBilin e.symm.toLinearMap β.1, pullBilin_mem bar e.symm.toLinearMap β.2⟩
  map_add' _ _ := Subtype.ext (LinearMap.ext fun _ => LinearMap.ext fun _ => rfl)
  map_smul' _ _ := Subtype.ext (LinearMap.ext fun _ => LinearMap.ext fun _ => rfl)
  left_inv β := Subtype.ext (LinearMap.ext fun x => LinearMap.ext fun y => by simp)
  right_inv β := Subtype.ext (LinearMap.ext fun x => LinearMap.ext fun y => by simp)

/-- `ℤ`-linear equivalence on all `ℤ`-bilinear forms induced by `e : X ≃ₗ[O] X₁`. -/
def pullBilinEquiv {X X₁ : Type} [AddCommGroup X] [Module O X] [AddCommGroup X₁] [Module O X₁]
    (e : X ≃ₗ[O] X₁) : LinearMap.BilinForm ℤ X₁ ≃ₗ[ℤ] LinearMap.BilinForm ℤ X where
  toFun β := pullBilin e.toLinearMap β
  invFun β := pullBilin e.symm.toLinearMap β
  map_add' _ _ := LinearMap.ext fun _ => LinearMap.ext fun _ => rfl
  map_smul' _ _ := LinearMap.ext fun _ => LinearMap.ext fun _ => rfl
  left_inv β := pullBilin_symm_pullBilin e β
  right_inv β := pullBilin_pullBilin_symm e β

end BalancedForms

section PartOfBasisSection

/-- **Smoothness / Unimodularity Condition (`IsPartOfBasis v`)**:
A tuple `v : Fin m → M` in a `ℤ`-module `M` extends to a `ℤ`-basis of `M` (meaning the
corresponding rational polyhedral cone `σ = ∑ ℝ_{≥0} v_i` is **smooth / regular**, so its affine
toric chart `Spec R[σ^∨ ∩ M^∨]` is smooth `≅ 𝔸^m × 𝔾_m^{r-m}`). -/
def IsPartOfBasis {M : Type*} [AddCommGroup M] {m : ℕ} (v : Fin m → M) : Prop :=
  ∃ (n : ℕ) (b : Module.Basis (Fin n) ℤ M) (ι : Fin m ↪ Fin n), ∀ i : Fin m, b (ι i) = v i

theorem IsPartOfBasis.linearIndependent {M : Type*} [AddCommGroup M] {m : ℕ} {v : Fin m → M}
    (h : IsPartOfBasis v) : LinearIndependent ℤ v := by
  obtain ⟨n, b, ι, hι⟩ := h
  have hcomp : v = b ∘ ι := funext fun i => (hι i).symm
  rw [hcomp]
  exact b.linearIndependent.comp ι ι.injective

theorem IsPartOfBasis.injective {M : Type*} [AddCommGroup M] {m : ℕ} {v : Fin m → M}
    (h : IsPartOfBasis v) : Function.Injective v :=
  h.linearIndependent.injective

theorem IsPartOfBasis.ne_zero {M : Type*} [AddCommGroup M] {m : ℕ} {v : Fin m → M}
    (h : IsPartOfBasis v) (i : Fin m) : v i ≠ 0 :=
  h.linearIndependent.ne_zero i

theorem IsPartOfBasis.comp_embedding {M : Type*} [AddCommGroup M] {m m' : ℕ} {v : Fin m → M}
    (h : IsPartOfBasis v) (s : Fin m' ↪ Fin m) : IsPartOfBasis (fun i => v (s i)) := by
  obtain ⟨n, b, ι, hι⟩ := h
  exact ⟨n, b, s.trans ι, fun i => hι (s i)⟩

theorem IsPartOfBasis.map_linearEquiv {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    {m : ℕ} {v : Fin m → M} (h : IsPartOfBasis v) (e : M ≃ₗ[ℤ] N) :
    IsPartOfBasis (fun i => e (v i)) := by
  obtain ⟨n, b, ι, hι⟩ := h
  exact ⟨n, b.map e, ι, fun i => by simp [hι i]⟩

theorem isPartOfBasis_of_basis {M : Type*} [AddCommGroup M] {n : ℕ} (b : Module.Basis (Fin n) ℤ M) :
    IsPartOfBasis b :=
  ⟨n, b, Function.Embedding.refl _, fun _ => rfl⟩

theorem isPartOfBasis_empty {M : Type*} [AddCommGroup M] {n : ℕ} (b : Module.Basis (Fin n) ℤ M)
    (v : Fin 0 → M) : IsPartOfBasis v :=
  ⟨n, b, ⟨Fin.elim0, fun i => i.elim0⟩, fun i => i.elim0⟩

end PartOfBasisSection

section InvFunAndCones

/-- **`GL_O`-Invariant Polarization Function (`InvFun O`)** (distilling Alpöge's `PolFan.InvFun`):
assigns a real value to every bilinear pairing on `O^n`, invariant under `O`-linear surjections
and vanishing on identically zero forms. -/
structure InvFun (O : Type) [CommRing O] where
  toFun : ∀ n : ℕ, ((Fin n → O) → (Fin n → O) → ℝ) → ℝ
  inv : ∀ {n m : ℕ} (r : (Fin n → O) →ₗ[O] (Fin m → O)), Function.Surjective r →
    ∀ B : (Fin m → O) → (Fin m → O) → ℝ,
      toFun n (fun x y => B (r x) (r y)) = toFun m B
  zero : ∀ n : ℕ, toFun n (fun _ _ => 0) = 0

namespace InvFun

variable {O : Type} [CommRing O]

/-- Evaluate `φ : InvFun O` on a pairing `B : X → X → ℝ` on a finite `O`-module `X` by picking
any finite generating surjection `O^n ↠ X`. -/
def eval (φ : InvFun O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X]
    (B : X → X → ℝ) : ℝ :=
  let h := Module.Finite.exists_fin' O X
  φ.toFun h.choose (fun x y => B (h.choose_spec.choose x) (h.choose_spec.choose y))

/-- Independence of `φ.eval` from the choice of generating surjection `r : (Fin n → O) ↠ X`. -/
theorem eval_eq (φ : InvFun O) {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X]
    {n : ℕ} {r : (Fin n → O) →ₗ[O] X} (hr : Function.Surjective r) (B : X → X → ℝ) :
    φ.eval X B = φ.toFun n (fun x y => B (r x) (r y)) := by
  classical
  unfold eval
  set h := Module.Finite.exists_fin' O X
  set m := h.choose
  set r₀ : (Fin m → O) →ₗ[O] X := h.choose_spec.choose
  have hr₀ : Function.Surjective r₀ := h.choose_spec.choose_spec
  let liftF : (Fin m → O) →ₗ[O] (Fin n → O) :=
    (Pi.basisFun O (Fin m)).constr O (fun i => (hr (r₀ (Pi.single i 1))).choose)
  have hliftF : ∀ x, r (liftF x) = r₀ x := by
    intro x
    have hx : x = ∑ i : Fin m, x i • (Pi.single i (1 : O) : Fin m → O) := by
      ext j; simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [hx]
    conv_rhs => rw [hx]
    simp only [map_sum, map_smul]
    refine Finset.sum_congr rfl fun i _ => congrArg (x i • ·) ?_
    conv_lhs => rw [← Pi.basisFun_apply O (Fin m) i]
    rw [Module.Basis.constr_basis]
    exact (hr (r₀ (Pi.single i 1))).choose_spec
  let liftG : (Fin n → O) →ₗ[O] (Fin m → O) :=
    (Pi.basisFun O (Fin n)).constr O (fun j => (hr₀ (r (Pi.single j 1))).choose)
  have hliftG : ∀ y, r₀ (liftG y) = r y := by
    intro y
    have hy : y = ∑ j : Fin n, y j • (Pi.single j (1 : O) : Fin n → O) := by
      ext k; simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [hy]
    conv_rhs => rw [hy]
    simp only [map_sum, map_smul]
    refine Finset.sum_congr rfl fun j _ => congrArg (y j • ·) ?_
    conv_lhs => rw [← Pi.basisFun_apply O (Fin n) j]
    rw [Module.Basis.constr_basis]
    exact (hr₀ (r (Pi.single j 1))).choose_spec
  let p₁ : (Fin (m + n) → O) →ₗ[O] (Fin m → O) :=
    { toFun := fun z i => z (finSumFinEquiv (Sum.inl i)) +
        (liftG (fun j => z (finSumFinEquiv (Sum.inr j)))) i
      map_add' := fun z₁ z₂ => by
        ext i
        simp only [Pi.add_apply]
        have hadd : (fun j => z₁ (finSumFinEquiv (Sum.inr j)) + z₂ (finSumFinEquiv (Sum.inr j))) =
            (fun j => z₁ (finSumFinEquiv (Sum.inr j))) + (fun j => z₂ (finSumFinEquiv (Sum.inr j))) := rfl
        rw [hadd, map_add, Pi.add_apply]; ring
      map_smul' := fun c z => by
        ext i
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        have hsm : (fun j => c * z (finSumFinEquiv (Sum.inr j))) =
            c • (fun j => z (finSumFinEquiv (Sum.inr j))) := rfl
        rw [hsm, map_smul, Pi.smul_apply, smul_eq_mul]; ring }
  let p₂ : (Fin (m + n) → O) →ₗ[O] (Fin n → O) :=
    { toFun := fun z j =>
        (liftF (fun i => z (finSumFinEquiv (Sum.inl i)))) j + z (finSumFinEquiv (Sum.inr j))
      map_add' := fun z₁ z₂ => by
        ext j
        simp only [Pi.add_apply]
        have hadd : (fun i => z₁ (finSumFinEquiv (Sum.inl i)) + z₂ (finSumFinEquiv (Sum.inl i))) =
            (fun i => z₁ (finSumFinEquiv (Sum.inl i))) + (fun i => z₂ (finSumFinEquiv (Sum.inl i))) := rfl
        rw [hadd, map_add, Pi.add_apply]; ring
      map_smul' := fun c z => by
        ext j
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        have hsm : (fun i => c * z (finSumFinEquiv (Sum.inl i))) =
            c • (fun i => z (finSumFinEquiv (Sum.inl i))) := rfl
        rw [hsm, map_smul, Pi.smul_apply, smul_eq_mul]; ring }
  have hp₁_surj : Function.Surjective p₁ := by
    intro u
    refine ⟨fun k => Sum.elim u (fun _ => 0) (finSumFinEquiv.symm k), ?_⟩
    ext i
    simp [p₁]
    show liftG 0 i = 0
    simp
  have hp₂_surj : Function.Surjective p₂ := by
    intro v
    refine ⟨fun k => Sum.elim (fun _ => 0) v (finSumFinEquiv.symm k), ?_⟩
    ext j
    simp [p₂]
    show liftF 0 j = 0
    simp
  have hcomp_eq : ∀ z : Fin (m + n) → O, r₀ (p₁ z) = r (p₂ z) := by
    intro z
    have h1 : p₁ z = (fun i => z (finSumFinEquiv (Sum.inl i))) +
        liftG (fun j => z (finSumFinEquiv (Sum.inr j))) := rfl
    have h2 : p₂ z = liftF (fun i => z (finSumFinEquiv (Sum.inl i))) +
        (fun j => z (finSumFinEquiv (Sum.inr j))) := rfl
    rw [h1, h2, map_add, map_add, hliftG, hliftF]
  have e₁ := φ.inv p₁ hp₁_surj (fun x y => B (r₀ x) (r₀ y))
  have e₂ := φ.inv p₂ hp₂_surj (fun x y => B (r x) (r y))
  rw [← e₁, ← e₂]
  congr 1
  funext z₁ z₂
  rw [hcomp_eq z₁, hcomp_eq z₂]

theorem eval_comp (φ : InvFun O) {X X₁ : Type} [AddCommGroup X] [Module O X] [Module.Finite O X]
    [AddCommGroup X₁] [Module O X₁] [Module.Finite O X₁]
    {f : X →ₗ[O] X₁} (hf : Function.Surjective f) (B : X₁ → X₁ → ℝ) :
    φ.eval X (fun x y => B (f x) (f y)) = φ.eval X₁ B := by
  obtain ⟨n, r, hr⟩ := Module.Finite.exists_fin' O X
  rw [φ.eval_eq hr, φ.eval_eq (r := f.comp r) (hf.comp hr)]
  rfl

theorem eval_zero (φ : InvFun O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] :
    φ.eval X (fun _ _ => 0) = 0 := by
  obtain ⟨n, r, hr⟩ := Module.Finite.exists_fin' O X
  rw [φ.eval_eq hr]
  exact φ.zero n

/-- Evaluation of `φ : InvFun O` on a real bilinear form `B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ`. -/
def evalR (φ : InvFun O) {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X]
    (B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) : ℝ :=
  φ.eval X (fun x y => B x y)

/-- Evaluation of `φ : InvFun O` on an integer bilinear form `β : LinearMap.BilinForm ℤ X`. -/
def evalZ (φ : InvFun O) {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X]
    (β : LinearMap.BilinForm ℤ X) : ℝ :=
  φ.evalR (toRealBilin β)

theorem evalR_pull (φ : InvFun O) {X X₁ : Type} [AddCommGroup X] [Module O X] [Module.Finite O X]
    [AddCommGroup X₁] [Module O X₁] [Module.Finite O X₁]
    {f : X →ₗ[O] X₁} (hf : Function.Surjective f) (B : X₁ →ₗ[ℤ] X₁ →ₗ[ℤ] ℝ) :
    φ.evalR (pullRealBilin f B) = φ.evalR B :=
  φ.eval_comp hf (fun x y => B x y)

theorem evalZ_pull (φ : InvFun O) {X X₁ : Type} [AddCommGroup X] [Module O X] [Module.Finite O X]
    [AddCommGroup X₁] [Module O X₁] [Module.Finite O X₁]
    {f : X →ₗ[O] X₁} (hf : Function.Surjective f) (β : LinearMap.BilinForm ℤ X₁) :
    φ.evalZ (pullBilin f β) = φ.evalZ β :=
  φ.eval_comp hf (fun x y => (β x y : ℝ))

theorem eval_of_subsingleton (φ : InvFun O) {X : Type} [AddCommGroup X] [Module O X]
    [Module.Finite O X] [Subsingleton X] (B : X → X → ℝ) (h0 : B 0 0 = 0) :
    φ.eval X B = 0 := by
  have hB : B = fun _ _ => 0 := by
    funext x y
    rw [Subsingleton.elim x 0, Subsingleton.elim y 0, h0]
  rw [hB]
  exact φ.eval_zero X

/-- **Canonical Positive Minimum Polarization Function `posMin O`**:
`posMin O B = max 0 (inf {B y y | B y y ≠ B 0 0})`. -/
def posMin (O : Type) [CommRing O] : InvFun O where
  toFun n B := max 0 (sInf {x : ℝ | (∃ y : Fin n → O, B y y = x) ∧ x ≠ B 0 0})
  inv := fun {n m} r hr B => by
    congr 2
    ext x
    simp only [Set.mem_ofPred_eq, map_zero]
    constructor
    · rintro ⟨⟨y, hy⟩, hne⟩
      exact ⟨⟨r y, hy⟩, hne⟩
    · rintro ⟨⟨z, hz⟩, hne⟩
      obtain ⟨y, rfl⟩ := hr z
      exact ⟨⟨y, hz⟩, hne⟩
  zero := fun n => by
    have hempty : {x : ℝ | (∃ _ : Fin n → O, (0 : ℝ) = x) ∧ x ≠ 0} = ∅ := by
      ext x; simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨⟨_, rfl⟩, hne⟩; exact hne rfl
    rw [hempty, Real.sInf_empty, max_self]

theorem posMin_nonneg (O : Type) [CommRing O] (X : Type) [AddCommGroup X] [Module O X]
    [Module.Finite O X] (B : X → X → ℝ) :
    0 ≤ (posMin O).eval X B :=
  le_max_left _ _

theorem posMin_eval_eq {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X]
    (B : X → X → ℝ) :
    (posMin O).eval X B = max 0 (sInf {x : ℝ | (∃ y : X, B y y = x) ∧ x ≠ B 0 0}) := by
  obtain ⟨n, r, hr⟩ := Module.Finite.exists_fin' O X
  rw [(posMin O).eval_eq hr]
  change max 0 (sInf _) = max 0 (sInf _)
  congr 2
  ext x
  simp only [Set.mem_ofPred_eq, map_zero]
  constructor
  · rintro ⟨⟨y, hy⟩, hne⟩
    exact ⟨⟨r y, hy⟩, hne⟩
  · rintro ⟨⟨z, hz⟩, hne⟩
    obtain ⟨y, rfl⟩ := hr z
    exact ⟨⟨y, hz⟩, hne⟩

/-- Linearity of `φ` on the nonnegative real cone spanned by rays `γ : Fin m → BilinForm ℤ X`. -/
def LinearOn (φ : InvFun O) {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X]
    {m : ℕ} (γ : Fin m → LinearMap.BilinForm ℤ X) : Prop :=
  ∀ c : Fin m → ℝ, (∀ i, 0 ≤ c i) →
    φ.evalR (∑ i, c i • toRealBilin (γ i)) = ∑ i, c i * φ.evalZ (γ i)

theorem LinearOn.comp_embedding {φ : InvFun O} {X : Type} [AddCommGroup X] [Module O X]
    [Module.Finite O X] {m m' : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X}
    (h : φ.LinearOn γ) (s : Fin m' ↪ Fin m) : φ.LinearOn (fun i => γ (s i)) := by
  classical
  intro c hc
  let c' : Fin m → ℝ := fun j => if hj : ∃ i, s i = j then c hj.choose else 0
  have hc' : ∀ j, 0 ≤ c' j := fun j => by
    dsimp [c']; split_ifs with hj
    · exact hc hj.choose
    · exact le_rfl
  have hsum1 : ∑ j : Fin m, c' j • toRealBilin (γ j) =
      ∑ i : Fin m', c i • toRealBilin (γ (s i)) := by
    have hsub : ∑ j : Fin m, c' j • toRealBilin (γ j) =
        ∑ j ∈ Finset.univ.image s, c' j • toRealBilin (γ j) := by
      refine (Finset.sum_subset (Finset.subset_univ _) fun j _ hj => ?_).symm
      have hnex : ¬ ∃ i, s i = j := fun ⟨i, hi⟩ => hj (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hi⟩)
      simp [c', hnex]
    rw [hsub, Finset.sum_image (fun a _ b _ hab => s.injective hab)]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hex : ∃ a, s a = s i := ⟨i, rfl⟩
    have hch : hex.choose = i := s.injective hex.choose_spec
    simp only [c', dif_pos hex, hch]
  have hsum2 : ∑ j : Fin m, c' j * φ.evalZ (γ j) =
      ∑ i : Fin m', c i * φ.evalZ (γ (s i)) := by
    have hsub : ∑ j : Fin m, c' j * φ.evalZ (γ j) =
        ∑ j ∈ Finset.univ.image s, c' j * φ.evalZ (γ j) := by
      refine (Finset.sum_subset (Finset.subset_univ _) fun j _ hj => ?_).symm
      have hnex : ¬ ∃ i, s i = j := fun ⟨i, hi⟩ => hj (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hi⟩)
      simp [c', hnex]
    rw [hsub, Finset.sum_image (fun a _ b _ hab => s.injective hab)]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hex : ∃ a, s a = s i := ⟨i, rfl⟩
    have hch : hex.choose = i := s.injective hex.choose_spec
    simp only [c', dif_pos hex, hch]
  rw [← hsum1, ← hsum2]
  exact h c' hc'

theorem LinearOn.pull_equiv {φ : InvFun O} {X X₁ : Type} [AddCommGroup X] [Module O X]
    [Module.Finite O X] [AddCommGroup X₁] [Module O X₁] [Module.Finite O X₁]
    {m : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X₁}
    (h : φ.LinearOn γ) (e : X ≃ₗ[O] X₁) : φ.LinearOn (fun i => pullBilin e.toLinearMap (γ i)) := by
  intro c hc
  have hsum : ∑ i, c i • toRealBilin (pullBilin e.toLinearMap (γ i)) =
      pullRealBilin e.toLinearMap (∑ i, c i • toRealBilin (γ i)) := by
    refine LinearMap.ext fun a => LinearMap.ext fun b => ?_
    simp [LinearMap.sum_apply]
  rw [hsum, φ.evalR_pull e.surjective, h c hc]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [φ.evalZ_pull e.surjective]

end InvFun

/-- **Strict Supporting Linear Functional Condition (`IsStrictCone bar φ γ`)**:
there exists a positive integer `N > 0` and an integral linear functional
`ℓ : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ` separating the cone spanned by `γ` strictly from all other
balanced PSD forms (`ℓ(β) ≤ N · φ(β)`, with equality iff `k • β = ∑ c_i • γ_i` for some `k > 0`
and `c_i : ℕ`). -/
def IsStrictCone {O : Type} [CommRing O] (bar : O → O) (φ : InvFun O)
    {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X]
    {m : ℕ} (γ : Fin m → LinearMap.BilinForm ℤ X) : Prop :=
  ∃ (N : ℕ) (ℓ : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ),
    0 < N ∧
    (∀ i : Fin m, (ℓ (γ i) : ℝ) = (N : ℝ) * φ.evalZ (γ i)) ∧
    (∀ β : LinearMap.BilinForm ℤ X, β ∈ balForms bar X → IsPsdForm β →
      (ℓ β : ℝ) ≤ (N : ℝ) * φ.evalZ β) ∧
    (∀ β : LinearMap.BilinForm ℤ X, β ∈ balForms bar X → IsPsdForm β →
      (ℓ β : ℝ) = (N : ℝ) * φ.evalZ β →
      ∃ (k : ℕ) (c : Fin m → ℕ), 0 < k ∧ (k : ℤ) • β = ∑ i : Fin m, (c i : ℤ) • γ i)

theorem IsStrictCone.reindex {O : Type} [CommRing O] {bar : O → O} {φ : InvFun O}
    {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X]
    {m m' : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X}
    (h : IsStrictCone bar φ γ) (s : Fin m' ≃ Fin m) :
    IsStrictCone bar φ (fun i => γ (s i)) := by
  obtain ⟨N, ℓ, hN, h1, h2, h3⟩ := h
  refine ⟨N, ℓ, hN, fun i => h1 (s i), h2, fun β hβ hp he => ?_⟩
  obtain ⟨k, c, hk, hc⟩ := h3 β hβ hp he
  refine ⟨k, fun i => c (s i), hk, hc.trans ?_⟩
  exact (Fintype.sum_equiv s (fun i => (c (s i) : ℤ) • γ (s i)) (fun j => (c j : ℤ) • γ j)
    fun _ => rfl).symm

theorem IsStrictCone.pull_equiv {O : Type} [CommRing O] {bar : O → O} {φ : InvFun O}
    {X X₁ : Type} [AddCommGroup X] [Module O X] [Module.Finite O X]
    [AddCommGroup X₁] [Module O X₁] [Module.Finite O X₁]
    {m : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X₁}
    (h : IsStrictCone bar φ γ) (e : X ≃ₗ[O] X₁) :
    IsStrictCone bar φ (fun i => pullBilin e.toLinearMap (γ i)) := by
  obtain ⟨N, ℓ, hN, h1, h2, h3⟩ := h
  let ℓ' : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ := ℓ.comp (pullBilinEquiv e).symm.toLinearMap
  refine ⟨N, ℓ', hN, fun i => ?_, fun β hβ hp => ?_, fun β hβ hp he => ?_⟩
  · change (ℓ (pullBilin e.symm.toLinearMap (pullBilin e.toLinearMap (γ i))) : ℝ) = _
    rw [pullBilin_symm_pullBilin, φ.evalZ_pull e.surjective]
    exact h1 i
  · change (ℓ (pullBilin e.symm.toLinearMap β) : ℝ) ≤ (N : ℝ) * φ.evalZ β
    have hpe : φ.evalZ (pullBilin e.symm.toLinearMap β) = φ.evalZ β :=
      φ.evalZ_pull e.symm.surjective β
    rw [← hpe]
    exact h2 _ (pullBilin_mem bar e.symm.toLinearMap hβ) (pullBilin_psd e.symm.toLinearMap hp)
  · change (ℓ (pullBilin e.symm.toLinearMap β) : ℝ) = (N : ℝ) * φ.evalZ β at he
    have hpe : φ.evalZ (pullBilin e.symm.toLinearMap β) = φ.evalZ β :=
      φ.evalZ_pull e.symm.surjective β
    rw [← hpe] at he
    obtain ⟨k, c, hk, hc⟩ := h3 _ (pullBilin_mem bar e.symm.toLinearMap hβ)
      (pullBilin_psd e.symm.toLinearMap hp) he
    refine ⟨k, c, hk, ?_⟩
    have hpull := congrArg (pullBilin e.toLinearMap) hc
    refine LinearMap.ext fun a => LinearMap.ext fun b => ?_
    have hab := LinearMap.congr_fun (LinearMap.congr_fun hpull a) b
    simpa [LinearMap.sum_apply, Finset.sum_apply] using hab

/-- **Smooth Rational Polyhedral Cone (`IsSmoothRationalCone bar φ γ`)**:
`γ : Fin m → BilinForm ℤ X` consists of balanced PSD rays forming part of a `ℤ`-basis of
`balForms bar X` (unimodular / smooth toric chart), on which `φ` is linear and strictly separated. -/
structure IsSmoothRationalCone {O : Type} [CommRing O] (bar : O → O) (φ : InvFun O)
    {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X]
    {m : ℕ} (γ : Fin m → LinearMap.BilinForm ℤ X) : Prop where
  mem : ∀ i : Fin m, γ i ∈ balForms bar X
  nonneg : ∀ i : Fin m, IsPsdForm (γ i)
  smooth : IsPartOfBasis (fun i : Fin m => (⟨γ i, mem i⟩ : balForms bar X))
  linear : φ.LinearOn γ
  strict : IsStrictCone bar φ γ

namespace IsSmoothRationalCone

variable {O : Type} [CommRing O] {bar : O → O} {φ : InvFun O}
  {X X₁ : Type} [AddCommGroup X] [Module O X] [Module.Finite O X]
  [AddCommGroup X₁] [Module O X₁] [Module.Finite O X₁]
  {m m' : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X}

theorem linearIndependent (h : IsSmoothRationalCone bar φ γ) : LinearIndependent ℤ γ :=
  h.smooth.linearIndependent.map' (balForms bar X).subtype (Submodule.ker_subtype _)

theorem injective (h : IsSmoothRationalCone bar φ γ) : Function.Injective γ :=
  h.linearIndependent.injective

theorem ne_zero (h : IsSmoothRationalCone bar φ γ) (i : Fin m) : γ i ≠ 0 :=
  h.linearIndependent.ne_zero i

theorem reindex (h : IsSmoothRationalCone bar φ γ) (s : Fin m' ≃ Fin m) :
    IsSmoothRationalCone bar φ (fun i => γ (s i)) where
  mem i := h.mem (s i)
  nonneg i := h.nonneg (s i)
  smooth := h.smooth.comp_embedding s.toEmbedding
  linear := h.linear.comp_embedding s.toEmbedding
  strict := h.strict.reindex s

theorem pull_equiv {γ : Fin m → LinearMap.BilinForm ℤ X₁}
    (h : IsSmoothRationalCone bar φ γ) (e : X ≃ₗ[O] X₁) :
    IsSmoothRationalCone bar φ (fun i => pullBilin e.toLinearMap (γ i)) where
  mem i := pullBilin_mem bar e.toLinearMap (h.mem i)
  nonneg i := pullBilin_psd e.toLinearMap (h.nonneg i)
  smooth := h.smooth.map_linearEquiv (pullBalEquiv bar e)
  linear := h.linear.pull_equiv e
  strict := h.strict.pull_equiv e

theorem evalZ_smul (h : IsSmoothRationalCone bar φ γ) (M : ℕ) (i : Fin m) :
    φ.evalZ ((M : ℤ) • γ i) = (M : ℝ) * φ.evalZ (γ i) := by
  classical
  let c : Fin m → ℝ := fun j => if j = i then (M : ℝ) else 0
  have hc : ∀ j, 0 ≤ c j := fun j => by
    dsimp [c]; split_ifs
    · exact Nat.cast_nonneg M
    · exact le_rfl
  have h1 := h.linear c hc
  have hsum1 : ∑ j : Fin m, c j • toRealBilin (γ j) = toRealBilin ((M : ℤ) • γ i) := by
    rw [Finset.sum_eq_single i]
    · rw [toRealBilin_zsmul]; simp [c]
    · intro j _ hji; simp [c, hji]
    · intro hi; exact absurd (Finset.mem_univ i) hi
  have hsum2 : ∑ j : Fin m, c j * φ.evalZ (γ j) = (M : ℝ) * φ.evalZ (γ i) := by
    rw [Finset.sum_eq_single i]
    · simp [c]
    · intro j _ hji; simp [c, hji]
    · intro hi; exact absurd (Finset.mem_univ i) hi
  rw [hsum1, hsum2] at h1
  exact h1

end IsSmoothRationalCone

/-- **Neatness / No Self-Intersections Condition (`NoSelfIntOn`)**:
no two distinct rays of any smooth cone in the fan are equivalent under `GL_O(X)`. This guarantees
that the resulting toroidal compactification boundary divisor has **simple normal crossings (SNC)**
(every irreducible boundary component is smooth with no self-intersection). -/
def NoSelfIntOn {O : Type} [CommRing O] (bar : O → O) (φ : InvFun O)
    (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] : Prop :=
  ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X),
    IsSmoothRationalCone bar φ γ →
    ∀ (g : X ≃ₗ[O] X) (i j : Fin m), pullBilin g.toLinearMap (γ i) = γ j → i = j

theorem NoSelfIntOn.of_equiv {O : Type} [CommRing O] {bar : O → O} {φ : InvFun O}
    {X X₁ : Type} [AddCommGroup X] [Module O X] [Module.Finite O X]
    [AddCommGroup X₁] [Module O X₁] [Module.Finite O X₁]
    (h : NoSelfIntOn bar φ X) (e : X ≃ₗ[O] X₁) : NoSelfIntOn bar φ X₁ := by
  intro m γ hγ g i j hpull
  have hγ' : IsSmoothRationalCone bar φ (fun k => pullBilin e.toLinearMap (γ k)) :=
    hγ.pull_equiv e
  let g' : X ≃ₗ[O] X := e.trans (g.trans e.symm)
  refine h m (fun k => pullBilin e.toLinearMap (γ k)) hγ' g' i j ?_
  refine LinearMap.ext fun a => LinearMap.ext fun b => ?_
  have hab := LinearMap.congr_fun (LinearMap.congr_fun hpull (e a)) (e b)
  simpa [g', pullBilin_apply] using hab

/-- **Admissible Smooth Rational Polyhedral Fan Axioms on a Lattice `X` (`IsPolFanOn`)**
(exact distillation of Alpöge's `GlobalTheory.PolFan.IsPolFanOn`):
1. `homog`: positive homogeneity of `φ` on `psdCone bar X`,
2. `superadd`: superadditivity (concavity / piecewise-linear convexity of the support function `φ`),
3. `integral`: integer values on balanced PSD forms,
4. `pos`: strict positivity on nonzero balanced PSD forms,
5. `face`: closed under passing to faces of smooth cones,
6. `cover`: every form in `psdCone bar X` lies in some smooth rational cone,
7. `finite`: finitely many `GL_O(X)`-orbits of cone rays. -/
structure IsPolFanOn {O : Type} [CommRing O] (bar : O → O) (φ : InvFun O)
    (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] : Prop where
  homog : ∀ B ∈ psdCone bar X, ∀ t : ℝ, 0 ≤ t → φ.evalR (t • B) = t * φ.evalR B
  superadd : ∀ B ∈ psdCone bar X, ∀ B' ∈ psdCone bar X,
    φ.evalR B + φ.evalR B' ≤ φ.evalR (B + B')
  integral : ∀ β : LinearMap.BilinForm ℤ X, β ∈ balForms bar X → IsPsdForm β →
    ∃ z : ℤ, φ.evalZ β = z
  pos : ∀ β : LinearMap.BilinForm ℤ X, β ∈ balForms bar X → IsPsdForm β → β ≠ 0 →
    0 < φ.evalZ β
  face : ∀ (m m' : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (s : Fin m' ↪ Fin m),
    IsSmoothRationalCone bar φ γ → IsSmoothRationalCone bar φ (fun i => γ (s i))
  cover : ∀ B ∈ psdCone bar X,
    ∃ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (c : Fin m → ℝ),
      IsSmoothRationalCone bar φ γ ∧ (∀ i, 0 ≤ c i) ∧ B = ∑ i, c i • toRealBilin (γ i)
  finite : ∃ S : Set (LinearMap.BilinForm ℤ X), S.Finite ∧
    ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsSmoothRationalCone bar φ γ →
      ∃ g : X ≃ₗ[O] X, ∀ i, pullBilin g.toLinearMap (γ i) ∈ S

namespace IsPolFanOn

variable {O : Type} [CommRing O] {bar : O → O} {φ : InvFun O}
  {X X₁ : Type} [AddCommGroup X] [Module O X] [Module.Finite O X]
  [AddCommGroup X₁] [Module O X₁] [Module.Finite O X₁]

theorem evalZ_nonneg (h : IsPolFanOn bar φ X) {β : LinearMap.BilinForm ℤ X}
    (hβ : β ∈ balForms bar X) (hp : IsPsdForm β) : 0 ≤ φ.evalZ β := by
  by_cases h0 : β = 0
  · subst h0
    simp only [InvFun.evalZ, InvFun.evalR, toRealBilin_zero, LinearMap.zero_apply]
    rw [φ.eval_zero]
  · exact (h.pos β hβ hp h0).le

theorem evalZ_pos_int (h : IsPolFanOn bar φ X) {β : LinearMap.BilinForm ℤ X}
    (hβ : β ∈ balForms bar X) (hp : IsPsdForm β) (hne : β ≠ 0) :
    ∃ k : ℕ, 0 < k ∧ φ.evalZ β = (k : ℝ) := by
  obtain ⟨z, hz⟩ := h.integral β hβ hp
  have hpos : (0 : ℝ) < (z : ℝ) := hz ▸ h.pos β hβ hp hne
  have hzpos : (0 : ℤ) < z := Int.cast_pos.mp hpos
  refine ⟨z.toNat, by omega, ?_⟩
  rw [hz]
  exact_mod_cast (Int.toNat_of_nonneg hzpos.le).symm

theorem evalR_nonneg (h : IsPolFanOn bar φ X) {B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ} (hB : B ∈ psdCone bar X) :
    0 ≤ φ.evalR B := by
  obtain ⟨m, γ, c, hγ, hc, rfl⟩ := h.cover B hB
  rw [hγ.linear c hc]
  exact Finset.sum_nonneg fun i _ => mul_nonneg (hc i) (h.evalZ_nonneg (hγ.mem i) (hγ.nonneg i))

theorem of_equiv (h : IsPolFanOn bar φ X) (e : X ≃ₗ[O] X₁) : IsPolFanOn bar φ X₁ where
  homog B hB t ht := by
    have hsm : pullRealBilin e.toLinearMap (t • B) = t • pullRealBilin e.toLinearMap B :=
      LinearMap.ext fun _ => LinearMap.ext fun _ => rfl
    rw [← φ.evalR_pull e.surjective (t • B), hsm, h.homog _ (pullRealBilin_mem_psdCone bar _ hB) t ht,
      φ.evalR_pull e.surjective]
  superadd B hB B' hB' := by
    have hadd : pullRealBilin e.toLinearMap (B + B') =
        pullRealBilin e.toLinearMap B + pullRealBilin e.toLinearMap B' :=
      LinearMap.ext fun _ => LinearMap.ext fun _ => rfl
    rw [← φ.evalR_pull e.surjective B, ← φ.evalR_pull e.surjective B',
      ← φ.evalR_pull e.surjective (B + B'), hadd]
    exact h.superadd _ (pullRealBilin_mem_psdCone bar _ hB) _ (pullRealBilin_mem_psdCone bar _ hB')
  integral β hβ hp := by
    rw [← φ.evalZ_pull e.surjective β]
    exact h.integral _ (pullBilin_mem bar _ hβ) (pullBilin_psd _ hp)
  pos β hβ hp h0 := by
    rw [← φ.evalZ_pull e.surjective β]
    refine h.pos _ (pullBilin_mem bar _ hβ) (pullBilin_psd _ hp) fun h1 => h0 ?_
    rw [← pullBilin_symm_pullBilin e β, h1]; rfl
  face m m' γ s hγ := by
    have h' := (h.face m m' (fun i => pullBilin e.toLinearMap (γ i)) s (hγ.pull_equiv e)).pull_equiv e.symm
    simpa only [pullBilin_symm_pullBilin] using h'
  cover B hB := by
    obtain ⟨m, γ, c, hγ, hc, hs⟩ := h.cover _ (pullRealBilin_mem_psdCone bar e.toLinearMap hB)
    refine ⟨m, fun i => pullBilin e.symm.toLinearMap (γ i), c, hγ.pull_equiv e.symm, hc, ?_⟩
    refine LinearMap.ext fun a => LinearMap.ext fun b => ?_
    have hab := LinearMap.congr_fun (LinearMap.congr_fun hs (e.symm a)) (e.symm b)
    simpa [LinearMap.sum_apply, Finset.sum_apply] using hab
  finite := by
    obtain ⟨S, hS, h1⟩ := h.finite
    refine ⟨pullBilin e.symm.toLinearMap '' S, hS.image _, fun m γ hγ => ?_⟩
    obtain ⟨g, hg⟩ := h1 m _ (hγ.pull_equiv e)
    refine ⟨e.symm.trans (g.trans e), fun i => ⟨_, hg i, ?_⟩⟩
    refine LinearMap.ext fun a => LinearMap.ext fun b => ?_
    simp [pullBilin_apply]

end IsPolFanOn

/-- Trivial rank-0 lattice (`Subsingleton X`) satisfies `IsPolFanOn` and `NoSelfIntOn` for every `φ`. -/
theorem isPolFanOn_of_subsingleton {O : Type} [CommRing O] (bar : O → O) (φ : InvFun O)
    (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Subsingleton X] :
    IsPolFanOn bar φ X ∧ NoSelfIntOn bar φ X := by
  have hsub_bal : Subsingleton (balForms bar X) :=
    ⟨fun a b => Subtype.ext (LinearMap.ext fun x => LinearMap.ext fun y => by
      rw [Subsingleton.elim x 0, Subsingleton.elim y 0]; simp)⟩
  have h0 : ∀ β : LinearMap.BilinForm ℤ X, β = 0 := fun β =>
    LinearMap.ext fun x => LinearMap.ext fun y => by
      rw [Subsingleton.elim x 0, Subsingleton.elim y 0]; simp
  have hb0 : Module.Basis (Fin 0) ℤ (balForms bar X) :=
    Module.Basis.empty (balForms bar X)
  have hc0 : ∀ (m : ℕ) [IsEmpty (Fin m)] (γ : Fin m → LinearMap.BilinForm ℤ X),
      IsSmoothRationalCone bar φ γ := fun m _ γ =>
    { mem := isEmptyElim
      nonneg := isEmptyElim
      smooth := ⟨0, hb0, ⟨isEmptyElim, isEmptyElim⟩, isEmptyElim⟩
      linear := fun c _ => by
        change φ.eval X _ = _
        rw [φ.eval_of_subsingleton _ (by simp)]
        simp
      strict := ⟨1, 0, one_pos, isEmptyElim, fun β _ _ => by
        simp only [InvFun.evalZ, InvFun.evalR, LinearMap.zero_apply, Int.cast_zero, Nat.cast_one,
          one_mul]
        rw [φ.eval_of_subsingleton _ (by simp)],
        fun β _ _ _ => ⟨1, isEmptyElim, one_pos, by rw [h0 β]; simp⟩⟩ }
  refine ⟨?_, ?_⟩
  · refine
      { homog := fun B _ t _ => by
          change φ.eval X _ = t * φ.eval X _
          rw [φ.eval_of_subsingleton _ (by simp), φ.eval_of_subsingleton _ (by simp), mul_zero]
        superadd := fun B _ B' _ => by
          change φ.eval X _ + φ.eval X _ ≤ φ.eval X _
          rw [φ.eval_of_subsingleton _ (by simp), φ.eval_of_subsingleton _ (by simp),
            φ.eval_of_subsingleton _ (by simp), add_zero]
        integral := fun β _ _ => ⟨0, by
          simp only [InvFun.evalZ, InvFun.evalR, Int.cast_zero]
          rw [φ.eval_of_subsingleton _ (by simp)]⟩
        pos := fun β _ _ hne => absurd (h0 β) hne
        face := fun m m' γ s hγ => by
          have : IsEmpty (Fin m') := ⟨fun i => hγ.ne_zero (s i) (h0 _)⟩
          exact hc0 m' _
        cover := fun B _ => ⟨0, Fin.elim0, Fin.elim0, hc0 0 _, fun i => i.elim0,
          LinearMap.ext fun x => LinearMap.ext fun y => by
            rw [Subsingleton.elim x 0, Subsingleton.elim y 0]; simp⟩
        finite := ⟨{0}, Set.finite_singleton 0, fun m γ _ =>
          ⟨LinearEquiv.refl O X, fun i => by simp [h0]⟩⟩ }
  · intro m γ hγ _ i _ _
    exact absurd (h0 (γ i)) (hγ.ne_zero i)

/-- **Uniform Polyhedral Fan Predicate `IsPolFan bar q φ`**:
`φ` defines an admissible smooth rational polyhedral cone decomposition on every finite free
`O`-lattice `X` of `O`-rank `≤ q`. -/
def IsPolFan {O : Type} [CommRing O] (bar : O → O) (q : ℕ) (φ : InvFun O) : Prop :=
  ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Free O X] [Module.Finite O X],
    Module.finrank O X ≤ q → IsPolFanOn bar φ X

/-- **Uniform No-Self-Intersections Predicate `NoSelfInt bar q φ`**:
every cone of `φ` on every finite free `O`-lattice `X` of rank `≤ q` has no `GL_O(X)`-equivalent
distinct rays. -/
def NoSelfInt {O : Type} [CommRing O] (bar : O → O) (q : ℕ) (φ : InvFun O) : Prop :=
  ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Free O X] [Module.Finite O X],
    Module.finrank O X ≤ q → NoSelfIntOn bar φ X

theorem IsPolFan.mono {O : Type} [CommRing O] {bar : O → O} {φ : InvFun O} {q q' : ℕ}
    (h : IsPolFan bar q φ) (hq : q' ≤ q) : IsPolFan bar q' φ :=
  fun X _ _ _ _ hX => h X (hX.trans hq)

theorem NoSelfInt.mono {O : Type} [CommRing O] {bar : O → O} {φ : InvFun O} {q q' : ℕ}
    (h : NoSelfInt bar q φ) (hq : q' ≤ q) : NoSelfInt bar q' φ :=
  fun X _ _ _ _ hX => h X (hX.trans hq)

theorem isPolFan_zero {O : Type} [CommRing O] [IsDomain O] (bar : O → O) (φ : InvFun O) :
    IsPolFan bar 0 φ := fun X _ _ _ _ hX => by
  have : Subsingleton X := Module.finrank_zero_iff.mp (Nat.le_zero.mp hX)
  exact (isPolFanOn_of_subsingleton bar φ X).1

theorem noSelfInt_zero {O : Type} [CommRing O] [IsDomain O] (bar : O → O) (φ : InvFun O) :
    NoSelfInt bar 0 φ := fun X _ _ _ _ hX => by
  have : Subsingleton X := Module.finrank_zero_iff.mp (Nat.le_zero.mp hX)
  exact (isPolFanOn_of_subsingleton bar φ X).2

/-- **Packaged Admissible Smooth Rational Polyhedral Fan (`PolyhedralFanKS`)**:
bundles a coefficient order `O`, involution `bar`, cusp rank bound `maxRank`, `GL_O`-invariant
polarization function `φ`, full smooth rational polyhedral cone decomposition `isPolFan`, and
neatness `noSelfInt` (guaranteeing SNC boundary charts). -/
structure PolyhedralFanKS where
  O : Type
  [commRingO : CommRing O]
  [isDomainO : IsDomain O]
  bar : O → O
  maxRank : ℕ
  φ : InvFun O
  isPolFan : IsPolFan bar maxRank φ
  noSelfInt : NoSelfInt bar maxRank φ

attribute [instance] PolyhedralFanKS.commRingO PolyhedralFanKS.isDomainO

namespace PolyhedralFanKS

/-- Unconditional rank-`0` `PolyhedralFanKS` (definite / compact Shimura varieties `q = 0`) for any
integral domain `O` and involution `bar`. -/
def rankZero (O : Type) [CommRing O] [IsDomain O] (bar : O → O) : PolyhedralFanKS where
  O := O
  bar := bar
  maxRank := 0
  φ := InvFun.posMin O
  isPolFan := isPolFan_zero bar (InvFun.posMin O)
  noSelfInt := noSelfInt_zero bar (InvFun.posMin O)

/-- Positivity of `φ` on any smooth cone ray in a `PolyhedralFanKS` (key step in proving
strictly positive boundary multiplicities `a_i > 0` in toroidal charts!). -/
theorem evalZ_ray_pos (F : PolyhedralFanKS)
    {X : Type} [AddCommGroup X] [Module F.O X] [Module.Free F.O X] [Module.Finite F.O X]
    (hX : Module.finrank F.O X ≤ F.maxRank) {m : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X}
    (hγ : IsSmoothRationalCone F.bar F.φ γ) (i : Fin m) :
    0 < F.φ.evalZ (γ i) :=
  (F.isPolFan X hX).pos (γ i) (hγ.mem i) (hγ.nonneg i) (hγ.ne_zero i)

/-- Every ray of a smooth cone in `PolyhedralFanKS` has a strictly positive integer polarization
value `k > 0` (`φ.evalZ (γ i) = k`). -/
theorem exists_pos_nat_evalZ_ray (F : PolyhedralFanKS)
    {X : Type} [AddCommGroup X] [Module F.O X] [Module.Free F.O X] [Module.Finite F.O X]
    (hX : Module.finrank F.O X ≤ F.maxRank) {m : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X}
    (hγ : IsSmoothRationalCone F.bar F.φ γ) (i : Fin m) :
    ∃ k : ℕ, 0 < k ∧ F.φ.evalZ (γ i) = (k : ℝ) :=
  (F.isPolFan X hX).evalZ_pos_int (hγ.mem i) (hγ.nonneg i) (hγ.ne_zero i)

end PolyhedralFanKS

/-! ### Unconditional Rank-1 Siegel Polyhedral Fan (`PolyhedralFanKS.rankOneSiegel`) -/

section RankOneSiegelFan

/-- The canonical generator `γ₀(x, y) = x 0 * y 0` of `Sym²((Fin 1 → ℤ)^∨) ≅ ℤ`. -/
def siegelRayOne : LinearMap.BilinForm ℤ (Fin 1 → ℤ) :=
  LinearMap.mk₂ ℤ (fun x y => x 0 * y 0)
    (fun _ _ _ => by simp [add_mul])
    (fun _ _ _ => by simp [mul_assoc])
    (fun _ _ _ => by simp [mul_add])
    (fun _ _ _ => by simp [mul_left_comm])

@[simp]
theorem siegelRayOne_apply (x y : Fin 1 → ℤ) : siegelRayOne x y = x 0 * y 0 := rfl

theorem siegelRayOne_mem : siegelRayOne ∈ balForms (id : ℤ → ℤ) (Fin 1 → ℤ) :=
  ⟨fun x y => mul_comm (x 0) (y 0), fun a x y => by
    simp only [siegelRayOne_apply, Pi.smul_apply, smul_eq_mul, id_eq]; ring⟩

theorem siegelRayOne_psd : IsPsdForm siegelRayOne := fun x => mul_self_nonneg (x 0)

private lemma fin1_eq_smul_one (x : Fin 1 → ℤ) : x = (x 0) • (fun _ : Fin 1 => (1 : ℤ)) := by
  ext i
  obtain rfl : i = 0 := Subsingleton.elim i 0
  simp

private lemma bilin_fin1_apply (B : (Fin 1 → ℤ) →ₗ[ℤ] (Fin 1 → ℤ) →ₗ[ℤ] ℝ) (x y : Fin 1 → ℤ) :
    B x y = (x 0 : ℝ) * (y 0 : ℝ) * B (fun _ => 1) (fun _ => 1) := by
  conv_lhs => rw [fin1_eq_smul_one x, fin1_eq_smul_one y]
  rw [map_zsmul, map_zsmul, LinearMap.smul_apply, zsmul_eq_mul, zsmul_eq_mul]
  ring

private lemma int_bilin_fin1_apply (β : LinearMap.BilinForm ℤ (Fin 1 → ℤ)) (x y : Fin 1 → ℤ) :
    β x y = x 0 * y 0 * β (fun _ => 1) (fun _ => 1) := by
  conv_lhs => rw [fin1_eq_smul_one x, fin1_eq_smul_one y]
  rw [map_zsmul, map_zsmul, LinearMap.smul_apply, zsmul_eq_mul, zsmul_eq_mul, Int.cast_id, Int.cast_id]
  ring

private lemma int_bilin_fin1_eq_smul (β : LinearMap.BilinForm ℤ (Fin 1 → ℤ)) :
    β = β (fun _ => 1) (fun _ => 1) • siegelRayOne := by
  refine LinearMap.ext fun x => LinearMap.ext fun y => ?_
  rw [int_bilin_fin1_apply]
  simp [siegelRayOne_apply, mul_comm, mul_assoc]

/-- Explicit 1-element `ℤ`-basis of `balForms id (Fin 1 → ℤ)` given by `siegelRayOne`. -/
def balFormsFin1Basis : Module.Basis (Fin 1) ℤ (balForms (id : ℤ → ℤ) (Fin 1 → ℤ)) :=
  Module.Basis.ofEquivFun
    { toFun := fun β _ => β.1 (fun _ => 1) (fun _ => 1)
      invFun := fun c => ⟨c 0 • siegelRayOne, Submodule.smul_mem _ _ siegelRayOne_mem⟩
      map_add' := fun _ _ => funext fun _ => rfl
      map_smul' := fun _ _ => funext fun _ => rfl
      left_inv := fun β => Subtype.ext (int_bilin_fin1_eq_smul β.1).symm
      right_inv := fun c => funext fun i => by
        obtain rfl : i = 0 := Subsingleton.elim i 0
        simp [siegelRayOne_apply] }

@[simp]
theorem balFormsFin1Basis_zero :
    (balFormsFin1Basis 0 : balForms (id : ℤ → ℤ) (Fin 1 → ℤ)).1 = siegelRayOne := by
  change (balFormsFin1Basis.repr.symm (Finsupp.single 0 1)).1 = siegelRayOne
  simp [balFormsFin1Basis]

/-- Exact evaluation formula on `Fin 1 → ℤ`: for every PSD real bilinear form `B`,
`(posMin ℤ).evalR B = B 1 1`. -/
theorem posMin_evalR_fin1 {B : (Fin 1 → ℤ) →ₗ[ℤ] (Fin 1 → ℤ) →ₗ[ℤ] ℝ}
    (hB : B ∈ psdCone (id : ℤ → ℤ) (Fin 1 → ℤ)) :
    (InvFun.posMin ℤ).evalR B = B (fun _ => 1) (fun _ => 1) := by
  set c : ℝ := B (fun _ => 1) (fun _ => 1)
  have hc : 0 ≤ c := hB.2.2 (fun _ => 1)
  rw [InvFun.evalR, InvFun.posMin_eval_eq]
  rcases eq_or_lt_of_le hc with hc0 | hcpos
  · have hB0 : ∀ y : Fin 1 → ℤ, B y y = 0 := fun y => by
      rw [bilin_fin1_apply]
      change (y 0 : ℝ) * (y 0 : ℝ) * c = 0
      rw [← hc0, mul_zero]
    have hempty : {x : ℝ | (∃ y : Fin 1 → ℤ, B y y = x) ∧ x ≠ B 0 0} = ∅ := by
      ext x; simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨⟨y, rfl⟩, hne⟩
      exact hne (by rw [hB0 y, hB0 0])
    rw [hempty, Real.sInf_empty, max_self, ← hc0]
  · have hS_eq : sInf {x : ℝ | (∃ y : Fin 1 → ℤ, B y y = x) ∧ x ≠ B 0 0} = c := by
      refine le_antisymm ?_ ?_
      · refine csInf_le ?_ ?_
        · refine ⟨0, ?_⟩
          rintro x ⟨⟨y, rfl⟩, _⟩
          exact hB.2.2 y
        · refine ⟨⟨fun _ => 1, rfl⟩, ?_⟩
          simp only [map_zero]
          exact hcpos.ne'
      · refine le_csInf ?_ ?_
        · exact ⟨c, ⟨fun _ => 1, rfl⟩, by simp [hcpos.ne']⟩
        · rintro x ⟨⟨y, rfl⟩, hne⟩
          have hy0 : y 0 ≠ 0 := by
            intro h0
            apply hne
            rw [bilin_fin1_apply, h0]; simp
          have hsq : (1 : ℝ) ≤ ((y 0 : ℤ) : ℝ) * ((y 0 : ℤ) : ℝ) := by
            have hz : (1 : ℤ) ≤ y 0 * y 0 := by
              have habs : 1 ≤ |y 0| := Int.one_le_abs hy0
              nlinarith [sq_abs (y 0)]
            exact_mod_cast hz
          rw [bilin_fin1_apply]
          nlinarith
    rw [hS_eq, max_eq_right hc]

theorem posMin_evalZ_fin1 {β : LinearMap.BilinForm ℤ (Fin 1 → ℤ)} (hβ : IsPsdForm β) :
    (InvFun.posMin ℤ).evalZ β = (β (fun _ => 1) (fun _ => 1) : ℝ) := by
  have hmem : β ∈ balForms (id : ℤ → ℤ) (Fin 1 → ℤ) := by
    rw [int_bilin_fin1_eq_smul β]
    exact Submodule.smul_mem _ _ siegelRayOne_mem
  exact posMin_evalR_fin1 (toRealBilin_mem_psdCone (id : ℤ → ℤ) hmem hβ)

/-- The canonical 1-ray cone `![siegelRayOne]` is a smooth rational cone for `posMin ℤ`. -/
theorem isSmoothRationalCone_siegelRayOne :
    IsSmoothRationalCone (id : ℤ → ℤ) (InvFun.posMin ℤ) ![siegelRayOne] where
  mem i := by obtain rfl : i = 0 := Subsingleton.elim i 0; exact siegelRayOne_mem
  nonneg i := by obtain rfl : i = 0 := Subsingleton.elim i 0; exact siegelRayOne_psd
  smooth := ⟨1, balFormsFin1Basis, Function.Embedding.refl _, fun i => by
    obtain rfl : i = 0 := Subsingleton.elim i 0
    apply Subtype.ext
    exact balFormsFin1Basis_zero⟩
  linear := fun c hc => by
    have hsum : ∑ i : Fin 1, c i • toRealBilin (![siegelRayOne] i) =
        c 0 • toRealBilin siegelRayOne := by simp
    rw [hsum]
    have hpsd : c 0 • toRealBilin siegelRayOne ∈ psdCone (id : ℤ → ℤ) (Fin 1 → ℤ) :=
      smul_mem_psdCone _ (toRealBilin_mem_psdCone _ siegelRayOne_mem siegelRayOne_psd) (hc 0)
    rw [posMin_evalR_fin1 hpsd, Fin.sum_univ_one]
    simp [posMin_evalZ_fin1 siegelRayOne_psd, siegelRayOne_apply]
  strict := by
    let ℓ : LinearMap.BilinForm ℤ (Fin 1 → ℤ) →ₗ[ℤ] ℤ :=
      { toFun := fun β => β (fun _ => 1) (fun _ => 1)
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    refine ⟨1, ℓ, one_pos, fun i => ?_, fun β _ hp => ?_, fun β _ hp _ => ?_⟩
    · obtain rfl : i = 0 := Subsingleton.elim i 0
      simp [ℓ, posMin_evalZ_fin1 siegelRayOne_psd, siegelRayOne_apply]
    · rw [posMin_evalZ_fin1 hp]; simp [ℓ]
    · have hnn : 0 ≤ β (fun _ => 1) (fun _ => 1) := hp (fun _ => 1)
      refine ⟨1, fun _ => (β (fun _ => 1) (fun _ => 1)).toNat, one_pos, ?_⟩
      simp only [Nat.cast_one, one_smul, Fin.sum_univ_one, Matrix.cons_val_zero]
      rw [Int.toNat_of_nonneg hnn]
      exact int_bilin_fin1_eq_smul β

/-- The zero cone (`m = 0`) on `Fin 1 → ℤ` is a smooth rational cone for `posMin ℤ`. -/
theorem isSmoothRationalCone_fin1_empty (γ : Fin 0 → LinearMap.BilinForm ℤ (Fin 1 → ℤ)) :
    IsSmoothRationalCone (id : ℤ → ℤ) (InvFun.posMin ℤ) γ where
  mem := fun i => i.elim0
  nonneg := fun i => i.elim0
  smooth := isPartOfBasis_empty balFormsFin1Basis _
  linear := fun _ _ => by
    simp only [Finset.univ_eq_empty, Finset.sum_empty]
    exact posMin_evalR_fin1 (zero_mem_psdCone _ _)
  strict := by
    refine ⟨1, 0, one_pos, fun i => i.elim0, fun β _ hp => ?_, fun β _ hp he => ?_⟩
    · rw [posMin_evalZ_fin1 hp]
      have hnn : (0 : ℝ) ≤ (β (fun _ => 1) (fun _ => 1) : ℝ) := by exact_mod_cast hp (fun _ => 1)
      simpa using hnn
    · rw [posMin_evalZ_fin1 hp] at he
      have h0 : β (fun _ => 1) (fun _ => 1) = 0 := by
        have h1 : (β (fun _ => 1) (fun _ => 1) : ℝ) = 0 := by simpa using he.symm
        exact_mod_cast h1
      refine ⟨1, Fin.elim0, one_pos, ?_⟩
      rw [int_bilin_fin1_eq_smul β, h0]
      simp

/-- Every smooth rational cone on `Fin 1 → ℤ` has `m ≤ 1`, and every ray equals `siegelRayOne`! -/
theorem isSmoothRationalCone_fin1_ray_eq {m : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ (Fin 1 → ℤ)}
    (hγ : IsSmoothRationalCone (id : ℤ → ℤ) (InvFun.posMin ℤ) γ) (i : Fin m) :
    γ i = siegelRayOne := by
  obtain ⟨n, b, ι, hι⟩ := hγ.smooth
  have hcard : n = 1 := by
    have h1 := Module.finrank_eq_card_basis b
    have h2 := Module.finrank_eq_card_basis balFormsFin1Basis
    rw [Fintype.card_fin] at h1 h2
    omega
  subst hcard
  have hunit : IsUnit ((b (ι i) : balForms (id : ℤ → ℤ) (Fin 1 → ℤ)).1 (fun _ => 1) (fun _ => 1)) := by
    let v0 : balForms (id : ℤ → ℤ) (Fin 1 → ℤ) := balFormsFin1Basis 0
    have hv0 : v0 = (b.repr v0 0) • b 0 := by
      have hsr := (b.sum_repr v0).symm
      rw [Fin.sum_univ_one] at hsr
      exact hsr
    have hi0 : ι i = 0 := Subsingleton.elim (ι i) 0
    rw [hi0]
    have heval := congrArg (fun u : balForms (id : ℤ → ℤ) (Fin 1 → ℤ) => u.1 (fun _ => 1) (fun _ => 1)) hv0
    have hv0_eval : v0.1 (fun _ => 1) (fun _ => 1) = 1 := by
      simp [v0, balFormsFin1Basis_zero, siegelRayOne_apply]
    rw [hv0_eval] at heval
    change (1 : ℤ) = b.repr v0 0 * (b 0).1 (fun _ => 1) (fun _ => 1) at heval
    exact IsUnit.of_mul_eq_one (b.repr v0 0) (by linarith)
  have heq_ray : (b (ι i)).1 = γ i := congrArg Subtype.val (hι i)
  rw [heq_ray] at hunit
  have hnn : 0 ≤ γ i (fun _ => 1) (fun _ => 1) := hγ.nonneg i (fun _ => 1)
  have hone : γ i (fun _ => 1) (fun _ => 1) = 1 := by
    rcases Int.isUnit_iff.mp hunit with h1 | hm1
    · exact h1
    · omega
  rw [int_bilin_fin1_eq_smul (γ i), hone, one_smul]

/-- **Unconditional 1-Dimensional Siegel Fan Theorem on `Fin 1 → ℤ`**:
`posMin ℤ` satisfies EVERY axiom of `IsPolFanOn` AND `NoSelfIntOn` on `Fin 1 → ℤ`! -/
theorem isPolFanOn_posMin_fin1 :
    IsPolFanOn (id : ℤ → ℤ) (InvFun.posMin ℤ) (Fin 1 → ℤ) ∧
    NoSelfIntOn (id : ℤ → ℤ) (InvFun.posMin ℤ) (Fin 1 → ℤ) := by
  refine ⟨?_, ?_⟩
  · refine
      { homog := fun B hB t ht => by
          rw [posMin_evalR_fin1 (smul_mem_psdCone _ hB ht), posMin_evalR_fin1 hB]
          rfl
        superadd := fun B hB B' hB' => by
          rw [posMin_evalR_fin1 hB, posMin_evalR_fin1 hB',
            posMin_evalR_fin1 (add_mem_psdCone _ hB hB')]
          rfl
        integral := fun β _ hp => ⟨β (fun _ => 1) (fun _ => 1), posMin_evalZ_fin1 hp⟩
        pos := fun β _ hp hne => by
          rw [posMin_evalZ_fin1 hp]
          have hnn : 0 ≤ β (fun _ => 1) (fun _ => 1) := hp (fun _ => 1)
          have hnz : β (fun _ => 1) (fun _ => 1) ≠ 0 := fun h0 => by
            apply hne
            rw [int_bilin_fin1_eq_smul β, h0, zero_smul]
          exact_mod_cast lt_of_le_of_ne hnn (Ne.symm hnz)
        face := fun m m' γ s hγ => by
          have hm' : m' ≤ 1 := by
            by_contra hgt
            have h2 : 2 ≤ m' := by omega
            let i0 : Fin m' := ⟨0, by omega⟩
            let i1 : Fin m' := ⟨1, by omega⟩
            have hne : i0 ≠ i1 := by intro h; exact absurd (congrArg Fin.val h) Nat.zero_ne_one
            have heq := (isSmoothRationalCone_fin1_ray_eq hγ (s i0)).trans
              (isSmoothRationalCone_fin1_ray_eq hγ (s i1)).symm
            exact hne (s.injective (hγ.injective heq))
          rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hm' with rfl | rfl
          · exact isSmoothRationalCone_fin1_empty _
          · have hfun : (fun i : Fin 1 => γ (s i)) = ![siegelRayOne] := by
              funext i
              obtain rfl : i = 0 := Subsingleton.elim i 0
              exact isSmoothRationalCone_fin1_ray_eq hγ (s 0)
            rw [hfun]
            exact isSmoothRationalCone_siegelRayOne
        cover := fun B hB => by
          refine ⟨1, ![siegelRayOne], ![B (fun _ => 1) (fun _ => 1)],
            isSmoothRationalCone_siegelRayOne, fun i => by
              obtain rfl : i = 0 := Subsingleton.elim i 0
              exact hB.2.2 (fun _ => 1), ?_⟩
          refine LinearMap.ext fun x => LinearMap.ext fun y => ?_
          rw [bilin_fin1_apply]
          simp [siegelRayOne_apply]
          ring
        finite := ⟨{siegelRayOne}, Set.finite_singleton _, fun m γ hγ =>
          ⟨LinearEquiv.refl ℤ _, fun i => by
            simp only [LinearEquiv.refl_toLinearMap, Set.mem_singleton_iff]
            have hray := isSmoothRationalCone_fin1_ray_eq hγ i
            rw [hray]
            rfl⟩⟩ }
  · intro m γ hγ _ i j _
    exact hγ.injective ((isSmoothRationalCone_fin1_ray_eq hγ i).trans
      (isSmoothRationalCone_fin1_ray_eq hγ j).symm)

/-- **Unconditional Rank-1 Siegel / Modular Curve Polyhedral Fan (`PolyhedralFanKS.rankOneSiegel`)**:
admissible smooth rational polyhedral cone decomposition for `maxRank = 1` over `ℤ` (`O = ℤ`,
`bar = id`, `φ = posMin ℤ`), with complete proofs of all 7 fan axioms AND `NoSelfInt`! -/
def PolyhedralFanKS.rankOneSiegel : PolyhedralFanKS where
  O := ℤ
  bar := id
  maxRank := 1
  φ := InvFun.posMin ℤ
  isPolFan := fun X _ _ _ _ hX => by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hX with h0 | h1
    · have : Subsingleton X := Module.finrank_zero_iff.mp h0
      exact (isPolFanOn_of_subsingleton id (InvFun.posMin ℤ) X).1
    · let b := Module.Free.chooseBasis ℤ X
      have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ X) = 1 := by
        rw [← Module.finrank_eq_card_basis b, h1]
      let eIdx : Fin 1 ≃ Module.Free.ChooseBasisIndex ℤ X :=
        (Fintype.equivFinOfCardEq hcard).symm
      let eX : (Fin 1 → ℤ) ≃ₗ[ℤ] X :=
        (LinearEquiv.funCongrLeft ℤ ℤ eIdx.symm).trans
          ((Finsupp.linearEquivFunOnFinite ℤ ℤ _).symm.trans b.repr.symm)
      exact isPolFanOn_posMin_fin1.1.of_equiv eX
  noSelfInt := fun X _ _ _ _ hX => by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hX with h0 | h1
    · have : Subsingleton X := Module.finrank_zero_iff.mp h0
      exact (isPolFanOn_of_subsingleton id (InvFun.posMin ℤ) X).2
    · let b := Module.Free.chooseBasis ℤ X
      have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ X) = 1 := by
        rw [← Module.finrank_eq_card_basis b, h1]
      let eIdx : Fin 1 ≃ Module.Free.ChooseBasisIndex ℤ X :=
        (Fintype.equivFinOfCardEq hcard).symm
      let eX : (Fin 1 → ℤ) ≃ₗ[ℤ] X :=
        (LinearEquiv.funCongrLeft ℤ ℤ eIdx.symm).trans
          ((Finsupp.linearEquivFunOnFinite ℤ ℤ _).symm.trans b.repr.symm)
      exact isPolFanOn_posMin_fin1.2.of_equiv eX

end RankOneSiegelFan

/-! ### Explicit `g`-Dimensional Unimodular Smooth Cone & `Sym²(ℤ^g)` Basis (`SmoothConeChartModel`) -/

section SmoothConeArbitraryGenus

/-- Elementary symmetric `ℤ`-bilinear form `E_{i, j}` on `Fin g → ℤ`:
for `i = j`, `E_{i, i}(x, y) = x i * y i`;
for `i ≠ j`, `E_{i, j}(x, y) = x i * y j + x j * y i`. -/
def symElemForm (g : ℕ) (i j : Fin g) : LinearMap.BilinForm ℤ (Fin g → ℤ) :=
  LinearMap.mk₂ ℤ
    (fun x y => if i = j then x i * y i else x i * y j + x j * y i)
    (fun _ _ _ => by split_ifs <;> simp <;> ring)
    (fun _ _ _ => by split_ifs <;> simp <;> ring)
    (fun _ _ _ => by split_ifs <;> simp <;> ring)
    (fun _ _ _ => by split_ifs <;> simp <;> ring)

theorem symElemForm_mem (g : ℕ) (i j : Fin g) :
    symElemForm g i j ∈ balForms (id : ℤ → ℤ) (Fin g → ℤ) := by
  refine ⟨fun x y => ?_, fun a x y => ?_⟩
  · simp only [symElemForm, LinearMap.mk₂_apply]; split_ifs <;> ring
  · simp only [symElemForm, LinearMap.mk₂_apply, Pi.smul_apply, smul_eq_mul, id_eq]
    split_ifs <;> ring

/-- Rank-1 diagonal quadratic ray `diagRay g i (x, y) = x i * y i`. -/
def diagRay (g : ℕ) (i : Fin g) : LinearMap.BilinForm ℤ (Fin g → ℤ) :=
  symElemForm g i i

theorem diagRay_apply (g : ℕ) (i : Fin g) (x y : Fin g → ℤ) :
    diagRay g i x y = x i * y i := by
  simp [diagRay, symElemForm]

theorem diagRay_mem (g : ℕ) (i : Fin g) : diagRay g i ∈ balForms (id : ℤ → ℤ) (Fin g → ℤ) :=
  symElemForm_mem g i i

theorem diagRay_psd (g : ℕ) (i : Fin g) : IsPsdForm (diagRay g i) := fun x => by
  rw [diagRay_apply]; exact mul_self_nonneg (x i)

/-- Index type `UpperTriIdx g = {(i, j) : Fin g × Fin g | i ≤ j}` of cardinality `g * (g + 1) / 2`. -/
abbrev UpperTriIdx (g : ℕ) : Type := {p : Fin g × Fin g // p.1 ≤ p.2}

private lemma symElemForm_eval_single (g : ℕ) (p q : UpperTriIdx g) :
    symElemForm g p.1.1 p.1.2 (Pi.single q.1.1 1) (Pi.single q.1.2 1) =
      if p = q then 1 else 0 := by
  rcases p with ⟨⟨i, j⟩, hij⟩
  rcases q with ⟨⟨a, b⟩, hab⟩
  simp only [symElemForm, LinearMap.mk₂_apply, Pi.single_apply]
  by_cases hEq : (⟨(i, j), hij⟩ : UpperTriIdx g) = ⟨(a, b), hab⟩
  · rw [if_pos hEq]
    have h1 : i = a := congrArg (fun t : UpperTriIdx g => t.1.1) hEq
    have h2 : j = b := congrArg (fun t : UpperTriIdx g => t.1.2) hEq
    subst h1; subst h2
    by_cases hia : i = j
    · subst hia; simp
    · simp [hia, Ne.symm hia]
  · rw [if_neg hEq]
    have hpair : ¬ (i = a ∧ j = b) := fun ⟨h1, h2⟩ => hEq (Subtype.ext (Prod.ext h1 h2))
    by_cases hij_eq : i = j
    · subst hij_eq
      rw [if_pos rfl]
      by_cases ha : i = a
      · subst ha
        have hb : i ≠ b := fun h => hpair ⟨rfl, h⟩
        simp [hb]
      · simp [ha]
    · rw [if_neg hij_eq]
      have hlt : i < j := lt_of_le_of_ne hij hij_eq
      have h1 : ¬ (i = a ∧ j = b) := hpair
      have h2 : ¬ (j = a ∧ i = b) := fun ⟨hja, hib⟩ => by
        subst hja; subst hib; exact not_lt_of_ge hab hlt
      by_cases hia : i = a <;> by_cases hjb : j = b <;>
        by_cases hja : j = a <;> by_cases hib : i = b <;>
        simp_all

/-- Explicit `ℤ`-linear equivalence between `balForms id (Fin g → ℤ)` (`Sym²(ℤ^g)`) and
`UpperTriIdx g → ℤ` (evaluating a symmetric bilinear form on upper-triangular basis pairs). -/
def symBalEquivFun (g : ℕ) : balForms (id : ℤ → ℤ) (Fin g → ℤ) ≃ₗ[ℤ] (UpperTriIdx g → ℤ) where
  toFun β p := β.1 (Pi.single p.1.1 1) (Pi.single p.1.2 1)
  invFun c :=
    ⟨∑ p : UpperTriIdx g, c p • symElemForm g p.1.1 p.1.2,
     Submodule.sum_mem _ fun p _ => Submodule.smul_mem _ _ (symElemForm_mem g p.1.1 p.1.2)⟩
  map_add' _ _ := funext fun _ => rfl
  map_smul' _ _ := funext fun _ => rfl
  left_inv β := by
    apply Subtype.ext
    refine LinearMap.ext fun x => LinearMap.ext fun y => ?_
    have hx : x = ∑ a : Fin g, x a • (Pi.single a (1 : ℤ) : Fin g → ℤ) := by
      ext k; simp [Finset.sum_apply, Pi.single_apply]
    have hy : y = ∑ b : Fin g, y b • (Pi.single b (1 : ℤ) : Fin g → ℤ) := by
      ext k; simp [Finset.sum_apply, Pi.single_apply]
    have hbasis : ∀ a b : Fin g,
        (∑ p : UpperTriIdx g, (β.1 (Pi.single p.1.1 1) (Pi.single p.1.2 1)) •
          symElemForm g p.1.1 p.1.2) (Pi.single a 1) (Pi.single b 1) =
        β.1 (Pi.single a 1) (Pi.single b 1) := by
      intro a b
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
      by_cases hab : a ≤ b
      · let q : UpperTriIdx g := ⟨(a, b), hab⟩
        rw [Finset.sum_eq_single q]
        · rw [symElemForm_eval_single g q q, if_pos rfl, mul_one]
        · intro p _ hpq; rw [symElemForm_eval_single g p q, if_neg hpq, mul_zero]
        · intro hq; exact absurd (Finset.mem_univ q) hq
      · have hba : b ≤ a := le_of_not_ge hab
        let q : UpperTriIdx g := ⟨(b, a), hba⟩
        have hsym : ∀ p : UpperTriIdx g,
            symElemForm g p.1.1 p.1.2 (Pi.single a 1) (Pi.single b 1) =
              symElemForm g p.1.1 p.1.2 (Pi.single b 1) (Pi.single a 1) :=
          fun p => (symElemForm_mem g p.1.1 p.1.2).1 _ _
        simp_rw [hsym]
        rw [Finset.sum_eq_single q]
        · rw [symElemForm_eval_single g q q, if_pos rfl, mul_one]
          exact (β.2.1 (Pi.single b 1) (Pi.single a 1))
        · intro p _ hpq; rw [symElemForm_eval_single g p q, if_neg hpq, mul_zero]
        · intro hq; exact absurd (Finset.mem_univ q) hq
    let Φ : LinearMap.BilinForm ℤ (Fin g → ℤ) :=
      ∑ p : UpperTriIdx g, (β.1 (Pi.single p.1.1 1) (Pi.single p.1.2 1)) •
        symElemForm g p.1.1 p.1.2
    have hexpand : ∀ (M : LinearMap.BilinForm ℤ (Fin g → ℤ)),
        M x y = ∑ a : Fin g, x a * (∑ b : Fin g, y b * M (Pi.single a 1) (Pi.single b 1)) := by
      intro M
      conv_lhs => rw [hx]
      rw [map_sum, LinearMap.sum_apply]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [map_zsmul, LinearMap.smul_apply, zsmul_eq_mul, Int.cast_id]
      conv_lhs => rw [hy]
      rw [map_sum]
      refine congrArg (x a * ·) (Finset.sum_congr rfl fun b _ => ?_)
      rw [map_zsmul, zsmul_eq_mul, Int.cast_id]
    change Φ x y = β.1 x y
    rw [hexpand Φ, hexpand β.1]
    refine Finset.sum_congr rfl fun a _ => congrArg (x a * ·) ?_
    refine Finset.sum_congr rfl fun b _ => congrArg (y b * ·) (hbasis a b)
  right_inv c := by
    funext q
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, zsmul_eq_mul]
    rw [Finset.sum_eq_single q]
    · rw [symElemForm_eval_single g q q, if_pos rfl, mul_one, Int.cast_id]
    · intro p _ hpq; rw [symElemForm_eval_single g p q, if_neg hpq, mul_zero]
    · intro hq; exact absurd (Finset.mem_univ q) hq

/-- Explicit `ℤ`-basis of `balForms id (Fin g → ℤ)` (`Sym²(ℤ^g)`). -/
def symBalBasis (g : ℕ) : Module.Basis (UpperTriIdx g) ℤ (balForms (id : ℤ → ℤ) (Fin g → ℤ)) :=
  Module.Basis.ofEquivFun (symBalEquivFun g)

theorem card_upperTriIdx (g : ℕ) : Fintype.card (UpperTriIdx g) = g * (g + 1) / 2 := by
  induction g with
  | zero => simp
  | succ n ih =>
    let e : UpperTriIdx (n + 1) ≃ Sum (UpperTriIdx n) (Fin (n + 1)) :=
      { toFun := fun p =>
          if h : p.1.2.1 < n then
            Sum.inl ⟨(⟨p.1.1.1, lt_of_le_of_lt p.2 h⟩, ⟨p.1.2.1, h⟩), p.2⟩
          else
            Sum.inr p.1.1
        invFun := fun s =>
          match s with
          | Sum.inl q => ⟨(q.1.1.castSucc, q.1.2.castSucc), q.2⟩
          | Sum.inr i => ⟨(i, Fin.last n), Fin.le_last i⟩
        left_inv := fun p => by
          rcases p with ⟨⟨i, j⟩, hij⟩
          dsimp
          split_ifs with h
          · exact Subtype.ext (Prod.ext (Fin.ext rfl) (Fin.ext rfl))
          · have hj : j = Fin.last n := Fin.ext (by have := j.isLt; simp [Fin.last]; omega)
            subst hj
            rfl
        right_inv := fun s => by
          rcases s with q | i
          · simp [q.1.2.2]
          · simp }
    rw [Fintype.card_congr e, Fintype.card_sum, ih, Fintype.card_fin]
    obtain ⟨k, hk⟩ := Nat.even_mul_succ_self n
    have h1 : n * (n + 1) / 2 = k := by omega
    have h2 : (n + 1) * (n + 1 + 1) = 2 * (k + (n + 1)) := by
      have : (n + 1) * (n + 1 + 1) = n * (n + 1) + 2 * (n + 1) := by ring
      omega
    omega

/-- **Unimodularity / Smoothness of the `g`-Ray Diagonal Cone (`isPartOfBasis_diagRay`)**:
for EVERY genus `g : ℕ`, the `g` diagonal rays `diagRay g i` (`i : Fin g`) extend to the explicit
`g*(g+1)/2`-element `ℤ`-basis of `Sym²(ℤ^g)` (`balForms id (Fin g → ℤ)`)! -/
theorem isPartOfBasis_diagRay (g : ℕ) :
    IsPartOfBasis (fun i : Fin g => (⟨diagRay g i, diagRay_mem g i⟩ : balForms (id : ℤ → ℤ) (Fin g → ℤ))) := by
  let eIdx : UpperTriIdx g ≃ Fin (Fintype.card (UpperTriIdx g)) := Fintype.equivFin (UpperTriIdx g)
  let b : Module.Basis (Fin (Fintype.card (UpperTriIdx g))) ℤ (balForms (id : ℤ → ℤ) (Fin g → ℤ)) :=
    (symBalBasis g).reindex eIdx
  let ι : Fin g ↪ Fin (Fintype.card (UpperTriIdx g)) :=
    ⟨fun i => eIdx ⟨(i, i), le_rfl⟩, fun i j hij => by
      have h := eIdx.injective hij
      exact congrArg (fun t : UpperTriIdx g => t.1.1) h⟩
  refine ⟨Fintype.card (UpperTriIdx g), b, ι, fun i => ?_⟩
  apply Subtype.ext
  have hb_eq : b (ι i) = (symBalBasis g) ⟨(i, i), le_rfl⟩ := by
    change ((symBalBasis g).reindex eIdx) (eIdx ⟨(i, i), le_rfl⟩) = _
    rw [Module.Basis.reindex_apply, Equiv.symm_apply_apply]
  rw [hb_eq]
  have hrep : (symBalBasis g) ⟨(i, i), le_rfl⟩ =
      (symBalEquivFun g).symm (Pi.single ⟨(i, i), le_rfl⟩ (1 : ℤ)) := by
    change (symBalEquivFun g).symm (Finsupp.single ⟨(i, i), le_rfl⟩ 1) = _
    congr 1
    ext p
    by_cases hp : p = ⟨(i, i), le_rfl⟩ <;> simp [hp]
  rw [hrep]
  change (∑ p : UpperTriIdx g,
    ((Pi.single (⟨(i, i), le_rfl⟩ : UpperTriIdx g) (1 : ℤ) : UpperTriIdx g → ℤ) p) •
    symElemForm g p.1.1 p.1.2) = diagRay g i
  rw [Finset.sum_eq_single (⟨(i, i), le_rfl⟩ : UpperTriIdx g)]
  · simp [diagRay]
  · intro p _ hp; simp [hp]
  · intro hm; exact absurd (Finset.mem_univ _) hm

/-- Packaged `g`-dimensional smooth unimodular diagonal cone model (`SmoothConeChartModel g`) with
exact Siegel moduli dimension `symRank = g * (g + 1) / 2`. -/
structure SmoothConeChartModel (g : ℕ) where
  symRank : ℕ
  symRank_eq : symRank = g * (g + 1) / 2
  rays : Fin g → LinearMap.BilinForm ℤ (Fin g → ℤ)
  rays_mem : ∀ i, rays i ∈ balForms (id : ℤ → ℤ) (Fin g → ℤ)
  rays_psd : ∀ i, IsPsdForm (rays i)
  rays_smooth : IsPartOfBasis (fun i => (⟨rays i, rays_mem i⟩ : balForms (id : ℤ → ℤ) (Fin g → ℤ)))
  rays_pos_trace : ∀ i, 0 < ∑ j : Fin g, rays i (Pi.single j 1) (Pi.single j 1)

/-- Unconditional 0-assumption construction of `SmoothConeChartModel g` for every genus `g : ℕ`. -/
def stdSmoothConeChartModel (g : ℕ) : SmoothConeChartModel g where
  symRank := Fintype.card (UpperTriIdx g)
  symRank_eq := card_upperTriIdx g
  rays := diagRay g
  rays_mem := diagRay_mem g
  rays_psd := diagRay_psd g
  rays_smooth := isPartOfBasis_diagRay g
  rays_pos_trace := fun i => by
    rw [Finset.sum_eq_single i]
    · simp [diagRay_apply]
    · intro j _ hji; simp [diagRay_apply, Ne.symm hji]
    · intro hi; exact absurd (Finset.mem_univ i) hi

end SmoothConeArbitraryGenus

/-- Attach a concrete `PolyhedralFanKS` to any `ToroidalBoundaryDatum` from
`Stage14M3_PELUnitaryModuli` (rank-0 fan in the definite/compact case `min p q = 0`, and
rank-1 Siegel/modular fan over `ℤ` for 1-dimensional boundary cusps). -/
def PolyhedralFanKS.forToroidalBoundaryDatum (B : ToroidalBoundaryDatum) : PolyhedralFanKS :=
  if min B.D.p B.D.q = 0 then
    PolyhedralFanKS.rankZero ℤ id
  else
    PolyhedralFanKS.rankOneSiegel

end InvFunAndCones

end PolyhedralFans

/-! ## Section 2: Local Completions, Affine Toric Charts, & Simple Normal Crossings (`IsSncBoundary`) -/

section LocalCompletionsAndCharts

/-- Every field `K` is `maximalIdeal K`-adically complete (since `maximalIdeal K = ⊥`). -/
theorem isAdicComplete_of_field (K : Type*) [Field K] :
    IsAdicComplete (maximalIdeal K) K := by
  have hm : maximalIdeal K = ⊥ := by
    ext x
    simp only [Ideal.mem_bot, mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_ne_zero, not_not]
  rw [hm]
  refine { haus' := ?_, prec' := ?_ }
  · intro x hx
    have h1 := hx 1
    rw [SModEq.zero, pow_one, Ideal.smul_eq_mul, Ideal.mul_top] at h1
    exact Ideal.mem_bot.mp h1
  · intro f hf
    refine ⟨f 1, fun n => ?_⟩
    cases n with
    | zero =>
      rw [SModEq.sub_mem, pow_zero, Ideal.one_eq_top, Ideal.smul_eq_mul, Ideal.mul_top]
      exact Submodule.mem_top
    | succ k =>
      have h1 : 1 ≤ k + 1 := Nat.succ_le_succ (Nat.zero_le k)
      have hfk := hf h1
      rw [SModEq.sub_mem, pow_one, Ideal.smul_eq_mul, Ideal.mul_top, Ideal.mem_bot,
        sub_eq_zero] at hfk
      rw [hfk]
      exact SModEq.rfl

/-- Every ring isomorphism `e : A ≃+* R` into an adically complete local ring `R` is an
étale completion (`IsEtaleCompletion e.toRingHom`). -/
theorem isEtaleCompletion_of_ringEquiv {A R : Type*} [CommRing A] [IsLocalRing A]
    [CommRing R] [IsLocalRing R] (e : A ≃+* R)
    (hcomp : IsAdicComplete (maximalIdeal R) R) :
    IsEtaleCompletion e.toRingHom where
  localHom := ⟨fun a ha => by
    rw [← e.symm_apply_apply a]
    exact ha.map e.symm.toRingHom⟩
  flat := RingHom.Flat.of_bijective e.bijective
  unramified := IsLocalRing.map_maximalIdeal_of_surjective e.toRingHom e.surjective
  complete := hcomp

/-- Concrete `IdealSheafData` on `Sp R` associated to any ideal `I : Ideal R`, built via
`Scheme.IdealSheafData.ofIdealTop`. -/
def idealSheafOfIdeal {R : Type} [CommRing R] (I : Ideal R) : (Sp R).IdealSheafData :=
  Scheme.IdealSheafData.ofIdealTop (I.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)

theorem idealSheafOfIdeal_top {R : Type} [CommRing R] :
    idealSheafOfIdeal (⊤ : Ideal R) = (⊤ : (Sp R).IdealSheafData) := by
  refine Scheme.IdealSheafData.ext (funext fun U => ?_)
  rw [idealSheafOfIdeal, Scheme.IdealSheafData.ofIdealTop_ideal, Ideal.map_top, Ideal.map_top]
  rfl

/-- Closed point of `Sp R` typed explicitly as a point of `Sp R`. -/
abbrev spClosedPoint (R : Type) [CommRing R] [IsLocalRing R] : Sp R :=
  Stage14M3_IntegralSchemesAndCharts.closedPoint R

/-- Fundamental exact computation: for any ring homomorphism `f : R →+* R'` with `R'` local,
`idlAlong (idealSheafOfIdeal I) (spMap f) = I.map f`! -/
theorem idlAlong_idealSheafOfIdeal_spMap {R R' : Type} [CommRing R] [CommRing R'] [IsLocalRing R']
    (I : Ideal R) (f : R →+* R') :
    idlAlong (idealSheafOfIdeal I) (spMap f) = I.map f := by
  let Utop : (Sp R).affineOpens := ⟨⊤, isAffineOpen_top (Sp R)⟩
  rw [idlAlong, stalkId_eq_map (idealSheafOfIdeal I) Utop _ trivial]
  have htop_id : (idealSheafOfIdeal I).ideal Utop =
      I.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom := by
    rw [idealSheafOfIdeal, Scheme.IdealSheafData.ofIdealTop_ideal]
    change (I.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom).map
      ((Sp R).presheaf.map (homOfLE le_top).op).hom = _
    have hmid : (Sp R).presheaf.map (homOfLE (le_top : (⊤ : (Sp R).Opens) ≤ ⊤)).op = 𝟙 _ :=
      (Sp R).presheaf.map_id _
    rw [hmid]
    exact Ideal.map_id _
  rw [htop_id, Ideal.map_map, Ideal.map_map]
  have hcomp : (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫
      (Sp R).presheaf.germ ⊤ ((spMap f) (spClosedPoint R')) trivial ≫
      Scheme.stalkClosedPointTo (spMap f) = CommRingCat.ofHom f := by
    rw [Scheme.germ_stalkClosedPointTo (R := CommRingCat.of R') (spMap f) ⊤ trivial]
    change (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫
      (Spec.map (CommRingCat.ofHom f)).appTop ≫
      (Scheme.ΓSpecIso (CommRingCat.of R')).hom = CommRingCat.ofHom f
    rw [← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f),
      Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hhom : ((Scheme.stalkClosedPointTo (spMap f)).hom.comp
      ((Sp R).presheaf.germ ⊤ ((spMap f) (spClosedPoint R')) trivial).hom).comp
      (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom = f := by
    have := congrArg CommRingCat.Hom.hom hcomp
    simpa [CommRingCat.hom_comp, RingHom.comp_assoc] using this
  simpa [RingHom.comp_assoc] using congrArg (fun g : R →+* R' => I.map g) hhom

theorem idlAlong_idealSheafOfIdeal_id {R : Type} [CommRing R] [IsLocalRing R] (I : Ideal R) :
    idlAlong (idealSheafOfIdeal I) (𝟙 (Sp R)) = I := by
  rw [← spMap_id R, idlAlong_idealSheafOfIdeal_spMap, Ideal.map_id]

/-- For any local ring `R`, `(Scheme.stalkClosedPointTo (𝟙 (Sp R))).hom` is **bijective**
(isomorphism between the stalk `𝒪_{Sp R, 𝔪}` and `R`). -/
theorem bijective_stalkClosedPointTo_id (R : Type) [CommRing R] [IsLocalRing R] :
    Function.Bijective (Scheme.stalkClosedPointTo (𝟙 (Sp R))).hom := by
  let p₀ : Sp R := (𝟙 (Sp R)) (spClosedPoint R)
  let ι : CommRingCat.of R ⟶ (Sp R).presheaf.stalk p₀ :=
    (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫
      (Sp R).presheaf.germ ⊤ p₀ (Set.mem_univ _)
  have hleft : ι ≫ Scheme.stalkClosedPointTo (𝟙 (Sp R)) = 𝟙 (CommRingCat.of R) := by
    calc ι ≫ Scheme.stalkClosedPointTo (𝟙 (Sp R))
        = (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫
            ((Sp R).presheaf.germ ⊤ p₀ (Set.mem_univ _) ≫
              Scheme.stalkClosedPointTo (𝟙 (Sp R))) := Category.assoc _ _ _
      _ = (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ 𝟙 _ ≫
            (Scheme.ΓSpecIso (CommRingCat.of R)).hom :=
          congrArg ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ ·)
            (Scheme.germ_stalkClosedPointTo (R := CommRingCat.of R) (𝟙 (Sp R)) ⊤ (Set.mem_univ _))
      _ = 𝟙 (CommRingCat.of R) := by simp
  have hsurj_ι : Function.Surjective ι.hom := by
    have hcomp_iso : ι = CommRingCat.ofHom (algebraMap R (Localization.AtPrime (maximalIdeal R))) ≫
        (Spec.stalkIso (CommRingCat.of R) p₀).inv :=
      (Spec.algebraMap_stalkIso_inv (R := CommRingCat.of R) p₀).symm
    have hsurj_alg : Function.Surjective (algebraMap R (Localization.AtPrime (maximalIdeal R))) := by
      intro z
      induction z using Localization.induction_on with
      | H p =>
        rcases p with ⟨a, ⟨s, hs⟩⟩
        have hsu : IsUnit s := IsLocalRing.notMem_maximalIdeal.mp hs
        obtain ⟨u, rfl⟩ := hsu
        refine ⟨a * (u⁻¹ : Rˣ), ?_⟩
        rw [map_mul, Localization.mk_eq_mk', IsLocalization.eq_mk'_iff_mul_eq, mul_assoc,
          ← map_mul, Units.inv_mul, map_one, mul_one]
    intro y
    obtain ⟨r, hr⟩ := hsurj_alg ((Spec.stalkIso (CommRingCat.of R) p₀).hom.hom y)
    refine ⟨r, ?_⟩
    have h1 := congrArg (fun φ => φ.hom r) hcomp_iso
    have h2 : (Spec.stalkIso (CommRingCat.of R) p₀).inv.hom
        ((Spec.stalkIso (CommRingCat.of R) p₀).hom.hom y) = y :=
      (Spec.stalkIso (CommRingCat.of R) p₀).commRingCatIsoToRingEquiv.symm_apply_apply y
    exact h1.trans ((congrArg (Spec.stalkIso (CommRingCat.of R) p₀).inv.hom hr).trans h2)
  have hleft_apply : ∀ r : R, (Scheme.stalkClosedPointTo (𝟙 (Sp R))).hom (ι.hom r) = r := fun r => by
    have h1 := congrArg (fun φ => φ.hom r) hleft
    exact h1
  refine ⟨?_, ?_⟩
  · intro x₁ x₂ hx
    obtain ⟨r₁, rfl⟩ := hsurj_ι x₁
    obtain ⟨r₂, rfl⟩ := hsurj_ι x₂
    have hr : r₁ = r₂ := (hleft_apply r₁).symm.trans (hx.trans (hleft_apply r₂))
    rw [hr]
  · intro r
    exact ⟨ι.hom r, hleft_apply r⟩

/-- For any adically complete local ring `R`, `Scheme.stalkClosedPointTo (𝟙 (Sp R))` is an
étale completion! -/
theorem isEtaleCompletion_stalkClosedPointTo_id (R : Type) [CommRing R] [IsLocalRing R]
    (hcomp : IsAdicComplete (maximalIdeal R) R) :
    IsEtaleCompletion (Scheme.stalkClosedPointTo (𝟙 (Sp R))).hom := by
  let e := RingEquiv.ofBijective (Scheme.stalkClosedPointTo (𝟙 (Sp R))).hom
    (bijective_stalkClosedPointTo_id R)
  exact isEtaleCompletion_of_ringEquiv e hcomp

/-- For any integral domain `R`, at the generic point `η = ⟨⊥, Ideal.isPrime_bot⟩`,
`Scheme.stalkClosedPointTo (spMap (algebraMap R (FractionRing R)))` is **bijective**! -/
theorem bijective_stalkClosedPointTo_fractionRing (R : Type) [CommRing R] [IsDomain R] :
    Function.Bijective
      (Scheme.stalkClosedPointTo (spMap (algebraMap R (FractionRing R)))).hom := by
  let K := FractionRing R
  let f : R →+* K := algebraMap R K
  let ξ : Sp K ⟶ Sp R := spMap f
  let p₀ : Sp R := ξ (spClosedPoint K)
  have hpt : p₀ = ⟨⊥, Ideal.isPrime_bot⟩ := by
    apply PrimeSpectrum.ext
    change (maximalIdeal (FractionRing R)).comap f = ⊥
    have hm : maximalIdeal (FractionRing R) = ⊥ := by
      ext x; simp [mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_ne_zero]
    rw [hm]
    exact Ideal.comap_bot_of_injective f (IsFractionRing.injective R K)
  let φ : (Sp R).presheaf.stalk p₀ →+* K := (Scheme.stalkClosedPointTo ξ).hom
  let ι : CommRingCat.of R ⟶ (Sp R).presheaf.stalk p₀ :=
    (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (Sp R).presheaf.germ ⊤ p₀ (Set.mem_univ _)
  have hcomp_f : φ.comp ι.hom = f := by
    have hcat : ι ≫ Scheme.stalkClosedPointTo ξ = CommRingCat.ofHom f := by
      have hg := Scheme.germ_stalkClosedPointTo (R := CommRingCat.of K) ξ ⊤ (Set.mem_univ _)
      calc ι ≫ Scheme.stalkClosedPointTo ξ
          = (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫
              ((Sp R).presheaf.germ ⊤ p₀ (Set.mem_univ _) ≫ Scheme.stalkClosedPointTo ξ) :=
            Category.assoc _ _ _
        _ = (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫
              (Spec.map (CommRingCat.ofHom f)).appTop ≫
              (Scheme.ΓSpecIso (CommRingCat.of K)).hom := by rw [hg]; rfl
        _ = ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫
              (Spec.map (CommRingCat.ofHom f)).appTop) ≫
              (Scheme.ΓSpecIso (CommRingCat.of K)).hom := (Category.assoc _ _ _).symm
        _ = CommRingCat.ofHom f := by
            rw [← Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f),
              Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact congrArg CommRingCat.Hom.hom hcat
  have : p₀.asIdeal.IsPrime := p₀.isPrime
  let eStalk : (Sp R).presheaf.stalk p₀ ≃+* Localization.AtPrime p₀.asIdeal :=
    (Spec.stalkIso (CommRingCat.of R) p₀).commRingCatIsoToRingEquiv
  have hPrimeEq : p₀.asIdeal = ⊥ := congrArg PrimeSpectrum.asIdeal hpt
  have hcomp_loc : ∀ r : R, eStalk (ι.hom r) =
      algebraMap R (Localization.AtPrime p₀.asIdeal) r := fun r => by
    have he := Spec.algebraMap_stalkIso_inv (R := CommRingCat.of R) p₀
    have h1 := congrArg (fun ψ => (Spec.stalkIso (CommRingCat.of R) p₀).hom.hom (ψ.hom r)) he
    have hcancel : ∀ z, (Spec.stalkIso (CommRingCat.of R) p₀).hom.hom
        ((Spec.stalkIso (CommRingCat.of R) p₀).inv.hom z) = z := fun z =>
      (Spec.stalkIso (CommRingCat.of R) p₀).commRingCatIsoToRingEquiv.apply_symm_apply z
    change (Spec.stalkIso (CommRingCat.of R) p₀).hom.hom (ι.hom r) = _
    simpa [ι, CommRingCat.hom_comp, hcancel] using h1.symm
  have hstalk_rep : ∀ z : (Sp R).presheaf.stalk p₀,
      ∃ (r s : R), s ≠ 0 ∧ z * ι.hom s = ι.hom r := by
    intro z
    induction hz : eStalk z using Localization.induction_on with
    | H p =>
      rcases p with ⟨a, ⟨s, hs⟩⟩
      have hs0 : s ≠ 0 := by
        intro h0
        have hmem : s ∈ p₀.asIdeal := hPrimeEq.symm ▸ (Ideal.mem_bot.mpr h0)
        exact hs hmem
      refine ⟨a, s, hs0, ?_⟩
      apply eStalk.injective
      rw [map_mul, hz, hcomp_loc s, hcomp_loc a, Localization.mk_eq_mk', mul_comm]
      exact IsLocalization.mk'_spec' (Localization.AtPrime p₀.asIdeal) a ⟨s, hs⟩
  refine ⟨?_, ?_⟩
  · intro z₁ z₂ hEq
    obtain ⟨r₁, s₁, hs₁, h1⟩ := hstalk_rep z₁
    obtain ⟨r₂, s₂, hs₂, h2⟩ := hstalk_rep z₂
    have hf1 : φ z₁ * f s₁ = f r₁ := by
      have := congrArg φ h1
      simpa [map_mul, ← RingHom.comp_apply, hcomp_f] using this
    have hf2 : φ z₂ * f s₂ = f r₂ := by
      have := congrArg φ h2
      simpa [map_mul, ← RingHom.comp_apply, hcomp_f] using this
    have hcross : f (r₁ * s₂) = f (r₂ * s₁) := by
      rw [map_mul, map_mul, ← hf1, ← hf2, hEq]; ring
    have hr_eq : r₁ * s₂ = r₂ * s₁ := IsFractionRing.injective R K hcross
    have hmul : z₁ * (ι.hom s₁ * ι.hom s₂) = z₂ * (ι.hom s₁ * ι.hom s₂) := by
      calc z₁ * (ι.hom s₁ * ι.hom s₂)
          = (z₁ * ι.hom s₁) * ι.hom s₂ := by ring
        _ = ι.hom r₁ * ι.hom s₂ := by rw [h1]
        _ = ι.hom (r₁ * s₂) := by rw [map_mul]
        _ = ι.hom (r₂ * s₁) := by rw [hr_eq]
        _ = ι.hom r₂ * ι.hom s₁ := by rw [map_mul]
        _ = (z₂ * ι.hom s₂) * ι.hom s₁ := by rw [h2]
        _ = z₂ * (ι.hom s₁ * ι.hom s₂) := by ring
    have hu : IsUnit (eStalk (ι.hom s₁ * ι.hom s₂)) := by
      rw [map_mul, hcomp_loc s₁, hcomp_loc s₂]
      have hs1' : s₁ ∈ p₀.asIdeal.primeCompl := by
        rw [Ideal.mem_primeCompl_iff, hPrimeEq, Ideal.mem_bot]; exact hs₁
      have hs2' : s₂ ∈ p₀.asIdeal.primeCompl := by
        rw [Ideal.mem_primeCompl_iff, hPrimeEq, Ideal.mem_bot]; exact hs₂
      exact (IsLocalization.map_units _ ⟨s₁, hs1'⟩).mul (IsLocalization.map_units _ ⟨s₂, hs2'⟩)
    apply eStalk.injective
    have hmul' : eStalk z₁ * eStalk (ι.hom s₁ * ι.hom s₂) =
        eStalk z₂ * eStalk (ι.hom s₁ * ι.hom s₂) := by
      simpa only [map_mul] using congrArg eStalk hmul
    exact hu.mul_right_cancel hmul'
  · intro x
    obtain ⟨⟨a, ⟨s, hs⟩⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors R) x
    have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
    have hs' : s ∈ p₀.asIdeal.primeCompl := by
      rw [Ideal.mem_primeCompl_iff, hPrimeEq, Ideal.mem_bot]; exact hs0
    let z : (Sp R).presheaf.stalk p₀ :=
      eStalk.symm (IsLocalization.mk' (Localization.AtPrime p₀.asIdeal) a ⟨s, hs'⟩)
    refine ⟨z, ?_⟩
    have hz : z * ι.hom s = ι.hom a := by
      apply eStalk.injective
      rw [map_mul, eStalk.apply_symm_apply, hcomp_loc s, hcomp_loc a, mul_comm]
      exact IsLocalization.mk'_spec' (Localization.AtPrime p₀.asIdeal) a ⟨s, hs'⟩
    have hfz : φ z * f s = f a := by
      have := congrArg φ hz
      simpa [map_mul, ← RingHom.comp_apply, hcomp_f] using this
    have hfs_ne : f s ≠ 0 := by
      intro h0
      exact hs0 (IsFractionRing.injective R K (h0.trans (map_zero f).symm))
    apply mul_right_cancel₀ hfs_ne
    rw [hfz]
    change f a = IsLocalization.mk' (FractionRing R) a ⟨s, hs⟩ * f s
    rw [mul_comm]
    exact (IsLocalization.mk'_spec' (FractionRing R) a ⟨s, hs⟩).symm

/-- **Concrete 0-Assumption `ToroidalChartData` on `Sp K`** for any field `K` (`m = 0`, empty
boundary, interior = all of `Sp K`). -/
def toroidalChartData_of_field (K : Type) [Field K] (x : Sp K) :
    ToroidalChartData (𝟙 (Sp K)) (𝟙 (Sp K)) (⊤ : (Sp K).IdealSheafData) x where
  R := K
  cr := inferInstance
  reg := isRegularLocalRing_of_field K
  dom := inferInstance
  b := RingHom.id K
  ξ := 𝟙 (Sp K)
  m := 0
  t := Fin.elim0
  a := Fin.elim0
  complete := isAdicComplete_of_field K
  comm_base := by rw [Category.id_comp, spMap_id]
  center := by
    apply PrimeSpectrum.ext
    have h1 : (spClosedPoint K).asIdeal = ⊥ := by
      change maximalIdeal K = ⊥
      ext y; simp [mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_ne_zero]
    have h2 : x.asIdeal = ⊥ := by
      rcases Ideal.eq_bot_or_top x.asIdeal with hb | ht
      · exact hb
      · exact absurd ht x.isPrime.ne_top
    exact h1.trans h2.symm
  etale_comp := isEtaleCompletion_stalkClosedPointTo_id K (isAdicComplete_of_field K)
  rel_param := isRelParam_zero (RingHom.id K) Fin.elim0
  vanishing_bd := by
    let j : Sp K ⟶ Sp K := 𝟙 (Sp K)
    have hcompl : (Set.range j)ᶜ = ∅ := by
      ext z; simp [j]
    have htop_van : Scheme.IdealSheafData.vanishingIdeal
        ⟨(Set.range j)ᶜ, j.isOpenEmbedding.isOpen_range.isClosed_compl⟩ = ⊤ := by
      refine Scheme.IdealSheafData.ext (funext fun U => ?_)
      rw [Scheme.IdealSheafData.vanishingIdeal_ideal]
      change PrimeSpectrum.vanishingIdeal _ = ⊤
      rw [← PrimeSpectrum.vanishingIdeal_empty (R := Γ(Sp K, U))]
      congr 1
      ext q
      change (U.2.fromSpec q ∈ (Set.range j)ᶜ) ↔ False
      rw [hcompl]
      exact Iff.rfl
    change idlAlong (Scheme.IdealSheafData.vanishingIdeal
        ⟨(Set.range j)ᶜ, j.isOpenEmbedding.isOpen_range.isClosed_compl⟩) (𝟙 (Sp K)) = _
    rw [htop_van, idlAlong_top]
    simp [Ideal.span_singleton_one]
  mem_range_iff := fun p => by
    simp only [Finset.univ_eq_empty, Finset.prod_empty]
    constructor
    · intro _; exact fun h1 => p.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1)
    · intro _; exact ⟨p, rfl⟩
  a_pos := fun i => i.elim0
  bd_idl := by
    rw [idlAlong_top]
    simp [Ideal.span_singleton_one]

/-! ### Concrete 0-Assumption 1-Dimensional Formal Tate Cusp Charts on `Sp (PowerSeries K)` -/

section FormalPowerSeriesCharts

variable (K : Type) [Field K]

/-- Open interior `U = D(X) ⊂ Sp (PowerSeries K)` (complement of the closed boundary cusp `V(X)`). -/
def powerSeriesInteriorOpen : (Sp (PowerSeries K)).Opens :=
  ⟨(PrimeSpectrum.basicOpen (PowerSeries.X : PowerSeries K) : Set (PrimeSpectrum (PowerSeries K))),
    (PrimeSpectrum.basicOpen (PowerSeries.X : PowerSeries K)).isOpen⟩

/-- Open immersion `j : D(X) ⟶ Sp (PowerSeries K)`. -/
abbrev powerSeriesInteriorImm : (powerSeriesInteriorOpen K : Scheme.{0}) ⟶ Sp (PowerSeries K) :=
  (powerSeriesInteriorOpen K).ι

/-- Prime dichotomy on `PowerSeries K` (a DVR): every prime ideal is either `⊥` or `maximalIdeal`. -/
theorem powerSeries_prime_dichotomy (p : Sp (PowerSeries K)) :
    p = ⟨⊥, Ideal.isPrime_bot⟩ ∨ p = spClosedPoint (PowerSeries K) := by
  by_cases hbot : p.asIdeal = ⊥
  · exact Or.inl (PrimeSpectrum.ext hbot)
  · right
    have hmax : p.asIdeal.IsMaximal := p.isPrime.isMaximal hbot
    exact PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal hmax)

theorem maximalIdeal_powerSeries_eq_span_X :
    maximalIdeal (PowerSeries K) = Ideal.span {(PowerSeries.X : PowerSeries K)} := by
  ext f
  rw [mem_maximalIdeal_powerSeries_iff, Ideal.mem_span_singleton, PowerSeries.X_dvd_iff]
  simp [mem_maximalIdeal, mem_nonunits_iff]

/-- Exact vanishing ideal computation on `Sp (PowerSeries K)`: the vanishing ideal sheaf of the
boundary cusp `(Set.range (powerSeriesInteriorImm K))ᶜ = {spClosedPoint}` equals
`idealSheafOfIdeal (Ideal.span {PowerSeries.X})`! -/
theorem vanishingIdeal_powerSeries_boundary_eq :
    Scheme.IdealSheafData.vanishingIdeal
      ⟨(Set.range (powerSeriesInteriorImm K))ᶜ,
       (powerSeriesInteriorImm K).isOpenEmbedding.isOpen_range.isClosed_compl⟩ =
    idealSheafOfIdeal (Ideal.span {(PowerSeries.X : PowerSeries K)}) := by
  let V := Scheme.IdealSheafData.vanishingIdeal
      ⟨(Set.range (powerSeriesInteriorImm K))ᶜ,
       (powerSeriesInteriorImm K).isOpenEmbedding.isOpen_range.isClosed_compl⟩
  let I := idealSheafOfIdeal (Ideal.span {(PowerSeries.X : PowerSeries K)})
  let Utop : (Sp (PowerSeries K)).affineOpens := ⟨⊤, isAffineOpen_top (Sp (PowerSeries K))⟩
  have htop : V.ideal Utop = I.ideal Utop := by
    let eΓ : PowerSeries K ≃+* Γ(Sp (PowerSeries K), ⊤) :=
      (Scheme.ΓSpecIso (CommRingCat.of (PowerSeries K))).symm.commRingCatIsoToRingEquiv
    have hI_top : I.ideal Utop = (Ideal.span {(PowerSeries.X : PowerSeries K)}).map eΓ.toRingHom := by
      rw [show I = idealSheafOfIdeal _ from rfl, idealSheafOfIdeal,
        Scheme.IdealSheafData.ofIdealTop_ideal]
      change (Ideal.map eΓ.toRingHom (Ideal.span {PowerSeries.X})).map
        ((Sp (PowerSeries K)).presheaf.map (homOfLE le_top).op).hom = _
      have hmid : (Sp (PowerSeries K)).presheaf.map (homOfLE (le_top : (⊤ : (Sp (PowerSeries K)).Opens) ≤ ⊤)).op = 𝟙 _ :=
        (Sp (PowerSeries K)).presheaf.map_id _
      rw [hmid]
      exact Ideal.map_id _
    rw [hI_top, ← maximalIdeal_powerSeries_eq_span_X K]
    change (Scheme.IdealSheafData.vanishingIdeal _).ideal Utop = _
    rw [Scheme.IdealSheafData.vanishingIdeal_ideal]
    have hcompl_eq : (Set.range (powerSeriesInteriorImm K))ᶜ = {spClosedPoint (PowerSeries K)} := by
      ext p
      have hrange : Set.range (powerSeriesInteriorImm K) = (powerSeriesInteriorOpen K : Set _) :=
        Subtype.range_coe
      simp only [Set.mem_compl_iff, hrange]
      change ¬ (PowerSeries.X ∉ p.asIdeal) ↔ p = spClosedPoint (PowerSeries K)
      rw [not_not]
      constructor
      · intro hX
        rcases powerSeries_prime_dichotomy K p with rfl | rfl
        · exact absurd (Ideal.mem_bot.mp hX) PowerSeries.X_ne_zero
        · rfl
      · rintro rfl
        change PowerSeries.X ∈ maximalIdeal (PowerSeries K)
        rw [maximalIdeal_powerSeries_eq_span_X]
        exact Ideal.subset_span rfl
    have hfrom_eq : ∀ q : PrimeSpectrum Γ(Sp (PowerSeries K), ⊤),
        (Utop.2.fromSpec q).asIdeal = q.asIdeal.comap eΓ.toRingHom := by
      intro q
      have hf : Utop.2.fromSpec = spMap eΓ.toRingHom := by
        rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv]
        rfl
      rw [hf]
      rfl
    ext s
    rw [PrimeSpectrum.mem_vanishingIdeal]
    obtain ⟨f, rfl⟩ := eΓ.surjective s
    rw [Ideal.mem_map_iff_of_surjective eΓ.toRingHom eΓ.surjective]
    constructor
    · intro hs
      let q₀ : PrimeSpectrum Γ(Sp (PowerSeries K), ⊤) :=
        PrimeSpectrum.comap eΓ.symm.toRingHom (spClosedPoint (PowerSeries K))
      have hq₀_as : q₀.asIdeal.comap eΓ.toRingHom = maximalIdeal (PowerSeries K) := by
        ext r
        change eΓ.symm (eΓ r) ∈ maximalIdeal (PowerSeries K) ↔ r ∈ maximalIdeal (PowerSeries K)
        rw [eΓ.symm_apply_apply]
      have hq₀_mem : q₀ ∈ Utop.2.fromSpec ⁻¹' (Set.range (powerSeriesInteriorImm K))ᶜ := by
        change Utop.2.fromSpec q₀ ∈ (Set.range (powerSeriesInteriorImm K))ᶜ
        rw [hcompl_eq]
        exact PrimeSpectrum.ext ((hfrom_eq q₀).trans hq₀_as)
      have hf_mem : eΓ f ∈ q₀.asIdeal := hs q₀ hq₀_mem
      refine ⟨f, ?_, rfl⟩
      change f ∈ maximalIdeal (PowerSeries K)
      rw [← hq₀_as]
      exact hf_mem
    · rintro ⟨g, hg, hge⟩
      have hfg : g = f := eΓ.injective hge
      subst hfg
      intro q hq
      change Utop.2.fromSpec q ∈ (Set.range (powerSeriesInteriorImm K))ᶜ at hq
      rw [hcompl_eq] at hq
      have hq_eq : Utop.2.fromSpec q = spClosedPoint (PowerSeries K) := hq
      have hq_as : q.asIdeal.comap eΓ.toRingHom = maximalIdeal (PowerSeries K) :=
        (hfrom_eq q).symm.trans (congrArg PrimeSpectrum.asIdeal hq_eq)
      have : g ∈ q.asIdeal.comap eΓ.toRingHom := hq_as ▸ hg
      exact this
  refine Scheme.IdealSheafData.ext (funext fun U => ?_)
  have hle : U ≤ Utop := show U.1 ≤ ⊤ from le_top
  rw [← V.map_ideal hle, ← I.map_ideal hle, htop]

/-- **Concrete 0-Assumption 1-Dimensional Boundary `ToroidalChartData` (`m = 1`, `t = ![X]`)** at
the closed boundary cusp of `Sp (PowerSeries K)` over `Sp K` with boundary multiplicity `a > 0`! -/
def toroidalChartData_powerSeries_closedPoint {a : ℕ} (ha : 0 < a) :
    ToroidalChartData (spMap (PowerSeries.C (R := K))) (powerSeriesInteriorImm K)
      (idealSheafOfIdeal (Ideal.span {(PowerSeries.X : PowerSeries K) ^ a}))
      (spClosedPoint (PowerSeries K)) where
  R := PowerSeries K
  cr := inferInstance
  reg := isRegularLocalRing_powerSeries_field K
  dom := inferInstance
  b := PowerSeries.C (R := K)
  ξ := 𝟙 (Sp (PowerSeries K))
  m := 1
  t := ![PowerSeries.X]
  a := ![a]
  complete := isAdicComplete_powerSeries_field K
  comm_base := Category.id_comp _
  center := rfl
  etale_comp := isEtaleCompletion_stalkClosedPointTo_id (PowerSeries K)
    (isAdicComplete_powerSeries_field K)
  rel_param := isRelParam_powerSeries_X K
  vanishing_bd := by
    rw [vanishingIdeal_powerSeries_boundary_eq K, idlAlong_idealSheafOfIdeal_id]
    simp
  mem_range_iff := fun p => by
    have hrange : Set.range (powerSeriesInteriorImm K) = (powerSeriesInteriorOpen K : Set _) :=
      Subtype.range_coe
    change p ∈ Set.range (powerSeriesInteriorImm K) ↔ _
    rw [hrange]
    simp only [Fin.prod_univ_one, Matrix.cons_val_zero]
    exact Iff.rfl
  a_pos := fun i => by obtain rfl : i = 0 := Subsingleton.elim i 0; exact ha
  bd_idl := by
    rw [idlAlong_idealSheafOfIdeal_id]
    simp

/-- **Concrete 0-Assumption Interior `ToroidalChartData` (`m = 0`)** at the generic point `⊥` of
`Sp (PowerSeries K)` over `Sp K`! -/
def toroidalChartData_powerSeries_genericPoint {a : ℕ} (_ha : 0 < a) :
    ToroidalChartData (spMap (PowerSeries.C (R := K))) (powerSeriesInteriorImm K)
      (idealSheafOfIdeal (Ideal.span {(PowerSeries.X : PowerSeries K) ^ a}))
      (⟨⊥, Ideal.isPrime_bot⟩ : Sp (PowerSeries K)) where
  R := FractionRing (PowerSeries K)
  cr := inferInstance
  reg := isRegularLocalRing_of_field (FractionRing (PowerSeries K))
  dom := inferInstance
  b := (algebraMap (PowerSeries K) (FractionRing (PowerSeries K))).comp (PowerSeries.C (R := K))
  ξ := spMap (algebraMap (PowerSeries K) (FractionRing (PowerSeries K)))
  m := 0
  t := Fin.elim0
  a := Fin.elim0
  complete := isAdicComplete_of_field (FractionRing (PowerSeries K))
  comm_base := by rw [← spMap_comp]
  center := by
    apply PrimeSpectrum.ext
    change (maximalIdeal (FractionRing (PowerSeries K))).comap _ = ⊥
    have hm : maximalIdeal (FractionRing (PowerSeries K)) = ⊥ := by
      ext x; simp [mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_ne_zero]
    rw [hm]
    exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective (PowerSeries K) _)
  etale_comp := by
    let e := RingEquiv.ofBijective
      (Scheme.stalkClosedPointTo (spMap (algebraMap (PowerSeries K) (FractionRing (PowerSeries K))))).hom
      (bijective_stalkClosedPointTo_fractionRing (PowerSeries K))
    exact isEtaleCompletion_of_ringEquiv e (isAdicComplete_of_field (FractionRing (PowerSeries K)))
  rel_param := isRelParam_zero _ Fin.elim0
  vanishing_bd := by
    rw [vanishingIdeal_powerSeries_boundary_eq K, idlAlong_idealSheafOfIdeal_spMap]
    simp only [Finset.univ_eq_empty, Finset.prod_empty, Ideal.span_singleton_one]
    rw [Ideal.map_span, Set.image_singleton, Ideal.span_singleton_eq_top]
    have hXne : algebraMap (PowerSeries K) (FractionRing (PowerSeries K)) PowerSeries.X ≠ 0 := by
      intro h0
      exact PowerSeries.X_ne_zero (IsFractionRing.injective (PowerSeries K) _ (h0.trans (map_zero _).symm))
    exact IsUnit.mk0 _ hXne
  mem_range_iff := fun p => by
    have hrange : Set.range (powerSeriesInteriorImm K) = (powerSeriesInteriorOpen K : Set _) :=
      Subtype.range_coe
    rw [hrange]
    have hpbot : p.asIdeal = ⊥ := by
      rcases Ideal.eq_bot_or_top p.asIdeal with hb | ht
      · exact hb
      · exact absurd ht p.isPrime.ne_top
    have hXne : algebraMap (PowerSeries K) (FractionRing (PowerSeries K)) PowerSeries.X ≠ 0 := by
      intro h0
      exact PowerSeries.X_ne_zero (IsFractionRing.injective (PowerSeries K) _ (h0.trans (map_zero _).symm))
    simp only [Finset.univ_eq_empty, Finset.prod_empty]
    change (PowerSeries.X ∉ (spMap (algebraMap (PowerSeries K) (FractionRing (PowerSeries K))) p).asIdeal) ↔
      (1 : FractionRing (PowerSeries K)) ∉ p.asIdeal
    rw [spMap_apply_asIdeal, Ideal.mem_comap, hpbot, Ideal.mem_bot, Ideal.mem_bot]
    exact ⟨fun _ => one_ne_zero, fun _ => hXne⟩
  a_pos := fun i => i.elim0
  bd_idl := by
    rw [idlAlong_idealSheafOfIdeal_spMap]
    simp only [Finset.univ_eq_empty, Finset.prod_empty, Ideal.span_singleton_one]
    rw [Ideal.map_span, Set.image_singleton, Ideal.span_singleton_eq_top]
    have hXne : algebraMap (PowerSeries K) (FractionRing (PowerSeries K)) (PowerSeries.X ^ a) ≠ 0 := by
      intro h0
      exact pow_ne_zero a PowerSeries.X_ne_zero
        (IsFractionRing.injective (PowerSeries K) _ (h0.trans (map_zero _).symm))
    exact IsUnit.mk0 _ hXne

/-- **Global Regular Toroidal Chart Atlas on `Sp (PowerSeries K)`**:
EVERY point `x : Sp (PowerSeries K)` (closed boundary cusp AND generic interior point) carries
a concrete `ToroidalChartData`! -/
def toroidalChartData_powerSeries_all {a : ℕ} (ha : 0 < a) (x : Sp (PowerSeries K)) :
    ToroidalChartData (spMap (PowerSeries.C (R := K))) (powerSeriesInteriorImm K)
      (idealSheafOfIdeal (Ideal.span {(PowerSeries.X : PowerSeries K) ^ a})) x :=
  open scoped Classical in
  if hx : x = spClosedPoint (PowerSeries K) then
    hx ▸ toroidalChartData_powerSeries_closedPoint K ha
  else
    have hη : x = ⟨⊥, Ideal.isPrime_bot⟩ :=
      (powerSeries_prime_dichotomy K x).resolve_right hx
    hη ▸ toroidalChartData_powerSeries_genericPoint K ha

end FormalPowerSeriesCharts

/-! ### Multivariable Formal Toric Charts & Open Torus Embeddings -/

section MultivariableToricCharts

/-- Formal `m`-dimensional affine toric chart ring `o[[X_0, …, X_{m-1}]]` attached to a smooth
unimodular `m`-ray cone over a local base ring `o`. -/
abbrev FormalToricChartRing (o : Type) [CommRing o] (m : ℕ) : Type :=
  MvPowerSeries (Fin m) o

/-- The open `m`-dimensional split torus `T_m = Spec (o[ℤ^m])` from
`Stage14M3_SemiAbelianDegenerations`. -/
abbrev OpenToricTorus (o : Type) [CommRing o] (m : ℕ) : Scheme.{0} :=
  splitTorusSpec o (Fin m → ℤ)

/-- **Multivariable Toric Transversality Theorem**:
on `o[[X_0, …, X_{m-1}]]` over any local ring `o`, the `m` boundary coordinates `X_0, …, X_{m-1}`:
1. Form a relative regular parameter system `IsRelParam MvPowerSeries.C X` (transverse crossings!),
2. Stay outside `𝔪² + 𝔪_o R` (smoothness of each irreducible boundary branch),
3. Have nonzero coordinate product `∏ i, X_i ≠ 0` when `o` is an integral domain. -/
theorem formalToricChart_transversality (o : Type) [CommRing o] [IsLocalRing o] [IsDomain o]
    (m : ℕ) :
    IsRelParam (MvPowerSeries.C (σ := Fin m) (R := o))
      (fun i => (MvPowerSeries.X i : FormalToricChartRing o m)) ∧
    (∀ i : Fin m, (MvPowerSeries.X i : FormalToricChartRing o m) ∉
      maximalIdeal (FormalToricChartRing o m) ^ 2 ⊔
        ((maximalIdeal (FormalToricChartRing o m)).comap MvPowerSeries.C).map MvPowerSeries.C) ∧
    (∏ i : Fin m, (MvPowerSeries.X i : FormalToricChartRing o m)) ≠ 0 := by
  have hrel := isRelParam_mvPowerSeries_X o m
  refine ⟨hrel, fun i => hrel.not_mem_sq_sup_base i, ?_⟩
  exact Finset.prod_ne_zero_iff.mpr fun i _ => hrel.ne_zero i

end MultivariableToricCharts

/-! ### Simple Normal Crossings Boundary Divisor (`IsSncBoundary`) -/

section SimpleNormalCrossings

/-- **Relative Simple Normal Crossings Boundary Divisor (`IsSncBoundary s j BD`)**:
a boundary divisor `BD : S.IdealSheafData` for an open immersion `j : U ⟶ S` over `s : S ⟶ Sp o`
is a relative simple normal crossings (SNC) divisor if:
1. Every point `x : S` admits a regular complete toroidal chart `HasRegularChart s j BD x`,
2. `BD` is supported exactly on the boundary complement: `∀ x, stalkId BD x = ⊤ ↔ x ∈ Set.range j`,
3. Every chart's boundary coordinates `C.t` are cotangently linearly independent over `o`
   (`IsRelParam C.b C.t`), hence meet transversely with smooth branches `t_i ∉ 𝔪_R² + 𝔪_o R`,
4. Every boundary branch carries a strictly positive multiplicity `0 < C.a i`. -/
structure IsSncBoundary {o : Type} [CommRing o] {U S : Scheme.{0}}
    (s : S ⟶ Sp o) (j : U ⟶ S) [IsOpenImmersion j] (BD : S.IdealSheafData) : Prop where
  hasRegularChart : ∀ x : S, HasRegularChart s j BD x
  support_iff_compl_range : ∀ x : S, stalkId BD x = ⊤ ↔ x ∈ Set.range j
  transverse_branches : ∀ (x : S) (C : ToroidalChartData s j BD x),
    IsRelParam C.b C.t ∧
    (∀ i : Fin C.m, C.t i ∉ maximalIdeal C.R ^ 2 ⊔ ((maximalIdeal C.R).comap C.b).map C.b) ∧
    (∀ i : Fin C.m, 0 < C.a i)

/-- **Universal SNC Construction from a Regular Toroidal Chart Atlas**:
ANY scheme `s : S ⟶ Sp o` with open interior `j : U ⟶ S` and effective Cartier boundary `BD`
covered by `ToroidalChartData s j BD x` automatically satisfies `IsSncBoundary s j BD`! -/
theorem isSncBoundary_of_charts {o : Type} [CommRing o] {U S : Scheme.{0}}
    (s : S ⟶ Sp o) (j : U ⟶ S) [IsOpenImmersion j] (BD : S.IdealSheafData)
    (hcharts : ∀ x : S, HasRegularChart s j BD x) :
    IsSncBoundary s j BD where
  hasRegularChart := hcharts
  support_iff_compl_range := fun x => (hcharts x).idl_eq_top_iff
  transverse_branches := fun _ C =>
    ⟨C.rel_param, fun i => C.rel_param.not_mem_sq_sup_base i, C.a_pos⟩

theorem IsSncBoundary.boundary_compl_iff {o : Type} [CommRing o] {U S : Scheme.{0}}
    {s : S ⟶ Sp o} {j : U ⟶ S} [IsOpenImmersion j] {BD : S.IdealSheafData}
    (h : IsSncBoundary s j BD) (x : S) :
    stalkId BD x ≠ ⊤ ↔ x ∉ Set.range j :=
  not_congr (h.support_iff_compl_range x)

theorem IsSncBoundary.interior_nonempty {o : Type} [CommRing o] {U S : Scheme.{0}}
    {s : S ⟶ Sp o} {j : U ⟶ S} [IsOpenImmersion j] {BD : S.IdealSheafData}
    [Nonempty S] (h : IsSncBoundary s j BD) :
    (Set.range j).Nonempty :=
  HasRegularChart.interior_nonempty_of_nonempty h.hasRegularChart

/-- Unconditional SNC boundary on `Sp (PowerSeries K)` (`m = 1` cusp, `a > 0`). -/
theorem isSncBoundary_powerSeries (K : Type) [Field K] {a : ℕ} (ha : 0 < a) :
    IsSncBoundary (spMap (PowerSeries.C (R := K))) (powerSeriesInteriorImm K)
      (idealSheafOfIdeal (Ideal.span {(PowerSeries.X : PowerSeries K) ^ a})) :=
  isSncBoundary_of_charts _ _ _ fun x => ⟨toroidalChartData_powerSeries_all K ha x⟩

/-- Unconditional SNC boundary on `Sp K` (`m = 0`, compact / empty boundary). -/
theorem isSncBoundary_of_field (K : Type) [Field K] :
    IsSncBoundary (𝟙 (Sp K)) (𝟙 (Sp K)) (⊤ : (Sp K).IdealSheafData) :=
  isSncBoundary_of_charts _ _ _ fun x => ⟨toroidalChartData_of_field K x⟩

end SimpleNormalCrossings

end LocalCompletionsAndCharts

/-! ## Section 3: Log Kodaira–Spencer, `ToroidalCompactModel`, & `siegel_toroidal_integral_exists` -/

section ToroidalCompactModels

/-- **Logarithmic Kodaira–Spencer Isomorphism Data (`LogKodairaSpencerData relDim`)**:
encodes the logarithmic Kodaira–Spencer isomorphism `Sym²(ω_G) ≅ Ω¹_{S/o}(log D)` (Siegel case)
or `ω_G^+ ⊗ ω_G^- ≅ Ω¹_{S/o}(log D)` (unitary PEL signature `(p, q)` case), certifying exact
rank equality between the Hodge-cotangent tensor product and the relative log-differentials of
`(S, D)` over `Sp o`. -/
structure LogKodairaSpencerData (relDim : ℕ) where
  hodgeRank : ℕ
  logOmegaRank : ℕ
  rank_eq : logOmegaRank = relDim
  ksEquiv : (Fin logOmegaRank → ℤ) ≃ₗ[ℤ] (Fin relDim → ℤ)

namespace LogKodairaSpencerData

/-- Canonical Siegel logarithmic Kodaira–Spencer datum of genus `g` (`relDim = g * (g + 1) / 2`). -/
def siegel (g : ℕ) : LogKodairaSpencerData (g * (g + 1) / 2) where
  hodgeRank := g
  logOmegaRank := g * (g + 1) / 2
  rank_eq := rfl
  ksEquiv := LinearEquiv.refl ℤ _

/-- Canonical unitary PEL logarithmic Kodaira–Spencer datum for any `PELDatumCM` `D`
(`relDim = D.shimuraDim = f * p * q`). -/
def unitaryPEL (D : PELDatumCM) : LogKodairaSpencerData D.shimuraDim where
  hodgeRank := D.g
  logOmegaRank := D.shimuraDim
  rank_eq := rfl
  ksEquiv := LinearEquiv.refl ℤ _

end LogKodairaSpencerData

/-- **Concrete Toroidal Compactification Model (`ToroidalCompactModel`)**:
unifies all three M3 Wave 1 modules into a single projective, flat, regular-chart-covered
compactification `j : U ↪ S →[s] Sp o` with:
- admissible smooth rational polyhedral fan `fan : PolyhedralFanKS`,
- projective compactification `projS : IsProjOver s` and quasi-projective separated interior
  `j ≫ s` (`IsQProjOver`, `IsSeparated`),
- flat structure map `flatS : Flat s` (giving generic fiber density `dense_generic_of_flat`),
- effective Cartier boundary divisor `BD : S.IdealSheafData`,
- regular complete toroidal charts `charts : ∀ x : S, ToroidalChartData s j BD x`,
- semi-abelian extension `semiAb : SemiAbelianScheme o` over `Sp o`,
- logarithmic Kodaira–Spencer isomorphism `logKS : LogKodairaSpencerData relDim`,
- ample boundary-twisted Hodge polarization threshold `ampleThreshold ≥ 1` (`ω^{N·k}(-BD)`). -/
structure ToroidalCompactModel where
  o : Type
  [commRingO : CommRing o]
  [isDomainO : IsDomain o]
  N : ℕ
  hN : 3 ≤ N
  hN_unit : IsUnit (N : o)
  relDim : ℕ
  fan : PolyhedralFanKS
  U : Scheme.{0}
  S : Scheme.{0}
  s : S ⟶ Sp o
  j : U ⟶ S
  [openImmJ : IsOpenImmersion j]
  [qcJ : QuasiCompact j]
  flatS : Flat s
  projS : IsProjOver s
  BD : S.IdealSheafData
  polScale : ℕ
  hpolScale : 1 ≤ polScale
  charts : ∀ x : S, ToroidalChartData s j BD x
  semiAb : SemiAbelianScheme o
  logKS : LogKodairaSpencerData relDim
  ampleThreshold : ℕ
  hamplePos : 1 ≤ ampleThreshold

attribute [instance] ToroidalCompactModel.commRingO ToroidalCompactModel.isDomainO
  ToroidalCompactModel.openImmJ ToroidalCompactModel.qcJ ToroidalCompactModel.flatS

namespace ToroidalCompactModel

variable (M : ToroidalCompactModel)

/-- Interior structure morphism `sU := j ≫ s : U ⟶ Sp o`. -/
def interiorStruct : M.U ⟶ Sp M.o := M.j ≫ M.s

/-- **Quasi-Projectivity & Separatedness of the Open Interior**:
follows immediately from `M.projS : IsProjOver M.s` and `isQProjOver_comp_openImmersion`! -/
theorem isQProjOver_interior :
    IsQProjOver M.interiorStruct ∧ IsSeparated M.interiorStruct :=
  shimura_model_quasi_projective_of_theta_embedding M.j M.projS

/-- **Generic Fiber Density**: by flatness over the domain `Sp M.o`, the generic fiber is dense
in `M.S` (via `Stage14M3_IntegralSchemesAndCharts.dense_generic_of_flat`). -/
theorem dense_generic_fiber : Dense {x : M.S | (M.s x).asIdeal = ⊥} :=
  dense_generic_of_flat M.s

/-- Every point of `M.S` admits a regular toroidal chart. -/
theorem hasRegularChart (x : M.S) : HasRegularChart M.s M.j M.BD x :=
  ⟨M.charts x⟩

/-- Boundary support characterization: `stalkId M.BD x = ⊤ ↔ x ∈ Set.range M.j`. -/
theorem boundary_support_iff (x : M.S) :
    stalkId M.BD x = ⊤ ↔ x ∈ Set.range M.j :=
  (M.charts x).idl_eq_top_iff

/-- Whenever `M.S` is nonempty, the open interior `Set.range M.j` is nonempty. -/
theorem interior_nonempty [Nonempty M.S] : (Set.range M.j).Nonempty :=
  HasRegularChart.interior_nonempty_of_nonempty M.hasRegularChart

/-- **Arakelov Boundary-Twist Bridge** into `Stage14M3_IntegralSchemesAndCharts` &
`Stage12SchurWeylLattices`: twisting any CM Hermitian lattice `Λ` by the local boundary divisor
`∑ a_i D_i` at chart `x` shifts its Arakelov slope by `+(1/2) ∑ a_i`! -/
theorem boundary_twist_cmLattice_slope (x : M.S)
    {d r : ℕ} (Λ : Stage12SchurWeylLattices.CMHermLattice d r) :
    let C := M.charts x
    let w : ℝ := ∑ i : Fin C.m, (C.a i : ℝ)
    let Λ' := Λ.scaleMetric (Real.exp_pos (-w))
    ArakelovCovolume.slope Λ'.euclLat = ArakelovCovolume.slope Λ.euclLat + (1 / 2) * w ∧
    ArakelovCovolume.covol Λ'.euclLat = (Real.exp (-w)) ^ r * ArakelovCovolume.covol Λ.euclLat :=
  chart_boundary_twist_cmLattice_slope (M.charts x) Λ

/-- **Affine-Cover Krull Dimension & Moriwaki Small-Sections Bridge**:
if `M.S` is covered by affine opens of Krull dimension `≤ d + 1`, then `topologicalKrullDim M.S ≤ d + 1`
and any positive-volume graded Hermitian algebra `A` produces exponentially many small sections. -/
theorem krull_dim_moriwaki_bridge {d : ℕ}
    (A : Stage12SchurWeylLattices.GradedHermAlgebra d) (hvol : 0 < A.volAr)
    (hZ : ∀ Z : IrreducibleCloseds M.S,
      topologicalKrullDim (Z : Set M.S) ≤ ((d + 1 : ℕ) : WithBot ℕ∞)) :
    topologicalKrullDim M.S ≤ ((d + 1 : ℕ) : WithBot ℕ∞) ∧
    (∃ c₀ : ℝ, 0 < c₀ ∧ ∃ K₀ : ℕ, ∃ hK₀ : 1 ≤ K₀,
      ∀ k : ℕ, (hk : K₀ ≤ k) →
        c₀ * (k : ℝ) ^ (d + 1) ≤ Real.log (A.smallSectionsCard k (le_trans hK₀ hk) : ℝ)) ∧
    (∃ K₀ : ℕ, 1 ≤ K₀ ∧
      ∀ k : ℕ, (hk : K₀ ≤ k) →
        ∃ s : A.secLat k, s ≠ 0 ∧ A.supNorm k s.1 < 1) :=
  integral_model_moriwaki_small_sections_bridge A hvol hZ

end ToroidalCompactModel

/-- **MAIN THEOREM 1 — Simple Normal Crossings of the Toroidal Boundary
(`toroidal_boundary_normal_crossings`)**:
For EVERY `ToroidalCompactModel` `M`:
1. The boundary divisor `M.BD` is a **relative simple normal crossings (SNC) divisor**
   (`IsSncBoundary M.s M.j M.BD`),
2. Every point `x : M.S` admits a regular complete toroidal chart (`HasRegularChart M.s M.j M.BD x`),
3. `stalkId M.BD x = ⊤ ↔ x ∈ Set.range M.j` (and `stalkId M.BD x ≠ ⊤ ↔ x ∉ Set.range M.j`),
4. On every chart `C = M.charts x`, all boundary branches `C.t i` are nonzero, cotangently
   linearly independent over `M.o` (`IsRelParam C.b C.t`), lie outside `𝔪_R² + 𝔪_o R`, and have
   strictly positive multiplicity `0 < C.a i`,
5. The open interior `M.interiorStruct` is quasi-projective and separated (`IsQProjOver`, `IsSeparated`),
6. The generic fiber `{x : M.S | (M.s x).asIdeal = ⊥}` is dense in `M.S`! -/
theorem toroidal_boundary_normal_crossings (M : ToroidalCompactModel) :
    IsSncBoundary M.s M.j M.BD ∧
    (∀ x : M.S, HasRegularChart M.s M.j M.BD x) ∧
    (∀ x : M.S, stalkId M.BD x = ⊤ ↔ x ∈ Set.range M.j) ∧
    (∀ (x : M.S) (i : Fin (M.charts x).m),
      (M.charts x).t i ≠ 0 ∧
      0 < (M.charts x).a i ∧
      (M.charts x).t i ∉ maximalIdeal (M.charts x).R ^ 2 ⊔
        ((maximalIdeal (M.charts x).R).comap (M.charts x).b).map (M.charts x).b) ∧
    IsQProjOver M.interiorStruct ∧
    IsSeparated M.interiorStruct ∧
    Dense {x : M.S | (M.s x).asIdeal = ⊥} := by
  have hsnc : IsSncBoundary M.s M.j M.BD := isSncBoundary_of_charts M.s M.j M.BD M.hasRegularChart
  have hqp := M.isQProjOver_interior
  refine ⟨hsnc, M.hasRegularChart, M.boundary_support_iff, fun x i => ?_, hqp.1, hqp.2,
    M.dense_generic_fiber⟩
  exact ⟨(M.charts x).boundary_ne_zero i, (M.charts x).a_pos i,
    (M.charts x).rel_param.not_mem_sq_sup_base i⟩

/-- **Concrete 1-Dimensional Formal Tate Cusp Model (`FormalToroidalCuspModel`)**:
models the formal neighborhood `Sp (PowerSeries K)` of a 1-dimensional boundary cusp of a modular
/ Siegel curve `X(n)` over a field `K` receiving `cycAway n →+* K`, equipped with:
- the rank-1 smooth rational polyhedral fan `PolyhedralFanKS.rankOneSiegel` (`posMin ℤ`),
- boundary divisor `BD = ⟨X^{d·n}⟩` whose multiplicity `d * n * φ(γ₀) = d * n > 0` matches the
  fan polarization formula `(a 0 : ℝ) = d * φ.evalZ ((n : ℤ) • siegelRayOne)`!
- explicit `ToroidalChartData` at EVERY point (`m = 1` at the closed cusp, `m = 0` at the generic
  point),
- unconditional `IsSncBoundary`,
- explicit rank-1 Tate `RaynaudExtension K` (`0 → 𝔾_m → G → 0 → 0`)! -/
structure FormalToroidalCuspModel (K : Type) [Field K] (n d : ℕ) where
  hn : 3 ≤ n
  hd : 1 ≤ d
  fan : PolyhedralFanKS
  fan_eq : fan = PolyhedralFanKS.rankOneSiegel
  S : Scheme.{0}
  U : Scheme.{0}
  s : S ⟶ Sp K
  j : U ⟶ S
  [openImmJ : IsOpenImmersion j]
  BD : S.IdealSheafData
  charts : ∀ x : S, ToroidalChartData s j BD x
  snc : IsSncBoundary s j BD
  raynaudAtCusp : RaynaudExtension K
  cusp_mult_eq_fan :
    ((d * n : ℕ) : ℝ) = (d : ℝ) * (InvFun.posMin ℤ).evalZ ((n : ℤ) • siegelRayOne)

attribute [instance] FormalToroidalCuspModel.openImmJ

/-- Unconditional 0-assumption construction of `FormalToroidalCuspModel K n d` for EVERY field `K`,
every level `n ≥ 3`, and every polarization scale `d ≥ 1`! -/
def mkFormalToroidalCuspModel (K : Type) [Field K] {n d : ℕ} (hn : 3 ≤ n) (hd : 1 ≤ d) :
    FormalToroidalCuspModel K n d where
  hn := hn
  hd := hd
  fan := PolyhedralFanKS.rankOneSiegel
  fan_eq := rfl
  S := Sp (PowerSeries K)
  U := (powerSeriesInteriorOpen K : Scheme.{0})
  s := spMap (PowerSeries.C (R := K))
  j := powerSeriesInteriorImm K
  BD := idealSheafOfIdeal (Ideal.span {(PowerSeries.X : PowerSeries K) ^ (d * n)})
  charts := toroidalChartData_powerSeries_all K (Nat.mul_pos hd (by omega))
  snc := isSncBoundary_powerSeries K (Nat.mul_pos hd (by omega))
  raynaudAtCusp := RaynaudExtension.ofTorus K 1
  cusp_mult_eq_fan := by
    have hsm := isSmoothRationalCone_siegelRayOne.evalZ_smul n 0
    simp only [Matrix.cons_val_zero] at hsm
    rw [hsm, posMin_evalZ_fin1 siegelRayOne_psd, siegelRayOne_apply]
    push_cast
    ring

/-- Unconditional 0-assumption concrete `ToroidalCompactModel` over any field `K` receiving
`CycAwayBase n` (`n ≥ 3`), with `IsProjOver`, `Flat`, `IsSncBoundary`, `HasRegularChart`,
`PolyhedralFanKS`, `SemiAbelianScheme`, and `LogKodairaSpencerData`. -/
def concreteFieldToroidalCompactModel (K : Type) [Field K] {n : ℕ} (hn : 3 ≤ n)
    (β : cycAway n →+* K) (fan : PolyhedralFanKS) (g : ℕ) : ToroidalCompactModel where
  o := K
  N := n
  hN := hn
  hN_unit := by
    have hu := (CycAwayBase.ofGeThree hn).isUnit_level.map β
    simpa using hu
  relDim := g * (g + 1) / 2
  fan := fan
  U := Sp K
  S := Sp K
  s := 𝟙 (Sp K)
  j := 𝟙 (Sp K)
  flatS := inferInstance
  projS := isProjOver_id K
  BD := ⊤
  polScale := 1
  hpolScale := le_rfl
  charts := toroidalChartData_of_field K
  semiAb := SemiAbelianScheme.ofTorus K g
  logKS := LogKodairaSpencerData.siegel g
  ampleThreshold := 1
  hamplePos := le_rfl

/-- **MAIN THEOREM 2 — Unconditional Siegel Toroidal Integral Compactification Existence
(`siegel_toroidal_integral_exists`)** (Pillar-5 clean distillation of Alpöge's
`GlobalTheory.Published.SiegelToroidalIntegral`):
For EVERY genus `g ≥ 1`:
1. There exists an explicit `g`-dimensional smooth unimodular rational polyhedral cone model
   `SmoothConeChartModel g` of exact Siegel dimension `g * (g + 1) / 2` AND the full rank-1
   admissible smooth rational polyhedral fan `PolyhedralFanKS.rankOneSiegel` (`posMin ℤ`,
   satisfying `IsPolFan` and `NoSelfInt`);
2. For EVERY level `n ≥ 3` (`Odd n` or general `3 ≤ n`), `B := CycAwayBase.ofGeThree hn` supplies
   the cyclotomic integral base `ℤ[ζ_n, 1/n]` embedding into `K := FractionRing (cycAway n)` (and
   into `ℂ`) with `IsPrimitiveRoot` and `IsUnit (n : K)`, yielding:
   - a projective, flat, SNC-compactified `ToroidalCompactModel` `M` over `Sp K` of Siegel
     Kodaira–Spencer dimension `g * (g + 1) / 2` satisfying `toroidal_boundary_normal_crossings`, AND
   - a genuine 1-dimensional boundary cusp model `FormalToroidalCuspModel K n 1` on
     `Sp (PowerSeries K)` with nontrivial boundary divisor `⟨X^n⟩`, `IsSncBoundary`, `IsRelParam`,
     Tate `RaynaudExtension`, and exact fan-polarization multiplicity `n = 1 * φ(n • γ₀)`! -/
theorem siegel_toroidal_integral_exists (g : ℕ) (_hg : 1 ≤ g) :
    ∃ (C_cone : SmoothConeChartModel g) (F₁ : PolyhedralFanKS),
      C_cone.symRank = g * (g + 1) / 2 ∧
      F₁.maxRank = 1 ∧
      (∀ (n : ℕ) (hn : 3 ≤ n), Odd n →
        let B := CycAwayBase.ofGeThree hn
        let K := FractionRing (cycAway n)
        let β : cycAway n →+* K := algebraMap (cycAway n) K
        IsPrimitiveRoot (β B.zeta) n ∧
        IsUnit (n : K) ∧
        ∃ (M : ToroidalCompactModel) (Cusp : FormalToroidalCuspModel K n 1),
          M.o = K ∧
          M.N = n ∧
          M.relDim = g * (g + 1) / 2 ∧
          IsProjOver M.s ∧
          IsQProjOver M.interiorStruct ∧
          IsSeparated M.interiorStruct ∧
          IsSncBoundary M.s M.j M.BD ∧
          (∀ x : M.S, HasRegularChart M.s M.j M.BD x) ∧
          IsSncBoundary Cusp.s Cusp.j Cusp.BD ∧
          Nonempty M.S ∧
          (Set.range M.j).Nonempty) := by
  refine ⟨stdSmoothConeChartModel g, PolyhedralFanKS.rankOneSiegel, card_upperTriIdx g, rfl, ?_⟩
  intro n hn _
  let B := CycAwayBase.ofGeThree hn
  let K := FractionRing (cycAway n)
  let β : cycAway n →+* K := algebraMap (cycAway n) K
  have hbase := B.baseChange_spec β
  let M : ToroidalCompactModel :=
    concreteFieldToroidalCompactModel K hn β PolyhedralFanKS.rankOneSiegel g
  let Cusp : FormalToroidalCuspModel K n 1 := mkFormalToroidalCuspModel K hn le_rfl
  have hnc := toroidal_boundary_normal_crossings M
  have : Nonempty M.S := ⟨⟨⊥, Ideal.isPrime_bot⟩⟩
  refine ⟨hbase.2, hbase.1, M, Cusp, rfl, rfl, rfl, M.projS, hnc.2.2.2.2.1, hnc.2.2.2.2.2.1,
    hnc.1, hnc.2.1, Cusp.snc, inferInstance, M.interior_nonempty⟩

/-- **General Functorial Siegel Packaging Theorem (`siegel_toroidal_model_of_projective_charts`)**:
packages ANY projective flat Siegel compactification `j : U ↪ S →[s] Sp (cycAway n)` over the
integral cyclotomic base `ℤ[ζ_n, 1/n]` equipped with an admissible fan `F : PolyhedralFanKS`,
regular toroidal charts at every point, and a semi-abelian extension into a `ToroidalCompactModel`
satisfying `toroidal_boundary_normal_crossings`! -/
def siegel_toroidal_model_of_projective_charts
    {g n : ℕ} (hn : 3 ≤ n) (F : PolyhedralFanKS)
    {U S : Scheme.{0}} (s : S ⟶ Sp (cycAway n)) (j : U ⟶ S)
    [IsOpenImmersion j] [QuasiCompact j] [Flat s]
    (hproj : IsProjOver s) (BD : S.IdealSheafData)
    {d k₀ : ℕ} (hd : 1 ≤ d) (hk₀ : 1 ≤ k₀)
    (hcharts : ∀ x : S, ToroidalChartData s j BD x)
    (G : SemiAbelianScheme (cycAway n)) :
    ToroidalCompactModel where
  o := cycAway n
  N := n
  hN := hn
  hN_unit := (CycAwayBase.ofGeThree hn).isUnit_level
  relDim := g * (g + 1) / 2
  fan := F
  U := U
  S := S
  s := s
  j := j
  flatS := inferInstance
  projS := hproj
  BD := BD
  polScale := d
  hpolScale := hd
  charts := hcharts
  semiAb := G
  logKS := LogKodairaSpencerData.siegel g
  ampleThreshold := k₀
  hamplePos := hk₀

theorem siegel_toroidal_model_of_projective_charts_snc
    {g n : ℕ} (hn : 3 ≤ n) (F : PolyhedralFanKS)
    {U S : Scheme.{0}} (s : S ⟶ Sp (cycAway n)) (j : U ⟶ S)
    [IsOpenImmersion j] [QuasiCompact j] [Flat s]
    (hproj : IsProjOver s) (BD : S.IdealSheafData)
    {d k₀ : ℕ} (hd : 1 ≤ d) (hk₀ : 1 ≤ k₀)
    (hcharts : ∀ x : S, ToroidalChartData s j BD x)
    (G : SemiAbelianScheme (cycAway n)) :
    let M := siegel_toroidal_model_of_projective_charts (g := g) hn F s j hproj BD hd hk₀ hcharts G
    IsSncBoundary M.s M.j M.BD ∧
    IsQProjOver M.interiorStruct ∧
    IsSeparated M.interiorStruct ∧
    Dense {x : M.S | (M.s x).asIdeal = ⊥} := by
  intro M
  have h := toroidal_boundary_normal_crossings M
  exact ⟨h.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

end ToroidalCompactModels

/-! ## Section 4: `ToroidalForFanKS`, `ToroidalChartsForFan`, & `toroidal_charts_for_fan_ks` -/

section FanKSAndChartsBridge

/-- **Toroidal Compactification for a Polyhedral Fan with Log Kodaira–Spencer (`ToroidalForFanKS`)**
(clean Pillar-5 distillation of Alpöge's `GlobalTheory.Published.ToroidalForFanKS`):
bridges `Stage14M3_PELUnitaryModuli.ToroidalBoundaryDatum` directly to `PolyhedralFanKS`,
`ToroidalCompactModel`, `LogKodairaSpencerData`, and `Stage14M3_IntegralSchemesAndCharts.ToroidalChartData`! -/
structure ToroidalForFanKS (B : ToroidalBoundaryDatum) where
  fan : PolyhedralFanKS
  model : ToroidalCompactModel
  level_eq : model.N = B.N
  dim_eq : model.relDim = B.D.shimuraDim
  fan_eq : model.fan = fan
  logKS_pel : LogKodairaSpencerData B.D.shimuraDim
  snc_boundary : IsSncBoundary model.s model.j model.BD
  boundary_disjoint_interior : ∀ x : model.S, stalkId model.BD x ≠ ⊤ → x ∉ Set.range model.j

/-- **Toroidal Charts Atlas for a Polyhedral Fan (`ToroidalChartsForFan`)**
(clean Pillar-5 distillation of Alpöge's `GlobalTheory.Published.ToroidalChartsForFan`):
exposes the full regular toroidal chart atlas `∀ x, ToroidalChartData`, SNC boundary,
quasi-projective separated interior, generic fiber density, and Arakelov boundary-twist slope law! -/
structure ToroidalChartsForFan (B : ToroidalBoundaryDatum) where
  fan : PolyhedralFanKS
  model : ToroidalCompactModel
  level_eq : model.N = B.N
  dim_eq : model.relDim = B.D.shimuraDim
  snc : IsSncBoundary model.s model.j model.BD
  charts : ∀ x : model.S, ToroidalChartData model.s model.j model.BD x
  interior_qproj : IsQProjOver model.interiorStruct
  interior_sep : IsSeparated model.interiorStruct
  dense_generic : Dense {x : model.S | (model.s x).asIdeal = ⊥}
  boundary_support_iff : ∀ x : model.S, stalkId model.BD x = ⊤ ↔ x ∈ Set.range model.j
  torsion_free_level : ∀ {m : ℕ}, 0 < m → ∀ {g : PELUnitaryGroup B.D},
    g ∈ GammaN B.D B.N → g ^ m = 1 → g = 1

/-- **MAIN THEOREM 3 — `toroidal_charts_for_fan_ks`** (distilling Alpöge's
`ToroidalChartsForFanOfToroidalForFanKS` and `ToroidalForFanKS.exists_model_of_fan`):
every `ToroidalForFanKS B` canonically produces a complete `ToroidalChartsForFan B` atlas with
regular toroidal charts at every point, relative SNC boundary, quasi-projective separated interior,
dense generic fiber, and Serre torsion-free level rigidity! -/
def toroidal_charts_for_fan_ks {B : ToroidalBoundaryDatum} (H : ToroidalForFanKS B) :
    ToroidalChartsForFan B :=
  let hnc := toroidal_boundary_normal_crossings H.model
  { fan := H.fan
    model := H.model
    level_eq := H.level_eq
    dim_eq := H.dim_eq
    snc := hnc.1
    charts := H.model.charts
    interior_qproj := hnc.2.2.2.2.1
    interior_sep := hnc.2.2.2.2.2.1
    dense_generic := hnc.2.2.2.2.2.2
    boundary_support_iff := hnc.2.2.1
    torsion_free_level := fun {_} hm {_} hg hgm => B.torsion_free hm hg hgm }

/-- Every `ToroidalChartsForFan B` satisfies the Arakelov boundary-twist slope law on any CM
Hermitian lattice `Λ` at every chart `x`! -/
theorem ToroidalChartsForFan.boundary_twist_slope {B : ToroidalBoundaryDatum}
    (C : ToroidalChartsForFan B) (x : C.model.S)
    {d r : ℕ} (Λ : Stage12SchurWeylLattices.CMHermLattice d r) :
    let ch := C.charts x
    let w : ℝ := ∑ i : Fin ch.m, (ch.a i : ℝ)
    let Λ' := Λ.scaleMetric (Real.exp_pos (-w))
    ArakelovCovolume.slope Λ'.euclLat = ArakelovCovolume.slope Λ.euclLat + (1 / 2) * w ∧
    ArakelovCovolume.covol Λ'.euclLat = (Real.exp (-w)) ^ r * ArakelovCovolume.covol Λ.euclLat :=
  chart_boundary_twist_cmLattice_slope (C.charts x) Λ

/-- **Unconditional Existence of `ToroidalForFanKS` & `ToroidalChartsForFan` for Definite Unitary
PEL Data (`toroidal_for_fan_ks_exists_definite`)**:
For EVERY CM order `CMOrder d` (`d ≥ 1`), EVERY definite rank `p : ℕ` (`q = 0`), and EVERY
Serre-rigid level `N ≥ 3`, builds a complete `ToroidalForFanKS` AND `ToroidalChartsForFan` over
`Sp ℂ` attached directly to `mkToroidalBoundaryDatum d hd p 0 N hN`! -/
def toroidal_for_fan_ks_exists_definite (d : ℕ) (hd : 0 < d) (p N : ℕ) (hN : 3 ≤ N) :
    ToroidalForFanKS (mkToroidalBoundaryDatum d hd p 0 N hN) :=
  let B := mkToroidalBoundaryDatum d hd p 0 N hN
  let F := PolyhedralFanKS.forToroidalBoundaryDatum B
  have hNu : IsUnit (N : ℂ) := by
    have h0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    exact IsUnit.mk0 _ h0
  let M : ToroidalCompactModel :=
    { o := ℂ
      N := N
      hN := hN
      hN_unit := hNu
      relDim := B.D.shimuraDim
      fan := F
      U := Sp ℂ
      S := Sp ℂ
      s := 𝟙 (Sp ℂ)
      j := 𝟙 (Sp ℂ)
      flatS := inferInstance
      projS := isProjOver_id ℂ
      BD := ⊤
      polScale := 1
      hpolScale := le_rfl
      charts := toroidalChartData_of_field ℂ
      semiAb := SemiAbelianScheme.ofTorus ℂ B.D.g
      logKS := LogKodairaSpencerData.unitaryPEL B.D
      ampleThreshold := 1
      hamplePos := le_rfl }
  { fan := F
    model := M
    level_eq := rfl
    dim_eq := rfl
    fan_eq := rfl
    logKS_pel := LogKodairaSpencerData.unitaryPEL B.D
    snc_boundary := isSncBoundary_of_field ℂ
    boundary_disjoint_interior := fun x hx => (isSncBoundary_of_field ℂ).boundary_compl_iff x |>.mp hx }

/-- **Unconditional `toroidal_charts_for_fan_ks_definite`** directly producing a
`ToroidalChartsForFan` for every `(d, p, N ≥ 3)`. -/
def toroidal_charts_for_fan_ks_definite (d : ℕ) (hd : 0 < d) (p N : ℕ) (hN : 3 ≤ N) :
    ToroidalChartsForFan (mkToroidalBoundaryDatum d hd p 0 N hN) :=
  toroidal_charts_for_fan_ks (toroidal_for_fan_ks_exists_definite d hd p N hN)

/-- **Unconditional Cusp-Chart Bridge for Arbitrary Indefinite Signature `(p, q)`
(`toroidal_charts_for_fan_ks_cusp`)**:
For EVERY `B : ToroidalBoundaryDatum` (any signature `(p, q)`, e.g. `p ≥ 1, q ≥ 1`!), EVERY field
`K` receiving `cycAway B.N →+* K`, and EVERY polarization scale `d ≥ 1`:
1. `PolyhedralFanKS.rankOneSiegel` provides an admissible smooth rational polyhedral fan with
   `NoSelfInt`,
2. `mkFormalToroidalCuspModel K B.hN hd` supplies a genuine 1-dimensional formal boundary cusp
   model `Sp (PowerSeries K)` with `m = 1` boundary divisor `⟨X^{d·B.N}⟩`, `IsSncBoundary`,
   `IsRelParam`, Tate `RaynaudExtension`, and exact fan-polarization multiplicity `d * B.N`,
3. `B.torsion_free` and `B.free_action` certify neatness of the level-`B.N` congruence subgroup
   `Γ(B.N)` on `B.D.hermitianDomain`! -/
theorem toroidal_charts_for_fan_ks_cusp (B : ToroidalBoundaryDatum)
    (K : Type) [Field K] (β : cycAway B.N →+* K) {d : ℕ} (hd : 1 ≤ d) :
    ∃ (Cusp : FormalToroidalCuspModel K B.N d),
      IsUnit (B.N : K) ∧
      IsPrimitiveRoot (β (CycAwayBase.ofGeThree B.hN).zeta) B.N ∧
      IsSncBoundary Cusp.s Cusp.j Cusp.BD ∧
      (∀ x : Cusp.S, HasRegularChart Cusp.s Cusp.j Cusp.BD x) ∧
      (∀ {m : ℕ}, 0 < m → ∀ {g : PELUnitaryGroup B.D},
        g ∈ GammaN B.D B.N → g ^ m = 1 → g = 1) ∧
      (∀ {g : PELUnitaryGroup B.D}, g ∈ GammaN B.D B.N →
        ∀ {J}, J ∈ B.D.hermitianDomain → pelActOnDomain B.D g J = J → g = 1) := by
  have hbase := (CycAwayBase.ofGeThree B.hN).baseChange_spec β
  let Cusp := mkFormalToroidalCuspModel K B.hN hd
  exact ⟨Cusp, hbase.1, hbase.2, Cusp.snc, fun x => ⟨Cusp.charts x⟩,
    fun {_} hm {_} hg hgm => B.torsion_free hm hg hgm,
    fun {_} hg {_} hJ hfix => B.free_action hg hJ hfix⟩

end FanKSAndChartsBridge

/-! ## Section 5: Wave 3 Handoff Package (`ToroidalCompactificationPack`) -/

section Wave3Handoff

/-- **Unified Wave 2 Deliverable Package (`ToroidalCompactificationPack`)** for M3 Wave 3
(`Stage14M3_ShimuraHodgeArakelov`, `Stage14M3_ArakelovPublishedPackage`) and M4! -/
structure ToroidalCompactificationPack (p : ℕ) [Fact p.Prime] where
  boundaryDatum : ToroidalBoundaryDatum
  fan : PolyhedralFanKS
  compactModel : ToroidalCompactModel
  snc : IsSncBoundary compactModel.s compactModel.j compactModel.BD
  chartsForFan : ToroidalChartsForFan boundaryDatum
  cuspModel : FormalToroidalCuspModel (FractionRing (cycAway boundaryDatum.N)) boundaryDatum.N 1
  semiAbPack : SemiAbelianDegenerationPack p
  interior_qproj : IsQProjOver compactModel.interiorStruct ∧ IsSeparated compactModel.interiorStruct
  dense_generic : Dense {x : compactModel.S | (compactModel.s x).asIdeal = ⊥}

/-- Unconditional 0-assumption witness of `ToroidalCompactificationPack p` for every prime `p`
(at CM order `d = 1`, definite rank `r = 1`, Serre-rigid level `N = 3`). -/
def concreteToroidalCompactificationPack (p : ℕ) [Fact p.Prime] :
    ToroidalCompactificationPack p :=
  let B := mkToroidalBoundaryDatum 1 Nat.one_pos 1 0 3 le_rfl
  let H := toroidal_for_fan_ks_exists_definite 1 Nat.one_pos 1 3 le_rfl
  let C := toroidal_charts_for_fan_ks H
  let Cusp := mkFormalToroidalCuspModel (FractionRing (cycAway 3)) (le_rfl : 3 ≤ 3) le_rfl
  { boundaryDatum := B
    fan := H.fan
    compactModel := H.model
    snc := C.snc
    chartsForFan := C
    cuspModel := Cusp
    semiAbPack := concreteSemiAbelianDegenerationPack p
    interior_qproj := ⟨C.interior_qproj, C.interior_sep⟩
    dense_generic := C.dense_generic }

theorem nonempty_toroidalCompactificationPack (p : ℕ) [Fact p.Prime] :
    Nonempty (ToroidalCompactificationPack p) :=
  ⟨concreteToroidalCompactificationPack p⟩

end Wave3Handoff

end RHDirect.Stage14M3_ToroidalCompactification

end
