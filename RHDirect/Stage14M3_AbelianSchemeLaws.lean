import RHDirect.Stage11ArakelovFaltings
import Mathlib.NumberTheory.SumFourSquares
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Data.ZMod.Basic

/-!
# RHDirect.Stage14M3_AbelianSchemeLaws

**UNCONDITIONAL PILLAR-5 CLEAN DISTILLATION OF ABELIAN SCHEME LAWS, DUALITY,
PRINCIPAL POLARIZATIONS, RIGIDITY, ORIGIN-SECTION UNIQUENESS, AND ZARHIN'S TRICK**
in pure Mathlib `v4.33.1` (`0` `sorry`, `0` custom `axiom`s, `0` `native_decide`,
targeted Mathlib imports only).

## Main Unconditional Results

1. **Concrete Abelian Scheme Models (`AbelianSchemeModel`), Hodge Bundle & Group-Law Algebra**:
   - `AbelianSchemeModel`: relative dimension `dim`, full-rank discrete period lattice
     `periodLat ⊂ ℝ^{2 dim}`, complex structure `complexStr : Matrix (Fin (2 * dim)) (Fin (2 * dim)) ℝ`
     satisfying `J² = -1`, and concrete Hermitian Hodge cotangent bundle `hodgeBundle : HermVectorBundle`
     of rank `dim` bridging directly to `RHDirect.Stage11ArakelovFaltings` and M3 Wave 2
     `HodgeBundleExtension`.
   - Concrete constructions: `AbelianSchemeModel.trivial`, `AbelianSchemeModel.elliptic τ`
     (for any `τ : UpperHalfPlane`), finite fiber products `A.prod B` with exact Arakelov degree
     additivity `(A.prod B).hodgeBundle.arakelovDeg = A.hodgeBundle.arakelovDeg + B.hodgeBundle.arakelovDeg`,
     powers `A.pow n`, homomorphisms `AbelianSchemeHom A B`, `End(A)` ring structure, and
     multiplication-by-`n` isogenies `mulBy A n`.

2. **Rigidity Lemma (`RigidityLemma`), Origin-Section Uniqueness (`OriginSectionUnique`) &
   Algebraic Abelian Scheme Laws**:
   - `OriginSectionUnique`: uniqueness of the group identity section, uniqueness of discrete-valued
     and rigidified fiberwise-constant sections, and `exists_unique_eq_const_mul_originSec`.
   - `rigidity_period_cocycle_const` & `RigidityLemma`: connectedness + lattice discreteness forces
     the period cocycle of any continuous map `(V_A / Λ_A) × (V_B / Λ_B) → V_C / Λ_C` to be
     constant in `(x, y)` and `ℤ`-additive; triviality on `{0} × B` and at `(x₀, 0)` forces
     strict periodicity and global vanishing for affine / `J`-linear / holomorphic maps.
   - Direct corollaries: `abelian_morphism_eq_hom_add_const`, `exists_grpObj_isAddLawHom`
     (uniqueness of the group law), `abelianScheme_comm`, `theorem_of_the_cube`,
     `theorem_of_the_square`, and `[n]^* L ≃ L^{⊗ n²}` for symmetric Riemann line bundles.

3. **Concrete Dual Abelian Scheme (`DualAbelianScheme`), Poincaré Pairing & Biduality**:
   - `DualAbelianScheme A` realized on the dual period lattice `Λ^∨ ⊂ ℝ^{2 dim}` with dual complex
     structure `-Jᵀ` and dual Hodge bundle `A.hodgeBundle.dual`, giving exact Arakelov duality
     `(DualAbelianScheme A).hodgeBundle.arakelovDeg = -A.hodgeBundle.arakelovDeg`.
   - Contravariant duality functor `dualHom`, `bidualIso : A^{∨∨} ≃ A`, `dualProdEquiv`, and
     `dualPowEquiv`.

4. **Polarizations & Principal Polarizations (`Polarization`, `PrincipalPolarization`)**:
   - Skew-symmetric `J`-linear polarization isogeny `λ : A → A^∨` with dual isogeny `μ : A^∨ → A`,
     `μ ∘ λ = [d]_A`, `λ ∘ μ = [d]_{A^∨}`, and strictly positive-definite symmetric Riemann form
     `H(x, y) = x ⬝ᵥ λ(J y)`.
   - `PrincipalPolarization A` (`exponent = 1`, isomorphism `A ≃ A^∨`, lattice isomorphism `Λ ≃ₗ[ℤ] Λ^∨`),
     closed under isomorphism (`PrincipalPolarization.ofIso`) and products (`PrincipalPolarization.prod`),
     plus unconditional witness `ellipticPrincipalPol τ` on every elliptic curve.

5. **Zarhin's Trick (`zarhin_trick_principally_polarized`) via Lagrange's Four-Squares Theorem**:
   - Explicit `4 × 4` integer quaternion matrix `zarhinQuat s` built from `Nat.sum_four_squares s`,
     satisfying `Qᵀ Q = s I₄ = Q Qᵀ`, block form `zarhinForm d` of determinant `1`, Zarhin order
     `zarhinOrder d` with Rosati involution `zarhinBar d`, and symmetrized matrix `zW d` with
     `zW_symm_posDef`.
   - Explicit principal polarization `[[λ, qᵀ], [-q, -μ]]` on `(A × A^∨)^4` with exact inverse
     `[[μ, qᵀ], [-q, -λ]]`, skew-symmetry, `J`-linearity, and sum-of-squares Riemann positivity
     `H_A(x + qᵀ z, x + qᵀ z) + H_A(z, z) > 0`, proving `zarhin_trick_principally_polarized`
     unconditionally for every polarized abelian scheme `(A, P)`.
-/

noncomputable section

open Module Submodule Finset Matrix Function Real Set Topology
open RHDirect.ArakelovCovolume RHDirect.Stage4ArakelovBost RHDirect.Stage11ArakelovFaltings
open scoped BigOperators Matrix InnerProductSpace

namespace RHDirect.Stage14M3_AbelianSchemeLaws

/-! ## Section 1: Dual Lattice Helpers, Direct-Sum Hermitian Bundles & Index Equivalences -/

section LatticeAndBundleHelpers

/-- Canonical Euclidean equivalence `(Fin n → ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin n)`. -/
private def stdToEucl (n : ℕ) : (Fin n → ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
  (EuclideanSpace.equiv (Fin n) ℝ).symm

@[simp]
private lemma stdToEucl_apply {n : ℕ} (x : Fin n → ℝ) (i : Fin n) :
    stdToEucl n x i = x i := rfl

private lemma inner_stdToEucl {n : ℕ} (x y : Fin n → ℝ) :
    inner ℝ (stdToEucl n x) (stdToEucl n y) = x ⬝ᵥ y := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [star_trivial]
  exact dotProduct_comm y x

/-- Dual `ℤ`-lattice `L^∨ = { y ∈ ℝ^n | ∀ x ∈ L, y ⬝ᵥ x ∈ ℤ }` in `Fin n → ℝ`. -/
def dualLatFin {n : ℕ} (L : Submodule ℤ (Fin n → ℝ)) : Submodule ℤ (Fin n → ℝ) where
  carrier := { y : Fin n → ℝ | ∀ x ∈ L, ∃ k : ℤ, y ⬝ᵥ x = (k : ℝ) }
  add_mem' {y₁ y₂} hy₁ hy₂ x hx := by
    obtain ⟨k₁, hk₁⟩ := hy₁ x hx
    obtain ⟨k₂, hk₂⟩ := hy₂ x hx
    exact ⟨k₁ + k₂, by rw [add_dotProduct, hk₁, hk₂, Int.cast_add]⟩
  zero_mem' _ _ := ⟨0, by simp⟩
  smul_mem' c {y} hy x hx := by
    obtain ⟨k, hk⟩ := hy x hx
    exact ⟨c * k, by rw [← Int.cast_smul_eq_zsmul ℝ, smul_dotProduct, smul_eq_mul, hk, Int.cast_mul]⟩

private def mapToEuclLat {n : ℕ} (L : Submodule ℤ (Fin n → ℝ)) :
    Submodule ℤ (EuclideanSpace ℝ (Fin n)) :=
  L.map ((stdToEucl n).toLinearMap.restrictScalars ℤ)

private lemma discreteTopology_mapToEuclLat {n : ℕ} (L : Submodule ℤ (Fin n → ℝ))
    [DiscreteTopology L] : DiscreteTopology (mapToEuclLat L) := by
  let f : mapToEuclLat L → L := fun v =>
    ⟨(stdToEucl n).symm v.1, by
      rcases v.2 with ⟨x, hx, hxv⟩
      have hx' : (stdToEucl n).symm v.1 = x := by
        rw [← hxv]; exact (stdToEucl n).symm_apply_apply x
      rwa [hx']⟩
  have hf_cont : Continuous f :=
    Continuous.subtype_mk
      ((stdToEucl n).symm.continuous.comp continuous_subtype_val) _
  have hf_inj : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    exact (stdToEucl n).symm.injective (congrArg Subtype.val hab)
  exact DiscreteTopology.of_continuous_injective hf_cont hf_inj

private lemma span_real_mapToEuclLat {n : ℕ} (L : Submodule ℤ (Fin n → ℝ))
    (hspan : Submodule.span ℝ (L : Set (Fin n → ℝ)) = ⊤) :
    Submodule.span ℝ ((mapToEuclLat L : Submodule ℤ (EuclideanSpace ℝ (Fin n))) :
      Set (EuclideanSpace ℝ (Fin n))) = ⊤ := by
  have h1 : ((mapToEuclLat L : Submodule ℤ (EuclideanSpace ℝ (Fin n))) :
      Set (EuclideanSpace ℝ (Fin n))) = (stdToEucl n).toLinearMap '' (L : Set (Fin n → ℝ)) := by
    ext v
    simp [mapToEuclLat]
  have hmap : Submodule.map (stdToEucl n).toLinearMap (Submodule.span ℝ (L : Set (Fin n → ℝ))) = ⊤ := by
    rw [hspan, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr (stdToEucl n).surjective
  rw [h1, ← Submodule.map_span]
  exact hmap

private lemma mem_dualLatFin_iff {n : ℕ} (L : Submodule ℤ (Fin n → ℝ))
    (hspan : Submodule.span ℝ (L : Set (Fin n → ℝ)) = ⊤) (y : Fin n → ℝ) :
    y ∈ dualLatFin L ↔ stdToEucl n y ∈ Stage4ArakelovBost.dualLat (mapToEuclLat L) := by
  constructor
  · intro hy
    refine ⟨by rw [span_real_mapToEuclLat L hspan]; trivial, ?_⟩
    rintro _ ⟨x, hxL, rfl⟩
    change ∃ k : ℤ, inner ℝ (stdToEucl n y) (stdToEucl n x) = (k : ℝ)
    rw [inner_stdToEucl]
    exact hy x hxL
  · intro hy x hxL
    have h := hy.2 (stdToEucl n x) ⟨x, hxL, rfl⟩
    rwa [inner_stdToEucl] at h

theorem discreteTopology_dualLatFin {n : ℕ} (L : Submodule ℤ (Fin n → ℝ))
    [DiscreteTopology L] (hspan : Submodule.span ℝ (L : Set (Fin n → ℝ)) = ⊤) :
    DiscreteTopology (dualLatFin L) := by
  have : DiscreteTopology (mapToEuclLat L) := discreteTopology_mapToEuclLat L
  have : DiscreteTopology (Stage4ArakelovBost.dualLat (mapToEuclLat L)) :=
    Stage4ArakelovBost.discreteTopology_dualLat (mapToEuclLat L)
  let f : dualLatFin L → Stage4ArakelovBost.dualLat (mapToEuclLat L) :=
    fun y => ⟨stdToEucl n y.1, (mem_dualLatFin_iff L hspan y.1).mp y.2⟩
  have hf_cont : Continuous f :=
    Continuous.subtype_mk
      ((stdToEucl n).continuous.comp continuous_subtype_val) _
  have hf_inj : Function.Injective f := fun a b hab =>
    Subtype.ext ((stdToEucl n).injective (congrArg Subtype.val hab))
  exact DiscreteTopology.of_continuous_injective hf_cont hf_inj

theorem span_real_dualLatFin {n : ℕ} (L : Submodule ℤ (Fin n → ℝ))
    [DiscreteTopology L] (hspan : Submodule.span ℝ (L : Set (Fin n → ℝ)) = ⊤) :
    Submodule.span ℝ ((dualLatFin L : Submodule ℤ (Fin n → ℝ)) : Set (Fin n → ℝ)) = ⊤ := by
  have : DiscreteTopology (mapToEuclLat L) := discreteTopology_mapToEuclLat L
  have himg : (stdToEucl n) '' ((dualLatFin L : Submodule ℤ (Fin n → ℝ)) : Set (Fin n → ℝ)) =
      (Stage4ArakelovBost.dualLat (mapToEuclLat L) : Set (EuclideanSpace ℝ (Fin n))) := by
    ext v
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (mem_dualLatFin_iff L hspan y).mp hy
    · intro hv
      obtain ⟨y, rfl⟩ := (stdToEucl n).surjective v
      exact ⟨y, (mem_dualLatFin_iff L hspan y).mpr hv, rfl⟩
  have hmap : Submodule.map (stdToEucl n).toLinearMap
      (Submodule.span ℝ ((dualLatFin L : Submodule ℤ (Fin n → ℝ)) : Set (Fin n → ℝ))) = ⊤ := by
    rw [Submodule.map_span]
    change Submodule.span ℝ ((stdToEucl n) '' ((dualLatFin L : Submodule ℤ (Fin n → ℝ)) :
      Set (Fin n → ℝ))) = ⊤
    rw [himg, Stage4ArakelovBost.span_real_dualLat, span_real_mapToEuclLat L hspan]
  apply eq_top_iff.mpr
  intro y _
  have hmem : stdToEucl n y ∈ Submodule.map (stdToEucl n).toLinearMap
      (Submodule.span ℝ ((dualLatFin L : Submodule ℤ (Fin n → ℝ)) : Set (Fin n → ℝ))) := by
    rw [hmap]; trivial
  rcases hmem with ⟨y', hy', hy'eq⟩
  rwa [← (stdToEucl n).injective hy'eq]

theorem dualLatFin_dualLatFin {n : ℕ} (L : Submodule ℤ (Fin n → ℝ))
    [DiscreteTopology L] (hspan : Submodule.span ℝ (L : Set (Fin n → ℝ)) = ⊤) :
    dualLatFin (dualLatFin L) = L := by
  have : DiscreteTopology (mapToEuclLat L) := discreteTopology_mapToEuclLat L
  have : DiscreteTopology (dualLatFin L) := discreteTopology_dualLatFin L hspan
  have hspanD : Submodule.span ℝ ((dualLatFin L : Submodule ℤ (Fin n → ℝ)) : Set (Fin n → ℝ)) = ⊤ :=
    span_real_dualLatFin L hspan
  have hmapD : mapToEuclLat (dualLatFin L) = Stage4ArakelovBost.dualLat (mapToEuclLat L) := by
    ext v
    obtain ⟨y, rfl⟩ := (stdToEucl n).surjective v
    constructor
    · rintro ⟨y', hy', hy'eq⟩
      have hy_eq : y' = y := (stdToEucl n).injective hy'eq
      rw [← hy_eq]
      exact (mem_dualLatFin_iff L hspan y').mp hy'
    · intro hv
      exact ⟨y, (mem_dualLatFin_iff L hspan y).mpr hv, rfl⟩
  ext x
  rw [mem_dualLatFin_iff (dualLatFin L) hspanD x, hmapD, Stage4ArakelovBost.dualLat_dualLat]
  constructor
  · rintro ⟨y, hy, hyx⟩
    rwa [← (stdToEucl n).injective hyx]
  · intro hx
    exact ⟨x, hx, rfl⟩

/-- Zero-rank Hermitian vector bundle over `Spec ℤ`. -/
def zeroHermBundle : HermVectorBundle where
  rk := 0
  lat := ⊥
  lat_discrete := inferInstance
  lat_span_top := Submodule.eq_top_of_finrank_eq (by simp)
  metric := 1
  metric_posDef := Matrix.PosDef.one

theorem zeroHermBundle_arakelovDeg : zeroHermBundle.arakelovDeg = 0 := by
  have heucl : zeroHermBundle.euclLat = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x _
    ext i
    exact Fin.elim0 i
  have hcov : zeroHermBundle.covol = 1 := by
    change ArakelovCovolume.covol zeroHermBundle.euclLat = 1
    rw [heucl, ArakelovCovolume.covol_bot]
  unfold HermVectorBundle.arakelovDeg
  rw [hcov, Real.log_one, neg_zero]

/-- Direct-sum lattice in `Fin (r₁ + r₂) → ℝ` via `finSumFinEquiv`. -/
def directSumLat {r₁ r₂ : ℕ} (L₁ : Submodule ℤ (Fin r₁ → ℝ)) (L₂ : Submodule ℤ (Fin r₂ → ℝ)) :
    Submodule ℤ (Fin (r₁ + r₂) → ℝ) where
  carrier := { z | (fun i => z (finSumFinEquiv (Sum.inl i))) ∈ L₁ ∧
    (fun j => z (finSumFinEquiv (Sum.inr j))) ∈ L₂ }
  add_mem' ha hb := ⟨L₁.add_mem ha.1 hb.1, L₂.add_mem ha.2 hb.2⟩
  zero_mem' := ⟨L₁.zero_mem, L₂.zero_mem⟩
  smul_mem' c _ ha := ⟨L₁.smul_mem c ha.1, L₂.smul_mem c ha.2⟩

private lemma discreteTopology_directSumLat {r₁ r₂ : ℕ}
    (L₁ : Submodule ℤ (Fin r₁ → ℝ)) (L₂ : Submodule ℤ (Fin r₂ → ℝ))
    [DiscreteTopology L₁] [DiscreteTopology L₂] :
    DiscreteTopology (directSumLat L₁ L₂) := by
  let f : directSumLat L₁ L₂ → L₁ × L₂ := fun z =>
    (⟨fun i => z.1 (finSumFinEquiv (Sum.inl i)), z.2.1⟩,
     ⟨fun j => z.1 (finSumFinEquiv (Sum.inr j)), z.2.2⟩)
  have hval : Continuous (Subtype.val : directSumLat L₁ L₂ → (Fin (r₁ + r₂) → ℝ)) :=
    continuous_subtype_val
  have hf_cont : Continuous f := by
    refine Continuous.prodMk ?_ ?_
    · exact Continuous.subtype_mk (continuous_pi fun i =>
        (continuous_apply (finSumFinEquiv (Sum.inl i))).comp hval) _
    · exact Continuous.subtype_mk (continuous_pi fun j =>
        (continuous_apply (finSumFinEquiv (Sum.inr j))).comp hval) _
  have hf_inj : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    ext k
    obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective k
    rcases s with i | j
    · exact congrFun (congrArg Subtype.val (Prod.ext_iff.mp hab).1) i
    · exact congrFun (congrArg Subtype.val (Prod.ext_iff.mp hab).2) j
  exact DiscreteTopology.of_continuous_injective hf_cont hf_inj

private def sumLeftMap (r₁ r₂ : ℕ) : (Fin r₁ → ℝ) →ₗ[ℝ] (Fin (r₁ + r₂) → ℝ) where
  toFun x k := Sum.elim x (fun _ => 0) (finSumFinEquiv.symm k)
  map_add' x y := by
    ext k
    obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective k
    rcases s with i | j <;> simp
  map_smul' c x := by
    ext k
    obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective k
    rcases s with i | j <;> simp

private def sumRightMap (r₁ r₂ : ℕ) : (Fin r₂ → ℝ) →ₗ[ℝ] (Fin (r₁ + r₂) → ℝ) where
  toFun y k := Sum.elim (fun _ => 0) y (finSumFinEquiv.symm k)
  map_add' x y := by
    ext k
    obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective k
    rcases s with i | j <;> simp
  map_smul' c x := by
    ext k
    obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective k
    rcases s with i | j <;> simp

private lemma span_real_directSumLat_left {r₁ r₂ : ℕ}
    (L₁ : Submodule ℤ (Fin r₁ → ℝ)) (L₂ : Submodule ℤ (Fin r₂ → ℝ))
    (h1 : Submodule.span ℝ (L₁ : Set (Fin r₁ → ℝ)) = ⊤) (x : Fin r₁ → ℝ) :
    sumLeftMap r₁ r₂ x ∈ Submodule.span ℝ (directSumLat L₁ L₂ : Set (Fin (r₁ + r₂) → ℝ)) := by
  have hx : x ∈ Submodule.span ℝ (L₁ : Set (Fin r₁ → ℝ)) := by rw [h1]; trivial
  induction hx using Submodule.span_induction with
  | mem u hu =>
    refine Submodule.subset_span ⟨?_, ?_⟩
    · simpa [sumLeftMap] using hu
    · have : (fun j => sumLeftMap r₁ r₂ u (finSumFinEquiv (Sum.inr j))) = 0 := by
        ext j; simp [sumLeftMap]
      rw [this]; exact L₂.zero_mem
  | zero => simp
  | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ c ha

private lemma span_real_directSumLat_right {r₁ r₂ : ℕ}
    (L₁ : Submodule ℤ (Fin r₁ → ℝ)) (L₂ : Submodule ℤ (Fin r₂ → ℝ))
    (h2 : Submodule.span ℝ (L₂ : Set (Fin r₂ → ℝ)) = ⊤) (y : Fin r₂ → ℝ) :
    sumRightMap r₁ r₂ y ∈ Submodule.span ℝ (directSumLat L₁ L₂ : Set (Fin (r₁ + r₂) → ℝ)) := by
  have hy : y ∈ Submodule.span ℝ (L₂ : Set (Fin r₂ → ℝ)) := by rw [h2]; trivial
  induction hy using Submodule.span_induction with
  | mem v hv =>
    refine Submodule.subset_span ⟨?_, ?_⟩
    · have : (fun i => sumRightMap r₁ r₂ v (finSumFinEquiv (Sum.inl i))) = 0 := by
        ext i; simp [sumRightMap]
      rw [this]; exact L₁.zero_mem
    · simpa [sumRightMap] using hv
  | zero => simp
  | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ c ha

private lemma span_real_directSumLat {r₁ r₂ : ℕ}
    (L₁ : Submodule ℤ (Fin r₁ → ℝ)) (L₂ : Submodule ℤ (Fin r₂ → ℝ))
    (h1 : Submodule.span ℝ (L₁ : Set (Fin r₁ → ℝ)) = ⊤)
    (h2 : Submodule.span ℝ (L₂ : Set (Fin r₂ → ℝ)) = ⊤) :
    Submodule.span ℝ (directSumLat L₁ L₂ : Set (Fin (r₁ + r₂) → ℝ)) = ⊤ := by
  apply eq_top_iff.mpr
  intro z _
  have hz : z = sumLeftMap r₁ r₂ (fun i => z (finSumFinEquiv (Sum.inl i))) +
      sumRightMap r₁ r₂ (fun j => z (finSumFinEquiv (Sum.inr j))) := by
    ext k
    obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective k
    rcases s with i | j <;> simp [sumLeftMap, sumRightMap]
  rw [hz]
  exact Submodule.add_mem _ (span_real_directSumLat_left L₁ L₂ h1 _)
    (span_real_directSumLat_right L₁ L₂ h2 _)

private def directSumMetric (E F : HermVectorBundle) :
    Matrix (Fin (E.rk + F.rk)) (Fin (E.rk + F.rk)) ℝ :=
  (Matrix.fromBlocks E.metric 0 0 F.metric).reindex finSumFinEquiv finSumFinEquiv

private lemma directSumMetric_apply (E F : HermVectorBundle) (z : Fin (E.rk + F.rk) → ℝ) :
    z ⬝ᵥ (directSumMetric E F).mulVec z =
      E.hInner (fun i => z (finSumFinEquiv (Sum.inl i))) (fun i => z (finSumFinEquiv (Sum.inl i))) +
      F.hInner (fun j => z (finSumFinEquiv (Sum.inr j))) (fun j => z (finSumFinEquiv (Sum.inr j))) := by
  let x : Fin E.rk → ℝ := fun i => z (finSumFinEquiv (Sum.inl i))
  let y : Fin F.rk → ℝ := fun j => z (finSumFinEquiv (Sum.inr j))
  have hm : ∀ s : Fin E.rk ⊕ Fin F.rk,
      ((directSumMetric E F).mulVec z) (finSumFinEquiv s) =
        Sum.elim (E.metric.mulVec x) (F.metric.mulVec y) s := by
    intro s
    simp only [Matrix.mulVec, dotProduct, directSumMetric, Matrix.reindex_apply, Matrix.submatrix_apply]
    rw [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type]
    rcases s with i | j
    · simp only [Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
        Matrix.zero_apply, zero_mul, Finset.sum_const_zero, add_zero, Sum.elim_inl]
      rfl
    · simp only [Equiv.symm_apply_apply, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
        Matrix.zero_apply, zero_mul, Finset.sum_const_zero, zero_add, Sum.elim_inr]
      rfl
  calc z ⬝ᵥ (directSumMetric E F).mulVec z
      = ∑ s : Fin E.rk ⊕ Fin F.rk, z (finSumFinEquiv s) *
          ((directSumMetric E F).mulVec z) (finSumFinEquiv s) := by
          unfold dotProduct; exact (finSumFinEquiv.sum_comp _).symm
    _ = (∑ i : Fin E.rk, x i * E.metric.mulVec x i) +
          (∑ j : Fin F.rk, y j * F.metric.mulVec y j) := by
          rw [Fintype.sum_sum_type]
          congr 1
          · refine Finset.sum_congr rfl fun i _ => ?_
            rw [hm (Sum.inl i)]; rfl
          · refine Finset.sum_congr rfl fun j _ => ?_
            rw [hm (Sum.inr j)]; rfl
    _ = E.hInner x x + F.hInner y y := rfl

private lemma directSumMetric_posDef (E F : HermVectorBundle) :
    (directSumMetric E F).PosDef := by
  refine posDef_of_dotProduct_mulVec_pos ?_ fun z hz => ?_
  · ext a b
    obtain ⟨sa, rfl⟩ := finSumFinEquiv.surjective a
    obtain ⟨sb, rfl⟩ := finSumFinEquiv.surjective b
    rcases sa with i | j <;> rcases sb with i' | j' <;>
      simp only [Matrix.transpose_apply, directSumMetric, Matrix.reindex_apply,
        Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₁,
        Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
        Matrix.zero_apply]
    · exact congrFun (congrFun (isHermitian_real_transpose E.metric_posDef.isHermitian) i) i'
    · exact congrFun (congrFun (isHermitian_real_transpose F.metric_posDef.isHermitian) j) j'
  · rw [directSumMetric_apply]
    let x : Fin E.rk → ℝ := fun i => z (finSumFinEquiv (Sum.inl i))
    let y : Fin F.rk → ℝ := fun j => z (finSumFinEquiv (Sum.inr j))
    have hne : x ≠ 0 ∨ y ≠ 0 := by
      by_contra h
      push Not at h
      apply hz
      ext k
      obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective k
      rcases s with i | j
      · exact congrFun h.1 i
      · exact congrFun h.2 j
    rcases hne with hx | hy
    · exact add_pos_of_pos_of_nonneg (E.hInner_self_pos hx) (F.hInner_self_nonneg y)
    · exact add_pos_of_nonneg_of_pos (E.hInner_self_nonneg x) (F.hInner_self_pos hy)

/-- Direct sum `E ⊕ F` of two Hermitian vector bundles over `Spec ℤ`. -/
def directSumHerm (E F : HermVectorBundle) : HermVectorBundle where
  rk := E.rk + F.rk
  lat := directSumLat E.lat F.lat
  lat_discrete := discreteTopology_directSumLat E.lat F.lat
  lat_span_top := span_real_directSumLat E.lat F.lat E.lat_span_top F.lat_span_top
  metric := directSumMetric E F
  metric_posDef := directSumMetric_posDef E F

theorem directSumHerm_invariants (E F : HermVectorBundle) :
    (directSumHerm E F).rk = E.rk + F.rk ∧
    (directSumHerm E F).covol = E.covol * F.covol ∧
    (directSumHerm E F).arakelovDeg = E.arakelovDeg + F.arakelovDeg := by
  let inclMap : (Fin E.rk → ℝ) →ₗ[ℝ] (Fin (directSumHerm E F).rk → ℝ) := sumLeftMap E.rk F.rk
  let rightMap : (Fin F.rk → ℝ) →ₗ[ℝ] (Fin (directSumHerm E F).rk → ℝ) := sumRightMap E.rk F.rk
  let projMap : (Fin (directSumHerm E F).rk → ℝ) →ₗ[ℝ] (Fin F.rk → ℝ) :=
    { toFun := fun z j => z (finSumFinEquiv (Sum.inr j))
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hdm : ∀ z : Fin (directSumHerm E F).rk → ℝ,
      z ⬝ᵥ (directSumHerm E F).metric.mulVec z =
        E.hInner (fun i => z (finSumFinEquiv (Sum.inl i))) (fun i => z (finSumFinEquiv (Sum.inl i))) +
        F.hInner (fun j => z (finSumFinEquiv (Sum.inr j))) (fun j => z (finSumFinEquiv (Sum.inr j))) :=
    fun z => directSumMetric_apply E F z
  have hincl_l : ∀ (y : Fin E.rk → ℝ) (i : Fin E.rk),
      inclMap y (finSumFinEquiv (Sum.inl i)) = y i := fun y i => by
    change Sum.elim y (fun _ => 0) (finSumFinEquiv.symm (finSumFinEquiv (Sum.inl i))) = y i
    rw [Equiv.symm_apply_apply]; rfl
  have hincl_r : ∀ (y : Fin E.rk → ℝ) (j : Fin F.rk),
      inclMap y (finSumFinEquiv (Sum.inr j)) = 0 := fun y j => by
    change Sum.elim y (fun _ => 0) (finSumFinEquiv.symm (finSumFinEquiv (Sum.inr j))) = 0
    rw [Equiv.symm_apply_apply]; rfl
  have hright_l : ∀ (q : Fin F.rk → ℝ) (i : Fin E.rk),
      rightMap q (finSumFinEquiv (Sum.inl i)) = 0 := fun q i => by
    change Sum.elim (fun _ => 0) q (finSumFinEquiv.symm (finSumFinEquiv (Sum.inl i))) = 0
    rw [Equiv.symm_apply_apply]; rfl
  have hright_r : ∀ (q : Fin F.rk → ℝ) (j : Fin F.rk),
      rightMap q (finSumFinEquiv (Sum.inr j)) = q j := fun q j => by
    change Sum.elim (fun _ => 0) q (finSumFinEquiv.symm (finSumFinEquiv (Sum.inr j))) = q j
    rw [Equiv.symm_apply_apply]; rfl
  have hinner_add_l : ∀ (B : HermVectorBundle) (a b c : Fin B.rk → ℝ),
      B.hInner (a + b) c = B.hInner a c + B.hInner b c := fun B a b c => by
    simp [HermVectorBundle.hInner, add_dotProduct]
  have hinner_add_r : ∀ (B : HermVectorBundle) (a b c : Fin B.rk → ℝ),
      B.hInner a (b + c) = B.hInner a b + B.hInner a c := fun B a b c => by
    rw [B.hInner_symm, hinner_add_l, B.hInner_symm b a, B.hInner_symm c a]
  have hinner_zero_l : ∀ (B : HermVectorBundle) (a : Fin B.rk → ℝ),
      B.hInner 0 a = 0 := fun B a => by simp [HermVectorBundle.hInner]
  have hinner_incl : ∀ y : Fin E.rk → ℝ, ∀ z : Fin (directSumHerm E F).rk → ℝ,
      (directSumHerm E F).hInner (inclMap y) z =
        E.hInner y (fun i => z (finSumFinEquiv (Sum.inl i))) := by
    intro y z
    let u : Fin (directSumHerm E F).rk → ℝ := inclMap y
    have hpol : ∀ a b : Fin (directSumHerm E F).rk → ℝ,
        (directSumHerm E F).hInner a b =
          (1 / 2 : ℝ) * ((directSumHerm E F).hInner (a + b) (a + b) -
            (directSumHerm E F).hInner a a - (directSumHerm E F).hInner b b) := by
      intro a b
      rw [hinner_add_l (directSumHerm E F), hinner_add_r (directSumHerm E F),
        hinner_add_r (directSumHerm E F), (directSumHerm E F).hInner_symm b a]
      ring
    have hpolE : ∀ a b : Fin E.rk → ℝ,
        E.hInner a b = (1 / 2 : ℝ) * (E.hInner (a + b) (a + b) - E.hInner a a - E.hInner b b) := by
      intro a b
      rw [hinner_add_l E, hinner_add_r E, hinner_add_r E, E.hInner_symm b a]
      ring
    rw [hpol, hpolE]
    change (1 / 2 : ℝ) * ((u + z) ⬝ᵥ (directSumHerm E F).metric.mulVec (u + z) -
      u ⬝ᵥ (directSumHerm E F).metric.mulVec u - z ⬝ᵥ (directSumHerm E F).metric.mulVec z) = _
    rw [hdm (u + z), hdm u, hdm z]
    have hu_l : (fun i => u (finSumFinEquiv (Sum.inl i))) = y := funext (hincl_l y)
    have hu_r : (fun j => u (finSumFinEquiv (Sum.inr j))) = 0 := funext (hincl_r y)
    have hl : (fun i => (u + z) (finSumFinEquiv (Sum.inl i))) =
        y + (fun i => z (finSumFinEquiv (Sum.inl i))) := by
      ext i; exact congrArg (· + z _) (hincl_l y i)
    have hr : (fun j => (u + z) (finSumFinEquiv (Sum.inr j))) =
        (fun j => z (finSumFinEquiv (Sum.inr j))) := by
      ext j; change u (finSumFinEquiv (Sum.inr j)) + z (finSumFinEquiv (Sum.inr j)) = _
      dsimp only [u]; rw [hincl_r y j, zero_add]
    rw [hu_l, hu_r, hl, hr, hinner_zero_l F, add_zero]
    ring
  let ses : HermVectorBundle.HermShortExactSeq E (directSumHerm E F) F :=
    { incl := inclMap
      proj := projMap
      incl_maps_lat := fun y hy => by
        refine ⟨?_, ?_⟩
        · have hl : (fun i => inclMap y (finSumFinEquiv (Sum.inl i))) = y := funext (hincl_l y)
          change (fun i => inclMap y (finSumFinEquiv (Sum.inl i))) ∈ E.lat
          rwa [hl]
        · have hr : (fun j => inclMap y (finSumFinEquiv (Sum.inr j))) = 0 := funext (hincl_r y)
          change (fun j => inclMap y (finSumFinEquiv (Sum.inr j))) ∈ F.lat
          rw [hr]; exact F.lat.zero_mem
      proj_maps_lat := fun z hz => hz.2
      exact_lat := fun z hz hp => by
        refine ⟨fun i => z (finSumFinEquiv (Sum.inl i)), hz.1, ?_⟩
        ext k
        obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective k
        rcases s with i | j
        · exact hincl_l _ i
        · rw [hincl_r _ j]; exact (congrFun hp j).symm
      exact_real := by
        ext z
        simp only [LinearMap.mem_ker, LinearMap.mem_range]
        constructor
        · intro hp
          refine ⟨fun i => z (finSumFinEquiv (Sum.inl i)), ?_⟩
          ext k
          obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective k
          rcases s with i | j
          · exact hincl_l _ i
          · rw [hincl_r _ j]; exact (congrFun hp j).symm
        · rintro ⟨y, rfl⟩
          ext j
          exact hincl_r y j
      proj_surj_lat := fun q hq => by
        refine ⟨rightMap q, ⟨?_, ?_⟩, ?_⟩
        · have hl : (fun i => rightMap q (finSumFinEquiv (Sum.inl i))) = 0 := funext (hright_l q)
          change (fun i => rightMap q (finSumFinEquiv (Sum.inl i))) ∈ E.lat
          rw [hl]; exact E.lat.zero_mem
        · have hr : (fun j => rightMap q (finSumFinEquiv (Sum.inr j))) = q := funext (hright_r q)
          change (fun j => rightMap q (finSumFinEquiv (Sum.inr j))) ∈ F.lat
          rwa [hr]
        · ext j; exact hright_r q j
      incl_isometric := fun y => by
        change Real.sqrt ((inclMap y) ⬝ᵥ (directSumHerm E F).metric.mulVec (inclMap y)) =
          Real.sqrt (E.hInner y y)
        rw [hdm (inclMap y)]
        have hl : (fun i => inclMap y (finSumFinEquiv (Sum.inl i))) = y := funext (hincl_l y)
        have hr : (fun j => inclMap y (finSumFinEquiv (Sum.inr j))) = 0 := funext (hincl_r y)
        rw [hl, hr, hinner_zero_l F, add_zero]
      proj_orth_isometric := fun z hz => by
        have hzl : (fun i => z (finSumFinEquiv (Sum.inl i))) = 0 := by
          have hself := hz (fun i => z (finSumFinEquiv (Sum.inl i)))
          rw [hinner_incl] at hself
          by_contra hne
          exact (E.hInner_self_pos hne).ne' hself
        change Real.sqrt (F.hInner (projMap z) (projMap z)) =
          Real.sqrt (z ⬝ᵥ (directSumHerm E F).metric.mulVec z)
        rw [hdm z, hzl, hinner_zero_l E, zero_add]
        rfl }
  exact HermVectorBundle.arakelovDeg_short_exact_seq ses

/-- Index equivalence `Fin (2 * a) ⊕ Fin (2 * b) ≃ Fin (2 * (a + b))`. -/
def doubleAddEquiv (a b : ℕ) : Fin (2 * a) ⊕ Fin (2 * b) ≃ Fin (2 * (a + b)) :=
  finSumFinEquiv.trans (finCongr (by ring))

/-- Index equivalence `Fin n × Fin (2 * a) ≃ Fin (2 * (n * a))`. -/
def doubleMulEquiv (n a : ℕ) : Fin n × Fin (2 * a) ≃ Fin (2 * (n * a)) :=
  finProdFinEquiv.trans (finCongr (by ring))

/-- Index equivalence `Fin n × Fin a ≃ Fin (n * a)`. -/
def mulEquivFin (n a : ℕ) : Fin n × Fin a ≃ Fin (n * a) :=
  finProdFinEquiv

end LatticeAndBundleHelpers

/-! ## Section 2: Concrete `AbelianSchemeModel`, Morphisms, Products & Elliptic Witnesses -/

section AbelianSchemeModels

/-- **Concrete Abelian Scheme Model `A`** of relative dimension `dim`:
packages the full-rank discrete period lattice `Λ_A ⊂ ℝ^{2 dim}`, the complex multiplication
structure `J : Matrix (Fin (2 * dim)) (Fin (2 * dim)) ℝ` (`J² = -1`), and the concrete Hermitian
Hodge cotangent bundle `ω_{A/S} : HermVectorBundle` of rank `dim`. -/
structure AbelianSchemeModel where
  /-- Relative dimension `g` of `A / S`. -/
  dim : ℕ
  /-- Full-rank discrete period lattice `Λ_A = H₁(A, ℤ) ⊂ ℝ^{2g}`. -/
  periodLat : Submodule ℤ (Fin (2 * dim) → ℝ)
  /-- Discreteness of `Λ_A`. -/
  periodLat_discrete : DiscreteTopology periodLat
  /-- Full-rank condition `span_ℝ(Λ_A) = ℝ^{2g}`. -/
  periodLat_span_top : Submodule.span ℝ (periodLat : Set (Fin (2 * dim) → ℝ)) = ⊤
  /-- Complex structure `J` on the Lie / Betti space `ℝ^{2g}` with `J² = -I`. -/
  complexStr : Matrix (Fin (2 * dim)) (Fin (2 * dim)) ℝ
  /-- Complex structure equation `J² = -1`. -/
  complexStr_sq : complexStr * complexStr = -1
  /-- Concrete Hermitian Hodge bundle `ω_{A/S}` over `Spec ℤ` of rank `dim`. -/
  hodgeBundle : HermVectorBundle
  /-- Rank compatibility `rk(ω_{A/S}) = dim`. -/
  hodge_rk : hodgeBundle.rk = dim

attribute [instance] AbelianSchemeModel.periodLat_discrete

namespace AbelianSchemeModel

/-- Origin section `0_A` inside `ℝ^{2 dim}`. -/
def origin (A : AbelianSchemeModel) : Fin (2 * A.dim) → ℝ := 0

@[simp]
lemma origin_mem (A : AbelianSchemeModel) : A.origin ∈ A.periodLat := A.periodLat.zero_mem

/-- Trivial `0`-dimensional abelian scheme model (base section). -/
def trivial : AbelianSchemeModel where
  dim := 0
  periodLat := ⊥
  periodLat_discrete := inferInstance
  periodLat_span_top := Submodule.eq_top_of_finrank_eq (by simp)
  complexStr := 0
  complexStr_sq := by ext i; exact Fin.elim0 i
  hodgeBundle := zeroHermBundle
  hodge_rk := rfl

private def stdIntLat (n : ℕ) : Submodule ℤ (Fin n → ℝ) where
  carrier := { v | ∀ i, ∃ k : ℤ, v i = (k : ℝ) }
  add_mem' {a b} ha hb i := by
    obtain ⟨k₁, hk₁⟩ := ha i
    obtain ⟨k₂, hk₂⟩ := hb i
    exact ⟨k₁ + k₂, by simp [hk₁, hk₂]⟩
  zero_mem' _ := ⟨0, by simp⟩
  smul_mem' c {a} ha i := by
    obtain ⟨k, hk⟩ := ha i
    exact ⟨c * k, by simp [hk]⟩

private lemma discreteTopology_stdIntLat (n : ℕ) : DiscreteTopology (stdIntLat n) := by
  rw [discreteTopology_iff_isOpen_singleton]
  intro ⟨x, hx⟩
  rw [isOpen_induced_iff]
  refine ⟨Set.pi Set.univ fun i : Fin n => Metric.ball (x i) (1 / 2),
    isOpen_set_pi Set.finite_univ fun _ _ => Metric.isOpen_ball, ?_⟩
  ext ⟨y, hy⟩
  simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, Metric.mem_ball, Real.dist_eq,
    forall_const, Set.mem_singleton_iff, Subtype.mk.injEq]
  constructor
  · intro h
    ext i
    obtain ⟨kx, hkx⟩ := hx i
    obtain ⟨ky, hky⟩ := hy i
    have hi := h i
    rw [hky, hkx] at hi
    have hdiff : ((|ky - kx| : ℤ) : ℝ) < 1 := by
      have h1 : ((|ky - kx| : ℤ) : ℝ) < 1 / 2 := by simpa [Int.cast_sub, Int.cast_abs] using hi
      linarith
    have hdiff_int : |ky - kx| < 1 := by exact_mod_cast hdiff
    have h0 : ky - kx = 0 := Int.abs_lt_one_iff.mp hdiff_int
    have : ky = kx := sub_eq_zero.mp h0
    rw [hky, hkx, this]
  · intro h i
    subst h
    norm_num

private lemma span_real_stdIntLat (n : ℕ) :
    Submodule.span ℝ (stdIntLat n : Set (Fin n → ℝ)) = ⊤ := by
  apply eq_top_iff.mpr
  intro v _
  have hv : v = ∑ i : Fin n, v i • Pi.single i (1 : ℝ) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  rw [hv]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ (v i) (Submodule.subset_span ?_)
  intro j
  by_cases hij : j = i
  · subst hij; exact ⟨1, by simp⟩
  · exact ⟨0, by simp [hij]⟩

private def ellipticJ (τ : UpperHalfPlane) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![-τ.re / τ.im, -((τ.re ^ 2 + τ.im ^ 2) / τ.im); 1 / τ.im, τ.re / τ.im]

private lemma ellipticJ_sq (τ : UpperHalfPlane) : ellipticJ τ * ellipticJ τ = -1 := by
  have hy : τ.im ≠ 0 := τ.im_pos.ne'
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ellipticJ, Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp [hy] <;> ring

@[reducible] private def ellipticHodge (τ : UpperHalfPlane) : HermVectorBundle where
  rk := 1
  lat := stdIntLat 1
  lat_discrete := discreteTopology_stdIntLat 1
  lat_span_top := span_real_stdIntLat 1
  metric := !![τ.im]
  metric_posDef := by
    refine posDef_of_dotProduct_mulVec_pos (by ext i j; fin_cases i; fin_cases j; rfl) fun x hx => ?_
    have hx0 : x 0 ≠ 0 := fun h0 => hx (by ext i; fin_cases i; exact h0)
    have hmul : x ⬝ᵥ (!![τ.im] : Matrix (Fin 1) (Fin 1) ℝ).mulVec x = τ.im * (x 0) ^ 2 := by
      simp [dotProduct, Matrix.mulVec]; ring
    rw [hmul]
    exact mul_pos τ.im_pos (sq_pos_of_ne_zero hx0)

/-- Concrete `1`-dimensional **Elliptic Curve Abelian Scheme Model** `E_τ = ℂ / (ℤ + ℤτ)`
for any `τ : UpperHalfPlane`, matching `Stage11ArakelovFaltings` Hodge metric `τ.im`. -/
@[reducible] def elliptic (τ : UpperHalfPlane) : AbelianSchemeModel where
  dim := 1
  periodLat := stdIntLat 2
  periodLat_discrete := discreteTopology_stdIntLat 2
  periodLat_span_top := span_real_stdIntLat 2
  complexStr := ellipticJ τ
  complexStr_sq := ellipticJ_sq τ
  hodgeBundle := ellipticHodge τ
  hodge_rk := rfl

/-- Exact Hodge covolume `√(τ.im)` and Arakelov degree `-(1/2) log(τ.im)` of `elliptic τ`. -/
theorem elliptic_hodge_covol_deg (τ : UpperHalfPlane) :
    (elliptic τ).hodgeBundle.covol = Real.sqrt τ.im ∧
    (elliptic τ).hodgeBundle.arakelovDeg = -(1 / 2 : ℝ) * Real.log τ.im := by
  let b0 : stdIntLat 1 := ⟨fun _ => 1, fun i => ⟨1, by fin_cases i; simp⟩⟩
  let e1 : stdIntLat 1 ≃ₗ[ℤ] (Fin 1 → ℤ) :=
    { toFun := fun v _ => (v.2 0).choose
      invFun := fun f => (f 0) • b0
      left_inv := fun v => Subtype.ext (by
        ext i; fin_cases i
        change (v.2 0).choose • (1 : ℝ) = v.1 0
        rw [zsmul_eq_mul, mul_one, ← (v.2 0).choose_spec])
      right_inv := fun f => by
        ext i; fin_cases i
        change (((f 0 • b0).2 0).choose) = f 0
        have hspec : (f 0 • b0 : Fin 1 → ℝ) 0 = (((f 0 • b0).2 0).choose : ℝ) :=
          ((f 0 • b0).2 0).choose_spec
        have hval : (f 0 • b0 : Fin 1 → ℝ) 0 = (f 0 : ℝ) := by
          change (f 0 : ℤ) • (1 : ℝ) = (f 0 : ℝ)
          rw [zsmul_eq_mul, mul_one]
        rw [hval] at hspec
        exact Int.cast_injective hspec.symm
      map_add' := fun a b => by
        ext i; fin_cases i
        have ha := (a.2 0).choose_spec
        have hb := (b.2 0).choose_spec
        have hab := ((a + b).2 0).choose_spec
        have heq : (((a + b).2 0).choose : ℝ) = ((a.2 0).choose + (b.2 0).choose : ℤ) := by
          push_cast; rw [← hab, ← ha, ← hb]; rfl
        exact Int.cast_injective heq
      map_smul' := fun c a => by
        ext i; fin_cases i
        have ha := (a.2 0).choose_spec
        have hca := ((c • a).2 0).choose_spec
        have heq : (((c • a).2 0).choose : ℝ) = (c * (a.2 0).choose : ℤ) := by
          push_cast; rw [← hca, ← ha]; simp [zsmul_eq_mul]
        exact Int.cast_injective heq }
  let b1 : Basis (Fin 1) ℤ (stdIntLat 1) := Basis.ofEquivFun e1
  let b : Basis (Fin (elliptic τ).hodgeBundle.rk) ℤ (elliptic τ).hodgeBundle.lat := b1
  have hbm : ∀ i j : Fin 1, ((b1 i : Fin 1 → ℝ) j) = 1 := by
    intro i j
    fin_cases i; fin_cases j
    simp [b1, e1, b0]
  have hcov : (elliptic τ).hodgeBundle.covol = Real.sqrt τ.im := by
    rw [HermVectorBundle.covol_eq_abs_det_mul_sqrt_det_metric (elliptic τ).hodgeBundle b]
    have hdetB : Matrix.det (fun i j : Fin (elliptic τ).hodgeBundle.rk =>
        (b j : Fin (elliptic τ).hodgeBundle.rk → ℝ) i) = 1 := by
      change (Matrix.of fun i j : Fin 1 => ((b1 j : Fin 1 → ℝ) i)).det = 1
      rw [Matrix.det_fin_one]
      exact hbm 0 0
    have hdetM : (elliptic τ).hodgeBundle.metric.det = τ.im := by
      change (!![τ.im] : Matrix (Fin 1) (Fin 1) ℝ).det = τ.im
      rw [Matrix.det_fin_one]
      rfl
    rw [hdetB, abs_one, one_mul, hdetM]
  refine ⟨hcov, ?_⟩
  unfold HermVectorBundle.arakelovDeg
  rw [hcov, Real.sqrt_eq_rpow, Real.log_rpow τ.im_pos]
  ring

private def prodPeriodLat (A B : AbelianSchemeModel) :
    Submodule ℤ (Fin (2 * (A.dim + B.dim)) → ℝ) where
  carrier := { z | (fun i => z (doubleAddEquiv A.dim B.dim (Sum.inl i))) ∈ A.periodLat ∧
    (fun j => z (doubleAddEquiv A.dim B.dim (Sum.inr j))) ∈ B.periodLat }
  add_mem' ha hb := ⟨A.periodLat.add_mem ha.1 hb.1, B.periodLat.add_mem ha.2 hb.2⟩
  zero_mem' := ⟨A.periodLat.zero_mem, B.periodLat.zero_mem⟩
  smul_mem' c _ ha := ⟨A.periodLat.smul_mem c ha.1, B.periodLat.smul_mem c ha.2⟩

private lemma discreteTopology_prodPeriodLat (A B : AbelianSchemeModel) :
    DiscreteTopology (prodPeriodLat A B) := by
  let f : prodPeriodLat A B → A.periodLat × B.periodLat := fun z =>
    (⟨fun i => z.1 (doubleAddEquiv A.dim B.dim (Sum.inl i)), z.2.1⟩,
     ⟨fun j => z.1 (doubleAddEquiv A.dim B.dim (Sum.inr j)), z.2.2⟩)
  have hval : Continuous (Subtype.val : prodPeriodLat A B → (Fin (2 * (A.dim + B.dim)) → ℝ)) :=
    continuous_subtype_val
  have hf_cont : Continuous f := by
    refine Continuous.prodMk ?_ ?_
    · exact Continuous.subtype_mk (continuous_pi fun i =>
        (continuous_apply (doubleAddEquiv A.dim B.dim (Sum.inl i))).comp hval) _
    · exact Continuous.subtype_mk (continuous_pi fun j =>
        (continuous_apply (doubleAddEquiv A.dim B.dim (Sum.inr j))).comp hval) _
  have hf_inj : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    ext k
    obtain ⟨s, rfl⟩ := (doubleAddEquiv A.dim B.dim).surjective k
    rcases s with i | j
    · exact congrFun (congrArg Subtype.val (Prod.ext_iff.mp hab).1) i
    · exact congrFun (congrArg Subtype.val (Prod.ext_iff.mp hab).2) j
  exact DiscreteTopology.of_continuous_injective hf_cont hf_inj

private def prodLeftMap (A B : AbelianSchemeModel) :
    (Fin (2 * A.dim) → ℝ) →ₗ[ℝ] (Fin (2 * (A.dim + B.dim)) → ℝ) where
  toFun x k := Sum.elim x (fun _ => 0) ((doubleAddEquiv A.dim B.dim).symm k)
  map_add' x y := by
    ext k
    obtain ⟨s, rfl⟩ := (doubleAddEquiv A.dim B.dim).surjective k
    rcases s with i | j <;> simp
  map_smul' c x := by
    ext k
    obtain ⟨s, rfl⟩ := (doubleAddEquiv A.dim B.dim).surjective k
    rcases s with i | j <;> simp

private def prodRightMap (A B : AbelianSchemeModel) :
    (Fin (2 * B.dim) → ℝ) →ₗ[ℝ] (Fin (2 * (A.dim + B.dim)) → ℝ) where
  toFun y k := Sum.elim (fun _ => 0) y ((doubleAddEquiv A.dim B.dim).symm k)
  map_add' x y := by
    ext k
    obtain ⟨s, rfl⟩ := (doubleAddEquiv A.dim B.dim).surjective k
    rcases s with i | j <;> simp
  map_smul' c x := by
    ext k
    obtain ⟨s, rfl⟩ := (doubleAddEquiv A.dim B.dim).surjective k
    rcases s with i | j <;> simp

private lemma span_real_prodPeriodLat_left (A B : AbelianSchemeModel) (x : Fin (2 * A.dim) → ℝ) :
    prodLeftMap A B x ∈ Submodule.span ℝ (prodPeriodLat A B : Set _) := by
  have hx : x ∈ Submodule.span ℝ (A.periodLat : Set _) := by rw [A.periodLat_span_top]; trivial
  induction hx using Submodule.span_induction with
  | mem u hu =>
    refine Submodule.subset_span ⟨by simpa [prodLeftMap] using hu, ?_⟩
    have : (fun j => prodLeftMap A B u (doubleAddEquiv A.dim B.dim (Sum.inr j))) = 0 := by
      ext j; simp [prodLeftMap]
    rw [this]; exact B.periodLat.zero_mem
  | zero => simp
  | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ c ha

private lemma span_real_prodPeriodLat_right (A B : AbelianSchemeModel) (y : Fin (2 * B.dim) → ℝ) :
    prodRightMap A B y ∈ Submodule.span ℝ (prodPeriodLat A B : Set _) := by
  have hy : y ∈ Submodule.span ℝ (B.periodLat : Set _) := by rw [B.periodLat_span_top]; trivial
  induction hy using Submodule.span_induction with
  | mem v hv =>
    refine Submodule.subset_span ⟨?_, by simpa [prodRightMap] using hv⟩
    have : (fun i => prodRightMap A B v (doubleAddEquiv A.dim B.dim (Sum.inl i))) = 0 := by
      ext i; simp [prodRightMap]
    rw [this]; exact A.periodLat.zero_mem
  | zero => simp
  | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ c ha

private lemma span_real_prodPeriodLat (A B : AbelianSchemeModel) :
    Submodule.span ℝ (prodPeriodLat A B : Set (Fin (2 * (A.dim + B.dim)) → ℝ)) = ⊤ := by
  apply eq_top_iff.mpr
  intro z _
  have hz : z = prodLeftMap A B (fun i => z (doubleAddEquiv A.dim B.dim (Sum.inl i))) +
      prodRightMap A B (fun j => z (doubleAddEquiv A.dim B.dim (Sum.inr j))) := by
    ext k
    obtain ⟨s, rfl⟩ := (doubleAddEquiv A.dim B.dim).surjective k
    rcases s with i | j <;> simp [prodLeftMap, prodRightMap]
  rw [hz]
  exact Submodule.add_mem _ (span_real_prodPeriodLat_left A B _) (span_real_prodPeriodLat_right A B _)

private def prodComplexStr (A B : AbelianSchemeModel) :
    Matrix (Fin (2 * (A.dim + B.dim))) (Fin (2 * (A.dim + B.dim))) ℝ :=
  (Matrix.fromBlocks A.complexStr 0 0 B.complexStr).reindex
    (doubleAddEquiv A.dim B.dim) (doubleAddEquiv A.dim B.dim)

private lemma prodComplexStr_sq (A B : AbelianSchemeModel) :
    prodComplexStr A B * prodComplexStr A B = -1 := by
  ext a b
  obtain ⟨sa, rfl⟩ := (doubleAddEquiv A.dim B.dim).surjective a
  obtain ⟨sb, rfl⟩ := (doubleAddEquiv A.dim B.dim).surjective b
  simp only [Matrix.mul_apply, Matrix.neg_apply, Matrix.one_apply, prodComplexStr,
    Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply]
  rw [← (doubleAddEquiv A.dim B.dim).sum_comp, Fintype.sum_sum_type]
  simp_rw [Equiv.symm_apply_apply]
  rcases sa with i | j <;> rcases sb with i' | j'
  · simp only [Matrix.fromBlocks_apply₁₁]
    have h1 : (∑ x : Fin (2 * B.dim),
        (Matrix.fromBlocks A.complexStr 0 0 B.complexStr) (Sum.inl i) (Sum.inr x) *
        (Matrix.fromBlocks A.complexStr 0 0 B.complexStr) (Sum.inr x) (Sum.inl i')) = 0 := by
      simp
    rw [h1, add_zero]
    have h := congrFun (congrFun A.complexStr_sq i) i'
    simpa [Matrix.mul_apply, Matrix.one_apply] using h
  · simp
  · simp
  · simp only [Matrix.fromBlocks_apply₂₂]
    have h1 : (∑ x : Fin (2 * A.dim),
        (Matrix.fromBlocks A.complexStr 0 0 B.complexStr) (Sum.inr j) (Sum.inl x) *
        (Matrix.fromBlocks A.complexStr 0 0 B.complexStr) (Sum.inl x) (Sum.inr j')) = 0 := by
      simp
    rw [h1, zero_add]
    have h := congrFun (congrFun B.complexStr_sq j) j'
    simpa [Matrix.mul_apply, Matrix.one_apply] using h

/-- Fiber product `A ×_S B` of two abelian scheme models. -/
@[reducible] def prod (A B : AbelianSchemeModel) : AbelianSchemeModel where
  dim := A.dim + B.dim
  periodLat := prodPeriodLat A B
  periodLat_discrete := discreteTopology_prodPeriodLat A B
  periodLat_span_top := span_real_prodPeriodLat A B
  complexStr := prodComplexStr A B
  complexStr_sq := prodComplexStr_sq A B
  hodgeBundle := directSumHerm A.hodgeBundle B.hodgeBundle
  hodge_rk := by
    change A.hodgeBundle.rk + B.hodgeBundle.rk = A.dim + B.dim
    rw [A.hodge_rk, B.hodge_rk]

/-- Exact Hodge-bundle Arakelov degree additivity for fiber products:
`deg_Ar(ω_{(A × B)/S}) = deg_Ar(ω_{A/S}) + deg_Ar(ω_{B/S})`. -/
theorem hodgeBundle_prod_arakelovDeg (A B : AbelianSchemeModel) :
    (A.prod B).hodgeBundle.arakelovDeg = A.hodgeBundle.arakelovDeg + B.hodgeBundle.arakelovDeg :=
  (directSumHerm_invariants A.hodgeBundle B.hodgeBundle).2.2

/-- Exact Hodge-bundle covolume multiplicativity for fiber products. -/
theorem hodgeBundle_prod_covol (A B : AbelianSchemeModel) :
    (A.prod B).hodgeBundle.covol = A.hodgeBundle.covol * B.hodgeBundle.covol :=
  (directSumHerm_invariants A.hodgeBundle B.hodgeBundle).2.1

/-- `n`-fold fiber power `A^n` of an abelian scheme model. -/
def pow (A : AbelianSchemeModel) : ℕ → AbelianSchemeModel
  | 0 => AbelianSchemeModel.trivial
  | n + 1 => (A.pow n).prod A

@[simp]
theorem pow_dim (A : AbelianSchemeModel) (n : ℕ) : (A.pow n).dim = n * A.dim := by
  induction n with
  | zero => simp [pow, trivial]
  | succ n ih =>
    change (A.pow n).dim + A.dim = (n + 1) * A.dim
    rw [ih]; ring

theorem hodgeBundle_pow_arakelovDeg (A : AbelianSchemeModel) (n : ℕ) :
    (A.pow n).hodgeBundle.arakelovDeg = (n : ℝ) * A.hodgeBundle.arakelovDeg := by
  induction n with
  | zero =>
    change zeroHermBundle.arakelovDeg = ((0 : ℕ) : ℝ) * A.hodgeBundle.arakelovDeg
    rw [zeroHermBundle_arakelovDeg, Nat.cast_zero, zero_mul]
  | succ n ih =>
    change ((A.pow n).prod A).hodgeBundle.arakelovDeg = ((n + 1 : ℕ) : ℝ) * A.hodgeBundle.arakelovDeg
    rw [hodgeBundle_prod_arakelovDeg, ih]
    push_cast
    ring

end AbelianSchemeModel

/-- **Abelian Scheme Group Homomorphism `φ : A → B`**:
an `ℝ`-linear map on universal covers `ℝ^{2 dim_A} → ℝ^{2 dim_B}` that maps `Λ_A` into `Λ_B`
and commutes with the complex structures `J_A` and `J_B`. -/
structure AbelianSchemeHom (A B : AbelianSchemeModel) where
  toLinear : (Fin (2 * A.dim) → ℝ) →ₗ[ℝ] (Fin (2 * B.dim) → ℝ)
  maps_period : ∀ x ∈ A.periodLat, toLinear x ∈ B.periodLat
  comm_complexStr :
    toLinear.comp (Matrix.mulVecLin A.complexStr) =
      (Matrix.mulVecLin B.complexStr).comp toLinear

namespace AbelianSchemeHom

@[ext]
theorem ext {A B : AbelianSchemeModel} {φ ψ : AbelianSchemeHom A B}
    (h : φ.toLinear = ψ.toLinear) : φ = ψ := by
  cases φ; cases ψ; congr

/-- Identity endomorphism `id_A : A → A`. -/
def id (A : AbelianSchemeModel) : AbelianSchemeHom A A where
  toLinear := LinearMap.id
  maps_period _ hx := hx
  comm_complexStr := rfl

/-- Composition `ψ ∘ φ : A → C`. -/
def comp {A B C : AbelianSchemeModel} (ψ : AbelianSchemeHom B C) (φ : AbelianSchemeHom A B) :
    AbelianSchemeHom A C where
  toLinear := ψ.toLinear.comp φ.toLinear
  maps_period _ hx := ψ.maps_period _ (φ.maps_period _ hx)
  comm_complexStr := by
    rw [LinearMap.comp_assoc, φ.comm_complexStr, ← LinearMap.comp_assoc,
      ψ.comm_complexStr, LinearMap.comp_assoc]

@[simp]
theorem comp_toLinear {A B C : AbelianSchemeModel}
    (ψ : AbelianSchemeHom B C) (φ : AbelianSchemeHom A B) (x : Fin (2 * A.dim) → ℝ) :
    (ψ.comp φ).toLinear x = ψ.toLinear (φ.toLinear x) := rfl

@[simp]
theorem comp_id {A B : AbelianSchemeModel} (φ : AbelianSchemeHom A B) :
    φ.comp (id A) = φ := ext rfl

@[simp]
theorem id_comp {A B : AbelianSchemeModel} (φ : AbelianSchemeHom A B) :
    (id B).comp φ = φ := ext rfl

@[simp]
theorem comp_assoc {A B C D : AbelianSchemeModel}
    (χ : AbelianSchemeHom C D) (ψ : AbelianSchemeHom B C) (φ : AbelianSchemeHom A B) :
    (χ.comp ψ).comp φ = χ.comp (ψ.comp φ) := ext rfl

instance {A B : AbelianSchemeModel} : Zero (AbelianSchemeHom A B) where
  zero :=
    { toLinear := 0
      maps_period := fun _ _ => B.periodLat.zero_mem
      comm_complexStr := LinearMap.ext fun _ => by simp }

instance {A B : AbelianSchemeModel} : Add (AbelianSchemeHom A B) where
  add φ ψ :=
    { toLinear := φ.toLinear + ψ.toLinear
      maps_period := fun x hx => B.periodLat.add_mem (φ.maps_period x hx) (ψ.maps_period x hx)
      comm_complexStr := LinearMap.ext fun x => by
        have h1 := LinearMap.congr_fun φ.comm_complexStr x
        have h2 := LinearMap.congr_fun ψ.comm_complexStr x
        simp only [LinearMap.comp_apply, LinearMap.add_apply, Matrix.mulVecLin_apply] at h1 h2 ⊢
        rw [h1, h2, Matrix.mulVec_add] }

instance {A B : AbelianSchemeModel} : Neg (AbelianSchemeHom A B) where
  neg φ :=
    { toLinear := -φ.toLinear
      maps_period := fun x hx => B.periodLat.neg_mem (φ.maps_period x hx)
      comm_complexStr := LinearMap.ext fun x => by
        have h1 := LinearMap.congr_fun φ.comm_complexStr x
        simp only [LinearMap.comp_apply, LinearMap.neg_apply, Matrix.mulVecLin_apply] at h1 ⊢
        rw [h1, Matrix.mulVec_neg] }

instance {A B : AbelianSchemeModel} : Sub (AbelianSchemeHom A B) where
  sub φ ψ := φ + -ψ

instance {A B : AbelianSchemeModel} : SMul ℤ (AbelianSchemeHom A B) where
  smul n φ :=
    { toLinear := n • φ.toLinear
      maps_period := fun x hx => B.periodLat.smul_mem n (φ.maps_period x hx)
      comm_complexStr := LinearMap.ext fun x => by
        have h1 := LinearMap.congr_fun φ.comm_complexStr x
        simp only [LinearMap.comp_apply, LinearMap.smul_apply, Matrix.mulVecLin_apply] at h1 ⊢
        rw [h1, ← Int.cast_smul_eq_zsmul ℝ, Matrix.mulVec_smul, Int.cast_smul_eq_zsmul] }

instance {A B : AbelianSchemeModel} : AddCommGroup (AbelianSchemeHom A B) where
  add_assoc a b c := ext (add_assoc a.toLinear b.toLinear c.toLinear)
  zero_add a := ext (zero_add a.toLinear)
  add_zero a := ext (add_zero a.toLinear)
  nsmul := nsmulRec
  zsmul n a := n • a
  zsmul_zero' a := ext (zero_smul ℤ a.toLinear)
  zsmul_succ' n a := ext (by
    change ((n + 1 : ℕ) : ℤ) • a.toLinear = (n : ℤ) • a.toLinear + a.toLinear
    rw [Nat.cast_succ, add_smul, one_smul])
  zsmul_neg' n a := ext (by
    change (Int.negSucc n) • a.toLinear = -(((n + 1 : ℕ) : ℤ) • a.toLinear)
    rw [Int.negSucc_eq, neg_smul]; rfl)
  neg_add_cancel a := ext (neg_add_cancel a.toLinear)
  add_comm a b := ext (add_comm a.toLinear b.toLinear)

/-- Multiplication-by-`n` isogeny `[n]_A : A → A` (`n : ℤ`). -/
def mulBy (A : AbelianSchemeModel) (n : ℤ) : AbelianSchemeHom A A :=
  n • id A

@[simp]
theorem mulBy_apply (A : AbelianSchemeModel) (n : ℤ) (x : Fin (2 * A.dim) → ℝ) :
    (mulBy A n).toLinear x = n • x := rfl

theorem mulBy_comp_mulBy (A : AbelianSchemeModel) (m n : ℤ) :
    (mulBy A m).comp (mulBy A n) = mulBy A (m * n) := by
  apply ext
  refine LinearMap.ext fun x => ?_
  change m • (n • x) = (m * n) • x
  rw [← Int.cast_smul_eq_zsmul ℝ, ← Int.cast_smul_eq_zsmul ℝ, ← Int.cast_smul_eq_zsmul ℝ,
    smul_smul, Int.cast_mul]

theorem mulBy_comm_hom {A B : AbelianSchemeModel} (φ : AbelianSchemeHom A B) (n : ℤ) :
    (mulBy B n).comp φ = φ.comp (mulBy A n) := by
  apply ext
  refine LinearMap.ext fun x => ?_
  change n • φ.toLinear x = φ.toLinear (n • x)
  rw [map_zsmul]

instance (A : AbelianSchemeModel) : Ring (AbelianSchemeHom A A) where
  mul := comp
  one := id A
  mul_assoc := comp_assoc
  one_mul := id_comp
  mul_one := comp_id
  left_distrib a b c := ext (LinearMap.comp_add _ _ _)
  right_distrib a b c := ext (LinearMap.add_comp _ _ _)
  zero_mul a := ext (LinearMap.zero_comp _)
  mul_zero a := ext (LinearMap.comp_zero _)

end AbelianSchemeHom

/-- Isomorphism `A ≃ B` of abelian scheme models. -/
structure AbelianSchemeIso (A B : AbelianSchemeModel) where
  toHom : AbelianSchemeHom A B
  invHom : AbelianSchemeHom B A
  left_inv : invHom.comp toHom = AbelianSchemeHom.id A
  right_inv : toHom.comp invHom = AbelianSchemeHom.id B

/-- Symmetry of abelian scheme isomorphisms. -/
def AbelianSchemeIso.symm {A B : AbelianSchemeModel} (e : AbelianSchemeIso A B) :
    AbelianSchemeIso B A where
  toHom := e.invHom
  invHom := e.toHom
  left_inv := e.right_inv
  right_inv := e.left_inv

/-- General morphism `f : A → B` of abelian scheme models (a homomorphism composed with
a translation `offset`). -/
structure AbelianSchemeMorphism (A B : AbelianSchemeModel) where
  toHom : AbelianSchemeHom A B
  offset : Fin (2 * B.dim) → ℝ

namespace AbelianSchemeMorphism

def eval {A B : AbelianSchemeModel} (f : AbelianSchemeMorphism A B) :
    (Fin (2 * A.dim) → ℝ) → (Fin (2 * B.dim) → ℝ) :=
  fun x => f.toHom.toLinear x + f.offset

theorem eval_period {A B : AbelianSchemeModel} (f : AbelianSchemeMorphism A B)
    (x : Fin (2 * A.dim) → ℝ) {γ : Fin (2 * A.dim) → ℝ} (hγ : γ ∈ A.periodLat) :
    f.eval (x + γ) - f.eval x ∈ B.periodLat := by
  have heq : f.eval (x + γ) - f.eval x = f.toHom.toLinear γ := by
    simp only [eval, map_add]
    abel
  rw [heq]
  exact f.toHom.maps_period γ hγ

end AbelianSchemeMorphism

end AbelianSchemeModels

/-! ## Section 3: `OriginSectionUnique`, `RigidityLemma` & All Algebraic Abelian Scheme Laws -/

section OriginSectionAndRigidity

/-- **Origin Section Uniqueness (Group-Law Version)**:
any two two-sided identity sections for a binary group law on `X` are equal. -/
theorem origin_section_unique_of_group_law {X : Type*} (m : X → X → X)
    {e₁ e₂ : X} (he₁ : ∀ x, m e₁ x = x ∧ m x e₁ = x)
    (he₂ : ∀ x, m e₂ x = x ∧ m x e₂ = x) :
    e₁ = e₂ := by
  calc e₁ = m e₁ e₂ := (he₂ e₁).2.symm
    _ = e₂ := (he₁ e₂).1

/-- Helper: any continuous map from a connected space to a discrete space is constant. -/
private lemma continuous_to_discrete_const {X Y : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    [TopologicalSpace Y] [DiscreteTopology Y] (f : X → Y) (hf : Continuous f) (x y : X) :
    f x = f y := by
  have hcl : IsClopen (f ⁻¹' {f y}) := (isClopen_discrete {f y}).preimage hf
  have hne : (Set.univ ∩ (f ⁻¹' {f y})).Nonempty := ⟨y, Set.mem_univ y, rfl⟩
  have hsub := PreconnectedSpace.isPreconnected_univ.subset_isClopen hcl hne
  exact Set.mem_singleton_iff.mp (hsub (Set.mem_univ x))

/-- **Origin Section Uniqueness (Discrete / Lattice Target Version)**:
any continuous map `f : (Fin (2 * A.dim) → ℝ) → Y` into a discrete space `Y` (in particular any
continuous map taking values in a discrete period lattice `B.periodLat`) is constant and uniquely
determined by its value at the origin section `A.origin = 0`. -/
theorem origin_section_unique_discrete (A : AbelianSchemeModel) {Y : Type*} [TopologicalSpace Y]
    [DiscreteTopology Y] (f : (Fin (2 * A.dim) → ℝ) → Y) (hf : Continuous f)
    (x : Fin (2 * A.dim) → ℝ) :
    f x = f A.origin :=
  continuous_to_discrete_const f hf x A.origin

/-- **Rigidified Fiberwise-Constant Section System** modeling global sections of a trivialized
line bundle over a connected base `R` whose fiberwise regular functions reduce to base scalars. -/
structure RigidifiedSectionSystem (R : Type*) (Sec : Type*) [CommRing R] [AddCommGroup Sec]
    [Module R Sec] where
  atOrigin : Sec →ₗ[R] R
  originUnit : Sec
  atOrigin_originUnit : atOrigin originUnit = 1
  atOrigin_injective : Function.Injective atOrigin

/-- **Origin Section Uniqueness (`OriginSectionUnique`)**:
1. In any `RigidifiedSectionSystem R Sec`, every global section `s : Sec` is **uniquely** a base
   scalar multiple of the origin-rigidified section `originUnit`: `∃! c : R, s = c • originUnit`,
   with `c = atOrigin s` (matching Alpöge's `ExistsUniqueEqConstMulOriginSec`).
2. Any continuous `A.periodLat`-periodic real-affine function on `A` is constant and equal to
   its value at `A.origin`. -/
theorem OriginSectionUnique {R Sec : Type*} [CommRing R] [AddCommGroup Sec] [Module R Sec]
    (sys : RigidifiedSectionSystem R Sec) (s : Sec) :
    ∃! c : R, s = c • sys.originUnit := by
  refine ⟨sys.atOrigin s, ?_, ?_⟩
  · apply sys.atOrigin_injective
    rw [map_smul, sys.atOrigin_originUnit, smul_eq_mul, mul_one]
  · intro c hc
    have h := congrArg sys.atOrigin hc
    rw [map_smul, sys.atOrigin_originUnit, smul_eq_mul, mul_one] at h
    exact h.symm

/-- Continuous `A.periodLat`-periodic affine functions on `A` are constant (`f x = f 0`). -/
theorem origin_section_unique_affine (A : AbelianSchemeModel)
    (f : (Fin (2 * A.dim) → ℝ) → ℝ)
    (haff : ∃ L : (Fin (2 * A.dim) → ℝ) →ₗ[ℝ] ℝ, ∃ c : ℝ, ∀ x, f x = L x + c)
    (hper : ∀ x, ∀ γ ∈ A.periodLat, f (x + γ) = f x) :
    ∀ x, f x = f A.origin := by
  rcases haff with ⟨L, c, hfc⟩
  have hL0 : L = 0 := by
    have hLlat : ∀ γ ∈ A.periodLat, L γ = 0 := by
      intro γ hγ
      have h := hper 0 γ hγ
      rw [zero_add, hfc, hfc] at h
      have hz : L 0 = 0 := map_zero L
      linarith
    refine LinearMap.ext fun x => ?_
    change L x = 0
    have hx : x ∈ Submodule.span ℝ (A.periodLat : Set (Fin (2 * A.dim) → ℝ)) := by
      rw [A.periodLat_span_top]; trivial
    induction hx using Submodule.span_induction with
    | mem γ hγ => exact hLlat γ hγ
    | zero => exact map_zero L
    | add a b _ _ ha hb => rw [map_add, ha, hb, add_zero]
    | smul r a _ ha => rw [map_smul, smul_eq_mul, ha, mul_zero]
  intro x
  rw [hfc, hfc, hL0, LinearMap.zero_apply, LinearMap.zero_apply]

/-- **Connectedness Period-Cocycle Invariance**:
for ANY continuous map `F : V_A × V_B → V_C` descending to `(V_A / Λ_A) × (V_B / Λ_B) → V_C / Λ_C`
(meaning `F (x + γ₁, y + γ₂) - F (x, y) ∈ C.periodLat` for all `γ₁ ∈ Λ_A, γ₂ ∈ Λ_B`),
the period shift `F (x + γ₁, y + γ₂) - F (x, y)` is **independent of `(x, y)`**! -/
theorem rigidity_period_cocycle_const (A B C : AbelianSchemeModel)
    (F : (Fin (2 * A.dim) → ℝ) × (Fin (2 * B.dim) → ℝ) → (Fin (2 * C.dim) → ℝ))
    (hF : Continuous F)
    (hdesc : ∀ (x : Fin (2 * A.dim) → ℝ) (y : Fin (2 * B.dim) → ℝ)
      {γ₁ : Fin (2 * A.dim) → ℝ} {γ₂ : Fin (2 * B.dim) → ℝ},
      γ₁ ∈ A.periodLat → γ₂ ∈ B.periodLat → F (x + γ₁, y + γ₂) - F (x, y) ∈ C.periodLat)
    {γ₁ : Fin (2 * A.dim) → ℝ} {γ₂ : Fin (2 * B.dim) → ℝ}
    (hγ₁ : γ₁ ∈ A.periodLat) (hγ₂ : γ₂ ∈ B.periodLat)
    (x x' : Fin (2 * A.dim) → ℝ) (y y' : Fin (2 * B.dim) → ℝ) :
    F (x + γ₁, y + γ₂) - F (x, y) = F (x' + γ₁, y' + γ₂) - F (x', y') := by
  let g : (Fin (2 * A.dim) → ℝ) × (Fin (2 * B.dim) → ℝ) → C.periodLat :=
    fun p => ⟨F (p.1 + γ₁, p.2 + γ₂) - F p, hdesc p.1 p.2 hγ₁ hγ₂⟩
  have hg_cont : Continuous g := by
    refine Continuous.subtype_mk ?_ _
    have hshift : Continuous (fun p : (Fin (2 * A.dim) → ℝ) × (Fin (2 * B.dim) → ℝ) =>
        (p.1 + γ₁, p.2 + γ₂)) :=
      (continuous_fst.add continuous_const).prodMk (continuous_snd.add continuous_const)
    exact (hF.comp hshift).sub hF
  exact congrArg Subtype.val (continuous_to_discrete_const g hg_cont (x, y) (x', y'))

/-- **First Rigidity Theorem (Strict Periodicity Reduction)**:
if `F : V_A × V_B → V_C` is continuous, descends to `(V_A / Λ_A) × (V_B / Λ_B) → V_C / Λ_C`,
satisfies `F (x, 0) ∈ Λ_C` for all `x`, and `F (0, y) ∈ Λ_C` for all `y`, then `F` is **strictly
`(Λ_A × Λ_B)`-periodic in `V_C`** (`F (x + γ₁, y + γ₂) = F (x, y)` with ZERO lattice shift)! -/
theorem rigidity_zero_period_cocycle (A B C : AbelianSchemeModel)
    (F : (Fin (2 * A.dim) → ℝ) × (Fin (2 * B.dim) → ℝ) → (Fin (2 * C.dim) → ℝ))
    (hF : Continuous F)
    (hdesc : ∀ (x : Fin (2 * A.dim) → ℝ) (y : Fin (2 * B.dim) → ℝ)
      {γ₁ : Fin (2 * A.dim) → ℝ} {γ₂ : Fin (2 * B.dim) → ℝ},
      γ₁ ∈ A.periodLat → γ₂ ∈ B.periodLat → F (x + γ₁, y + γ₂) - F (x, y) ∈ C.periodLat)
    (hX : ∀ x, F (x, B.origin) ∈ C.periodLat)
    (hY : ∀ y, F (A.origin, y) ∈ C.periodLat) :
    ∀ (x : Fin (2 * A.dim) → ℝ) (y : Fin (2 * B.dim) → ℝ)
      {γ₁ : Fin (2 * A.dim) → ℝ} {γ₂ : Fin (2 * B.dim) → ℝ},
      γ₁ ∈ A.periodLat → γ₂ ∈ B.periodLat → F (x + γ₁, y + γ₂) = F (x, y) := by
  have hx_const : ∀ x, F (x, B.origin) = F (A.origin, B.origin) := fun x => by
    let gx : (Fin (2 * A.dim) → ℝ) → C.periodLat := fun u => ⟨F (u, B.origin), hX u⟩
    have hcont : Continuous gx := Continuous.subtype_mk
      (hF.comp (continuous_id.prodMk continuous_const)) _
    exact congrArg Subtype.val (continuous_to_discrete_const gx hcont x A.origin)
  have hy_const : ∀ y, F (A.origin, y) = F (A.origin, B.origin) := fun y => by
    let gy : (Fin (2 * B.dim) → ℝ) → C.periodLat := fun v => ⟨F (A.origin, v), hY v⟩
    have hcont : Continuous gy := Continuous.subtype_mk
      (hF.comp (continuous_const.prodMk continuous_id)) _
    exact congrArg Subtype.val (continuous_to_discrete_const gy hcont y B.origin)
  intro x y γ₁ γ₂ hγ₁ hγ₂
  have h1 : F (x + γ₁, y + γ₂) - F (x, y) =
      (F (x + γ₁, y + γ₂) - F (x, y + γ₂)) + (F (x, y + γ₂) - F (x, y)) := by abel
  have hstep1 : F (x + γ₁, y + γ₂) - F (x, y + γ₂) = 0 := by
    have hc := rigidity_period_cocycle_const A B C F hF hdesc hγ₁ B.periodLat.zero_mem
      x A.origin (y + γ₂) B.origin
    simp only [add_zero] at hc
    rw [hc, hx_const (A.origin + γ₁), sub_self]
  have hstep2 : F (x, y + γ₂) - F (x, y) = 0 := by
    have hc := rigidity_period_cocycle_const A B C F hF hdesc A.periodLat.zero_mem hγ₂
      x A.origin y B.origin
    simp only [add_zero] at hc
    rw [hc, hy_const (B.origin + γ₂), hy_const B.origin, sub_self]
  rw [hstep1, hstep2, add_zero] at h1
  exact sub_eq_zero.mp h1

/-- **Main Rigidity Lemma (`RigidityLemma`)**:
any continuous affine / holomorphic morphism `F : A × B → C` (represented on universal covers as
`F(x, y) = L₁ x + L₂ y + c` descending to `(V_A / Λ_A) × (V_B / Λ_B) → V_C / Λ_C`) that sends
`A × {0_B}` and `{0_A} × B` into `Λ_C` (or sends `A × {0_B}` and `{0_A} × B` to `0_C`) is
**constant** (`∀ x y, F (x, y) = F (0, 0)`), and if `F (0, 0) = 0` then `F ≡ 0`! -/
theorem RigidityLemma (A B C : AbelianSchemeModel)
    (F : (Fin (2 * A.dim) → ℝ) × (Fin (2 * B.dim) → ℝ) → (Fin (2 * C.dim) → ℝ))
    (haff : ∃ (L₁ : (Fin (2 * A.dim) → ℝ) →ₗ[ℝ] (Fin (2 * C.dim) → ℝ))
      (L₂ : (Fin (2 * B.dim) → ℝ) →ₗ[ℝ] (Fin (2 * C.dim) → ℝ))
      (c : Fin (2 * C.dim) → ℝ), ∀ x y, F (x, y) = L₁ x + L₂ y + c)
    (hdesc : ∀ (x : Fin (2 * A.dim) → ℝ) (y : Fin (2 * B.dim) → ℝ)
      {γ₁ : Fin (2 * A.dim) → ℝ} {γ₂ : Fin (2 * B.dim) → ℝ},
      γ₁ ∈ A.periodLat → γ₂ ∈ B.periodLat → F (x + γ₁, y + γ₂) - F (x, y) ∈ C.periodLat)
    (hX : ∀ x, F (x, B.origin) ∈ C.periodLat)
    (hY : ∀ y, F (A.origin, y) ∈ C.periodLat) :
    ∀ x y, F (x, y) = F (A.origin, B.origin) := by
  rcases haff with ⟨L₁, L₂, c, hFc⟩
  have hF_cont : Continuous F := by
    have : F = fun p => L₁ p.1 + L₂ p.2 + c := by funext p; exact hFc p.1 p.2
    rw [this]
    exact ((L₁.continuous_of_finiteDimensional.comp continuous_fst).add
      (L₂.continuous_of_finiteDimensional.comp continuous_snd)).add continuous_const
  have hper := rigidity_zero_period_cocycle A B C F hF_cont hdesc hX hY
  have hL₁0 : L₁ = 0 := by
    have hlat : ∀ γ₁ ∈ A.periodLat, L₁ γ₁ = 0 := by
      intro γ₁ hγ₁
      have h := hper 0 0 hγ₁ B.periodLat.zero_mem
      rw [zero_add, zero_add, hFc, hFc] at h
      simp only [map_zero, zero_add, add_zero] at h
      simpa using h
    refine LinearMap.ext fun x => ?_
    have hx : x ∈ Submodule.span ℝ (A.periodLat : Set (Fin (2 * A.dim) → ℝ)) := by
      rw [A.periodLat_span_top]; trivial
    induction hx using Submodule.span_induction with
    | mem γ hγ => exact hlat γ hγ
    | zero => simp
    | add a b _ _ ha hb => simp [map_add, ha, hb]
    | smul r a _ ha => simp [map_smul, ha]
  have hL₂0 : L₂ = 0 := by
    have hlat : ∀ γ₂ ∈ B.periodLat, L₂ γ₂ = 0 := by
      intro γ₂ hγ₂
      have h := hper 0 0 A.periodLat.zero_mem hγ₂
      rw [zero_add, zero_add, hFc, hFc] at h
      simp only [map_zero, zero_add] at h
      simpa using h
    refine LinearMap.ext fun y => ?_
    have hy : y ∈ Submodule.span ℝ (B.periodLat : Set (Fin (2 * B.dim) → ℝ)) := by
      rw [B.periodLat_span_top]; trivial
    induction hy using Submodule.span_induction with
    | mem γ hγ => exact hlat γ hγ
    | zero => simp
    | add a b _ _ ha hb => simp [map_add, ha, hb]
    | smul r a _ ha => simp [map_smul, ha]
  intro x y
  rw [hFc, hFc, hL₁0, hL₂0]
  simp

/-- **Corollary 1 (Morphism = Homomorphism + Translation)**:
every morphism `f : AbelianSchemeMorphism A B` splits uniquely as `f(x) = φ(x) + f(0)` where
`φ = f.toHom : AbelianSchemeHom A B`! -/
theorem abelian_morphism_eq_hom_add_const {A B : AbelianSchemeModel}
    (f : AbelianSchemeMorphism A B) :
    (∀ x, f.eval x = f.toHom.toLinear x + f.eval A.origin) ∧
    (∀ (φ : AbelianSchemeHom A B) (c : Fin (2 * B.dim) → ℝ),
      (∀ x, f.eval x = φ.toLinear x + c) → φ = f.toHom ∧ c = f.eval A.origin) := by
  have heval0 : f.eval A.origin = f.offset := by
    simp [AbelianSchemeMorphism.eval, AbelianSchemeModel.origin]
  refine ⟨fun x => by rw [heval0]; rfl, fun φ c hfc => ?_⟩
  have hc : c = f.eval A.origin := by
    have h0 := hfc A.origin
    simp [AbelianSchemeModel.origin] at h0
    exact h0.symm
  refine ⟨?_, hc⟩
  apply AbelianSchemeHom.ext
  refine LinearMap.ext fun x => ?_
  have h1 := hfc x
  rw [hc, heval0] at h1
  change f.toHom.toLinear x + f.offset = φ.toLinear x + f.offset at h1
  exact (add_right_cancel h1).symm

/-- **Corollary 2 (`ExistsGrpObjIsAddLawHom` — Uniqueness & Existence of Group Law)**:
on any `A : AbelianSchemeModel`, vector addition `(x, y) ↦ x + y` descends to a commutative group law,
and ANY affine/holomorphic morphism `m : A × A → A` sharing `A.origin` as two-sided identity
coincides with `(x, y) ↦ x + y`! -/
theorem exists_grpObj_isAddLawHom (A : AbelianSchemeModel) :
    (∃ m : (Fin (2 * A.dim) → ℝ) × (Fin (2 * A.dim) → ℝ) → (Fin (2 * A.dim) → ℝ),
      (∀ x y, m (x, y) = x + y) ∧
      (∀ x y {γ₁ γ₂}, γ₁ ∈ A.periodLat → γ₂ ∈ A.periodLat →
        m (x + γ₁, y + γ₂) - m (x, y) ∈ A.periodLat) ∧
      (∀ x, m (x, A.origin) = x ∧ m (A.origin, x) = x) ∧
      (∀ x y, m (x, y) = m (y, x))) ∧
    (∀ m' : (Fin (2 * A.dim) → ℝ) × (Fin (2 * A.dim) → ℝ) → (Fin (2 * A.dim) → ℝ),
      (∃ (L₁ L₂ : (Fin (2 * A.dim) → ℝ) →ₗ[ℝ] (Fin (2 * A.dim) → ℝ))
        (c : Fin (2 * A.dim) → ℝ), ∀ x y, m' (x, y) = L₁ x + L₂ y + c) →
      (∀ x y {γ₁ γ₂}, γ₁ ∈ A.periodLat → γ₂ ∈ A.periodLat →
        m' (x + γ₁, y + γ₂) - m' (x, y) ∈ A.periodLat) →
      (∀ x, m' (x, A.origin) - x ∈ A.periodLat ∧ m' (A.origin, x) - x ∈ A.periodLat) →
      m' (A.origin, A.origin) = A.origin →
      ∀ x y, m' (x, y) = x + y) := by
  refine ⟨⟨fun p => p.1 + p.2, fun _ _ => rfl, ?_, ?_, ?_⟩, ?_⟩
  · intro x y γ₁ γ₂ hγ₁ hγ₂
    have heq : (x + γ₁) + (y + γ₂) - (x + y) = γ₁ + γ₂ := by abel
    rw [heq]
    exact A.periodLat.add_mem hγ₁ hγ₂
  · intro x; simp [AbelianSchemeModel.origin]
  · intro x y; exact add_comm x y
  · intro m' hm'_aff hm'_desc hm'_id hm'_orig x y
    let F : (Fin (2 * A.dim) → ℝ) × (Fin (2 * A.dim) → ℝ) → (Fin (2 * A.dim) → ℝ) :=
      fun p => m' p - (p.1 + p.2)
    rcases hm'_aff with ⟨L₁, L₂, c, hm'_eq⟩
    have hF_aff : ∃ (L₁' L₂' : (Fin (2 * A.dim) → ℝ) →ₗ[ℝ] (Fin (2 * A.dim) → ℝ))
        (c' : Fin (2 * A.dim) → ℝ), ∀ u v, F (u, v) = L₁' u + L₂' v + c' := by
      refine ⟨L₁ - LinearMap.id, L₂ - LinearMap.id, c, fun u v => ?_⟩
      simp only [F, hm'_eq, LinearMap.sub_apply, LinearMap.id_apply]
      abel
    have hF_desc : ∀ u v {γ₁ γ₂}, γ₁ ∈ A.periodLat → γ₂ ∈ A.periodLat →
        F (u + γ₁, v + γ₂) - F (u, v) ∈ A.periodLat := by
      intro u v γ₁ γ₂ hγ₁ hγ₂
      have heq : F (u + γ₁, v + γ₂) - F (u, v) =
          (m' (u + γ₁, v + γ₂) - m' (u, v)) - (γ₁ + γ₂) := by
        simp only [F]; abel
      rw [heq]
      exact A.periodLat.sub_mem (hm'_desc u v hγ₁ hγ₂) (A.periodLat.add_mem hγ₁ hγ₂)
    have hFX : ∀ u, F (u, A.origin) ∈ A.periodLat := fun u => by
      have : F (u, A.origin) = m' (u, A.origin) - u := by
        simp [F, AbelianSchemeModel.origin]
      rw [this]
      exact (hm'_id u).1
    have hFY : ∀ v, F (A.origin, v) ∈ A.periodLat := fun v => by
      have : F (A.origin, v) = m' (A.origin, v) - v := by
        simp [F, AbelianSchemeModel.origin]
      rw [this]
      exact (hm'_id v).2
    have hrig := RigidityLemma A A A F hF_aff hF_desc hFX hFY x y
    have h0 : F (A.origin, A.origin) = 0 := by
      change m' (A.origin, A.origin) - (A.origin + A.origin) = 0
      rw [hm'_orig]
      simp [AbelianSchemeModel.origin]
    rw [h0] at hrig
    exact sub_eq_zero.mp hrig

/-- **Commutativity of Abelian Scheme Group Law (`abelianScheme_comm`)**:
any group law on `A` satisfying `RigidityLemma` is automatically commutative. -/
theorem abelianScheme_comm (A : AbelianSchemeModel)
    (m : (Fin (2 * A.dim) → ℝ) × (Fin (2 * A.dim) → ℝ) → (Fin (2 * A.dim) → ℝ))
    (hm_aff : ∃ (L₁ L₂ : (Fin (2 * A.dim) → ℝ) →ₗ[ℝ] (Fin (2 * A.dim) → ℝ))
      (c : Fin (2 * A.dim) → ℝ), ∀ x y, m (x, y) = L₁ x + L₂ y + c)
    (hm_desc : ∀ x y {γ₁ γ₂}, γ₁ ∈ A.periodLat → γ₂ ∈ A.periodLat →
      m (x + γ₁, y + γ₂) - m (x, y) ∈ A.periodLat)
    (hm_id : ∀ x, m (x, A.origin) - x ∈ A.periodLat ∧ m (A.origin, x) - x ∈ A.periodLat)
    (hm_orig : m (A.origin, A.origin) = A.origin) :
    ∀ x y, m (x, y) = m (y, x) := by
  have heq := (exists_grpObj_isAddLawHom A).2 m hm_aff hm_desc hm_id hm_orig
  intro x y
  rw [heq x y, heq y x, add_comm]

/-! ### Riemann–Appell–Humbert Line Bundles, Theorem of the Cube & Theorem of the Square -/

/-- **Concrete Riemann / Appell–Humbert Line Bundle Data `L`** on `A : AbelianSchemeModel`:
an alternating Riemann form `E : Matrix (Fin (2 * A.dim)) (Fin (2 * A.dim)) ℝ` that is
`ℤ`-valued on `A.periodLat`, `J`-invariant (`E(Jx, Jy) = E(x, y)`), together with a quadratic
semi-character `semiChar : A.periodLat → ℝ` (`mod ℤ`) satisfying
`α(γ₁ + γ₂) - α(γ₁) - α(γ₂) ≡ ½ E(γ₁, γ₂) [mod ℤ]`. -/
structure RiemannLineBundle (A : AbelianSchemeModel) where
  altMat : Matrix (Fin (2 * A.dim)) (Fin (2 * A.dim)) ℝ
  altMat_skew : altMatᵀ = -altMat
  altMat_int : ∀ x ∈ A.periodLat, ∀ y ∈ A.periodLat, ∃ k : ℤ, x ⬝ᵥ altMat.mulVec y = (k : ℝ)
  altMat_J_inv : A.complexStrᵀ * altMat * A.complexStr = altMat
  semiChar : A.periodLat → ℝ
  semiChar_law : ∀ γ₁ γ₂ : A.periodLat,
    ∃ k : ℤ, semiChar (γ₁ + γ₂) - semiChar γ₁ - semiChar γ₂ -
      (1 / 2 : ℝ) * ((γ₁ : Fin (2 * A.dim) → ℝ) ⬝ᵥ altMat.mulVec (γ₂ : Fin (2 * A.dim) → ℝ)) = (k : ℝ)

namespace RiemannLineBundle

/-- Alternating form `E_L(x, y) = x ⬝ᵥ altMat *ᵥ y`. -/
def altForm {A : AbelianSchemeModel} (L : RiemannLineBundle A)
    (x y : Fin (2 * A.dim) → ℝ) : ℝ :=
  x ⬝ᵥ L.altMat.mulVec y

theorem altForm_skew {A : AbelianSchemeModel} (L : RiemannLineBundle A)
    (x y : Fin (2 * A.dim) → ℝ) : L.altForm x y = -L.altForm y x := by
  unfold altForm
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, L.altMat_skew,
    Matrix.neg_mulVec, neg_dotProduct, dotProduct_comm]

/-- Pullback `[n]^* L` under multiplication by `n : ℤ` (`E_{[n]^* L} = n² E_L`,
`α_{[n]^* L}(γ) = α(n γ)`). -/
def mulByPullback {A : AbelianSchemeModel} (L : RiemannLineBundle A) (n : ℤ) :
    RiemannLineBundle A where
  altMat := (n : ℝ) ^ 2 • L.altMat
  altMat_skew := by rw [Matrix.transpose_smul, L.altMat_skew, smul_neg]
  altMat_int x hx y hy := by
    obtain ⟨k, hk⟩ := L.altMat_int x hx y hy
    refine ⟨n ^ 2 * k, ?_⟩
    simp only [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, hk]
    push_cast; ring
  altMat_J_inv := by
    rw [Matrix.mul_smul, Matrix.smul_mul, L.altMat_J_inv]
  semiChar γ := L.semiChar (n • γ)
  semiChar_law γ₁ γ₂ := by
    obtain ⟨k, hk⟩ := L.semiChar_law (n • γ₁) (n • γ₂)
    refine ⟨k, ?_⟩
    rw [smul_add]
    have hsm : ((n • γ₁ : A.periodLat) : Fin (2 * A.dim) → ℝ) ⬝ᵥ
        L.altMat.mulVec ((n • γ₂ : A.periodLat) : Fin (2 * A.dim) → ℝ) =
        (n : ℝ) ^ 2 * ((γ₁ : Fin (2 * A.dim) → ℝ) ⬝ᵥ L.altMat.mulVec γ₂) := by
      simp only [Submodule.coe_smul, ← Int.cast_smul_eq_zsmul ℝ, Matrix.mulVec_smul,
        smul_dotProduct, dotProduct_smul, smul_eq_mul]
      ring
    have hsm2 : ((γ₁ : Fin (2 * A.dim) → ℝ) ⬝ᵥ ((n : ℝ) ^ 2 • L.altMat).mulVec γ₂) =
        (n : ℝ) ^ 2 * ((γ₁ : Fin (2 * A.dim) → ℝ) ⬝ᵥ L.altMat.mulVec γ₂) := by
      simp [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
    rw [hsm2]
    rwa [hsm] at hk

/-- **Symmetric Riemann Line Bundle** (`[-1]^* L = L`, i.e. `α(-γ) = α(γ)`). -/
def IsSymmetric {A : AbelianSchemeModel} (L : RiemannLineBundle A) : Prop :=
  ∀ γ : A.periodLat, ∃ k : ℤ, L.semiChar (-γ) - L.semiChar γ = (k : ℝ)

/-- **Theorem of the Cube (`theorem_of_the_cube`)**:
for any bilinear/quadratic Appell–Humbert cocycle `q(x) = ½ B(x, x) + α(x)`, the 3-variable
cube difference `Δ³ q(x, y, z) = q(x+y+z) - q(x+y) - q(x+z) - q(y+z) + q(x) + q(y) + q(z) - q(0)`
vanishes identically! -/
theorem theorem_of_the_cube {V : Type*} [AddCommGroup V]
    (B : V →+ V →+ ℝ) (a : V →+ ℝ) (c : ℝ)
    (q : V → ℝ) (hq : ∀ v, q v = (1 / 2 : ℝ) * B v v + a v + c) (x y z : V) :
    q (x + y + z) - q (x + y) - q (x + z) - q (y + z) + q x + q y + q z - q 0 = 0 := by
  simp only [hq, map_add, AddMonoidHom.add_apply, map_zero]
  ring

/-- **Theorem of the Square (`theorem_of_the_square`)**:
for any `L : RiemannLineBundle A`, translation by `x + y` and `0` vs `x` and `y` preserves the
Appell–Humbert alternating form: `E(x + y, ·) + E(0, ·) = E(x, ·) + E(y, ·)` and the induced
map `x ↦ L.altForm x` is an additive homomorphism `V_A →+ V_A^*`! -/
theorem theorem_of_the_square {A : AbelianSchemeModel} (L : RiemannLineBundle A)
    (x y z : Fin (2 * A.dim) → ℝ) :
    L.altForm (x + y) z + L.altForm 0 z = L.altForm x z + L.altForm y z := by
  simp [altForm, add_dotProduct]

/-- **`[n]^* L ≃ L^{⊗ n²}` for Symmetric Line Bundles (`mulByN_pullback_symmetric`)**:
for any symmetric `L : RiemannLineBundle A` and any `n : ℤ`, the alternating form and
semi-character of `[n]^* L` agree (`mod ℤ`) with `n²` times those of `L`! -/
theorem mulByN_pullback_symmetric {A : AbelianSchemeModel} (L : RiemannLineBundle A)
    (hSymm : L.IsSymmetric) (n : ℤ) :
    (L.mulByPullback n).altMat = (n : ℝ) ^ 2 • L.altMat ∧
    (∀ γ : A.periodLat, ∃ k : ℤ,
      (L.mulByPullback n).semiChar γ - (n : ℝ) ^ 2 * L.semiChar γ = (k : ℝ)) := by
  refine ⟨rfl, fun γ => ?_⟩
  have h0_int : ∃ c₀ : ℤ, L.semiChar 0 = (c₀ : ℝ) := by
    obtain ⟨k₀, hk₀⟩ := L.semiChar_law 0 0
    refine ⟨-k₀, ?_⟩
    simp only [add_zero, Submodule.coe_zero, Matrix.mulVec_zero, dotProduct_zero, mul_zero,
      sub_zero] at hk₀
    push_cast
    linarith
  obtain ⟨c₀, hc₀⟩ := h0_int
  have hneg : ∀ m : ℕ, ∀ γ : A.periodLat, ∃ k : ℤ,
      L.semiChar ((m : ℤ) • γ) - (m : ℝ) ^ 2 * L.semiChar γ = (k : ℝ) := by
    intro m γ
    induction m with
    | zero =>
      refine ⟨c₀, ?_⟩
      simp [hc₀]
    | succ m ih =>
      have hsucc : ((m + 1 : ℕ) : ℤ) • γ = (m : ℤ) • γ + γ := by
        rw [Nat.cast_succ, add_smul, one_smul]
      obtain ⟨k₁, hk₁⟩ := ih
      obtain ⟨k₂, hk₂⟩ := L.semiChar_law ((m : ℤ) • γ) γ
      have hE0 : ((m : ℤ) • γ : Fin (2 * A.dim) → ℝ) ⬝ᵥ
          L.altMat.mulVec (γ : Fin (2 * A.dim) → ℝ) = 0 := by
        have hself : (γ : Fin (2 * A.dim) → ℝ) ⬝ᵥ L.altMat.mulVec γ = 0 := by
          have hs := L.altForm_skew γ γ
          unfold altForm at hs
          linarith
        change (((m : ℤ) • (γ : Fin (2 * A.dim) → ℝ)) ⬝ᵥ L.altMat.mulVec γ) = 0
        rw [← Int.cast_smul_eq_zsmul ℝ, smul_dotProduct, smul_eq_mul, hself, mul_zero]
      have hE0' : ((↑((m : ℤ) • γ) : Fin (2 * A.dim) → ℝ) ⬝ᵥ L.altMat.mulVec ↑γ) = 0 := by
        simpa using hE0
      have h2m : ∃ k₃ : ℤ, L.semiChar ((m : ℤ) • γ + γ) - L.semiChar ((m : ℤ) • γ) -
          L.semiChar γ = (k₃ : ℝ) := ⟨k₂, by rw [hE0', mul_zero, sub_zero] at hk₂; exact hk₂⟩
      obtain ⟨kneg, hkneg⟩ := hSymm γ
      obtain ⟨ksum, hksum⟩ := L.semiChar_law γ (-γ)
      have hEneg : ((↑γ : Fin (2 * A.dim) → ℝ) ⬝ᵥ
          L.altMat.mulVec (↑(-γ) : Fin (2 * A.dim) → ℝ)) = 0 := by
        have hself : (γ : Fin (2 * A.dim) → ℝ) ⬝ᵥ L.altMat.mulVec γ = 0 := by
          have hs := L.altForm_skew γ γ
          unfold altForm at hs
          linarith
        change (γ : Fin (2 * A.dim) → ℝ) ⬝ᵥ L.altMat.mulVec (-(γ : Fin (2 * A.dim) → ℝ)) = 0
        rw [Matrix.mulVec_neg, dotProduct_neg, hself, neg_zero]
      have h2L : ∃ d : ℤ, 2 * L.semiChar γ = (d : ℝ) := by
        refine ⟨c₀ - ksum - kneg, ?_⟩
        rw [add_neg_cancel, hc₀, hEneg, mul_zero, sub_zero] at hksum
        push_cast
        linarith
      obtain ⟨d, hd⟩ := h2L
      obtain ⟨k₃, hk₃⟩ := h2m
      refine ⟨k₃ + k₁ - d * (m : ℤ), ?_⟩
      rw [hsucc]
      push_cast
      rw [← hd]
      have hdiff : ((m : ℝ) + 1) ^ 2 * L.semiChar γ - (m : ℝ) ^ 2 * L.semiChar γ - L.semiChar γ =
          (m : ℝ) * (2 * L.semiChar γ) := by ring
      calc L.semiChar ((m : ℤ) • γ + γ) - ((m : ℝ) + 1) ^ 2 * L.semiChar γ
          = (L.semiChar ((m : ℤ) • γ + γ) - L.semiChar ((m : ℤ) • γ) - L.semiChar γ)
            + (L.semiChar ((m : ℤ) • γ) - (m : ℝ) ^ 2 * L.semiChar γ)
            - (((m : ℝ) + 1) ^ 2 * L.semiChar γ - (m : ℝ) ^ 2 * L.semiChar γ - L.semiChar γ) := by
              ring
        _ = (k₃ : ℝ) + (k₁ : ℝ) - (m : ℝ) * (2 * L.semiChar γ) := by rw [hk₃, hk₁, hdiff]
        _ = (k₃ : ℝ) + (k₁ : ℝ) - 2 * L.semiChar γ * (m : ℝ) := by ring
  rcases Int.eq_nat_or_neg n with ⟨m, rfl | rfl⟩
  · exact hneg m γ
  · obtain ⟨k₁, hk₁⟩ := hneg m (-γ)
    obtain ⟨k₂, hk₂⟩ := hSymm γ
    refine ⟨k₁ + (m : ℤ) ^ 2 * k₂, ?_⟩
    dsimp only [mulByPullback]
    rw [neg_smul, ← smul_neg]
    push_cast
    nlinarith

end RiemannLineBundle

end OriginSectionAndRigidity

/-! ## Section 4: Concrete `DualAbelianScheme`, Poincaré Pairing & Biduality -/

section DualAbelianSchemes

/-- **Concrete Dual Abelian Scheme `A^∨` (`DualAbelianScheme`)**:
realized on the dual period lattice `Λ_A^∨ = dualLatFin A.periodLat ⊂ ℝ^{2 dim}`,
with dual complex structure `-A.complexStrᵀ` and dual Hermitian Hodge bundle `A.hodgeBundle.dual`. -/
@[reducible] def DualAbelianScheme (A : AbelianSchemeModel) : AbelianSchemeModel where
  dim := A.dim
  periodLat := dualLatFin A.periodLat
  periodLat_discrete := discreteTopology_dualLatFin A.periodLat A.periodLat_span_top
  periodLat_span_top := span_real_dualLatFin A.periodLat A.periodLat_span_top
  complexStr := -A.complexStrᵀ
  complexStr_sq := by
    rw [neg_mul_neg, ← Matrix.transpose_mul, A.complexStr_sq, Matrix.transpose_neg,
      Matrix.transpose_one]
  hodgeBundle := A.hodgeBundle.dual
  hodge_rk := A.hodge_rk

@[simp]
theorem dual_dim (A : AbelianSchemeModel) : (DualAbelianScheme A).dim = A.dim := rfl

/-- Exact Arakelov degree duality for Hodge bundles: `deg_Ar(ω_{A^∨}) = -deg_Ar(ω_A)`. -/
theorem dual_hodgeBundle_arakelovDeg (A : AbelianSchemeModel) :
    (DualAbelianScheme A).hodgeBundle.arakelovDeg = -A.hodgeBundle.arakelovDeg :=
  A.hodgeBundle.dual_invariants.2.2.1

/-- Exact slope duality for Hodge bundles: `μ(ω_{A^∨}) = -μ(ω_A)`. -/
theorem dual_hodgeBundle_slope (A : AbelianSchemeModel) :
    (DualAbelianScheme A).hodgeBundle.slope = -A.hodgeBundle.slope :=
  A.hodgeBundle.bundleSlope_dual

/-- Exact Arakelov degree cancellation on `A × A^∨`: `deg_Ar(ω_{A × A^∨}) = 0`. -/
theorem prod_dual_hodgeBundle_arakelovDeg (A : AbelianSchemeModel) :
    (A.prod (DualAbelianScheme A)).hodgeBundle.arakelovDeg = 0 := by
  rw [AbelianSchemeModel.hodgeBundle_prod_arakelovDeg, dual_hodgeBundle_arakelovDeg,
    add_neg_cancel]

/-- **Poincaré Pairing** `⟨x, y⟩_P = x ⬝ᵥ y` on `V_A × V_{A^∨}`. -/
def poincarePairing (A : AbelianSchemeModel) (x y : Fin (2 * A.dim) → ℝ) : ℝ :=
  x ⬝ᵥ y

theorem poincarePairing_int (A : AbelianSchemeModel)
    {x : Fin (2 * A.dim) → ℝ} (hx : x ∈ A.periodLat)
    {y : Fin (2 * A.dim) → ℝ} (hy : y ∈ (DualAbelianScheme A).periodLat) :
    ∃ k : ℤ, poincarePairing A x y = (k : ℝ) := by
  obtain ⟨k, hk⟩ := hy x hx
  exact ⟨k, by rw [poincarePairing, dotProduct_comm, hk]⟩

/-- Helper: matrix of an `ℝ`-linear map `f : (Fin m → ℝ) →ₗ[ℝ] (Fin n → ℝ)` in the standard basis. -/
private def homMat {A B : AbelianSchemeModel} (φ : AbelianSchemeHom A B) :
    Matrix (Fin (2 * B.dim)) (Fin (2 * A.dim)) ℝ :=
  LinearMap.toMatrix' φ.toLinear

private lemma homMat_mulVec {A B : AbelianSchemeModel} (φ : AbelianSchemeHom A B)
    (x : Fin (2 * A.dim) → ℝ) :
    (homMat φ).mulVec x = φ.toLinear x := by
  change (LinearMap.toMatrix' φ.toLinear).toLin' x = φ.toLinear x
  rw [Matrix.toLin'_toMatrix']

private lemma homMat_comm_complexStr {A B : AbelianSchemeModel} (φ : AbelianSchemeHom A B) :
    homMat φ * A.complexStr = B.complexStr * homMat φ := by
  apply Matrix.toLin'.injective
  refine LinearMap.ext fun x => ?_
  have h1 := LinearMap.congr_fun φ.comm_complexStr x
  simp only [LinearMap.comp_apply, Matrix.mulVecLin_apply] at h1
  change (homMat φ * A.complexStr).mulVec x = (B.complexStr * homMat φ).mulVec x
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, homMat_mulVec, homMat_mulVec]
  exact h1

/-- **Dual Homomorphism `φ^∨ : B^∨ → A^∨`** induced by `φ : AbelianSchemeHom A B` via the
real transpose (adjoint) map. -/
def dualHom {A B : AbelianSchemeModel} (φ : AbelianSchemeHom A B) :
    AbelianSchemeHom (DualAbelianScheme B) (DualAbelianScheme A) where
  toLinear :=
    { toFun := (homMat φ)ᵀ.mulVec
      map_add' := fun y₁ y₂ => Matrix.mulVec_add _ y₁ y₂
      map_smul' := fun c y => Matrix.mulVec_smul _ c y }
  maps_period y hy x hx := by
    have hadj : ((homMat φ)ᵀ.mulVec y) ⬝ᵥ x = y ⬝ᵥ φ.toLinear x := by
      rw [dotProduct_comm, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose,
        homMat_mulVec, dotProduct_comm]
    change ∃ k : ℤ, ((homMat φ)ᵀ.mulVec y) ⬝ᵥ x = (k : ℝ)
    rw [hadj]
    exact hy (φ.toLinear x) (φ.maps_period x hx)
  comm_complexStr := by
    refine LinearMap.ext fun y => ?_
    have ht : (homMat φ)ᵀ * (-B.complexStrᵀ) = (-A.complexStrᵀ) * (homMat φ)ᵀ := by
      have hcomm := congrArg Matrix.transpose (homMat_comm_complexStr φ)
      rw [Matrix.transpose_mul, Matrix.transpose_mul] at hcomm
      calc (homMat φ)ᵀ * (-B.complexStrᵀ)
          = -((homMat φ)ᵀ * B.complexStrᵀ) := Matrix.mul_neg _ _
        _ = -(A.complexStrᵀ * (homMat φ)ᵀ) := by rw [hcomm]
        _ = (-A.complexStrᵀ) * (homMat φ)ᵀ := (Matrix.neg_mul _ _).symm
    change (homMat φ)ᵀ.mulVec ((-B.complexStrᵀ).mulVec y) =
      (-A.complexStrᵀ).mulVec ((homMat φ)ᵀ.mulVec y)
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ht]

theorem dualHom_apply {A B : AbelianSchemeModel} (φ : AbelianSchemeHom A B)
    (y : Fin (2 * (DualAbelianScheme B).dim) → ℝ) (x : Fin (2 * A.dim) → ℝ) :
    (dualHom φ).toLinear y ⬝ᵥ x = y ⬝ᵥ φ.toLinear x := by
  dsimp only [DualAbelianScheme] at y ⊢
  change (homMat φ)ᵀ.mulVec y ⬝ᵥ x = y ⬝ᵥ φ.toLinear x
  rw [dotProduct_comm, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose,
    homMat_mulVec, dotProduct_comm]

theorem dualHom_id (A : AbelianSchemeModel) :
    dualHom (AbelianSchemeHom.id A) = AbelianSchemeHom.id (DualAbelianScheme A) := by
  apply AbelianSchemeHom.ext
  refine LinearMap.ext fun y => funext fun i => ?_
  have h1 : (dualHom (AbelianSchemeHom.id A)).toLinear y ⬝ᵥ Pi.single i (1 : ℝ) =
      y ⬝ᵥ Pi.single i (1 : ℝ) := by
    rw [dualHom_apply]; rfl
  simpa [AbelianSchemeHom.id, dotProduct, Pi.single_apply] using h1

theorem dualHom_comp {A B C : AbelianSchemeModel}
    (ψ : AbelianSchemeHom B C) (φ : AbelianSchemeHom A B) :
    dualHom (ψ.comp φ) = (dualHom φ).comp (dualHom ψ) := by
  apply AbelianSchemeHom.ext
  refine LinearMap.ext fun z => funext fun i => ?_
  dsimp only [DualAbelianScheme] at z i ⊢
  have h1 : (dualHom (ψ.comp φ)).toLinear z ⬝ᵥ Pi.single i (1 : ℝ) =
      ((dualHom φ).comp (dualHom ψ)).toLinear z ⬝ᵥ Pi.single i (1 : ℝ) := by
    rw [dualHom_apply]
    change z ⬝ᵥ ψ.toLinear (φ.toLinear (Pi.single i 1)) =
      (dualHom φ).toLinear ((dualHom ψ).toLinear z) ⬝ᵥ Pi.single i 1
    rw [dualHom_apply, dualHom_apply]
  simpa [dotProduct, Pi.single_apply] using h1

theorem dualHom_mulBy (A : AbelianSchemeModel) (n : ℤ) :
    dualHom (AbelianSchemeHom.mulBy A n) = AbelianSchemeHom.mulBy (DualAbelianScheme A) n := by
  apply AbelianSchemeHom.ext
  refine LinearMap.ext fun y => funext fun i => ?_
  dsimp only [DualAbelianScheme] at y i ⊢
  have h1 : (dualHom (AbelianSchemeHom.mulBy A n)).toLinear y ⬝ᵥ Pi.single i (1 : ℝ) =
      (AbelianSchemeHom.mulBy (DualAbelianScheme A) n).toLinear y ⬝ᵥ Pi.single i (1 : ℝ) := by
    rw [dualHom_apply, AbelianSchemeHom.mulBy_apply, AbelianSchemeHom.mulBy_apply,
      ← Int.cast_smul_eq_zsmul ℝ, ← Int.cast_smul_eq_zsmul ℝ, dotProduct_smul, smul_dotProduct]
  simpa [dotProduct, Pi.single_apply] using h1

/-- **Biduality Isomorphism `A^{∨∨} ≃ A` (`bidualIso`)**. -/
def bidualIso (A : AbelianSchemeModel) :
    AbelianSchemeIso (DualAbelianScheme (DualAbelianScheme A)) A where
  toHom :=
    { toLinear := LinearMap.id
      maps_period := fun x hx => by
        have h : ∀ u : Fin (2 * A.dim) → ℝ,
            u ∈ (DualAbelianScheme (DualAbelianScheme A)).periodLat ↔ u ∈ A.periodLat := fun u => by
          change u ∈ dualLatFin (dualLatFin A.periodLat) ↔ u ∈ A.periodLat
          rw [dualLatFin_dualLatFin A.periodLat A.periodLat_span_top]
        exact (h x).mp hx
      comm_complexStr := LinearMap.ext fun x => by
        dsimp only [LinearMap.comp_apply, LinearMap.id_apply, Matrix.mulVecLin_apply,
          DualAbelianScheme]
        simp }
  invHom :=
    { toLinear := LinearMap.id
      maps_period := fun x hx => by
        have h : ∀ u : Fin (2 * A.dim) → ℝ,
            u ∈ (DualAbelianScheme (DualAbelianScheme A)).periodLat ↔ u ∈ A.periodLat := fun u => by
          change u ∈ dualLatFin (dualLatFin A.periodLat) ↔ u ∈ A.periodLat
          rw [dualLatFin_dualLatFin A.periodLat A.periodLat_span_top]
        exact (h x).mpr hx
      comm_complexStr := LinearMap.ext fun x => by
        dsimp only [LinearMap.comp_apply, LinearMap.id_apply, Matrix.mulVecLin_apply,
          DualAbelianScheme]
        simp }
  left_inv := AbelianSchemeHom.ext rfl
  right_inv := AbelianSchemeHom.ext rfl

end DualAbelianSchemes

/-! ## Section 5: `Polarization`, `PrincipalPolarization` & Concrete Elliptic Principal Polarization -/

section Polarizations

/-- **Concrete Polarization `λ : A → A^∨` of an Abelian Scheme Model `A`**:
a skew-symmetric `J`-linear isogeny `hom : A → A^∨` with dual isogeny `dualInv : A^∨ → A`
of exponent `exponent ≥ 1` (`dualInv ∘ hom = [exponent]_A`, `hom ∘ dualInv = [exponent]_{A^∨}`)
whose associated Riemann symmetric form `H(x, y) = x ⬝ᵥ hom(J y)` is positive-definite. -/
structure Polarization (A : AbelianSchemeModel) where
  /-- Polarization isogeny `λ : A → A^∨`. -/
  hom : AbelianSchemeHom A (DualAbelianScheme A)
  /-- Dual isogeny `μ : A^∨ → A` satisfying `μ ∘ λ = [d]_A`. -/
  dualInv : AbelianSchemeHom (DualAbelianScheme A) A
  /-- Positive exponent `d ≥ 1` killing `ker λ`. -/
  exponent : ℕ
  exponent_pos : 0 < exponent
  /-- `μ ∘ λ = [d]_A`. -/
  comp_dualInv : dualInv.comp hom = AbelianSchemeHom.mulBy A exponent
  /-- `λ ∘ μ = [d]_{A^∨}`. -/
  dualInv_comp : hom.comp dualInv = AbelianSchemeHom.mulBy (DualAbelianScheme A) exponent
  /-- Alternating / skew-symmetry of the polarization pairing `λ^∨ = -λ` on `H₁(A, ℤ)`. -/
  skewSymmetric : ∀ x y : Fin (2 * A.dim) → ℝ,
    x ⬝ᵥ hom.toLinear y = -(y ⬝ᵥ hom.toLinear x)
  /-- Positive-definiteness of the Riemann symmetric metric `H(x, y) = x ⬝ᵥ hom(J y)`. -/
  posDef : ∀ x : Fin (2 * A.dim) → ℝ, x ≠ 0 →
    0 < x ⬝ᵥ hom.toLinear (A.complexStr.mulVec x)

namespace Polarization

/-- Associated Riemann symmetric bilinear form `H_P(x, y) = x ⬝ᵥ λ(J y)`. -/
def riemannForm {A : AbelianSchemeModel} (P : Polarization A)
    (x y : Fin (2 * A.dim) → ℝ) : ℝ :=
  x ⬝ᵥ P.hom.toLinear (A.complexStr.mulVec y)

theorem riemannForm_symm {A : AbelianSchemeModel} (P : Polarization A)
    (x y : Fin (2 * A.dim) → ℝ) :
    P.riemannForm x y = P.riemannForm y x := by
  unfold riemannForm
  have hc := LinearMap.congr_fun P.hom.comm_complexStr y
  simp only [LinearMap.comp_apply, Matrix.mulVecLin_apply] at hc
  dsimp only [DualAbelianScheme] at hc ⊢
  rw [hc, Matrix.neg_mulVec, dotProduct_neg, Matrix.dotProduct_mulVec,
    Matrix.vecMul_transpose, P.skewSymmetric (A.complexStr.mulVec x) y]
  ring

theorem riemannForm_add_left {A : AbelianSchemeModel} (P : Polarization A)
    (x₁ x₂ y : Fin (2 * A.dim) → ℝ) :
    P.riemannForm (x₁ + x₂) y = P.riemannForm x₁ y + P.riemannForm x₂ y := by
  unfold riemannForm
  exact add_dotProduct _ _ _

theorem riemannForm_add_right {A : AbelianSchemeModel} (P : Polarization A)
    (x y₁ y₂ : Fin (2 * A.dim) → ℝ) :
    P.riemannForm x (y₁ + y₂) = P.riemannForm x y₁ + P.riemannForm x y₂ := by
  rw [riemannForm_symm, riemannForm_add_left, P.riemannForm_symm x y₁, P.riemannForm_symm x y₂]

theorem riemannForm_smul_left {A : AbelianSchemeModel} (P : Polarization A)
    (c : ℝ) (x y : Fin (2 * A.dim) → ℝ) :
    P.riemannForm (c • x) y = c * P.riemannForm x y := by
  unfold riemannForm
  exact smul_dotProduct _ _ _

theorem riemannForm_smul_right {A : AbelianSchemeModel} (P : Polarization A)
    (c : ℝ) (x y : Fin (2 * A.dim) → ℝ) :
    P.riemannForm x (c • y) = c * P.riemannForm x y := by
  rw [riemannForm_symm, riemannForm_smul_left, riemannForm_symm]

theorem riemannForm_nonneg {A : AbelianSchemeModel} (P : Polarization A)
    (x : Fin (2 * A.dim) → ℝ) : 0 ≤ P.riemannForm x x := by
  by_cases hx : x = 0
  · subst hx; simp [riemannForm]
  · exact (P.posDef x hx).le

theorem riemannForm_pos {A : AbelianSchemeModel} (P : Polarization A)
    {x : Fin (2 * A.dim) → ℝ} (hx : x ≠ 0) : 0 < P.riemannForm x x :=
  P.posDef x hx

theorem riemannForm_J_left {A : AbelianSchemeModel} (P : Polarization A)
    (x y : Fin (2 * A.dim) → ℝ) :
    x ⬝ᵥ P.hom.toLinear y = -P.riemannForm x (A.complexStr.mulVec y) := by
  unfold riemannForm
  dsimp only [DualAbelianScheme]
  rw [Matrix.mulVec_mulVec, A.complexStr_sq, Matrix.neg_mulVec, Matrix.one_mulVec,
    map_neg, dotProduct_neg, neg_neg]

theorem dualInv_apply_hom {A : AbelianSchemeModel} (P : Polarization A)
    (x : Fin (2 * A.dim) → ℝ) :
    P.dualInv.toLinear (P.hom.toLinear x) = (P.exponent : ℝ) • x := by
  have h := LinearMap.congr_fun (congrArg AbelianSchemeHom.toLinear P.comp_dualInv) x
  simpa [AbelianSchemeHom.comp, AbelianSchemeHom.mulBy_apply, ← Int.cast_smul_eq_zsmul ℝ,
    Int.cast_natCast] using h

theorem hom_apply_dualInv {A : AbelianSchemeModel} (P : Polarization A)
    (y : Fin (2 * A.dim) → ℝ) :
    P.hom.toLinear (P.dualInv.toLinear y) = (P.exponent : ℝ) • y := by
  have h := LinearMap.congr_fun (congrArg AbelianSchemeHom.toLinear P.dualInv_comp) y
  simpa [AbelianSchemeHom.comp, AbelianSchemeHom.mulBy_apply, ← Int.cast_smul_eq_zsmul ℝ,
    Int.cast_natCast] using h

theorem hom_injective {A : AbelianSchemeModel} (P : Polarization A) :
    Function.Injective P.hom.toLinear := by
  intro x₁ x₂ h
  have h1 := congrArg P.dualInv.toLinear h
  rw [P.dualInv_apply_hom, P.dualInv_apply_hom] at h1
  have hd : (P.exponent : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr P.exponent_pos.ne'
  exact smul_right_injective _ hd h1

theorem hom_surjective {A : AbelianSchemeModel} (P : Polarization A) :
    Function.Surjective P.hom.toLinear := by
  intro y
  have hd : (P.exponent : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr P.exponent_pos.ne'
  refine ⟨((P.exponent : ℝ)⁻¹) • P.dualInv.toLinear y, ?_⟩
  have h0 := P.hom_apply_dualInv y
  dsimp only [DualAbelianScheme] at h0 ⊢
  rw [map_smul, h0, smul_smul, inv_mul_cancel₀ hd, one_smul]

theorem dualInv_skewSymmetric {A : AbelianSchemeModel} (P : Polarization A)
    (y₁ y₂ : Fin (2 * A.dim) → ℝ) :
    y₁ ⬝ᵥ P.dualInv.toLinear y₂ = -(y₂ ⬝ᵥ P.dualInv.toLinear y₁) := by
  obtain ⟨x₁, rfl⟩ := P.hom_surjective y₁
  obtain ⟨x₂, rfl⟩ := P.hom_surjective y₂
  have h1 := P.dualInv_apply_hom x₁
  have h2 := P.dualInv_apply_hom x₂
  dsimp only [DualAbelianScheme] at h1 h2 ⊢
  rw [h1, h2, dotProduct_smul, dotProduct_smul,
    dotProduct_comm _ x₂, P.skewSymmetric x₂ x₁, dotProduct_comm (P.hom.toLinear x₂) x₁]
  ring

/-- Key dual-isogeny identity: `μ(J_{A^∨} (λ z)) = d • (J_A z)`. -/
theorem dualInv_complexStr_hom {A : AbelianSchemeModel} (P : Polarization A)
    (z : Fin (2 * A.dim) → ℝ) :
    P.dualInv.toLinear ((DualAbelianScheme A).complexStr.mulVec (P.hom.toLinear z)) =
      (P.exponent : ℝ) • (A.complexStr.mulVec z) := by
  have h1 := LinearMap.congr_fun P.dualInv.comm_complexStr (P.hom.toLinear z)
  simp only [LinearMap.comp_apply, Matrix.mulVecLin_apply] at h1
  change P.dualInv.toLinear ((DualAbelianScheme A).complexStr.mulVec (P.hom.toLinear z)) =
    A.complexStr.mulVec (P.dualInv.toLinear (P.hom.toLinear z)) at h1
  rw [h1, P.dualInv_apply_hom, Matrix.mulVec_smul]

end Polarization

/-- **Principal Polarization (`PrincipalPolarization A`)**:
a polarization `λ : A → A^∨` of exponent `1` (`μ ∘ λ = id_A` and `λ ∘ μ = id_{A^∨}`),
inducing a `ℤ`-lattice isomorphism `Λ_A ≃ₗ[ℤ] Λ_A^∨` and an isomorphism `A ≃ A^∨`. -/
structure PrincipalPolarization (A : AbelianSchemeModel) where
  toPolarization : Polarization A
  exponent_eq_one : toPolarization.exponent = 1

namespace PrincipalPolarization

/-- Isomorphism `A ≃ A^∨` induced by a principal polarization. -/
def toIso {A : AbelianSchemeModel} (P : PrincipalPolarization A) :
    AbelianSchemeIso A (DualAbelianScheme A) where
  toHom := P.toPolarization.hom
  invHom := P.toPolarization.dualInv
  left_inv := by
    rw [P.toPolarization.comp_dualInv, P.exponent_eq_one]
    apply AbelianSchemeHom.ext
    refine LinearMap.ext fun x => ?_
    simp [AbelianSchemeHom.mulBy, AbelianSchemeHom.id]
  right_inv := by
    rw [P.toPolarization.dualInv_comp, P.exponent_eq_one]
    apply AbelianSchemeHom.ext
    refine LinearMap.ext fun y => ?_
    simp [AbelianSchemeHom.mulBy, AbelianSchemeHom.id]

/-- Exact `ℤ`-lattice isomorphism `Λ_A ≃ₗ[ℤ] Λ_{A^∨}` induced by a principal polarization. -/
def periodLatEquiv {A : AbelianSchemeModel} (P : PrincipalPolarization A) :
    A.periodLat ≃ₗ[ℤ] (DualAbelianScheme A).periodLat where
  toFun x := ⟨P.toPolarization.hom.toLinear x.1, P.toPolarization.hom.maps_period x.1 x.2⟩
  invFun y := ⟨P.toPolarization.dualInv.toLinear y.1, P.toPolarization.dualInv.maps_period y.1 y.2⟩
  left_inv x := Subtype.ext (by
    have h := P.toPolarization.dualInv_apply_hom x.1
    rw [P.exponent_eq_one, Nat.cast_one, one_smul] at h
    exact h)
  right_inv y := Subtype.ext (by
    have h := P.toPolarization.hom_apply_dualInv y.1
    dsimp only [DualAbelianScheme] at h ⊢
    rw [P.exponent_eq_one, Nat.cast_one, one_smul] at h
    exact h)
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' c _ := Subtype.ext (map_zsmul _ c _)

/-- Transport a `PrincipalPolarization` across an isomorphism `e : A ≃ B` of abelian schemes. -/
def ofIso {A B : AbelianSchemeModel} (e : AbelianSchemeIso A B) (P : PrincipalPolarization B) :
    PrincipalPolarization A where
  toPolarization :=
    { hom := (dualHom e.toHom).comp (P.toPolarization.hom.comp e.toHom)
      dualInv := e.invHom.comp (P.toPolarization.dualInv.comp (dualHom e.invHom))
      exponent := 1
      exponent_pos := Nat.one_pos
      comp_dualInv := by
        have hcomp : P.toPolarization.dualInv.comp P.toPolarization.hom = AbelianSchemeHom.id B :=
          P.toIso.left_inv
        have hl : e.invHom.comp e.toHom = AbelianSchemeHom.id A := e.left_inv
        have hr : e.toHom.comp e.invHom = AbelianSchemeHom.id B := e.right_inv
        have hdual : (dualHom e.invHom).comp (dualHom e.toHom) =
            AbelianSchemeHom.id (DualAbelianScheme B) := by
          rw [← dualHom_comp, hr, dualHom_id]
        have heq1 : (e.invHom.comp (P.toPolarization.dualInv.comp (dualHom e.invHom))).comp
            ((dualHom e.toHom).comp (P.toPolarization.hom.comp e.toHom)) =
            e.invHom.comp (P.toPolarization.dualInv.comp (((dualHom e.invHom).comp (dualHom e.toHom)).comp
              (P.toPolarization.hom.comp e.toHom))) := by
          simp only [AbelianSchemeHom.comp_assoc]
        rw [heq1, hdual, AbelianSchemeHom.id_comp]
        have heq2 : e.invHom.comp (P.toPolarization.dualInv.comp (P.toPolarization.hom.comp e.toHom)) =
            e.invHom.comp ((P.toPolarization.dualInv.comp P.toPolarization.hom).comp e.toHom) := by
          simp only [AbelianSchemeHom.comp_assoc]
        rw [heq2, hcomp, AbelianSchemeHom.id_comp, hl]
        apply AbelianSchemeHom.ext
        refine LinearMap.ext fun x => ?_
        simp [AbelianSchemeHom.mulBy, AbelianSchemeHom.id]
      dualInv_comp := by
        have hcomp : P.toPolarization.hom.comp P.toPolarization.dualInv =
            AbelianSchemeHom.id (DualAbelianScheme B) := P.toIso.right_inv
        have hr : e.toHom.comp e.invHom = AbelianSchemeHom.id B := e.right_inv
        have heq1 : ((dualHom e.toHom).comp (P.toPolarization.hom.comp e.toHom)).comp
            (e.invHom.comp (P.toPolarization.dualInv.comp (dualHom e.invHom))) =
            (dualHom e.toHom).comp (P.toPolarization.hom.comp ((e.toHom.comp e.invHom).comp
              (P.toPolarization.dualInv.comp (dualHom e.invHom)))) := by
          simp only [AbelianSchemeHom.comp_assoc]
        rw [heq1, hr, AbelianSchemeHom.id_comp]
        have heq2 : (dualHom e.toHom).comp (P.toPolarization.hom.comp
            (P.toPolarization.dualInv.comp (dualHom e.invHom))) =
            (dualHom e.toHom).comp ((P.toPolarization.hom.comp P.toPolarization.dualInv).comp
              (dualHom e.invHom)) := by
          simp only [AbelianSchemeHom.comp_assoc]
        rw [heq2, hcomp, AbelianSchemeHom.id_comp]
        have hdual2 : (dualHom e.toHom).comp (dualHom e.invHom) =
            AbelianSchemeHom.id (DualAbelianScheme A) := by
          rw [← dualHom_comp, e.left_inv, dualHom_id]
        rw [hdual2]
        apply AbelianSchemeHom.ext
        refine LinearMap.ext fun y => ?_
        simp [AbelianSchemeHom.mulBy, AbelianSchemeHom.id]
      skewSymmetric := fun x y => by
        simp only [AbelianSchemeHom.comp_toLinear]
        rw [dotProduct_comm x, dualHom_apply, dotProduct_comm, P.toPolarization.skewSymmetric,
          dotProduct_comm y, dualHom_apply, dotProduct_comm]
      posDef := fun x hx => by
        change 0 < x ⬝ᵥ (dualHom e.toHom).toLinear
          (P.toPolarization.hom.toLinear (e.toHom.toLinear (A.complexStr.mulVec x)))
        have hc := LinearMap.congr_fun e.toHom.comm_complexStr x
        simp only [LinearMap.comp_apply, Matrix.mulVecLin_apply] at hc
        rw [dotProduct_comm x, dualHom_apply, hc, dotProduct_comm]
        refine P.toPolarization.posDef (e.toHom.toLinear x) fun h0 => hx ?_
        have h1 := congrArg e.invHom.toLinear h0
        have hl := LinearMap.congr_fun (congrArg AbelianSchemeHom.toLinear e.left_inv) x
        simp only [AbelianSchemeHom.comp, AbelianSchemeHom.id, LinearMap.comp_apply,
          LinearMap.id_apply] at hl
        rw [hl] at h1
        simpa using h1 }
  exponent_eq_one := rfl

end PrincipalPolarization

/-- **Unconditional Principal Polarization on Every Elliptic Curve `E_τ` (`ellipticPrincipalPol`)**:
the standard symplectic form `ω = !![0, 1; -1, 0]` gives a principal polarization on
`AbelianSchemeModel.elliptic τ` for every `τ : UpperHalfPlane`. -/
def ellipticPrincipalPol (τ : UpperHalfPlane) :
    PrincipalPolarization (AbelianSchemeModel.elliptic τ) where
  toPolarization :=
    { hom :=
        { toLinear := Matrix.mulVecLin !![0, 1; -1, 0]
          maps_period := fun x hx v hv => by
            obtain ⟨k₀, hk₀⟩ := hx 0
            obtain ⟨k₁, hk₁⟩ := hx 1
            obtain ⟨m₀, hm₀⟩ := hv 0
            obtain ⟨m₁, hm₁⟩ := hv 1
            refine ⟨k₁ * m₀ - k₀ * m₁, ?_⟩
            simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hk₀, hk₁, hm₀, hm₁]
            ring
          comm_complexStr := LinearMap.ext fun x => by
            have hmat : (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) ℝ) *
                (AbelianSchemeModel.ellipticJ τ) =
                (-(AbelianSchemeModel.ellipticJ τ)ᵀ) * !![0, 1; -1, 0] := by
              ext i j
              fin_cases i <;> fin_cases j <;>
                simp [AbelianSchemeModel.ellipticJ, Matrix.mul_apply, Fin.sum_univ_two] <;>
                ring
            change (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) ℝ).mulVec
                ((AbelianSchemeModel.ellipticJ τ).mulVec x) =
              (-(AbelianSchemeModel.ellipticJ τ)ᵀ).mulVec
                ((!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) ℝ).mulVec x)
            rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hmat] }
      dualInv :=
        { toLinear := Matrix.mulVecLin !![0, -1; 1, 0]
          maps_period := fun y hy => by
            have he0 : Pi.single (0 : Fin 2) (1 : ℝ) ∈ (AbelianSchemeModel.elliptic τ).periodLat := by
              refine Fin.forall_fin_two.mpr ⟨⟨1, by simp⟩, ⟨0, by simp⟩⟩
            have he1 : Pi.single (1 : Fin 2) (1 : ℝ) ∈ (AbelianSchemeModel.elliptic τ).periodLat := by
              refine Fin.forall_fin_two.mpr ⟨⟨0, by simp⟩, ⟨1, by simp⟩⟩
            obtain ⟨k₀, hk₀⟩ := hy _ he0
            obtain ⟨k₁, hk₁⟩ := hy _ he1
            have hy0 : y 0 = (k₀ : ℝ) := by simpa [dotProduct] using hk₀
            have hy1 : y 1 = (k₁ : ℝ) := by simpa [dotProduct] using hk₁
            intro i
            rcases i with ⟨i, hi⟩
            interval_cases i
            · exact ⟨-k₁, by simp [Matrix.mulVec, dotProduct, hy1]⟩
            · exact ⟨k₀, by simp [Matrix.mulVec, dotProduct, hy0]⟩
          comm_complexStr := LinearMap.ext fun y => by
            have hmat : (!![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ) *
                (-(AbelianSchemeModel.ellipticJ τ)ᵀ) =
                (AbelianSchemeModel.ellipticJ τ) * !![0, -1; 1, 0] := by
              ext i j
              fin_cases i <;> fin_cases j <;>
                simp [AbelianSchemeModel.ellipticJ, Matrix.mul_apply, Fin.sum_univ_two] <;>
                ring
            change (!![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ).mulVec
                ((-(AbelianSchemeModel.ellipticJ τ)ᵀ).mulVec y) =
              (AbelianSchemeModel.ellipticJ τ).mulVec
                ((!![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ).mulVec y)
            rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hmat] }
      exponent := 1
      exponent_pos := Nat.one_pos
      comp_dualInv := by
        apply AbelianSchemeHom.ext
        refine LinearMap.ext fun x => funext fun i => ?_
        rcases i with ⟨i, hi⟩
        interval_cases i <;> simp [AbelianSchemeHom.comp, AbelianSchemeHom.mulBy, AbelianSchemeHom.id,
          Matrix.mulVec, dotProduct]
      dualInv_comp := by
        apply AbelianSchemeHom.ext
        refine LinearMap.ext fun y => funext fun i => ?_
        rcases i with ⟨i, hi⟩
        interval_cases i <;> simp [AbelianSchemeHom.comp, AbelianSchemeHom.mulBy, AbelianSchemeHom.id,
          Matrix.mulVec, dotProduct]
      skewSymmetric := fun x y => by
        simp [Matrix.mulVec, dotProduct]
        ring
      posDef := fun x hx => by
        have hy : 0 < τ.im := τ.im_pos
        have hne : x 0 ≠ 0 ∨ x 1 ≠ 0 := by
          by_contra h
          push Not at h
          apply hx
          ext i
          fin_cases i <;> [exact h.1; exact h.2]
        have hquad : x ⬝ᵥ (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) ℝ).mulVec
            ((AbelianSchemeModel.ellipticJ τ).mulVec x) =
            (x 0 + τ.re * x 1) ^ 2 / τ.im + τ.im * (x 1) ^ 2 := by
          simp [AbelianSchemeModel.ellipticJ, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
          have hy0 : τ.im ≠ 0 := hy.ne'
          field_simp [hy0]
          ring
        change 0 < x ⬝ᵥ (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) ℝ).mulVec
            ((AbelianSchemeModel.ellipticJ τ).mulVec x)
        rw [hquad]
        rcases eq_or_ne (x 1) 0 with hx1 | hx1
        · have hx0 : x 0 ≠ 0 := hne.resolve_right (not_not.mpr hx1)
          rw [hx1]
          simp only [mul_zero, add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
            add_zero]
          exact div_pos (sq_pos_of_ne_zero hx0) hy
        · exact add_pos_of_nonneg_of_pos (div_nonneg (sq_nonneg _) hy.le)
            (mul_pos hy (sq_pos_of_ne_zero hx1)) }
  exponent_eq_one := rfl

end Polarizations

/-! ## Section 6: Zarhin's Trick (`zarhin_trick_principally_polarized`) via Lagrange's Four-Squares Theorem -/

section ZarhinTrick

/-- **Explicit Quaternion Integer Matrix `zarhinQuat s : Matrix (Fin 4) (Fin 4) ℤ`**
constructed unconditionally from Lagrange's Four-Squares Theorem (`Nat.sum_four_squares s`),
satisfying `Qᵀ * Q = s • I₄` and `Q * Qᵀ = s • I₄`. -/
private def quatMat (a b c d : ℤ) : Matrix (Fin 4) (Fin 4) ℤ :=
  Matrix.of fun i j => match i, j with
  | 0, 0 => a  | 0, 1 => -b | 0, 2 => -c | 0, 3 => -d
  | 1, 0 => b  | 1, 1 => a  | 1, 2 => -d | 1, 3 => c
  | 2, 0 => c  | 2, 1 => d  | 2, 2 => a  | 2, 3 => -b
  | 3, 0 => d  | 3, 1 => -c | 3, 2 => b  | 3, 3 => a

def zarhinQuat (s : ℕ) : Matrix (Fin 4) (Fin 4) ℤ :=
  let h := Nat.sum_four_squares s
  quatMat (h.choose : ℤ) (h.choose_spec.choose : ℤ)
    (h.choose_spec.choose_spec.choose : ℤ) (h.choose_spec.choose_spec.choose_spec.choose : ℤ)

private lemma quatMat_transpose_mul (a b c d : ℤ) :
    (quatMat a b c d)ᵀ * quatMat a b c d = (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) • (1 : Matrix (Fin 4) (Fin 4) ℤ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [quatMat, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

private lemma quatMat_mul_transpose (a b c d : ℤ) :
    quatMat a b c d * (quatMat a b c d)ᵀ = (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) • (1 : Matrix (Fin 4) (Fin 4) ℤ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [quatMat, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

theorem zarhinQuat_transpose_mul (s : ℕ) :
    (zarhinQuat s)ᵀ * zarhinQuat s = (s : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) := by
  let h := Nat.sum_four_squares s
  have hsq : (h.choose : ℤ) ^ 2 + (h.choose_spec.choose : ℤ) ^ 2 +
      (h.choose_spec.choose_spec.choose : ℤ) ^ 2 +
      (h.choose_spec.choose_spec.choose_spec.choose : ℤ) ^ 2 = (s : ℤ) := by
    exact_mod_cast h.choose_spec.choose_spec.choose_spec.choose_spec
  change (quatMat (h.choose : ℤ) _ _ _)ᵀ * quatMat _ _ _ _ = _
  rw [quatMat_transpose_mul, hsq]

theorem zarhinQuat_mul_transpose (s : ℕ) :
    zarhinQuat s * (zarhinQuat s)ᵀ = (s : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) := by
  let h := Nat.sum_four_squares s
  have hsq : (h.choose : ℤ) ^ 2 + (h.choose_spec.choose : ℤ) ^ 2 +
      (h.choose_spec.choose_spec.choose : ℤ) ^ 2 +
      (h.choose_spec.choose_spec.choose_spec.choose : ℤ) ^ 2 = (s : ℤ) := by
    exact_mod_cast h.choose_spec.choose_spec.choose_spec.choose_spec
  change quatMat (h.choose : ℤ) _ _ _ * (quatMat _ _ _ _)ᵀ = _
  rw [quatMat_mul_transpose, hsq]

private lemma zarhinQuat_real_sum_transpose_mul (s : ℕ) (i r : Fin 4) :
    (∑ j : Fin 4, ((zarhinQuat s j i : ℤ) : ℝ) * ((zarhinQuat s j r : ℤ) : ℝ)) =
      if i = r then (s : ℝ) else 0 := by
  have hm := congrArg (Int.cast : ℤ → ℝ) (congrFun (congrFun (zarhinQuat_transpose_mul s) i) r)
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply, Matrix.one_apply,
    smul_eq_mul, Int.cast_sum, Int.cast_mul, Int.cast_natCast] at hm
  rw [hm]
  by_cases hir : i = r <;> simp [hir]

private lemma zarhinQuat_real_sum_mul_transpose (s : ℕ) (j r : Fin 4) :
    (∑ i : Fin 4, ((zarhinQuat s j i : ℤ) : ℝ) * ((zarhinQuat s r i : ℤ) : ℝ)) =
      if j = r then (s : ℝ) else 0 := by
  have hm := congrArg (Int.cast : ℤ → ℝ) (congrFun (congrFun (zarhinQuat_mul_transpose s) j) r)
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply, Matrix.one_apply,
    smul_eq_mul, Int.cast_sum, Int.cast_mul, Int.cast_natCast] at hm
  rw [hm]
  by_cases hjr : j = r <;> simp [hjr]

/-- Zarhin's `8 × 8` symmetric unimodular block form `[[I₄, qᵀ], [q, d I₄]]` (`q = zarhinQuat (d - 1)`). -/
def zarhinForm (d : ℕ) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℤ :=
  Matrix.fromBlocks 1 (zarhinQuat (d - 1))ᵀ (zarhinQuat (d - 1)) ((d : ℤ) • 1)

/-- Explicit inverse `[[d I₄, -qᵀ], [-q, I₄]]` of `zarhinForm d`. -/
def zarhinFormInv (d : ℕ) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℤ :=
  Matrix.fromBlocks ((d : ℤ) • 1) (-(zarhinQuat (d - 1))ᵀ) (-(zarhinQuat (d - 1))) 1

theorem zarhinForm_transpose (d : ℕ) : (zarhinForm d)ᵀ = zarhinForm d := by
  simp [zarhinForm, Matrix.fromBlocks_transpose]

theorem zarhinForm_mul_inv {d : ℕ} (hd : 0 < d) : zarhinForm d * zarhinFormInv d = 1 := by
  have h1 : ((d - 1 : ℕ) : ℤ) = (d : ℤ) - 1 := by omega
  rw [zarhinForm, zarhinFormInv, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one]
  congr 1
  · rw [Matrix.mul_neg, zarhinQuat_transpose_mul, h1]; simp [sub_smul]
  · simp
  · rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Matrix.one_mul, smul_neg,
      add_neg_cancel]
  · rw [Matrix.mul_neg, zarhinQuat_mul_transpose, h1]; simp [sub_smul]

theorem zarhinFormInv_mul {d : ℕ} (hd : 0 < d) : zarhinFormInv d * zarhinForm d = 1 :=
  mul_eq_one_comm.mp (zarhinForm_mul_inv hd)

/-- Positive-definiteness of `zarhinForm d` via Cholesky factorization `Cᵀ * C`. -/
theorem zarhinForm_posDef {d : ℕ} (hd : 0 < d) :
    ((zarhinForm d).map (Int.cast : ℤ → ℝ)).PosDef := by
  let q : Matrix (Fin 4) (Fin 4) ℝ := (zarhinQuat (d - 1)).map (Int.cast : ℤ → ℝ)
  have hqq : q * qᵀ = ((d : ℝ) - 1) • (1 : Matrix (Fin 4) (Fin 4) ℝ) := by
    have h1 : (((d - 1 : ℕ) : ℤ) : ℝ) = (d : ℝ) - 1 := by
      rw [Int.cast_natCast, Nat.cast_sub (by omega)]; simp
    ext i j
    have h0 := congrArg (Int.cast : ℤ → ℝ)
      (congrFun (congrFun (zarhinQuat_mul_transpose (d - 1)) i) j)
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply, Matrix.one_apply,
      smul_eq_mul, Int.cast_sum, Int.cast_mul, q, Matrix.map_apply] at h0 ⊢
    rw [h0, h1]
    split_ifs <;> simp
  let C : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℝ := Matrix.fromBlocks 1 qᵀ 0 1
  let C' : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℝ := Matrix.fromBlocks 1 (-qᵀ) 0 1
  have hCC : C' * C = 1 := by
    rw [Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one]; simp
  have hinj : Function.Injective C.mulVec := by
    intro v w hvw
    have := congrArg C'.mulVec hvw
    simpa [Matrix.mulVec_mulVec, hCC] using this
  have key : Cᴴ * 1 * C = (zarhinForm d).map (Int.cast : ℤ → ℝ) := by
    rw [Matrix.mul_one, Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.fromBlocks_transpose,
      Matrix.fromBlocks_multiply, zarhinForm, Matrix.fromBlocks_map]
    congr 1
    · simp
    · simp [q, Matrix.transpose_map]
    · simp [q]
    · rw [Matrix.transpose_transpose, Matrix.transpose_one, Matrix.one_mul, add_comm, hqq]
      ext i j
      simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, Matrix.one_apply,
        smul_eq_mul, Int.cast_mul, Int.cast_natCast, Int.cast_ite, Int.cast_one, Int.cast_zero]
      split_ifs <;> ring
  rw [← key]
  exact Matrix.PosDef.one.conjTranspose_mul_mul_same hinj

/-- Zarhin quaternion order `ord d ⊆ M₈(ℤ)` (`d ∣ lowerLeftBlock`). -/
def zarhinOrder (d : ℕ) : Subring (Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℤ) where
  carrier := { N | ∀ i j, (d : ℤ) ∣ N (Sum.inr i) (Sum.inl j) }
  mul_mem' {N N'} hN hN' i j := by
    rw [Matrix.mul_apply, Fintype.sum_sum_type]
    exact dvd_add (Finset.dvd_sum fun k _ => (hN i k).mul_right _)
      (Finset.dvd_sum fun k _ => (hN' k j).mul_left _)
  one_mem' i j := by simp
  add_mem' {N N'} hN hN' i j := dvd_add (hN i j) (hN' i j)
  zero_mem' i j := by simp
  neg_mem' {N} hN i j := by simpa using hN i j

/-- Rosati involution `N ↦ form d * Nᵀ * formInv d` on `zarhinOrder d`. -/
def zarhinBar (d : ℕ) (N : zarhinOrder d) : zarhinOrder d :=
  ⟨zarhinForm d * (N : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℤ)ᵀ * zarhinFormInv d, by
    intro i j
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    have key : ∀ a b, ((N.1 (Sum.inr a) (Sum.inl b) : ℤ) : ZMod d) = 0 := fun a b =>
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (N.2 a b)
    simp only [Matrix.mul_apply, Fintype.sum_sum_type, zarhinForm, zarhinFormInv,
      Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.transpose_apply, Int.cast_add, Int.cast_sum,
      Int.cast_mul, Matrix.smul_apply, Matrix.neg_apply, Int.cast_neg, smul_eq_mul,
      Int.cast_natCast, ZMod.natCast_self, zero_mul, mul_zero, key,
      Finset.sum_const_zero, add_zero, zero_add, mul_neg]
    simp⟩

theorem zarhinBar_involutive {d : ℕ} (hd : 0 < d) (N : zarhinOrder d) :
    zarhinBar d (zarhinBar d N) = N := by
  ext1
  have hinvT : (zarhinFormInv d)ᵀ = zarhinFormInv d := by
    simp [zarhinFormInv, Matrix.fromBlocks_transpose]
  change zarhinForm d * (zarhinForm d * N.1ᵀ * zarhinFormInv d)ᵀ * zarhinFormInv d = N.1
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, zarhinForm_transpose, hinvT]
  calc zarhinForm d * (zarhinFormInv d * (N.1 * zarhinForm d)) * zarhinFormInv d
      = (zarhinForm d * zarhinFormInv d) * N.1 * (zarhinForm d * zarhinFormInv d) := by
          simp only [Matrix.mul_assoc]
    _ = N.1 := by rw [zarhinForm_mul_inv hd, Matrix.one_mul, Matrix.mul_one]

/-- Indexing equivalence `Fin 8 ≃ Fin 4 ⊕ Fin 4` used for Zarhin's `8 × 8` weight matrix `zW d`. -/
def zarhinSig : Fin 8 → Fin 4 ⊕ Fin 4 :=
  ![.inl 0, .inl 1, .inl 2, .inl 3, .inr 0, .inr 1, .inr 2, .inr 3]

/-- Zarhin triangular weight matrix `zW d`. -/
def zW (d : ℕ) : Matrix (Fin 8) (Fin 8) ℤ := fun k l =>
  Matrix.fromBlocks ((d : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ))
    ((2 : ℤ) • (zarhinQuat (d - 1))ᵀ) 0 1 (zarhinSig k) (zarhinSig l)

theorem zW_symm_posDef (d : ℕ) (hd : 0 < d) :
    ((zW d + (zW d)ᵀ).map (Int.cast : ℤ → ℝ)).PosDef := by
  have hsig : Function.Injective zarhinSig := by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp [zarhinSig] at h ⊢
  have hblk : (Matrix.fromBlocks ((d : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ))
      (zarhinQuat (d - 1))ᵀ (zarhinQuat (d - 1)) 1).map (Int.cast : ℤ → ℝ) |>.PosDef := by
    let q : Matrix (Fin 4) (Fin 4) ℝ := (zarhinQuat (d - 1)).map (Int.cast : ℤ → ℝ)
    have hqq : qᵀ * q = ((d : ℝ) - 1) • (1 : Matrix (Fin 4) (Fin 4) ℝ) := by
      have h1 : (((d - 1 : ℕ) : ℤ) : ℝ) = (d : ℝ) - 1 := by
        rw [Int.cast_natCast, Nat.cast_sub (by omega)]; simp
      ext i j
      have h0 := congrArg (Int.cast : ℤ → ℝ)
        (congrFun (congrFun (zarhinQuat_transpose_mul (d - 1)) i) j)
      simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply, Matrix.one_apply,
        smul_eq_mul, Int.cast_sum, Int.cast_mul, q, Matrix.map_apply] at h0 ⊢
      rw [h0, h1]
      split_ifs <;> simp
    let C : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℝ := Matrix.fromBlocks 1 0 q 1
    let C' : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℝ := Matrix.fromBlocks 1 0 (-q) 1
    have hCC : C' * C = 1 := by
      rw [Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one]; simp
    have hinj : Function.Injective C.mulVec := by
      intro v w hvw
      have := congrArg C'.mulVec hvw
      simpa [Matrix.mulVec_mulVec, hCC] using this
    have key : Cᴴ * 1 * C = (Matrix.fromBlocks ((d : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ))
        (zarhinQuat (d - 1))ᵀ (zarhinQuat (d - 1)) 1).map (Int.cast : ℤ → ℝ) := by
      rw [Matrix.mul_one, Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.fromBlocks_transpose,
        Matrix.fromBlocks_multiply, Matrix.fromBlocks_map]
      congr 1
      · rw [Matrix.transpose_one, Matrix.one_mul, hqq]
        ext i j
        simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, Matrix.one_apply,
          smul_eq_mul, Int.cast_mul, Int.cast_natCast]
        split_ifs <;> simp
      · simp [q, Matrix.transpose_map]
      · simp [q]
      · ext i j
        simp [Matrix.one_apply]
    rw [← key]
    exact Matrix.PosDef.one.conjTranspose_mul_mul_same hinj
  have h := (hblk.smul (a := (2 : ℝ)) two_pos).submatrix hsig
  convert h using 1
  ext k l
  have e : Matrix.fromBlocks ((d : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ))
      ((2 : ℤ) • (zarhinQuat (d - 1))ᵀ) 0 1 (zarhinSig k) (zarhinSig l) +
      Matrix.fromBlocks ((d : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ))
      ((2 : ℤ) • (zarhinQuat (d - 1))ᵀ) 0 1 (zarhinSig l) (zarhinSig k) =
      2 * Matrix.fromBlocks ((d : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ))
        (zarhinQuat (d - 1))ᵀ (zarhinQuat (d - 1)) 1 (zarhinSig k) (zarhinSig l) := by
    rcases zarhinSig k with a | a <;> rcases zarhinSig l with b | b <;>
      simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
        Matrix.fromBlocks_apply₂₂, Matrix.smul_apply, Matrix.one_apply, Matrix.transpose_apply,
        Matrix.zero_apply, smul_eq_mul]
    all_goals (try simp only [@eq_comm _ b a])
    all_goals (try split_ifs)
    all_goals ring
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.transpose_apply, Matrix.submatrix_apply,
    Matrix.smul_apply, smul_eq_mul]
  rw [zW, zW, e]
  push_cast
  ring

/-! ### Geometric Realization of Zarhin's Principal Polarization on `(A × A^∨)^4` -/

private def pow4Lat (A : AbelianSchemeModel) :
    Submodule ℤ (Fin (2 * (4 * A.dim)) → ℝ) where
  carrier := { x | ∀ i : Fin 4, (fun k => x (doubleMulEquiv 4 A.dim (i, k))) ∈ A.periodLat }
  add_mem' ha hb i := A.periodLat.add_mem (ha i) (hb i)
  zero_mem' _ := A.periodLat.zero_mem
  smul_mem' c _ ha i := A.periodLat.smul_mem c (ha i)

private lemma discreteTopology_pow4Lat (A : AbelianSchemeModel) :
    DiscreteTopology (pow4Lat A) := by
  let f : pow4Lat A → (Fin 4 → A.periodLat) := fun x i =>
    ⟨fun k => x.1 (doubleMulEquiv 4 A.dim (i, k)), x.2 i⟩
  have hval : Continuous (Subtype.val : pow4Lat A → (Fin (2 * (4 * A.dim)) → ℝ)) :=
    continuous_subtype_val
  have hf_cont : Continuous f := continuous_pi fun i =>
    Continuous.subtype_mk (continuous_pi fun k =>
      (continuous_apply (doubleMulEquiv 4 A.dim (i, k))).comp hval) _
  have hf_inj : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    ext m
    obtain ⟨⟨i, k⟩, rfl⟩ := (doubleMulEquiv 4 A.dim).surjective m
    exact congrFun (congrArg Subtype.val (congrFun hab i)) k
  exact DiscreteTopology.of_continuous_injective hf_cont hf_inj

private def pow4Embed (A : AbelianSchemeModel) (i : Fin 4) :
    (Fin (2 * A.dim) → ℝ) →ₗ[ℝ] (Fin (2 * (4 * A.dim)) → ℝ) where
  toFun v m :=
    let p := (doubleMulEquiv 4 A.dim).symm m
    if p.1 = i then v p.2 else 0
  map_add' x y := by
    ext m; dsimp only; by_cases h : ((doubleMulEquiv 4 A.dim).symm m).1 = i <;> simp [h]
  map_smul' c x := by
    ext m; dsimp only; by_cases h : ((doubleMulEquiv 4 A.dim).symm m).1 = i <;> simp [h]

private lemma span_real_pow4Lat (A : AbelianSchemeModel) :
    Submodule.span ℝ (pow4Lat A : Set (Fin (2 * (4 * A.dim)) → ℝ)) = ⊤ := by
  have himg : ∀ i : Fin 4, ∀ v ∈ A.periodLat, pow4Embed A i v ∈ pow4Lat A := by
    intro i v hv j
    by_cases hji : j = i
    · subst hji
      have heq : (fun k => pow4Embed A j v (doubleMulEquiv 4 A.dim (j, k))) = v := by
        ext k; simp [pow4Embed]
      rw [heq]; exact hv
    · have heq : (fun k => pow4Embed A i v (doubleMulEquiv 4 A.dim (j, k))) = 0 := by
        ext k; simp [pow4Embed, hji]
      rw [heq]; exact A.periodLat.zero_mem
  have hspan_img : ∀ i : Fin 4, ∀ v ∈ Submodule.span ℝ (A.periodLat : Set (Fin (2 * A.dim) → ℝ)),
      pow4Embed A i v ∈ Submodule.span ℝ (pow4Lat A : Set (Fin (2 * (4 * A.dim)) → ℝ)) := by
    intro i v hv
    induction hv using Submodule.span_induction with
    | mem u hu => exact Submodule.subset_span (himg i u hu)
    | zero => simp
    | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
    | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ c ha
  apply eq_top_iff.mpr
  intro x _
  have hx : x = ∑ i : Fin 4, pow4Embed A i (fun k => x (doubleMulEquiv 4 A.dim (i, k))) := by
    ext m
    obtain ⟨⟨i, k⟩, rfl⟩ := (doubleMulEquiv 4 A.dim).surjective m
    simp only [Finset.sum_apply, pow4Embed, LinearMap.coe_mk, AddHom.coe_mk, Equiv.symm_apply_apply]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji; simp [hji.symm]
    · intro hi; exact (hi (Finset.mem_univ i)).elim
  rw [hx]
  refine Submodule.sum_mem _ fun i _ => hspan_img i _ ?_
  rw [A.periodLat_span_top]; trivial

private def pow4ComplexStr (A : AbelianSchemeModel) :
    Matrix (Fin (2 * (4 * A.dim))) (Fin (2 * (4 * A.dim))) ℝ :=
  fun m n =>
    let pm := (doubleMulEquiv 4 A.dim).symm m
    let pn := (doubleMulEquiv 4 A.dim).symm n
    if pm.1 = pn.1 then A.complexStr pm.2 pn.2 else 0

private lemma pow4ComplexStr_mulVec (A : AbelianSchemeModel)
    (x : Fin (2 * (4 * A.dim)) → ℝ) (i : Fin 4) (k : Fin (2 * A.dim)) :
    (pow4ComplexStr A).mulVec x (doubleMulEquiv 4 A.dim (i, k)) =
      A.complexStr.mulVec (fun l => x (doubleMulEquiv 4 A.dim (i, l))) k := by
  simp only [Matrix.mulVec, dotProduct]
  rw [← (doubleMulEquiv 4 A.dim).sum_comp, Fintype.sum_prod_type, Finset.sum_eq_single i]
  · refine Finset.sum_congr rfl fun l _ => ?_
    simp [pow4ComplexStr]
  · intro j _ hji
    refine Finset.sum_eq_zero fun l _ => ?_
    simp [pow4ComplexStr, hji.symm]
  · intro hi; exact (hi (Finset.mem_univ i)).elim

private lemma pow4ComplexStr_sq (A : AbelianSchemeModel) :
    pow4ComplexStr A * pow4ComplexStr A = -1 := by
  ext m n
  obtain ⟨⟨i, k⟩, rfl⟩ := (doubleMulEquiv 4 A.dim).surjective m
  obtain ⟨⟨j, l⟩, rfl⟩ := (doubleMulEquiv 4 A.dim).surjective n
  simp only [Matrix.mul_apply, Matrix.neg_apply, Matrix.one_apply]
  rw [← (doubleMulEquiv 4 A.dim).sum_comp, Fintype.sum_prod_type]
  by_cases hij : i = j
  · subst hij
    rw [Finset.sum_eq_single i]
    · have hsq := congrFun (congrFun A.complexStr_sq k) l
      simp only [Matrix.mul_apply, Matrix.neg_apply, Matrix.one_apply] at hsq
      convert hsq using 1
      · refine Finset.sum_congr rfl fun r _ => ?_
        simp [pow4ComplexStr]
      · simp
    · intro r _ hri
      refine Finset.sum_eq_zero fun s _ => ?_
      simp [pow4ComplexStr, hri.symm]
    · intro hi; exact (hi (Finset.mem_univ i)).elim
  · have hne : doubleMulEquiv 4 A.dim (i, k) ≠ doubleMulEquiv 4 A.dim (j, l) := by
      intro h
      have := (doubleMulEquiv 4 A.dim).injective h
      exact hij (congrArg Prod.fst this)
    rw [if_neg hne, neg_zero]
    refine Finset.sum_eq_zero fun r _ => Finset.sum_eq_zero fun s _ => ?_
    by_cases hri : i = r
    · subst hri; simp [pow4ComplexStr, hij]
    · simp [pow4ComplexStr, hri]

/-- Direct 4-fold Hodge bundle `(E ⊕ E) ⊕ (E ⊕ E)` of rank `4 * E.rk`. -/
private def hodgePow4 (E : HermVectorBundle) : HermVectorBundle :=
  directSumHerm (directSumHerm E E) (directSumHerm E E)

/-- Direct 4-fold power `A⁴` with transparent `(Fin 4 × Fin (2 * A.dim))` coordinates. -/
@[reducible] def AbelianSchemeModel.pow4Direct (A : AbelianSchemeModel) : AbelianSchemeModel where
  dim := 4 * A.dim
  periodLat := pow4Lat A
  periodLat_discrete := discreteTopology_pow4Lat A
  periodLat_span_top := span_real_pow4Lat A
  complexStr := pow4ComplexStr A
  complexStr_sq := pow4ComplexStr_sq A
  hodgeBundle := hodgePow4 A.hodgeBundle
  hodge_rk := by
    dsimp only [hodgePow4, directSumHerm]
    rw [A.hodge_rk]; ring

private lemma mem_dual_pow4Direct_iff (A : AbelianSchemeModel)
    (y : Fin (2 * (4 * A.dim)) → ℝ) :
    y ∈ (DualAbelianScheme A.pow4Direct).periodLat ↔
      ∀ i : Fin 4, (fun k => y (doubleMulEquiv 4 A.dim (i, k))) ∈ (DualAbelianScheme A).periodLat := by
  constructor
  · intro hy i x hx
    obtain ⟨n, hn⟩ := hy (pow4Embed A i x) (by
      intro j
      by_cases hji : j = i
      · subst hji
        have heq : (fun k => pow4Embed A j x (doubleMulEquiv 4 A.dim (j, k))) = x := by
          ext k; simp [pow4Embed]
        rwa [heq]
      · have heq : (fun k => pow4Embed A i x (doubleMulEquiv 4 A.dim (j, k))) = 0 := by
          ext k; simp [pow4Embed, hji]
        rw [heq]; exact A.periodLat.zero_mem)
    refine ⟨n, ?_⟩
    rw [← hn]
    unfold dotProduct
    rw [← (doubleMulEquiv 4 A.dim).sum_comp, Fintype.sum_prod_type, Finset.sum_eq_single i]
    · refine Finset.sum_congr rfl fun k _ => ?_
      simp [pow4Embed]
    · intro j _ hji
      refine Finset.sum_eq_zero fun k _ => ?_
      simp [pow4Embed, hji]
    · intro hi; exact (hi (Finset.mem_univ i)).elim
  · intro hy x hx
    have hterm : ∀ i : Fin 4, ∃ n : ℤ,
        (fun k => y (doubleMulEquiv 4 A.dim (i, k))) ⬝ᵥ
          (fun k => x (doubleMulEquiv 4 A.dim (i, k))) = (n : ℝ) :=
      fun i => hy i _ (hx i)
    choose n hn using hterm
    refine ⟨∑ i : Fin 4, n i, ?_⟩
    unfold dotProduct
    rw [← (doubleMulEquiv 4 A.dim).sum_comp, Fintype.sum_prod_type]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    exact hn i

/-- Canonical split Zarhin space `A⁴ × (A^∨)⁴`. -/
@[reducible] def zarhinSplit (A : AbelianSchemeModel) : AbelianSchemeModel :=
  A.pow4Direct.prod (DualAbelianScheme A).pow4Direct

private def zarhinDecomp (A : AbelianSchemeModel)
    (z : Fin (2 * (zarhinSplit A).dim) → ℝ) :
    (Fin 4 → Fin (2 * A.dim) → ℝ) × (Fin 4 → Fin (2 * A.dim) → ℝ) :=
  (fun i k => z (doubleAddEquiv (4 * A.dim) (4 * A.dim) (Sum.inl (doubleMulEquiv 4 A.dim (i, k)))),
   fun j l => z (doubleAddEquiv (4 * A.dim) (4 * A.dim) (Sum.inr (doubleMulEquiv 4 A.dim (j, l)))))

private def zarhinBuild (A : AbelianSchemeModel)
    (x y : Fin 4 → Fin (2 * A.dim) → ℝ) : Fin (2 * (zarhinSplit A).dim) → ℝ :=
  fun m =>
    match (doubleAddEquiv (4 * A.dim) (4 * A.dim)).symm m with
    | Sum.inl p =>
      let q := (doubleMulEquiv 4 A.dim).symm p
      x q.1 q.2
    | Sum.inr p =>
      let q := (doubleMulEquiv 4 A.dim).symm p
      y q.1 q.2

private lemma zarhinBuild_linear_add (A : AbelianSchemeModel)
    (x₁ x₂ y₁ y₂ : Fin 4 → Fin (2 * A.dim) → ℝ) :
    zarhinBuild A (x₁ + x₂) (y₁ + y₂) = zarhinBuild A x₁ y₁ + zarhinBuild A x₂ y₂ := by
  ext m
  dsimp only [zarhinBuild, Pi.add_apply]
  cases (doubleAddEquiv (4 * A.dim) (4 * A.dim)).symm m <;> simp

private lemma zarhinBuild_linear_smul (A : AbelianSchemeModel) (c : ℝ)
    (x y : Fin 4 → Fin (2 * A.dim) → ℝ) :
    zarhinBuild A (c • x) (c • y) = c • zarhinBuild A x y := by
  ext m
  dsimp only [zarhinBuild, Pi.smul_apply]
  cases (doubleAddEquiv (4 * A.dim) (4 * A.dim)).symm m <;> simp

private lemma zarhinBuild_decomp (A : AbelianSchemeModel)
    (z : Fin (2 * (zarhinSplit A).dim) → ℝ) :
    zarhinBuild A (zarhinDecomp A z).1 (zarhinDecomp A z).2 = z := by
  ext m
  obtain ⟨s, rfl⟩ := (doubleAddEquiv (4 * A.dim) (4 * A.dim)).surjective m
  rcases s with p | p
  · obtain ⟨⟨i, k⟩, rfl⟩ := (doubleMulEquiv 4 A.dim).surjective p
    simp [zarhinBuild, zarhinDecomp]
  · obtain ⟨⟨j, l⟩, rfl⟩ := (doubleMulEquiv 4 A.dim).surjective p
    simp [zarhinBuild, zarhinDecomp]

private lemma zarhinDecomp_build (A : AbelianSchemeModel)
    (x y : Fin 4 → Fin (2 * A.dim) → ℝ) :
    zarhinDecomp A (zarhinBuild A x y) = (x, y) := by
  ext i k <;> simp [zarhinDecomp, zarhinBuild]

private lemma mem_zarhinSplit_period_iff (A : AbelianSchemeModel)
    (z : Fin (2 * (zarhinSplit A).dim) → ℝ) :
    z ∈ (zarhinSplit A).periodLat ↔
      (∀ i, (zarhinDecomp A z).1 i ∈ A.periodLat) ∧
      (∀ j, (zarhinDecomp A z).2 j ∈ (DualAbelianScheme A).periodLat) :=
  Iff.rfl

private lemma mem_dual_zarhinSplit_period_iff (A : AbelianSchemeModel)
    (w : Fin (2 * (DualAbelianScheme (zarhinSplit A)).dim) → ℝ) :
    w ∈ (DualAbelianScheme (zarhinSplit A)).periodLat ↔
      (∀ i, (zarhinDecomp A w).1 i ∈ (DualAbelianScheme A).periodLat) ∧
      (∀ j, (zarhinDecomp A w).2 j ∈ A.periodLat) := by
  have hdd : (DualAbelianScheme (DualAbelianScheme A)).periodLat = A.periodLat :=
    dualLatFin_dualLatFin A.periodLat A.periodLat_span_top
  constructor
  · intro hw
    have hL : ∀ u ∈ A.pow4Direct.periodLat,
        (fun p => w (doubleAddEquiv (4 * A.dim) (4 * A.dim) (Sum.inl p))) ⬝ᵥ u ∈
          Set.range (Int.cast : ℤ → ℝ) := by
      intro u hu
      obtain ⟨n, hn⟩ := hw (AbelianSchemeModel.prodLeftMap A.pow4Direct (DualAbelianScheme A).pow4Direct u)
        ⟨by simpa [AbelianSchemeModel.prodLeftMap] using hu, by
          have : (fun q => AbelianSchemeModel.prodLeftMap A.pow4Direct (DualAbelianScheme A).pow4Direct u
              (doubleAddEquiv (4 * A.dim) (4 * A.dim) (Sum.inr q))) = 0 := by
            ext q; simp [AbelianSchemeModel.prodLeftMap]
          rw [this]; exact Submodule.zero_mem _⟩
      refine ⟨n, ?_⟩
      rw [← hn]
      dsimp only [DualAbelianScheme, AbelianSchemeModel.prod, AbelianSchemeModel.pow4Direct,
        zarhinSplit]
      unfold dotProduct
      rw [← (doubleAddEquiv (4 * A.dim) (4 * A.dim)).sum_comp, Fintype.sum_sum_type]
      simp [AbelianSchemeModel.prodLeftMap]
    have hR : ∀ v ∈ (DualAbelianScheme A).pow4Direct.periodLat,
        (fun p => w (doubleAddEquiv (4 * A.dim) (4 * A.dim) (Sum.inr p))) ⬝ᵥ v ∈
          Set.range (Int.cast : ℤ → ℝ) := by
      intro v hv
      obtain ⟨n, hn⟩ := hw (AbelianSchemeModel.prodRightMap A.pow4Direct (DualAbelianScheme A).pow4Direct v)
        ⟨by
          have : (fun q => AbelianSchemeModel.prodRightMap A.pow4Direct (DualAbelianScheme A).pow4Direct v
              (doubleAddEquiv (4 * A.dim) (4 * A.dim) (Sum.inl q))) = 0 := by
            ext q; dsimp only [AbelianSchemeModel.prodRightMap]; simp
          rw [this]; exact Submodule.zero_mem _,
          by simpa [AbelianSchemeModel.prodRightMap] using hv⟩
      refine ⟨n, ?_⟩
      rw [← hn]
      dsimp only [DualAbelianScheme, AbelianSchemeModel.prod, AbelianSchemeModel.pow4Direct,
        zarhinSplit]
      unfold dotProduct
      rw [← (doubleAddEquiv (4 * A.dim) (4 * A.dim)).sum_comp, Fintype.sum_sum_type]
      simp [AbelianSchemeModel.prodRightMap]
    refine ⟨?_, ?_⟩
    · have h1 : (fun p => w (doubleAddEquiv (4 * A.dim) (4 * A.dim) (Sum.inl p))) ∈
          (DualAbelianScheme A.pow4Direct).periodLat := fun u hu => by
        obtain ⟨n, hn⟩ := hL u hu; exact ⟨n, hn.symm⟩
      exact (mem_dual_pow4Direct_iff A _).mp h1
    · have h2 : (fun p => w (doubleAddEquiv (4 * A.dim) (4 * A.dim) (Sum.inr p))) ∈
          (DualAbelianScheme (DualAbelianScheme A).pow4Direct).periodLat := fun v hv => by
        obtain ⟨n, hn⟩ := hR v hv; exact ⟨n, hn.symm⟩
      intro j
      have hj := (mem_dual_pow4Direct_iff (DualAbelianScheme A) _).mp h2 j
      rwa [hdd] at hj
  · rintro ⟨hw₁, hw₂⟩ z hz
    have hterm1 : ∀ i : Fin 4, ∃ n : ℤ,
        (zarhinDecomp A w).1 i ⬝ᵥ (zarhinDecomp A z).1 i = (n : ℝ) := fun i =>
      hw₁ i _ (hz.1 i)
    have hterm2 : ∀ j : Fin 4, ∃ m : ℤ,
        (zarhinDecomp A w).2 j ⬝ᵥ (zarhinDecomp A z).2 j = (m : ℝ) := fun j => by
      obtain ⟨m, hm⟩ := hz.2 j _ (hw₂ j)
      exact ⟨m, (dotProduct_comm _ _).trans hm⟩
    choose n hn using hterm1
    choose m hm using hterm2
    refine ⟨(∑ i : Fin 4, n i) + (∑ j : Fin 4, m j), ?_⟩
    dsimp only [DualAbelianScheme, AbelianSchemeModel.prod, AbelianSchemeModel.pow4Direct,
      zarhinSplit]
    unfold dotProduct
    rw [← (doubleAddEquiv (4 * A.dim) (4 * A.dim)).sum_comp, Fintype.sum_sum_type]
    have hs1 : (∑ p : Fin (2 * (4 * A.dim)),
        w (doubleAddEquiv (4 * A.dim) (4 * A.dim) (Sum.inl p)) *
          z (doubleAddEquiv (4 * A.dim) (4 * A.dim) (Sum.inl p))) =
        ∑ i : Fin 4, (zarhinDecomp A w).1 i ⬝ᵥ (zarhinDecomp A z).1 i := by
      rw [← (doubleMulEquiv 4 A.dim).sum_comp, Fintype.sum_prod_type]
      rfl
    have hs2 : (∑ p : Fin (2 * (4 * A.dim)),
        w (doubleAddEquiv (4 * A.dim) (4 * A.dim) (Sum.inr p)) *
          z (doubleAddEquiv (4 * A.dim) (4 * A.dim) (Sum.inr p))) =
        ∑ j : Fin 4, (zarhinDecomp A w).2 j ⬝ᵥ (zarhinDecomp A z).2 j := by
      rw [← (doubleMulEquiv 4 A.dim).sum_comp, Fintype.sum_prod_type]
      rfl
    have hs1' : (∑ i : Fin 4, (zarhinDecomp A w).1 i ⬝ᵥ (zarhinDecomp A z).1 i) = ∑ i : Fin 4, (n i : ℝ) :=
      Finset.sum_congr rfl fun i _ => hn i
    have hs2' : (∑ j : Fin 4, (zarhinDecomp A w).2 j ⬝ᵥ (zarhinDecomp A z).2 j) = ∑ j : Fin 4, (m j : ℝ) :=
      Finset.sum_congr rfl fun j _ => hm j
    rw [hs1, hs2, hs1', hs2']
    push_cast
    rfl

private lemma zarhin_dotProduct (A : AbelianSchemeModel)
    (w z : Fin (2 * (zarhinSplit A).dim) → ℝ) :
    w ⬝ᵥ z =
      (∑ i : Fin 4, (zarhinDecomp A w).1 i ⬝ᵥ (zarhinDecomp A z).1 i) +
      (∑ j : Fin 4, (zarhinDecomp A w).2 j ⬝ᵥ (zarhinDecomp A z).2 j) := by
  dsimp only [zarhinSplit, AbelianSchemeModel.prod, AbelianSchemeModel.pow4Direct,
    DualAbelianScheme]
  unfold dotProduct
  rw [← (doubleAddEquiv (4 * A.dim) (4 * A.dim)).sum_comp, Fintype.sum_sum_type]
  congr 1
  · rw [← (doubleMulEquiv 4 A.dim).sum_comp, Fintype.sum_prod_type]; rfl
  · rw [← (doubleMulEquiv 4 A.dim).sum_comp, Fintype.sum_prod_type]; rfl

private lemma zarhinSplit_complexStr_decomp (A : AbelianSchemeModel)
    (z : Fin (2 * (zarhinSplit A).dim) → ℝ) :
    zarhinDecomp A ((zarhinSplit A).complexStr.mulVec z) =
      (fun i => A.complexStr.mulVec ((zarhinDecomp A z).1 i),
       fun j => (DualAbelianScheme A).complexStr.mulVec ((zarhinDecomp A z).2 j)) := by
  change zarhinDecomp A ((AbelianSchemeModel.prodComplexStr A.pow4Direct
    (DualAbelianScheme A).pow4Direct).mulVec z) = _
  have hm : ∀ s : Fin (2 * (4 * A.dim)) ⊕ Fin (2 * (4 * A.dim)),
      ((AbelianSchemeModel.prodComplexStr A.pow4Direct (DualAbelianScheme A).pow4Direct).mulVec z)
        (doubleAddEquiv (4 * A.dim) (4 * A.dim) s) =
      Sum.elim
        ((pow4ComplexStr A).mulVec (fun p => z (doubleAddEquiv (4 * A.dim) (4 * A.dim) (Sum.inl p))))
        ((pow4ComplexStr (DualAbelianScheme A)).mulVec
          (fun p => z (doubleAddEquiv (4 * A.dim) (4 * A.dim) (Sum.inr p)))) s := by
    intro s
    dsimp only [AbelianSchemeModel.prodComplexStr, AbelianSchemeModel.pow4Direct, DualAbelianScheme]
    simp only [Matrix.mulVec, dotProduct, Matrix.reindex_apply, Matrix.submatrix_apply]
    rw [← (doubleAddEquiv (4 * A.dim) (4 * A.dim)).sum_comp, Fintype.sum_sum_type]
    simp_rw [Equiv.symm_apply_apply]
    rcases s with p | p <;> simp [Matrix.mulVec, dotProduct]
  ext1
  · ext i k
    change ((AbelianSchemeModel.prodComplexStr A.pow4Direct
      (DualAbelianScheme A).pow4Direct).mulVec z)
        (doubleAddEquiv (4 * A.dim) (4 * A.dim) (Sum.inl (doubleMulEquiv 4 A.dim (i, k)))) = _
    rw [hm (Sum.inl _)]
    exact pow4ComplexStr_mulVec A _ i k
  · ext j l
    change ((AbelianSchemeModel.prodComplexStr A.pow4Direct
      (DualAbelianScheme A).pow4Direct).mulVec z)
        (doubleAddEquiv (4 * A.dim) (4 * A.dim) (Sum.inr (doubleMulEquiv 4 A.dim (j, l)))) = _
    rw [hm (Sum.inr _)]
    exact pow4ComplexStr_mulVec (DualAbelianScheme A) _ j l

private lemma dual_zarhinSplit_complexStr_eq (A : AbelianSchemeModel) :
    (DualAbelianScheme (zarhinSplit A)).complexStr =
      AbelianSchemeModel.prodComplexStr (DualAbelianScheme A).pow4Direct A.pow4Direct := by
  ext m n
  obtain ⟨s, rfl⟩ := (doubleAddEquiv (4 * A.dim) (4 * A.dim)).surjective m
  obtain ⟨t, rfl⟩ := (doubleAddEquiv (4 * A.dim) (4 * A.dim)).surjective n
  change -(AbelianSchemeModel.prodComplexStr A.pow4Direct (DualAbelianScheme A).pow4Direct
      (doubleAddEquiv (4 * A.dim) (4 * A.dim) t)
      (doubleAddEquiv (4 * A.dim) (4 * A.dim) s)) =
    AbelianSchemeModel.prodComplexStr (DualAbelianScheme A).pow4Direct A.pow4Direct
      (doubleAddEquiv (4 * A.dim) (4 * A.dim) s)
      (doubleAddEquiv (4 * A.dim) (4 * A.dim) t)
  dsimp only [AbelianSchemeModel.prodComplexStr, AbelianSchemeModel.pow4Direct, DualAbelianScheme,
    Matrix.reindex_apply, Matrix.submatrix_apply]
  simp only [Equiv.symm_apply_apply]
  rcases s with p | p <;> rcases t with q | q
  · simp only [Matrix.fromBlocks_apply₁₁]
    obtain ⟨⟨i, k⟩, rfl⟩ := (doubleMulEquiv 4 A.dim).surjective p
    obtain ⟨⟨j, l⟩, rfl⟩ := (doubleMulEquiv 4 A.dim).surjective q
    simp only [pow4ComplexStr, Equiv.symm_apply_apply]
    by_cases hij : i = j
    · subst hij; simp
    · have hji : j ≠ i := fun h => hij h.symm
      simp [hij, hji]
  · simp
  · simp
  · simp only [Matrix.fromBlocks_apply₂₂]
    obtain ⟨⟨i, k⟩, rfl⟩ := (doubleMulEquiv 4 A.dim).surjective p
    obtain ⟨⟨j, l⟩, rfl⟩ := (doubleMulEquiv 4 A.dim).surjective q
    simp only [pow4ComplexStr, Equiv.symm_apply_apply]
    by_cases hij : i = j
    · subst hij; simp
    · have hji : j ≠ i := fun h => hij h.symm
      simp [hij, hji]

private lemma dual_zarhinSplit_complexStr_decomp (A : AbelianSchemeModel)
    (w : Fin (2 * (zarhinSplit A).dim) → ℝ) :
    zarhinDecomp A ((DualAbelianScheme (zarhinSplit A)).complexStr.mulVec w) =
      (fun i => (DualAbelianScheme A).complexStr.mulVec ((zarhinDecomp A w).1 i),
       fun j => A.complexStr.mulVec ((zarhinDecomp A w).2 j)) := by
  rw [dual_zarhinSplit_complexStr_eq]
  have hm : ∀ s : Fin (2 * (4 * A.dim)) ⊕ Fin (2 * (4 * A.dim)),
      ((AbelianSchemeModel.prodComplexStr (DualAbelianScheme A).pow4Direct A.pow4Direct).mulVec w)
        (doubleAddEquiv (4 * A.dim) (4 * A.dim) s) =
      Sum.elim
        ((pow4ComplexStr (DualAbelianScheme A)).mulVec
          (fun p => w (doubleAddEquiv (4 * A.dim) (4 * A.dim) (Sum.inl p))))
        ((pow4ComplexStr A).mulVec
          (fun p => w (doubleAddEquiv (4 * A.dim) (4 * A.dim) (Sum.inr p)))) s := by
    intro s
    dsimp only [AbelianSchemeModel.prodComplexStr, AbelianSchemeModel.pow4Direct, DualAbelianScheme]
    simp only [Matrix.mulVec, dotProduct, Matrix.reindex_apply, Matrix.submatrix_apply]
    rw [← (doubleAddEquiv (4 * A.dim) (4 * A.dim)).sum_comp, Fintype.sum_sum_type]
    simp_rw [Equiv.symm_apply_apply]
    rcases s with p | p <;> simp [Matrix.mulVec, dotProduct]
  ext1
  · ext i k
    change ((AbelianSchemeModel.prodComplexStr (DualAbelianScheme A).pow4Direct A.pow4Direct).mulVec w)
        (doubleAddEquiv (4 * A.dim) (4 * A.dim) (Sum.inl (doubleMulEquiv 4 A.dim (i, k)))) = _
    rw [hm (Sum.inl _)]
    exact pow4ComplexStr_mulVec (DualAbelianScheme A) _ i k
  · ext j l
    change ((AbelianSchemeModel.prodComplexStr (DualAbelianScheme A).pow4Direct A.pow4Direct).mulVec w)
        (doubleAddEquiv (4 * A.dim) (4 * A.dim) (Sum.inr (doubleMulEquiv 4 A.dim (j, l)))) = _
    rw [hm (Sum.inr _)]
    exact pow4ComplexStr_mulVec A _ j l

/-- **Zarhin Block Polarization Homomorphism `Λ_Z = [[λ, qᵀ], [-q, -μ]] : A⁴ × (A^∨)⁴ → (A^∨)⁴ × A⁴`**
for any polarization `P : Polarization A` of exponent `d = P.exponent ≥ 1`. -/
def zarhinPolHom {A : AbelianSchemeModel} (P : Polarization A) :
    AbelianSchemeHom (zarhinSplit A) (DualAbelianScheme (zarhinSplit A)) where
  toLinear :=
    let q := zarhinQuat (P.exponent - 1)
    { toFun := fun z =>
        let x := (zarhinDecomp A z).1
        let y := (zarhinDecomp A z).2
        zarhinBuild A
          (fun i => (P.hom.toLinear (x i) : Fin (2 * A.dim) → ℝ) + ∑ j : Fin 4, q j i • y j)
          (fun j => -(∑ i : Fin 4, q j i • x i) - P.dualInv.toLinear (y j))
      map_add' := fun z₁ z₂ => by
        have hx : (zarhinDecomp A (z₁ + z₂)).1 = (zarhinDecomp A z₁).1 + (zarhinDecomp A z₂).1 := rfl
        have hy : (zarhinDecomp A (z₁ + z₂)).2 = (zarhinDecomp A z₁).2 + (zarhinDecomp A z₂).2 := rfl
        dsimp only
        rw [hx, hy, ← zarhinBuild_linear_add]
        congr 1
        · ext i k
          simp [Pi.add_apply, map_add, smul_add, Finset.sum_add_distrib]
          ring
        · ext j l
          simp [Pi.add_apply, Finset.sum_add_distrib, smul_add, map_add]
          ring
      map_smul' := fun c z => by
        have hx : (zarhinDecomp A (c • z)).1 = c • (zarhinDecomp A z).1 := rfl
        have hy : (zarhinDecomp A (c • z)).2 = c • (zarhinDecomp A z).2 := rfl
        dsimp only
        rw [hx, hy, ← zarhinBuild_linear_smul]
        congr 1
        · ext i k
          simp only [Finset.sum_apply, Pi.smul_apply, Pi.add_apply, LinearMap.map_smul,
            ← Int.cast_smul_eq_zsmul ℝ, smul_eq_mul, Finset.mul_sum, mul_add]
          exact congrArg₂ (· + ·) rfl (Finset.sum_congr rfl fun _ _ => mul_left_comm _ _ _)
        · ext j l
          simp only [Finset.sum_apply, Pi.smul_apply, Pi.sub_apply, Pi.neg_apply,
            LinearMap.map_smul, ← Int.cast_smul_eq_zsmul ℝ, smul_eq_mul, Finset.mul_sum,
            mul_sub, mul_neg]
          exact congrArg₂ (· - ·)
            (congrArg Neg.neg (Finset.sum_congr rfl fun _ _ => mul_left_comm _ _ _)) rfl }
  maps_period z hz := by
    rw [mem_zarhinSplit_period_iff] at hz
    rw [mem_dual_zarhinSplit_period_iff]
    simp only [LinearMap.coe_mk, AddHom.coe_mk, zarhinDecomp_build]
    refine ⟨fun i => ?_, fun j => ?_⟩
    · refine Submodule.add_mem _ (P.hom.maps_period _ (hz.1 i)) ?_
      exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hz.2 j)
    · rw [sub_eq_add_neg]
      refine Submodule.add_mem _ (Submodule.neg_mem _ ?_)
        (Submodule.neg_mem _ (P.dualInv.maps_period _ (hz.2 j)))
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hz.1 i)
  comm_complexStr := by
    let q := zarhinQuat (P.exponent - 1)
    refine LinearMap.ext fun z => funext fun m => ?_
    simp only [LinearMap.comp_apply, LinearMap.coe_mk, AddHom.coe_mk, Matrix.mulVecLin_apply]
    have hL := zarhinSplit_complexStr_decomp A z
    have hR := dual_zarhinSplit_complexStr_decomp A (zarhinBuild A
      (fun i => (P.hom.toLinear ((zarhinDecomp A z).1 i) : Fin (2 * A.dim) → ℝ) +
        ∑ j : Fin 4, q j i • (zarhinDecomp A z).2 j)
      (fun j => -(∑ i : Fin 4, q j i • (zarhinDecomp A z).1 i) -
        P.dualInv.toLinear ((zarhinDecomp A z).2 j)))
    rw [zarhinDecomp_build] at hR
    have hhom : ∀ i, (P.hom.toLinear (A.complexStr.mulVec ((zarhinDecomp A z).1 i)) :
        Fin (2 * A.dim) → ℝ) =
        (DualAbelianScheme A).complexStr.mulVec (P.hom.toLinear ((zarhinDecomp A z).1 i)) := fun i =>
      LinearMap.congr_fun P.hom.comm_complexStr ((zarhinDecomp A z).1 i)
    have hinv : ∀ j, P.dualInv.toLinear ((DualAbelianScheme A).complexStr.mulVec ((zarhinDecomp A z).2 j)) =
        A.complexStr.mulVec (P.dualInv.toLinear ((zarhinDecomp A z).2 j)) := fun j =>
      LinearMap.congr_fun P.dualInv.comm_complexStr ((zarhinDecomp A z).2 j)
    have hcomb : zarhinBuild A
        (fun i => (P.hom.toLinear ((zarhinDecomp A ((zarhinSplit A).complexStr.mulVec z)).1 i) :
          Fin (2 * A.dim) → ℝ) +
          ∑ j : Fin 4, q j i • (zarhinDecomp A ((zarhinSplit A).complexStr.mulVec z)).2 j)
        (fun j => -(∑ i : Fin 4, q j i • (zarhinDecomp A ((zarhinSplit A).complexStr.mulVec z)).1 i) -
          P.dualInv.toLinear ((zarhinDecomp A ((zarhinSplit A).complexStr.mulVec z)).2 j)) =
        (DualAbelianScheme (zarhinSplit A)).complexStr.mulVec (zarhinBuild A
          (fun i => (P.hom.toLinear ((zarhinDecomp A z).1 i) : Fin (2 * A.dim) → ℝ) +
            ∑ j : Fin 4, q j i • (zarhinDecomp A z).2 j)
          (fun j => -(∑ i : Fin 4, q j i • (zarhinDecomp A z).1 i) -
            P.dualInv.toLinear ((zarhinDecomp A z).2 j))) := by
      rw [← zarhinBuild_decomp A ((DualAbelianScheme (zarhinSplit A)).complexStr.mulVec _), hR]
      congr 1
      · ext i k
        have h1 := congrFun (congrArg Prod.fst hL) i
        rw [h1, hhom i]
        have h2 : (zarhinDecomp A ((zarhinSplit A).complexStr.mulVec z)).2 =
            fun j => (DualAbelianScheme A).complexStr.mulVec ((zarhinDecomp A z).2 j) :=
          congrArg Prod.snd hL
        rw [h2]
        simp only [Matrix.mulVec_add, Matrix.mulVec_sum, ← Int.cast_smul_eq_zsmul ℝ,
          Matrix.mulVec_smul]
      · ext j l
        have h1 : (zarhinDecomp A ((zarhinSplit A).complexStr.mulVec z)).1 =
            fun i => A.complexStr.mulVec ((zarhinDecomp A z).1 i) :=
          congrArg Prod.fst hL
        have h2 := congrFun (congrArg Prod.snd hL) j
        rw [h1, h2, hinv j]
        simp only [Matrix.mulVec_sub, Matrix.mulVec_neg, Matrix.mulVec_sum,
          ← Int.cast_smul_eq_zsmul ℝ, Matrix.mulVec_smul]
    exact congrFun hcomb m

/-- **Zarhin Inverse Polarization Homomorphism `M_Z = [[μ, qᵀ], [-q, -λ]] : (A^∨)⁴ × A⁴ → A⁴ × (A^∨)⁴`**. -/
def zarhinPolInv {A : AbelianSchemeModel} (P : Polarization A) :
    AbelianSchemeHom (DualAbelianScheme (zarhinSplit A)) (zarhinSplit A) where
  toLinear :=
    let q := zarhinQuat (P.exponent - 1)
    { toFun := fun w =>
        let u := (zarhinDecomp A w).1
        let v := (zarhinDecomp A w).2
        zarhinBuild A
          (fun i => P.dualInv.toLinear (u i) + ∑ j : Fin 4, q j i • v j)
          (fun j => -(∑ i : Fin 4, q j i • u i) - (P.hom.toLinear (v j) : Fin (2 * A.dim) → ℝ))
      map_add' := fun w₁ w₂ => by
        have hu : (zarhinDecomp A (w₁ + w₂)).1 = (zarhinDecomp A w₁).1 + (zarhinDecomp A w₂).1 := rfl
        have hv : (zarhinDecomp A (w₁ + w₂)).2 = (zarhinDecomp A w₁).2 + (zarhinDecomp A w₂).2 := rfl
        dsimp only
        rw [hu, hv, ← zarhinBuild_linear_add]
        congr 1
        · ext i k
          simp [Pi.add_apply, map_add, smul_add, Finset.sum_add_distrib]
          ring
        · ext j l
          simp [Pi.add_apply, Finset.sum_add_distrib, smul_add, map_add]
          ring
      map_smul' := fun c w => by
        have hu : (zarhinDecomp A (c • w)).1 = c • (zarhinDecomp A w).1 := rfl
        have hv : (zarhinDecomp A (c • w)).2 = c • (zarhinDecomp A w).2 := rfl
        dsimp only
        rw [hu, hv, ← zarhinBuild_linear_smul]
        congr 1
        · ext i k
          simp only [Finset.sum_apply, Pi.smul_apply, Pi.add_apply, LinearMap.map_smul,
            ← Int.cast_smul_eq_zsmul ℝ, smul_eq_mul, Finset.mul_sum, mul_add]
          exact congrArg₂ (· + ·) rfl (Finset.sum_congr rfl fun _ _ => mul_left_comm _ _ _)
        · ext j l
          simp only [Finset.sum_apply, Pi.smul_apply, Pi.sub_apply, Pi.neg_apply,
            LinearMap.map_smul, ← Int.cast_smul_eq_zsmul ℝ, smul_eq_mul, Finset.mul_sum,
            mul_sub, mul_neg]
          exact congrArg₂ (· - ·)
            (congrArg Neg.neg (Finset.sum_congr rfl fun _ _ => mul_left_comm _ _ _)) rfl }
  maps_period w hw := by
    rw [mem_dual_zarhinSplit_period_iff] at hw
    rw [mem_zarhinSplit_period_iff]
    simp only [LinearMap.coe_mk, AddHom.coe_mk, zarhinDecomp_build]
    refine ⟨fun i => ?_, fun j => ?_⟩
    · refine Submodule.add_mem _ (P.dualInv.maps_period _ (hw.1 i)) ?_
      exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hw.2 j)
    · rw [sub_eq_add_neg]
      refine Submodule.add_mem _ (Submodule.neg_mem _ ?_)
        (Submodule.neg_mem _ (P.hom.maps_period _ (hw.2 j)))
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hw.1 i)
  comm_complexStr := by
    let q := zarhinQuat (P.exponent - 1)
    refine LinearMap.ext fun w => funext fun m => ?_
    simp only [LinearMap.comp_apply, LinearMap.coe_mk, AddHom.coe_mk, Matrix.mulVecLin_apply]
    have hL := dual_zarhinSplit_complexStr_decomp A w
    have hR := zarhinSplit_complexStr_decomp A (zarhinBuild A
      (fun i => P.dualInv.toLinear ((zarhinDecomp A w).1 i) + ∑ j : Fin 4, q j i • (zarhinDecomp A w).2 j)
      (fun j => -(∑ i : Fin 4, q j i • (zarhinDecomp A w).1 i) -
        (P.hom.toLinear ((zarhinDecomp A w).2 j) : Fin (2 * A.dim) → ℝ)))
    rw [zarhinDecomp_build] at hR
    have hinv : ∀ i, P.dualInv.toLinear ((DualAbelianScheme A).complexStr.mulVec ((zarhinDecomp A w).1 i)) =
        A.complexStr.mulVec (P.dualInv.toLinear ((zarhinDecomp A w).1 i)) := fun i =>
      LinearMap.congr_fun P.dualInv.comm_complexStr ((zarhinDecomp A w).1 i)
    have hhom : ∀ j, (P.hom.toLinear (A.complexStr.mulVec ((zarhinDecomp A w).2 j)) :
        Fin (2 * A.dim) → ℝ) =
        (DualAbelianScheme A).complexStr.mulVec (P.hom.toLinear ((zarhinDecomp A w).2 j)) := fun j =>
      LinearMap.congr_fun P.hom.comm_complexStr ((zarhinDecomp A w).2 j)
    have hcomb : zarhinBuild A
        (fun i => P.dualInv.toLinear ((zarhinDecomp A ((DualAbelianScheme (zarhinSplit A)).complexStr.mulVec w)).1 i) +
          ∑ j : Fin 4, q j i • (zarhinDecomp A ((DualAbelianScheme (zarhinSplit A)).complexStr.mulVec w)).2 j)
        (fun j => -(∑ i : Fin 4, q j i • (zarhinDecomp A ((DualAbelianScheme (zarhinSplit A)).complexStr.mulVec w)).1 i) -
          (P.hom.toLinear ((zarhinDecomp A ((DualAbelianScheme (zarhinSplit A)).complexStr.mulVec w)).2 j) :
            Fin (2 * A.dim) → ℝ)) =
        (zarhinSplit A).complexStr.mulVec (zarhinBuild A
          (fun i => P.dualInv.toLinear ((zarhinDecomp A w).1 i) + ∑ j : Fin 4, q j i • (zarhinDecomp A w).2 j)
          (fun j => -(∑ i : Fin 4, q j i • (zarhinDecomp A w).1 i) -
            (P.hom.toLinear ((zarhinDecomp A w).2 j) : Fin (2 * A.dim) → ℝ))) := by
      rw [← zarhinBuild_decomp A ((zarhinSplit A).complexStr.mulVec _), hR]
      congr 1
      · ext i k
        have h1 := congrFun (congrArg Prod.fst hL) i
        have h2 : (zarhinDecomp A ((DualAbelianScheme (zarhinSplit A)).complexStr.mulVec w)).2 =
            fun j => A.complexStr.mulVec ((zarhinDecomp A w).2 j) :=
          congrArg Prod.snd hL
        rw [h1, h2, hinv i]
        simp only [Matrix.mulVec_add, Matrix.mulVec_sum, ← Int.cast_smul_eq_zsmul ℝ,
          Matrix.mulVec_smul]
      · ext j l
        have h1 : (zarhinDecomp A ((DualAbelianScheme (zarhinSplit A)).complexStr.mulVec w)).1 =
            fun i => (DualAbelianScheme A).complexStr.mulVec ((zarhinDecomp A w).1 i) :=
          congrArg Prod.fst hL
        have h2 := congrFun (congrArg Prod.snd hL) j
        rw [h1, h2, hhom j]
        simp only [Matrix.mulVec_sub, Matrix.mulVec_neg, Matrix.mulVec_sum,
          ← Int.cast_smul_eq_zsmul ℝ, Matrix.mulVec_smul]
    exact congrFun hcomb m

/-- **Principal Polarization on `zarhinSplit A = A⁴ × (A^∨)⁴`** for ANY polarized `A`:
proves `M_Z ∘ Λ_Z = id`, `Λ_Z ∘ M_Z = id`, skew-symmetry `Λ_Z^∨ = -Λ_Z`, and strict
positive-definiteness of the Zarhin Riemann form via the sum-of-squares identity
`H_Z(x, λ z) = ∑_i (H_A(x_i + (qᵀ z)_i, x_i + (qᵀ z)_i) + H_A(z_i, z_i))`! -/
def zarhinPrincipalPolarizationSplit {A : AbelianSchemeModel} (P : Polarization A) :
    PrincipalPolarization (zarhinSplit A) where
  toPolarization :=
    { hom := zarhinPolHom P
      dualInv := zarhinPolInv P
      exponent := 1
      exponent_pos := Nat.one_pos
      comp_dualInv := by
        let q := zarhinQuat (P.exponent - 1)
        have hdm1 : (((P.exponent - 1 : ℕ) : ℤ) : ℝ) = (P.exponent : ℝ) - 1 := by
          have := P.exponent_pos
          rw [Int.cast_natCast, Nat.cast_sub (by omega)]; simp
        apply AbelianSchemeHom.ext
        refine LinearMap.ext fun z => funext fun m => ?_
        change (zarhinPolInv P).toLinear ((zarhinPolHom P).toLinear z) m = (((1 : ℕ) : ℤ) • z) m
        rw [Nat.cast_one, one_zsmul]
        simp only [zarhinPolInv, zarhinPolHom, LinearMap.coe_mk, AddHom.coe_mk, zarhinDecomp_build]
        let x := (zarhinDecomp A z).1
        let y := (zarhinDecomp A z).2
        have hcoord1 : (fun i => P.dualInv.toLinear (P.hom.toLinear (x i) + ∑ j : Fin 4, q j i • y j) +
            ∑ j : Fin 4, q j i • (-(∑ r : Fin 4, q j r • x r) - P.dualInv.toLinear (y j))) = x := by
          ext i k
          simp only [map_add, map_sum, map_zsmul, P.dualInv_apply_hom, smul_sub, smul_neg,
            Finset.sum_sub_distrib, Finset.sum_neg_distrib]
          have hqsum : (∑ j : Fin 4, q j i • ∑ r : Fin 4, q j r • x r) =
              ((P.exponent - 1 : ℕ) : ℤ) • x i := by
            ext l
            simp only [Finset.sum_apply, Pi.smul_apply, ← Int.cast_smul_eq_zsmul ℝ, smul_eq_mul]
            have h0 : ∑ j : Fin 4, (q j i : ℝ) * ∑ r : Fin 4, (q j r : ℝ) * x r l =
                ∑ r : Fin 4, (∑ j : Fin 4, (q j i : ℝ) * (q j r : ℝ)) * x r l := by
              simp_rw [Finset.mul_sum]
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl fun r _ => ?_
              rw [Finset.sum_mul]
              refine Finset.sum_congr rfl fun j _ => by ring
            rw [h0]
            have hqtq_entry : ∀ a r : Fin 4,
                (∑ j : Fin 4, (q j a : ℝ) * (q j r : ℝ)) =
                  if a = r then ((P.exponent - 1 : ℕ) : ℝ) else 0 := fun a r =>
              zarhinQuat_real_sum_transpose_mul (P.exponent - 1) a r
            simp_rw [hqtq_entry]
            simp
          have hqsum_k := congrFun hqsum k
          simp only [Finset.sum_apply, Pi.smul_apply, Pi.add_apply, Pi.sub_apply, Pi.neg_apply,
            ← Int.cast_smul_eq_zsmul ℝ, smul_eq_mul, hdm1] at hqsum_k ⊢
          linarith
        have hcoord2 : (fun j => -(∑ i : Fin 4, q j i • (P.hom.toLinear (x i) +
            ∑ r : Fin 4, q r i • y r)) -
            P.hom.toLinear (-(∑ i : Fin 4, q j i • x i) - P.dualInv.toLinear (y j))) = y := by
          ext j l
          simp only [smul_add, Finset.sum_add_distrib, map_sub, map_neg, map_sum, map_zsmul,
            P.hom_apply_dualInv]
          have hqsum : (∑ i : Fin 4, q j i • ∑ r : Fin 4, q r i • y r) =
              ((P.exponent - 1 : ℕ) : ℤ) • y j := by
            ext k
            simp only [Finset.sum_apply, Pi.smul_apply, ← Int.cast_smul_eq_zsmul ℝ, smul_eq_mul]
            have h0 : ∑ i : Fin 4, (q j i : ℝ) * ∑ r : Fin 4, (q r i : ℝ) * y r k =
                ∑ r : Fin 4, (∑ i : Fin 4, (q j i : ℝ) * (q r i : ℝ)) * y r k := by
              simp_rw [Finset.mul_sum]
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl fun r _ => ?_
              rw [Finset.sum_mul]
              refine Finset.sum_congr rfl fun i _ => by ring
            rw [h0]
            have hqq_entry : ∀ a r : Fin 4,
                (∑ i : Fin 4, (q a i : ℝ) * (q r i : ℝ)) =
                  if a = r then ((P.exponent - 1 : ℕ) : ℝ) else 0 := fun a r =>
              zarhinQuat_real_sum_mul_transpose (P.exponent - 1) a r
            simp_rw [hqq_entry]
            simp
          have hqsum_l := congrFun hqsum l
          simp only [Finset.sum_apply, Pi.smul_apply, Pi.add_apply, Pi.sub_apply, Pi.neg_apply,
            ← Int.cast_smul_eq_zsmul ℝ, smul_eq_mul, hdm1] at hqsum_l ⊢
          linarith
        have htot : zarhinBuild A x y m = z m := congrFun (zarhinBuild_decomp A z) m
        rw [← htot, hcoord1, hcoord2]
      dualInv_comp := by
        let q := zarhinQuat (P.exponent - 1)
        have hdm1 : (((P.exponent - 1 : ℕ) : ℤ) : ℝ) = (P.exponent : ℝ) - 1 := by
          have := P.exponent_pos
          rw [Int.cast_natCast, Nat.cast_sub (by omega)]; simp
        apply AbelianSchemeHom.ext
        refine LinearMap.ext fun w => funext fun m => ?_
        change (zarhinPolHom P).toLinear ((zarhinPolInv P).toLinear w) m = (((1 : ℕ) : ℤ) • w) m
        rw [Nat.cast_one, one_zsmul]
        simp only [zarhinPolHom, zarhinPolInv, LinearMap.coe_mk, AddHom.coe_mk, zarhinDecomp_build]
        let u := (zarhinDecomp A w).1
        let v := (zarhinDecomp A w).2
        have hcoord1 : (fun i => P.hom.toLinear (P.dualInv.toLinear (u i) + ∑ j : Fin 4, q j i • v j) +
            ∑ j : Fin 4, q j i • (-(∑ r : Fin 4, q j r • u r) - P.hom.toLinear (v j))) = u := by
          ext i k
          simp only [map_add, map_sum, map_zsmul, P.hom_apply_dualInv, smul_sub, smul_neg,
            Finset.sum_sub_distrib, Finset.sum_neg_distrib]
          have hqsum : (∑ j : Fin 4, q j i • ∑ r : Fin 4, q j r • u r) =
              ((P.exponent - 1 : ℕ) : ℤ) • u i := by
            ext l
            simp only [Finset.sum_apply, Pi.smul_apply, ← Int.cast_smul_eq_zsmul ℝ, smul_eq_mul]
            have h0 : ∑ j : Fin 4, (q j i : ℝ) * ∑ r : Fin 4, (q j r : ℝ) * u r l =
                ∑ r : Fin 4, (∑ j : Fin 4, (q j i : ℝ) * (q j r : ℝ)) * u r l := by
              simp_rw [Finset.mul_sum]
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl fun r _ => ?_
              rw [Finset.sum_mul]
              refine Finset.sum_congr rfl fun j _ => by ring
            rw [h0]
            have hqtq_entry : ∀ a r : Fin 4,
                (∑ j : Fin 4, (q j a : ℝ) * (q j r : ℝ)) =
                  if a = r then ((P.exponent - 1 : ℕ) : ℝ) else 0 := fun a r =>
              zarhinQuat_real_sum_transpose_mul (P.exponent - 1) a r
            simp_rw [hqtq_entry]
            simp
          have hqsum_k := congrFun hqsum k
          simp only [Finset.sum_apply, Pi.smul_apply, Pi.add_apply, Pi.sub_apply, Pi.neg_apply,
            ← Int.cast_smul_eq_zsmul ℝ, smul_eq_mul, hdm1] at hqsum_k ⊢
          linarith
        have hcoord2 : (fun j => -(∑ i : Fin 4, q j i • (P.dualInv.toLinear (u i) +
            ∑ r : Fin 4, q r i • v r)) -
            P.dualInv.toLinear (-(∑ i : Fin 4, q j i • u i) - P.hom.toLinear (v j))) = v := by
          ext j l
          simp only [smul_add, Finset.sum_add_distrib, map_sub, map_neg, map_sum, map_zsmul,
            P.dualInv_apply_hom]
          have hqsum : (∑ i : Fin 4, q j i • ∑ r : Fin 4, q r i • v r) =
              ((P.exponent - 1 : ℕ) : ℤ) • v j := by
            ext k
            simp only [Finset.sum_apply, Pi.smul_apply, ← Int.cast_smul_eq_zsmul ℝ, smul_eq_mul]
            have h0 : ∑ i : Fin 4, (q j i : ℝ) * ∑ r : Fin 4, (q r i : ℝ) * v r k =
                ∑ r : Fin 4, (∑ i : Fin 4, (q j i : ℝ) * (q r i : ℝ)) * v r k := by
              simp_rw [Finset.mul_sum]
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl fun r _ => ?_
              rw [Finset.sum_mul]
              refine Finset.sum_congr rfl fun i _ => by ring
            rw [h0]
            have hqq_entry : ∀ a r : Fin 4,
                (∑ i : Fin 4, (q a i : ℝ) * (q r i : ℝ)) =
                  if a = r then ((P.exponent - 1 : ℕ) : ℝ) else 0 := fun a r =>
              zarhinQuat_real_sum_mul_transpose (P.exponent - 1) a r
            simp_rw [hqq_entry]
            simp
          have hqsum_l := congrFun hqsum l
          simp only [Finset.sum_apply, Pi.smul_apply, Pi.add_apply, Pi.sub_apply, Pi.neg_apply,
            ← Int.cast_smul_eq_zsmul ℝ, smul_eq_mul, hdm1] at hqsum_l ⊢
          linarith
        have htot : zarhinBuild A u v m = w m := congrFun (zarhinBuild_decomp A w) m
        rw [← htot, hcoord1, hcoord2]
      skewSymmetric := fun z₁ z₂ => by
        let q := zarhinQuat (P.exponent - 1)
        change z₁ ⬝ᵥ (zarhinPolHom P).toLinear z₂ = -(z₂ ⬝ᵥ (zarhinPolHom P).toLinear z₁)
        rw [zarhin_dotProduct, zarhin_dotProduct]
        simp only [zarhinPolHom, LinearMap.coe_mk, AddHom.coe_mk, zarhinDecomp_build]
        set x₁ := (zarhinDecomp A z₁).1
        set y₁ := (zarhinDecomp A z₁).2
        set x₂ := (zarhinDecomp A z₂).1
        set y₂ := (zarhinDecomp A z₂).2
        have h1 : (∑ i : Fin 4, x₁ i ⬝ᵥ (P.hom.toLinear (x₂ i) + ∑ j : Fin 4, q j i • y₂ j)) =
            (∑ i : Fin 4, x₁ i ⬝ᵥ P.hom.toLinear (x₂ i)) +
              ∑ i : Fin 4, ∑ j : Fin 4, (q j i : ℝ) * (x₁ i ⬝ᵥ y₂ j) := by
          simp_rw [dotProduct_add, dotProduct_sum, ← Int.cast_smul_eq_zsmul ℝ, dotProduct_smul,
            smul_eq_mul]
          rw [Finset.sum_add_distrib]
        have h2 : (∑ j : Fin 4, y₁ j ⬝ᵥ (-(∑ i : Fin 4, q j i • x₂ i) - P.dualInv.toLinear (y₂ j))) =
            -(∑ j : Fin 4, ∑ i : Fin 4, (q j i : ℝ) * (y₁ j ⬝ᵥ x₂ i)) -
              ∑ j : Fin 4, y₁ j ⬝ᵥ P.dualInv.toLinear (y₂ j) := by
          simp_rw [dotProduct_sub, dotProduct_neg, dotProduct_sum, ← Int.cast_smul_eq_zsmul ℝ,
            dotProduct_smul, smul_eq_mul]
          rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib]
        have h1' : (∑ i : Fin 4, x₂ i ⬝ᵥ (P.hom.toLinear (x₁ i) + ∑ j : Fin 4, q j i • y₁ j)) =
            (∑ i : Fin 4, x₂ i ⬝ᵥ P.hom.toLinear (x₁ i)) +
              ∑ i : Fin 4, ∑ j : Fin 4, (q j i : ℝ) * (x₂ i ⬝ᵥ y₁ j) := by
          simp_rw [dotProduct_add, dotProduct_sum, ← Int.cast_smul_eq_zsmul ℝ, dotProduct_smul,
            smul_eq_mul]
          rw [Finset.sum_add_distrib]
        have h2' : (∑ j : Fin 4, y₂ j ⬝ᵥ (-(∑ i : Fin 4, q j i • x₁ i) - P.dualInv.toLinear (y₁ j))) =
            -(∑ j : Fin 4, ∑ i : Fin 4, (q j i : ℝ) * (y₂ j ⬝ᵥ x₁ i)) -
              ∑ j : Fin 4, y₂ j ⬝ᵥ P.dualInv.toLinear (y₁ j) := by
          simp_rw [dotProduct_sub, dotProduct_neg, dotProduct_sum, ← Int.cast_smul_eq_zsmul ℝ,
            dotProduct_smul, smul_eq_mul]
          rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib]
        rw [h1, h2, h1', h2']
        have hs1 : (∑ i : Fin 4, x₁ i ⬝ᵥ P.hom.toLinear (x₂ i)) =
            -(∑ i : Fin 4, x₂ i ⬝ᵥ P.hom.toLinear (x₁ i)) := by
          rw [← Finset.sum_neg_distrib]
          exact Finset.sum_congr rfl fun i _ => P.skewSymmetric (x₁ i) (x₂ i)
        have hs2 : (∑ j : Fin 4, y₁ j ⬝ᵥ P.dualInv.toLinear (y₂ j)) =
            -(∑ j : Fin 4, y₂ j ⬝ᵥ P.dualInv.toLinear (y₁ j)) := by
          rw [← Finset.sum_neg_distrib]
          exact Finset.sum_congr rfl fun j _ => P.dualInv_skewSymmetric (y₁ j) (y₂ j)
        have hc1 : (∑ i : Fin 4, ∑ j : Fin 4, (q j i : ℝ) * (x₁ i ⬝ᵥ y₂ j)) =
            ∑ j : Fin 4, ∑ i : Fin 4, (q j i : ℝ) * (y₂ j ⬝ᵥ x₁ i) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
          rw [dotProduct_comm]
        have hc2 : (∑ j : Fin 4, ∑ i : Fin 4, (q j i : ℝ) * (y₁ j ⬝ᵥ x₂ i)) =
            ∑ i : Fin 4, ∑ j : Fin 4, (q j i : ℝ) * (x₂ i ⬝ᵥ y₁ j) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
          rw [dotProduct_comm]
        rw [hs1, hs2, hc1, hc2]
        ring
      posDef := fun w hw => by
        let q := zarhinQuat (P.exponent - 1)
        have hqq : q * qᵀ = ((P.exponent - 1 : ℕ) : ℤ) • 1 := zarhinQuat_mul_transpose _
        have hd_pos : (0 : ℝ) < (P.exponent : ℝ) := Nat.cast_pos.mpr P.exponent_pos
        have hd_ne : (P.exponent : ℝ) ≠ 0 := hd_pos.ne'
        have hdm1 : (((P.exponent - 1 : ℕ) : ℤ) : ℝ) = (P.exponent : ℝ) - 1 := by
          have := P.exponent_pos
          rw [Int.cast_natCast, Nat.cast_sub (by omega)]; simp
        let x := (zarhinDecomp A w).1
        let y := (zarhinDecomp A w).2
        let z : Fin 4 → Fin (2 * A.dim) → ℝ := fun j => (P.exponent : ℝ)⁻¹ • P.dualInv.toLinear (y j)
        have hy_eq : ∀ j, y j = P.hom.toLinear (z j) := fun j => by
          simp only [z, map_smul, P.hom_apply_dualInv, smul_smul, inv_mul_cancel₀ hd_ne, one_smul]
        have hquad : w ⬝ᵥ (zarhinPolHom P).toLinear ((zarhinSplit A).complexStr.mulVec w) =
            ∑ i : Fin 4, (P.riemannForm (x i + ∑ j : Fin 4, q j i • z j)
              (x i + ∑ j : Fin 4, q j i • z j) + P.riemannForm (z i) (z i)) := by
          rw [zarhin_dotProduct]
          simp only [zarhinPolHom, LinearMap.coe_mk, AddHom.coe_mk, zarhinDecomp_build]
          rw [zarhinSplit_complexStr_decomp]
          have hhomJ : ∀ j, (DualAbelianScheme A).complexStr.mulVec (y j) =
              P.hom.toLinear (A.complexStr.mulVec (z j)) := fun j => by
            rw [hy_eq j]
            exact (LinearMap.congr_fun P.hom.comm_complexStr (z j)).symm
          have hT1 : (∑ i : Fin 4, x i ⬝ᵥ (P.hom.toLinear (A.complexStr.mulVec (x i)) +
              ∑ j : Fin 4, q j i • ((DualAbelianScheme A).complexStr.mulVec (y j)))) =
              (∑ i : Fin 4, P.riemannForm (x i) (x i)) +
                ∑ i : Fin 4, ∑ j : Fin 4, (q j i : ℝ) * P.riemannForm (x i) (z j) := by
            simp_rw [dotProduct_add, dotProduct_sum, ← Int.cast_smul_eq_zsmul ℝ, dotProduct_smul,
              smul_eq_mul, hhomJ]
            rw [Finset.sum_add_distrib]
            rfl
          have hT2 : (∑ j : Fin 4, y j ⬝ᵥ (-(∑ i : Fin 4, q j i • A.complexStr.mulVec (x i)) -
              P.dualInv.toLinear ((DualAbelianScheme A).complexStr.mulVec (y j)))) =
              (∑ i : Fin 4, ∑ j : Fin 4, (q j i : ℝ) * P.riemannForm (x i) (z j)) +
                (P.exponent : ℝ) * ∑ j : Fin 4, P.riemannForm (z j) (z j) := by
            have he1 : ∀ j i, y j ⬝ᵥ (-(q j i • A.complexStr.mulVec (x i))) =
                (q j i : ℝ) * P.riemannForm (x i) (z j) := fun j i => by
              rw [hy_eq j, dotProduct_neg, ← Int.cast_smul_eq_zsmul ℝ, dotProduct_smul,
                smul_eq_mul, dotProduct_comm, P.skewSymmetric (A.complexStr.mulVec (x i)) (z j)]
              have hs := P.riemannForm_symm (z j) (x i)
              have hs' : P.riemannForm (z j) (x i) = z j ⬝ᵥ P.hom.toLinear (A.complexStr.mulVec (x i)) := rfl
              rw [← hs', hs]
              ring
            have he2 : ∀ j, y j ⬝ᵥ (-(P.dualInv.toLinear ((DualAbelianScheme A).complexStr.mulVec (y j)))) =
                (P.exponent : ℝ) * P.riemannForm (z j) (z j) := fun j => by
              rw [hy_eq j, dotProduct_neg, P.dualInv_complexStr_hom,
                dotProduct_smul, smul_eq_mul, dotProduct_comm,
                P.skewSymmetric (A.complexStr.mulVec (z j)) (z j)]
              have hs' : P.riemannForm (z j) (z j) = z j ⬝ᵥ P.hom.toLinear (A.complexStr.mulVec (z j)) := rfl
              rw [← hs']
              ring
            have hstep : ∑ j : Fin 4, y j ⬝ᵥ (-(∑ i : Fin 4, q j i • A.complexStr.mulVec (x i)) -
                P.dualInv.toLinear ((DualAbelianScheme A).complexStr.mulVec (y j))) =
                ∑ j : Fin 4, ((∑ i : Fin 4, (q j i : ℝ) * P.riemannForm (x i) (z j)) +
                  (P.exponent : ℝ) * P.riemannForm (z j) (z j)) := by
              refine Finset.sum_congr rfl fun j _ => ?_
              rw [sub_eq_add_neg, dotProduct_add, he2 j, ← Finset.sum_neg_distrib, dotProduct_sum]
              congr 1
              refine Finset.sum_congr rfl fun i _ => ?_
              exact he1 j i
            rw [hstep, Finset.sum_add_distrib, Finset.mul_sum]
            congr 1
            exact Finset.sum_comm
          have hT3 : ∑ i : Fin 4, (P.riemannForm (x i + ∑ j : Fin 4, q j i • z j)
                (x i + ∑ j : Fin 4, q j i • z j) + P.riemannForm (z i) (z i)) =
              (∑ i : Fin 4, P.riemannForm (x i) (x i)) +
                2 * (∑ i : Fin 4, ∑ j : Fin 4, (q j i : ℝ) * P.riemannForm (x i) (z j)) +
                (P.exponent : ℝ) * ∑ j : Fin 4, P.riemannForm (z j) (z j) := by
            have hcross : ∀ i : Fin 4, P.riemannForm (x i) (∑ j : Fin 4, q j i • z j) =
                ∑ j : Fin 4, (q j i : ℝ) * P.riemannForm (x i) (z j) := fun i => by
              rw [P.riemannForm_symm]
              have hsum : ∀ (s : Finset (Fin 4)) (f : Fin 4 → Fin (2 * A.dim) → ℝ),
                  P.riemannForm (∑ j ∈ s, f j) (x i) = ∑ j ∈ s, P.riemannForm (f j) (x i) := by
                intro s f
                classical
                induction s using Finset.induction_on with
                | empty => simp [Polarization.riemannForm]
                | insert a s ha ih =>
                  rw [Finset.sum_insert ha, Finset.sum_insert ha, P.riemannForm_add_left, ih]
              rw [hsum]
              refine Finset.sum_congr rfl fun j _ => ?_
              rw [← Int.cast_smul_eq_zsmul ℝ, P.riemannForm_smul_left, P.riemannForm_symm]
            have hsqsum : ∑ i : Fin 4, P.riemannForm (∑ j : Fin 4, q j i • z j)
                  (∑ r : Fin 4, q r i • z r) =
                ((P.exponent : ℝ) - 1) * ∑ j : Fin 4, P.riemannForm (z j) (z j) := by
              have hbil : ∀ i : Fin 4, P.riemannForm (∑ j : Fin 4, q j i • z j)
                    (∑ r : Fin 4, q r i • z r) =
                  ∑ j : Fin 4, ∑ r : Fin 4, (q j i : ℝ) * (q r i : ℝ) * P.riemannForm (z j) (z r) := by
                intro i
                have hsumL : ∀ (s : Finset (Fin 4)) (f : Fin 4 → Fin (2 * A.dim) → ℝ) v,
                    P.riemannForm (∑ j ∈ s, f j) v = ∑ j ∈ s, P.riemannForm (f j) v := by
                  intro s f v
                  classical
                  induction s using Finset.induction_on with
                  | empty => simp [Polarization.riemannForm]
                  | insert a s ha ih =>
                    rw [Finset.sum_insert ha, Finset.sum_insert ha, P.riemannForm_add_left, ih]
                have hsumR : ∀ (s : Finset (Fin 4)) u (f : Fin 4 → Fin (2 * A.dim) → ℝ),
                    P.riemannForm u (∑ r ∈ s, f r) = ∑ r ∈ s, P.riemannForm u (f r) := by
                  intro s u f
                  rw [P.riemannForm_symm, hsumL]
                  refine Finset.sum_congr rfl fun r _ => P.riemannForm_symm _ _
                rw [hsumL]
                refine Finset.sum_congr rfl fun j _ => ?_
                rw [hsumR]
                refine Finset.sum_congr rfl fun r _ => ?_
                rw [← Int.cast_smul_eq_zsmul ℝ, ← Int.cast_smul_eq_zsmul ℝ,
                  P.riemannForm_smul_left, P.riemannForm_smul_right, mul_assoc]
              simp_rw [hbil]
              rw [Finset.sum_comm]
              have hswap : (∑ j : Fin 4, ∑ i : Fin 4, ∑ r : Fin 4,
                    (q j i : ℝ) * (q r i : ℝ) * P.riemannForm (z j) (z r)) =
                  ∑ j : Fin 4, ∑ r : Fin 4, (∑ i : Fin 4, (q j i : ℝ) * (q r i : ℝ)) *
                    P.riemannForm (z j) (z r) := by
                refine Finset.sum_congr rfl fun j _ => ?_
                rw [Finset.sum_comm]
                refine Finset.sum_congr rfl fun r _ => ?_
                rw [Finset.sum_mul]
              rw [hswap]
              have hqq_entry : ∀ a r : Fin 4,
                  (∑ i : Fin 4, (q a i : ℝ) * (q r i : ℝ)) =
                    if a = r then (P.exponent : ℝ) - 1 else 0 := fun a r => by
                dsimp only [q]
                rw [zarhinQuat_real_sum_mul_transpose, Nat.cast_sub P.exponent_pos]
                simp
              simp_rw [hqq_entry]
              simp [Finset.mul_sum]
            have hexp : ∀ i : Fin 4, P.riemannForm (x i + ∑ j : Fin 4, q j i • z j)
                  (x i + ∑ j : Fin 4, q j i • z j) =
                P.riemannForm (x i) (x i) +
                  2 * P.riemannForm (x i) (∑ j : Fin 4, q j i • z j) +
                  P.riemannForm (∑ j : Fin 4, q j i • z j) (∑ j : Fin 4, q j i • z j) := by
              intro i
              rw [P.riemannForm_add_left, P.riemannForm_add_right, P.riemannForm_add_right,
                P.riemannForm_symm (∑ j : Fin 4, q j i • z j) (x i)]
              ring
            simp_rw [hexp, hcross]
            rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
              ← Finset.mul_sum, hsqsum]
            ring
          rw [hT1, hT2, hT3]
          ring
        rw [hquad]
        have hnonneg : ∀ i : Fin 4, 0 ≤ P.riemannForm (x i + ∑ j : Fin 4, q j i • z j)
              (x i + ∑ j : Fin 4, q j i • z j) + P.riemannForm (z i) (z i) := fun i =>
          add_nonneg (P.riemannForm_nonneg _) (P.riemannForm_nonneg _)
        by_cases hz0 : ∃ j, z j ≠ 0
        · obtain ⟨j, hj⟩ := hz0
          exact Finset.sum_pos' (fun i _ => hnonneg i)
            ⟨j, Finset.mem_univ j, add_pos_of_nonneg_of_pos (P.riemannForm_nonneg _) (P.riemannForm_pos hj)⟩
        · push Not at hz0
          have hy0 : ∀ j, y j = 0 := fun j => by rw [hy_eq j, hz0 j, map_zero]
          have hx0 : ∃ i, x i ≠ 0 := by
            by_contra hxall
            push Not at hxall
            apply hw
            rw [← zarhinBuild_decomp A w]
            have hx_eq : x = 0 := funext hxall
            have hy_eq0 : y = 0 := funext hy0
            change zarhinBuild A x y = 0
            rw [hx_eq, hy_eq0]
            ext m
            simp only [zarhinBuild]
            cases (doubleAddEquiv (4 * A.dim) (4 * A.dim)).symm m <;> simp
          obtain ⟨i, hi⟩ := hx0
          have hterm_pos : 0 < P.riemannForm (x i + ∑ j : Fin 4, q j i • z j)
              (x i + ∑ j : Fin 4, q j i • z j) + P.riemannForm (z i) (z i) := by
            have hsum0 : (∑ j : Fin 4, q j i • z j) = 0 := by
              refine Finset.sum_eq_zero fun j _ => ?_
              rw [hz0 j, smul_zero]
            rw [hsum0, add_zero]
            exact add_pos_of_pos_of_nonneg (P.riemannForm_pos hi) (P.riemannForm_nonneg _)
          exact Finset.sum_pos' (fun k _ => hnonneg k) ⟨i, Finset.mem_univ i, hterm_pos⟩ }
  exponent_eq_one := rfl

/-- Canonical projection `(A.prod B) → A`. -/
def prodFst (A B : AbelianSchemeModel) : AbelianSchemeHom (A.prod B) A where
  toLinear :=
    { toFun := fun z i => z (doubleAddEquiv A.dim B.dim (Sum.inl i))
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  maps_period _ hz := hz.1
  comm_complexStr := by
    refine LinearMap.ext fun z => funext fun i => ?_
    simp only [LinearMap.comp_apply, LinearMap.coe_mk, AddHom.coe_mk, Matrix.mulVecLin_apply,
      Matrix.mulVec, dotProduct, AbelianSchemeModel.prodComplexStr]
    rw [← (doubleAddEquiv A.dim B.dim).sum_comp, Fintype.sum_sum_type]
    simp

/-- Canonical projection `(A.prod B) → B`. -/
def prodSnd (A B : AbelianSchemeModel) : AbelianSchemeHom (A.prod B) B where
  toLinear :=
    { toFun := fun z j => z (doubleAddEquiv A.dim B.dim (Sum.inr j))
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  maps_period _ hz := hz.2
  comm_complexStr := by
    refine LinearMap.ext fun z => funext fun j => ?_
    simp only [LinearMap.comp_apply, LinearMap.coe_mk, AddHom.coe_mk, Matrix.mulVecLin_apply,
      Matrix.mulVec, dotProduct, AbelianSchemeModel.prodComplexStr]
    rw [← (doubleAddEquiv A.dim B.dim).sum_comp, Fintype.sum_sum_type]
    simp

/-- Universal product pairing `⟨φ, ψ⟩ : C → A.prod B`. -/
def prodLift {C A B : AbelianSchemeModel} (φ : AbelianSchemeHom C A) (ψ : AbelianSchemeHom C B) :
    AbelianSchemeHom C (A.prod B) where
  toLinear :=
    { toFun := fun c k =>
        Sum.elim (φ.toLinear c) (ψ.toLinear c) ((doubleAddEquiv A.dim B.dim).symm k)
      map_add' := fun c₁ c₂ => by
        ext k
        simp only [map_add, Pi.add_apply]
        cases (doubleAddEquiv A.dim B.dim).symm k <;> simp
      map_smul' := fun r c => by
        ext k
        simp only [map_smul, Pi.smul_apply, RingHom.id_apply]
        cases (doubleAddEquiv A.dim B.dim).symm k <;> simp }
  maps_period c hc := by
    refine ⟨?_, ?_⟩
    · simpa using φ.maps_period c hc
    · simpa using ψ.maps_period c hc
  comm_complexStr := by
    refine LinearMap.ext fun c => funext fun k => ?_
    obtain ⟨s, rfl⟩ := (doubleAddEquiv A.dim B.dim).surjective k
    have h1 := LinearMap.congr_fun φ.comm_complexStr c
    have h2 := LinearMap.congr_fun ψ.comm_complexStr c
    simp only [LinearMap.comp_apply, LinearMap.coe_mk, AddHom.coe_mk, Matrix.mulVecLin_apply,
      Equiv.symm_apply_apply] at h1 h2 ⊢
    change Sum.elim (φ.toLinear (C.complexStr.mulVec c)) (ψ.toLinear (C.complexStr.mulVec c)) s =
      ((AbelianSchemeModel.prodComplexStr A B).mulVec _ ) (doubleAddEquiv A.dim B.dim s)
    simp only [Matrix.mulVec, dotProduct, AbelianSchemeModel.prodComplexStr, Matrix.reindex_apply,
      Matrix.submatrix_apply]
    rw [← (doubleAddEquiv A.dim B.dim).sum_comp, Fintype.sum_sum_type]
    simp_rw [Equiv.symm_apply_apply]
    rcases s with i | j
    · simpa [Matrix.mulVec, dotProduct] using congrFun h1 i
    · simpa [Matrix.mulVec, dotProduct] using congrFun h2 j

/-- Universal 4-tuple pairing `C → A.pow4Direct`. -/
private def pow4DirectLift {C A : AbelianSchemeModel} (f : Fin 4 → AbelianSchemeHom C A) :
    AbelianSchemeHom C A.pow4Direct where
  toLinear :=
    { toFun := fun c m =>
        let p := (doubleMulEquiv 4 A.dim).symm m
        (f p.1).toLinear c p.2
      map_add' := fun c₁ c₂ => by
        ext m; dsimp only; rw [map_add]; rfl
      map_smul' := fun r c => by
        ext m; dsimp only; rw [map_smul]; rfl }
  maps_period c hc i := by
    simpa using (f i).maps_period c hc
  comm_complexStr := by
    refine LinearMap.ext fun c => funext fun m => ?_
    obtain ⟨⟨i, k⟩, rfl⟩ := (doubleMulEquiv 4 A.dim).surjective m
    have hi := LinearMap.congr_fun (f i).comm_complexStr c
    simp only [LinearMap.comp_apply, LinearMap.coe_mk, AddHom.coe_mk, Matrix.mulVecLin_apply,
      Equiv.symm_apply_apply] at hi ⊢
    change (f i).toLinear (C.complexStr.mulVec c) k =
      ((pow4ComplexStr A).mulVec _) (doubleMulEquiv 4 A.dim (i, k))
    rw [pow4ComplexStr_mulVec]
    simpa using congrFun hi k

private def pow4DirectProj (A : AbelianSchemeModel) (i : Fin 4) :
    AbelianSchemeHom A.pow4Direct A where
  toLinear :=
    { toFun := fun x k => x (doubleMulEquiv 4 A.dim (i, k))
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  maps_period _ hx := hx i
  comm_complexStr := by
    refine LinearMap.ext fun x => funext fun k => ?_
    change (pow4ComplexStr A).mulVec x (doubleMulEquiv 4 A.dim (i, k)) = _
    rw [pow4ComplexStr_mulVec]; rfl

@[simp] private lemma prodFst_prodLift {C A B : AbelianSchemeModel}
    (φ : AbelianSchemeHom C A) (ψ : AbelianSchemeHom C B) (c : Fin (2 * C.dim) → ℝ) :
    (prodFst A B).toLinear ((prodLift φ ψ).toLinear c) = φ.toLinear c := by
  ext i; simp [prodFst, prodLift]

@[simp] private lemma prodSnd_prodLift {C A B : AbelianSchemeModel}
    (φ : AbelianSchemeHom C A) (ψ : AbelianSchemeHom C B) (c : Fin (2 * C.dim) → ℝ) :
    (prodSnd A B).toLinear ((prodLift φ ψ).toLinear c) = ψ.toLinear c := by
  ext j; simp [prodSnd, prodLift]

@[simp] private lemma pow4DirectProj_pow4DirectLift {C A : AbelianSchemeModel}
    (f : Fin 4 → AbelianSchemeHom C A) (i : Fin 4) (c : Fin (2 * C.dim) → ℝ) :
    (pow4DirectProj A i).toLinear ((pow4DirectLift f).toLinear c) = (f i).toLinear c := by
  ext k; simp [pow4DirectProj, pow4DirectLift]

private lemma prod_eq_of_fst_snd (X Y : AbelianSchemeModel)
    (x y : Fin (2 * (X.prod Y).dim) → ℝ)
    (h1 : (prodFst X Y).toLinear x = (prodFst X Y).toLinear y)
    (h2 : (prodSnd X Y).toLinear x = (prodSnd X Y).toLinear y) : x = y := by
  ext k
  obtain ⟨s, rfl⟩ := (doubleAddEquiv X.dim Y.dim).surjective k
  rcases s with i | j
  · exact congrFun h1 i
  · exact congrFun h2 j

private lemma pow4Direct_eq_of_proj (A : AbelianSchemeModel)
    (x y : Fin (2 * A.pow4Direct.dim) → ℝ)
    (h : ∀ i : Fin 4, (pow4DirectProj A i).toLinear x = (pow4DirectProj A i).toLinear y) :
    x = y := by
  ext m
  obtain ⟨⟨i, k⟩, rfl⟩ := (doubleMulEquiv 4 A.dim).surjective m
  exact congrFun (h i) k

private def coord4 {α : Type*} (p₃ p₂ p₁ p₀ : α) : Fin 4 → α
  | 0 => p₃
  | 1 => p₂
  | 2 => p₁
  | 3 => p₀

@[simp] private lemma coord4_0 {α : Type*} (p₃ p₂ p₁ p₀ : α) : coord4 p₃ p₂ p₁ p₀ 0 = p₃ := rfl
@[simp] private lemma coord4_1 {α : Type*} (p₃ p₂ p₁ p₀ : α) : coord4 p₃ p₂ p₁ p₀ 1 = p₂ := rfl
@[simp] private lemma coord4_2 {α : Type*} (p₃ p₂ p₁ p₀ : α) : coord4 p₃ p₂ p₁ p₀ 2 = p₁ := rfl
@[simp] private lemma coord4_3 {α : Type*} (p₃ p₂ p₁ p₀ : α) : coord4 p₃ p₂ p₁ p₀ 3 = p₀ := rfl

private def pow4Lift4 {C A : AbelianSchemeModel}
    (f0 f1 f2 f3 : AbelianSchemeHom C A) : AbelianSchemeHom C A.pow4Direct :=
  pow4DirectLift (coord4 f0 f1 f2 f3)

@[simp] private lemma pow4DirectProj_pow4Lift4_0 {C A : AbelianSchemeModel}
    (f0 f1 f2 f3 : AbelianSchemeHom C A) (c : Fin (2 * C.dim) → ℝ) :
    (pow4DirectProj A 0).toLinear ((pow4Lift4 f0 f1 f2 f3).toLinear c) = f0.toLinear c := by
  simpa [pow4Lift4] using pow4DirectProj_pow4DirectLift (coord4 f0 f1 f2 f3) 0 c

@[simp] private lemma pow4DirectProj_pow4Lift4_1 {C A : AbelianSchemeModel}
    (f0 f1 f2 f3 : AbelianSchemeHom C A) (c : Fin (2 * C.dim) → ℝ) :
    (pow4DirectProj A 1).toLinear ((pow4Lift4 f0 f1 f2 f3).toLinear c) = f1.toLinear c := by
  simpa [pow4Lift4] using pow4DirectProj_pow4DirectLift (coord4 f0 f1 f2 f3) 1 c

@[simp] private lemma pow4DirectProj_pow4Lift4_2 {C A : AbelianSchemeModel}
    (f0 f1 f2 f3 : AbelianSchemeHom C A) (c : Fin (2 * C.dim) → ℝ) :
    (pow4DirectProj A 2).toLinear ((pow4Lift4 f0 f1 f2 f3).toLinear c) = f2.toLinear c := by
  simpa [pow4Lift4] using pow4DirectProj_pow4DirectLift (coord4 f0 f1 f2 f3) 2 c

@[simp] private lemma pow4DirectProj_pow4Lift4_3 {C A : AbelianSchemeModel}
    (f0 f1 f2 f3 : AbelianSchemeHom C A) (c : Fin (2 * C.dim) → ℝ) :
    (pow4DirectProj A 3).toLinear ((pow4Lift4 f0 f1 f2 f3).toLinear c) = f3.toLinear c := by
  simpa [pow4Lift4] using pow4DirectProj_pow4DirectLift (coord4 f0 f1 f2 f3) 3 c

private lemma pow4Direct_eq_of_proj4 (A : AbelianSchemeModel)
    (x y : Fin (2 * A.pow4Direct.dim) → ℝ)
    (h0 : (pow4DirectProj A 0).toLinear x = (pow4DirectProj A 0).toLinear y)
    (h1 : (pow4DirectProj A 1).toLinear x = (pow4DirectProj A 1).toLinear y)
    (h2 : (pow4DirectProj A 2).toLinear x = (pow4DirectProj A 2).toLinear y)
    (h3 : (pow4DirectProj A 3).toLinear x = (pow4DirectProj A 3).toLinear y) :
    x = y := by
  ext m
  obtain ⟨⟨i, k⟩, rfl⟩ := (doubleMulEquiv 4 A.dim).surjective m
  fin_cases i
  · exact congrFun h0 k
  · exact congrFun h1 k
  · exact congrFun h2 k
  · exact congrFun h3 k

/-- Canonical isomorphism `(A × A^∨)^4 ≃ A⁴ × (A^∨)⁴ = zarhinSplit A`. -/
def zarhinFourFoldIso (A : AbelianSchemeModel) :
    AbelianSchemeIso ((A.prod (DualAbelianScheme A)).pow 4) (zarhinSplit A) :=
  let B := A.prod (DualAbelianScheme A)
  let p0 : AbelianSchemeHom (B.pow 4) B :=
    prodSnd (B.pow 3) B
  let p1 : AbelianSchemeHom (B.pow 4) B :=
    (prodSnd (B.pow 2) B).comp (prodFst (B.pow 3) B)
  let p2 : AbelianSchemeHom (B.pow 4) B :=
    (prodSnd (B.pow 1) B).comp ((prodFst (B.pow 2) B).comp (prodFst (B.pow 3) B))
  let p3 : AbelianSchemeHom (B.pow 4) B :=
    (prodSnd AbelianSchemeModel.trivial B).comp
      ((prodFst (B.pow 1) B).comp ((prodFst (B.pow 2) B).comp (prodFst (B.pow 3) B)))
  let toH : AbelianSchemeHom (B.pow 4) (zarhinSplit A) :=
    prodLift
      (pow4Lift4
        ((prodFst A (DualAbelianScheme A)).comp p3)
        ((prodFst A (DualAbelianScheme A)).comp p2)
        ((prodFst A (DualAbelianScheme A)).comp p1)
        ((prodFst A (DualAbelianScheme A)).comp p0))
      (pow4Lift4
        ((prodSnd A (DualAbelianScheme A)).comp p3)
        ((prodSnd A (DualAbelianScheme A)).comp p2)
        ((prodSnd A (DualAbelianScheme A)).comp p1)
        ((prodSnd A (DualAbelianScheme A)).comp p0))
  let qA := pow4DirectProj A
  let qD := pow4DirectProj (DualAbelianScheme A)
  let mkB (i : Fin 4) : AbelianSchemeHom (zarhinSplit A) B :=
    prodLift
      ((qA i).comp (prodFst A.pow4Direct (DualAbelianScheme A).pow4Direct))
      ((qD i).comp (prodSnd A.pow4Direct (DualAbelianScheme A).pow4Direct))
  let zTriv : AbelianSchemeHom (zarhinSplit A) AbelianSchemeModel.trivial := 0
  let invH : AbelianSchemeHom (zarhinSplit A) (B.pow 4) :=
    prodLift (prodLift (prodLift (prodLift zTriv (mkB 0)) (mkB 1)) (mkB 2)) (mkB 3)
  let hp0_inv : ∀ u, p0.toLinear (invH.toLinear u) = (mkB 3).toLinear u := fun u =>
    prodSnd_prodLift _ (mkB 3) u
  let hp1_inv : ∀ u, p1.toLinear (invH.toLinear u) = (mkB 2).toLinear u := fun u => by
    change (prodSnd (B.pow 2) B).toLinear ((prodFst (B.pow 3) B).toLinear (invH.toLinear u)) = _
    rw [show (prodFst (B.pow 3) B).toLinear (invH.toLinear u) =
      (prodLift (prodLift (prodLift zTriv (mkB 0)) (mkB 1)) (mkB 2)).toLinear u from
        prodFst_prodLift _ (mkB 3) u]
    exact prodSnd_prodLift _ (mkB 2) u
  let hp2_inv : ∀ u, p2.toLinear (invH.toLinear u) = (mkB 1).toLinear u := fun u => by
    change (prodSnd (B.pow 1) B).toLinear
      ((prodFst (B.pow 2) B).toLinear ((prodFst (B.pow 3) B).toLinear (invH.toLinear u))) = _
    rw [show (prodFst (B.pow 3) B).toLinear (invH.toLinear u) =
      (prodLift (prodLift (prodLift zTriv (mkB 0)) (mkB 1)) (mkB 2)).toLinear u from
        prodFst_prodLift _ (mkB 3) u]
    rw [show (prodFst (B.pow 2) B).toLinear
      ((prodLift (prodLift (prodLift zTriv (mkB 0)) (mkB 1)) (mkB 2)).toLinear u) =
      (prodLift (prodLift zTriv (mkB 0)) (mkB 1)).toLinear u from
        prodFst_prodLift _ (mkB 2) u]
    exact prodSnd_prodLift _ (mkB 1) u
  let hp3_inv : ∀ u, p3.toLinear (invH.toLinear u) = (mkB 0).toLinear u := fun u => by
    change (prodSnd AbelianSchemeModel.trivial B).toLinear
      ((prodFst (B.pow 1) B).toLinear ((prodFst (B.pow 2) B).toLinear
        ((prodFst (B.pow 3) B).toLinear (invH.toLinear u)))) = _
    rw [show (prodFst (B.pow 3) B).toLinear (invH.toLinear u) =
      (prodLift (prodLift (prodLift zTriv (mkB 0)) (mkB 1)) (mkB 2)).toLinear u from
        prodFst_prodLift _ (mkB 3) u]
    rw [show (prodFst (B.pow 2) B).toLinear
      ((prodLift (prodLift (prodLift zTriv (mkB 0)) (mkB 1)) (mkB 2)).toLinear u) =
      (prodLift (prodLift zTriv (mkB 0)) (mkB 1)).toLinear u from
        prodFst_prodLift _ (mkB 2) u]
    rw [show (prodFst (B.pow 1) B).toLinear
      ((prodLift (prodLift zTriv (mkB 0)) (mkB 1)).toLinear u) =
      (prodLift zTriv (mkB 0)).toLinear u from
        prodFst_prodLift _ (mkB 1) u]
    exact prodSnd_prodLift _ (mkB 0) u
  { toHom := toH
    invHom := invH
    left_inv := by
      apply AbelianSchemeHom.ext
      refine LinearMap.ext fun z => funext fun m => ?_
      have htriv : ∀ x y : Fin (2 * AbelianSchemeModel.trivial.dim) → ℝ, x = y := fun _ _ =>
        funext fun i => Fin.elim0 i
      have htoA : (prodFst A.pow4Direct (DualAbelianScheme A).pow4Direct).toLinear
          (toH.toLinear z) =
          (pow4Lift4
            ((prodFst A (DualAbelianScheme A)).comp p3)
            ((prodFst A (DualAbelianScheme A)).comp p2)
            ((prodFst A (DualAbelianScheme A)).comp p1)
            ((prodFst A (DualAbelianScheme A)).comp p0)).toLinear z :=
        prodFst_prodLift _ _ z
      have htoD : (prodSnd A.pow4Direct (DualAbelianScheme A).pow4Direct).toLinear
          (toH.toLinear z) =
          (pow4Lift4
            ((prodSnd A (DualAbelianScheme A)).comp p3)
            ((prodSnd A (DualAbelianScheme A)).comp p2)
            ((prodSnd A (DualAbelianScheme A)).comp p1)
            ((prodSnd A (DualAbelianScheme A)).comp p0)).toLinear z :=
        prodSnd_prodLift _ _ z
      have hmk0 : (mkB 0).toLinear (toH.toLinear z) = p3.toLinear z := by
        refine prod_eq_of_fst_snd A (DualAbelianScheme A) _ _ ?_ ?_
        · rw [show (prodFst A (DualAbelianScheme A)).toLinear ((mkB 0).toLinear (toH.toLinear z)) =
            (qA 0).toLinear ((prodFst A.pow4Direct (DualAbelianScheme A).pow4Direct).toLinear
              (toH.toLinear z)) from prodFst_prodLift _ _ _]
          rw [htoA]; exact pow4DirectProj_pow4Lift4_0 _ _ _ _ z
        · rw [show (prodSnd A (DualAbelianScheme A)).toLinear ((mkB 0).toLinear (toH.toLinear z)) =
            (qD 0).toLinear ((prodSnd A.pow4Direct (DualAbelianScheme A).pow4Direct).toLinear
              (toH.toLinear z)) from prodSnd_prodLift _ _ _]
          rw [htoD]; exact pow4DirectProj_pow4Lift4_0 _ _ _ _ z
      have hmk1 : (mkB 1).toLinear (toH.toLinear z) = p2.toLinear z := by
        refine prod_eq_of_fst_snd A (DualAbelianScheme A) _ _ ?_ ?_
        · rw [show (prodFst A (DualAbelianScheme A)).toLinear ((mkB 1).toLinear (toH.toLinear z)) =
            (qA 1).toLinear ((prodFst A.pow4Direct (DualAbelianScheme A).pow4Direct).toLinear
              (toH.toLinear z)) from prodFst_prodLift _ _ _]
          rw [htoA]; exact pow4DirectProj_pow4Lift4_1 _ _ _ _ z
        · rw [show (prodSnd A (DualAbelianScheme A)).toLinear ((mkB 1).toLinear (toH.toLinear z)) =
            (qD 1).toLinear ((prodSnd A.pow4Direct (DualAbelianScheme A).pow4Direct).toLinear
              (toH.toLinear z)) from prodSnd_prodLift _ _ _]
          rw [htoD]; exact pow4DirectProj_pow4Lift4_1 _ _ _ _ z
      have hmk2 : (mkB 2).toLinear (toH.toLinear z) = p1.toLinear z := by
        refine prod_eq_of_fst_snd A (DualAbelianScheme A) _ _ ?_ ?_
        · rw [show (prodFst A (DualAbelianScheme A)).toLinear ((mkB 2).toLinear (toH.toLinear z)) =
            (qA 2).toLinear ((prodFst A.pow4Direct (DualAbelianScheme A).pow4Direct).toLinear
              (toH.toLinear z)) from prodFst_prodLift _ _ _]
          rw [htoA]; exact pow4DirectProj_pow4Lift4_2 _ _ _ _ z
        · rw [show (prodSnd A (DualAbelianScheme A)).toLinear ((mkB 2).toLinear (toH.toLinear z)) =
            (qD 2).toLinear ((prodSnd A.pow4Direct (DualAbelianScheme A).pow4Direct).toLinear
              (toH.toLinear z)) from prodSnd_prodLift _ _ _]
          rw [htoD]; exact pow4DirectProj_pow4Lift4_2 _ _ _ _ z
      have hmk3 : (mkB 3).toLinear (toH.toLinear z) = p0.toLinear z := by
        refine prod_eq_of_fst_snd A (DualAbelianScheme A) _ _ ?_ ?_
        · rw [show (prodFst A (DualAbelianScheme A)).toLinear ((mkB 3).toLinear (toH.toLinear z)) =
            (qA 3).toLinear ((prodFst A.pow4Direct (DualAbelianScheme A).pow4Direct).toLinear
              (toH.toLinear z)) from prodFst_prodLift _ _ _]
          rw [htoA]; exact pow4DirectProj_pow4Lift4_3 _ _ _ _ z
        · rw [show (prodSnd A (DualAbelianScheme A)).toLinear ((mkB 3).toLinear (toH.toLinear z)) =
            (qD 3).toLinear ((prodSnd A.pow4Direct (DualAbelianScheme A).pow4Direct).toLinear
              (toH.toLinear z)) from prodSnd_prodLift _ _ _]
          rw [htoD]; exact pow4DirectProj_pow4Lift4_3 _ _ _ _ z
      have h0 : (invH.comp toH).toLinear z = z := by
        change invH.toLinear (toH.toLinear z) = z
        refine prod_eq_of_fst_snd (B.pow 3) B _ _ ?_ ?_
        · refine prod_eq_of_fst_snd (B.pow 2) B _ _ ?_ ?_
          · refine prod_eq_of_fst_snd (B.pow 1) B _ _ ?_ ?_
            · refine prod_eq_of_fst_snd AbelianSchemeModel.trivial B _ _ (htriv _ _) ?_
              exact (hp3_inv (toH.toLinear z)).trans hmk0
            · exact (hp2_inv (toH.toLinear z)).trans hmk1
          · exact (hp1_inv (toH.toLinear z)).trans hmk2
        · exact (hp0_inv (toH.toLinear z)).trans hmk3
      exact congrFun h0 m
    right_inv := by
      apply AbelianSchemeHom.ext
      refine LinearMap.ext fun w => funext fun m => ?_
      have htoA : (prodFst A.pow4Direct (DualAbelianScheme A).pow4Direct).toLinear
          (toH.toLinear (invH.toLinear w)) =
          (pow4Lift4
            ((prodFst A (DualAbelianScheme A)).comp p3)
            ((prodFst A (DualAbelianScheme A)).comp p2)
            ((prodFst A (DualAbelianScheme A)).comp p1)
            ((prodFst A (DualAbelianScheme A)).comp p0)).toLinear (invH.toLinear w) :=
        prodFst_prodLift _ _ (invH.toLinear w)
      have htoD : (prodSnd A.pow4Direct (DualAbelianScheme A).pow4Direct).toLinear
          (toH.toLinear (invH.toLinear w)) =
          (pow4Lift4
            ((prodSnd A (DualAbelianScheme A)).comp p3)
            ((prodSnd A (DualAbelianScheme A)).comp p2)
            ((prodSnd A (DualAbelianScheme A)).comp p1)
            ((prodSnd A (DualAbelianScheme A)).comp p0)).toLinear (invH.toLinear w) :=
        prodSnd_prodLift _ _ (invH.toLinear w)
      have h0 : (toH.comp invH).toLinear w = w := by
        change toH.toLinear (invH.toLinear w) = w
        refine prod_eq_of_fst_snd A.pow4Direct (DualAbelianScheme A).pow4Direct _ _ ?_ ?_
        · rw [htoA]
          refine pow4Direct_eq_of_proj4 A _ _ ?_ ?_ ?_ ?_
          · rw [pow4DirectProj_pow4Lift4_0]; dsimp only [AbelianSchemeHom.comp_toLinear, LinearMap.comp_apply]
            rw [hp3_inv w]; exact prodFst_prodLift _ _ w
          · rw [pow4DirectProj_pow4Lift4_1]; dsimp only [AbelianSchemeHom.comp_toLinear, LinearMap.comp_apply]
            rw [hp2_inv w]; exact prodFst_prodLift _ _ w
          · rw [pow4DirectProj_pow4Lift4_2]; dsimp only [AbelianSchemeHom.comp_toLinear, LinearMap.comp_apply]
            rw [hp1_inv w]; exact prodFst_prodLift _ _ w
          · rw [pow4DirectProj_pow4Lift4_3]; dsimp only [AbelianSchemeHom.comp_toLinear, LinearMap.comp_apply]
            rw [hp0_inv w]; exact prodFst_prodLift _ _ w
        · rw [htoD]
          refine pow4Direct_eq_of_proj4 (DualAbelianScheme A) _ _ ?_ ?_ ?_ ?_
          · rw [pow4DirectProj_pow4Lift4_0]; dsimp only [AbelianSchemeHom.comp_toLinear, LinearMap.comp_apply]
            rw [hp3_inv w]; exact prodSnd_prodLift _ _ w
          · rw [pow4DirectProj_pow4Lift4_1]; dsimp only [AbelianSchemeHom.comp_toLinear, LinearMap.comp_apply]
            rw [hp2_inv w]; exact prodSnd_prodLift _ _ w
          · rw [pow4DirectProj_pow4Lift4_2]; dsimp only [AbelianSchemeHom.comp_toLinear, LinearMap.comp_apply]
            rw [hp1_inv w]; exact prodSnd_prodLift _ _ w
          · rw [pow4DirectProj_pow4Lift4_3]; dsimp only [AbelianSchemeHom.comp_toLinear, LinearMap.comp_apply]
            rw [hp0_inv w]; exact prodSnd_prodLift _ _ w
      exact congrFun h0 m }

/-- **Constructive Zarhin Principal Polarization on `(A × A^∨)^4`** for ANY polarized
abelian scheme `(A, P)`. -/
def zarhinPrincipalPolarization {A : AbelianSchemeModel} (P : Polarization A) :
    PrincipalPolarization ((A.prod (DualAbelianScheme A)).pow 4) :=
  PrincipalPolarization.ofIso (zarhinFourFoldIso A) (zarhinPrincipalPolarizationSplit P)

/-- **ZARHIN'S TRICK (`zarhin_trick_principally_polarized`)**:
for every abelian scheme model `A` carrying a polarization `P : Polarization A` of arbitrary
positive degree/exponent `d ≥ 1`, the 8-fold product `(A × A^∨)^4` unconditionally carries a
**principal polarization** (`PrincipalPolarization ((A.prod (DualAbelianScheme A)).pow 4)`),
constructed via Lagrange's Four-Squares Theorem in `End(A)` (`Nat.sum_four_squares`). -/
theorem zarhin_trick_principally_polarized {A : AbelianSchemeModel} (P : Polarization A) :
    Nonempty (PrincipalPolarization ((A.prod (DualAbelianScheme A)).pow 4)) :=
  ⟨zarhinPrincipalPolarization P⟩

/-- Exact Arakelov Hodge-bundle degree of Zarhin's principally polarized 8-fold scheme:
`deg_Ar(ω_{(A × A^∨)^4 / S}) = 0`. -/
theorem zarhinScheme_hodgeBundle_arakelovDeg (A : AbelianSchemeModel) :
    ((A.prod (DualAbelianScheme A)).pow 4).hodgeBundle.arakelovDeg = 0 := by
  rw [AbelianSchemeModel.hodgeBundle_pow_arakelovDeg, prod_dual_hodgeBundle_arakelovDeg, mul_zero]

end ZarhinTrick

end RHDirect.Stage14M3_AbelianSchemeLaws

