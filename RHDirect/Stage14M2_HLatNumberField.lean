import RHDirect.Stage12SchurWeylLattices
import RHDirect.Stage11BostDworkSqueeze
import RHDirect.ArakelovCovolume
import Mathlib.NumberTheory.NumberField.Discriminant.Basic
import Mathlib.RingTheory.Discriminant
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas

/-!
# RHDirect.Stage14M2_HLatNumberField

Field-2 Package M2 (Wave 1, Module 1 of 6): **General Number-Field Hermitian Lattices (`HLat K`),
Realization, `ZLattice.covolume` Grounding, Normalized Slopes, Exact Duality, and Orthogonal
Direct Sums** in pure Mathlib `v4.33.1`.

Zero `sorry`, zero custom `axiom`s, zero `native_decide`, zero `opaque`.

## Main Exports (Ready for M2 Wave 2 & Wave 3)

1. **`HLat K` & `realizeHLat`**:
   - Concrete `HLat K` over a number field `K` (matching Alpöge's `DataArith.HLat`), with
     `FrameOK`, `Good`, `withL`, `rank`, and bridge `toNumberFieldHLat` to
     `Stage12SchurWeylLattices.NumberFieldHLat K`.
   - `vecAt`, `fcoord`, `normAt`, `majAt`, `realizeHLat`, `zRealize`, `norm_sq_realizeHLat`,
     `inner_realizeHLat_eq_sum_majAt`, and `realizeHLat_injective`.
2. **Lattice Structure & `covolHLat_eq_zlattice_covolume`**:
   - Unconditional `discreteTopology_zRealize_of_fg`, `isZLattice_zRealize_of_good`,
     `rk_zRealize_eq` (`rk (zRealize L) = [K : ℚ] * rkK L`), and
     `covolHLat_eq_zlattice_covolume` via `Stage12SchurWeylLattices`.
   - Saturation characterization `saturation_zRealize_eq` and `twist_index`
     (`[L : 𝔟 • L] = (Ideal.absNorm 𝔟) ^ rkK L` for nonzero ideals `𝔟 ≤ 𝓞 K`).
3. **Normalized Slopes (`muDef`, `muMaxDef`, `muMinDef`) & Comparison Bounds**:
   - `muDef`, `muMaxDef`, `muMinDef` (matching `StatementPl.lean` & `DataArith.lean`),
     variational characterizations (`muMaxO_char`, `muMinO_char`), comparison with `ℤ`-lattice
     slopes (`muMaxDef_le_zMuMax`, `zMuMin_le_muMinDef`), rescaling (`rescaleFrame`), and Bost
     morphism slope inequalities.
4. **`dualHLat` & `hlat_duality_slope_neg`**:
   - `dualHLat A` (`V*`, `b.dualBasis`, `dualFrame X`, `dualLatO L`), exact different-ideal
     relation `dual_inf_ann_eq`, `deg_dualHLat`, and `hlat_duality_slope_neg`:
     `mu (dualHLat A) = - mu A`, `muMax (dualHLat A) = - muMin A`, `muMin (dualHLat A) = - muMax A`,
     plus `bridge_ccb_dual` for `BesselIntegrality`.
5. **`hlat_orthog_direct_sum`**:
   - Internal orthogonal direct sum (`⨆ c ∈ s, N c`) and external `directSumHLat A B`:
     exact rank additivity, degree additivity, weighted/equal-rank `mu` averaging,
     `muMax` supremum, and `muMin` infimum.
-/

noncomputable section

open Module Submodule Finset Real MeasureTheory Filter Matrix NumberField IsDedekindDomain
open scoped BigOperators Matrix ENNReal InnerProductSpace Topology ComplexOrder Pointwise

open RHDirect.ArakelovCovolume (rk covol degAr discreteTopology_of_le
  covol_eq_sqrt_det_gram finrank_int_eq_finrank_real_span linearIndependent_coe_basis
  det_gram_basis_pos covol_pos rk_pos_of_ne_bot covol_bot degAr_bot
  covol_le_of_le_same_rank bost_slope_inequality bost_degree_inequality)
open RHDirect.Stage4ArakelovBost (IsSaturated saturation quotLat projOrth
  discreteTopology_of_fin_basis_real_li discreteTopology_quotLat rk_add_quotLat
  covol_eq_mul_quotLat degAr_eq_add_quotLat dualLat discreteTopology_dualLat
  rk_dualLat covol_dualLat degAr_dualLat span_real_dualLat dualLat_dualLat
  projOrth_mem_orthogonal sub_projOrth_mem_span inner_projOrth_left
  projOrth_eq_self_of_mem_orthogonal)
open RHDirect.Stage11BostDworkSqueeze (latIndex finite_quotient_of_le_same_rank
  covol_eq_index_mul_covol degAr_eq_degAr_sub_log_index)
open RHDirect.Stage12SchurWeylLattices (euclideanSpaceCongr NumberFieldHLat)

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace RHDirect.Stage14M2_HLatNumberField

/-! ## Section 1: Concrete `HLat K`, `realizeHLat`, Sesquilinear Majorant & Frame Basics -/

section RealizeBasics

variable {K V ι : Type*} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
  [Fintype ι] [DecidableEq ι]

/-- Archimedean coordinate vector at infinite place `v : InfinitePlace K` in basis `b`. -/
def vecAt (b : Module.Basis ι K V) (v : InfinitePlace K) (x : V) : ι → ℂ :=
  RHDirect.Stage12SchurWeylLattices.vecAt b v x

/-- Frame-twisted coordinate vector `(X v)⁻¹ *ᵥ vecAt b v x`. -/
def fcoord (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (v : InfinitePlace K) (x : V) : ι → ℂ :=
  RHDirect.Stage12SchurWeylLattices.fcoord b X v x

/-- Hermitian norm at infinite place `v`. -/
def normAt (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (v : InfinitePlace K) (x : V) : ℝ :=
  RHDirect.Stage12SchurWeylLattices.normAt b X v x

/-- Majorant Hermitian sesquilinear form at infinite place `v`:
`majAt b X v x y = ∑ i, star (fcoord b X v x i) * fcoord b X v y i`. -/
def majAt (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (v : InfinitePlace K) (x y : V) : ℂ :=
  ∑ i : ι, star (fcoord b X v x i) * fcoord b X v y i

/-- Canonical real Euclidean realization
`V →+ EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2)`. -/
def realizeHLat (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) :
    V →+ EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2) :=
  RHDirect.Stage12SchurWeylLattices.realizeHLat b X

lemma vecAt_apply (b : Module.Basis ι K V) (v : InfinitePlace K) (x : V) (i : ι) :
    vecAt b v x i = v.embedding (b.repr x i) := rfl

lemma vecAt_smul (b : Module.Basis ι K V) (v : InfinitePlace K) (a : K) (x : V) :
    vecAt b v (a • x) = v.embedding a • vecAt b v x := by
  funext i
  simp [vecAt, RHDirect.Stage12SchurWeylLattices.vecAt, map_mul]

lemma vecAt_smul_basis (b : Module.Basis ι K V) (v : InfinitePlace K) (a : K) (i : ι) :
    vecAt b v (a • b i) = Pi.single i (v.embedding a) := by
  funext j
  simp only [vecAt, RHDirect.Stage12SchurWeylLattices.vecAt, map_smul, Basis.repr_self,
    Finsupp.smul_single, smul_eq_mul, mul_one, Finsupp.single_apply, Pi.single_apply]
  by_cases h : i = j
  · subst h; simp
  · simp [h, Ne.symm h]

lemma fcoord_zero (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (v : InfinitePlace K) : fcoord b X v 0 = 0 :=
  RHDirect.Stage12SchurWeylLattices.fcoord_zero b X v

lemma fcoord_add (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (v : InfinitePlace K) (x y : V) :
    fcoord b X v (x + y) = fcoord b X v x + fcoord b X v y :=
  RHDirect.Stage12SchurWeylLattices.fcoord_add b X v x y

lemma fcoord_smul (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (v : InfinitePlace K) (a : K) (x : V) :
    fcoord b X v (a • x) = v.embedding a • fcoord b X v x := by
  change RHDirect.Stage12SchurWeylLattices.fcoord b X v (a • x) =
    v.embedding a • RHDirect.Stage12SchurWeylLattices.fcoord b X v x
  unfold RHDirect.Stage12SchurWeylLattices.fcoord
  change ((X v)⁻¹).mulVec (vecAt b v (a • x)) = v.embedding a • ((X v)⁻¹).mulVec (vecAt b v x)
  rw [vecAt_smul, Matrix.mulVec_smul]

lemma realizeHLat_apply0 (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (x : V) (v : InfinitePlace K) (i : ι) :
    realizeHLat b X x (v, i, 0) = (fcoord b X v x i).re := rfl

lemma realizeHLat_apply1 (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (x : V) (v : InfinitePlace K) (i : ι) :
    realizeHLat b X x (v, i, 1) = (fcoord b X v x i).im := by
  simp [realizeHLat, RHDirect.Stage12SchurWeylLattices.realizeHLat, fcoord]

lemma realizeHLat_smul_rat (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (q : ℚ) (x : V) :
    realizeHLat b X ((algebraMap ℚ K q) • x) = (q : ℝ) • realizeHLat b X x := by
  ext p
  have hfc : fcoord b X p.1 ((algebraMap ℚ K q) • x) p.2.1 =
      ((q : ℝ) : ℂ) * fcoord b X p.1 x p.2.1 := by
    rw [fcoord_smul, Pi.smul_apply, smul_eq_mul]
    congr 1
    simp
  change (if p.2.2 = 0 then (fcoord b X p.1 ((algebraMap ℚ K q) • x) p.2.1).re
    else (fcoord b X p.1 ((algebraMap ℚ K q) • x) p.2.1).im) =
    (q : ℝ) * (if p.2.2 = 0 then (fcoord b X p.1 x p.2.1).re else (fcoord b X p.1 x p.2.1).im)
  rw [hfc]
  split_ifs <;> simp

/-- Exact archimedean norm-squared identity `‖realizeHLat b X x‖ ^ 2 = ∑ v, normAt b X v x ^ 2`. -/
theorem norm_sq_realizeHLat (b : Module.Basis ι K V)
    (X : InfinitePlace K → Matrix ι ι ℂ) (x : V) :
    ‖realizeHLat b X x‖ ^ 2 = ∑ v : InfinitePlace K, normAt b X v x ^ 2 :=
  RHDirect.Stage12SchurWeylLattices.norm_sq_realizeHLat b X x

/-- Real inner product on `EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2)` in terms of `majAt`. -/
theorem inner_realizeHLat_eq_sum_majAt (b : Module.Basis ι K V)
    (X : InfinitePlace K → Matrix ι ι ℂ) (x y : V) :
    inner ℝ (realizeHLat b X x) (realizeHLat b X y) =
      ∑ v : InfinitePlace K, (majAt b X v x y).re := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Fintype.sum_prod_type]
  unfold majAt
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fin.sum_univ_two]
  simp only [star_trivial, realizeHLat_apply0, realizeHLat_apply1, Complex.star_def,
    Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

theorem majAt_self_eq_normAt_sq (b : Module.Basis ι K V)
    (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K) (x : V) :
    majAt b X v x x = ((normAt b X v x ^ 2 : ℝ) : ℂ) := by
  unfold majAt normAt
  change (∑ i : ι, star (fcoord b X v x i) * fcoord b X v x i) =
    ((Real.sqrt (∑ i : ι, ‖fcoord b X v x i‖ ^ 2) ^ 2 : ℝ) : ℂ)
  rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.star_def, Complex.conj_mul']

theorem majAt_add_left (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (v : InfinitePlace K) (x₁ x₂ y : V) :
    majAt b X v (x₁ + x₂) y = majAt b X v x₁ y + majAt b X v x₂ y := by
  simp only [majAt, fcoord_add, Pi.add_apply, star_add, add_mul, Finset.sum_add_distrib]

theorem majAt_add_right (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (v : InfinitePlace K) (x y₁ y₂ : V) :
    majAt b X v x (y₁ + y₂) = majAt b X v x y₁ + majAt b X v x y₂ := by
  simp only [majAt, fcoord_add, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem majAt_smul_left (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (v : InfinitePlace K) (a : K) (x y : V) :
    majAt b X v (a • x) y = starRingEnd ℂ (v.embedding a) * majAt b X v x y := by
  simp only [majAt, fcoord_smul, Pi.smul_apply, smul_eq_mul, star_mul', Complex.star_def,
    mul_assoc, Finset.mul_sum]

theorem majAt_smul_right (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (v : InfinitePlace K) (a : K) (x y : V) :
    majAt b X v x (a • y) = v.embedding a * majAt b X v x y := by
  simp only [majAt, fcoord_smul, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => by ring

/-- Injectivity of `realizeHLat b X` when every archimedean frame `X v` is invertible. -/
theorem realizeHLat_injective (b : Module.Basis ι K V)
    (X : InfinitePlace K → Matrix ι ι ℂ) (hX : ∀ v, IsUnit (X v).det) :
    Function.Injective (realizeHLat b X) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  have hf : ∀ v i, fcoord b X v x i = 0 := by
    intro v i
    apply Complex.ext
    · rw [← realizeHLat_apply0 b X x v i, hx]; rfl
    · rw [← realizeHLat_apply1 b X x v i, hx]; rfl
  have hv : ∀ v, vecAt b v x = 0 := by
    intro v
    have h0 : ((X v)⁻¹).mulVec (vecAt b v x) = 0 := funext (hf v)
    have h1 := congrArg (X v).mulVec h0
    rwa [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (hX v), Matrix.one_mulVec,
      Matrix.mulVec_zero] at h1
  obtain ⟨v⟩ : Nonempty (InfinitePlace K) := inferInstance
  apply b.repr.injective
  ext i
  have hvi := congrFun (hv v) i
  simp only [vecAt, RHDirect.Stage12SchurWeylLattices.vecAt, Pi.zero_apply, map_eq_zero] at hvi
  simpa using hvi

/-- Realized `ℤ`-submodule in `EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2)` of an
`𝓞 K`-submodule `L ≤ V`. -/
def zRealize [Module (𝓞 K) V] (b : Module.Basis ι K V)
    (X : InfinitePlace K → Matrix ι ι ℂ) (L : Submodule (𝓞 K) V) :
    Submodule ℤ (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2)) :=
  (L.restrictScalars ℤ).map (realizeHLat b X).toIntLinearMap

lemma mem_zRealize [Module (𝓞 K) V] (b : Module.Basis ι K V)
    (X : InfinitePlace K → Matrix ι ι ℂ) (L : Submodule (𝓞 K) V)
    (w : EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2)) :
    w ∈ zRealize b X L ↔ ∃ x ∈ L, realizeHLat b X x = w := Iff.rfl

lemma zRealize_mono [Module (𝓞 K) V] (b : Module.Basis ι K V)
    (X : InfinitePlace K → Matrix ι ι ℂ) {L₁ L₂ : Submodule (𝓞 K) V} (h : L₁ ≤ L₂) :
    zRealize b X L₁ ≤ zRealize b X L₂ :=
  Submodule.map_mono h

lemma zRealize_bot [Module (𝓞 K) V] (b : Module.Basis ι K V)
    (X : InfinitePlace K → Matrix ι ι ℂ) :
    zRealize b X (⊥ : Submodule (𝓞 K) V) = ⊥ := by
  simp [zRealize]

lemma zRealize_sup [Module (𝓞 K) V] (b : Module.Basis ι K V)
    (X : InfinitePlace K → Matrix ι ι ℂ) (L₁ L₂ : Submodule (𝓞 K) V) :
    zRealize b X (L₁ ⊔ L₂) = zRealize b X L₁ ⊔ zRealize b X L₂ := by
  unfold zRealize
  rw [Submodule.restrictScalars_sup, Submodule.map_sup]

lemma zRealize_iSup [Module (𝓞 K) V] (b : Module.Basis ι K V)
    (X : InfinitePlace K → Matrix ι ι ℂ) {γ : Type*} (L : γ → Submodule (𝓞 K) V) :
    zRealize b X (⨆ c, L c) = ⨆ c, zRealize b X (L c) := by
  unfold zRealize
  rw [Submodule.restrictScalars_iSup, Submodule.map_iSup]

end RealizeBasics

/-- `K`-rank of an `𝓞 K`-submodule `L ≤ V`. -/
def rkK {K V : Type*} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] (L : Submodule (𝓞 K) V) : ℕ :=
  Module.finrank K (Submodule.span K (L : Set V))

/-- **Concrete Number-Field Hermitian Lattice `HLat K`** (matching `DataArith.HLat`). -/
structure HLat (K : Type) [Field K] [NumberField K] [StarRing K] where
  V : Type
  [addV : AddCommGroup V]
  [modV : Module K V]
  [modOV : Module (𝓞 K) V]
  [towV : IsScalarTower (𝓞 K) K V]
  ι : Type
  [finι : Fintype ι]
  [decι : DecidableEq ι]
  b : Module.Basis ι K V
  X : InfinitePlace K → Matrix ι ι ℂ
  L : Submodule (𝓞 K) V

attribute [instance] HLat.addV HLat.modV HLat.modOV HLat.towV HLat.finι HLat.decι

namespace HLat

variable {K : Type} [Field K] [NumberField K] [StarRing K]

/-- Invertibility of all archimedean frame matrices `A.X v`. -/
def FrameOK (A : HLat K) : Prop := ∀ v : InfinitePlace K, IsUnit (A.X v).det

/-- Full-rank finitely generated Hermitian lattice over `𝓞 K`. -/
def Good (A : HLat K) : Prop :=
  A.FrameOK ∧ A.L.FG ∧ Submodule.span K (A.L : Set A.V) = ⊤

/-- `K`-rank of `A : HLat K`. -/
def rank (A : HLat K) : ℕ := rkK (K := K) A.L

/-- Replace the underlying `𝓞 K`-lattice `A.L` while keeping `(V, b, X)`. -/
def withL (A : HLat K) (L' : Submodule (𝓞 K) A.V) : HLat K :=
  { A with L := L' }

/-- Realized `ℤ`-lattice of `A : HLat K`. -/
abbrev zRealize (A : HLat K) :
    Submodule ℤ (EuclideanSpace ℝ (InfinitePlace K × A.ι × Fin 2)) :=
  RHDirect.Stage14M2_HLatNumberField.zRealize A.b A.X A.L

end HLat

/-! ## Section 2: Lattice Structure (`DiscreteTopology`, `IsZLattice`, `covolHLat_eq_zlattice_covolume`) -/

section LatticeStructure

section AuxiliaryLinearIndep

variable {K : Type*} [Field K] [NumberField K]

/-- A real linear combination of `v.embedding (integralBasis K k)` vanishing at every infinite
place `v` must have zero coefficients. -/
theorem sum_embedding_integralBasis_eq_zero {t : Free.ChooseBasisIndex ℤ (𝓞 K) → ℝ}
    (h : ∀ v : InfinitePlace K,
      ∑ k, (t k : ℂ) * v.embedding (NumberField.integralBasis K k) = 0) :
    t = 0 := by
  have hφ : ∀ φ : K →+* ℂ, ∑ k, (t k : ℂ) * φ (NumberField.integralBasis K k) = 0 := by
    intro φ
    rcases InfinitePlace.embedding_mk_eq φ with hφ | hφ
    · simpa [hφ] using h (InfinitePlace.mk φ)
    · have h2 := congrArg (starRingEnd ℂ) (h (InfinitePlace.mk φ))
      simpa [hφ, map_sum, map_mul, Complex.conj_ofReal] using h2
  have hli := (NumberField.canonicalEmbedding.latticeBasis K).linearIndependent
  rw [Fintype.linearIndependent_iff] at hli
  have hz := hli (fun k => (t k : ℂ)) (by
    funext φ
    simpa [NumberField.canonicalEmbedding.latticeBasis_apply, Finset.sum_apply,
      smul_eq_mul] using hφ φ)
  funext k
  exact_mod_cast hz k

/-- `ℝ`-linear independence of `{ realizeHLat b X (integralBasis K k • e j) }` for any
`K`-linearly independent family `e : κ → V`. -/
theorem linearIndependent_realizeHLat_integralBasis {V ι κ : Type*}
    [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (e : κ → V) (he : LinearIndependent K e) :
    LinearIndependent ℝ (fun p : Free.ChooseBasisIndex ℤ (𝓞 K) × κ =>
      realizeHLat b X (NumberField.integralBasis K p.1 • e p.2)) := by
  rw [Fintype.linearIndependent_iff]
  intro t ht p
  have hcoord : ∀ v i r, ∑ q, t q *
      (realizeHLat b X (NumberField.integralBasis K q.1 • e q.2)) (v, i, r) = 0 := by
    intro v i r
    have h1 := congrArg (fun z => z (v, i, r)) ht
    simpa [Finset.sum_apply] using h1
  have hC : ∀ v i, ∑ q, (t q : ℂ) *
      fcoord b X v (NumberField.integralBasis K q.1 • e q.2) i = 0 := by
    intro v i
    apply Complex.ext
    · have h0 := hcoord v i 0
      simpa [realizeHLat_apply0, Complex.re_sum, Complex.re_ofReal_mul] using h0
    · have h1 := hcoord v i 1
      simpa [realizeHLat_apply1, Complex.im_sum, Complex.im_ofReal_mul] using h1
  have hV : ∀ v, ∑ q, (t q : ℂ) • vecAt b v (NumberField.integralBasis K q.1 • e q.2) = 0 := by
    intro v
    have h0 : Matrix.mulVec (X v)⁻¹
        (∑ q, (t q : ℂ) • vecAt b v (NumberField.integralBasis K q.1 • e q.2)) = 0 := by
      funext i
      rw [Matrix.mulVec_sum]
      simp only [Matrix.mulVec_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      exact hC v i
    have hinv : X v * (X v)⁻¹ = 1 := Matrix.mul_nonsing_inv _ (hX v)
    calc ∑ q, (t q : ℂ) • vecAt b v (NumberField.integralBasis K q.1 • e q.2)
        = Matrix.mulVec (X v * (X v)⁻¹)
            (∑ q, (t q : ℂ) • vecAt b v (NumberField.integralBasis K q.1 • e q.2)) := by
          rw [hinv, Matrix.one_mulVec]
      _ = 0 := by rw [← Matrix.mulVec_mulVec, h0, Matrix.mulVec_zero]
  let V₀ := Submodule.span K (Set.range e)
  let bE : Module.Basis κ K V₀ := Module.Basis.span he
  obtain ⟨ψ, hψ⟩ := LinearMap.exists_extend (bE.coord p.2)
  have hψe : ∀ j : κ, ψ (e j) = if j = p.2 then 1 else 0 := by
    intro j
    have h1 : ψ (V₀.subtype (bE j)) = bE.coord p.2 (bE j) := LinearMap.congr_fun hψ (bE j)
    have hbEj : (V₀.subtype (bE j) : V) = e j := by
      change (bE j : V) = e j
      rw [Module.Basis.span_apply]
    rw [hbEj, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply] at h1
    exact h1
  let c : ι → K := fun i => ψ (b i)
  have hS : ∀ v : InfinitePlace K,
      ∑ k, ((t (k, p.2) : ℝ) : ℂ) * v.embedding (NumberField.integralBasis K k) = 0 := by
    intro v
    have hsum := congrArg (fun w : ι → ℂ => ∑ i : ι, v.embedding (c i) * w i) (hV v)
    simp only [Finset.mul_sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Pi.zero_apply, mul_zero, Finset.sum_const_zero] at hsum
    rw [Finset.sum_comm] at hsum
    have hinner : ∀ q : Free.ChooseBasisIndex ℤ (𝓞 K) × κ,
        ∑ i : ι, v.embedding (c i) * ((t q : ℂ) *
          vecAt b v (NumberField.integralBasis K q.1 • e q.2) i) =
        (t q : ℂ) * v.embedding (NumberField.integralBasis K q.1) *
          v.embedding (ψ (e q.2)) := by
      intro q
      have hψeq : ψ (e q.2) = ∑ i : ι, b.repr (e q.2) i * c i := by
        conv_lhs => rw [← b.sum_repr (e q.2)]
        rw [map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_smul, smul_eq_mul]
      rw [hψeq, map_sum]
      simp only [vecAt, RHDirect.Stage12SchurWeylLattices.vecAt, map_smul, Finsupp.smul_apply,
        smul_eq_mul, map_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => by ring
    simp only [hinner, hψe] at hsum
    rw [Fintype.sum_prod_type] at hsum
    have hsum' : ∑ k, (t (k, p.2) : ℂ) * v.embedding (NumberField.integralBasis K k) = 0 := by
      rw [← hsum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.sum_eq_single p.2]
      · simp
      · intro j _ hjp; simp [hjp]
      · intro h; exact absurd (Finset.mem_univ p.2) h
    exact hsum'
  exact congrFun (sum_embedding_integralBasis_eq_zero hS) p.1

/-- Clearing denominators in `K`: every `x : K` becomes an `𝓞 K`-element after multiplying by
a strictly positive natural number `d : ℕ`. -/
lemma exists_pos_nat_mul_mem_ringOfIntegers (x : K) :
    ∃ (d : ℕ) (a : 𝓞 K), 0 < d ∧ (d : K) * x = (a : K) := by
  obtain ⟨⟨n, m⟩, hnm⟩ := IsLocalization.surj (nonZeroDivisors (𝓞 K)) x
  have hm0 : (m : 𝓞 K) ≠ 0 := nonZeroDivisors.ne_zero m.2
  have hmK : ((m : 𝓞 K) : K) ≠ 0 :=
    FaithfulSMul.algebraMap_injective (𝓞 K) K |>.ne hm0
  let I : Ideal (𝓞 K) := Ideal.span {(m : 𝓞 K)}
  have hI0 : I ≠ ⊥ := by
    rw [ne_eq, Ideal.span_singleton_eq_bot]
    exact hm0
  let d : ℕ := Ideal.absNorm I
  have hd_pos : 0 < d := Nat.pos_of_ne_zero (fun h => hI0 (Ideal.absNorm_eq_zero_iff.mp h))
  have hd_mem : (d : 𝓞 K) ∈ I := Ideal.absNorm_mem I
  rw [Ideal.mem_span_singleton] at hd_mem
  obtain ⟨u, hu⟩ := hd_mem
  refine ⟨d, u * n, hd_pos, ?_⟩
  have hnm' : x * ((m : 𝓞 K) : K) = ((n : 𝓞 K) : K) := by simpa using hnm
  have huK : (d : K) = ((u : 𝓞 K) : K) * ((m : 𝓞 K) : K) := by
    rw [mul_comm] at hu
    exact_mod_cast hu
  have hcalc : ((d : K) * x) * ((m : 𝓞 K) : K) = (((u * n : 𝓞 K) : K)) * ((m : 𝓞 K) : K) := by
    calc ((d : K) * x) * ((m : 𝓞 K) : K)
        = (d : K) * (x * ((m : 𝓞 K) : K)) := by ring
      _ = (d : K) * ((n : 𝓞 K) : K) := by rw [hnm']
      _ = (((u : 𝓞 K) : K) * ((m : 𝓞 K) : K)) * ((n : 𝓞 K) : K) := by rw [huK]
      _ = (((u * n : 𝓞 K) : K)) * ((m : 𝓞 K) : K) := by push_cast; ring
  exact mul_right_cancel₀ hmK hcalc

/-- Clearing denominators for a finite family `f : ι → K`. -/
lemma exists_pos_nat_mul_mem_ringOfIntegers_fin {κ : Type*} [Fintype κ] (f : κ → K) :
    ∃ (d : ℕ), 0 < d ∧ ∀ i : κ, ∃ a : 𝓞 K, (d : K) * f i = (a : K) := by
  classical
  choose d a hd ha using fun i => exists_pos_nat_mul_mem_ringOfIntegers (f i)
  refine ⟨∏ i : κ, d i, Finset.prod_pos fun i _ => hd i, fun i => ?_⟩
  let q : ℕ := ∏ j ∈ Finset.univ.erase i, d j
  refine ⟨(q : 𝓞 K) * a i, ?_⟩
  have hprod : (∏ j : κ, d j : ℕ) = q * d i := by
    rw [← Finset.mul_prod_erase Finset.univ d (Finset.mem_univ i), mul_comm]
  rw [hprod, Nat.cast_mul, mul_assoc, ha i]
  push_cast
  ring

/-- `zRealize b X (span (𝓞 K) (range e))` equals the `ℤ`-span of
`realizeHLat b X (integralBasis K p.1 • e p.2)`. -/
lemma zRealize_span_eq {V ι κ : Type*} [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι] [Fintype κ]
    (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (e : κ → V) :
    zRealize b X (Submodule.span (𝓞 K) (Set.range e)) =
      Submodule.span ℤ (Set.range fun p : Free.ChooseBasisIndex ℤ (𝓞 K) × κ =>
        realizeHLat b X (NumberField.integralBasis K p.1 • e p.2)) := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    change x ∈ Submodule.span (𝓞 K) (Set.range e) at hx
    rw [Submodule.mem_span_range_iff_exists_fun] at hx
    obtain ⟨c, rfl⟩ := hx
    have hsum : ∑ j : κ, c j • e j =
        ∑ j : κ, ∑ k : Free.ChooseBasisIndex ℤ (𝓞 K),
          ((RingOfIntegers.basis K).repr (c j) k) •
            (NumberField.integralBasis K k • e j) := by
      refine Finset.sum_congr rfl fun j _ => ?_
      have hc : c j = ∑ k : Free.ChooseBasisIndex ℤ (𝓞 K),
          ((RingOfIntegers.basis K).repr (c j) k) • RingOfIntegers.basis K k :=
        ((RingOfIntegers.basis K).sum_repr (c j)).symm
      conv_lhs => rw [hc]
      rw [Finset.sum_smul]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [smul_assoc, NumberField.integralBasis_apply, algebraMap_smul]
    rw [hsum, map_sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [map_sum]
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [map_zsmul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(k, j), rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨⟨k, j⟩, rfl⟩
    refine ⟨(RingOfIntegers.basis K k : 𝓞 K) • e j,
      Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self j)), ?_⟩
    change realizeHLat b X ((RingOfIntegers.basis K k : 𝓞 K) • e j) =
      realizeHLat b X (NumberField.integralBasis K k • e j)
    rw [NumberField.integralBasis_apply, algebraMap_smul]

/-- For any `K`-linearly independent `e : κ → V`, the realized lattice
`zRealize b X (span (𝓞 K) (range e))` is discrete of `ℤ`-rank `[K : ℚ] * #κ`. -/
theorem discrete_and_rk_zRealize_span {V ι κ : Type*} [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (e : κ → V) (he : LinearIndependent K e) :
    DiscreteTopology (zRealize b X (Submodule.span (𝓞 K) (Set.range e))) ∧
      rk (zRealize b X (Submodule.span (𝓞 K) (Set.range e))) =
        Module.finrank ℚ K * Fintype.card κ := by
  let v : Free.ChooseBasisIndex ℤ (𝓞 K) × κ →
      EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2) :=
    fun p => realizeHLat b X (NumberField.integralBasis K p.1 • e p.2)
  have hv_li : LinearIndependent ℝ v :=
    linearIndependent_realizeHLat_integralBasis b X hX e he
  have hv_liZ : LinearIndependent ℤ v := hv_li.restrict_scalars (fun a b hab => by
    simpa [zsmul_eq_mul] using hab)
  let M := zRealize b X (Submodule.span (𝓞 K) (Set.range e))
  have hM : M = Submodule.span ℤ (Set.range v) := zRealize_span_eq b X e
  let vM : Free.ChooseBasisIndex ℤ (𝓞 K) × κ → M :=
    fun p => ⟨v p, hM ▸ Submodule.subset_span ⟨p, rfl⟩⟩
  have hvM_li : LinearIndependent ℤ vM := by
    apply LinearIndependent.of_comp M.subtype
    exact hv_liZ
  have hvM_sp : ⊤ ≤ Submodule.span ℤ (Set.range vM) := by
    intro y _
    have hy : (y : EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2)) ∈
        Submodule.span ℤ (Set.range v) := hM ▸ y.2
    rw [Submodule.mem_span_range_iff_exists_fun] at hy
    obtain ⟨c, hc⟩ := hy
    have hy' : y = ∑ p, c p • vM p := by
      apply Subtype.ext
      rw [Submodule.coe_sum]
      simpa [vM] using hc.symm
    rw [hy']
    exact Submodule.sum_mem _ fun p _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨p, rfl⟩)
  let eIdx := Fintype.equivFin (Free.ChooseBasisIndex ℤ (𝓞 K) × κ)
  let bM : Module.Basis (Fin (Fintype.card (Free.ChooseBasisIndex ℤ (𝓞 K) × κ))) ℤ M :=
    (Module.Basis.mk hvM_li hvM_sp).reindex eIdx
  have hbM_coe : ∀ p, (bM p : EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2)) = v (eIdx.symm p) :=
    fun p => by simp [bM, vM]
  have hDisc : DiscreteTopology M := by
    refine discreteTopology_of_fin_basis_real_li bM ?_
    rw [show (fun p => (bM p : EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2))) =
      fun p => v (eIdx.symm p) from funext hbM_coe]
    exact hv_li.comp eIdx.symm eIdx.symm.injective
  have hrk : rk M = Module.finrank ℚ K * Fintype.card κ := by
    unfold rk
    rw [Module.finrank_eq_card_basis bM, Fintype.card_fin, Fintype.card_prod,
      ← Module.finrank_eq_card_basis (RingOfIntegers.basis K), NumberField.RingOfIntegers.rank]
  exact ⟨hDisc, hrk⟩

end AuxiliaryLinearIndep

section LatticeProps

variable {K : Type*} [Field K] [NumberField K]

/-- Every finitely generated `𝓞 K`-submodule `L ≤ V` with invertible frame `X` realizes to a
discrete `ℤ`-lattice in `EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2)`. -/
theorem discreteTopology_zRealize_of_fg {V ι : Type*} [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (L : Submodule (𝓞 K) V) (hL : L.FG) :
    DiscreteTopology (zRealize b X L) := by
  classical
  obtain ⟨S, hS⟩ := hL
  let κ := (S : Set V)
  have hS_fin : Fintype κ := inferInstance
  -- Clear denominators of all coordinates `b.repr s i` for `s ∈ S, i : ι` simultaneously.
  let coords : κ × ι → K := fun p => b.repr (p.1 : V) p.2
  obtain ⟨D, hD_pos, hD⟩ := exists_pos_nat_mul_mem_ringOfIntegers_fin coords
  choose a ha using hD
  let M0 : Submodule (𝓞 K) V := Submodule.span (𝓞 K) (Set.range b)
  have hmem_M0 : ∀ s ∈ S, (D : 𝓞 K) • s ∈ M0 := by
    intro s hs
    have hs_eq : (D : 𝓞 K) • s = ∑ i : ι, a (⟨s, hs⟩, i) • b i := by
      rw [← algebraMap_smul K (D : 𝓞 K) s]
      conv_lhs => rw [← b.sum_repr s, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_smul, show algebraMap (𝓞 K) K (D : 𝓞 K) = (D : K) by simp]
      rw [ha (⟨s, hs⟩, i), ← algebraMap_smul K (a (⟨s, hs⟩, i)) (b i)]
    rw [hs_eq]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hL_le : L ≤ M0.comap (LinearMap.lsmul (𝓞 K) V (D : 𝓞 K)) := by
    rw [← hS, Submodule.span_le]
    intro s hs
    exact hmem_M0 s hs
  have hDL_le : (D : ℤ) • zRealize b X L ≤ zRealize b X M0 := by
    rintro _ ⟨w, ⟨x, hxL, rfl⟩, rfl⟩
    have hDx : (D : 𝓞 K) • x ∈ M0 := hL_le hxL
    refine ⟨(D : 𝓞 K) • x, hDx, ?_⟩
    have hsm : ((D : ℤ) • x : V) = (D : 𝓞 K) • x := by
      rw [← Int.cast_smul_eq_zsmul (𝓞 K)]; simp
    change realizeHLat b X ((D : 𝓞 K) • x) = (D : ℤ) • realizeHLat b X x
    rw [← hsm, map_zsmul]
  have hDiscM0 : DiscreteTopology (zRealize b X M0) :=
    (discrete_and_rk_zRealize_span b X hX b b.linearIndependent).1
  have hDiscDL : DiscreteTopology ↥((D : ℤ) • zRealize b X L) :=
    discreteTopology_of_le hDL_le
  -- `w ↦ (D : ℤ) • w` is a continuous injective map `zRealize b X L → (D : ℤ) • zRealize b X L`.
  let f : ↥(zRealize b X L) → ↥((D : ℤ) • zRealize b X L) :=
    fun w => ⟨(D : ℤ) • w.1, Submodule.smul_mem_pointwise_smul w.1 D _ w.2⟩
  have hf_cont : Continuous f := by
    refine Continuous.subtype_mk ?_ _
    have hfn : (fun w : ↥(zRealize b X L) => (D : ℤ) • (w : EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2))) =
        fun w : ↥(zRealize b X L) => (D : ℝ) • (w : EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2)) := by
      funext w
      rw [← Int.cast_smul_eq_zsmul ℝ]
      simp
    rw [hfn]
    exact (continuous_const_smul (D : ℝ)).comp continuous_subtype_val
  have hf_inj : Function.Injective f := by
    intro w₁ w₂ h
    have h1 : (D : ℝ) • (w₁ : EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2)) =
        (D : ℝ) • (w₂ : EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2)) := by
      have := congrArg Subtype.val h
      simpa [f, ← Int.cast_smul_eq_zsmul ℝ] using this
    exact Subtype.ext (smul_right_injective _ (Nat.cast_ne_zero.mpr hD_pos.ne') h1)
  exact DiscreteTopology.of_continuous_injective hf_cont hf_inj

/-- **Exact `ℤ`-Rank Formula (`rk_zRealize_eq`)**:
for any finitely generated `L : Submodule (𝓞 K) V` with invertible frame `X`,
`rk (zRealize b X L) = [K : ℚ] * rkK L`. -/
theorem rk_zRealize_eq {V ι : Type*} [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (L : Submodule (𝓞 K) V) (hL : L.FG) :
    rk (zRealize b X L) = Module.finrank ℚ K * rkK (K := K) L := by
  classical
  have : Module.Finite K V := Module.Finite.of_basis b
  have hDiscL : DiscreteTopology (zRealize b X L) := discreteTopology_zRealize_of_fg b X hX L hL
  let W := Submodule.span K (L : Set V)
  let r' := Module.finrank K W
  let bW : Module.Basis (Fin r') K W := Module.finBasis K W
  -- Express each `bW j ∈ span K (L : Set V)` as a finite `K`-linear combination of elements of `L`,
  -- and clear denominators to get `e : Fin r' → V` inside `L`!
  have hex : ∀ j : Fin r', ∃ (d : ℕ), 0 < d ∧ (d : K) • (bW j : V) ∈ L := by
    intro j
    have hj : (bW j : V) ∈ Submodule.span K (L : Set V) := (bW j).2
    obtain ⟨c, hcL, hc_sum⟩ := Submodule.mem_span_set.mp hj
    obtain ⟨D, hD_pos, hD⟩ :=
      exists_pos_nat_mul_mem_ringOfIntegers_fin (fun x : c.support => c x)
    choose a ha using hD
    refine ⟨D, hD_pos, ?_⟩
    rw [← hc_sum, Finsupp.sum, Finset.smul_sum]
    refine Submodule.sum_mem L fun x hx => ?_
    rw [smul_smul, ha ⟨x, hx⟩, algebraMap_smul K (a ⟨x, hx⟩) x]
    exact L.smul_mem _ (hcL hx)
  choose d hd_pos hd_mem using hex
  let e : Fin r' → V := fun j => (d j : K) • (bW j : V)
  have he_mem : ∀ j, e j ∈ L := hd_mem
  have he_li : LinearIndependent K e := by
    have h1 : LinearIndependent K (fun j : Fin r' => (bW j : V)) :=
      bW.linearIndependent.map' W.subtype (Submodule.ker_subtype W)
    refine h1.units_smul (fun j => Units.mk0 (d j : K) (Nat.cast_ne_zero.mpr (hd_pos j).ne'))
  have he_span : Submodule.span K (Set.range e) = W := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      exact Submodule.smul_mem W _ (bW j).2
    · have hdim : Module.finrank K (Submodule.span K (Set.range e)) = Module.finrank K W := by
        rw [finrank_span_eq_card he_li, Fintype.card_fin]
      exact le_of_eq (Submodule.eq_of_le_of_finrank_eq
        (Submodule.span_le.mpr (by rintro _ ⟨j, rfl⟩; exact Submodule.smul_mem W _ (bW j).2))
        hdim).symm
  -- Now `M₁ = span (𝓞 K) (range e) ≤ L`, and `(D : 𝓞 K) • L ≤ M₁` for some `D > 0`.
  let M₁ : Submodule (𝓞 K) V := Submodule.span (𝓞 K) (Set.range e)
  have hM₁_le : M₁ ≤ L := Submodule.span_le.mpr (by rintro _ ⟨j, rfl⟩; exact he_mem j)
  let bE : Module.Basis (Fin r') K W :=
    (Module.Basis.span he_li).map (LinearEquiv.ofEq _ _ he_span)
  have hbE_apply : ∀ j : Fin r', (bE j : V) = e j := fun j => by
    simp [bE]
  obtain ⟨S, hS⟩ := hL
  let κ := (S : Set V)
  have hS_fin : Fintype κ := inferInstance
  let coords : κ × Fin r' → K := fun p => bE.repr ⟨(p.1 : V), Submodule.subset_span (by
    rw [← hS]; exact Submodule.subset_span p.1.2)⟩ p.2
  obtain ⟨D, hD_pos, hD⟩ := exists_pos_nat_mul_mem_ringOfIntegers_fin coords
  choose a ha using hD
  have hL_le_M₁ : L ≤ M₁.comap (LinearMap.lsmul (𝓞 K) V (D : 𝓞 K)) := by
    rw [← hS, Submodule.span_le]
    intro y hy
    have hyW : y ∈ W := Submodule.subset_span (hS ▸ Submodule.subset_span hy)
    have hy_eq : y = ∑ j : Fin r', coords (⟨y, hy⟩, j) • e j := by
      have h1 := congrArg Subtype.val (bE.sum_repr ⟨y, hyW⟩)
      rw [Submodule.coe_sum] at h1
      simpa [hbE_apply, coords] using h1.symm
    have hDy : (D : 𝓞 K) • y = ∑ j : Fin r', a (⟨y, hy⟩, j) • e j := by
      rw [← algebraMap_smul K (D : 𝓞 K) y]
      conv_lhs => rw [hy_eq, Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [smul_smul, show algebraMap (𝓞 K) K (D : 𝓞 K) = (D : K) by simp,
        ha (⟨y, hy⟩, j), algebraMap_smul K (a (⟨y, hy⟩, j)) (e j)]
    change (D : 𝓞 K) • y ∈ M₁
    rw [hDy]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  have ⟨hDiscM₁, hrkM₁⟩ := discrete_and_rk_zRealize_span b X hX e he_li
  rw [Fintype.card_fin] at hrkM₁
  have hZ_M₁_le : zRealize b X M₁ ≤ zRealize b X L := zRealize_mono b X hM₁_le
  have hZ_DL_le : (D : ℤ) • zRealize b X L ≤ zRealize b X M₁ := by
    rintro _ ⟨w, ⟨x, hxL, rfl⟩, rfl⟩
    refine ⟨(D : 𝓞 K) • x, hL_le_M₁ hxL, ?_⟩
    have hsm : ((D : ℤ) • x : V) = (D : 𝓞 K) • x := by
      rw [← Int.cast_smul_eq_zsmul (𝓞 K)]; simp
    change realizeHLat b X ((D : 𝓞 K) • x) = (D : ℤ) • realizeHLat b X x
    rw [← hsm, map_zsmul]
  have hDiscDL : DiscreteTopology ↥((D : ℤ) • zRealize b X L) := discreteTopology_of_le hZ_DL_le
  let fD : ↥(zRealize b X L) →ₗ[ℤ] ↥((D : ℤ) • zRealize b X L) :=
    { toFun := fun w => ⟨(D : ℤ) • w.1, Submodule.smul_mem_pointwise_smul w.1 D _ w.2⟩
      map_add' := fun _ _ => Subtype.ext (smul_add _ _ _)
      map_smul' := fun _ _ => Subtype.ext (smul_comm _ _ _) }
  have hfD_bij : Function.Bijective fD := by
    constructor
    · intro w₁ w₂ h
      have h1 : (D : ℝ) • (w₁ : EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2)) =
          (D : ℝ) • (w₂ : EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2)) := by
        have := congrArg Subtype.val h
        simpa [fD, ← Int.cast_smul_eq_zsmul ℝ] using this
      exact Subtype.ext (smul_right_injective _ (Nat.cast_ne_zero.mpr hD_pos.ne') h1)
    · rintro ⟨_, ⟨w, hw, rfl⟩⟩
      exact ⟨⟨w, hw⟩, rfl⟩
  let isoD : ↥(zRealize b X L) ≃ₗ[ℤ] ↥((D : ℤ) • zRealize b X L) :=
    LinearEquiv.ofBijective fD hfD_bij
  have hle1 : rk (zRealize b X M₁) ≤ rk (zRealize b X L) :=
    Submodule.finrank_mono (Submodule.map_mono hM₁_le)
  have hle2 : rk ((D : ℤ) • zRealize b X L) ≤ rk (zRealize b X M₁) :=
    Submodule.finrank_mono hZ_DL_le
  have hrkD : rk (zRealize b X L) = rk ((D : ℤ) • zRealize b X L) := isoD.finrank_eq
  rw [← hrkD, hrkM₁] at hle2
  rw [hrkM₁] at hle1
  change rk (zRealize b X L) = Module.finrank ℚ K * r'
  exact le_antisymm hle2 hle1

/-- For a totally complex number field `K`, `2 * card (InfinitePlace K) = [K : ℚ]`. -/
theorem two_mul_card_infinitePlace [IsTotallyComplex K] :
    2 * Fintype.card (InfinitePlace K) = Module.finrank ℚ K := by
  have h1 := InfinitePlace.card_add_two_mul_card_eq_rank K
  have h2 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces K
  have h0 : InfinitePlace.nrRealPlaces K = 0 := IsTotallyComplex.nrRealPlaces_eq_zero K
  omega

/-- For a totally complex number field `K` and a good `HLat K`, `A.zRealize` is a full
`IsZLattice ℝ` in `EuclideanSpace ℝ (InfinitePlace K × A.ι × Fin 2)`. -/
theorem isZLattice_zRealize_of_good [IsTotallyComplex K] {V ι : Type*}
    [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (L : Submodule (𝓞 K) V)
    (hL : L.FG) (hsp : Submodule.span K (L : Set V) = ⊤)
    [DiscreteTopology (zRealize b X L)] :
    IsZLattice ℝ (zRealize b X L) := by
  constructor
  let Z : Submodule ℤ (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2)) := zRealize b X L
  have hfin : Module.finrank ℝ
      (Submodule.span ℝ (Z : Set (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2)))) =
      Module.finrank ℝ (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2)) := by
    rw [← finrank_int_eq_finrank_real_span Z]
    change rk (zRealize b X L) = _
    rw [rk_zRealize_eq b X hX L hL]
    unfold rkK
    rw [hsp, finrank_top, Module.finrank_eq_card_basis b,
      Module.finrank_eq_card_basis (EuclideanSpace.basisFun (InfinitePlace K × ι × Fin 2) ℝ).toBasis,
      Fintype.card_prod, Fintype.card_prod, Fintype.card_fin]
    have hcard := two_mul_card_infinitePlace (K := K)
    nlinarith
  exact Submodule.eq_top_of_finrank_eq hfin

/-- Bridge from `HLat K` with `hG : A.Good` to `Stage12SchurWeylLattices.NumberFieldHLat K`. -/
def toNumberFieldHLat {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] [StarRing K]
    (A : HLat K) (hG : A.Good) : NumberFieldHLat K where
  V := A.V
  ι := A.ι
  b := A.b
  X := A.X
  hX := hG.1
  L := A.L
  discReal := discreteTopology_zRealize_of_fg A.b A.X hG.1 A.L hG.2.1
  zlatReal :=
    letI := discreteTopology_zRealize_of_fg A.b A.X hG.1 A.L hG.2.1
    isZLattice_zRealize_of_good A.b A.X hG.1 A.L hG.2.1 hG.2.2

/-- **Grounding on Mathlib `ZLattice.covolume` (`covolHLat_eq_zlattice_covolume`)**:
for any good `HLat K`, `ArakelovCovolume.covol A.zRealize` equals Mathlib's `ZLattice.covolume`
under the canonical coordinate equivalence `(InfinitePlace K × A.ι × Fin 2) ≃ Fin d`. -/
theorem covolHLat_eq_zlattice_covolume {K : Type} [Field K] [NumberField K]
    [IsTotallyComplex K] [StarRing K] (A : HLat K) (hG : A.Good) :
    let e : (InfinitePlace K × A.ι × Fin 2) ≃ Fin (Fintype.card (InfinitePlace K × A.ι × Fin 2)) :=
      Fintype.equivFin _
    let iso : EuclideanSpace ℝ (InfinitePlace K × A.ι × Fin 2) ≃ₗᵢ[ℝ]
        EuclideanSpace ℝ (Fin (Fintype.card (InfinitePlace K × A.ι × Fin 2))) :=
      euclideanSpaceCongr e
    let Λ := A.zRealize.map (iso.toLinearEquiv.toLinearMap.restrictScalars ℤ)
    ∃ (_ : DiscreteTopology Λ) (_ : IsZLattice ℝ Λ),
      covol A.zRealize = ZLattice.covolume Λ volume :=
  (toNumberFieldHLat A hG).covol_eq_zlattice_covolume

/-- `𝓞 K`-saturation of `N ≤ L` inside `L`: `L ∩ span_K(N)`. -/
def satO {V : Type*} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] (L N : Submodule (𝓞 K) V) : Submodule (𝓞 K) V :=
  L ⊓ (Submodule.span K (N : Set V)).restrictScalars (𝓞 K)

lemma le_satO {V : Type*} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] {L N : Submodule (𝓞 K) V} (hNL : N ≤ L) :
    N ≤ satO (K := K) L N :=
  fun _ hx => ⟨hNL hx, Submodule.subset_span hx⟩

lemma satO_le {V : Type*} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] (L N : Submodule (𝓞 K) V) : satO (K := K) L N ≤ L :=
  inf_le_left

lemma span_K_satO {V : Type*} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] {L N : Submodule (𝓞 K) V} (hNL : N ≤ L) :
    Submodule.span K ((satO (K := K) L N : Submodule (𝓞 K) V) : Set V) =
      Submodule.span K (N : Set V) := by
  apply le_antisymm
  · exact Submodule.span_le.mpr fun _ hx => hx.2
  · exact Submodule.span_mono (le_satO hNL)

lemma rkK_satO {V : Type*} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] {L N : Submodule (𝓞 K) V} (hNL : N ≤ L) :
    rkK (K := K) (satO (K := K) L N) = rkK (K := K) N := by
  unfold rkK
  rw [span_K_satO hNL]

/-- **Exact Saturation Correspondence**:
`saturation (zRealize b X L) (zRealize b X N) = zRealize b X (satO L N)`. -/
theorem saturation_zRealize_eq {V ι : Type*} [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) {L N : Submodule (𝓞 K) V} (hNL : N ≤ L) :
    saturation (zRealize b X L) (zRealize b X N) = zRealize b X (satO (K := K) L N) := by
  classical
  let _ := hNL
  have : Module.Finite K V := Module.Finite.of_basis b
  apply le_antisymm
  · rintro _ ⟨⟨x, hxL, rfl⟩, hxsp⟩
    refine ⟨x, ⟨hxL, ?_⟩, rfl⟩
    let WN := Submodule.span K (N : Set V)
    let rN := Module.finrank K WN
    let bN : Module.Basis (Fin rN) K WN := Module.finBasis K WN
    have hliN : LinearIndependent K (fun j : Fin rN => (bN j : V)) :=
      bN.linearIndependent.map' WN.subtype (Submodule.ker_subtype WN)
    obtain ⟨WC, hWC⟩ := Submodule.exists_isCompl WN
    let rC := Module.finrank K WC
    let bC : Module.Basis (Fin rC) K WC := Module.finBasis K WC
    let e : Fin rN ⊕ Fin rC → V := Sum.elim (fun j => (bN j : V)) (fun k => (bC k : V))
    have he_li : LinearIndependent K e := by
      rw [Fintype.linearIndependent_iff]
      intro c hc
      have hsplit : ∑ j : Fin rN, c (Sum.inl j) • (bN j : V) +
          ∑ k : Fin rC, c (Sum.inr k) • (bC k : V) = 0 := by
        simpa [e, Fintype.sum_sum_type] using hc
      have h1 : ∑ j : Fin rN, c (Sum.inl j) • (bN j : V) ∈ WN :=
        Submodule.sum_mem WN fun j _ => Submodule.smul_mem WN _ (bN j).2
      have h2 : ∑ k : Fin rC, c (Sum.inr k) • (bC k : V) ∈ WC :=
        Submodule.sum_mem WC fun k _ => Submodule.smul_mem WC _ (bC k).2
      have h1eq : ∑ j : Fin rN, c (Sum.inl j) • (bN j : V) =
          -(∑ k : Fin rC, c (Sum.inr k) • (bC k : V)) := eq_neg_of_add_eq_zero_left hsplit
      have hmem : ∑ j : Fin rN, c (Sum.inl j) • (bN j : V) ∈ WN ⊓ WC :=
        ⟨h1, h1eq ▸ WC.neg_mem h2⟩
      rw [hWC.inf_eq_bot, Submodule.mem_bot] at hmem
      have h2eq : ∑ k : Fin rC, c (Sum.inr k) • (bC k : V) = 0 := by
        rw [hmem, zero_add] at hsplit; exact hsplit
      have hcN : ∀ j, c (Sum.inl j) = 0 := fun j =>
        Fintype.linearIndependent_iff.mp hliN (fun j => c (Sum.inl j)) hmem j
      have hliC : LinearIndependent K (fun k : Fin rC => (bC k : V)) :=
        bC.linearIndependent.map' WC.subtype (Submodule.ker_subtype WC)
      have hcC : ∀ k, c (Sum.inr k) = 0 := fun k =>
        Fintype.linearIndependent_iff.mp hliC (fun k => c (Sum.inr k)) h2eq k
      rintro (j | k)
      · exact hcN j
      · exact hcC k
    have he_sp : ⊤ ≤ Submodule.span K (Set.range e) := by
      intro v _
      have hv : v ∈ WN ⊔ WC := hWC.sup_eq_top ▸ trivial
      rw [Submodule.mem_sup] at hv
      obtain ⟨wN, hwN, wC, hwC, rfl⟩ := hv
      have hwN' : wN ∈ Submodule.span K (Set.range (fun j : Fin rN => (bN j : V))) := by
        have h1 := congrArg Subtype.val (bN.sum_repr ⟨wN, hwN⟩)
        simp only [Submodule.coe_sum] at h1
        change (∑ i, (bN.repr ⟨wN, hwN⟩) i • (bN i : V)) = wN at h1
        rw [← h1]
        exact Submodule.sum_mem _ fun j _ =>
          Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
      have hwC' : wC ∈ Submodule.span K (Set.range (fun k : Fin rC => (bC k : V))) := by
        have h1 := congrArg Subtype.val (bC.sum_repr ⟨wC, hwC⟩)
        simp only [Submodule.coe_sum] at h1
        change (∑ i, (bC.repr ⟨wC, hwC⟩) i • (bC i : V)) = wC at h1
        rw [← h1]
        exact Submodule.sum_mem _ fun k _ =>
          Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
      exact Submodule.add_mem _
        (Submodule.span_mono (by rintro _ ⟨j, rfl⟩; exact ⟨Sum.inl j, rfl⟩) hwN')
        (Submodule.span_mono (by rintro _ ⟨k, rfl⟩; exact ⟨Sum.inr k, rfl⟩) hwC')
    let bE : Module.Basis (Fin rN ⊕ Fin rC) K V := Module.Basis.mk he_li he_sp
    -- Express `x = ∑ q, bE.repr x q • e q` and clear denominators with `D > 0`.
    obtain ⟨D, hD_pos, hD⟩ := exists_pos_nat_mul_mem_ringOfIntegers_fin (fun q => bE.repr x q)
    choose a ha using hD
    have hDx_real : realizeHLat b X ((D : K) • x) = (D : ℝ) • realizeHLat b X x := by
      simpa using realizeHLat_smul_rat b X (D : ℚ) x
    have hDx_sp : realizeHLat b X ((D : K) • x) ∈
        Submodule.span ℝ (Set.range fun p : Free.ChooseBasisIndex ℤ (𝓞 K) × Fin rN =>
          realizeHLat b X (NumberField.integralBasis K p.1 • (bN p.2 : V))) := by
      have h1 : realizeHLat b X ((D : K) • x) ∈ Submodule.span ℝ (zRealize b X N : Set _) := by
        rw [hDx_real]
        exact Submodule.smul_mem _ _ hxsp
      have h2 : Submodule.span ℝ (zRealize b X N : Set _) ≤
          Submodule.span ℝ (Set.range fun p : Free.ChooseBasisIndex ℤ (𝓞 K) × Fin rN =>
            realizeHLat b X (NumberField.integralBasis K p.1 • (bN p.2 : V))) := by
        rw [Submodule.span_le]
        rintro _ ⟨y, hyN, rfl⟩
        have hyWN : y ∈ WN := Submodule.subset_span hyN
        have hy_eq : y = ∑ j : Fin rN, bN.repr ⟨y, hyWN⟩ j • (bN j : V) := by
          have := congrArg Subtype.val (bN.sum_repr ⟨y, hyWN⟩)
          rw [Submodule.coe_sum] at this
          exact this.symm
        obtain ⟨D', hD'_pos, hD'⟩ :=
          exists_pos_nat_mul_mem_ringOfIntegers_fin (fun j => bN.repr ⟨y, hyWN⟩ j)
        choose a' ha' using hD'
        have hDy : (D' : K) • y = ∑ j : Fin rN, ∑ k : Free.ChooseBasisIndex ℤ (𝓞 K),
            ((RingOfIntegers.basis K).repr (a' j) k : ℤ) •
              (NumberField.integralBasis K k • (bN j : V)) := by
          rw [hy_eq, Finset.smul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [smul_smul, ha' j]
          have ha'_eq : a' j = ∑ k, ((RingOfIntegers.basis K).repr (a' j) k) •
              RingOfIntegers.basis K k := ((RingOfIntegers.basis K).sum_repr (a' j)).symm
          rw [algebraMap_smul K (a' j) (bN j : V)]
          conv_lhs => rw [ha'_eq, Finset.sum_smul]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [smul_assoc, NumberField.integralBasis_apply, algebraMap_smul]
        have hDy_real : (D' : ℝ) • realizeHLat b X y =
            ∑ j : Fin rN, ∑ k : Free.ChooseBasisIndex ℤ (𝓞 K),
              (((RingOfIntegers.basis K).repr (a' j) k : ℤ) : ℝ) •
                realizeHLat b X (NumberField.integralBasis K k • (bN j : V)) := by
          have hrat := realizeHLat_smul_rat b X (D' : ℚ) y
          simp only [map_natCast, Rat.cast_natCast] at hrat
          rw [← hrat]
          have hmap := congrArg (realizeHLat b X) hDy
          simpa [map_sum, map_zsmul, Int.cast_smul_eq_zsmul] using hmap
        have hmem_sp : (D' : ℝ) • realizeHLat b X y ∈
            Submodule.span ℝ (Set.range fun p : Free.ChooseBasisIndex ℤ (𝓞 K) × Fin rN =>
              realizeHLat b X (NumberField.integralBasis K p.1 • (bN p.2 : V))) := by
          rw [hDy_real]
          exact Submodule.sum_mem _ fun j _ => Submodule.sum_mem _ fun k _ =>
            Submodule.smul_mem _ _ (Submodule.subset_span ⟨(k, j), rfl⟩)
        have hinv := Submodule.smul_mem _ (D' : ℝ)⁻¹ hmem_sp
        rwa [inv_smul_smul₀ (Nat.cast_ne_zero.mpr hD'_pos.ne')] at hinv
      exact h2 h1
    rw [Submodule.mem_span_range_iff_exists_fun] at hDx_sp
    obtain ⟨c, hc⟩ := hDx_sp
    have hbE_eq : ∀ q : Fin rN ⊕ Fin rC, bE q = e q := fun q => by simp [bE]
    have hDx_exp : (D : K) • x = ∑ q : Fin rN ⊕ Fin rC, ∑ k : Free.ChooseBasisIndex ℤ (𝓞 K),
        ((RingOfIntegers.basis K).repr (a q) k : ℤ) •
          (NumberField.integralBasis K k • e q) := by
      conv_lhs => rw [← bE.sum_repr x, Finset.smul_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [smul_smul, ha q, hbE_eq q, algebraMap_smul K (a q) (e q)]
      have ha_eq : a q = ∑ k, ((RingOfIntegers.basis K).repr (a q) k) •
          RingOfIntegers.basis K k := ((RingOfIntegers.basis K).sum_repr (a q)).symm
      conv_lhs => rw [ha_eq, Finset.sum_smul]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [smul_assoc, NumberField.integralBasis_apply, algebraMap_smul]
    have hDx_real_exp : realizeHLat b X ((D : K) • x) =
        ∑ q : Fin rN ⊕ Fin rC, ∑ k : Free.ChooseBasisIndex ℤ (𝓞 K),
          (((RingOfIntegers.basis K).repr (a q) k : ℤ) : ℝ) •
            realizeHLat b X (NumberField.integralBasis K k • e q) := by
      have hmap := congrArg (realizeHLat b X) hDx_exp
      simpa [map_sum, map_zsmul, Int.cast_smul_eq_zsmul] using hmap
    let t : Free.ChooseBasisIndex ℤ (𝓞 K) × (Fin rN ⊕ Fin rC) → ℝ :=
      fun p => (((RingOfIntegers.basis K).repr (a p.2) p.1 : ℤ) : ℝ) -
        match p.2 with
        | Sum.inl j => c (p.1, j)
        | Sum.inr _ => 0
    have ht_zero : ∑ p : Free.ChooseBasisIndex ℤ (𝓞 K) × (Fin rN ⊕ Fin rC),
        t p • realizeHLat b X (NumberField.integralBasis K p.1 • e p.2) = 0 := by
      have heq : ∑ p : Free.ChooseBasisIndex ℤ (𝓞 K) × (Fin rN ⊕ Fin rC),
          (((RingOfIntegers.basis K).repr (a p.2) p.1 : ℤ) : ℝ) •
            realizeHLat b X (NumberField.integralBasis K p.1 • e p.2) =
          ∑ p : Free.ChooseBasisIndex ℤ (𝓞 K) × (Fin rN ⊕ Fin rC),
            (match p.2 with | Sum.inl j => c (p.1, j) | Sum.inr _ => 0) •
              realizeHLat b X (NumberField.integralBasis K p.1 • e p.2) := by
        rw [Fintype.sum_prod_type, Finset.sum_comm, ← hDx_real_exp, ← hc, Fintype.sum_prod_type,
          Fintype.sum_prod_type]
        simp only [Fintype.sum_sum_type, zero_smul, Finset.sum_const_zero, add_zero, e,
          Sum.elim_inl]
      simp only [t, sub_smul, Finset.sum_sub_distrib, heq, sub_self]
    have ht_coeff := Fintype.linearIndependent_iff.mp
      (linearIndependent_realizeHLat_integralBasis b X hX e he_li) t ht_zero
    have hC_zero : ∀ k : Fin rC, bE.repr x (Sum.inr k) = 0 := by
      intro k
      have hak : ∀ j, ((RingOfIntegers.basis K).repr (a (Sum.inr k)) j : ℤ) = 0 := by
        intro j
        have h1 := ht_coeff (j, Sum.inr k)
        simp only [t, sub_zero] at h1
        exact_mod_cast h1
      have ha0 : a (Sum.inr k) = 0 := by
        rw [← (RingOfIntegers.basis K).sum_repr (a (Sum.inr k))]
        refine Finset.sum_eq_zero fun j _ => by rw [hak j, zero_smul]
      have hDk : (D : K) * bE.repr x (Sum.inr k) = 0 := by
        rw [ha (Sum.inr k), ha0]; simp
      exact (mul_eq_zero.mp hDk).resolve_left (Nat.cast_ne_zero.mpr hD_pos.ne')
    have hx_in_WN : x = ∑ j : Fin rN, bE.repr x (Sum.inl j) • (bN j : V) := by
      conv_lhs => rw [← bE.sum_repr x]
      rw [Fintype.sum_sum_type]
      have hzero : ∑ k : Fin rC, bE.repr x (Sum.inr k) • bE (Sum.inr k) = 0 :=
        Finset.sum_eq_zero fun k _ => by rw [hC_zero k, zero_smul]
      rw [hzero, add_zero]
      refine Finset.sum_congr rfl fun j _ => by simp [bE, e]
    rw [hx_in_WN]
    exact Submodule.sum_mem WN fun j _ => Submodule.smul_mem WN _ (bN j).2
  · rintro _ ⟨x, ⟨hxL, hxWN⟩, rfl⟩
    refine ⟨⟨x, hxL, rfl⟩, ?_⟩
    have hx_sp : x ∈ Submodule.span K (N : Set V) := hxWN
    rw [Submodule.mem_span_set] at hx_sp
    obtain ⟨c, hcN, hc_sum⟩ := hx_sp
    obtain ⟨D, hD_pos, hD⟩ := exists_pos_nat_mul_mem_ringOfIntegers_fin (fun y : c.support => c y)
    choose a ha using hD
    have hDx : (D : K) • x ∈ N := by
      rw [← hc_sum, Finsupp.sum, Finset.smul_sum]
      refine Submodule.sum_mem N fun y hy => ?_
      rw [smul_smul, ha ⟨y, hy⟩, algebraMap_smul K (a ⟨y, hy⟩) y]
      exact N.smul_mem _ (hcN hy)
    have hDx_mem : (D : ℝ) • realizeHLat b X x ∈ Submodule.span ℝ ((zRealize b X N : Submodule ℤ _) : Set _) := by
      have hrat := realizeHLat_smul_rat b X (D : ℚ) x
      simp only [map_natCast, Rat.cast_natCast] at hrat
      rw [← hrat]
      exact Submodule.subset_span ⟨(D : K) • x, hDx, rfl⟩
    have hinv := Submodule.smul_mem _ (D : ℝ)⁻¹ hDx_mem
    rwa [inv_smul_smul₀ (Nat.cast_ne_zero.mpr hD_pos.ne' : (D : ℝ) ≠ 0)] at hinv

/-! ### Ideal-Twist Index Formula (`[M : 𝔟 • M] = (Ideal.absNorm 𝔟) ^ rkK M`) -/

section IdealTwistIndex

attribute [local instance] Ideal.Quotient.field

variable {V : Type*} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] [FiniteDimensional K V]

lemma twist_span_smul (M : Submodule (𝓞 K) V) (𝔞 : Ideal (𝓞 K)) (h𝔞 : 𝔞 ≠ ⊥) :
    Submodule.span K ((𝔞 • M : Submodule (𝓞 K) V) : Set V) = Submodule.span K (M : Set V) := by
  apply le_antisymm
  · exact Submodule.span_mono Submodule.smul_le_right
  · rw [Submodule.span_le]
    intro x hx
    obtain ⟨α, hα, hα0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h𝔞
    have hmem : α • x ∈ 𝔞 • M := Submodule.smul_mem_smul hα hx
    have hK : (algebraMap (𝓞 K) K α) ≠ 0 :=
      (FaithfulSMul.algebraMap_injective (𝓞 K) K).ne hα0
    have hx' : x = (algebraMap (𝓞 K) K α)⁻¹ • (α • x) := by
      rw [← algebraMap_smul K α x, smul_smul, inv_mul_cancel₀ hK, one_smul]
    rw [SetLike.mem_coe, hx']
    exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)

lemma twist_prime_le (M : Submodule (𝓞 K) V) (hM : M.FG) (𝔭 : Ideal (𝓞 K))
    [h𝔭 : 𝔭.IsMaximal] (h0 : 𝔭 ≠ ⊥) :
    (𝔭 • M).toAddSubgroup.relIndex M.toAddSubgroup ≤
      Ideal.absNorm 𝔭 ^ rkK (K := K) M := by
  change Nat.card (M ⧸ (𝔭 • M).comap M.subtype) ≤ _
  let e : (M ⧸ (𝔭 • M).comap M.subtype) ≃ₗ[𝓞 K] (M ⧸ (𝔭 • (⊤ : Submodule (𝓞 K) M))) :=
    Submodule.quotEquivOfEq _ _ (Submodule.map_injective_of_injective M.injective_subtype
      (by simp [Submodule.smul_le_right]))
  rw [Nat.card_congr e.toEquiv]
  have : Module.Finite (𝓞 K) M := Module.Finite.iff_fg.mpr hM
  have : Finite (𝓞 K ⧸ 𝔭) := (Ideal.absNorm_ne_zero_iff 𝔭).1
    (fun h => h0 (Ideal.absNorm_eq_zero_iff.1 h))
  have : Module.Finite (𝓞 K ⧸ 𝔭) (M ⧸ (𝔭 • (⊤ : Submodule (𝓞 K) M))) :=
    Module.Finite.of_restrictScalars_finite (𝓞 K) _ _
  have : Finite (M ⧸ (𝔭 • (⊤ : Submodule (𝓞 K) M))) := Module.finite_of_finite (𝓞 K ⧸ 𝔭)
  have hcard : Nat.card (M ⧸ (𝔭 • (⊤ : Submodule (𝓞 K) M))) =
      Nat.card (𝓞 K ⧸ 𝔭) ^ Module.finrank (𝓞 K ⧸ 𝔭) (M ⧸ (𝔭 • (⊤ : Submodule (𝓞 K) M))) := by
    haveI := Fintype.ofFinite (M ⧸ (𝔭 • (⊤ : Submodule (𝓞 K) M)))
    haveI := Fintype.ofFinite (𝓞 K ⧸ 𝔭)
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    exact Module.card_eq_pow_finrank
  have hN : Nat.card (𝓞 K ⧸ 𝔭) = Ideal.absNorm 𝔭 := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  rw [hcard, hN]
  apply Nat.pow_le_pow_right (Nat.pos_of_ne_zero (fun h => h0 (Ideal.absNorm_eq_zero_iff.1 h)))
  let B := Module.finBasis (𝓞 K ⧸ 𝔭) (M ⧸ (𝔭 • (⊤ : Submodule (𝓞 K) M)))
  have hsurj := Submodule.mkQ_surjective (𝔭 • (⊤ : Submodule (𝓞 K) M))
  choose b' hb' using fun i => hsurj (B i)
  have hli : LinearIndependent (𝓞 K ⧸ 𝔭)
      ((Submodule.mkQ (𝔭 • (⊤ : Submodule (𝓞 K) M))) ∘ b') := by
    have : (Submodule.mkQ (𝔭 • (⊤ : Submodule (𝓞 K) M))) ∘ b' = B := funext hb'
    rw [this]; exact B.linearIndependent
  have hg_li : LinearIndependent K (fun i => (b' i : V)) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    by_contra hc_ne
    have hex : ∃ i₀, c i₀ ≠ 0 := by
      by_contra hall
      apply hc_ne; intro i; by_contra hi; exact hall ⟨i, hi⟩
    obtain ⟨i₀, hi₀⟩ := hex
    obtain ⟨D, hD_pos, hD⟩ := exists_pos_nat_mul_mem_ringOfIntegers_fin c
    choose a ha using hD
    have ha_ne : a i₀ ≠ 0 := by
      intro h0
      have h1 : (D : K) * c i₀ = 0 := by rw [ha i₀, h0]; simp
      exact hi₀ ((mul_eq_zero.mp h1).resolve_left (Nat.cast_ne_zero.mpr hD_pos.ne'))
    have ha_sum : ∑ i, (a i : K) • (b' i : V) = 0 := by
      have h1 := congrArg (fun v : V => (D : K) • v) hc
      rw [smul_zero, Finset.smul_sum] at h1
      rw [← h1]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_smul, ha i]
    let I : Ideal (𝓞 K) := Ideal.span (Set.range a)
    have hI0 : I ≠ ⊥ := by
      intro hbot
      have hmem : a i₀ ∈ I := Ideal.subset_span (Set.mem_range_self i₀)
      rw [hbot, Submodule.mem_bot] at hmem
      exact ha_ne hmem
    have hnorm_ge : 2 ≤ Ideal.absNorm 𝔭 := by
      have h1 : Ideal.absNorm 𝔭 ≠ 0 := fun h => h0 (Ideal.absNorm_eq_zero_iff.mp h)
      have h2 : Ideal.absNorm 𝔭 ≠ 1 := fun h => h𝔭.ne_top (Ideal.absNorm_eq_one_iff.mp h)
      omega
    classical
    have hnot_all : ∃ k : ℕ, ¬ (I ≤ 𝔭 ^ (k + 1)) := by
      refine ⟨Ideal.absNorm I, fun hle => ?_⟩
      have hdvd : (Ideal.absNorm 𝔭) ^ (Ideal.absNorm I + 1) ∣ Ideal.absNorm I := by
        rw [← map_pow Ideal.absNorm]
        exact Ideal.absNorm_dvd_absNorm_of_le hle
      have hIpos : 0 < Ideal.absNorm I :=
        Nat.pos_of_ne_zero (fun h => hI0 (Ideal.absNorm_eq_zero_iff.mp h))
      have hpow_le : (Ideal.absNorm 𝔭) ^ (Ideal.absNorm I + 1) ≤ Ideal.absNorm I :=
        Nat.le_of_dvd hIpos hdvd
      have h2pow : 2 ^ (Ideal.absNorm I + 1) ≤ (Ideal.absNorm 𝔭) ^ (Ideal.absNorm I + 1) :=
        Nat.pow_le_pow_left hnorm_ge _
      have hlt : Ideal.absNorm I + 1 < 2 ^ (Ideal.absNorm I + 1) := Nat.lt_two_pow_self
      omega
    let k := Nat.find hnot_all
    have hk_le : I ≤ 𝔭 ^ k := by
      rcases Nat.eq_zero_or_pos k with hk0 | hkpos
      · rw [hk0]; simp
      · exact not_not.mp fun hnot => by
          have hk_lt : k - 1 < Nat.find hnot_all := Nat.sub_lt hkpos zero_lt_one
          have h1 : ¬ I ≤ 𝔭 ^ (k - 1 + 1) := by rwa [Nat.sub_add_cancel hkpos]
          exact Nat.find_min hnot_all hk_lt h1
    have hk_not : ¬ (I ≤ 𝔭 ^ (k + 1)) := Nat.find_spec hnot_all
    have hpk0 : (𝔭 ^ k : Ideal (𝓞 K)) ≠ ⊥ := pow_ne_zero k h0
    have hpk_frac0 : ((𝔭 ^ k : Ideal (𝓞 K)) : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ≠ 0 := by
      simpa using hpk0
    let J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K :=
      ((𝔭 ^ k : Ideal (𝓞 K)) : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)⁻¹ *
        (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)
    have hJ_not : ¬ (J ≤ (𝔭 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)) := by
      intro hJle
      apply hk_not
      have hmul : ((𝔭 ^ k : Ideal (𝓞 K)) : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) * J ≤
          ((𝔭 ^ k : Ideal (𝓞 K)) : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) *
            (𝔭 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) := by
        intro z hz
        rw [← FractionalIdeal.mem_coe, FractionalIdeal.coe_mul] at hz ⊢
        exact Submodule.mul_induction_on hz
          (fun a ha b hb => Submodule.mul_mem_mul ha (hJle hb))
          (fun x y hx hy => Submodule.add_mem _ hx hy)
      have hleft : ((𝔭 ^ k : Ideal (𝓞 K)) : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) * J =
          (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) := by
        dsimp only [J]
        rw [← mul_assoc, mul_inv_cancel₀ hpk_frac0, one_mul]
      rw [hleft, ← FractionalIdeal.coeIdeal_mul] at hmul
      rw [pow_succ]
      exact (FractionalIdeal.coeIdeal_le_coeIdeal K).mp hmul
    have hex_t : ∃ t ∈ ((𝔭 ^ k : Ideal (𝓞 K)) : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)⁻¹,
        ∃ j, t * (a j : K) ∉ (𝔭 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) := by
      by_contra hall
      push Not at hall
      apply hJ_not
      intro z hz
      rw [← FractionalIdeal.mem_coe, FractionalIdeal.coe_mul] at hz
      refine Submodule.mul_induction_on hz ?_ ?_
      · intro t ht u hu
        obtain ⟨u₀, hu₀, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).mp hu
        have hu_span : u₀ ∈ Ideal.span (Set.range a) := hu₀
        rw [Ideal.mem_span_range_iff_exists_fun] at hu_span
        obtain ⟨r, rfl⟩ := hu_span
        have hsum : t * (algebraMap (𝓞 K) K (∑ i, r i * a i)) =
            ∑ i, (algebraMap (𝓞 K) K (r i)) * (t * (a i : K)) := by
          simp only [map_sum, map_mul, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => by ring
        rw [hsum]
        refine Submodule.sum_mem _ fun i _ => ?_
        have hmem_p := hall t ht i
        have hr_mem : (algebraMap (𝓞 K) K (r i)) ∈ (1 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) :=
          (FractionalIdeal.mem_one_iff _).mpr ⟨r i, rfl⟩
        have hprod := FractionalIdeal.mul_mem_mul hr_mem hmem_p
        rwa [one_mul] at hprod
      · intro z₁ z₂ h₁ h₂
        exact Submodule.add_mem _ h₁ h₂
    obtain ⟨t, ht, j₀, hj₀⟩ := hex_t
    have hd_ex : ∀ i, ∃ d : 𝓞 K, t * (a i : K) = (d : K) := by
      intro i
      have h1 : (algebraMap (𝓞 K) K (a i)) ∈
          ((𝔭 ^ k : Ideal (𝓞 K)) : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) :=
        (FractionalIdeal.mem_coeIdeal _).mpr
          ⟨a i, hk_le (Ideal.subset_span (Set.mem_range_self i)), rfl⟩
      have h2 := FractionalIdeal.mul_mem_mul ht h1
      rw [inv_mul_cancel₀ hpk_frac0] at h2
      obtain ⟨d, hd⟩ := (FractionalIdeal.mem_one_iff (nonZeroDivisors (𝓞 K))).mp h2
      exact ⟨d, hd.symm⟩
    choose d hd using hd_ex
    have hj₀_not : d j₀ ∉ 𝔭 := by
      intro hmem
      apply hj₀
      rw [hd j₀]
      exact (FractionalIdeal.mem_coeIdeal _).mpr ⟨d j₀, hmem, rfl⟩
    have hd_sumV : ∑ i, (d i : K) • (b' i : V) = 0 := by
      have h1 : ∑ i, (d i : K) • (b' i : V) = t • ∑ i, (a i : K) • (b' i : V) := by
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [smul_smul, ← hd i]
      rw [h1, ha_sum, smul_zero]
    have hd_sumM : ∑ i, d i • b' i = 0 := by
      apply Subtype.ext
      rw [Submodule.coe_sum, Submodule.coe_zero, ← hd_sumV]
      refine Finset.sum_congr rfl fun i _ => ?_
      exact (algebraMap_smul K (d i) (b' i : V)).symm
    have hq_sum : ∑ i, (algebraMap (𝓞 K) (𝓞 K ⧸ 𝔭) (d i)) • B i = 0 := by
      have hmap := congrArg (Submodule.mkQ (𝔭 • (⊤ : Submodule (𝓞 K) M))) hd_sumM
      rw [map_zero, map_sum] at hmap
      rw [← hmap]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, hb' i, algebraMap_smul]
    have hcoeff := Fintype.linearIndependent_iff.mp B.linearIndependent
      (fun i => algebraMap (𝓞 K) (𝓞 K ⧸ 𝔭) (d i)) hq_sum j₀
    rw [Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem] at hcoeff
    exact hj₀_not hcoeff
  let g : _ → Submodule.span K (M : Set V) :=
    fun i => ⟨(b' i : V), Submodule.subset_span (b' i).2⟩
  have hg : LinearIndependent K g :=
    LinearIndependent.of_comp (Submodule.span K (M : Set V)).subtype hg_li
  simpa [rkK] using hg.fintype_card_le_finrank

lemma twist_le (𝔟 : Ideal (𝓞 K)) (h𝔟 : 𝔟 ≠ ⊥) : ∀ (M : Submodule (𝓞 K) V), M.FG →
    (𝔟 • M).toAddSubgroup.relIndex M.toAddSubgroup ≤
      Ideal.absNorm 𝔟 ^ rkK (K := K) M := by
  revert h𝔟
  refine UniqueFactorizationMonoid.induction_on_prime 𝔟 ?_ ?_ ?_
  · intro h; exact absurd Submodule.zero_eq_bot h
  · intro x hx _ M _
    rw [Ideal.isUnit_iff.1 hx, Submodule.top_smul, Ideal.absNorm_top, one_pow,
      AddSubgroup.relIndex_self]
  · intro a p ha hp ih _ M hM
    have hpb : p ≠ ⊥ := hp.ne_zero
    have hab : a ≠ ⊥ := ha
    haveI : p.IsMaximal := (Ideal.isPrime_of_prime hp).isMaximal hpb
    rw [Submodule.mul_smul, ← AddSubgroup.relIndex_mul_relIndex (p • a • M).toAddSubgroup
      (a • M).toAddSubgroup M.toAddSubgroup ((Submodule.toAddSubgroup_le _ _).2 Submodule.smul_le_right)
      ((Submodule.toAddSubgroup_le _ _).2 Submodule.smul_le_right)]
    have h1 := twist_prime_le (K := K) (a • M) (Submodule.FG.smul (IsNoetherian.noetherian a) hM) p hpb
    rw [show rkK (K := K) (a • M) = rkK (K := K) M from by unfold rkK; rw [twist_span_smul M a hab]] at h1
    have h2 := ih hab M hM
    rw [map_mul, mul_pow]
    exact Nat.mul_le_mul h1 h2

lemma twist_finrank_int (M : Submodule (𝓞 K) V) (hM : M.FG) :
    Module.finrank ℤ M = Module.finrank ℚ K * rkK (K := K) M := by
  let b := Module.finBasis K V
  let Xf : InfinitePlace K → Matrix (Fin (Module.finrank K V)) (Fin (Module.finrank K V)) ℂ :=
    fun _ => 1
  have hXf : ∀ v, IsUnit (Xf v).det := fun v => by simp [Xf]
  have hinj := realizeHLat_injective b Xf hXf
  let e : M.toAddSubgroup ≃+ (M.toAddSubgroup.map (realizeHLat b Xf)) :=
    AddSubgroup.equivMapOfInjective _ _ hinj
  have h1 : Module.finrank ℤ M = rk (zRealize b Xf M) := by
    change Module.finrank ℤ M = Module.finrank ℤ (zRealize b Xf M)
    exact e.toIntLinearEquiv.finrank_eq
  rw [h1]
  exact rk_zRealize_eq b Xf hXf M hM

lemma twist_int (M : Submodule (𝓞 K) V) (hM : M.FG) (m : ℕ) (hm : m ≠ 0) :
    ((Ideal.span {(m : 𝓞 K)}) • M).toAddSubgroup.relIndex M.toAddSubgroup =
      m ^ Module.finrank ℤ M := by
  have : IsAddTorsionFree V := ⟨fun n hn a c h => by
    have h' : (n : K) • a = (n : K) • c := by simpa [Nat.cast_smul_eq_nsmul] using h
    exact smul_right_injective V (Nat.cast_ne_zero.2 hn) h'⟩
  have : Module.Finite (𝓞 K) M := Module.Finite.iff_fg.mpr hM
  have : Module.Finite ℤ M := Module.Finite.trans (𝓞 K) M
  rw [Submodule.ideal_span_singleton_smul]
  set H := ((m : 𝓞 K) • M).toAddSubgroup.addSubgroupOf M.toAddSubgroup with hH
  have hcoe : ∀ x : M, ((m • x : M) : V) = (m : 𝓞 K) • (x : V) := fun x => by
    rw [Submodule.coe_smul_of_tower, ← Nat.cast_smul_eq_nsmul (𝓞 K)]
  have hmem : ∀ x : M, m • x ∈ H.toIntSubmodule := fun x => by
    show m • x ∈ H
    rw [hH, AddSubgroup.mem_addSubgroupOf, Submodule.mem_toAddSubgroup, hcoe]
    exact Submodule.smul_mem_pointwise_smul _ _ _ x.2
  let f : M →+ H.toIntSubmodule :=
    { toFun := fun x => ⟨m • x, hmem x⟩
      map_zero' := by ext; simp
      map_add' := fun x y => by ext; simp [smul_add] }
  have hf : Function.Bijective f := by
    constructor
    · intro x y hxy
      have h1 : ((m • x : M) : V) = ((m • y : M) : V) := by
        have := congrArg (fun z : H.toIntSubmodule => ((z : M) : V)) hxy
        simpa [f] using this
      rw [Submodule.coe_smul_of_tower, Submodule.coe_smul_of_tower] at h1
      exact Subtype.ext (nsmul_right_injective hm h1)
    · rintro ⟨z, hz⟩
      have hz' : (z : V) ∈ (m : 𝓞 K) • M := by
        have : z ∈ H := hz
        rwa [hH, AddSubgroup.mem_addSubgroupOf, Submodule.mem_toAddSubgroup] at this
      obtain ⟨x, hx, hxz⟩ := Submodule.mem_smul_pointwise_iff_exists _ _ _ |>.1 hz'
      refine ⟨⟨x, hx⟩, ?_⟩
      ext
      simp only [f, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
      rw [hcoe]
      exact hxz
  let e := AddEquiv.ofBijective f hf
  have key := Submodule.natAbs_det_equiv H.toIntSubmodule e
  have hlin : H.toIntSubmodule.subtype ∘ₗ AddMonoidHom.toIntLinearMap (e : M →+ H.toIntSubmodule) =
      (m : ℤ) • LinearMap.id := by
    ext x
    simp [e, f]
  rw [hlin, LinearMap.det_smul, LinearMap.det_id, mul_one] at key
  change H.index = _
  rw [Int.natAbs_pow, Int.natAbs_natCast] at key
  exact key.symm

/-- **Exact Ideal-Twist Index Formula (`twist_index`)**:
for any finitely generated `M : Submodule (𝓞 K) V` and nonzero ideal `𝔟 ≤ 𝓞 K`,
`[M : 𝔟 • M] = (Ideal.absNorm 𝔟) ^ rkK M`. -/
theorem twist_index (M : Submodule (𝓞 K) V) (hM : M.FG) (𝔟 : Ideal (𝓞 K)) (h𝔟 : 𝔟 ≠ ⊥) :
    (𝔟 • M).toAddSubgroup.relIndex M.toAddSubgroup =
      Ideal.absNorm 𝔟 ^ rkK (K := K) M := by
  set m := Ideal.absNorm 𝔟 with hmdef
  have hm : m ≠ 0 := fun h => h𝔟 (Ideal.absNorm_eq_zero_iff.1 h)
  have hmem : (m : 𝓞 K) ∈ 𝔟 := Ideal.absNorm_mem 𝔟
  obtain ⟨𝔠, h𝔠⟩ : 𝔟 ∣ Ideal.span {(m : 𝓞 K)} :=
    Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hmem)
  have hspan0 : Ideal.span {(m : 𝓞 K)} ≠ ⊥ := by
    rw [ne_eq, Ideal.span_singleton_eq_bot]
    exact_mod_cast hm
  have h𝔠0 : 𝔠 ≠ ⊥ := by
    rintro rfl
    rw [Ideal.mul_bot] at h𝔠
    exact hspan0 h𝔠
  set r := rkK (K := K) M with hr
  have hall := twist_int M hM m hm
  rw [twist_finrank_int M hM, h𝔠, mul_comm, Submodule.mul_smul,
    ← AddSubgroup.relIndex_mul_relIndex (𝔠 • 𝔟 • M).toAddSubgroup
      (𝔟 • M).toAddSubgroup M.toAddSubgroup ((Submodule.toAddSubgroup_le _ _).2 Submodule.smul_le_right)
      ((Submodule.toAddSubgroup_le _ _).2 Submodule.smul_le_right)] at hall
  have ha := twist_le 𝔟 h𝔟 M hM
  have hb := twist_le 𝔠 h𝔠0 (𝔟 • M) (Submodule.FG.smul (IsNoetherian.noetherian 𝔟) hM)
  rw [show rkK (K := K) (𝔟 • M) = r from by rw [hr]; unfold rkK; rw [twist_span_smul M 𝔟 h𝔟]] at hb
  have hm_pos : 0 < m := Nat.pos_of_ne_zero hm
  have hnorm : Ideal.absNorm 𝔠 * m = m ^ Module.finrank ℚ K := by
    rw [hmdef, ← map_mul, mul_comm, ← h𝔠]
    -- `Ideal.absNorm (Ideal.span {(m : 𝓞 K)}) = m ^ [K : ℚ]` via `twist_int` on `L = ⊤ ≤ K`?
    -- Actually `Ideal.absNorm (Ideal.span {(m : 𝓞 K)}) = Nat.card (𝓞 K ⧸ Ideal.span {(m : 𝓞 K)})`
    -- and `(Ideal.span {(m : 𝓞 K)} • (⊤ : Submodule (𝓞 K) K)).relIndex (⊤)`!
    -- Even better: `RingOfIntegers` is `ℤ`-free of rank `[K : ℚ]`: `𝓞 K ⧸ (m • ⊤) ≃ (Free.ChooseBasisIndex ℤ (𝓞 K) → ZMod m)`!
    letI : NeZero m := ⟨hm⟩
    let bO := RingOfIntegers.basis K
    let eQ : (𝓞 K ⧸ Ideal.span {(m : 𝓞 K)}) ≃ (Free.ChooseBasisIndex ℤ (𝓞 K) → ZMod m) :=
      { toFun := Quotient.lift (fun x k => (bO.repr x k : ZMod m)) (fun x y hxy => by
          funext k
          have hsub : x - y ∈ Ideal.span {(m : 𝓞 K)} :=
            Ideal.Quotient.eq.mp (Quotient.sound hxy)
          rw [Ideal.mem_span_singleton] at hsub
          obtain ⟨q, hq⟩ := hsub
          have hq' : x - y = m • q := by rw [hq, ← nsmul_eq_mul]
          have hrepr : bO.repr x k - bO.repr y k = (m : ℤ) * bO.repr q k := by
            have := congrArg (fun z => bO.repr z k) hq'
            rw [map_sub, map_nsmul] at this
            simpa [Finsupp.sub_apply, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul] using this
          rw [← sub_eq_zero, ← Int.cast_sub, ZMod.intCast_zmod_eq_zero_iff_dvd]
          exact ⟨bO.repr q k, hrepr⟩)
        invFun := fun f => Ideal.Quotient.mk _ (∑ k, ((f k).val : ℤ) • bO k)
        left_inv := fun q => by
          obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
          rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem, Ideal.mem_span_singleton]
          have hdiff : ∑ k, (((bO.repr x k : ZMod m).val : ℤ) - bO.repr x k) • bO k =
              (∑ k, ((bO.repr x k : ZMod m).val : ℤ) • bO k) - x := by
            conv_rhs => rhs; rw [← bO.sum_repr x]
            rw [← Finset.sum_sub_distrib]
            refine Finset.sum_congr rfl fun k _ => by rw [sub_smul]
          have hdvd : ∀ k, (m : ℤ) ∣ (((bO.repr x k : ZMod m).val : ℤ) - bO.repr x k) := by
            intro k
            rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
            simp
          choose c hc using hdvd
          refine ⟨∑ k, c k • bO k, ?_⟩
          erw [Quotient.lift_mk]
          have hsum : (m : 𝓞 K) * ∑ k, c k • bO k =
              ∑ k, (((bO.repr x k : ZMod m).val : ℤ) - bO.repr x k) • bO k := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun k _ => ?_
            have hterm : (m : 𝓞 K) * (c k • bO k) = ((m : ℤ) * c k) • bO k := by
              rw [zsmul_eq_mul, zsmul_eq_mul, ← mul_assoc]
              congr 1
              norm_cast
            rw [hterm, ← hc k]
          rw [← hdiff, hsum, hdiff]
        right_inv := fun f => by
          funext k
          change Quotient.lift (fun x k => (bO.repr x k : ZMod m)) _
            (Ideal.Quotient.mk (Ideal.span {(m : 𝓞 K)}) (∑ x, ((f x).val : ℤ) • bO x)) k = f k
          erw [Quotient.lift_mk]
          rw [map_sum]
          simp only [Finsupp.coe_finsetSum, Finset.sum_apply, map_zsmul, bO.repr_self,
            Finsupp.smul_single, smul_eq_mul, mul_one, Finsupp.single_apply, Finset.sum_ite_eq',
            Finset.mem_univ, ↓reduceIte, Int.cast_natCast, ZMod.natCast_zmod_val] }
    have hcard : Ideal.absNorm (Ideal.span {(m : 𝓞 K)}) = m ^ Module.finrank ℚ K := by
      rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_congr eQ,
        Nat.card_pi, Finset.prod_const, Finset.card_univ]
      simp only [Nat.card_eq_fintype_card, ZMod.card,
        ← Module.finrank_eq_card_basis bO, NumberField.RingOfIntegers.rank]
    exact hcard
  have hB : 0 < Ideal.absNorm 𝔠 ^ r :=
    pow_pos (Nat.pos_of_ne_zero (fun h => h𝔠0 (Ideal.absNorm_eq_zero_iff.1 h))) _
  have htot : Ideal.absNorm 𝔠 ^ r * m ^ r = m ^ (Module.finrank ℚ K * r) := by
    rw [← mul_pow, hnorm, ← pow_mul]
  by_contra hne
  have hlt := lt_of_le_of_ne ha hne
  have h1 : (𝔠 • 𝔟 • M).toAddSubgroup.relIndex (𝔟 • M).toAddSubgroup *
      (𝔟 • M).toAddSubgroup.relIndex M.toAddSubgroup < Ideal.absNorm 𝔠 ^ r * m ^ r :=
    lt_of_le_of_lt (Nat.mul_le_mul_right _ hb) (Nat.mul_lt_mul_of_pos_left hlt hB)
  rw [hall, htot] at h1
  exact lt_irrefl _ h1

end IdealTwistIndex

end LatticeProps

end LatticeStructure

/-! ## Section 3: Normalized Arakelov Slopes (`muDef`, `muMaxDef`, `muMinDef`), Variational Forms & Bost -/

section NormalizedSlopes

variable {K : Type*} [Field K] [NumberField K]

/-- Normalized logarithmic discriminant `log |discr K| / [K : ℚ]`. -/
def logDiscDivDeg (K : Type*) [Field K] [NumberField K] : ℝ :=
  Real.log |(NumberField.discr K : ℝ)| / (Module.finrank ℚ K : ℝ)

/-- Discriminant shift constant `c₂(K) = log 2 - log |discr K| / [K : ℚ]`. -/
def discShift (K : Type*) [Field K] [NumberField K] : ℝ :=
  Real.log 2 - logDiscDivDeg K

section Invariants

variable {V ι : Type*} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι]

/-- `ℤ`-lattice Arakelov degree of `zRealize b X L`. -/
def degHLat (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (L : Submodule (𝓞 K) V) : ℝ :=
  degAr (zRealize b X L)

/-- `ℤ`-lattice slope `degHLat b X L / rk (zRealize b X L)`. -/
def slopeHLat (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (L : Submodule (𝓞 K) V) : ℝ :=
  ArakelovCovolume.slope (zRealize b X L)

/-- Set of `slopeHLat` values of nonzero `𝓞 K`-submodules `N ≤ L`. -/
def slopesO (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (L : Submodule (𝓞 K) V) : Set ℝ :=
  { t | ∃ N : Submodule (𝓞 K) V, N ≤ L ∧ N ≠ ⊥ ∧ slopeHLat b X N = t }

/-- Set of quotient slopes of proper saturated `𝓞 K`-submodules `N ≤ L`. -/
def quotSlopesO (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (L : Submodule (𝓞 K) V) : Set ℝ :=
  { t | ∃ N : Submodule (𝓞 K) V, N ≤ L ∧
    IsSaturated (zRealize b X L) (zRealize b X N) ∧ N ≠ L ∧
    ArakelovCovolume.slope (quotLat (zRealize b X L) (zRealize b X N)) = t }

/-- Maximal `𝓞 K`-submodule slope `muMaxO`. -/
def muMaxO (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (L : Submodule (𝓞 K) V) : ℝ :=
  sSup (slopesO b X L)

/-- Minimal `𝓞 K`-quotient slope `muMinO`. -/
def muMinO (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (L : Submodule (𝓞 K) V) : ℝ :=
  sInf (quotSlopesO b X L)

/-- **Normalized Arakelov slope `muDef`** matching `StatementPl.lean` & `DataArith.lean`:
`muDef b X L = 2 * slopeHLat b X L - log 2 + log |discr K| / [K : ℚ]`. -/
def muDef (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (L : Submodule (𝓞 K) V) : ℝ :=
  2 * slopeHLat b X L - Real.log 2 + logDiscDivDeg K

/-- **Normalized maximal Arakelov slope `muMaxDef`**. -/
def muMaxDef (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (L : Submodule (𝓞 K) V) : ℝ :=
  2 * muMaxO b X L - Real.log 2 + logDiscDivDeg K

/-- **Normalized minimal Arakelov slope `muMinDef`**. -/
def muMinDef (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (L : Submodule (𝓞 K) V) : ℝ :=
  2 * muMinO b X L - Real.log 2 + logDiscDivDeg K

/-- Normalized log-covolume `lcv b X L = (2 / [K : ℚ]) * log (covol (zRealize b X L))`. -/
def lcvDef (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (L : Submodule (𝓞 K) V) : ℝ :=
  (2 / (Module.finrank ℚ K : ℝ)) * Real.log (covol (zRealize b X L))

lemma slopesO_subset_slopes (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (L : Submodule (𝓞 K) V) :
    slopesO b X L ⊆ RHDirect.ArakelovCovolume.slopes (zRealize b X L) := by
  rintro t ⟨N, hNL, hN0, rfl⟩
  refine ⟨zRealize b X N, zRealize_mono b X hNL, ?_, rfl⟩
  intro hbot
  apply hN0
  rw [eq_bot_iff]
  intro x hxN
  have hx0 : realizeHLat b X x = 0 := by
    have hmem : realizeHLat b X x ∈ zRealize b X N := ⟨x, hxN, rfl⟩
    rwa [hbot, Submodule.mem_bot] at hmem
  exact realizeHLat_injective b X hX (hx0.trans (map_zero (realizeHLat b X)).symm)

lemma quotSlopesO_subset_quotSlopes (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (L : Submodule (𝓞 K) V) :
    quotSlopesO b X L ⊆ RHDirect.Stage4ArakelovBost.quotSlopes (zRealize b X L) := by
  rintro t ⟨N, hNL, hsat, hNneL, rfl⟩
  refine ⟨zRealize b X N, hsat, ?_, rfl⟩
  intro heq
  apply hNneL
  apply le_antisymm hNL
  intro x hxL
  have hmem : realizeHLat b X x ∈ zRealize b X N := heq ▸ ⟨x, hxL, rfl⟩
  rcases hmem with ⟨y, hyN, hyx⟩
  rwa [← realizeHLat_injective b X hX hyx]

lemma slopesO_bddAbove (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (L : Submodule (𝓞 K) V) (hL : L.FG) :
    BddAbove (slopesO b X L) := by
  have : DiscreteTopology (zRealize b X L) := discreteTopology_zRealize_of_fg b X hX L hL
  exact (RHDirect.ArakelovCovolume.slopes_bddAbove (zRealize b X L)).mono
    (slopesO_subset_slopes b X hX L)

lemma quotSlopesO_bddBelow (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (L : Submodule (𝓞 K) V) (hL : L.FG) :
    BddBelow (quotSlopesO b X L) := by
  have : DiscreteTopology (zRealize b X L) := discreteTopology_zRealize_of_fg b X hX L hL
  refine ⟨RHDirect.Stage4ArakelovBost.muMin (zRealize b X L), ?_⟩
  rintro _ ⟨N, hNL, hsat, hNneL, rfl⟩
  have hZ_ne : zRealize b X N ≠ zRealize b X L := by
    intro heq
    apply hNneL
    apply le_antisymm hNL
    intro x hxL
    have hmem : realizeHLat b X x ∈ zRealize b X N := heq ▸ ⟨x, hxL, rfl⟩
    rcases hmem with ⟨y, hyN, hyx⟩
    rwa [← realizeHLat_injective b X hX hyx]
  exact RHDirect.Stage4ArakelovBost.muMin_le_slope_quotLat hsat hZ_ne

lemma slopesO_nonempty (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (L : Submodule (𝓞 K) V) (hL0 : L ≠ ⊥) :
    (slopesO b X L).Nonempty :=
  ⟨slopeHLat b X L, L, le_rfl, hL0, rfl⟩

lemma quotSlopesO_nonempty (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (L : Submodule (𝓞 K) V) (hL0 : L ≠ ⊥) :
    (quotSlopesO b X L).Nonempty := by
  refine ⟨ArakelovCovolume.slope (quotLat (zRealize b X L) (zRealize b X ⊥)), ⊥, bot_le, ?_, hL0.symm, rfl⟩
  rw [zRealize_bot]
  exact RHDirect.Stage4ArakelovBost.isSaturated_bot (zRealize b X L)

/-- Comparison with `ℤ`-lattice maximal slope: `muMaxO ≤ ArakelovCovolume.muMax (zRealize L)`. -/
theorem muMaxO_le_zMuMax (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (L : Submodule (𝓞 K) V) (hL : L.FG) (hL0 : L ≠ ⊥) :
    muMaxO b X L ≤ RHDirect.ArakelovCovolume.muMax (zRealize b X L) := by
  have : DiscreteTopology (zRealize b X L) := discreteTopology_zRealize_of_fg b X hX L hL
  exact csSup_le_csSup (RHDirect.ArakelovCovolume.slopes_bddAbove (zRealize b X L))
    (slopesO_nonempty b X L hL0) (slopesO_subset_slopes b X hX L)

/-- Comparison with `ℤ`-lattice minimal slope: `Stage4ArakelovBost.muMin (zRealize L) ≤ muMinO`. -/
theorem zMuMin_le_muMinO (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (L : Submodule (𝓞 K) V) (hL : L.FG) (hL0 : L ≠ ⊥) :
    RHDirect.Stage4ArakelovBost.muMin (zRealize b X L) ≤ muMinO b X L := by
  have : DiscreteTopology (zRealize b X L) := discreteTopology_zRealize_of_fg b X hX L hL
  refine le_csInf (quotSlopesO_nonempty b X L hL0) ?_
  rintro _ ⟨N, hNL, hsat, hNneL, rfl⟩
  have hZ_ne : zRealize b X N ≠ zRealize b X L := by
    intro heq
    apply hNneL
    apply le_antisymm hNL
    intro x hxL
    have hmem : realizeHLat b X x ∈ zRealize b X N := heq ▸ ⟨x, hxL, rfl⟩
    rcases hmem with ⟨y, hyN, hyx⟩
    rwa [← realizeHLat_injective b X hX hyx]
  exact RHDirect.Stage4ArakelovBost.muMin_le_slope_quotLat hsat hZ_ne

/-- Normalized comparison with `Stage12SchurWeylLattices` `ℤ`-lattice maximal slope:
`muMaxDef ≤ 2 * ArakelovCovolume.muMax (zRealize) - log 2 + logDiscDivDeg K`. -/
theorem muMaxDef_le_zMuMax (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (L : Submodule (𝓞 K) V) (hL : L.FG) (hL0 : L ≠ ⊥) :
    muMaxDef b X L ≤ 2 * RHDirect.ArakelovCovolume.muMax (zRealize b X L) - Real.log 2 +
      logDiscDivDeg K := by
  unfold muMaxDef
  linarith [muMaxO_le_zMuMax b X hX L hL hL0]

/-- Normalized comparison with `Stage4ArakelovBost` `ℤ`-lattice minimal slope. -/
theorem zMuMin_le_muMinDef (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (L : Submodule (𝓞 K) V) (hL : L.FG) (hL0 : L ≠ ⊥) :
    2 * RHDirect.Stage4ArakelovBost.muMin (zRealize b X L) - Real.log 2 + logDiscDivDeg K ≤
      muMinDef b X L := by
  unfold muMinDef
  linarith [zMuMin_le_muMinO b X hX L hL hL0]

lemma zRealize_ne_bot (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) {L : Submodule (𝓞 K) V} (hL0 : L ≠ ⊥) :
    zRealize b X L ≠ ⊥ := by
  intro hbot
  apply hL0
  rw [eq_bot_iff]
  intro x hx
  have hmem : realizeHLat b X x ∈ zRealize b X L := ⟨x, hx, rfl⟩
  rw [hbot, Submodule.mem_bot] at hmem
  exact realizeHLat_injective b X hX (hmem.trans (map_zero (realizeHLat b X)).symm)

/-- Variational characterization of `muMaxO`:
`muMaxO b X L ≤ θ ↔ ∀ N ≤ L, degHLat b X N ≤ θ * rk (zRealize b X N)`. -/
theorem muMaxO_char (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (L : Submodule (𝓞 K) V) (hL : L.FG) (hL0 : L ≠ ⊥) (θ : ℝ) :
    muMaxO b X L ≤ θ ↔ ∀ N : Submodule (𝓞 K) V, N ≤ L →
      degHLat b X N ≤ θ * (rk (zRealize b X N) : ℝ) := by
  have : DiscreteTopology (zRealize b X L) := discreteTopology_zRealize_of_fg b X hX L hL
  constructor
  · intro hle N hNL
    by_cases hN0 : N = ⊥
    · subst hN0
      unfold degHLat
      rw [zRealize_bot, degAr_bot]
      have hrk0 : rk (⊥ : Submodule ℤ (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2))) = 0 := by
        simp [rk]
      rw [hrk0]
      simp
    · have hN_ne : zRealize b X N ≠ ⊥ := zRealize_ne_bot b X hX hN0
      have : DiscreteTopology (zRealize b X N) := discreteTopology_of_le (zRealize_mono b X hNL)
      have hrk_pos : (0 : ℝ) < rk (zRealize b X N) :=
        Nat.cast_pos.mpr (rk_pos_of_ne_bot (zRealize b X N) hN_ne)
      have hsl : slopeHLat b X N ≤ muMaxO b X L :=
        le_csSup (slopesO_bddAbove b X hX L hL) ⟨N, hNL, hN0, rfl⟩
      have hdiv : degHLat b X N / (rk (zRealize b X N) : ℝ) ≤ θ := hsl.trans hle
      exact (div_le_iff₀ hrk_pos).mp hdiv
  · intro hforall
    refine csSup_le (slopesO_nonempty b X L hL0) ?_
    rintro _ ⟨N, hNL, hN0, rfl⟩
    have : DiscreteTopology (zRealize b X N) := discreteTopology_of_le (zRealize_mono b X hNL)
    have hN_ne : zRealize b X N ≠ ⊥ := zRealize_ne_bot b X hX hN0
    have hrk_pos : (0 : ℝ) < rk (zRealize b X N) :=
      Nat.cast_pos.mpr (rk_pos_of_ne_bot (zRealize b X N) hN_ne)
    exact (div_le_iff₀ hrk_pos).mpr (hforall N hNL)

/-- Variational characterization of `muMinO`:
`θ ≤ muMinO b X L ↔ ∀ N ≤ L, θ * (rk (zRealize L) - rk (zRealize N)) ≤ degHLat L - degHLat N`. -/
theorem muMinO_char (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (L : Submodule (𝓞 K) V) (hL : L.FG) (hL0 : L ≠ ⊥) (θ : ℝ) :
    θ ≤ muMinO b X L ↔ ∀ N : Submodule (𝓞 K) V, N ≤ L →
      θ * ((rk (zRealize b X L) : ℝ) - (rk (zRealize b X N) : ℝ)) ≤
        degHLat b X L - degHLat b X N := by
  have : DiscreteTopology (zRealize b X L) := discreteTopology_zRealize_of_fg b X hX L hL
  constructor
  · intro hle N hNL
    let N' := satO (K := K) L N
    have hN'L : N' ≤ L := satO_le L N
    have hsat : IsSaturated (zRealize b X L) (zRealize b X N') := by
      rw [← saturation_zRealize_eq b X hX hNL]
      exact RHDirect.Stage4ArakelovBost.isSaturated_saturation (zRealize_mono b X hNL)
    have hrk_eq : rk (zRealize b X N') = rk (zRealize b X N) := by
      have : (zRealize b X N') = saturation (zRealize b X L) (zRealize b X N) :=
        (saturation_zRealize_eq b X hX hNL).symm
      rw [this]
      exact RHDirect.Stage4ArakelovBost.rk_saturation (zRealize_mono b X hNL)
    have hdeg_le : degHLat b X N ≤ degHLat b X N' := by
      have h1 := RHDirect.Stage4ArakelovBost.covol_saturation_le (zRealize_mono b X hNL)
      rw [saturation_zRealize_eq b X hX hNL] at h1
      exact h1.2
    by_cases hN'eqL : N' = L
    · have hrkL : rk (zRealize b X L) = rk (zRealize b X N) := by
        rw [← hN'eqL, hrk_eq]
      have hdegL : degHLat b X N ≤ degHLat b X L := hN'eqL ▸ hdeg_le
      rw [hrkL, sub_self, mul_zero]
      linarith
    · have hZ_ne : zRealize b X N' ≠ zRealize b X L := by
        intro heq
        apply hN'eqL
        apply le_antisymm hN'L
        intro x hxL
        have hmem : realizeHLat b X x ∈ zRealize b X N' := heq ▸ ⟨x, hxL, rfl⟩
        rcases hmem with ⟨y, hyN', hyx⟩
        rwa [← realizeHLat_injective b X hX hyx]
      have hq_ne : quotLat (zRealize b X L) (zRealize b X N') ≠ ⊥ :=
        RHDirect.Stage4ArakelovBost.quotLat_ne_bot_of_lt hsat hZ_ne
      have : DiscreteTopology (quotLat (zRealize b X L) (zRealize b X N')) :=
        discreteTopology_quotLat hsat
      have hq_rk_pos : (0 : ℝ) < rk (quotLat (zRealize b X L) (zRealize b X N')) :=
        Nat.cast_pos.mpr (rk_pos_of_ne_bot _ hq_ne)
      have hq_slope : θ ≤ ArakelovCovolume.slope (quotLat (zRealize b X L) (zRealize b X N')) :=
        hle.trans (csInf_le (quotSlopesO_bddBelow b X hX L hL) ⟨N', hN'L, hsat, hN'eqL, rfl⟩)
      have hq_deg : θ * (rk (quotLat (zRealize b X L) (zRealize b X N')) : ℝ) ≤
          degAr (quotLat (zRealize b X L) (zRealize b X N')) :=
        (le_div_iff₀ hq_rk_pos).mp hq_slope
      have hrk_add := rk_add_quotLat hsat
      have hdeg_add := degAr_eq_add_quotLat hsat
      have hrk_sub : (rk (quotLat (zRealize b X L) (zRealize b X N')) : ℝ) =
          (rk (zRealize b X L) : ℝ) - (rk (zRealize b X N) : ℝ) := by
        rw [← hrk_eq]
        have : rk (quotLat (zRealize b X L) (zRealize b X N')) + rk (zRealize b X N') =
            rk (zRealize b X L) := by omega
        exact eq_sub_of_add_eq (by exact_mod_cast this)
      rw [hrk_sub] at hq_deg
      change degAr (zRealize b X L) = degAr (zRealize b X N') +
        degAr (quotLat (zRealize b X L) (zRealize b X N')) at hdeg_add
      unfold degHLat at hdeg_le ⊢
      linarith
  · intro hforall
    refine le_csInf (quotSlopesO_nonempty b X L hL0) ?_
    rintro _ ⟨N, hNL, hsat, hNneL, rfl⟩
    have hZ_ne : zRealize b X N ≠ zRealize b X L := by
      intro heq
      apply hNneL
      apply le_antisymm hNL
      intro x hxL
      have hmem : realizeHLat b X x ∈ zRealize b X N := heq ▸ ⟨x, hxL, rfl⟩
      rcases hmem with ⟨y, hyN, hyx⟩
      rwa [← realizeHLat_injective b X hX hyx]
    have : DiscreteTopology (quotLat (zRealize b X L) (zRealize b X N)) :=
      discreteTopology_quotLat hsat
    have hq_ne : quotLat (zRealize b X L) (zRealize b X N) ≠ ⊥ :=
      RHDirect.Stage4ArakelovBost.quotLat_ne_bot_of_lt hsat hZ_ne
    have hq_rk_pos : (0 : ℝ) < rk (quotLat (zRealize b X L) (zRealize b X N)) :=
      Nat.cast_pos.mpr (rk_pos_of_ne_bot _ hq_ne)
    have hrk_add := rk_add_quotLat hsat
    have hdeg_add := degAr_eq_add_quotLat hsat
    have hrk_sub : (rk (quotLat (zRealize b X L) (zRealize b X N)) : ℝ) =
        (rk (zRealize b X L) : ℝ) - (rk (zRealize b X N) : ℝ) := by
      have : rk (quotLat (zRealize b X L) (zRealize b X N)) + rk (zRealize b X N) =
          rk (zRealize b X L) := by omega
      exact eq_sub_of_add_eq (by exact_mod_cast this)
    have hdeg_sub : degAr (quotLat (zRealize b X L) (zRealize b X N)) =
        degHLat b X L - degHLat b X N := by
      unfold degHLat; linarith
    refine (le_div_iff₀ hq_rk_pos).mpr ?_
    rw [hrk_sub, hdeg_sub]
    exact hforall N hNL

theorem muMinO_le_slope_le_muMaxO (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (L : Submodule (𝓞 K) V) (hL : L.FG) (hL0 : L ≠ ⊥) :
    muMinO b X L ≤ slopeHLat b X L ∧ slopeHLat b X L ≤ muMaxO b X L := by
  have : DiscreteTopology (zRealize b X L) := discreteTopology_zRealize_of_fg b X hX L hL
  have h1 : muMinO b X L ≤ slopeHLat b X L := by
    have hbot : (⊥ : Submodule (𝓞 K) V) ≤ L := bot_le
    have hsat : IsSaturated (zRealize b X L) (zRealize b X (⊥ : Submodule (𝓞 K) V)) := by
      rw [zRealize_bot]
      exact RHDirect.Stage4ArakelovBost.isSaturated_bot (zRealize b X L)
    have hle := csInf_le (quotSlopesO_bddBelow b X hX L hL)
      ⟨⊥, hbot, hsat, hL0.symm, rfl⟩
    have hq_eq : quotLat (zRealize b X L) (zRealize b X (⊥ : Submodule (𝓞 K) V)) = zRealize b X L := by
      rw [zRealize_bot]
      exact RHDirect.Stage4ArakelovBost.quotLat_bot (zRealize b X L)
    rw [hq_eq] at hle
    exact hle
  have h2 : slopeHLat b X L ≤ muMaxO b X L :=
    le_csSup (slopesO_bddAbove b X hX L hL) ⟨L, le_rfl, hL0, rfl⟩
  exact ⟨h1, h2⟩

theorem muMinDef_le_muDef_le_muMaxDef (b : Module.Basis ι K V)
    (X : InfinitePlace K → Matrix ι ι ℂ) (hX : ∀ v, IsUnit (X v).det)
    (L : Submodule (𝓞 K) V) (hL : L.FG) (hL0 : L ≠ ⊥) :
    muMinDef b X L ≤ muDef b X L ∧ muDef b X L ≤ muMaxDef b X L := by
  obtain ⟨h1, h2⟩ := muMinO_le_slope_le_muMaxO b X hX L hL hL0
  unfold muMinDef muDef muMaxDef
  constructor <;> linarith

/-- Submodule monotonicity of `muMaxDef` (`N ≤ L → muMaxDef N ≤ muMaxDef L`). -/
theorem muMaxDef_mono (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) {N L : Submodule (𝓞 K) V} (hL : L.FG) (hN0 : N ≠ ⊥)
    (hNL : N ≤ L) :
    muMaxDef b X N ≤ muMaxDef b X L := by
  unfold muMaxDef
  have hsub : muMaxO b X N ≤ muMaxO b X L := by
    refine csSup_le (slopesO_nonempty b X N hN0) ?_
    rintro t ⟨M, hMN, hM0, rfl⟩
    exact le_csSup (slopesO_bddAbove b X hX L hL) ⟨M, hMN.trans hNL, hM0, rfl⟩
  linarith

/-- Full-rank sublattice index formula for `muDef`:
`muDef b X L' = muDef b X L - 2 * log [L : L'] / ([K : ℚ] * rkK L)`. -/
theorem muDef_sublattice_index (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) {L' L : Submodule (𝓞 K) V} (hL : L.FG) (hL0 : L ≠ ⊥)
    (hL'L : L' ≤ L) (hrk : rkK (K := K) L' = rkK (K := K) L) :
    muDef b X L' = muDef b X L -
      2 * Real.log (L'.toAddSubgroup.relIndex L.toAddSubgroup : ℝ) /
        ((Module.finrank ℚ K : ℝ) * (rkK (K := K) L : ℝ)) := by
  have : DiscreteTopology (zRealize b X L) := discreteTopology_zRealize_of_fg b X hX L hL
  have hL'fg : L'.FG := Submodule.FG.of_le hL hL'L
  have : DiscreteTopology (zRealize b X L') := discreteTopology_zRealize_of_fg b X hX L' hL'fg
  have hrkZ : rk (zRealize b X L') = rk (zRealize b X L) := by
    rw [rk_zRealize_eq b X hX L' hL'fg, rk_zRealize_eq b X hX L hL, hrk]
  have hcov := covol_eq_index_mul_covol (zRealize_mono b X hL'L) hrkZ
  have hidx : latIndex (zRealize b X L) (zRealize b X L') =
      L'.toAddSubgroup.relIndex L.toAddSubgroup := by
    change ((zRealize b X L').toAddSubgroup.relIndex (zRealize b X L).toAddSubgroup) = _
    exact AddSubgroup.relIndex_map_map_of_injective L'.toAddSubgroup L.toAddSubgroup
      (realizeHLat_injective b X hX)
  have hdeg := degAr_eq_degAr_sub_log_index (zRealize_mono b X hL'L) hrkZ
  rw [hidx] at hdeg
  have hrk_pos : 0 < rk (zRealize b X L) :=
    rk_pos_of_ne_bot _ (zRealize_ne_bot b X hX hL0)
  have hrk_eq : (rk (zRealize b X L) : ℝ) = (Module.finrank ℚ K : ℝ) * (rkK (K := K) L : ℝ) := by
    rw [rk_zRealize_eq b X hX L hL]; push_cast; rfl
  unfold muDef slopeHLat ArakelovCovolume.slope
  rw [hrkZ, hdeg, hrk_eq]
  have hne : (Module.finrank ℚ K : ℝ) * (rkK (K := K) L : ℝ) ≠ 0 := by
    rw [← hrk_eq]; exact (Nat.cast_pos.mpr hrk_pos).ne'
  field_simp [hne]
  ring

end Invariants

end NormalizedSlopes

namespace HLat

variable {K : Type} [Field K] [NumberField K] [StarRing K]

/-- Normalized slope `mu` of `A : HLat K`. -/
def mu (A : HLat K) : ℝ := muDef A.b A.X A.L

/-- Normalized maximal slope `muMax` of `A : HLat K`. -/
def muMax (A : HLat K) : ℝ := muMaxDef A.b A.X A.L

/-- Normalized minimal slope `muMin` of `A : HLat K`. -/
def muMin (A : HLat K) : ℝ := muMinDef A.b A.X A.L

/-- Normalized log-covolume `lcv` of `A : HLat K`. -/
def lcv (A : HLat K) : ℝ := lcvDef A.b A.X A.L

end HLat

/-! ## Section 4: `dualHLat`, Different-Ideal Index, `hlat_duality_slope_neg`, and `bridge_ccb_dual` -/

section Duality

section DualDefs

variable {K V ι : Type*} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι]

/-- `𝓞 K`-dual lattice `dualLatO A = { f : Module.Dual K V | ∀ x ∈ A, f x ∈ 𝓞 K }`. -/
def dualLatO (A : Submodule (𝓞 K) V) : Submodule (𝓞 K) (Module.Dual K V) where
  carrier := {f | ∀ x ∈ A, f x ∈ Set.range (algebraMap (𝓞 K) K)}
  zero_mem' := fun _ _ => ⟨0, by simp⟩
  add_mem' := by
    rintro f g hf hg x hx
    obtain ⟨a, ha⟩ := hf x hx
    obtain ⟨c, hc⟩ := hg x hx
    exact ⟨a + c, by simp [ha, hc]⟩
  smul_mem' := by
    rintro r f hf x hx
    obtain ⟨a, ha⟩ := hf x hx
    exact ⟨r * a, by simp [ha, Algebra.smul_def]⟩

/-- Trace-dual lattice `tdualLatO A = { f : Module.Dual K V | ∀ x ∈ A, Tr_{K/ℚ}(f x) ∈ ℤ }`. -/
def tdualLatO (A : Submodule (𝓞 K) V) : Submodule (𝓞 K) (Module.Dual K V) where
  carrier := {f | ∀ x ∈ A, ∃ z : ℤ, Algebra.trace ℚ K (f x) = z}
  zero_mem' := fun _ _ => ⟨0, by simp⟩
  add_mem' := by
    rintro f g hf hg x hx
    obtain ⟨a, ha⟩ := hf x hx
    obtain ⟨c, hc⟩ := hg x hx
    exact ⟨a + c, by simp [ha, hc]⟩
  smul_mem' := by
    rintro r f hf x hx
    obtain ⟨a, ha⟩ := hf (r • x) (A.smul_mem r hx)
    have e : (r • f) x = f (r • x) := by
      rw [LinearMap.smul_apply, ← algebraMap_smul K r x, map_smul, algebraMap_smul]
    exact ⟨a, e ▸ ha⟩

/-- `𝓞 K`-annihilator submodule `annO N = { f : Module.Dual K V | ∀ x ∈ N, f x = 0 }`. -/
def annO (N : Submodule (𝓞 K) V) : Submodule (𝓞 K) (Module.Dual K V) where
  carrier := {f | ∀ x ∈ N, f x = 0}
  zero_mem' := fun _ _ => by simp
  add_mem' := by rintro f g hf hg x hx; simp [hf x hx, hg x hx]
  smul_mem' := by rintro r f hf x hx; simp [hf x hx]

/-- Dual archimedean frame `(dualFrame X) v = ((X v)ᵀ)⁻¹`. -/
def dualFrame (X : InfinitePlace K → Matrix ι ι ℂ) : InfinitePlace K → Matrix ι ι ℂ :=
  fun v => ((X v).transpose)⁻¹

lemma dualFrame_frameOK (X : InfinitePlace K → Matrix ι ι ℂ) (hX : ∀ v, IsUnit (X v).det) :
    ∀ v, IsUnit (dualFrame X v).det := by
  intro v
  exact Matrix.isUnit_nonsing_inv_det _ (by rw [Matrix.det_transpose]; exact hX v)

lemma dualFrame_dualFrame (X : InfinitePlace K → Matrix ι ι ℂ) (hX : ∀ v, IsUnit (X v).det) :
    dualFrame (dualFrame X) = X := by
  funext v
  unfold dualFrame
  rw [Matrix.transpose_nonsing_inv, Matrix.transpose_transpose,
    Matrix.nonsing_inv_nonsing_inv _ (hX v)]

end DualDefs

/-- **Dual Hermitian Lattice `dualHLat A`**:
underlying `K`-space `Module.Dual K A.V`, dual basis `A.b.dualBasis`, dual frame
`dualFrame A.X`, and `𝓞 K`-dual lattice `dualLatO A.L`. -/
def dualHLat {K : Type} [Field K] [NumberField K] [StarRing K] (A : HLat K) : HLat K where
  V := Module.Dual K A.V
  ι := A.ι
  b := A.b.dualBasis
  X := dualFrame A.X
  L := dualLatO (K := K) A.L

/-- **`bridge_ccb_dual` (ready for `BesselIntegrality`)**:
a `K`-linear map `B : W →ₗ[K] Module.Dual K V` maps `N` into `dualLatO A` iff it restricts
to an `𝓞 K`-bilinear pairing `N →ₗ[𝓞 K] Module.Dual (𝓞 K) A`. -/
theorem bridge_ccb_dual {K V W : Type*} [Field K] [NumberField K]
    [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
    (A : Submodule (𝓞 K) V) (N : Submodule (𝓞 K) W) (B : W →ₗ[K] Module.Dual K V) :
    (∃ β : N →ₗ[𝓞 K] Module.Dual (𝓞 K) A,
      ∀ (φ : N) (F : A), algebraMap (𝓞 K) K (β φ F) = B (φ : W) (F : V)) ↔
      N.map (B.restrictScalars (𝓞 K)) ≤ dualLatO (K := K) A := by
  constructor
  · rintro ⟨β, hβ⟩ _ ⟨φ, hφ, rfl⟩ x hx
    change (B φ) x ∈ Set.range (algebraMap (𝓞 K) K)
    exact ⟨β ⟨φ, hφ⟩ ⟨x, hx⟩, hβ ⟨φ, hφ⟩ ⟨x, hx⟩⟩
  · intro hle
    have hmem : ∀ (φ : N) (F : A), B (φ : W) (F : V) ∈ Set.range (algebraMap (𝓞 K) K) :=
      fun φ F => hle ⟨φ.1, φ.2, rfl⟩ F.1 F.2
    choose val hval using fun (φ : N) (F : A) => hmem φ F
    have hinj := FaithfulSMul.algebraMap_injective (𝓞 K) K
    refine ⟨{
      toFun := fun φ => {
        toFun := fun F => val φ F
        map_add' := fun F₁ F₂ => hinj (by
          rw [map_add, hval φ F₁, hval φ F₂, hval φ (F₁ + F₂)]
          exact map_add (B (φ : W)) (F₁ : V) (F₂ : V))
        map_smul' := fun r F => hinj (by
          rw [RingHom.id_apply, smul_eq_mul, map_mul, hval φ (r • F), hval φ F]
          change B (φ : W) (r • (F : V)) = algebraMap (𝓞 K) K r * B (φ : W) (F : V)
          rw [← algebraMap_smul K r (F : V), map_smul, smul_eq_mul])
      }
      map_add' := fun φ₁ φ₂ => by
        ext F
        change (algebraMap (𝓞 K) K) (val (φ₁ + φ₂) F) =
          (algebraMap (𝓞 K) K) (val φ₁ F + val φ₂ F)
        rw [map_add, hval (φ₁ + φ₂) F, hval φ₁ F, hval φ₂ F]
        change B ((φ₁ : W) + (φ₂ : W)) (F : V) = B (φ₁ : W) (F : V) + B (φ₂ : W) (F : V)
        rw [map_add, LinearMap.add_apply]
      map_smul' := fun r φ => by
        ext F
        change (algebraMap (𝓞 K) K) (val (r • φ) F) =
          (algebraMap (𝓞 K) K) (r * val φ F)
        rw [map_mul, hval (r • φ) F, hval φ F]
        change B (r • (φ : W)) (F : V) = algebraMap (𝓞 K) K r * B (φ : W) (F : V)
        rw [← algebraMap_smul K r (φ : W), map_smul, LinearMap.smul_apply, smul_eq_mul]
    }, fun φ F => hval φ F⟩

section DualProofs

variable {K V ι : Type*} [Field K] [NumberField K] [IsTotallyComplex K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  [Fintype ι] [DecidableEq ι]

/-- Coordinate conjugation linear isometry on `EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2)`. -/
def cE (K ι : Type*) [Field K] [NumberField K] [Fintype ι] :
    EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2) →ₗ[ℝ]
      EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2) where
  toFun w := WithLp.toLp 2 fun p => (if p.2.2 = 0 then (1 : ℝ) else -1) * w p
  map_add' u v := by ext p; simp [mul_add]
  map_smul' c u := by ext p; simp [smul_eq_mul, mul_left_comm]

lemma cE_apply (w : EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2))
    (p : InfinitePlace K × ι × Fin 2) :
    cE K ι w p = (if p.2.2 = 0 then (1 : ℝ) else -1) * w p := rfl

lemma cE_cE (w : EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2)) :
    cE K ι (cE K ι w) = w := by
  ext p
  rw [cE_apply, cE_apply]
  split_ifs <;> ring

lemma inner_cE (u v : EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2)) :
    inner ℝ (cE K ι u) (cE K ι v) = inner ℝ u v := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct,
    dotProduct, dotProduct]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [star_trivial, star_trivial, cE_apply, cE_apply]
  split_ifs <;> ring

lemma ident_trace_eq (a : K) :
    ((Algebra.trace ℚ K a : ℚ) : ℝ) = ∑ v : InfinitePlace K, 2 * (v.embedding a).re := by
  classical
  have h := trace_eq_sum_embeddings (K := ℚ) (L := K) ℂ (x := a)
  rw [← Fintype.sum_equiv (RingHom.equivRatAlgHom K ℂ) (fun φ => φ a)
      (fun σ => σ a) (fun _ => by simp [RingHom.equivRatAlgHom_apply])] at h
  rw [← Finset.sum_fiberwise Finset.univ InfinitePlace.mk (fun φ => φ a)] at h
  have h2 := congrArg Complex.re h
  rw [Complex.re_sum] at h2
  have hq : (algebraMap ℚ ℂ (Algebra.trace ℚ K a)).re = ((Algebra.trace ℚ K a : ℚ) : ℝ) := by
    simp
  rw [hq] at h2
  rw [h2]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Complex.re_sum]
  have hfib : ∀ φ ∈ (Finset.univ.filter fun φ : K →+* ℂ => InfinitePlace.mk φ = w),
      (φ a).re = (w.embedding a).re := by
    intro φ hφ
    have hm := (Finset.mem_filter.mp hφ).2
    rw [← InfinitePlace.mk_embedding w, InfinitePlace.mk_eq_iff] at hm
    rcases hm with rfl | hc
    · rfl
    · rw [← hc, ComplexEmbedding.conjugate_coe_eq, Complex.conj_re]
  rw [Finset.sum_congr rfl hfib, Finset.sum_const]
  have hcard : (Finset.univ.filter fun φ : K →+* ℂ => InfinitePlace.mk φ = w).card = 2 := by
    have hnr : ¬ w.IsReal := fun hr =>
      (Fintype.card_eq_zero_iff.mp (IsTotallyComplex.nrRealPlaces_eq_zero (K := K))).false ⟨w, hr⟩
    rw [InfinitePlace.card_filter_mk_eq w, InfinitePlace.mult, if_neg hnr]
  rw [hcard, nsmul_eq_mul]
  push_cast
  ring

/-- **Exact Trace–Pairing Identity**:
`inner ℝ (realizeHLat b X x) (2 • cE (realizeHLat b.dualBasis (dualFrame X) f)) = Tr_{K/ℚ}(f x)`. -/
theorem inner_realizeHLat_cE (b : Module.Basis ι K V)
    (X : InfinitePlace K → Matrix ι ι ℂ) (hX : ∀ v, IsUnit (X v).det)
    (x : V) (f : Module.Dual K V) :
    inner ℝ (realizeHLat b X x)
        ((2 : ℝ) • cE K ι (realizeHLat b.dualBasis (dualFrame X) f)) =
      ((Algebra.trace ℚ K (f x) : ℚ) : ℝ) := by
  rw [real_inner_smul_right, EuclideanSpace.inner_eq_star_dotProduct, dotProduct,
    Fintype.sum_prod_type, Finset.mul_sum, ident_trace_eq (f x)]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Fintype.sum_prod_type]
  have hplace : ∑ i : ι, ∑ r : Fin 2, star (realizeHLat b X x (v, i, r)) *
      cE K ι (realizeHLat b.dualBasis (dualFrame X) f) (v, i, r) =
      (∑ i : ι, fcoord b X v x i * fcoord b.dualBasis (dualFrame X) v f i).re := by
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Fin.sum_univ_two]
    simp only [star_trivial, realizeHLat_apply0, realizeHLat_apply1, cE_apply, ↓reduceIte,
      Fin.one_eq_zero_iff, Nat.reduceEqDiff, Complex.mul_re]
    ring
  have hcomm : ∑ i : ι, ∑ r : Fin 2,
      cE K ι (realizeHLat b.dualBasis (dualFrame X) f) (v, i, r) *
        star (realizeHLat b X x (v, i, r)) =
      ∑ i : ι, ∑ r : Fin 2, star (realizeHLat b X x (v, i, r)) *
        cE K ι (realizeHLat b.dualBasis (dualFrame X) f) (v, i, r) :=
    Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun r _ => mul_comm _ _
  change 2 * (∑ i : ι, ∑ r : Fin 2,
      cE K ι (realizeHLat b.dualBasis (dualFrame X) f) (v, i, r) *
        star (realizeHLat b X x (v, i, r))) = 2 * (v.embedding (f x)).re
  rw [hcomm, hplace]
  have hdot : ∑ i : ι, fcoord b X v x i * fcoord b.dualBasis (dualFrame X) v f i =
      v.embedding (f x) := by
    have hinv : (dualFrame X v)⁻¹ = (X v).transpose := by
      unfold dualFrame
      exact Matrix.nonsing_inv_nonsing_inv _ (by rw [Matrix.det_transpose]; exact hX v)
    change dotProduct (((X v)⁻¹).mulVec (vecAt b v x))
      (((dualFrame X v)⁻¹).mulVec (vecAt b.dualBasis v f)) = v.embedding (f x)
    rw [hinv, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose,
      Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (hX v), Matrix.one_mulVec]
    have hfx : f x = ∑ i : ι, b.repr x i * b.dualBasis.repr f i := by
      conv_lhs => rw [← b.sum_repr x, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, smul_eq_mul, b.dualBasis_repr]
    rw [hfx, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul]
    rfl
  rw [hdot]

open nonZeroDivisors in
lemma misc_mem_dual_one (t : K) :
    t ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 K)⁰ K) ↔
      ∀ s : 𝓞 K, ∃ z : ℤ, Algebra.trace ℚ K (t * (s : K)) = z := by
  have h1 : (1 : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := one_ne_zero
  rw [FractionalIdeal.mem_dual h1]
  constructor
  · intro h s
    obtain ⟨z, hz⟩ := h (s : K) ((FractionalIdeal.mem_one_iff _).2 ⟨s, rfl⟩)
    exact ⟨z, by simpa [Algebra.traceForm_apply] using hz.symm⟩
  · intro h a ha
    obtain ⟨s, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 ha
    obtain ⟨z, hz⟩ := h s
    exact ⟨z, by simpa [Algebra.traceForm_apply] using hz.symm⟩

open nonZeroDivisors in
lemma misc_diff_mul :
    ((differentIdeal ℤ (𝓞 K) : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) *
      FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 K)⁰ K) = 1 := by
  rw [coeIdeal_differentIdeal ℤ ℚ K (𝓞 K)]
  exact inv_mul_cancel₀ (FractionalIdeal.dual_ne_zero ℤ ℚ one_ne_zero)

open nonZeroDivisors in
/-- **Exact Different-Ideal Relation (`dual_inf_ann_eq`)**:
`dualLatO A ⊓ annO N = differentIdeal ℤ (𝓞 K) • (tdualLatO A ⊓ annO N)`. -/
theorem dual_inf_ann_eq (A N : Submodule (𝓞 K) V) :
    dualLatO (K := K) A ⊓ annO (K := K) N =
      differentIdeal ℤ (𝓞 K) • (tdualLatO (K := K) A ⊓ annO (K := K) N) := by
  set D1 := FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 K)⁰ K)
  set 𝔡 := differentIdeal ℤ (𝓞 K)
  apply le_antisymm
  · rintro f ⟨hfA, hfN⟩
    have key : ∀ t ∈ ((𝔡 : FractionalIdeal (𝓞 K)⁰ K) * D1 : FractionalIdeal (𝓞 K)⁰ K),
        t • f ∈ 𝔡 • (tdualLatO (K := K) A ⊓ annO (K := K) N) := by
      intro t ht
      rw [← FractionalIdeal.mem_coe, FractionalIdeal.coe_mul] at ht
      refine Submodule.mul_induction_on ht ?_ ?_
      · intro r hr η hη
        obtain ⟨r₀, hr₀, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hr
        have hηf : η • f ∈ tdualLatO (K := K) A ⊓ annO (K := K) N := by
          refine ⟨?_, fun x hx => by simp [hfN x hx]⟩
          intro x hx
          obtain ⟨s, hs⟩ := hfA x hx
          obtain ⟨z, hz⟩ := (misc_mem_dual_one η).1 hη s
          exact ⟨z, by simp only [LinearMap.smul_apply, smul_eq_mul, ← hs]; exact hz⟩
        have hsm : (algebraMap (𝓞 K) K r₀ * η) • f = r₀ • (η • f) := by
          rw [mul_smul, algebraMap_smul]
        rw [hsm]
        exact Submodule.smul_mem_smul hr₀ hηf
      · intro t₁ t₂ h₁ h₂
        rw [add_smul]
        exact add_mem h₁ h₂
    have h1 : (1 : K) ∈ ((𝔡 : FractionalIdeal (𝓞 K)⁰ K) * D1 : FractionalIdeal (𝓞 K)⁰ K) := by
      rw [misc_diff_mul]
      exact (FractionalIdeal.mem_one_iff _).2 ⟨1, by simp⟩
    simpa using key 1 h1
  · rw [Submodule.smul_le]
    rintro r hr g ⟨hgA, hgN⟩
    refine ⟨?_, (annO (K := K) N).smul_mem r hgN⟩
    intro x hx
    have hgx : g x ∈ D1 := by
      rw [misc_mem_dual_one]
      intro s
      obtain ⟨z, hz⟩ := hgA (s • x) (A.smul_mem s hx)
      exact ⟨z, by rw [← hz, ← algebraMap_smul K s x, map_smul, smul_eq_mul, mul_comm]⟩
    have hr' : (algebraMap (𝓞 K) K r) ∈ (𝔡 : FractionalIdeal (𝓞 K)⁰ K) :=
      (FractionalIdeal.mem_coeIdeal _).2 ⟨r, hr, rfl⟩
    have hm := FractionalIdeal.mul_mem_mul hr' hgx
    rw [misc_diff_mul] at hm
    obtain ⟨s, hs⟩ := (FractionalIdeal.mem_one_iff _).1 hm
    exact ⟨s, by rw [hs, LinearMap.smul_apply, ← algebraMap_smul K r (g x), smul_eq_mul]⟩

lemma span_zRealize_top (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (A : Submodule (𝓞 K) V) (hA : A.FG)
    (hsp : Submodule.span K (A : Set V) = ⊤) :
    Submodule.span ℝ ((zRealize b X A : Submodule ℤ _) :
      Set (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2))) = ⊤ := by
  letI := discreteTopology_zRealize_of_fg b X hX A hA
  exact (isZLattice_zRealize_of_good b X hX A hA hsp).span_top

/-- **Euclidean Dual / Annihilator Correspondence**:
`dualLat (zRealize A) ⊓ (span ℝ (zRealize N))ᗮ = (zRealize (tdualLatO A ⊓ annO N)).map (2 • cE)`. -/
theorem dualZ_zRealize_eq (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (A : Submodule (𝓞 K) V) (hA : A.FG)
    (hsp : Submodule.span K (A : Set V) = ⊤) (N : Submodule (𝓞 K) V) :
    dualLat (zRealize b X A) ⊓
        ((Submodule.span ℝ ((zRealize b X N : Submodule ℤ _) : Set _))ᗮ).restrictScalars ℤ =
      (zRealize b.dualBasis (dualFrame X) (tdualLatO (K := K) A ⊓ annO (K := K) N)).map
        (((2 : ℝ) • cE K ι).restrictScalars ℤ) := by
  classical
  have : Module.Finite K V := Module.Finite.of_basis b
  set ρ := realizeHLat b X
  set ρ' := realizeHLat b.dualBasis (dualFrame X)
  let T : EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2) →ₗ[ℝ] _ := (2 : ℝ) • cE K ι
  have hT : ∀ (x : V) (f : Module.Dual K V),
      inner ℝ (ρ x) (T (ρ' f)) = ((Algebra.trace ℚ K (f x) : ℚ) : ℝ) :=
    fun x f => inner_realizeHLat_cE b X hX x f
  have hspanA := span_zRealize_top b X hX A hA hsp
  ext y
  simp only [Submodule.mem_inf, Submodule.restrictScalars_mem, Submodule.mem_map,
    LinearMap.restrictScalars_apply]
  constructor
  · rintro ⟨⟨_, hy1⟩, hy2⟩
    obtain ⟨s, hsA, hspan, hli⟩ := exists_linearIndependent K (A : Set V)
    let _ : Fintype s := hli.setFinite.fintype
    let e : s → V := Subtype.val
    have he : ∀ j : s, (j : V) ∈ A := fun j => hsA j.2
    have hmemA : ∀ (k : Free.ChooseBasisIndex ℤ (𝓞 K)) (j : s),
        (RingOfIntegers.basis K k : 𝓞 K) • (j : V) ∈ A :=
      fun k j => A.smul_mem _ (he j)
    have hex : ∀ (j : s) (k : Free.ChooseBasisIndex ℤ (𝓞 K)),
        ∃ n : ℤ, (n : ℝ) = inner ℝ (ρ (NumberField.integralBasis K k • (j : V))) y := by
      intro j k
      have hk_eq : NumberField.integralBasis K k • (j : V) =
          (RingOfIntegers.basis K k : 𝓞 K) • (j : V) := by
        rw [NumberField.integralBasis_apply, algebraMap_smul]
      rw [hk_eq]
      obtain ⟨n, hn⟩ := hy1 _ ⟨_, hmemA k j, rfl⟩
      exact ⟨n, by rw [real_inner_comm]; exact hn.symm⟩
    choose t ht using hex
    let ω' := (Algebra.traceForm ℚ K).dualBasis (traceForm_nondegenerate ℚ K)
      (NumberField.integralBasis K)
    have hω : ∀ k l, Algebra.trace ℚ K (NumberField.integralBasis K l * ω' k) =
        if l = k then 1 else 0 := fun k l => by
      rw [mul_comm, ← Algebra.traceForm_apply]
      exact LinearMap.BilinForm.apply_dualBasis_left _ _ k l
    let c : s → K := fun j => ∑ k, ((t j k : ℚ)) • ω' k
    have hc : ∀ j l, Algebra.trace ℚ K (NumberField.integralBasis K l * c j) = (t j l : ℚ) := by
      intro j l
      simp only [c, Finset.mul_sum, mul_smul_comm, map_sum, map_smul, hω, smul_eq_mul, mul_ite,
        mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    have hsp' : ⊤ ≤ Submodule.span K (Set.range e) := by
      rw [show Set.range e = s from Subtype.range_coe, hspan, hsp]
    let eB : Module.Basis s K V := Module.Basis.mk hli hsp'
    let f : Module.Dual K V := ∑ j, c j • eB.coord j
    have hfe : ∀ j : s, f (j : V) = c j := by
      intro j
      have : (j : V) = eB j := by simp [eB, e]
      rw [this]
      simp [f, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
    have hTy : T (ρ' f) = y := by
      set z := T (ρ' f) - y
      have hgen : ∀ p : Free.ChooseBasisIndex ℤ (𝓞 K) × s,
          inner ℝ (ρ (NumberField.integralBasis K p.1 • e p.2)) z = 0 := by
        intro p
        simp only [z, inner_sub_right, hT, map_smul, smul_eq_mul, e, hfe, hc, ← ht]
        push_cast; ring
      have hM : Submodule.span K ((Submodule.span (𝓞 K) (Set.range e) : Submodule (𝓞 K) V) :
          Set V) = ⊤ := by
        rw [Submodule.span_span_of_tower]; exact top_le_iff.mp hsp'
      have hsM := span_zRealize_top b X hX _ (Submodule.fg_span (Set.finite_range e)) hM
      have hzl := zRealize_span_eq b X e
      have h1 : ∀ u ∈ zRealize b X (Submodule.span (𝓞 K) (Set.range e)), inner ℝ u z = 0 := by
        intro u hu
        rw [hzl] at hu
        induction hu using Submodule.span_induction with
        | mem _ h => rcases h with ⟨p, rfl⟩; exact hgen p
        | zero => simp
        | add _ _ _ _ h₁ h₂ => rw [inner_add_left, h₁, h₂, add_zero]
        | smul n _ _ h =>
          rw [← Int.cast_smul_eq_zsmul ℝ, real_inner_smul_left, h, mul_zero]
      have h2 : inner ℝ z z = 0 := by
        have hz_sp : z ∈ Submodule.span ℝ ((zRealize b X (Submodule.span (𝓞 K) (Set.range e)) :
            Submodule ℤ _) : Set _) := by rw [hsM]; trivial
        have h_all : ∀ w ∈ Submodule.span ℝ ((zRealize b X (Submodule.span (𝓞 K) (Set.range e)) :
            Submodule ℤ _) : Set _), inner ℝ w z = 0 := by
          intro w hw_sp
          induction hw_sp using Submodule.span_induction with
          | mem u hu => exact h1 u hu
          | zero => simp
          | add _ _ _ _ h₁ h₂ => rw [inner_add_left, h₁, h₂, add_zero]
          | smul a _ _ h => rw [real_inner_smul_left, h, mul_zero]
        exact h_all z hz_sp
      exact sub_eq_zero.mp (inner_self_eq_zero.mp h2)
    refine ⟨ρ' f, ⟨f, Submodule.mem_inf.mpr ⟨?_, ?_⟩, rfl⟩, hTy⟩
    · intro x hx
      obtain ⟨n, hn⟩ := hy1 (ρ x) ⟨x, hx, rfl⟩
      refine ⟨n, ?_⟩
      have h3 := hT x f
      rw [hTy, real_inner_comm, hn] at h3
      exact_mod_cast h3.symm
    · intro x hx
      have h0 : ∀ r : 𝓞 K, Algebra.trace ℚ K ((r : K) * f x) = 0 := by
        intro r
        have hm : ρ (r • x) ∈ Submodule.span ℝ ((zRealize b X N : Submodule ℤ _) : Set _) :=
          Submodule.subset_span ⟨r • x, N.smul_mem r hx, rfl⟩
        have h1 := Submodule.inner_right_of_mem_orthogonal hm hy2
        rw [← hTy, hT] at h1
        have h4 : f (r • x) = (r : K) * f x := by
          rw [← algebraMap_smul K r x, map_smul, smul_eq_mul]
        rw [h4] at h1
        exact_mod_cast h1
      have hz : Algebra.traceForm ℚ K (f x) = 0 :=
        (NumberField.integralBasis K).ext fun k => by
          rw [LinearMap.zero_apply, Algebra.traceForm_apply, NumberField.integralBasis_apply,
            mul_comm]
          exact h0 _
      exact (traceForm_nondegenerate ℚ K).1 (f x) fun n => by rw [hz]; rfl
  · rintro ⟨w, ⟨f, ⟨hfA, hfN⟩, rfl⟩, rfl⟩
    refine ⟨⟨by rw [hspanA]; trivial, ?_⟩, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩
      obtain ⟨n, hn⟩ := hfA x hx
      refine ⟨n, ?_⟩
      rw [real_inner_comm]
      change inner ℝ (ρ x) (T (ρ' f)) = (n : ℝ)
      rw [hT, hn]; simp
    · rw [Submodule.mem_orthogonal]
      intro u hu
      induction hu using Submodule.span_induction with
      | mem _ h =>
        rcases h with ⟨x, hx, rfl⟩
        change inner ℝ (ρ x) (T (ρ' f)) = 0
        rw [hT, hfN x hx, map_zero]; simp
      | zero => simp
      | add _ _ _ _ h₁ h₂ => rw [inner_add_left, h₁, h₂, add_zero]
      | smul a _ _ h => rw [real_inner_smul_left, h, mul_zero]

/-- Scaling covolume of a discrete lattice under a `c`-similarity (`‖φ x‖ = c * ‖x‖`). -/
lemma covol_map_scaled {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] (φ : E →ₗ[ℝ] F) (c : ℝ) (hc : 0 < c)
    (hφ : ∀ x y : E, inner ℝ (φ x) (φ y) = c ^ 2 * inner ℝ x y)
    (M : Submodule ℤ E) [DiscreteTopology M] :
    ∃ (_ : DiscreteTopology (M.map (φ.restrictScalars ℤ))),
      rk (M.map (φ.restrictScalars ℤ)) = rk M ∧
      covol (M.map (φ.restrictScalars ℤ)) = c ^ rk M * covol M := by
  have hφ_inj : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    have h0 : c ^ 2 * inner ℝ x x = 0 := by rw [← hφ x x, hx, inner_zero_left]
    have hx0 : inner ℝ x x = 0 := (mul_eq_zero.mp h0).resolve_left (pow_ne_zero 2 hc.ne')
    exact inner_self_eq_zero.mp hx0
  let M' := M.map (φ.restrictScalars ℤ)
  let b := Module.finBasis ℤ M
  let e : M ≃ₗ[ℤ] M' := LinearEquiv.ofInjective (φ.restrictScalars ℤ |>.comp M.subtype)
    (hφ_inj.comp Subtype.val_injective) |>.trans
    (LinearEquiv.ofEq _ _ (by ext y; simp [M']))
  let b' := b.map e
  have hb' : ∀ i, (b' i : F) = φ (b i : E) := fun i => rfl
  have hli' : LinearIndependent ℝ (fun i => (b' i : F)) := by
    rw [Fintype.linearIndependent_iff]
    intro t ht i
    have ht' : φ (∑ j, t j • (b j : E)) = 0 := by
      rw [map_sum]
      simpa [map_smul, hb'] using ht
    exact Fintype.linearIndependent_iff.mp (linearIndependent_coe_basis M b) t
      (hφ_inj (ht'.trans (map_zero φ).symm)) i
  have hDisc' : DiscreteTopology M' := discreteTopology_of_fin_basis_real_li b' hli'
  have hrk' : rk M' = rk M := e.symm.finrank_eq
  have hG : Matrix.gram ℝ (fun i => (b' i : F)) = (c ^ 2) • Matrix.gram ℝ (fun i => (b i : E)) := by
    ext i j
    simp only [Matrix.gram_apply, Matrix.smul_apply, smul_eq_mul, hb']
    exact hφ _ _
  have hcov' : covol M' = c ^ rk M * covol M := by
    rw [covol_eq_sqrt_det_gram M' b', covol_eq_sqrt_det_gram M b, hG, Matrix.det_smul,
      Fintype.card_fin]
    have hnn : 0 ≤ (c ^ 2) ^ Module.finrank ℤ M := by positivity
    change Real.sqrt ((c ^ 2) ^ Module.finrank ℤ M * (Matrix.gram ℝ fun i => (b i : E)).det) =
      c ^ Module.finrank ℤ M * Real.sqrt (Matrix.gram ℝ fun i => (b i : E)).det
    rw [Real.sqrt_mul hnn, ← pow_mul, mul_comm 2, pow_mul, Real.sqrt_sq (pow_nonneg hc.le _)]
  exact ⟨hDisc', hrk', hcov'⟩

lemma dualLatO_fg (bV : Module.Basis ι K V) (A : Submodule (𝓞 K) V)
    (hsp : Submodule.span K (A : Set V) = ⊤) :
    (dualLatO (K := K) A).FG := by
  classical
  have : Module.Finite K V := Module.Finite.of_basis bV
  have hex : ∀ j : ι, ∃ (d : ℕ), 0 < d ∧ (d : K) • bV j ∈ A := by
    intro j
    have hj : bV j ∈ Submodule.span K (A : Set V) := hsp ▸ trivial
    obtain ⟨c, hcA, hc_sum⟩ := Submodule.mem_span_set.mp hj
    obtain ⟨D, hD_pos, hD⟩ :=
      exists_pos_nat_mul_mem_ringOfIntegers_fin (fun x : c.support => c x)
    choose a ha using hD
    refine ⟨D, hD_pos, ?_⟩
    rw [← hc_sum, Finsupp.sum, Finset.smul_sum]
    refine Submodule.sum_mem A fun x hx => ?_
    rw [smul_smul, ha ⟨x, hx⟩, algebraMap_smul K (a ⟨x, hx⟩) x]
    exact A.smul_mem _ (hcA hx)
  choose d hd_pos hd_mem using hex
  let e : ι → V := fun j => (d j : K) • bV j
  have he_li : LinearIndependent K e :=
    bV.linearIndependent.units_smul (fun j => Units.mk0 (d j : K) (Nat.cast_ne_zero.mpr (hd_pos j).ne'))
  have he_sp : ⊤ ≤ Submodule.span K (Set.range e) := by
    rw [top_le_iff]
    have hfin : Module.finrank K (Submodule.span K (Set.range e)) = Module.finrank K V := by
      rw [finrank_span_eq_card he_li, Module.finrank_eq_card_basis bV]
    exact Submodule.eq_top_of_finrank_eq hfin
  let bE : Module.Basis ι K V := Module.Basis.mk he_li he_sp
  have hle : dualLatO (K := K) A ≤ Submodule.span (𝓞 K) (Set.range bE.dualBasis) := by
    intro f hf
    have hcoeff : ∀ j : ι, ∃ a : 𝓞 K, f (bE j) = algebraMap (𝓞 K) K a := by
      intro j
      have hj : bE j ∈ A := by simp [bE, e, hd_mem j]
      obtain ⟨a, ha⟩ := hf (bE j) hj
      exact ⟨a, ha.symm⟩
    choose a ha using hcoeff
    have hf_eq : f = ∑ j : ι, a j • bE.dualBasis j := by
      apply bE.ext
      intro j
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, ← algebraMap_smul K (a _) _,
        smul_eq_mul, ha j, Module.Basis.dualBasis_apply_self, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
    rw [hf_eq]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  exact Submodule.FG.of_le (Submodule.fg_span (Set.finite_range bE.dualBasis)) hle

lemma dualLatO_span_top (b : Module.Basis ι K V) (A : Submodule (𝓞 K) V) (hA : A.FG) :
    Submodule.span K ((dualLatO (K := K) A : Submodule (𝓞 K) (Module.Dual K V)) :
      Set (Module.Dual K V)) = ⊤ := by
  classical
  have : Module.Finite K V := Module.Finite.of_basis b
  obtain ⟨S, hS⟩ := hA
  let coords : S × ι → K := fun p => b.repr (p.1 : V) p.2
  obtain ⟨D, hD_pos, hD⟩ := exists_pos_nat_mul_mem_ringOfIntegers_fin coords
  choose a ha using hD
  have hcoord : ∀ (y : V) (j : ι), b.dualBasis j y = b.repr y j := by
    intro y j
    conv_lhs => rw [← b.sum_repr y]
    simp only [map_sum, map_smul, smul_eq_mul, b.dualBasis_apply_self, mul_ite, mul_one,
      mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  have hmem : ∀ i : ι, (D : 𝓞 K) • b.dualBasis i ∈ dualLatO (K := K) A := by
    intro i x hxA
    have hxS : x ∈ Submodule.span (𝓞 K) (S : Set V) := hS ▸ hxA
    have key : ∀ y ∈ Submodule.span (𝓞 K) (S : Set V),
        ((D : 𝓞 K) • b.dualBasis i) y ∈ Set.range (algebraMap (𝓞 K) K) := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem s hs =>
        refine ⟨a (⟨s, hs⟩, i), ?_⟩
        have h1 : ((D : 𝓞 K) • b.dualBasis i) s = (D : K) * b.dualBasis i s := by
          rw [LinearMap.smul_apply, ← algebraMap_smul K (D : 𝓞 K), smul_eq_mul]; simp
        rw [h1, hcoord s i]
        exact (ha (⟨s, hs⟩, i)).symm
      | zero => exact ⟨0, by simp⟩
      | add u w _ _ hu hw =>
        obtain ⟨a₁, ha₁⟩ := hu
        obtain ⟨a₂, ha₂⟩ := hw
        exact ⟨a₁ + a₂, by rw [map_add, map_add, ha₁, ha₂]⟩
      | smul r y _ hy =>
        obtain ⟨a₁, ha₁⟩ := hy
        refine ⟨r * a₁, ?_⟩
        rw [map_mul, ha₁, ← smul_eq_mul, LinearMap.map_smul_of_tower, smul_eq_mul, Algebra.smul_def]
    exact key x hxS
  rw [eq_top_iff]
  intro f _
  have hf_eq : f = ∑ i : ι, (f (b i) * (D : K)⁻¹) • ((D : K) • b.dualBasis i) := by
    apply b.ext
    intro j
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
      Module.Basis.dualBasis_apply_self, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
    have hD_ne : (D : K) ≠ 0 := Nat.cast_ne_zero.mpr hD_pos.ne'
    field_simp [hD_ne]
  rw [hf_eq]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
  have h1 : (D : K) • b.dualBasis i = (D : 𝓞 K) • b.dualBasis i := by
    rw [← algebraMap_smul K (D : 𝓞 K)]; simp
  rw [h1]
  exact Submodule.subset_span (hmem i)

private lemma trace_coe_eq (K : Type*) [Field K] [NumberField K] (z : 𝓞 K) :
    ((Algebra.trace ℤ (𝓞 K) z : ℤ) : ℚ) = Algebra.trace ℚ K (z : K) := by
  let bO := RingOfIntegers.basis K
  let bK := NumberField.integralBasis K
  rw [Algebra.trace_eq_matrix_trace bO z, Algebra.trace_eq_matrix_trace bK (z : K)]
  simp only [Matrix.trace, Matrix.diag, Int.cast_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.leftMulMatrix_apply, Algebra.leftMulMatrix_apply,
    LinearMap.toMatrix_apply, LinearMap.toMatrix_apply]
  have h1 : (Algebra.lmul ℚ K (z : K)) (bK i) = ((z * bO i : 𝓞 K) : K) := by
    change (z : K) * bK i = _
    rw [NumberField.integralBasis_apply]; rfl
  have h2 : ((z * bO i : 𝓞 K) : K) = ∑ j, ((bO.repr (z * bO i) j : ℤ) : ℚ) • bK j := by
    conv_lhs =>
      rw [show ((z * bO i : 𝓞 K) : K) = algebraMap (𝓞 K) K (z * bO i) from rfl,
        ← bO.sum_repr (z * bO i), map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_zsmul, NumberField.integralBasis_apply, Int.cast_smul_eq_zsmul ℚ]
  rw [h1, h2, map_sum]
  simp only [map_smul, Finsupp.coe_finsetSum, Finsupp.coe_smul, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, bK.repr_self, Finsupp.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  rfl

/-- **Exact Ideal-Norm Formula for the Different Ideal (`absNorm_differentIdeal_eq_discr`)**:
`Ideal.absNorm (differentIdeal ℤ (𝓞 K)) = |(discr K : ℝ)|`, proved directly from
`NumberField.discr_eq_discr`, the inverse codifferent fractional ideal `FractionalIdeal.dual ℤ ℚ 1`,
`twist_index`, and `covol_eq_index_mul_covol`. -/
theorem absNorm_differentIdeal_eq_discr (K : Type*) [Field K] [NumberField K]
    [IsTotallyComplex K] :
    (Ideal.absNorm (differentIdeal ℤ (𝓞 K)) : ℝ) = |(NumberField.discr K : ℝ)| := by
  classical
  let bO := RingOfIntegers.basis K
  let bK := NumberField.integralBasis K
  let ω' := (Algebra.traceForm ℚ K).dualBasis (traceForm_nondegenerate ℚ K) bK
  have hω : ∀ k l, Algebra.trace ℚ K (bK l * ω' k) = if l = k then 1 else 0 := fun k l => by
    rw [mul_comm, ← Algebra.traceForm_apply]
    exact LinearMap.BilinForm.apply_dualBasis_left _ _ k l
  let G : Matrix (Free.ChooseBasisIndex ℤ (𝓞 K)) (Free.ChooseBasisIndex ℤ (𝓞 K)) ℤ :=
    fun j i => Algebra.trace ℤ (𝓞 K) (bO i * bO j)
  have hG_det : G.det = NumberField.discr K := by
    rw [← NumberField.discr_eq_discr K bO, Algebra.discr_def]
    congr 1
    ext i j
    simp [G, Algebra.traceMatrix_apply, Algebra.traceForm_apply, mul_comm]
  have hbK_exp : ∀ i, bK i = ∑ j, (G j i : ℚ) • ω' j := by
    intro i
    have hcoeff : ∀ l, Algebra.trace ℚ K (bK l * bK i) =
        Algebra.trace ℚ K (bK l * ∑ j, (G j i : ℚ) • ω' j) := by
      intro l
      have hL : Algebra.trace ℚ K (bK l * bK i) = (G l i : ℚ) := by
        rw [NumberField.integralBasis_apply, NumberField.integralBasis_apply]
        simpa [G, mul_comm] using (trace_coe_eq K (bO i * bO l)).symm
      have hR : Algebra.trace ℚ K (bK l * ∑ j, (G j i : ℚ) • ω' j) = (G l i : ℚ) := by
        simp only [Finset.mul_sum, mul_smul_comm, map_sum, map_smul, hω, smul_eq_mul,
          mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
      rw [hL, hR]
    apply sub_eq_zero.mp
    refine (traceForm_nondegenerate ℚ K).1 _ fun x => ?_
    rw [← bK.sum_repr x, Algebra.traceForm_apply, Finset.mul_sum, map_sum]
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [mul_smul_comm, map_smul,
      show (bK i - ∑ j, (G j i : ℚ) • ω' j) * bK l =
        bK l * bK i - bK l * ∑ j, (G j i : ℚ) • ω' j by ring,
      map_sub, hcoeff l, sub_self, smul_zero]
  let D1 := FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)
  let M : Submodule (𝓞 K) K := (D1 : Submodule (𝓞 K) K)
  let O_sub : Submodule (𝓞 K) K := ((1 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : Submodule (𝓞 K) K)
  have hmem_D1 : ∀ x : K, x ∈ D1 ↔ ∀ y : 𝓞 K, ∃ z : ℤ, Algebra.trace ℚ K (x * (y : K)) = z := by
    intro x
    rw [FractionalIdeal.mem_dual]
    · simp only [FractionalIdeal.mem_one_iff, forall_exists_index, forall_apply_eq_imp_iff]
      constructor
      · intro h y
        obtain ⟨r, hr⟩ := h y
        exact ⟨r, by simpa [Algebra.traceForm_apply] using hr.symm⟩
      · intro h y
        obtain ⟨z, hz⟩ := h y
        exact ⟨z, by simpa [Algebra.traceForm_apply] using hz.symm⟩
    · exact one_ne_zero
  have hM_spanZ : M.restrictScalars ℤ = Submodule.span ℤ (Set.range ω') := by
    ext x
    change x ∈ D1 ↔ x ∈ Submodule.span ℤ (Set.range ω')
    constructor
    · intro hx
      rw [hmem_D1] at hx
      have hc : ∀ j, ∃ z : ℤ, Algebra.trace ℚ K (x * bK j) = z := fun j => by
        rw [NumberField.integralBasis_apply]
        exact hx (bO j)
      choose c hc using hc
      have hx_eq : x = ∑ j, (c j : ℤ) • ω' j := by
        apply sub_eq_zero.mp
        refine (traceForm_nondegenerate ℚ K).1 _ fun y => ?_
        rw [← bK.sum_repr y, Algebra.traceForm_apply, Finset.mul_sum, map_sum]
        refine Finset.sum_eq_zero fun j _ => ?_
        rw [mul_smul_comm, map_smul]
        have htr : Algebra.trace ℚ K ((x - ∑ k, (c k : ℤ) • ω' k) * bK j) = 0 := by
          rw [sub_mul, map_sub, hc j]
          have hsum : ∑ k, ((c k : ℤ) • ω' k) * bK j = ∑ k, (c k : ℚ) • (bK j * ω' k) :=
            Finset.sum_congr rfl fun k _ => by
              rw [← Int.cast_smul_eq_zsmul ℚ, smul_mul_assoc, mul_comm (ω' k)]
          rw [Finset.sum_mul, hsum, map_sum]
          simp only [map_smul, hω, smul_eq_mul, mul_ite, mul_one, mul_zero]
          simp [sub_self]
        rw [htr, smul_zero]
      rw [hx_eq]
      exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
    · intro hx
      rw [hmem_D1]
      intro y
      have hy_repr : (y : K) = ∑ j, (bO.repr y j : ℚ) • bK j := by
        conv_lhs => rw [show (y : K) = algebraMap (𝓞 K) K y from rfl, ← bO.sum_repr y, map_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_zsmul, NumberField.integralBasis_apply, Int.cast_smul_eq_zsmul ℚ]
      induction hx using Submodule.span_induction with
      | mem _ h =>
        rcases h with ⟨k, rfl⟩
        refine ⟨bO.repr y k, ?_⟩
        rw [hy_repr, Finset.mul_sum]
        simp only [mul_smul_comm, map_sum, map_smul, mul_comm (ω' k) (bK _), hω, smul_eq_mul,
          mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
      | zero => exact ⟨0, by simp⟩
      | add u w _ _ hu hw =>
        obtain ⟨z₁, hz₁⟩ := hu
        obtain ⟨z₂, hz₂⟩ := hw
        exact ⟨z₁ + z₂, by rw [add_mul, map_add, hz₁, hz₂, Int.cast_add]⟩
      | smul n u _ hu =>
        obtain ⟨z, hz⟩ := hu
        exact ⟨n * z, by rw [smul_mul_assoc, map_zsmul, hz, zsmul_eq_mul, Int.cast_mul]⟩
  have hO_spanZ : O_sub.restrictScalars ℤ = Submodule.span ℤ (Set.range bK) := by
    ext x
    change x ∈ (1 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ↔ x ∈ Submodule.span ℤ (Set.range bK)
    rw [FractionalIdeal.mem_one_iff]
    constructor
    · rintro ⟨y, rfl⟩
      have hy : (algebraMap (𝓞 K) K y) = ∑ j, (bO.repr y j : ℤ) • bK j := by
        conv_lhs => rw [← bO.sum_repr y, map_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_zsmul, NumberField.integralBasis_apply]
      rw [hy]
      exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
    · intro hx
      induction hx using Submodule.span_induction with
      | mem _ h => rcases h with ⟨j, rfl⟩; exact ⟨bO j, (NumberField.integralBasis_apply K j).symm⟩
      | zero => exact ⟨0, by simp⟩
      | add _ _ _ _ ha hb =>
        obtain ⟨a, ha⟩ := ha
        obtain ⟨b, hb⟩ := hb
        exact ⟨a + b, by rw [map_add, ha, hb]⟩
      | smul n _ _ ha =>
        obtain ⟨a, ha⟩ := ha
        exact ⟨n • a, by rw [map_zsmul, ha]⟩
  have hM_fg : M.FG := by
    refine ⟨Finset.univ.image ω', ?_⟩
    apply le_antisymm
    · rw [Finset.coe_image, Finset.coe_univ, Set.image_univ, Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      change ω' k ∈ M.restrictScalars ℤ
      rw [hM_spanZ]
      exact Submodule.subset_span ⟨k, rfl⟩
    · intro x hx
      have hxZ : x ∈ M.restrictScalars ℤ := hx
      rw [hM_spanZ] at hxZ
      have hsub : Submodule.span ℤ (Set.range ω') ≤
          (Submodule.span (𝓞 K) (Finset.univ.image ω' : Set K)).restrictScalars ℤ := by
        rw [Submodule.span_le]
        rintro _ ⟨k, rfl⟩
        exact Submodule.subset_span (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ (Finset.mem_univ k)))
      exact hsub hxZ
  have hdiff_mul : (differentIdeal ℤ (𝓞 K) : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) * D1 = 1 := by
    rw [coeIdeal_differentIdeal ℤ ℚ K (𝓞 K)]
    exact inv_mul_cancel₀ (FractionalIdeal.dual_ne_zero ℤ ℚ one_ne_zero)
  have hsmul_eq : differentIdeal ℤ (𝓞 K) • M = O_sub := by
    apply le_antisymm
    · rw [Submodule.smul_le]
      intro r hr x hx
      change x ∈ D1 at hx
      change (algebraMap (𝓞 K) K r) * x ∈ (1 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)
      rw [← hdiff_mul]
      exact FractionalIdeal.mul_mem_mul ((FractionalIdeal.mem_coeIdeal _).mpr ⟨r, hr, rfl⟩) hx
    · intro y hy
      change y ∈ (1 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) at hy
      obtain ⟨y₀, rfl⟩ := (FractionalIdeal.mem_one_iff _).mp hy
      have h1_mem : (1 : K) ∈ (differentIdeal ℤ (𝓞 K) : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) * D1 := by
        rw [hdiff_mul]; exact (FractionalIdeal.mem_one_iff _).mpr ⟨1, by simp⟩
      have h1_smul : (1 : K) ∈ differentIdeal ℤ (𝓞 K) • M := by
        rw [← FractionalIdeal.mem_coe, FractionalIdeal.coe_mul] at h1_mem
        refine Submodule.mul_induction_on h1_mem ?_ ?_
        · intro r hr m hm
          obtain ⟨r₀, hr₀, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).mp hr
          change r₀ • m ∈ differentIdeal ℤ (𝓞 K) • M
          exact Submodule.smul_mem_smul hr₀ hm
        · intro a b ha hb; exact Submodule.add_mem _ ha hb
      simpa [Algebra.smul_def] using (differentIdeal ℤ (𝓞 K) • M).smul_mem y₀ h1_smul
  have hM_sp : Submodule.span K (M : Set K) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have h1 : (1 : K) ∈ M := by
      have h0 : (1 : K) ∈ O_sub := (FractionalIdeal.mem_one_iff _).mpr ⟨1, by simp⟩
      rw [← hsmul_eq] at h0
      exact Submodule.smul_le_right h0
    simpa using Submodule.smul_mem _ x (Submodule.subset_span h1)
  have hidx_diff : O_sub.toAddSubgroup.relIndex M.toAddSubgroup = Ideal.absNorm (differentIdeal ℤ (𝓞 K)) := by
    have htw := twist_index M hM_fg (differentIdeal ℤ (𝓞 K)) differentIdeal_ne_bot
    have hrk1 : rkK (K := K) M = 1 := by
      unfold rkK
      rw [hM_sp, finrank_top, Module.finrank_self]
    rw [← hsmul_eq, htw, hrk1, pow_one]
  let b₁ : Module.Basis PUnit.{1} K K := Module.Basis.singleton PUnit.{1} K
  let X₁ : InfinitePlace K → Matrix PUnit.{1} PUnit.{1} ℂ := fun _ => 1
  have hX₁ : ∀ v, IsUnit (X₁ v).det := fun v => by simp [X₁]
  let ρ := realizeHLat b₁ X₁
  have h_inj : Function.Injective ρ := realizeHLat_injective b₁ X₁ hX₁
  have h_rat : ∀ (q : ℚ) (x : K), ρ (q • x) = (q : ℝ) • ρ x := fun q x => by
    rw [Rat.smul_def]
    exact realizeHLat_smul_rat b₁ X₁ q x
  have h_bK_li : LinearIndependent ℝ (fun i => ρ (bK i)) := by
    have he : LinearIndependent K (fun _ : PUnit.{1} => (1 : K)) := by
      rw [Fintype.linearIndependent_iff]
      intro c hc _
      simpa using hc
    have hfull := linearIndependent_realizeHLat_integralBasis b₁ X₁ hX₁ (fun _ : PUnit.{1} => (1 : K)) he
    have hcomp := hfull.comp (fun i => (i, PUnit.unit)) (fun _ _ h => (Prod.ext_iff.mp h).1)
    have h_bK_eq : (fun i => ρ (bK i)) =
        (fun p : Free.ChooseBasisIndex ℤ (𝓞 K) × PUnit.{1} => ρ (bK p.1 • (1 : K))) ∘
          (fun i => (i, PUnit.unit)) := by
      funext i
      simp [bK]
    rw [h_bK_eq]
    exact hcomp
  let zM : Submodule ℤ (EuclideanSpace ℝ (InfinitePlace K × PUnit.{1} × Fin 2)) :=
    (M.toAddSubgroup.map ρ).toIntSubmodule
  let zO : Submodule ℤ (EuclideanSpace ℝ (InfinitePlace K × PUnit.{1} × Fin 2)) :=
    (O_sub.toAddSubgroup.map ρ).toIntSubmodule
  have hzO_le : zO ≤ zM := by
    intro w hw
    rcases hw with ⟨x, hx, rfl⟩
    refine ⟨x, ?_, rfl⟩
    have hx' : x ∈ O_sub := hx
    rw [← hsmul_eq] at hx'
    exact Submodule.smul_le_right hx'
  have h_ω_li : LinearIndependent ℝ (fun i => ρ (ω' i)) := by
    let H : Matrix (Free.ChooseBasisIndex ℤ (𝓞 K)) (Free.ChooseBasisIndex ℤ (𝓞 K)) ℚ :=
      fun k i => bK.repr (ω' i) k
    have hHG : H * G.map (Int.cast : ℤ → ℚ) = 1 := by
      ext k j
      rw [Matrix.mul_apply, Matrix.one_apply]
      have hj : bK j = ∑ i, (G i j : ℚ) • (∑ l, H l i • bK l) := by
        conv_lhs => rw [hbK_exp j]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← bK.sum_repr (ω' i)]
      have hrep := congrArg (fun x => bK.repr x k) hj
      rw [bK.repr_self, Finsupp.single_apply] at hrep
      simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finsupp.coe_smul, Finset.sum_apply,
        Pi.smul_apply, smul_eq_mul, bK.repr_self, Finsupp.single_apply, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] at hrep
      have hrep' : (if k = j then (1 : ℚ) else 0) = ∑ x, (G x j : ℚ) * H k x := by
        simpa only [eq_comm] using hrep
      rw [hrep']
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [H, mul_comm]
    have hdetH : (G.map (Int.cast : ℤ → ℚ)).det * H.det = 1 := by
      have h1 := congrArg Matrix.det hHG
      rw [Matrix.det_mul, Matrix.det_one] at h1
      linarith
    have hunitG : IsUnit (G.map (Int.cast : ℤ → ℚ)).det :=
      isUnit_iff_exists_inv.mpr ⟨H.det, hdetH⟩
    have hinvG : (G.map (Int.cast : ℤ → ℚ))⁻¹ = H := Matrix.inv_eq_left_inv hHG
    have hGH : G.map (Int.cast : ℤ → ℚ) * H = 1 := by
      rw [← hinvG]
      exact Matrix.mul_nonsing_inv _ hunitG
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    have hsum_bK : ∑ k, (∑ j, ((H k j : ℚ) : ℝ) * c j) • ρ (bK k) = 0 := by
      have h1 : ∀ j, ρ (ω' j) = ∑ k, ((H k j : ℚ) : ℝ) • ρ (bK k) := fun j => by
        conv_lhs => rw [← bK.sum_repr (ω' j)]
        rw [map_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [h_rat]
      have h2 : ∑ j, c j • (∑ k, ((H k j : ℚ) : ℝ) • ρ (bK k)) = 0 := by
        simpa only [← h1] using hc
      simp_rw [Finset.smul_sum, smul_smul] at h2
      rw [Finset.sum_comm] at h2
      rw [← h2]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← Finset.sum_smul]
      refine congrArg (· • ρ (bK k)) (Finset.sum_congr rfl fun j _ => mul_comm _ _)
    have hHc : ∀ k, ∑ j, ((H k j : ℚ) : ℝ) * c j = 0 :=
      fun k => Fintype.linearIndependent_iff.mp h_bK_li _ hsum_bK k
    have hmul_zero : ∑ k, ((G i k : ℤ) : ℝ) * (∑ j, ((H k j : ℚ) : ℝ) * c j) = 0 :=
      Finset.sum_eq_zero fun k _ => by rw [hHc k, mul_zero]
    simp_rw [Finset.mul_sum, ← mul_assoc] at hmul_zero
    rw [Finset.sum_comm] at hmul_zero
    have hdiag : ∀ j, (∑ k, ((G i k : ℤ) : ℝ) * ((H k j : ℚ) : ℝ)) * c j =
        (if i = j then (1 : ℝ) else 0) * c j := by
      intro j
      congr 1
      have hGH_ij := congrFun (congrFun hGH i) j
      rw [Matrix.mul_apply, Matrix.one_apply] at hGH_ij
      have hcast := congrArg (Rat.cast : ℚ → ℝ) hGH_ij
      simp only [Matrix.map_apply, Rat.cast_sum, Rat.cast_mul, Rat.cast_intCast] at hcast
      rw [hcast]
      split_ifs <;> simp
    have hfin' : ∑ j, (if i = j then (1 : ℝ) else 0) * c j =
        ∑ j, ∑ k, ((G i k : ℤ) : ℝ) * ((H k j : ℚ) : ℝ) * c j := by
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← hdiag j, Finset.sum_mul]
    have hfin : ∑ j, (if i = j then (1 : ℝ) else 0) * c j = 0 := hfin'.trans hmul_zero
    simpa [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ] using hfin
  have hω_mem_zM : ∀ i, ρ (ω' i) ∈ zM := fun i => ⟨ω' i, by
    have : ω' i ∈ M.restrictScalars ℤ := by rw [hM_spanZ]; exact Submodule.subset_span ⟨i, rfl⟩
    exact this, rfl⟩
  have hzM_basis_li : LinearIndependent ℤ (fun i => (⟨ρ (ω' i), hω_mem_zM i⟩ : zM)) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    have h1 : ∑ j, (c j : ℝ) • ρ (ω' j) = 0 := by
      have := congrArg Subtype.val hc
      simpa [Submodule.coe_sum, Int.cast_smul_eq_zsmul] using this
    exact_mod_cast Fintype.linearIndependent_iff.mp h_ω_li (fun j => (c j : ℝ)) h1 i
  have hzM_basis_sp : ⊤ ≤ Submodule.span ℤ (Set.range fun i => (⟨ρ (ω' i), hω_mem_zM i⟩ : zM)) := by
    rintro ⟨w, ⟨x, hxM, rfl⟩⟩ _
    have hxZ : x ∈ M.restrictScalars ℤ := hxM
    rw [hM_spanZ, Submodule.mem_span_range_iff_exists_fun] at hxZ
    obtain ⟨c, hc⟩ := hxZ
    have hx_eq : x = ∑ i, c i • ω' i := hc.symm
    have hmem : ρ x ∈ zM := ⟨x, hxM, rfl⟩
    have heq : (⟨ρ x, hmem⟩ : zM) =
        ∑ i, c i • (⟨ρ (ω' i), hω_mem_zM i⟩ : zM) := by
      apply Subtype.ext
      rw [show (⟨ρ x, hmem⟩ : zM).1 = ρ (∑ i, c i • ω' i) from congrArg ρ hx_eq,
        map_sum, Submodule.coe_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_zsmul]; rfl
    rw [heq]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  let b_zM : Module.Basis (Free.ChooseBasisIndex ℤ (𝓞 K)) ℤ zM :=
    Module.Basis.mk hzM_basis_li hzM_basis_sp
  have hbK_mem_zO : ∀ i, ρ (bK i) ∈ zO := fun i => ⟨bK i, by
    have : bK i ∈ O_sub.restrictScalars ℤ := by rw [hO_spanZ]; exact Submodule.subset_span ⟨i, rfl⟩
    exact this, rfl⟩
  have hzO_basis_li : LinearIndependent ℤ (fun i => (⟨ρ (bK i), hbK_mem_zO i⟩ : zO)) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    have h1 : ∑ j, (c j : ℝ) • ρ (bK j) = 0 := by
      have := congrArg Subtype.val hc
      simpa [Submodule.coe_sum, Int.cast_smul_eq_zsmul] using this
    exact_mod_cast Fintype.linearIndependent_iff.mp h_bK_li (fun j => (c j : ℝ)) h1 i
  have hzO_basis_sp : ⊤ ≤ Submodule.span ℤ (Set.range fun i => (⟨ρ (bK i), hbK_mem_zO i⟩ : zO)) := by
    rintro ⟨w, ⟨x, hxO, rfl⟩⟩ _
    have hxZ : x ∈ O_sub.restrictScalars ℤ := hxO
    rw [hO_spanZ, Submodule.mem_span_range_iff_exists_fun] at hxZ
    obtain ⟨c, hc⟩ := hxZ
    have hx_eq : x = ∑ i, c i • bK i := hc.symm
    have hmem : ρ x ∈ zO := ⟨x, hxO, rfl⟩
    have heq : (⟨ρ x, hmem⟩ : zO) =
        ∑ i, c i • (⟨ρ (bK i), hbK_mem_zO i⟩ : zO) := by
      apply Subtype.ext
      rw [show (⟨ρ x, hmem⟩ : zO).1 = ρ (∑ i, c i • bK i) from congrArg ρ hx_eq,
        map_sum, Submodule.coe_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_zsmul]; rfl
    rw [heq]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  let b_zO : Module.Basis (Free.ChooseBasisIndex ℤ (𝓞 K)) ℤ zO :=
    Module.Basis.mk hzO_basis_li hzO_basis_sp
  have h_b_zM_li : LinearIndependent ℝ (fun i => (b_zM i : EuclideanSpace ℝ (InfinitePlace K × PUnit.{1} × Fin 2))) := by
    simpa [b_zM, Module.Basis.coe_mk] using h_ω_li
  have h_b_zO_li : LinearIndependent ℝ (fun i => (b_zO i : EuclideanSpace ℝ (InfinitePlace K × PUnit.{1} × Fin 2))) := by
    simpa [b_zO, Module.Basis.coe_mk] using h_bK_li
  let eIdx := Fintype.equivFin (Free.ChooseBasisIndex ℤ (𝓞 K))
  have : DiscreteTopology zM :=
    discreteTopology_of_fin_basis_real_li (b_zM.reindex eIdx)
      (by
        have h1 : (fun i => ((b_zM.reindex eIdx) i :
              EuclideanSpace ℝ (InfinitePlace K × PUnit.{1} × Fin 2))) =
            (fun i => (b_zM i : EuclideanSpace ℝ (InfinitePlace K × PUnit.{1} × Fin 2))) ∘
              eIdx.symm := by
          funext i
          simp [Module.Basis.reindex_apply]
        rw [h1]
        exact h_b_zM_li.comp eIdx.symm eIdx.symm.injective)
  have : DiscreteTopology zO :=
    discreteTopology_of_fin_basis_real_li (b_zO.reindex eIdx)
      (by
        have h1 : (fun i => ((b_zO.reindex eIdx) i :
              EuclideanSpace ℝ (InfinitePlace K × PUnit.{1} × Fin 2))) =
            (fun i => (b_zO i : EuclideanSpace ℝ (InfinitePlace K × PUnit.{1} × Fin 2))) ∘
              eIdx.symm := by
          funext i
          simp [Module.Basis.reindex_apply]
        rw [h1]
        exact h_b_zO_li.comp eIdx.symm eIdx.symm.injective)
  have hrk_eq : rk zO = rk zM := by
    show Module.finrank ℤ zO = Module.finrank ℤ zM
    rw [Module.finrank_eq_card_basis b_zO, Module.finrank_eq_card_basis b_zM]
  have hcov_idx := covol_eq_index_mul_covol hzO_le hrk_eq
  have hidx_eq : latIndex zM zO = Ideal.absNorm (differentIdeal ℤ (𝓞 K)) := by
    change zO.toAddSubgroup.relIndex zM.toAddSubgroup = _
    have hrel : zO.toAddSubgroup.relIndex zM.toAddSubgroup =
        O_sub.toAddSubgroup.relIndex M.toAddSubgroup :=
      AddSubgroup.relIndex_map_map_of_injective O_sub.toAddSubgroup M.toAddSubgroup h_inj
    rw [hrel, hidx_diff]
  have hG_eq : (fun j => (b_zO j : EuclideanSpace ℝ (InfinitePlace K × PUnit.{1} × Fin 2))) =
      fun j => ∑ k, (G.map (Int.cast : ℤ → ℝ)) k j •
        (b_zM k : EuclideanSpace ℝ (InfinitePlace K × PUnit.{1} × Fin 2)) := by
    funext j
    dsimp only [b_zO, b_zM]
    rw [Module.Basis.coe_mk]
    simp_rw [Module.Basis.coe_mk]
    change ρ (bK j) = ∑ k, ((G k j : ℤ) : ℝ) • ρ (ω' k)
    rw [hbK_exp j, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [h_rat]; simp
  have hdet_eq : (Matrix.gram ℝ (fun j => (b_zO j : EuclideanSpace ℝ (InfinitePlace K × PUnit.{1} × Fin 2)))).det =
      ((G.det : ℤ) : ℝ) ^ 2 *
        (Matrix.gram ℝ (fun k => (b_zM k : EuclideanSpace ℝ (InfinitePlace K × PUnit.{1} × Fin 2)))).det := by
    rw [hG_eq, RHDirect.ArakelovCovolume.gram_sum_smul_eq_transpose_mul, Matrix.det_mul, Matrix.det_mul,
      Matrix.det_transpose, show (G.map (Int.cast : ℤ → ℝ)).det = (G.det : ℝ) from (Int.cast_det G).symm]
    ring
  have hcov_sq : covol zO = |(NumberField.discr K : ℝ)| * covol zM := by
    rw [covol_eq_sqrt_det_gram zO b_zO, covol_eq_sqrt_det_gram zM b_zM, hdet_eq,
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs, hG_det]
  rw [hcov_idx, hidx_eq] at hcov_sq
  have hcov_pos : (0 : ℝ) < covol zM := covol_pos zM
  exact mul_right_cancel₀ hcov_pos.ne' hcov_sq

/-- **Exact Degree & Rank Formula for `dualLatO A ⊓ annO N`** (for saturated `N ≤ A`):
`rk (dualLatO A ⊓ annO N) = rk (quotLat A N)` and
`degHLat (dualLatO A ⊓ annO N) = - degAr (quotLat A N) + discShift K * rk (quotLat A N)`. -/
theorem deg_dualLatO_inf_annO (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (A : Submodule (𝓞 K) V) (hA : A.FG)
    (hsp : Submodule.span K (A : Set V) = ⊤) (N : Submodule (𝓞 K) V)
    (hN : N ≤ A) (hsat : IsSaturated (zRealize b X A) (zRealize b X N)) :
    rk (zRealize b.dualBasis (dualFrame X) (dualLatO (K := K) A ⊓ annO (K := K) N)) =
        rk (quotLat (zRealize b X A) (zRealize b X N)) ∧
      degHLat b.dualBasis (dualFrame X) (dualLatO (K := K) A ⊓ annO (K := K) N) =
        -degAr (quotLat (zRealize b X A) (zRealize b X N)) +
          discShift K * (rk (quotLat (zRealize b X A) (zRealize b X N)) : ℝ) := by
  classical
  have : Module.Finite K V := Module.Finite.of_basis b
  have hX' := dualFrame_frameOK X hX
  let _ := hN
  set L := zRealize b X A
  set S := zRealize b X N
  haveI hLd : DiscreteTopology L := discreteTopology_zRealize_of_fg b X hX A hA
  haveI hQd : DiscreteTopology (quotLat L S) := discreteTopology_quotLat hsat
  haveI hDd : DiscreteTopology (dualLat (quotLat L S)) := discreteTopology_dualLat (quotLat L S)
  set Rp := tdualLatO (K := K) A ⊓ annO (K := K) N
  set R := dualLatO (K := K) A ⊓ annO (K := K) N
  set 𝔡 := differentIdeal ℤ (𝓞 K)
  have h𝔡0 : 𝔡 ≠ ⊥ := differentIdeal_ne_bot
  have hRdR : R = 𝔡 • Rp := dual_inf_ann_eq A N
  have hRfg : R.FG := Submodule.FG.of_le (dualLatO_fg b A hsp) inf_le_left
  have hRpfg : Rp.FG := by
    set m : ℕ := Ideal.absNorm 𝔡
    have hm0 : m ≠ 0 := fun h => h𝔡0 (Ideal.absNorm_eq_zero_iff.1 h)
    have hmK : (m : K) ≠ 0 := Nat.cast_ne_zero.2 hm0
    have hmem : (m : 𝓞 K) ∈ 𝔡 := Ideal.absNorm_mem 𝔡
    let ψ : Module.Dual K V →ₗ[𝓞 K] Module.Dual K V :=
      (((m : K)⁻¹) • (LinearMap.id : Module.Dual K V →ₗ[K] Module.Dual K V)).restrictScalars (𝓞 K)
    refine Submodule.FG.of_le ((dualLatO_fg b A hsp).map ψ) ?_
    intro g hg
    refine ⟨(m : 𝓞 K) • g, ?_, ?_⟩
    · have : (m : 𝓞 K) • g ∈ R := by rw [hRdR]; exact Submodule.smul_mem_smul hmem hg
      exact this.1
    · change ((m : K)⁻¹) • ((m : 𝓞 K) • g) = g
      rw [← algebraMap_smul K (m : 𝓞 K) g, map_natCast, smul_smul, inv_mul_cancel₀ hmK, one_smul]
  have hspR : Submodule.span K (R : Set (Module.Dual K V)) =
      Submodule.span K (Rp : Set (Module.Dual K V)) := by
    rw [hRdR]; exact twist_span_smul Rp 𝔡 h𝔡0
  have hrkR : rkK (K := K) R = rkK (K := K) Rp := by unfold rkK; rw [hspR]
  have hrkZ_R : rk (zRealize b.dualBasis (dualFrame X) R) = Module.finrank ℚ K * rkK (K := K) R :=
    rk_zRealize_eq b.dualBasis (dualFrame X) hX' R hRfg
  have hrkZ_Rp : rk (zRealize b.dualBasis (dualFrame X) Rp) = Module.finrank ℚ K * rkK (K := K) Rp :=
    rk_zRealize_eq b.dualBasis (dualFrame X) hX' Rp hRpfg
  have hrkZ_eq : rk (zRealize b.dualBasis (dualFrame X) R) =
      rk (zRealize b.dualBasis (dualFrame X) Rp) := by
    rw [hrkZ_R, hrkZ_Rp, hrkR]
  have hann := RHDirect.Stage4ArakelovBost.annLat_eq_dualLat_quotLat hsat
  have hE1 : dualLat L ⊓ ((Submodule.span ℝ ((S : Submodule ℤ _) : Set _))ᗮ).restrictScalars ℤ =
      dualLat (quotLat L S) := hann.2
  have hE2 := dualZ_zRealize_eq b X hX A hA hsp N
  let φ2 : EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2) →ₗ[ℝ] _ := (2 : ℝ) • cE K ι
  let φh : EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2) →ₗ[ℝ] _ := ((1 : ℝ) / 2) • cE K ι
  have hcomp : φh.restrictScalars ℤ ∘ₗ φ2.restrictScalars ℤ = LinearMap.id := by
    ext w
    simp only [φh, φ2, LinearMap.coe_comp, Function.comp_apply, LinearMap.restrictScalars_apply,
      LinearMap.smul_apply, map_smul, cE_cE, smul_smul, LinearMap.id_apply]
    norm_num
  have hM' : zRealize b.dualBasis (dualFrame X) Rp =
      (dualLat (quotLat L S)).map (φh.restrictScalars ℤ) := by
    rw [← hE1, hE2, ← Submodule.map_comp, hcomp, Submodule.map_id]
  have hφhi : ∀ x y, inner ℝ (φh x) (φh y) = ((1 : ℝ) / 2) ^ 2 * inner ℝ x y := fun x y => by
    simp only [φh, LinearMap.smul_apply, real_inner_smul_left, real_inner_smul_right, inner_cE]
    ring
  obtain ⟨hM'd, hrkM', hcovM'⟩ :=
    covol_map_scaled φh ((1 : ℝ) / 2) (by norm_num) hφhi (dualLat (quotLat L S))
  rw [← hM'] at hM'd hrkM' hcovM'
  haveI := hM'd
  have hRRp : R ≤ Rp := by rw [hRdR]; exact Submodule.smul_le_right
  have hzlle : zRealize b.dualBasis (dualFrame X) R ≤ zRealize b.dualBasis (dualFrame X) Rp :=
    zRealize_mono _ _ hRRp
  haveI : DiscreteTopology (zRealize b.dualBasis (dualFrame X) R) :=
    discreteTopology_zRealize_of_fg b.dualBasis (dualFrame X) hX' R hRfg
  have hcov := covol_eq_index_mul_covol hzlle hrkZ_eq
  have hidx : latIndex (zRealize b.dualBasis (dualFrame X) Rp)
      (zRealize b.dualBasis (dualFrame X) R) =
      R.toAddSubgroup.relIndex Rp.toAddSubgroup := by
    change ((zRealize b.dualBasis (dualFrame X) R).toAddSubgroup.relIndex
      (zRealize b.dualBasis (dualFrame X) Rp).toAddSubgroup) = _
    exact AddSubgroup.relIndex_map_map_of_injective R.toAddSubgroup Rp.toAddSubgroup
      (realizeHLat_injective b.dualBasis (dualFrame X) hX')
  have htw : R.toAddSubgroup.relIndex Rp.toAddSubgroup = Ideal.absNorm 𝔡 ^ rkK (K := K) Rp := by
    rw [hRdR]; exact twist_index Rp hRpfg 𝔡 h𝔡0
  have hnorm : (Ideal.absNorm 𝔡 : ℝ) = |(NumberField.discr K : ℝ)| :=
    absNorm_differentIdeal_eq_discr K
  have hrk_final : rk (zRealize b.dualBasis (dualFrame X) R) = rk (quotLat L S) := by
    rw [hrkZ_eq, hrkM', rk_dualLat]
  refine ⟨hrk_final, ?_⟩
  rw [covol_dualLat] at hcovM'
  rw [hidx, htw, hcovM', Nat.cast_pow, hnorm, rk_dualLat] at hcov
  have hcovQ_pos : 0 < covol (quotLat L S) := covol_pos (quotLat L S)
  have hcovR_pos : 0 < covol (zRealize b.dualBasis (dualFrame X) R) :=
    covol_pos (zRealize b.dualBasis (dualFrame X) R)
  have hdisc_pos : 0 < |(NumberField.discr K : ℝ)| :=
    abs_pos.mpr (Int.cast_ne_zero.mpr (NumberField.discr_ne_zero K))
  have hrkQ_eq : rk (quotLat L S) = Module.finrank ℚ K * rkK (K := K) Rp := by
    rw [← hrk_final, hrkZ_R, hrkR]
  unfold degHLat degAr discShift logDiscDivDeg
  rw [hcov]
  have hhalf_pos : (0 : ℝ) < (1 / 2 : ℝ) ^ rk (quotLat L S) := by positivity
  rw [Real.log_mul (pow_pos hdisc_pos _).ne'
    (mul_pos hhalf_pos (inv_pos.mpr hcovQ_pos)).ne',
    Real.log_mul hhalf_pos.ne' (inv_pos.mpr hcovQ_pos).ne',
    Real.log_pow, Real.log_pow, Real.log_inv,
    show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.log_inv]
  have hn_ne : (Module.finrank ℚ K : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
  have hrkQ_R : (rk (quotLat L S) : ℝ) = (Module.finrank ℚ K : ℝ) * (rkK (K := K) Rp : ℝ) := by
    exact_mod_cast hrkQ_eq
  rw [hrkQ_R]
  field_simp [hn_ne]
  ring

/-- **Exact `HLat` Slope Duality (`hlat_duality_slope_neg`)**:
for any good `HLat K` over a totally complex number field `K` (`0 < A.rank`):
- `(dualHLat A).mu = - A.mu`
- `(dualHLat A).muMax = - A.muMin`
- `(dualHLat A).muMin = - A.muMax` -/
theorem hlat_duality_slope_neg {K : Type} [Field K] [NumberField K] [IsTotallyComplex K]
    [StarRing K] (A : HLat K) (hG : A.Good) (hr : 0 < A.rank) :
    (dualHLat A).mu = -A.mu ∧
      (dualHLat A).muMax = -A.muMin ∧
      (dualHLat A).muMin = -A.muMax := by
  classical
  have : Module.Finite K A.V := Module.Finite.of_basis A.b
  have hX' := dualFrame_frameOK A.X hG.1
  have hA_ne : A.L ≠ ⊥ := by
    intro h0
    have h1 : A.rank = 0 := by unfold HLat.rank rkK; rw [h0]; simp
    omega
  have hD_fg : (dualLatO (K := K) A.L).FG := dualLatO_fg A.b A.L hG.2.2
  have hD_sp : Submodule.span K ((dualLatO (K := K) A.L : Submodule (𝓞 K) (Module.Dual K A.V)) :
      Set (Module.Dual K A.V)) = ⊤ := dualLatO_span_top A.b A.L hG.2.1
  have hD_good : (dualHLat A).Good := ⟨hX', hD_fg, hD_sp⟩
  have hD_ne : (dualHLat A).L ≠ ⊥ := by
    intro h0
    have hsp := hD_sp
    have h0' : dualLatO (K := K) A.L = ⊥ := h0
    rw [h0', Submodule.bot_coe, Submodule.span_zero_singleton] at hsp
    have h0'' : Module.finrank K (Module.Dual K A.V) = 0 := by
      rw [← finrank_top K (Module.Dual K A.V), ← hsp, finrank_bot]
    rw [Subspace.dual_finrank_eq] at h0''
    have hle : A.rank ≤ Module.finrank K A.V := Submodule.finrank_le _
    omega
  -- 1. `mu (dualHLat A) = - mu A` via `N = ⊥`.
  have hmu_dual : (dualHLat A).mu = -A.mu := by
    have hsat0 : IsSaturated A.zRealize (zRealize A.b A.X (⊥ : Submodule (𝓞 K) A.V)) := by
      rw [zRealize_bot]
      exact RHDirect.Stage4ArakelovBost.isSaturated_bot A.zRealize
    have ⟨hrk0, hdeg0⟩ := deg_dualLatO_inf_annO A.b A.X hG.1 A.L hG.2.1 hG.2.2 ⊥ bot_le hsat0
    have hann0 : annO (K := K) (⊥ : Submodule (𝓞 K) A.V) = ⊤ := by
      ext f; simp [annO]
    have hq0 : quotLat A.zRealize (zRealize A.b A.X (⊥ : Submodule (𝓞 K) A.V)) = A.zRealize := by
      rw [zRealize_bot]
      exact RHDirect.Stage4ArakelovBost.quotLat_bot A.zRealize
    rw [hann0, inf_top_eq, hq0] at hrk0 hdeg0
    have hA_Zne : A.zRealize ≠ ⊥ := zRealize_ne_bot A.b A.X hG.1 hA_ne
    haveI : DiscreteTopology A.zRealize := discreteTopology_zRealize_of_fg A.b A.X hG.1 A.L hG.2.1
    have hrk_pos : (0 : ℝ) < (rk A.zRealize : ℝ) :=
      Nat.cast_pos.mpr (rk_pos_of_ne_bot A.zRealize hA_Zne)
    have hslope : slopeHLat A.b.dualBasis (dualFrame A.X) (dualLatO (K := K) A.L) =
        -slopeHLat A.b A.X A.L + discShift K := by
      unfold slopeHLat ArakelovCovolume.slope
      change degHLat A.b.dualBasis (dualFrame A.X) (dualLatO (K := K) A.L) /
          (rk (zRealize A.b.dualBasis (dualFrame A.X) (dualLatO (K := K) A.L)) : ℝ) = _
      rw [hrk0, hdeg0]
      change (-degHLat A.b A.X A.L + discShift K * (rk A.zRealize : ℝ)) /
          (rk A.zRealize : ℝ) = - (degHLat A.b A.X A.L / (rk A.zRealize : ℝ)) + discShift K
      field_simp [hrk_pos.ne']
    show muDef A.b.dualBasis (dualFrame A.X) (dualLatO (K := K) A.L) = -muDef A.b A.X A.L
    unfold muDef
    rw [hslope]
    unfold discShift
    ring
  -- 2. `muMax (dualHLat A) = - muMin A` via `annO` + `dualCoannihilator`.
  have hmuMax_eq : ∀ (B : HLat K), B.Good → B.L ≠ ⊥ →
      (dualHLat B).muMax = -B.muMin := by
    intro B hBG hBne
    have : Module.Finite K B.V := Module.Finite.of_basis B.b
    have hBX' := dualFrame_frameOK B.X hBG.1
    have hBD_fg : (dualLatO (K := K) B.L).FG := dualLatO_fg B.b B.L hBG.2.2
    have hBD_ne : (dualHLat B).L ≠ ⊥ := by
      intro h0
      have hsp := dualLatO_span_top B.b B.L hBG.2.1
      have h0' : dualLatO (K := K) B.L = ⊥ := h0
      rw [h0', Submodule.bot_coe, Submodule.span_zero_singleton] at hsp
      have h0'' : Module.finrank K (Module.Dual K B.V) = 0 := by
        rw [← finrank_top K (Module.Dual K B.V), ← hsp, finrank_bot]
      rw [Subspace.dual_finrank_eq] at h0''
      obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hBne
      haveI : Nontrivial B.V := ⟨⟨x, 0, hx0⟩⟩
      exact absurd h0'' Module.finrank_pos.ne'
    haveI : DiscreteTopology B.zRealize := discreteTopology_zRealize_of_fg B.b B.X hBG.1 B.L hBG.2.1
    have hle1 : muMaxO B.b.dualBasis (dualFrame B.X) (dualLatO (K := K) B.L) ≤
        discShift K - muMinO B.b B.X B.L := by
      rw [muMaxO_char B.b.dualBasis (dualFrame B.X) hBX' (dualLatO (K := K) B.L) hBD_fg hBD_ne]
      intro R hRL
      by_cases hR0 : R = ⊥
      · subst hR0
        unfold degHLat
        rw [zRealize_bot, degAr_bot]
        have hrk0 : rk (⊥ : Submodule ℤ (EuclideanSpace ℝ (InfinitePlace K × B.ι × Fin 2))) = 0 := by
          simp [rk]
        rw [hrk0]
        simp
      · let W : Submodule K B.V := {
          carrier := {x : B.V | ∀ f ∈ Submodule.span K (R : Set (Module.Dual K B.V)), f x = 0}
          zero_mem' := fun f _ => map_zero f
          add_mem' := fun hx hy f hf => by rw [map_add, hx f hf, hy f hf, add_zero]
          smul_mem' := fun c x hx f hf => by rw [map_smul, hx f hf, smul_zero] }
        let N : Submodule (𝓞 K) B.V := B.L ⊓ W.restrictScalars (𝓞 K)
        have hNL : N ≤ B.L := inf_le_left
        have hW_sp : Submodule.span K (N : Set B.V) = W := by
          apply le_antisymm
          · exact Submodule.span_le.mpr fun _ hx => hx.2
          · intro w hw
            have hw' : w ∈ Submodule.span K (B.L : Set B.V) := hBG.2.2 ▸ trivial
            obtain ⟨c, hcL, hc_sum⟩ := Submodule.mem_span_set.mp hw'
            obtain ⟨D, hD_pos, hD⟩ :=
              exists_pos_nat_mul_mem_ringOfIntegers_fin (fun x : c.support => c x)
            choose a ha using hD
            have hDw_L : (D : K) • w ∈ B.L := by
              rw [← hc_sum, Finsupp.sum, Finset.smul_sum]
              refine Submodule.sum_mem B.L fun y hy => ?_
              rw [smul_smul, ha ⟨y, hy⟩, algebraMap_smul K (a ⟨y, hy⟩) y]
              exact B.L.smul_mem _ (hcL hy)
            have hDw_W : (D : K) • w ∈ W := W.smul_mem _ hw
            have hDw_N : (D : K) • w ∈ N := ⟨hDw_L, hDw_W⟩
            have hw_inv : w = (D : K)⁻¹ • ((D : K) • w) := by
              rw [smul_smul, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hD_pos.ne'), one_smul]
            rw [hw_inv]
            exact Submodule.smul_mem _ _ (Submodule.subset_span hDw_N)
        have hN_satO : satO (K := K) B.L N = N := by
          apply le_antisymm _ (le_satO hNL)
          intro x hx
          exact ⟨hx.1, by rw [← hW_sp]; exact hx.2⟩
        have hsatN : IsSaturated B.zRealize (zRealize B.b B.X N) := by
          have := saturation_zRealize_eq B.b B.X hBG.1 hNL
          rw [hN_satO] at this
          rw [← this]
          exact RHDirect.Stage4ArakelovBost.isSaturated_saturation (zRealize_mono B.b B.X hNL)
        let R' := dualLatO (K := K) B.L ⊓ annO (K := K) N
        have hRR' : R ≤ R' := by
          intro f hfR
          refine ⟨hRL hfR, fun x hxN => ?_⟩
          have hf_sp : f ∈ Submodule.span K (R : Set (Module.Dual K B.V)) := Submodule.subset_span hfR
          exact hxN.2 f hf_sp
        have hR'fg : R'.FG := Submodule.FG.of_le hBD_fg inf_le_left
        have hRfg : R.FG := Submodule.FG.of_le hR'fg hRR'
        have ⟨hrkR', hdegR'⟩ := deg_dualLatO_inf_annO B.b B.X hBG.1 B.L hBG.2.1 hBG.2.2 N hNL hsatN
        have hrk_add := rk_add_quotLat hsatN
        have hdeg_add := degAr_eq_add_quotLat hsatN
        have hrkK_R_le : rkK (K := K) R ≤ rkK (K := K) R' :=
          Submodule.finrank_mono (Submodule.span_mono hRR')
        have hrkK_R'_le : rkK (K := K) R' ≤ rkK (K := K) R := by
          have h1 : rk (zRealize B.b.dualBasis (dualFrame B.X) R') =
              rk (quotLat B.zRealize (zRealize B.b B.X N)) := hrkR'
          have h2 : rk B.zRealize = Module.finrank ℚ K * Module.finrank K B.V := by
            rw [rk_zRealize_eq B.b B.X hBG.1 B.L hBG.2.1]
            unfold rkK; rw [hBG.2.2, finrank_top]
          have h3 : rk (zRealize B.b B.X N) = Module.finrank ℚ K * Module.finrank K W := by
            rw [rk_zRealize_eq B.b B.X hBG.1 N (Submodule.FG.of_le hBG.2.1 hNL)]
            unfold rkK; rw [hW_sp]
          have h4 : rk (zRealize B.b.dualBasis (dualFrame B.X) R') =
              Module.finrank ℚ K * rkK (K := K) R' :=
            rk_zRealize_eq B.b.dualBasis (dualFrame B.X) hBX' R' hR'fg
          have hW_eq : W = (Submodule.span K (R : Set (Module.Dual K B.V))).dualCoannihilator := by
            ext x
            change (∀ f ∈ Submodule.span K (R : Set (Module.Dual K B.V)), f x = 0) ↔ _
            rw [Submodule.mem_dualCoannihilator]
          have h5 : Module.finrank K (Submodule.span K (R : Set (Module.Dual K B.V))) +
              Module.finrank K W = Module.finrank K B.V := by
            rw [hW_eq]
            exact Subspace.finrank_add_finrank_dualCoannihilator_eq
              (Submodule.span K (R : Set (Module.Dual K B.V)))
          have hn0 : 0 < Module.finrank ℚ K := Module.finrank_pos
          have hq_rk : rk (quotLat B.zRealize (zRealize B.b B.X N)) =
              Module.finrank ℚ K * rkK (K := K) R := by
            have hsub1 : rk (quotLat B.zRealize (zRealize B.b B.X N)) =
                rk B.zRealize - rk (zRealize B.b B.X N) := by omega
            have hle_W : Module.finrank K W ≤ Module.finrank K B.V := by omega
            have hsub2 : Module.finrank K B.V - Module.finrank K W =
                Module.finrank K (Submodule.span K (R : Set (Module.Dual K B.V))) := by omega
            rw [hsub1, h2, h3, ← Nat.mul_sub_left_distrib, hsub2]
            rfl
          have hmul : Module.finrank ℚ K * rkK (K := K) R' =
              Module.finrank ℚ K * rkK (K := K) R := by
            rw [← h4, h1, hq_rk]
          exact le_of_eq (Nat.eq_of_mul_eq_mul_left hn0 hmul)
        have hrk_eq : rk (zRealize B.b.dualBasis (dualFrame B.X) R) =
            rk (zRealize B.b.dualBasis (dualFrame B.X) R') := by
          rw [rk_zRealize_eq _ _ hBX' R hRfg, rk_zRealize_eq _ _ hBX' R' hR'fg,
            le_antisymm hrkK_R_le hrkK_R'_le]
        have hdeg_le : degHLat B.b.dualBasis (dualFrame B.X) R ≤
            degHLat B.b.dualBasis (dualFrame B.X) R' := by
          haveI : DiscreteTopology (zRealize B.b.dualBasis (dualFrame B.X) R') :=
            discreteTopology_zRealize_of_fg _ _ hBX' R' hR'fg
          exact (covol_le_of_le_same_rank (zRealize_mono _ _ hRR') hrk_eq).2
        have hmin := (muMinO_char B.b B.X hBG.1 B.L hBG.2.1 hBne
          (muMinO B.b B.X B.L)).mp le_rfl N hNL
        have hrk_sub : (rk (quotLat B.zRealize (zRealize B.b B.X N)) : ℝ) =
            (rk (zRealize B.b B.X B.L) : ℝ) - (rk (zRealize B.b B.X N) : ℝ) := by
          have : rk (quotLat B.zRealize (zRealize B.b B.X N)) + rk (zRealize B.b B.X N) =
              rk B.zRealize := by omega
          exact eq_sub_of_add_eq (by exact_mod_cast this)
        change degAr (zRealize B.b B.X B.L) =
          degAr (zRealize B.b B.X N) + degAr (quotLat B.zRealize (zRealize B.b B.X N)) at hdeg_add
        rw [hrk_sub] at hdegR'
        unfold degHLat at hdegR' hmin hdeg_le ⊢
        rw [hrk_eq, hrkR', hrk_sub]
        linarith
    have hle2 : discShift K - muMinO B.b B.X B.L ≤
        muMaxO B.b.dualBasis (dualFrame B.X) (dualLatO (K := K) B.L) := by
      have hmin_le : discShift K - muMaxO B.b.dualBasis (dualFrame B.X) (dualLatO (K := K) B.L) ≤
          muMinO B.b B.X B.L := by
        rw [muMinO_char B.b B.X hBG.1 B.L hBG.2.1 hBne]
        intro N hNL
        let N' := satO (K := K) B.L N
        have hN'L : N' ≤ B.L := satO_le B.L N
        have hsat : IsSaturated B.zRealize (zRealize B.b B.X N') := by
          rw [← saturation_zRealize_eq B.b B.X hBG.1 hNL]
          exact RHDirect.Stage4ArakelovBost.isSaturated_saturation (zRealize_mono B.b B.X hNL)
        have hrk_eq : rk (zRealize B.b B.X N') = rk (zRealize B.b B.X N) := by
          have : zRealize B.b B.X N' = saturation B.zRealize (zRealize B.b B.X N) :=
            (saturation_zRealize_eq B.b B.X hBG.1 hNL).symm
          rw [this]
          exact RHDirect.Stage4ArakelovBost.rk_saturation (zRealize_mono B.b B.X hNL)
        have hdeg_le : degHLat B.b B.X N ≤ degHLat B.b B.X N' := by
          have h1 := RHDirect.Stage4ArakelovBost.covol_saturation_le (zRealize_mono B.b B.X hNL)
          rw [saturation_zRealize_eq B.b B.X hBG.1 hNL] at h1
          exact h1.2
        let R' := dualLatO (K := K) B.L ⊓ annO (K := K) N'
        have ⟨hrkR', hdegR'⟩ := deg_dualLatO_inf_annO B.b B.X hBG.1 B.L hBG.2.1 hBG.2.2 N' hN'L hsat
        have hmax := (muMaxO_char B.b.dualBasis (dualFrame B.X) hBX' (dualLatO (K := K) B.L)
          hBD_fg hBD_ne (muMaxO B.b.dualBasis (dualFrame B.X) (dualLatO (K := K) B.L))).mp
          le_rfl R' inf_le_left
        have hrk_add := rk_add_quotLat hsat
        have hdeg_add := degAr_eq_add_quotLat hsat
        have hrk_sub : (rk (quotLat B.zRealize (zRealize B.b B.X N')) : ℝ) =
            (rk (zRealize B.b B.X B.L) : ℝ) - (rk (zRealize B.b B.X N) : ℝ) := by
          rw [← hrk_eq]
          have : rk (quotLat B.zRealize (zRealize B.b B.X N')) + rk (zRealize B.b B.X N') =
              rk B.zRealize := by omega
          exact eq_sub_of_add_eq (by exact_mod_cast this)
        change degAr (zRealize B.b B.X B.L) =
          degAr (zRealize B.b B.X N') + degAr (quotLat B.zRealize (zRealize B.b B.X N')) at hdeg_add
        change rk (zRealize B.b.dualBasis (dualFrame B.X) R') = _ at hrkR'
        change degHLat B.b.dualBasis (dualFrame B.X) R' = _ at hdegR'
        rw [hrkR'] at hmax
        rw [hrk_sub] at hmax hdegR'
        unfold degHLat at hdegR' hmax hdeg_le ⊢
        linarith
      linarith
    have heq : muMaxO B.b.dualBasis (dualFrame B.X) (dualLatO (K := K) B.L) =
        discShift K - muMinO B.b B.X B.L := le_antisymm hle1 hle2
    show muMaxDef B.b.dualBasis (dualFrame B.X) (dualLatO (K := K) B.L) =
      -muMinDef B.b B.X B.L
    unfold muMaxDef muMinDef
    rw [heq]
    unfold discShift
    ring
  -- 3. `muMin (dualHLat A) = - muMax A` by applying (2) to `dualHLat A` + double-dual isometry.
  have hmuMin_dual : (dualHLat A).muMin = -A.muMax := by
    have h2 := hmuMax_eq (dualHLat A) hD_good hD_ne
    haveI : DiscreteTopology A.zRealize := discreteTopology_zRealize_of_fg A.b A.X hG.1 A.L hG.2.1
    have hcoord : ∀ (y : A.V) (i : A.ι), A.b.dualBasis i y = A.b.repr y i := by
      intro y i
      conv_lhs => rw [← A.b.sum_repr y]
      simp only [map_sum, map_smul, smul_eq_mul, A.b.dualBasis_apply_self, mul_ite, mul_one,
        mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    let ev : A.V ≃ₗ[K] Module.Dual K (Module.Dual K A.V) :=
      { toFun := Module.Dual.eval K A.V
        invFun := fun Φ => ∑ i, Φ (A.b.dualBasis i) • A.b i
        map_add' := (Module.Dual.eval K A.V).map_add
        map_smul' := (Module.Dual.eval K A.V).map_smul
        left_inv := fun x => by
          conv_rhs => rw [← A.b.sum_repr x]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Module.Dual.eval_apply, hcoord x i]
        right_inv := fun Φ => by
          apply A.b.dualBasis.ext
          intro j
          change (A.b.dualBasis j) (∑ i, Φ (A.b.dualBasis i) • A.b i) = Φ (A.b.dualBasis j)
          rw [map_sum]
          simp [Finsupp.single_apply] }
    let b2 := A.b.dualBasis.dualBasis
    let X2 := dualFrame (dualFrame A.X)
    let L2 := dualLatO (K := K) (dualLatO (K := K) A.L)
    have hev_norm : ∀ x : A.V, realizeHLat b2 X2 (ev x) = realizeHLat A.b A.X x := by
      intro x
      ext p
      have hfc : fcoord b2 X2 p.1 (ev x) p.2.1 = fcoord A.b A.X p.1 x p.2.1 := by
        unfold fcoord RHDirect.Stage12SchurWeylLattices.fcoord
        have hX2 : X2 p.1 = A.X p.1 := congrFun (dualFrame_dualFrame A.X hG.1) p.1
        have hvec : RHDirect.Stage12SchurWeylLattices.vecAt b2 p.1 (ev x) =
            RHDirect.Stage12SchurWeylLattices.vecAt A.b p.1 x := by
          funext i
          simp only [RHDirect.Stage12SchurWeylLattices.vecAt]
          congr 1
          rw [show (b2.repr (ev x)) i = (ev x) (A.b.dualBasis i) from
            Module.Basis.dualBasis_repr A.b.dualBasis (ev x) i]
          exact hcoord x i
        rw [hX2, hvec]
      change (if p.2.2 = 0 then (fcoord b2 X2 p.1 (ev x) p.2.1).re
        else (fcoord b2 X2 p.1 (ev x) p.2.1).im) =
        (if p.2.2 = 0 then (fcoord A.b A.X p.1 x p.2.1).re
        else (fcoord A.b A.X p.1 x p.2.1).im)
      rw [hfc]
    let evO : A.V →ₗ[𝓞 K] Module.Dual K (Module.Dual K A.V) :=
      ev.toLinearMap.restrictScalars (𝓞 K)
    have hev_L : A.L.map evO = L2 := by
      apply le_antisymm
      · rintro _ ⟨x, hxA, rfl⟩ f hfD
        exact hfD x hxA
      · intro φ hφ
        refine ⟨ev.symm φ, ?_, ev.apply_symm_apply φ⟩
        have hφ' : ∀ f ∈ dualLatO (K := K) A.L, f (ev.symm φ) ∈ Set.range (algebraMap (𝓞 K) K) :=
          fun f hf => by
            have h1 : φ f ∈ Set.range (algebraMap (𝓞 K) K) := hφ f hf
            have hev_back : φ f = f (ev.symm φ) := by
              conv_lhs => rw [← ev.apply_symm_apply φ]
              rfl
            rwa [← hev_back]
        have hdd : realizeHLat A.b A.X (ev.symm φ) ∈ A.zRealize := by
          rw [← dualLat_dualLat A.zRealize]
          refine ⟨?_, ?_⟩
          · rw [span_real_dualLat, span_zRealize_top A.b A.X hG.1 A.L hG.2.1 hG.2.2]; trivial
          · intro w hw
            have hw_inf : w ∈ dualLat A.zRealize ⊓
                ((Submodule.span ℝ ((zRealize A.b A.X (⊥ : Submodule (𝓞 K) A.V) : Submodule ℤ _) :
                  Set _))ᗮ).restrictScalars ℤ := by
              refine ⟨hw, ?_⟩
              rw [zRealize_bot, Submodule.bot_coe, Submodule.span_zero_singleton]
              simp
            rw [dualZ_zRealize_eq A.b A.X hG.1 A.L hG.2.1 hG.2.2 ⊥] at hw_inf
            rcases hw_inf with ⟨_, ⟨f, ⟨hfA, _⟩, rfl⟩, rfl⟩
            have h1 : (1 : K) ∈ ((differentIdeal ℤ (𝓞 K) : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) *
                FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) :
                  FractionalIdeal (nonZeroDivisors (𝓞 K)) K) := by
              rw [misc_diff_mul]
              exact (FractionalIdeal.mem_one_iff _).2 ⟨1, by simp⟩
            have htrZ : ∃ z : ℤ, Algebra.trace ℚ K (f (ev.symm φ)) = z := by
              have key : ∀ t ∈ ((differentIdeal ℤ (𝓞 K) : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) *
                  FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) :
                    FractionalIdeal (nonZeroDivisors (𝓞 K)) K),
                  ∃ z : ℤ, Algebra.trace ℚ K (t * f (ev.symm φ)) = z := by
                intro t ht
                rw [← FractionalIdeal.mem_coe, FractionalIdeal.coe_mul] at ht
                refine Submodule.mul_induction_on ht ?_ ?_
                · intro r hr η hη
                  obtain ⟨r₀, hr₀, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hr
                  have hr₀f : r₀ • f ∈ dualLatO (K := K) A.L := by
                    have hmem : r₀ • f ∈ differentIdeal ℤ (𝓞 K) • (tdualLatO (K := K) A.L ⊓ annO (K := K) ⊥) :=
                      Submodule.smul_mem_smul hr₀ ⟨hfA, fun _ hx => by subst hx; exact map_zero f⟩
                    rw [← dual_inf_ann_eq A.L ⊥] at hmem
                    exact hmem.1
                  obtain ⟨s, hs⟩ := hφ' (r₀ • f) hr₀f
                  obtain ⟨z, hz⟩ := (misc_mem_dual_one η).1 hη s
                  refine ⟨z, ?_⟩
                  have heq : (algebraMap (𝓞 K) K r₀ * η) * f (ev.symm φ) = η * (s : K) := by
                    have hs' : (algebraMap (𝓞 K) K) s = (algebraMap (𝓞 K) K r₀) * f (ev.symm φ) := by
                      rw [hs, ← algebraMap_smul K r₀ f, LinearMap.smul_apply, smul_eq_mul]
                    rw [show (s : K) = algebraMap (𝓞 K) K s from rfl, hs']
                    ring
                  rw [heq]; exact hz
                · rintro t₁ t₂ ⟨z₁, hz₁⟩ ⟨z₂, hz₂⟩
                  exact ⟨z₁ + z₂, by rw [add_mul, map_add, hz₁, hz₂, Int.cast_add]⟩
              simpa using key 1 h1
            obtain ⟨z, hz⟩ := htrZ
            refine ⟨z, ?_⟩
            have hinner := inner_realizeHLat_cE A.b A.X hG.1 (ev.symm φ) f
            change inner ℝ (realizeHLat A.b A.X (ev.symm φ))
              ((2 : ℝ) • cE K A.ι (realizeHLat A.b.dualBasis (dualFrame A.X) f)) = (z : ℝ)
            rw [hinner, hz]
            simp
        rcases hdd with ⟨x, hxA, hxeq⟩
        rwa [← realizeHLat_injective A.b A.X hG.1 hxeq]
    have hslopes_eq : slopesO b2 X2 L2 = slopesO A.b A.X A.L := by
      have hdeg_ev : ∀ N : Submodule (𝓞 K) A.V, N.FG →
          rk (zRealize b2 X2 (N.map evO)) = rk (zRealize A.b A.X N) ∧
          degHLat b2 X2 (N.map evO) = degHLat A.b A.X N := by
        intro N hN
        have heq_Z : zRealize b2 X2 (N.map evO) = zRealize A.b A.X N := by
          ext w
          change (∃ y ∈ N.map evO, realizeHLat b2 X2 y = w) ↔
            (∃ x ∈ N, realizeHLat A.b A.X x = w)
          constructor
          · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
            exact ⟨x, hx, (hev_norm x).symm⟩
          · rintro ⟨x, hx, rfl⟩
            exact ⟨evO x, ⟨x, hx, rfl⟩, hev_norm x⟩
        unfold degHLat
        rw [heq_Z]
        exact ⟨rfl, rfl⟩
      ext t
      constructor
      · rintro ⟨M, hML, hM0, rfl⟩
        let N := M.comap evO
        have hNM : N.map evO = M := by
          ext y
          simp only [Submodule.mem_map, Submodule.mem_comap, evO,
            LinearMap.restrictScalars_apply, LinearEquiv.coe_toLinearMap, N]
          exact ⟨fun ⟨x, hx, hxy⟩ => hxy ▸ hx, fun hy => ⟨ev.symm y,
            by simpa only [ev.apply_symm_apply] using hy, ev.apply_symm_apply y⟩⟩
        have hNL : N ≤ A.L := by
          intro x hx
          have hmem : evO x ∈ L2 := hML hx
          rw [← hev_L] at hmem
          rcases hmem with ⟨y, hyA, hyx⟩
          rwa [← ev.injective hyx]
        have hN0 : N ≠ ⊥ := by
          intro h0
          apply hM0
          rw [← hNM, h0, Submodule.map_bot]
        refine ⟨N, hNL, hN0, ?_⟩
        have hNfg : N.FG := Submodule.FG.of_le hG.2.1 hNL
        have ⟨hrk, hdeg⟩ := hdeg_ev N hNfg
        rw [hNM] at hrk hdeg
        show slopeHLat A.b A.X N = slopeHLat b2 X2 M
        unfold slopeHLat ArakelovCovolume.slope
        change degHLat A.b A.X N / (rk (zRealize A.b A.X N) : ℝ) =
          degHLat b2 X2 M / (rk (zRealize b2 X2 M) : ℝ)
        rw [hrk, hdeg]
      · rintro ⟨N, hNL, hN0, rfl⟩
        let M := N.map evO
        have hML : M ≤ L2 := by
          rw [← hev_L]
          exact Submodule.map_mono hNL
        have hM0 : M ≠ ⊥ := by
          intro h0
          apply hN0
          rw [eq_bot_iff]
          intro x hxN
          have hmem : evO x ∈ M := ⟨x, hxN, rfl⟩
          rw [h0, Submodule.mem_bot] at hmem
          exact ev.injective (hmem.trans (map_zero ev).symm)
        refine ⟨M, hML, hM0, ?_⟩
        have hNfg : N.FG := Submodule.FG.of_le hG.2.1 hNL
        have ⟨hrk, hdeg⟩ := hdeg_ev N hNfg
        show slopeHLat b2 X2 M = slopeHLat A.b A.X N
        unfold slopeHLat ArakelovCovolume.slope
        change degHLat b2 X2 M / (rk (zRealize b2 X2 M) : ℝ) =
          degHLat A.b A.X N / (rk (zRealize A.b A.X N) : ℝ)
        rw [hrk, hdeg]
    have hmuMax_dd : (dualHLat (dualHLat A)).muMax = A.muMax := by
      show muMaxDef b2 X2 L2 = muMaxDef A.b A.X A.L
      unfold muMaxDef muMaxO
      rw [hslopes_eq]
    linarith
  exact ⟨hmu_dual, hmuMax_eq A hG hA_ne, hmuMin_dual⟩

end DualProofs

end Duality

/-! ## Section 5: Orthogonal Direct Sums (`hlat_orthog_direct_sum` & `directSumHLat`) -/

section OrthogonalDirectSum

section TwoTermOrthogonal

variable {K V ι : Type*} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι]

private lemma pos_nat_smul_mem_of_mem_span_K (M : Submodule (𝓞 K) V) {x : V}
    (hx : x ∈ Submodule.span K (M : Set V)) :
    ∃ D : ℕ, 0 < D ∧ (D : K) • x ∈ M := by
  rw [Submodule.mem_span_set] at hx
  obtain ⟨c, hcM, hc_sum⟩ := hx
  obtain ⟨D, hD_pos, hD⟩ := exists_pos_nat_mul_mem_ringOfIntegers_fin (fun y : c.support => c y)
  choose a' ha' using hD
  refine ⟨D, hD_pos, ?_⟩
  rw [← hc_sum, Finsupp.sum, Finset.smul_sum]
  refine Submodule.sum_mem M fun y hy => ?_
  rw [smul_smul, ha' ⟨y, hy⟩, algebraMap_smul K (a' ⟨y, hy⟩) y]
  exact M.smul_mem _ (hcM hy)

private lemma mem_real_span_zRealize_of_mem_span_K (b : Module.Basis ι K V)
    (X : InfinitePlace K → Matrix ι ι ℂ) (M : Submodule (𝓞 K) V) {x : V}
    (hx : x ∈ Submodule.span K (M : Set V)) :
    realizeHLat b X x ∈ Submodule.span ℝ ((zRealize b X M : Submodule ℤ _) : Set _) := by
  obtain ⟨D, hD_pos, hDx⟩ := pos_nat_smul_mem_of_mem_span_K M hx
  have h1 : (D : ℝ) • realizeHLat b X x ∈
      Submodule.span ℝ ((zRealize b X M : Submodule ℤ _) : Set _) := by
    have hrat := realizeHLat_smul_rat b X (D : ℚ) x
    simp only [map_natCast, Rat.cast_natCast] at hrat
    rw [← hrat]
    exact Submodule.subset_span ⟨(D : K) • x, hDx, rfl⟩
  simpa [inv_smul_smul₀ (Nat.cast_ne_zero.mpr hD_pos.ne' : (D : ℝ) ≠ 0)] using
    Submodule.smul_mem _ (D : ℝ)⁻¹ h1

private lemma muMinO_sup_le_left (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (A B : Submodule (𝓞 K) V) (hA : A.FG) (hB : B.FG)
    (hA0 : A ≠ ⊥)
    (horth : ∀ x ∈ A, ∀ y ∈ B, inner ℝ (realizeHLat b X x) (realizeHLat b X y) = 0) :
    muMinO b X (A ⊔ B) ≤ muMinO b X A := by
  haveI : DiscreteTopology (zRealize b X A) := discreteTopology_zRealize_of_fg b X hX A hA
  haveI : DiscreteTopology (zRealize b X B) := discreteTopology_zRealize_of_fg b X hX B hB
  have hAB_fg : (A ⊔ B).FG := hA.sup hB
  haveI : DiscreteTopology (zRealize b X (A ⊔ B)) :=
    discreteTopology_zRealize_of_fg b X hX (A ⊔ B) hAB_fg
  have horth_span : ∀ u ∈ Submodule.span ℝ (zRealize b X A :
        Set (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2))),
      ∀ w ∈ Submodule.span ℝ (zRealize b X B :
        Set (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2))), inner ℝ u w = 0 := by
    intro u hu w hw
    induction hu using Submodule.span_induction with
    | mem x hx =>
      induction hw using Submodule.span_induction with
      | mem y hy =>
        rcases hx with ⟨a, ha, rfl⟩
        rcases hy with ⟨b', hb', rfl⟩
        exact horth a ha b' hb'
      | zero => simp
      | add _ _ _ _ h₁ h₂ => rw [inner_add_right, h₁, h₂, add_zero]
      | smul c _ _ h => rw [real_inner_smul_right, h, mul_zero]
    | zero => simp
    | add _ _ _ _ h₁ h₂ => rw [inner_add_left, h₁, h₂, add_zero]
    | smul c _ _ h => rw [real_inner_smul_left, h, mul_zero]
  have hAB_inf : A ⊓ B = ⊥ := by
    rw [eq_bot_iff]
    intro x ⟨hxA, hxB⟩
    exact realizeHLat_injective b X hX ((inner_self_eq_zero.mp (horth x hxA x hxB)).trans (map_zero _).symm)
  have hAB_ne : A ⊔ B ≠ ⊥ := fun h => hA0 (eq_bot_iff.mpr (h ▸ le_sup_left))
  refine le_csInf (quotSlopesO_nonempty b X A hA0) ?_
  rintro t ⟨N, hNA, hsatN, hNneA, rfl⟩
  have hN_fg : N.FG := Submodule.FG.of_le hA hNA
  haveI : DiscreteTopology (zRealize b X N) := discreteTopology_zRealize_of_fg b X hX N hN_fg
  have hNB_fg : (N ⊔ B).FG := hN_fg.sup hB
  haveI : DiscreteTopology (zRealize b X (N ⊔ B)) :=
    discreteTopology_zRealize_of_fg b X hX (N ⊔ B) hNB_fg
  have hNB_le : N ⊔ B ≤ A ⊔ B := sup_le (hNA.trans le_sup_left) le_sup_right
  have hsatNB : IsSaturated (zRealize b X (A ⊔ B)) (zRealize b X (N ⊔ B)) := by
    refine ⟨zRealize_mono b X hNB_le, ?_⟩
    rintro w ⟨x, hxAB, rfl⟩ hw_sp
    change x ∈ A ⊔ B at hxAB
    rw [Submodule.mem_sup] at hxAB
    obtain ⟨a, haA, b', hbB, rfl⟩ := hxAB
    have hsp_NB : Submodule.span ℝ ((zRealize b X (N ⊔ B) : Submodule ℤ _) :
          Set (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2))) ≤
        Submodule.span ℝ ((zRealize b X N : Submodule ℤ _) :
          Set (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2))) ⊔
          Submodule.span ℝ ((zRealize b X B : Submodule ℤ _) :
            Set (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2))) := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨z, hz, rfl⟩
      change z ∈ N ⊔ B at hz
      rw [Submodule.mem_sup] at hz
      obtain ⟨n, hnN, b₁, hb₁, rfl⟩ := hz
      rw [map_add]
      exact Submodule.add_mem _ (Submodule.mem_sup_left (Submodule.subset_span ⟨n, hnN, rfl⟩))
        (Submodule.mem_sup_right (Submodule.subset_span ⟨b₁, hb₁, rfl⟩))
    have hb_spB : realizeHLat b X b' ∈ Submodule.span ℝ ((zRealize b X B : Submodule ℤ _) : Set _) :=
      Submodule.subset_span ⟨b', hbB, rfl⟩
    have ha_sup : realizeHLat b X a ∈
        Submodule.span ℝ ((zRealize b X N : Submodule ℤ _) : Set _) ⊔
          Submodule.span ℝ ((zRealize b X B : Submodule ℤ _) : Set _) := by
      have hsub := Submodule.sub_mem _ (hsp_NB hw_sp) (Submodule.mem_sup_right hb_spB)
      simpa [map_add] using hsub
    rw [Submodule.mem_sup] at ha_sup
    obtain ⟨uN, huN, uB, huB, hu_eq⟩ := ha_sup
    have huN_A : uN ∈ Submodule.span ℝ ((zRealize b X A : Submodule ℤ _) : Set _) :=
      Submodule.span_mono (zRealize_mono b X hNA) huN
    have ha_A : realizeHLat b X a ∈ Submodule.span ℝ ((zRealize b X A : Submodule ℤ _) : Set _) :=
      Submodule.subset_span ⟨a, haA, rfl⟩
    have huB_A : uB ∈ Submodule.span ℝ ((zRealize b X A : Submodule ℤ _) : Set _) := by
      have hsub := Submodule.sub_mem _ ha_A huN_A
      rw [← hu_eq] at hsub
      simpa using hsub
    have huB0 : uB = 0 := inner_self_eq_zero.mp (horth_span uB huB_A uB huB)
    rw [huB0, add_zero] at hu_eq
    have ha_N : realizeHLat b X a ∈ zRealize b X N :=
      hsatN.2 (realizeHLat b X a) ⟨a, haA, rfl⟩ (hu_eq ▸ huN)
    rw [map_add]
    exact (zRealize b X (N ⊔ B)).add_mem (zRealize_mono b X le_sup_left ha_N)
      (zRealize_mono b X le_sup_right ⟨b', hbB, rfl⟩)
  have hNB_ne : N ⊔ B ≠ A ⊔ B := by
    intro heq
    apply hNneA
    apply le_antisymm hNA
    intro a haA
    have ha_in : a ∈ N ⊔ B := by rw [heq]; exact Submodule.mem_sup_left haA
    rw [Submodule.mem_sup] at ha_in
    obtain ⟨n, hnN, b', hbB, hnb⟩ := ha_in
    have hb_inf : b' ∈ A ⊓ B := by
      refine ⟨?_, hbB⟩
      have heqb : b' = a - n := by rw [← hnb]; abel
      rw [heqb]
      exact A.sub_mem haA (hNA hnN)
    rw [hAB_inf, Submodule.mem_bot] at hb_inf
    subst hb_inf
    rw [add_zero] at hnb
    rwa [← hnb]
  have hquot_eq : quotLat (zRealize b X (A ⊔ B)) (zRealize b X (N ⊔ B)) =
      quotLat (zRealize b X A) (zRealize b X N) := by
    have hproj_b : ∀ b' ∈ B, projOrth (zRealize b X (N ⊔ B)) (realizeHLat b X b') = 0 := fun b' hb' =>
      (RHDirect.Stage4ArakelovBost.projOrth_eq_zero_iff (zRealize b X (N ⊔ B)) _).mpr
        (Submodule.subset_span ⟨b', Submodule.mem_sup_right hb', rfl⟩)
    have hproj_a : ∀ a ∈ A, projOrth (zRealize b X (N ⊔ B)) (realizeHLat b X a) =
        projOrth (zRealize b X N) (realizeHLat b X a) := by
      intro a haA
      set y := projOrth (zRealize b X N) (realizeHLat b X a)
      have hdiff_N : realizeHLat b X a - y ∈
          Submodule.span ℝ ((zRealize b X N : Submodule ℤ _) : Set _) :=
        RHDirect.Stage4ArakelovBost.sub_projOrth_mem_span (zRealize b X N) (realizeHLat b X a)
      have hdiff_NB : realizeHLat b X a - y ∈
          Submodule.span ℝ ((zRealize b X (N ⊔ B) : Submodule ℤ _) : Set _) :=
        Submodule.span_mono (zRealize_mono b X le_sup_left) hdiff_N
      have hy_A : y ∈ Submodule.span ℝ ((zRealize b X A : Submodule ℤ _) : Set _) := by
        have h1 : realizeHLat b X a ∈ Submodule.span ℝ ((zRealize b X A : Submodule ℤ _) : Set _) :=
          Submodule.subset_span ⟨a, haA, rfl⟩
        have h2 : realizeHLat b X a - y ∈
            Submodule.span ℝ ((zRealize b X A : Submodule ℤ _) : Set _) :=
          Submodule.span_mono (zRealize_mono b X hNA) hdiff_N
        simpa using Submodule.sub_mem _ h1 h2
      have hy_orth : y ∈ (Submodule.span ℝ ((zRealize b X (N ⊔ B) : Submodule ℤ _) : Set _))ᗮ := by
        rw [Submodule.mem_orthogonal]
        intro u hu
        induction hu using Submodule.span_induction with
        | mem w hw =>
          rcases hw with ⟨z, hz, rfl⟩
          change z ∈ N ⊔ B at hz
          rw [Submodule.mem_sup] at hz
          obtain ⟨n, hnN, b', hbB, rfl⟩ := hz
          rw [map_add, inner_add_left]
          have hyn : inner ℝ (realizeHLat b X n) y = 0 :=
            RHDirect.Stage4ArakelovBost.projOrth_mem_orthogonal (zRealize b X N)
              (realizeHLat b X a) (realizeHLat b X n) (Submodule.subset_span ⟨n, hnN, rfl⟩)
          have hyb : inner ℝ (realizeHLat b X b') y = 0 := by
            rw [real_inner_comm]
            exact horth_span y hy_A (realizeHLat b X b') (Submodule.subset_span ⟨b', hbB, rfl⟩)
          change inner ℝ (realizeHLat b X n) y + inner ℝ (realizeHLat b X b') y = 0
          rw [hyn, hyb, add_zero]
        | zero => simp
        | add _ _ _ _ h₁ h₂ => rw [inner_add_left, h₁, h₂, add_zero]
        | smul c _ _ h => rw [real_inner_smul_left, h, mul_zero]
      have hpy : projOrth (zRealize b X (N ⊔ B)) y = y :=
        projOrth_eq_self_of_mem_orthogonal (zRealize b X (N ⊔ B)) hy_orth
      have hpdiff : projOrth (zRealize b X (N ⊔ B)) (realizeHLat b X a - y) = 0 :=
        (RHDirect.Stage4ArakelovBost.projOrth_eq_zero_iff (zRealize b X (N ⊔ B)) _).mpr hdiff_NB
      rw [map_sub, sub_eq_zero] at hpdiff
      rw [hpdiff, hpy]
    ext w
    simp only [quotLat, Submodule.mem_map]
    constructor
    · rintro ⟨_, ⟨x, hxAB, rfl⟩, rfl⟩
      change x ∈ A ⊔ B at hxAB
      rw [Submodule.mem_sup] at hxAB
      obtain ⟨a, haA, b', hbB, rfl⟩ := hxAB
      change (projOrth (zRealize b X (N ⊔ B))) (realizeHLat b X (a + b')) ∈
        (zRealize b X A).map ((projOrth (zRealize b X N)).restrictScalars ℤ)
      rw [map_add, map_add, hproj_a a haA, hproj_b b' hbB, add_zero]
      exact ⟨realizeHLat b X a, ⟨a, haA, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨a, haA, rfl⟩, rfl⟩
      refine ⟨realizeHLat b X a, ⟨a, Submodule.mem_sup_left haA, rfl⟩, ?_⟩
      first | simpa using (hproj_a a haA).symm | simpa using (hproj_a a haA)
  refine csInf_le (quotSlopesO_bddBelow b X hX (A ⊔ B) hAB_fg) ?_
  exact ⟨N ⊔ B, hNB_le, hsatNB, hNB_ne, congrArg ArakelovCovolume.slope hquot_eq⟩

/-- Two `𝓞 K`-submodules `A, B ≤ V` whose Euclidean realizations are orthogonal decompose as an
orthogonal direct sum (`deg` additivity, `rk` additivity, `muMax` sup, `muMin` inf). -/
theorem hlat_orthog_two_sum (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (A B : Submodule (𝓞 K) V) (hA : A.FG) (hB : B.FG)
    (horth : ∀ x ∈ A, ∀ y ∈ B, inner ℝ (realizeHLat b X x) (realizeHLat b X y) = 0) :
    rk (zRealize b X (A ⊔ B)) = rk (zRealize b X A) + rk (zRealize b X B) ∧
      degHLat b X (A ⊔ B) = degHLat b X A + degHLat b X B ∧
      (A ≠ ⊥ → B ≠ ⊥ →
        muMaxO b X (A ⊔ B) = max (muMaxO b X A) (muMaxO b X B) ∧
        muMinO b X (A ⊔ B) = min (muMinO b X A) (muMinO b X B)) := by
  haveI : DiscreteTopology (zRealize b X A) := discreteTopology_zRealize_of_fg b X hX A hA
  haveI : DiscreteTopology (zRealize b X B) := discreteTopology_zRealize_of_fg b X hX B hB
  have hAB_fg : (A ⊔ B).FG := hA.sup hB
  haveI : DiscreteTopology (zRealize b X (A ⊔ B)) :=
    discreteTopology_zRealize_of_fg b X hX (A ⊔ B) hAB_fg
  have horthZ : ∀ u ∈ zRealize b X A, ∀ w ∈ zRealize b X B, inner ℝ u w = 0 := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    exact horth x hx y hy
  have horth_span : ∀ u ∈ Submodule.span ℝ (zRealize b X A :
        Set (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2))),
      ∀ w ∈ Submodule.span ℝ (zRealize b X B :
        Set (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2))), inner ℝ u w = 0 := by
    intro u hu w hw
    induction hu using Submodule.span_induction with
    | mem x hx =>
      induction hw using Submodule.span_induction with
      | mem y hy => exact horthZ x hx y hy
      | zero => simp
      | add _ _ _ _ h₁ h₂ => rw [inner_add_right, h₁, h₂, add_zero]
      | smul c _ _ h => rw [real_inner_smul_right, h, mul_zero]
    | zero => simp
    | add _ _ _ _ h₁ h₂ => rw [inner_add_left, h₁, h₂, add_zero]
    | smul c _ _ h => rw [real_inner_smul_left, h, mul_zero]
  -- `zRealize A` is saturated in `zRealize (A ⊔ B)`, and `quotLat (zRealize (A ⊔ B)) (zRealize A) = zRealize B`.
  have hsatA : IsSaturated (zRealize b X (A ⊔ B)) (zRealize b X A) := by
    refine ⟨zRealize_mono b X le_sup_left, ?_⟩
    rintro w ⟨x, hx, rfl⟩ hw_sp
    change x ∈ A ⊔ B at hx
    rw [Submodule.mem_sup] at hx
    obtain ⟨a, ha, b', hb', rfl⟩ := hx
    have ha_sp : realizeHLat b X a ∈ Submodule.span ℝ ((zRealize b X A : Submodule ℤ _) : Set _) :=
      Submodule.subset_span ⟨a, ha, rfl⟩
    have hb_sp : realizeHLat b X b' ∈ Submodule.span ℝ ((zRealize b X A : Submodule ℤ _) : Set _) := by
      have hsub := Submodule.sub_mem _ hw_sp ha_sp
      simpa [map_add] using hsub
    have hb_self : inner ℝ (realizeHLat b X b') (realizeHLat b X b') = 0 :=
      horth_span (realizeHLat b X b') hb_sp (realizeHLat b X b')
        (Submodule.subset_span ⟨b', hb', rfl⟩)
    have hb0 : realizeHLat b X b' = 0 := inner_self_eq_zero.mp hb_self
    change realizeHLat b X (a + b') ∈ zRealize b X A
    rw [map_add, hb0, add_zero]
    exact ⟨a, ha, rfl⟩
  have hquot_eq : quotLat (zRealize b X (A ⊔ B)) (zRealize b X A) = zRealize b X B := by
    ext w
    simp only [quotLat, Submodule.mem_map]
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      change x ∈ A ⊔ B at hx
      rw [Submodule.mem_sup] at hx
      obtain ⟨a, ha, b', hb', rfl⟩ := hx
      have hpa : projOrth (zRealize b X A) (realizeHLat b X a) = 0 :=
        (RHDirect.Stage4ArakelovBost.projOrth_eq_zero_iff (zRealize b X A) _).mpr
          (Submodule.subset_span ⟨a, ha, rfl⟩)
      have hpb : projOrth (zRealize b X A) (realizeHLat b X b') = realizeHLat b X b' :=
        projOrth_eq_self_of_mem_orthogonal (zRealize b X A) (by
          rw [Submodule.mem_orthogonal]
          intro u hu
          exact horth_span u hu _ (Submodule.subset_span ⟨b', hb', rfl⟩))
      change (projOrth (zRealize b X A)) (realizeHLat b X (a + b')) ∈ _
      rw [map_add, map_add, hpa, zero_add, hpb]
      exact ⟨b', hb', rfl⟩
    · rintro ⟨b', hb', rfl⟩
      have hpb : projOrth (zRealize b X A) (realizeHLat b X b') = realizeHLat b X b' :=
        projOrth_eq_self_of_mem_orthogonal (zRealize b X A) (by
          rw [Submodule.mem_orthogonal]
          intro u hu
          exact horth_span u hu _ (Submodule.subset_span ⟨b', hb', rfl⟩))
      exact ⟨realizeHLat b X b', ⟨b', Submodule.mem_sup_right hb', rfl⟩, hpb⟩
  have hrk_add : rk (zRealize b X (A ⊔ B)) = rk (zRealize b X A) + rk (zRealize b X B) := by
    have h := rk_add_quotLat hsatA
    rw [hquot_eq] at h
    exact h
  have hdeg_add : degHLat b X (A ⊔ B) = degHLat b X A + degHLat b X B := by
    have h := degAr_eq_add_quotLat hsatA
    rw [hquot_eq] at h
    exact h
  refine ⟨hrk_add, hdeg_add, fun hA0 hB0 => ?_⟩
  have hAB_inf : A ⊓ B = ⊥ := by
    rw [eq_bot_iff]
    intro x ⟨hxA, hxB⟩
    have h0 : inner ℝ (realizeHLat b X x) (realizeHLat b X x) = 0 := horth x hxA x hxB
    exact realizeHLat_injective b X hX ((inner_self_eq_zero.mp h0).trans (map_zero _).symm)
  have hAB_deg : ∀ N : Submodule (𝓞 K) V, N ≤ A ⊔ B →
      ∃ (NA NB : Submodule (𝓞 K) V), NA ≤ A ∧ NB ≤ B ∧
        rk (zRealize b X N) = rk (zRealize b X NA) + rk (zRealize b X NB) ∧
        degHLat b X N ≤ degHLat b X NA + degHLat b X NB := by
    intro N hN
    let NA := N ⊓ A
    have hNA_le : NA ≤ A := inf_le_right
    -- Define `NB := { y ∈ B | ∃ a ∈ A, a + y ∈ N }`.
    let NB : Submodule (𝓞 K) V :=
      { carrier := { y ∈ B | ∃ a ∈ A, a + y ∈ N }
        zero_mem' := ⟨B.zero_mem, 0, A.zero_mem, by simp⟩
        add_mem' := by
          rintro y₁ y₂ ⟨hy₁, a₁, ha₁, h₁⟩ ⟨hy₂, a₂, ha₂, h₂⟩
          refine ⟨B.add_mem hy₁ hy₂, a₁ + a₂, A.add_mem ha₁ ha₂, ?_⟩
          have heq : a₁ + a₂ + (y₁ + y₂) = (a₁ + y₁) + (a₂ + y₂) := by abel
          rw [heq]; exact N.add_mem h₁ h₂
        smul_mem' := by
          rintro r y ⟨hy, a, ha, h⟩
          refine ⟨B.smul_mem r hy, r • a, A.smul_mem r ha, ?_⟩
          rw [← smul_add]; exact N.smul_mem r h }
    have hNB_le : NB ≤ B := fun _ h => h.1
    have hNA_fg : NA.FG := Submodule.FG.of_le hA hNA_le
    have hNB_fg : NB.FG := Submodule.FG.of_le hB hNB_le
    have hN_fg : N.FG := Submodule.FG.of_le hAB_fg hN
    haveI : DiscreteTopology (zRealize b X N) := discreteTopology_zRealize_of_fg b X hX N hN_fg
    haveI : DiscreteTopology (zRealize b X NA) := discreteTopology_zRealize_of_fg b X hX NA hNA_fg
    haveI : DiscreteTopology (zRealize b X NB) := discreteTopology_zRealize_of_fg b X hX NB hNB_fg
    -- `zRealize NA` is saturated in `zRealize N`.
    have hsatNA : IsSaturated (zRealize b X N) (zRealize b X NA) := by
      refine ⟨zRealize_mono b X inf_le_left, ?_⟩
      rintro w ⟨x, hxN, rfl⟩ hw_sp
      have hxAB := hN hxN
      rw [Submodule.mem_sup] at hxAB
      obtain ⟨a, haA, b', hbB, rfl⟩ := hxAB
      have hw_orth : inner ℝ (realizeHLat b X b') (realizeHLat b X b') = 0 := by
        have ha_sp : realizeHLat b X a ∈ Submodule.span ℝ ((zRealize b X A : Submodule ℤ _) : Set _) :=
          Submodule.subset_span ⟨a, haA, rfl⟩
        have hw_spA : realizeHLat b X (a + b') ∈ Submodule.span ℝ ((zRealize b X A : Submodule ℤ _) : Set _) :=
          Submodule.span_mono (zRealize_mono b X hNA_le) hw_sp
        have hb_spA : realizeHLat b X b' ∈ Submodule.span ℝ ((zRealize b X A : Submodule ℤ _) : Set _) := by
          have := Submodule.sub_mem _ hw_spA ha_sp
          simpa [map_add] using this
        exact horth_span _ hb_spA _ (Submodule.subset_span ⟨b', hbB, rfl⟩)
      have hb0 : b' = 0 :=
        realizeHLat_injective b X hX ((inner_self_eq_zero.mp hw_orth).trans (map_zero _).symm)
      subst hb0
      rw [add_zero] at hxN ⊢
      exact ⟨a, ⟨hxN, haA⟩, rfl⟩
    have hN_eq : rk (zRealize b X N) = rk (zRealize b X NA) + rk (zRealize b X NB) := by
      -- Exact sequence `0 → NA → N → NB → 0` of `𝓞 K`-modules!
      have hex_seq : rkK (K := K) N = rkK (K := K) NA + rkK (K := K) NB := by
        have hN_sp : Module.finrank K (Submodule.span K (N : Set V)) =
            Module.finrank K (Submodule.span K (NA : Set V)) +
              Module.finrank K (Submodule.span K (NB : Set V)) := by
          -- Map `span K N →ₗ[K] V` via `IsCompl` projection onto `WB` with kernel `span K NA`!
          let WA := Submodule.span K (A : Set V)
          let WB := Submodule.span K (B : Set V)
          let WN := Submodule.span K (N : Set V)
          have hW_inf : WA ⊓ WB = ⊥ := by
            rw [eq_bot_iff]
            intro x ⟨hxA, hxB⟩
            have hx_realA := mem_real_span_zRealize_of_mem_span_K b X A hxA
            have hx_realB := mem_real_span_zRealize_of_mem_span_K b X B hxB
            exact realizeHLat_injective b X hX
              ((inner_self_eq_zero.mp (horth_span _ hx_realA _ hx_realB)).trans (map_zero _).symm)
          have hN_le_sup : WN ≤ WA ⊔ WB := by
            refine Submodule.span_le.mpr fun x hx => ?_
            have hxAB := hN hx
            rw [Submodule.mem_sup] at hxAB
            obtain ⟨a, ha, b', hb', rfl⟩ := hxAB
            exact Submodule.add_mem _ (Submodule.mem_sup_left (Submodule.subset_span ha))
              (Submodule.mem_sup_right (Submodule.subset_span hb'))
          let WA₀ : Submodule K ↥(WA ⊔ WB) := WA.comap (WA ⊔ WB).subtype
          let WB₀ : Submodule K ↥(WA ⊔ WB) := WB.comap (WA ⊔ WB).subtype
          have hcompl : IsCompl WA₀ WB₀ := by
            refine ⟨?_, ?_⟩
            · rw [disjoint_iff, eq_bot_iff]
              rintro ⟨x, hx⟩ ⟨hxA, hxB⟩
              exact Subtype.ext ((eq_bot_iff.mp hW_inf) ⟨hxA, hxB⟩)
            · rw [codisjoint_iff, eq_top_iff]
              rintro ⟨x, hx⟩ _
              rw [Submodule.mem_sup] at hx ⊢
              obtain ⟨a, ha, b', hb', rfl⟩ := hx
              exact ⟨⟨a, Submodule.mem_sup_left ha⟩, ha, ⟨b', Submodule.mem_sup_right hb'⟩, hb', rfl⟩
          let projB : ↥(WA ⊔ WB) →ₗ[K] V :=
            ((WA ⊔ WB).subtype.comp WB₀.subtype).comp (WB₀.projectionOnto WA₀ hcompl.symm)
          have hprojB_add : ∀ {a b' : V} (ha : a ∈ WA) (hb' : b' ∈ WB),
              projB ⟨a + b', Submodule.add_mem _ (Submodule.mem_sup_left ha)
                (Submodule.mem_sup_right hb')⟩ = b' := by
            intro a b' ha hb'
            let xa : ↥WA₀ := ⟨⟨a, Submodule.mem_sup_left ha⟩, ha⟩
            let xb : ↥WB₀ := ⟨⟨b', Submodule.mem_sup_right hb'⟩, hb'⟩
            have hsplit : (⟨a + b', Submodule.add_mem _ (Submodule.mem_sup_left ha)
                (Submodule.mem_sup_right hb')⟩ : ↥(WA ⊔ WB)) = (xa : ↥(WA ⊔ WB)) + (xb : ↥(WA ⊔ WB)) := rfl
            rw [hsplit]
            simp only [projB, LinearMap.comp_apply, map_add, Submodule.coe_subtype,
              Submodule.projectionOnto_apply_right hcompl.symm xa,
              Submodule.projectionOnto_apply_left hcompl.symm xb]
            simp [xb]
          let f : ↥WN →ₗ[K] V := projB.comp (Submodule.inclusion hN_le_sup)
          have hker_f : (LinearMap.ker f).map WN.subtype = Submodule.span K (NA : Set V) := by
            ext v
            simp only [Submodule.mem_map, LinearMap.mem_ker, Submodule.coe_subtype,
              Subtype.exists, exists_and_right, exists_eq_right]
            constructor
            · rintro ⟨hv, hfv⟩
              obtain ⟨D, hD_pos, hDv⟩ := pos_nat_smul_mem_of_mem_span_K N hv
              have hDv_AB := hN hDv
              rw [Submodule.mem_sup] at hDv_AB
              obtain ⟨a, haA, b', hbB, hab⟩ := hDv_AB
              have hfD : f ⟨(D : K) • v, WN.smul_mem (D : K) hv⟩ = b' := by
                change projB ⟨(D : K) • v, _⟩ = b'
                have hpt : (⟨(D : K) • v, hN_le_sup (WN.smul_mem (D : K) hv)⟩ : ↥(WA ⊔ WB)) =
                    ⟨a + b', Submodule.add_mem _ (Submodule.mem_sup_left (Submodule.subset_span haA))
                      (Submodule.mem_sup_right (Submodule.subset_span hbB))⟩ :=
                  Subtype.ext hab.symm
                rw [hpt]
                exact hprojB_add (Submodule.subset_span haA) (Submodule.subset_span hbB)
              have hfD0 : f ⟨(D : K) • v, WN.smul_mem (D : K) hv⟩ = 0 := by
                change f ((D : K) • ⟨v, hv⟩) = 0
                rw [map_smul, hfv, smul_zero]
              have hb0 : b' = 0 := by rw [← hfD, hfD0]
              subst hb0
              rw [add_zero] at hab
              have hDv_NA : (D : K) • v ∈ NA := ⟨hDv, hab ▸ haA⟩
              have hv_eq : v = (D : K)⁻¹ • ((D : K) • v) :=
                (inv_smul_smul₀ (Nat.cast_ne_zero.mpr hD_pos.ne') v).symm
              rw [hv_eq]
              exact Submodule.smul_mem _ _ (Submodule.subset_span hDv_NA)
            · intro hv_NA
              have hv_WN : v ∈ WN := Submodule.span_mono (inf_le_left : NA ≤ N) hv_NA
              refine ⟨hv_WN, ?_⟩
              obtain ⟨D, hD_pos, hDv⟩ := pos_nat_smul_mem_of_mem_span_K NA hv_NA
              have hDvA : (D : K) • v ∈ WA := Submodule.subset_span (hNA_le hDv)
              have hfD : f ((D : K) • ⟨v, hv_WN⟩) = 0 := by
                have hpt : (⟨(D : K) • v, hN_le_sup (WN.smul_mem (D : K) hv_WN)⟩ : ↥(WA ⊔ WB)) =
                    ⟨(D : K) • v + 0, Submodule.add_mem _ (Submodule.mem_sup_left hDvA)
                      (Submodule.mem_sup_right WB.zero_mem)⟩ :=
                  Subtype.ext (add_zero _).symm
                change projB ⟨(D : K) • v, hN_le_sup (WN.smul_mem (D : K) hv_WN)⟩ = 0
                rw [hpt]
                exact hprojB_add hDvA WB.zero_mem
              rw [map_smul] at hfD
              exact (smul_eq_zero.mp hfD).resolve_left (Nat.cast_ne_zero.mpr hD_pos.ne')
          have hrange_f : LinearMap.range f = Submodule.span K (NB : Set V) := by
            ext v
            rw [LinearMap.mem_range]
            constructor
            · rintro ⟨⟨x, hx⟩, rfl⟩
              obtain ⟨D, hD_pos, hDx⟩ := pos_nat_smul_mem_of_mem_span_K N hx
              have hDx_AB := hN hDx
              rw [Submodule.mem_sup] at hDx_AB
              obtain ⟨a, haA, b', hbB, hab⟩ := hDx_AB
              have hfD : f ((D : K) • ⟨x, hx⟩) = b' := by
                change projB ⟨(D : K) • x, _⟩ = b'
                have hpt : (⟨(D : K) • x, hN_le_sup (WN.smul_mem (D : K) hx)⟩ : ↥(WA ⊔ WB)) =
                    ⟨a + b', Submodule.add_mem _ (Submodule.mem_sup_left (Submodule.subset_span haA))
                      (Submodule.mem_sup_right (Submodule.subset_span hbB))⟩ :=
                  Subtype.ext hab.symm
                rw [hpt]
                exact hprojB_add (Submodule.subset_span haA) (Submodule.subset_span hbB)
              have hbNB : b' ∈ NB := ⟨hbB, a, haA, hab ▸ hDx⟩
              rw [map_smul] at hfD
              have hfx_eq : f ⟨x, hx⟩ = (D : K)⁻¹ • b' := by
                rw [← hfD, inv_smul_smul₀ (Nat.cast_ne_zero.mpr hD_pos.ne')]
              rw [hfx_eq]
              exact Submodule.smul_mem _ _ (Submodule.subset_span hbNB)
            · intro hv_NB
              obtain ⟨D, hD_pos, hDv⟩ := pos_nat_smul_mem_of_mem_span_K NB hv_NB
              rcases hDv with ⟨hDvB, a, haA, han⟩
              have han_WN : a + (D : K) • v ∈ WN := Submodule.subset_span han
              refine ⟨⟨(D : K)⁻¹ • (a + (D : K) • v), WN.smul_mem _ han_WN⟩, ?_⟩
              change f ((D : K)⁻¹ • ⟨a + (D : K) • v, han_WN⟩) = v
              rw [map_smul]
              have hfa : f ⟨a + (D : K) • v, han_WN⟩ = (D : K) • v := by
                change projB ⟨a + (D : K) • v, _⟩ = (D : K) • v
                exact hprojB_add (Submodule.subset_span haA) (Submodule.subset_span hDvB)
              rw [hfa, inv_smul_smul₀ (Nat.cast_ne_zero.mpr hD_pos.ne')]
          have hrk_ker : Module.finrank K (LinearMap.ker f) =
              Module.finrank K (Submodule.span K (NA : Set V)) := by
            rw [← hker_f, Submodule.finrank_map_subtype_eq]
          have hrk_range : Module.finrank K (LinearMap.range f) =
              Module.finrank K (Submodule.span K (NB : Set V)) := by
            rw [hrange_f]
          have : Module.Finite K V := Module.Finite.of_basis b
          have hrank_null := LinearMap.finrank_range_add_finrank_ker f
          rw [hrk_range, hrk_ker, add_comm] at hrank_null
          exact hrank_null.symm
        exact hN_sp
      rw [rk_zRealize_eq b X hX N hN_fg, rk_zRealize_eq b X hX NA hNA_fg,
        rk_zRealize_eq b X hX NB hNB_fg, hex_seq, mul_add]
    have hdeg_le : degHLat b X N ≤ degHLat b X NA + degHLat b X NB := by
      have hdeg_q := degAr_eq_add_quotLat hsatNA
      have hrk_q := rk_add_quotLat hsatNA
      haveI : DiscreteTopology (quotLat (zRealize b X N) (zRealize b X NA)) :=
        discreteTopology_quotLat hsatNA
      have hqrk : rk (quotLat (zRealize b X N) (zRealize b X NA)) = rk (zRealize b X NB) := by
        omega
      -- Contraction `projOrth (zRealize b X A)` maps `quotLat (zRealize N) (zRealize NA)` onto `zRealize NB`!
      by_cases hNB0 : NB = ⊥
      · have hNA_eq : NA = N := by
          apply le_antisymm inf_le_left
          intro x hxN
          have hxAB := hN hxN
          rw [Submodule.mem_sup] at hxAB
          obtain ⟨a, haA, b', hbB, rfl⟩ := hxAB
          have hb_mem : b' ∈ NB := ⟨hbB, a, haA, hxN⟩
          rw [hNB0, Submodule.mem_bot] at hb_mem
          rw [hb_mem, add_zero] at hxN ⊢
          exact ⟨hxN, haA⟩
        rw [hNB0, show degHLat b X (⊥ : Submodule (𝓞 K) V) = 0 by
          unfold degHLat; rw [zRealize_bot, degAr_bot], add_zero, hNA_eq]
      · have hNB_Zne : zRealize b X NB ≠ ⊥ := zRealize_ne_bot b X hX hNB0
        have hq_ne : quotLat (zRealize b X N) (zRealize b X NA) ≠ ⊥ := by
          intro h0
          rw [h0, show rk (⊥ : Submodule ℤ _) = 0 by simp [rk]] at hqrk
          have := rk_pos_of_ne_bot _ hNB_Zne
          omega
        -- Construct `φ : quotLat (zRealize N) (zRealize NA) →ₗ[ℤ] zRealize NB` using `projOrth (zRealize A)`!
        let φ : quotLat (zRealize b X N) (zRealize b X NA) →ₗ[ℤ] zRealize b X NB :=
          { toFun := fun q => ⟨projOrth (zRealize b X A) q.1, by
              obtain ⟨w, ⟨x, hxN, rfl⟩, hq_eq⟩ := q.2
              have hxAB := hN hxN
              rw [Submodule.mem_sup] at hxAB
              obtain ⟨a, haA, b', hbB, rfl⟩ := hxAB
              have hpa : projOrth (zRealize b X A) (realizeHLat b X a) = 0 :=
                (RHDirect.Stage4ArakelovBost.projOrth_eq_zero_iff (zRealize b X A) _).mpr
                  (Submodule.subset_span ⟨a, haA, rfl⟩)
              have hpb : projOrth (zRealize b X A) (realizeHLat b X b') = realizeHLat b X b' :=
                projOrth_eq_self_of_mem_orthogonal (zRealize b X A) (by
                  rw [Submodule.mem_orthogonal]
                  intro u hu
                  exact horth_span u hu _ (Submodule.subset_span ⟨b', hbB, rfl⟩))
              have h1 : projOrth (zRealize b X A) (projOrth (zRealize b X NA) (realizeHLat b X (a + b'))) =
                  realizeHLat b X b' := by
                have hdiff : realizeHLat b X (a + b') - projOrth (zRealize b X NA) (realizeHLat b X (a + b')) ∈
                    Submodule.span ℝ ((zRealize b X NA : Submodule ℤ _) : Set _) :=
                  sub_projOrth_mem_span _ _
                have hdiffA : realizeHLat b X (a + b') - projOrth (zRealize b X NA) (realizeHLat b X (a + b')) ∈
                    Submodule.span ℝ ((zRealize b X A : Submodule ℤ _) : Set _) :=
                  Submodule.span_mono (zRealize_mono b X hNA_le) hdiff
                have hkill : projOrth (zRealize b X A)
                    (realizeHLat b X (a + b') - projOrth (zRealize b X NA) (realizeHLat b X (a + b'))) = 0 :=
                  (RHDirect.Stage4ArakelovBost.projOrth_eq_zero_iff (zRealize b X A) _).mpr hdiffA
                rw [map_sub, sub_eq_zero] at hkill
                rw [← hkill, map_add, map_add, hpa, zero_add, hpb]
              rw [← hq_eq]
              change projOrth (zRealize b X A) ((projOrth (zRealize b X NA)) (realizeHLat b X (a + b'))) ∈ _
              rw [h1]
              exact ⟨b', ⟨hbB, a, haA, hxN⟩, rfl⟩⟩
            map_add' := fun u v => Subtype.ext (map_add _ u.1 v.1)
            map_smul' := fun c u => Subtype.ext (map_zsmul _ c u.1) }
        have hφ_surj : Function.Surjective φ := by
          rintro ⟨_, ⟨b', ⟨hbB, a, haA, hxN⟩, rfl⟩⟩
          refine ⟨⟨projOrth (zRealize b X NA) (realizeHLat b X (a + b')),
            ⟨realizeHLat b X (a + b'), ⟨a + b', hxN, rfl⟩, rfl⟩⟩, ?_⟩
          apply Subtype.ext
          have hdiff : realizeHLat b X (a + b') - projOrth (zRealize b X NA) (realizeHLat b X (a + b')) ∈
              Submodule.span ℝ ((zRealize b X A : Submodule ℤ _) : Set _) :=
            Submodule.span_mono (zRealize_mono b X hNA_le) (sub_projOrth_mem_span _ _)
          have hkill : projOrth (zRealize b X A)
              (realizeHLat b X (a + b') - projOrth (zRealize b X NA) (realizeHLat b X (a + b'))) = 0 :=
            (RHDirect.Stage4ArakelovBost.projOrth_eq_zero_iff _ _).mpr hdiff
          rw [map_sub, sub_eq_zero] at hkill
          have hpa : projOrth (zRealize b X A) (realizeHLat b X a) = 0 :=
            (RHDirect.Stage4ArakelovBost.projOrth_eq_zero_iff _ _).mpr
              (Submodule.subset_span ⟨a, haA, rfl⟩)
          have hpb : projOrth (zRealize b X A) (realizeHLat b X b') = realizeHLat b X b' :=
            projOrth_eq_self_of_mem_orthogonal _ (by
              rw [Submodule.mem_orthogonal]
              intro u hu
              exact horth_span u hu _ (Submodule.subset_span ⟨b', hbB, rfl⟩))
          change projOrth (zRealize b X A) (projOrth (zRealize b X NA) (realizeHLat b X (a + b'))) =
            realizeHLat b X b'
          rw [← hkill, map_add, map_add, hpa, zero_add, hpb]
        let r := rk (quotLat (zRealize b X N) (zRealize b X NA))
        let bQ : Module.Basis (Fin r) ℤ (quotLat (zRealize b X N) (zRealize b X NA)) :=
          Module.finBasis ℤ (quotLat (zRealize b X N) (zRealize b X NA))
        let bNB : Module.Basis (Fin r) ℤ (zRealize b X NB) :=
          (Module.finBasis ℤ (zRealize b X NB)).reindex (finCongr hqrk.symm)
        have hs_ex : ∀ j : Fin r, ∃ s, φ s = bNB j := fun j => hφ_surj (bNB j)
        choose s hs using hs_ex
        let ψ : zRealize b X NB →ₗ[ℤ] quotLat (zRealize b X N) (zRealize b X NA) :=
          bNB.constr ℤ s
        let M : Matrix (Fin r) (Fin r) ℤ := fun k i => bNB.repr (φ (bQ i)) k
        let P : Matrix (Fin r) (Fin r) ℤ := fun i j => bQ.repr (s j) i
        have hMP : M * P = 1 := by
          ext k j
          rw [Matrix.mul_apply, Matrix.one_apply]
          have hs_repr : s j = ∑ i, P i j • bQ i := (bQ.sum_repr (s j)).symm
          have hφ_s : φ (s j) = ∑ i, P i j • φ (bQ i) := by
            conv_lhs => rw [hs_repr]
            simp only [map_sum, map_zsmul]
          have h1 : bNB.repr (bNB j) k = bNB.repr (φ (s j)) k := by rw [hs j]
          rw [hφ_s, map_sum] at h1
          simp only [map_zsmul, Finsupp.coe_finsetSum, Finsupp.coe_smul, Finset.sum_apply,
            Pi.smul_apply, smul_eq_mul, bNB.repr_self, Finsupp.single_apply] at h1
          calc ∑ i, M k i * P i j = ∑ i, P i j * (bNB.repr (φ (bQ i))) k :=
                Finset.sum_congr rfl fun i _ => mul_comm _ _
            _ = if j = k then 1 else 0 := h1.symm
            _ = if k = j then 1 else 0 := by simp only [eq_comm]
        have hdet : M.det * P.det = 1 := by rw [← Matrix.det_mul, hMP, Matrix.det_one]
        have hunit : IsUnit M.det := isUnit_iff_exists_inv.mpr ⟨P.det, hdet⟩
        have hPM : P * M = 1 := by
          rw [show P = M⁻¹ from (Matrix.inv_eq_right_inv hMP).symm, Matrix.nonsing_inv_mul _ hunit]
        have hψφ : ψ.comp φ = LinearMap.id := by
          apply bQ.ext
          intro i
          simp only [LinearMap.comp_apply, LinearMap.id_apply]
          have hφ_repr : φ (bQ i) = ∑ k, M k i • bNB k := (bNB.sum_repr (φ (bQ i))).symm
          rw [hφ_repr, map_sum]
          have hψ_b : ∀ k, ψ (bNB k) = s k := fun k => bNB.constr_basis ℤ s k
          simp_rw [map_zsmul, hψ_b]
          have hsum_s : ∑ k, M k i • s k = ∑ k, M k i • ∑ j, P j k • bQ j := by
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [← (bQ.sum_repr (s k)).symm]
          rw [hsum_s]
          simp_rw [Finset.smul_sum, smul_smul]
          rw [Finset.sum_comm]
          have hdiag : ∀ j, (∑ k, M k i * P j k) • bQ j = (if j = i then (1 : ℤ) else 0) • bQ j := by
            intro j
            congr 1
            have hPM_ji := congrFun (congrFun hPM j) i
            rw [Matrix.mul_apply, Matrix.one_apply] at hPM_ji
            calc ∑ k, M k i * P j k = ∑ k, P j k * M k i :=
                    Finset.sum_congr rfl fun k _ => mul_comm _ _
              _ = if j = i then 1 else 0 := hPM_ji
          simp only [← Finset.sum_smul, hdiag, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq',
            Finset.mem_univ, ↓reduceIte]
        have hφ_ψ : φ.comp ψ = LinearMap.id := by
          apply bNB.ext
          intro j
          simp only [LinearMap.comp_apply, LinearMap.id_apply, ψ, bNB.constr_basis, hs j]
        let e : quotLat (zRealize b X N) (zRealize b X NA) ≃ₗ[ℤ] zRealize b X NB :=
          LinearEquiv.ofLinearMap φ ψ hφ_ψ hψφ
        let bQ' : Module.Basis (Fin r) ℤ (zRealize b X NB) := bQ.map e
        let vQ : Fin r → EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2) := fun i => (bQ i : _)
        let xNB : Fin r → EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2) := fun i => (bQ' i : _)
        have hxNB_eq : ∀ i, xNB i = projOrth (zRealize b X A) (vQ i) := fun _ => rfl
        have hli_x : LinearIndependent ℝ xNB := linearIndependent_coe_basis (zRealize b X NB) bQ'
        have hcov_le_gram : covol (zRealize b X NB) ≤ Real.sqrt (Matrix.gram ℝ xNB).det :=
          RHDirect.ArakelovCovolume.covol_le_sqrt_det_gram xNB (fun i => (bQ' i).2) hli_x
            (by simp [r, hqrk])
        have hgram_le : (Matrix.gram ℝ xNB).det ≤ 1 ^ (2 * Fintype.card (Fin r)) * (Matrix.gram ℝ vQ).det := by
          refine RHDirect.ArakelovCovolume.gram_det_le vQ xNB 1 fun c => ?_
          have hsum_x : ∑ i, c i • xNB i = projOrth (zRealize b X A) (∑ i, c i • vQ i) := by
            simp_rw [hxNB_eq, map_sum, map_smul]
          rw [hsum_x, one_mul]
          exact RHDirect.Stage4ArakelovBost.norm_projOrth_le (zRealize b X A) _
        simp only [one_pow, one_mul] at hgram_le
        have hcov_le : covol (zRealize b X NB) ≤ covol (quotLat (zRealize b X N) (zRealize b X NA)) := by
          calc covol (zRealize b X NB) ≤ Real.sqrt (Matrix.gram ℝ xNB).det := hcov_le_gram
            _ ≤ Real.sqrt (Matrix.gram ℝ vQ).det := Real.sqrt_le_sqrt hgram_le
            _ = covol (quotLat (zRealize b X N) (zRealize b X NA)) :=
              (covol_eq_sqrt_det_gram (quotLat (zRealize b X N) (zRealize b X NA)) bQ).symm
        have hdeg_q_le : degAr (quotLat (zRealize b X N) (zRealize b X NA)) ≤ degHLat b X NB := by
          show degAr (quotLat (zRealize b X N) (zRealize b X NA)) ≤ degAr (zRealize b X NB)
          unfold degAr
          linarith [Real.log_le_log (covol_pos (zRealize b X NB)) hcov_le]
        change degAr (quotLat (zRealize b X N) (zRealize b X NA)) ≤ degAr (zRealize b X NB) at hdeg_q_le
        unfold degHLat
        linarith
    exact ⟨NA, NB, hNA_le, hNB_le, hN_eq, hdeg_le⟩
  constructor
  · -- `muMaxO (A ⊔ B) = max (muMaxO A) (muMaxO B)`
    apply le_antisymm
    · rw [muMaxO_char b X hX (A ⊔ B) hAB_fg (fun h => hA0 (eq_bot_iff.mpr (h ▸ le_sup_left)))]
      intro N hN
      obtain ⟨NA, NB, hNA_le, hNB_le, hrkN, hdegN⟩ := hAB_deg N hN
      have hA_b := (muMaxO_char b X hX A hA hA0 (muMaxO b X A)).mp le_rfl NA hNA_le
      have hB_b := (muMaxO_char b X hX B hB hB0 (muMaxO b X B)).mp le_rfl NB hNB_le
      have h1 : muMaxO b X A * (rk (zRealize b X NA) : ℝ) ≤
          max (muMaxO b X A) (muMaxO b X B) * (rk (zRealize b X NA) : ℝ) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (Nat.cast_nonneg _)
      have h2 : muMaxO b X B * (rk (zRealize b X NB) : ℝ) ≤
          max (muMaxO b X A) (muMaxO b X B) * (rk (zRealize b X NB) : ℝ) :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (Nat.cast_nonneg _)
      rw [hrkN, Nat.cast_add]
      linarith
    · refine max_le ?_ ?_
      · refine csSup_le (slopesO_nonempty b X A hA0) ?_
        rintro t ⟨M, hMA, hM0, rfl⟩
        exact le_csSup (slopesO_bddAbove b X hX (A ⊔ B) hAB_fg) ⟨M, hMA.trans le_sup_left, hM0, rfl⟩
      · refine csSup_le (slopesO_nonempty b X B hB0) ?_
        rintro t ⟨M, hMB, hM0, rfl⟩
        exact le_csSup (slopesO_bddAbove b X hX (A ⊔ B) hAB_fg) ⟨M, hMB.trans le_sup_right, hM0, rfl⟩
  · -- `muMinO (A ⊔ B) = min (muMinO A) (muMinO B)`
    apply le_antisymm
    · refine le_min (muMinO_sup_le_left b X hX A B hA hB hA0 horth) ?_
      rw [sup_comm]
      refine muMinO_sup_le_left b X hX B A hB hA hB0 fun y hy x hx => ?_
      rw [real_inner_comm]
      exact horth x hx y hy
    · rw [muMinO_char b X hX (A ⊔ B) hAB_fg (fun h => hA0 (eq_bot_iff.mpr (h ▸ le_sup_left)))]
      intro N hN
      obtain ⟨NA, NB, hNA_le, hNB_le, hrkN, hdegN⟩ := hAB_deg N hN
      have hA_b := (muMinO_char b X hX A hA hA0 (muMinO b X A)).mp le_rfl NA hNA_le
      have hB_b := (muMinO_char b X hX B hB hB0 (muMinO b X B)).mp le_rfl NB hNB_le
      have hrkNA_le : rk (zRealize b X NA) ≤ rk (zRealize b X A) :=
        Submodule.finrank_mono (zRealize_mono b X hNA_le)
      have hrkNB_le : rk (zRealize b X NB) ≤ rk (zRealize b X B) :=
        Submodule.finrank_mono (zRealize_mono b X hNB_le)
      have h1 : min (muMinO b X A) (muMinO b X B) * ((rk (zRealize b X A) : ℝ) - rk (zRealize b X NA)) ≤
          muMinO b X A * ((rk (zRealize b X A) : ℝ) - rk (zRealize b X NA)) :=
        mul_le_mul_of_nonneg_right (min_le_left _ _) (sub_nonneg.mpr (Nat.cast_le.mpr hrkNA_le))
      have h2 : min (muMinO b X A) (muMinO b X B) * ((rk (zRealize b X B) : ℝ) - rk (zRealize b X NB)) ≤
          muMinO b X B * ((rk (zRealize b X B) : ℝ) - rk (zRealize b X NB)) :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) (sub_nonneg.mpr (Nat.cast_le.mpr hrkNB_le))
      rw [hrk_add, hrkN, Nat.cast_add, Nat.cast_add, hdeg_add]
      linarith

end TwoTermOrthogonal

section IndexedOrthogonal

variable {K V ι : Type*} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι]

private lemma biSup_insert_finset {γ : Type*} [DecidableEq γ] (a : γ) (t : Finset γ)
    (N : γ → Submodule (𝓞 K) V) :
    (⨆ c ∈ insert a t, N c) = N a ⊔ ⨆ c ∈ t, N c := by
  simp only [Finset.mem_insert, iSup_or, iSup_sup_eq, iSup_iSup_eq_left]

private lemma fg_biSup_finset {γ : Type*} [DecidableEq γ] (s : Finset γ)
    (N : γ → Submodule (𝓞 K) V) (hN : ∀ c ∈ s, (N c).FG) :
    (⨆ c ∈ s, N c).FG := by
  induction s using Finset.induction_on with
  | empty => simp [Submodule.fg_bot]
  | @insert a t hat ih =>
    rw [biSup_insert_finset]
    exact (hN a (Finset.mem_insert_self a t)).sup (ih fun c hc => hN c (Finset.mem_insert_of_mem hc))

private lemma inner_realize_orthog_biSup {γ : Type*} [DecidableEq γ]
    (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (a : γ) (t : Finset γ) (_hat : a ∉ t) (N : γ → Submodule (𝓞 K) V)
    (horth : ∀ c ∈ t, ∀ x ∈ N a, ∀ y ∈ N c, inner ℝ (realizeHLat b X x) (realizeHLat b X y) = 0)
    {x y : V} (hx : x ∈ N a) (hy : y ∈ ⨆ c ∈ t, N c) :
    inner ℝ (realizeHLat b X x) (realizeHLat b X y) = 0 := by
  suffices h : ∀ (y : V), y ∈ ⨆ c ∈ t, N c →
      (∀ c ∈ t, ∀ x ∈ N a, ∀ z ∈ N c, inner ℝ (realizeHLat b X x) (realizeHLat b X z) = 0) →
      inner ℝ (realizeHLat b X x) (realizeHLat b X y) = 0 from h y hy horth
  clear _hat y hy horth
  induction t using Finset.induction_on with
  | empty =>
    intro y hy _
    have hbot : (⨆ c ∈ (∅ : Finset γ), N c) = ⊥ :=
      iSup₂_eq_bot.mpr fun _ hc => absurd hc (Finset.notMem_empty _)
    rw [hbot, Submodule.mem_bot] at hy
    subst hy
    simp
  | @insert c₀ t' hc₀ ih =>
    intro y hy horth'
    rw [biSup_insert_finset, Submodule.mem_sup] at hy
    obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := hy
    rw [map_add, inner_add_right]
    have h1 := horth' c₀ (Finset.mem_insert_self c₀ t') x hx y₁ hy₁
    have h2 := ih y₂ hy₂ (fun c hc => horth' c (Finset.mem_insert_of_mem hc))
    rw [h1, h2, add_zero]

/-- **Indexed Orthogonal Direct Sum (`hlat_orthog_direct_sum`)**:
for a finite family `N : γ → Submodule (𝓞 K) V` indexed by `s : Finset γ` whose Euclidean
realizations are pairwise orthogonal, `⨆ c ∈ s, N c` has additive `rk`, additive `degHLat`,
`muMax` equal to the maximum of the `N c` (`∃ c ∈ s`), and `muMin` equal to the minimum (`∃ c ∈ s`). -/
theorem hlat_orthog_direct_sum {γ : Type*} [DecidableEq γ]
    (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (s : Finset γ) (N : γ → Submodule (𝓞 K) V)
    (hN_fg : ∀ c ∈ s, (N c).FG)
    (horth : ∀ c ∈ s, ∀ c' ∈ s, c ≠ c' → ∀ x ∈ N c, ∀ y ∈ N c',
      inner ℝ (realizeHLat b X x) (realizeHLat b X y) = 0) :
    (⨆ c ∈ s, N c).FG ∧
      rk (zRealize b X (⨆ c ∈ s, N c)) = ∑ c ∈ s, rk (zRealize b X (N c)) ∧
      degHLat b X (⨆ c ∈ s, N c) = ∑ c ∈ s, degHLat b X (N c) ∧
      (s.Nonempty → (∀ c ∈ s, N c ≠ ⊥) →
        (∃ c ∈ s, muMaxO b X (⨆ c ∈ s, N c) = muMaxO b X (N c)) ∧
        (∀ c ∈ s, muMaxO b X (N c) ≤ muMaxO b X (⨆ c ∈ s, N c)) ∧
        (∃ c ∈ s, muMinO b X (⨆ c ∈ s, N c) = muMinO b X (N c)) ∧
        (∀ c ∈ s, muMinO b X (⨆ c ∈ s, N c) ≤ muMinO b X (N c))) := by
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨by simp [Submodule.fg_bot], ?_, ?_, fun hne => ?_⟩
    · rw [show (⨆ c ∈ (∅ : Finset γ), N c) = ⊥ by simp, zRealize_bot]
      simp [rk]
    · simp only [Finset.notMem_empty, iSup_false, iSup_bot, Finset.sum_empty]
      unfold degHLat; rw [zRealize_bot, degAr_bot]
    · exact absurd hne Finset.not_nonempty_empty
  | @insert a t hat ih =>
    have hNt_fg : ∀ c ∈ t, (N c).FG := fun c hc => hN_fg c (Finset.mem_insert_of_mem hc)
    have ht_orth : ∀ c ∈ t, ∀ c' ∈ t, c ≠ c' → ∀ x ∈ N c, ∀ y ∈ N c',
        inner ℝ (realizeHLat b X x) (realizeHLat b X y) = 0 :=
      fun c hc c' hc' hne => horth c (Finset.mem_insert_of_mem hc) c' (Finset.mem_insert_of_mem hc') hne
    obtain ⟨ht_fg, ht_rk, ht_deg, ht_mu⟩ := ih hNt_fg ht_orth
    have ha_fg : (N a).FG := hN_fg a (Finset.mem_insert_self a t)
    have ha_orth : ∀ x ∈ N a, ∀ y ∈ ⨆ c ∈ t, N c,
        inner ℝ (realizeHLat b X x) (realizeHLat b X y) = 0 :=
      fun x hx y hy => inner_realize_orthog_biSup b X a t hat N (fun c hc =>
        horth a (Finset.mem_insert_self a t) c (Finset.mem_insert_of_mem hc) (fun h => hat (h ▸ hc)))
        hx hy
    obtain ⟨hsup_rk, hsup_deg, hsup_mu⟩ :=
      hlat_orthog_two_sum b X hX (N a) (⨆ c ∈ t, N c) ha_fg ht_fg ha_orth
    simp_rw [biSup_insert_finset, Finset.sum_insert hat]
    refine ⟨ha_fg.sup ht_fg, hsup_rk.trans (by rw [ht_rk]), hsup_deg.trans (by rw [ht_deg]), ?_⟩
    intro _ hne_all
    by_cases ht_emp : t = ⊥
    · subst ht_emp
      have hbot : (⨆ c ∈ (⊥ : Finset γ), N c) = ⊥ :=
        iSup₂_eq_bot.mpr fun c hc => absurd hc (Finset.notMem_empty c)
      rw [hbot, sup_bot_eq]
      refine ⟨⟨a, Finset.mem_insert_self a ⊥, rfl⟩, fun c hc => ?_,
        ⟨a, Finset.mem_insert_self a ⊥, rfl⟩, fun c hc => ?_⟩
      · rw [Finset.mem_insert] at hc
        rcases hc with rfl | hc
        · exact le_rfl
        · exact False.elim (Finset.notMem_empty c hc)
      · rw [Finset.mem_insert] at hc
        rcases hc with rfl | hc
        · exact le_rfl
        · exact False.elim (Finset.notMem_empty c hc)
    · have ht_ne : t.Nonempty := Finset.nonempty_iff_ne_empty.mpr ht_emp
      have ht_ne_all : ∀ c ∈ t, N c ≠ ⊥ := fun c hc => hne_all c (Finset.mem_insert_of_mem hc)
      obtain ⟨⟨c₁, hc₁, hc₁_eq⟩, hc₁_le, ⟨c₂, hc₂, hc₂_eq⟩, hc₂_le⟩ := ht_mu ht_ne ht_ne_all
      have ha0 : N a ≠ ⊥ := hne_all a (Finset.mem_insert_self a t)
      have hM0 : (⨆ c ∈ t, N c) ≠ ⊥ := by
        obtain ⟨c₀, hc₀⟩ := ht_ne
        intro hbot
        apply ht_ne_all c₀ hc₀
        exact eq_bot_iff.mpr (hbot ▸ le_biSup N hc₀)
      obtain ⟨hmax_eq, hmin_eq⟩ := hsup_mu ha0 hM0
      refine ⟨?_, ?_, ?_, ?_⟩
      · rcases le_total (muMaxO b X (N a)) (muMaxO b X (⨆ c ∈ t, N c)) with hle | hle
        · refine ⟨c₁, Finset.mem_insert_of_mem hc₁, ?_⟩
          rw [hmax_eq, max_eq_right hle, hc₁_eq]
        · refine ⟨a, Finset.mem_insert_self a t, ?_⟩
          rw [hmax_eq, max_eq_left hle]
      · intro c hc
        rw [hmax_eq]
        rcases Finset.mem_insert.mp hc with rfl | hct
        · exact le_max_left _ _
        · exact (hc₁_le c hct).trans (le_max_right _ _)
      · rcases le_total (muMinO b X (N a)) (muMinO b X (⨆ c ∈ t, N c)) with hle | hle
        · refine ⟨a, Finset.mem_insert_self a t, ?_⟩
          rw [hmin_eq, min_eq_left hle]
        · refine ⟨c₂, Finset.mem_insert_of_mem hc₂, ?_⟩
          rw [hmin_eq, min_eq_right hle, hc₂_eq]
      · intro c hc
        rw [hmin_eq]
        rcases Finset.mem_insert.mp hc with rfl | hct
        · exact min_le_left _ _
        · exact (min_le_right _ _).trans (hc₂_le c hct)

/-- **Normalized Slope Formulas for Indexed Orthogonal Direct Sums** (`muDef`, `muMaxDef`, `muMinDef`),
matching Alpöge's `BrzoPairAtZeroRight.hlat_orth_sum`. -/
theorem hlat_orthog_direct_sum_normalized {γ : Type*} [DecidableEq γ]
    (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (s : Finset γ) (N : γ → Submodule (𝓞 K) V)
    (hN_fg : ∀ c ∈ s, (N c).FG)
    (horth : ∀ c ∈ s, ∀ c' ∈ s, c ≠ c' → ∀ x ∈ N c, ∀ y ∈ N c',
      inner ℝ (realizeHLat b X x) (realizeHLat b X y) = 0) :
    rkK (K := K) (⨆ c ∈ s, N c) = ∑ c ∈ s, rkK (K := K) (N c) ∧
      (s.Nonempty → (∀ c ∈ s, N c ≠ ⊥) →
        muDef b X (⨆ c ∈ s, N c) * (∑ c ∈ s, (rkK (K := K) (N c) : ℝ)) =
          ∑ c ∈ s, muDef b X (N c) * (rkK (K := K) (N c) : ℝ)) ∧
      (s.Nonempty → (∀ c ∈ s, N c ≠ ⊥) →
        (∃ c ∈ s, muMaxDef b X (⨆ c ∈ s, N c) = muMaxDef b X (N c)) ∧
        (∀ c ∈ s, muMaxDef b X (N c) ≤ muMaxDef b X (⨆ c ∈ s, N c)) ∧
        (∃ c ∈ s, muMinDef b X (⨆ c ∈ s, N c) = muMinDef b X (N c)) ∧
        (∀ c ∈ s, muMinDef b X (⨆ c ∈ s, N c) ≤ muMinDef b X (N c))) := by
  obtain ⟨hsup_fg, hrk_sum, hdeg_sum, hmu⟩ :=
    hlat_orthog_direct_sum b X hX s N hN_fg horth
  haveI : ∀ c ∈ s, DiscreteTopology (zRealize b X (N c)) :=
    fun c hc => discreteTopology_zRealize_of_fg b X hX (N c) (hN_fg c hc)
  haveI : DiscreteTopology (zRealize b X (⨆ c ∈ s, N c)) :=
    discreteTopology_zRealize_of_fg b X hX _ hsup_fg
  have hn_pos : 0 < Module.finrank ℚ K := Module.finrank_pos
  have hrkK_sum : rkK (K := K) (⨆ c ∈ s, N c) = ∑ c ∈ s, rkK (K := K) (N c) := by
    have hmul : Module.finrank ℚ K * rkK (K := K) (⨆ c ∈ s, N c) =
        Module.finrank ℚ K * ∑ c ∈ s, rkK (K := K) (N c) := by
      rw [← rk_zRealize_eq b X hX _ hsup_fg, hrk_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun c hc => rk_zRealize_eq b X hX (N c) (hN_fg c hc)
    exact Nat.eq_of_mul_eq_mul_left hn_pos hmul
  refine ⟨hrkK_sum, ?_, ?_⟩
  · intro hs_ne hne_all
    have hmu_term : ∀ (M : Submodule (𝓞 K) V), M.FG → M ≠ ⊥ →
        muDef b X M * (rkK (K := K) M : ℝ) =
          (2 / (Module.finrank ℚ K : ℝ)) * degHLat b X M +
            (-Real.log 2 + logDiscDivDeg K) * (rkK (K := K) M : ℝ) := by
      intro M hM hM0
      haveI : DiscreteTopology (zRealize b X M) := discreteTopology_zRealize_of_fg b X hX M hM
      have hrk_pos : 0 < rkK (K := K) M := by
        have := rk_pos_of_ne_bot (zRealize b X M) (zRealize_ne_bot b X hX hM0)
        rw [rk_zRealize_eq b X hX M hM] at this
        exact Nat.pos_of_mul_pos_left this
      have hn_ne : (Module.finrank ℚ K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn_pos.ne'
      have hr_ne : (rkK (K := K) M : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hrk_pos.ne'
      unfold muDef slopeHLat ArakelovCovolume.slope degHLat
      rw [rk_zRealize_eq b X hX M hM]
      push_cast
      field_simp [hn_ne, hr_ne]
      ring
    have hsup_ne : (⨆ c ∈ s, N c) ≠ ⊥ := by
      obtain ⟨c₀, hc₀⟩ := hs_ne
      intro hbot
      exact hne_all c₀ hc₀ (eq_bot_iff.mpr (hbot ▸ le_biSup N hc₀))
    have hrkK_R : (rkK (K := K) (⨆ c ∈ s, N c) : ℝ) = ∑ c ∈ s, (rkK (K := K) (N c) : ℝ) := by
      exact_mod_cast hrkK_sum
    rw [← hrkK_R, hmu_term _ hsup_fg hsup_ne, hdeg_sum, hrkK_R]
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c hc => ?_
    exact (hmu_term (N c) (hN_fg c hc) (hne_all c hc)).symm
  · intro hs_ne hne_all
    obtain ⟨⟨c₁, hc₁, hc₁_eq⟩, hc₁_le, ⟨c₂, hc₂, hc₂_eq⟩, hc₂_le⟩ := hmu hs_ne hne_all
    refine ⟨⟨c₁, hc₁, ?_⟩, fun c hc => ?_, ⟨c₂, hc₂, ?_⟩, fun c hc => ?_⟩
    · unfold muMaxDef; rw [hc₁_eq]
    · unfold muMaxDef; linarith [hc₁_le c hc]
    · unfold muMinDef; rw [hc₂_eq]
    · unfold muMinDef; linarith [hc₂_le c hc]

/-- Equal-rank Fintype specialization of `hlat_orthog_direct_sum_normalized`:
when `∀ c : γ, rkK (N c) = r₀` with `0 < r₀`,
`mu (⨆ c, N c) = (∑ c, mu (N c)) / Fintype.card γ` and `∃ c, muMax (⨆ c, N c) ≤ muMax (N c)`. -/
theorem hlat_orthog_direct_sum_equal_rank {γ : Type*} [Fintype γ] [Nonempty γ] [DecidableEq γ]
    (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (N : γ → Submodule (𝓞 K) V)
    (r₀ : ℕ) (hr₀ : 0 < r₀) (hrk : ∀ c, rkK (K := K) (N c) = r₀)
    (hN_fg : ∀ c, (N c).FG)
    (horth : ∀ c c', c ≠ c' → ∀ x ∈ N c, ∀ y ∈ N c',
      inner ℝ (realizeHLat b X x) (realizeHLat b X y) = 0) :
    muDef b X (⨆ c, N c) = (∑ c, muDef b X (N c)) / (Fintype.card γ : ℝ) ∧
      (∃ c, muMaxDef b X (⨆ c, N c) = muMaxDef b X (N c)) ∧
      (∃ c, muMinDef b X (⨆ c, N c) = muMinDef b X (N c)) := by
  have hne_all : ∀ c ∈ (Finset.univ : Finset γ), N c ≠ ⊥ := by
    intro c _ hbot
    have h0 : rkK (K := K) (N c) = 0 := by unfold rkK; rw [hbot]; simp
    have hr := hrk c
    omega
  obtain ⟨_, hmu_w, hmu_ex⟩ :=
    hlat_orthog_direct_sum_normalized b X hX Finset.univ N (fun c _ => hN_fg c)
      (fun c _ c' _ hne => horth c c' hne)
  have hsup_eq : (⨆ c ∈ (Finset.univ : Finset γ), N c) = ⨆ c, N c := by simp
  rw [hsup_eq] at hmu_w
  obtain ⟨⟨c₁, _, hc₁_eq⟩, _, ⟨c₂, _, hc₂_eq⟩, _⟩ := hmu_ex Finset.univ_nonempty hne_all
  rw [hsup_eq] at hc₁_eq hc₂_eq
  have hw := hmu_w Finset.univ_nonempty hne_all
  have hr₀_ne : (r₀ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hr₀.ne'
  have hcard_ne : (Fintype.card γ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hsum_rk : ∑ c : γ, (rkK (K := K) (N c) : ℝ) = (Fintype.card γ : ℝ) * (r₀ : ℝ) := by
    simp [hrk, Finset.sum_const, nsmul_eq_mul]
  have hsum_mu : ∑ c : γ, muDef b X (N c) * (rkK (K := K) (N c) : ℝ) =
      (∑ c : γ, muDef b X (N c)) * (r₀ : ℝ) := by
    simp [hrk, ← Finset.sum_mul]
  rw [hsum_rk, hsum_mu] at hw
  have hmu_eq : muDef b X (⨆ c, N c) = (∑ c, muDef b X (N c)) / (Fintype.card γ : ℝ) := by
    field_simp [hr₀_ne, hcard_ne] at hw ⊢
    linarith
  exact ⟨hmu_eq, ⟨c₁, hc₁_eq⟩, ⟨c₂, hc₂_eq⟩⟩

end IndexedOrthogonal

section ExternalDirectSum

/-- **External Orthogonal Direct Sum `directSumHLat A B : HLat K`**:
product `K`-space `A.V × B.V`, basis `A.b.prod B.b`, block-diagonal frames
`Matrix.fromBlocks (A.X v) 0 0 (B.X v)`, and product `𝓞 K`-lattice `A.L.prod B.L`. -/
def directSumHLat {K : Type} [Field K] [NumberField K] [StarRing K] (A B : HLat K) : HLat K where
  V := A.V × B.V
  ι := A.ι ⊕ B.ι
  b := A.b.prod B.b
  X := fun v => Matrix.fromBlocks (A.X v) 0 0 (B.X v)
  L := A.L.prod B.L

lemma directSumHLat_frameOK {K : Type} [Field K] [NumberField K] [StarRing K] (A B : HLat K)
    (hA : HLat.FrameOK A) (hB : HLat.FrameOK B) :
    HLat.FrameOK (directSumHLat A B) := by
  intro v
  change IsUnit (Matrix.fromBlocks (A.X v) 0 0 (B.X v)).det
  rw [Matrix.det_fromBlocks_zero₁₂]
  exact (hA v).mul (hB v)

lemma directSumHLat_good {K : Type} [Field K] [NumberField K] [StarRing K] (A B : HLat K)
    (hA : A.Good) (hB : B.Good) : (directSumHLat A B).Good := by
  haveI : Module.Finite K A.V := Module.Finite.of_basis A.b
  haveI : Module.Finite K B.V := Module.Finite.of_basis B.b
  refine ⟨directSumHLat_frameOK A B hA.1 hB.1, ?_, ?_⟩
  · have heq : A.L.prod B.L =
        A.L.map (LinearMap.inl (𝓞 K) A.V B.V) ⊔ B.L.map (LinearMap.inr (𝓞 K) A.V B.V) := by
      ext ⟨x, y⟩
      simp only [Submodule.mem_prod, Submodule.mem_sup, Submodule.mem_map,
        LinearMap.inl_apply, LinearMap.inr_apply]
      constructor
      · rintro ⟨hx, hy⟩
        exact ⟨(x, 0), ⟨x, hx, rfl⟩, (0, y), ⟨y, hy, rfl⟩, by ext <;> simp⟩
      · rintro ⟨_, ⟨x', hx', rfl⟩, _, ⟨y', hy', rfl⟩, hxy⟩
        obtain ⟨rfl, rfl⟩ : x' = x ∧ y' = y := by simpa using Prod.ext_iff.mp hxy
        exact ⟨hx', hy'⟩
    change (A.L.prod B.L).FG
    rw [heq]
    exact (hA.2.1.map _).sup (hB.2.1.map _)
  · rw [eq_top_iff]
    rintro ⟨x, y⟩ _
    have hx : x ∈ Submodule.span K (A.L : Set A.V) := hA.2.2 ▸ trivial
    have hy : y ∈ Submodule.span K (B.L : Set B.V) := hB.2.2 ▸ trivial
    have hx_lift : ∀ z ∈ Submodule.span K (A.L : Set A.V),
        (z, (0 : B.V)) ∈ Submodule.span K ((A.L.prod B.L : Submodule (𝓞 K) (A.V × B.V)) :
          Set (A.V × B.V)) := by
      intro z hz
      induction hz using Submodule.span_induction with
      | mem a ha => exact Submodule.subset_span ⟨ha, B.L.zero_mem⟩
      | zero => exact Submodule.zero_mem _
      | add u w _ _ h₁ h₂ =>
        have heq : (u + w, (0 : B.V)) = (u, (0 : B.V)) + (w, (0 : B.V)) := by ext <;> simp
        rw [heq]; exact Submodule.add_mem _ h₁ h₂
      | smul c u _ h =>
        have heq : (c • u, (0 : B.V)) = c • (u, (0 : B.V)) := by ext <;> simp
        rw [heq]; exact Submodule.smul_mem _ c h
    have hy_lift : ∀ w ∈ Submodule.span K (B.L : Set B.V),
        ((0 : A.V), w) ∈ Submodule.span K ((A.L.prod B.L : Submodule (𝓞 K) (A.V × B.V)) :
          Set (A.V × B.V)) := by
      intro w hw
      induction hw using Submodule.span_induction with
      | mem b' hb' => exact Submodule.subset_span ⟨A.L.zero_mem, hb'⟩
      | zero => exact Submodule.zero_mem _
      | add u w _ _ h₁ h₂ =>
        have heq : ((0 : A.V), u + w) = ((0 : A.V), u) + ((0 : A.V), w) := by ext <;> simp
        rw [heq]; exact Submodule.add_mem _ h₁ h₂
      | smul c u _ h =>
        have heq : ((0 : A.V), c • u) = c • ((0 : A.V), u) := by ext <;> simp
        rw [heq]; exact Submodule.smul_mem _ c h
    have hsum : (x, y) = (x, (0 : B.V)) + ((0 : A.V), y) := by ext <;> simp
    change (x, y) ∈ Submodule.span K ((A.L.prod B.L : Submodule (𝓞 K) (A.V × B.V)) :
        Set (A.V × B.V))
    rw [hsum]
    exact Submodule.add_mem _ (hx_lift x hx) (hy_lift y hy)

private lemma directSumHLat_iso_inv {K : Type} [Field K] [NumberField K]
    {W₁ W₂ : Type*} [AddCommGroup W₁] [Module K W₁] [Module (𝓞 K) W₁]
    [IsScalarTower (𝓞 K) K W₁] [AddCommGroup W₂] [Module K W₂] [Module (𝓞 K) W₂]
    [IsScalarTower (𝓞 K) K W₂] {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁]
    [Fintype ι₂] [DecidableEq ι₂]
    (b₁ : Module.Basis ι₁ K W₁) (X₁ : InfinitePlace K → Matrix ι₁ ι₁ ℂ) (hX₁ : ∀ v, IsUnit (X₁ v).det)
    (b₂ : Module.Basis ι₂ K W₂) (X₂ : InfinitePlace K → Matrix ι₂ ι₂ ℂ) (hX₂ : ∀ v, IsUnit (X₂ v).det)
    (g : W₁ →ₗ[K] W₂)
    (φ : EuclideanSpace ℝ (InfinitePlace K × ι₁ × Fin 2) →ₗ[ℝ]
      EuclideanSpace ℝ (InfinitePlace K × ι₂ × Fin 2))
    (hφ_iso : ∀ u w, inner ℝ (φ u) (φ w) = inner ℝ u w)
    (hφ_real : ∀ x : W₁, realizeHLat b₂ X₂ (g x) = φ (realizeHLat b₁ X₁ x))
    (M : Submodule (𝓞 K) W₁) (hM : M.FG) :
    rk (zRealize b₂ X₂ (M.map (g.restrictScalars (𝓞 K)))) = rk (zRealize b₁ X₁ M) ∧
      degHLat b₂ X₂ (M.map (g.restrictScalars (𝓞 K))) = degHLat b₁ X₁ M := by
  have : DiscreteTopology (zRealize b₁ X₁ M) := discreteTopology_zRealize_of_fg b₁ X₁ hX₁ M hM
  have : DiscreteTopology (zRealize b₂ X₂ (M.map (g.restrictScalars (𝓞 K)))) :=
    discreteTopology_zRealize_of_fg b₂ X₂ hX₂ _ (hM.map _)
  have hmap : zRealize b₂ X₂ (M.map (g.restrictScalars (𝓞 K))) =
      (zRealize b₁ X₁ M).map (φ.restrictScalars ℤ) := by
    ext w
    change (∃ y ∈ M.map (g.restrictScalars (𝓞 K)), realizeHLat b₂ X₂ y = w) ↔
      (∃ u ∈ zRealize b₁ X₁ M, φ u = w)
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨realizeHLat b₁ X₁ x, ⟨x, hx, rfl⟩, (hφ_real x).symm⟩
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨g x, ⟨x, hx, rfl⟩, hφ_real x⟩
  obtain ⟨_, hrk, hcov⟩ := covol_map_scaled φ 1 zero_lt_one (fun u w => by simp [hφ_iso u w])
    (zRealize b₁ X₁ M)
  refine ⟨by rw [hmap, hrk], ?_⟩
  unfold degHLat degAr
  rw [hmap, hcov, one_pow, one_mul]

private lemma directSumHLat_iso_slopes {K : Type} [Field K] [NumberField K]
    {W₁ W₂ : Type*} [AddCommGroup W₁] [Module K W₁] [Module (𝓞 K) W₁]
    [IsScalarTower (𝓞 K) K W₁] [AddCommGroup W₂] [Module K W₂] [Module (𝓞 K) W₂]
    [IsScalarTower (𝓞 K) K W₂] {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁]
    [Fintype ι₂] [DecidableEq ι₂]
    (b₁ : Module.Basis ι₁ K W₁) (X₁ : InfinitePlace K → Matrix ι₁ ι₁ ℂ) (hX₁ : ∀ v, IsUnit (X₁ v).det)
    (b₂ : Module.Basis ι₂ K W₂) (X₂ : InfinitePlace K → Matrix ι₂ ι₂ ℂ) (hX₂ : ∀ v, IsUnit (X₂ v).det)
    (g : W₁ →ₗ[K] W₂) (hg_inj : Function.Injective g)
    (φ : EuclideanSpace ℝ (InfinitePlace K × ι₁ × Fin 2) →ₗ[ℝ]
      EuclideanSpace ℝ (InfinitePlace K × ι₂ × Fin 2))
    (hφ_iso : ∀ u w, inner ℝ (φ u) (φ w) = inner ℝ u w)
    (hφ_real : ∀ x : W₁, realizeHLat b₂ X₂ (g x) = φ (realizeHLat b₁ X₁ x))
    (L₁ : Submodule (𝓞 K) W₁) (hL₁ : L₁.FG) :
    slopesO b₂ X₂ (L₁.map (g.restrictScalars (𝓞 K))) = slopesO b₁ X₁ L₁ := by
  let gO := g.restrictScalars (𝓞 K)
  have hgO_inj : Function.Injective gO := hg_inj
  ext t
  constructor
  · rintro ⟨N', hN'L, hN'0, rfl⟩
    let N := N'.comap gO
    have hNN' : N.map gO = N' := by
      ext y
      simp only [Submodule.mem_map, Submodule.mem_comap, N]
      constructor
      · rintro ⟨x, hx, rfl⟩; exact hx
      · intro hy
        obtain ⟨x, _, rfl⟩ := hN'L hy
        exact ⟨x, hy, rfl⟩
    have hNL : N ≤ L₁ := by
      intro x hx
      rcases hN'L hx with ⟨y, hyL, hyx⟩
      rwa [← hgO_inj hyx]
    have hN0 : N ≠ ⊥ := fun h0 => hN'0 (by rw [← hNN', h0, Submodule.map_bot])
    have hNfg : N.FG := Submodule.FG.of_le hL₁ hNL
    obtain ⟨hrk, hdeg⟩ := directSumHLat_iso_inv b₁ X₁ hX₁ b₂ X₂ hX₂ g φ hφ_iso hφ_real N hNfg
    rw [show N.map (g.restrictScalars (𝓞 K)) = N' from hNN'] at hrk hdeg
    refine ⟨N, hNL, hN0, ?_⟩
    show slopeHLat b₁ X₁ N = slopeHLat b₂ X₂ N'
    unfold slopeHLat ArakelovCovolume.slope
    change degHLat b₁ X₁ N / (rk (zRealize b₁ X₁ N) : ℝ) =
      degHLat b₂ X₂ N' / (rk (zRealize b₂ X₂ N') : ℝ)
    rw [hrk, hdeg]
  · rintro ⟨N, hNL, hN0, rfl⟩
    let N' := N.map gO
    have hN'L : N' ≤ L₁.map gO := Submodule.map_mono hNL
    have hN'0 : N' ≠ ⊥ := by
      intro h0; apply hN0; rw [eq_bot_iff]; intro x hxN
      have hmem : gO x ∈ N' := ⟨x, hxN, rfl⟩
      rw [h0, Submodule.mem_bot] at hmem
      exact hgO_inj (hmem.trans (map_zero gO).symm)
    have hNfg : N.FG := Submodule.FG.of_le hL₁ hNL
    obtain ⟨hrk, hdeg⟩ := directSumHLat_iso_inv b₁ X₁ hX₁ b₂ X₂ hX₂ g φ hφ_iso hφ_real N hNfg
    refine ⟨N', hN'L, hN'0, ?_⟩
    show slopeHLat b₂ X₂ N' = slopeHLat b₁ X₁ N
    unfold slopeHLat ArakelovCovolume.slope
    change degHLat b₂ X₂ N' / (rk (zRealize b₂ X₂ N') : ℝ) =
      degHLat b₁ X₁ N / (rk (zRealize b₁ X₁ N) : ℝ)
    rw [hrk, hdeg]

private lemma directSumHLat_iso_muMinO {K : Type} [Field K] [NumberField K]
    {W₁ W₂ : Type*} [AddCommGroup W₁] [Module K W₁] [Module (𝓞 K) W₁]
    [IsScalarTower (𝓞 K) K W₁] [AddCommGroup W₂] [Module K W₂] [Module (𝓞 K) W₂]
    [IsScalarTower (𝓞 K) K W₂] {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁]
    [Fintype ι₂] [DecidableEq ι₂]
    (b₁ : Module.Basis ι₁ K W₁) (X₁ : InfinitePlace K → Matrix ι₁ ι₁ ℂ) (hX₁ : ∀ v, IsUnit (X₁ v).det)
    (b₂ : Module.Basis ι₂ K W₂) (X₂ : InfinitePlace K → Matrix ι₂ ι₂ ℂ) (hX₂ : ∀ v, IsUnit (X₂ v).det)
    (g : W₁ →ₗ[K] W₂) (hg_inj : Function.Injective g)
    (φ : EuclideanSpace ℝ (InfinitePlace K × ι₁ × Fin 2) →ₗ[ℝ]
      EuclideanSpace ℝ (InfinitePlace K × ι₂ × Fin 2))
    (hφ_iso : ∀ u w, inner ℝ (φ u) (φ w) = inner ℝ u w)
    (hφ_real : ∀ x : W₁, realizeHLat b₂ X₂ (g x) = φ (realizeHLat b₁ X₁ x))
    (L₁ : Submodule (𝓞 K) W₁) (hL₁ : L₁.FG) (hL₁_ne : L₁ ≠ ⊥) :
    muMinO b₂ X₂ (L₁.map (g.restrictScalars (𝓞 K))) = muMinO b₁ X₁ L₁ := by
  let gO := g.restrictScalars (𝓞 K)
  have hL₁'_fg : (L₁.map gO).FG := hL₁.map _
  have hL₁'_ne : L₁.map gO ≠ ⊥ := by
    intro h0; apply hL₁_ne; rw [eq_bot_iff]; intro x hx
    have hm : gO x ∈ L₁.map gO := ⟨x, hx, rfl⟩
    rw [h0, Submodule.mem_bot] at hm; exact hg_inj (hm.trans (map_zero gO).symm)
  obtain ⟨hrkL, hdegL⟩ := directSumHLat_iso_inv b₁ X₁ hX₁ b₂ X₂ hX₂ g φ hφ_iso hφ_real L₁ hL₁
  apply le_antisymm
  · rw [muMinO_char b₁ X₁ hX₁ L₁ hL₁ hL₁_ne]
    intro N hNL
    have hNfg : N.FG := Submodule.FG.of_le hL₁ hNL
    obtain ⟨hrkN, hdegN⟩ := directSumHLat_iso_inv b₁ X₁ hX₁ b₂ X₂ hX₂ g φ hφ_iso hφ_real N hNfg
    have hmin := (muMinO_char b₂ X₂ hX₂ (L₁.map gO) hL₁'_fg hL₁'_ne
      (muMinO b₂ X₂ (L₁.map gO))).mp le_rfl (N.map gO) (Submodule.map_mono hNL)
    rw [hrkL, hdegL, hrkN, hdegN] at hmin
    exact hmin
  · rw [muMinO_char b₂ X₂ hX₂ (L₁.map gO) hL₁'_fg hL₁'_ne]
    intro N' hN'
    let N := N'.comap gO
    have hNN' : N.map gO = N' := by
      ext y; simp only [Submodule.mem_map, Submodule.mem_comap, N]
      exact ⟨fun ⟨x, hx, hxy⟩ => hxy ▸ hx, fun hy => by obtain ⟨x, _, rfl⟩ := hN' hy; exact ⟨x, hy, rfl⟩⟩
    have hNL : N ≤ L₁ := fun x hx => by rcases hN' hx with ⟨y, hy, hyx⟩; rwa [← hg_inj hyx]
    have hNfg : N.FG := Submodule.FG.of_le hL₁ hNL
    obtain ⟨hrkN, hdegN⟩ := directSumHLat_iso_inv b₁ X₁ hX₁ b₂ X₂ hX₂ g φ hφ_iso hφ_real N hNfg
    rw [show N.map (g.restrictScalars (𝓞 K)) = N' from hNN'] at hrkN hdegN
    have hmin := (muMinO_char b₁ X₁ hX₁ L₁ hL₁ hL₁_ne (muMinO b₁ X₁ L₁)).mp le_rfl N hNL
    rw [hrkL, hdegL, hrkN, hdegN]
    exact hmin

/-- Exact invariants of `directSumHLat A B` (`rk`, `rank`, `degHLat`, `covol`, `muMax`, `muMin`, `mu`). -/
theorem directSumHLat_invariants {K : Type} [Field K] [NumberField K] [StarRing K] (A B : HLat K)
    (hA : A.Good) (hB : B.Good) :
    rk (directSumHLat A B).zRealize = rk A.zRealize + rk B.zRealize ∧
      (directSumHLat A B).rank = A.rank + B.rank ∧
      degHLat (directSumHLat A B).b (directSumHLat A B).X (directSumHLat A B).L =
        degHLat A.b A.X A.L + degHLat B.b B.X B.L ∧
      covol (directSumHLat A B).zRealize = covol A.zRealize * covol B.zRealize ∧
      (A.L ≠ ⊥ → B.L ≠ ⊥ →
        (directSumHLat A B).muMax = max A.muMax B.muMax ∧
        (directSumHLat A B).muMin = min A.muMin B.muMin ∧
        (directSumHLat A B).mu * ((A.rank : ℝ) + B.rank) =
          A.mu * A.rank + B.mu * B.rank) := by
  classical
  haveI : Module.Finite K A.V := Module.Finite.of_basis A.b
  haveI : Module.Finite K B.V := Module.Finite.of_basis B.b
  have hG := directSumHLat_good A B hA hB
  let D := directSumHLat A B
  have hXinv : ∀ v, (D.X v)⁻¹ = Matrix.fromBlocks (A.X v)⁻¹ 0 0 (B.X v)⁻¹ := by
    intro v
    apply Matrix.inv_eq_right_inv
    change Matrix.fromBlocks (A.X v) 0 0 (B.X v) *
      Matrix.fromBlocks (A.X v)⁻¹ 0 0 (B.X v)⁻¹ = 1
    rw [Matrix.fromBlocks_multiply]
    simp [Matrix.mul_nonsing_inv _ (hA.1 v), Matrix.mul_nonsing_inv _ (hB.1 v),
      Matrix.fromBlocks_one]
  have hfcoord : ∀ (v : InfinitePlace K) (x : A.V) (y : B.V),
      (∀ i, fcoord D.b D.X v (x, y) (Sum.inl i) = fcoord A.b A.X v x i) ∧
      (∀ j, fcoord D.b D.X v (x, y) (Sum.inr j) = fcoord B.b B.X v y j) := by
    intro v x y
    have hvec : RHDirect.Stage12SchurWeylLattices.vecAt D.b v (x, y) =
        Sum.elim (RHDirect.Stage12SchurWeylLattices.vecAt A.b v x)
          (RHDirect.Stage12SchurWeylLattices.vecAt B.b v y) := by
      have hxy : (x, y) = ∑ i : A.ι, A.b.repr x i • (A.b.prod B.b) (Sum.inl i) +
          ∑ j : B.ι, B.b.repr y j • (A.b.prod B.b) (Sum.inr j) := by
        ext
        · conv_lhs => rw [← A.b.sum_repr x]
          simp [Module.Basis.prod_apply, Prod.fst_sum]
        · conv_lhs => rw [← B.b.sum_repr y]
          simp [Module.Basis.prod_apply, Prod.snd_sum]
      have hrepr : ∀ k : A.ι ⊕ B.ι, (A.b.prod B.b).repr (x, y) k =
          Sum.elim (A.b.repr x) (B.b.repr y) k := by
        intro k
        conv_lhs => rw [hxy]
        rw [map_add, map_sum, map_sum]
        cases k with
        | inl i =>
          simp only [map_smul, Module.Basis.repr_self, Finsupp.coe_add, Finsupp.coe_finsetSum,
            Finsupp.coe_smul, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
            Finsupp.single_apply, Sum.elim_inl]
          simp [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ]
        | inr j =>
          simp only [map_smul, Module.Basis.repr_self, Finsupp.coe_add, Finsupp.coe_finsetSum,
            Finsupp.coe_smul, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
            Finsupp.single_apply, Sum.elim_inr]
          simp [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ]
      ext k
      cases k with
      | inl i =>
        simp only [RHDirect.Stage12SchurWeylLattices.vecAt, Sum.elim_inl]
        exact congrArg v.embedding (hrepr (Sum.inl i))
      | inr j =>
        simp only [RHDirect.Stage12SchurWeylLattices.vecAt, Sum.elim_inr]
        exact congrArg v.embedding (hrepr (Sum.inr j))
    have hmul : (D.X v)⁻¹ *ᵥ RHDirect.Stage12SchurWeylLattices.vecAt D.b v (x, y) =
        Sum.elim ((A.X v)⁻¹ *ᵥ RHDirect.Stage12SchurWeylLattices.vecAt A.b v x)
          ((B.X v)⁻¹ *ᵥ RHDirect.Stage12SchurWeylLattices.vecAt B.b v y) := by
      rw [hXinv v, hvec]
      ext k
      cases k with
      | inl i =>
        unfold Matrix.mulVec dotProduct
        erw [Fintype.sum_sum_type]
        simp
      | inr j =>
        unfold Matrix.mulVec dotProduct
        erw [Fintype.sum_sum_type]
        simp
    constructor
    · intro i
      unfold fcoord RHDirect.Stage12SchurWeylLattices.fcoord
      exact congrFun hmul (Sum.inl i)
    · intro j
      unfold fcoord RHDirect.Stage12SchurWeylLattices.fcoord
      exact congrFun hmul (Sum.inr j)
  -- Isometric embeddings `φA : E_A →ₗᵢ[ℝ] E_D` and `φB : E_B →ₗᵢ[ℝ] E_D`
  let φA : EuclideanSpace ℝ (InfinitePlace K × A.ι × Fin 2) →ₗ[ℝ]
      EuclideanSpace ℝ (InfinitePlace K × D.ι × Fin 2) :=
    { toFun := fun w => WithLp.toLp 2 fun p => match p.2.1 with
        | Sum.inl i => w (p.1, i, p.2.2)
        | Sum.inr _ => 0
      map_add' := fun u v => by ext ⟨p, k, r⟩; cases k <;> simp
      map_smul' := fun c u => by ext ⟨p, k, r⟩; cases k <;> simp }
  let φB : EuclideanSpace ℝ (InfinitePlace K × B.ι × Fin 2) →ₗ[ℝ]
      EuclideanSpace ℝ (InfinitePlace K × D.ι × Fin 2) :=
    { toFun := fun w => WithLp.toLp 2 fun p => match p.2.1 with
        | Sum.inl _ => 0
        | Sum.inr j => w (p.1, j, p.2.2)
      map_add' := fun u v => by ext ⟨p, k, r⟩; cases k <;> simp
      map_smul' := fun c u => by ext ⟨p, k, r⟩; cases k <;> simp }
  have hφA_real : ∀ x : A.V, realizeHLat D.b D.X (x, 0) = φA (realizeHLat A.b A.X x) := by
    intro x
    ext ⟨v, k, r⟩
    cases k with
    | inl i =>
      change (if r = 0 then (fcoord D.b D.X v (x, (0 : B.V)) (Sum.inl i)).re
        else (fcoord D.b D.X v (x, (0 : B.V)) (Sum.inl i)).im) = _
      rw [(hfcoord v x 0).1 i]
      rfl
    | inr j =>
      have h0 : fcoord B.b B.X v (0 : B.V) j = 0 := by
        unfold fcoord RHDirect.Stage12SchurWeylLattices.fcoord
        have : RHDirect.Stage12SchurWeylLattices.vecAt B.b v (0 : B.V) = 0 := by
          funext t; simp [RHDirect.Stage12SchurWeylLattices.vecAt]
        rw [this, Matrix.mulVec_zero]; rfl
      change (if r = 0 then (fcoord D.b D.X v (x, (0 : B.V)) (Sum.inr j)).re
        else (fcoord D.b D.X v (x, (0 : B.V)) (Sum.inr j)).im) = 0
      rw [(hfcoord v x 0).2 j, h0]
      simp
  have hφB_real : ∀ y : B.V, realizeHLat D.b D.X (0, y) = φB (realizeHLat B.b B.X y) := by
    intro y
    ext ⟨v, k, r⟩
    cases k with
    | inl i =>
      have h0 : fcoord A.b A.X v (0 : A.V) i = 0 := by
        unfold fcoord RHDirect.Stage12SchurWeylLattices.fcoord
        have : RHDirect.Stage12SchurWeylLattices.vecAt A.b v (0 : A.V) = 0 := by
          funext t; simp [RHDirect.Stage12SchurWeylLattices.vecAt]
        rw [this, Matrix.mulVec_zero]; rfl
      change (if r = 0 then (fcoord D.b D.X v ((0 : A.V), y) (Sum.inl i)).re
        else (fcoord D.b D.X v ((0 : A.V), y) (Sum.inl i)).im) = 0
      rw [(hfcoord v 0 y).1 i, h0]
      simp
    | inr j =>
      change (if r = 0 then (fcoord D.b D.X v ((0 : A.V), y) (Sum.inr j)).re
        else (fcoord D.b D.X v ((0 : A.V), y) (Sum.inr j)).im) = _
      rw [(hfcoord v 0 y).2 j]
      rfl
  have hφA_iso : ∀ u w, inner ℝ (φA u) (φA w) = inner ℝ u w := by
    intro u w
    simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, star_trivial,
      Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun v _ => ?_
    erw [Fintype.sum_sum_type]
    simp [φA]
  have hφB_iso : ∀ u w, inner ℝ (φB u) (φB w) = inner ℝ u w := by
    intro u w
    simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, star_trivial,
      Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun v _ => ?_
    erw [Fintype.sum_sum_type]
    simp [φB]
  have horth_AB : ∀ u w, inner ℝ (φA u) (φB w) = 0 := by
    intro u w
    simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, star_trivial,
      Fintype.sum_prod_type]
    refine Finset.sum_eq_zero fun v _ => ?_
    erw [Fintype.sum_sum_type]
    simp [φA, φB]
  let LA' : Submodule (𝓞 K) (A.V × B.V) := A.L.map (LinearMap.inl (𝓞 K) A.V B.V)
  let LB' : Submodule (𝓞 K) (A.V × B.V) := B.L.map (LinearMap.inr (𝓞 K) A.V B.V)
  have hD_sup : (D.L : Submodule (𝓞 K) (A.V × B.V)) = LA' ⊔ LB' := by
    ext ⟨x, y⟩
    show (x, y) ∈ A.L.prod B.L ↔ (x, y) ∈ LA' ⊔ LB'
    simp only [Submodule.mem_prod, Submodule.mem_sup, Submodule.mem_map,
      LinearMap.inl_apply, LinearMap.inr_apply, LA', LB']
    constructor
    · rintro ⟨hx, hy⟩
      exact ⟨(x, 0), ⟨x, hx, rfl⟩, (0, y), ⟨y, hy, rfl⟩, by ext <;> simp⟩
    · rintro ⟨_, ⟨x', hx', rfl⟩, _, ⟨y', hy', rfl⟩, hxy⟩
      obtain ⟨rfl, rfl⟩ : x' = x ∧ y' = y := by simpa using Prod.ext_iff.mp hxy
      exact ⟨hx', hy'⟩
  have horth_mod : ∀ x ∈ LA', ∀ y ∈ LB', inner ℝ (realizeHLat D.b D.X x) (realizeHLat D.b D.X y) = 0 := by
    rintro _ ⟨a, _, rfl⟩ _ ⟨b', _, rfl⟩
    change inner ℝ (realizeHLat D.b D.X (a, (0 : B.V))) (realizeHLat D.b D.X ((0 : A.V), b')) = 0
    rw [hφA_real, hφB_real]
    exact horth_AB _ _
  have hLA'_fg : LA'.FG := hA.2.1.map _
  have hLB'_fg : LB'.FG := hB.2.1.map _
  haveI : DiscreteTopology A.zRealize := discreteTopology_zRealize_of_fg A.b A.X hA.1 A.L hA.2.1
  haveI : DiscreteTopology B.zRealize := discreteTopology_zRealize_of_fg B.b B.X hB.1 B.L hB.2.1
  haveI : DiscreteTopology D.zRealize := discreteTopology_zRealize_of_fg D.b D.X hG.1 D.L hG.2.1
  let XD : InfinitePlace K → Matrix (A.ι ⊕ B.ι) (A.ι ⊕ B.ι) ℂ :=
    fun v => Matrix.fromBlocks (A.X v) 0 0 (B.X v)
  have hXD : ∀ v, IsUnit (XD v).det := directSumHLat_frameOK A B hA.1 hB.1
  have hLA'_inv := directSumHLat_iso_inv A.b A.X hA.1 (A.b.prod B.b) XD hXD
    (LinearMap.inl K A.V B.V) φA hφA_iso hφA_real A.L hA.2.1
  have hLB'_inv := directSumHLat_iso_inv B.b B.X hB.1 (A.b.prod B.b) XD hXD
    (LinearMap.inr K A.V B.V) φB hφB_iso hφB_real B.L hB.2.1
  obtain ⟨hsup_rk, hsup_deg, hsup_mu⟩ :=
    hlat_orthog_two_sum (A.b.prod B.b) XD hXD LA' LB' hLA'_fg hLB'_fg horth_mod
  have hLA'_eq : A.L.map ((LinearMap.inl K A.V B.V).restrictScalars (𝓞 K)) = LA' := rfl
  have hLB'_eq : B.L.map ((LinearMap.inr K A.V B.V).restrictScalars (𝓞 K)) = LB' := rfl
  rw [hLA'_eq] at hLA'_inv
  rw [hLB'_eq] at hLB'_inv
  have hD_rk : rk D.zRealize = rk A.zRealize + rk B.zRealize := by
    change rk (zRealize (A.b.prod B.b) XD D.L) = rk A.zRealize + rk B.zRealize
    rw [hD_sup, hsup_rk, hLA'_inv.1, hLB'_inv.1]
  have hD_deg : degHLat D.b D.X D.L = degHLat A.b A.X A.L + degHLat B.b B.X B.L := by
    change degHLat (A.b.prod B.b) XD (A.L.prod B.L) = degHLat A.b A.X A.L + degHLat B.b B.X B.L
    rw [show (A.L.prod B.L : Submodule (𝓞 K) (A.V × B.V)) = LA' ⊔ LB' from hD_sup,
      hsup_deg, hLA'_inv.2, hLB'_inv.2]
  have hn_pos : 0 < Module.finrank ℚ K := Module.finrank_pos
  have hD_rank : D.rank = A.rank + B.rank := by
    unfold HLat.rank
    have hmul : Module.finrank ℚ K * rkK (K := K) D.L =
        Module.finrank ℚ K * (rkK (K := K) A.L + rkK (K := K) B.L) := by
      rw [← rk_zRealize_eq D.b D.X hG.1 D.L hG.2.1, mul_add,
        ← rk_zRealize_eq A.b A.X hA.1 A.L hA.2.1, ← rk_zRealize_eq B.b B.X hB.1 B.L hB.2.1]
      exact hD_rk
    exact Nat.eq_of_mul_eq_mul_left hn_pos hmul
  have hD_cov : covol D.zRealize = covol A.zRealize * covol B.zRealize := by
    have hlog : Real.log (covol D.zRealize) = Real.log (covol A.zRealize * covol B.zRealize) := by
      have h1 : degAr D.zRealize = degAr A.zRealize + degAr B.zRealize := hD_deg
      unfold degAr at h1
      rw [Real.log_mul (covol_pos A.zRealize).ne' (covol_pos B.zRealize).ne']
      linarith
    exact Real.log_injOn_pos (covol_pos D.zRealize) (mul_pos (covol_pos A.zRealize) (covol_pos B.zRealize)) hlog
  refine ⟨hD_rk, hD_rank, hD_deg, hD_cov, fun hA0 hB0 => ?_⟩
  have hLA'_ne : LA' ≠ ⊥ := by
    intro h0
    apply hA0
    rw [eq_bot_iff]
    intro a ha
    have hmem : (a, (0 : B.V)) ∈ LA' := ⟨a, ha, rfl⟩
    rw [h0, Submodule.mem_bot] at hmem
    exact (Prod.ext_iff.mp hmem).1
  have hLB'_ne : LB' ≠ ⊥ := by
    intro h0
    apply hB0
    rw [eq_bot_iff]
    intro b' hb'
    have hmem : ((0 : A.V), b') ∈ LB' := ⟨b', hb', rfl⟩
    rw [h0, Submodule.mem_bot] at hmem
    exact (Prod.ext_iff.mp hmem).2
  obtain ⟨hmax_sup, hmin_sup⟩ := hsup_mu hLA'_ne hLB'_ne
  have hA_sl := directSumHLat_iso_slopes A.b A.X hA.1 (A.b.prod B.b) XD hXD
    (LinearMap.inl K A.V B.V) (fun a₁ a₂ h => (Prod.ext_iff.mp h).1)
    φA hφA_iso hφA_real A.L hA.2.1
  have hB_sl := directSumHLat_iso_slopes B.b B.X hB.1 (A.b.prod B.b) XD hXD
    (LinearMap.inr K A.V B.V) (fun b₁ b₂ h => (Prod.ext_iff.mp h).2)
    φB hφB_iso hφB_real B.L hB.2.1
  have hmuMax_LA' : muMaxO (A.b.prod B.b) XD LA' = muMaxO A.b A.X A.L := by
    unfold muMaxO
    rw [← hLA'_eq, hA_sl]
  have hmuMax_LB' : muMaxO (A.b.prod B.b) XD LB' = muMaxO B.b B.X B.L := by
    unfold muMaxO
    rw [← hLB'_eq, hB_sl]
  have h_muMax : D.muMax = max A.muMax B.muMax := by
    change muMaxDef (A.b.prod B.b) XD (A.L.prod B.L) = max (muMaxDef A.b A.X A.L) (muMaxDef B.b B.X B.L)
    unfold muMaxDef
    rw [show (A.L.prod B.L : Submodule (𝓞 K) (A.V × B.V)) = LA' ⊔ LB' from hD_sup,
      hmax_sup, hmuMax_LA', hmuMax_LB']
    have h1 : ∀ a b c d : ℝ, 2 * max a b - c + d = max (2 * a - c + d) (2 * b - c + d) := by
      intro a b c d; rcases le_total a b with h | h <;> simp [h]
    exact h1 _ _ _ _
  have hmuMin_LA' := directSumHLat_iso_muMinO A.b A.X hA.1 (A.b.prod B.b) XD hXD
    (LinearMap.inl K A.V B.V) (fun a₁ a₂ h => (Prod.ext_iff.mp h).1)
    φA hφA_iso hφA_real A.L hA.2.1 hA0
  have hmuMin_LB' := directSumHLat_iso_muMinO B.b B.X hB.1 (A.b.prod B.b) XD hXD
    (LinearMap.inr K A.V B.V) (fun b₁ b₂ h => (Prod.ext_iff.mp h).2)
    φB hφB_iso hφB_real B.L hB.2.1 hB0
  have h_muMin : D.muMin = min A.muMin B.muMin := by
    change muMinDef (A.b.prod B.b) XD (A.L.prod B.L) = min (muMinDef A.b A.X A.L) (muMinDef B.b B.X B.L)
    unfold muMinDef
    rw [show (A.L.prod B.L : Submodule (𝓞 K) (A.V × B.V)) = LA' ⊔ LB' from hD_sup,
      hmin_sup, ← hLA'_eq, hmuMin_LA', ← hLB'_eq, hmuMin_LB']
    have h1 : ∀ a b c d : ℝ, 2 * min a b - c + d = min (2 * a - c + d) (2 * b - c + d) := by
      intro a b c d; rcases le_total a b with h | h <;> simp [h]
    exact h1 _ _ _ _
  have h_mu : D.mu * ((A.rank : ℝ) + B.rank) = A.mu * A.rank + B.mu * B.rank := by
    have hrk_posA : 0 < A.rank := by
      have := rk_pos_of_ne_bot A.zRealize (zRealize_ne_bot A.b A.X hA.1 hA0)
      rw [rk_zRealize_eq A.b A.X hA.1 A.L hA.2.1] at this
      exact Nat.pos_of_mul_pos_left this
    have hrk_posB : 0 < B.rank := by
      have := rk_pos_of_ne_bot B.zRealize (zRealize_ne_bot B.b B.X hB.1 hB0)
      rw [rk_zRealize_eq B.b B.X hB.1 B.L hB.2.1] at this
      exact Nat.pos_of_mul_pos_left this
    have hn_ne : (Module.finrank ℚ K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn_pos.ne'
    have hrA_ne : (A.rank : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hrk_posA.ne'
    have hrB_ne : (B.rank : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hrk_posB.ne'
    have hrD_ne : ((A.rank : ℝ) + B.rank) ≠ 0 := by positivity
    show muDef D.b D.X D.L * ((A.rank : ℝ) + B.rank) =
      muDef A.b A.X A.L * A.rank + muDef B.b B.X B.L * B.rank
    unfold muDef slopeHLat ArakelovCovolume.slope
    change (2 * (degHLat D.b D.X D.L / (rk D.zRealize : ℝ)) - Real.log 2 + logDiscDivDeg K) *
        ((A.rank : ℝ) + B.rank) =
      (2 * (degHLat A.b A.X A.L / (rk A.zRealize : ℝ)) - Real.log 2 + logDiscDivDeg K) * A.rank +
      (2 * (degHLat B.b B.X B.L / (rk B.zRealize : ℝ)) - Real.log 2 + logDiscDivDeg K) * B.rank
    rw [rk_zRealize_eq D.b D.X hG.1 D.L hG.2.1, rk_zRealize_eq A.b A.X hA.1 A.L hA.2.1,
      rk_zRealize_eq B.b B.X hB.1 B.L hB.2.1]
    change (2 * (degHLat D.b D.X D.L / ((Module.finrank ℚ K * D.rank : ℕ) : ℝ)) -
        Real.log 2 + logDiscDivDeg K) * ((A.rank : ℝ) + B.rank) = _
    rw [hD_rank, hD_deg]
    unfold HLat.rank at hrA_ne hrB_ne hrD_ne ⊢
    push_cast
    field_simp [hn_ne, hrA_ne, hrB_ne, hrD_ne]
    ring
  exact ⟨h_muMax, h_muMin, h_mu⟩

end ExternalDirectSum

end OrthogonalDirectSum

end RHDirect.Stage14M2_HLatNumberField


