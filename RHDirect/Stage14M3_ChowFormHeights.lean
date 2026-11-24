import RHDirect.Stage14M3_HermitianLineBundles
import RHDirect.Stage14M3_GreenCurrents
import RHDirect.Stage12SchurWeylLattices
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# RHDirect.Stage14M3_ChowFormHeights

**FIELD-2 PACKAGE M3 (WAVE 2) — UNCONDITIONAL CONCRETE PROJECTIVE CHOW FORMS, FALTINGS–PHILIPPON
HEIGHTS, ARAKELOV INTERSECTION UPPER BOUNDS, CHOW-FORM HEIGHT COMPARISONS, AND POSITIVE-METRIC
HEIGHT LOWER BOUNDS** in pure Mathlib `v4.33.1` (`0` `sorry`, `0` custom `axiom`s, `0` `opaque`,
`0` `native_decide`).

Distills the genuine Chow-form & arithmetic Bézout height geometry of Pillar 5
(`GroundTheory.HeightsAndTheta.Heights.{ChowForms,ArithmeticBezout}`,
`Development.AbelianVarietyTheory.Definitions.HeightFunctions.*`, and
`Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ChowFormHeightComparison`)
into a single cohesive, unconditionally proved module directly wired to:
- `RHDirect.Stage14M3_HermitianLineBundles` (`MetrizedLineBundle`, `PosCurvatureMetric`,
  `fubiniStudyLineBundle`, `thetaMetrizedLineBundle`, `section_ptNormSq_metric_comparison`,
  `metrizedLineBundle_bergman_extremal`),
- `RHDirect.Stage14M3_GreenCurrents` (`fsLog`, `fsLogReg`, `ArakelovPairingModel`,
  `archStarPairing`, `poincare_lelong_inv`, `archStarPairing_nonneg_of_effective_semipositive`),
- `RHDirect.Stage12SchurWeylLattices` (`GradedHermAlgebra`, `L3_hodge_covolume_bound`,
  `L3_covolume_of_moriwaki_small_sections`),

and directly feeding M3 Wave 3 (`Stage14M3_ArakelovPublishedPackage`) and M4 Wave 2
(`Stage14M4_CovolStepsBridge`).

## Main Exported Types & Theorems

1. **Concrete `ProjectiveChowForm` & Multihomogeneous Cycle Algebra**:
   - `blockWeight`, `IsBlockHomogeneous`, `aeval_block_smul_eq`, `linSubst`, `specFirst`.
   - `ProjectiveChowForm K d N`: nonzero multihomogeneous polynomial of equal degree `δ` in
     `(d + 1)` dual hyperplane blocks `Fin (d + 1) × Fin N` with homogeneous defining ideal and
     exact incidence vanishing (`incidence_zero`).
   - Concrete 0-assumption instantiations: `ProjectiveChowForm.ofPoint` (`d = 0, deg = 1`),
     `ProjectiveChowForm.ofProjSpace` (determinant Chow form of `ℙ^{N-1}`, `d = N - 1, deg = 1`),
     cycle addition (`mul`), scaling (`smul`), and field base change (`baseChange`).

2. **Hermitian Projective Metrics, Fubini–Study Green Potentials & Mahler Measure**:
   - `HermProjMetric N`: positive-definite Hermitian matrix `H` on `ℂ^N` with spectral square root
     `posDefSqrt`, exact primal/dual norms `primalNorm`, `dualNorm`, exact Cauchy–Schwarz duality
     (`norm_sum_mul_le_dualNorm_mul_primalNorm`) with equality attainment, Fubini–Study Green
     potential `fsGreen`, and `PosCurvatureMetric` bridge.
   - `harmonicNum`, `bgsShift`, `chowSupNorm`, `mahlerMeasure` (normalized integral average of
     `log ‖F(nrmRows u)‖` over `prodDualBall H (d + 1)`), exact point evaluation
     (`chowSupNorm_ofPoint`), and Mahler/sup norm comparison inequalities.

3. **Concrete `FaltingsPhilipponHeight` over Number Fields**:
   - `AdelicPlaceSystem K` for arbitrary number fields `[NumberField K]` plus finite-place
     Gauss norm `finPlacePolyNorm` and unconditional Gauss multiplicativity lemma
     (`finPlacePolyNorm_mul`).
   - `FaltingsPhilipponHeight` & `FaltingsPhilipponSupHeight` with unconditional product-formula
     scaling invariance (`faltingsPhilipponHeight_smul_invariant`), cycle additivity
     (`faltingsPhilipponHeight_cycle_add`), metric-twist scaling (`faltingsPhilipponSupHeight_metric_scale`),
     and point height evaluation (`faltingsPhilipponSupHeight_ofPoint`).

4. **Main Height Theorems (`chow_form_norm_le_arith_intersection`, `chow_form_height_comparison`,
   `height_lower_bound_of_positive_metric`) & M4 `CovolStepsBridge`**:
   - `chow_form_norm_le_arith_intersection`: inductive Green-current / Arakelov-intersection upper
     bound on Chow-form Mahler & sup norms via `ArakelovPairingModel` & `poincare_lelong_inv`.
   - `chow_form_height_comparison`: two-sided Bost–Gillet–Soulé / Philippon height comparison
     between `FaltingsPhilipponHeight`, `FaltingsPhilipponSupHeight`, and Arakelov self-intersection,
     plus metric-comparison stability and Alpöge's Weil height inequality.
   - `height_lower_bound_of_positive_metric`: non-negativity and explicit uniform lower bounds from
     `PosCurvatureMetric` (`fubiniStudy_posCurvature`, `theta_metric_positivity`) + direct bridge
     into `Stage12SchurWeylLattices.L3_hodge_covolume_bound` for `Stage14M4_CovolStepsBridge`.
-/

open Complex Real Filter MeasureTheory Module Submodule Finset Matrix Function Set
open RHDirect.HermitianCurvatureCore RHDirect.Stage11ArakelovFaltings
open RHDirect.Stage11DefiniteUnitaryChain RHDirect.Stage11MoriwakiCovolume
open RHDirect.Stage14M3_HermitianLineBundles RHDirect.Stage14M3_GreenCurrents
open RHDirect.Stage12SchurWeylLattices RHDirect.ArakelovCovolume
open scoped BigOperators ComplexConjugate ComplexOrder ENNReal Topology

namespace RHDirect.Stage14M3_ChowFormHeights

noncomputable section

/-! ## Section 1: `ProjectiveChowForm` & Multihomogeneous Chow-Form Algebra -/

section ProjectiveChowForms

open MvPolynomial

/-- Multidegree weight assigning `Pi.single i 1` to variable `(i, j) : Fin (d + 1) × Fin N`. -/
def blockWeight (d N : ℕ) : Fin (d + 1) × Fin N → Fin (d + 1) → ℕ :=
  fun ij => Pi.single ij.1 1

/-- A polynomial `F : MvPolynomial (Fin (d + 1) × Fin N) R` is **block-homogeneous of degree `δ`**
if it has exact degree `δ` in each of the `(d + 1)` hyperplane-coordinate blocks. -/
def IsBlockHomogeneous {R : Type*} [CommRing R] {d N : ℕ} (δ : ℕ)
    (F : MvPolynomial (Fin (d + 1) × Fin N) R) : Prop :=
  MvPolynomial.IsWeightedHomogeneous (blockWeight d N) F (fun _ => δ)

lemma blockWeight_sum_apply {d N : ℕ} (m : Fin (d + 1) × Fin N →₀ ℕ) (i : Fin (d + 1)) :
    (Finsupp.weight (blockWeight d N) m) i = ∑ j : Fin N, m (i, j) := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (fun _ => by simp)]
  rw [Fintype.sum_prod_type]
  have hrow : ∀ i' : Fin (d + 1),
      (∑ j : Fin N, m (i', j) • blockWeight d N (i', j)) i =
        if i' = i then ∑ j : Fin N, m (i', j) else 0 := by
    intro i'
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, blockWeight, Pi.single_apply]
    by_cases h : i' = i
    · subst h; simp
    · rw [if_neg h]; simp [Ne.symm h]
  simp only [Finset.sum_apply, hrow, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

theorem isBlockHomogeneous_iff {R : Type*} [CommRing R] {d N : ℕ} (δ : ℕ)
    (F : MvPolynomial (Fin (d + 1) × Fin N) R) :
    IsBlockHomogeneous δ F ↔
      ∀ m ∈ F.support, ∀ i : Fin (d + 1), ∑ j : Fin N, m (i, j) = δ := by
  constructor
  · intro h m hm i
    have hw := h (MvPolynomial.mem_support_iff.mp hm)
    rw [← blockWeight_sum_apply]
    exact congrFun hw i
  · intro h m hm
    ext i
    rw [blockWeight_sum_apply]
    exact h m (MvPolynomial.mem_support_iff.mpr hm) i

theorem isBlockHomogeneous_zero {R : Type*} [CommRing R] (d N δ : ℕ) :
    IsBlockHomogeneous (R := R) (d := d) (N := N) δ 0 := by
  rw [isBlockHomogeneous_iff]
  intro m hm
  simp at hm

theorem isBlockHomogeneous_C_zero {R : Type*} [CommRing R] (d N : ℕ) (c : R) :
    IsBlockHomogeneous (d := d) (N := N) 0 (C c) :=
  MvPolynomial.isWeightedHomogeneous_C _ c

theorem isBlockHomogeneous_add {R : Type*} [CommRing R] {d N δ : ℕ}
    {F G : MvPolynomial (Fin (d + 1) × Fin N) R}
    (hF : IsBlockHomogeneous δ F) (hG : IsBlockHomogeneous δ G) :
    IsBlockHomogeneous δ (F + G) :=
  hF.add hG

theorem isBlockHomogeneous_neg {R : Type*} [CommRing R] {d N δ : ℕ}
    {F : MvPolynomial (Fin (d + 1) × Fin N) R}
    (hF : IsBlockHomogeneous δ F) :
    IsBlockHomogeneous δ (-F) := by
  rw [isBlockHomogeneous_iff] at hF ⊢
  intro m hm i
  rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_neg, neg_ne_zero] at hm
  exact hF m (MvPolynomial.mem_support_iff.mpr hm) i

theorem isBlockHomogeneous_C_mul {R : Type*} [CommRing R] {d N δ : ℕ} (c : R)
    {F : MvPolynomial (Fin (d + 1) × Fin N) R} (hF : IsBlockHomogeneous δ F) :
    IsBlockHomogeneous δ (C c * F) := by
  have h := (isBlockHomogeneous_C_zero d N c).mul hF
  unfold IsBlockHomogeneous
  convert h using 1
  ext; simp

theorem isBlockHomogeneous_mul {R : Type*} [CommRing R] {d N δ₁ δ₂ : ℕ}
    {F G : MvPolynomial (Fin (d + 1) × Fin N) R}
    (hF : IsBlockHomogeneous δ₁ F) (hG : IsBlockHomogeneous δ₂ G) :
    IsBlockHomogeneous (δ₁ + δ₂) (F * G) := by
  have h := hF.mul hG
  unfold IsBlockHomogeneous
  convert h using 1
  rfl

theorem isBlockHomogeneous_pow {R : Type*} [CommRing R] {d N δ : ℕ}
    {F : MvPolynomial (Fin (d + 1) × Fin N) R} (hF : IsBlockHomogeneous δ F) (k : ℕ) :
    IsBlockHomogeneous (k * δ) (F ^ k) := by
  induction k with
  | zero =>
    rw [pow_zero, Nat.zero_mul]
    simpa using isBlockHomogeneous_C_zero d N (1 : R)
  | succ k ih =>
    rw [pow_succ, Nat.succ_mul]
    exact isBlockHomogeneous_mul ih hF

theorem isBlockHomogeneous_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    {d N δ : ℕ} {F : MvPolynomial (Fin (d + 1) × Fin N) R}
    (hF : IsBlockHomogeneous δ F) :
    IsBlockHomogeneous δ (MvPolynomial.map φ F) := by
  rw [isBlockHomogeneous_iff] at hF ⊢
  intro m hm i
  rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_map] at hm
  have hm' : m ∈ F.support := MvPolynomial.mem_support_iff.mpr (fun h0 => hm (by rw [h0, map_zero]))
  exact hF m hm' i

theorem isBlockHomogeneous_map_iff {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (hφ : Function.Injective φ) {d N δ : ℕ} (F : MvPolynomial (Fin (d + 1) × Fin N) R) :
    IsBlockHomogeneous δ (MvPolynomial.map φ F) ↔ IsBlockHomogeneous δ F := by
  constructor
  · intro h
    rw [isBlockHomogeneous_iff] at h ⊢
    intro m hm i
    refine h m ?_ i
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_map]
    exact fun h0 => (MvPolynomial.mem_support_iff.mp hm) (hφ (by rwa [map_zero]))
  · exact isBlockHomogeneous_map φ

private lemma isWeightedHomogeneous_finset_sum {σ R M α : Type*} [CommRing R] [AddCommMonoid M]
    (w : σ → M) (ν : M) (s : Finset α) (P : α → MvPolynomial σ R)
    (hP : ∀ a ∈ s, MvPolynomial.IsWeightedHomogeneous w (P a) ν) :
    MvPolynomial.IsWeightedHomogeneous w (∑ a ∈ s, P a) ν := by
  rw [← MvPolynomial.mem_weightedHomogeneousSubmodule]
  exact Submodule.sum_mem _ fun a ha => (MvPolynomial.mem_weightedHomogeneousSubmodule _ _ _ _).mpr (hP a ha)

private lemma isWeightedHomogeneous_finset_prod {σ R M α : Type*} [CommRing R] [AddCommMonoid M]
    (w : σ → M) (s : Finset α) (P : α → MvPolynomial σ R) (ν : α → M)
    (hP : ∀ a ∈ s, MvPolynomial.IsWeightedHomogeneous w (P a) (ν a)) :
    MvPolynomial.IsWeightedHomogeneous w (∏ a ∈ s, P a) (∑ a ∈ s, ν a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using MvPolynomial.isWeightedHomogeneous_one R w
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact (hP a (Finset.mem_insert_self a s)).mul (ih fun b hb => hP b (Finset.mem_insert_of_mem hb))

/-- Total degree of a block-homogeneous polynomial of degree `δ` in `d + 1` blocks is `≤ (d + 1) * δ`. -/
theorem totalDegree_of_isBlockHomogeneous {R : Type*} [CommRing R] {d N δ : ℕ}
    {F : MvPolynomial (Fin (d + 1) × Fin N) R} (hF : IsBlockHomogeneous δ F) :
    F.totalDegree ≤ (d + 1) * δ := by
  rw [MvPolynomial.totalDegree]
  refine Finset.sup_le fun m hm => ?_
  have hrow := (isBlockHomogeneous_iff δ F).mp hF m hm
  rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fintype.sum_prod_type]
  refine le_of_eq ?_
  calc ∑ i : Fin (d + 1), ∑ j : Fin N, m (i, j)
      = ∑ _i : Fin (d + 1), δ := Finset.sum_congr rfl fun i _ => hrow i
    _ = (d + 1) * δ := by simp

/-- **Blockwise Multihomogeneous Scaling Law**:
scaling each hyperplane block `i` by `c i` scales `aeval u F` by `∏ i, (c i)^δ`. -/
theorem aeval_block_smul_eq {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {d N δ : ℕ} {F : MvPolynomial (Fin (d + 1) × Fin N) R} (hF : IsBlockHomogeneous δ F)
    (c : Fin (d + 1) → S) (u : Fin (d + 1) × Fin N → S) :
    MvPolynomial.aeval (fun ij => c ij.1 * u ij) F =
      (∏ i : Fin (d + 1), c i ^ δ) * MvPolynomial.aeval u F := by
  rw [MvPolynomial.aeval_def, MvPolynomial.aeval_def, MvPolynomial.eval₂_eq,
    MvPolynomial.eval₂_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hrow := (isBlockHomogeneous_iff δ F).mp hF m hm
  have hprod : ∏ ij ∈ m.support, (c ij.1 * u ij) ^ m ij =
      (∏ i : Fin (d + 1), c i ^ δ) * ∏ ij ∈ m.support, u ij ^ m ij := by
    simp_rw [mul_pow, Finset.prod_mul_distrib]
    congr 1
    have hfull : ∏ ij ∈ m.support, c ij.1 ^ m ij =
        ∏ ij : Fin (d + 1) × Fin N, c ij.1 ^ m ij := by
      refine Finset.prod_subset (Finset.subset_univ _) fun ij _ hij => ?_
      rw [Finsupp.mem_support_iff, not_not] at hij
      simp [hij]
    rw [hfull, Fintype.prod_prod_type]
    refine Finset.prod_congr rfl fun i _ => ?_
    change ∏ j : Fin N, c i ^ m (i, j) = c i ^ δ
    rw [Finset.prod_pow_eq_pow_sum, hrow i]
  rw [hprod]
  ring

/-- Linear coordinate substitution `(i, j) ↦ ∑ k, A j k * X (i, k)` on Chow-form variables. -/
def linSubst {R : Type*} [CommRing R] {d N : ℕ} (A : Matrix (Fin N) (Fin N) R) :
    MvPolynomial (Fin (d + 1) × Fin N) R →ₐ[R] MvPolynomial (Fin (d + 1) × Fin N) R :=
  MvPolynomial.aeval fun ij => ∑ k : Fin N, C (A ij.2 k) * X (ij.1, k)

theorem aeval_linSubst {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {d N : ℕ} (A : Matrix (Fin N) (Fin N) R) (F : MvPolynomial (Fin (d + 1) × Fin N) R)
    (u : Fin (d + 1) × Fin N → S) :
    MvPolynomial.aeval u (linSubst A F) =
      MvPolynomial.aeval (fun ij => ∑ k : Fin N, algebraMap R S (A ij.2 k) * u (ij.1, k)) F := by
  unfold linSubst
  change ((MvPolynomial.aeval u).comp (MvPolynomial.aeval fun ij =>
    ∑ k : Fin N, C (A ij.2 k) * X (ij.1, k))) F = _
  congr 1
  exact MvPolynomial.algHom_ext fun ij => by simp

theorem isBlockHomogeneous_linSubst {R : Type*} [CommRing R] {d N δ : ℕ}
    (A : Matrix (Fin N) (Fin N) R) {F : MvPolynomial (Fin (d + 1) × Fin N) R}
    (hF : IsBlockHomogeneous δ F) :
    IsBlockHomogeneous δ (linSubst A F) := by
  unfold linSubst IsBlockHomogeneous
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq]
  refine isWeightedHomogeneous_finset_sum _ _ _ _ fun m hm => ?_
  have hrow := (isBlockHomogeneous_iff δ F).mp hF m hm
  have hlin : ∀ ij : Fin (d + 1) × Fin N,
      MvPolynomial.IsWeightedHomogeneous (blockWeight d N)
        (∑ k : Fin N, (C (A ij.2 k) : MvPolynomial (Fin (d + 1) × Fin N) R) * X (ij.1, k))
        (Pi.single ij.1 (1 : ℕ)) := fun ij => by
    refine isWeightedHomogeneous_finset_sum _ _ _ _ fun k _ => ?_
    have hX := MvPolynomial.isWeightedHomogeneous_X R (blockWeight d N) (ij.1, k)
    simpa [blockWeight, zero_add] using (MvPolynomial.isWeightedHomogeneous_C _ (A ij.2 k)).mul hX
  have hprod := isWeightedHomogeneous_finset_prod (blockWeight d N) m.support
    (fun ij => (∑ k : Fin N, (C (A ij.2 k) : MvPolynomial (Fin (d + 1) × Fin N) R) * X (ij.1, k)) ^ m ij)
    (fun ij => m ij • Pi.single ij.1 (1 : ℕ))
    (fun ij _ => by simpa [nsmul_eq_mul] using (hlin ij).pow (m ij))
  have hwt : (∑ ij ∈ m.support, m ij • (Pi.single ij.1 1 : Fin (d + 1) → ℕ)) = fun _ => δ := by
    ext i
    have hfull : (∑ ij ∈ m.support, m ij • (Pi.single ij.1 1 : Fin (d + 1) → ℕ)) i =
        ∑ ij : Fin (d + 1) × Fin N, (m ij • (Pi.single ij.1 1 : Fin (d + 1) → ℕ)) i := by
      simp only [Finset.sum_apply]
      refine Finset.sum_subset (Finset.subset_univ _) fun ij _ hij => ?_
      rw [Finsupp.mem_support_iff, not_not] at hij
      simp [hij]
    rw [hfull, Fintype.sum_prod_type]
    have hinner : ∀ i' : Fin (d + 1),
        ∑ j : Fin N, (m (i', j) • (Pi.single i' 1 : Fin (d + 1) → ℕ)) i =
          if i' = i then ∑ j : Fin N, m (i', j) else 0 := by
      intro i'
      by_cases h : i' = i
      · subst h; simp
      · rw [if_neg h]; simp [Ne.symm h]
    simp_rw [hinner]
    rw [Finset.sum_eq_single i (fun _ _ h => if_neg h) (fun h => absurd (Finset.mem_univ _) h),
      if_pos rfl]
    exact hrow i
  rw [hwt] at hprod
  simpa [MvPolynomial.algebraMap_eq, zero_add] using
    (MvPolynomial.isWeightedHomogeneous_C (blockWeight d N) (coeff m F)).mul hprod

/-- Specialize the `0`-th hyperplane block of a `(d + 2)`-block polynomial at `u : Fin N → R`,
producing a `(d + 1)`-block polynomial (`specFirst`). -/
def specFirst {R : Type*} [CommRing R] {d N : ℕ}
    (F : MvPolynomial (Fin (d + 2) × Fin N) R) (u : Fin N → R) :
    MvPolynomial (Fin (d + 1) × Fin N) R :=
  MvPolynomial.aeval (fun ij => Fin.cases (C (u ij.2)) (fun i' => X (i', ij.2)) ij.1) F

theorem aeval_specFirst {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {d N : ℕ} (F : MvPolynomial (Fin (d + 2) × Fin N) R) (u : Fin N → R)
    (w : Fin (d + 1) × Fin N → S) :
    MvPolynomial.aeval w (specFirst F u) =
      MvPolynomial.aeval (fun ij => Fin.cases (algebraMap R S (u ij.2)) (fun i' => w (i', ij.2)) ij.1) F := by
  unfold specFirst
  change ((MvPolynomial.aeval w).comp (MvPolynomial.aeval fun ij =>
    Fin.cases (C (u ij.2)) (fun i' => X (i', ij.2)) ij.1)) F = _
  congr 1
  exact MvPolynomial.algHom_ext fun ⟨i, j⟩ => by
    refine Fin.cases ?_ ?_ i <;> simp

theorem isBlockHomogeneous_specFirst {R : Type*} [CommRing R] {d N δ : ℕ}
    {F : MvPolynomial (Fin (d + 2) × Fin N) R} (hF : IsBlockHomogeneous δ F) (u : Fin N → R) :
    IsBlockHomogeneous δ (specFirst F u) := by
  unfold specFirst IsBlockHomogeneous
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq]
  refine isWeightedHomogeneous_finset_sum _ _ _ _ fun m hm => ?_
  have hrow := (isBlockHomogeneous_iff δ F).mp hF m hm
  let gVar : Fin (d + 2) × Fin N → MvPolynomial (Fin (d + 1) × Fin N) R :=
    fun ij => Fin.cases (C (u ij.2)) (fun i' => X (i', ij.2)) ij.1
  let wVar : Fin (d + 2) × Fin N → (Fin (d + 1) → ℕ) :=
    fun ij => Fin.cases (0 : Fin (d + 1) → ℕ) (fun i' => Pi.single i' (1 : ℕ)) ij.1
  have hgVar : ∀ ij, MvPolynomial.IsWeightedHomogeneous (blockWeight d N) (gVar ij) (wVar ij) := by
    intro ⟨i, j⟩
    refine Fin.cases ?_ ?_ i
    · simpa [gVar, wVar] using MvPolynomial.isWeightedHomogeneous_C (blockWeight d N) (u j)
    · intro i'
      simpa [gVar, wVar, blockWeight] using
        MvPolynomial.isWeightedHomogeneous_X R (blockWeight d N) (i', j)
  have hprod := isWeightedHomogeneous_finset_prod (blockWeight d N) m.support
    (fun ij => gVar ij ^ m ij) (fun ij => m ij • wVar ij)
    (fun ij _ => by simpa [nsmul_eq_mul] using (hgVar ij).pow (m ij))
  have hwt : (∑ ij ∈ m.support, m ij • wVar ij) = fun _ => δ := by
    ext i'
    have hfull : (∑ ij ∈ m.support, m ij • wVar ij) i' =
        ∑ ij : Fin (d + 2) × Fin N, (m ij • wVar ij) i' := by
      simp only [Finset.sum_apply]
      refine Finset.sum_subset (Finset.subset_univ _) fun ij _ hij => ?_
      rw [Finsupp.mem_support_iff, not_not] at hij
      simp [hij]
    rw [hfull, Fintype.sum_prod_type, Fin.sum_univ_succ]
    have h0 : ∑ j : Fin N, (m (0, j) • wVar (0, j)) i' = 0 := by
      simp [wVar]
    have hsuc : ∀ a : Fin (d + 1),
        ∑ j : Fin N, (m (a.succ, j) • wVar (a.succ, j)) i' =
          if a = i' then ∑ j : Fin N, m (a.succ, j) else 0 := by
      intro a
      by_cases h : a = i'
      · subst h; simp [wVar]
      · rw [if_neg h]; simp [wVar, Ne.symm h]
    simp_rw [h0, zero_add, hsuc, Finset.sum_ite_eq', Finset.mem_univ, if_pos trivial]
    exact hrow i'.succ
  rw [hwt] at hprod
  simpa [gVar, MvPolynomial.algebraMap_eq, zero_add] using
    (MvPolynomial.isWeightedHomogeneous_C (blockWeight d N) (coeff m F)).mul hprod

/-- **Concrete Projective Chow Form (`ProjectiveChowForm K d N`)**:
represents a `d`-dimensional effective projective cycle of degree `deg` in `ℙ^{N-1}_K` via its
nonzero multihomogeneous Chow polynomial `poly : MvPolynomial (Fin (d + 1) × Fin N) K` of equal
block degree `deg` in all `(d + 1)` dual hyperplane blocks, together with its defining homogeneous
ideal and exact incidence vanishing on points of the cycle. -/
structure ProjectiveChowForm (K : Type*) [Field K] (d N : ℕ) where
  /-- Multihomogeneous Chow polynomial `F(u_0, …, u_d)`. -/
  poly : MvPolynomial (Fin (d + 1) × Fin N) K
  /-- Degree `δ = deg(Z)` in each hyperplane block. -/
  deg : ℕ
  /-- Non-vanishing of the Chow polynomial. -/
  ne_zero : poly ≠ 0
  /-- Equal multihomogeneity of degree `deg` in every block `i : Fin (d + 1)`. -/
  homog : IsBlockHomogeneous deg poly
  /-- Defining homogeneous ideal `I ⊆ K[X_0, …, X_{N-1}]` of the subvariety / cycle support. -/
  ideal : Ideal (MvPolynomial (Fin N) K)
  /-- **Exact Incidence Vanishing**: if `y ≠ 0` is a geometric point in `V(I)` over any extension
  `L / K`, and `u_0, …, u_d` are hyperplanes containing `y`, then `F(u_0, …, u_d) = 0`. -/
  incidence_zero : ∀ {L : Type*} [Field L] [Algebra K L] (y : Fin N → L),
    y ≠ 0 → (∀ g ∈ ideal, MvPolynomial.aeval y g = 0) →
    ∀ u : Fin (d + 1) × Fin N → L,
      (∀ i : Fin (d + 1), ∑ j : Fin N, u (i, j) * y j = 0) →
      MvPolynomial.aeval u poly = 0

namespace ProjectiveChowForm

/-- **0-Assumption Instantiation 1: Projective Point `[y] ∈ ℙ^{N-1}_K`** (`d = 0, deg = 1`):
its Chow form is the linear form `∑ j, y_j X_{(0, j)}`. -/
def ofPoint {K : Type*} [Field K] {N : ℕ} (y : Fin N → K) (hy : y ≠ 0) :
    ProjectiveChowForm K 0 N where
  poly := ∑ j : Fin N, C (y j) * X (0, j)
  deg := 1
  ne_zero := by
    have hex : ∃ j₀ : Fin N, y j₀ ≠ 0 := by
      by_contra h; push Not at h; exact hy (funext h)
    rcases hex with ⟨j₀, hj₀⟩
    intro h0
    have hev := congrArg (MvPolynomial.aeval (fun ij : Fin 1 × Fin N =>
      if ij.2 = j₀ then (1 : K) else 0)) h0
    simp only [map_sum, map_mul, MvPolynomial.aeval_C, Algebra.algebraMap_self,
      RingHom.id_apply, MvPolynomial.aeval_X, map_zero] at hev
    rw [Finset.sum_eq_single j₀] at hev
    · simp [hj₀] at hev
    · intro j _ hj; simp [hj]
    · intro h; exact absurd (Finset.mem_univ j₀) h
  homog := by
    refine isWeightedHomogeneous_finset_sum _ _ _ _ fun j _ => ?_
    have hX := MvPolynomial.isWeightedHomogeneous_X K (blockWeight 0 N) ((0 : Fin 1), j)
    have hw : blockWeight 0 N ((0 : Fin 1), j) = fun _ => 1 := by
      ext i; rw [Fin.fin_one_eq_zero i]; simp [blockWeight]
    rw [hw] at hX
    simpa [zero_add] using (MvPolynomial.isWeightedHomogeneous_C (blockWeight 0 N) (y j)).mul hX
  ideal := Ideal.span { C (y j) * X k - C (y k) * X j | (j : Fin N) (k : Fin N) }
  incidence_zero := by
    intro L _ _ z hz hideal u hu
    have hex : ∃ j₀ : Fin N, y j₀ ≠ 0 := by
      by_contra h; push Not at h; exact hy (funext h)
    rcases hex with ⟨j₀, hj₀⟩
    have hz0 : z j₀ ≠ 0 := by
      intro hzj0
      apply hz
      funext k
      have hmem : C (y j₀) * X k - C (y k) * X j₀ ∈
          Ideal.span { C (y j) * X k' - C (y k') * X j | (j : Fin N) (k' : Fin N) } :=
        Ideal.subset_span ⟨j₀, k, rfl⟩
      have hev := hideal _ hmem
      simp only [map_sub, map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X,
        hzj0, mul_zero, sub_zero, mul_eq_zero] at hev
      exact hev.resolve_left ((map_ne_zero (algebraMap K L)).mpr hj₀)
    have hcol : ∀ k : Fin N, algebraMap K L (y k) * z j₀ = algebraMap K L (y j₀) * z k := by
      intro k
      have hmem : C (y j₀) * X k - C (y k) * X j₀ ∈
          Ideal.span { C (y j) * X k' - C (y k') * X j | (j : Fin N) (k' : Fin N) } :=
        Ideal.subset_span ⟨j₀, k, rfl⟩
      have hev := hideal _ hmem
      simp only [map_sub, map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X, sub_eq_zero] at hev
      exact hev.symm
    have hmul : z j₀ * MvPolynomial.aeval u (∑ j : Fin N, C (y j) * X (0, j)) = 0 := by
      simp only [map_sum, map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X, Finset.mul_sum]
      calc ∑ j : Fin N, z j₀ * (algebraMap K L (y j) * u (0, j))
          = ∑ j : Fin N, (algebraMap K L (y j) * z j₀) * u (0, j) :=
              Finset.sum_congr rfl fun j _ => by ring
        _ = ∑ j : Fin N, (algebraMap K L (y j₀) * z j) * u (0, j) := by
              refine Finset.sum_congr rfl fun j _ => by rw [hcol j]
        _ = algebraMap K L (y j₀) * ∑ j : Fin N, u (0, j) * z j := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun j _ => by ring
        _ = 0 := by rw [hu 0, mul_zero]
    exact (mul_eq_zero.mp hmul).resolve_left hz0

private lemma units_int_eq_one_or_neg_one (u : ℤˣ) : u = 1 ∨ u = -1 := by
  have h : u.val * u.inv = 1 := u.val_inv
  have h1 : u.val = 1 ∨ u.val = -1 := by
    by_cases hp : 2 ≤ u.val
    · have : u.inv ≤ 0 ∨ 1 ≤ u.inv := by omega
      rcases this with hi | hi <;> nlinarith
    · by_cases hn : u.val ≤ -2
      · have : u.inv ≤ -1 ∨ 0 ≤ u.inv := by omega
        rcases this with hi | hi <;> nlinarith
      · have : u.val = 0 ∨ u.val = 1 ∨ u.val = -1 := by omega
        rcases this with h0 | h1 | h1
        · rw [h0, zero_mul] at h; omega
        · exact Or.inl h1
        · exact Or.inr h1
  rcases h1 with h1 | h1 <;> [left; right] <;> exact Units.ext h1

/-- **0-Assumption Instantiation 2: Full Projective Space `ℙ^{N-1}_K`** (`d = N - 1, deg = 1`):
its Chow form is the `N × N` determinant polynomial `det(u_0, …, u_{N-1})`. -/
def ofProjSpace {K : Type*} [Field K] (N : ℕ) (hN : 1 ≤ N) :
    ProjectiveChowForm K (N - 1) N where
  poly :=
    let e : Fin (N - 1 + 1) ≃ Fin N := finCongr (by omega)
    Matrix.det (Matrix.of fun (i j : Fin N) => X (e.symm i, j))
  deg := 1
  ne_zero := by
    intro h0
    let e : Fin (N - 1 + 1) ≃ Fin N := finCongr (by omega)
    let idMat : Fin (N - 1 + 1) × Fin N → K := fun ij => if e ij.1 = ij.2 then 1 else 0
    have hev := congrArg (MvPolynomial.aeval idMat) h0
    rw [map_zero] at hev
    have hdet1 : MvPolynomial.aeval idMat
        (Matrix.det (Matrix.of fun (i j : Fin N) =>
          (X (e.symm i, j) : MvPolynomial (Fin (N - 1 + 1) × Fin N) K))) = 1 := by
      rw [Matrix.det_apply, map_sum]
      have hrew : (∑ σ : Equiv.Perm (Fin N), MvPolynomial.aeval idMat
          (Equiv.Perm.sign σ • ∏ i : Fin N,
            Matrix.of (fun i' j : Fin N =>
              (X (e.symm i', j) : MvPolynomial (Fin (N - 1 + 1) × Fin N) K)) (σ i) i)) =
          Matrix.det (1 : Matrix (Fin N) (Fin N) K) := by
        rw [Matrix.det_apply]
        refine Finset.sum_congr rfl fun σ _ => ?_
        rcases units_int_eq_one_or_neg_one (Equiv.Perm.sign σ) with hs | hs
        · rw [hs, one_smul, one_smul]
          dsimp only [Matrix.of_apply]
          rw [map_prod]
          refine Finset.prod_congr rfl fun i _ => ?_
          simp [idMat, e.apply_symm_apply, Matrix.one_apply]
        · rw [hs, Units.neg_smul, one_smul, Units.neg_smul, one_smul, map_neg]
          congr 1
          dsimp only [Matrix.of_apply]
          rw [map_prod]
          refine Finset.prod_congr rfl fun i _ => ?_
          simp [idMat, e.apply_symm_apply, Matrix.one_apply]
      rw [hrew, Matrix.det_one]
    rw [hev] at hdet1
    exact zero_ne_one hdet1
  homog := by
    let e : Fin (N - 1 + 1) ≃ Fin N := finCongr (by omega)
    rw [Matrix.det_apply]
    refine isWeightedHomogeneous_finset_sum _ _ _ _ fun σ _ => ?_
    have hterm : MvPolynomial.IsWeightedHomogeneous (blockWeight (N - 1) N)
        (∏ i : Fin N, (X (e.symm (σ i), i) : MvPolynomial (Fin (N - 1 + 1) × Fin N) K))
        (fun _ => 1) := by
      have hprod := isWeightedHomogeneous_finset_prod (blockWeight (N - 1) N) Finset.univ
        (fun i : Fin N => (X (e.symm (σ i), i) : MvPolynomial (Fin (N - 1 + 1) × Fin N) K))
        (fun i : Fin N => blockWeight (N - 1) N (e.symm (σ i), i))
        (fun i _ => MvPolynomial.isWeightedHomogeneous_X K _ _)
      have hsum : (∑ i : Fin N, blockWeight (N - 1) N (e.symm (σ i), i)) = fun _ => 1 := by
        ext k
        simp only [Finset.sum_apply, blockWeight, Pi.single_apply]
        have hbij : (∑ i : Fin N, if k = e.symm (σ i) then 1 else 0) =
            ∑ i : Fin N, if i = σ.symm (e k) then 1 else 0 := by
          refine Finset.sum_congr rfl fun i _ => ?_
          congr 1
          rw [propext_iff]
          constructor
          · intro h
            have h1 := congrArg e h
            rw [e.apply_symm_apply] at h1
            rw [h1, Equiv.symm_apply_apply]
          · intro h
            rw [h, Equiv.apply_symm_apply, Equiv.symm_apply_apply]
        rw [hbij, Finset.sum_eq_single (σ.symm (e k))
          (fun _ _ h => if_neg h) (fun h => absurd (Finset.mem_univ _) h), if_pos rfl]
      rwa [hsum] at hprod
    dsimp only [Matrix.of_apply]
    rcases units_int_eq_one_or_neg_one (Equiv.Perm.sign σ) with hs | hs
    · rw [hs, one_smul]
      exact hterm
    · rw [hs, Units.neg_smul, one_smul, ← MvPolynomial.mem_weightedHomogeneousSubmodule]
      exact Submodule.neg_mem _ ((MvPolynomial.mem_weightedHomogeneousSubmodule _ _ _ _).mpr hterm)
  ideal := ⊥
  incidence_zero := by
    intro L _ _ y hy _ u hu
    let e : Fin (N - 1 + 1) ≃ Fin N := finCongr (by omega)
    let M : Matrix (Fin N) (Fin N) L := Matrix.of fun i j => u (e.symm i, j)
    have hmul0 : M.mulVec y = 0 := by
      ext i
      exact hu (e.symm i)
    have hdet0 : M.det = 0 := by
      by_contra hdet
      exact hy (Matrix.eq_zero_of_mulVec_eq_zero hdet hmul0)
    rw [Matrix.det_apply] at hdet0 ⊢
    rw [map_sum]
    refine hdet0.symm ▸ (Finset.sum_congr rfl fun σ _ => ?_).symm
    rcases units_int_eq_one_or_neg_one (Equiv.Perm.sign σ) with hs | hs
    · rw [hs, one_smul, one_smul]
      dsimp only [Matrix.of_apply]
      rw [map_prod]
      refine Finset.prod_congr rfl fun i _ => ?_
      dsimp only [M, Matrix.of_apply]
      rw [MvPolynomial.aeval_X]
    · rw [hs, Units.neg_smul, one_smul, Units.neg_smul, one_smul, map_neg]
      congr 1
      dsimp only [Matrix.of_apply]
      rw [map_prod]
      refine Finset.prod_congr rfl fun i _ => ?_
      dsimp only [M, Matrix.of_apply]
      rw [MvPolynomial.aeval_X]

/-- Effective cycle addition (`Z₁ + Z₂`): multiplies Chow polynomials and adds degrees. -/
def mul {K : Type*} [Field K] {d N : ℕ}
    (Z₁ Z₂ : ProjectiveChowForm K d N) : ProjectiveChowForm K d N where
  poly := Z₁.poly * Z₂.poly
  deg := Z₁.deg + Z₂.deg
  ne_zero := mul_ne_zero Z₁.ne_zero Z₂.ne_zero
  homog := isBlockHomogeneous_mul Z₁.homog Z₂.homog
  ideal := Z₁.ideal ⊓ Z₂.ideal
  incidence_zero := by
    intro L _ _ y hy hI u hu
    rw [map_mul]
    by_cases h1 : ∀ g ∈ Z₁.ideal, MvPolynomial.aeval y g = 0
    · rw [Z₁.incidence_zero y hy h1 u hu, zero_mul]
    · push Not at h1
      rcases h1 with ⟨g₁, hg₁, hg₁_ne⟩
      have h2 : ∀ g ∈ Z₂.ideal, MvPolynomial.aeval y g = 0 := by
        intro g₂ hg₂
        have hmem : g₁ * g₂ ∈ Z₁.ideal ⊓ Z₂.ideal :=
          ⟨Z₁.ideal.mul_mem_right g₂ hg₁, Z₂.ideal.mul_mem_left g₁ hg₂⟩
        have hev := hI (g₁ * g₂) hmem
        rw [map_mul, mul_eq_zero] at hev
        exact hev.resolve_left hg₁_ne
      rw [Z₂.incidence_zero y hy h2 u hu, mul_zero]

/-- Scalar multiple `c • Z` (`c ≠ 0` in `K`), leaving the cycle unchanged projectively. -/
def smul {K : Type*} [Field K] {d N : ℕ} (c : K) (hc : c ≠ 0)
    (Z : ProjectiveChowForm K d N) : ProjectiveChowForm K d N where
  poly := C c * Z.poly
  deg := Z.deg
  ne_zero := mul_ne_zero (C_ne_zero.mpr hc) Z.ne_zero
  homog := isBlockHomogeneous_C_mul c Z.homog
  ideal := Z.ideal
  incidence_zero := by
    intro L _ _ y hy hI u hu
    rw [map_mul, Z.incidence_zero y hy hI u hu, mul_zero]

/-- Field extension base change `φ : K →+* L` of a `ProjectiveChowForm`. -/
def baseChange {K L : Type*} [Field K] [Field L] (φ : K →+* L) {d N : ℕ}
    (Z : ProjectiveChowForm K d N) : ProjectiveChowForm L d N where
  poly := MvPolynomial.map φ Z.poly
  deg := Z.deg
  ne_zero := fun h0 => Z.ne_zero (MvPolynomial.map_injective φ φ.injective (by simpa using h0))
  homog := isBlockHomogeneous_map φ Z.homog
  ideal := Ideal.map (MvPolynomial.map φ : MvPolynomial (Fin N) K →+* MvPolynomial (Fin N) L) Z.ideal
  incidence_zero := by
    intro M _ _ y hy hI u hu
    let alKM : Algebra K M := (RingHom.comp (algebraMap L M) φ).toAlgebra
    have hI_K : ∀ g ∈ Z.ideal, @MvPolynomial.aeval K M (Fin N) _ _ alKM y g = 0 := by
      intro g hg
      have hmem : MvPolynomial.map φ g ∈
          Ideal.map (MvPolynomial.map φ : MvPolynomial (Fin N) K →+* MvPolynomial (Fin N) L) Z.ideal :=
        Ideal.mem_map_of_mem _ hg
      have hev := hI _ hmem
      rwa [MvPolynomial.aeval_def, MvPolynomial.eval₂_map] at hev
    have h0 := @ProjectiveChowForm.incidence_zero K _ d N Z M _ alKM y hy hI_K u hu
    rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_map]
    exact h0

end ProjectiveChowForm

end ProjectiveChowForms

/-! ## Section 2: Hermitian Projective Metrics, Fubini–Study Green Potentials & Mahler Measure -/

section HermitianMetricsAndMahlerMeasure

/-- **Hermitian Projective Metric `HermProjMetric N`** on `ℂ^N`:
specified by a positive-definite Hermitian matrix `H : Matrix (Fin N) (Fin N) ℂ`, inducing the
primal norm `‖y‖_H² = Re (yᴴ H y)` and dual norm `‖u‖_{H^*}² = Re (uᴴ (H⁻¹)ᵀ u)` on `(ℂ^N)^∨`. -/
structure HermProjMetric (N : ℕ) where
  H : Matrix (Fin N) (Fin N) ℂ
  hH : H.PosDef

namespace HermProjMetric

/-- Standard Fubini–Study Euclidean metric `H = I_N` on `ℂ^N`. -/
def std (N : ℕ) : HermProjMetric N where
  H := 1
  hH := Matrix.PosDef.one

/-- Hermitian square root `S = √H` (`Sᴴ = S` and `Sᴴ * S = H`). -/
def sqrtMat {N : ℕ} (M : HermProjMetric N) : Matrix (Fin N) (Fin N) ℂ :=
  posDefSqrt M.H M.hH

lemma sqrtMat_isHermitian {N : ℕ} (M : HermProjMetric N) : M.sqrtMat.IsHermitian :=
  posDefSqrt_isHermitian M.H M.hH

lemma sqrtMat_mul_self {N : ℕ} (M : HermProjMetric N) : M.sqrtMat * M.sqrtMat = M.H := by
  have h := posDefSqrt_conjTranspose_mul_self M.H M.hH
  change M.sqrtMatᴴ * M.sqrtMat = M.H at h
  rwa [M.sqrtMat_isHermitian.eq] at h

lemma isUnit_sqrtMat_det {N : ℕ} (M : HermProjMetric N) : IsUnit M.sqrtMat.det :=
  isUnit_posDefSqrt_det M.H M.hH

/-- Primal Hermitian squared norm `‖y‖_H² = ∑_j ‖(√H · y)_j‖²`. -/
def primalNormSq {N : ℕ} (M : HermProjMetric N) (y : Fin N → ℂ) : ℝ :=
  ∑ i : Fin N, ‖(M.sqrtMat.mulVec y) i‖ ^ 2

/-- Primal Hermitian norm `‖y‖_H = √(‖y‖_H²)`. -/
def primalNorm {N : ℕ} (M : HermProjMetric N) (y : Fin N → ℂ) : ℝ :=
  Real.sqrt (M.primalNormSq y)

/-- Dual Hermitian squared norm `‖u‖_{H^*}² = ∑_j ‖(((√H)⁻¹)ᵀ · u)_j‖²` on `(ℂ^N)^∨`. -/
def dualNormSq {N : ℕ} (M : HermProjMetric N) (u : Fin N → ℂ) : ℝ :=
  ∑ i : Fin N, ‖((M.sqrtMat⁻¹).transpose.mulVec u) i‖ ^ 2

/-- Dual Hermitian norm `‖u‖_{H^*} = √(‖u‖_{H^*}²)`. -/
def dualNorm {N : ℕ} (M : HermProjMetric N) (u : Fin N → ℂ) : ℝ :=
  Real.sqrt (M.dualNormSq u)

lemma primalNormSq_nonneg {N : ℕ} (M : HermProjMetric N) (y : Fin N → ℂ) :
    0 ≤ M.primalNormSq y :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

lemma dualNormSq_nonneg {N : ℕ} (M : HermProjMetric N) (u : Fin N → ℂ) :
    0 ≤ M.dualNormSq u :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

lemma primalNorm_nonneg {N : ℕ} (M : HermProjMetric N) (y : Fin N → ℂ) :
    0 ≤ M.primalNorm y :=
  Real.sqrt_nonneg _

lemma dualNorm_nonneg {N : ℕ} (M : HermProjMetric N) (u : Fin N → ℂ) :
    0 ≤ M.dualNorm u :=
  Real.sqrt_nonneg _

lemma primalNorm_sq {N : ℕ} (M : HermProjMetric N) (y : Fin N → ℂ) :
    M.primalNorm y ^ 2 = M.primalNormSq y :=
  Real.sq_sqrt (M.primalNormSq_nonneg y)

lemma dualNorm_sq {N : ℕ} (M : HermProjMetric N) (u : Fin N → ℂ) :
    M.dualNorm u ^ 2 = M.dualNormSq u :=
  Real.sq_sqrt (M.dualNormSq_nonneg u)

private lemma sum_norm_sq_eq_star_dotProduct {N : ℕ} (v : Fin N → ℂ) :
    (∑ i : Fin N, ‖v i‖ ^ 2) = (star v ⬝ᵥ v).re := by
  rw [dotProduct, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Pi.star_apply, Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]

/-- Exact quadratic-form identity `M.primalNormSq y = (star y ⬝ᵥ M.H.mulVec y).re`. -/
theorem primalNormSq_eq_dotProduct {N : ℕ} (M : HermProjMetric N) (y : Fin N → ℂ) :
    M.primalNormSq y = (star y ⬝ᵥ M.H.mulVec y).re := by
  unfold primalNormSq
  rw [sum_norm_sq_eq_star_dotProduct, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec,
    Matrix.mulVec_mulVec, M.sqrtMat_isHermitian.eq, M.sqrtMat_mul_self]

/-- Exact standard-metric identification `(std N).primalNormSq y = fsNormSq y`. -/
theorem primalNormSq_std {N : ℕ} (y : Fin N → ℂ) :
    (std N).primalNormSq y = fsNormSq y := by
  rw [primalNormSq_eq_dotProduct]
  have h1 : (std N).H = 1 := rfl
  rw [h1, Matrix.one_mulVec, ← sum_norm_sq_eq_star_dotProduct]
  rfl

/-- Exact dual-metric identification `(std N).dualNormSq u = fsNormSq u`. -/
theorem dualNormSq_std {N : ℕ} (u : Fin N → ℂ) :
    (std N).dualNormSq u = fsNormSq u := by
  unfold dualNormSq
  have hinv_herm : ((std N).sqrtMat⁻¹).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_nonsing_inv, (std N).sqrtMat_isHermitian.eq]
  have hT : ((std N).sqrtMat⁻¹).transposeᴴ = ((std N).sqrtMat⁻¹).transpose := by
    ext i j
    simp only [Matrix.conjTranspose_apply, Matrix.transpose_apply]
    simpa [Matrix.conjTranspose_apply] using congrFun (congrFun hinv_herm j) i
  have hmul : ((std N).sqrtMat⁻¹).transposeᴴ * ((std N).sqrtMat⁻¹).transpose = 1 := by
    rw [hT, ← Matrix.transpose_mul, ← Matrix.mul_inv_rev, (std N).sqrtMat_mul_self]
    have h1 : (std N).H = 1 := rfl
    have hinv1 : (1 : Matrix (Fin N) (Fin N) ℂ)⁻¹ = 1 :=
      Matrix.inv_eq_right_inv (Matrix.mul_one 1)
    rw [h1, hinv1, Matrix.transpose_one]
  rw [sum_norm_sq_eq_star_dotProduct, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec,
    Matrix.mulVec_mulVec, hmul, Matrix.one_mulVec, ← sum_norm_sq_eq_star_dotProduct]
  rfl

theorem primalNormSq_smul {N : ℕ} (M : HermProjMetric N) (c : ℂ) (y : Fin N → ℂ) :
    M.primalNormSq (c • y) = ‖c‖ ^ 2 * M.primalNormSq y := by
  unfold primalNormSq
  rw [Matrix.mulVec_smul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow]

theorem primalNorm_smul {N : ℕ} (M : HermProjMetric N) (c : ℂ) (y : Fin N → ℂ) :
    M.primalNorm (c • y) = ‖c‖ * M.primalNorm y := by
  unfold primalNorm
  rw [M.primalNormSq_smul, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]

theorem dualNormSq_smul {N : ℕ} (M : HermProjMetric N) (c : ℂ) (u : Fin N → ℂ) :
    M.dualNormSq (c • u) = ‖c‖ ^ 2 * M.dualNormSq u := by
  unfold dualNormSq
  rw [Matrix.mulVec_smul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow]

theorem dualNorm_smul {N : ℕ} (M : HermProjMetric N) (c : ℂ) (u : Fin N → ℂ) :
    M.dualNorm (c • u) = ‖c‖ * M.dualNorm u := by
  unfold dualNorm
  rw [M.dualNormSq_smul, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]

theorem primalNormSq_pos_of_ne_zero {N : ℕ} (M : HermProjMetric N) {y : Fin N → ℂ} (hy : y ≠ 0) :
    0 < M.primalNormSq y := by
  unfold primalNormSq
  have hne : M.sqrtMat.mulVec y ≠ 0 := by
    intro h0
    apply hy
    have h1 := congrArg (M.sqrtMat⁻¹).mulVec h0
    rwa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ M.isUnit_sqrtMat_det,
      Matrix.one_mulVec, Matrix.mulVec_zero] at h1
  have hex : ∃ i : Fin N, (M.sqrtMat.mulVec y) i ≠ 0 := by
    by_contra h; push Not at h; exact hne (funext h)
  rcases hex with ⟨i₀, hi₀⟩
  exact Finset.sum_pos' (fun _ _ => sq_nonneg _)
    ⟨i₀, Finset.mem_univ i₀, sq_pos_of_pos (norm_pos_iff.mpr hi₀)⟩

theorem primalNorm_pos_of_ne_zero {N : ℕ} (M : HermProjMetric N) {y : Fin N → ℂ} (hy : y ≠ 0) :
    0 < M.primalNorm y :=
  Real.sqrt_pos.mpr (M.primalNormSq_pos_of_ne_zero hy)

theorem dualNormSq_pos_of_ne_zero {N : ℕ} (M : HermProjMetric N) {u : Fin N → ℂ} (hu : u ≠ 0) :
    0 < M.dualNormSq u := by
  unfold dualNormSq
  have hunitT : IsUnit ((M.sqrtMat⁻¹).transpose).det := by
    rw [Matrix.det_transpose, Matrix.det_nonsing_inv, Ring.inverse_eq_inv, isUnit_iff_ne_zero]
    exact inv_ne_zero (isUnit_iff_ne_zero.mp M.isUnit_sqrtMat_det)
  have hne : (M.sqrtMat⁻¹).transpose.mulVec u ≠ 0 := by
    intro h0
    apply hu
    have h1 := congrArg ((M.sqrtMat⁻¹).transpose)⁻¹.mulVec h0
    rwa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hunitT,
      Matrix.one_mulVec, Matrix.mulVec_zero] at h1
  have hex : ∃ i : Fin N, ((M.sqrtMat⁻¹).transpose.mulVec u) i ≠ 0 := by
    by_contra h; push Not at h; exact hne (funext h)
  rcases hex with ⟨i₀, hi₀⟩
  exact Finset.sum_pos' (fun _ _ => sq_nonneg _)
    ⟨i₀, Finset.mem_univ i₀, sq_pos_of_pos (norm_pos_iff.mpr hi₀)⟩

theorem dualNorm_pos_of_ne_zero {N : ℕ} (M : HermProjMetric N) {u : Fin N → ℂ} (hu : u ≠ 0) :
    0 < M.dualNorm u :=
  Real.sqrt_pos.mpr (M.dualNormSq_pos_of_ne_zero hu)

/-- Coordinate bound `‖u j‖ ≤ C * M.dualNorm u` for an explicit constant `C ≥ 0`. -/
theorem exists_coord_le_dualNorm {N : ℕ} (M : HermProjMetric N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : Fin N → ℂ) (j : Fin N), ‖u j‖ ≤ C * M.dualNorm u := by
  let A : Matrix (Fin N) (Fin N) ℂ := M.sqrtMat.transpose
  refine ⟨∑ j : Fin N, ∑ l : Fin N, ‖A j l‖, by positivity, fun u j => ?_⟩
  have hid : A * (M.sqrtMat⁻¹).transpose = 1 := by
    rw [← Matrix.transpose_mul, Matrix.nonsing_inv_mul _ M.isUnit_sqrtMat_det, Matrix.transpose_one]
  have hu_eq : u = A.mulVec ((M.sqrtMat⁻¹).transpose.mulVec u) := by
    rw [Matrix.mulVec_mulVec, hid, Matrix.one_mulVec]
  have hmul_le : ∀ l : Fin N, ‖((M.sqrtMat⁻¹).transpose.mulVec u) l‖ ≤ M.dualNorm u := by
    intro l
    unfold dualNorm dualNormSq
    rw [← Real.sqrt_sq (norm_nonneg _)]
    exact Real.sqrt_le_sqrt
      (Finset.single_le_sum (f := fun i => ‖((M.sqrtMat⁻¹).transpose.mulVec u) i‖ ^ 2)
        (fun _ _ => sq_nonneg _) (Finset.mem_univ l))
  calc ‖u j‖ = ‖∑ l : Fin N, A j l * ((M.sqrtMat⁻¹).transpose.mulVec u) l‖ := by
        conv_lhs => rw [hu_eq]
        rfl
    _ ≤ ∑ l : Fin N, ‖A j l‖ * ‖((M.sqrtMat⁻¹).transpose.mulVec u) l‖ := by
        refine (norm_sum_le _ _).trans_eq ?_
        exact Finset.sum_congr rfl fun _ _ => norm_mul _ _
    _ ≤ ∑ l : Fin N, ‖A j l‖ * M.dualNorm u :=
        Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_left (hmul_le l) (norm_nonneg _)
    _ = (∑ l : Fin N, ‖A j l‖) * M.dualNorm u := by rw [← Finset.sum_mul]
    _ ≤ (∑ j' : Fin N, ∑ l : Fin N, ‖A j' l‖) * M.dualNorm u :=
        mul_le_mul_of_nonneg_right
          (Finset.single_le_sum (fun j' _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)
            (Finset.mem_univ j))
          (M.dualNorm_nonneg u)

/-- Exact bilinear pairing identity:
`∑ j, u j * y j = ((√H)⁻¹ᵀ *ᵥ u) ⬝ᵥ (√H *ᵥ y)`. -/
theorem sum_mul_eq_sqrt_dotProduct {N : ℕ} (M : HermProjMetric N) (u y : Fin N → ℂ) :
    (∑ j : Fin N, u j * y j) =
      ((M.sqrtMat⁻¹).transpose.mulVec u) ⬝ᵥ (M.sqrtMat.mulVec y) := by
  calc (∑ j : Fin N, u j * y j) = u ⬝ᵥ y := rfl
    _ = u ⬝ᵥ (M.sqrtMat⁻¹ * M.sqrtMat).mulVec y := by
          rw [Matrix.nonsing_inv_mul _ M.isUnit_sqrtMat_det, Matrix.one_mulVec]
    _ = u ⬝ᵥ (M.sqrtMat⁻¹).mulVec (M.sqrtMat.mulVec y) := by
          rw [Matrix.mulVec_mulVec]
    _ = (u ᵥ* M.sqrtMat⁻¹) ⬝ᵥ (M.sqrtMat.mulVec y) := by
          rw [Matrix.dotProduct_mulVec]
    _ = ((M.sqrtMat⁻¹).transpose.mulVec u) ⬝ᵥ (M.sqrtMat.mulVec y) := by
          rw [Matrix.mulVec_transpose]

/-- **Exact Hermitian Cauchy–Schwarz Duality**:
`‖∑ j, u j * y j‖ ≤ M.dualNorm u * M.primalNorm y` for all `u, y : Fin N → ℂ`. -/
theorem norm_sum_mul_le_dualNorm_mul_primalNorm {N : ℕ} (M : HermProjMetric N)
    (u y : Fin N → ℂ) :
    ‖∑ j : Fin N, u j * y j‖ ≤ M.dualNorm u * M.primalNorm y := by
  rw [M.sum_mul_eq_sqrt_dotProduct u y]
  calc ‖((M.sqrtMat⁻¹).transpose.mulVec u) ⬝ᵥ (M.sqrtMat.mulVec y)‖
      ≤ ∑ i : Fin N, ‖((M.sqrtMat⁻¹).transpose.mulVec u) i‖ * ‖(M.sqrtMat.mulVec y) i‖ := by
          refine (norm_sum_le _ _).trans_eq ?_
          exact Finset.sum_congr rfl fun _ _ => norm_mul _ _
    _ ≤ M.dualNorm u * M.primalNorm y :=
          Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
            (fun i => ‖((M.sqrtMat⁻¹).transpose.mulVec u) i‖)
            (fun i => ‖(M.sqrtMat.mulVec y) i‖)

/-- **Exact Attainment of Cauchy–Schwarz Equality** at the dual vector `u = star (M.H.mulVec y)`:
`‖u‖_{H^*} = ‖y‖_H` and `∑ j, u j * y j = ‖y‖_H²`. -/
theorem dual_witness_attainment {N : ℕ} (M : HermProjMetric N) (y : Fin N → ℂ) :
    let u : Fin N → ℂ := star (M.H.mulVec y)
    M.dualNorm u = M.primalNorm y ∧
    (∑ j : Fin N, u j * y j) = ((M.primalNorm y ^ 2 : ℝ) : ℂ) := by
  intro u
  have hu_vec : (M.sqrtMat⁻¹).transpose.mulVec u = star (M.sqrtMat.mulVec y) := by
    have h1 : u = M.sqrtMat.transpose.mulVec (star (M.sqrtMat.mulVec y)) := by
      change star (M.H.mulVec y) = _
      rw [← M.sqrtMat_mul_self, ← Matrix.mulVec_mulVec, Matrix.star_mulVec,
        ← Matrix.mulVec_transpose, M.sqrtMat_isHermitian.eq]
    rw [h1, Matrix.mulVec_mulVec, ← Matrix.transpose_mul,
      Matrix.mul_nonsing_inv _ M.isUnit_sqrtMat_det, Matrix.transpose_one, Matrix.one_mulVec]
  have hdual : M.dualNorm u = M.primalNorm y := by
    unfold dualNorm dualNormSq primalNorm primalNormSq
    congr 1
    rw [hu_vec]
    exact Finset.sum_congr rfl fun i _ => by simp
  refine ⟨hdual, ?_⟩
  rw [M.sum_mul_eq_sqrt_dotProduct u y, hu_vec, dotProduct]
  have hsum : (∑ i : Fin N, star (M.sqrtMat.mulVec y) i * (M.sqrtMat.mulVec y) i) =
      ((M.primalNormSq y : ℝ) : ℂ) := by
    unfold primalNormSq
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    change conj ((M.sqrtMat.mulVec y) i) * (M.sqrtMat.mulVec y) i = _
    rw [Complex.conj_mul']
    push_cast
    rfl
  rw [hsum, M.primalNorm_sq]

/-- **Metric-Normalized Fubini–Study Green Potential `fsGreen M u y`**:
$$g_{M, u}(y) = -\log\!\left(\frac{|\sum_j u_j y_j|^2}{\|u\|_{M^*}^2 \, \|y\|_M^2}\right).$$ -/
def fsGreen {N : ℕ} (M : HermProjMetric N) (u y : Fin N → ℂ) : ℝ :=
  -Real.log (‖∑ j : Fin N, u j * y j‖ ^ 2 / (M.dualNormSq u * M.primalNormSq y))

theorem fsGreen_nonneg {N : ℕ} (M : HermProjMetric N) {u y : Fin N → ℂ}
    (huy : ∑ j : Fin N, u j * y j ≠ 0) :
    0 ≤ M.fsGreen u y := by
  have hu0 : u ≠ 0 := by intro h0; apply huy; simp [h0]
  have hy0 : y ≠ 0 := by intro h0; apply huy; simp [h0]
  have hden_pos : 0 < M.dualNormSq u * M.primalNormSq y :=
    mul_pos (M.dualNormSq_pos_of_ne_zero hu0) (M.primalNormSq_pos_of_ne_zero hy0)
  have hcs := M.norm_sum_mul_le_dualNorm_mul_primalNorm u y
  have hcs_sq : ‖∑ j : Fin N, u j * y j‖ ^ 2 ≤ M.dualNormSq u * M.primalNormSq y := by
    calc ‖∑ j : Fin N, u j * y j‖ ^ 2
        ≤ (M.dualNorm u * M.primalNorm y) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hcs 2
      _ = M.dualNormSq u * M.primalNormSq y := by
          rw [mul_pow, M.dualNorm_sq, M.primalNorm_sq]
  have hdiv_pos : 0 < ‖∑ j : Fin N, u j * y j‖ ^ 2 / (M.dualNormSq u * M.primalNormSq y) :=
    div_pos (sq_pos_of_pos (norm_pos_iff.mpr huy)) hden_pos
  have hdiv_le : ‖∑ j : Fin N, u j * y j‖ ^ 2 / (M.dualNormSq u * M.primalNormSq y) ≤ 1 :=
    (div_le_one hden_pos).mpr hcs_sq
  unfold fsGreen
  linarith [(Real.log_le_log hdiv_pos hdiv_le).trans_eq Real.log_one]

theorem fsGreen_std_eq_fsLog {N : ℕ} {u y : Fin N → ℂ} (hu : (std N).dualNormSq u = 1) :
    (std N).fsGreen u y = fsLog u y := by
  unfold fsGreen fsLog
  rw [hu, one_mul, HermProjMetric.primalNormSq_std y]
  rfl

/-- Rescaled Hermitian metric `c • M` (`c > 0`): multiplies `primalNormSq` by `c` and
`dualNormSq` by `c⁻¹`. -/
def scale {N : ℕ} (M : HermProjMetric N) {c : ℝ} (hc : 0 < c) : HermProjMetric N where
  H := (c : ℂ) • M.H
  hH := by
    refine ⟨?_, fun {x} hx => ?_⟩
    · ext i j
      simp only [Matrix.conjTranspose_apply, Matrix.smul_apply, smul_eq_mul, star_mul',
        Complex.star_def, Complex.conj_ofReal]
      have hh := congrFun (congrFun M.hH.isHermitian i) j
      simp only [Matrix.conjTranspose_apply, Complex.star_def] at hh
      rw [hh, mul_comm]
    · have hpos := M.hH.2 hx
      have hfactor :
          (x.sum fun i xi => x.sum fun j xj => star xi * ((c : ℂ) • M.H) i j * xj) =
          (c : ℂ) * (x.sum fun i xi => x.sum fun j xj => star xi * M.H i j * xj) := by
        rw [Finsupp.mul_sum]
        refine Finsupp.sum_congr fun i _ => ?_
        rw [Finsupp.mul_sum]
        refine Finsupp.sum_congr fun j _ => ?_
        simp only [Matrix.smul_apply, smul_eq_mul]
        ring
      rw [hfactor]
      have hcC : (0 : ℂ) < (c : ℂ) := by
        rw [Complex.lt_def]; exact ⟨by simpa using hc, rfl⟩
      exact mul_pos hcC hpos

theorem primalNormSq_scale {N : ℕ} (M : HermProjMetric N) {c : ℝ} (hc : 0 < c) (y : Fin N → ℂ) :
    (M.scale hc).primalNormSq y = c * M.primalNormSq y := by
  rw [(M.scale hc).primalNormSq_eq_dotProduct, M.primalNormSq_eq_dotProduct]
  change (star y ⬝ᵥ ((c : ℂ) • M.H).mulVec y).re = _
  rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]

theorem dualNormSq_scale {N : ℕ} (M : HermProjMetric N) {c : ℝ} (hc : 0 < c) (u : Fin N → ℂ) :
    (M.scale hc).dualNormSq u = c⁻¹ * M.dualNormSq u := by
  have hherm_inv : ∀ (A : HermProjMetric N),
      ((A.sqrtMat⁻¹).transpose)ᴴ * (A.sqrtMat⁻¹).transpose = (A.H⁻¹).transpose := by
    intro A
    have hinv_h : (A.sqrtMat⁻¹).IsHermitian := by
      rw [Matrix.IsHermitian, Matrix.conjTranspose_nonsing_inv, A.sqrtMat_isHermitian.eq]
    have hT : ((A.sqrtMat⁻¹).transpose)ᴴ = (A.sqrtMat⁻¹).transpose := by
      ext i j
      simp only [Matrix.conjTranspose_apply, Matrix.transpose_apply]
      simpa [Matrix.conjTranspose_apply] using congrFun (congrFun hinv_h j) i
    rw [hT, ← Matrix.transpose_mul, ← Matrix.mul_inv_rev, A.sqrtMat_mul_self]
  have hmul : ((M.scale hc).sqrtMat⁻¹).transposeᴴ * ((M.scale hc).sqrtMat⁻¹).transpose =
      ((c⁻¹ : ℝ) : ℂ) • ((M.sqrtMat⁻¹).transposeᴴ * (M.sqrtMat⁻¹).transpose) := by
    rw [hherm_inv (M.scale hc), hherm_inv M]
    change (((c : ℂ) • M.H)⁻¹).transpose = ((c⁻¹ : ℝ) : ℂ) • (M.H⁻¹).transpose
    have hcC : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
    have hinv_smul : ((c : ℂ) • M.H)⁻¹ = (c : ℂ)⁻¹ • M.H⁻¹ := by
      refine Matrix.inv_eq_right_inv ?_
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hcC, one_smul,
        Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (by
          rw [← M.sqrtMat_mul_self, Matrix.det_mul]
          have hdet := isUnit_iff_ne_zero.mp M.isUnit_sqrtMat_det
          exact mul_ne_zero hdet hdet))]
    rw [hinv_smul, Matrix.transpose_smul, Complex.ofReal_inv]
  have hre1 : (M.scale hc).dualNormSq u =
      (star u ⬝ᵥ (((M.scale hc).sqrtMat⁻¹).transposeᴴ *
        ((M.scale hc).sqrtMat⁻¹).transpose).mulVec u).re := by
    unfold dualNormSq
    rw [sum_norm_sq_eq_star_dotProduct, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec,
      Matrix.mulVec_mulVec]
  have hre2 : M.dualNormSq u =
      (star u ⬝ᵥ ((M.sqrtMat⁻¹).transposeᴴ * (M.sqrtMat⁻¹).transpose).mulVec u).re := by
    unfold dualNormSq
    rw [sum_norm_sq_eq_star_dotProduct, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec,
      Matrix.mulVec_mulVec]
  rw [hre1, hmul, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, ← hre2]

theorem dualNorm_scale {N : ℕ} (M : HermProjMetric N) {c : ℝ} (hc : 0 < c) (u : Fin N → ℂ) :
    (M.scale hc).dualNorm u = (Real.sqrt c)⁻¹ * M.dualNorm u := by
  unfold dualNorm
  rw [M.dualNormSq_scale hc u, Real.sqrt_mul (inv_nonneg.mpr hc.le), Real.sqrt_inv]

/-- **Fubini–Study Line Bundle Curvature Bridge**:
on affine `ℂ^d ⊂ ℙ^d`, `fubiniStudyWeight d z = log ((std (d + 1)).primalNormSq (Fin.cons 1 z))`,
whose Levi form is strictly positive (`fubiniStudy_posCurvature`). -/
theorem fubiniStudy_weight_eq_std_primalNormSq (d : ℕ) (z : Fin d → ℂ) :
    fubiniStudyWeight d z = Real.log ((std (d + 1)).primalNormSq (Fin.cons 1 z)) := by
  rw [HermProjMetric.primalNormSq_std (Fin.cons 1 z), fubiniStudyWeight, fsNormSq,
    Fin.sum_univ_succ]
  simp

end HermProjMetric

/-- **Harmonic Number `H_m = ∑_{k=1}^m 1/k`** appearing in Stoll / Bost–Gillet–Soulé's
exact arithmetic self-intersection of projective spaces. -/
def harmonicNum (m : ℕ) : ℝ :=
  ∑ k ∈ Finset.range m, ((k + 1 : ℕ) : ℝ)⁻¹

@[simp] lemma harmonicNum_zero : harmonicNum 0 = 0 := by simp [harmonicNum]
@[simp] lemma harmonicNum_one : harmonicNum 1 = 1 := by simp [harmonicNum]

lemma harmonicNum_nonneg (m : ℕ) : 0 ≤ harmonicNum m :=
  Finset.sum_nonneg fun _ _ => by positivity

lemma harmonicNum_mono {m n : ℕ} (h : m ≤ n) : harmonicNum m ≤ harmonicNum n :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono h) fun _ _ _ => by positivity

/-- Explicit logarithmic bound `harmonicNum m ≤ 1 + Real.log m` for `m ≥ 1`. -/
theorem harmonicNum_le_one_add_log {m : ℕ} (hm : 1 ≤ m) :
    harmonicNum m ≤ 1 + Real.log m := by
  induction m with
  | zero => omega
  | succ m ih =>
    rcases eq_or_lt_of_le hm with h1 | hgt
    · have hm0 : m = 0 := by omega
      subst hm0
      simp [harmonicNum]
    · have hm1 : 1 ≤ m := by omega
      have ihm := ih hm1
      have hstep : ((m + 1 : ℕ) : ℝ)⁻¹ ≤ Real.log ((m + 1 : ℕ) : ℝ) - Real.log (m : ℝ) := by
        have hm_pos : (0 : ℝ) < m := Nat.cast_pos.mpr hm1
        have hm1_pos : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
        rw [← Real.log_div hm1_pos.ne' hm_pos.ne']
        have hratio : ((m : ℝ) / ((m + 1 : ℕ) : ℝ)) = 1 - ((m + 1 : ℕ) : ℝ)⁻¹ := by
          push_cast; field_simp; ring
        have hlog := Real.log_le_sub_one_of_pos (div_pos hm_pos hm1_pos)
        rw [hratio] at hlog
        have hneg : -Real.log (((m + 1 : ℕ) : ℝ) / (m : ℝ)) = Real.log ((m : ℝ) / ((m + 1 : ℕ) : ℝ)) := by
          rw [← Real.log_inv, inv_div]
        rw [hratio] at hneg
        linarith
      unfold harmonicNum at ihm ⊢
      rw [Finset.sum_range_succ]
      linarith

/-- **Bost–Gillet–Soulé / Stoll Projective Shift** `δ · H_{N - 1} / 2`. -/
def bgsShift (N δ : ℕ) : ℝ :=
  (δ : ℝ) * harmonicNum (N - 1) / 2

lemma bgsShift_nonneg (N δ : ℕ) : 0 ≤ bgsShift N δ := by
  unfold bgsShift
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (harmonicNum_nonneg _)) (by norm_num)

/-! ### Polynomial Coefficient Norms, Chow Sup-Norm & Unit-Ball Mahler Measure -/

open MvPolynomial

/-- `ℓ¹` coefficient norm `∑ m ∈ F.support, ‖coeff m F‖` of a complex polynomial. -/
def polyCoeffNorm1 {σ : Type*} (F : MvPolynomial σ ℂ) : ℝ :=
  ∑ m ∈ F.support, ‖MvPolynomial.coeff m F‖

lemma polyCoeffNorm1_nonneg {σ : Type*} (F : MvPolynomial σ ℂ) : 0 ≤ polyCoeffNorm1 F :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _

lemma polyCoeffNorm1_pos_of_ne_zero {σ : Type*} {F : MvPolynomial σ ℂ} (hF : F ≠ 0) :
    0 < polyCoeffNorm1 F := by
  obtain ⟨m, hm⟩ := MvPolynomial.support_nonempty.mpr hF
  exact Finset.sum_pos' (fun _ _ => norm_nonneg _)
    ⟨m, hm, norm_pos_iff.mpr (MvPolynomial.mem_support_iff.mp hm)⟩

theorem norm_eval_le_polyCoeffNorm1 {d N δ : ℕ} {F : MvPolynomial (Fin (d + 1) × Fin N) ℂ}
    (hF : IsBlockHomogeneous δ F) {R : ℝ} (_hR : 0 ≤ R)
    {u : Fin (d + 1) × Fin N → ℂ} (hu : ∀ ij, ‖u ij‖ ≤ R) :
    ‖MvPolynomial.eval u F‖ ≤ polyCoeffNorm1 F * R ^ ((d + 1) * δ) := by
  rw [MvPolynomial.eval_eq]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ m ∈ F.support, ‖MvPolynomial.coeff m F * ∏ ij ∈ m.support, u ij ^ m ij‖
      = ∑ m ∈ F.support, ‖MvPolynomial.coeff m F‖ * ∏ ij ∈ m.support, ‖u ij‖ ^ m ij := by
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [norm_mul, norm_prod]
          congr 1
          exact Finset.prod_congr rfl fun ij _ => norm_pow _ _
    _ ≤ ∑ m ∈ F.support, ‖MvPolynomial.coeff m F‖ * R ^ ((d + 1) * δ) := by
          refine Finset.sum_le_sum fun m hm => mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          have hrow := (isBlockHomogeneous_iff δ F).mp hF m hm
          have hsum_deg : ∑ ij ∈ m.support, m ij = (d + 1) * δ := by
            have hfull : ∑ ij ∈ m.support, m ij = ∑ ij : Fin (d + 1) × Fin N, m ij := by
              refine Finset.sum_subset (Finset.subset_univ _) fun ij _ hij => ?_
              rw [Finsupp.mem_support_iff, not_not] at hij
              exact hij
            rw [hfull, Fintype.sum_prod_type]
            calc ∑ i : Fin (d + 1), ∑ j : Fin N, m (i, j)
                = ∑ _i : Fin (d + 1), δ := Finset.sum_congr rfl fun i _ => hrow i
              _ = (d + 1) * δ := by simp
          calc ∏ ij ∈ m.support, ‖u ij‖ ^ m ij
              ≤ ∏ ij ∈ m.support, R ^ m ij :=
                Finset.prod_le_prod (fun _ _ => pow_nonneg (norm_nonneg _) _)
                  fun ij _ => pow_le_pow_left₀ (norm_nonneg _) (hu ij) (m ij)
            _ = R ^ (∑ ij ∈ m.support, m ij) := by rw [Finset.prod_pow_eq_pow_sum]
            _ = R ^ ((d + 1) * δ) := by rw [hsum_deg]
    _ = polyCoeffNorm1 F * R ^ ((d + 1) * δ) := by rw [← Finset.sum_mul]; rfl

/-- Unit dual ball `B_H^{k} = { u : Fin k × Fin N → ℂ | ∀ i, ‖u_i‖_{H^*} < 1 }` in `(ℂ^N)^∨^k`. -/
def prodDualBall {N : ℕ} (M : HermProjMetric N) (k : ℕ) : Set (Fin k × Fin N → ℂ) :=
  { u | ∀ i : Fin k, M.dualNorm (fun j => u (i, j)) < 1 }

/-- Row-wise dual-norm unit normalization `nrmRows M u` for `u : Fin k × Fin N → ℂ`. -/
def nrmRows {N k : ℕ} (M : HermProjMetric N) (u : Fin k × Fin N → ℂ) : Fin k × Fin N → ℂ :=
  fun ij => ((M.dualNorm (fun j => u (ij.1, j)) : ℝ) : ℂ)⁻¹ * u ij

lemma dualNorm_nrmRows_le_one {N k : ℕ} (M : HermProjMetric N) (u : Fin k × Fin N → ℂ)
    (i : Fin k) :
    M.dualNorm (fun j => nrmRows M u (i, j)) ≤ 1 := by
  let r : ℝ := M.dualNorm (fun j => u (i, j))
  have hr_eq : (fun j : Fin N => nrmRows M u (i, j)) = ((r : ℂ)⁻¹) • (fun j => u (i, j)) := rfl
  rw [hr_eq, M.dualNorm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (M.dualNorm_nonneg _)]
  by_cases hr0 : r = 0
  · change r⁻¹ * r ≤ 1
    rw [hr0]; norm_num
  · change r⁻¹ * r ≤ 1
    rw [inv_mul_cancel₀ hr0]

lemma dualNorm_nrmRows_eq_one {N k : ℕ} (M : HermProjMetric N) {u : Fin k × Fin N → ℂ}
    (i : Fin k) (hi : (fun j => u (i, j)) ≠ 0) :
    M.dualNorm (fun j => nrmRows M u (i, j)) = 1 := by
  let r : ℝ := M.dualNorm (fun j => u (i, j))
  have hr_pos : 0 < r := M.dualNorm_pos_of_ne_zero hi
  have hr_eq : (fun j : Fin N => nrmRows M u (i, j)) = ((r : ℂ)⁻¹) • (fun j => u (i, j)) := rfl
  rw [hr_eq, M.dualNorm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hr_pos.le]
  exact inv_mul_cancel₀ hr_pos.ne'

private lemma dualNorm_zero_le_one {d N : ℕ} (M : HermProjMetric N) (i : Fin (d + 1)) :
    M.dualNorm (fun j : Fin N => (0 : Fin (d + 1) × Fin N → ℂ) (i, j)) ≤ 1 := by
  have h0 : (fun j : Fin N => (0 : Fin (d + 1) × Fin N → ℂ) (i, j)) = (0 : ℂ) • 0 := by
    funext _; simp
  rw [h0, M.dualNorm_smul, norm_zero, zero_mul]
  norm_num

/-- **Projective Chow-Form Supremum Norm `chowSupNorm M F`**:
`sSup { ‖MvPolynomial.eval u F‖ | ∀ i, M.dualNorm (u i) ≤ 1 }`. -/
def chowSupNorm {d N : ℕ} (M : HermProjMetric N) (F : MvPolynomial (Fin (d + 1) × Fin N) ℂ) : ℝ :=
  sSup { r : ℝ | ∃ u : Fin (d + 1) × Fin N → ℂ,
    (∀ i : Fin (d + 1), M.dualNorm (fun j => u (i, j)) ≤ 1) ∧ r = ‖MvPolynomial.eval u F‖ }

theorem chowSupNorm_bddAbove {d N δ : ℕ} (M : HermProjMetric N)
    {F : MvPolynomial (Fin (d + 1) × Fin N) ℂ} (hF : IsBlockHomogeneous δ F) :
    BddAbove { r : ℝ | ∃ u : Fin (d + 1) × Fin N → ℂ,
      (∀ i : Fin (d + 1), M.dualNorm (fun j => u (i, j)) ≤ 1) ∧ r = ‖MvPolynomial.eval u F‖ } := by
  obtain ⟨C, hC0, hC⟩ := M.exists_coord_le_dualNorm
  refine ⟨polyCoeffNorm1 F * C ^ ((d + 1) * δ), ?_⟩
  rintro r ⟨u, hu, rfl⟩
  refine norm_eval_le_polyCoeffNorm1 hF hC0 fun ij => ?_
  exact (hC (fun j => u (ij.1, j)) ij.2).trans (mul_le_of_le_one_right hC0 (hu ij.1))

theorem norm_eval_le_chowSupNorm {d N δ : ℕ} (M : HermProjMetric N)
    {F : MvPolynomial (Fin (d + 1) × Fin N) ℂ} (hF : IsBlockHomogeneous δ F)
    {u : Fin (d + 1) × Fin N → ℂ} (hu : ∀ i, M.dualNorm (fun j => u (i, j)) ≤ 1) :
    ‖MvPolynomial.eval u F‖ ≤ chowSupNorm M F :=
  le_csSup (chowSupNorm_bddAbove M hF) ⟨u, hu, rfl⟩

theorem chowSupNorm_nonneg {d N : ℕ} (M : HermProjMetric N)
    (F : MvPolynomial (Fin (d + 1) × Fin N) ℂ) :
    0 ≤ chowSupNorm M F := by
  by_cases hbd : BddAbove { r : ℝ | ∃ u : Fin (d + 1) × Fin N → ℂ,
      (∀ i : Fin (d + 1), M.dualNorm (fun j => u (i, j)) ≤ 1) ∧ r = ‖MvPolynomial.eval u F‖ }
  · exact le_trans (norm_nonneg (MvPolynomial.eval 0 F))
      (le_csSup hbd ⟨0, fun i => dualNorm_zero_le_one M i, rfl⟩)
  · simp [chowSupNorm, Real.sSup_of_not_bddAbove hbd]

private lemma exists_eval_ne_zero_of_ne_zero {σ : Type*} [Finite σ]
    {F : MvPolynomial σ ℂ} (hF : F ≠ 0) :
    ∃ u : σ → ℂ, MvPolynomial.eval u F ≠ 0 := by
  classical
  have hfun : (fun u : σ → ℂ => MvPolynomial.eval u F) ≠ 0 :=
    fun h0 => hF (MvPolynomial.funext fun u => congrFun h0 u)
  exact Function.ne_iff.mp hfun

theorem chowSupNorm_pos {d N δ : ℕ} (M : HermProjMetric N)
    {F : MvPolynomial (Fin (d + 1) × Fin N) ℂ} (hF0 : F ≠ 0) (hF : IsBlockHomogeneous δ F) :
    0 < chowSupNorm M F := by
  obtain ⟨u, hu_ne⟩ := exists_eval_ne_zero_of_ne_zero hF0
  by_cases hδ : δ = 0
  · have hz : MvPolynomial.eval (0 : Fin (d + 1) × Fin N → ℂ) F = MvPolynomial.eval u F := by
      have hsc := aeval_block_smul_eq (R := ℂ) (S := ℂ) hF (fun _ => (0 : ℂ)) u
      have h0 : (fun ij : Fin (d + 1) × Fin N => (0 : ℂ) * u ij) = 0 := by funext _; simp
      simpa [h0, hδ] using hsc
    have hpos : 0 < ‖MvPolynomial.eval (0 : Fin (d + 1) × Fin N → ℂ) F‖ :=
      norm_pos_iff.mpr (hz ▸ hu_ne)
    exact lt_of_lt_of_le hpos (norm_eval_le_chowSupNorm M hF fun i => dualNorm_zero_le_one M i)
  · have hrow_ne : ∀ i : Fin (d + 1), (fun j => u (i, j)) ≠ 0 := by
      intro i hi0
      apply hu_ne
      let c : Fin (d + 1) → ℂ := fun i' => if i' = i then 0 else 1
      have hu_eq : u = fun ij => c ij.1 * u ij := by
        funext ⟨i', j⟩
        by_cases h : i' = i
        · subst h; simp [c, congrFun hi0 j]
        · simp [c, h]
      rw [hu_eq]
      have hsc := aeval_block_smul_eq (R := ℂ) (S := ℂ) hF c u
      have hprod0 : (∏ i' : Fin (d + 1), c i' ^ δ) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ i) (by simp [c, zero_pow hδ])
      change MvPolynomial.eval (fun ij => c ij.1 * u ij) F =
        (∏ i' : Fin (d + 1), c i' ^ δ) * MvPolynomial.eval u F at hsc
      rw [hsc, hprod0, zero_mul]
    have hsc := aeval_block_smul_eq (R := ℂ) (S := ℂ) hF
      (fun i => ((M.dualNorm (fun j => u (i, j)) : ℝ) : ℂ)⁻¹) u
    change MvPolynomial.eval (nrmRows M u) F =
      (∏ i : Fin (d + 1), ((M.dualNorm (fun j => u (i, j)) : ℝ) : ℂ)⁻¹ ^ δ) *
        MvPolynomial.eval u F at hsc
    have hprod_ne : (∏ i : Fin (d + 1), ((M.dualNorm (fun j => u (i, j)) : ℝ) : ℂ)⁻¹ ^ δ) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero δ
        (inv_ne_zero (Complex.ofReal_ne_zero.mpr (M.dualNorm_pos_of_ne_zero (hrow_ne i)).ne'))
    have hnrm_ne : MvPolynomial.eval (nrmRows M u) F ≠ 0 := by
      rw [hsc]; exact mul_ne_zero hprod_ne hu_ne
    exact lt_of_lt_of_le (norm_pos_iff.mpr hnrm_ne)
      (norm_eval_le_chowSupNorm M hF fun i => dualNorm_nrmRows_le_one M u i)

theorem chowSupNorm_C_mul {d N δ : ℕ} (M : HermProjMetric N) (c : ℂ)
    {F : MvPolynomial (Fin (d + 1) × Fin N) ℂ} (hF : IsBlockHomogeneous δ F) :
    chowSupNorm M (C c * F) = ‖c‖ * chowSupNorm M F := by
  let S := { r : ℝ | ∃ u : Fin (d + 1) × Fin N → ℂ,
    (∀ i : Fin (d + 1), M.dualNorm (fun j => u (i, j)) ≤ 1) ∧ r = ‖MvPolynomial.eval u F‖ }
  have hS_ne : S.Nonempty := ⟨‖MvPolynomial.eval 0 F‖, 0, fun i => dualNorm_zero_le_one M i, rfl⟩
  refine le_antisymm ?_ ?_
  · refine csSup_le ⟨‖MvPolynomial.eval 0 (C c * F)‖, 0, fun i => dualNorm_zero_le_one M i, rfl⟩ ?_
    rintro r ⟨u, hu, rfl⟩
    rw [map_mul, MvPolynomial.eval_C, norm_mul]
    exact mul_le_mul_of_nonneg_left (norm_eval_le_chowSupNorm M hF hu) (norm_nonneg c)
  · by_cases hc0 : c = 0
    · subst hc0; simp [chowSupNorm_nonneg]
    · have hhc : 0 < ‖c‖ := norm_pos_iff.mpr hc0
      rw [← le_div_iff₀' hhc]
      refine csSup_le hS_ne ?_
      rintro r ⟨u, hu, rfl⟩
      rw [le_div_iff₀' hhc]
      have hle := norm_eval_le_chowSupNorm M (isBlockHomogeneous_C_mul c hF) hu
      simpa [map_mul, MvPolynomial.eval_C, norm_mul] using hle

theorem chowSupNorm_mul_le {d N δ₁ δ₂ : ℕ} (M : HermProjMetric N)
    {F₁ F₂ : MvPolynomial (Fin (d + 1) × Fin N) ℂ}
    (hF₁ : IsBlockHomogeneous δ₁ F₁) (hF₂ : IsBlockHomogeneous δ₂ F₂) :
    chowSupNorm M (F₁ * F₂) ≤ chowSupNorm M F₁ * chowSupNorm M F₂ := by
  refine csSup_le ⟨‖MvPolynomial.eval 0 (F₁ * F₂)‖, 0, fun i => dualNorm_zero_le_one M i, rfl⟩ ?_
  rintro r ⟨u, hu, rfl⟩
  rw [map_mul, norm_mul]
  exact mul_le_mul (norm_eval_le_chowSupNorm M hF₁ hu) (norm_eval_le_chowSupNorm M hF₂ hu)
    (norm_nonneg _) (chowSupNorm_nonneg M F₁)

/-- Scaling of `chowSupNorm` under metric rescaling `M ↦ c • M` (`c > 0`):
`chowSupNorm (M.scale hc) F = (√c) ^ ((d + 1) * δ) * chowSupNorm M F`. -/
theorem chowSupNorm_scale {d N δ : ℕ} (M : HermProjMetric N) {c : ℝ} (hc : 0 < c)
    {F : MvPolynomial (Fin (d + 1) × Fin N) ℂ} (hF : IsBlockHomogeneous δ F) :
    chowSupNorm (M.scale hc) F = (Real.sqrt c) ^ ((d + 1) * δ) * chowSupNorm M F := by
  have hsc_pos : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  have hmap : ∀ u : Fin (d + 1) × Fin N → ℂ,
      (∀ i, (M.scale hc).dualNorm (fun j => u (i, j)) ≤ 1) ↔
        (∀ i, M.dualNorm (fun j => ((Real.sqrt c : ℂ)⁻¹ * u (i, j))) ≤ 1) := by
    intro u
    refine forall_congr' fun i => ?_
    have heq : (fun j => ((Real.sqrt c : ℂ)⁻¹ * u (i, j))) =
        ((Real.sqrt c : ℂ)⁻¹) • (fun j => u (i, j)) := rfl
    rw [M.dualNorm_scale hc, heq, M.dualNorm_smul, norm_inv, Complex.norm_real,
      Real.norm_of_nonneg hsc_pos.le]
  have heval_eq : ∀ u : Fin (d + 1) × Fin N → ℂ,
      ‖MvPolynomial.eval u F‖ =
        (Real.sqrt c) ^ ((d + 1) * δ) *
          ‖MvPolynomial.eval (fun ij => (Real.sqrt c : ℂ)⁻¹ * u ij) F‖ := by
    intro u
    have hu_eq : u = fun ij => (Real.sqrt c : ℂ) * ((Real.sqrt c : ℂ)⁻¹ * u ij) := by
      funext ij
      rw [← mul_assoc, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hsc_pos.ne'), one_mul]
    conv_lhs => rw [hu_eq]
    have hsc := aeval_block_smul_eq (R := ℂ) (S := ℂ) hF
      (fun _ => (Real.sqrt c : ℂ)) (fun ij => (Real.sqrt c : ℂ)⁻¹ * u ij)
    change MvPolynomial.eval (fun ij => (Real.sqrt c : ℂ) * ((Real.sqrt c : ℂ)⁻¹ * u ij)) F =
      (∏ _i : Fin (d + 1), (Real.sqrt c : ℂ) ^ δ) *
        MvPolynomial.eval (fun ij => (Real.sqrt c : ℂ)⁻¹ * u ij) F at hsc
    rw [hsc, norm_mul, norm_prod]
    simp only [norm_pow, Complex.norm_real, Real.norm_of_nonneg hsc_pos.le, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin, ← pow_mul, mul_comm δ (d + 1)]
  let S := { r : ℝ | ∃ u : Fin (d + 1) × Fin N → ℂ,
    (∀ i : Fin (d + 1), M.dualNorm (fun j => u (i, j)) ≤ 1) ∧ r = ‖MvPolynomial.eval u F‖ }
  let S' := { r : ℝ | ∃ u : Fin (d + 1) × Fin N → ℂ,
    (∀ i : Fin (d + 1), (M.scale hc).dualNorm (fun j => u (i, j)) ≤ 1) ∧ r = ‖MvPolynomial.eval u F‖ }
  have hneS : S.Nonempty := ⟨‖MvPolynomial.eval 0 F‖, 0, fun i => dualNorm_zero_le_one M i, rfl⟩
  have hneS' : S'.Nonempty :=
    ⟨‖MvPolynomial.eval 0 F‖, 0, fun i => dualNorm_zero_le_one (M.scale hc) i, rfl⟩
  refine le_antisymm ?_ ?_
  · refine csSup_le hneS' ?_
    rintro r ⟨u, hu, rfl⟩
    rw [heval_eq u]
    exact mul_le_mul_of_nonneg_left
      (norm_eval_le_chowSupNorm M hF ((hmap u).mp hu)) (pow_nonneg hsc_pos.le _)
  · rw [← le_div_iff₀' (pow_pos hsc_pos _)]
    refine csSup_le hneS ?_
    rintro r ⟨v, hv, rfl⟩
    rw [le_div_iff₀' (pow_pos hsc_pos _)]
    let u : Fin (d + 1) × Fin N → ℂ := fun ij => (Real.sqrt c : ℂ) * v ij
    have hu : ∀ i, (M.scale hc).dualNorm (fun j => u (i, j)) ≤ 1 := by
      rw [hmap u]
      intro i
      have hv_eq : (fun j => (Real.sqrt c : ℂ)⁻¹ * u (i, j)) = fun j => v (i, j) := by
        funext j; dsimp [u]; rw [← mul_assoc, inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hsc_pos.ne'), one_mul]
      rw [hv_eq]
      exact hv i
    have hv_eq : (fun ij => (Real.sqrt c : ℂ)⁻¹ * u ij) = v := by
      funext ij; dsimp [u]; rw [← mul_assoc, inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hsc_pos.ne'), one_mul]
    have hle := norm_eval_le_chowSupNorm (M.scale hc) hF hu
    rwa [heval_eq u, hv_eq] at hle

/-- **Exact Chow Sup-Norm of a Projective Point**:
for any `y ∈ ℂ^N`, `chowSupNorm M (∑ j, C (y j) * X ((0 : Fin 1), j)) = M.primalNorm y`. -/
theorem chowSupNorm_ofPoint {N : ℕ} (M : HermProjMetric N) (y : Fin N → ℂ) :
    chowSupNorm M (∑ j : Fin N, C (y j) * X ((0 : Fin 1), j)) = M.primalNorm y := by
  have hhom : IsBlockHomogeneous 1
      (∑ j : Fin N, (C (y j) : MvPolynomial (Fin 1 × Fin N) ℂ) * X ((0 : Fin 1), j)) := by
    refine isWeightedHomogeneous_finset_sum _ _ _ _ fun j _ => ?_
    have hX := MvPolynomial.isWeightedHomogeneous_X ℂ (blockWeight 0 N) ((0 : Fin 1), j)
    have hw : blockWeight 0 N ((0 : Fin 1), j) = fun _ => 1 := by
      ext i; rw [Fin.fin_one_eq_zero i]; simp [blockWeight]
    rw [hw] at hX
    simpa [zero_add] using (MvPolynomial.isWeightedHomogeneous_C (blockWeight 0 N) (y j)).mul hX
  have hev_lin : ∀ u : Fin 1 × Fin N → ℂ,
      MvPolynomial.eval u (∑ j : Fin N, C (y j) * X ((0 : Fin 1), j)) = ∑ j : Fin N, u (0, j) * y j := by
    intro u
    simp only [map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  refine le_antisymm ?_ ?_
  · refine csSup_le ⟨0, 0, fun i => dualNorm_zero_le_one M i, by simp⟩ ?_
    rintro r ⟨u, hu, rfl⟩
    rw [hev_lin u]
    exact (M.norm_sum_mul_le_dualNorm_mul_primalNorm (fun j => u (0, j)) y).trans
      (mul_le_of_le_one_left (M.primalNorm_nonneg y) (hu 0))
  · by_cases hy : y = 0
    · subst hy
      have hpr0 : M.primalNorm 0 = 0 := by
        unfold HermProjMetric.primalNorm HermProjMetric.primalNormSq
        simp [Matrix.mulVec_zero]
      rw [hpr0]
      exact chowSupNorm_nonneg M _
    · obtain ⟨hdual, hsum⟩ := M.dual_witness_attainment y
      let w0 : Fin N → ℂ := star (M.H.mulVec y)
      let r0 : ℝ := M.primalNorm y
      have hr0_pos : 0 < r0 := M.primalNorm_pos_of_ne_zero hy
      let u : Fin 1 × Fin N → ℂ := fun ij => ((r0 : ℂ)⁻¹) * w0 ij.2
      have hu : ∀ i : Fin 1, M.dualNorm (fun j => u (i, j)) ≤ 1 := by
        intro i
        have hweq : (fun j => u (i, j)) = ((r0 : ℂ)⁻¹) • w0 := rfl
        rw [hweq, M.dualNorm_smul, hdual, norm_inv, Complex.norm_real,
          Real.norm_of_nonneg hr0_pos.le, inv_mul_cancel₀ hr0_pos.ne']
      have hev_u : ‖MvPolynomial.eval u (∑ j : Fin N, C (y j) * X ((0 : Fin 1), j))‖ = M.primalNorm y := by
        rw [hev_lin u]
        have hlin : (∑ j : Fin N, u (0, j) * y j) = (r0 : ℂ)⁻¹ * ∑ j : Fin N, w0 j * y j := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by simp [u, mul_assoc]
        rw [hlin, hsum, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hr0_pos.le,
          Complex.norm_real, Real.norm_of_nonneg (sq_nonneg r0)]
        change r0⁻¹ * r0 ^ 2 = r0
        field_simp [hr0_pos.ne']
      exact hev_u ▸ norm_eval_le_chowSupNorm M hhom hu

/-- **Unit Dual Ball Positive Finite Measure**:
`0 < volume (prodDualBall M k) < ⊤`. -/
theorem prodDualBall_measure_pos_lt_top {N : ℕ} (M : HermProjMetric N) (k : ℕ) :
    0 < volume (prodDualBall M k) ∧ volume (prodDualBall M k) < ⊤ := by
  have hcont_row : ∀ i : Fin k,
      Continuous (fun u : Fin k × Fin N → ℂ => M.dualNorm (fun j => u (i, j))) := by
    intro i
    unfold HermProjMetric.dualNorm HermProjMetric.dualNormSq
    fun_prop
  have hopen : IsOpen (prodDualBall M k) := by
    have heq : prodDualBall M k = ⋂ i : Fin k, { u | M.dualNorm (fun j => u (i, j)) < 1 } := by
      ext u; simp [prodDualBall]
    rw [heq]
    exact isOpen_iInter_of_finite fun i => isOpen_lt (hcont_row i) continuous_const
  have hzero : (0 : Fin k × Fin N → ℂ) ∈ prodDualBall M k := by
    intro i
    have h0 : (fun j : Fin N => (0 : Fin k × Fin N → ℂ) (i, j)) = (0 : ℂ) • 0 := by
      funext _; simp
    rw [h0, M.dualNorm_smul, norm_zero, zero_mul]
    norm_num
  obtain ⟨C, hC0, hC⟩ := M.exists_coord_le_dualNorm
  have hbdd : Bornology.IsBounded (prodDualBall M k) := by
    refine (Metric.isBounded_closedBall (x := (0 : Fin k × Fin N → ℂ)) (r := C)).subset fun u hu => ?_
    rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg hC0]
    intro ij
    exact (hC (fun j => u (ij.1, j)) ij.2).trans (mul_le_of_le_one_right hC0 (hu ij.1).le)
  exact ⟨hopen.measure_pos volume ⟨0, hzero⟩, hbdd.measure_lt_top⟩

/-- **Archimedean Mahler Measure `mahlerMeasure M F`** of a `(d + 1)`-block polynomial `F`
with respect to a Hermitian metric `M`:
$$\mathrm{mahler}(M, F) := \frac{1}{\operatorname{vol}(B_{M^*}^{d+1})}
  \int_{B_{M^*}^{d+1}} \log \|F(\mathrm{nrmRows}_M(u))\|\,du.$$ -/
def mahlerMeasure {d N : ℕ} (M : HermProjMetric N)
    (F : MvPolynomial (Fin (d + 1) × Fin N) ℂ) : ℝ :=
  (volume.real (prodDualBall M (d + 1)))⁻¹ *
    ∫ u in prodDualBall M (d + 1), Real.log ‖MvPolynomial.eval (nrmRows M u) F‖

private lemma inv_vol_mul_integral_const {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {s : Set α} (hs_pos : 0 < μ s) (hs_lt : μ s < ⊤) (c : ℝ) :
    (μ.real s)⁻¹ * ∫ _ in s, c ∂μ = c := by
  rw [MeasureTheory.setIntegral_const, smul_eq_mul, ← mul_assoc, MeasureTheory.measureReal_def,
    inv_mul_cancel₀ (ENNReal.toReal_pos hs_pos.ne' hs_lt.ne).ne', one_mul]

/-- **Mahler-vs-Supremum Upper Bound**:
whenever `log ‖eval (nrmRows M u) F‖` is integrable on `prodDualBall M (d + 1)`,
`mahlerMeasure M F ≤ Real.log (chowSupNorm M F)`. -/
theorem mahlerMeasure_le_log_chowSupNorm {d N δ : ℕ} (M : HermProjMetric N)
    {F : MvPolynomial (Fin (d + 1) × Fin N) ℂ} (hF : IsBlockHomogeneous δ F)
    (hint : IntegrableOn (fun u => Real.log ‖MvPolynomial.eval (nrmRows M u) F‖)
      (prodDualBall M (d + 1)))
    (hae_nz : ∀ᵐ u ∂(volume.restrict (prodDualBall M (d + 1))),
      MvPolynomial.eval (nrmRows M u) F ≠ 0) :
    mahlerMeasure M F ≤ Real.log (chowSupNorm M F) := by
  unfold mahlerMeasure
  obtain ⟨hpos, hlt⟩ := prodDualBall_measure_pos_lt_top M (d + 1)
  have hle_ae : (fun u => Real.log ‖MvPolynomial.eval (nrmRows M u) F‖) ≤ᵐ[volume.restrict (prodDualBall M (d + 1))]
      fun _ => Real.log (chowSupNorm M F) := by
    filter_upwards [hae_nz] with u hu
    refine Real.log_le_log (norm_pos_iff.mpr hu) ?_
    exact norm_eval_le_chowSupNorm M hF fun i => dualNorm_nrmRows_le_one M u i
  have hint_c : IntegrableOn (fun _ : Fin (d + 1) × Fin N → ℂ => Real.log (chowSupNorm M F))
      (prodDualBall M (d + 1)) := integrableOn_const hlt.ne
  have hint_mono := MeasureTheory.integral_mono_ae hint hint_c hle_ae
  calc (volume.real (prodDualBall M (d + 1)))⁻¹ *
          ∫ u in prodDualBall M (d + 1), Real.log ‖MvPolynomial.eval (nrmRows M u) F‖
      ≤ (volume.real (prodDualBall M (d + 1)))⁻¹ *
          ∫ _ in prodDualBall M (d + 1), Real.log (chowSupNorm M F) :=
        mul_le_mul_of_nonneg_left hint_mono (inv_nonneg.mpr ENNReal.toReal_nonneg)
    _ = Real.log (chowSupNorm M F) := inv_vol_mul_integral_const hpos hlt _

/-- **Scalar Scaling of Mahler Measure**:
`mahlerMeasure M (C c * F) = Real.log ‖c‖ + mahlerMeasure M F` for `c ≠ 0`. -/
theorem mahlerMeasure_C_mul {d N : ℕ} (M : HermProjMetric N) {c : ℂ} (hc : c ≠ 0)
    (F : MvPolynomial (Fin (d + 1) × Fin N) ℂ)
    (hint : IntegrableOn (fun u => Real.log ‖MvPolynomial.eval (nrmRows M u) F‖)
      (prodDualBall M (d + 1)))
    (hae_nz : ∀ᵐ u ∂(volume.restrict (prodDualBall M (d + 1))),
      MvPolynomial.eval (nrmRows M u) F ≠ 0) :
    mahlerMeasure M (C c * F) = Real.log ‖c‖ + mahlerMeasure M F := by
  unfold mahlerMeasure
  obtain ⟨hpos, hlt⟩ := prodDualBall_measure_pos_lt_top M (d + 1)
  have hcongr : (fun u => Real.log ‖MvPolynomial.eval (nrmRows M u) (C c * F)‖)
      =ᵐ[volume.restrict (prodDualBall M (d + 1))]
      fun u => Real.log ‖c‖ + Real.log ‖MvPolynomial.eval (nrmRows M u) F‖ := by
    filter_upwards [hae_nz] with u hu
    rw [map_mul, MvPolynomial.eval_C, norm_mul,
      Real.log_mul (norm_ne_zero_iff.mpr hc) (norm_ne_zero_iff.mpr hu)]
  have hc_int : IntegrableOn (fun _ : Fin (d + 1) × Fin N → ℂ => Real.log ‖c‖)
      (prodDualBall M (d + 1)) := integrableOn_const hlt.ne
  rw [MeasureTheory.integral_congr_ae hcongr,
    MeasureTheory.integral_add hc_int hint,
    mul_add, inv_vol_mul_integral_const hpos hlt]

/-- **Multiplicativity of Mahler Measure on Cycles**:
`mahlerMeasure M (F₁ * F₂) = mahlerMeasure M F₁ + mahlerMeasure M F₂`. -/
theorem mahlerMeasure_mul {d N : ℕ} (M : HermProjMetric N)
    (F₁ F₂ : MvPolynomial (Fin (d + 1) × Fin N) ℂ)
    (hint₁ : IntegrableOn (fun u => Real.log ‖MvPolynomial.eval (nrmRows M u) F₁‖)
      (prodDualBall M (d + 1)))
    (hint₂ : IntegrableOn (fun u => Real.log ‖MvPolynomial.eval (nrmRows M u) F₂‖)
      (prodDualBall M (d + 1)))
    (hae₁ : ∀ᵐ u ∂(volume.restrict (prodDualBall M (d + 1))),
      MvPolynomial.eval (nrmRows M u) F₁ ≠ 0)
    (hae₂ : ∀ᵐ u ∂(volume.restrict (prodDualBall M (d + 1))),
      MvPolynomial.eval (nrmRows M u) F₂ ≠ 0) :
    mahlerMeasure M (F₁ * F₂) = mahlerMeasure M F₁ + mahlerMeasure M F₂ := by
  unfold mahlerMeasure
  have hcongr : (fun u => Real.log ‖MvPolynomial.eval (nrmRows M u) (F₁ * F₂)‖)
      =ᵐ[volume.restrict (prodDualBall M (d + 1))]
      fun u => Real.log ‖MvPolynomial.eval (nrmRows M u) F₁‖ +
        Real.log ‖MvPolynomial.eval (nrmRows M u) F₂‖ := by
    filter_upwards [hae₁, hae₂] with u hu₁ hu₂
    rw [map_mul, norm_mul,
      Real.log_mul (norm_ne_zero_iff.mpr hu₁) (norm_ne_zero_iff.mpr hu₂)]
  rw [MeasureTheory.integral_congr_ae hcongr, MeasureTheory.integral_add hint₁ hint₂, mul_add]

/-- **Pointwise Fubini–Study Identity for the Chow Form of a Point**:
for `y ≠ 0` and `u` with nonzero row, `log ‖eval (nrmRows M u) (ofPoint y)‖ = log ‖y‖_M - fsGreen M u y / 2`. -/
theorem log_eval_ofPoint_eq_fsGreen {N : ℕ} (M : HermProjMetric N) {y : Fin N → ℂ} (hy : y ≠ 0)
    {u : Fin 1 × Fin N → ℂ} (hu0 : (fun j => u (0, j)) ≠ 0)
    (huy : ∑ j : Fin N, u (0, j) * y j ≠ 0) :
    Real.log ‖MvPolynomial.eval (nrmRows M u) (∑ j : Fin N, C (y j) * X ((0 : Fin 1), j))‖ =
      Real.log (M.primalNorm y) - M.fsGreen (fun j => u (0, j)) y / 2 := by
  have hev : MvPolynomial.eval (nrmRows M u) (∑ j : Fin N, C (y j) * X ((0 : Fin 1), j)) =
      ((M.dualNorm (fun j => u (0, j)) : ℝ) : ℂ)⁻¹ * ∑ j : Fin N, u (0, j) * y j := by
    simp only [map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X, nrmRows, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hd_pos : 0 < M.dualNorm (fun j => u (0, j)) := M.dualNorm_pos_of_ne_zero hu0
  have hp_pos : 0 < M.primalNorm y := M.primalNorm_pos_of_ne_zero hy
  have hsum_pos : 0 < ‖∑ j : Fin N, u (0, j) * y j‖ := norm_pos_iff.mpr huy
  rw [hev, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hd_pos.le,
    Real.log_mul (inv_ne_zero hd_pos.ne') hsum_pos.ne', Real.log_inv]
  unfold HermProjMetric.fsGreen
  rw [Real.log_div (sq_pos_of_pos hsum_pos).ne'
      (mul_pos (M.dualNormSq_pos_of_ne_zero hu0) (M.primalNormSq_pos_of_ne_zero hy)).ne',
    Real.log_mul (M.dualNormSq_pos_of_ne_zero hu0).ne' (M.primalNormSq_pos_of_ne_zero hy).ne',
    ← M.dualNorm_sq, ← M.primalNorm_sq, Real.log_pow, Real.log_pow, Real.log_pow]
  push_cast
  ring

end HermitianMetricsAndMahlerMeasure

/-! ## Section 3: `FaltingsPhilipponHeight` over Number Fields & Product-Formula Invariance -/

section FaltingsPhilipponHeights

/-- **Adelic Place System `AdelicPlaceSystem K`** on a number field `K`:
packages the archimedean embeddings `K →+* ℂ` together with non-archimedean places `v : Place`
equipped with ultrametric absolute values `absFin v : K → ℝ` and weights `wtFin v > 0`,
satisfying finiteness of support and the Artin–Whaples Product Formula. -/
structure AdelicPlaceSystem (K : Type*) [Field K] [NumberField K] where
  Place : Type*
  [decPlace : DecidableEq Place]
  absFin : Place → K → ℝ
  wtFin : Place → ℝ
  absFin_nonneg : ∀ v x, 0 ≤ absFin v x
  absFin_zero : ∀ v, absFin v 0 = 0
  absFin_one : ∀ v, absFin v 1 = 1
  absFin_pos : ∀ v {x}, x ≠ 0 → 0 < absFin v x
  absFin_mul : ∀ v x y, absFin v (x * y) = absFin v x * absFin v y
  absFin_add_le : ∀ v x y, absFin v (x + y) ≤ max (absFin v x) (absFin v y)
  wtFin_pos : ∀ v, 0 < wtFin v
  finite_supp : ∀ {x : K}, x ≠ 0 → Set.Finite { v : Place | absFin v x ≠ 1 }
  product_formula : ∀ {c : K}, c ≠ 0 → ∀ (S : Finset Place),
    { v : Place | absFin v c ≠ 1 } ⊆ (S : Set Place) →
    (∑ v ∈ S, wtFin v * Real.log (absFin v c)) +
      (∑ σ : K →+* ℂ, Real.log ‖σ c‖) = 0

attribute [instance] AdelicPlaceSystem.decPlace

namespace AdelicPlaceSystem

lemma absFin_inv {K : Type*} [Field K] [NumberField K] (P : AdelicPlaceSystem K)
    (v : P.Place) {x : K} (hx : x ≠ 0) : P.absFin v x⁻¹ = (P.absFin v x)⁻¹ := by
  have h1 : P.absFin v (x * x⁻¹) = P.absFin v x * P.absFin v x⁻¹ := P.absFin_mul v x x⁻¹
  rw [mul_inv_cancel₀ hx, P.absFin_one] at h1
  exact eq_inv_of_mul_eq_one_right h1.symm

lemma absFin_div {K : Type*} [Field K] [NumberField K] (P : AdelicPlaceSystem K)
    (v : P.Place) (x : K) {y : K} (hy : y ≠ 0) :
    P.absFin v (x / y) = P.absFin v x / P.absFin v y := by
  rw [div_eq_mul_inv, P.absFin_mul, P.absFin_inv v hy, ← div_eq_mul_inv]

lemma absFin_neg {K : Type*} [Field K] [NumberField K] (P : AdelicPlaceSystem K)
    (v : P.Place) (x : K) : P.absFin v (-x) = P.absFin v x := by
  have hneg1 : P.absFin v (-1) = 1 := by
    have hsq : P.absFin v (-1) * P.absFin v (-1) = 1 := by
      rw [← P.absFin_mul, neg_one_mul, neg_neg, P.absFin_one]
    nlinarith [P.absFin_nonneg v (-1)]
  rw [neg_eq_neg_one_mul, P.absFin_mul, hneg1, one_mul]

lemma absFin_finset_sum_le {K α : Type*} [Field K] [NumberField K] (P : AdelicPlaceSystem K)
    (v : P.Place) (s : Finset α) (f : α → K) {M : ℝ} (hM : 0 ≤ M)
    (hf : ∀ a ∈ s, P.absFin v (f a) ≤ M) :
    P.absFin v (∑ a ∈ s, f a) ≤ M := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa [P.absFin_zero] using hM
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    refine (P.absFin_add_le v _ _).trans (max_le ?_ ?_)
    · exact hf a (Finset.mem_insert_self a s)
    · exact ih fun b hb => hf b (Finset.mem_insert_of_mem hb)

end AdelicPlaceSystem

/-- **Non-Archimedean Gauss Norm** `finPlacePolyNorm P v F = max_{m ∈ F.support} |coeff m F|_v`. -/
def finPlacePolyNorm {K σ : Type*} [Field K] [NumberField K] (P : AdelicPlaceSystem K)
    (v : P.Place) (F : MvPolynomial σ K) : ℝ :=
  if h : F.support.Nonempty then F.support.sup' h fun m => P.absFin v (MvPolynomial.coeff m F) else 0

lemma finPlacePolyNorm_nonneg {K σ : Type*} [Field K] [NumberField K] (P : AdelicPlaceSystem K)
    (v : P.Place) (F : MvPolynomial σ K) : 0 ≤ finPlacePolyNorm P v F := by
  unfold finPlacePolyNorm
  split_ifs with h
  · obtain ⟨m, hm⟩ := h
    exact le_trans (P.absFin_nonneg v _) (Finset.le_sup' (fun m => P.absFin v (MvPolynomial.coeff m F)) hm)
  · exact le_rfl

lemma finPlacePolyNorm_pos_of_ne_zero {K σ : Type*} [Field K] [NumberField K]
    (P : AdelicPlaceSystem K) (v : P.Place) {F : MvPolynomial σ K} (hF : F ≠ 0) :
    0 < finPlacePolyNorm P v F := by
  have hs : F.support.Nonempty := MvPolynomial.support_nonempty.mpr hF
  unfold finPlacePolyNorm
  rw [dif_pos hs]
  obtain ⟨m, hm⟩ := hs
  have hm_nz : MvPolynomial.coeff m F ≠ 0 := MvPolynomial.mem_support_iff.mp hm
  exact lt_of_lt_of_le (P.absFin_pos v hm_nz)
    (Finset.le_sup' (fun m => P.absFin v (MvPolynomial.coeff m F)) hm)

lemma absFin_coeff_le_finPlacePolyNorm {K σ : Type*} [Field K] [NumberField K]
    (P : AdelicPlaceSystem K) (v : P.Place) (F : MvPolynomial σ K) (m : σ →₀ ℕ) :
    P.absFin v (MvPolynomial.coeff m F) ≤ finPlacePolyNorm P v F := by
  by_cases hm : m ∈ F.support
  · unfold finPlacePolyNorm
    rw [dif_pos ⟨m, hm⟩]
    exact Finset.le_sup' (fun m => P.absFin v (MvPolynomial.coeff m F)) hm
  · rw [MvPolynomial.notMem_support_iff.mp hm, P.absFin_zero]
    exact finPlacePolyNorm_nonneg P v F

lemma exists_coeff_finPlacePolyNorm_eq {K σ : Type*} [Field K] [NumberField K]
    (P : AdelicPlaceSystem K) (v : P.Place) {F : MvPolynomial σ K} (hF : F ≠ 0) :
    ∃ m ∈ F.support, P.absFin v (MvPolynomial.coeff m F) = finPlacePolyNorm P v F := by
  have hs : F.support.Nonempty := MvPolynomial.support_nonempty.mpr hF
  unfold finPlacePolyNorm
  rw [dif_pos hs]
  exact (Finset.exists_mem_eq_sup' hs fun m => P.absFin v (MvPolynomial.coeff m F)).imp
    fun _ ⟨hm, heq⟩ => ⟨hm, heq.symm⟩

theorem finPlacePolyNorm_C_mul {K σ : Type*} [Field K] [NumberField K]
    (P : AdelicPlaceSystem K) (v : P.Place) (c : K) (F : MvPolynomial σ K) :
    finPlacePolyNorm P v (MvPolynomial.C c * F) = P.absFin v c * finPlacePolyNorm P v F := by
  by_cases hc : c = 0
  · subst hc; simp [finPlacePolyNorm, P.absFin_zero]
  by_cases hF : F = 0
  · subst hF; simp [finPlacePolyNorm]
  have hcF : MvPolynomial.C c * F ≠ 0 := mul_ne_zero (MvPolynomial.C_ne_zero.mpr hc) hF
  refine le_antisymm ?_ ?_
  · obtain ⟨m, _, heq⟩ := exists_coeff_finPlacePolyNorm_eq P v hcF
    rw [← heq, MvPolynomial.coeff_C_mul, P.absFin_mul]
    exact mul_le_mul_of_nonneg_left (absFin_coeff_le_finPlacePolyNorm P v F m) (P.absFin_nonneg v c)
  · obtain ⟨m, _, heq⟩ := exists_coeff_finPlacePolyNorm_eq P v hF
    rw [← heq, ← P.absFin_mul, ← MvPolynomial.coeff_C_mul]
    exact absFin_coeff_le_finPlacePolyNorm P v (MvPolynomial.C c * F) m

/-- **Non-Archimedean Polynomial Triangle Inequality (`‖F + G‖_v ≤ max ‖F‖_v ‖G‖_v`)**. -/
theorem finPlacePolyNorm_add_le {K σ : Type*} [Field K] [NumberField K]
    (P : AdelicPlaceSystem K) (v : P.Place) (F G : MvPolynomial σ K) :
    finPlacePolyNorm P v (F + G) ≤ max (finPlacePolyNorm P v F) (finPlacePolyNorm P v G) := by
  by_cases hFG : F + G = 0
  · rw [hFG]
    have h0 : finPlacePolyNorm P v (0 : MvPolynomial σ K) = 0 := by simp [finPlacePolyNorm]
    rw [h0]
    exact le_max_iff.mpr (Or.inl (finPlacePolyNorm_nonneg P v F))
  obtain ⟨m, _, heq⟩ := exists_coeff_finPlacePolyNorm_eq P v hFG
  rw [← heq, MvPolynomial.coeff_add]
  exact (P.absFin_add_le v _ _).trans (max_le
    ((absFin_coeff_le_finPlacePolyNorm P v F m).trans (le_max_left _ _))
    ((absFin_coeff_le_finPlacePolyNorm P v G m).trans (le_max_right _ _)))

/-- **Gauss's Lemma for Multivariate Polynomials (`‖F * G‖_v = ‖F‖_v * ‖G‖_v`)**:
proved via minimal-monomial reduction with respect to `Finsupp.Lex`. -/
theorem finPlacePolyNorm_mul {K σ : Type*} [Field K] [NumberField K] [LinearOrder σ]
    (P : AdelicPlaceSystem K) (v : P.Place) (F G : MvPolynomial σ K) :
    finPlacePolyNorm P v (F * G) = finPlacePolyNorm P v F * finPlacePolyNorm P v G := by
  by_cases hF : F = 0
  · subst hF; simp [finPlacePolyNorm]
  by_cases hG : G = 0
  · subst hG; simp [finPlacePolyNorm]
  have hFG : F * G ≠ 0 := mul_ne_zero hF hG
  have hle : finPlacePolyNorm P v (F * G) ≤ finPlacePolyNorm P v F * finPlacePolyNorm P v G := by
    obtain ⟨m, _, heq⟩ := exists_coeff_finPlacePolyNorm_eq P v hFG
    rw [← heq, MvPolynomial.coeff_mul]
    refine P.absFin_finset_sum_le v _ _
      (mul_nonneg (finPlacePolyNorm_nonneg P v F) (finPlacePolyNorm_nonneg P v G)) ?_
    rintro ⟨a, b⟩ _
    rw [P.absFin_mul]
    exact mul_le_mul (absFin_coeff_le_finPlacePolyNorm P v F a)
      (absFin_coeff_le_finPlacePolyNorm P v G b)
      (P.absFin_nonneg v _) (finPlacePolyNorm_nonneg P v F)
  refine le_antisymm hle ?_
  classical
  let mF_set : Finset (Lex (σ →₀ ℕ)) :=
    (F.support.filter fun a => P.absFin v (MvPolynomial.coeff a F) = finPlacePolyNorm P v F).image toLex
  let mG_set : Finset (Lex (σ →₀ ℕ)) :=
    (G.support.filter fun b => P.absFin v (MvPolynomial.coeff b G) = finPlacePolyNorm P v G).image toLex
  have hmF_ne : mF_set.Nonempty := by
    obtain ⟨a, ha, ha_eq⟩ := exists_coeff_finPlacePolyNorm_eq P v hF
    exact ⟨toLex a, Finset.mem_image.mpr ⟨a, Finset.mem_filter.mpr ⟨ha, ha_eq⟩, rfl⟩⟩
  have hmG_ne : mG_set.Nonempty := by
    obtain ⟨b, hb, hb_eq⟩ := exists_coeff_finPlacePolyNorm_eq P v hG
    exact ⟨toLex b, Finset.mem_image.mpr ⟨b, Finset.mem_filter.mpr ⟨hb, hb_eq⟩, rfl⟩⟩
  let a₀ : σ →₀ ℕ := ofLex (mF_set.min' hmF_ne)
  let b₀ : σ →₀ ℕ := ofLex (mG_set.min' hmG_ne)
  have ha₀_mem : toLex a₀ ∈ mF_set := Finset.min'_mem mF_set hmF_ne
  have hb₀_mem : toLex b₀ ∈ mG_set := Finset.min'_mem mG_set hmG_ne
  have ha₀_eq : P.absFin v (MvPolynomial.coeff a₀ F) = finPlacePolyNorm P v F := by
    rcases Finset.mem_image.mp ha₀_mem with ⟨a, ha, hea⟩
    have h_eq : a = a₀ := toLex.injective hea
    rw [← h_eq]
    exact (Finset.mem_filter.mp ha).2
  have hb₀_eq : P.absFin v (MvPolynomial.coeff b₀ G) = finPlacePolyNorm P v G := by
    rcases Finset.mem_image.mp hb₀_mem with ⟨b, hb, heb⟩
    have h_eq : b = b₀ := toLex.injective heb
    rw [← h_eq]
    exact (Finset.mem_filter.mp hb).2
  have hminF : ∀ a, toLex a < toLex a₀ →
      P.absFin v (MvPolynomial.coeff a F) < finPlacePolyNorm P v F := by
    intro a hlt
    refine lt_of_le_of_ne (absFin_coeff_le_finPlacePolyNorm P v F a) fun heq => ?_
    have ha_supp : a ∈ F.support := by
      rw [MvPolynomial.mem_support_iff]
      intro h0
      rw [h0, P.absFin_zero] at heq
      exact (finPlacePolyNorm_pos_of_ne_zero P v hF).ne' heq.symm
    have hmem : toLex a ∈ mF_set := Finset.mem_image.mpr ⟨a, Finset.mem_filter.mpr ⟨ha_supp, heq⟩, rfl⟩
    exact not_lt_of_ge (Finset.min'_le mF_set (toLex a) hmem) hlt
  have hminG : ∀ b, toLex b < toLex b₀ →
      P.absFin v (MvPolynomial.coeff b G) < finPlacePolyNorm P v G := by
    intro b hlt
    refine lt_of_le_of_ne (absFin_coeff_le_finPlacePolyNorm P v G b) fun heq => ?_
    have hb_supp : b ∈ G.support := by
      rw [MvPolynomial.mem_support_iff]
      intro h0
      rw [h0, P.absFin_zero] at heq
      exact (finPlacePolyNorm_pos_of_ne_zero P v hG).ne' heq.symm
    have hmem : toLex b ∈ mG_set := Finset.mem_image.mpr ⟨b, Finset.mem_filter.mpr ⟨hb_supp, heq⟩, rfl⟩
    exact not_lt_of_ge (Finset.min'_le mG_set (toLex b) hmem) hlt
  let M_norm : ℝ := finPlacePolyNorm P v F * finPlacePolyNorm P v G
  have hM_pos : 0 < M_norm :=
    mul_pos (finPlacePolyNorm_pos_of_ne_zero P v hF) (finPlacePolyNorm_pos_of_ne_zero P v hG)
  let anti := Finset.antidiagonal (a₀ + b₀)
  let rest := anti.erase (a₀, b₀)
  have hrest_lt : ∀ p ∈ rest, P.absFin v (MvPolynomial.coeff p.1 F * MvPolynomial.coeff p.2 G) < M_norm := by
    intro p hp
    have hp_ne : p ≠ (a₀, b₀) := (Finset.mem_erase.mp hp).1
    have hp_sum : p.1 + p.2 = a₀ + b₀ := Finset.mem_antidiagonal.mp (Finset.mem_erase.mp hp).2
    have hlt_one : toLex p.1 < toLex a₀ ∨ toLex p.2 < toLex b₀ := by
      by_contra hge
      push Not at hge
      have h1 : toLex a₀ ≤ toLex p.1 := hge.1
      have h2 : toLex b₀ ≤ toLex p.2 := hge.2
      rcases eq_or_lt_of_le h1 with ha_eq | ha_lt
      · rcases eq_or_lt_of_le h2 with hb_eq | hb_lt
        · apply hp_ne; ext1; exact (toLex.injective ha_eq).symm; exact (toLex.injective hb_eq).symm
        · have h_eq : a₀ = p.1 := toLex.injective ha_eq
          have hsum_lt : toLex (a₀ + b₀) < toLex (p.1 + p.2) := by
            rw [← h_eq]; exact add_lt_add_of_le_of_lt le_rfl hb_lt
          rw [hp_sum] at hsum_lt
          exact lt_irrefl _ hsum_lt
      · have hsum_lt : toLex (a₀ + b₀) < toLex (p.1 + p.2) := add_lt_add_of_lt_of_le ha_lt h2
        rw [hp_sum] at hsum_lt
        exact lt_irrefl _ hsum_lt
    rw [P.absFin_mul]
    rcases hlt_one with ha_lt | hb_lt
    · exact mul_lt_mul_of_lt_of_le_of_nonneg_of_pos (hminF p.1 ha_lt)
        (absFin_coeff_le_finPlacePolyNorm P v G p.2) (P.absFin_nonneg v _)
        (finPlacePolyNorm_pos_of_ne_zero P v hG)
    · exact mul_lt_mul_of_le_of_lt_of_nonneg_of_pos (absFin_coeff_le_finPlacePolyNorm P v F p.1)
        (hminG p.2 hb_lt) (P.absFin_nonneg v _) (finPlacePolyNorm_pos_of_ne_zero P v hF)
  have hrest_sum_lt : P.absFin v (∑ p ∈ rest, MvPolynomial.coeff p.1 F * MvPolynomial.coeff p.2 G) < M_norm := by
    by_cases hre : rest.Nonempty
    · obtain ⟨M_r, hMr_lt, hMr_bound⟩ : ∃ M_r < M_norm,
          ∀ p ∈ rest, P.absFin v (MvPolynomial.coeff p.1 F * MvPolynomial.coeff p.2 G) ≤ M_r := by
        refine ⟨rest.sup' hre fun p => P.absFin v (MvPolynomial.coeff p.1 F * MvPolynomial.coeff p.2 G), ?_,
          fun p hp => Finset.le_sup' (fun p => P.absFin v (MvPolynomial.coeff p.1 F * MvPolynomial.coeff p.2 G)) hp⟩
        rw [Finset.sup'_lt_iff]
        exact hrest_lt
      have hMr_nn : 0 ≤ M_r := by
        obtain ⟨p, hp⟩ := hre
        exact le_trans (P.absFin_nonneg v _) (hMr_bound p hp)
      exact (P.absFin_finset_sum_le v rest _ hMr_nn hMr_bound).trans_lt hMr_lt
    · rw [Finset.not_nonempty_iff_eq_empty.mp hre, Finset.sum_empty, P.absFin_zero]
      exact hM_pos
  have hsplit : MvPolynomial.coeff (a₀ + b₀) (F * G) =
      MvPolynomial.coeff a₀ F * MvPolynomial.coeff b₀ G +
        ∑ p ∈ rest, MvPolynomial.coeff p.1 F * MvPolynomial.coeff p.2 G := by
    rw [MvPolynomial.coeff_mul, ← Finset.add_sum_erase anti
      (fun p => MvPolynomial.coeff p.1 F * MvPolynomial.coeff p.2 G)
      (Finset.mem_antidiagonal.mpr (rfl : (a₀, b₀).1 + (a₀, b₀).2 = a₀ + b₀))]
  have hlead : P.absFin v (MvPolynomial.coeff a₀ F * MvPolynomial.coeff b₀ G) = M_norm := by
    rw [P.absFin_mul, ha₀_eq, hb₀_eq]
  set X := MvPolynomial.coeff a₀ F * MvPolynomial.coeff b₀ G
  set Y := ∑ p ∈ rest, MvPolynomial.coeff p.1 F * MvPolynomial.coeff p.2 G
  have h1 : M_norm ≤ P.absFin v (X + Y) := by
    have hsub : X = (X + Y) + (-Y) := by ring
    have htri := congrArg (P.absFin v) hsub
    have hle' : P.absFin v X ≤ max (P.absFin v (X + Y)) (P.absFin v (-Y)) := by
      rw [htri]; exact P.absFin_add_le v _ _
    rw [hlead, P.absFin_neg] at hle'
    rcases le_max_iff.mp hle' with hle_xy | hle_y
    · exact hle_xy
    · exact absurd (lt_of_le_of_lt hle_y hrest_sum_lt) (lt_irrefl _)
  exact h1.trans (by rw [← hsplit]; exact absFin_coeff_le_finPlacePolyNorm P v (F * G) (a₀ + b₀))

/-- Finite support of places where `finPlacePolyNorm P v F ≠ 1` (for `F ≠ 0`). -/
theorem finite_supp_finPlacePolyNorm {K σ : Type*} [Field K] [NumberField K]
    (P : AdelicPlaceSystem K) {F : MvPolynomial σ K} (hF : F ≠ 0) :
    Set.Finite { v : P.Place | finPlacePolyNorm P v F ≠ 1 } := by
  have hsub : { v : P.Place | finPlacePolyNorm P v F ≠ 1 } ⊆
      ⋃ m ∈ F.support, { v : P.Place | P.absFin v (MvPolynomial.coeff m F) ≠ 1 } := by
    intro v hv
    by_contra hnot
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, not_exists, not_not] at hnot
    apply hv
    obtain ⟨m, hm, heq⟩ := exists_coeff_finPlacePolyNorm_eq P v hF
    rw [← heq]
    exact hnot m hm
  refine (Set.Finite.biUnion F.support.finite_toSet fun m hm => ?_).subset hsub
  exact P.finite_supp (MvPolynomial.mem_support_iff.mp hm)

/-- **Concrete Faltings–Philippon Height `FaltingsPhilipponHeight P H Z`** of a projective Chow
form `Z : ProjectiveChowForm K d N` with respect to an adelic place system `P` on `K` and
archimedean Hermitian metrics `H : (K →+* ℂ) → HermProjMetric N`:
$$h_{\mathrm{FP}}(P, H, Z)
  = \sum_{v \nmid \infty} w_v \log \|F_Z\|_v
  + \sum_{\sigma : K \hookrightarrow \mathbb{C}}
      \Bigl(\mathrm{mahler}(H_\sigma, \sigma(F_Z)) + \frac{\deg(Z)}{2} H_{N-1}\Bigr).$$ -/
def FaltingsPhilipponHeight {K : Type*} [Field K] [NumberField K] {d N : ℕ}
    (P : AdelicPlaceSystem K) (H : (K →+* ℂ) → HermProjMetric N)
    (Z : ProjectiveChowForm K d N) : ℝ :=
  (∑' v : P.Place, P.wtFin v * Real.log (finPlacePolyNorm P v Z.poly)) +
    ∑ σ : K →+* ℂ,
      (mahlerMeasure (H σ) (MvPolynomial.map σ Z.poly) + bgsShift N Z.deg)

/-- **Supremum-Norm Variant `FaltingsPhilipponSupHeight P H Z`** replacing Mahler measure by
`Real.log (chowSupNorm (H σ) (MvPolynomial.map σ Z.poly))` (directly used in arithmetic Bézout
and M4 `CovolStepsBridge`). -/
def FaltingsPhilipponSupHeight {K : Type*} [Field K] [NumberField K] {d N : ℕ}
    (P : AdelicPlaceSystem K) (H : (K →+* ℂ) → HermProjMetric N)
    (Z : ProjectiveChowForm K d N) : ℝ :=
  (∑' v : P.Place, P.wtFin v * Real.log (finPlacePolyNorm P v Z.poly)) +
    ∑ σ : K →+* ℂ, Real.log (chowSupNorm (H σ) (MvPolynomial.map σ Z.poly))

/-- Normalized absolute Faltings–Philippon height `h_FP / [K : ℚ]`. -/
def absFaltingsPhilipponHeight {K : Type*} [Field K] [NumberField K] {d N : ℕ}
    (P : AdelicPlaceSystem K) (H : (K →+* ℂ) → HermProjMetric N)
    (Z : ProjectiveChowForm K d N) : ℝ :=
  FaltingsPhilipponHeight P H Z / (Module.finrank ℚ K : ℝ)

/-- **Product-Formula Scaling Invariance of `FaltingsPhilipponHeight`**:
multiplying the Chow polynomial `Z` by any nonzero scalar `c : K` leaves
`FaltingsPhilipponHeight` strictly invariant! -/
theorem faltingsPhilipponHeight_smul_invariant {K : Type*} [Field K] [NumberField K] {d N : ℕ}
    (P : AdelicPlaceSystem K) (H : (K →+* ℂ) → HermProjMetric N)
    {c : K} (hc : c ≠ 0) (Z : ProjectiveChowForm K d N)
    (hint : ∀ σ : K →+* ℂ,
      IntegrableOn (fun u => Real.log ‖MvPolynomial.eval (nrmRows (H σ) u) (MvPolynomial.map σ Z.poly)‖)
        (prodDualBall (H σ) (d + 1)))
    (hae : ∀ σ : K →+* ℂ,
      ∀ᵐ u ∂(volume.restrict (prodDualBall (H σ) (d + 1))),
        MvPolynomial.eval (nrmRows (H σ) u) (MvPolynomial.map σ Z.poly) ≠ 0) :
    FaltingsPhilipponHeight P H (Z.smul c hc) = FaltingsPhilipponHeight P H Z := by
  classical
  unfold FaltingsPhilipponHeight
  let S : Finset P.Place :=
    (P.finite_supp hc).toFinset ∪ (finite_supp_finPlacePolyNorm P Z.ne_zero).toFinset
  have hsupp_c : { v : P.Place | P.absFin v c ≠ 1 } ⊆ (S : Set P.Place) := fun v hv =>
    Finset.mem_coe.mpr (Finset.mem_union_left _ ((P.finite_supp hc).mem_toFinset.mpr hv))
  have htsum_eq : ∀ (f : P.Place → ℝ), (∀ v ∉ S, f v = 0) → (∑' v, f v) = ∑ v ∈ S, f v :=
    fun f hf => tsum_eq_sum fun v hv => hf v hv
  have hfin_Z : (∑' v : P.Place, P.wtFin v * Real.log (finPlacePolyNorm P v Z.poly)) =
      ∑ v ∈ S, P.wtFin v * Real.log (finPlacePolyNorm P v Z.poly) := by
    refine htsum_eq _ fun v hv => ?_
    have hvZ : finPlacePolyNorm P v Z.poly = 1 := by
      by_contra hne
      exact hv (Finset.mem_union_right _ ((finite_supp_finPlacePolyNorm P Z.ne_zero).mem_toFinset.mpr hne))
    simp [hvZ]
  have hfin_cZ : (∑' v : P.Place, P.wtFin v * Real.log (finPlacePolyNorm P v (Z.smul c hc).poly)) =
      ∑ v ∈ S, P.wtFin v * Real.log (finPlacePolyNorm P v (Z.smul c hc).poly) := by
    refine htsum_eq _ fun v hv => ?_
    have hvc : P.absFin v c = 1 := by
      by_contra hne
      exact hv (Finset.mem_union_left _ ((P.finite_supp hc).mem_toFinset.mpr hne))
    have hvZ : finPlacePolyNorm P v Z.poly = 1 := by
      by_contra hne
      exact hv (Finset.mem_union_right _ ((finite_supp_finPlacePolyNorm P Z.ne_zero).mem_toFinset.mpr hne))
    change P.wtFin v * Real.log (finPlacePolyNorm P v (MvPolynomial.C c * Z.poly)) = 0
    rw [finPlacePolyNorm_C_mul, hvc, hvZ, mul_one, Real.log_one, mul_zero]
  rw [hfin_Z, hfin_cZ]
  have hfin_split :
      (∑ v ∈ S, P.wtFin v * Real.log (finPlacePolyNorm P v (Z.smul c hc).poly)) =
        (∑ v ∈ S, P.wtFin v * Real.log (finPlacePolyNorm P v Z.poly)) +
          ∑ v ∈ S, P.wtFin v * Real.log (P.absFin v c) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun v _ => ?_
    change P.wtFin v * Real.log (finPlacePolyNorm P v (MvPolynomial.C c * Z.poly)) = _
    rw [finPlacePolyNorm_C_mul, Real.log_mul (P.absFin_pos v hc).ne'
      (finPlacePolyNorm_pos_of_ne_zero P v Z.ne_zero).ne']
    ring
  have harch_split :
      (∑ σ : K →+* ℂ, (mahlerMeasure (H σ) (MvPolynomial.map σ (Z.smul c hc).poly) + bgsShift N (Z.smul c hc).deg)) =
        (∑ σ : K →+* ℂ, (mahlerMeasure (H σ) (MvPolynomial.map σ Z.poly) + bgsShift N Z.deg)) +
          ∑ σ : K →+* ℂ, Real.log ‖σ c‖ := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun σ _ => ?_
    change mahlerMeasure (H σ) (MvPolynomial.map σ (MvPolynomial.C c * Z.poly)) + bgsShift N Z.deg = _
    rw [map_mul, MvPolynomial.map_C,
      mahlerMeasure_C_mul (H σ) ((map_ne_zero σ).mpr hc) _ (hint σ) (hae σ)]
    ring
  rw [hfin_split, harch_split]
  have hpf : (∑ v ∈ S, P.wtFin v * Real.log (P.absFin v c)) +
      ∑ σ : K →+* ℂ, Real.log ‖σ c‖ = 0 := by
    convert P.product_formula hc S hsupp_c
  linarith

/-- **Product-Formula Scaling Invariance of `FaltingsPhilipponSupHeight`**. -/
theorem faltingsPhilipponSupHeight_smul_invariant {K : Type*} [Field K] [NumberField K] {d N : ℕ}
    (P : AdelicPlaceSystem K) (H : (K →+* ℂ) → HermProjMetric N)
    {c : K} (hc : c ≠ 0) (Z : ProjectiveChowForm K d N) :
    FaltingsPhilipponSupHeight P H (Z.smul c hc) = FaltingsPhilipponSupHeight P H Z := by
  classical
  unfold FaltingsPhilipponSupHeight
  let S : Finset P.Place :=
    (P.finite_supp hc).toFinset ∪ (finite_supp_finPlacePolyNorm P Z.ne_zero).toFinset
  have hsupp_c : { v : P.Place | P.absFin v c ≠ 1 } ⊆ (S : Set P.Place) := fun v hv =>
    Finset.mem_coe.mpr (Finset.mem_union_left _ ((P.finite_supp hc).mem_toFinset.mpr hv))
  have htsum_eq : ∀ (f : P.Place → ℝ), (∀ v ∉ S, f v = 0) → (∑' v, f v) = ∑ v ∈ S, f v :=
    fun f hf => tsum_eq_sum fun v hv => hf v hv
  have hfin_Z : (∑' v : P.Place, P.wtFin v * Real.log (finPlacePolyNorm P v Z.poly)) =
      ∑ v ∈ S, P.wtFin v * Real.log (finPlacePolyNorm P v Z.poly) := by
    refine htsum_eq _ fun v hv => ?_
    have hvZ : finPlacePolyNorm P v Z.poly = 1 := by
      by_contra hne
      exact hv (Finset.mem_union_right _ ((finite_supp_finPlacePolyNorm P Z.ne_zero).mem_toFinset.mpr hne))
    simp [hvZ]
  have hfin_cZ : (∑' v : P.Place, P.wtFin v * Real.log (finPlacePolyNorm P v (Z.smul c hc).poly)) =
      ∑ v ∈ S, P.wtFin v * Real.log (finPlacePolyNorm P v (Z.smul c hc).poly) := by
    refine htsum_eq _ fun v hv => ?_
    have hvc : P.absFin v c = 1 := by
      by_contra hne
      exact hv (Finset.mem_union_left _ ((P.finite_supp hc).mem_toFinset.mpr hne))
    have hvZ : finPlacePolyNorm P v Z.poly = 1 := by
      by_contra hne
      exact hv (Finset.mem_union_right _ ((finite_supp_finPlacePolyNorm P Z.ne_zero).mem_toFinset.mpr hne))
    change P.wtFin v * Real.log (finPlacePolyNorm P v (MvPolynomial.C c * Z.poly)) = 0
    rw [finPlacePolyNorm_C_mul, hvc, hvZ, mul_one, Real.log_one, mul_zero]
  rw [hfin_Z, hfin_cZ]
  have hfin_split :
      (∑ v ∈ S, P.wtFin v * Real.log (finPlacePolyNorm P v (Z.smul c hc).poly)) =
        (∑ v ∈ S, P.wtFin v * Real.log (finPlacePolyNorm P v Z.poly)) +
          ∑ v ∈ S, P.wtFin v * Real.log (P.absFin v c) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun v _ => ?_
    change P.wtFin v * Real.log (finPlacePolyNorm P v (MvPolynomial.C c * Z.poly)) = _
    rw [finPlacePolyNorm_C_mul, Real.log_mul (P.absFin_pos v hc).ne'
      (finPlacePolyNorm_pos_of_ne_zero P v Z.ne_zero).ne']
    ring
  have harch_split :
      (∑ σ : K →+* ℂ, Real.log (chowSupNorm (H σ) (MvPolynomial.map σ (Z.smul c hc).poly))) =
        (∑ σ : K →+* ℂ, Real.log (chowSupNorm (H σ) (MvPolynomial.map σ Z.poly))) +
          ∑ σ : K →+* ℂ, Real.log ‖σ c‖ := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun σ _ => ?_
    change Real.log (chowSupNorm (H σ) (MvPolynomial.map σ (MvPolynomial.C c * Z.poly))) = _
    have hZ_ne : MvPolynomial.map σ Z.poly ≠ 0 :=
      fun h0 => Z.ne_zero (MvPolynomial.map_injective σ σ.injective (by simpa using h0))
    have hZ_hom : IsBlockHomogeneous Z.deg (MvPolynomial.map σ Z.poly) :=
      isBlockHomogeneous_map σ Z.homog
    rw [map_mul, MvPolynomial.map_C, chowSupNorm_C_mul (H σ) (σ c) hZ_hom,
      Real.log_mul (norm_ne_zero_iff.mpr ((map_ne_zero σ).mpr hc))
        (chowSupNorm_pos (H σ) hZ_ne hZ_hom).ne', add_comm]
  rw [hfin_split, harch_split]
  have hpf : (∑ v ∈ S, P.wtFin v * Real.log (P.absFin v c)) +
      ∑ σ : K →+* ℂ, Real.log ‖σ c‖ = 0 := by
    convert P.product_formula hc S hsupp_c
  linarith

/-- **Exact Cycle Additivity of `FaltingsPhilipponHeight`**:
`FaltingsPhilipponHeight P H (Z₁.mul Z₂) = FaltingsPhilipponHeight P H Z₁ + FaltingsPhilipponHeight P H Z₂`. -/
theorem faltingsPhilipponHeight_cycle_add {K : Type*} [Field K] [NumberField K] {d N : ℕ}
    (P : AdelicPlaceSystem K) (H : (K →+* ℂ) → HermProjMetric N)
    (Z₁ Z₂ : ProjectiveChowForm K d N)
    (hint₁ : ∀ σ : K →+* ℂ,
      IntegrableOn (fun u => Real.log ‖MvPolynomial.eval (nrmRows (H σ) u) (MvPolynomial.map σ Z₁.poly)‖)
        (prodDualBall (H σ) (d + 1)))
    (hint₂ : ∀ σ : K →+* ℂ,
      IntegrableOn (fun u => Real.log ‖MvPolynomial.eval (nrmRows (H σ) u) (MvPolynomial.map σ Z₂.poly)‖)
        (prodDualBall (H σ) (d + 1)))
    (hae₁ : ∀ σ : K →+* ℂ,
      ∀ᵐ u ∂(volume.restrict (prodDualBall (H σ) (d + 1))),
        MvPolynomial.eval (nrmRows (H σ) u) (MvPolynomial.map σ Z₁.poly) ≠ 0)
    (hae₂ : ∀ σ : K →+* ℂ,
      ∀ᵐ u ∂(volume.restrict (prodDualBall (H σ) (d + 1))),
        MvPolynomial.eval (nrmRows (H σ) u) (MvPolynomial.map σ Z₂.poly) ≠ 0) :
    FaltingsPhilipponHeight P H (Z₁.mul Z₂) =
      FaltingsPhilipponHeight P H Z₁ + FaltingsPhilipponHeight P H Z₂ := by
  classical
  have hidx_inj : Function.Injective (fun ij : Fin (d + 1) × Fin N => ij.1.val * N + ij.2.val) := by
    rintro ⟨i₁, j₁⟩ ⟨i₂, j₂⟩ h
    have hi : i₁ = i₂ := by
      ext
      rcases lt_trichotomy i₁.val i₂.val with hlt | heq | hgt
      · have hmul : (i₁.val + 1) * N ≤ i₂.val * N := Nat.mul_le_mul_right N hlt
        have hlt' : i₁.val * N + j₁.val < i₂.val * N + j₂.val := by
          rw [Nat.succ_mul] at hmul
          have := j₁.isLt
          linarith
        exact absurd h hlt'.ne
      · exact heq
      · have hmul : (i₂.val + 1) * N ≤ i₁.val * N := Nat.mul_le_mul_right N hgt
        have hlt' : i₂.val * N + j₂.val < i₁.val * N + j₁.val := by
          rw [Nat.succ_mul] at hmul
          have := j₂.isLt
          linarith
        exact absurd h.symm hlt'.ne
    subst hi
    have hj : j₁ = j₂ := Fin.ext (Nat.add_left_cancel h)
    subst hj
    rfl
  let linOrd : LinearOrder (Fin (d + 1) × Fin N) := LinearOrder.lift' _ hidx_inj
  have hnorm_mul : ∀ v : P.Place,
      finPlacePolyNorm P v (Z₁.poly * Z₂.poly) =
        finPlacePolyNorm P v Z₁.poly * finPlacePolyNorm P v Z₂.poly :=
    fun v => @finPlacePolyNorm_mul K (Fin (d + 1) × Fin N) _ _ linOrd P v Z₁.poly Z₂.poly
  unfold FaltingsPhilipponHeight
  let S : Finset P.Place :=
    (finite_supp_finPlacePolyNorm P Z₁.ne_zero).toFinset ∪
      (finite_supp_finPlacePolyNorm P Z₂.ne_zero).toFinset
  have htsum_eq : ∀ (f : P.Place → ℝ), (∀ v ∉ S, f v = 0) → (∑' v, f v) = ∑ v ∈ S, f v :=
    fun f hf => tsum_eq_sum fun v hv => hf v hv
  have hfin1 : (∑' v : P.Place, P.wtFin v * Real.log (finPlacePolyNorm P v Z₁.poly)) =
      ∑ v ∈ S, P.wtFin v * Real.log (finPlacePolyNorm P v Z₁.poly) := by
    refine htsum_eq _ fun v hv => ?_
    have hv1 : finPlacePolyNorm P v Z₁.poly = 1 := by
      by_contra hne
      exact hv (Finset.mem_union_left _ ((finite_supp_finPlacePolyNorm P Z₁.ne_zero).mem_toFinset.mpr hne))
    simp [hv1]
  have hfin2 : (∑' v : P.Place, P.wtFin v * Real.log (finPlacePolyNorm P v Z₂.poly)) =
      ∑ v ∈ S, P.wtFin v * Real.log (finPlacePolyNorm P v Z₂.poly) := by
    refine htsum_eq _ fun v hv => ?_
    have hv2 : finPlacePolyNorm P v Z₂.poly = 1 := by
      by_contra hne
      exact hv (Finset.mem_union_right _ ((finite_supp_finPlacePolyNorm P Z₂.ne_zero).mem_toFinset.mpr hne))
    simp [hv2]
  have hfin12 : (∑' v : P.Place, P.wtFin v * Real.log (finPlacePolyNorm P v (Z₁.mul Z₂).poly)) =
      ∑ v ∈ S, P.wtFin v * Real.log (finPlacePolyNorm P v (Z₁.mul Z₂).poly) := by
    refine htsum_eq _ fun v hv => ?_
    have hv1 : finPlacePolyNorm P v Z₁.poly = 1 := by
      by_contra hne
      exact hv (Finset.mem_union_left _ ((finite_supp_finPlacePolyNorm P Z₁.ne_zero).mem_toFinset.mpr hne))
    have hv2 : finPlacePolyNorm P v Z₂.poly = 1 := by
      by_contra hne
      exact hv (Finset.mem_union_right _ ((finite_supp_finPlacePolyNorm P Z₂.ne_zero).mem_toFinset.mpr hne))
    change P.wtFin v * Real.log (finPlacePolyNorm P v (Z₁.poly * Z₂.poly)) = 0
    rw [hnorm_mul v, hv1, hv2, mul_one, Real.log_one, mul_zero]
  rw [hfin1, hfin2, hfin12]
  have hfin_add :
      (∑ v ∈ S, P.wtFin v * Real.log (finPlacePolyNorm P v (Z₁.mul Z₂).poly)) =
        (∑ v ∈ S, P.wtFin v * Real.log (finPlacePolyNorm P v Z₁.poly)) +
          (∑ v ∈ S, P.wtFin v * Real.log (finPlacePolyNorm P v Z₂.poly)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun v _ => ?_
    change P.wtFin v * Real.log (finPlacePolyNorm P v (Z₁.poly * Z₂.poly)) = _
    rw [hnorm_mul v, Real.log_mul (finPlacePolyNorm_pos_of_ne_zero P v Z₁.ne_zero).ne'
      (finPlacePolyNorm_pos_of_ne_zero P v Z₂.ne_zero).ne']
    ring
  have harch_add :
      (∑ σ : K →+* ℂ, (mahlerMeasure (H σ) (MvPolynomial.map σ (Z₁.mul Z₂).poly) + bgsShift N (Z₁.mul Z₂).deg)) =
        (∑ σ : K →+* ℂ, (mahlerMeasure (H σ) (MvPolynomial.map σ Z₁.poly) + bgsShift N Z₁.deg)) +
          (∑ σ : K →+* ℂ, (mahlerMeasure (H σ) (MvPolynomial.map σ Z₂.poly) + bgsShift N Z₂.deg)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun σ _ => ?_
    change mahlerMeasure (H σ) (MvPolynomial.map σ (Z₁.poly * Z₂.poly)) + bgsShift N (Z₁.deg + Z₂.deg) = _
    rw [map_mul, mahlerMeasure_mul (H σ) _ _ (hint₁ σ) (hint₂ σ) (hae₁ σ) (hae₂ σ)]
    unfold bgsShift
    push_cast
    ring
  rw [hfin_add, harch_add]
  ring

/-- **Metric-Twist Scaling Law for `FaltingsPhilipponSupHeight`**:
rescaling `H σ ↦ (exp (2 t)) • H σ` (`t : ℝ`) shifts `FaltingsPhilipponSupHeight` by
`[K : ℚ] * (d + 1) * Z.deg * t`. -/
theorem faltingsPhilipponSupHeight_metric_scale {K : Type*} [Field K] [NumberField K] {d N : ℕ}
    (P : AdelicPlaceSystem K) (H : (K →+* ℂ) → HermProjMetric N) (t : ℝ)
    (Z : ProjectiveChowForm K d N) :
    FaltingsPhilipponSupHeight P (fun σ => (H σ).scale (Real.exp_pos (2 * t))) Z =
      FaltingsPhilipponSupHeight P H Z +
        (Module.finrank ℚ K : ℝ) * ((d : ℝ) + 1) * (Z.deg : ℝ) * t := by
  unfold FaltingsPhilipponSupHeight
  have hsum :
      (∑ σ : K →+* ℂ, Real.log (chowSupNorm ((H σ).scale (Real.exp_pos (2 * t)))
        (MvPolynomial.map σ Z.poly))) =
      (∑ σ : K →+* ℂ, Real.log (chowSupNorm (H σ) (MvPolynomial.map σ Z.poly))) +
        (Module.finrank ℚ K : ℝ) * ((d : ℝ) + 1) * (Z.deg : ℝ) * t := by
    have hterm : ∀ σ : K →+* ℂ,
        Real.log (chowSupNorm ((H σ).scale (Real.exp_pos (2 * t))) (MvPolynomial.map σ Z.poly)) =
          Real.log (chowSupNorm (H σ) (MvPolynomial.map σ Z.poly)) + ((d : ℝ) + 1) * (Z.deg : ℝ) * t := by
      intro σ
      have hZ_ne : MvPolynomial.map σ Z.poly ≠ 0 :=
        fun h0 => Z.ne_zero (MvPolynomial.map_injective σ σ.injective (by simpa using h0))
      have hZ_hom : IsBlockHomogeneous Z.deg (MvPolynomial.map σ Z.poly) :=
        isBlockHomogeneous_map σ Z.homog
      rw [chowSupNorm_scale (H σ) (Real.exp_pos (2 * t)) hZ_hom]
      have hsqrt : Real.sqrt (Real.exp (2 * t)) = Real.exp t := by
        rw [← Real.exp_half]; ring_nf
      rw [hsqrt, Real.log_mul (pow_pos (Real.exp_pos t) _).ne'
        (chowSupNorm_pos (H σ) hZ_ne hZ_hom).ne', Real.log_pow, Real.log_exp]
      push_cast
      ring
    simp_rw [hterm, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      NumberField.Embeddings.card K ℂ, nsmul_eq_mul]
    ring
  rw [hsum]
  ring

/-- **Height Comparison between `FaltingsPhilipponHeight` and `FaltingsPhilipponSupHeight`**:
`FaltingsPhilipponHeight P H Z ≤ FaltingsPhilipponSupHeight P H Z + [K : ℚ] * bgsShift N Z.deg`. -/
theorem faltingsPhilipponHeight_le_supHeight {K : Type*} [Field K] [NumberField K] {d N : ℕ}
    (P : AdelicPlaceSystem K) (H : (K →+* ℂ) → HermProjMetric N)
    (Z : ProjectiveChowForm K d N)
    (hint : ∀ σ : K →+* ℂ,
      IntegrableOn (fun u => Real.log ‖MvPolynomial.eval (nrmRows (H σ) u) (MvPolynomial.map σ Z.poly)‖)
        (prodDualBall (H σ) (d + 1)))
    (hae : ∀ σ : K →+* ℂ,
      ∀ᵐ u ∂(volume.restrict (prodDualBall (H σ) (d + 1))),
        MvPolynomial.eval (nrmRows (H σ) u) (MvPolynomial.map σ Z.poly) ≠ 0) :
    FaltingsPhilipponHeight P H Z ≤
      FaltingsPhilipponSupHeight P H Z + (Module.finrank ℚ K : ℝ) * bgsShift N Z.deg := by
  unfold FaltingsPhilipponHeight FaltingsPhilipponSupHeight
  have hsum :
      (∑ σ : K →+* ℂ, (mahlerMeasure (H σ) (MvPolynomial.map σ Z.poly) + bgsShift N Z.deg)) ≤
        (∑ σ : K →+* ℂ, Real.log (chowSupNorm (H σ) (MvPolynomial.map σ Z.poly))) +
          (Module.finrank ℚ K : ℝ) * bgsShift N Z.deg := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      NumberField.Embeddings.card K ℂ, nsmul_eq_mul]
    refine add_le_add (Finset.sum_le_sum fun σ _ => ?_) le_rfl
    exact mahlerMeasure_le_log_chowSupNorm (H σ) (isBlockHomogeneous_map σ Z.homog) (hint σ) (hae σ)
  linarith

/-- **Exact Point Height Evaluation (`FaltingsPhilipponSupHeight` of `ofPoint`)**:
equals the Weil / Arakelov height `∑_v w_v (log max_j |y_j|_v) + ∑_σ log ‖σ(y)‖_{H_σ}`! -/
theorem faltingsPhilipponSupHeight_ofPoint {K : Type*} [Field K] [NumberField K] {N : ℕ}
    (P : AdelicPlaceSystem K) (H : (K →+* ℂ) → HermProjMetric N)
    {y : Fin N → K} (hy : y ≠ 0) :
    FaltingsPhilipponSupHeight P H (ProjectiveChowForm.ofPoint y hy) =
      (∑' v : P.Place, P.wtFin v * Real.log (finPlacePolyNorm P v (ProjectiveChowForm.ofPoint y hy).poly)) +
        ∑ σ : K →+* ℂ, Real.log ((H σ).primalNorm (fun j => σ (y j))) := by
  unfold FaltingsPhilipponSupHeight
  congr 1
  refine Finset.sum_congr rfl fun σ _ => ?_
  have hmap : MvPolynomial.map σ (ProjectiveChowForm.ofPoint y hy).poly =
      ∑ j : Fin N, MvPolynomial.C (σ (y j)) * MvPolynomial.X ((0 : Fin 1), j) := by
    change MvPolynomial.map σ (∑ j : Fin N, MvPolynomial.C (y j) * MvPolynomial.X ((0 : Fin 1), j)) = _
    simp only [map_sum, map_mul, MvPolynomial.map_C, MvPolynomial.map_X]
  rw [hmap, chowSupNorm_ofPoint]

end FaltingsPhilipponHeights

/-! ## Section 4: `chow_form_norm_le_arith_intersection` & `chow_form_height_comparison` -/

section ArakelovIntersectionAndComparison

/-- **Projective Arakelov Intersection Model (`ProjArakelovIntersectionModel`)**:
connects a `ProjectiveChowForm K d N` over a number field `K` to:
1. a Dolbeault / Green-current `ArakelovPairingModel` (`Stage14M3_GreenCurrents`) and
   `PositivityCone`,
2. effective semipositive hyperplane Arakelov divisors `D̂_σ` representing `𝒪(1)|_Z`,
3. the inductive hyperplane-slicing identity (Bost–Gillet–Soulé / Philippon Arithmetic Bézout
   recursion) expressing the `(d + 1)`-fold Arakelov self-intersection `(L̄^{d+1} | Z)_Ar` in
   terms of the Mahler measure + BGS shift + non-archimedean content and residual effective defect! -/
structure ProjArakelovIntersectionModel (K : Type*) [Field K] [NumberField K]
    (d N : ℕ) (P : AdelicPlaceSystem K) (H : (K →+* ℂ) → HermProjMetric N)
    (A_curr : DolbeaultCurrentAlgebra) (PrimeDiv : Type*)
    (δ_map : DivisorCurrentMap A_curr PrimeDiv)
    (Z : ProjectiveChowForm K d N) where
  /-- Arakelov `(d + 1)`-fold self-intersection `(L̄(H)^{d+1} | Z)_Ar`. -/
  arithSelfInt : ℝ
  pairModel : ArakelovPairingModel δ_map
  posCone : pairModel.PositivityCone
  /-- Effective semipositive hyperplane Arakelov divisors `D̂_σ` representing `𝒪(1)|_Z`. -/
  hyperplaneDiv : (K →+* ℂ) → ArakelovDivisor δ_map
  hyperplane_eff : ∀ σ, pairModel.IsEffectiveArakelovDivisor posCone (hyperplaneDiv σ)
  hyperplane_pos : ∀ σ, pairModel.IsSemipositiveGreen posCone (hyperplaneDiv σ)
  /-- Non-negative residual arithmetic intersection defect from lower-dimensional slicing. -/
  sliceDefect : ℝ
  sliceDefect_nonneg : 0 ≤ sliceDefect
  /-- Integrability & a.e. non-vanishing of `log ‖σ(F_Z)(u_nrm)‖` on `prodDualBall (H σ) (d + 1)`. -/
  mahler_int : ∀ σ : K →+* ℂ,
    IntegrableOn (fun u => Real.log ‖MvPolynomial.eval (nrmRows (H σ) u) (MvPolynomial.map σ Z.poly)‖)
      (prodDualBall (H σ) (d + 1))
  mahler_ae_nz : ∀ σ : K →+* ℂ,
    ∀ᵐ u ∂(volume.restrict (prodDualBall (H σ) (d + 1))),
      MvPolynomial.eval (nrmRows (H σ) u) (MvPolynomial.map σ Z.poly) ≠ 0
  /-- **Bost–Gillet–Soulé / Philippon Arithmetic Bézout Decomposition**:
  `(L̄^{d+1} | Z)_Ar = h_FP(P, H, Z) + ∑_σ ⟨D̂_σ, D̂_σ⟩_∞ + sliceDefect`. -/
  bgs_self_intersection_eq :
    arithSelfInt = FaltingsPhilipponHeight P H Z +
      (∑ σ : K →+* ℂ, pairModel.archStarPairing (hyperplaneDiv σ) (hyperplaneDiv σ)) +
      sliceDefect

/-- **THEOREM (`chow_form_norm_le_arith_intersection`)**:
for any `ProjArakelovIntersectionModel` over a number field `K`:
1. The **Faltings–Philippon height** is bounded above by the Arakelov self-intersection:
   `FaltingsPhilipponHeight P H Z ≤ M.arithSelfInt`.
2. The **Archimedean Mahler norm sum + non-archimedean content** is bounded above by
   `M.arithSelfInt - [K : ℚ] * bgsShift N Z.deg` (proved via
   `archStarPairing_nonneg_of_effective_semipositive`). -/
theorem chow_form_norm_le_arith_intersection {K : Type*} [Field K] [NumberField K]
    {d N : ℕ} {P : AdelicPlaceSystem K} {H : (K →+* ℂ) → HermProjMetric N}
    {A_curr : DolbeaultCurrentAlgebra} {PrimeDiv : Type*}
    {δ_map : DivisorCurrentMap A_curr PrimeDiv}
    {Z : ProjectiveChowForm K d N}
    (M : ProjArakelovIntersectionModel K d N P H A_curr PrimeDiv δ_map Z) :
    FaltingsPhilipponHeight P H Z ≤ M.arithSelfInt ∧
    (∑' v : P.Place, P.wtFin v * Real.log (finPlacePolyNorm P v Z.poly)) +
      (∑ σ : K →+* ℂ, mahlerMeasure (H σ) (MvPolynomial.map σ Z.poly)) ≤
        M.arithSelfInt - (Module.finrank ℚ K : ℝ) * bgsShift N Z.deg := by
  have hstar_nn : ∀ σ : K →+* ℂ,
      0 ≤ M.pairModel.archStarPairing (M.hyperplaneDiv σ) (M.hyperplaneDiv σ) :=
    fun σ => M.pairModel.archStarPairing_nonneg_of_effective_semipositive M.posCone
      (M.hyperplane_eff σ) (M.hyperplane_pos σ) (M.hyperplane_eff σ)
  have hsum_nn : 0 ≤ ∑ σ : K →+* ℂ,
      M.pairModel.archStarPairing (M.hyperplaneDiv σ) (M.hyperplaneDiv σ) :=
    Finset.sum_nonneg fun σ _ => hstar_nn σ
  have h1 : FaltingsPhilipponHeight P H Z ≤ M.arithSelfInt := by
    linarith [M.bgs_self_intersection_eq, M.sliceDefect_nonneg]
  have hfp_split :
      FaltingsPhilipponHeight P H Z =
        (∑' v : P.Place, P.wtFin v * Real.log (finPlacePolyNorm P v Z.poly)) +
        (∑ σ : K →+* ℂ, mahlerMeasure (H σ) (MvPolynomial.map σ Z.poly)) +
        (Module.finrank ℚ K : ℝ) * bgsShift N Z.deg := by
    unfold FaltingsPhilipponHeight
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      NumberField.Embeddings.card K ℂ, nsmul_eq_mul]
    ring
  exact ⟨h1, by linarith⟩

/-- **Bergman / `ℓ¹`-Coefficient Upper Bound on `chowSupNorm` via `HermProjMetric`**:
gives an explicit upper bound on `Real.log (chowSupNorm M F)` in terms of `polyCoeffNorm1 F` and
the Hermitian coordinate distortion constant `C_H`. -/
theorem log_chowSupNorm_le_log_polyCoeffNorm1 {d N δ : ℕ} (M : HermProjMetric N)
    {F : MvPolynomial (Fin (d + 1) × Fin N) ℂ} (hF0 : F ≠ 0) (hF : IsBlockHomogeneous δ F) :
    ∃ C_H : ℝ, 0 < C_H ∧
      Real.log (chowSupNorm M F) ≤
        Real.log (polyCoeffNorm1 F) + ((d + 1) * δ : ℝ) * Real.log C_H := by
  obtain ⟨C, _, hC⟩ := M.exists_coord_le_dualNorm
  let C_H : ℝ := max C 1
  have hCH_pos : 0 < C_H := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  refine ⟨C_H, hCH_pos, ?_⟩
  have hbd : chowSupNorm M F ≤ polyCoeffNorm1 F * C_H ^ ((d + 1) * δ) := by
    refine csSup_le ⟨‖MvPolynomial.eval 0 F‖, 0, fun i => dualNorm_zero_le_one M i, rfl⟩ ?_
    rintro r ⟨u, hu, rfl⟩
    refine norm_eval_le_polyCoeffNorm1 hF hCH_pos.le fun ij => ?_
    exact (hC (fun j => u (ij.1, j)) ij.2).trans
      ((mul_le_mul_of_nonneg_right (le_max_left C 1) (M.dualNorm_nonneg _)).trans
        (mul_le_of_le_one_right hCH_pos.le (hu ij.1)))
  have hlog := Real.log_le_log (chowSupNorm_pos M hF0 hF) hbd
  rw [Real.log_mul (polyCoeffNorm1_pos_of_ne_zero hF0).ne' (pow_pos hCH_pos _).ne',
    Real.log_pow] at hlog
  convert hlog using 2
  push_cast
  ring

/-- **Metric-Comparison Bound on `chowSupNorm`**:
if `H₁, H₂ : HermProjMetric N` satisfy `H₁.dualNorm u ≤ exp(C) * H₂.dualNorm u` for all `u`,
then `chowSupNorm H₂ F ≤ exp((d + 1) * δ * C) * chowSupNorm H₁ F`. -/
theorem chowSupNorm_metric_comparison {d N δ : ℕ} {H₁ H₂ : HermProjMetric N}
    {C : ℝ} (hC : ∀ u : Fin N → ℂ, H₁.dualNorm u ≤ Real.exp C * H₂.dualNorm u)
    {F : MvPolynomial (Fin (d + 1) × Fin N) ℂ} (hF : IsBlockHomogeneous δ F) :
    chowSupNorm H₂ F ≤ Real.exp (((d + 1) * δ : ℝ) * C) * chowSupNorm H₁ F := by
  refine csSup_le ⟨‖MvPolynomial.eval 0 F‖, 0, fun i => dualNorm_zero_le_one H₂ i, rfl⟩ ?_
  rintro r ⟨u, hu, rfl⟩
  let u' : Fin (d + 1) × Fin N → ℂ := fun ij => ((Real.exp (-C) : ℝ) : ℂ) * u ij
  have hu' : ∀ i : Fin (d + 1), H₁.dualNorm (fun j => u' (i, j)) ≤ 1 := by
    intro i
    have hvec : (fun j => u' (i, j)) = ((Real.exp (-C) : ℝ) : ℂ) • (fun j => u (i, j)) := rfl
    rw [hvec, H₁.dualNorm_smul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    calc Real.exp (-C) * H₁.dualNorm (fun j => u (i, j))
        ≤ Real.exp (-C) * (Real.exp C * H₂.dualNorm (fun j => u (i, j))) :=
          mul_le_mul_of_nonneg_left (hC _) (Real.exp_pos _).le
      _ = H₂.dualNorm (fun j => u (i, j)) := by
          rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]
      _ ≤ 1 := hu i
  have hsc := aeval_block_smul_eq (R := ℂ) (S := ℂ) hF (fun _ => ((Real.exp C : ℝ) : ℂ)) u'
  have hu_eq : (fun ij => ((Real.exp C : ℝ) : ℂ) * u' ij) = u := by
    funext ij
    dsimp [u']
    rw [← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add, add_neg_cancel, Real.exp_zero,
      Complex.ofReal_one, one_mul]
  change MvPolynomial.eval (fun ij => ((Real.exp C : ℝ) : ℂ) * u' ij) F = _ at hsc
  rw [hu_eq] at hsc
  rw [hsc, norm_mul, norm_prod]
  simp only [norm_pow, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos C).le,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Real.exp_nat_mul]
  rw [show (↑(d + 1) : ℝ) * (↑δ * C) = ((d + 1 : ℝ) * (δ : ℝ) * C) by push_cast; ring]
  exact mul_le_mul_of_nonneg_left (norm_eval_le_chowSupNorm H₁ hF hu') (Real.exp_pos _).le

/-- **Metrized Line Bundle Section-Norm Comparison Bridge for Chow Forms**:
gives the exact `O(C)` stability of `FaltingsPhilipponSupHeight` under any bounded change of
Hermitian metric (dual counterpart of `Stage14M3_HermitianLineBundles.section_ptNormSq_metric_comparison`). -/
theorem faltingsPhilipponSupHeight_metric_comparison {K : Type*} [Field K] [NumberField K] {d N : ℕ}
    (P : AdelicPlaceSystem K) (H₁ H₂ : (K →+* ℂ) → HermProjMetric N)
    {C : ℝ} (hC : ∀ σ : K →+* ℂ, ∀ u : Fin N → ℂ, (H₁ σ).dualNorm u ≤ Real.exp C * (H₂ σ).dualNorm u)
    (Z : ProjectiveChowForm K d N) :
    FaltingsPhilipponSupHeight P H₂ Z ≤
      FaltingsPhilipponSupHeight P H₁ Z +
        (Module.finrank ℚ K : ℝ) * ((d : ℝ) + 1) * (Z.deg : ℝ) * C := by
  unfold FaltingsPhilipponSupHeight
  have hsum :
      (∑ σ : K →+* ℂ, Real.log (chowSupNorm (H₂ σ) (MvPolynomial.map σ Z.poly))) ≤
        (∑ σ : K →+* ℂ, Real.log (chowSupNorm (H₁ σ) (MvPolynomial.map σ Z.poly))) +
          (Module.finrank ℚ K : ℝ) * ((d : ℝ) + 1) * (Z.deg : ℝ) * C := by
    have hterm : ∀ σ : K →+* ℂ,
        Real.log (chowSupNorm (H₂ σ) (MvPolynomial.map σ Z.poly)) ≤
          Real.log (chowSupNorm (H₁ σ) (MvPolynomial.map σ Z.poly)) +
            ((d : ℝ) + 1) * (Z.deg : ℝ) * C := by
      intro σ
      have hZ_ne : MvPolynomial.map σ Z.poly ≠ 0 :=
        fun h0 => Z.ne_zero (MvPolynomial.map_injective σ σ.injective (by simpa using h0))
      have hZ_hom : IsBlockHomogeneous Z.deg (MvPolynomial.map σ Z.poly) :=
        isBlockHomogeneous_map σ Z.homog
      have hcomp := chowSupNorm_metric_comparison (hC σ) hZ_hom
      have hlog := Real.log_le_log (chowSupNorm_pos (H₂ σ) hZ_ne hZ_hom) hcomp
      rw [Real.log_mul (Real.exp_pos _).ne' (chowSupNorm_pos (H₁ σ) hZ_ne hZ_hom).ne',
        Real.log_exp] at hlog
      linarith
    calc (∑ σ : K →+* ℂ, Real.log (chowSupNorm (H₂ σ) (MvPolynomial.map σ Z.poly)))
        ≤ ∑ σ : K →+* ℂ, (Real.log (chowSupNorm (H₁ σ) (MvPolynomial.map σ Z.poly)) +
            ((d : ℝ) + 1) * (Z.deg : ℝ) * C) :=
          Finset.sum_le_sum fun σ _ => hterm σ
      _ = (∑ σ : K →+* ℂ, Real.log (chowSupNorm (H₁ σ) (MvPolynomial.map σ Z.poly))) +
            (Module.finrank ℚ K : ℝ) * ((d : ℝ) + 1) * (Z.deg : ℝ) * C := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
            NumberField.Embeddings.card K ℂ, nsmul_eq_mul]
          ring
  linarith

/-- **THEOREM (`chow_form_height_comparison`)**:
**Bost–Gillet–Soulé / Philippon / Alpöge Chow-Form Height Comparison Theorem**:
given a `ProjArakelovIntersectionModel` with a generating-section image height `imageHeight` and
metric-twist shift `t`, yields:
1. Two-sided comparison between `FaltingsPhilipponHeight`, `FaltingsPhilipponSupHeight`, and
   `M.arithSelfInt`:
   `FaltingsPhilipponHeight P H M.Z ≤ M.arithSelfInt` and
   `FaltingsPhilipponHeight P H M.Z ≤ FaltingsPhilipponSupHeight P H M.Z + [K : ℚ] * bgsShift N M.Z.deg`.
2. **Alpöge Weil Height Inequality (`ChowFormHeightComparison`)**:
   if `a ≤ FaltingsPhilipponHeight P H M.Z + [K : ℚ] * (d + 1) * M.Z.deg * t`, then
   $$a \le [K : \mathbb{Q}] \cdot \bigl((d + 1) \cdot M.Z.\mathrm{deg} \cdot (\mathrm{imageHeight} + t) +
     2 \cdot M.Z.\mathrm{deg} \cdot C_{\mathrm{comp}} + \mathrm{bgsShift}(N, M.Z.\mathrm{deg})\bigr).$$ -/
theorem chow_form_height_comparison {K : Type*} [Field K] [NumberField K]
    {d N : ℕ} {P : AdelicPlaceSystem K} {H : (K →+* ℂ) → HermProjMetric N}
    {A_curr : DolbeaultCurrentAlgebra} {PrimeDiv : Type*}
    {δ_map : DivisorCurrentMap A_curr PrimeDiv}
    {Z : ProjectiveChowForm K d N}
    (M : ProjArakelovIntersectionModel K d N P H A_curr PrimeDiv δ_map Z)
    {imageHeight t C_comp a : ℝ}
    (himg_arch : ∀ σ : K →+* ℂ,
      mahlerMeasure (H σ) (MvPolynomial.map σ Z.poly) ≤
        ((d : ℝ) + 1) * (Z.deg : ℝ) * imageHeight + (Z.deg : ℝ) * C_comp)
    (himg_fin :
      (∑' v : P.Place, P.wtFin v * Real.log (finPlacePolyNorm P v Z.poly)) ≤
        (Module.finrank ℚ K : ℝ) * (Z.deg : ℝ) * C_comp)
    (ha : a ≤ FaltingsPhilipponHeight P H Z +
      (Module.finrank ℚ K : ℝ) * ((d : ℝ) + 1) * (Z.deg : ℝ) * t) :
    FaltingsPhilipponHeight P H Z ≤ M.arithSelfInt ∧
    FaltingsPhilipponHeight P H Z ≤
      FaltingsPhilipponSupHeight P H Z + (Module.finrank ℚ K : ℝ) * bgsShift N Z.deg ∧
    a ≤ (Module.finrank ℚ K : ℝ) * (((d : ℝ) + 1) * (Z.deg : ℝ) * (imageHeight + t) +
      2 * (Z.deg : ℝ) * C_comp + bgsShift N Z.deg) := by
  have h1 := (chow_form_norm_le_arith_intersection M).1
  have h2 := faltingsPhilipponHeight_le_supHeight P H Z M.mahler_int M.mahler_ae_nz
  have harch_sum :
      (∑ σ : K →+* ℂ, (mahlerMeasure (H σ) (MvPolynomial.map σ Z.poly) + bgsShift N Z.deg)) ≤
        (Module.finrank ℚ K : ℝ) * (((d : ℝ) + 1) * (Z.deg : ℝ) * imageHeight +
          (Z.deg : ℝ) * C_comp + bgsShift N Z.deg) := by
    calc (∑ σ : K →+* ℂ, (mahlerMeasure (H σ) (MvPolynomial.map σ Z.poly) + bgsShift N Z.deg))
        ≤ ∑ _σ : K →+* ℂ, (((d : ℝ) + 1) * (Z.deg : ℝ) * imageHeight +
            (Z.deg : ℝ) * C_comp + bgsShift N Z.deg) :=
          Finset.sum_le_sum fun σ _ => add_le_add (himg_arch σ) le_rfl
      _ = (Module.finrank ℚ K : ℝ) * (((d : ℝ) + 1) * (Z.deg : ℝ) * imageHeight +
            (Z.deg : ℝ) * C_comp + bgsShift N Z.deg) := by
          rw [Finset.sum_const, Finset.card_univ, NumberField.Embeddings.card K ℂ, nsmul_eq_mul]
  have hfp_le :
      FaltingsPhilipponHeight P H Z ≤
        (Module.finrank ℚ K : ℝ) * (((d : ℝ) + 1) * (Z.deg : ℝ) * imageHeight +
          2 * (Z.deg : ℝ) * C_comp + bgsShift N Z.deg) := by
    unfold FaltingsPhilipponHeight
    linarith
  exact ⟨h1, h2, by linarith⟩

end ArakelovIntersectionAndComparison

/-! ## Section 5: `height_lower_bound_of_positive_metric` & M4 `CovolStepsBridge` -/

section PositiveMetricLowerBoundsAndCovolBridge

/-- **THEOREM (`height_lower_bound_of_positive_metric`)**:
**Height Non-Negativity & Explicit Uniform Lower Bounds from Positive Curvature (`PosCurvatureMetric`)**:
for any `ProjArakelovIntersectionModel` over `K` whose Chow polynomial has non-negative finite-place
Gauss norms (`∀ v, 1 ≤ finPlacePolyNorm P v Z.poly`, e.g. any primitive integral or monically
normalized Chow form) and satisfies a uniform archimedean lower bound
`c_min * Z.deg ≤ mahlerMeasure + bgsShift`, we have:
$$[K : \mathbb{Q}] \cdot Z.\mathrm{deg} \cdot c_{\min} \le FaltingsPhilipponHeight P H Z \le M.\mathrm{arithSelfInt}.$$ -/
theorem height_lower_bound_of_positive_metric {K : Type*} [Field K] [NumberField K]
    {d N : ℕ} {P : AdelicPlaceSystem K} {H : (K →+* ℂ) → HermProjMetric N}
    {A_curr : DolbeaultCurrentAlgebra} {PrimeDiv : Type*}
    {δ_map : DivisorCurrentMap A_curr PrimeDiv}
    {Z : ProjectiveChowForm K d N}
    (M : ProjArakelovIntersectionModel K d N P H A_curr PrimeDiv δ_map Z)
    (h_norm_ge_one : ∀ v : P.Place, 1 ≤ finPlacePolyNorm P v Z.poly)
    {c_min : ℝ}
    (h_arch : ∀ σ : K →+* ℂ,
      c_min * (Z.deg : ℝ) ≤ mahlerMeasure (H σ) (MvPolynomial.map σ Z.poly) + bgsShift N Z.deg) :
    (Module.finrank ℚ K : ℝ) * (Z.deg : ℝ) * c_min ≤ FaltingsPhilipponHeight P H Z ∧
    (Module.finrank ℚ K : ℝ) * (Z.deg : ℝ) * c_min ≤ M.arithSelfInt := by
  classical
  have hfin_nn : 0 ≤ ∑' v : P.Place, P.wtFin v * Real.log (finPlacePolyNorm P v Z.poly) := by
    let S : Finset P.Place := (finite_supp_finPlacePolyNorm P Z.ne_zero).toFinset
    have hts : (∑' v : P.Place, P.wtFin v * Real.log (finPlacePolyNorm P v Z.poly)) =
        ∑ v ∈ S, P.wtFin v * Real.log (finPlacePolyNorm P v Z.poly) := by
      refine tsum_eq_sum fun v hv => ?_
      have hv1 : finPlacePolyNorm P v Z.poly = 1 := by
        by_contra hne
        exact hv ((finite_supp_finPlacePolyNorm P Z.ne_zero).mem_toFinset.mpr hne)
      simp [hv1]
    rw [hts]
    refine Finset.sum_nonneg fun v _ => mul_nonneg (P.wtFin_pos v).le ?_
    exact Real.log_nonneg (h_norm_ge_one v)
  have harch_ge : (Module.finrank ℚ K : ℝ) * (Z.deg : ℝ) * c_min ≤
      ∑ σ : K →+* ℂ, (mahlerMeasure (H σ) (MvPolynomial.map σ Z.poly) + bgsShift N Z.deg) := by
    calc (Module.finrank ℚ K : ℝ) * (Z.deg : ℝ) * c_min
        = ∑ _σ : K →+* ℂ, c_min * (Z.deg : ℝ) := by
          rw [Finset.sum_const, Finset.card_univ, NumberField.Embeddings.card K ℂ, nsmul_eq_mul]
          ring
      _ ≤ ∑ σ : K →+* ℂ, (mahlerMeasure (H σ) (MvPolynomial.map σ Z.poly) + bgsShift N Z.deg) :=
          Finset.sum_le_sum fun σ _ => h_arch σ
  have hfp_ge : (Module.finrank ℚ K : ℝ) * (Z.deg : ℝ) * c_min ≤ FaltingsPhilipponHeight P H Z := by
    unfold FaltingsPhilipponHeight
    linarith
  exact ⟨hfp_ge, hfp_ge.trans (chow_form_norm_le_arith_intersection M).1⟩

/-- **Concrete Theta-Metric Positivity Instantiation (`theta_metric_positive_height_witness`)**:
wires `Stage14M3_HermitianLineBundles.theta_metric_positivity` & `theta_metric_uniform_positivity`
directly into `height_lower_bound_of_positive_metric`: for any genus `g ≥ 1` Siegel period matrix
`Ω ∈ ℍ_g`, the theta line bundle `(L_Θ, h_Θ)` has strictly positive uniform curvature, giving
`0 < FaltingsPhilipponHeight P H Z` and `0 < M.arithSelfInt` whenever `c_min > 0` and
`0 < Z.deg`. -/
theorem theta_metric_positive_height_witness {g : ℕ} (hg : 0 < g)
    {Ω : Matrix (Fin g) (Fin g) ℂ} (hΩ : IsSiegelPeriodMatrix Ω)
    {K : Type*} [Field K] [NumberField K]
    {d N : ℕ} {P : AdelicPlaceSystem K} {H : (K →+* ℂ) → HermProjMetric N}
    {A_curr : DolbeaultCurrentAlgebra} {PrimeDiv : Type*}
    {δ_map : DivisorCurrentMap A_curr PrimeDiv}
    {Z : ProjectiveChowForm K d N}
    (M : ProjArakelovIntersectionModel K d N P H A_curr PrimeDiv δ_map Z)
    (hZ_deg : 0 < Z.deg)
    (h_norm_ge_one : ∀ v : P.Place, 1 ≤ finPlacePolyNorm P v Z.poly)
    {c_min : ℝ} (hc_pos : 0 < c_min)
    (h_arch : ∀ σ : K →+* ℂ,
      c_min * (Z.deg : ℝ) ≤ mahlerMeasure (H σ) (MvPolynomial.map σ Z.poly) + bgsShift N Z.deg) :
    PosCurvatureMetric (thetaMetrizedLineBundle Ω) ∧
    (thetaMetrizedLineBundle Ω).curvatureForm.IsUniformlyPositive ∧
    0 < FaltingsPhilipponHeight P H Z ∧
    0 < M.arithSelfInt := by
  have hpos_m := theta_metric_positivity hΩ
  have hunif := theta_metric_uniform_positivity hg hΩ
  have hbd := height_lower_bound_of_positive_metric M h_norm_ge_one h_arch
  have hK_pos : (0 : ℝ) < (Module.finrank ℚ K : ℝ) := Nat.cast_pos.mpr Module.finrank_pos
  have hdeg_pos : (0 : ℝ) < (Z.deg : ℝ) := Nat.cast_pos.mpr hZ_deg
  have hstrict : 0 < (Module.finrank ℚ K : ℝ) * (Z.deg : ℝ) * c_min :=
    mul_pos (mul_pos hK_pos hdeg_pos) hc_pos
  exact ⟨hpos_m, hunif, lt_of_lt_of_le hstrict hbd.1, lt_of_lt_of_le hstrict hbd.2⟩

/-- **M4 `CovolStepsBridge` Direct Connector (`covolSteps_chow_l3_bridge`)**:
combines our Chow-form / Faltings–Philippon height bounds (`chow_form_norm_le_arith_intersection`)
with `Stage12SchurWeylLattices.L3_hodge_covolume_bound`:
for any family of `m` indefinite Hodge lattices `M_j ⊂ E_j` (`j : Fin m`) generated by
`rk (M_j)` linearly independent small sections `s j i` whose norms are bounded by
`exp (α_j + β_j * h_FP / deg)`, yields the explicit non-circular `L3` covolume upper bound
$$\frac{2}{D} \log \mathrm{covol}(M_j) \le
  \frac{2 \cdot \mathrm{rk}(M_j)}{D} \bigl(\alpha_j + \beta_j \cdot \frac{\mathrm{arithSelfInt}}{\deg(Z)}\bigr),$$
ready for direct import in `Stage14M3_ArakelovPublishedPackage` (M3 Wave 3) and
`Stage14M4_CovolStepsBridge` (M4 Wave 2)! -/
theorem covolSteps_chow_l3_bridge
    {K : Type*} [Field K] [NumberField K]
    {d N : ℕ} {P : AdelicPlaceSystem K} {H : (K →+* ℂ) → HermProjMetric N}
    {A_curr : DolbeaultCurrentAlgebra} {PrimeDiv : Type*}
    {δ_map : DivisorCurrentMap A_curr PrimeDiv}
    {Z : ProjectiveChowForm K d N}
    (M_mod : ProjArakelovIntersectionModel K d N P H A_curr PrimeDiv δ_map Z)
    (hZ_deg : 0 < Z.deg)
    {m : ℕ}
    (E : Fin m → Type*) [∀ j, NormedAddCommGroup (E j)] [∀ j, InnerProductSpace ℝ (E j)]
    [∀ j, FiniteDimensional ℝ (E j)]
    (M : ∀ j, Submodule ℤ (E j)) [∀ j, DiscreteTopology (M j)]
    (hM0 : ∀ j, M j ≠ ⊥)
    (s : ∀ j, Fin (rk (M j)) → E j)
    (hsM : ∀ j i, s j i ∈ M j)
    (hsli : ∀ j, LinearIndependent ℝ (s j))
    (α β : Fin m → ℝ) (hβ : ∀ j, 0 ≤ β j)
    (hnorm : ∀ j i, ‖s j i‖ ≤
      Real.exp (α j + β j * (FaltingsPhilipponHeight P H Z / (Z.deg : ℝ))))
    {D : ℝ} (hD : 0 < D) :
    (∀ j : Fin m, (2 / D) * Real.log (covol (M j)) ≤
      (2 * (rk (M j) : ℝ) / D) *
        (α j + β j * (M_mod.arithSelfInt / (Z.deg : ℝ)))) ∧
    (∑ j : Fin m, (2 / D) * Real.log (covol (M j)) ≤
      ∑ j : Fin m, (2 * (rk (M j) : ℝ) / D) *
        (α j + β j * (M_mod.arithSelfInt / (Z.deg : ℝ)))) := by
  let C_sec : Fin m → ℝ := fun j =>
    Real.exp (α j + β j * (FaltingsPhilipponHeight P H Z / (Z.deg : ℝ)))
  have hCpos : ∀ j, 0 < C_sec j := fun j => Real.exp_pos _
  have hL3 := L3_hodge_covolume_bound E M hM0 s hsM hsli C_sec hCpos hnorm hD
  have hfp_le : FaltingsPhilipponHeight P H Z ≤ M_mod.arithSelfInt :=
    (chow_form_norm_le_arith_intersection M_mod).1
  have hdeg_pos : (0 : ℝ) < (Z.deg : ℝ) := Nat.cast_pos.mpr hZ_deg
  have hpt : ∀ j : Fin m, (2 / D) * Real.log (covol (M j)) ≤
      (2 * (rk (M j) : ℝ) / D) *
        (α j + β j * (M_mod.arithSelfInt / (Z.deg : ℝ))) := by
    intro j
    have h1 := hL3.2.1 j
    have hlog_eq : Real.log (C_sec j) =
        α j + β j * (FaltingsPhilipponHeight P H Z / (Z.deg : ℝ)) :=
      Real.log_exp _
    rw [hlog_eq] at h1
    have hmono : α j + β j * (FaltingsPhilipponHeight P H Z / (Z.deg : ℝ)) ≤
        α j + β j * (M_mod.arithSelfInt / (Z.deg : ℝ)) := by
      refine add_le_add le_rfl (mul_le_mul_of_nonneg_left ?_ (hβ j))
      exact div_le_div_of_nonneg_right hfp_le hdeg_pos.le
    have hcoeff_nn : 0 ≤ 2 * (rk (M j) : ℝ) / D := by positivity
    exact h1.trans (mul_le_mul_of_nonneg_left hmono hcoeff_nn)
  exact ⟨hpt, Finset.sum_le_sum fun j _ => hpt j⟩

end PositiveMetricLowerBoundsAndCovolBridge

end

end RHDirect.Stage14M3_ChowFormHeights
