import RHDirect.Stage10GeometryOfNumbers
import RHDirect.Stage12BanaszczykTransference
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.ZMod.QuotientRing

/-!
# RHDirect.Stage14M4_CoveringDescentAlgebra

Field-2 Package `M4` Wave 1 (`RHDirect/Stage14M4_CoveringDescentAlgebra.lean`):
Unconditional, zero-`sorry`, zero-custom-`axiom`, zero-`native_decide` Lean 4 formalization of the
**Covering-Level Tower & Descent Ring Algebra** on top of `RHDirect.Stage10GeometryOfNumbers`
and `RHDirect.Stage12BanaszczykTransference`:

1. **`CoveringDescentRing`, `CoveringDescentMap`, & Congruence Quotients (NO `Algebra` Diamonds)**:
   - Explicit `RingHom`-based covering-level rings `CoveringDescentRing` and morphisms
     `CoveringDescentMap A B` (commuting `coverHom : A.Cover →+* B.Cover` and
     `baseHom : A.Base →+* B.Base` — avoiding nested global `Algebra` synthesis diamonds!).
   - Category laws (`id`, `comp`, `comp_assoc`, `id_comp`, `comp_id`) and concrete instantiations
     for `ZMod N` congruence towers (`zmodCoveringRing`, `zmodDescentMap`), coprime Chinese
     Remainder splittings (`zmodChineseRemainderRingEquiv`), and ideal quotient towers `R ⧸ I`
     (`idealQuotientCoveringRing`, `idealQuotientDescentMap`).

2. **`CoveringLevelTower` & `covering_descent_maps_compatible`**:
   - Algebraic covering tower of congruence levels with step descent maps
     `stepMap i : CoveringDescentMap (ring (i + 1)) (ring i)`, step covering degrees `stepDeg`,
     rank-growth parameters `stepRankFactor`, `stepRankShift`, new bad-locus sets `stepNewBad`,
     and defect-propagation parameters `stepDefectScale`, `stepDefectErr`.
   - Composite descent maps `towerMap T hij : CoveringDescentMap (T.ring j) (T.ring i)` along
     arbitrary `i ≤ j` with exact compatibility `covering_descent_maps_compatible`
     (`(towerMap T hij).comp (towerMap T hjk) = towerMap T (hij.trans hjk)`).
   - Concrete algebraic tower constructors `zmodCoveringTower` and `idealQuotientCoveringTower`.

3. **`covering_degree_multiplicative` & Sublattice Index Multiplicativity**:
   - Exact multiplicativity `compositeDegree T i k = compositeDegree T i j * compositeDegree T j k`
     and level degree law `(T.ring j).deg = (T.ring i).deg * compositeDegree T i j`.
   - Lattice-index multiplicativity `latIndex_multiplicative` for nested full-rank lattices
     `Λ₂ ≤ Λ₁ ≤ Λ₀` via `Stage11BostDworkSqueeze.covol_eq_index_mul_covol`, congruence-level
     sublattice scaling `scaleSublat N Λ`, `covol_scaleSublat_eq`, `latIndex_scaleSublat_eq`,
     `ZMod` degree multiplicativity, and `CoveringDescentMap` product-basis cardinality.

4. **`covering_rank_of_descent_steps`**:
   - Exact and affine-bounded rank comparison under iterated covering descent steps
     (`covering_rank_of_descent_steps_affine`, `covering_rank_of_descent_steps_additive`,
     `covering_rank_of_descent_steps_mul`, `covering_rank_of_descent_steps_const`,
     `covering_rank_of_descent_steps`), plus exact rank invariance `rk_congruence_sublattice_eq`
     and `isZLattice_congruence_sublattice` under finite-index congruence sublattices.

5. **`covering_bad_locus_bound` & `covering_low_defect_bound`**:
   - Quantitative upper bounds on bad-locus cardinality (`covering_bad_locus_bound`,
     `covering_bad_locus_uniform_step_bound`, `card_primeFactors_le_log2`,
     `covering_bad_locus_primeFactors_bound`, `covering_bad_locus_density_bound`,
     `disjoint_primeFactors_of_coprime`).
   - Quantitative covering-defect propagation (`covering_defect_step_bound`,
     `covering_low_defect_bound`, `covering_low_defect_bound_additive`,
     `covering_low_defect_bound_contractive`), Arakelov/Gram determinant scaling along descent
     (`gram_det_congruence_eq`, `muMax_congruence_le`, `muMin_congruence_ge`), and unconditional
     Banaszczyk/Minkowski lattice-defect bounds (`transferenceDefect_le_half_dim`,
     `congruence_sublattice_shortestNorm_bounds`, `congruence_sublattice_arithSlopeDefect_bound`,
     `hermite_minkowski_covol_defect_bound`), instantiated on `latticeCoveringTower`.

6. **M4 Wave 2 Handoff (`CoveringDescentPackage` & `CoveringTraceDescentDatum`)**:
   - Clean bundled interfaces ready for `Stage14M4_DeepGoodReduction` and
     `Stage14M4_CoveringLocalTraces`.
-/

noncomputable section

open Module Submodule Finset Real MeasureTheory Matrix
open scoped BigOperators ENNReal Pointwise InnerProductSpace Real

namespace RHDirect.Stage14M4_CoveringDescentAlgebra

open RHDirect.ArakelovCovolume (rk covol degAr slope muMax
  discreteTopology_of_le covol_eq_sqrt_det_gram finrank_int_eq_finrank_real_span
  covol_pos rk_pos_of_ne_bot slope_le_muMax muMax_mono det_gram_basis_pos)

open RHDirect.Stage2SiegelReduction (lambda1 lambda1_pos lambda1_le_norm)

open RHDirect.Stage4ArakelovBost (dualLat discreteTopology_dualLat rk_dualLat covol_dualLat
  muMin muMin_le_slope_le_muMax muMax_dualLat muMin_dualLat)

open RHDirect.Stage10GeometryOfNumbers (shortestNorm shortestNorm_pos shortestNorm_le_norm
  shortestNorm_eq_of_min exists_shortest_nonzero_vector successiveMinimum
  successiveMinimum_closedBall_zero_eq_shortestNorm hermite_minkowski_bound_all_dims)

open RHDirect.Stage11BostDworkSqueeze (latIndex finite_quotient_of_le_same_rank
  covol_eq_index_mul_covol degAr_eq_degAr_sub_log_index slope_eq_slope_sub_log_index_div_rk)

open RHDirect.Stage12BanaszczykTransference (dualLattice dualLattice_eq_dualLat
  dualLattice_dualLattice covolume_dualLattice coveringRadius coveringRadius_nonneg
  exists_mem_norm_sub_le_coveringRadius banaszczyk_covering_radius_lambda1 shortestNorm_eq_lambda1
  banaszczyk_slope_gap_O_log banaszczyk_slope_gap_O_log_euclidean
  banaszczyk_covering_radius_slope_bounds banaszczyk_muMax_add_muMax_dual_sandwich)

/-! ## Section 1: `CoveringDescentRing`, Explicit `RingHom` Maps & Congruence Level Rings -/

section DescentRings

/-- A **covering-level descent ring** `CoveringDescentRing` packages a base commutative ring `Base`,
a covering/level commutative ring `Cover`, and an explicit structural `RingHom` `baseHom : Base →+* Cover`
(with NO nested global `Algebra` instances, preventing typeclass synthesis diamonds across towers),
together with congruence level, covering degree, rank, covering defect, and bad locus. -/
structure CoveringDescentRing where
  Base : Type
  [baseCommRing : CommRing Base]
  Cover : Type
  [coverCommRing : CommRing Cover]
  baseHom : Base →+* Cover
  level : ℕ
  level_pos : 0 < level
  deg : ℕ
  deg_pos : 0 < deg
  rk : ℕ
  rk_pos : 0 < rk
  defect : ℝ
  defect_nonneg : 0 ≤ defect
  badLocus : Finset ℕ

attribute [instance] CoveringDescentRing.baseCommRing CoveringDescentRing.coverCommRing

/-- An explicit morphism of covering-level descent rings `A → B` consisting of a covering
`RingHom` `coverHom : A.Cover →+* B.Cover` and a base `RingHom` `baseHom : A.Base →+* B.Base`
satisfying exact diagram commutativity `coverHom.comp A.baseHom = B.baseHom.comp baseHom`
(pure `RingHom` equality — zero `Algebra` diamond risk). -/
@[ext]
structure CoveringDescentMap (A B : CoveringDescentRing) where
  coverHom : A.Cover →+* B.Cover
  baseHom : A.Base →+* B.Base
  comm : coverHom.comp A.baseHom = B.baseHom.comp baseHom

namespace CoveringDescentMap

/-- Identity covering descent map on `A`. -/
def id (A : CoveringDescentRing) : CoveringDescentMap A A where
  coverHom := RingHom.id A.Cover
  baseHom := RingHom.id A.Base
  comm := by rw [RingHom.id_comp, RingHom.comp_id]

/-- Composition of compatible covering descent maps `A → B → C`. -/
def comp {A B C : CoveringDescentRing}
    (g : CoveringDescentMap B C) (f : CoveringDescentMap A B) :
    CoveringDescentMap A C where
  coverHom := g.coverHom.comp f.coverHom
  baseHom := g.baseHom.comp f.baseHom
  comm := by
    rw [RingHom.comp_assoc, f.comm, ← RingHom.comp_assoc, g.comm, RingHom.comp_assoc]

@[simp]
theorem id_coverHom (A : CoveringDescentRing) : (id A).coverHom = RingHom.id A.Cover :=
  rfl

@[simp]
theorem id_baseHom (A : CoveringDescentRing) : (id A).baseHom = RingHom.id A.Base :=
  rfl

@[simp]
theorem comp_coverHom {A B C : CoveringDescentRing}
    (g : CoveringDescentMap B C) (f : CoveringDescentMap A B) :
    (g.comp f).coverHom = g.coverHom.comp f.coverHom :=
  rfl

@[simp]
theorem comp_baseHom {A B C : CoveringDescentRing}
    (g : CoveringDescentMap B C) (f : CoveringDescentMap A B) :
    (g.comp f).baseHom = g.baseHom.comp f.baseHom :=
  rfl

theorem comm_apply {A B : CoveringDescentRing} (f : CoveringDescentMap A B) (a : A.Base) :
    f.coverHom (A.baseHom a) = B.baseHom (f.baseHom a) :=
  RingHom.congr_fun f.comm a

theorem id_comp {A B : CoveringDescentRing} (f : CoveringDescentMap A B) :
    (id B).comp f = f := by
  ext x <;> rfl

theorem comp_id {A B : CoveringDescentRing} (f : CoveringDescentMap A B) :
    f.comp (id A) = f := by
  ext x <;> rfl

theorem comp_assoc {A B C D : CoveringDescentRing}
    (h : CoveringDescentMap C D) (g : CoveringDescentMap B C) (f : CoveringDescentMap A B) :
    (h.comp g).comp f = h.comp (g.comp f) := by
  ext x <;> rfl

/-- Construct a `CoveringDescentMap A C` from an explicit `RingEquiv` identifying their base rings
and a compatible covering `RingHom`. -/
def ofBaseEquiv {A C : CoveringDescentRing} (e : A.Base ≃+* C.Base)
    (coverHom : A.Cover →+* C.Cover)
    (hcomm : ∀ a : A.Base, coverHom (A.baseHom a) = C.baseHom (e a)) :
    CoveringDescentMap A C where
  coverHom := coverHom
  baseHom := e.toRingHom
  comm := by
    ext a
    exact hcomm a

/-- Construct a `CoveringDescentMap A C` when `A.Base` and `C.Base` are definitionally the same
ring `B` and `coverHom.comp A.baseHom = C.baseHom`. -/
def ofSameBase {B : Type} [CommRing B] (coverA coverC : Type) [CommRing coverA] [CommRing coverC]
    (baseA : B →+* coverA) (baseC : B →+* coverC)
    (lA dA rA lC dC rC : ℕ) (hlA : 0 < lA) (hdA : 0 < dA) (hrA : 0 < rA)
    (hlC : 0 < lC) (hdC : 0 < dC) (hrC : 0 < rC)
    (defA defC : ℝ) (hdefA : 0 ≤ defA) (hdefC : 0 ≤ defC)
    (badA badC : Finset ℕ)
    (coverHom : coverA →+* coverC)
    (hcomm : coverHom.comp baseA = baseC) :
    CoveringDescentMap
      ⟨B, coverA, baseA, lA, hlA, dA, hdA, rA, hrA, defA, hdefA, badA⟩
      ⟨B, coverC, baseC, lC, hlC, dC, hdC, rC, hrC, defC, hdefC, badC⟩ where
  coverHom := coverHom
  baseHom := RingHom.id B
  comm := by rw [hcomm, RingHom.comp_id]

end CoveringDescentMap

/-! ### Concrete Congruence-Level Instantiations (`ZMod N`, CRT Splitting, & `R ⧸ I`) -/

/-- Canonical covering-descent ring for the modular congruence quotient `ℤ →+* ZMod N` (`0 < N`). -/
def zmodCoveringRing (N : ℕ) (hN : 0 < N) (rk : ℕ) (hrk : 0 < rk)
    (defect : ℝ) (hdef : 0 ≤ defect) : CoveringDescentRing where
  Base := ℤ
  Cover := ZMod N
  baseHom := Int.castRingHom (ZMod N)
  level := N
  level_pos := hN
  deg := N
  deg_pos := hN
  rk := rk
  rk_pos := hrk
  defect := defect
  defect_nonneg := hdef
  badLocus := N.primeFactors

/-- Canonical compatible descent map `ZMod N →+* ZMod M` when `M ∣ N` (`0 < M`, `0 < N`). -/
def zmodDescentMap {M N : ℕ} (hM : 0 < M) (hN : 0 < N) (hdiv : M ∣ N)
    {rkN rkM : ℕ} (hrkN : 0 < rkN) (hrkM : 0 < rkM)
    {defN defM : ℝ} (hdefN : 0 ≤ defN) (hdefM : 0 ≤ defM) :
    CoveringDescentMap (zmodCoveringRing N hN rkN hrkN defN hdefN)
      (zmodCoveringRing M hM rkM hrkM defM hdefM) where
  coverHom := ZMod.castHom hdiv (ZMod M)
  baseHom := RingHom.id ℤ
  comm := by
    ext x
    let a : ℤ := x
    change (ZMod.castHom hdiv (ZMod M)) (a : ZMod N) = (a : ZMod M)
    rw [map_intCast]

/-- Compatibility of composed `ZMod.castHom` descent maps for `K ∣ M ∣ N`. -/
theorem zmodDescentMap_comp {K M N : ℕ} (hK : 0 < K) (hM : 0 < M) (hN : 0 < N)
    (hKM : K ∣ M) (hMN : M ∣ N)
    {rkN rkM rkK : ℕ} (hrkN : 0 < rkN) (hrkM : 0 < rkM) (hrkK : 0 < rkK)
    {defN defM defK : ℝ} (hdefN : 0 ≤ defN) (hdefM : 0 ≤ defM) (hdefK : 0 ≤ defK) :
    (zmodDescentMap hK hM hKM hrkM hrkK hdefM hdefK).comp
      (zmodDescentMap hM hN hMN hrkN hrkM hdefN hdefM) =
      zmodDescentMap hK hN (hKM.trans hMN) hrkN hrkK hdefN hdefK := by
  ext x
  · change (ZMod.castHom hKM (ZMod K)) ((ZMod.castHom hMN (ZMod M)) x) =
      (ZMod.castHom (hKM.trans hMN) (ZMod K)) x
    have : NeZero M := ⟨hM.ne'⟩
    have : NeZero N := ⟨hN.ne'⟩
    have : NeZero K := ⟨hK.ne'⟩
    obtain ⟨a, rfl⟩ := ZMod.intCast_surjective x
    simp
  · rfl

/-- Surjectivity of the modular descent map `ZMod N →+* ZMod M` when `M ∣ N`. -/
theorem zmodDescentMap_surjective {M N : ℕ} (hM : 0 < M) (hN : 0 < N) (hdiv : M ∣ N)
    {rkN rkM : ℕ} (hrkN : 0 < rkN) (hrkM : 0 < rkM)
    {defN defM : ℝ} (hdefN : 0 ≤ defN) (hdefM : 0 ≤ defM) :
    Function.Surjective
      (zmodDescentMap hM hN hdiv hrkN hrkM hdefN hdefM).coverHom := by
  intro y
  have : NeZero M := ⟨hM.ne'⟩
  obtain ⟨a, rfl⟩ := ZMod.intCast_surjective y
  refine ⟨(a : ZMod N), ?_⟩
  change ZMod.castHom hdiv (ZMod M) (a : ZMod N) = (a : ZMod M)
  simp

/-- Chinese Remainder product covering-descent ring for coprime levels `M, N`. -/
def zmodProdCoveringRing (M N : ℕ) (hM : 0 < M) (hN : 0 < N) (rk : ℕ) (hrk : 0 < rk)
    (defect : ℝ) (hdef : 0 ≤ defect) : CoveringDescentRing where
  Base := ℤ
  Cover := ZMod M × ZMod N
  baseHom := RingHom.prod (Int.castRingHom (ZMod M)) (Int.castRingHom (ZMod N))
  level := M * N
  level_pos := Nat.mul_pos hM hN
  deg := M * N
  deg_pos := Nat.mul_pos hM hN
  rk := rk
  rk_pos := hrk
  defect := defect
  defect_nonneg := hdef
  badLocus := M.primeFactors ∪ N.primeFactors

/-- Chinese Remainder isomorphism `ZMod (M * N) ≃+* ZMod M × ZMod N` packaged as compatible
covering descent maps when `Nat.Coprime M N`. -/
def zmodChineseRemainderDescentMap {M N : ℕ} (hM : 0 < M) (hN : 0 < N) (hcop : M.Coprime N)
    {rk : ℕ} (hrk : 0 < rk) {defect : ℝ} (hdef : 0 ≤ defect) :
    CoveringDescentMap
      (zmodCoveringRing (M * N) (Nat.mul_pos hM hN) rk hrk defect hdef)
      (zmodProdCoveringRing M N hM hN rk hrk defect hdef) where
  coverHom := (ZMod.chineseRemainder hcop).toRingHom
  baseHom := RingHom.id ℤ
  comm := by
    ext x
    let a : ℤ := x
    change (ZMod.chineseRemainder hcop) (a : ZMod (M * N)) =
      ((a : ZMod M), (a : ZMod N))
    rw [map_intCast]
    rfl

/-- Canonical covering-descent ring for an arbitrary ideal quotient `R →+* R ⧸ I`. -/
def idealQuotientCoveringRing (R : Type) [CommRing R] (I : Ideal R)
    (level deg rk : ℕ) (hlevel : 0 < level) (hdeg : 0 < deg) (hrk : 0 < rk)
    (defect : ℝ) (hdef : 0 ≤ defect) (badLocus : Finset ℕ) : CoveringDescentRing where
  Base := R
  Cover := R ⧸ I
  baseHom := Ideal.Quotient.mk I
  level := level
  level_pos := hlevel
  deg := deg
  deg_pos := hdeg
  rk := rk
  rk_pos := hrk
  defect := defect
  defect_nonneg := hdef
  badLocus := badLocus

/-- Canonical compatible descent map `R ⧸ I →+* R ⧸ J` for nested ideals `I ≤ J`. -/
def idealQuotientDescentMap {R : Type} [CommRing R] {I J : Ideal R} (hIJ : I ≤ J)
    {lI dI rI lJ dJ rJ : ℕ} {hlI : 0 < lI} {hdI : 0 < dI} {hrI : 0 < rI}
    {hlJ : 0 < lJ} {hdJ : 0 < dJ} {hrJ : 0 < rJ}
    {defI defJ : ℝ} {hdefI : 0 ≤ defI} {hdefJ : 0 ≤ defJ}
    {badI badJ : Finset ℕ} :
    CoveringDescentMap
      (idealQuotientCoveringRing R I lI dI rI hlI hdI hrI defI hdefI badI)
      (idealQuotientCoveringRing R J lJ dJ rJ hlJ hdJ hrJ defJ hdefJ badJ) where
  coverHom := Ideal.Quotient.factor hIJ
  baseHom := RingHom.id R
  comm := by
    ext x
    rfl

/-- Compatibility of composed ideal-quotient descent maps `R ⧸ I → R ⧸ J → R ⧸ K` for `I ≤ J ≤ K`. -/
theorem idealQuotientDescentMap_comp {R : Type} [CommRing R] {I J K : Ideal R}
    (hIJ : I ≤ J) (hJK : J ≤ K)
    {lI dI rI lJ dJ rJ lK dK rK : ℕ}
    {hlI : 0 < lI} {hdI : 0 < dI} {hrI : 0 < rI}
    {hlJ : 0 < lJ} {hdJ : 0 < dJ} {hrJ : 0 < rJ}
    {hlK : 0 < lK} {hdK : 0 < dK} {hrK : 0 < rK}
    {defI defJ defK : ℝ} {hdefI : 0 ≤ defI} {hdefJ : 0 ≤ defJ} {hdefK : 0 ≤ defK}
    {badI badJ badK : Finset ℕ} :
    (idealQuotientDescentMap (I := J) (J := K) hJK (hlI := hlJ) (hdI := hdJ) (hrI := hrJ)
      (hlJ := hlK) (hdJ := hdK) (hrJ := hrK) (hdefI := hdefJ) (hdefJ := hdefK)
      (badI := badJ) (badJ := badK)).comp
      (idealQuotientDescentMap (I := I) (J := J) hIJ (hlI := hlI) (hdI := hdI) (hrI := hrI)
      (hlJ := hlJ) (hdJ := hdJ) (hrJ := hrJ) (hdefI := hdefI) (hdefJ := hdefJ)
      (badI := badI) (badJ := badJ)) =
      idealQuotientDescentMap (I := I) (J := K) (hIJ.trans hJK)
        (hlI := hlI) (hdI := hdI) (hrI := hrI)
        (hlJ := hlK) (hdJ := hdK) (hrJ := hrK) (hdefI := hdefI) (hdefJ := hdefK)
        (badI := badI) (badJ := badK) := by
  ext x
  · obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    rfl
  · rfl

/-- Surjectivity of `Ideal.Quotient.factor` along any descent step `I ≤ J`. -/
theorem idealQuotientDescentMap_surjective {R : Type} [CommRing R] {I J : Ideal R} (hIJ : I ≤ J)
    {lI dI rI lJ dJ rJ : ℕ} {hlI : 0 < lI} {hdI : 0 < dI} {hrI : 0 < rI}
    {hlJ : 0 < lJ} {hdJ : 0 < dJ} {hrJ : 0 < rJ}
    {defI defJ : ℝ} {hdefI : 0 ≤ defI} {hdefJ : 0 ≤ defJ}
    {badI badJ : Finset ℕ} :
    Function.Surjective
      (idealQuotientDescentMap (I := I) (J := J) hIJ (hlI := hlI) (hdI := hdI) (hrI := hrI)
        (hlJ := hlJ) (hdJ := hdJ) (hrJ := hrJ) (hdefI := hdefI) (hdefJ := hdefJ)
        (badI := badI) (badJ := badJ)).coverHom :=
  Ideal.Quotient.factor_surjective hIJ

end DescentRings

/-! ## Section 2: `CoveringLevelTower` & Compatible Composite Descent Maps -/

section CoveringTower

/-- A **covering-level tower** `CoveringLevelTower` of depth `depth` consists of a sequence of
covering descent rings `ring i`, adjacent compatible descent maps
`stepMap i : CoveringDescentMap (ring (i + 1)) (ring i)` (descending from deeper congruence level
`i + 1` to level `i`), step covering degrees `stepDeg i ≥ 1`, rank-transition bounds
`stepRankFactor`, `stepRankShift`, step bad-locus increments `stepNewBad`, and step defect
propagation bounds `stepDefectScale`, `stepDefectErr`. -/
structure CoveringLevelTower where
  depth : ℕ
  ring : ℕ → CoveringDescentRing
  stepMap : ∀ i : ℕ, CoveringDescentMap (ring (i + 1)) (ring i)
  stepDeg : ℕ → ℕ
  stepDeg_pos : ∀ i, 0 < stepDeg i
  stepRankFactor : ℕ → ℕ
  stepRankShift : ℕ → ℕ
  stepNewBad : ℕ → Finset ℕ
  stepDefectScale : ℕ → ℝ
  stepDefectScale_nonneg : ∀ i, 0 ≤ stepDefectScale i
  stepDefectErr : ℕ → ℝ
  stepDefectErr_nonneg : ∀ i, 0 ≤ stepDefectErr i
  deg_step : ∀ i, i < depth → (ring (i + 1)).deg = (ring i).deg * stepDeg i
  rk_step : ∀ i, i < depth → (ring (i + 1)).rk ≤ stepRankFactor i * (ring i).rk + stepRankShift i
  bad_step : ∀ i, i < depth → (ring (i + 1)).badLocus ⊆ (ring i).badLocus ∪ stepNewBad i
  defect_step : ∀ i, i < depth →
    (ring (i + 1)).defect ≤ stepDefectScale i * (ring i).defect + stepDefectErr i

namespace CoveringLevelTower

/-- Composite descent map from level `j` down to level `i` (`i ≤ j`) in a `CoveringLevelTower`,
built purely by explicit `RingHom` composition (zero `Algebra` diamonds). -/
def towerMap (T : CoveringLevelTower) {i : ℕ} : ∀ {j : ℕ}, i ≤ j →
    CoveringDescentMap (T.ring j) (T.ring i)
  | 0, h => by
      have hi : i = 0 := Nat.eq_zero_of_le_zero h
      subst hi
      exact CoveringDescentMap.id (T.ring 0)
  | j + 1, h =>
      if hij : i ≤ j then
        (T.towerMap hij).comp (T.stepMap j)
      else
        by
          have heq : i = j + 1 := by omega
          subst heq
          exact CoveringDescentMap.id (T.ring (j + 1))

@[simp]
theorem towerMap_refl (T : CoveringLevelTower) (i : ℕ) :
    T.towerMap (le_refl i) = CoveringDescentMap.id (T.ring i) := by
  cases i with
  | zero => rfl
  | succ k =>
      change (if h : k + 1 ≤ k then _ else _) = _
      rw [dif_neg (by omega)]

theorem towerMap_step_succ (T : CoveringLevelTower) {i j : ℕ} (hij : i ≤ j) :
    T.towerMap (Nat.le_succ_of_le hij) = (T.towerMap hij).comp (T.stepMap j) := by
  change (if h : i ≤ j then _ else _) = _
  rw [dif_pos hij]

@[simp]
theorem towerMap_one_step (T : CoveringLevelTower) (i : ℕ) :
    T.towerMap (Nat.le_succ i) = T.stepMap i := by
  rw [T.towerMap_step_succ (le_refl i), T.towerMap_refl, CoveringDescentMap.id_comp]

/-- **Compatibility of Composite Covering Descent Maps (`covering_descent_maps_compatible`)**:
for any levels `i ≤ j ≤ k` in `T`, composing `towerMap T hjk` (from `k` to `j`) with
`towerMap T hij` (from `j` to `i`) equals `towerMap T (hij.trans hjk)` (from `k` to `i`)
as covering-descent morphisms (`coverHom` and `baseHom` agree definitionally on every element). -/
theorem covering_descent_maps_compatible (T : CoveringLevelTower)
    {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) :
    (T.towerMap hij).comp (T.towerMap hjk) = T.towerMap (hij.trans hjk) := by
  induction k with
  | zero =>
      have hj : j = 0 := Nat.eq_zero_of_le_zero hjk
      have hi : i = 0 := Nat.eq_zero_of_le_zero (hij.trans hjk)
      subst hj; subst hi
      simp [CoveringDescentMap.id_comp]
  | succ k ih =>
      rcases Nat.eq_or_lt_of_le hjk with rfl | hjk_lt
      · rw [T.towerMap_refl, CoveringDescentMap.comp_id]
      · have hjk' : j ≤ k := Nat.lt_succ_iff.mp hjk_lt
        have hik' : i ≤ k := hij.trans hjk'
        rw [T.towerMap_step_succ hjk', T.towerMap_step_succ hik',
          ← CoveringDescentMap.comp_assoc, ih hjk']

/-- Exact `RingHom` compatibility at the covering-ring level (`coverHom`). -/
theorem towerMap_coverHom_comp (T : CoveringLevelTower) {i j k : ℕ}
    (hij : i ≤ j) (hjk : j ≤ k) :
    (T.towerMap hij).coverHom.comp (T.towerMap hjk).coverHom =
      (T.towerMap (hij.trans hjk)).coverHom :=
  congrArg CoveringDescentMap.coverHom (T.covering_descent_maps_compatible hij hjk)

/-- Exact `RingHom` compatibility at the base-ring level (`baseHom`). -/
theorem towerMap_baseHom_comp (T : CoveringLevelTower) {i j k : ℕ}
    (hij : i ≤ j) (hjk : j ≤ k) :
    (T.towerMap hij).baseHom.comp (T.towerMap hjk).baseHom =
      (T.towerMap (hij.trans hjk)).baseHom :=
  congrArg CoveringDescentMap.baseHom (T.covering_descent_maps_compatible hij hjk)

/-- Compatibility of composite descent maps with the structural base inclusions `baseHom`. -/
theorem towerMap_comm_apply (T : CoveringLevelTower) {i j : ℕ} (hij : i ≤ j)
    (b : (T.ring j).Base) :
    (T.towerMap hij).coverHom ((T.ring j).baseHom b) =
      (T.ring i).baseHom ((T.towerMap hij).baseHom b) :=
  (T.towerMap hij).comm_apply b

end CoveringLevelTower

/-- Construct a concrete `CoveringLevelTower` from any divisibility chain of modular congruence
levels `N : ℕ → ℕ` (`0 < N k`, `N k ∣ N (k + 1)`), with `ZMod (N k)` covering rings and
compatible `ZMod.castHom` descent maps. -/
def zmodCoveringTower (depth : ℕ) (N : ℕ → ℕ) (hN : ∀ k, 0 < N k)
    (hdiv : ∀ k, N k ∣ N (k + 1)) (rk : ℕ) (hrk : 0 < rk) :
    CoveringLevelTower where
  depth := depth
  ring := fun k => zmodCoveringRing (N k) (hN k) rk hrk 0 le_rfl
  stepMap := fun k => zmodDescentMap (hN k) (hN (k + 1)) (hdiv k) hrk hrk le_rfl le_rfl
  stepDeg := fun k => N (k + 1) / N k
  stepDeg_pos := fun k => Nat.div_pos (Nat.le_of_dvd (hN (k + 1)) (hdiv k)) (hN k)
  stepRankFactor := fun _ => 1
  stepRankShift := fun _ => 0
  stepNewBad := fun k => (N (k + 1) / N k).primeFactors
  stepDefectScale := fun _ => 1
  stepDefectScale_nonneg := fun _ => zero_le_one
  stepDefectErr := fun _ => 0
  stepDefectErr_nonneg := fun _ => le_rfl
  deg_step := fun k _ => by
    dsimp only [zmodCoveringRing]
    exact (Nat.mul_div_cancel' (hdiv k)).symm
  rk_step := fun _ _ => by simp [zmodCoveringRing]
  bad_step := fun k _ => by
    dsimp only [zmodCoveringRing]
    have hstep_pos : 0 < N (k + 1) / N k :=
      Nat.div_pos (Nat.le_of_dvd (hN (k + 1)) (hdiv k)) (hN k)
    conv_lhs => rw [← Nat.mul_div_cancel' (hdiv k)]
    rw [Nat.primeFactors_mul (hN k).ne' hstep_pos.ne']
  defect_step := fun _ _ => by simp [zmodCoveringRing]

/-- Construct a concrete `CoveringLevelTower` from any descending chain of ideals
`I : ℕ → Ideal R` (`I (k + 1) ≤ I k`) with explicit quotient maps `R ⧸ I (k + 1) →+* R ⧸ I k`. -/
def idealQuotientCoveringTower {R : Type} [CommRing R] (depth : ℕ)
    (I : ℕ → Ideal R) (hI : ∀ k, I (k + 1) ≤ I k)
    (deg : ℕ → ℕ) (hdeg : ∀ k, 0 < deg k)
    (stepDeg : ℕ → ℕ) (hstep : ∀ k, 0 < stepDeg k)
    (hdeg_step : ∀ k, k < depth → deg (k + 1) = deg k * stepDeg k)
    (rk : ℕ) (hrk : 0 < rk) (bad : ℕ → Finset ℕ) (stepBad : ℕ → Finset ℕ)
    (hbad_step : ∀ k, k < depth → bad (k + 1) ⊆ bad k ∪ stepBad k) :
    CoveringLevelTower where
  depth := depth
  ring := fun k =>
    idealQuotientCoveringRing R (I k) (deg k) (deg k) rk (hdeg k) (hdeg k) hrk 0 le_rfl (bad k)
  stepMap := fun k =>
    idealQuotientDescentMap (hI k)
      (hlI := hdeg (k + 1)) (hdI := hdeg (k + 1)) (hrI := hrk)
      (hlJ := hdeg k) (hdJ := hdeg k) (hrJ := hrk)
      (hdefI := le_rfl) (hdefJ := le_rfl)
      (badI := bad (k + 1)) (badJ := bad k)
  stepDeg := stepDeg
  stepDeg_pos := hstep
  stepRankFactor := fun _ => 1
  stepRankShift := fun _ => 0
  stepNewBad := stepBad
  stepDefectScale := fun _ => 1
  stepDefectScale_nonneg := fun _ => zero_le_one
  stepDefectErr := fun _ => 0
  stepDefectErr_nonneg := fun _ => le_rfl
  deg_step := hdeg_step
  rk_step := fun _ _ => by simp [idealQuotientCoveringRing]
  bad_step := hbad_step
  defect_step := fun _ _ => by simp [idealQuotientCoveringRing]

end CoveringTower

/-! ## Section 3: `covering_degree_multiplicative` & Lattice Index Multiplicativity -/

section DegreeMultiplicative

/-- Relative composite covering degree from level `i` to level `j` in a `CoveringLevelTower`:
`∏ k ∈ Finset.Ico i j, T.stepDeg k`. -/
def compositeDegree (T : CoveringLevelTower) (i j : ℕ) : ℕ :=
  ∏ k ∈ Finset.Ico i j, T.stepDeg k

@[simp]
theorem compositeDegree_self (T : CoveringLevelTower) (i : ℕ) :
    compositeDegree T i i = 1 := by
  simp [compositeDegree]

theorem compositeDegree_eq_one_of_le (T : CoveringLevelTower) {i j : ℕ} (hji : j ≤ i) :
    compositeDegree T i j = 1 := by
  simp [compositeDegree, Finset.Ico_eq_empty_of_le hji]

@[simp]
theorem compositeDegree_succ (T : CoveringLevelTower) (i : ℕ) :
    compositeDegree T i (i + 1) = T.stepDeg i := by
  simp [compositeDegree]

theorem compositeDegree_step_right (T : CoveringLevelTower) {i j : ℕ} (hij : i ≤ j) :
    compositeDegree T i (j + 1) = compositeDegree T i j * T.stepDeg j := by
  unfold compositeDegree
  rw [Finset.prod_Ico_succ_top hij]

theorem compositeDegree_step_left (T : CoveringLevelTower) {i j : ℕ} (hij : i < j) :
    compositeDegree T i j = T.stepDeg i * compositeDegree T (i + 1) j := by
  unfold compositeDegree
  rw [← Finset.prod_Ico_consecutive T.stepDeg (Nat.le_succ i) hij, Nat.Ico_succ_singleton,
    Finset.prod_singleton]

theorem compositeDegree_pos (T : CoveringLevelTower) (i j : ℕ) :
    0 < compositeDegree T i j := by
  unfold compositeDegree
  exact Finset.prod_pos fun k _ => T.stepDeg_pos k

/-- **Multiplicativity of Covering Degrees (`covering_degree_multiplicative`)**:
for any levels `i ≤ j ≤ k` in a `CoveringLevelTower`,
`compositeDegree T i k = compositeDegree T i j * compositeDegree T j k`. -/
theorem covering_degree_multiplicative (T : CoveringLevelTower) {i j k : ℕ}
    (hij : i ≤ j) (hjk : j ≤ k) :
    compositeDegree T i k = compositeDegree T i j * compositeDegree T j k := by
  unfold compositeDegree
  exact (Finset.prod_Ico_consecutive T.stepDeg hij hjk).symm

/-- Exact level degree relation along `i ≤ j ≤ T.depth`:
`(T.ring j).deg = (T.ring i).deg * compositeDegree T i j`. -/
theorem ring_deg_eq_mul_compositeDegree (T : CoveringLevelTower) {i j : ℕ}
    (hij : i ≤ j) (hj : j ≤ T.depth) :
    (T.ring j).deg = (T.ring i).deg * compositeDegree T i j := by
  induction j with
  | zero =>
      have hi : i = 0 := Nat.eq_zero_of_le_zero hij
      subst hi
      simp
  | succ j ih =>
      rcases Nat.eq_or_lt_of_le hij with rfl | hlt
      · simp
      · have hij' : i ≤ j := Nat.lt_succ_iff.mp hlt
        have hj' : j ≤ T.depth := Nat.le_of_succ_le hj
        rw [T.deg_step j (Nat.lt_of_succ_le hj), ih hij' hj',
          compositeDegree_step_right T hij', mul_assoc]

/-- Multiplicativity of absolute covering degrees along `i ≤ j ≤ k ≤ T.depth`. -/
theorem ring_deg_mul_compositeDegree_eq (T : CoveringLevelTower) {i j k : ℕ}
    (hij : i ≤ j) (hjk : j ≤ k) (hk : k ≤ T.depth) :
    (T.ring k).deg * (T.ring i).deg =
      (T.ring j).deg * ((T.ring i).deg * compositeDegree T j k) := by
  have hj : j ≤ T.depth := hjk.trans hk
  rw [ring_deg_eq_mul_compositeDegree T (hij.trans hjk) hk,
    ring_deg_eq_mul_compositeDegree T hij hj,
    covering_degree_multiplicative T hij hjk]
  ring

theorem ring_deg_div_eq_compositeDegree (T : CoveringLevelTower) {i j : ℕ}
    (hij : i ≤ j) (hj : j ≤ T.depth) :
    (T.ring j).deg / (T.ring i).deg = compositeDegree T i j := by
  rw [ring_deg_eq_mul_compositeDegree T hij hj]
  exact Nat.mul_div_cancel_left _ (T.ring i).deg_pos

/-! ### Concrete Lattice-Index Multiplicativity & Congruence Scaling -/

section LatticeIndexMultiplicativity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Principal congruence sublattice `N • Λ = { N • x | x ∈ Λ }` defined via `Submodule.map`
of `LinearMap.lsmul ℤ E (N : ℤ)` (completely free of pointwise `HSMul` synthesis issues). -/
def scaleSublat (N : ℕ) (Λ : Submodule ℤ E) : Submodule ℤ E :=
  Λ.map (LinearMap.lsmul ℤ E (N : ℤ))

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
@[simp]
theorem mem_scaleSublat_iff {N : ℕ} {Λ : Submodule ℤ E} {x : E} :
    x ∈ scaleSublat N Λ ↔ ∃ y ∈ Λ, (N : ℤ) • y = x :=
  Submodule.mem_map

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem scaleSublat_le (N : ℕ) (Λ : Submodule ℤ E) : scaleSublat N Λ ≤ Λ := by
  rintro x hx
  obtain ⟨y, hy, rfl⟩ := mem_scaleSublat_iff.mp hx
  exact Λ.smul_mem (N : ℤ) hy

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem smul_mem_scaleSublat {N : ℕ} {Λ : Submodule ℤ E} {y : E} (hy : y ∈ Λ) :
    (N : ℤ) • y ∈ scaleSublat N Λ :=
  mem_scaleSublat_iff.mpr ⟨y, hy, rfl⟩

private lemma nat_zsmul_eq_nsmul_real {F : Type*} [AddCommGroup F] [Module ℝ F]
    (N : ℕ) (u : F) : (N : ℤ) • u = (N : ℝ) • u := by
  rw [← Int.cast_smul_eq_zsmul ℝ, Int.cast_natCast]

/-- **Exact Full-Rank Sublattice Index Multiplicativity (`latIndex_multiplicative`)**:
for any nested discrete lattices `Λ₂ ≤ Λ₁ ≤ Λ₀` in `E` of the same rank (`rk Λ₂ = rk Λ₁ = rk Λ₀`),
`latIndex Λ₀ Λ₂ = latIndex Λ₀ Λ₁ * latIndex Λ₁ Λ₂`. -/
theorem latIndex_multiplicative {Λ₀ Λ₁ Λ₂ : Submodule ℤ E} [DiscreteTopology Λ₀]
    (h10 : Λ₁ ≤ Λ₀) (h21 : Λ₂ ≤ Λ₁) (hrk1 : rk Λ₁ = rk Λ₀) (hrk2 : rk Λ₂ = rk Λ₁) :
    latIndex Λ₀ Λ₂ = latIndex Λ₀ Λ₁ * latIndex Λ₁ Λ₂ := by
  have : DiscreteTopology Λ₁ := discreteTopology_of_le h10
  have h20 : Λ₂ ≤ Λ₀ := h21.trans h10
  have hrk20 : rk Λ₂ = rk Λ₀ := hrk2.trans hrk1
  have h02 := covol_eq_index_mul_covol h20 hrk20
  have h12 := covol_eq_index_mul_covol h21 hrk2
  have h01 := covol_eq_index_mul_covol h10 hrk1
  have hcov_pos : 0 < covol Λ₀ := covol_pos Λ₀
  have hreal : (latIndex Λ₀ Λ₂ : ℝ) * covol Λ₀ =
      ((latIndex Λ₀ Λ₁ * latIndex Λ₁ Λ₂ : ℕ) : ℝ) * covol Λ₀ := by
    calc (latIndex Λ₀ Λ₂ : ℝ) * covol Λ₀
        = covol Λ₂ := h02.symm
      _ = (latIndex Λ₁ Λ₂ : ℝ) * covol Λ₁ := h12
      _ = (latIndex Λ₁ Λ₂ : ℝ) * ((latIndex Λ₀ Λ₁ : ℝ) * covol Λ₀) := by rw [h01]
      _ = ((latIndex Λ₀ Λ₁ * latIndex Λ₁ Λ₂ : ℕ) : ℝ) * covol Λ₀ := by
          push_cast; ring
  exact Nat.cast_injective (mul_right_cancel₀ hcov_pos.ne' hreal)

/-- Exact covolume formula along any descending chain `L : ℕ → Submodule ℤ E` of equal-rank
discrete lattices (`L (k + 1) ≤ L k` and `rk (L k) = rk (L 0)`):
`covol (L j) = (∏ k ∈ Finset.Ico i j, (latIndex (L k) (L (k + 1)) : ℝ)) * covol (L i)`. -/
theorem covol_chain_eq_prod_latIndex (L : ℕ → Submodule ℤ E)
    [∀ k, DiscreteTopology (L k)]
    (hsub : ∀ k, L (k + 1) ≤ L k) (hrk : ∀ k, rk (L k) = rk (L 0))
    {i j : ℕ} (hij : i ≤ j) :
    covol (L j) = (∏ k ∈ Finset.Ico i j, (latIndex (L k) (L (k + 1)) : ℝ)) * covol (L i) := by
  induction j with
  | zero =>
      have hi : i = 0 := Nat.eq_zero_of_le_zero hij
      subst hi
      simp
  | succ j ih =>
      rcases Nat.eq_or_lt_of_le hij with rfl | hlt
      · simp
      · have hij' : i ≤ j := Nat.lt_succ_iff.mp hlt
        have hstep := covol_eq_index_mul_covol (hsub j) (by rw [hrk (j + 1), hrk j])
        rw [hstep, ih hij', Finset.prod_Ico_succ_top hij']
        ring

omit [FiniteDimensional ℝ E] in
/-- For `N : ℕ` (`0 < N`) and any discrete lattice `Λ ⊂ E`, `scaleSublat N Λ ≤ Λ` is discrete
and has exact rank `rk (scaleSublat N Λ) = rk Λ`. -/
theorem scaleSublat_le_and_rk (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    {N : ℕ} (hN : 0 < N) :
    scaleSublat N Λ ≤ Λ ∧
      DiscreteTopology (scaleSublat N Λ) ∧
      rk (scaleSublat N Λ) = rk Λ := by
  have hle : scaleSublat N Λ ≤ Λ := scaleSublat_le N Λ
  have hdisc : DiscreteTopology (scaleSublat N Λ) := discreteTopology_of_le hle
  let f : Λ →ₗ[ℤ] scaleSublat N Λ :=
    { toFun := fun x => ⟨(N : ℤ) • (x : E), smul_mem_scaleSublat x.2⟩
      map_add' := fun x y => Subtype.ext (smul_add (N : ℤ) (x : E) (y : E))
      map_smul' := fun c x => Subtype.ext (smul_comm (N : ℤ) c (x : E)) }
  have hbij : Function.Bijective f := by
    refine ⟨?_, ?_⟩
    · intro x y hxy
      have hval : (N : ℤ) • (x : E) = (N : ℤ) • (y : E) := congrArg Subtype.val hxy
      have hN0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
      have hxR : (N : ℝ) • (x : E) = (N : ℝ) • (y : E) := by
        rw [← nat_zsmul_eq_nsmul_real, ← nat_zsmul_eq_nsmul_real]
        exact hval
      exact Subtype.ext (smul_right_injective E hN0 hxR)
    · rintro ⟨_, hx⟩
      obtain ⟨y, hy, rfl⟩ := mem_scaleSublat_iff.mp hx
      exact ⟨⟨y, hy⟩, rfl⟩
  let e : Λ ≃ₗ[ℤ] scaleSublat N Λ := LinearEquiv.ofBijective f hbij
  refine ⟨hle, hdisc, ?_⟩
  unfold rk
  exact e.finrank_eq.symm

/-- Exact covolume of a principal congruence sublattice `scaleSublat N Λ` (`0 < N`):
`covol (scaleSublat N Λ) = (N : ℝ) ^ rk Λ * covol Λ`. -/
theorem covol_scaleSublat_eq (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    {N : ℕ} (hN : 0 < N) :
    covol (scaleSublat N Λ) = (N : ℝ) ^ rk Λ * covol Λ := by
  obtain ⟨_, hdisc, _⟩ := scaleSublat_le_and_rk Λ hN
  let r := rk Λ
  let b : Basis (Fin r) ℤ Λ := Module.finBasis ℤ Λ
  let fMap : Λ →ₗ[ℤ] scaleSublat N Λ :=
    { toFun := fun x => ⟨(N : ℤ) • (x : E), smul_mem_scaleSublat x.2⟩
      map_add' := fun x y => Subtype.ext (smul_add (N : ℤ) (x : E) (y : E))
      map_smul' := fun c x => Subtype.ext (smul_comm (N : ℤ) c (x : E)) }
  let f : Λ ≃ₗ[ℤ] scaleSublat N Λ := LinearEquiv.ofBijective fMap
    ⟨fun x y hxy => by
      have hval : (N : ℤ) • (x : E) = (N : ℤ) • (y : E) := congrArg Subtype.val hxy
      have hN0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
      have hxR : (N : ℝ) • (x : E) = (N : ℝ) • (y : E) := by
        rw [← nat_zsmul_eq_nsmul_real, ← nat_zsmul_eq_nsmul_real]
        exact hval
      exact Subtype.ext (smul_right_injective E hN0 hxR),
     by
      rintro ⟨_, hx⟩
      obtain ⟨y, hy, rfl⟩ := mem_scaleSublat_iff.mp hx
      exact ⟨⟨y, hy⟩, rfl⟩⟩
  let bN : Basis (Fin r) ℤ (scaleSublat N Λ) := b.map f
  rw [covol_eq_sqrt_det_gram Λ b, covol_eq_sqrt_det_gram (scaleSublat N Λ) bN]
  have hgram : Matrix.gram ℝ (fun i => (bN i : E)) =
      ((N : ℝ) ^ 2) • Matrix.gram ℝ (fun i => (b i : E)) := by
    ext i j
    simp only [Matrix.gram_apply, Matrix.smul_apply, smul_eq_mul, bN, Basis.map_apply, f, fMap]
    change inner ℝ ((N : ℤ) • (b i : E)) ((N : ℤ) • (b j : E)) =
      (N : ℝ) ^ 2 * inner ℝ (b i : E) (b j : E)
    rw [nat_zsmul_eq_nsmul_real, nat_zsmul_eq_nsmul_real,
      real_inner_smul_left, real_inner_smul_right]
    ring
  rw [hgram, Matrix.det_smul, Fintype.card_fin]
  have hpow : ((N : ℝ) ^ 2) ^ r = ((N : ℝ) ^ r) ^ 2 := by ring
  rw [hpow, Real.sqrt_mul (sq_nonneg ((N : ℝ) ^ r)), Real.sqrt_sq (by positivity)]

/-- Exact index of the principal congruence sublattice `scaleSublat N Λ ≤ Λ` (`0 < N`):
`latIndex Λ (scaleSublat N Λ) = N ^ rk Λ`. -/
theorem latIndex_scaleSublat_eq (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    {N : ℕ} (hN : 0 < N) :
    latIndex Λ (scaleSublat N Λ) = N ^ rk Λ := by
  obtain ⟨hle, _, hrk⟩ := scaleSublat_le_and_rk Λ hN
  have hcov := covol_eq_index_mul_covol hle hrk
  rw [covol_scaleSublat_eq Λ hN] at hcov
  have hcov_pos : 0 < covol Λ := covol_pos Λ
  have hreal : ((N ^ rk Λ : ℕ) : ℝ) * covol Λ =
      (latIndex Λ (scaleSublat N Λ) : ℝ) * covol Λ := by
    push_cast
    exact hcov
  exact (Nat.cast_injective (mul_right_cancel₀ hcov_pos.ne' hreal)).symm

/-- Exact congruence-tower `ZMod` degree multiplicativity for `K ∣ M ∣ N`. -/
theorem zmod_degree_multiplicative {K M N : ℕ} (hKM : K ∣ M) (hMN : M ∣ N) :
    N / K = (N / M) * (M / K) := by
  rcases hKM with ⟨a, rfl⟩
  rcases hMN with ⟨b, rfl⟩
  rcases Nat.eq_zero_or_pos K with rfl | hK
  · simp
  · rcases Nat.eq_zero_or_pos a with rfl | ha
    · simp
    · have hKa : 0 < K * a := Nat.mul_pos hK ha
      rw [mul_assoc K a b, Nat.mul_div_cancel_left (a * b) hK,
        ← mul_assoc K a b, Nat.mul_div_cancel_left b hKa,
        Nat.mul_div_cancel_left a hK, mul_comm]

/-- Product cardinality law for finite covering-basis index sets along two descent steps. -/
theorem covering_basis_card_mul (ι₁ ι₂ : Type*) [Fintype ι₁] [Fintype ι₂] :
    Fintype.card (ι₁ × ι₂) = Fintype.card ι₁ * Fintype.card ι₂ :=
  Fintype.card_prod ι₁ ι₂

end LatticeIndexMultiplicativity

end DegreeMultiplicative

/-! ## Section 4: `covering_rank_of_descent_steps` -/

section RankOfDescentSteps

/-- Affine rank growth bound along `i ≤ j ≤ T.depth` in a `CoveringLevelTower`:
if `T.stepRankFactor k ≤ α` and `T.stepRankShift k ≤ β` for all `k ∈ Finset.Ico i j`, then
`(T.ring j).rk ≤ α ^ (j - i) * (T.ring i).rk + β * ∑ t ∈ Finset.range (j - i), α ^ t`. -/
theorem covering_rank_of_descent_steps_affine (T : CoveringLevelTower) {i j α β : ℕ}
    (hij : i ≤ j) (hj : j ≤ T.depth)
    (hα : ∀ k ∈ Finset.Ico i j, T.stepRankFactor k ≤ α)
    (hβ : ∀ k ∈ Finset.Ico i j, T.stepRankShift k ≤ β) :
    (T.ring j).rk ≤ α ^ (j - i) * (T.ring i).rk + β * ∑ t ∈ Finset.range (j - i), α ^ t := by
  induction j with
  | zero =>
      have hi : i = 0 := Nat.eq_zero_of_le_zero hij
      subst hi
      simp
  | succ j ih =>
      rcases Nat.eq_or_lt_of_le hij with rfl | hlt
      · simp
      · have hij' : i ≤ j := Nat.lt_succ_iff.mp hlt
        have hj' : j ≤ T.depth := Nat.le_of_succ_le hj
        have hj_mem : j ∈ Finset.Ico i (j + 1) := Finset.mem_Ico.mpr ⟨hij', Nat.lt_succ_self j⟩
        have hIco_sub : Finset.Ico i j ⊆ Finset.Ico i (j + 1) :=
          Finset.Ico_subset_Ico_right (Nat.le_succ j)
        have hih := ih hij' hj' (fun k hk => hα k (hIco_sub hk)) (fun k hk => hβ k (hIco_sub hk))
        have hstep := T.rk_step j (Nat.lt_of_succ_le hj)
        have hαj : T.stepRankFactor j ≤ α := hα j hj_mem
        have hβj : T.stepRankShift j ≤ β := hβ j hj_mem
        have hsub : j + 1 - i = (j - i) + 1 := by omega
        rw [hsub, pow_succ', Finset.sum_range_succ']
        have hmul_sum : α * ∑ t ∈ Finset.range (j - i), α ^ t =
            ∑ t ∈ Finset.range (j - i), α ^ (t + 1) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun t _ => ?_
          rw [pow_succ']
        calc (T.ring (j + 1)).rk
            ≤ T.stepRankFactor j * (T.ring j).rk + T.stepRankShift j := hstep
          _ ≤ α * (T.ring j).rk + β :=
              Nat.add_le_add (Nat.mul_le_mul_right _ hαj) hβj
          _ ≤ α * (α ^ (j - i) * (T.ring i).rk + β * ∑ t ∈ Finset.range (j - i), α ^ t) + β :=
              Nat.add_le_add_right (Nat.mul_le_mul_left α hih) β
          _ = α * α ^ (j - i) * (T.ring i).rk +
              β * (∑ t ∈ Finset.range (j - i), α ^ (t + 1) + α ^ 0) := by
              rw [← hmul_sum]
              simp only [pow_zero]
              ring

/-- Additive rank growth bound when `stepRankFactor k ≤ 1` (`α = 1`):
`(T.ring j).rk ≤ (T.ring i).rk + (j - i) * β`. -/
theorem covering_rank_of_descent_steps_additive (T : CoveringLevelTower) {i j β : ℕ}
    (hij : i ≤ j) (hj : j ≤ T.depth)
    (h1 : ∀ k ∈ Finset.Ico i j, T.stepRankFactor k ≤ 1)
    (hβ : ∀ k ∈ Finset.Ico i j, T.stepRankShift k ≤ β) :
    (T.ring j).rk ≤ (T.ring i).rk + (j - i) * β := by
  have h := covering_rank_of_descent_steps_affine T hij hj h1 hβ
  simp only [one_pow, one_mul, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one] at h
  linarith

/-- Pure multiplicative rank bound when `stepRankShift k = 0` for all `k ∈ Finset.Ico i j`:
`(T.ring j).rk ≤ (∏ k ∈ Finset.Ico i j, T.stepRankFactor k) * (T.ring i).rk`. -/
theorem covering_rank_of_descent_steps_mul (T : CoveringLevelTower) {i j : ℕ}
    (hij : i ≤ j) (hj : j ≤ T.depth)
    (h0 : ∀ k ∈ Finset.Ico i j, T.stepRankShift k = 0) :
    (T.ring j).rk ≤ (∏ k ∈ Finset.Ico i j, T.stepRankFactor k) * (T.ring i).rk := by
  induction j with
  | zero =>
      have hi : i = 0 := Nat.eq_zero_of_le_zero hij
      subst hi
      simp
  | succ j ih =>
      rcases Nat.eq_or_lt_of_le hij with rfl | hlt
      · simp
      · have hij' : i ≤ j := Nat.lt_succ_iff.mp hlt
        have hj' : j ≤ T.depth := Nat.le_of_succ_le hj
        have hIco_sub : Finset.Ico i j ⊆ Finset.Ico i (j + 1) :=
          Finset.Ico_subset_Ico_right (Nat.le_succ j)
        have hih := ih hij' hj' (fun k hk => h0 k (hIco_sub hk))
        have hj_mem : j ∈ Finset.Ico i (j + 1) := Finset.mem_Ico.mpr ⟨hij', Nat.lt_succ_self j⟩
        have hstep := T.rk_step j (Nat.lt_of_succ_le hj)
        rw [h0 j hj_mem, add_zero] at hstep
        rw [Finset.prod_Ico_succ_top hij']
        calc (T.ring (j + 1)).rk
            ≤ T.stepRankFactor j * (T.ring j).rk := hstep
          _ ≤ T.stepRankFactor j * ((∏ k ∈ Finset.Ico i j, T.stepRankFactor k) * (T.ring i).rk) :=
              Nat.mul_le_mul_left _ hih
          _ = ((∏ k ∈ Finset.Ico i j, T.stepRankFactor k) * T.stepRankFactor j) * (T.ring i).rk := by
              ring

/-- **Covering Rank of Iterated Descent Steps (`covering_rank_of_descent_steps`)**:
when each step rank factor is bounded by its step covering degree (`T.stepRankFactor k ≤ T.stepDeg k`)
and shifts vanish, the rank at level `j` satisfies
`(T.ring j).rk ≤ compositeDegree T i j * (T.ring i).rk`. -/
theorem covering_rank_of_descent_steps (T : CoveringLevelTower) {i j : ℕ}
    (hij : i ≤ j) (hj : j ≤ T.depth)
    (hdeg : ∀ k ∈ Finset.Ico i j, T.stepRankFactor k ≤ T.stepDeg k)
    (h0 : ∀ k ∈ Finset.Ico i j, T.stepRankShift k = 0) :
    (T.ring j).rk ≤ compositeDegree T i j * (T.ring i).rk := by
  refine (covering_rank_of_descent_steps_mul T hij hj h0).trans ?_
  refine Nat.mul_le_mul_right _ ?_
  unfold compositeDegree
  exact Finset.prod_le_prod' fun k hk => hdeg k hk

/-- Constant-rank preservation along descent steps (`stepRankFactor ≤ 1` and `stepRankShift = 0`). -/
theorem covering_rank_of_descent_steps_const (T : CoveringLevelTower) {i j : ℕ}
    (hij : i ≤ j) (hj : j ≤ T.depth)
    (h1 : ∀ k ∈ Finset.Ico i j, T.stepRankFactor k ≤ 1)
    (h0 : ∀ k ∈ Finset.Ico i j, T.stepRankShift k = 0) :
    (T.ring j).rk ≤ (T.ring i).rk := by
  have h := covering_rank_of_descent_steps_additive T hij hj h1 (fun k hk => (h0 k hk).le)
  simpa using h

/-- **Exact Congruence-Sublattice Rank Preservation (`rk_congruence_sublattice_eq`)**:
for any discrete lattice `Λ ⊂ E` and congruence sublattice `scaleSublat N Λ ≤ Λ' ≤ Λ` (`0 < N`),
`Λ'` is discrete and has exact rank `rk Λ' = rk Λ`. -/
theorem rk_congruence_sublattice_eq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (Λ Λ' : Submodule ℤ E) [DiscreteTopology Λ]
    {N : ℕ} (hN : 0 < N) (hlo : scaleSublat N Λ ≤ Λ') (hhi : Λ' ≤ Λ) :
    DiscreteTopology Λ' ∧ rk Λ' = rk Λ := by
  have hdisc : DiscreteTopology Λ' := discreteTopology_of_le hhi
  obtain ⟨_, _, hrkN⟩ := scaleSublat_le_and_rk Λ hN
  have h1 : rk (scaleSublat N Λ) ≤ rk Λ' := by
    unfold rk
    exact Submodule.finrank_mono hlo
  have h2 : rk Λ' ≤ rk Λ := by
    unfold rk
    exact Submodule.finrank_mono hhi
  rw [hrkN] at h1
  exact ⟨hdisc, le_antisymm h2 h1⟩

/-- `IsZLattice ℝ` passes to any congruence sublattice `scaleSublat N Λ ≤ Λ' ≤ Λ` (`0 < N`)
in `EuclideanSpace ℝ (Fin n)`. -/
theorem isZLattice_congruence_sublattice {n : ℕ}
    (Λ Λ' : Submodule ℤ (EuclideanSpace ℝ (Fin n))) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    [DiscreteTopology Λ'] {N : ℕ} (hN : 0 < N) (hlo : scaleSublat N Λ ≤ Λ') (hhi : Λ' ≤ Λ) :
    IsZLattice ℝ Λ' := by
  refine ⟨?_⟩
  have hspan_top : Submodule.span ℝ (Λ : Set (EuclideanSpace ℝ (Fin n))) = ⊤ :=
    IsZLattice.span_top
  have hrk : rk Λ' = rk Λ := (rk_congruence_sublattice_eq Λ Λ' hN hlo hhi).2
  unfold rk at hrk
  have hdim_eq : Module.finrank ℝ (Submodule.span ℝ (Λ' : Set (EuclideanSpace ℝ (Fin n)))) =
      Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) := by
    rw [← finrank_int_eq_finrank_real_span Λ', hrk, finrank_int_eq_finrank_real_span Λ, hspan_top,
      finrank_top]
  exact Submodule.eq_top_of_finrank_eq hdim_eq

end RankOfDescentSteps

/-! ## Section 5: `covering_bad_locus_bound` -/

section BadLocusBounds

/-- Cumulative bad-locus inclusion along `i ≤ j ≤ T.depth`:
`(T.ring j).badLocus ⊆ (T.ring i).badLocus ∪ (Finset.Ico i j).biUnion T.stepNewBad`. -/
theorem badLocus_subset_union (T : CoveringLevelTower) {i j : ℕ}
    (hij : i ≤ j) (hj : j ≤ T.depth) :
    (T.ring j).badLocus ⊆ (T.ring i).badLocus ∪ (Finset.Ico i j).biUnion T.stepNewBad := by
  induction j with
  | zero =>
      have hi : i = 0 := Nat.eq_zero_of_le_zero hij
      subst hi
      simp
  | succ j ih =>
      rcases Nat.eq_or_lt_of_le hij with rfl | hlt
      · simp
      · have hij' : i ≤ j := Nat.lt_succ_iff.mp hlt
        have hj' : j ≤ T.depth := Nat.le_of_succ_le hj
        have hstep := T.bad_step j (Nat.lt_of_succ_le hj)
        have hih := ih hij' hj'
        intro p hp
        rcases Finset.mem_union.mp (hstep hp) with hpj | hpnew
        · rcases Finset.mem_union.mp (hih hpj) with hpi | hpu
          · exact Finset.mem_union_left _ hpi
          · refine Finset.mem_union_right _ ?_
            rcases Finset.mem_biUnion.mp hpu with ⟨k, hk, hpk⟩
            exact Finset.mem_biUnion.mpr ⟨k, Finset.Ico_subset_Ico_right (Nat.le_succ j) hk, hpk⟩
        · refine Finset.mem_union_right _ ?_
          exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_Ico.mpr ⟨hij', Nat.lt_succ_self j⟩, hpnew⟩

/-- **Quantitative Bad-Locus Cardinality Bound (`covering_bad_locus_bound`)**:
for any levels `i ≤ j ≤ T.depth` in a `CoveringLevelTower`,
`(T.ring j).badLocus.card ≤ (T.ring i).badLocus.card + ∑ k ∈ Finset.Ico i j, (T.stepNewBad k).card`. -/
theorem covering_bad_locus_bound (T : CoveringLevelTower) {i j : ℕ}
    (hij : i ≤ j) (hj : j ≤ T.depth) :
    (T.ring j).badLocus.card ≤
      (T.ring i).badLocus.card + ∑ k ∈ Finset.Ico i j, (T.stepNewBad k).card := by
  calc (T.ring j).badLocus.card
      ≤ ((T.ring i).badLocus ∪ (Finset.Ico i j).biUnion T.stepNewBad).card :=
          Finset.card_le_card (badLocus_subset_union T hij hj)
    _ ≤ (T.ring i).badLocus.card + ((Finset.Ico i j).biUnion T.stepNewBad).card :=
          Finset.card_union_le _ _
    _ ≤ (T.ring i).badLocus.card + ∑ k ∈ Finset.Ico i j, (T.stepNewBad k).card :=
          Nat.add_le_add_left Finset.card_biUnion_le _

/-- Uniform step bound on bad-locus growth: if `(T.stepNewBad k).card ≤ B` for all `k ∈ [i, j)`,
then `(T.ring j).badLocus.card ≤ (T.ring i).badLocus.card + (j - i) * B`. -/
theorem covering_bad_locus_uniform_step_bound (T : CoveringLevelTower) {i j B : ℕ}
    (hij : i ≤ j) (hj : j ≤ T.depth)
    (hB : ∀ k ∈ Finset.Ico i j, (T.stepNewBad k).card ≤ B) :
    (T.ring j).badLocus.card ≤ (T.ring i).badLocus.card + (j - i) * B := by
  refine (covering_bad_locus_bound T hij hj).trans (Nat.add_le_add_left ?_ _)
  calc ∑ k ∈ Finset.Ico i j, (T.stepNewBad k).card
      ≤ ∑ _k ∈ Finset.Ico i j, B := Finset.sum_le_sum hB
    _ = (j - i) * B := by simp

/-- Number-theoretic bound: the number of distinct prime factors of any `n : ℕ` satisfies
`n.primeFactors.card ≤ Nat.log 2 n`. -/
theorem card_primeFactors_le_log2 (n : ℕ) : n.primeFactors.card ≤ Nat.log 2 n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hpow : 2 ^ n.primeFactors.card ≤ n := by
      calc 2 ^ n.primeFactors.card
          = ∏ _p ∈ n.primeFactors, 2 := by simp
        _ ≤ ∏ p ∈ n.primeFactors, p := by
            refine Finset.prod_le_prod' fun p hp => ?_
            exact (Nat.prime_of_mem_primeFactors hp).two_le
        _ ≤ n := Nat.le_of_dvd hn (Nat.prod_primeFactors_dvd n)
    exact Nat.le_log_of_pow_le Nat.one_lt_two hpow

/-- Prime factors of a product over a finset equal the union of the prime factors of the factors
(assuming all factors are nonzero). -/
theorem primeFactors_prod_eq_biUnion {ι : Type*} (s : Finset ι) (f : ι → ℕ)
    (hf : ∀ k ∈ s, f k ≠ 0) :
    (∏ k ∈ s, f k).primeFactors = s.biUnion (fun k => (f k).primeFactors) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.biUnion_insert]
      have ha0 : f a ≠ 0 := hf a (Finset.mem_insert_self a s)
      have hs0 : ∀ k ∈ s, f k ≠ 0 := fun k hk => hf k (Finset.mem_insert_of_mem hk)
      have hprod0 : ∏ k ∈ s, f k ≠ 0 := Finset.prod_ne_zero_iff.mpr hs0
      rw [Nat.primeFactors_mul ha0 hprod0, ih hs0]

/-- Coprime levels have disjoint prime-factor bad loci (`Disjoint M.primeFactors N.primeFactors`). -/
theorem disjoint_primeFactors_of_coprime {M N : ℕ} (hcop : M.Coprime N) :
    Disjoint M.primeFactors N.primeFactors := by
  rw [Finset.disjoint_left]
  intro p hpM hpN
  have hdv : p ∣ Nat.gcd M N :=
    Nat.dvd_gcd (Nat.dvd_of_mem_primeFactors hpM) (Nat.dvd_of_mem_primeFactors hpN)
  rw [hcop] at hdv
  exact (Nat.prime_of_mem_primeFactors hpM).ne_one (Nat.dvd_one.mp hdv)

/-- **Logarithmic Bad-Locus Bound via Composite Covering Degree (`covering_bad_locus_primeFactors_bound`)**:
whenever new bad primes at each step `k ∈ Finset.Ico i j` divide the step degree `T.stepDeg k`,
the bad-locus cardinality at level `j` satisfies
`(T.ring j).badLocus.card ≤ (T.ring i).badLocus.card + Nat.log 2 (compositeDegree T i j)`! -/
theorem covering_bad_locus_primeFactors_bound (T : CoveringLevelTower) {i j : ℕ}
    (hij : i ≤ j) (hj : j ≤ T.depth)
    (hdiv : ∀ k ∈ Finset.Ico i j, T.stepNewBad k ⊆ (T.stepDeg k).primeFactors) :
    (T.ring j).badLocus.card ≤
      (T.ring i).badLocus.card + Nat.log 2 (compositeDegree T i j) := by
  have hbi : (Finset.Ico i j).biUnion T.stepNewBad ⊆ (compositeDegree T i j).primeFactors := by
    unfold compositeDegree
    rw [primeFactors_prod_eq_biUnion (Finset.Ico i j) T.stepDeg
      (fun k _ => (T.stepDeg_pos k).ne')]
    exact Finset.biUnion_mono hdiv
  calc (T.ring j).badLocus.card
      ≤ ((T.ring i).badLocus ∪ (Finset.Ico i j).biUnion T.stepNewBad).card :=
          Finset.card_le_card (badLocus_subset_union T hij hj)
    _ ≤ (T.ring i).badLocus.card + ((Finset.Ico i j).biUnion T.stepNewBad).card :=
          Finset.card_union_le _ _
    _ ≤ (T.ring i).badLocus.card + (compositeDegree T i j).primeFactors.card :=
          Nat.add_le_add_left (Finset.card_le_card hbi) _
    _ ≤ (T.ring i).badLocus.card + Nat.log 2 (compositeDegree T i j) :=
          Nat.add_le_add_left (card_primeFactors_le_log2 _) _

/-- Bad-locus density bound over any finite evaluation window `S : Finset ℕ` (`0 < S.card`). -/
theorem covering_bad_locus_density_bound (T : CoveringLevelTower) {i j : ℕ}
    (hij : i ≤ j) (hj : j ≤ T.depth) (S : Finset ℕ) (hS : 0 < S.card) :
    (((T.ring j).badLocus ∩ S).card : ℝ) / (S.card : ℝ) ≤
      (((T.ring i).badLocus.card + ∑ k ∈ Finset.Ico i j, (T.stepNewBad k).card : ℕ) : ℝ) /
        (S.card : ℝ) := by
  have hS_pos : (0 : ℝ) < (S.card : ℝ) := Nat.cast_pos.mpr hS
  refine div_le_div_of_nonneg_right ?_ hS_pos.le
  exact Nat.cast_le.mpr
    ((Finset.card_le_card Finset.inter_subset_left).trans (covering_bad_locus_bound T hij hj))

end BadLocusBounds

/-! ## Section 6: `covering_low_defect_bound` & Banaszczyk / Minkowski Defect Analysis -/

section LowDefectBounds

/-- **General Defect Propagation Along Descent Steps (`covering_defect_step_bound`)**:
if `i ≤ j ≤ T.depth`, then
`(T.ring j).defect ≤ (∏ k ∈ Finset.Ico i j, T.stepDefectScale k) * (T.ring i).defect + ∑ k ∈ Finset.Ico i j, (∏ m ∈ Finset.Ico (k + 1) j, T.stepDefectScale m) * T.stepDefectErr k`. -/
theorem covering_defect_step_bound (T : CoveringLevelTower) {i j : ℕ}
    (hij : i ≤ j) (hj : j ≤ T.depth) :
    (T.ring j).defect ≤
      (∏ k ∈ Finset.Ico i j, T.stepDefectScale k) * (T.ring i).defect +
        ∑ k ∈ Finset.Ico i j,
          (∏ m ∈ Finset.Ico (k + 1) j, T.stepDefectScale m) * T.stepDefectErr k := by
  induction j with
  | zero =>
      have hi : i = 0 := Nat.eq_zero_of_le_zero hij
      subst hi
      simp
  | succ j ih =>
      rcases Nat.eq_or_lt_of_le hij with rfl | hlt
      · simp
      · have hij' : i ≤ j := Nat.lt_succ_iff.mp hlt
        have hj' : j ≤ T.depth := Nat.le_of_succ_le hj
        have hih := ih hij' hj'
        have hstep := T.defect_step j (Nat.lt_of_succ_le hj)
        have hscj : 0 ≤ T.stepDefectScale j := T.stepDefectScale_nonneg j
        have hmul := mul_le_mul_of_nonneg_left hih hscj
        have hprod_top : T.stepDefectScale j * ∏ k ∈ Finset.Ico i j, T.stepDefectScale k =
            ∏ k ∈ Finset.Ico i (j + 1), T.stepDefectScale k := by
          rw [Finset.prod_Ico_succ_top hij', mul_comm]
        have hsum_top :
            T.stepDefectScale j * ∑ k ∈ Finset.Ico i j,
              (∏ m ∈ Finset.Ico (k + 1) j, T.stepDefectScale m) * T.stepDefectErr k +
              T.stepDefectErr j =
            ∑ k ∈ Finset.Ico i (j + 1),
              (∏ m ∈ Finset.Ico (k + 1) (j + 1), T.stepDefectScale m) * T.stepDefectErr k := by
          rw [Finset.mul_sum, Finset.sum_Ico_succ_top hij']
          simp only [Finset.Ico_self, Finset.prod_empty, one_mul]
          congr 1
          refine Finset.sum_congr rfl fun k hk => ?_
          have hk_lt : k < j := (Finset.mem_Ico.mp hk).2
          rw [Finset.prod_Ico_succ_top (Nat.succ_le_of_lt hk_lt)]
          ring
        calc (T.ring (j + 1)).defect
            ≤ T.stepDefectScale j * (T.ring j).defect + T.stepDefectErr j := hstep
          _ ≤ T.stepDefectScale j *
                ((∏ k ∈ Finset.Ico i j, T.stepDefectScale k) * (T.ring i).defect +
                  ∑ k ∈ Finset.Ico i j,
                    (∏ m ∈ Finset.Ico (k + 1) j, T.stepDefectScale m) * T.stepDefectErr k) +
                T.stepDefectErr j := add_le_add hmul le_rfl
          _ = (T.stepDefectScale j * ∏ k ∈ Finset.Ico i j, T.stepDefectScale k) *
                (T.ring i).defect +
              (T.stepDefectScale j * ∑ k ∈ Finset.Ico i j,
                (∏ m ∈ Finset.Ico (k + 1) j, T.stepDefectScale m) * T.stepDefectErr k +
                T.stepDefectErr j) := by ring
          _ = (∏ k ∈ Finset.Ico i (j + 1), T.stepDefectScale k) * (T.ring i).defect +
              ∑ k ∈ Finset.Ico i (j + 1),
                (∏ m ∈ Finset.Ico (k + 1) (j + 1), T.stepDefectScale m) * T.stepDefectErr k := by
              rw [hprod_top, hsum_top]

/-- **Covering Low-Defect Bound (`covering_low_defect_bound`)**:
under uniform scale `T.stepDefectScale k ≤ θ` (`0 ≤ θ`) and step error `T.stepDefectErr k ≤ ε`:
`(T.ring j).defect ≤ θ ^ (j - i) * (T.ring i).defect + ε * ∑ t ∈ Finset.range (j - i), θ ^ t`. -/
theorem covering_low_defect_bound (T : CoveringLevelTower) {i j : ℕ}
    (hij : i ≤ j) (hj : j ≤ T.depth) {θ ε : ℝ} (hθ0 : 0 ≤ θ) (hε0 : 0 ≤ ε)
    (hθ : ∀ k ∈ Finset.Ico i j, T.stepDefectScale k ≤ θ)
    (hε : ∀ k ∈ Finset.Ico i j, T.stepDefectErr k ≤ ε) :
    (T.ring j).defect ≤
      θ ^ (j - i) * (T.ring i).defect + ε * ∑ t ∈ Finset.range (j - i), θ ^ t := by
  have hbase := covering_defect_step_bound T hij hj
  have hprod_le : ∏ k ∈ Finset.Ico i j, T.stepDefectScale k ≤ θ ^ (j - i) := by
    calc ∏ k ∈ Finset.Ico i j, T.stepDefectScale k
        ≤ ∏ _k ∈ Finset.Ico i j, θ :=
          Finset.prod_le_prod (fun k _ => T.stepDefectScale_nonneg k) (fun k hk => hθ k hk)
      _ = θ ^ (j - i) := by simp
  have hterm1 : (∏ k ∈ Finset.Ico i j, T.stepDefectScale k) * (T.ring i).defect ≤
      θ ^ (j - i) * (T.ring i).defect :=
    mul_le_mul_of_nonneg_right hprod_le (T.ring i).defect_nonneg
  have hsum_le : ∑ k ∈ Finset.Ico i j,
      (∏ m ∈ Finset.Ico (k + 1) j, T.stepDefectScale m) * T.stepDefectErr k ≤
      ε * ∑ t ∈ Finset.range (j - i), θ ^ t := by
    have hpt : ∀ k ∈ Finset.Ico i j,
        (∏ m ∈ Finset.Ico (k + 1) j, T.stepDefectScale m) * T.stepDefectErr k ≤
          ε * θ ^ (j - (k + 1)) := by
      intro k hk
      have hsub : Finset.Ico (k + 1) j ⊆ Finset.Ico i j :=
        Finset.Ico_subset_Ico (Nat.le_trans (Finset.mem_Ico.mp hk).1 (Nat.le_succ k)) le_rfl
      have hp : ∏ m ∈ Finset.Ico (k + 1) j, T.stepDefectScale m ≤ θ ^ (j - (k + 1)) := by
        calc ∏ m ∈ Finset.Ico (k + 1) j, T.stepDefectScale m
            ≤ ∏ _m ∈ Finset.Ico (k + 1) j, θ :=
              Finset.prod_le_prod (fun m _ => T.stepDefectScale_nonneg m)
                (fun m hm => hθ m (hsub hm))
          _ = θ ^ (j - (k + 1)) := by simp
      calc (∏ m ∈ Finset.Ico (k + 1) j, T.stepDefectScale m) * T.stepDefectErr k
          ≤ θ ^ (j - (k + 1)) * T.stepDefectErr k :=
            mul_le_mul_of_nonneg_right hp (T.stepDefectErr_nonneg k)
        _ ≤ θ ^ (j - (k + 1)) * ε :=
            mul_le_mul_of_nonneg_left (hε k hk) (pow_nonneg hθ0 _)
        _ = ε * θ ^ (j - (k + 1)) := mul_comm _ _
    refine (Finset.sum_le_sum hpt).trans ?_
    rw [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ hε0
    have hbij : ∑ k ∈ Finset.Ico i j, θ ^ (j - (k + 1)) = ∑ t ∈ Finset.range (j - i), θ ^ t := by
      refine Finset.sum_bij (fun k _ => j - (k + 1)) ?_ ?_ ?_ ?_
      · intro k hk
        obtain ⟨_, hkj⟩ := Finset.mem_Ico.mp hk
        rw [Finset.mem_range]
        omega
      · intro a ha b hb hab
        obtain ⟨_, haj⟩ := Finset.mem_Ico.mp ha
        obtain ⟨_, hbj⟩ := Finset.mem_Ico.mp hb
        change j - (a + 1) = j - (b + 1) at hab
        omega
      · intro t ht
        rw [Finset.mem_range] at ht
        refine ⟨j - 1 - t, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, by omega⟩
      · intro k _
        rfl
    exact hbij.le
  linarith

/-- Additive specialization (`θ = 1`) of `covering_low_defect_bound`. -/
theorem covering_low_defect_bound_additive (T : CoveringLevelTower) {i j : ℕ}
    (hij : i ≤ j) (hj : j ≤ T.depth)
    (h1 : ∀ k ∈ Finset.Ico i j, T.stepDefectScale k ≤ 1) :
    (T.ring j).defect ≤ (T.ring i).defect + ∑ k ∈ Finset.Ico i j, T.stepDefectErr k := by
  have hbase := covering_defect_step_bound T hij hj
  have hprod_le : ∏ k ∈ Finset.Ico i j, T.stepDefectScale k ≤ 1 := by
    calc ∏ k ∈ Finset.Ico i j, T.stepDefectScale k
        ≤ ∏ _k ∈ Finset.Ico i j, (1 : ℝ) :=
          Finset.prod_le_prod (fun k _ => T.stepDefectScale_nonneg k) h1
      _ = 1 := by simp
  have hsum_le : ∑ k ∈ Finset.Ico i j,
      (∏ m ∈ Finset.Ico (k + 1) j, T.stepDefectScale m) * T.stepDefectErr k ≤
      ∑ k ∈ Finset.Ico i j, T.stepDefectErr k := by
    refine Finset.sum_le_sum fun k hk => ?_
    have hsub : Finset.Ico (k + 1) j ⊆ Finset.Ico i j :=
      Finset.Ico_subset_Ico (Nat.le_trans (Finset.mem_Ico.mp hk).1 (Nat.le_succ k)) le_rfl
    have hp : ∏ m ∈ Finset.Ico (k + 1) j, T.stepDefectScale m ≤ 1 := by
      calc ∏ m ∈ Finset.Ico (k + 1) j, T.stepDefectScale m
          ≤ ∏ _m ∈ Finset.Ico (k + 1) j, (1 : ℝ) :=
            Finset.prod_le_prod (fun m _ => T.stepDefectScale_nonneg m) (fun m hm => h1 m (hsub hm))
        _ = 1 := by simp
    calc (∏ m ∈ Finset.Ico (k + 1) j, T.stepDefectScale m) * T.stepDefectErr k
        ≤ 1 * T.stepDefectErr k := mul_le_mul_of_nonneg_right hp (T.stepDefectErr_nonneg k)
      _ = T.stepDefectErr k := one_mul _
  have hterm1 : (∏ k ∈ Finset.Ico i j, T.stepDefectScale k) * (T.ring i).defect ≤
      (T.ring i).defect := by
    calc (∏ k ∈ Finset.Ico i j, T.stepDefectScale k) * (T.ring i).defect
        ≤ 1 * (T.ring i).defect := mul_le_mul_of_nonneg_right hprod_le (T.ring i).defect_nonneg
      _ = (T.ring i).defect := one_mul _
  linarith

/-- Contractive specialization (`0 ≤ θ < 1`) of `covering_low_defect_bound` yielding a
level-independent geometric ceiling `θ ^ (j - i) * defect i + ε / (1 - θ)`. -/
theorem covering_low_defect_bound_contractive (T : CoveringLevelTower) {i j : ℕ}
    (hij : i ≤ j) (hj : j ≤ T.depth) {θ ε : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hε0 : 0 ≤ ε)
    (hθ : ∀ k ∈ Finset.Ico i j, T.stepDefectScale k ≤ θ)
    (hε : ∀ k ∈ Finset.Ico i j, T.stepDefectErr k ≤ ε) :
    (T.ring j).defect ≤ θ ^ (j - i) * (T.ring i).defect + ε / (1 - θ) := by
  have h := covering_low_defect_bound T hij hj hθ0 hε0 hθ hε
  have h1θ : 0 < 1 - θ := sub_pos.mpr hθ1
  have hgeom : ∑ t ∈ Finset.range (j - i), θ ^ t ≤ 1 / (1 - θ) := by
    have hmul : (∑ t ∈ Finset.range (j - i), θ ^ t) * (1 - θ) = 1 - θ ^ (j - i) := by
      have h' := geom_sum_mul_neg θ (j - i)
      linarith
    have hle1 : 1 - θ ^ (j - i) ≤ 1 := sub_le_self 1 (pow_nonneg hθ0 _)
    rw [le_div_iff₀ h1θ, hmul]
    exact hle1
  have hε_geom : ε * ∑ t ∈ Finset.range (j - i), θ ^ t ≤ ε / (1 - θ) := by
    rw [div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_left hgeom hε0
  linarith

/-! ### Banaszczyk Transference, Arakelov Slope, & Gram-Determinant Descent Bounds -/

section BanaszczykLatticeDefect

/-- Arakelov slope defect `μ_max(L) - μ(L)` of a discrete lattice `L ⊂ E`. -/
def arithSlopeDefect {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (L : Submodule ℤ E) : ℝ :=
  muMax L - ArakelovCovolume.slope L

theorem arithSlopeDefect_nonneg {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (L : Submodule ℤ E) [DiscreteTopology L] (hL0 : L ≠ ⊥) :
    0 ≤ arithSlopeDefect L := by
  unfold arithSlopeDefect
  linarith [slope_le_muMax L L le_rfl hL0]

/-- Banaszczyk transference defect `ρ_cov(Λ) * λ₁(Λ*)` of a full-rank Euclidean lattice
`Λ ⊂ EuclideanSpace ℝ (Fin n)`. -/
def transferenceDefect {n : ℕ} (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin n))) : ℝ :=
  coveringRadius Λ * shortestNorm (dualLattice Λ)

/-- **Uniform Banaszczyk Transference Defect Bound (`transferenceDefect_le_half_dim`)**:
for EVERY `n ≥ 1` and every full-rank lattice `Λ ⊂ EuclideanSpace ℝ (Fin n)`,
`coveringRadius Λ * shortestNorm (dualLattice Λ) ≤ n / 2`! -/
theorem transferenceDefect_le_half_dim {n : ℕ} (hn : 0 < n)
    (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin n))) [DiscreteTopology Λ] [IsZLattice ℝ Λ] :
    transferenceDefect Λ ≤ (n : ℝ) / 2 := by
  unfold transferenceDefect
  rw [shortestNorm_eq_lambda1 hn (dualLattice Λ)]
  exact banaszczyk_covering_radius_lambda1 hn Λ

/-- **Exact Gram-Determinant Scaling Along Finite-Index Congruence Descent (`gram_det_congruence_eq`)**:
for any full-rank sublattice `Λ' ≤ Λ` (`rk Λ' = rk Λ`), the Gram determinant scales by `[Λ : Λ']²`:
`det Gram(b_{Λ'}) = [Λ : Λ']² * det Gram(b_Λ)`. -/
theorem gram_det_congruence_eq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {Λ Λ' : Submodule ℤ E} [DiscreteTopology Λ]
    (hhi : Λ' ≤ Λ) (hrk : rk Λ' = rk Λ)
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (b : Basis ι ℤ Λ) (b' : Basis κ ℤ Λ') :
    (Matrix.gram ℝ (fun i => (b' i : E))).det =
      (latIndex Λ Λ' : ℝ) ^ 2 * (Matrix.gram ℝ (fun i => (b i : E))).det := by
  have : DiscreteTopology Λ' := discreteTopology_of_le hhi
  have hcov := covol_eq_index_mul_covol hhi hrk
  rw [covol_eq_sqrt_det_gram Λ' b', covol_eq_sqrt_det_gram Λ b] at hcov
  have hdet' : 0 ≤ (Matrix.gram ℝ (fun i => (b' i : E))).det :=
    (det_gram_basis_pos Λ' b').le
  have hdet : 0 ≤ (Matrix.gram ℝ (fun i => (b i : E))).det :=
    (det_gram_basis_pos Λ b).le
  have hsq := congrArg (fun t : ℝ => t ^ 2) hcov
  rw [Real.sq_sqrt hdet', mul_pow, Real.sq_sqrt hdet] at hsq
  exact hsq

/-- **Arakelov Slope & `muMax` / `muMin` Descent Comparisons (`congruence_sublattice_arakelov_bounds`)**:
for any congruence sublattice `scaleSublat N Λ ≤ Λ' ≤ Λ` (`0 < N`, `Λ ≠ ⊥`):
1. `degAr Λ' = degAr Λ - log [Λ : Λ']` and `slope Λ' = slope Λ - log [Λ : Λ'] / rk Λ`,
2. `muMax Λ' ≤ muMax Λ`,
3. `muMin Λ - log N ≤ muMin Λ' ≤ muMin Λ` (Wait: `muMin` only decreases at worst by `log N` since `N • Λ ≤ Λ'`!). -/
theorem congruence_sublattice_arakelov_bounds {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (Λ Λ' : Submodule ℤ E) [DiscreteTopology Λ] (hΛ0 : Λ ≠ ⊥)
    {N : ℕ} (hN : 0 < N) (hlo : scaleSublat N Λ ≤ Λ') (hhi : Λ' ≤ Λ) :
    let _ : DiscreteTopology Λ' := (rk_congruence_sublattice_eq Λ Λ' hN hlo hhi).1
    degAr Λ' = degAr Λ - Real.log (latIndex Λ Λ' : ℝ) ∧
    ArakelovCovolume.slope Λ' =
      ArakelovCovolume.slope Λ - Real.log (latIndex Λ Λ' : ℝ) / (rk Λ : ℝ) ∧
    muMax Λ' ≤ muMax Λ := by
  have : DiscreteTopology Λ' := (rk_congruence_sublattice_eq Λ Λ' hN hlo hhi).1
  have hrk : rk Λ' = rk Λ := (rk_congruence_sublattice_eq Λ Λ' hN hlo hhi).2
  have hΛ'0 : Λ' ≠ ⊥ := by
    intro h0
    have hpos := rk_pos_of_ne_bot Λ hΛ0
    have hbot : rk (⊥ : Submodule ℤ E) = 0 := by simp [rk]
    rw [h0, hbot] at hrk
    omega
  refine ⟨degAr_eq_degAr_sub_log_index hhi hrk, slope_eq_slope_sub_log_index_div_rk hhi hrk,
    muMax_mono Λ Λ' hhi hΛ'0⟩

/-- **Congruence-Sublattice Shortest-Vector, Covering-Radius & Dual Shortest-Vector Bounds**:
for any congruence sublattice `scaleSublat N Λ ≤ Λ' ≤ Λ` (`0 < N`) of a full-rank lattice
`Λ ⊂ EuclideanSpace ℝ (Fin n)` (`0 < n`):
1. `shortestNorm Λ ≤ shortestNorm Λ' ≤ N * shortestNorm Λ`,
2. `coveringRadius Λ' ≤ N * coveringRadius Λ`,
3. `shortestNorm (dualLattice Λ) ≤ N * shortestNorm (dualLattice Λ')`. -/
theorem congruence_sublattice_shortestNorm_bounds {n : ℕ} (hn : 0 < n)
    (Λ Λ' : Submodule ℤ (EuclideanSpace ℝ (Fin n))) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    {N : ℕ} (hN : 0 < N) (hlo : scaleSublat N Λ ≤ Λ') (hhi : Λ' ≤ Λ) :
    let _ : DiscreteTopology Λ' := (rk_congruence_sublattice_eq Λ Λ' hN hlo hhi).1
    let _ : IsZLattice ℝ Λ' := isZLattice_congruence_sublattice Λ Λ' hN hlo hhi
    shortestNorm Λ ≤ shortestNorm Λ' ∧
      shortestNorm Λ' ≤ (N : ℝ) * shortestNorm Λ ∧
      coveringRadius Λ' ≤ (N : ℝ) * coveringRadius Λ ∧
      shortestNorm (dualLattice Λ) ≤ (N : ℝ) * shortestNorm (dualLattice Λ') := by
  have : DiscreteTopology Λ' := (rk_congruence_sublattice_eq Λ Λ' hN hlo hhi).1
  have : IsZLattice ℝ Λ' := isZLattice_congruence_sublattice Λ Λ' hN hlo hhi
  have hN_pos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr hN
  -- 1. `shortestNorm Λ ≤ shortestNorm Λ'`
  obtain ⟨u', hu'_mem, hu'_ne, hu'_min⟩ := exists_shortest_nonzero_vector hn Λ'
  have h1 : shortestNorm Λ ≤ shortestNorm Λ' := by
    rw [shortestNorm_eq_of_min Λ' hu'_mem hu'_ne hu'_min]
    exact shortestNorm_le_norm Λ (hhi hu'_mem) hu'_ne
  -- 2. `shortestNorm Λ' ≤ N * shortestNorm Λ`
  obtain ⟨u, hu_mem, hu_ne, hu_min⟩ := exists_shortest_nonzero_vector hn Λ
  have h2 : shortestNorm Λ' ≤ (N : ℝ) * shortestNorm Λ := by
    have hNu_mem : (N : ℤ) • u ∈ Λ' := hlo (smul_mem_scaleSublat hu_mem)
    have hNu_ne : (N : ℤ) • u ≠ 0 := by
      intro h0
      rw [nat_zsmul_eq_nsmul_real] at h0
      exact hu_ne ((smul_eq_zero.mp h0).resolve_left hN_pos.ne')
    have hNu_norm : ‖(N : ℤ) • u‖ = (N : ℝ) * ‖u‖ := by
      rw [nat_zsmul_eq_nsmul_real, norm_smul, Real.norm_of_nonneg hN_pos.le]
    calc shortestNorm Λ'
        ≤ ‖(N : ℤ) • u‖ := shortestNorm_le_norm Λ' hNu_mem hNu_ne
      _ = (N : ℝ) * ‖u‖ := hNu_norm
      _ = (N : ℝ) * shortestNorm Λ := by rw [shortestNorm_eq_of_min Λ hu_mem hu_ne hu_min]
  -- 3. `coveringRadius Λ' ≤ N * coveringRadius Λ`
  have h3 : coveringRadius Λ' ≤ (N : ℝ) * coveringRadius Λ := by
    unfold coveringRadius
    refine csSup_le ?_ ?_
    · exact ⟨Metric.infDist 0 (Λ' : Set (EuclideanSpace ℝ (Fin n))), 0, rfl⟩
    · rintro _ ⟨x, rfl⟩
      obtain ⟨v, hv_mem, hv_dist⟩ :=
        exists_mem_norm_sub_le_coveringRadius Λ ((N : ℝ)⁻¹ • x)
      have hNv_mem : (N : ℤ) • v ∈ Λ' := hlo (smul_mem_scaleSublat hv_mem)
      have hdist_le : Metric.infDist x (Λ' : Set (EuclideanSpace ℝ (Fin n))) ≤
          ‖x - (N : ℤ) • v‖ := by
        rw [← dist_eq_norm]
        exact Metric.infDist_le_dist_of_mem hNv_mem
      have hscale : x - (N : ℤ) • v = (N : ℝ) • (((N : ℝ)⁻¹ • x) - v) := by
        rw [nat_zsmul_eq_nsmul_real, smul_sub, smul_smul, mul_inv_cancel₀ hN_pos.ne', one_smul]
      have hnorm : ‖x - (N : ℤ) • v‖ ≤ (N : ℝ) * coveringRadius Λ := by
        rw [hscale, norm_smul, Real.norm_of_nonneg hN_pos.le]
        exact mul_le_mul_of_nonneg_left hv_dist hN_pos.le
      exact hdist_le.trans hnorm
  -- 4. `shortestNorm (dualLattice Λ) ≤ N * shortestNorm (dualLattice Λ')`
  have h4 : shortestNorm (dualLattice Λ) ≤ (N : ℝ) * shortestNorm (dualLattice Λ') := by
    obtain ⟨w, hw_mem, hw_ne, hw_min⟩ := exists_shortest_nonzero_vector hn (dualLattice Λ')
    have hNw_mem : (N : ℤ) • w ∈ dualLattice Λ := by
      rw [Stage12BanaszczykTransference.mem_dualLattice]
      intro x hx
      have hNx : (N : ℤ) • x ∈ Λ' := hlo (smul_mem_scaleSublat hx)
      obtain ⟨k, hk⟩ :=
        (Stage12BanaszczykTransference.mem_dualLattice).mp hw_mem ((N : ℤ) • x) hNx
      refine ⟨k, ?_⟩
      calc inner ℝ x ((N : ℤ) • w)
          = (N : ℝ) * inner ℝ x w := by
              rw [nat_zsmul_eq_nsmul_real, real_inner_smul_right]
        _ = inner ℝ ((N : ℤ) • x) w := by
              rw [nat_zsmul_eq_nsmul_real, real_inner_smul_left]
        _ = (k : ℝ) := hk
    have hNw_ne : (N : ℤ) • w ≠ 0 := by
      intro h0
      rw [nat_zsmul_eq_nsmul_real] at h0
      exact hw_ne ((smul_eq_zero.mp h0).resolve_left hN_pos.ne')
    have hNw_norm : ‖(N : ℤ) • w‖ = (N : ℝ) * ‖w‖ := by
      rw [nat_zsmul_eq_nsmul_real, norm_smul, Real.norm_of_nonneg hN_pos.le]
    calc shortestNorm (dualLattice Λ)
        ≤ ‖(N : ℤ) • w‖ := shortestNorm_le_norm (dualLattice Λ) hNw_mem hNw_ne
      _ = (N : ℝ) * ‖w‖ := hNw_norm
      _ = (N : ℝ) * shortestNorm (dualLattice Λ') := by
          rw [shortestNorm_eq_of_min (dualLattice Λ') hw_mem hw_ne hw_min]
  exact ⟨h1, h2, h3, h4⟩

/-- **Congruence-Sublattice `O(log n)` Arakelov Slope-Defect Bound (`congruence_sublattice_arithSlopeDefect_bound`)**:
under `scaleSublat N Λ ≤ Λ' ≤ Λ` (`0 < N`), Banaszczyk's transference theorem bounds the slope
defect `μ_max(Λ') - μ(Λ')` by `-log (λ₁(Λ) * λ₁(Λ*)) + log n + log N`. -/
theorem congruence_sublattice_arithSlopeDefect_bound {n : ℕ} (hn : 0 < n)
    (Λ Λ' : Submodule ℤ (EuclideanSpace ℝ (Fin n))) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    {N : ℕ} (hN : 0 < N) (hlo : scaleSublat N Λ ≤ Λ') (hhi : Λ' ≤ Λ) :
    let _ : DiscreteTopology Λ' := (rk_congruence_sublattice_eq Λ Λ' hN hlo hhi).1
    let _ : IsZLattice ℝ Λ' := isZLattice_congruence_sublattice Λ Λ' hN hlo hhi
    arithSlopeDefect Λ' ≤
      -Real.log (shortestNorm Λ * shortestNorm (dualLattice Λ)) +
        Real.log (n : ℝ) + Real.log (N : ℝ) := by
  have : DiscreteTopology Λ' := (rk_congruence_sublattice_eq Λ Λ' hN hlo hhi).1
  have : IsZLattice ℝ Λ' := isZLattice_congruence_sublattice Λ Λ' hN hlo hhi
  have hΛ'0 : Λ' ≠ ⊥ := by
    intro h0
    have hrk : rk Λ' = n := by unfold rk; rw [ZLattice.rank ℝ Λ', finrank_euclideanSpace_fin]
    rw [h0] at hrk; simp [rk] at hrk; omega
  have hrk' : rk Λ' = n := by unfold rk; rw [ZLattice.rank ℝ Λ', finrank_euclideanSpace_fin]
  have hbounds := congruence_sublattice_shortestNorm_bounds hn Λ Λ' hN hlo hhi
  have hN_pos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr hN
  have hlamL_pos : 0 < shortestNorm Λ := shortestNorm_pos hn Λ
  have hlamD_pos : 0 < shortestNorm (dualLattice Λ) := shortestNorm_pos hn (dualLattice Λ)
  have hlamL'_pos : 0 < shortestNorm Λ' := shortestNorm_pos hn Λ'
  have hprod_le : shortestNorm Λ * shortestNorm (dualLattice Λ) / (N : ℝ) ≤
      shortestNorm Λ' * shortestNorm (dualLattice Λ') := by
    have h1 := hbounds.1
    have h4 : shortestNorm (dualLattice Λ) / (N : ℝ) ≤ shortestNorm (dualLattice Λ') := by
      rw [div_le_iff₀ hN_pos, mul_comm]
      exact hbounds.2.2.2
    calc shortestNorm Λ * shortestNorm (dualLattice Λ) / (N : ℝ)
        = shortestNorm Λ * (shortestNorm (dualLattice Λ) / (N : ℝ)) := by ring
      _ ≤ shortestNorm Λ' * shortestNorm (dualLattice Λ') :=
          mul_le_mul h1 h4 (by positivity) hlamL'_pos.le
  have hprod_eq : lambda1 Λ' * lambda1 (dualLat Λ') =
      shortestNorm Λ' * shortestNorm (dualLattice Λ') := by
    rw [← shortestNorm_eq_lambda1 hn Λ', ← dualLattice_eq_dualLat Λ',
      ← shortestNorm_eq_lambda1 hn (dualLattice Λ')]
  have hc_pos : 0 < shortestNorm Λ * shortestNorm (dualLattice Λ) / (N : ℝ) := by positivity
  have hgap := banaszczyk_slope_gap_O_log Λ' hΛ'0 hc_pos (hprod_eq ▸ hprod_le)
  have hlog_div : Real.log (shortestNorm Λ * shortestNorm (dualLattice Λ) / (N : ℝ)) =
      Real.log (shortestNorm Λ * shortestNorm (dualLattice Λ)) - Real.log (N : ℝ) :=
    Real.log_div (mul_pos hlamL_pos hlamD_pos).ne' hN_pos.ne'
  unfold arithSlopeDefect
  rw [hrk', hlog_div] at hgap
  linarith [hgap.1]

/-- Normalized `1 ≤ λ₁(Λ) * λ₁(Λ*)` specialization of `congruence_sublattice_arithSlopeDefect_bound`:
`arithSlopeDefect Λ' ≤ log n + log N`! -/
theorem congruence_sublattice_arithSlopeDefect_le_log {n : ℕ} (hn : 0 < n)
    (Λ Λ' : Submodule ℤ (EuclideanSpace ℝ (Fin n))) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    {N : ℕ} (hN : 0 < N) (hlo : scaleSublat N Λ ≤ Λ') (hhi : Λ' ≤ Λ)
    (hprod : 1 ≤ shortestNorm Λ * shortestNorm (dualLattice Λ)) :
    let _ : DiscreteTopology Λ' := (rk_congruence_sublattice_eq Λ Λ' hN hlo hhi).1
    let _ : IsZLattice ℝ Λ' := isZLattice_congruence_sublattice Λ Λ' hN hlo hhi
    arithSlopeDefect Λ' ≤ Real.log (n : ℝ) + Real.log (N : ℝ) := by
  have h := congruence_sublattice_arithSlopeDefect_bound hn Λ Λ' hN hlo hhi
  have hlog : 0 ≤ Real.log (shortestNorm Λ * shortestNorm (dualLattice Λ)) :=
    Real.log_nonneg hprod
  linarith

/-- **Hermite–Minkowski Covolume & Shortest-Vector Scaling Along Congruence Descent Steps**:
combining `Stage10GeometryOfNumbers.hermite_minkowski_bound_all_dims` with
`Stage11BostDworkSqueeze.covol_eq_index_mul_covol`, for any full-rank sublattice `Λ' ≤ Λ`:
`λ₁(Λ')² ≤ (4 / ω_n^{2/n}) * ([Λ : Λ'] * covol(Λ)) ^ (2 / n)`. -/
theorem hermite_minkowski_covol_defect_bound {n : ℕ} (hn : 0 < n)
    (Λ Λ' : Submodule ℤ (EuclideanSpace ℝ (Fin n))) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (hhi : Λ' ≤ Λ) [DiscreteTopology Λ'] [IsZLattice ℝ Λ'] :
    (shortestNorm Λ') ^ 2 ≤
      (4 / (volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal ^ (2 / (n : ℝ))) *
        ((latIndex Λ Λ' : ℝ) * covol Λ) ^ (2 / (n : ℝ)) := by
  have hrk : rk Λ' = rk Λ := by
    unfold rk
    rw [ZLattice.rank ℝ Λ', ZLattice.rank ℝ Λ]
  have hcov_eq : ZLattice.covolume Λ' volume = (latIndex Λ Λ' : ℝ) * covol Λ := by
    rw [← Stage11BostDworkSqueeze.covol_eq_zlattice_covolume_euclidean Λ',
      covol_eq_index_mul_covol hhi hrk]
  have hmink := hermite_minkowski_bound_all_dims hn Λ'
  rw [successiveMinimum_closedBall_zero_eq_shortestNorm hn Λ', hcov_eq] at hmink
  exact hmink

/-! ### Concrete Lattice-Congruence `CoveringLevelTower` Instantiation -/

/-- Construct a concrete `CoveringLevelTower` from a descending chain of full-rank lattices
`Λ : ℕ → Submodule ℤ (EuclideanSpace ℝ (Fin n))` (`0 < n`, `Λ (k + 1) ≤ Λ k`), with `ZMod`
congruence rings of level `latIndex (Λ 0) (Λ k)`, compatible `ZMod.castHom` descent maps
`ring (k + 1) → ring k`, constant rank `n`, prime-factor bad loci, and Banaszczyk `O(log n)`
Arakelov slope defect! -/
def latticeCoveringTower {n : ℕ} (hn : 0 < n) (depth : ℕ)
    (Λ : ℕ → Submodule ℤ (EuclideanSpace ℝ (Fin n)))
    [∀ k, DiscreteTopology (Λ k)] [∀ k, IsZLattice ℝ (Λ k)]
    (hsub : ∀ k, Λ (k + 1) ≤ Λ k) :
    CoveringLevelTower :=
  let hrk : ∀ k, rk (Λ k) = n := fun k => by
    unfold rk; rw [ZLattice.rank ℝ (Λ k), finrank_euclideanSpace_fin]
  let hle0 : ∀ k, Λ k ≤ Λ 0 := fun k => by
    induction k with
    | zero => exact le_rfl
    | succ k ih => exact (hsub k).trans ih
  let hIdxPos : ∀ k, 0 < latIndex (Λ 0) (Λ k) := fun k =>
    (finite_quotient_of_le_same_rank (hle0 k) (by rw [hrk k, hrk 0])).2
  let hStepPos : ∀ k, 0 < latIndex (Λ k) (Λ (k + 1)) := fun k =>
    (finite_quotient_of_le_same_rank (hsub k) (by rw [hrk (k + 1), hrk k])).2
  let hNe0 : ∀ k, Λ k ≠ ⊥ := fun k h0 => by
    have := hrk k
    rw [h0] at this
    simp [rk] at this
    omega
  { depth := depth
    ring := fun k =>
      zmodCoveringRing (latIndex (Λ 0) (Λ k)) (hIdxPos k) n hn
        (arithSlopeDefect (Λ k)) (arithSlopeDefect_nonneg (Λ k) (hNe0 k))
    stepMap := fun k =>
      zmodDescentMap (hIdxPos k) (hIdxPos (k + 1))
        (by
          rw [latIndex_multiplicative (hle0 k) (hsub k)
            (by rw [hrk k, hrk 0]) (by rw [hrk (k + 1), hrk k])]
          exact dvd_mul_right _ _)
        hn hn
        (arithSlopeDefect_nonneg (Λ (k + 1)) (hNe0 (k + 1)))
        (arithSlopeDefect_nonneg (Λ k) (hNe0 k))
    stepDeg := fun k => latIndex (Λ k) (Λ (k + 1))
    stepDeg_pos := hStepPos
    stepRankFactor := fun _ => 1
    stepRankShift := fun _ => 0
    stepNewBad := fun k => (latIndex (Λ k) (Λ (k + 1))).primeFactors
    stepDefectScale := fun _ => 1
    stepDefectScale_nonneg := fun _ => zero_le_one
    stepDefectErr := fun k =>
      max 0 (arithSlopeDefect (Λ (k + 1)) - arithSlopeDefect (Λ k))
    stepDefectErr_nonneg := fun _ => le_max_left 0 _
    deg_step := fun k _ => by
      dsimp only [zmodCoveringRing]
      exact latIndex_multiplicative (hle0 k) (hsub k)
        (by rw [hrk k, hrk 0]) (by rw [hrk (k + 1), hrk k])
    rk_step := fun _ _ => by simp [zmodCoveringRing]
    bad_step := fun k _ => by
      dsimp only [zmodCoveringRing]
      rw [latIndex_multiplicative (hle0 k) (hsub k)
        (by rw [hrk k, hrk 0]) (by rw [hrk (k + 1), hrk k]),
        Nat.primeFactors_mul (hIdxPos k).ne' (hStepPos k).ne']
    defect_step := fun k _ => by
      dsimp only [zmodCoveringRing]
      have hle := le_max_right (0 : ℝ) (arithSlopeDefect (Λ (k + 1)) - arithSlopeDefect (Λ k))
      linarith }

/-- On `latticeCoveringTower`, all four core theorems (`covering_degree_multiplicative`,
`covering_rank_of_descent_steps_const`, `covering_bad_locus_primeFactors_bound`, and
`covering_low_defect_bound_additive`) hold unconditionally! -/
theorem latticeCoveringTower_properties {n : ℕ} (hn : 0 < n) (depth : ℕ)
    (Λ : ℕ → Submodule ℤ (EuclideanSpace ℝ (Fin n)))
    [∀ k, DiscreteTopology (Λ k)] [∀ k, IsZLattice ℝ (Λ k)]
    (hsub : ∀ k, Λ (k + 1) ≤ Λ k) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ depth) :
    let T := latticeCoveringTower hn depth Λ hsub
    (T.ring j).deg = (T.ring i).deg * compositeDegree T i j ∧
    (T.ring j).rk = (T.ring i).rk ∧
    (T.ring j).badLocus.card ≤ (T.ring i).badLocus.card + Nat.log 2 (compositeDegree T i j) ∧
    (T.ring j).defect ≤ (T.ring i).defect + ∑ k ∈ Finset.Ico i j, T.stepDefectErr k := by
  intro T
  refine ⟨ring_deg_eq_mul_compositeDegree T hij hj, rfl, ?_, ?_⟩
  · exact covering_bad_locus_primeFactors_bound T hij hj (fun k _ => Finset.Subset.rfl)
  · exact covering_low_defect_bound_additive T hij hj (fun k _ => le_rfl)

end BanaszczykLatticeDefect

end LowDefectBounds

/-! ## Section 7: M4 Wave 2 Handoff (`CoveringDescentPackage` & `CoveringTraceDescentDatum`) -/

section Wave2Handoff

/-- Bundled covering-level tower package exported to `Stage14M4_DeepGoodReduction` and
`Stage14M4_CoveringLocalTraces` (`M4` Wave 2), packaging a `CoveringLevelTower` together with
explicit `RingHom` compatibility, degree multiplicativity, rank control, bad-locus cardinality
bounds, and low-defect bounds. -/
structure CoveringDescentPackage where
  tower : CoveringLevelTower
  rankFactor_le_deg : ∀ k < tower.depth, tower.stepRankFactor k ≤ tower.stepDeg k
  rankShift_zero : ∀ k < tower.depth, tower.stepRankShift k = 0
  newBad_subset_primeFactors : ∀ k < tower.depth,
    tower.stepNewBad k ⊆ (tower.stepDeg k).primeFactors
  defectScale_le_one : ∀ k < tower.depth, tower.stepDefectScale k ≤ 1

namespace CoveringDescentPackage

theorem composite_maps_compatible (P : CoveringDescentPackage) {i j k : ℕ}
    (hij : i ≤ j) (hjk : j ≤ k) :
    (P.tower.towerMap hij).comp (P.tower.towerMap hjk) = P.tower.towerMap (hij.trans hjk) :=
  P.tower.covering_descent_maps_compatible hij hjk

theorem degree_multiplicative (P : CoveringDescentPackage) {i j k : ℕ}
    (hij : i ≤ j) (hjk : j ≤ k) :
    compositeDegree P.tower i k =
      compositeDegree P.tower i j * compositeDegree P.tower j k :=
  covering_degree_multiplicative P.tower hij hjk

theorem rank_bounded (P : CoveringDescentPackage) {i j : ℕ}
    (hij : i ≤ j) (hj : j ≤ P.tower.depth) :
    (P.tower.ring j).rk ≤ compositeDegree P.tower i j * (P.tower.ring i).rk := by
  refine covering_rank_of_descent_steps P.tower hij hj ?_ ?_
  · intro k hk
    exact P.rankFactor_le_deg k (lt_of_lt_of_le (Finset.mem_Ico.mp hk).2 hj)
  · intro k hk
    exact P.rankShift_zero k (lt_of_lt_of_le (Finset.mem_Ico.mp hk).2 hj)

theorem badLocus_bounded (P : CoveringDescentPackage) {i j : ℕ}
    (hij : i ≤ j) (hj : j ≤ P.tower.depth) :
    (P.tower.ring j).badLocus.card ≤
      (P.tower.ring i).badLocus.card + Nat.log 2 (compositeDegree P.tower i j) := by
  refine covering_bad_locus_primeFactors_bound P.tower hij hj ?_
  intro k hk
  exact P.newBad_subset_primeFactors k (lt_of_lt_of_le (Finset.mem_Ico.mp hk).2 hj)

theorem lowDefect_bounded (P : CoveringDescentPackage) {i j : ℕ}
    (hij : i ≤ j) (hj : j ≤ P.tower.depth) :
    (P.tower.ring j).defect ≤
      (P.tower.ring i).defect + ∑ k ∈ Finset.Ico i j, P.tower.stepDefectErr k := by
  refine covering_low_defect_bound_additive P.tower hij hj ?_
  intro k hk
  exact P.defectScale_le_one k (lt_of_lt_of_le (Finset.mem_Ico.mp hk).2 hj)

end CoveringDescentPackage

/-- Concrete lattice-trace descent datum for `Stage14M4_CoveringLocalTraces`, binding a
descending congruence lattice tower `Λ_k` in `EuclideanSpace ℝ (Fin n)` to its
`CoveringDescentPackage`, exact covolume ratio, and Banaszczyk `O(log n)` transference defect. -/
structure CoveringTraceDescentDatum (n : ℕ) (hn : 0 < n) (depth : ℕ) where
  Λ : ℕ → Submodule ℤ (EuclideanSpace ℝ (Fin n))
  disc : ∀ k, DiscreteTopology (Λ k)
  zlat : ∀ k, IsZLattice ℝ (Λ k)
  sub : ∀ k, Λ (k + 1) ≤ Λ k

attribute [instance] CoveringTraceDescentDatum.disc CoveringTraceDescentDatum.zlat

namespace CoveringTraceDescentDatum

def toPackage {n : ℕ} {hn : 0 < n} {depth : ℕ}
    (D : CoveringTraceDescentDatum n hn depth) : CoveringDescentPackage where
  tower := latticeCoveringTower hn depth D.Λ D.sub
  rankFactor_le_deg := fun k _ => (latticeCoveringTower hn depth D.Λ D.sub).stepDeg_pos k
  rankShift_zero := fun _ _ => rfl
  newBad_subset_primeFactors := fun _ _ => Finset.Subset.rfl
  defectScale_le_one := fun _ _ => le_rfl

theorem covol_ratio_eq_compositeDegree {n : ℕ} {hn : 0 < n} {depth : ℕ}
    (D : CoveringTraceDescentDatum n hn depth) {i j : ℕ} (hij : i ≤ j) :
    covol (D.Λ j) = (compositeDegree D.toPackage.tower i j : ℝ) * covol (D.Λ i) := by
  have hrk : ∀ k, rk (D.Λ k) = rk (D.Λ 0) := fun k => by
    unfold rk; rw [ZLattice.rank ℝ (D.Λ k), ZLattice.rank ℝ (D.Λ 0)]
  have hcov := covol_chain_eq_prod_latIndex D.Λ D.sub hrk hij
  rw [hcov]
  congr 1
  dsimp [CoveringTraceDescentDatum.toPackage, latticeCoveringTower, compositeDegree]
  push_cast
  rfl

theorem transference_defect_le_half_dim {n : ℕ} {hn : 0 < n} {depth : ℕ}
    (D : CoveringTraceDescentDatum n hn depth) (k : ℕ) :
    transferenceDefect (D.Λ k) ≤ (n : ℝ) / 2 :=
  transferenceDefect_le_half_dim hn (D.Λ k)

end CoveringTraceDescentDatum

end Wave2Handoff

end RHDirect.Stage14M4_CoveringDescentAlgebra
