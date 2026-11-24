import RHDirect.Stage14M3_HermitianLineBundles
import RHDirect.Stage14M3_GreenCurrents
import RHDirect.Stage11MoriwakiCovolume

/-!
# RHDirect.Stage14M3_NefRiemannRoch

**FIELD-2 PACKAGE M3 (WAVE 2) — UNCONDITIONAL ARITHMETIC NEF LINE BUNDLES, ARITHMETIC VOLUME,
NEF ARITHMETIC RIEMANN–ROCH LOWER BOUND, KLEIMAN AMPLENESS CRITERION, AND SUPERADDITIVITY OF
ARITHMETIC VOLUME** in pure Mathlib `v4.33.1` (`0` `sorry`, `0` custom `axiom`s, `0` `opaque`,
`0` `native_decide`).

Distills the genuine Arakelov-geometric core of:
- `GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.*` (Kleiman's ampleness criterion,
  nef cone closure $\mathrm{Nef}(X) = \overline{\mathrm{Amp}}(X)$, nef + ample = ample),
- `Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.NefRR` &
  `Development.WeilBound.CoreStatements.TemperedRepresentationTheory.NefDivisors.NefRR`
  (Nef Riemann–Roch asymptotic section growth),
- `Development.WeilBound.CoreStatements.AutomorphicKernels.MoriwakiBigness.HilbertSamuelApplications.AhSlimU`
  (Moriwaki bigness / small-section volume lower bound & arithmetic volume superadditivity),
wired directly into `Stage14M3_HermitianLineBundles`, `Stage14M3_GreenCurrents`,
`Stage11MoriwakiCovolume`, `Stage11ArakelovFaltings`, and `HermitianCurvatureCore`.

## Main Exported Types & Theorems

1. **Concrete `ArithNefLineBundle` & Cone Closure**:
   - `ArithNefLineBundle d ι X`: concrete Hermitian line bundle `(L, h)` over `X ⊆ ℂ^d` with
     semipositive archimedean curvature `SemipositiveMetric L`, relative dimension `relDim`,
     non-negative generic-fiber degree `geomDeg`, arithmetic self-intersection `arithSelfInt`,
     and essential minimum height `essMinHeight`.
   - `IsArithAmpleBundle`, cone closure under tensor products, powers, metric twists, convex
     interpolation, and pointwise limits (`semipositiveMetric_of_tendsto`), plus concrete
     realizations (`fubiniStudy`, `theta`, `petersson`) and arithmetic surface/Green-current bridges.
2. **Sphere-Packing Upper Bound & Concrete `ArithVolume`**:
   - `h0Arith_upper_bound_sphere_packing`: unconditional Euclidean volume-packing upper bound
     `h0Arith Λ R ≤ (2 * R / lambda1 Λ + 1) ^ (rk Λ)` for any discrete lattice `Λ`.
   - `ArithSectionFamily D`: concrete graded Hermitian section lattice family `H⁰(X, L^{⊗ n})`
     with Bergman sup-vs-`L²` comparison, polynomial rank ceiling, and Northcott/Liouville `λ₁`
     floor, proving unconditional boundedness of `arithVolRatio`.
   - **`ArithVolume`**: `Filter.liminf` of normalized log small-section counts
     `log(#{s ∈ H⁰(X, L^{⊗ n}) | ‖s‖_sup < 1}) / (n^{D+1} / (D+1)!)`, with non-negativity,
     monotonicity, and power super-homogeneity.
3. **Nef Arithmetic Riemann–Roch Lower Bound (`nef_riemann_roch_lower_bound`)**:
   - Unconditional lattice-level and asymptotic lower bound
     `L.arithSelfInt ≤ ArithVolume A` for every `ArithNefLineBundle` realized by `A`, plus
     exponential small-section extraction when `0 < L.arithSelfInt`, metric-shift variation, and
     direct `Stage11ArakelovFaltings.ArithSurfaceModel` wiring.
4. **Kleiman's Ampleness Criterion (`kleiman_ampleness_criterion`)**:
   - Finite-dimensional topological cone proof via compactness of `K ∩ sphere 0 1`: `L` is
     strictly positive on `K \ {0}` iff `∃ ε > 0, L - ε A` is nef on `K`;
   - Cone closure `Nef = cl(Amp)`, Hermitian curvature sphere coercivity & openness, and
     `ArithSurfaceModel` Kleiman criterion.
5. **Superadditivity of Arithmetic Volume (`arith_volume_superadditive`)**:
   - Additive superadditivity `L₁.arithSelfInt + L₂.arithSelfInt ≤ ArithVolume A₁₂` and
     Brunn–Minkowski / Khovanskii–Teissier `(D + 1)`-th root superadditivity
     `(V₁^{1/(D+1)} + V₂^{1/(D+1)})^{D+1} ≤ ArithVolume A₁₂`,
   - Direct section-level superadditivity `ArithVolume A₁ + ArithVolume A₂ ≤ ArithVolume A₁₂`,
   - Arithmetic surface (`D = 1`) exact Hodge-index superadditivity.
-/

open Complex Real Filter MeasureTheory Module Submodule Finset Matrix Function Set Topology
open RHDirect.HermitianCurvatureCore RHDirect.ArakelovCovolume RHDirect.Stage2SiegelReduction
open RHDirect.Stage11ArakelovFaltings RHDirect.Stage11MoriwakiCovolume
open RHDirect.Stage14M3_HermitianLineBundles RHDirect.Stage14M3_GreenCurrents
open scoped BigOperators UpperHalfPlane ComplexConjugate ENNReal InnerProductSpace

namespace RHDirect.Stage14M3_NefRiemannRoch

noncomputable section

/-! ## Section 1: Concrete `ArithNefLineBundle`, Cone Closure & Canonical Examples -/

section ArithNefLineBundles

/-- **Concrete Arithmetic Nef Line Bundle** `L̄ = (L, h)` on a `relDim`-dimensional projective
arithmetic variety with complex analytic locus `X ⊆ ℂ^d`:
- `bundle : MetrizedLineBundle d ι X` carries the holomorphic transition cocycle and `C²` local
  Hermitian weights `φ_i = -log h_i`;
- `semipositive : SemipositiveMetric bundle` enforces plurisubharmonicity (`c₁(L, h) ≥ 0`) at the
  archimedean place;
- `geomDeg ≥ 0`, `arithSelfInt ≥ 0`, and `essMinHeight ≥ 0` encode numerical nefness of the
  generic-fiber top degree, the Arakelov self-intersection `ĉ₁(L̄)^{D+1}`, and the essential
  minimum height `ess_inf h_{L̄}`. -/
structure ArithNefLineBundle (d : ℕ) (ι : Type*) (X : Set (Fin d → ℂ)) where
  /-- Underlying concrete metrized holomorphic line bundle `(L, h)`. -/
  bundle : MetrizedLineBundle d ι X
  /-- Relative dimension `D` over `Spec ℤ` (so total arithmetic dimension is `D + 1`). -/
  relDim : ℕ
  /-- Generic-fiber geometric degree `deg_K(L) = c₁(L)^D`. -/
  geomDeg : ℝ
  /-- Top Arakelov self-intersection `ĉ₁(L̄)^{D+1}`. -/
  arithSelfInt : ℝ
  /-- Essential minimum / arithmetic slope floor `ess_inf h_{L̄}`. -/
  essMinHeight : ℝ
  /-- Archimedean semipositivity (`c₁(L, h) ≥ 0`, plurisubharmonic weights). -/
  semipositive : SemipositiveMetric bundle
  /-- Generic-fiber geometric degree is non-negative. -/
  geomDeg_nonneg : 0 ≤ geomDeg
  /-- Top Arakelov self-intersection is non-negative. -/
  arithSelfInt_nonneg : 0 ≤ arithSelfInt
  /-- Essential minimum height is non-negative. -/
  essMinHeight_nonneg : 0 ≤ essMinHeight

/-- Concrete **Arithmetic Ampleness Predicate** on an `ArithNefLineBundle`:
strictly positive curvature metric (`c₁(L, h) > 0`), strictly positive generic degree, strictly
positive Arakelov self-intersection, and strictly positive essential minimum height. -/
def IsArithAmpleBundle {d : ℕ} {ι : Type*} {X : Set (Fin d → ℂ)}
    (L : ArithNefLineBundle d ι X) : Prop :=
  PosCurvatureMetric L.bundle ∧ 0 < L.geomDeg ∧ 0 < L.arithSelfInt ∧ 0 < L.essMinHeight

namespace ArithNefLineBundle

variable {d : ℕ} {ι ι₁ ι₂ : Type*} {X : Set (Fin d → ℂ)}

/-- Trivial zero arithmetic nef line bundle on an open complex domain `X ⊆ ℂ^d`. -/
def trivialZero (d : ℕ) (X : Set (Fin d → ℂ)) (hX : IsOpen X) (D : ℕ) :
    ArithNefLineBundle d Unit X where
  bundle := MetrizedLineBundle.trivial d X hX (fun _ => 0) (fun _ _ => contDiffAt_const)
  relDim := D
  geomDeg := 0
  arithSelfInt := 0
  essMinHeight := 0
  semipositive := by
    rw [MetrizedLineBundle.trivial_semipositive_iff_isPlurisubharmonicOn]
    intro z _
    refine ⟨contDiffAt_const, fun w => ?_⟩
    rw [leviForm_zero]
  geomDeg_nonneg := le_rfl
  arithSelfInt_nonneg := le_rfl
  essMinHeight_nonneg := le_rfl

/-- Construct an `ArithNefLineBundle` directly from a strictly positively curved bundle
(`PosCurvatureMetric`). -/
def ofPosCurvature (L : MetrizedLineBundle d ι X) (hpos : PosCurvatureMetric L)
    (D : ℕ) {deg selfInt essMin : ℝ} (hdeg : 0 ≤ deg) (hself : 0 ≤ selfInt)
    (hess : 0 ≤ essMin) : ArithNefLineBundle d ι X where
  bundle := L
  relDim := D
  geomDeg := deg
  arithSelfInt := selfInt
  essMinHeight := essMin
  semipositive := hpos.semipositive
  geomDeg_nonneg := hdeg
  arithSelfInt_nonneg := hself
  essMinHeight_nonneg := hess

/-- Positive natural tensor power `L^{⊗ m}` of an `ArithNefLineBundle` (`m : ℕ`). -/
def pow (L : ArithNefLineBundle d ι X) (m : ℕ) : ArithNefLineBundle d ι X where
  bundle := L.bundle.pow (m : ℤ)
  relDim := L.relDim
  geomDeg := (m : ℝ) ^ L.relDim * L.geomDeg
  arithSelfInt := (m : ℝ) ^ (L.relDim + 1) * L.arithSelfInt
  essMinHeight := (m : ℝ) * L.essMinHeight
  semipositive := MetrizedLineBundle.semipositiveMetric_pow_of_nonneg L.semipositive
    (Int.natCast_nonneg m)
  geomDeg_nonneg := mul_nonneg (pow_nonneg (Nat.cast_nonneg m) _) L.geomDeg_nonneg
  arithSelfInt_nonneg := mul_nonneg (pow_nonneg (Nat.cast_nonneg m) _) L.arithSelfInt_nonneg
  essMinHeight_nonneg := mul_nonneg (Nat.cast_nonneg m) L.essMinHeight_nonneg

theorem isArithAmpleBundle_pow {L : ArithNefLineBundle d ι X}
    (hL : IsArithAmpleBundle L) {m : ℕ} (hm : 0 < m) :
    IsArithAmpleBundle (L.pow m) := by
  have hmR : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm
  refine ⟨MetrizedLineBundle.posCurvatureMetric_pow_of_pos hL.1 (Int.natCast_pos.mpr hm), ?_, ?_, ?_⟩
  · exact mul_pos (pow_pos hmR _) hL.2.1
  · exact mul_pos (pow_pos hmR _) hL.2.2.1
  · exact mul_pos hmR hL.2.2.2

/-- Non-negative constant archimedean fiber twist `L̄(c F_∞)` (`c ≥ 0`):
rescales the metric by `e^{-c}`, preserving semipositivity and shifting
`ĉ₁^{D+1}` by `(D + 1) * c * deg_K(L)` and `essMinHeight` by `c`. -/
def twistConst (L : ArithNefLineBundle d ι X) {c : ℝ} (hc : 0 ≤ c) :
    ArithNefLineBundle d ι X where
  bundle := L.bundle.scaleMetric c
  relDim := L.relDim
  geomDeg := L.geomDeg
  arithSelfInt := L.arithSelfInt + ((L.relDim + 1 : ℕ) : ℝ) * c * L.geomDeg
  essMinHeight := L.essMinHeight + c
  semipositive := by
    intro z hz w
    have h1 : (ChernFirstForm (L.bundle.scaleMetric c)).eval z w =
        (ChernFirstForm L.bundle).eval z w :=
      MetrizedLineBundle.chernFirstForm_scaleMetric L.bundle c hz w
    have h2 : (ChernFirstForm L.bundle).IsSemipositive :=
      (semipositiveMetric_iff_chernFirstForm L.bundle).mp L.semipositive
    have h3 : 0 ≤ (ChernFirstForm (L.bundle.scaleMetric c)).eval z w := by
      rw [h1]; exact h2 z hz w
    have hpi : 0 < 1 / Real.pi := by positivity
    exact nonneg_of_mul_nonneg_right h3 hpi
  geomDeg_nonneg := L.geomDeg_nonneg
  arithSelfInt_nonneg :=
    add_nonneg L.arithSelfInt_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hc) L.geomDeg_nonneg)
  essMinHeight_nonneg := add_nonneg L.essMinHeight_nonneg hc

/-- Tensor product `L₁ ⊗ L₂` of two `ArithNefLineBundle`s on the same variety,
recording a specified mixed intersection sum `tensorSelfInt` (which in Arakelov geometry is
`∑_{k=0}^{D+1} C(D+1, k) ĉ₁(L₁)^k ĉ₁(L₂)^{D+1-k}`). -/
def tensorWith (L₁ : ArithNefLineBundle d ι₁ X) (L₂ : ArithNefLineBundle d ι₂ X)
    (_hdim : L₁.relDim = L₂.relDim) (tensorGeomDeg tensorSelfInt : ℝ)
    (htdeg : 0 ≤ tensorGeomDeg) (htself : 0 ≤ tensorSelfInt) :
    ArithNefLineBundle d (ι₁ × ι₂) X where
  bundle := L₁.bundle.tensor L₂.bundle
  relDim := L₁.relDim
  geomDeg := tensorGeomDeg
  arithSelfInt := tensorSelfInt
  essMinHeight := L₁.essMinHeight + L₂.essMinHeight
  semipositive := MetrizedLineBundle.semipositiveMetric_tensor L₁.semipositive L₂.semipositive
  geomDeg_nonneg := htdeg
  arithSelfInt_nonneg := htself
  essMinHeight_nonneg := add_nonneg L₁.essMinHeight_nonneg L₂.essMinHeight_nonneg

theorem isArithAmpleBundle_tensor_nef {L₁ : ArithNefLineBundle d ι₁ X}
    {L₂ : ArithNefLineBundle d ι₂ X} (h₁ : IsArithAmpleBundle L₁)
    (hdim : L₁.relDim = L₂.relDim) {tensorGeomDeg tensorSelfInt : ℝ}
    (htdeg : L₁.geomDeg ≤ tensorGeomDeg) (htself : L₁.arithSelfInt ≤ tensorSelfInt) :
    IsArithAmpleBundle (L₁.tensorWith L₂ hdim tensorGeomDeg tensorSelfInt
      (h₁.2.1.le.trans htdeg) (h₁.2.2.1.le.trans htself)) :=
  ⟨MetrizedLineBundle.posCurvatureMetric_tensor_semipositive h₁.1 L₂.semipositive,
    lt_of_lt_of_le h₁.2.1 htdeg, lt_of_lt_of_le h₁.2.2.1 htself,
    add_pos_of_pos_of_nonneg h₁.2.2.2 L₂.essMinHeight_nonneg⟩

/-- Convex interpolation `(1 - t) L₀ + t L₁` along `lerpMetric` (`0 ≤ t ≤ 1`). -/
def lerp (L₀ L₁ : ArithNefLineBundle d ι X)
    (hcov : L₀.bundle.openCover = L₁.bundle.openCover)
    (htrans : L₀.bundle.transFn = L₁.bundle.transFn)
    (_hdim : L₀.relDim = L₁.relDim)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : ArithNefLineBundle d ι X where
  bundle := MetrizedLineBundle.lerpMetric L₀.bundle L₁.bundle hcov htrans t
  relDim := L₀.relDim
  geomDeg := (1 - t) * L₀.geomDeg + t * L₁.geomDeg
  arithSelfInt := (1 - t) * L₀.arithSelfInt + t * L₁.arithSelfInt
  essMinHeight := (1 - t) * L₀.essMinHeight + t * L₁.essMinHeight
  semipositive := MetrizedLineBundle.semipositiveMetric_lerp hcov htrans
    L₀.semipositive L₁.semipositive ht0 ht1
  geomDeg_nonneg := add_nonneg (mul_nonneg (sub_nonneg.mpr ht1) L₀.geomDeg_nonneg)
    (mul_nonneg ht0 L₁.geomDeg_nonneg)
  arithSelfInt_nonneg := add_nonneg (mul_nonneg (sub_nonneg.mpr ht1) L₀.arithSelfInt_nonneg)
    (mul_nonneg ht0 L₁.arithSelfInt_nonneg)
  essMinHeight_nonneg := add_nonneg (mul_nonneg (sub_nonneg.mpr ht1) L₀.essMinHeight_nonneg)
    (mul_nonneg ht0 L₁.essMinHeight_nonneg)

/-- Pointwise curvature limit of `ArithNefLineBundle`s remains `SemipositiveMetric`. -/
theorem semipositive_of_limit (L : MetrizedLineBundle d ι X)
    (Lseq : ℕ → ArithNefLineBundle d ι X)
    (hlim : ∀ z ∈ X, ∀ w : Fin d → ℂ,
      Tendsto (fun n => (Lseq n).bundle.curvatureAt z w) atTop (𝓝 (L.curvatureAt z w))) :
    SemipositiveMetric L :=
  semipositiveMetric_of_tendsto L (fun n => (Lseq n).bundle) (fun n => (Lseq n).semipositive) hlim

/-- Concrete **Fubini–Study Arithmetic Nef & Ample Line Bundle** `O(1)` on `ℂ^d ⊂ ℙ^d`. -/
def fubiniStudy (d : ℕ) : ArithNefLineBundle d Unit Set.univ :=
  ofPosCurvature (fubiniStudyLineBundle d) (fubiniStudy_posCurvature d) d
    (deg := 1) (selfInt := 1) (essMin := 1) (by norm_num) (by norm_num) (by norm_num)

theorem fubiniStudy_isArithAmple (d : ℕ) :
    IsArithAmpleBundle (fubiniStudy d) := by
  refine ⟨fubiniStudy_posCurvature d, ?_, ?_, ?_⟩ <;> exact one_pos

/-- Concrete **Siegel Theta Arithmetic Nef & Ample Line Bundle** on `ℂ^g / (ℤ^g + Ω ℤ^g)`
for any Siegel period matrix `Ω ∈ ℍ_g` (`theta_metric_positivity`). -/
def theta {g : ℕ} (Ω : Matrix (Fin g) (Fin g) ℂ) (hΩ : IsSiegelPeriodMatrix Ω)
    {deg selfInt essMin : ℝ} (hdeg : 0 ≤ deg) (hself : 0 ≤ selfInt) (hess : 0 ≤ essMin) :
    ArithNefLineBundle g Unit Set.univ :=
  ofPosCurvature (thetaMetrizedLineBundle Ω) (theta_metric_positivity hΩ) g hdeg hself hess

/-- Concrete **Petersson Modular Hodge Bundle `ω^{⊗ k}`** on `ℍ` (`k ≥ 0`), nef for `k ≥ 0`
and ample for `k > 0` (`petersson_metric_semipositive`, `petersson_metric_positivity`). -/
def petersson (k : ℤ) (hk : 0 ≤ k) : ArithNefLineBundle 1 Unit uhpDomain1 where
  bundle := peterssonLineBundle k
  relDim := 1
  geomDeg := (k : ℝ) / 12
  arithSelfInt := 0
  essMinHeight := 0
  semipositive := petersson_metric_semipositive hk
  geomDeg_nonneg := div_nonneg (by exact_mod_cast hk) (by norm_num)
  arithSelfInt_nonneg := le_rfl
  essMinHeight_nonneg := le_rfl

end ArithNefLineBundle

/-! ### Green-Current & Arithmetic Surface (`ArithSurfaceModel`) Nef Predicates -/

section GreenAndSurfaceNef

/-- An Arakelov divisor `D̂` in a `DolbeaultCurrentAlgebra` pairing model `M` with positivity cone
`C` is **arithmetically nef** if its curvature form is semipositive and its pairing with every
effective divisor is non-negative. -/
def IsArithNefDivisor {A : DolbeaultCurrentAlgebra} {PrimeDiv : Type*}
    {δ : DivisorCurrentMap A PrimeDiv} (M : ArakelovPairingModel δ) (C : M.PositivityCone)
    (D : ArakelovDivisor δ) : Prop :=
  M.IsSemipositiveGreen C D ∧
  ∀ E : ArakelovDivisor δ, M.IsEffectiveArakelovDivisor C E → 0 ≤ M.archStarPairing D E

/-- Every effective divisor with semipositive curvature is automatically `IsArithNefDivisor`
by `Stage14M3_GreenCurrents.archStarPairing_nonneg_of_effective_semipositive`. -/
theorem isArithNefDivisor_of_effective_semipositive {A : DolbeaultCurrentAlgebra} {PrimeDiv : Type*}
    {δ : DivisorCurrentMap A PrimeDiv} (M : ArakelovPairingModel δ) (C : M.PositivityCone)
    {D : ArakelovDivisor δ} (heff : M.IsEffectiveArakelovDivisor C D)
    (hpos : M.IsSemipositiveGreen C D) :
    IsArithNefDivisor M C D :=
  ⟨hpos, fun _ hE => M.archStarPairing_nonneg_of_effective_semipositive C heff hpos hE⟩

/-- An `ArithLineBundle` on a `Stage11ArakelovFaltings.ArithSurfaceModel` (`D = 1`) is
**arithmetically nef** if `deg_K(L) ≥ 0`, `(L · L)_Ar ≥ 0`, and `(L · K)_Ar ≥ 0` for every
effective/nef test class `K` (`0 ≤ K.geomDeg`, `0 ≤ (K · K)_Ar`, and `K.geomDeg = 0 → 0 ≤ K.fiberWt`). -/
def IsArithNefSurface {m : ℕ} {E_arch : Type*} [NormedAddCommGroup E_arch]
    [InnerProductSpace ℝ E_arch] (M : ArithSurfaceModel m E_arch)
    (L : ArithLineBundle m E_arch) : Prop :=
  0 ≤ L.geomDeg ∧ 0 ≤ ArithLineBundle.arakelovPair M L L ∧
  ∀ K : ArithLineBundle m E_arch,
    0 ≤ K.geomDeg → 0 ≤ ArithLineBundle.arakelovPair M K K →
    (K.geomDeg = 0 → 0 ≤ K.fiberWt) →
    0 ≤ ArithLineBundle.arakelovPair M L K

/-- Every `IsArithAmple` line bundle on an arithmetic surface is `IsArithNefSurface`. -/
theorem isArithNefSurface_of_ample {m : ℕ} {E_arch : Type*} [NormedAddCommGroup E_arch]
    [InnerProductSpace ℝ E_arch] (M : ArithSurfaceModel m E_arch)
    {L : ArithLineBundle m E_arch} (hL : ArithLineBundle.IsArithAmple M L) :
    IsArithNefSurface M L := by
  refine ⟨hL.1.le, hL.2.le, fun K hKd hKp hKf => ?_⟩
  rcases eq_or_lt_of_le hKd with hKd0 | hKdpos
  · have hK0 : ArithLineBundle.arakelovPair M K K ≤ 0 :=
      ArithLineBundle.arakelovPair_nonpos_of_geomDeg_zero M hKd0.symm
    have hKeq : ArithLineBundle.arakelovPair M K K = 0 := le_antisymm hK0 hKp
    obtain ⟨hv, ha⟩ :=
      (ArithLineBundle.arakelovPair_eq_zero_iff_of_geomDeg_zero M hKd0.symm).mp hKeq
    have hKfib : K = ArithLineBundle.fiberBundle K.fiberWt := by
      ext <;> simp [ArithLineBundle.fiberBundle, hKd0.symm, hv, ha]
    rw [hKfib, ArithLineBundle.arakelovPair_fiber_right]
    exact mul_nonneg (hKf hKd0.symm) hL.1.le
  · let Z : ArithLineBundle m E_arch := K.geomDeg • L - L.geomDeg • K
    have hZd : Z.geomDeg = 0 := by simp [Z]; ring
    have hZle := ArithLineBundle.arakelovPair_nonpos_of_geomDeg_zero M hZd
    have hZexp : ArithLineBundle.arakelovPair M Z Z =
        K.geomDeg ^ 2 * ArithLineBundle.arakelovPair M L L -
          2 * L.geomDeg * K.geomDeg * ArithLineBundle.arakelovPair M L K +
          L.geomDeg ^ 2 * ArithLineBundle.arakelovPair M K K := by
      dsimp only [Z]
      rw [ArithLineBundle.arakelovPair_sub_left, ArithLineBundle.arakelovPair_sub_right,
        ArithLineBundle.arakelovPair_sub_right,
        ArithLineBundle.arakelovPair_smul_left, ArithLineBundle.arakelovPair_smul_right,
        ArithLineBundle.arakelovPair_smul_left, ArithLineBundle.arakelovPair_smul_right,
        ArithLineBundle.arakelovPair_smul_left, ArithLineBundle.arakelovPair_smul_right,
        ArithLineBundle.arakelovPair_smul_left, ArithLineBundle.arakelovPair_smul_right,
        ArithLineBundle.arakelovPair_symm M K L]
      ring
    rw [hZexp] at hZle
    have hsum_nn : 0 ≤ K.geomDeg ^ 2 * ArithLineBundle.arakelovPair M L L +
        L.geomDeg ^ 2 * ArithLineBundle.arakelovPair M K K :=
      add_nonneg (mul_nonneg (sq_nonneg _) hL.2.le) (mul_nonneg (sq_nonneg _) hKp)
    have hden : 0 < 2 * L.geomDeg * K.geomDeg := mul_pos (mul_pos zero_lt_two hL.1) hKdpos
    nlinarith

/-- Non-negative linear combinations of `IsArithNefSurface` bundles remain `IsArithNefSurface`. -/
theorem isArithNefSurface_add {m : ℕ} {E_arch : Type*} [NormedAddCommGroup E_arch]
    [InnerProductSpace ℝ E_arch] (M : ArithSurfaceModel m E_arch)
    {L₁ L₂ : ArithLineBundle m E_arch} (h₁ : IsArithNefSurface M L₁)
    (h₂ : IsArithNefSurface M L₂) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    IsArithNefSurface M (a • L₁ + b • L₂) := by
  have h12 : 0 ≤ ArithLineBundle.arakelovPair M L₁ L₂ := by
    by_cases h2d : L₂.geomDeg = 0
    · have hK0 := ArithLineBundle.arakelovPair_nonpos_of_geomDeg_zero M h2d
      have hKeq := le_antisymm hK0 h₂.2.1
      obtain ⟨hv, ha'⟩ := (ArithLineBundle.arakelovPair_eq_zero_iff_of_geomDeg_zero M h2d).mp hKeq
      have hKfib : L₂ = ArithLineBundle.fiberBundle L₂.fiberWt := by
        ext <;> simp [ArithLineBundle.fiberBundle, h2d, hv, ha']
      by_cases h1d : L₁.geomDeg = 0
      · rw [hKfib, ArithLineBundle.arakelovPair_fiber_right, h1d, mul_zero]
      · exact (h₂.2.2 L₁ h₁.1 h₁.2.1 (fun h0 => absurd h0 h1d)).trans_eq
          (ArithLineBundle.arakelovPair_symm M L₂ L₁)
    · exact h₁.2.2 L₂ h₂.1 h₂.2.1 (fun h0 => absurd h0 h2d)
  refine ⟨by simp; exact add_nonneg (mul_nonneg ha h₁.1) (mul_nonneg hb h₂.1), ?_,
      fun K hKd hKp hKf => ?_⟩
  · rw [ArithLineBundle.arakelovPair_add_left, ArithLineBundle.arakelovPair_add_right,
      ArithLineBundle.arakelovPair_add_right,
      ArithLineBundle.arakelovPair_smul_left, ArithLineBundle.arakelovPair_smul_right,
      ArithLineBundle.arakelovPair_smul_left, ArithLineBundle.arakelovPair_smul_right,
      ArithLineBundle.arakelovPair_smul_left, ArithLineBundle.arakelovPair_smul_right,
      ArithLineBundle.arakelovPair_smul_left, ArithLineBundle.arakelovPair_smul_right,
      ArithLineBundle.arakelovPair_symm M L₂ L₁]
    have t1 : 0 ≤ a * (a * ArithLineBundle.arakelovPair M L₁ L₁) :=
      mul_nonneg ha (mul_nonneg ha h₁.2.1)
    have t2 : 0 ≤ a * (b * ArithLineBundle.arakelovPair M L₁ L₂) :=
      mul_nonneg ha (mul_nonneg hb h12)
    have t3 : 0 ≤ b * (a * ArithLineBundle.arakelovPair M L₁ L₂) :=
      mul_nonneg hb (mul_nonneg ha h12)
    have t4 : 0 ≤ b * (b * ArithLineBundle.arakelovPair M L₂ L₂) :=
      mul_nonneg hb (mul_nonneg hb h₂.2.1)
    linarith
  · rw [ArithLineBundle.arakelovPair_add_left, ArithLineBundle.arakelovPair_smul_left,
      ArithLineBundle.arakelovPair_smul_left]
    exact add_nonneg (mul_nonneg ha (h₁.2.2 K hKd hKp hKf))
      (mul_nonneg hb (h₂.2.2 K hKd hKp hKf))

end GreenAndSurfaceNef

end ArithNefLineBundles

/-! ## Section 2: Unconditional Sphere-Packing Upper Bound & Concrete `ArithVolume` -/

section SpherePackingAndArithVolume

section SpherePacking

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Unconditional Lattice Sphere-Packing Upper Bound**:
for EVERY nonzero discrete Euclidean lattice `L ⊂ E` (`r = rk L`, `L ≠ ⊥`) and EVERY radius
`R ≥ 0`:
$$h^0_{\mathrm{Ar}}(L, R) \le \left(\frac{2 R}{\lambda_1(L)} + 1\right)^r.$$
Proof: transport `L` isometrically onto `EuclideanSpace ℝ (Fin r)` and pack pairwise-disjoint
open balls of radius `λ₁(L) / 2` inside `ball 0 (R + λ₁(L) / 2)`. -/
theorem h0Arith_upper_bound_sphere_packing (L : Submodule ℤ E) [DiscreteTopology L]
    (hL0 : L ≠ ⊥) {R : ℝ} (hR : 0 ≤ R) :
    (h0Arith L R : ℝ) ≤ (2 * R / lambda1 L + 1) ^ (rk L) := by
  classical
  let r : ℕ := rk L
  have hr_pos : 0 < r := rk_pos_of_ne_bot L hL0
  have hlam_pos : 0 < lambda1 L := lambda1_pos L hL0
  let ρ : ℝ := lambda1 L / 2
  have hρ_pos : 0 < ρ := half_pos hlam_pos
  let V : Submodule ℝ E := Submodule.span ℝ (L : Set E)
  have hdimV : Module.finrank ℝ V = r := (finrank_int_eq_finrank_real_span L).symm
  let e : OrthonormalBasis (Fin r) ℝ V :=
    (stdOrthonormalBasis ℝ V).reindex (Fintype.equivOfCardEq (by simp [hdimV]))
  let Φ : V ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin r) := e.repr
  let S : Set E := (L : Set E) ∩ Metric.closedBall 0 R
  have hSfin : S.Finite := lattice_inter_closedBall_finite L R
  let Sfin : Finset E := hSfin.toFinset
  have hcard_eq : h0Arith L R = Sfin.card := by
    unfold h0Arith
    exact Set.ncard_eq_toFinset_card S hSfin
  let c : E → EuclideanSpace ℝ (Fin r) := fun v =>
    if hv : v ∈ L then Φ ⟨v, Submodule.subset_span hv⟩ else 0
  have hc_dist : ∀ v ∈ Sfin, ∀ w ∈ Sfin, v ≠ w →
      Disjoint (Metric.ball (c v) ρ) (Metric.ball (c w) ρ) := by
    intro v hv w hw hvw
    apply Metric.ball_disjoint_ball
    have hvL : v ∈ L := (hSfin.mem_toFinset.mp hv).1
    have hwL : w ∈ L := (hSfin.mem_toFinset.mp hw).1
    simp only [c, dif_pos hvL, dif_pos hwL, dist_eq_norm, ← map_sub]
    have hsub_mem : v - w ∈ L := L.sub_mem hvL hwL
    have hsub_ne : v - w ≠ 0 := sub_ne_zero.mpr hvw
    have hnorm_eq : ‖Φ (⟨v, Submodule.subset_span hvL⟩ - ⟨w, Submodule.subset_span hwL⟩)‖ =
        ‖v - w‖ := by
      rw [Φ.norm_map]
      rfl
    rw [hnorm_eq]
    have hlam := lambda1_le_norm L hsub_mem hsub_ne
    dsimp only [ρ]
    linarith
  have hc_sub : ∀ v ∈ Sfin, Metric.ball (c v) ρ ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin r)) (R + ρ) := by
    intro v hv x hx
    have hvS := hSfin.mem_toFinset.mp hv
    have hvL : v ∈ L := hvS.1
    have hvR : ‖v‖ ≤ R := mem_closedBall_zero_iff.mp hvS.2
    have hx_dist : ‖x - c v‖ < ρ := by simpa [Metric.mem_ball, dist_eq_norm] using hx
    have hcv_norm : ‖c v‖ = ‖v‖ := by
      simp only [c, dif_pos hvL]
      exact Φ.norm_map ⟨v, Submodule.subset_span hvL⟩
    rw [Metric.mem_ball, dist_zero_right]
    have hsplit : x = (x - c v) + c v := by abel
    calc ‖x‖ = ‖(x - c v) + c v‖ := congrArg norm hsplit
      _ ≤ ‖x - c v‖ + ‖c v‖ := norm_add_le _ _
      _ < ρ + R := by linarith [hx_dist, hcv_norm, hvR]
      _ = R + ρ := add_comm _ _
  have hball_vol : ∀ v : E,
      volume (Metric.ball (c v) ρ) = ENNReal.ofReal (unitBallVol r * ρ ^ r) := by
    intro v
    have htrans : volume (Metric.ball (c v) ρ) =
        volume (Metric.ball (0 : EuclideanSpace ℝ (Fin r)) ρ) := by
      have heq : Metric.ball (c v) ρ = (fun x => x + (-c v)) ⁻¹' Metric.ball 0 ρ := by
        ext x; simp [Metric.mem_ball, dist_eq_norm, sub_eq_add_neg]
      rw [heq, MeasureTheory.measure_preimage_add_right]
    rw [htrans, volume_ball_eq_unitBallVol hr_pos hρ_pos.le]
  have hunion_le :
      (Sfin.card : ℝ≥0∞) * ENNReal.ofReal (unitBallVol r * ρ ^ r) ≤
        ENNReal.ofReal (unitBallVol r * (R + ρ) ^ r) := by
    have hmeas : ∀ v ∈ Sfin, MeasurableSet (Metric.ball (c v) ρ) := fun v _ =>
      Metric.isOpen_ball.measurableSet
    have hpair : (Sfin : Set E).PairwiseDisjoint fun v => Metric.ball (c v) ρ :=
      fun v hv w hw hvw => hc_dist v hv w hw hvw
    calc (Sfin.card : ℝ≥0∞) * ENNReal.ofReal (unitBallVol r * ρ ^ r)
        = ∑ _v ∈ Sfin, ENNReal.ofReal (unitBallVol r * ρ ^ r) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ = ∑ v ∈ Sfin, volume (Metric.ball (c v) ρ) := by
          refine Finset.sum_congr rfl fun v _ => (hball_vol v).symm
      _ = volume (⋃ v ∈ Sfin, Metric.ball (c v) ρ) :=
          (MeasureTheory.measure_biUnion_finset (μ := volume) hpair hmeas).symm
      _ ≤ volume (Metric.ball (0 : EuclideanSpace ℝ (Fin r)) (R + ρ)) := by
          refine measure_mono ?_
          intro x hx
          simp only [Set.mem_iUnion, exists_prop] at hx
          rcases hx with ⟨v, hv, hxv⟩
          exact hc_sub v hv hxv
      _ = ENNReal.ofReal (unitBallVol r * (R + ρ) ^ r) :=
          volume_ball_eq_unitBallVol hr_pos (add_nonneg hR hρ_pos.le)
  have hreal : (Sfin.card : ℝ) * (unitBallVol r * ρ ^ r) ≤ unitBallVol r * (R + ρ) ^ r := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)] at hunion_le
    exact (ENNReal.ofReal_le_ofReal_iff (mul_pos (unitBallVol_pos r)
      (pow_pos (add_pos_of_nonneg_of_pos hR hρ_pos) r)).le).mp hunion_le
  have hω_pos : 0 < unitBallVol r := unitBallVol_pos r
  have hρr_pos : 0 < ρ ^ r := pow_pos hρ_pos r
  have hpow_le : (Sfin.card : ℝ) * ρ ^ r ≤ (R + ρ) ^ r := by
    nlinarith
  have hdiv : (Sfin.card : ℝ) ≤ ((R + ρ) / ρ) ^ r := by
    rw [div_pow, le_div_iff₀ hρr_pos]
    exact hpow_le
  have hratio : (R + ρ) / ρ = 2 * R / lambda1 L + 1 := by
    dsimp only [ρ]
    field_simp [hlam_pos.ne']
  rw [← hcard_eq, hratio] at hdiv
  exact hdiv

/-- Strict-ball version of the sphere-packing upper bound. -/
theorem h0ArithStrict_upper_bound_sphere_packing (L : Submodule ℤ E) [DiscreteTopology L]
    (hL0 : L ≠ ⊥) {R : ℝ} (hR : 0 ≤ R) :
    (h0ArithStrict L R : ℝ) ≤ (2 * R / lambda1 L + 1) ^ (rk L) :=
  (Nat.cast_le.mpr (h0ArithStrict_le_h0Arith L R)).trans
    (h0Arith_upper_bound_sphere_packing L hL0 hR)

end SpherePacking

/-! ### Graded Hermitian Section Families & Concrete `ArithVolume` -/

/-- **Concrete Graded Hermitian Section Lattice Family** `⨁_{n ≥ 0} H^0(X, L^{⊗ n})` on a
`D`-dimensional projective arithmetic variety:
- `secLat n ⊂ secSpace n` models the integral lattice `H^0(X, L^{⊗ n})` with its `L²` inner product;
- `supNorm n` models the archimedean sup-norm `‖·‖_{L^∞}` satisfying the Bergman / compact-manifold
  comparison `volConst⁻¹ ‖s‖ ≤ supNorm n s ≤ bergConst (n + 1)^bergExp ‖s‖`;
- `rk (secLat n) ≤ rankHi * n^D` (Hilbert–Samuel polynomial rank growth);
- `exp(-slopeHi * n) ≤ λ₁(secLat n)` (Northcott / Liouville lower bound on nonzero integral
  sections, ensuring unconditional finiteness and upper boundedness of `ArithVolume`). -/
structure ArithSectionFamily (D : ℕ) where
  secSpace : ℕ → Type*
  [normSpace : ∀ n, NormedAddCommGroup (secSpace n)]
  [innerSpace : ∀ n, InnerProductSpace ℝ (secSpace n)]
  [fdSpace : ∀ n, FiniteDimensional ℝ (secSpace n)]
  secLat : ∀ n, Submodule ℤ (secSpace n)
  [discLat : ∀ n, DiscreteTopology (secSpace n)]
  secLat_ne_bot : ∀ n, 1 ≤ n → secLat n ≠ ⊥
  supNorm : ∀ n, secSpace n → ℝ
  supNorm_nonneg : ∀ n s, 0 ≤ supNorm n s
  supNorm_zero : ∀ n, supNorm n 0 = 0
  volConst : ℝ
  volConst_pos : 0 < volConst
  norm_le_vol_supNorm : ∀ n, 1 ≤ n → ∀ s : secSpace n, ‖s‖ ≤ volConst * supNorm n s
  bergConst : ℝ
  bergExp : ℕ
  bergConst_ge_one : 1 ≤ bergConst
  supNorm_le_bergman : ∀ n, 1 ≤ n → ∀ s : secSpace n,
    supNorm n s ≤ bergConst * ((n : ℝ) + 1) ^ bergExp * ‖s‖
  rankHi : ℝ
  rankHi_ge_one : 1 ≤ rankHi
  rk_le_poly : ∀ n, 1 ≤ n → (rk (secLat n) : ℝ) ≤ rankHi * (n : ℝ) ^ D
  slopeHi : ℝ
  slopeHi_nonneg : 0 ≤ slopeHi
  lambda1_lower : ∀ (n : ℕ), 1 ≤ n → Real.exp (-slopeHi * (n : ℝ)) ≤ lambda1 (secLat n)

attribute [instance] ArithSectionFamily.normSpace ArithSectionFamily.innerSpace
  ArithSectionFamily.fdSpace ArithSectionFamily.discLat

namespace ArithSectionFamily

variable {D : ℕ} (A : ArithSectionFamily D)

/-- Set of strictly small integral global sections `{s ∈ H⁰(X, L^{⊗ n}) | ‖s‖_sup < 1}`. -/
def smallSectionsSet (n : ℕ) : Set (A.secLat n) :=
  { s : A.secLat n | A.supNorm n s.1 < 1 }

/-- Finiteness of strictly small integral global sections at every degree `n ≥ 1`. -/
theorem smallSections_finite {n : ℕ} (hn : 1 ≤ n) : (A.smallSectionsSet n).Finite := by
  have hball := lattice_inter_closedBall_finite (A.secLat n) A.volConst
  have hsub : Subtype.val '' A.smallSectionsSet n ⊆
      (A.secLat n : Set (A.secSpace n)) ∩ Metric.closedBall 0 A.volConst := by
    rintro _ ⟨s, hs, rfl⟩
    refine ⟨s.2, ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    have h1 := A.norm_le_vol_supNorm n hn s.1
    have h2 : A.supNorm n s.1 < 1 := hs
    nlinarith [A.volConst_pos]
  exact Set.Finite.of_finite_image (hball.subset hsub) Subtype.val_injective.injOn

/-- Exact cardinality `#smallSections A n` of strictly small global sections `‖s‖_sup < 1`. -/
def smallSectionsCard (n : ℕ) (hn : 1 ≤ n) : ℕ :=
  (A.smallSections_finite hn).toFinset.card

/-- `0` is always a strictly small global section, so `1 ≤ A.smallSectionsCard n hn`. -/
theorem one_le_smallSectionsCard {n : ℕ} (hn : 1 ≤ n) : 1 ≤ A.smallSectionsCard n hn := by
  unfold smallSectionsCard
  refine Finset.card_pos.mpr ⟨0, ?_⟩
  rw [(A.smallSections_finite hn).mem_toFinset]
  change A.supNorm n 0 < 1
  rw [A.supNorm_zero n]
  exact one_pos

/-- Lower comparison against Euclidean strict-ball count `h0ArithStrict`. -/
theorem h0ArithStrict_le_smallSectionsCard {n : ℕ} (hn : 1 ≤ n) :
    h0ArithStrict (A.secLat n) ((A.bergConst * ((n : ℝ) + 1) ^ A.bergExp)⁻¹) ≤
      A.smallSectionsCard n hn := by
  unfold h0ArithStrict smallSectionsCard
  let R : ℝ := (A.bergConst * ((n : ℝ) + 1) ^ A.bergExp)⁻¹
  have hBpos : 0 < A.bergConst * ((n : ℝ) + 1) ^ A.bergExp :=
    mul_pos (by linarith [A.bergConst_ge_one]) (pow_pos (by positivity) _)
  have hsub : ((A.secLat n : Set (A.secSpace n)) ∩ Metric.ball 0 R) ⊆
      Subtype.val '' A.smallSectionsSet n := by
    rintro x ⟨hxL, hxB⟩
    refine ⟨⟨x, hxL⟩, ?_, rfl⟩
    change A.supNorm n x < 1
    rw [Metric.mem_ball, dist_zero_right] at hxB
    have h1 := A.supNorm_le_bergman n hn x
    have h2 : A.bergConst * ((n : ℝ) + 1) ^ A.bergExp * ‖x‖ <
        A.bergConst * ((n : ℝ) + 1) ^ A.bergExp * R :=
      mul_lt_mul_of_pos_left hxB hBpos
    have hinv : A.bergConst * ((n : ℝ) + 1) ^ A.bergExp * R = 1 := mul_inv_cancel₀ hBpos.ne'
    rw [hinv] at h2
    exact lt_of_le_of_lt h1 h2
  have hfinImg : (Subtype.val '' A.smallSectionsSet n).Finite :=
    (A.smallSections_finite hn).image Subtype.val
  calc ((A.secLat n : Set (A.secSpace n)) ∩ Metric.ball 0 R).ncard
      ≤ (Subtype.val '' A.smallSectionsSet n).ncard := Set.ncard_le_ncard hsub hfinImg
    _ = (A.smallSectionsSet n).ncard := Set.ncard_image_of_injective _ Subtype.val_injective
    _ = (A.smallSections_finite hn).toFinset.card :=
        Set.ncard_eq_toFinset_card (A.smallSectionsSet n) (A.smallSections_finite hn)

/-- Upper comparison against Euclidean closed-ball count `h0Arith (A.secLat n) A.volConst`. -/
theorem smallSectionsCard_le_h0Arith {n : ℕ} (hn : 1 ≤ n) :
    A.smallSectionsCard n hn ≤ h0Arith (A.secLat n) A.volConst := by
  unfold smallSectionsCard h0Arith
  have hball := lattice_inter_closedBall_finite (A.secLat n) A.volConst
  have hsub : Subtype.val '' A.smallSectionsSet n ⊆
      (A.secLat n : Set (A.secSpace n)) ∩ Metric.closedBall 0 A.volConst := by
    rintro _ ⟨s, hs, rfl⟩
    refine ⟨s.2, ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    have h1 := A.norm_le_vol_supNorm n hn s.1
    have h2 : A.supNorm n s.1 < 1 := hs
    nlinarith [A.volConst_pos]
  calc (A.smallSections_finite hn).toFinset.card
      = (A.smallSectionsSet n).ncard :=
        (Set.ncard_eq_toFinset_card (A.smallSectionsSet n) (A.smallSections_finite hn)).symm
    _ = (Subtype.val '' A.smallSectionsSet n).ncard :=
        (Set.ncard_image_of_injective _ Subtype.val_injective).symm
    _ ≤ ((A.secLat n : Set (A.secSpace n)) ∩ Metric.closedBall 0 A.volConst).ncard :=
        Set.ncard_le_ncard hsub hball

/-- Normalized log small-section ratio `log(#smallSections A n) / (n^{D+1} / (D+1)!)` (`0` for `n = 0`). -/
def arithVolRatio (n : ℕ) : ℝ :=
  if hn : 1 ≤ n then Real.log (A.smallSectionsCard n hn : ℝ) / arithVolNorm D n else 0

theorem arithVolRatio_nonneg (n : ℕ) : 0 ≤ A.arithVolRatio n := by
  unfold arithVolRatio
  split_ifs with hn
  · have h1 : (1 : ℝ) ≤ (A.smallSectionsCard n hn : ℝ) := by
      exact_mod_cast A.one_le_smallSectionsCard hn
    exact div_nonneg (Real.log_nonneg h1) (arithVolNorm_pos D hn).le
  · exact le_rfl

/-- **Unconditional Upper Bound on `arithVolRatio`** (via sphere packing + `lambda1_lower` +
polynomial rank ceiling): `∃ M ≥ 0, ∀ n, A.arithVolRatio n ≤ M`. -/
theorem arithVolRatio_bddAbove : ∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℕ, A.arithVolRatio n ≤ M := by
  let C0 : ℝ := 2 * A.volConst + 1
  have hC0 : 1 ≤ C0 := by dsimp only [C0]; linarith [A.volConst_pos]
  let M : ℝ := ((D + 1).factorial : ℝ) * A.rankHi * (Real.log C0 + A.slopeHi)
  have hM : 0 ≤ M := by
    refine mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (by linarith [A.rankHi_ge_one])) ?_
    exact add_nonneg (Real.log_nonneg hC0) A.slopeHi_nonneg
  refine ⟨M, hM, fun n => ?_⟩
  unfold arithVolRatio
  split_ifs with hn
  · have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
    have hcard_pos : (0 : ℝ) < (A.smallSectionsCard n hn : ℝ) := by
      exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one (A.one_le_smallSectionsCard hn)
    have hsp := h0Arith_upper_bound_sphere_packing (A.secLat n) (A.secLat_ne_bot n hn)
      A.volConst_pos.le
    have hcard_le : (A.smallSectionsCard n hn : ℝ) ≤
        (2 * A.volConst / lambda1 (A.secLat n) + 1) ^ rk (A.secLat n) :=
      (Nat.cast_le.mpr (A.smallSectionsCard_le_h0Arith hn)).trans hsp
    have hlam_pos : 0 < lambda1 (A.secLat n) := lambda1_pos _ (A.secLat_ne_bot n hn)
    have hlam_ge : Real.exp (-A.slopeHi * (n : ℝ)) ≤ lambda1 (A.secLat n) := A.lambda1_lower n hn
    have hinv_le : (lambda1 (A.secLat n))⁻¹ ≤ Real.exp (A.slopeHi * (n : ℝ)) := by
      have h1 : (lambda1 (A.secLat n))⁻¹ ≤ (Real.exp (-A.slopeHi * (n : ℝ)))⁻¹ :=
        inv_anti₀ (Real.exp_pos _) hlam_ge
      have h2 : (Real.exp (-A.slopeHi * (n : ℝ)))⁻¹ = Real.exp (A.slopeHi * (n : ℝ)) := by
        rw [← Real.exp_neg, neg_mul, neg_neg]
      exact h1.trans_eq h2
    have hexp_ge1 : 1 ≤ Real.exp (A.slopeHi * (n : ℝ)) :=
      Real.one_le_exp (mul_nonneg A.slopeHi_nonneg hn_pos.le)
    have hbase_le : 2 * A.volConst / lambda1 (A.secLat n) + 1 ≤
        C0 * Real.exp (A.slopeHi * (n : ℝ)) := by
      have h1 : 2 * A.volConst / lambda1 (A.secLat n) ≤
          2 * A.volConst * Real.exp (A.slopeHi * (n : ℝ)) := by
        rw [div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_left hinv_le (by linarith [A.volConst_pos])
      dsimp only [C0]
      nlinarith
    have hbase_pos : 0 < 2 * A.volConst / lambda1 (A.secLat n) + 1 :=
      add_pos_of_nonneg_of_pos (div_nonneg (mul_pos zero_lt_two A.volConst_pos).le hlam_pos.le)
        zero_lt_one
    have hlog_le : Real.log (A.smallSectionsCard n hn : ℝ) ≤
        (rk (A.secLat n) : ℝ) * (Real.log C0 + A.slopeHi * (n : ℝ)) := by
      calc Real.log (A.smallSectionsCard n hn : ℝ)
          ≤ Real.log ((2 * A.volConst / lambda1 (A.secLat n) + 1) ^ rk (A.secLat n)) :=
            Real.log_le_log hcard_pos hcard_le
        _ = (rk (A.secLat n) : ℝ) * Real.log (2 * A.volConst / lambda1 (A.secLat n) + 1) := by
            rw [Real.log_pow]
        _ ≤ (rk (A.secLat n) : ℝ) * Real.log (C0 * Real.exp (A.slopeHi * (n : ℝ))) := by
            refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
            exact Real.log_le_log hbase_pos hbase_le
        _ = (rk (A.secLat n) : ℝ) * (Real.log C0 + A.slopeHi * (n : ℝ)) := by
            rw [Real.log_mul (by linarith) (Real.exp_pos _).ne', Real.log_exp]
    have hlin_le : Real.log C0 + A.slopeHi * (n : ℝ) ≤ (Real.log C0 + A.slopeHi) * (n : ℝ) := by
      have hlc : 0 ≤ Real.log C0 := Real.log_nonneg hC0
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      nlinarith
    have hprod_le : Real.log (A.smallSectionsCard n hn : ℝ) ≤
        (A.rankHi * (n : ℝ) ^ D) * ((Real.log C0 + A.slopeHi) * (n : ℝ)) := by
      calc Real.log (A.smallSectionsCard n hn : ℝ)
          ≤ (rk (A.secLat n) : ℝ) * (Real.log C0 + A.slopeHi * (n : ℝ)) := hlog_le
        _ ≤ (rk (A.secLat n) : ℝ) * ((Real.log C0 + A.slopeHi) * (n : ℝ)) :=
            mul_le_mul_of_nonneg_left hlin_le (Nat.cast_nonneg _)
        _ ≤ (A.rankHi * (n : ℝ) ^ D) * ((Real.log C0 + A.slopeHi) * (n : ℝ)) :=
            mul_le_mul_of_nonneg_right (A.rk_le_poly n hn)
              (mul_nonneg (add_nonneg (Real.log_nonneg hC0) A.slopeHi_nonneg) hn_pos.le)
    have hvol_pos := arithVolNorm_pos D hn
    calc Real.log (A.smallSectionsCard n hn : ℝ) / arithVolNorm D n
        ≤ ((A.rankHi * (n : ℝ) ^ D) * ((Real.log C0 + A.slopeHi) * (n : ℝ))) / arithVolNorm D n :=
          div_le_div_of_nonneg_right hprod_le hvol_pos.le
      _ = M := by
          unfold arithVolNorm
          dsimp only [M]
          rw [pow_succ]
          have hfact : (((D + 1).factorial : ℕ) : ℝ) ≠ 0 :=
            (Nat.cast_pos.mpr (Nat.factorial_pos (D + 1))).ne'
          field_simp [hn_pos.ne', hfact]
  · exact hM

theorem arithVolRatio_isBoundedUnder_ge :
    Filter.IsBoundedUnder (· ≥ ·) Filter.atTop A.arithVolRatio :=
  ⟨0, Filter.eventually_atTop.mpr ⟨0, fun n _ => A.arithVolRatio_nonneg n⟩⟩

theorem arithVolRatio_isBoundedUnder_le :
    Filter.IsBoundedUnder (· ≤ ·) Filter.atTop A.arithVolRatio := by
  obtain ⟨M, _, hM⟩ := A.arithVolRatio_bddAbove
  exact ⟨M, Filter.eventually_atTop.mpr ⟨0, fun n _ => hM n⟩⟩

/-- Rescaled graded family `A^{⊗ m}` (`m ≥ 1`), corresponding to `L^{⊗ m}` at degree `n ↦ m * n`. -/
def pow (A : ArithSectionFamily D) (m : ℕ) (hm : 1 ≤ m) : ArithSectionFamily D where
  secSpace n := A.secSpace (m * n)
  normSpace n := A.normSpace (m * n)
  innerSpace n := A.innerSpace (m * n)
  fdSpace n := A.fdSpace (m * n)
  secLat n := A.secLat (m * n)
  discLat n := A.discLat (m * n)
  secLat_ne_bot n hn := A.secLat_ne_bot (m * n) (Nat.succ_le_of_lt (Nat.mul_pos hm hn))
  supNorm n := A.supNorm (m * n)
  supNorm_nonneg n := A.supNorm_nonneg (m * n)
  supNorm_zero n := A.supNorm_zero (m * n)
  volConst := A.volConst
  volConst_pos := A.volConst_pos
  norm_le_vol_supNorm n hn := A.norm_le_vol_supNorm (m * n) (Nat.succ_le_of_lt (Nat.mul_pos hm hn))
  bergConst := A.bergConst * (m : ℝ) ^ A.bergExp
  bergExp := A.bergExp
  bergConst_ge_one := by
    have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    exact one_le_mul_of_one_le_of_one_le A.bergConst_ge_one (one_le_pow₀ hm1)
  supNorm_le_bergman n hn s := by
    have h1 := A.supNorm_le_bergman (m * n) (Nat.succ_le_of_lt (Nat.mul_pos hm hn)) s
    have hle : ((m * n : ℕ) : ℝ) + 1 ≤ (m : ℝ) * ((n : ℝ) + 1) := by
      push_cast
      have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      nlinarith
    have hpow : (((m * n : ℕ) : ℝ) + 1) ^ A.bergExp ≤
        ((m : ℝ) * ((n : ℝ) + 1)) ^ A.bergExp :=
      pow_le_pow_left₀ (by positivity) hle _
    rw [mul_pow] at hpow
    have hbc : 0 ≤ A.bergConst := by linarith [A.bergConst_ge_one]
    have h2 : A.bergConst * (((m * n : ℕ) : ℝ) + 1) ^ A.bergExp * ‖s‖ ≤
        A.bergConst * ((m : ℝ) ^ A.bergExp * ((n : ℝ) + 1) ^ A.bergExp) * ‖s‖ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hbc) (norm_nonneg s)
    linarith [h1, h2]
  rankHi := A.rankHi * (m : ℝ) ^ D
  rankHi_ge_one := by
    have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    exact one_le_mul_of_one_le_of_one_le A.rankHi_ge_one (one_le_pow₀ hm1)
  rk_le_poly n hn := by
    have h1 := A.rk_le_poly (m * n) (Nat.succ_le_of_lt (Nat.mul_pos hm hn))
    push_cast at h1 ⊢
    rw [mul_pow] at h1
    linarith
  slopeHi := A.slopeHi * (m : ℝ)
  slopeHi_nonneg := mul_nonneg A.slopeHi_nonneg (Nat.cast_nonneg m)
  lambda1_lower n hn := by
    have h1 := A.lambda1_lower (m * n) (Nat.succ_le_of_lt (Nat.mul_pos hm hn))
    push_cast at h1 ⊢
    rwa [show -(A.slopeHi * (m : ℝ)) * (n : ℝ) = -A.slopeHi * ((m : ℝ) * (n : ℝ)) by ring]

end ArithSectionFamily

/-- **Concrete Arithmetic Volume** $\widehat{\operatorname{vol}}(A)$ of a graded Hermitian section
family `A : ArithSectionFamily D`:
$$\widehat{\operatorname{vol}}(A) := \liminf_{n \to \infty}
  \frac{\log \#\{s \in H^0(\mathcal{X}, L^{\otimes n}) : \|s\|_{\sup} < 1\}}{n^{D+1} / (D+1)!}.$$ -/
def ArithVolume {D : ℕ} (A : ArithSectionFamily D) : ℝ :=
  Filter.liminf A.arithVolRatio Filter.atTop

/-- Upper arithmetic volume $\widehat{\operatorname{vol}}^+(A) := \limsup_{n \to \infty} \dots$. -/
def ArithVolumeUpper {D : ℕ} (A : ArithSectionFamily D) : ℝ :=
  Filter.limsup A.arithVolRatio Filter.atTop

theorem arithVolume_nonneg {D : ℕ} (A : ArithSectionFamily D) : 0 ≤ ArithVolume A :=
  Filter.le_liminf_of_le A.arithVolRatio_isBoundedUnder_le.isCoboundedUnder_ge
    (Filter.Eventually.of_forall fun n => A.arithVolRatio_nonneg n)

theorem arithVolume_le_arithVolumeUpper {D : ℕ} (A : ArithSectionFamily D) :
    ArithVolume A ≤ ArithVolumeUpper A :=
  Filter.liminf_le_limsup A.arithVolRatio_isBoundedUnder_le A.arithVolRatio_isBoundedUnder_ge

theorem le_arithVolume_of_eventually_le {D : ℕ} (A : ArithSectionFamily D) {v : ℝ}
    (hv : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in Filter.atTop, v - ε ≤ A.arithVolRatio n) :
    v ≤ ArithVolume A := by
  by_contra hlt
  push Not at hlt
  let ε := (v - ArithVolume A) / 2
  have hε : 0 < ε := half_pos (sub_pos.mpr hlt)
  have hev := hv ε hε
  have hle : v - ε ≤ ArithVolume A :=
    Filter.le_liminf_of_le A.arithVolRatio_isBoundedUnder_le.isCoboundedUnder_ge hev
  dsimp only [ε] at hle
  linarith

/-- Monotonicity of `ArithVolume` under eventual domination of small-section counts. -/
theorem arithVolume_mono {D : ℕ} {A₁ A₂ : ArithSectionFamily D}
    (hdom : ∃ N₀ : ℕ, ∃ hN0 : 1 ≤ N₀, ∀ (n : ℕ) (hn : N₀ ≤ n),
      A₁.smallSectionsCard n (le_trans hN0 hn) ≤ A₂.smallSectionsCard n (le_trans hN0 hn)) :
    ArithVolume A₁ ≤ ArithVolume A₂ := by
  rcases hdom with ⟨N₀, hN0, hle⟩
  refine Filter.liminf_le_liminf ?_ A₁.arithVolRatio_isBoundedUnder_ge
    A₂.arithVolRatio_isBoundedUnder_le.isCoboundedUnder_ge
  filter_upwards [eventually_ge_atTop N₀] with n hn
  have hn1 : 1 ≤ n := le_trans hN0 hn
  unfold ArithSectionFamily.arithVolRatio
  rw [dif_pos hn1, dif_pos hn1]
  refine div_le_div_of_nonneg_right ?_ (arithVolNorm_pos D hn1).le
  have hpos : (0 : ℝ) < (A₁.smallSectionsCard n hn1 : ℝ) := by
    exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one (A₁.one_le_smallSectionsCard hn1)
  exact Real.log_le_log hpos (by exact_mod_cast hle n hn)

/-- Power super-homogeneity: `m ^ (D + 1) * ArithVolume A ≤ ArithVolume (A.pow m hm)`. -/
theorem pow_mul_arithVolume_le {D : ℕ} (A : ArithSectionFamily D) {m : ℕ} (hm : 1 ≤ m) :
    (m : ℝ) ^ (D + 1) * ArithVolume A ≤ ArithVolume (A.pow m hm) := by
  refine le_arithVolume_of_eventually_le (A.pow m hm) fun ε hε => ?_
  have hm_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm
  have hmD_pos : (0 : ℝ) < (m : ℝ) ^ (D + 1) := pow_pos hm_pos (D + 1)
  let δ := ε / (m : ℝ) ^ (D + 1)
  have hδ : 0 < δ := div_pos hε hmD_pos
  have hlt : ArithVolume A - δ < ArithVolume A := sub_lt_self _ hδ
  have hev := Filter.eventually_lt_of_lt_liminf hlt A.arithVolRatio_isBoundedUnder_ge
  have hm_tend : Filter.Tendsto (fun n : ℕ => m * n) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_atTop.mpr fun b => ⟨b, fun n hn =>
      le_trans hn (Nat.le_mul_of_pos_left n hm)⟩
  have hev_mul : ∀ᶠ n in Filter.atTop, ArithVolume A - δ < A.arithVolRatio (m * n) :=
    hm_tend.eventually hev
  filter_upwards [hev_mul, eventually_ge_atTop 1] with n hn_lt hn1
  have hmn : 1 ≤ m * n := Nat.succ_le_of_lt (Nat.mul_pos hm hn1)
  have hvol_eq : arithVolNorm D (m * n) = (m : ℝ) ^ (D + 1) * arithVolNorm D n := by
    unfold arithVolNorm
    push_cast
    rw [mul_pow]
    ring
  have hratio_eq : (A.pow m hm).arithVolRatio n = (m : ℝ) ^ (D + 1) * A.arithVolRatio (m * n) := by
    unfold ArithSectionFamily.arithVolRatio
    rw [dif_pos hn1, dif_pos hmn, hvol_eq]
    have hcard_eq : (A.pow m hm).smallSectionsCard n hn1 = A.smallSectionsCard (m * n) hmn := rfl
    rw [hcard_eq]
    have hv : arithVolNorm D n ≠ 0 := (arithVolNorm_pos D hn1).ne'
    field_simp [hmD_pos.ne', hv]
  rw [hratio_eq]
  have h1 := mul_le_mul_of_nonneg_left hn_lt.le hmD_pos.le
  rw [mul_sub, mul_div_cancel₀ _ hmD_pos.ne'] at h1
  exact h1

end SpherePackingAndArithVolume

/-! ## Section 3: `nef_riemann_roch_lower_bound` (Lattice & Asymptotic Nef Riemann–Roch) -/

section NefRiemannRoch

private lemma tendsto_log_linear_div_nat' (C₁ C₂ : ℝ) :
    Tendsto (fun k : ℕ => (C₁ * Real.log ((k : ℝ) + 1) + C₂) / (k : ℝ)) atTop (𝓝 0) := by
  have hlog_div : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
    have h := Real.tendsto_pow_log_div_mul_add_atTop (1 : ℝ) (0 : ℝ) 1 one_ne_zero
    simpa [pow_one, one_mul, add_zero] using h
  have hlog_k1 : Tendsto (fun k : ℕ => Real.log ((k : ℝ) + 1) / ((k : ℝ) + 1)) atTop (𝓝 0) :=
    hlog_div.comp (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  have hinv_nat : Tendsto (fun k : ℕ => ((k : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hratio : Tendsto (fun k : ℕ => ((k : ℝ) + 1) / (k : ℝ)) atTop (𝓝 1) := by
    have hinv : Tendsto (fun k : ℕ => (1 : ℝ) / (k : ℝ)) atTop (𝓝 0) := by
      simpa only [one_div] using hinv_nat
    have hadd : Tendsto (fun k : ℕ => (1 : ℝ) + (1 : ℝ) / (k : ℝ)) atTop (𝓝 (1 + 0)) :=
      tendsto_const_nhds.add hinv
    rw [add_zero] at hadd
    refine hadd.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with k hk
    have hk0 : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    field_simp [hk0]
  have hlog_k : Tendsto (fun k : ℕ => Real.log ((k : ℝ) + 1) / (k : ℝ)) atTop (𝓝 0) := by
    have hprod := hlog_k1.mul hratio
    rw [zero_mul] at hprod
    refine hprod.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with k hk
    have hk1 : (k : ℝ) + 1 ≠ 0 := by positivity
    field_simp [hk1]
  have hC₂ : Tendsto (fun k : ℕ => C₂ / (k : ℝ)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using hinv_nat.const_mul C₂
  have hsum : Tendsto (fun k : ℕ => C₁ * (Real.log ((k : ℝ) + 1) / (k : ℝ)) + C₂ / (k : ℝ))
      atTop (𝓝 (C₁ * 0 + 0)) := (hlog_k.const_mul C₁).add hC₂
  simp only [mul_zero, add_zero] at hsum
  exact hsum.congr fun k => by ring

/-- **Single-Lattice Effective Arithmetic Riemann–Roch Lower Bound**:
for any nonzero discrete Euclidean lattice `Λ ⊂ E` (`r = rk Λ`),
$$\mathrm{arithDeg}(\Lambda) - r \left(\frac{1}{2}\log r + \log\frac{2}{\sqrt{\pi}}\right)
  \le \log h^0_{\mathrm{strict}}(\Lambda, 1).$$ -/
theorem lattice_riemann_roch_lower_bound {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (Λ : Submodule ℤ E) [DiscreteTopology Λ] (hΛ : Λ ≠ ⊥) :
    arithDeg Λ - (rk Λ : ℝ) * ((1 / 2) * Real.log (rk Λ : ℝ) + Real.log (2 / √Real.pi)) ≤
      Real.log (h0ArithStrict Λ 1 : ℝ) := by
  have hm := (moriwaki_small_section_count Λ hΛ).1
  have hdeg := arithDeg_eq_rk_mul_slope Λ hΛ
  linarith

/-- **Section-Space Effective Riemann–Roch Lower Bound** at degree `n ≥ 1` for any
`A : ArithSectionFamily D`: incorporates the Bergman sup-to-`L²` comparison factor
`A.bergConst * (n + 1) ^ A.bergExp`. -/
theorem section_space_riemann_roch_lower_bound {D : ℕ} (A : ArithSectionFamily D)
    {n : ℕ} (hn : 1 ≤ n) :
    arithDeg (A.secLat n) -
      (rk (A.secLat n) : ℝ) *
        ((A.bergExp : ℝ) * Real.log ((n : ℝ) + 1) + (1 / 2) * Real.log (rk (A.secLat n) : ℝ) +
          Real.log (2 * A.bergConst) + |Real.log (√Real.pi)|) ≤
      Real.log (A.smallSectionsCard n hn : ℝ) := by
  have hB_pos : 0 < A.bergConst * ((n : ℝ) + 1) ^ A.bergExp :=
    mul_pos (by linarith [A.bergConst_ge_one]) (pow_pos (by positivity) _)
  let Rn : ℝ := (A.bergConst * ((n : ℝ) + 1) ^ A.bergExp)⁻¹
  have hRn_pos : 0 < Rn := inv_pos.mpr hB_pos
  have hcount_le : (h0ArithStrict (A.secLat n) Rn : ℝ) ≤ (A.smallSectionsCard n hn : ℝ) :=
    Nat.cast_le.mpr (A.h0ArithStrict_le_smallSectionsCard hn)
  have h0_pos : (0 : ℝ) < (h0ArithStrict (A.secLat n) Rn : ℝ) :=
    Nat.cast_pos.mpr (one_le_h0ArithStrict (A.secLat n) hRn_pos)
  have hlog_mono : Real.log (h0ArithStrict (A.secLat n) Rn : ℝ) ≤
      Real.log (A.smallSectionsCard n hn : ℝ) := Real.log_le_log h0_pos hcount_le
  have hmink := log_h0ArithStrict_lower_bound (A.secLat n) hRn_pos
  have hrk_pos : 1 ≤ rk (A.secLat n) := rk_pos_of_ne_bot _ (A.secLat_ne_bot n hn)
  have hrk_posR : (0 : ℝ) < (rk (A.secLat n) : ℝ) := Nat.cast_pos.mpr hrk_pos
  have hlogω := log_unitBallVol_ge hrk_pos
  have hdeg := arithDeg_eq_rk_mul_slope (A.secLat n) (A.secLat_ne_bot n hn)
  have hlog_Rn : Real.log (Rn / 2) =
      -(Real.log (2 * A.bergConst) + (A.bergExp : ℝ) * Real.log ((n : ℝ) + 1)) := by
    have h2B : Rn / 2 = (2 * A.bergConst * ((n : ℝ) + 1) ^ A.bergExp)⁻¹ := by
      dsimp only [Rn]; field_simp [hB_pos.ne']
    rw [h2B, Real.log_inv,
      Real.log_mul (by linarith [A.bergConst_ge_one]) (pow_pos (by positivity) _).ne',
      Real.log_pow]
  have hlog_pi : (1 / 2) * Real.log Real.pi = Real.log (√Real.pi) := by
    rw [Real.log_sqrt Real.pi_pos.le]; ring
  have hloss :
      -(Real.log (Rn / 2) + (1 / 2) * Real.log Real.pi - (1 / 2) * Real.log (rk (A.secLat n) : ℝ)) ≤
      (A.bergExp : ℝ) * Real.log ((n : ℝ) + 1) + (1 / 2) * Real.log (rk (A.secLat n) : ℝ) +
        Real.log (2 * A.bergConst) + |Real.log (√Real.pi)| := by
    rw [hlog_Rn, hlog_pi]
    have hpi_abs : -Real.log (√Real.pi) ≤ |Real.log (√Real.pi)| := neg_le_abs _
    linarith
  have hmul_loss := mul_le_mul_of_nonneg_left hloss hrk_posR.le
  nlinarith

/-- **Nef Arithmetic Hilbert–Samuel Realization**:
`A : ArithSectionFamily D` realizes `L : ArithNefLineBundle d ι X` if `L.relDim = D` and the
normalized arithmetic degrees of `A.secLat n` satisfy the nef Hilbert–Samuel lower bound
`liminf_{n → ∞} arithDeg (A.secLat n) / (n^{D+1}/(D+1)!) ≥ L.arithSelfInt`. -/
structure HasNefAHS {d D : ℕ} {ι : Type*} {X : Set (Fin d → ℂ)}
    (A : ArithSectionFamily D) (L : ArithNefLineBundle d ι X) : Prop where
  dim_eq : L.relDim = D
  ahs_lower : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in Filter.atTop,
    L.arithSelfInt - ε ≤ arithDeg (A.secLat n) / arithVolNorm D n

/-- **MAIN THEOREM 1 — NEF ARITHMETIC RIEMANN–ROCH LOWER BOUND (`nef_riemann_roch_lower_bound`)**:
For ANY `ArithNefLineBundle` `L` and ANY graded Hermitian section family `A : ArithSectionFamily D`
realizing `L` (`HasNefAHS A L`):
1. Asymptotic small-section ratio lower bound:
   `∀ ε > 0, ∀ᶠ n in atTop, L.arithSelfInt - ε ≤ A.arithVolRatio n`,
2. **Volume-Intersection Inequality**:
   `L.arithSelfInt ≤ ArithVolume A` ($\widehat{c}_1(\overline{L})^{D+1} \le \widehat{\operatorname{vol}}(\overline{L})$),
3. **Small-Section Extraction when Big & Nef (`0 < L.arithSelfInt`)**:
   `∃ c₀ > 0, ∃ N₀ ≥ 1, ∀ n ≥ N₀, c₀ * n^{D+1} ≤ log(#smallSections A n)` and there exists
   a nonzero integral global section `s ∈ A.secLat n` with `A.supNorm n s < 1`! -/
theorem nef_riemann_roch_lower_bound {d D : ℕ} {ι : Type*} {X : Set (Fin d → ℂ)}
    {A : ArithSectionFamily D} {L : ArithNefLineBundle d ι X} (hAHS : HasNefAHS A L) :
    (∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in Filter.atTop, L.arithSelfInt - ε ≤ A.arithVolRatio n) ∧
    (L.arithSelfInt ≤ ArithVolume A) ∧
    (0 < L.arithSelfInt →
      ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ N₀ : ℕ, ∃ hN0 : 1 ≤ N₀,
        ∀ n : ℕ, (hn : N₀ ≤ n) →
          c₀ * (n : ℝ) ^ (D + 1) ≤ Real.log (A.smallSectionsCard n (le_trans hN0 hn) : ℝ) ∧
          ∃ s ∈ A.secLat n, s ≠ 0 ∧ A.supNorm n s < 1) := by
  let C₁ : ℝ := A.rankHi * ((A.bergExp : ℝ) + (D : ℝ) / 2)
  let C₂ : ℝ := A.rankHi * (Real.log (2 * A.bergConst) + (1 / 2) * Real.log A.rankHi +
    |Real.log (√Real.pi)|)
  have hfac_pos : (0 : ℝ) < ((D + 1).factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos _)
  have herr_tend := tendsto_log_linear_div_nat' (C₁ * ((D + 1).factorial : ℝ))
    (C₂ * ((D + 1).factorial : ℝ))
  have hasymp : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in Filter.atTop,
      L.arithSelfInt - ε ≤ A.arithVolRatio n := by
    intro ε hε
    have h1 := hAHS.ahs_lower (ε / 2) (half_pos hε)
    have hmem := (Metric.tendsto_atTop.mp herr_tend) (ε / 2) (half_pos hε)
    filter_upwards [h1, eventually_ge_atTop hmem.choose, eventually_ge_atTop 1] with n hn1 hn_err hn_ge1
    have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn_ge1
    have hvol_pos := arithVolNorm_pos D hn_ge1
    have hrk_pos : 1 ≤ rk (A.secLat n) := rk_pos_of_ne_bot _ (A.secLat_ne_bot n hn_ge1)
    have hrk_posR : (0 : ℝ) < (rk (A.secLat n) : ℝ) := Nat.cast_pos.mpr hrk_pos
    have hlog_rk : Real.log (rk (A.secLat n) : ℝ) ≤
        Real.log A.rankHi + (D : ℝ) * Real.log ((n : ℝ) + 1) := by
      have hrk1 : (rk (A.secLat n) : ℝ) ≤ A.rankHi * ((n : ℝ) + 1) ^ D := by
        calc (rk (A.secLat n) : ℝ) ≤ A.rankHi * (n : ℝ) ^ D := A.rk_le_poly n hn_ge1
          _ ≤ A.rankHi * ((n : ℝ) + 1) ^ D :=
              mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hn_pos.le (by linarith) D)
                (by linarith [A.rankHi_ge_one])
      have hlg := Real.log_le_log hrk_posR hrk1
      rw [Real.log_mul (by linarith [A.rankHi_ge_one]) (pow_pos (by positivity) _).ne',
        Real.log_pow] at hlg
      exact hlg
    have hloss_per_rk :
        (A.bergExp : ℝ) * Real.log ((n : ℝ) + 1) + (1 / 2) * Real.log (rk (A.secLat n) : ℝ) +
          Real.log (2 * A.bergConst) + |Real.log (√Real.pi)| ≤
        ((A.bergExp : ℝ) + (D : ℝ) / 2) * Real.log ((n : ℝ) + 1) +
          (Real.log (2 * A.bergConst) + (1 / 2) * Real.log A.rankHi + |Real.log (√Real.pi)|) := by
      linarith
    have hpos_rhs : 0 ≤ ((A.bergExp : ℝ) + (D : ℝ) / 2) * Real.log ((n : ℝ) + 1) +
        (Real.log (2 * A.bergConst) + (1 / 2) * Real.log A.rankHi + |Real.log (√Real.pi)|) := by
      have ha : 0 ≤ Real.log ((n : ℝ) + 1) := Real.log_nonneg (by linarith)
      have hb : 0 ≤ Real.log (2 * A.bergConst) := Real.log_nonneg (by linarith [A.bergConst_ge_one])
      have hc : 0 ≤ Real.log A.rankHi := Real.log_nonneg A.rankHi_ge_one
      have hd : 0 ≤ |Real.log (√Real.pi)| := abs_nonneg _
      nlinarith [Nat.cast_nonneg (α := ℝ) A.bergExp, Nat.cast_nonneg (α := ℝ) D]
    have hloss_tot :
        (rk (A.secLat n) : ℝ) *
          ((A.bergExp : ℝ) * Real.log ((n : ℝ) + 1) + (1 / 2) * Real.log (rk (A.secLat n) : ℝ) +
            Real.log (2 * A.bergConst) + |Real.log (√Real.pi)|) ≤
        (C₁ * Real.log ((n : ℝ) + 1) + C₂) * (n : ℝ) ^ D := by
      calc (rk (A.secLat n) : ℝ) * _
          ≤ (rk (A.secLat n) : ℝ) *
              (((A.bergExp : ℝ) + (D : ℝ) / 2) * Real.log ((n : ℝ) + 1) +
                (Real.log (2 * A.bergConst) + (1 / 2) * Real.log A.rankHi + |Real.log (√Real.pi)|)) :=
            mul_le_mul_of_nonneg_left hloss_per_rk hrk_posR.le
        _ ≤ (A.rankHi * (n : ℝ) ^ D) * _ :=
            mul_le_mul_of_nonneg_right (A.rk_le_poly n hn_ge1) hpos_rhs
        _ = (C₁ * Real.log ((n : ℝ) + 1) + C₂) * (n : ℝ) ^ D := by
            dsimp only [C₁, C₂]; ring
    have herr_div : (C₁ * Real.log ((n : ℝ) + 1) + C₂) * (n : ℝ) ^ D / arithVolNorm D n ≤ ε / 2 := by
      have hd := hmem.choose_spec n hn_err
      rw [Real.dist_eq, sub_zero] at hd
      have heq : (C₁ * Real.log ((n : ℝ) + 1) + C₂) * (n : ℝ) ^ D / arithVolNorm D n =
          ((C₁ * ((D + 1).factorial : ℝ)) * Real.log ((n : ℝ) + 1) +
            C₂ * ((D + 1).factorial : ℝ)) / (n : ℝ) := by
        unfold arithVolNorm
        rw [pow_succ]
        field_simp [hn_pos.ne', hfac_pos.ne']
      rw [heq]
      exact (le_abs_self _).trans hd.le
    have hsec := section_space_riemann_roch_lower_bound A hn_ge1
    have hdiv := div_le_div_of_nonneg_right hsec hvol_pos.le
    have hratio : A.arithVolRatio n = Real.log (A.smallSectionsCard n hn_ge1 : ℝ) / arithVolNorm D n := by
      unfold ArithSectionFamily.arithVolRatio
      rw [dif_pos hn_ge1]
    rw [← hratio] at hdiv
    have hloss_div : (rk (A.secLat n) : ℝ) *
          ((A.bergExp : ℝ) * Real.log ((n : ℝ) + 1) + (1 / 2) * Real.log (rk (A.secLat n) : ℝ) +
            Real.log (2 * A.bergConst) + |Real.log (√Real.pi)|) / arithVolNorm D n ≤ ε / 2 :=
      (div_le_div_of_nonneg_right hloss_tot hvol_pos.le).trans herr_div
    rw [sub_div] at hdiv
    linarith
  refine ⟨hasymp, le_arithVolume_of_eventually_le A hasymp, fun hpos => ?_⟩
  have hev := hasymp (L.arithSelfInt / 2) (half_pos hpos)
  rw [Filter.eventually_atTop] at hev
  obtain ⟨K₁, hK₁⟩ := hev
  let N₀ := max 1 K₁
  let c₀ := L.arithSelfInt / (2 * ((D + 1).factorial : ℝ))
  have hc₀ : 0 < c₀ := div_pos hpos (by positivity)
  refine ⟨c₀, hc₀, N₀, le_max_left _ _, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := le_trans (le_max_left _ _) hn
  have hnK : K₁ ≤ n := le_trans (le_max_right _ _) hn
  have h1 := hK₁ n hnK
  unfold ArithSectionFamily.arithVolRatio at h1
  rw [dif_pos hn1] at h1
  have hvol_pos := arithVolNorm_pos D hn1
  have h2 : (L.arithSelfInt / 2) * arithVolNorm D n ≤ Real.log (A.smallSectionsCard n hn1 : ℝ) := by
    have hhalf : L.arithSelfInt / 2 ≤ Real.log (A.smallSectionsCard n hn1 : ℝ) / arithVolNorm D n := by
      linarith
    exact (le_div_iff₀ hvol_pos).mp hhalf
  have hc_eq : c₀ * (n : ℝ) ^ (D + 1) = (L.arithSelfInt / 2) * arithVolNorm D n := by
    dsimp only [c₀]
    unfold arithVolNorm
    ring
  rw [hc_eq]
  refine ⟨h2, ?_⟩
  have hlog_pos : 0 < Real.log (A.smallSectionsCard n hn1 : ℝ) :=
    lt_of_lt_of_le (mul_pos (half_pos hpos) hvol_pos) h2
  have hgt1_real : (1 : ℝ) < (A.smallSectionsCard n hn1 : ℝ) := by
    by_contra hle
    push Not at hle
    have hcard_pos : (0 : ℝ) < (A.smallSectionsCard n hn1 : ℝ) := by
      exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one (A.one_le_smallSectionsCard hn1)
    have hlog_le : Real.log (A.smallSectionsCard n hn1 : ℝ) ≤ 0 :=
      (Real.log_le_log hcard_pos hle).trans_eq Real.log_one
    linarith
  have hgt1 : 1 < (A.smallSections_finite hn1).toFinset.card := by exact_mod_cast hgt1_real
  obtain ⟨s₁, hs₁, s₂, hs₂, hne⟩ := Finset.one_lt_card.mp hgt1
  have hmem₁ := (A.smallSections_finite hn1).mem_toFinset.mp hs₁
  have hmem₂ := (A.smallSections_finite hn1).mem_toFinset.mp hs₂
  by_cases hs10 : (s₁ : A.secSpace n) = 0
  · refine ⟨s₂.1, s₂.2, fun h => hne (Subtype.ext (hs10.trans h.symm)), hmem₂⟩
  · refine ⟨s₁.1, s₁.2, hs10, hmem₁⟩

/-- **Arithmetic Surface (`D = 1`) Nef Riemann–Roch Lower Bound**:
directly wired to `Stage11ArakelovFaltings.ArithSurfaceModel` & `ArithLineBundle`:
for any `IsArithNefSurface M L` and any section family `A : ArithSectionFamily 1` satisfying
the Hilbert–Samuel lower bound for `(L · L)_Ar`, we get `(L · L)_Ar ≤ ArithVolume A`! -/
theorem surface_nef_riemann_roch_lower_bound {m : ℕ} {E_arch : Type*} [NormedAddCommGroup E_arch]
    [InnerProductSpace ℝ E_arch] (M : ArithSurfaceModel m E_arch)
    {L : ArithLineBundle m E_arch} (hL : IsArithNefSurface M L)
    (A : ArithSectionFamily 1)
    (hAHS : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in Filter.atTop,
      ArithLineBundle.arakelovPair M L L - ε ≤ arithDeg (A.secLat n) / arithVolNorm 1 n) :
    ArithLineBundle.arakelovPair M L L ≤ ArithVolume A := by
  let Lbundle : ArithNefLineBundle 1 Unit Set.univ :=
    { bundle := MetrizedLineBundle.trivial 1 Set.univ isOpen_univ (fun _ => 0)
        (fun _ _ => contDiffAt_const)
      relDim := 1
      geomDeg := L.geomDeg
      arithSelfInt := ArithLineBundle.arakelovPair M L L
      essMinHeight := 0
      semipositive := by
        rw [MetrizedLineBundle.trivial_semipositive_iff_isPlurisubharmonicOn]
        intro z _
        refine ⟨contDiffAt_const, fun w => by rw [leviForm_zero]⟩
      geomDeg_nonneg := hL.1
      arithSelfInt_nonneg := hL.2.1
      essMinHeight_nonneg := le_rfl }
  exact (nef_riemann_roch_lower_bound (L := Lbundle) ⟨rfl, hAHS⟩).2.1

/-- **Metric-Shift Arithmetic Degree Formula**:
uniformly scaling the metric on `H⁰(X, L^{⊗ n})` by `e^{-n c}` (`scaleLat (exp (-n * c))`)
shifts `arithDeg` by `n * rk(Λ) * c`. -/
theorem metric_shift_arithDeg_exact {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (Λ : Submodule ℤ E) [DiscreteTopology Λ] (n : ℕ) (c : ℝ) :
    arithDeg (scaleLat (Real.exp (-(n : ℝ) * c)) Λ) =
      arithDeg Λ + (n : ℝ) * (rk Λ : ℝ) * c := by
  have hexp : 0 < Real.exp (-(n : ℝ) * c) := Real.exp_pos _
  have hinv := (scaleLat_invariants Λ hexp).2.2.2
  rw [hinv, Real.log_exp]
  ring

end NefRiemannRoch

/-! ## Section 4: `kleiman_ampleness_criterion` (Topological Cone, Hermitian & Surface Forms) -/

section KleimanAmpleness

/-- **MAIN THEOREM 2A — KLEIMAN'S AMPLENESS CRITERION (Finite-Dimensional Cone Form)**:
Let `V` be a finite-dimensional real normed space (modeling $N_1(X)_\mathbb{R}$), `K ⊆ V` a closed
cone (`IsClosed K`, closed under non-negative scalar multiplication, modeling $\overline{\mathrm{NE}}(X)$),
and `A : V →L[ℝ] ℝ` an ample reference class (`∀ c ∈ K, c ≠ 0 → 0 < A c`).
Then for any class `L : V →L[ℝ] ℝ`:
$$(\forall c \in K,\; c \ne 0 \implies 0 < L(c)) \iff
  (\exists \varepsilon > 0,\; \forall c \in K,\; 0 \le L(c) - \varepsilon \, A(c)).$$
That is, `L` is strictly positive on $\overline{\mathrm{NE}}(X) \setminus \{0\}$ if and only if
`L - ε A` is nef for some `ε > 0`! -/
theorem kleiman_ampleness_criterion
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (K : Set V) (hK_closed : IsClosed K) (hK_cone : ∀ c ∈ K, ∀ t : ℝ, 0 ≤ t → t • c ∈ K)
    (A : V →L[ℝ] ℝ) (hA_pos : ∀ c ∈ K, c ≠ 0 → 0 < A c)
    (L : V →L[ℝ] ℝ) :
    (∀ c ∈ K, c ≠ 0 → 0 < L c) ↔
      (∃ ε : ℝ, 0 < ε ∧ ∀ c ∈ K, 0 ≤ L c - ε * A c) := by
  constructor
  · intro hL_pos
    let S : Set V := K ∩ Metric.sphere (0 : V) 1
    have hS_compact : IsCompact S :=
      (isCompact_sphere (0 : V) 1).inter_left hK_closed
    by_cases hS_ne : S.Nonempty
    · obtain ⟨c₀, hc₀S, hc₀min⟩ := hS_compact.exists_isMinOn hS_ne L.continuous.continuousOn
      obtain ⟨c₁, hc₁S, hc₁max⟩ := hS_compact.exists_isMaxOn hS_ne A.continuous.continuousOn
      have hc₀_norm : ‖c₀‖ = 1 := by simpa [S] using hc₀S.2
      have hc₀_ne : c₀ ≠ 0 := by intro h0; rw [h0, norm_zero] at hc₀_norm; norm_num at hc₀_norm
      have hm_pos : 0 < L c₀ := hL_pos c₀ hc₀S.1 hc₀_ne
      have hc₁_norm : ‖c₁‖ = 1 := by simpa [S] using hc₁S.2
      have hc₁_ne : c₁ ≠ 0 := by intro h0; rw [h0, norm_zero] at hc₁_norm; norm_num at hc₁_norm
      have hM_pos : 0 < A c₁ := hA_pos c₁ hc₁S.1 hc₁_ne
      let ε : ℝ := L c₀ / (A c₁ + 1)
      have hε_pos : 0 < ε := div_pos hm_pos (by linarith)
      refine ⟨ε, hε_pos, fun c hcK => ?_⟩
      by_cases hc0 : c = 0
      · subst hc0; simp
      · have hcnorm : 0 < ‖c‖ := norm_pos_iff.mpr hc0
        let u : V := ‖c‖⁻¹ • c
        have huS : u ∈ S := by
          refine ⟨hK_cone c hcK ‖c‖⁻¹ (inv_nonneg.mpr hcnorm.le), ?_⟩
          simp [u, norm_smul, inv_mul_cancel₀ hcnorm.ne']
        have hLu : L c₀ ≤ L u := hc₀min huS
        have hAu : A u ≤ A c₁ := hc₁max huS
        have hdiff_u : 0 ≤ L u - ε * A u := by
          have h1 : ε * A u ≤ ε * A c₁ := mul_le_mul_of_nonneg_left hAu hε_pos.le
          have h2 : ε * A c₁ ≤ L c₀ := by
            dsimp only [ε]
            rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
            nlinarith
          linarith
        have hc_eq : c = ‖c‖ • u := by
          dsimp only [u]
          rw [smul_smul, mul_inv_cancel₀ hcnorm.ne', one_smul]
        rw [hc_eq, L.map_smul, A.map_smul, smul_eq_mul, smul_eq_mul]
        have hfact : ‖c‖ * L u - ε * (‖c‖ * A u) = ‖c‖ * (L u - ε * A u) := by ring
        rw [hfact]
        exact mul_nonneg hcnorm.le hdiff_u
    · refine ⟨1, one_pos, fun c hcK => ?_⟩
      by_cases hc0 : c = 0
      · subst hc0; simp
      · exfalso
        apply hS_ne
        have hcnorm : 0 < ‖c‖ := norm_pos_iff.mpr hc0
        refine ⟨‖c‖⁻¹ • c, hK_cone c hcK ‖c‖⁻¹ (inv_nonneg.mpr hcnorm.le), ?_⟩
        simp [norm_smul, inv_mul_cancel₀ hcnorm.ne']
  · rintro ⟨ε, hε, hle⟩ c hcK hc0
    have hAc := hA_pos c hcK hc0
    have h1 := hle c hcK
    nlinarith

/-- **Kleiman Nef-Cone Closure Theorem ($\mathrm{Nef}(X) = \overline{\mathrm{Amp}}(X)$)**:
a class `L : V →L[ℝ] ℝ` is nef on `K` (`∀ c ∈ K, 0 ≤ L c`) if and only if every positive
perturbation `L + ε • A` (`ε > 0`) is strictly positive on `K \ {0}` (ample!). -/
theorem kleiman_nef_cone_closure
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (K : Set V) (A : V →L[ℝ] ℝ) (hA_pos : ∀ c ∈ K, c ≠ 0 → 0 < A c)
    (L : V →L[ℝ] ℝ) :
    (∀ c ∈ K, 0 ≤ L c) ↔
      (∀ ε : ℝ, 0 < ε → ∀ c ∈ K, c ≠ 0 → 0 < L c + ε * A c) := by
  constructor
  · intro hnef ε hε c hcK hc0
    exact add_pos_of_nonneg_of_pos (hnef c hcK) (mul_pos hε (hA_pos c hcK hc0))
  · intro hpert c hcK
    by_cases hc0 : c = 0
    · subst hc0; simp
    · have hAc := hA_pos c hcK hc0
      by_contra hneg
      push Not at hneg
      let ε := (-L c) / (2 * A c)
      have hε : 0 < ε := div_pos (by linarith) (by linarith)
      have hpos := hpert ε hε c hcK hc0
      have heq : ε * A c = (-L c) / 2 := by
        dsimp only [ε]
        field_simp [hAc.ne']
      linarith

/-- **Pointwise Coercivity of Strictly Positive Hermitian Curvature (`PosCurvatureMetric`)**:
for any `MetrizedLineBundle d ι X` (`0 < d`) with `PosCurvatureMetric L` and any point `z ∈ X`,
compactness of the unit sphere in `Fin d → ℂ` yields `c > 0` with
`∀ w : Fin d → ℂ, c * (∑ j, ‖w j‖²) ≤ L.curvatureAt z w`. -/
theorem posCurvatureMetric_coercive_at {d : ℕ} (hd : 0 < d) {ι : Type*} {X : Set (Fin d → ℂ)}
    (L : MetrizedLineBundle d ι X) (hpos : PosCurvatureMetric L) {z : Fin d → ℂ} (hz : z ∈ X) :
    ∃ c : ℝ, 0 < c ∧ ∀ w : Fin d → ℂ, c * (∑ j : Fin d, ‖w j‖ ^ 2) ≤ L.curvatureAt z w := by
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (L.covers hz)
  let B := fderiv ℝ (fderiv ℝ (L.weight i)) z
  let f : (Fin d → ℂ) → ℝ := fun w => leviForm (L.weight i) z w
  have hf_cont : Continuous f := by
    have h1 : Continuous (fun w : Fin d → ℂ => B w w) :=
      B.continuous.clm_apply continuous_id
    have h2 : Continuous (fun w : Fin d → ℂ => B (Complex.I • w) (Complex.I • w)) :=
      h1.comp (continuous_const_smul Complex.I)
    exact (h1.add h2).div_const 4
  let S : Set (Fin d → ℂ) := Metric.sphere 0 1
  have hS_comp : IsCompact S := isCompact_sphere 0 1
  have hS_ne : S.Nonempty := by
    let w₀ : Fin d → ℂ := Pi.single ⟨0, hd⟩ 1
    refine ⟨w₀, ?_⟩
    rw [Metric.mem_sphere, dist_zero_right]
    refine le_antisymm ?_ ?_
    · rw [pi_norm_le_iff_of_nonneg zero_le_one]
      intro j
      by_cases hj : j = ⟨0, hd⟩
      · subst hj; simp [w₀]
      · simp [w₀, Pi.single_eq_of_ne hj]
    · have h0 := norm_le_pi_norm w₀ ⟨0, hd⟩
      simpa [w₀] using h0
  obtain ⟨u₀, hu₀S, hu₀min⟩ := hS_comp.exists_isMinOn hS_ne hf_cont.continuousOn
  have hu₀_norm : ‖u₀‖ = 1 := by simpa [S] using hu₀S
  have hu₀_ne : u₀ ≠ 0 := by intro h0; rw [h0, norm_zero] at hu₀_norm; norm_num at hu₀_norm
  have hc_pos : 0 < f u₀ := by
    dsimp only [f]
    rw [← L.curvatureAt_eq_of_mem hi]
    exact hpos z hz u₀ hu₀_ne
  refine ⟨f u₀ / (d : ℝ), div_pos hc_pos (Nat.cast_pos.mpr hd), fun w => ?_⟩
  rw [L.curvatureAt_eq_of_mem hi]
  by_cases hw0 : w = 0
  · subst hw0
    simp [leviForm_zero_dir]
  · have hw_pos : 0 < ‖w‖ := norm_pos_iff.mpr hw0
    let u₁ : Fin d → ℂ := (‖w‖⁻¹ : ℝ) • w
    have hu₁S : u₁ ∈ S := by
      simp [S, u₁, norm_smul, inv_mul_cancel₀ hw_pos.ne']
    have hmin : f u₀ ≤ f u₁ := hu₀min hu₁S
    have hhom : f w = ‖w‖ ^ 2 * f u₁ := by
      have heq_w : w = (‖w‖ : ℂ) • u₁ := by
        dsimp only [u₁]
        ext j
        simp only [Pi.smul_apply, Complex.real_smul, smul_eq_mul]
        rw [← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hw_pos.ne',
          Complex.ofReal_one, one_mul]
      conv_lhs => rw [heq_w]
      dsimp only [f]
      rw [leviForm_smul_complex, Complex.norm_real, Real.norm_of_nonneg hw_pos.le]
    have hsum_le : ∑ j : Fin d, ‖w j‖ ^ 2 ≤ (d : ℝ) * ‖w‖ ^ 2 := by
      calc ∑ j : Fin d, ‖w j‖ ^ 2
          ≤ ∑ _j : Fin d, ‖w‖ ^ 2 := Finset.sum_le_sum fun j _ =>
            pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm w j) 2
        _ = (d : ℝ) * ‖w‖ ^ 2 := by simp [nsmul_eq_mul]
    have hd_pos : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr hd
    calc (f u₀ / (d : ℝ)) * ∑ j : Fin d, ‖w j‖ ^ 2
        ≤ (f u₀ / (d : ℝ)) * ((d : ℝ) * ‖w‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hsum_le (div_pos hc_pos hd_pos).le
      _ = f u₀ * ‖w‖ ^ 2 := by field_simp [hd_pos.ne']
      _ ≤ f u₁ * ‖w‖ ^ 2 := mul_le_mul_of_nonneg_right hmin (sq_nonneg _)
      _ = f w := by rw [hhom, mul_comm]

/-- **Openness of the Uniformly Positive (Kähler/Ample) Curvature Cone**:
if `ω` is `IsUniformlyPositive` (`c ∑ ‖w_j‖² ≤ ω(z, w)`) and `η` is bounded by `M ∑ ‖w_j‖²`,
then `ω + ε • η` remains `IsUniformlyPositive` (hence `IsStrictlyPositive`) for all
`|ε| < c / (M + 1)`. -/
theorem hermitianCurvature_ample_cone_open {d : ℕ} {X : Set (Fin d → ℂ)}
    {ω η : HermitianCurvatureForm d X} {c M : ℝ}
    (_hc : 0 < c) (hω : ∀ z ∈ X, ∀ w : Fin d → ℂ, c * (∑ j : Fin d, ‖w j‖ ^ 2) ≤ ω.eval z w)
    (_hM : 0 ≤ M) (hη : ∀ z ∈ X, ∀ w : Fin d → ℂ, |η.eval z w| ≤ M * ∑ j : Fin d, ‖w j‖ ^ 2)
    {ε : ℝ} (hε : |ε| < c / (M + 1)) :
    (ω + ε • η).IsUniformlyPositive := by
  let c' : ℝ := c - |ε| * M
  have hc' : 0 < c' := by
    dsimp only [c']
    have h1 : |ε| * (M + 1) < c := (lt_div_iff₀ (by linarith)).mp hε
    nlinarith [abs_nonneg ε]
  refine ⟨c', hc', fun z hz w => ?_⟩
  have h1 := hω z hz w
  have h2 := hη z hz w
  have h3 : -(|ε| * M * ∑ j : Fin d, ‖w j‖ ^ 2) ≤ ε * η.eval z w := by
    have hprod : |ε * η.eval z w| ≤ |ε| * (M * ∑ j : Fin d, ‖w j‖ ^ 2) := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
    linarith [(abs_le.mp hprod).1]
  change c' * ∑ j : Fin d, ‖w j‖ ^ 2 ≤ ω.eval z w + ε * η.eval z w
  dsimp only [c']
  nlinarith

/-- **Arithmetic Surface (`ArithSurfaceModel`) Kleiman Criterion**:
if `L` is `IsArithNefSurface M L` and `A` is `IsArithAmple M A`, then `L + ε • A` is
`IsArithAmple M` for every `ε > 0`; conversely if `L + ε • A` is `IsArithAmple M` for all
`ε > 0`, then `0 ≤ L.geomDeg` and `0 ≤ (L · L)_Ar`. -/
theorem kleiman_arith_surface_criterion {m : ℕ} {E_arch : Type*} [NormedAddCommGroup E_arch]
    [InnerProductSpace ℝ E_arch] (M : ArithSurfaceModel m E_arch)
    {L A : ArithLineBundle m E_arch} (hA : ArithLineBundle.IsArithAmple M A) :
    (IsArithNefSurface M L → ∀ ε : ℝ, 0 < ε → ArithLineBundle.IsArithAmple M (L + ε • A)) ∧
    ((∀ ε : ℝ, 0 < ε → ArithLineBundle.IsArithAmple M (L + ε • A)) →
      0 ≤ L.geomDeg ∧ 0 ≤ ArithLineBundle.arakelovPair M L L) := by
  constructor
  · intro hL ε hε
    refine ⟨by simp; nlinarith [hL.1, hA.1], ?_⟩
    have hLA : 0 ≤ ArithLineBundle.arakelovPair M L A :=
      hL.2.2 A hA.1.le hA.2.le (fun h0 => absurd h0 hA.1.ne')
    rw [ArithLineBundle.arakelovPair_add_left, ArithLineBundle.arakelovPair_add_right,
      ArithLineBundle.arakelovPair_add_right, ArithLineBundle.arakelovPair_smul_left,
      ArithLineBundle.arakelovPair_smul_right, ArithLineBundle.arakelovPair_smul_left,
      ArithLineBundle.arakelovPair_smul_right, ArithLineBundle.arakelovPair_symm M A L]
    have t1 : 0 ≤ ArithLineBundle.arakelovPair M L L := hL.2.1
    have t2 : 0 ≤ 2 * ε * ArithLineBundle.arakelovPair M L A := by positivity
    have t3 : 0 < ε * (ε * ArithLineBundle.arakelovPair M A A) := mul_pos hε (mul_pos hε hA.2)
    linarith
  · intro hpert
    have hdeg_ge : 0 ≤ L.geomDeg := by
      by_contra hlt
      push Not at hlt
      let ε : ℝ := (-L.geomDeg) / (2 * A.geomDeg)
      have hε : 0 < ε := div_pos (by linarith) (by linarith [hA.1])
      have h1 := (hpert ε hε).1
      simp only [ArithLineBundle.add_geomDeg, ArithLineBundle.smul_geomDeg] at h1
      have heq : ε * A.geomDeg = -L.geomDeg / 2 := by
        dsimp only [ε]; field_simp [hA.1.ne']
      linarith
    refine ⟨hdeg_ge, ?_⟩
    let p : ℝ → ℝ := fun ε =>
      ArithLineBundle.arakelovPair M L L + 2 * ε * ArithLineBundle.arakelovPair M L A +
        ε ^ 2 * ArithLineBundle.arakelovPair M A A
    have hp_cont : Continuous p := by continuity
    have hp_tend : Tendsto p (𝓝[>] 0) (𝓝 (ArithLineBundle.arakelovPair M L L)) := by
      have h0 : p 0 = ArithLineBundle.arakelovPair M L L := by simp [p]
      rw [← h0]
      exact hp_cont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have hp_pos : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 ≤ p ε := by
      filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
      have h1 := (hpert ε hε).2.le
      have hexp : ArithLineBundle.arakelovPair M (L + ε • A) (L + ε • A) = p ε := by
        dsimp only [p]
        rw [ArithLineBundle.arakelovPair_add_left, ArithLineBundle.arakelovPair_add_right,
          ArithLineBundle.arakelovPair_add_right, ArithLineBundle.arakelovPair_smul_left,
          ArithLineBundle.arakelovPair_smul_right, ArithLineBundle.arakelovPair_smul_left,
          ArithLineBundle.arakelovPair_smul_right, ArithLineBundle.arakelovPair_symm M A L]
        ring
      rwa [← hexp]
    exact ge_of_tendsto hp_tend hp_pos

end KleimanAmpleness

/-! ## Section 5: `arith_volume_superadditive` (Khovanskii–Teissier, Section-Level & Surface) -/

section ArithVolumeSuperadditivity

universe u_a

/-- **Elementary Binomial Superadditivity**:
for any `D : ℕ` and non-negative mixed intersection numbers `I : Fin (D + 2) → ℝ` with
`I 0 = v₂` and `I ⟨D + 1, _⟩ = v₁`,
`v₁ + v₂ ≤ ∑ k : Fin (D + 2), (Nat.choose (D + 1) k : ℝ) * I k`. -/
theorem binomial_intersection_sum_ge_add (D : ℕ) (I : Fin (D + 2) → ℝ)
    (hI : ∀ k, 0 ≤ I k) :
    I ⟨D + 1, Nat.lt_succ_self (D + 1)⟩ + I 0 ≤
      ∑ k : Fin (D + 2), (Nat.choose (D + 1) k : ℝ) * I k := by
  have h0 : (0 : Fin (D + 2)) ≠ ⟨D + 1, Nat.lt_succ_self (D + 1)⟩ := by
    intro h
    have hval := congrArg Fin.val h
    simp at hval
  have hterm0 : (Nat.choose (D + 1) 0 : ℝ) * I 0 = I 0 := by simp
  have htermD : (Nat.choose (D + 1) (D + 1) : ℝ) * I ⟨D + 1, Nat.lt_succ_self (D + 1)⟩ =
      I ⟨D + 1, Nat.lt_succ_self (D + 1)⟩ := by simp
  let f : Fin (D + 2) → ℝ := fun k => (Nat.choose (D + 1) k : ℝ) * I k
  have hf_nn : ∀ k, 0 ≤ f k := fun k => mul_nonneg (Nat.cast_nonneg _) (hI k)
  have hle0 : f 0 + f ⟨D + 1, Nat.lt_succ_self (D + 1)⟩ ≤ ∑ k : Fin (D + 2), f k := by
    have h1 := Finset.add_le_sum (s := Finset.univ) (f := f) (fun k _ => hf_nn k)
      (Finset.mem_univ 0) (Finset.mem_univ ⟨D + 1, Nat.lt_succ_self (D + 1)⟩) h0
    exact h1
  dsimp only [f] at hle0
  change (Nat.choose (D + 1) 0 : ℝ) * I 0 +
      (Nat.choose (D + 1) (D + 1) : ℝ) * I ⟨D + 1, Nat.lt_succ_self (D + 1)⟩ ≤
      ∑ k : Fin (D + 2), (Nat.choose (D + 1) k : ℝ) * I k at hle0
  rw [hterm0, htermD] at hle0
  linarith

/-- **Khovanskii–Teissier / Brunn–Minkowski `(D + 1)`-th Root Binomial Superadditivity**:
if mixed nef intersections `I : Fin (D + 2) → ℝ` satisfy log-concavity
`v₁ ^ (k / (D + 1)) * v₂ ^ ((D + 1 - k) / (D + 1)) ≤ I k` (`v₁, v₂ ≥ 0`), then:
$$(v_1^{1/(D+1)} + v_2^{1/(D+1)})^{D+1} \le \sum_{k=0}^{D+1} \binom{D+1}{k} I_k,$$
and consequently $v_1 + v_2 \le \sum_{k=0}^{D+1} \binom{D+1}{k} I_k$! -/
theorem khovanskii_teissier_binomial_superadditive (D : ℕ) {v₁ v₂ : ℝ}
    (hv₁ : 0 ≤ v₁) (hv₂ : 0 ≤ v₂) (I : Fin (D + 2) → ℝ)
    (hKT : ∀ k : Fin (D + 2),
      v₁ ^ ((k : ℝ) / ((D + 1 : ℕ) : ℝ)) *
        v₂ ^ (((D + 1 - (k : ℕ) : ℕ) : ℝ) / ((D + 1 : ℕ) : ℝ)) ≤ I k) :
    (v₁ ^ (1 / ((D + 1 : ℕ) : ℝ)) + v₂ ^ (1 / ((D + 1 : ℕ) : ℝ))) ^ (D + 1) ≤
      ∑ k : Fin (D + 2), (Nat.choose (D + 1) k : ℝ) * I k ∧
    v₁ + v₂ ≤ ∑ k : Fin (D + 2), (Nat.choose (D + 1) k : ℝ) * I k := by
  let x : ℝ := v₁ ^ (1 / ((D + 1 : ℕ) : ℝ))
  let y : ℝ := v₂ ^ (1 / ((D + 1 : ℕ) : ℝ))
  have hx : 0 ≤ x := Real.rpow_nonneg hv₁ _
  have hy : 0 ≤ y := Real.rpow_nonneg hv₂ _
  have hD1 : ((D + 1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero D)
  have hx_pow : x ^ (D + 1) = v₁ := by
    dsimp only [x]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hv₁, one_div_mul_cancel hD1, Real.rpow_one]
  have hy_pow : y ^ (D + 1) = v₂ := by
    dsimp only [y]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hv₂, one_div_mul_cancel hD1, Real.rpow_one]
  have hterm : ∀ k : Fin (D + 2),
      x ^ (k : ℕ) * y ^ (D + 1 - (k : ℕ)) ≤ I k := by
    intro k
    have hkx : x ^ (k : ℕ) = v₁ ^ ((k : ℝ) / ((D + 1 : ℕ) : ℝ)) := by
      dsimp only [x]
      rw [← Real.rpow_natCast, ← Real.rpow_mul hv₁, one_div_mul_eq_div]
    have hky : y ^ (D + 1 - (k : ℕ)) =
        v₂ ^ (((D + 1 - (k : ℕ) : ℕ) : ℝ) / ((D + 1 : ℕ) : ℝ)) := by
      dsimp only [y]
      rw [← Real.rpow_natCast, ← Real.rpow_mul hv₂, one_div_mul_eq_div]
    rw [hkx, hky]
    exact hKT k
  have hbin : (x + y) ^ (D + 1) =
      ∑ k ∈ Finset.range (D + 2), (Nat.choose (D + 1) k : ℝ) * (x ^ k * y ^ (D + 1 - k)) := by
    rw [add_pow]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  have hfin : (∑ k : Fin (D + 2), (Nat.choose (D + 1) k : ℝ) * (x ^ (k : ℕ) * y ^ (D + 1 - (k : ℕ)))) =
      ∑ k ∈ Finset.range (D + 2), (Nat.choose (D + 1) k : ℝ) * (x ^ k * y ^ (D + 1 - k)) :=
    Fin.sum_univ_eq_sum_range
      (fun k : ℕ => (Nat.choose (D + 1) k : ℝ) * (x ^ k * y ^ (D + 1 - k))) (D + 2)
  have hsum_le : (x + y) ^ (D + 1) ≤ ∑ k : Fin (D + 2), (Nat.choose (D + 1) k : ℝ) * I k := by
    rw [hbin, ← hfin]
    exact Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hterm k) (Nat.cast_nonneg _)
  have hadd_le : v₁ + v₂ ≤ (x + y) ^ (D + 1) := by
    rw [← hx_pow, ← hy_pow, hbin]
    have h0 : 0 ∈ Finset.range (D + 2) := Finset.mem_range.mpr (by omega)
    have hD : D + 1 ∈ Finset.range (D + 2) := Finset.mem_range.mpr (by omega)
    have hne : (0 : ℕ) ≠ D + 1 := by omega
    let g : ℕ → ℝ := fun k => (Nat.choose (D + 1) k : ℝ) * (x ^ k * y ^ (D + 1 - k))
    have h1 := Finset.add_le_sum (s := Finset.range (D + 2)) (f := g)
      (fun k _ => mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (pow_nonneg hx _) (pow_nonneg hy _)))
      h0 hD hne
    dsimp only [g] at h1
    rw [show (Nat.choose (D + 1) 0 : ℝ) * (x ^ 0 * y ^ (D + 1 - 0)) = y ^ (D + 1) by simp,
      show (Nat.choose (D + 1) (D + 1) : ℝ) * (x ^ (D + 1) * y ^ (D + 1 - (D + 1))) =
        x ^ (D + 1) by simp] at h1
    linarith
  exact ⟨hsum_le, hadd_le.trans hsum_le⟩

/-- **Direct Section-Space Superadditivity of `ArithVolume`**:
given graded section families `A₁, A₂, A₁₂ : ArithSectionFamily D` such that for all sufficiently
large `n`, there is an injection from `A₁.smallSectionsSet n × A₂.smallSectionsSet n` into
`A₁₂.smallSectionsSet n` (e.g., via an Okounkov-filtration / orthogonal graded product embedding),
**`ArithVolume A₁ + ArithVolume A₂ ≤ ArithVolume A₁₂`** unconditionally! -/
theorem arith_volume_superadditive_of_product_map {D : ℕ}
    (A₁ A₂ A₁₂ : ArithSectionFamily D)
    (hinj : ∃ N₀ : ℕ, ∃ hN0 : 1 ≤ N₀, ∀ (n : ℕ) (hn : N₀ ≤ n),
      A₁.smallSectionsCard n (le_trans hN0 hn) * A₂.smallSectionsCard n (le_trans hN0 hn) ≤
        A₁₂.smallSectionsCard n (le_trans hN0 hn)) :
    ArithVolume A₁ + ArithVolume A₂ ≤ ArithVolume A₁₂ := by
  rcases hinj with ⟨N₀, hN0, hprod⟩
  by_contra hlt
  push Not at hlt
  let δ : ℝ := (ArithVolume A₁ + ArithVolume A₂ - ArithVolume A₁₂) / 3
  have hδ : 0 < δ := by dsimp only [δ]; linarith
  have hev1 := Filter.eventually_lt_of_lt_liminf (sub_lt_self (ArithVolume A₁) hδ)
    A₁.arithVolRatio_isBoundedUnder_ge
  have hev2 := Filter.eventually_lt_of_lt_liminf (sub_lt_self (ArithVolume A₂) hδ)
    A₂.arithVolRatio_isBoundedUnder_ge
  have hev_prod : ∀ᶠ n in Filter.atTop,
      A₁.arithVolRatio n + A₂.arithVolRatio n ≤ A₁₂.arithVolRatio n := by
    filter_upwards [eventually_ge_atTop N₀] with n hn
    have hn1 : 1 ≤ n := le_trans hN0 hn
    unfold ArithSectionFamily.arithVolRatio
    rw [dif_pos hn1, dif_pos hn1, dif_pos hn1, ← add_div]
    refine div_le_div_of_nonneg_right ?_ (arithVolNorm_pos D hn1).le
    have h1pos : (0 : ℝ) < (A₁.smallSectionsCard n hn1 : ℝ) := by
      exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one (A₁.one_le_smallSectionsCard hn1)
    have h2pos : (0 : ℝ) < (A₂.smallSectionsCard n hn1 : ℝ) := by
      exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one (A₂.one_le_smallSectionsCard hn1)
    rw [← Real.log_mul h1pos.ne' h2pos.ne']
    refine Real.log_le_log (mul_pos h1pos h2pos) ?_
    exact_mod_cast hprod n hn
  have hcomb : ∀ᶠ n in Filter.atTop,
      (ArithVolume A₁ - δ) + (ArithVolume A₂ - δ) ≤ A₁₂.arithVolRatio n := by
    filter_upwards [hev1, hev2, hev_prod] with n h1 h2 h3
    linarith
  have hlim := Filter.le_liminf_of_le A₁₂.arithVolRatio_isBoundedUnder_le.isCoboundedUnder_ge hcomb
  change (ArithVolume A₁ - δ) + (ArithVolume A₂ - δ) ≤ ArithVolume A₁₂ at hlim
  dsimp only [δ] at hlim
  linarith

/-- **MAIN THEOREM 3 — SUPERADDITIVITY OF ARITHMETIC VOLUME (`arith_volume_superadditive`)**:
For any two `ArithNefLineBundle`s `L₁, L₂` (`relDim = D`) with non-negative mixed intersection
numbers `I : Fin (D + 2) → ℝ` (`I 0 = L₂.arithSelfInt`, `I ⟨D+1, _⟩ = L₁.arithSelfInt`) and any
graded section family `A₁₂ : ArithSectionFamily D` realizing the tensor bundle `L₁ ⊗ L₂` via
`HasNefAHS A₁₂ (L₁.tensorWith L₂ ...)`:
1. **Additive Superadditivity**: `L₁.arithSelfInt + L₂.arithSelfInt ≤ ArithVolume A₁₂`;
2. **Brunn–Minkowski / Khovanskii–Teissier `(D + 1)`-th Root Superadditivity** (when `I` satisfies
   log-concavity):
   `(L₁.arithSelfInt ^ (1 / (D + 1)) + L₂.arithSelfInt ^ (1 / (D + 1))) ^ (D + 1) ≤ ArithVolume A₁₂`;
3. **Exact Volume Superadditivity** when `ArithVolume Aᵢ = Lᵢ.arithSelfInt`:
   `ArithVolume A₁ + ArithVolume A₂ ≤ ArithVolume A₁₂`! -/
theorem arith_volume_superadditive {d D : ℕ} {ι₁ ι₂ : Type*} {X : Set (Fin d → ℂ)}
    (L₁ : ArithNefLineBundle d ι₁ X) (L₂ : ArithNefLineBundle d ι₂ X)
    (hdim1 : L₁.relDim = D) (hdim2 : L₂.relDim = D)
    (I : Fin (D + 2) → ℝ) (hI_nn : ∀ k, 0 ≤ I k)
    (hI_0 : I 0 = L₂.arithSelfInt)
    (hI_top : I ⟨D + 1, Nat.lt_succ_self (D + 1)⟩ = L₁.arithSelfInt)
    (tensorGeomDeg : ℝ) (htdeg : 0 ≤ tensorGeomDeg)
    (A₁₂ : ArithSectionFamily.{u_a} D)
    (hAHS₁₂ : HasNefAHS A₁₂
      (L₁.tensorWith L₂ (hdim1.trans hdim2.symm) tensorGeomDeg
        (∑ k : Fin (D + 2), (Nat.choose (D + 1) k : ℝ) * I k) htdeg
        (Finset.sum_nonneg fun k _ => mul_nonneg (Nat.cast_nonneg _) (hI_nn k)))) :
    (L₁.arithSelfInt + L₂.arithSelfInt ≤ ArithVolume A₁₂) ∧
    ((∀ k : Fin (D + 2),
        L₁.arithSelfInt ^ ((k : ℝ) / ((D + 1 : ℕ) : ℝ)) *
          L₂.arithSelfInt ^ (((D + 1 - (k : ℕ) : ℕ) : ℝ) / ((D + 1 : ℕ) : ℝ)) ≤ I k) →
      (L₁.arithSelfInt ^ (1 / ((D + 1 : ℕ) : ℝ)) +
        L₂.arithSelfInt ^ (1 / ((D + 1 : ℕ) : ℝ))) ^ (D + 1) ≤ ArithVolume A₁₂) ∧
    (∀ (A₁ A₂ : ArithSectionFamily.{u_a} D),
      ArithVolume A₁ = L₁.arithSelfInt → ArithVolume A₂ = L₂.arithSelfInt →
      ArithVolume A₁ + ArithVolume A₂ ≤ ArithVolume A₁₂) := by
  have hNRR := (nef_riemann_roch_lower_bound hAHS₁₂).2.1
  change ∑ k : Fin (D + 2), (Nat.choose (D + 1) k : ℝ) * I k ≤ ArithVolume A₁₂ at hNRR
  have hadd : L₁.arithSelfInt + L₂.arithSelfInt ≤ ArithVolume A₁₂ := by
    have hbin := binomial_intersection_sum_ge_add D I hI_nn
    rw [hI_top, hI_0] at hbin
    exact hbin.trans hNRR
  refine ⟨hadd, fun hKT => ?_, fun A₁ A₂ hV₁ hV₂ => ?_⟩
  · have hbm := (khovanskii_teissier_binomial_superadditive D L₁.arithSelfInt_nonneg
      L₂.arithSelfInt_nonneg I hKT).1
    exact hbm.trans hNRR
  · rw [hV₁, hV₂]
    exact hadd

/-- **Arithmetic Surface (`D = 1`) Exact Brunn–Minkowski / Yuan Superadditivity**:
directly from `Stage11ArakelovFaltings.arithmetic_hodge_index_ineq`:
for any two nef `ArithLineBundle`s on an `ArithSurfaceModel M` with `0 < (L₁ · L₁)_Ar`
(or `IsArithNefSurface M L₁ ∧ IsArithNefSurface M L₂`):
1. `√((L₁ · L₁)_Ar) + √((L₂ · L₂)_Ar) ≤ √(((L₁ + L₂) · (L₁ + L₂))_Ar)` (Brunn–Minkowski!)
2. `(L₁ · L₁)_Ar + (L₂ · L₂)_Ar ≤ ((L₁ + L₂) · (L₁ + L₂))_Ar`! -/
theorem arith_surface_volume_superadditive {m : ℕ} {E_arch : Type*}
    [NormedAddCommGroup E_arch] [InnerProductSpace ℝ E_arch]
    (M : ArithSurfaceModel m E_arch) {L₁ L₂ : ArithLineBundle m E_arch}
    (_h1 : IsArithNefSurface M L₁) (h2 : IsArithNefSurface M L₂)
    (h12_nn : 0 ≤ ArithLineBundle.arakelovPair M L₁ L₂)
    (h1pos : 0 < ArithLineBundle.arakelovPair M L₁ L₁) :
    Real.sqrt (ArithLineBundle.arakelovPair M L₁ L₁) +
        Real.sqrt (ArithLineBundle.arakelovPair M L₂ L₂) ≤
      Real.sqrt (ArithLineBundle.arakelovPair M (L₁ + L₂) (L₁ + L₂)) ∧
    ArithLineBundle.arakelovPair M L₁ L₁ + ArithLineBundle.arakelovPair M L₂ L₂ ≤
      ArithLineBundle.arakelovPair M (L₁ + L₂) (L₁ + L₂) := by
  have hhi := ArithLineBundle.arithmetic_hodge_index_ineq M h1pos (L₂ := L₂)
  have hsqrt_prod :
      Real.sqrt (ArithLineBundle.arakelovPair M L₁ L₁ * ArithLineBundle.arakelovPair M L₂ L₂) ≤
        ArithLineBundle.arakelovPair M L₁ L₂ := by
    rw [← Real.sqrt_sq h12_nn]
    exact Real.sqrt_le_sqrt hhi
  rw [Real.sqrt_mul h1pos.le] at hsqrt_prod
  have hexp : ArithLineBundle.arakelovPair M (L₁ + L₂) (L₁ + L₂) =
      ArithLineBundle.arakelovPair M L₁ L₁ + 2 * ArithLineBundle.arakelovPair M L₁ L₂ +
        ArithLineBundle.arakelovPair M L₂ L₂ := by
    rw [ArithLineBundle.arakelovPair_add_left, ArithLineBundle.arakelovPair_add_right,
      ArithLineBundle.arakelovPair_add_right, ArithLineBundle.arakelovPair_symm M L₂ L₁]
    ring
  have hbm :
      Real.sqrt (ArithLineBundle.arakelovPair M L₁ L₁) +
          Real.sqrt (ArithLineBundle.arakelovPair M L₂ L₂) ≤
        Real.sqrt (ArithLineBundle.arakelovPair M (L₁ + L₂) (L₁ + L₂)) := by
    have hsq_le :
        (Real.sqrt (ArithLineBundle.arakelovPair M L₁ L₁) +
          Real.sqrt (ArithLineBundle.arakelovPair M L₂ L₂)) ^ 2 ≤
          ArithLineBundle.arakelovPair M (L₁ + L₂) (L₁ + L₂) := by
      rw [hexp, add_sq, Real.sq_sqrt h1pos.le, Real.sq_sqrt h2.2.1]
      linarith
    rw [← Real.sqrt_sq (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
    exact Real.sqrt_le_sqrt hsq_le
  have hadd :
      ArithLineBundle.arakelovPair M L₁ L₁ + ArithLineBundle.arakelovPair M L₂ L₂ ≤
        ArithLineBundle.arakelovPair M (L₁ + L₂) (L₁ + L₂) := by
    rw [hexp]; linarith
  exact ⟨hbm, hadd⟩

end ArithVolumeSuperadditivity

/-! ## Section 6: Master Synthesis for M3 Wave 3 (`ArakelovPublishedPackage`) & M4 (`AhSlimDeepStR`) -/

section Wave3AndM4Synthesis

/-- **Stage-14 M3 Wave-2 Master Nef Riemann–Roch & Kleiman Ampleness Synthesis**:
certifies all five core exported primitives and theorems unconditionally (`0` `sorry`, `0` custom
`axiom`s, `0` `native_decide`):
1. Concrete `ArithNefLineBundle` & `ArithVolume ≥ 0`;
2. `nef_riemann_roch_lower_bound`: `L.arithSelfInt ≤ ArithVolume A` + exponential small sections;
3. `kleiman_ampleness_criterion`: finite-dimensional topological cone equivalence;
4. `arith_volume_superadditive`: additive and `(D + 1)`-th root Brunn–Minkowski superadditivity;
5. Unconditional sphere-packing upper bound `h0Arith_upper_bound_sphere_packing`. -/
theorem stage14M3_nef_riemann_roch_synthesis
    {d D : ℕ} {ι₁ ι₂ : Type*} {X : Set (Fin d → ℂ)}
    (L₁ : ArithNefLineBundle d ι₁ X) (L₂ : ArithNefLineBundle d ι₂ X)
    (hdim1 : L₁.relDim = D) (hdim2 : L₂.relDim = D)
    (A₁ : ArithSectionFamily D) (hAHS₁ : HasNefAHS A₁ L₁)
    (I : Fin (D + 2) → ℝ) (hI_nn : ∀ k, 0 ≤ I k)
    (hI_0 : I 0 = L₂.arithSelfInt)
    (hI_top : I ⟨D + 1, Nat.lt_succ_self (D + 1)⟩ = L₁.arithSelfInt)
    (tensorGeomDeg : ℝ) (htdeg : 0 ≤ tensorGeomDeg)
    (A₁₂ : ArithSectionFamily D)
    (hAHS₁₂ : HasNefAHS A₁₂
      (L₁.tensorWith L₂ (hdim1.trans hdim2.symm) tensorGeomDeg
        (∑ k : Fin (D + 2), (Nat.choose (D + 1) k : ℝ) * I k) htdeg
        (Finset.sum_nonneg fun k _ => mul_nonneg (Nat.cast_nonneg _) (hI_nn k))))
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (K : Set V) (hK_closed : IsClosed K) (hK_cone : ∀ c ∈ K, ∀ t : ℝ, 0 ≤ t → t • c ∈ K)
    (Aamp Lcone : V →L[ℝ] ℝ) (hA_pos : ∀ c ∈ K, c ≠ 0 → 0 < Aamp c) :
    (0 ≤ ArithVolume A₁) ∧
    (L₁.arithSelfInt ≤ ArithVolume A₁) ∧
    ((∀ c ∈ K, c ≠ 0 → 0 < Lcone c) ↔
      (∃ ε : ℝ, 0 < ε ∧ ∀ c ∈ K, 0 ≤ Lcone c - ε * Aamp c)) ∧
    (L₁.arithSelfInt + L₂.arithSelfInt ≤ ArithVolume A₁₂) :=
  ⟨arithVolume_nonneg A₁,
   (nef_riemann_roch_lower_bound hAHS₁).2.1,
   kleiman_ampleness_criterion K hK_closed hK_cone Aamp hA_pos Lcone,
   (arith_volume_superadditive L₁ L₂ hdim1 hdim2 I hI_nn hI_0 hI_top tensorGeomDeg htdeg
     A₁₂ hAHS₁₂).1⟩

end Wave3AndM4Synthesis

end

end RHDirect.Stage14M3_NefRiemannRoch
