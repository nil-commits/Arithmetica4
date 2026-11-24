import RHDirect.Stage11ArakelovFaltings
import RHDirect.Stage12SchurWeylLattices
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import Mathlib.Topology.KrullDimension
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.Ideal.GoingDown
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-!
# RHDirect.Stage14M3_IntegralSchemesAndCharts

Package `M3` Wave 1 (1 of 6) — **Pillar-5 Clean Distillation**: Integral Schemes, Cyclotomic Base
Rings, Flat Generic Density, Relative Parameter Systems, Topological Krull Dimension, and
Regular Toroidal Charts in pure Mathlib `v4.33.1` (`0` `sorry`, `0` custom `axiom`s,
`0` `native_decide`).

## Main Exports

1. **Cyclotomic Base Ring `CycAwayBase` (`ℤ[ζ_n, 1/n]`) & `TBase`**:
   - `cycAway n : Subring ℂ` (`ℤ[ζ_n, 1/n]`), `zetaAway n`, `isUnit_natCast_cycAway`,
     `isPrimitiveRoot_map_cycAway`, `TBase`, and `CycAwayBase`.
2. **Affine Schemes `Sp`, `spMap`, Stalks, & Flat Generic Density (`dense_generic_of_flat`)**:
   - `Sp R`, `spMap f`, `closedPoint R`, `stalkId`, `idlAlong`, `dense_generic_spMap`,
     and **`dense_generic_of_flat`** (`[IsDomain o] (s : S ⟶ Sp o) [Flat s] → Dense {x : S | (s x).asIdeal = ⊥}`).
3. **Relative Parameter Systems (`IsRelParam`) & Power-Series Regularity**:
   - `IsRelParam b t`, cotangent linear independence, and unconditional proofs of
     **`isRelParam_powerSeries_X`** and **`isRelParam_mvPowerSeries_X`**.
4. **Topological Krull Dimension (`krull_dim_le_of_irreducible_closeds`)**:
   - **`krull_dim_le_of_irreducible_closeds`**, `krull_dim_mono`, `krull_dim_union`,
     `krull_dim_eq_iSup_closure`, `krull_dim_eq_bot_iff`, `krull_dim_spec_eq_ringKrullDim`,
     and `krull_dim_le_of_openCover`.
5. **Regular Local Rings, `ToroidalChartData`, `HasRegularChart`, & Arakelov Bridges**:
   - `IsRegularLocalRing`, `IsEtaleCompletion`, **`ToroidalChartData`**, **`HasRegularChart`**,
     `HasRegularChart.idl_eq_top_iff`, concrete 0-assumption `hasRegularChart_powerSeries_closedPoint`,
     and bridges to `Stage11ArakelovFaltings` and `Stage12SchurWeylLattices`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace IsLocalRing
open scoped BigOperators Pointwise

namespace RHDirect.Stage14M3_IntegralSchemesAndCharts

/-! ## Section 1: Cyclotomic Base Rings `CycAwayBase` (`ℤ[ζ_n, 1/n]`) & `TBase` -/

section CycAwayBaseSection

/-- Standard primitive `n`-th root of unity `exp(2πi / n)` in `ℂ`. -/
def zetaC (n : ℕ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I / n)

/-- Cyclotomic subring `ℤ[ζ_n, 1/n] ⊂ ℂ` with `n` inverted. -/
def cycAway (n : ℕ) : Subring ℂ :=
  Subring.closure {zetaC n, (n : ℂ)⁻¹}

/-- The canonical `n`-th root of unity `ζ_n ∈ cycAway n`. -/
def zetaAway (n : ℕ) : cycAway n :=
  ⟨zetaC n, Subring.subset_closure (Or.inl rfl)⟩

/-- The canonical inverse `n⁻¹ ∈ cycAway n`. -/
def invNatAway (n : ℕ) : cycAway n :=
  ⟨(n : ℂ)⁻¹, Subring.subset_closure (Or.inr rfl)⟩

instance instIsDomainCycAway (n : ℕ) : IsDomain (cycAway n) :=
  inferInstance

instance instCharZeroCycAway (n : ℕ) : CharZero (cycAway n) :=
  inferInstance

@[simp]
theorem zetaAway_coe (n : ℕ) : ((zetaAway n : cycAway n) : ℂ) = zetaC n :=
  rfl

@[simp]
theorem invNatAway_coe (n : ℕ) : ((invNatAway n : cycAway n) : ℂ) = (n : ℂ)⁻¹ :=
  rfl

/-- `zetaC n` is a primitive `n`-th root of unity in `ℂ` for `n ≠ 0`. -/
theorem isPrimitiveRoot_zetaC {n : ℕ} (hn : n ≠ 0) : IsPrimitiveRoot (zetaC n) n :=
  Complex.isPrimitiveRoot_exp n hn

/-- `zetaAway n` is a primitive `n`-th root of unity in `cycAway n` for `n ≠ 0`. -/
theorem isPrimitiveRoot_zetaAway {n : ℕ} (hn : n ≠ 0) : IsPrimitiveRoot (zetaAway n) n :=
  IsPrimitiveRoot.of_map_of_injective (f := (cycAway n).subtype)
    (isPrimitiveRoot_zetaC hn) Subtype.val_injective

/-- In `cycAway n`, `(n : cycAway n)` is a unit whenever `n ≠ 0`. -/
theorem isUnit_natCast_cycAway {n : ℕ} (hn : n ≠ 0) : IsUnit (n : cycAway n) :=
  IsUnit.of_mul_eq_one (invNatAway n)
    (Subtype.ext (by
      push_cast
      exact mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hn)))

/-- `zetaAway n ^ n = 1` in `cycAway n` for `n ≠ 0`. -/
theorem zetaAway_pow_eq_one {n : ℕ} (hn : n ≠ 0) : zetaAway n ^ n = 1 :=
  (isPrimitiveRoot_zetaAway hn).pow_eq_one

/-- Over any field `K` receiving a ring homomorphism `β : cycAway n →+* K`, `β (zetaAway n)` is a
primitive `n`-th root of unity (since `n` is invertible in `cycAway n`, hence `char K ∤ n`). -/
theorem isPrimitiveRoot_map_cycAway {n : ℕ} (hn : n ≠ 0) {K : Type*} [Field K]
    (β : cycAway n →+* K) : IsPrimitiveRoot (β (zetaAway n)) n := by
  have h1 : IsPrimitiveRoot (zetaAway n) n := isPrimitiveRoot_zetaAway hn
  have hnz : NeZero (n : K) := ⟨by
    have hu : IsUnit (β (n : cycAway n)) := (isUnit_natCast_cycAway hn).map β
    simpa using hu.ne_zero⟩
  have h2 := (h1.isRoot_cyclotomic (Nat.pos_of_ne_zero hn)).map (f := β)
  rwa [Polynomial.map_cyclotomic, Polynomial.isRoot_cyclotomic_iff] at h2

/-- `zetaAway n` is integral over `ℤ` (as a root of `X^n - 1`). -/
theorem isIntegral_zetaAway {n : ℕ} (hn : n ≠ 0) : IsIntegral ℤ (zetaAway n) := by
  refine ⟨Polynomial.X ^ n - 1, Polynomial.monic_X_pow_sub_C 1 hn, ?_⟩
  simp [zetaAway_pow_eq_one hn]

/-- Generic cyclotomic base datum `TBase o k`: a commutative ring `o` with a unit `ζ : oˣ` and
`k : o` invertible such that `β ζ` is a primitive `k`-th root of unity in every target field `K`. -/
structure TBase (o : Type*) [CommRing o] (k : ℕ) where
  ζ : oˣ
  unit : IsUnit (k : o)
  prim : ∀ (K : Type) [Field K] (β : o →+* K), IsPrimitiveRoot (β ζ) k

/-- Canonical `TBase` structure on `cycAway n` for any `n ≠ 0`. -/
def cycBase {n : ℕ} (hn : n ≠ 0) : TBase (cycAway n) n where
  ζ := Units.ofPowEqOne (zetaAway n) n (zetaAway_pow_eq_one hn) hn
  unit := isUnit_natCast_cycAway hn
  prim _ _ β := isPrimitiveRoot_map_cycAway hn β

@[simp]
theorem cycBase_ζ {n : ℕ} (hn : n ≠ 0) : ((cycBase hn).ζ : cycAway n) = zetaAway n :=
  rfl

/-- Packaged **Cyclotomic Away-from-`n` Base `CycAwayBase n`**:
combines `ℤ[ζ_n, 1/n]`, its `TBase` primitive-root datum, domain & characteristic-zero instances,
and its associated affine base scheme `Spec (ℤ[ζ_n, 1/n])`. -/
structure CycAwayBase (n : ℕ) where
  hn : n ≠ 0
  tbase : TBase (cycAway n) n
  zeta_eq : (tbase.ζ : cycAway n) = zetaAway n

namespace CycAwayBase

variable {n : ℕ}

/-- Construct `CycAwayBase n` from `n ≠ 0`. -/
def ofNeZero (hn : n ≠ 0) : CycAwayBase n where
  hn := hn
  tbase := cycBase hn
  zeta_eq := rfl

/-- Construct `CycAwayBase n` from `3 ≤ n` (standard fine-moduli level hypothesis). -/
def ofGeThree (hn : 3 ≤ n) : CycAwayBase n :=
  ofNeZero (by omega)

/-- The underlying subring `ℤ[ζ_n, 1/n] ⊂ ℂ`. -/
abbrev ring (_ : CycAwayBase n) : Type := cycAway n

/-- The canonical primitive `n`-th root of unity in `B.ring`. -/
def zeta (B : CycAwayBase n) : (cycAway n)ˣ := B.tbase.ζ

theorem zeta_val (B : CycAwayBase n) : (B.zeta : cycAway n) = zetaAway n := B.zeta_eq

theorem isUnit_level (B : CycAwayBase n) : IsUnit (n : cycAway n) := B.tbase.unit

theorem isPrimitiveRoot_map (B : CycAwayBase n) {K : Type} [Field K] (β : cycAway n →+* K) :
    IsPrimitiveRoot (β B.zeta) n :=
  B.tbase.prim K β

theorem isDomain (_ : CycAwayBase n) : IsDomain (cycAway n) := inferInstance

theorem charZero (_ : CycAwayBase n) : CharZero (cycAway n) := inferInstance

/-- Base change of `CycAwayBase n` to any field `K` via `β : cycAway n →+* K` preserves
primitivity of `ζ_n` and invertibility of `n`. -/
theorem baseChange_spec (B : CycAwayBase n) {K : Type} [Field K] (β : cycAway n →+* K) :
    IsUnit (n : K) ∧ IsPrimitiveRoot (β B.zeta) n := by
  refine ⟨?_, B.isPrimitiveRoot_map β⟩
  simpa using B.isUnit_level.map β

/-- For any ring homomorphism `β : cycAway n →+* A` into a nontrivial ring, `β n ≠ 0`. -/
theorem map_level_ne_zero (B : CycAwayBase n) {A : Type*} [CommRing A] [Nontrivial A]
    (β : cycAway n →+* A) : β (n : cycAway n) ≠ 0 :=
  (B.isUnit_level.map β).ne_zero

end CycAwayBase

end CycAwayBaseSection

/-! ## Section 2: Affine Schemes `Sp`, `spMap`, Stalks, & Flat Generic Density (`dense_generic_of_flat`) -/

section SchemesAndFlatDensity

/-- Universe-0 affine scheme `Spec (CommRingCat.of R)`. -/
abbrev Sp (R : Type) [CommRing R] : Scheme.{0} :=
  Spec (CommRingCat.of R)

/-- Contravariant morphism `Sp R' ⟶ Sp R` induced by a ring homomorphism `f : R →+* R'`. -/
abbrev spMap {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') : Sp R' ⟶ Sp R :=
  Spec.map (CommRingCat.ofHom f)

/-- Closed point of `Sp R` for a local ring `R`. -/
abbrev closedPoint (R : Type) [CommRing R] [IsLocalRing R] : Sp R :=
  IsLocalRing.closedPoint R

theorem spMap_id (R : Type) [CommRing R] : spMap (RingHom.id R) = 𝟙 (Sp R) := by
  simp [spMap]

theorem spMap_comp {R₁ R₂ R₃ : Type} [CommRing R₁] [CommRing R₂] [CommRing R₃]
    (f : R₁ →+* R₂) (g : R₂ →+* R₃) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

theorem spMap_injective {R R' : Type} [CommRing R] [CommRing R'] {f g : R →+* R'}
    (h : spMap f = spMap g) : f = g :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective h)

@[simp]
theorem spMap_apply_asIdeal {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (x : Sp R') :
    (spMap f x).asIdeal = x.asIdeal.comap f :=
  rfl

/-- A local ring homomorphism maps the closed point of `Sp R'` to the closed point of `Sp R`. -/
theorem spMap_closedPoint {R R' : Type} [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R']
    (f : R →+* R') [IsLocalHom f] :
    spMap f (closedPoint R') = closedPoint R :=
  PrimeSpectrum.ext (IsLocalRing.maximalIdeal_comap f)

/-- Stalk of an ideal sheaf `I : X.IdealSheafData` at `x : X`. -/
def stalkId {X : Scheme.{0}} (I : X.IdealSheafData) (x : X) : Ideal (X.presheaf.stalk x) :=
  ⨆ (U : X.affineOpens) (hx : x ∈ U.1), Ideal.map (X.presheaf.germ U.1 x hx).hom (I.ideal U)

private lemma map_germ_ideal_eq_of_le {X : Scheme.{0}} (I : X.IdealSheafData)
    {U V : X.affineOpens} (h : U ≤ V) (x : X) (hx : x ∈ U.1) :
    Ideal.map (X.presheaf.germ V.1 x (h hx)).hom (I.ideal V) =
      Ideal.map (X.presheaf.germ U.1 x hx).hom (I.ideal U) := by
  rw [← I.map_ideal h, Ideal.map_map, ← CommRingCat.hom_comp]
  congr 2
  exact (TopCat.Presheaf.germ_res X.presheaf _ x hx).symm

/-- On any affine open `U` containing `x`, `stalkId I x` equals the pushforward of `I.ideal U`. -/
theorem stalkId_eq_map {X : Scheme.{0}} (I : X.IdealSheafData) (U : X.affineOpens) (x : X)
    (hx : x ∈ U.1) :
    stalkId I x = Ideal.map (X.presheaf.germ U.1 x hx).hom (I.ideal U) := by
  unfold stalkId
  apply le_antisymm
  · refine iSup₂_le fun U' hx' => ?_
    have hxi : x ∈ U.1 ⊓ U'.1 := ⟨hx, hx'⟩
    obtain ⟨O, hO, hxO, hOle⟩ : ∃ O ∈ X.affineOpens, x ∈ O ∧ O ≤ U.1 ⊓ U'.1 :=
      (Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens) hxi
    let U'' : X.affineOpens := ⟨O, hO⟩
    have h1 : U'' ≤ U := (le_inf_iff.mp hOle).1
    have h2 : U'' ≤ U' := (le_inf_iff.mp hOle).2
    have e1 := map_germ_ideal_eq_of_le I h1 x hxO
    have e2 := map_germ_ideal_eq_of_le I h2 x hxO
    rw [e1, e2]
  · exact le_iSup₂_of_le U hx le_rfl

theorem stalkId_top {X : Scheme.{0}} (x : X) : stalkId (⊤ : X.IdealSheafData) x = ⊤ := by
  obtain ⟨U, hU, hx, -⟩ :=
    Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens (show x ∈ (⊤ : X.Opens) from trivial)
  refine top_le_iff.1 (le_trans ?_ (le_iSup₂_of_le (⟨U, hU⟩ : X.affineOpens) hx le_rfl))
  simp [Ideal.map_top]

/-- Pullback of the stalk ideal of `I : X.IdealSheafData` along a local chart `ξ : Sp R ⟶ X`. -/
def idlAlong {X : Scheme.{0}} (I : X.IdealSheafData) {R : Type} [CommRing R] [IsLocalRing R]
    (ξ : Sp R ⟶ X) : Ideal R :=
  (stalkId I (ξ (closedPoint R))).map (Scheme.stalkClosedPointTo ξ).hom

theorem idlAlong_top {X : Scheme.{0}} {R : Type} [CommRing R] [IsLocalRing R] (ξ : Sp R ⟶ X) :
    idlAlong (⊤ : X.IdealSheafData) ξ = ⊤ := by
  rw [idlAlong, stalkId_top, Ideal.map_top]

/-- `idlAlong I ξ = ⊤` iff `stalkId I (ξ (closedPoint R)) = ⊤`. -/
theorem idlAlong_eq_top_iff {X : Scheme.{0}} (I : X.IdealSheafData) {R : Type} [CommRing R]
    [IsLocalRing R] (ξ : Sp R ⟶ X) :
    idlAlong I ξ = ⊤ ↔ stalkId I (ξ (closedPoint R)) = ⊤ := by
  refine ⟨fun h => by_contra fun h' => ?_, fun h => by rw [idlAlong, h, Ideal.map_top]⟩
  refine (maximalIdeal.isMaximal R).ne_top
    (top_le_iff.1 (h.ge.trans (Ideal.map_le_iff_le_comap.2 fun c hc => ?_)))
  exact (map_mem_nonunits_iff (Scheme.stalkClosedPointTo ξ).hom c).2 (le_maximalIdeal h' hc)

/-- **Affine Flat Generic Density (`dense_generic_spMap`)**:
for an injective homomorphism `β : o →+* O` with `O` a domain, the fiber over `⊥` is dense in `Sp O`. -/
theorem dense_generic_spMap {o O : Type} [CommRing o] [CommRing O] [IsDomain O]
    (β : o →+* O) (hβ : Function.Injective β) :
    Dense {x : Sp O | (spMap β x).asIdeal = ⊥} := by
  intro x
  have hη : (show ↥(Sp O) from (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum O)) ⤳ x :=
    (PrimeSpectrum.le_iff_specializes _ _).1 (show (⊥ : Ideal O) ≤ x.asIdeal from bot_le)
  refine hη.mem_closed isClosed_closure (subset_closure ?_)
  change (PrimeSpectrum.comap β ⟨⊥, Ideal.isPrime_bot⟩).asIdeal = ⊥
  exact Ideal.comap_bot_of_injective β hβ

/-- **Flat Generic Density (`dense_generic_of_flat`)**:
if `o` is a domain and `s : S ⟶ Sp o` is flat, then the generic fiber `{x : S | (s x).asIdeal = ⊥}`
is dense in `S`. (Follows from `RingHom.Flat.generalizingMap_comap` on an affine cover.) -/
theorem dense_generic_of_flat {o : Type} [CommRing o] [IsDomain o] {S : Scheme.{0}}
    (s : S ⟶ Sp o) [Flat s] :
    Dense {x : S | (s x).asIdeal = ⊥} := by
  intro x
  obtain ⟨y, hy⟩ := S.affineCover.covers x
  have hcomp : Flat (S.affineCover.f (S.affineCover.idx x) ≫ s) :=
    MorphismProperty.comp_mem _ _ _ inferInstance ‹Flat s›
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (S.affineCover.f (S.affineCover.idx x) ≫ s)
  have hfl : φ.hom.Flat := by
    rw [← HasRingHomProperty.Spec_iff (P := @Flat), hφ]
    exact hcomp
  have hsp : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum o) ⤳ PrimeSpectrum.comap φ.hom y :=
    (PrimeSpectrum.le_iff_specializes _ _).1 (show (⊥ : Ideal o) ≤ _ from bot_le)
  obtain ⟨y', hy'1, hy'2⟩ := RingHom.Flat.generalizingMap_comap hfl hsp
  have hφy := congrArg (fun m => (m y').asIdeal) hφ
  have hmem : S.affineCover.f (S.affineCover.idx x) y' ∈ {x : S | (s x).asIdeal = ⊥} := by
    change ((S.affineCover.f (S.affineCover.idx x) ≫ s) y').asIdeal = ⊥
    refine Eq.trans ?_ (congrArg PrimeSpectrum.asIdeal hy'2)
    exact hφy.symm
  have h₁ : S.affineCover.f (S.affineCover.idx x) y' ⤳ S.affineCover.f (S.affineCover.idx x) y :=
    hy'1.map (S.affineCover.f (S.affineCover.idx x)).continuous
  have h₂ : S.affineCover.f (S.affineCover.idx x) y ⤳ x := by rw [hy]
  exact (h₁.trans h₂).mem_closed isClosed_closure (subset_closure hmem)

/-- Every nonempty open subset of a scheme flat over a domain `Sp o` meets the generic fiber. -/
theorem exists_generic_point_mem_of_flat {o : Type} [CommRing o] [IsDomain o] {S : Scheme.{0}}
    (s : S ⟶ Sp o) [Flat s] {U : Set S} (hUo : IsOpen U) (hUne : U.Nonempty) :
    ∃ x ∈ U, (s x).asIdeal = ⊥ :=
  (dense_generic_of_flat s).inter_open_nonempty U hUo hUne

/-- Specialization along `dense_generic_of_flat` over `CycAwayBase n`. -/
theorem dense_generic_of_flat_cycAway {n : ℕ} (B : CycAwayBase n) {S : Scheme.{0}}
    (s : S ⟶ Sp (cycAway n)) [Flat s] :
    Dense {x : S | (s x).asIdeal = ⊥} := by
  have : IsDomain (cycAway n) := B.isDomain
  exact dense_generic_of_flat s

end SchemesAndFlatDensity

/-! ## Section 3: Relative Parameter Systems (`IsRelParam`) & Power-Series Regularity -/

section RelativeParameters

section DefAndProperties

variable {o R : Type*} [CommRing o] [CommRing R] [IsLocalRing R] {m : ℕ}

/-- **Relative Regular Parameter System (`IsRelParam b t`)**:
`t : Fin m → R` lies in `𝔪_R` and is `k_R`-linearly independent in the relative cotangent space
`𝔪_R / (𝔪_R² + 𝔪_o R)`, i.e. any relation `∑ i, c i * t i ∈ 𝔪_R² ⊔ (𝔪_R.comap b).map b`
forces `∀ i, c i ∈ 𝔪_R`. -/
def IsRelParam (b : o →+* R) (t : Fin m → R) : Prop :=
  (∀ i, t i ∈ maximalIdeal R) ∧
  ∀ c : Fin m → R,
    ∑ i, c i * t i ∈ maximalIdeal R ^ 2 ⊔ ((maximalIdeal R).comap b).map b →
    ∀ i, c i ∈ maximalIdeal R

theorem IsRelParam.mem_maximalIdeal {b : o →+* R} {t : Fin m → R} (h : IsRelParam b t) (i : Fin m) :
    t i ∈ maximalIdeal R :=
  h.1 i

theorem IsRelParam.mem_of_mem_sq {b : o →+* R} {t : Fin m → R} (h : IsRelParam b t)
    (c : Fin m → R) (hc : ∑ i, c i * t i ∈ maximalIdeal R ^ 2) (i : Fin m) :
    c i ∈ maximalIdeal R :=
  h.2 c (Ideal.mem_sup_left hc) i

theorem IsRelParam.mem_of_mem_base {b : o →+* R} {t : Fin m → R} (h : IsRelParam b t)
    (c : Fin m → R) (hc : ∑ i, c i * t i ∈ ((maximalIdeal R).comap b).map b) (i : Fin m) :
    c i ∈ maximalIdeal R :=
  h.2 c (Ideal.mem_sup_right hc) i

/-- An element coming from the base ring `o` can never be a relative parameter. -/
theorem IsRelParam.not_mem_image (b : o →+* R) (p : o) : ¬ IsRelParam b ![b p] := by
  intro h
  have h1 : (1 : R) ∈ maximalIdeal R := by
    have hmem : (∑ i : Fin 1, (![(1 : R)] : Fin 1 → R) i * ![b p] i) ∈
        maximalIdeal R ^ 2 ⊔ ((maximalIdeal R).comap b).map b := by
      refine Ideal.mem_sup_right ?_
      simpa using Ideal.mem_map_of_mem b (show p ∈ (maximalIdeal R).comap b from h.1 0)
    simpa using h.2 ![1] hmem 0
  exact (maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).mpr h1)

/-- Empty family (`m = 0`) is vacuously a relative parameter system. -/
theorem isRelParam_zero (b : o →+* R) (t : Fin 0 → R) : IsRelParam b t :=
  ⟨fun i => i.elim0, fun _ _ i => i.elim0⟩

/-- Reindexing a relative parameter system by an equivalence `e : Fin k ≃ Fin m` preserves `IsRelParam`. -/
theorem IsRelParam.comp_equiv {b : o →+* R} {t : Fin m → R} (h : IsRelParam b t)
    {k : ℕ} (e : Fin k ≃ Fin m) : IsRelParam b (t ∘ e) := by
  refine ⟨fun i => h.1 (e i), fun c hc i => ?_⟩
  let c' : Fin m → R := fun j => c (e.symm j)
  have hsum : ∑ j : Fin m, c' j * t j = ∑ l : Fin k, c l * (t ∘ e) l := by
    refine Fintype.sum_equiv e.symm _ _ fun j => ?_
    simp [c']
  rw [← hsum] at hc
  simpa [c'] using h.2 c' hc (e i)

/-- Restricting a relative parameter system along an injection `ι : Fin k ↪ Fin m` preserves `IsRelParam`. -/
theorem IsRelParam.comp_embedding {b : o →+* R} {t : Fin m → R} (h : IsRelParam b t)
    {k : ℕ} (ι : Fin k ↪ Fin m) : IsRelParam b (t ∘ ι) := by
  classical
  refine ⟨fun i => h.1 (ι i), fun c hc i => ?_⟩
  let c' : Fin m → R := fun j => if hj : ∃ a, ι a = j then c hj.choose else 0
  have hsum : ∑ j : Fin m, c' j * t j = ∑ a : Fin k, c a * (t ∘ ι) a := by
    have hsplit : ∑ j : Fin m, c' j * t j =
        ∑ j ∈ Finset.univ.image ι, c' j * t j := by
      refine (Finset.sum_subset (Finset.subset_univ _) fun j _ hj => ?_).symm
      have hnex : ¬ ∃ a, ι a = j := fun ⟨a, ha⟩ => hj (Finset.mem_image.mpr ⟨a, Finset.mem_univ a, ha⟩)
      simp [c', hnex]
    rw [hsplit, Finset.sum_image (fun a _ b _ hab => ι.injective hab)]
    refine Finset.sum_congr rfl fun a _ => ?_
    have hex : ∃ a', ι a' = ι a := ⟨a, rfl⟩
    have hch : hex.choose = a := ι.injective hex.choose_spec
    simp [c']
  rw [← hsum] at hc
  have hmem := h.2 c' hc (ι i)
  simpa [c'] using hmem

/-- `IsRelParam` is preserved under a ring isomorphism `e : R ≃+* R'`. -/
theorem IsRelParam.map_ringEquiv {R' : Type*} [CommRing R'] [IsLocalRing R']
    {b : o →+* R} {t : Fin m → R} (h : IsRelParam b t) (e : R ≃+* R') :
    IsRelParam (e.toRingHom.comp b) (fun i => e (t i)) := by
  have hm : Ideal.map e.toRingHom (maximalIdeal R) = maximalIdeal R' :=
    IsLocalRing.map_maximalIdeal_of_surjective e.toRingHom e.surjective
  have heLoc : IsLocalHom e.toRingHom :=
    ⟨fun a ha => by
      rw [← e.symm_apply_apply a]
      exact ha.map e.symm.toRingHom⟩
  have hcomap : (maximalIdeal R').comap e.toRingHom = maximalIdeal R :=
    IsLocalRing.maximalIdeal_comap e.toRingHom
  refine ⟨fun i => ?_, fun c hc i => ?_⟩
  · rw [← hm]
    exact Ideal.mem_map_of_mem _ (h.1 i)
  · let c0 : Fin m → R := fun j => e.symm (c j)
    have hsum : e (∑ j, c0 j * t j) = ∑ j, c j * e (t j) := by
      simp [map_sum, map_mul, c0]
    have hmem_pre : ∑ j, c0 j * t j ∈
        maximalIdeal R ^ 2 ⊔ ((maximalIdeal R).comap b).map b := by
      let J := maximalIdeal R ^ 2 ⊔ ((maximalIdeal R).comap b).map b
      have hle : maximalIdeal R' ^ 2 ⊔ ((maximalIdeal R').comap (e.toRingHom.comp b)).map
          (e.toRingHom.comp b) ≤ J.map e.toRingHom := by
        refine sup_le ?_ ?_
        · rw [← hm, ← Ideal.map_pow]
          exact Ideal.map_mono le_sup_left
        · rw [← Ideal.comap_comap, hcomap, ← Ideal.map_map]
          exact Ideal.map_mono le_sup_right
      have hmemJ : e (∑ j, c0 j * t j) ∈ J.map e.toRingHom := hle (hsum ▸ hc)
      rw [Ideal.mem_map_iff_of_surjective e.toRingHom e.surjective] at hmemJ
      rcases hmemJ with ⟨y, hy, hey⟩
      have hyeq : y = ∑ j, c0 j * t j := e.injective hey
      rwa [← hyeq]
    have hc0i := h.2 c0 hmem_pre i
    rw [← hm]
    have hce : c i = e (c0 i) := by simp [c0]
    rw [hce]
    exact Ideal.mem_map_of_mem _ hc0i

/-- Each relative parameter `t i` stays outside `𝔪_R² ⊔ (𝔪_R.comap b).map b`. -/
theorem IsRelParam.not_mem_sq_sup_base {b : o →+* R} {t : Fin m → R} (h : IsRelParam b t) (i : Fin m) :
    t i ∉ maximalIdeal R ^ 2 ⊔ ((maximalIdeal R).comap b).map b := by
  classical
  intro hmem
  let c : Fin m → R := fun j => if j = i then 1 else 0
  have hsum : ∑ j, c j * t j = t i := by
    rw [Finset.sum_eq_single i]
    · simp [c]
    · intro j _ hj; simp [c, hj]
    · intro hi; exact absurd (Finset.mem_univ i) hi
  have hc1 : (1 : R) ∈ maximalIdeal R := by
    simpa [c] using h.2 c (hsum ▸ hmem) i
  exact (maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).mpr hc1)

/-- In particular, if `m ≥ 1`, no relative parameter `t i` can vanish (`t i ≠ 0`). -/
theorem IsRelParam.ne_zero {b : o →+* R} {t : Fin m → R} (h : IsRelParam b t) (i : Fin m) :
    t i ≠ 0 := by
  intro h0
  exact h.not_mem_sq_sup_base i (h0 ▸ Submodule.zero_mem _)

/-- Relative cotangent linear independence: `∑ i, (c i : k_R) • [t i] = 0` in the relative
cotangent module `R / (𝔪_R² ⊔ (𝔪_R.comap b).map b)` implies `c i = 0` in `ResidueField R`. -/
theorem IsRelParam.residue_eq_zero_of_sum_mem {b : o →+* R} {t : Fin m → R} (h : IsRelParam b t)
    (c : Fin m → R) (hc : ∑ i, c i * t i ∈ maximalIdeal R ^ 2 ⊔ ((maximalIdeal R).comap b).map b)
    (i : Fin m) :
    IsLocalRing.residue R (c i) = 0 :=
  (IsLocalRing.residue_eq_zero_iff (c i)).mpr (h.2 c hc i)

end DefAndProperties

section PowerSeriesParam

/-- Helper: characterizing the maximal ideal of `PowerSeries o` via the constant coefficient. -/
theorem mem_maximalIdeal_powerSeries_iff {o : Type*} [CommRing o] [IsLocalRing o]
    (f : PowerSeries o) :
    f ∈ maximalIdeal (PowerSeries o) ↔ PowerSeries.coeff 0 f ∈ maximalIdeal o := by
  simp [mem_maximalIdeal, mem_nonunits_iff, PowerSeries.isUnit_iff_constantCoeff]

/-- **1-Variable Power Series Relative Parameter Theorem (`isRelParam_powerSeries_X`)**:
for any local ring `o`, `X` is a relative regular parameter of `o[[X]]` over `o`! -/
theorem isRelParam_powerSeries_X (o : Type*) [CommRing o] [IsLocalRing o] :
    IsRelParam (PowerSeries.C (R := o)) ![(PowerSeries.X : PowerSeries o)] := by
  have hm := mem_maximalIdeal_powerSeries_iff (o := o)
  refine ⟨fun i => by simp [hm], fun c hc i => ?_⟩
  obtain rfl : i = 0 := Subsingleton.elim _ _
  have h0 : ∀ f g : PowerSeries o,
      PowerSeries.coeff 0 (f * g) = PowerSeries.coeff 0 f * PowerSeries.coeff 0 g := by simp
  have h1 : ∀ f g : PowerSeries o,
      PowerSeries.coeff 1 (f * g) =
        PowerSeries.coeff 0 f * PowerSeries.coeff 1 g +
        PowerSeries.coeff 1 f * PowerSeries.coeff 0 g := fun f g => by
    rw [PowerSeries.coeff_mul, Finset.Nat.antidiagonal_succ]
    simp
  let J : Ideal (PowerSeries o) :=
    { carrier := {f | PowerSeries.coeff 0 f ∈ maximalIdeal o ∧
        PowerSeries.coeff 1 f ∈ maximalIdeal o}
      add_mem' := fun h h' => ⟨by simpa using add_mem h.1 h'.1, by simpa using add_mem h.2 h'.2⟩
      zero_mem' := by simp
      smul_mem' := fun f g h => ⟨h0 f g ▸ Ideal.mul_mem_left _ _ h.1,
        h1 f g ▸ add_mem (Ideal.mul_mem_left _ _ h.2) (Ideal.mul_mem_left _ _ h.1)⟩ }
  have hJ : maximalIdeal (PowerSeries o) ^ 2 ⊔
      ((maximalIdeal (PowerSeries o)).comap PowerSeries.C).map PowerSeries.C ≤ J := by
    refine sup_le ?_ (Ideal.map_le_iff_le_comap.2 fun a ha =>
      ⟨by simpa [hm] using ha, by simp⟩)
    rw [sq]
    refine Ideal.mul_le.2 fun f hf g hg => ?_
    rw [hm] at hf hg
    exact ⟨h0 f g ▸ Ideal.mul_mem_left _ _ hg,
      h1 f g ▸ add_mem (Ideal.mul_mem_right _ _ hf) (Ideal.mul_mem_left _ _ hg)⟩
  have hmem := (hJ hc).2
  simpa [hm, PowerSeries.coeff_succ_mul_X] using hmem

/-- Helper: characterizing the maximal ideal of `MvPowerSeries σ o` via constant coefficient. -/
theorem mem_maximalIdeal_mvPowerSeries_iff {σ : Type*} {o : Type*} [CommRing o] [IsLocalRing o]
    (f : MvPowerSeries σ o) :
    f ∈ maximalIdeal (MvPowerSeries σ o) ↔ MvPowerSeries.constantCoeff f ∈ maximalIdeal o := by
  simp [mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff]

/-- **Multivariable Power Series Relative Parameter Theorem (`isRelParam_mvPowerSeries_X`)**:
for any local ring `o` and any `m : ℕ`, the coordinate tuple `i ↦ X_i` is a relative regular
parameter system of `o[[X_0, …, X_{m-1}]]` over `o`! -/
theorem isRelParam_mvPowerSeries_X (o : Type*) [CommRing o] [IsLocalRing o] (m : ℕ) :
    IsRelParam (MvPowerSeries.C (σ := Fin m) (R := o))
      (fun i => (MvPowerSeries.X i : MvPowerSeries (Fin m) o)) := by
  classical
  have hm := mem_maximalIdeal_mvPowerSeries_iff (σ := Fin m) (o := o)
  refine ⟨fun i => ?_, fun c hc i => ?_⟩
  · rw [hm, MvPowerSeries.constantCoeff_X]
    exact Ideal.zero_mem _
  · let ei : Fin m →₀ ℕ := Finsupp.single i 1
    have hcoeff_single : ∀ j : Fin m,
        MvPowerSeries.coeff ei (MvPowerSeries.X j : MvPowerSeries (Fin m) o) =
          if j = i then 1 else 0 := by
      intro j
      rw [MvPowerSeries.coeff_X]
      split_ifs with h1 h2 h2
      · rfl
      · exact False.elim (h2 (Finsupp.single_left_injective Nat.one_ne_zero h1).symm)
      · exact False.elim (h1 (by rw [h2]))
      · rfl
    have hmul_zero : ∀ f g : MvPowerSeries (Fin m) o,
        MvPowerSeries.constantCoeff (f * g) =
          MvPowerSeries.constantCoeff f * MvPowerSeries.constantCoeff g := by
      intro f g; simp
    have hmul_ei : ∀ f g : MvPowerSeries (Fin m) o,
        MvPowerSeries.coeff ei (f * g) =
          MvPowerSeries.constantCoeff f * MvPowerSeries.coeff ei g +
          MvPowerSeries.coeff ei f * MvPowerSeries.constantCoeff g := by
      intro f g
      rw [MvPowerSeries.coeff_mul]
      have hsupp : Finset.antidiagonal ei = {(0, ei), (ei, 0)} := by
        ext ⟨a, b⟩
        simp only [Finset.mem_antidiagonal, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
        constructor
        · intro hab
          have habi : a i + b i = 1 := by
            have := congrArg (fun t : Fin m →₀ ℕ => t i) hab
            simpa [ei] using this
          have hother : ∀ j ≠ i, a j = 0 ∧ b j = 0 := by
            intro j hj
            have := congrArg (fun t : Fin m →₀ ℕ => t j) hab
            simp [ei, hj] at this
            omega
          rcases (by omega : a i = 0 ∧ b i = 1 ∨ a i = 1 ∧ b i = 0) with ⟨ha, hb⟩ | ⟨ha, hb⟩
          · left
            refine ⟨Finsupp.ext fun j => ?_, Finsupp.ext fun j => ?_⟩
            · by_cases hj : j = i <;> simp [hj, ha, hother j]
            · by_cases hj : j = i <;> simp [ei, hj, hb, hother j]
          · right
            refine ⟨Finsupp.ext fun j => ?_, Finsupp.ext fun j => ?_⟩
            · by_cases hj : j = i <;> simp [ei, hj, ha, hother j]
            · by_cases hj : j = i <;> simp [hj, hb, hother j]
        · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> simp
      rw [hsupp, Finset.sum_pair (by
        intro h
        have := congrArg (fun p : (Fin m →₀ ℕ) × (Fin m →₀ ℕ) => p.1 i) h
        simp [ei] at this)]
      simp [MvPowerSeries.coeff_zero_eq_constantCoeff]
    let J : Ideal (MvPowerSeries (Fin m) o) :=
      { carrier := {f | MvPowerSeries.constantCoeff f ∈ maximalIdeal o ∧
          MvPowerSeries.coeff ei f ∈ maximalIdeal o}
        add_mem' := fun h h' => ⟨by simpa using add_mem h.1 h'.1, by simpa using add_mem h.2 h'.2⟩
        zero_mem' := by simp
        smul_mem' := fun f g h => ⟨hmul_zero f g ▸ Ideal.mul_mem_left _ _ h.1,
          hmul_ei f g ▸ add_mem (Ideal.mul_mem_left _ _ h.2) (Ideal.mul_mem_left _ _ h.1)⟩ }
    have hJ : maximalIdeal (MvPowerSeries (Fin m) o) ^ 2 ⊔
        ((maximalIdeal (MvPowerSeries (Fin m) o)).comap MvPowerSeries.C).map MvPowerSeries.C ≤ J := by
      refine sup_le ?_ (Ideal.map_le_iff_le_comap.2 fun a ha => ⟨by simpa [hm] using ha, by
        change MvPowerSeries.coeff ei (MvPowerSeries.C a) ∈ maximalIdeal o
        rw [MvPowerSeries.coeff_C]
        have hne : ei ≠ 0 := by
          intro h0
          have := congrArg (fun t : Fin m →₀ ℕ => t i) h0
          simp [ei] at this
        simp [hne]⟩)
      rw [sq]
      refine Ideal.mul_le.2 fun f hf g hg => ?_
      rw [hm] at hf hg
      exact ⟨hmul_zero f g ▸ Ideal.mul_mem_left _ _ hg,
        hmul_ei f g ▸ add_mem (Ideal.mul_mem_right _ _ hf) (Ideal.mul_mem_left _ _ hg)⟩
    have hmem := (hJ hc).2
    have hsum_coeff : MvPowerSeries.coeff ei
        (∑ j : Fin m, c j * (MvPowerSeries.X j : MvPowerSeries (Fin m) o)) =
        MvPowerSeries.constantCoeff (c i) := by
      rw [map_sum]
      have hterm : ∀ j : Fin m, MvPowerSeries.coeff ei
          (c j * (MvPowerSeries.X j : MvPowerSeries (Fin m) o)) =
          if j = i then MvPowerSeries.constantCoeff (c i) else 0 := by
        intro j
        rw [hmul_ei, hcoeff_single j, MvPowerSeries.constantCoeff_X, mul_zero, add_zero]
        split_ifs with hji <;> simp [hji]
      simp_rw [hterm]
      simp
    rw [hsum_coeff] at hmem
    rwa [hm]

end PowerSeriesParam

end RelativeParameters

/-! ## Section 4: Topological Krull Dimension & `krull_dim_le_of_irreducible_closeds` -/

section TopologicalKrullDimSection

/-- An inducing map reflects irreducibility of subsets from their images. -/
theorem isIrreducible_of_isInducing_image {S T : Type*} [TopologicalSpace S] [TopologicalSpace T]
    {f : S → T} (hf : Topology.IsInducing f) {s : Set S} (h : IsIrreducible (f '' s)) :
    IsIrreducible s := by
  refine ⟨h.nonempty.of_image, fun a b ha hb ⟨x, hx, hxa⟩ ⟨y, hy, hyb⟩ => ?_⟩
  obtain ⟨a, ha', rfl⟩ := hf.isOpen_iff.1 ha
  obtain ⟨b, hb', rfl⟩ := hf.isOpen_iff.1 hb
  obtain ⟨_, ⟨z, hz, rfl⟩, hza⟩ := h.2 a b ha' hb' ⟨_, ⟨x, hx, rfl⟩, hxa⟩ ⟨_, ⟨y, hy, rfl⟩, hyb⟩
  exact ⟨z, hz, hza⟩

/-- **Topological Krull Dimension Bound from Irreducible Closed Subsets (`krull_dim_le_of_irreducible_closeds`)**:
if every irreducible closed subset `Z : IrreducibleCloseds T` satisfies `topologicalKrullDim Z ≤ d`,
then `topologicalKrullDim T ≤ d`. -/
theorem krull_dim_le_of_irreducible_closeds {T : Type*} [TopologicalSpace T]
    {d : WithBot ℕ∞} (h : ∀ Z : IrreducibleCloseds T, topologicalKrullDim (Z : Set T) ≤ d) :
    topologicalKrullDim T ≤ d := by
  refine iSup_le fun p => le_trans ?_ (h p.last)
  let L : Set T := (p.last : IrreducibleCloseds T)
  have hle (i : Fin (p.length + 1)) : ((p i : IrreducibleCloseds T) : Set T) ⊆ L :=
    p.monotone (Fin.le_last i)
  have him (i : Fin (p.length + 1)) :
      Subtype.val '' ((Subtype.val : L → T) ⁻¹' (p i : IrreducibleCloseds T)) =
        (p i : IrreducibleCloseds T) := by
    rw [Subtype.image_preimage_coe, Set.inter_eq_right.2 (hle i)]
  let q : LTSeries (IrreducibleCloseds L) := LTSeries.mk p.length
    (fun i => ⟨Subtype.val ⁻¹' ((p i : IrreducibleCloseds T) : Set T),
      isIrreducible_of_isInducing_image .subtypeVal ((him i).symm ▸ (p i).isIrreducible),
      (p i).isClosed.preimage continuous_subtype_val⟩)
    fun i j hij => by
      refine lt_of_le_of_ne (fun z hz => p.monotone hij.le hz) fun e =>
        (p.strictMono hij).ne (IrreducibleCloseds.ext ?_)
      rw [← him i, ← him j]
      exact congrArg (fun Z : IrreducibleCloseds L => Subtype.val '' (Z : Set L)) e
  exact Order.LTSeries.length_le_krullDim q

/-- Monotonicity of topological Krull dimension under subset inclusion. -/
theorem krull_dim_mono {T : Type*} [TopologicalSpace T] {s t : Set T} (h : s ⊆ t) :
    topologicalKrullDim s ≤ topologicalKrullDim t :=
  (Topology.IsEmbedding.inclusion h).isInducing.topologicalKrullDim_le

/-- Bound `topologicalKrullDim s ≤ d` by checking every irreducible subset `Z ⊆ s`. -/
theorem krull_dim_le_of_isIrreducible {T : Type*} [TopologicalSpace T] {s : Set T}
    {d : WithBot ℕ∞} (h : ∀ Z ⊆ s, IsIrreducible Z → topologicalKrullDim Z ≤ d) :
    topologicalKrullDim s ≤ d := by
  refine krull_dim_le_of_irreducible_closeds fun Z => le_trans ?_
    (h (Subtype.val '' (Z : Set s)) (Subtype.coe_image_subset _ _)
      (Z.isIrreducible.image _ continuous_subtype_val.continuousOn))
  exact (Topology.IsEmbedding.subtypeVal.homeomorphImage
    (Z : Set s)).isInducing.topologicalKrullDim_le

/-- Finite closed union formula: `topologicalKrullDim (s ∪ t) = max (dim s) (dim t)`. -/
theorem krull_dim_union {T : Type*} [TopologicalSpace T] {s t : Set T}
    (hs : IsClosed s) (ht : IsClosed t) :
    topologicalKrullDim (s ∪ t :) = max (topologicalKrullDim s) (topologicalKrullDim t) := by
  refine le_antisymm (krull_dim_le_of_isIrreducible fun Z hZ hirr => ?_)
    (max_le (krull_dim_mono Set.subset_union_left) (krull_dim_mono Set.subset_union_right))
  rcases isPreirreducible_iff_isClosed_union_isClosed.1 hirr.2 s t hs ht hZ with h | h
  · exact (krull_dim_mono h).trans (le_max_left _ _)
  · exact (krull_dim_mono h).trans (le_max_right _ _)

/-- In a quasi-sober space, `topologicalKrullDim s` for closed `s` is the supremum over `x ∈ s`
of `topologicalKrullDim (closure {x})`. -/
theorem krull_dim_eq_iSup_closure {T : Type*} [TopologicalSpace T] [QuasiSober T]
    {s : Set T} (hs : IsClosed s) :
    topologicalKrullDim s = ⨆ x ∈ s, topologicalKrullDim (closure {x} : Set T) := by
  refine le_antisymm (krull_dim_le_of_isIrreducible fun Z hZ hirr => ?_)
    (iSup₂_le fun x hx => krull_dim_mono (hs.closure_subset_iff.2 (Set.singleton_subset_iff.2 hx)))
  have hx := hirr.isGenericPoint_genericPoint_closure
  refine le_iSup₂_of_le hirr.genericPoint (hs.closure_subset_iff.2 hZ hx.mem) (krull_dim_mono ?_)
  rw [hx.def]
  exact subset_closure

theorem krull_dim_eq_bot_iff {T : Type*} [TopologicalSpace T] :
    topologicalKrullDim T = ⊥ ↔ IsEmpty T := by
  rw [topologicalKrullDim, Order.krullDim_eq_bot_iff]
  exact ⟨fun h => ⟨fun x => h.false ⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩⟩,
    fun h => ⟨fun Z => h.false Z.isIrreducible.nonempty.some⟩⟩

private lemma isPreirreducible_preimage_open {T : Type*} [TopologicalSpace T]
    {S W : Set T} (hS : IsPreirreducible S) (hWo : IsOpen W) :
    IsPreirreducible ((Subtype.val : W → T) ⁻¹' S) := by
  intro u v hu hv ⟨x, hxS, hxu⟩ ⟨y, hyS, hyv⟩
  have hua : IsOpen ((Subtype.val : W → T) '' u) := hWo.isOpenMap_subtype_val u hu
  have hvb : IsOpen ((Subtype.val : W → T) '' v) := hWo.isOpenMap_subtype_val v hv
  obtain ⟨z, hzS, ⟨z', hz'u, hzeq1⟩, ⟨z'', hz''v, hzeq2⟩⟩ := hS _ _ hua hvb
    ⟨x.1, hxS, ⟨x, hxu, rfl⟩⟩ ⟨y.1, hyS, ⟨y, hyv, rfl⟩⟩
  have hzz : z' = z'' := Subtype.ext (hzeq1.trans hzeq2.symm)
  exact ⟨z', by simpa [← hzeq1] using hzS, hz'u, hzz ▸ hz''v⟩

/-- **Open-Cover Krull Dimension Bound (`krull_dim_le_of_openCover`)**:
if `{U i}` is an open cover of `T` and each `topologicalKrullDim (U i) ≤ d`, then
`topologicalKrullDim T ≤ d`. -/
theorem krull_dim_le_of_openCover {T : Type*} [TopologicalSpace T] {ι : Type*}
    (U : ι → Set T) (hUo : ∀ i, IsOpen (U i)) (hcov : (⋃ i, U i) = Set.univ)
    {d : WithBot ℕ∞} (hd : ∀ i, topologicalKrullDim (U i) ≤ d) :
    topologicalKrullDim T ≤ d := by
  refine iSup_le fun p => ?_
  obtain ⟨x, hx0⟩ := (p 0).isIrreducible.nonempty
  have hxU : x ∈ ⋃ i, U i := by rw [hcov]; trivial
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hxU
  let f : Fin (p.length + 1) → IrreducibleCloseds (U i) := fun k =>
    ⟨(Subtype.val : U i → T) ⁻¹' (p k : Set T),
      ⟨⟨⟨x, hxi⟩, p.monotone (Fin.zero_le k) hx0⟩,
        isPreirreducible_preimage_open (p k).isIrreducible.isPreirreducible (hUo i)⟩,
      (p k).isClosed.preimage continuous_subtype_val⟩
  have hf_strict : StrictMono f := by
    intro a b hab
    refine lt_of_le_of_ne (fun z hz => p.monotone hab.le hz) fun heq => ?_
    have hcl_eq : (p a : Set T) = (p b : Set T) := by
      refine subset_antisymm (p.monotone hab.le) fun z hz => ?_
      have hmem_cl : z ∈ closure ((p b : Set T) ∩ U i) := by
        rw [mem_closure_iff]
        intro V hVo hzV
        obtain ⟨w, hwb, hwV, hwU⟩ :=
          (p b).isIrreducible.isPreirreducible V (U i) hVo (hUo i) ⟨z, hz, hzV⟩
            ⟨x, p.monotone (Fin.zero_le b) hx0, hxi⟩
        exact ⟨w, hwV, hwb, hwU⟩
      have hinter_eq : (p b : Set T) ∩ U i = (p a : Set T) ∩ U i := by
        ext w
        constructor
        · rintro ⟨hwb, hwU⟩
          have hw' : (⟨w, hwU⟩ : U i) ∈ (f b : Set (U i)) := hwb
          rw [← heq] at hw'
          exact ⟨hw', hwU⟩
        · rintro ⟨hwa, hwU⟩
          exact ⟨p.monotone hab.le hwa, hwU⟩
      rw [hinter_eq] at hmem_cl
      exact (p a).isClosed.closure_subset_iff.2 Set.inter_subset_left hmem_cl
    exact (p.strictMono hab).ne (IrreducibleCloseds.ext hcl_eq)
  exact (Order.LTSeries.length_le_krullDim (LTSeries.mk p.length f hf_strict)).trans (hd i)

/-- Every ring with a `Subsingleton (PrimeSpectrum R)` (e.g. a field) has `ringKrullDim R = 0`. -/
theorem ringKrullDim_eq_zero_of_subsingleton {R : Type*} [CommRing R]
    [Subsingleton (PrimeSpectrum R)] [Nonempty (PrimeSpectrum R)] :
    ringKrullDim R = 0 := by
  refine le_antisymm (iSup_le fun s => ?_) ?_
  · have hs0 : s.length = 0 := by
      by_contra hne
      have hlt : (0 : ℕ) < s.length := Nat.pos_of_ne_zero hne
      have h01 := s.strictMono (show (⟨0, Nat.succ_pos _⟩ : Fin (s.length + 1)) <
        ⟨1, Nat.succ_lt_succ hlt⟩ by exact Fin.mk_lt_mk.mpr zero_lt_one)
      exact h01.ne (Subsingleton.elim _ _)
    simp [hs0]
  · obtain ⟨p⟩ := ‹Nonempty (PrimeSpectrum R)›
    exact Order.LTSeries.length_le_krullDim (LTSeries.mk 0 (fun _ => p) fun _ _ h => absurd h (by omega))

/-- Affine scheme Krull dimension equals `ringKrullDim R`. -/
theorem krull_dim_spec_eq_ringKrullDim (R : Type) [CommRing R] :
    topologicalKrullDim (Sp R) = ringKrullDim R :=
  PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim R

theorem krull_dim_spec_field_eq_zero (K : Type) [Field K] :
    topologicalKrullDim (Sp K) = 0 := by
  rw [krull_dim_spec_eq_ringKrullDim]
  exact ringKrullDim_eq_zero_of_subsingleton

/-- **Affine-Open-Cover Krull Dimension Bound (`krull_dim_le_of_affineCover`)**:
if `{U i}` is an open cover of a scheme `X` by affine opens (`haff : ∀ i, IsAffineOpen (U i)`)
each satisfying `ringKrullDim Γ(X, U i) ≤ d`, then `topologicalKrullDim X ≤ d`. -/
theorem krull_dim_le_of_affineCover {X : Scheme.{0}} {ι : Type*}
    (U : ι → X.Opens) (haff : ∀ i, IsAffineOpen (U i)) (hcov : (⋃ i, (U i : Set X)) = Set.univ)
    {d : WithBot ℕ∞} (hd : ∀ i, ringKrullDim Γ(X, U i) ≤ d) :
    topologicalKrullDim X ≤ d := by
  refine krull_dim_le_of_openCover (fun i => (U i : Set X)) (fun i => (U i).isOpen) hcov fun i => ?_
  let e : (U i : Set X) ≃ₜ PrimeSpectrum Γ(X, U i) :=
    TopCat.homeoOfIso (Scheme.forgetToTop.mapIso ((haff i).isoSpec))
  have hdim_eq : topologicalKrullDim (U i : Set X) ≤ topologicalKrullDim (PrimeSpectrum Γ(X, U i)) :=
    e.isInducing.topologicalKrullDim_le
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim] at hdim_eq
  exact hdim_eq.trans (hd i)

end TopologicalKrullDimSection

/-! ## Section 5: Regular Local Rings, `ToroidalChartData`, `HasRegularChart`, & Arakelov Bridges -/

section RegularChartsAndBridges

/-- **Regular Local Ring (`IsRegularLocalRing R`)**:
a Noetherian local ring `(R, 𝔪)` whose Krull dimension equals the `k_R`-dimension of its
Zariski cotangent space `𝔪 / 𝔪²`. -/
class IsRegularLocalRing (R : Type*) [CommRing R] : Prop extends IsLocalRing R, IsNoetherianRing R where
  krullDim_eq_cotangent_finrank :
    ringKrullDim R = (Module.finrank (ResidueField R) (CotangentSpace R) : WithBot ℕ∞)

/-- Every field `K` is a regular local ring of Krull dimension `0`. -/
theorem isRegularLocalRing_of_field (K : Type*) [Field K] : IsRegularLocalRing K where
  krullDim_eq_cotangent_finrank := by
    have h0 : ringKrullDim K = 0 := ringKrullDim_eq_zero_of_subsingleton
    have hm : maximalIdeal K = ⊥ := by
      ext x
      simp only [Ideal.mem_bot]
      constructor
      · intro hx
        by_contra hx0
        exact (IsLocalRing.notMem_maximalIdeal.mpr (IsUnit.mk0 x hx0)) hx
      · rintro rfl; exact Ideal.zero_mem _
    have hsub : Subsingleton (CotangentSpace K) := by
      refine ⟨fun x y => ?_⟩
      obtain ⟨⟨a, ha⟩, rfl⟩ := Ideal.toCotangent_surjective _ x
      obtain ⟨⟨b, hb⟩, rfl⟩ := Ideal.toCotangent_surjective _ y
      rw [hm] at ha hb
      simp only [Ideal.mem_bot] at ha hb
      subst ha hb
      rfl
    have hf : Module.finrank (ResidueField K) (CotangentSpace K) = 0 :=
      Module.finrank_zero_of_subsingleton
    rw [h0, hf]
    rfl

/-- Every discrete valuation ring is a 1-dimensional regular local ring! -/
theorem isRegularLocalRing_of_dvr (R : Type*) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] : IsRegularLocalRing R where
  krullDim_eq_cotangent_finrank := by
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
    have hm : maximalIdeal R = Ideal.span {ϖ} := by
      have hmax : (Ideal.span {ϖ} : Ideal R).IsMaximal :=
        PrincipalIdealRing.isMaximal_of_irreducible hϖ
      exact (IsLocalRing.eq_maximalIdeal hmax).symm
    have hprime_dichotomy : ∀ p : PrimeSpectrum R,
        p = ⟨⊥, Ideal.isPrime_bot⟩ ∨ p = IsLocalRing.closedPoint R := by
      intro p
      by_cases hbot : p.asIdeal = ⊥
      · exact Or.inl (PrimeSpectrum.ext hbot)
      · right
        have hmax : p.asIdeal.IsMaximal := p.isPrime.isMaximal hbot
        exact PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal hmax)
    have hbot_lt_closed :
        (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R) < IsLocalRing.closedPoint R := by
      refine lt_of_le_of_ne (show (⊥ : Ideal R) ≤ maximalIdeal R from bot_le) fun h => ?_
      have h_as : (⊥ : Ideal R) = maximalIdeal R := congrArg PrimeSpectrum.asIdeal h
      have hmem : ϖ ∈ (⊥ : Ideal R) := h_as ▸ (hm ▸ Ideal.subset_span rfl)
      exact hϖ.ne_zero (Ideal.mem_bot.mp hmem)
    have hdim : ringKrullDim R = 1 := by
      refine le_antisymm (iSup_le fun s => ?_) ?_
      · have hs1 : s.length ≤ 1 := by
          by_contra hgt
          have h2 : 2 ≤ s.length := by omega
          let p0 := s ⟨0, by omega⟩
          let p1 := s ⟨1, by omega⟩
          let p2 := s ⟨2, by omega⟩
          have h01 : p0 < p1 := s.strictMono (Fin.mk_lt_mk.mpr (by omega))
          have h12 : p1 < p2 := s.strictMono (Fin.mk_lt_mk.mpr (by omega))
          have hle_closed : ∀ p : PrimeSpectrum R, p ≤ IsLocalRing.closedPoint R := fun p =>
            (hprime_dichotomy p).elim (fun hp => hp ▸ hbot_lt_closed.le) (fun hp => hp ▸ le_rfl)
          have hbot_le : ∀ p : PrimeSpectrum R, (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R) ≤ p :=
            fun _ => bot_le
          have hp0_eq : p0 = ⟨⊥, Ideal.isPrime_bot⟩ := by
            rcases hprime_dichotomy p0 with h | h
            · exact h
            · exact absurd (h ▸ h01) (not_lt_of_ge (hle_closed p1))
          have hp2_eq : p2 = IsLocalRing.closedPoint R := by
            rcases hprime_dichotomy p2 with h | h
            · exact absurd (h ▸ h12) (not_lt_of_ge (hbot_le p1))
            · exact h
          rcases hprime_dichotomy p1 with h1 | h1
          · exact h01.ne (hp0_eq.trans h1.symm)
          · exact h12.ne (h1.trans hp2_eq.symm)
        exact_mod_cast hs1
      · let s : LTSeries (PrimeSpectrum R) := LTSeries.mk 1
          (Fin.cases ⟨⊥, Ideal.isPrime_bot⟩ (fun _ => IsLocalRing.closedPoint R))
          (fun i j hij => by
            fin_cases i <;> fin_cases j
            · exact absurd hij (lt_irrefl _)
            · exact hbot_lt_closed
            · exact absurd hij (by decide)
            · exact absurd hij (lt_irrefl _))
        exact Order.LTSeries.length_le_krullDim s
    have hspan_le : Module.finrank (ResidueField R) (CotangentSpace R) ≤ 1 := by
      let v0 : CotangentSpace R := Ideal.toCotangent (maximalIdeal R) ⟨ϖ, hm ▸ Ideal.subset_span rfl⟩
      have hgen : Submodule.span (ResidueField R) ({v0} : Set (CotangentSpace R)) = ⊤ := by
        rw [eq_top_iff]
        intro v _
        obtain ⟨⟨x, hx⟩, rfl⟩ := Ideal.toCotangent_surjective (maximalIdeal R) v
        rw [hm, Ideal.mem_span_singleton] at hx
        rcases hx with ⟨c, rfl⟩
        have hmul : (⟨ϖ * c, hm ▸ Ideal.mem_span_singleton.mpr ⟨c, rfl⟩⟩ : maximalIdeal R) =
            c • ⟨ϖ, hm ▸ Ideal.subset_span rfl⟩ := by
          ext; simp [mul_comm]
        have heq : Ideal.toCotangent (maximalIdeal R)
            ⟨ϖ * c, hm ▸ Ideal.mem_span_singleton.mpr ⟨c, rfl⟩⟩ =
            IsLocalRing.residue R c • v0 := by
          rw [hmul, map_smul]
          rfl
        rw [heq]
        exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)
      have hle := finrank_span_le_card (R := ResidueField R) ({v0} : Set (CotangentSpace R))
      rw [hgen, finrank_top] at hle
      simpa using hle
    have hpos : 0 < Module.finrank (ResidueField R) (CotangentSpace R) := by
      have hne : Nontrivial (CotangentSpace R) := by
        refine ⟨⟨Ideal.toCotangent (maximalIdeal R) ⟨ϖ, hm ▸ Ideal.subset_span rfl⟩, 0, ?_⟩⟩
        intro h0
        have hmem : ϖ ∈ maximalIdeal R ^ 2 :=
          (Ideal.toCotangent_eq_zero (maximalIdeal R) ⟨ϖ, hm ▸ Ideal.subset_span rfl⟩).mp h0
        rw [hm, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hmem
        rcases hmem with ⟨u, hu⟩
        have hu0 : 1 = ϖ * u := by
          apply mul_left_cancel₀ hϖ.ne_zero
          simpa [sq, mul_assoc] using hu
        exact hϖ.not_isUnit (IsUnit.of_mul_eq_one u hu0.symm)
      exact Module.finrank_pos
    have hfin : Module.finrank (ResidueField R) (CotangentSpace R) = 1 := by omega
    rw [hdim, hfin]
    rfl

/-- `PowerSeries K` over any field `K` is a 1-dimensional regular local ring. -/
theorem isRegularLocalRing_powerSeries_field (K : Type*) [Field K] :
    IsRegularLocalRing (PowerSeries K) :=
  isRegularLocalRing_of_dvr (PowerSeries K)

/-- `PowerSeries K` is `maximalIdeal`-adically complete. -/
theorem isAdicComplete_powerSeries_field (K : Type*) [Field K] :
    IsAdicComplete (maximalIdeal (PowerSeries K)) (PowerSeries K) := by
  have hm : maximalIdeal (PowerSeries K) = Ideal.span {PowerSeries.X} := by
    ext f
    rw [mem_maximalIdeal_powerSeries_iff, Ideal.mem_span_singleton, PowerSeries.X_dvd_iff]
    simp [mem_maximalIdeal, mem_nonunits_iff]
  rw [hm]
  refine { haus' := ?_, prec' := ?_ }
  · intro x hx
    ext k
    have hmem := hx (k + 1)
    rw [SModEq.zero, Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton, PowerSeries.X_pow_dvd_iff] at hmem
    simp [hmem k (Nat.lt_succ_self k)]
  · intro f hf
    refine ⟨PowerSeries.mk fun k => PowerSeries.coeff k (f (k + 1)), fun n => ?_⟩
    rw [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton, PowerSeries.X_pow_dvd_iff]
    intro d hd
    simp only [map_sub, PowerSeries.coeff_mk]
    have hle : d + 1 ≤ n := by omega
    have hfn := hf hle
    rw [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton, PowerSeries.X_pow_dvd_iff] at hfn
    have hd0 := hfn d (by omega)
    rw [map_sub, sub_eq_zero] at hd0
    rw [hd0, sub_self]

/-- **Étale-Complete Local Homomorphism (`IsEtaleCompletion φ`)**:
`φ : A →+* R` is flat, local, unramified (`𝔪_A R = 𝔪_R`), and `R` is `𝔪_R`-adically complete. -/
structure IsEtaleCompletion {A R : Type*} [CommRing A] [IsLocalRing A] [CommRing R] [IsLocalRing R]
    (φ : A →+* R) : Prop where
  localHom : IsLocalHom φ
  flat : φ.Flat
  unramified : (maximalIdeal A).map φ = maximalIdeal R
  complete : IsAdicComplete (maximalIdeal R) R

theorem IsEtaleCompletion.id {R : Type*} [CommRing R] [IsLocalRing R]
    (hcomp : IsAdicComplete (maximalIdeal R) R) : IsEtaleCompletion (RingHom.id R) where
  localHom := inferInstance
  flat := RingHom.Flat.id R
  unramified := Ideal.map_id _
  complete := hcomp

/-- **Toroidal Chart Data (`ToroidalChartData`)**:
a concrete regular complete local chart `ξ : Sp R ⟶ S` centered at `x : S` on an integral model
`s : S ⟶ Sp o` with open interior `j : U ⟶ S`, relative boundary coordinates `t : Fin m → R`,
and effective Cartier boundary divisor `BD` with multiplicities `a : Fin m → ℕ`. -/
structure ToroidalChartData {o : Type} [CommRing o] {U S : Scheme.{0}}
    (s : S ⟶ Sp o) (j : U ⟶ S) [IsOpenImmersion j] (BD : S.IdealSheafData) (x : S) : Type 1 where
  R : Type
  [cr : CommRing R]
  [reg : IsRegularLocalRing R]
  [dom : IsDomain R]
  b : o →+* R
  ξ : Sp R ⟶ S
  m : ℕ
  t : Fin m → R
  a : Fin m → ℕ
  complete : IsAdicComplete (maximalIdeal R) R
  comm_base : ξ ≫ s = spMap b
  center : ξ (closedPoint R) = x
  etale_comp : IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom
  rel_param : IsRelParam b t
  vanishing_bd :
    idlAlong (Scheme.IdealSheafData.vanishingIdeal ⟨(Set.range j)ᶜ, j.isOpenEmbedding.isOpen_range.isClosed_compl⟩) ξ =
      Ideal.span {∏ i, t i}
  mem_range_iff : ∀ p : Sp R, ξ p ∈ Set.range j ↔ ∏ i, t i ∉ p.asIdeal
  a_pos : ∀ i, 0 < a i
  bd_idl : idlAlong BD ξ = Ideal.span {∏ i, t i ^ a i}

attribute [instance] ToroidalChartData.cr ToroidalChartData.reg ToroidalChartData.dom

namespace ToroidalChartData

variable {o : Type} [CommRing o] {U S : Scheme.{0}} {s : S ⟶ Sp o} {j : U ⟶ S}
  [IsOpenImmersion j] {BD : S.IdealSheafData} {x : S}

/-- No boundary coordinate `t i` in a toroidal chart can vanish identically. -/
theorem boundary_ne_zero (C : ToroidalChartData s j BD x) (i : Fin C.m) : C.t i ≠ 0 :=
  C.rel_param.ne_zero i

/-- The product `∏ i, t i` defining the boundary divisor on the chart is nonzero. -/
theorem prod_boundary_ne_zero (C : ToroidalChartData s j BD x) : (∏ i, C.t i) ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun i _ => C.boundary_ne_zero i

/-- The generic point `⊥` of `Sp C.R` maps into the open interior `Set.range j`! -/
theorem generic_mem_interior (C : ToroidalChartData s j BD x) :
    C.ξ (⟨⊥, Ideal.isPrime_bot⟩ : Sp C.R) ∈ Set.range j := by
  have hiff := C.mem_range_iff (⟨⊥, Ideal.isPrime_bot⟩ : Sp C.R)
  rw [hiff]
  change (∏ i, C.t i) ∉ (⊥ : Ideal C.R)
  rw [Ideal.mem_bot]
  exact C.prod_boundary_ne_zero

/-- On any toroidal chart, `stalkId BD x = ⊤ ↔ x ∈ Set.range j`. -/
theorem idl_eq_top_iff (C : ToroidalChartData s j BD x) :
    stalkId BD x = ⊤ ↔ x ∈ Set.range j := by
  have e1 : stalkId BD (C.ξ (closedPoint C.R)) = ⊤ ↔ idlAlong BD C.ξ = ⊤ :=
    (idlAlong_eq_top_iff BD C.ξ).symm
  rw [← C.center]
  refine e1.trans (Iff.trans ?_ (C.mem_range_iff (closedPoint C.R)).symm)
  rw [C.bd_idl, Ideal.span_singleton_eq_top, ← notMem_maximalIdeal]
  change ∏ i, C.t i ^ C.a i ∉ maximalIdeal C.R ↔ ∏ i, C.t i ∉ maximalIdeal C.R
  have hprim := (maximalIdeal.isMaximal C.R).isPrime
  simp only [hprim.prod_mem_iff, Finset.mem_univ, true_and, not_exists]
  exact forall_congr' fun i => not_congr (hprim.pow_mem_iff_mem (C.a i) (C.a_pos i))

end ToroidalChartData

/-- **Regular Toroidal Chart Existence (`HasRegularChart`)**:
`x : S` admits a regular complete toroidal chart over `s : S ⟶ Sp o` with interior `j` and
effective boundary divisor `BD`. -/
def HasRegularChart {o : Type} [CommRing o] {U S : Scheme.{0}}
    (s : S ⟶ Sp o) (j : U ⟶ S) [IsOpenImmersion j] (BD : S.IdealSheafData) (x : S) : Prop :=
  Nonempty (ToroidalChartData s j BD x)

theorem HasRegularChart.idl_eq_top_iff {o : Type} [CommRing o] {U S : Scheme.{0}}
    {s : S ⟶ Sp o} {j : U ⟶ S} [IsOpenImmersion j] {BD : S.IdealSheafData} {x : S}
    (h : HasRegularChart s j BD x) :
    stalkId BD x = ⊤ ↔ x ∈ Set.range j :=
  h.some.idl_eq_top_iff

/-- If every point of a nonempty scheme `S` admits a regular toroidal chart, the interior `Set.range j`
is nonempty (witnessed by the generic point of any chart). -/
theorem HasRegularChart.interior_nonempty_of_nonempty {o : Type} [CommRing o] {U S : Scheme.{0}}
    {s : S ⟶ Sp o} {j : U ⟶ S} [IsOpenImmersion j] {BD : S.IdealSheafData}
    [Nonempty S] (h : ∀ x : S, HasRegularChart s j BD x) :
    (Set.range j).Nonempty := by
  obtain ⟨x⟩ := ‹Nonempty S›
  obtain ⟨C⟩ := h x
  exact ⟨_, C.generic_mem_interior⟩

/-- **Concrete 0-Assumption Power-Series DVR Toroidal Chart**:
for any field `K`, on `S = Sp (PowerSeries K)` over `Sp K` with open interior
`j = (S.basicOpen X).ι` (`D(X)`), `PowerSeries K` furnishes `IsRelParam PowerSeries.C ![X]`,
`IsRegularLocalRing (PowerSeries K)`, `IsAdicComplete`, and `p ∈ Set.range j ↔ X ∉ p.asIdeal`! -/
theorem hasRegularChart_powerSeries_closedPoint (K : Type) [Field K] :
    let R := PowerSeries K
    let S := Sp R
    let Uopen : S.Opens := ⟨(PrimeSpectrum.basicOpen (PowerSeries.X : R) : Set (PrimeSpectrum R)),
      (PrimeSpectrum.basicOpen (PowerSeries.X : R)).isOpen⟩
    let j : (Uopen : Scheme.{0}) ⟶ S := Uopen.ι
    IsRelParam (PowerSeries.C (R := K)) ![(PowerSeries.X : R)] ∧
    IsRegularLocalRing R ∧
    IsAdicComplete (maximalIdeal R) R ∧
    (∀ p : Sp R, p ∈ Set.range j ↔ PowerSeries.X ∉ p.asIdeal) := by
  intro R S Uopen j
  refine ⟨isRelParam_powerSeries_X K, isRegularLocalRing_powerSeries_field K,
    isAdicComplete_powerSeries_field K, ?_⟩
  intro p
  have hrange : Set.range j = (Uopen : Set S) := Subtype.range_coe
  rw [hrange]
  exact Iff.rfl

/-! ### Stage 11 & Stage 12 Arakelov / Moriwaki Chart Bridges -/

/-- **Bridge to `Stage11ArakelovFaltings` & `Stage12SchurWeylLattices`**:
given a graded Hermitian section algebra `A : Stage12SchurWeylLattices.GradedHermAlgebra d` over
a base scheme `S` of topological Krull dimension `≤ d + 1` with `0 < A.volAr`:
1. `topologicalKrullDim S ≤ d + 1` via `krull_dim_le_of_irreducible_closeds`,
2. Moriwaki small integral sections grow exponentially (`c₀ * k^(d+1) ≤ log (#smallSections A k)`),
3. Eventually `∃ s ∈ A.secLat k, s ≠ 0 ∧ A.supNorm k s.1 < 1`! -/
theorem integral_model_moriwaki_small_sections_bridge
    {d : ℕ} (A : Stage12SchurWeylLattices.GradedHermAlgebra d) (hvol : 0 < A.volAr)
    {S : Scheme.{0}}
    (hZ : ∀ Z : IrreducibleCloseds S, topologicalKrullDim (Z : Set S) ≤ ((d + 1 : ℕ) : WithBot ℕ∞)) :
    topologicalKrullDim S ≤ ((d + 1 : ℕ) : WithBot ℕ∞) ∧
    (∃ c₀ : ℝ, 0 < c₀ ∧ ∃ K₀ : ℕ, ∃ hK₀ : 1 ≤ K₀,
      ∀ k : ℕ, (hk : K₀ ≤ k) →
        c₀ * (k : ℝ) ^ (d + 1) ≤ Real.log (A.smallSectionsCard k (le_trans hK₀ hk) : ℝ)) ∧
    (∃ K₀ : ℕ, 1 ≤ K₀ ∧
      ∀ k : ℕ, (hk : K₀ ≤ k) →
        ∃ s : A.secLat k, s ≠ 0 ∧ A.supNorm k s.1 < 1) := by
  refine ⟨krull_dim_le_of_irreducible_closeds hZ,
    Stage12SchurWeylLattices.moriwaki_big_small_sections A hvol,
    Stage12SchurWeylLattices.moriwaki_exists_nonzero_small_section A hvol⟩

/-- **Bridge to `Stage12SchurWeylLattices.CMHermLattice` & `Stage11ArakelovFaltings`**:
a regular toroidal chart's boundary multiplicities `a : Fin m → ℕ` induce an explicit positive-metric
scaling of any rank-`r` CM Hermitian lattice `Λ : CMHermLattice d r` (modeling boundary twists
`𝒪(-∑ a_i D_i)`), scaling `covol` by `exp (-r * w)` and shifting `slope` by `+ w / 2`! -/
theorem chart_boundary_twist_cmLattice_slope
    {o : Type} [CommRing o] {U S : Scheme.{0}} {s : S ⟶ Sp o} {j : U ⟶ S}
    [IsOpenImmersion j] {BD : S.IdealSheafData} {x : S}
    (C : ToroidalChartData s j BD x)
    {d r : ℕ} (Λ : Stage12SchurWeylLattices.CMHermLattice d r) :
    let w : ℝ := ∑ i : Fin C.m, (C.a i : ℝ)
    let Λ' := Λ.scaleMetric (Real.exp_pos (-w))
    ArakelovCovolume.slope Λ'.euclLat = ArakelovCovolume.slope Λ.euclLat + (1 / 2) * w ∧
    ArakelovCovolume.covol Λ'.euclLat = (Real.exp (-w)) ^ r * ArakelovCovolume.covol Λ.euclLat := by
  intro w Λ'
  refine ⟨?_, Λ.covol_scaleMetric (Real.exp_pos (-w))⟩
  rw [Λ.slope_scaleMetric (Real.exp_pos (-w)), Real.log_exp]
  ring

end RegularChartsAndBridges

end RHDirect.Stage14M3_IntegralSchemesAndCharts

end
