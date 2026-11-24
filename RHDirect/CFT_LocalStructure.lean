import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.Valuation.ValuationRing
import Mathlib.RingTheory.Valuation.Integers
import Mathlib.RingTheory.Valuation.Integral
import Mathlib.RingTheory.Valuation.RankOne
import Mathlib.RingTheory.Valuation.Discrete.Basic
import Mathlib.RingTheory.Valuation.Discrete.RankOne
import Mathlib.RingTheory.Valuation.ExtendToLocalization
import Mathlib.RingTheory.Valuation.Extension
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.NumberTheory.RamificationInertia.Inertia
import Mathlib.NumberTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.RingTheory.PowerSeries.Evaluation
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.NumberTheory.Padics.ValuativeRel
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.AdicCompletion.RingHom
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.HahnSeries.Basic
import Mathlib.RingTheory.HahnSeries.Valuation
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.Norm.Basic
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.RingTheory.Trace.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.Over
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.NumberTheory.Padics.Hensel
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.FieldTheory.Separable
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Topology.Algebra.Valued.ValuativeRel
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.Topology.Algebra.Valued.WithVal
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.LinearTopology
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
import Mathlib.Topology.Algebra.Nonarchimedean.Bases
import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
import Mathlib.Topology.Algebra.InfiniteSum.Group
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Algebra.GroupCompletion
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.MetricSpace.Ultra.Basic
import Mathlib.Analysis.Normed.Field.ProperSpace
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Multiplicity
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# RHDirect.CFT_LocalStructure

Local Field Structure Foundation (`namespace RHDirect.CFT.LocalField`):
- Core `IsNonarchimedeanLocalField` interface, finite extensions, integer rings, uniqueness of valuation
- Unit group filtration `unitFiltration`, Galois action on units, Teichmüller & `n`-th powers
- Filtered surjectivity, `unitFiltration` completeness & separatedness
- Local field examples (`ℚ_p`, char-0 embedding, equal-char Teichmüller & Laurent series `k((t))`)
- Norm & power image unit-filtration containment
- `p`-adic logarithm & exponential series, homomorphisms, `ℤ_p`-module structure and rank of principal units
- Complete trivial cohomology (`TateZero`/`TateNegOne`, `StableFiltration`) & Hilbert 90 for cyclic extensions
-/

noncomputable section

namespace RHDirect.CFT.LocalField


/-! ### Interface -/
section Sec_Interface

open ValuativeRel

section Algebraic

variable (K L : Type*) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
  [Algebra K L] [ValuativeExtension K L]

instance valuation_hasExtension : (valuation K).HasExtension (valuation L) where
  val_isEquiv_comap a b := by
    rw [Valuation.comap_apply, Valuation.comap_apply, ← Valuation.vle_iff_le,
      ← Valuation.vle_iff_le, ValuativeExtension.vle_iff_vle]

@[simp]
theorem coe_algebraMap_integer (x : 𝒪[K]) :
    ((algebraMap 𝒪[K] 𝒪[L] x : 𝒪[L]) : L) = algebraMap K L (x : K) :=
  rfl

theorem algebraMap_integer_injective : Function.Injective (algebraMap 𝒪[K] 𝒪[L]) :=
  Valuation.HasExtension.algebraMap_injective

theorem algebraMap_mem_integer_iff (x : K) : algebraMap K L x ∈ 𝒪[L] ↔ x ∈ 𝒪[K] := by
  simp only [Valuation.mem_integer_iff]
  exact Valuation.HasExtension.val_map_le_one_iff (valuation K) (valuation L) x

example : IsScalarTower 𝒪[K] 𝒪[L] L := inferInstance
example : IsScalarTower 𝒪[K] K L := inferInstance
example : IsLocalHom (algebraMap 𝒪[K] 𝒪[L]) := inferInstance
example : Algebra 𝓀[K] 𝓀[L] := inferInstance
example : FaithfulSMul 𝒪[K] 𝒪[L] := inferInstance

end Algebraic

section Topological

variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L]

theorem continuous_algebraMap : Continuous (algebraMap K L) := by
  refine continuous_of_continuousAt_zero (algebraMap K L) ?_
  rw [ContinuousAt, map_zero, (IsValuativeTopology.hasBasis_nhds_zero K).tendsto_iff
    (IsValuativeTopology.hasBasis_nhds_zero L)]
  intro γ _
  obtain ⟨δ, hδ0, hδ1⟩ := IsNontrivial.exists_lt_one (R := K)
  obtain ⟨a, rfl⟩ := valuation_surjective δ
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp at hδ0
  have hb : valuation L (algebraMap K L a) < 1 := by
    exact (Valuation.HasExtension.val_map_lt_one_iff (valuation K) (valuation L) a).mpr hδ1
  obtain ⟨n, hn⟩ := exists_pow_lt₀ hb γ
  refine ⟨Units.mk0 (valuation K (a ^ n)) (by simp [ha0]), trivial, fun x hx => ?_⟩
  simp only [Set.mem_ofPred_eq, Units.val_mk0] at hx ⊢
  calc valuation L (algebraMap K L x) < valuation L (algebraMap K L (a ^ n)) := by
        rw [← (valuation L).vlt_iff_lt, ValuativeExtension.vlt_iff_vlt, (valuation K).vlt_iff_lt]
        exact hx
    _ = valuation L (algebraMap K L a) ^ n := by simp
    _ < γ := hn

instance continuousSMul : ContinuousSMul K L :=
  continuousSMul_of_algebraMap K L (continuous_algebraMap K L)

end Topological

end Sec_Interface


/-! ### FiniteExtension -/
section Sec_FiniteExtension

open ValuativeRel

section Base

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

@[instance_reducible]
def normedField : NontriviallyNormedField K :=
  letI := IsTopologicalAddGroup.rightUniformSpace K
  haveI := isUniformAddGroup_of_addCommGroup (G := K)
  letI : (Valued.v (R := K)).RankOne :=
  { hom' := IsRankLeOne.nonempty.some.emb (R := K).comp MonoidWithZeroHom.ValueGroup₀.embedding
    strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  Valued.toNontriviallyNormedField K (ValueGroupWithZero K)

theorem normedField_topology :
    (normedField K).toUniformSpace.toTopologicalSpace = ‹TopologicalSpace K› := rfl

theorem normedField_norm_le_norm_iff (x y : K) :
    letI := normedField K
    ‖x‖ ≤ ‖y‖ ↔ x ≤ᵥ y := by
  let := IsTopologicalAddGroup.rightUniformSpace K
  have := isUniformAddGroup_of_addCommGroup (G := K)
  let : (Valued.v (R := K)).RankOne :=
  { hom' := IsRankLeOne.nonempty.some.emb (R := K).comp MonoidWithZeroHom.ValueGroup₀.embedding
    strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  rw [(valuation K).vle_iff_le]
  exact Valued.toNormedField.norm_le_iff

theorem normedField_isUltrametricDist :
    letI := normedField K
    IsUltrametricDist K := by
  let := normedField K
  refine IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm fun x y => ?_
  rcases vle_add_cases x y with h | h
  · exact ((normedField_norm_le_norm_iff K _ _).2 h).trans (le_max_left _ _)
  · exact ((normedField_norm_le_norm_iff K _ _).2 h).trans (le_max_right _ _)

theorem normedField_completeSpace :
    letI := normedField K
    CompleteSpace K := by
  let := IsTopologicalAddGroup.rightUniformSpace K
  have := isUniformAddGroup_of_addCommGroup (G := K)
  exact (inferInstance : CompleteSpace K)

theorem normedField_properSpace :
    letI := normedField K
    ProperSpace K := by
  let := normedField K
  exact .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace K

end Base

section Extension

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]

@[instance_reducible]
def spectralNormedField : NontriviallyNormedField L :=
  letI := normedField K
  haveI := normedField_isUltrametricDist K
  haveI := normedField_completeSpace K
  spectralNorm.nontriviallyNormedField K L

theorem spectralNormedField_norm (x : L) :
    letI := normedField K
    letI := spectralNormedField K L
    ‖x‖ = spectralNorm K L x := rfl

theorem spectralNormedField_isUltrametricDist :
    letI := spectralNormedField K L
    IsUltrametricDist L := by
  let := normedField K
  have := normedField_isUltrametricDist K
  have := normedField_completeSpace K
  let := spectralNormedField K L
  exact IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm
    (isNonarchimedean_spectralNorm (K := K) (L := L))

theorem spectralNormedField_norm_algebraMap (a : K) :
    letI := normedField K
    letI := spectralNormedField K L
    ‖algebraMap K L a‖ = ‖a‖ := by
  let := normedField K
  exact spectralNorm_extends a

structure LocalFieldStructure (L : Type*) [Field L] where

  rel : ValuativeRel L

  top : TopologicalSpace L

@[instance_reducible]
def finiteExtensionStructure : LocalFieldStructure L :=
  letI := spectralNormedField K L
  haveI := spectralNormedField_isUltrametricDist K L
  { rel := ValuativeRel.ofValuation (NormedField.valuation (K := L))
    top := inferInstance }

theorem finiteExtensionStructure_vle_iff (x y : L) :
    letI := normedField K
    letI := spectralNormedField K L
    letI := (finiteExtensionStructure K L).rel
    x ≤ᵥ y ↔ ‖x‖ ≤ ‖y‖ := Iff.rfl

theorem finiteExtensionStructure_top :
    (finiteExtensionStructure K L).top =
      (spectralNormedField K L).toUniformSpace.toTopologicalSpace := rfl

theorem finiteExtensionStructure_valuativeExtension :
    letI := (finiteExtensionStructure K L).rel
    ValuativeExtension K L := by
  let := (finiteExtensionStructure K L).rel
  constructor
  intro a b
  rw [finiteExtensionStructure_vle_iff, spectralNormedField_norm_algebraMap,
    spectralNormedField_norm_algebraMap, normedField_norm_le_norm_iff]

theorem finiteExtensionStructure_isNonarchimedeanLocalField :
    letI := (finiteExtensionStructure K L).rel
    letI := (finiteExtensionStructure K L).top
    IsNonarchimedeanLocalField L := by
  let := normedField K
  have := normedField_isUltrametricDist K
  have := normedField_completeSpace K
  have := normedField_properSpace K
  let := spectralNormedField K L
  have := spectralNormedField_isUltrametricDist K L
  let := (finiteExtensionStructure K L).rel
  have hc : (NormedField.valuation (K := L)).Compatible := Valuation.Compatible.ofValuation _
  refine { toIsValuativeTopology := ?_, toLocallyCompactSpace := ?_, toIsNontrivial := ?_ }
  · exact IsValuativeTopology.of_mem_nhds_zero_iff_vle (NormedField.valuation (K := L))
      (fun {s} => (NormedField.toValued (K := L)).is_topological_valuation s)
  · let : NormedSpace K L := spectralNorm.normedSpace K L
    have : ProperSpace L := FiniteDimensional.proper K L
    infer_instance
  · rw [isNontrivial_iff_isNontrivial (NormedField.valuation (K := L))]
    infer_instance

theorem exists_isNonarchimedeanLocalField_valuativeExtension :
    ∃ (_ : ValuativeRel L) (_ : TopologicalSpace L),
      IsNonarchimedeanLocalField L ∧ ValuativeExtension K L :=
  ⟨(finiteExtensionStructure K L).rel, (finiteExtensionStructure K L).top,
    finiteExtensionStructure_isNonarchimedeanLocalField K L,
    finiteExtensionStructure_valuativeExtension K L⟩

end Extension

end Sec_FiniteExtension


/-! ### Integers -/
section Sec_Integers

open ValuativeRel

section Algebraic

variable (K L : Type*) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
  [Algebra K L] [ValuativeExtension K L]

abbrev ramificationIndex : ℕ := (IsLocalRing.maximalIdeal 𝒪[L]).ramificationIdx 𝒪[K]

abbrev residueDegree : ℕ := (IsLocalRing.maximalIdeal 𝒪[L]).inertiaDeg 𝒪[K]

end Algebraic

section Topological

variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L]

instance t2Space : T2Space L := by
  let := IsTopologicalAddGroup.rightUniformSpace L
  have := isUniformAddGroup_of_addCommGroup (G := L)
  infer_instance

variable [FiniteDimensional K L]

theorem exists_basis_coord_bound : ∃ a : K, a ≠ 0 ∧ ∀ x : L, valuation L x ≤ 1 →
    ∀ i, valuation K ((Module.finBasis K L).repr x i / a) ≤ 1 := by
  let := normedField K
  have := normedField_completeSpace K
  let b := Module.finBasis K L
  let e := b.equivFun.toContinuousLinearEquiv
  have hc : IsCompact (e '' {x : L | valuation L x ≤ 1}) :=
    (IsNonarchimedeanLocalField.isCompact_closedBall L 1).image e.continuous
  obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall 0).1 hc.isBounded
  obtain ⟨a, ha⟩ := NormedField.exists_lt_norm K (max r 1)
  have ha0 : 0 < ‖a‖ := lt_of_lt_of_le zero_lt_one (le_max_right r 1) |>.trans ha
  refine ⟨a, norm_pos_iff.1 ha0, fun x hx i => ?_⟩
  have h1 : ‖e x‖ ≤ r := by simpa using hr ⟨x, hx, rfl⟩
  have h2 : ‖b.repr x i‖ ≤ r := (norm_le_pi_norm (e x) i).trans h1
  have h3 : ‖b.repr x i / a‖ ≤ ‖(1 : K)‖ := by
    rw [norm_div, norm_one, div_le_one ha0]
    exact h2.trans ((le_max_left r 1).trans ha.le)
  have := (normedField_norm_le_norm_iff K _ _).1 h3
  rwa [(valuation K).vle_iff_le, map_one] at this

theorem finite_integer : Module.Finite 𝒪[K] 𝒪[L] := by
  obtain ⟨a, ha, hb⟩ := exists_basis_coord_bound K L
  let b := Module.finBasis K L
  let N : Submodule 𝒪[K] L := Submodule.span 𝒪[K] (Set.range fun i => a • b i)
  have hN : N.FG := Submodule.fg_span (Set.finite_range _)
  have : IsNoetherian 𝒪[K] N := isNoetherian_of_fg_of_noetherian N hN
  have hmem : ∀ x : 𝒪[L], (x : L) ∈ N := by
    intro x
    have hx : valuation L (x : L) ≤ 1 := x.2
    rw [← b.sum_repr (x : L)]
    refine Submodule.sum_mem _ fun i _ => ?_
    have hc := hb x hx i
    have : b.repr x i • b i = (⟨b.repr x i / a, hc⟩ : 𝒪[K]) • (a • b i) := by
      rw [← algebraMap_smul K (⟨_, hc⟩ : 𝒪[K]) (a • b i), smul_smul]
      congr 1
      exact (div_mul_cancel₀ _ ha).symm
    rw [this]
    exact N.smul_mem _ (Submodule.subset_span ⟨i, rfl⟩)
  let f : 𝒪[L] →ₗ[𝒪[K]] N :=
    LinearMap.codRestrict N ((IsScalarTower.toAlgHom 𝒪[K] 𝒪[L] L).toLinearMap) fun x => hmem x
  refine Module.Finite.of_injective f fun x y h => ?_
  have h' := congrArg Subtype.val h
  exact Subtype.ext h'

instance : Module.Finite 𝒪[K] 𝒪[L] := finite_integer K L

theorem free_integer : Module.Free 𝒪[K] 𝒪[L] := Module.free_of_finite_type_torsion_free'

instance : Module.Free 𝒪[K] 𝒪[L] := free_integer K L

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [FiniteDimensional K L] in

theorem finrank_integer : Module.finrank 𝒪[K] 𝒪[L] = Module.finrank K L :=
  (IsFractionRing.finrank_eq 𝒪[K] K 𝒪[L] L).symm

theorem isIntegral_iff (x : L) : IsIntegral 𝒪[K] x ↔ valuation L x ≤ 1 := by
  constructor
  · intro hx
    have h2 : IsIntegral 𝒪[L] x := hx.tower_top
    obtain ⟨y, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.1 h2
    exact y.2
  · intro hx
    have : IsIntegral 𝒪[K] (⟨x, hx⟩ : 𝒪[L]) := Algebra.IsIntegral.isIntegral _
    exact this.map (IsScalarTower.toAlgHom 𝒪[K] 𝒪[L] L)

instance isIntegralClosure : IsIntegralClosure 𝒪[L] 𝒪[K] L where
  algebraMap_injective := Subtype.val_injective
  isIntegral_iff {x} := by
    rw [isIntegral_iff]
    exact ⟨fun h => ⟨⟨x, h⟩, rfl⟩, by rintro ⟨y, rfl⟩; exact y.2⟩

theorem isDiscreteValuationRing : IsDiscreteValuationRing 𝒪[L] := inferInstance

theorem primesOver_eq : (IsLocalRing.maximalIdeal 𝒪[K]).primesOver 𝒪[L] =
    {IsLocalRing.maximalIdeal 𝒪[L]} := by
  ext P
  constructor
  · rintro ⟨hP, hl⟩
    have : P.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal P (IsLocalRing.maximalIdeal 𝒪[K])
    exact IsLocalRing.eq_maximalIdeal this
  · rintro rfl
    exact ⟨inferInstance, inferInstance⟩

instance uniquePrimesOver : Unique ((IsLocalRing.maximalIdeal 𝒪[K]).primesOver 𝒪[L]) where
  default := ⟨IsLocalRing.maximalIdeal 𝒪[L], inferInstance, inferInstance⟩
  uniq P := Subtype.ext (Set.mem_singleton_iff.1 ((Set.ext_iff.1 (primesOver_eq K L) P.1).1 P.2))

theorem ramificationIndex_mul_residueDegree :
    ramificationIndex K L * residueDegree K L = Module.finrank K L := by
  let : Fintype ((IsLocalRing.maximalIdeal 𝒪[K]).primesOver 𝒪[L]) := Fintype.ofFinite _
  have := Ideal.sum_ramification_inertia_eq_finrank (IsLocalRing.maximalIdeal 𝒪[K]) 𝒪[L]
  rw [Fintype.sum_unique, finrank_integer] at this
  exact this

theorem maximalIdeal_ne_bot : IsLocalRing.maximalIdeal 𝒪[K] ≠ ⊥ :=
  IsDiscreteValuationRing.not_a_field _

theorem map_maximalIdeal :
    (IsLocalRing.maximalIdeal 𝒪[K]).map (algebraMap 𝒪[K] 𝒪[L]) =
      IsLocalRing.maximalIdeal 𝒪[L] ^ ramificationIndex K L := by
  have hne : (IsLocalRing.maximalIdeal 𝒪[K]).map (algebraMap 𝒪[K] 𝒪[L]) ≠ ⊥ :=
    Ideal.map_ne_bot_of_ne_bot (maximalIdeal_ne_bot K)
  obtain ⟨n, hn⟩ := exists_maximalIdeal_pow_eq_of_principal 𝒪[L]
    (IsPrincipalIdealRing.principal _) _ hne
  have hL : IsLocalRing.maximalIdeal 𝒪[L] ≠ ⊥ := IsDiscreteValuationRing.not_a_field _
  have h : (IsLocalRing.maximalIdeal 𝒪[K]).ramificationIdx' (IsLocalRing.maximalIdeal 𝒪[L]) = n :=
    Ideal.ramificationIdx'_spec hn.le (by
      rw [hn]
      exact not_le_of_gt (Ideal.pow_succ_lt_pow hL n))
  rw [ramificationIndex, ← Ideal.ramificationIdx'_eq_ramificationIdx _ _ (maximalIdeal_ne_bot K), h,
    hn]

theorem ramificationIndex_pos : 0 < ramificationIndex K L := Ideal.ramificationIdx_pos _ _

theorem residueDegree_pos : 0 < residueDegree K L := Ideal.inertiaDeg_pos _ _

theorem residueDegree_eq_finrank : residueDegree K L = Module.finrank 𝓀[K] 𝓀[L] :=
  Ideal.inertiaDeg_eq_of_isMaximal (IsLocalRing.maximalIdeal 𝒪[K]) (IsLocalRing.maximalIdeal 𝒪[L])

end Topological

section Tower

variable (K L M : Type*) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
  [Field M] [ValuativeRel M] [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]

theorem valuativeExtension_trans [ValuativeExtension K L] [ValuativeExtension L M] :
    ValuativeExtension K M where
  vle_iff_vle a b := by
    rw [IsScalarTower.algebraMap_apply K L M, IsScalarTower.algebraMap_apply K L M,
      ValuativeExtension.vle_iff_vle, ValuativeExtension.vle_iff_vle]

variable [ValuativeExtension K L] [ValuativeExtension L M] [ValuativeExtension K M]

instance isScalarTower_integer : IsScalarTower 𝒪[K] 𝒪[L] 𝒪[M] :=
  IsScalarTower.of_algebraMap_eq fun x =>
    Subtype.ext (IsScalarTower.algebraMap_apply K L M (x : K))

theorem residueDegree_tower :
    residueDegree K M = residueDegree K L * residueDegree L M :=
  Ideal.inertiaDeg_tower _ _

theorem ramificationIndex_tower [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [TopologicalSpace M] [IsNonarchimedeanLocalField M] [FiniteDimensional L M] :
    ramificationIndex K M = ramificationIndex K L * ramificationIndex L M :=
  Ideal.ramificationIdx_tower _ _

end Tower

end Sec_Integers


/-! ### Uniqueness -/
section Sec_Uniqueness

open ValuativeRel Topology Filter

section Topology

variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]

theorem t2Space_of_isNonarchimedeanLocalField : T2Space L := by
  let := IsTopologicalAddGroup.rightUniformSpace L
  have := isUniformAddGroup_of_addCommGroup (G := L)
  infer_instance

@[instance_reducible]
def nontriviallyNormedField : NontriviallyNormedField K :=
  letI := IsTopologicalAddGroup.rightUniformSpace K
  haveI := isUniformAddGroup_of_addCommGroup (G := K)
  letI : (Valued.v (R := K)).RankOne :=
  { hom' := IsRankLeOne.nonempty.some.emb (R := K).comp MonoidWithZeroHom.ValueGroup₀.embedding
    strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  Valued.toNontriviallyNormedField K (ValueGroupWithZero K)

example : (nontriviallyNormedField K).toUniformSpace.toTopologicalSpace = ‹TopologicalSpace K› :=
  rfl

theorem completeSpace_nontriviallyNormedField :
    @CompleteSpace K (nontriviallyNormedField K).toUniformSpace := by
  let := IsTopologicalAddGroup.rightUniformSpace K
  have := isUniformAddGroup_of_addCommGroup (G := K)
  exact (inferInstance : CompleteSpace K)

variable [Algebra K L] [ValuativeExtension K L]

theorem isModuleTopology [FiniteDimensional K L] : IsModuleTopology K L := by
  let := nontriviallyNormedField K
  have := completeSpace_nontriviallyNormedField K
  have := t2Space_of_isNonarchimedeanLocalField L
  exact isModuleTopologyOfFiniteDimensional

end Topology

section Nilpotent

variable {F : Type*} [Field F] [ValuativeRel F]

theorem vle_iff_not_valuation_div_lt_one {x : F} (hx : x ≠ 0) (y : F) :
    x ≤ᵥ y ↔ ¬ valuation F (y / x) < 1 := by
  have hx' : 0 < valuation F x := by
    rw [zero_lt_iff]
    simpa using hx
  rw [(valuation F).vle_iff_le, map_div₀, div_lt_one₀ hx', not_lt]

theorem vle_map_iff_of_valuation_lt_one_iff {F' : Type*} [Field F'] [ValuativeRel F']
    (f : F →+* F') (hf : ∀ z, valuation F' (f z) < 1 ↔ valuation F z < 1) (x y : F) :
    f x ≤ᵥ f y ↔ x ≤ᵥ y := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp only [map_zero]
    exact ⟨fun _ ↦ ValuativeRel.zero_vle y, fun _ ↦ ValuativeRel.zero_vle (f y)⟩
  · rw [vle_iff_not_valuation_div_lt_one hx, vle_iff_not_valuation_div_lt_one
      ((map_ne_zero f).mpr hx), ← map_div₀, hf]

variable [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem tendsto_pow_atTop_nhds_zero_iff (x : F) :
    Tendsto (fun n : ℕ ↦ x ^ n) atTop (𝓝 0) ↔ valuation F x < 1 := by
  rw [(IsValuativeTopology.hasBasis_nhds_zero F).tendsto_right_iff]
  constructor
  · intro h
    obtain ⟨n, hn⟩ := (h 1 trivial).exists
    simp only [Set.mem_ofPred_eq, map_pow, Units.val_one] at hn
    by_contra hx
    exact (one_le_pow₀ (not_lt.mp hx)).not_gt hn
  · intro hx γ _
    obtain ⟨n, hn⟩ := exists_pow_lt₀ hx γ
    filter_upwards [eventually_ge_atTop n] with m hm
    simp only [map_pow]
    exact (pow_le_pow_of_le_one zero_le hx.le hm).trans_lt hn

end Nilpotent

section Maps

variable {K L M : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
  [Field M] [ValuativeRel M] [TopologicalSpace M] [IsNonarchimedeanLocalField M]
  [Algebra K M] [ValuativeExtension K M]

theorem continuous_algHom (f : L →ₐ[K] M) : Continuous f := by
  have := isModuleTopology K L
  exact IsModuleTopology.continuous_of_linearMap (R := K) f.toLinearMap

theorem isClosedEmbedding_algHom (f : L →ₐ[K] M) : IsClosedEmbedding f := by
  let := nontriviallyNormedField K
  have := completeSpace_nontriviallyNormedField K
  have := t2Space_of_isNonarchimedeanLocalField L
  have := t2Space_of_isNonarchimedeanLocalField M
  exact LinearMap.isClosedEmbedding_of_injective (f := f.toLinearMap)
    (LinearMap.ker_eq_bot.mpr f.toRingHom.injective)

theorem valuation_map_lt_one_iff (f : L →ₐ[K] M) (x : L) :
    valuation M (f x) < 1 ↔ valuation L x < 1 := by
  rw [← tendsto_pow_atTop_nhds_zero_iff, ← tendsto_pow_atTop_nhds_zero_iff,
    (isClosedEmbedding_algHom f).isInducing.tendsto_nhds_iff, ← map_zero f]
  simp only [Function.comp_def, map_pow]

theorem vle_map_iff (f : L →ₐ[K] M) (x y : L) : f x ≤ᵥ f y ↔ x ≤ᵥ y :=
  vle_map_iff_of_valuation_lt_one_iff f.toRingHom (valuation_map_lt_one_iff f) x y

theorem vlt_map_iff (f : L →ₐ[K] M) (x y : L) : f x <ᵥ f y ↔ x <ᵥ y := by
  rw [← not_vle, vle_map_iff, not_vle]

theorem valuativeExtension_algHom (f : L →ₐ[K] M) :
    letI := f.toRingHom.toAlgebra
    ValuativeExtension L M :=
  letI := f.toRingHom.toAlgebra
  ⟨vle_map_iff f⟩

theorem valuativeExtension_of_isScalarTower [Algebra L M] [IsScalarTower K L M] :
    ValuativeExtension L M :=
  ⟨vle_map_iff (IsScalarTower.toAlgHom K L M)⟩

end Maps

section Uniqueness

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  {L : Type*} [Field L] [Algebra K L] [FiniteDimensional K L]

theorem topologicalSpace_eq_moduleTopology [ValuativeRel L] [t : TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [ValuativeExtension K L] : t = moduleTopology K L :=
  have := isModuleTopology K L
  eq_moduleTopology K L

theorem topologicalSpace_unique {v₁ v₂ : ValuativeRel L} {t₁ t₂ : TopologicalSpace L}
    (h₁ : @IsNonarchimedeanLocalField L _ v₁ t₁) (h₂ : @IsNonarchimedeanLocalField L _ v₂ t₂)
    (e₁ : @ValuativeExtension K L _ _ _ v₁ _) (e₂ : @ValuativeExtension K L _ _ _ v₂ _) :
    t₁ = t₂ :=
  (@topologicalSpace_eq_moduleTopology K _ _ _ _ L _ _ _ v₁ t₁ h₁ e₁).trans
    (@topologicalSpace_eq_moduleTopology K _ _ _ _ L _ _ _ v₂ t₂ h₂ e₂).symm

theorem valuativeRel_unique {v₁ v₂ : ValuativeRel L} {t₁ t₂ : TopologicalSpace L}
    (h₁ : @IsNonarchimedeanLocalField L _ v₁ t₁) (h₂ : @IsNonarchimedeanLocalField L _ v₂ t₂)
    (e₁ : @ValuativeExtension K L _ _ _ v₁ _) (e₂ : @ValuativeExtension K L _ _ _ v₂ _) :
    v₁ = v₂ := by
  have ht := topologicalSpace_unique K h₁ h₂ e₁ e₂
  subst ht
  have hlt (z : L) : @valuation L _ v₂ z < 1 ↔ @valuation L _ v₁ z < 1 := by
    rw [← @tendsto_pow_atTop_nhds_zero_iff L _ v₁ t₁ h₁,
      ← @tendsto_pow_atTop_nhds_zero_iff L _ v₂ t₁ h₂]
  ext x y
  exact (@vle_map_iff_of_valuation_lt_one_iff L _ v₁ L _ v₂ (RingHom.id L) hlt x y).symm

end Uniqueness

section Galois

variable {K L M : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
  [Field M] [ValuativeRel M] [TopologicalSpace M] [IsNonarchimedeanLocalField M]
  [Algebra K M] [ValuativeExtension K M]

theorem valuation_map_le_iff (f : L →ₐ[K] M) (x y : L) :
    valuation M (f x) ≤ valuation M (f y) ↔ valuation L x ≤ valuation L y := by
  rw [← (valuation M).vle_iff_le, ← (valuation L).vle_iff_le, vle_map_iff]

theorem valuation_map_lt_iff (f : L →ₐ[K] M) (x y : L) :
    valuation M (f x) < valuation M (f y) ↔ valuation L x < valuation L y := by
  rw [← (valuation M).vlt_iff_lt, ← (valuation L).vlt_iff_lt, vlt_map_iff]

theorem valuation_map_eq_iff (f : L →ₐ[K] M) (x y : L) :
    valuation M (f x) = valuation M (f y) ↔ valuation L x = valuation L y := by
  rw [le_antisymm_iff, le_antisymm_iff, valuation_map_le_iff, valuation_map_le_iff]

theorem map_mem_integer_iff (f : L →ₐ[K] M) (x : L) : f x ∈ 𝒪[M] ↔ x ∈ 𝒪[L] := by
  simp only [Valuation.mem_integer_iff]
  rw [← map_one (valuation M), ← map_one f, valuation_map_le_iff, map_one]

def continuousAlgHom (f : L →ₐ[K] M) : L →A[K] M where
  __ := f
  cont := continuous_algHom f

@[simp]
theorem coe_continuousAlgHom (f : L →ₐ[K] M) : ⇑(continuousAlgHom f) = f :=
  rfl

def integerAlgHom (f : L →ₐ[K] M) : 𝒪[L] →ₐ[𝒪[K]] 𝒪[M] where
  toFun x := ⟨f x, (map_mem_integer_iff f x).mpr x.2⟩
  map_one' := by ext; simp
  map_mul' x y := by ext; simp
  map_zero' := by ext; simp
  map_add' x y := by ext; simp
  commutes' r := by ext; simp

@[simp]
theorem coe_integerAlgHom_apply (f : L →ₐ[K] M) (x : 𝒪[L]) :
    (integerAlgHom f x : M) = f x :=
  rfl

instance isLocalHom_integerAlgHom (f : L →ₐ[K] M) : IsLocalHom (integerAlgHom f) where
  map_nonunit x hx := by
    rw [(Valuation.integer.integers (valuation M)).isUnit_iff_valuation_eq_one] at hx
    rw [(Valuation.integer.integers (valuation L)).isUnit_iff_valuation_eq_one]
    have hx' : valuation M (f x) = valuation M (f 1) := by
      rw [map_one, map_one]
      exact hx
    exact ((valuation_map_eq_iff f x 1).mp hx').trans (map_one _)

def residueAlgHom (f : L →ₐ[K] M) : 𝓀[L] →ₐ[𝓀[K]] 𝓀[M] :=
  IsLocalRing.ResidueField.mapAlgHom' (integerAlgHom f)

@[simp]
theorem residueAlgHom_residue (f : L →ₐ[K] M) (x : 𝒪[L]) :
    residueAlgHom f (IsLocalRing.residue 𝒪[L] x) =
      IsLocalRing.residue 𝒪[M] (integerAlgHom f x) :=
  rfl

variable (K L)

theorem valuation_algEquiv_apply (σ : L ≃ₐ[K] L) (x : L) : valuation L (σ x) = valuation L x := by

  have key : ∀ (τ : L ≃ₐ[K] L) (y : L), ¬ valuation L (τ y) < valuation L y := by
    intro τ y h
    have hpow : ∀ m : ℕ, valuation L ((τ ^ (m + 1)) y) < valuation L y := by
      intro m
      induction m with
      | zero => simpa using h
      | succ m ih =>
        rw [pow_succ', AlgEquiv.mul_apply]
        exact ((valuation_map_lt_iff τ.toAlgHom _ _).mpr ih).trans h
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (orderOf_pos τ).ne'
    have := hpow m
    rw [← Nat.succ_eq_add_one, ← hm, pow_orderOf_eq_one, AlgEquiv.one_apply] at this
    exact this.false
  rcases lt_trichotomy (valuation L (σ x)) (valuation L x) with h | h | h
  · exact (key σ x h).elim
  · exact h
  · refine (key σ.symm (σ x) ?_).elim
    simpa using h

theorem vle_algEquiv_iff (σ : L ≃ₐ[K] L) (x y : L) : σ x ≤ᵥ σ y ↔ x ≤ᵥ y :=
  vle_map_iff σ.toAlgHom x y

def continuousAlgEquiv (σ : L ≃ₐ[K] L) : L ≃A[K] L where
  toAlgEquiv := σ
  continuous_toFun := continuous_algHom σ.toAlgHom
  continuous_invFun := continuous_algHom σ.symm.toAlgHom

@[simp]
theorem coe_continuousAlgEquiv (σ : L ≃ₐ[K] L) : ⇑(continuousAlgEquiv K L σ) = σ :=
  rfl

def homeomorph (σ : L ≃ₐ[K] L) : L ≃ₜ L :=
  (continuousAlgEquiv K L σ).toHomeomorph

@[simp]
theorem coe_homeomorph (σ : L ≃ₐ[K] L) : ⇑(homeomorph K L σ) = σ :=
  rfl

def integerAlgEquiv : (L ≃ₐ[K] L) →* (𝒪[L] ≃ₐ[𝒪[K]] 𝒪[L]) where
  toFun σ := AlgEquiv.ofAlgHom (integerAlgHom σ.toAlgHom) (integerAlgHom σ.symm.toAlgHom)
    (by ext; simp) (by ext; simp)
  map_one' := by ext; rfl
  map_mul' _ _ := by ext; rfl

@[simp]
theorem coe_integerAlgEquiv_apply (σ : L ≃ₐ[K] L) (x : 𝒪[L]) :
    (integerAlgEquiv K L σ x : L) = σ x :=
  rfl

def residueAlgEquiv : (L ≃ₐ[K] L) →* (𝓀[L] ≃ₐ[𝓀[K]] 𝓀[L]) where
  toFun σ := IsLocalRing.ResidueField.mapAlgEquiv' (integerAlgEquiv K L σ)
  map_one' := by
    ext x
    obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective x
    simp
  map_mul' σ τ := by
    ext x
    obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective x
    simp

@[simp]
theorem residueAlgEquiv_residue (σ : L ≃ₐ[K] L) (x : 𝒪[L]) :
    residueAlgEquiv K L σ (IsLocalRing.residue 𝒪[L] x) =
      IsLocalRing.residue 𝒪[L] (integerAlgEquiv K L σ x) :=
  rfl

end Galois

end Sec_Uniqueness


/-! ### UnitsBasic -/
section Sec_UnitsBasic

open ValuativeRel IsLocalRing
open scoped WithZero

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

section Filtration

def unitFiltration (n : ℕ) : Subgroup 𝒪[K]ˣ where
  carrier := {u | (u : 𝒪[K]) - 1 ∈ 𝓂[K] ^ n}
  one_mem' := by simp
  mul_mem' {u w} hu hw := by
    have h : ((u * w : 𝒪[K]ˣ) : 𝒪[K]) - 1 =
        (u : 𝒪[K]) * ((w : 𝒪[K]) - 1) + ((u : 𝒪[K]) - 1) := by
      push_cast; ring
    simp only [Set.mem_ofPred_eq] at hu hw ⊢
    rw [h]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hw) hu
  inv_mem' {u} hu := by
    have h : ((u⁻¹ : 𝒪[K]ˣ) : 𝒪[K]) - 1 = -((u⁻¹ : 𝒪[K]ˣ) : 𝒪[K]) * ((u : 𝒪[K]) - 1) := by
      linear_combination (u.inv_mul)
    simp only [Set.mem_ofPred_eq] at hu ⊢
    rw [h]
    exact Ideal.mul_mem_left _ _ hu

variable {K} in
theorem mem_unitFiltration {n : ℕ} {u : 𝒪[K]ˣ} :
    u ∈ unitFiltration K n ↔ (u : 𝒪[K]) - 1 ∈ 𝓂[K] ^ n := Iff.rfl

@[simp]
theorem unitFiltration_zero : unitFiltration K 0 = ⊤ := by
  ext u; simp [mem_unitFiltration]

theorem unitFiltration_antitone : Antitone (unitFiltration K) :=
  fun _ _ hmn _ hu ↦ Ideal.pow_le_pow_right hmn hu

theorem unitFiltration_succ_le (n : ℕ) : unitFiltration K (n + 1) ≤ unitFiltration K n :=
  unitFiltration_antitone K n.le_succ

end Filtration

section Uniformizer

variable {K}

theorem mem_maximalIdeal_pow_iff {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) {n : ℕ} {x : 𝒪[K]} :
    x ∈ 𝓂[K] ^ n ↔ ϖ ^ n ∣ x := by
  rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton]

theorem mem_maximalIdeal_iff_dvd {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) {x : 𝒪[K]} :
    x ∈ 𝓂[K] ↔ ϖ ∣ x := by
  simpa using mem_maximalIdeal_pow_iff hϖ (n := 1) (x := x)

theorem uniformizer_mem_maximalIdeal {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) : ϖ ∈ 𝓂[K] :=
  (mem_maximalIdeal_iff_dvd hϖ).mpr dvd_rfl

theorem residue_uniformizer {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) : residue 𝒪[K] ϖ = 0 :=
  (residue_eq_zero_iff _).mpr (uniformizer_mem_maximalIdeal hϖ)

end Uniformizer

section Valuation

noncomputable def normalizedValuation : Valuation K ℤᵐ⁰ :=
  (valuation K).map
    (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K).toMulEquiv.toMonoidWithZeroHom
    (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K).toOrderIso.monotone

variable {K}

theorem normalizedValuation_apply (x : K) :
    normalizedValuation K x = IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
      (valuation K x) := by
  simp [normalizedValuation, Valuation.map_apply]

theorem normalizedValuation_le_iff {x y : K} :
    normalizedValuation K x ≤ normalizedValuation K y ↔ valuation K x ≤ valuation K y := by
  rw [normalizedValuation_apply, normalizedValuation_apply]
  exact map_le_map_iff _

theorem normalizedValuation_lt_iff {x y : K} :
    normalizedValuation K x < normalizedValuation K y ↔ valuation K x < valuation K y := by
  rw [normalizedValuation_apply, normalizedValuation_apply]
  exact map_lt_map_iff _

theorem normalizedValuation_eq_iff {x y : K} :
    normalizedValuation K x = normalizedValuation K y ↔ valuation K x = valuation K y := by
  rw [normalizedValuation_apply, normalizedValuation_apply]
  exact (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K).injective.eq_iff

theorem normalizedValuation_le_one_iff {x : K} :
    normalizedValuation K x ≤ 1 ↔ x ∈ 𝒪[K] := by
  rw [← map_one (normalizedValuation K), normalizedValuation_le_iff, map_one]
  exact (Valuation.mem_integer_iff _ _).symm

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
theorem valuation_unit (u : 𝒪[K]ˣ) : valuation K ((u : 𝒪[K]) : K) = 1 :=
  (Valuation.integer.integers (valuation K)).isUnit_iff_valuation_eq_one.mp u.isUnit

theorem normalizedValuation_unit (u : 𝒪[K]ˣ) : normalizedValuation K ((u : 𝒪[K]) : K) = 1 := by
  rw [← map_one (normalizedValuation K), normalizedValuation_eq_iff, map_one]
  exact valuation_unit u

theorem valuation_lt_one_of_mem_maximalIdeal {x : 𝒪[K]} (hx : x ∈ 𝓂[K]) :
    valuation K (x : K) < 1 := by
  refine lt_of_le_of_ne x.2 fun h ↦ ?_
  exact (IsLocalRing.mem_maximalIdeal x).mp hx
    ((Valuation.integer.integers (valuation K)).isUnit_iff_valuation_eq_one.mpr h)

theorem normalizedValuation_uniformizer {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) :
    normalizedValuation K ϖ = WithZero.exp (-1) := by
  have hne : normalizedValuation K ϖ ≠ 0 := by
    rw [Ne, Valuation.zero_iff]
    exact_mod_cast hϖ.ne_zero
  have hlt : normalizedValuation K ϖ < 1 := by
    rw [← map_one (normalizedValuation K), normalizedValuation_lt_iff, map_one]
    exact valuation_lt_one_of_mem_maximalIdeal (uniformizer_mem_maximalIdeal hϖ)
  obtain ⟨y, hy⟩ : ∃ y : K, normalizedValuation K y = WithZero.exp (-1) := by
    obtain ⟨y, hy⟩ := ValuativeRel.valuation_surjective
      ((IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K).symm (WithZero.exp (-1)))
    exact ⟨y, by rw [normalizedValuation_apply, hy]; simp⟩
  have hexp : WithZero.exp (-1 : ℤ) < 1 := by
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
  have hy1 : valuation K y < 1 := by
    rw [← map_one (valuation K), ← normalizedValuation_lt_iff, map_one, hy]; exact hexp
  have hymem : (⟨y, hy1.le⟩ : 𝒪[K]) ∈ 𝓂[K] := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      (Valuation.integer.integers (valuation K)).isUnit_iff_valuation_eq_one]
    exact hy1.ne
  have hyϖ : valuation K y ≤ valuation K ϖ := by
    have := hϖ.maximalIdeal_eq_setOfPred_le_v_coe (v := valuation K)
    have h2 : (⟨y, hy1.le⟩ : 𝒪[K]) ∈ (𝓂[K] : Set 𝒪[K]) := hymem
    rw [this] at h2
    exact h2
  rw [← normalizedValuation_le_iff, hy] at hyϖ
  rw [← WithZero.exp_log hne] at hyϖ hlt ⊢
  rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at hlt
  rw [WithZero.exp_le_exp] at hyϖ
  congr 1
  omega

noncomputable def ord (x : K) : ℤ := -WithZero.log (normalizedValuation K x)

theorem normalizedValuation_eq_exp_ord {x : K} (hx : x ≠ 0) :
    normalizedValuation K x = WithZero.exp (-ord x) := by
  rw [ord, neg_neg, WithZero.exp_log]
  simpa using hx

theorem ord_mul {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) : ord (x * y) = ord x + ord y := by
  simp [ord, WithZero.log_mul, hx, hy]; ring

theorem ord_uniformizer {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) : ord (ϖ : K) = 1 := by
  simp [ord, normalizedValuation_uniformizer hϖ]

theorem ord_unit (u : 𝒪[K]ˣ) : ord ((u : 𝒪[K]) : K) = 0 := by
  simp [ord, normalizedValuation_unit u]

end Valuation

section UnitsDecomposition

noncomputable def unitsIncl : 𝒪[K]ˣ →* Kˣ :=
  Units.map (𝒪[K].subtype : 𝒪[K] →+* K).toMonoidHom

variable {K}

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
@[simp]
theorem coe_unitsIncl (u : 𝒪[K]ˣ) : ((unitsIncl K u : Kˣ) : K) = ((u : 𝒪[K]) : K) := rfl

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
theorem unitsIncl_injective : Function.Injective (unitsIncl K) := by
  intro u w h
  ext
  have := congrArg Units.val h
  simpa using this

theorem mem_range_unitsIncl_iff {x : Kˣ} :
    x ∈ (unitsIncl K).range ↔ normalizedValuation K x = 1 := by
  constructor
  · rintro ⟨u, rfl⟩
    simpa using normalizedValuation_unit u
  · intro h
    have h1 : valuation K (x : K) = 1 := by
      rwa [← map_one (normalizedValuation K), normalizedValuation_eq_iff, map_one] at h
    have h2 : valuation K ((x⁻¹ : Kˣ) : K) = 1 := by
      rw [Units.val_inv_eq_inv_val, map_inv₀, h1, inv_one]
    refine ⟨⟨⟨x, h1.le⟩, ⟨(x⁻¹ : Kˣ), h2.le⟩, ?_, ?_⟩, ?_⟩
    · ext; simp
    · ext; simp
    · ext; rfl

noncomputable def uniformizerUnit {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) : Kˣ :=
  Units.mk0 (ϖ : K) (by exact_mod_cast hϖ.ne_zero)

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
@[simp]
theorem coe_uniformizerUnit {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) :
    ((uniformizerUnit hϖ : Kˣ) : K) = ϖ := rfl

noncomputable def unitsOfIntProd {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) :
    Multiplicative ℤ × 𝒪[K]ˣ →* Kˣ :=
  (zpowersHom Kˣ (uniformizerUnit hϖ)).coprod (unitsIncl K)

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
theorem coe_unitsOfIntProd {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) (n : Multiplicative ℤ)
    (u : 𝒪[K]ˣ) :
    ((unitsOfIntProd hϖ (n, u) : Kˣ) : K) = (ϖ : K) ^ n.toAdd * ((u : 𝒪[K]) : K) := by
  simp [unitsOfIntProd, zpowersHom_apply, Units.val_zpow_eq_zpow_val]

theorem normalizedValuation_unitsOfIntProd {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ)
    (n : Multiplicative ℤ) (u : 𝒪[K]ˣ) :
    normalizedValuation K (unitsOfIntProd hϖ (n, u) : K) = WithZero.exp (-n.toAdd) := by
  rw [coe_unitsOfIntProd, map_mul, map_zpow₀, normalizedValuation_uniformizer hϖ,
    normalizedValuation_unit, mul_one, ← WithZero.exp_zsmul]
  congr 1
  simp

theorem unitsOfIntProd_bijective {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) :
    Function.Bijective (unitsOfIntProd hϖ) := by
  constructor
  · rw [injective_iff_map_eq_one]
    rintro ⟨n, u⟩ h
    have hv := normalizedValuation_unitsOfIntProd hϖ n u
    rw [h, Units.val_one, map_one, ← WithZero.exp_zero, WithZero.exp_inj] at hv
    have hn : n = 1 := by
      rw [← toAdd_eq_zero]; omega
    subst hn
    have hu : unitsIncl K u = 1 := by
      simpa [unitsOfIntProd] using h
    rw [← map_one (unitsIncl K)] at hu
    rw [unitsIncl_injective hu]
    rfl
  · intro x
    obtain ⟨n, u, hx⟩ := IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible
      (K := K) hϖ x.ne_zero
    refine ⟨(Multiplicative.ofAdd n, u), ?_⟩
    ext
    rw [coe_unitsOfIntProd, hx, Units.smul_def, Algebra.smul_def, toAdd_ofAdd, mul_comm]
    rfl

noncomputable def unitsEquivIntProd {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) :
    Kˣ ≃* Multiplicative ℤ × 𝒪[K]ˣ :=
  (MulEquiv.ofBijective (unitsOfIntProd hϖ) (unitsOfIntProd_bijective hϖ)).symm

theorem unitsEquivIntProd_symm_apply {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ)
    (p : Multiplicative ℤ × 𝒪[K]ˣ) :
    (unitsEquivIntProd hϖ).symm p = unitsOfIntProd hϖ p := rfl

theorem unitsEquivIntProd_fst {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) (x : Kˣ) :
    (unitsEquivIntProd hϖ x).1 = Multiplicative.ofAdd (ord (x : K)) := by
  set p := unitsEquivIntProd hϖ x
  have hx : x = unitsOfIntProd hϖ p := by
    rw [← unitsEquivIntProd_symm_apply, MulEquiv.symm_apply_apply]
  have hv := normalizedValuation_eq_exp_ord x.ne_zero
  rw [hx, normalizedValuation_unitsOfIntProd, WithZero.exp_inj, neg_inj] at hv
  simp only [← hx] at hv
  rw [← hv]
  rfl

theorem unitsEquivIntProd_uniformizer {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) :
    unitsEquivIntProd hϖ (uniformizerUnit hϖ) = (Multiplicative.ofAdd 1, 1) := by
  rw [← MulEquiv.eq_symm_apply, unitsEquivIntProd_symm_apply]
  ext
  simp [coe_unitsOfIntProd]

theorem unitsEquivIntProd_unitsIncl {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) (u : 𝒪[K]ˣ) :
    unitsEquivIntProd hϖ (unitsIncl K u) = (1, u) := by
  rw [← MulEquiv.eq_symm_apply, unitsEquivIntProd_symm_apply]
  ext
  simp [coe_unitsOfIntProd]

end UnitsDecomposition

section Residue

noncomputable def unitsToResidue : 𝒪[K]ˣ →* 𝓀[K]ˣ :=
  Units.map (residue 𝒪[K]).toMonoidHom

theorem unitsToResidue_surjective : Function.Surjective (unitsToResidue K) :=
  surjective_units_map_of_local_ringHom _ residue_surjective inferInstance

@[simp]
theorem coe_unitsToResidue (u : 𝒪[K]ˣ) :
    ((unitsToResidue K u : 𝓀[K]ˣ) : 𝓀[K]) = residue 𝒪[K] u := rfl

theorem ker_unitsToResidue : (unitsToResidue K).ker = unitFiltration K 1 := by
  ext u
  rw [MonoidHom.mem_ker, mem_unitFiltration, pow_one, ← residue_eq_zero_iff, map_sub, map_one,
    sub_eq_zero, Units.ext_iff]
  rfl

noncomputable def unitsModPrincipalEquiv : 𝒪[K]ˣ ⧸ unitFiltration K 1 ≃* 𝓀[K]ˣ :=
  (QuotientGroup.quotientMulEquivOfEq (ker_unitsToResidue K).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (unitsToResidue_surjective K))

@[simp]
theorem unitsModPrincipalEquiv_mk (u : 𝒪[K]ˣ) :
    unitsModPrincipalEquiv K (QuotientGroup.mk u) = unitsToResidue K u := rfl

end Residue

section Graded

variable {K} {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ)
include hϖ

theorem exists_sub_one_eq_mul {n : ℕ} (u : unitFiltration K n) :
    ∃ a : 𝒪[K], ((u : 𝒪[K]ˣ) : 𝒪[K]) - 1 = ϖ ^ n * a :=
  (mem_maximalIdeal_pow_iff hϖ).mp u.2

noncomputable def filtrationCoeff {n : ℕ} (u : unitFiltration K n) : 𝒪[K] :=
  (exists_sub_one_eq_mul hϖ u).choose

theorem sub_one_eq_filtrationCoeff {n : ℕ} (u : unitFiltration K n) :
    ((u : 𝒪[K]ˣ) : 𝒪[K]) - 1 = ϖ ^ n * filtrationCoeff hϖ u :=
  (exists_sub_one_eq_mul hϖ u).choose_spec

theorem filtrationCoeff_eq {n : ℕ} {u : unitFiltration K n} {a : 𝒪[K]}
    (h : ((u : 𝒪[K]ˣ) : 𝒪[K]) - 1 = ϖ ^ n * a) : filtrationCoeff hϖ u = a :=
  mul_left_cancel₀ (pow_ne_zero n hϖ.ne_zero) ((sub_one_eq_filtrationCoeff hϖ u).symm.trans h)

theorem isUnit_one_add_mul {n : ℕ} (hn : 1 ≤ n) (a : 𝒪[K]) : IsUnit (1 + ϖ ^ n * a) := by
  have hm : ϖ ^ n * a ∈ 𝓂[K] :=
    Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ (uniformizer_mem_maximalIdeal hϖ) n (by omega))
  simpa using isUnit_one_sub_self_of_mem_nonunits (-(ϖ ^ n * a))
    ((IsLocalRing.mem_maximalIdeal _).mp (neg_mem hm))

noncomputable def filtrationGradedHom {n : ℕ} (hn : 1 ≤ n) :
    unitFiltration K n →* Multiplicative 𝓀[K] where
  toFun u := Multiplicative.ofAdd (residue 𝒪[K] (filtrationCoeff hϖ u))
  map_one' := by
    rw [filtrationCoeff_eq hϖ (a := 0) (by simp)]
    simp
  map_mul' u w := by
    have hu := sub_one_eq_filtrationCoeff hϖ u
    have hw := sub_one_eq_filtrationCoeff hϖ w
    have h := filtrationCoeff_eq hϖ (u := u * w)
      (a := filtrationCoeff hϖ u + filtrationCoeff hϖ w +
        ϖ ^ n * (filtrationCoeff hϖ u * filtrationCoeff hϖ w)) (by
      simp only [Subgroup.coe_mul, Units.val_mul]
      linear_combination ((w : 𝒪[K]ˣ) : 𝒪[K]) * hu + (1 + ϖ ^ n * filtrationCoeff hϖ u) * hw)
    rw [h, ← ofAdd_add]
    congr 1
    simp [residue_uniformizer hϖ, zero_pow (by omega : n ≠ 0)]

theorem filtrationGradedHom_apply {n : ℕ} (hn : 1 ≤ n) (u : unitFiltration K n) :
    filtrationGradedHom hϖ hn u = Multiplicative.ofAdd (residue 𝒪[K] (filtrationCoeff hϖ u)) :=
  rfl

theorem ker_filtrationGradedHom {n : ℕ} (hn : 1 ≤ n) :
    (filtrationGradedHom hϖ hn).ker =
      (unitFiltration K (n + 1)).subgroupOf (unitFiltration K n) := by
  ext u
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_unitFiltration, mem_maximalIdeal_pow_iff hϖ,
    sub_one_eq_filtrationCoeff hϖ u, pow_succ,
    mul_dvd_mul_iff_left (pow_ne_zero n hϖ.ne_zero), ← mem_maximalIdeal_iff_dvd hϖ,
    ← residue_eq_zero_iff, filtrationGradedHom_apply]
  exact ofAdd_eq_one

theorem filtrationGradedHom_surjective {n : ℕ} (hn : 1 ≤ n) :
    Function.Surjective (filtrationGradedHom hϖ hn) := by
  intro r
  obtain ⟨a, ha⟩ := residue_surjective (Multiplicative.toAdd r)
  have hu := isUnit_one_add_mul hϖ hn a
  refine ⟨⟨hu.unit, ?_⟩, ?_⟩
  · rw [mem_unitFiltration, IsUnit.unit_spec, add_sub_cancel_left, mem_maximalIdeal_pow_iff hϖ]
    exact dvd_mul_right _ _
  · rw [filtrationGradedHom_apply, filtrationCoeff_eq hϖ (a := a) (by simp), ha]
    rfl

noncomputable def unitFiltrationGradedEquiv {n : ℕ} (hn : 1 ≤ n) :
    unitFiltration K n ⧸ (unitFiltration K (n + 1)).subgroupOf (unitFiltration K n) ≃*
      Multiplicative 𝓀[K] :=
  (QuotientGroup.quotientMulEquivOfEq (ker_filtrationGradedHom hϖ hn).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (filtrationGradedHom_surjective hϖ hn))

omit hϖ in
theorem relIndex_unitFiltration_succ {n : ℕ} (hn : 1 ≤ n) (hϖ : Irreducible ϖ) :
    (unitFiltration K (n + 1)).relIndex (unitFiltration K n) = Nat.card 𝓀[K] :=
  (Nat.card_congr (unitFiltrationGradedEquiv hϖ hn).toEquiv).trans rfl

end Graded

section Index

theorem index_unitFiltration_one : (unitFiltration K 1).index = Nat.card 𝓀[K] - 1 :=
  (Nat.card_congr (unitsModPrincipalEquiv K).toEquiv).trans (Nat.card_units 𝓀[K])

theorem index_unitFiltration {n : ℕ} (hn : 1 ≤ n) :
    (unitFiltration K n).index = (Nat.card 𝓀[K] - 1) * Nat.card 𝓀[K] ^ (n - 1) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  induction n, hn using Nat.le_induction with
  | base => simp [index_unitFiltration_one]
  | succ n hn ih =>
    rw [← Subgroup.relIndex_mul_index (unitFiltration_succ_le K n),
      relIndex_unitFiltration_succ hn hϖ, ih, Nat.add_sub_cancel]
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    simp only [Nat.add_sub_cancel, pow_succ]
    ring

theorem index_unitFiltration_ne_zero (n : ℕ) : (unitFiltration K n).index ≠ 0 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [index_unitFiltration K hn]
    have : 1 < Nat.card 𝓀[K] := Finite.one_lt_card
    exact Nat.mul_ne_zero (by omega) (pow_ne_zero _ (by omega))

instance (n : ℕ) : (unitFiltration K n).FiniteIndex := ⟨index_unitFiltration_ne_zero K n⟩

instance (n : ℕ) : Finite (𝒪[K]ˣ ⧸ unitFiltration K n) :=
  Subgroup.finite_quotient_of_finiteIndex

end Index

end Sec_UnitsBasic


/-! ### UnitsGalois -/
section Sec_UnitsGalois

open ValuativeRel

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

instance integerUnitsAction : MulDistribMulAction (L ≃ₐ[K] L) 𝒪[L]ˣ where
  smul σ u := Units.map (integerAlgEquiv K L σ : 𝒪[L] →* 𝒪[L]) u
  one_smul u := by ext; rfl
  mul_smul σ τ u := by ext; rfl
  smul_mul σ u w := map_mul (Units.map (integerAlgEquiv K L σ : 𝒪[L] →* 𝒪[L])) u w
  smul_one σ := map_one (Units.map (integerAlgEquiv K L σ : 𝒪[L] →* 𝒪[L]))

@[simp]
theorem coe_smul_integerUnits (σ : L ≃ₐ[K] L) (u : 𝒪[L]ˣ) :
    (((σ • u : 𝒪[L]ˣ) : 𝒪[L]) : L) = σ ((u : 𝒪[L]) : L) :=
  rfl

theorem unitsIncl_smul (σ : L ≃ₐ[K] L) (u : 𝒪[L]ˣ) :
    unitsIncl L (σ • u) = σ • unitsIncl L u := by
  ext
  rfl

end Sec_UnitsGalois


/-! ### ExistsRootOfAdicComplete -/
section Sec_ExistsRootOfAdicComplete

open Polynomial


private lemma exists_root_of_adicComplete {R : Type*} [CommRing R] (I : Ideal R)
    [IsAdicComplete I R] (f : R[X]) (a₀ : R) (h₁ : f.eval a₀ ∈ I)
    (h₂ : IsUnit (Ideal.Quotient.mk I (f.derivative.eval a₀))) :
    ∃ a : R, f.eval a = 0 ∧ a - a₀ ∈ I := by
  classical
  obtain ⟨f', hf'⟩ : ∃ f' : R[X], f' = derivative f := ⟨_, rfl⟩
  obtain ⟨c, hc0, hc⟩ : ∃ c : ℕ → R, c 0 = a₀ ∧
      ∀ n, c (n + 1) = c n - f.eval (c n) * Ring.inverse (f'.eval (c n)) :=
    ⟨fun n => Nat.recOn n a₀ fun _ b => b - f.eval b * Ring.inverse (f'.eval b), rfl,
      fun _ => rfl⟩
  rw [← hf'] at h₂
  have hc_mod : ∀ n, c n ≡ a₀ [SMOD I] := by
    intro n
    induction n with
    | zero => rw [hc0]
    | succ n ih =>
      rw [hc, sub_eq_add_neg, ← add_zero a₀]
      refine ih.add ?_
      rw [SModEq.zero, Ideal.neg_mem_iff]
      refine I.mul_mem_right _ ?_
      rw [← SModEq.zero] at h₁ ⊢
      exact (ih.eval f).trans h₁
  have hf'c : ∀ n, IsUnit (f'.eval (c n)) := by
    intro n
    have := isLocalHom_of_le_jacobson_bot I (IsAdicComplete.le_jacobson_bot I)
    apply IsUnit.of_map (Ideal.Quotient.mk I)
    convert! h₂ using 1
    exact SModEq.def.mp ((hc_mod n).eval _)
  have hfcI : ∀ n, f.eval (c n) ∈ I ^ (n + 1) := by
    intro n
    induction n with
    | zero => simpa only [hc0, zero_add, pow_one] using h₁
    | succ n ih =>
      obtain ⟨q, hq⟩ := Polynomial.binomExpansion f (c n)
        (-(f.eval (c n) * Ring.inverse (f'.eval (c n))))
      rw [hc, sub_eq_add_neg, hq]
      have hcancel : f'.eval (c n) * Ring.inverse (f'.eval (c n)) = 1 :=
        Ring.mul_inverse_cancel _ (hf'c n)
      have hz : eval (c n) f + eval (c n) (derivative f) *
          (-(f.eval (c n) * Ring.inverse (f'.eval (c n)))) = 0 := by
        rw [← hf']
        linear_combination (-(f.eval (c n))) * hcancel
      rw [hz, zero_add]
      have hle : I ^ (2 * (n + 1)) ≤ I ^ (n + 1 + 1) :=
        Ideal.pow_le_pow_right (by omega)
      refine Ideal.mul_mem_left _ _ (hle ?_)
      rw [pow_mul']
      exact Ideal.pow_mem_pow ((Ideal.neg_mem_iff _).2 <| Ideal.mul_mem_right _ _ ih) _
  have aux : ∀ m n, m ≤ n → c m ≡ c n [SMOD (I ^ m • ⊤ : Ideal R)] := by
    intro m n hmn
    rw [← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one]
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
    clear hmn
    induction k with
    | zero => rw [add_zero]
    | succ k ih =>
      rw [← add_assoc, hc, ← add_zero (c m), sub_eq_add_neg]
      refine ih.add ?_
      symm
      rw [SModEq.zero, Ideal.neg_mem_iff]
      refine Ideal.mul_mem_right _ _ (Ideal.pow_le_pow_right ?_ (hfcI _))
      rw [add_assoc]
      exact le_self_add
  obtain ⟨a, ha⟩ := IsPrecomplete.prec' c (aux _ _)
  refine ⟨a, ?_, ?_⟩
  · suffices ∀ n, f.eval a ≡ 0 [SMOD (I ^ n • ⊤ : Ideal R)] by exact IsHausdorff.haus' _ this
    intro n
    specialize ha n
    rw [← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one] at ha ⊢
    refine (ha.symm.eval f).trans ?_
    rw [SModEq.zero]
    exact Ideal.pow_le_pow_right le_self_add (hfcI _)
  · specialize ha (0 + 1)
    rw [hc, hc0, pow_one, ← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one, sub_eq_add_neg] at ha
    rw [← SModEq.sub_mem, ← add_zero a₀]
    refine ha.symm.trans (SModEq.rfl.add ?_)
    rw [SModEq.zero, Ideal.neg_mem_iff]
    exact Ideal.mul_mem_right _ _ h₁

private lemma root_of_local {R : Type*} [CommRing R] [IsLocalRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R] {ϖ : R}
    (hϖ : ϖ ∈ IsLocalRing.maximalIdeal R) (f : R[X]) (a : R) (k : ℕ) (ε : Rˣ)
    (h1 : f.derivative.eval a = ϖ ^ k * ε) (h2 : ϖ ^ (2 * k + 1) ∣ f.eval a) :
    ∃ b : R, f.eval b = 0 ∧ ϖ ^ (k + 1) ∣ b - a := by
  obtain ⟨c, hc⟩ := h2
  obtain ⟨q, hq⟩ := Polynomial.binomExpansion (f.map C) (C a) (C (ϖ ^ (k + 1)) * X)
  have hcomp : eval (C a + C (ϖ ^ (k + 1)) * X) (f.map C) =
      f.comp (C a + C (ϖ ^ (k + 1)) * X) := by
    rw [eval_map]; rfl
  rw [hcomp, eval_map_apply, derivative_map, eval_map_apply, h1, hc] at hq
  let g : R[X] := C c + C (ε : R) * X + C ϖ * q * X ^ 2
  have hgy : ∀ y, g.eval y = c + ε * y + ϖ * (q.eval y * y ^ 2) := by
    intro y; simp only [g, eval_add, eval_mul, eval_C, eval_X, eval_pow]; ring
  have hg'y : ∀ y, g.derivative.eval y =
      ε + ϖ * (q.derivative.eval y * y ^ 2 + q.eval y * (2 * y)) := by
    intro y
    simp only [g, derivative_add, derivative_mul, derivative_C, derivative_X, derivative_X_pow,
      eval_add, eval_mul, eval_C, eval_X, eval_pow, eval_zero, eval_one, map_natCast, eval_natCast]
    norm_num
    ring
  set y₀ : R := -((ε⁻¹ : Rˣ) : R) * c with hy₀
  have hεy : (ε : R) * y₀ = -c := by
    rw [hy₀, ← mul_assoc, mul_neg, Units.mul_inv]; ring
  have hroot₀ : g.eval y₀ ∈ IsLocalRing.maximalIdeal R := by
    rw [hgy, add_assoc, ← add_assoc c, hεy, add_neg_cancel, zero_add]
    exact Ideal.mul_mem_right _ _ hϖ
  have hunit : IsUnit (g.derivative.eval y₀) := by
    rw [hg'y]
    by_contra hn
    have hm := (IsLocalRing.mem_maximalIdeal _).2 hn
    have hε : (ε : R) ∈ IsLocalRing.maximalIdeal R := by
      have := Ideal.sub_mem _ hm (Ideal.mul_mem_right
        (q.derivative.eval y₀ * y₀ ^ 2 + q.eval y₀ * (2 * y₀)) _ hϖ)
      simp at this
    exact (IsLocalRing.mem_maximalIdeal _).1 hε ε.isUnit
  obtain ⟨y, hy, -⟩ := exists_root_of_adicComplete (IsLocalRing.maximalIdeal R) g y₀ hroot₀
    (hunit.map _)
  refine ⟨a + ϖ ^ (k + 1) * y, ?_, ⟨y, by ring⟩⟩
  have hev := congrArg (eval y) hq
  simp only [eval_comp, eval_add, eval_mul, eval_C, eval_X, eval_pow] at hev
  rw [hev]
  have : ϖ ^ (2 * k + 1) * g.eval y = 0 := by rw [hy, mul_zero]
  rw [hgy] at this
  linear_combination this

end Sec_ExistsRootOfAdicComplete


/-! ### UnitsPowers -/
section Sec_UnitsPowers

open ValuativeRel IsLocalRing Polynomial
open scoped WithZero

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

theorem isAdicComplete_integer : IsAdicComplete 𝓂[K] 𝒪[K] := by
  let := IsTopologicalAddGroup.rightUniformSpace K
  have := isUniformAddGroup_of_addCommGroup (G := K)
  infer_instance

variable {K}

theorem isUnit_unit_add {η : 𝒪[K]ˣ} {x : 𝒪[K]} (hx : x ∈ 𝓂[K]) : IsUnit ((η : 𝒪[K]) + x) := by
  have h1 : IsUnit (1 + (η⁻¹ : 𝒪[K]ˣ) * x) := by
    simpa using isUnit_one_sub_self_of_mem_nonunits (-(((η⁻¹ : 𝒪[K]ˣ) : 𝒪[K]) * x))
      ((IsLocalRing.mem_maximalIdeal _).mp (neg_mem (Ideal.mul_mem_left _ _ hx)))
  have : (η : 𝒪[K]) + x = η * (1 + (η⁻¹ : 𝒪[K]ˣ) * x) := by
    rw [mul_add, mul_one, ← mul_assoc, Units.mul_inv, one_mul]
  rw [this]
  exact η.isUnit.mul h1

theorem exists_root_of_dvd {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) (f : 𝒪[K][X]) (a : 𝒪[K]) (k : ℕ)
    (ε : 𝒪[K]ˣ) (hd : f.derivative.eval a = ϖ ^ k * ε) (hf : ϖ ^ (2 * k + 1) ∣ f.eval a) :
    ∃ b, f.eval b = 0 ∧ ϖ ^ (k + 1) ∣ b - a := by
  let := IsTopologicalAddGroup.rightUniformSpace K
  have := isUniformAddGroup_of_addCommGroup (G := K)
  exact root_of_local ((IsLocalRing.mem_maximalIdeal _).2 hϖ.not_isUnit) f a k ε hd hf

theorem eq_one_of_pow_eq_one {m : ℕ} (hm : (m : 𝓀[K]) ≠ 0) {u : 𝒪[K]ˣ}
    (hu : u ∈ unitFiltration K 1) (h : u ^ m = 1) : u = 1 := by
  have hres : residue 𝒪[K] (u : 𝒪[K]) = 1 := by
    have := (residue_eq_zero_iff _).mpr (by have := mem_unitFiltration.mp hu; rwa [pow_one] at this)
    rwa [map_sub, map_one, sub_eq_zero] at this
  have hgeom := geom_sum_mul (u : 𝒪[K]) m
  rw [← Units.val_pow_eq_pow_val, h, Units.val_one, sub_self] at hgeom
  have hS : IsUnit (∑ i ∈ Finset.range m, (u : 𝒪[K]) ^ i) := by
    rw [← residue_ne_zero_iff_isUnit]
    simpa [map_sum, hres] using hm
  have := (hS.mul_right_eq_zero).mp hgeom
  ext
  simpa [sub_eq_zero] using this

section Teichmuller

variable (K)

theorem one_lt_card_residueField : 1 < Nat.card 𝓀[K] := Finite.one_lt_card

theorem natCast_card_residueField_sub_one_ne_zero : ((Nat.card 𝓀[K] - 1 : ℕ) : 𝓀[K]) ≠ 0 := by
  have : Fintype 𝓀[K] := Fintype.ofFinite _
  have hq : ((Nat.card 𝓀[K] : ℕ) : 𝓀[K]) = 0 := by
    rw [Nat.card_eq_fintype_card]; exact FiniteField.cast_card_eq_zero _
  rw [Nat.cast_sub (one_lt_card_residueField K).le, hq, Nat.cast_one, zero_sub]
  exact neg_ne_zero.mpr one_ne_zero

variable {K}

theorem exists_teichmuller_lift (ζ : 𝓀[K]ˣ) :
    ∃ u : 𝒪[K]ˣ, u ^ (Nat.card 𝓀[K] - 1) = 1 ∧ unitsToResidue K u = ζ := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  set n := Nat.card 𝓀[K] - 1 with hn
  have hn0 : n ≠ 0 := by have := one_lt_card_residueField K; omega
  obtain ⟨a, ha⟩ := residue_surjective (ζ : 𝓀[K])
  have hζ : ζ ^ n = 1 := by
    rw [hn, ← Nat.card_units]; exact pow_card_eq_one'
  set f : 𝒪[K][X] := X ^ n - 1
  have hfa : f.eval a ∈ 𝓂[K] := by
    rw [← residue_eq_zero_iff]
    simp [f, ha, ← Units.val_pow_eq_pow_val, hζ]
  have hd : IsUnit (f.derivative.eval a) := by
    rw [← residue_ne_zero_iff_isUnit]
    simp only [f, derivative_sub, derivative_X_pow, derivative_one, sub_zero, eval_mul,
      eval_pow, eval_X, eval_natCast, map_mul, map_natCast, map_pow, ha]
    exact mul_ne_zero (natCast_card_residueField_sub_one_ne_zero K) (pow_ne_zero _ ζ.ne_zero)
  obtain ⟨b, hb, hba⟩ := exists_root_of_dvd hϖ f a 0 hd.unit (by simp)
    (by simpa using (mem_maximalIdeal_iff_dvd hϖ).mp hfa)
  have hbn : b ^ n = 1 := by simpa [f, sub_eq_zero] using hb
  have hbu : IsUnit b := (isUnit_pow_iff hn0).mp (hbn ▸ isUnit_one)
  refine ⟨hbu.unit, ?_, ?_⟩
  · ext; simp [hbn]
  · ext
    rw [coe_unitsToResidue, IsUnit.unit_spec, ← ha, ← sub_eq_zero, ← map_sub,
      residue_eq_zero_iff, mem_maximalIdeal_iff_dvd hϖ]
    simpa using hba

theorem eq_of_pow_card_sub_one {u w : 𝒪[K]ˣ} (hu : u ^ (Nat.card 𝓀[K] - 1) = 1)
    (hw : w ^ (Nat.card 𝓀[K] - 1) = 1) (h : unitsToResidue K u = unitsToResidue K w) :
    u = w := by
  have hmem : u * w⁻¹ ∈ unitFiltration K 1 := by
    rw [← ker_unitsToResidue, MonoidHom.mem_ker, map_mul, map_inv, h, mul_inv_cancel]
  have := eq_one_of_pow_eq_one (natCast_card_residueField_sub_one_ne_zero K) hmem
    (by rw [mul_pow, inv_pow, hu, hw, inv_one, mul_one])
  rwa [mul_inv_eq_one] at this

variable (K)

noncomputable def teichmuller : 𝓀[K]ˣ →* 𝒪[K]ˣ where
  toFun ζ := (exists_teichmuller_lift ζ).choose
  map_one' := eq_of_pow_card_sub_one (exists_teichmuller_lift 1).choose_spec.1 (one_pow _)
    (by rw [(exists_teichmuller_lift 1).choose_spec.2, map_one])
  map_mul' ζ η := eq_of_pow_card_sub_one (exists_teichmuller_lift (ζ * η)).choose_spec.1
    (by rw [mul_pow, (exists_teichmuller_lift ζ).choose_spec.1,
      (exists_teichmuller_lift η).choose_spec.1, one_mul])
    (by rw [(exists_teichmuller_lift (ζ * η)).choose_spec.2, map_mul,
      (exists_teichmuller_lift ζ).choose_spec.2, (exists_teichmuller_lift η).choose_spec.2])

variable {K}

@[simp]
theorem unitsToResidue_teichmuller (ζ : 𝓀[K]ˣ) : unitsToResidue K (teichmuller K ζ) = ζ :=
  (exists_teichmuller_lift ζ).choose_spec.2

theorem teichmuller_pow_card_sub_one (ζ : 𝓀[K]ˣ) :
    teichmuller K ζ ^ (Nat.card 𝓀[K] - 1) = 1 :=
  (exists_teichmuller_lift ζ).choose_spec.1

theorem unitsMulInvTeichmuller_mem (u : 𝒪[K]ˣ) :
    u * (teichmuller K (unitsToResidue K u))⁻¹ ∈ unitFiltration K 1 := by
  rw [← ker_unitsToResidue, MonoidHom.mem_ker, map_mul, map_inv, unitsToResidue_teichmuller,
    mul_inv_cancel]

variable (K)

noncomputable def unitsEquivResidueProd : 𝒪[K]ˣ ≃* 𝓀[K]ˣ × unitFiltration K 1 where
  toFun u := (unitsToResidue K u, ⟨_, unitsMulInvTeichmuller_mem u⟩)
  invFun p := teichmuller K p.1 * p.2
  left_inv u := by simp
  right_inv p := by
    obtain ⟨ζ, v, hv⟩ := p
    have hv' : unitsToResidue K v = 1 := by rwa [← MonoidHom.mem_ker, ker_unitsToResidue]
    ext
    · simp [hv']
    · simp [hv']
  map_mul' u w := by
    ext
    · simp
    · simp only [map_mul, mul_inv_rev, Prod.snd_mul, Subgroup.coe_mul]
      simp only [mul_comm, mul_left_comm, mul_assoc]

@[simp]
theorem unitsEquivResidueProd_fst (u : 𝒪[K]ˣ) :
    (unitsEquivResidueProd K u).1 = unitsToResidue K u := rfl

@[simp]
theorem unitsEquivResidueProd_symm_apply (ζ : 𝓀[K]ˣ) (v : unitFiltration K 1) :
    (unitsEquivResidueProd K).symm (ζ, v) = teichmuller K ζ * v := rfl

end Teichmuller

section Powers

theorem exists_pow_eq_of_mem {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) {m k : ℕ} (hm : m ≠ 0)
    {ε : 𝒪[K]ˣ} (hmk : (m : 𝒪[K]) = ϖ ^ k * ε) {w : 𝒪[K]ˣ}
    (hw : w ∈ unitFiltration K (2 * k + 1)) : ∃ x : 𝒪[K]ˣ, x ^ m = w := by
  set f : 𝒪[K][X] := X ^ m - C (w : 𝒪[K])
  obtain ⟨b, hb, -⟩ := exists_root_of_dvd hϖ f 1 k ε
    (by
      simp only [f, derivative_sub, derivative_C, sub_zero, derivative_X_pow, eval_mul,
        eval_C, eval_pow, eval_X, one_pow, mul_one]
      exact hmk)
    (by
      have := (mem_maximalIdeal_pow_iff hϖ).mp (mem_unitFiltration.mp hw)
      have e : f.eval 1 = -((w : 𝒪[K]) - 1) := by simp [f]
      rw [e, dvd_neg]
      exact this)
  have hbm : b ^ m = w := by simpa [f, sub_eq_zero] using hb
  have hbu : IsUnit b := (isUnit_pow_iff hm).mp (hbm ▸ w.isUnit)
  exact ⟨hbu.unit, by ext; simp [hbm]⟩

theorem exists_unitFiltration_le_range_pow {m : ℕ} (hm : (m : K) ≠ 0) :
    ∃ N, unitFiltration K N ≤ (powMonoidHom m : 𝒪[K]ˣ →* 𝒪[K]ˣ).range := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  have hm' : (m : 𝒪[K]) ≠ 0 := fun h ↦ hm (by have := congrArg Subtype.val h; simpa using this)
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm
  obtain ⟨k, ε, hk⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hm' hϖ
  refine ⟨2 * k + 1, fun w hw ↦ ?_⟩
  obtain ⟨x, hx⟩ := exists_pow_eq_of_mem hϖ hm0 (ε := ε) (by rw [hk, mul_comm]) hw
  exact ⟨x, hx⟩

theorem unitFiltration_one_le_range_pow {m : ℕ} (hm : (m : 𝓀[K]) ≠ 0) :
    unitFiltration K 1 ≤ (powMonoidHom m : 𝒪[K]ˣ →* 𝒪[K]ˣ).range := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  have hu : IsUnit (m : 𝒪[K]) := by
    rw [← residue_ne_zero_iff_isUnit, map_natCast]; exact hm
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm
  intro w hw
  obtain ⟨x, hx⟩ := exists_pow_eq_of_mem hϖ hm0 (k := 0) (ε := hu.unit) (by simp)
    (by simpa using hw)
  exact ⟨x, hx⟩

theorem finite_quotient_range_pow {m : ℕ} (hm : (m : K) ≠ 0) :
    Finite (Kˣ ⧸ (powMonoidHom m : Kˣ →* Kˣ).range) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  obtain ⟨N, hN⟩ := exists_unitFiltration_le_range_pow hm
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm
  set H := (powMonoidHom m : Kˣ →* Kˣ).range
  set ψ : 𝒪[K]ˣ →* Kˣ ⧸ H := (QuotientGroup.mk' H).comp (unitsIncl K)
  have hle : unitFiltration K N ≤ ψ.ker := by
    intro w hw
    obtain ⟨x, rfl⟩ := hN hw
    rw [MonoidHom.mem_ker]
    simp only [ψ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact ⟨unitsIncl K x, by simp⟩
  set ψ' := QuotientGroup.lift _ ψ hle
  set π := uniformizerUnit hϖ
  let g : Fin m × (𝒪[K]ˣ ⧸ unitFiltration K N) → Kˣ ⧸ H :=
    fun p ↦ (QuotientGroup.mk π : Kˣ ⧸ H) ^ (p.1 : ℕ) * ψ' p.2
  refine Finite.of_surjective g ?_
  intro y
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
  set p := unitsEquivIntProd hϖ x
  have hx : x = unitsOfIntProd hϖ p := by
    rw [← unitsEquivIntProd_symm_apply, MulEquiv.symm_apply_apply]
  set n := Multiplicative.toAdd p.1
  have hmpos : (0 : ℤ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm0
  set r := n % (m : ℤ)
  set q := n / (m : ℤ)
  have hr0 : 0 ≤ r := Int.emod_nonneg _ hmpos.ne'
  have hrm : r < m := Int.emod_lt_of_pos _ hmpos
  have hnrq : n = r + m * q := by have := Int.mul_ediv_add_emod n m; linarith
  refine ⟨(⟨r.toNat, by omega⟩, QuotientGroup.mk p.2), ?_⟩
  have hπ : π ^ n = π ^ r.toNat * (π ^ q) ^ m := by
    rw [← zpow_natCast, ← zpow_natCast (π ^ q) m, ← zpow_mul, ← zpow_add, Int.toNat_of_nonneg hr0,
      hnrq, mul_comm]
  have hxπ : x = π ^ n * unitsIncl K p.2 := by
    rw [hx]
    rfl
  simp only [g, ψ', QuotientGroup.lift_mk, ψ, MonoidHom.comp_apply, QuotientGroup.mk'_apply]
  rw [hxπ, hπ, ← QuotientGroup.mk_pow, ← QuotientGroup.mk_mul, QuotientGroup.eq]
  refine ⟨π ^ q, ?_⟩
  rw [powMonoidHom_apply, mul_right_comm (π ^ r.toNat), inv_mul_cancel_left]

theorem finite_quotient_range_pow_of_charZero [CharZero K] {m : ℕ} (hm : m ≠ 0) :
    Finite (Kˣ ⧸ (powMonoidHom m : Kˣ →* Kˣ).range) :=
  finite_quotient_range_pow (Nat.cast_ne_zero.mpr hm)

end Powers

end Sec_UnitsPowers


/-! ### FilteredSurj -/
section Sec_FilteredSurj

open Filter Topology Uniformity

section Filtration

variable {G : Type*} [Group G]

@[to_additive AddFiltrationCauchy
]
def FiltrationCauchy (F : ℕ → Subgroup G) (x : ℕ → G) : Prop :=
  ∀ N, ∃ M, ∀ m ≥ M, ∀ n ≥ M, x n / x m ∈ F N

@[to_additive AddFiltrationTendsto
]
def FiltrationTendsto (F : ℕ → Subgroup G) (x : ℕ → G) (y : G) : Prop :=
  ∀ N, ∃ M, ∀ n ≥ M, x n / y ∈ F N

@[to_additive AddFiltrationComplete
]
def FiltrationComplete (F : ℕ → Subgroup G) : Prop :=
  ∀ x : ℕ → G, FiltrationCauchy F x → ∃ y, FiltrationTendsto F x y

@[to_additive AddFiltrationSeparated
]
def FiltrationSeparated (F : ℕ → Subgroup G) : Prop :=
  ∀ g : G, (∀ n, g ∈ F n) → g = 1

end Filtration

section Surjectivity

variable {G H : Type*} [Group G] [Group H]

@[to_additive map_eq_of_graded_surjective_add
]
theorem map_eq_of_graded_surjective {F : ℕ → Subgroup G} {E : ℕ → Subgroup H}
    (hF : Antitone F) (hE : Antitone E) (hG : FiltrationComplete F)
    (hH : FiltrationSeparated E) (f : G →* H) {φ : ℕ → ℕ} (hφ : Tendsto φ atTop atTop)
    (k : ℕ) (hmap : ∀ n, k ≤ n → ∀ g ∈ F n, f g ∈ E (φ n))
    (hgr : ∀ n, k ≤ n → ∀ h ∈ E (φ n), ∃ g ∈ F n, h / f g ∈ E (φ (n + 1))) :
    (F k).map f = E (φ k) := by
  apply le_antisymm
  · rintro _ ⟨g, hg, rfl⟩
    exact hmap k le_rfl g hg
  intro h hh
  rw [Subgroup.mem_map]
  have hs : ∀ (n : ℕ) (a : H), ∃ g : G,
      k ≤ n → a ∈ E (φ n) → g ∈ F n ∧ a / f g ∈ E (φ (n + 1)) := by
    intro n a
    by_cases hc : k ≤ n ∧ a ∈ E (φ n)
    · obtain ⟨g, hg1, hg2⟩ := hgr n hc.1 a hc.2
      exact ⟨g, fun _ _ => ⟨hg1, hg2⟩⟩
    · exact ⟨1, fun h1 h2 => absurd ⟨h1, h2⟩ hc⟩
  choose s hs using hs

  obtain ⟨r, hr0, hrs⟩ : ∃ r : ℕ → H, r 0 = h ∧ ∀ j, r (j + 1) = r j / f (s (k + j) (r j)) :=
    ⟨fun j => Nat.rec h (fun j rj => rj / f (s (k + j) rj)) j, rfl, fun _ => rfl⟩
  have hrE : ∀ j, r j ∈ E (φ (k + j)) := by
    intro j
    induction j with
    | zero => simpa [hr0] using hh
    | succ j ih =>
      rw [hrs, ← add_assoc]
      exact (hs (k + j) (r j) (Nat.le_add_right k j) ih).2

  obtain ⟨D, hD⟩ : ∃ D : ℕ → G, ∀ j, D j = s (k + j) (r j) := ⟨_, fun _ => rfl⟩
  have hDF : ∀ j, D j ∈ F (k + j) := fun j => by
    rw [hD]
    exact (hs (k + j) (r j) (Nat.le_add_right k j) (hrE j)).1
  have hrs' : ∀ j, r (j + 1) = r j / f (D j) := fun j => by rw [hrs, hD]

  obtain ⟨x, hx0, hxs⟩ : ∃ x : ℕ → G, x 0 = D 0 ∧ ∀ j, x (j + 1) = D (j + 1) * x j :=
    ⟨fun j => Nat.rec (D 0) (fun j xj => D (j + 1) * xj) j, rfl, fun _ => rfl⟩
  have hxr : ∀ j, h / f (x j) = r (j + 1) := by
    intro j
    induction j with
    | zero => rw [hx0, hrs', hr0]
    | succ j ih =>
      rw [hxs, hrs' (j + 1), ← ih, map_mul]
      simp only [div_eq_mul_inv, mul_inv_rev, mul_assoc]
  have hxF : ∀ m d, x (m + d) / x m ∈ F (k + m + 1) := by
    intro m d
    induction d with
    | zero => simp
    | succ d ih =>
      have e : x (m + (d + 1)) / x m = D (m + d + 1) * (x (m + d) / x m) := by
        rw [← add_assoc, hxs, div_eq_mul_inv, div_eq_mul_inv, mul_assoc]
      rw [e]
      exact (F _).mul_mem (hF (by omega) (hDF (m + d + 1))) ih
  have hC : FiltrationCauchy F x := by
    intro N
    refine ⟨N, fun m hm n hn => ?_⟩
    rcases le_total m n with hmn | hnm
    · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
      exact hF (by omega) (hxF m d)
    · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hnm
      have e := (F _).inv_mem (hxF n d)
      rw [inv_div] at e
      exact hF (by omega) e
  have hxk : ∀ j, x j ∈ F k := by
    intro j
    induction j with
    | zero => rw [hx0]; simpa using hDF 0
    | succ j ih => rw [hxs]; exact (F k).mul_mem (hF (by omega) (hDF (j + 1))) ih
  obtain ⟨y, hy⟩ := hG x hC
  obtain ⟨M0, hM0⟩ := hy k
  have hyk : y ∈ F k := by
    have e : (x M0 / y)⁻¹ * x M0 = y := by
      simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel, mul_one]
    rw [← e]
    exact (F k).mul_mem ((F k).inv_mem (hM0 M0 le_rfl)) (hxk M0)
  refine ⟨y, hyk, ?_⟩
  have h1 : h / f y = 1 := by
    apply hH
    intro m
    obtain ⟨N0, hN0⟩ := Filter.tendsto_atTop_atTop.mp hφ m
    obtain ⟨M, hM⟩ := hy (max N0 k)
    have e : h / f y = r (max M N0 + 1) * f (x (max M N0) / y) := by
      rw [← hxr (max M N0), map_div]
      simp only [div_eq_mul_inv, mul_assoc, inv_mul_cancel_left]
    rw [e]
    refine (E m).mul_mem ?_ ?_
    · exact hE (hN0 _ (by omega)) (hrE (max M N0 + 1))
    · exact hE (hN0 _ (le_max_left _ _))
        (hmap _ (le_max_right _ _) _ (hM (max M N0) (le_max_left _ _)))
  exact (div_eq_one.mp h1).symm

@[to_additive surjective_of_graded_surjective_add
]
theorem surjective_of_graded_surjective {F : ℕ → Subgroup G} {E : ℕ → Subgroup H}
    (hF : Antitone F) (hE : Antitone E) (hG : FiltrationComplete F)
    (hH : FiltrationSeparated E) (f : G →* H) {φ : ℕ → ℕ} (hφ : Tendsto φ atTop atTop)
    (hF0 : F 0 = ⊤) (hE0 : E (φ 0) = ⊤) (hmap : ∀ n, ∀ g ∈ F n, f g ∈ E (φ n))
    (hgr : ∀ n, ∀ h ∈ E (φ n), ∃ g ∈ F n, h / f g ∈ E (φ (n + 1))) :
    Function.Surjective f := by
  intro h
  have e := map_eq_of_graded_surjective hF hE hG hH f hφ 0 (fun n _ => hmap n)
    (fun n _ => hgr n)
  have hh : h ∈ E (φ 0) := by rw [hE0]; exact Subgroup.mem_top h
  rw [← e, hF0] at hh
  obtain ⟨g, -, rfl⟩ := hh
  exact ⟨g, rfl⟩

end Surjectivity

section Topological

@[to_additive addFiltrationComplete_of_hasBasis
]
theorem filtrationComplete_of_hasBasis {G : Type*} [Group G] [UniformSpace G]
    [IsRightUniformGroup G] [CompleteSpace G] {F : ℕ → Subgroup G}
    (hb : (𝓝 (1 : G)).HasBasis (fun _ => True) (fun n => (F n : Set G))) :
    FiltrationComplete F := by
  intro x hx
  have hU : (𝓤 G).HasBasis (fun _ : ℕ => True)
      (fun n => (fun p : G × G => p.2 / p.1) ⁻¹' (F n : Set G)) := by
    rw [uniformity_eq_comap_nhds_one G]
    exact hb.comap _
  have hcs : CauchySeq x := by
    rw [hU.cauchySeq_iff]
    intro N _
    obtain ⟨M, hM⟩ := hx N
    exact ⟨M, fun m hm n hn => hM m hm n hn⟩
  obtain ⟨y, hy⟩ := cauchySeq_tendsto_of_complete hcs
  refine ⟨y, fun N => ?_⟩
  have h1 : Tendsto (fun n => x n / y) atTop (𝓝 1) := by
    simpa using hy.div_const' y
  exact eventually_atTop.mp ((hb.tendsto_right_iff.mp h1) N trivial)

@[to_additive addFiltrationSeparated_of_hasBasis
]
theorem filtrationSeparated_of_hasBasis {H : Type*} [Group H] [TopologicalSpace H] [T1Space H]
    {E : ℕ → Subgroup H}
    (hb : (𝓝 (1 : H)).HasBasis (fun _ => True) (fun n => (E n : Set H))) :
    FiltrationSeparated E := by
  intro g hg
  by_contra hne
  obtain ⟨i, -, hi⟩ := hb.mem_iff.mp
    (isOpen_compl_singleton.mem_nhds (Set.mem_compl_singleton_iff.mpr (Ne.symm hne)))
  exact hi (hg i) rfl

@[to_additive map_eq_of_graded_surjective_of_hasBasis_add
]
theorem map_eq_of_graded_surjective_of_hasBasis {G H : Type*} [Group G] [UniformSpace G]
    [IsRightUniformGroup G] [CompleteSpace G] [Group H] [TopologicalSpace H] [T1Space H]
    {F : ℕ → Subgroup G} {E : ℕ → Subgroup H} (hF : Antitone F) (hE : Antitone E)
    (hFb : (𝓝 (1 : G)).HasBasis (fun _ => True) (fun n => (F n : Set G)))
    (hEb : (𝓝 (1 : H)).HasBasis (fun _ => True) (fun n => (E n : Set H)))
    (f : G →* H) {φ : ℕ → ℕ} (hφ : Tendsto φ atTop atTop)
    (k : ℕ) (hmap : ∀ n, k ≤ n → ∀ g ∈ F n, f g ∈ E (φ n))
    (hgr : ∀ n, k ≤ n → ∀ h ∈ E (φ n), ∃ g ∈ F n, h / f g ∈ E (φ (n + 1))) :
    (F k).map f = E (φ k) :=
  map_eq_of_graded_surjective hF hE (filtrationComplete_of_hasBasis hFb)
    (filtrationSeparated_of_hasBasis hEb) f hφ k hmap hgr

end Topological

end Sec_FilteredSurj


section Sec_UnitFiltrationComplete

open ValuativeRel IsLocalRing
open scoped WithZero

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

section Filtration

theorem div_mem_unitFiltration_iff {k : ℕ} {x y : 𝒪[K]ˣ} :
    x / y ∈ unitFiltration K k ↔ (x : 𝒪[K]) - y ∈ 𝓂[K] ^ k := by
  rw [mem_unitFiltration]
  have h1 : ((x / y : 𝒪[K]ˣ) : 𝒪[K]) - 1 = ((x : 𝒪[K]) - y) * ((y⁻¹ : 𝒪[K]ˣ) : 𝒪[K]) := by
    rw [div_eq_mul_inv, Units.val_mul]
    linear_combination (Units.mul_inv y)
  have h2 : (x : 𝒪[K]) - y = (y : 𝒪[K]) * (((x / y : 𝒪[K]ˣ) : 𝒪[K]) - 1) := by
    rw [div_eq_mul_inv, Units.val_mul]
    linear_combination (-(x : 𝒪[K])) * (Units.mul_inv y)
  constructor
  · intro h; rw [h2]; exact Ideal.mul_mem_left _ _ h
  · intro h; rw [h1]; exact Ideal.mul_mem_right _ _ h

theorem eq_zero_of_forall_mem_maximalIdeal_pow {x : 𝒪[K]} (hx : ∀ k, x ∈ 𝓂[K] ^ k) : x = 0 := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  by_contra h0
  obtain ⟨m, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible h0 hϖ
  have h := (mem_maximalIdeal_pow_iff hϖ).mp (hx (m + 1))
  rw [pow_succ, mul_comm (u : 𝒪[K]), mul_dvd_mul_iff_left (pow_ne_zero m hϖ.ne_zero)] at h
  exact hϖ.not_isUnit (isUnit_of_dvd_unit h u.isUnit)

theorem filtrationSeparated_unitFiltration : FiltrationSeparated (unitFiltration K) := by
  intro u hu
  have : (u : 𝒪[K]) - 1 = 0 := eq_zero_of_forall_mem_maximalIdeal_pow fun k ↦ hu k
  ext
  simpa [sub_eq_zero] using this

theorem filtrationComplete_unitFiltration : FiltrationComplete (unitFiltration K) := by
  have hc := (isAdicComplete_integer (K := K)).toIsPrecomplete
  intro x hx
  choose M hM using hx

  let M' : ℕ → ℕ := fun N ↦ (Finset.range (N + 1)).sup M
  have hM'ge : ∀ N, M N ≤ M' N := fun N ↦ Finset.le_sup (Finset.self_mem_range_succ N)
  have hM'mono : Monotone M' := fun a b hab ↦
    Finset.sup_mono (Finset.range_subset_range.2 (by omega))
  have hy : ∀ {a b : ℕ}, a ≤ b →
      ((x (M' a) : 𝒪[K]) ≡ x (M' b) [SMOD (𝓂[K] ^ a • ⊤ : Submodule 𝒪[K] 𝒪[K])]) := by
    intro a b hab
    rw [smul_eq_mul, Ideal.mul_top, SModEq.sub_mem]
    exact div_mem_unitFiltration_iff.mp
      (hM a (M' b) ((hM'ge a).trans (hM'mono hab)) (M' a) (hM'ge a))
  obtain ⟨L, hL⟩ := hc.prec' (fun N ↦ (x (M' N) : 𝒪[K])) hy
  have hL' : ∀ N, (x (M' N) : 𝒪[K]) - L ∈ 𝓂[K] ^ N := fun N ↦ by
    have := hL N
    rwa [smul_eq_mul, Ideal.mul_top, SModEq.sub_mem] at this
  have hLu : IsUnit L := by
    by_contra hL0
    have h1 : L ∈ 𝓂[K] := (IsLocalRing.mem_maximalIdeal L).mpr hL0
    have h2 := hL' 1
    rw [pow_one] at h2
    have : (x (M' 1) : 𝒪[K]) ∈ 𝓂[K] := by
      simpa using Ideal.add_mem _ h2 h1
    exact (IsLocalRing.mem_maximalIdeal _).mp this (x (M' 1)).isUnit
  refine ⟨hLu.unit, fun N ↦ ⟨M' N, fun n hn ↦ ?_⟩⟩
  rw [div_mem_unitFiltration_iff, IsUnit.unit_spec]
  have h1 : (x n : 𝒪[K]) - x (M' N) ∈ 𝓂[K] ^ N :=
    div_mem_unitFiltration_iff.mp (hM N (M' N) (hM'ge N) n ((hM'ge N).trans hn))
  have := Ideal.add_mem _ h1 (hL' N)
  rwa [sub_add_sub_cancel] at this

end Filtration

end Sec_UnitFiltrationComplete


/-! ### Examples -/
section Sec_Examples

open ValuativeRel WithZero

theorem isValuativeTopology_of_valued {R : Type*} [CommRing R] [ValuativeRel R]
    {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] [Valued R Γ₀]
    [(Valued.v : Valuation R Γ₀).Compatible] : IsValuativeTopology R :=
  IsValuativeTopology.of_mem_nhds_zero_iff_vle (Valued.v : Valuation R Γ₀) fun {s} => by
    simpa using (Valued.hasBasis_nhds_zero R Γ₀).mem_iff (t := s)

namespace Padic

variable (p : ℕ) [hp : Fact p.Prime]

theorem mulValuation_le_iff_norm_le (x y : ℚ_[p]) :
    Padic.mulValuation x ≤ Padic.mulValuation y ↔ ‖x‖ ≤ ‖y‖ := by
  by_cases hx : x = 0
  · simp [hx]
  by_cases hy : y = 0
  · simp [hx, hy]
  rw [Padic.norm_eq_zpow_neg_valuation hx, Padic.norm_eq_zpow_neg_valuation hy,
    zpow_le_zpow_iff_right₀ (by exact_mod_cast hp.out.one_lt)]
  simp [hx, hy, -exp_neg]

instance isValuativeTopology : IsValuativeTopology ℚ_[p] :=
  letI : Valued ℚ_[p] NNReal := NormedField.toValued
  haveI : (Valued.v : Valuation ℚ_[p] NNReal).Compatible := ⟨fun x y => by
    rw [Valuation.Compatible.vle_iff_le (v := Padic.mulValuation) x y,
      mulValuation_le_iff_norm_le]
    rfl⟩
  isValuativeTopology_of_valued

instance isNonarchimedeanLocalField : IsNonarchimedeanLocalField ℚ_[p] where
  toIsValuativeTopology := inferInstance
  toLocallyCompactSpace := inferInstance
  toIsNontrivial := inferInstance

end Padic

namespace LaurentSeries

open _root_.LaurentSeries HahnSeries

variable (K : Type*) [Field K]

noncomputable instance : ValuativeRel K⸨X⸩ := .ofValuation Valued.v

instance : (Valued.v : Valuation K⸨X⸩ ℤᵐ⁰).Compatible := .ofValuation _

instance : IsValuativeTopology K⸨X⸩ := isValuativeTopology_of_valued

theorem valued_X : Valued.v (single 1 1 : K⸨X⸩) = exp (-1 : ℤ) := by
  simpa using valuation_single_zpow (K := K) 1

instance : ValuativeRel.IsNontrivial K⸨X⸩ where
  condition := ⟨valuation _ (single 1 1), by simp, by
    intro h
    have := (ValuativeRel.isEquiv (valuation K⸨X⸩) Valued.v).eq_one_iff_eq_one.mp h
    rw [valued_X] at this
    simp at this⟩

section Finite

variable {K}

theorem mem_integer_iff (f : K⸨X⸩) :
    f ∈ Valued.integer K⸨X⸩ ↔ ∀ n : ℤ, n < 0 → f.coeff n = 0 := by
  change Valued.v f ≤ 1 ↔ _
  simpa using valuation_le_iff_coeff_lt_eq_zero (K := K) (D := 0) (f := f)

theorem C_mem_integer (c : K) : (HahnSeries.C c : K⸨X⸩) ∈ Valued.integer K⸨X⸩ := by
  rw [mem_integer_iff]
  intro n hn
  simp [HahnSeries.C_apply, hn.ne]

theorem residue_C_coeff_zero (x : Valued.integer K⸨X⸩) :
    IsLocalRing.residue _ ⟨HahnSeries.C ((x : K⸨X⸩).coeff 0), C_mem_integer _⟩ =
      IsLocalRing.residue _ x := by
  change Ideal.Quotient.mk _ _ = Ideal.Quotient.mk _ _
  rw [Ideal.Quotient.eq, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    Valuation.Integer.not_isUnit_iff_valuation_lt_one]
  have hx := (mem_integer_iff (x : K⸨X⸩)).mp x.2
  have : Valued.v (HahnSeries.C ((x : K⸨X⸩).coeff 0) - (x : K⸨X⸩)) ≤ exp (-1 : ℤ) := by
    rw [valuation_le_iff_coeff_lt_eq_zero]
    intro n hn
    rcases lt_or_eq_of_le (show n ≤ 0 by omega) with h | rfl
    · simp [HahnSeries.C_apply, h.ne, hx n h]
    · simp [HahnSeries.C_apply]
  refine lt_of_le_of_lt this ?_
  rw [← exp_zero, exp_lt_exp]
  norm_num

variable (K) [Finite K]

instance finite_residueField : Finite (IsLocalRing.ResidueField (Valued.integer K⸨X⸩)) :=
  Finite.of_surjective (fun c : K => IsLocalRing.residue _ ⟨HahnSeries.C c, C_mem_integer c⟩)
    fun r => by
      obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective r
      exact ⟨_, residue_C_coeff_zero x⟩

end Finite

instance : Nontrivial (MonoidWithZeroHom.valueGroup
    (MonoidWithZeroHom.ofClass (Valued.v : Valuation K⸨X⸩ ℤᵐ⁰))) := by
  refine ⟨⟨⟨Units.mk0 (exp (-1 : ℤ)) (by simp), MonoidWithZeroHom.mem_valueGroup _ ?_⟩, 1, ?_⟩⟩
  · exact ⟨single 1 1, valued_X K⟩
  · intro h
    have := congrArg (fun u : MonoidWithZeroHom.valueGroup _ => ((u : ℤᵐ⁰ˣ) : ℤᵐ⁰)) h
    simp at this

instance : IsDiscreteValuationRing (Valued.integer K⸨X⸩) :=
  inferInstanceAs (IsDiscreteValuationRing (Valued.v : Valuation K⸨X⸩ ℤᵐ⁰).valuationSubring)

instance [Finite K] : LocallyCompactSpace K⸨X⸩ := by
  let := Valuation.IsRankOneDiscrete.rankOne (Valued.v : Valuation K⸨X⸩ ℤᵐ⁰)
    (e := 2) one_lt_two
  have hc : CompactSpace (Valued.integer K⸨X⸩) :=
    Valued.integer.compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField.mpr
      ⟨(Valued.isClosed_integer K⸨X⸩).completeSpace_coe, inferInstance, inferInstance⟩
  exact IsCompact.locallyCompactSpace_of_mem_nhds_of_addGroup
    (isCompact_iff_compactSpace.mpr hc) ((Valued.isOpen_integer K⸨X⸩).mem_nhds (zero_mem _))

instance isNonarchimedeanLocalField [Finite K] : IsNonarchimedeanLocalField K⸨X⸩ where
  toIsValuativeTopology := inferInstance
  toLocallyCompactSpace := inferInstance
  toIsNontrivial := inferInstance

end LaurentSeries

end Sec_Examples


/-! ### ExamplesCharZero -/
section Sec_ExamplesCharZero

open ValuativeRel WithZero Topology

namespace CharZero

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

instance fact_prime_ringChar : Fact (ringChar 𝓀[K]).Prime :=
  ⟨CharP.char_is_prime 𝓀[K] (ringChar 𝓀[K])⟩

variable (p : ℕ) [CharP 𝓀[K] p]

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in

theorem valuation_intCast_le_one (n : ℤ) : valuation K (n : K) ≤ 1 :=
  (Valuation.mem_integer_iff _ _).mp (intCast_mem _ n)

theorem valuation_intCast_eq_one_iff (n : ℤ) : valuation K (n : K) = 1 ↔ ¬ (p : ℤ) ∣ n := by
  have hres : IsLocalRing.residue 𝒪[K] (n : 𝒪[K]) = (n : 𝓀[K]) := map_intCast _ n
  rw [← CharP.intCast_eq_zero_iff 𝓀[K] p n, ← hres, IsLocalRing.residue_eq_zero_iff,
    IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    Valuation.Integer.not_isUnit_iff_valuation_lt_one]
  push_cast
  constructor
  · intro h
    simp [h]
  · intro h
    exact le_antisymm (valuation_intCast_le_one K n) (not_lt.mp h)

variable [Fact p.Prime]

omit [Fact p.Prime] in

theorem valuation_p_lt_one : valuation K (p : K) < 1 := by
  refine lt_of_le_of_ne (by exact_mod_cast valuation_intCast_le_one K p) fun h => ?_
  have := (valuation_intCast_eq_one_iff K p p).mp (by exact_mod_cast h)
  exact this dvd_rfl

variable [CharZero K]

theorem valuation_ratCast_le_one_iff (q : ℚ) : valuation K (q : K) ≤ 1 ↔ ¬ p ∣ q.den := by
  have hden : (q.den : K) ≠ 0 := by exact_mod_cast q.den_ne_zero
  have hq : (q : K) = (q.num : K) / (q.den : K) := by
    rw [← Rat.cast_intCast, ← Rat.cast_natCast, ← Rat.cast_div, Rat.num_div_den]
  have hvden : valuation K (q.den : K) ≠ 0 := by simp
  rw [hq, map_div₀, div_le_one₀ (zero_lt_iff.mpr hvden)]
  constructor
  · intro h hp
    have hnum : ¬ (p : ℤ) ∣ q.num := by
      intro hn
      rw [Int.natCast_dvd] at hn
      exact Nat.not_coprime_of_dvd_of_dvd (Nat.Prime.one_lt Fact.out) hn hp q.reduced
    have h1 := (valuation_intCast_eq_one_iff K p q.num).mpr hnum
    obtain ⟨m, hm⟩ := hp
    have h2 : valuation K (q.den : K) < 1 := by
      rw [hm, Nat.cast_mul, map_mul]
      calc valuation K (p : K) * valuation K (m : K)
          ≤ valuation K (p : K) * 1 := by
            gcongr
            exact_mod_cast valuation_intCast_le_one K m
        _ < 1 := by simp [valuation_p_lt_one K p]
    rw [h1] at h
    exact absurd h (not_le.mpr h2)
  · intro hp
    have h1 : valuation K (q.den : K) = 1 := by
      have := (valuation_intCast_eq_one_iff K p q.den).mpr (by exact_mod_cast hp)
      exact_mod_cast this
    rw [h1]
    exact valuation_intCast_le_one K q.num

theorem isEquiv_comap_ratCast :
    ((valuation K).comap (Rat.castHom K)).IsEquiv (Rat.padicValuation p) :=
  Valuation.isEquiv_of_val_le_one fun q => by
    simp [valuation_ratCast_le_one_iff K p, Rat.padicValuation_le_one_iff]

section Embedding

noncomputable abbrev ratHom : WithVal (Rat.padicValuation p) →+* K :=
  (Rat.castHom K).comp (WithVal.equiv (Rat.padicValuation p)).toRingHom

theorem continuousAt_ratHom : ContinuousAt (ratHom K p) 0 := by
  rw [ContinuousAt, map_zero]
  refine ((IsValuativeTopology.hasBasis_nhds_zero' _).tendsto_iff
    (IsValuativeTopology.hasBasis_nhds_zero' K)).mpr fun γ hγ => ?_
  obtain ⟨n, hn⟩ := exists_pow_lt₀ (valuation_p_lt_one K p) (Units.mk0 γ hγ)
  set v := Rat.padicValuation p
  set t : WithVal v := (WithVal.equiv v).symm ((p : ℚ) ^ n)
  refine ⟨valuation (WithVal v) t, ?_, fun x hx => ?_⟩
  · simp [t, Nat.Prime.ne_zero Fact.out]
  · simp only [Set.mem_ofPred_eq] at hx ⊢
    have h1 := (ValuativeRel.isEquiv (valuation (WithVal v)) (WithVal.valuation v)).lt_iff_lt.mp hx
    have h2 : v (WithVal.equiv v x) < v ((p : ℚ) ^ n) := by simpa [t] using h1
    have h3 := (isEquiv_comap_ratCast K p).lt_iff_lt.mpr h2
    simp only [Valuation.comap_apply, Rat.coe_castHom] at h3
    calc valuation K (ratHom K p x) = valuation K ((WithVal.equiv v x : ℚ) : K) := rfl
      _ < valuation K (((p : ℚ) ^ n : ℚ) : K) := h3
      _ = valuation K (p : K) ^ n := by simp
      _ < γ := hn

section Uniform

local instance uniformSpaceK : UniformSpace K := IsTopologicalAddGroup.rightUniformSpace K

local instance isUniformAddGroupK : IsUniformAddGroup K := isUniformAddGroup_of_addCommGroup

theorem uniformContinuous_ratHom : UniformContinuous (ratHom K p) :=
  uniformContinuous_of_continuousAt_zero (ratHom K p) (continuousAt_ratHom K p)

noncomputable def padicHom : ℚ_[p] →+* K :=
  IsDenseInducing.extendRingHom Padic.isUniformInducing_cast_withVal
    Padic.isDenseInducing_cast_withVal.dense (uniformContinuous_ratHom K p)

theorem continuous_padicHom : Continuous (padicHom K p) :=
  (uniformContinuous_uniformly_extend Padic.isUniformInducing_cast_withVal
    Padic.isDenseInducing_cast_withVal.dense (uniformContinuous_ratHom K p)).continuous

end Uniform

theorem valuation_padicHom_padicInt_le_one (x : ℤ_[p]) :
    valuation K (padicHom K p (x : ℚ_[p])) ≤ 1 := by
  refine PadicInt.denseRange_intCast.induction_on x ?_ fun n => ?_
  · exact (Valuation.isClosed_integer (v := valuation K)).preimage
      ((continuous_padicHom K p).comp continuous_subtype_val)
  · simpa using valuation_intCast_le_one K n

theorem valuation_padicHom_le_one_iff (x : ℚ_[p]) :
    valuation K (padicHom K p x) ≤ 1 ↔ ‖x‖ ≤ 1 := by
  refine ⟨fun hv => ?_, fun hx => valuation_padicHom_padicInt_le_one K p ⟨x, hx⟩⟩
  by_contra hx
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hx
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Nat.Prime.ne_zero Fact.out)
  set y : ℚ_[p] := ((p : ℚ_[p]) * x)⁻¹
  have hxinv : ‖x⁻¹‖ ≤ (p : ℝ) ^ (-1 : ℤ) := by
    have : ‖x⁻¹‖ < (p : ℝ) ^ (0 : ℤ) := by
      rw [norm_inv, zpow_zero]
      exact inv_lt_one_of_one_lt₀ (not_le.mp hx)
    simpa using (Padic.norm_lt_pow_iff_norm_le_pow_sub_one x⁻¹ 0).mp this
  have hy : ‖y‖ ≤ 1 := by
    have hp : (0 : ℝ) < p := by exact_mod_cast (Nat.Prime.pos Fact.out)
    simp only [y, mul_inv, norm_mul, norm_inv, Padic.norm_p, inv_inv] at hxinv ⊢
    rw [zpow_neg_one] at hxinv
    calc (p : ℝ) * ‖x‖⁻¹ ≤ p * (p : ℝ)⁻¹ := by gcongr
      _ = 1 := mul_inv_cancel₀ hp.ne'
  have hvy := valuation_padicHom_padicInt_le_one K p ⟨y, hy⟩
  simp only at hvy
  have hone : padicHom K p x * padicHom K p y * padicHom K p p = 1 := by
    rw [← map_mul, ← map_mul]
    simp [y, hx0, hp0]
  have hvp : valuation K (padicHom K p p) < 1 := by
    simpa using valuation_p_lt_one K p
  have := congrArg (valuation K) hone
  rw [map_mul, map_mul, map_one] at this
  have h1 : valuation K (padicHom K p x) * valuation K (padicHom K p y) ≤ 1 :=
    mul_le_one' hv hvy
  have h2 := (mul_le_of_le_one_left' h1 : _ ≤ valuation K (padicHom K p p))
  exact absurd (this ▸ h2) (not_le.mpr hvp)

theorem isEquiv_comap_padicHom :
    ((valuation K).comap (padicHom K p)).IsEquiv Padic.mulValuation :=
  Valuation.isEquiv_of_val_le_one fun x => by
    rw [Valuation.comap_apply, valuation_padicHom_le_one_iff]
    simpa using (RHDirect.CFT.LocalField.Padic.mulValuation_le_iff_norm_le p x 1).symm

theorem padicHom_vle_iff (a b : ℚ_[p]) : padicHom K p a ≤ᵥ padicHom K p b ↔ a ≤ᵥ b := by
  rw [Valuation.Compatible.vle_iff_le (v := valuation K),
    Valuation.Compatible.vle_iff_le (v := Padic.mulValuation)]
  simpa using (isEquiv_comap_padicHom K p).le_iff_le (x := a) (y := b)

theorem finiteDimensional_padicHom :
    letI := (padicHom K p).toAlgebra
    FiniteDimensional ℚ_[p] K := by
  let := (padicHom K p).toAlgebra
  have : T2Space K := by
    let := IsTopologicalAddGroup.rightUniformSpace K
    have := isUniformAddGroup_of_addCommGroup (G := K)
    infer_instance
  have : ContinuousSMul ℚ_[p] K :=
    ⟨((continuous_padicHom K p).comp continuous_fst).mul continuous_snd⟩
  exact FiniteDimensional.of_locallyCompactSpace ℚ_[p]

end Embedding

end CharZero

theorem exists_padic_finiteDimensional_of_charZero (K : Type*) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] [CharZero K] :
    ∃ (p : ℕ) (_ : Fact p.Prime) (_ : Algebra ℚ_[p] K), p = ringChar 𝓀[K] ∧
      ValuativeExtension ℚ_[p] K ∧ FiniteDimensional ℚ_[p] K ∧
        Continuous (algebraMap ℚ_[p] K) := by
  let alg := (CharZero.padicHom K (ringChar 𝓀[K])).toAlgebra
  exact ⟨ringChar 𝓀[K], inferInstance, alg, rfl, ⟨CharZero.padicHom_vle_iff K _⟩,
    CharZero.finiteDimensional_padicHom K _, CharZero.continuous_padicHom K _⟩

end Sec_ExamplesCharZero


/-! ### ExamplesTeichmuller -/
section Sec_ExamplesTeichmuller

open ValuativeRel Polynomial IsLocalRing

namespace EqualChar

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable (p : ℕ) [hp : Fact p.Prime] [CharP K p]

instance charP_integer : CharP 𝒪[K] p :=
  (CharP.charP_iff_prime_eq_zero hp.out).mpr (Subtype.ext (by simp))

instance charP_residueField : CharP 𝓀[K] p :=
  (CharP.charP_iff_prime_eq_zero hp.out).mpr (by
    rw [← map_natCast (residue 𝒪[K]), CharP.cast_eq_zero, map_zero])

theorem exists_card_residueField_eq : ∃ n : ℕ, 0 < n ∧ Nat.card 𝓀[K] = p ^ n := by
  let := Fintype.ofFinite 𝓀[K]
  obtain ⟨n, -, h⟩ := FiniteField.card 𝓀[K] p
  exact ⟨n, n.pos, by rw [Nat.card_eq_fintype_card, h]⟩

noncomputable def residueExponent : ℕ := (exists_card_residueField_eq K p).choose

theorem residueExponent_pos : 0 < residueExponent K p :=
  (exists_card_residueField_eq K p).choose_spec.1

theorem card_residueField : Nat.card 𝓀[K] = p ^ residueExponent K p :=
  (exists_card_residueField_eq K p).choose_spec.2

theorem one_lt_card_residueField : 1 < p ^ residueExponent K p :=
  Nat.one_lt_pow (residueExponent_pos K p).ne' hp.out.one_lt

theorem pow_card_residueField (a : 𝓀[K]) : a ^ p ^ residueExponent K p = a := by
  let := Fintype.ofFinite 𝓀[K]
  rw [← card_residueField, Nat.card_eq_fintype_card]
  exact FiniteField.pow_card a

noncomputable def teichmullerSubring : Subring 𝒪[K] :=
  (iterateFrobenius 𝒪[K] p (residueExponent K p)).eqLocus (RingHom.id _)

theorem mem_teichmullerSubring {x : 𝒪[K]} :
    x ∈ teichmullerSubring K p ↔ x ^ p ^ residueExponent K p = x := Iff.rfl

theorem eq_zero_of_mem_teichmullerSubring {x : 𝒪[K]} (hx : x ∈ teichmullerSubring K p)
    (h0 : residue 𝒪[K] x = 0) : x = 0 := by
  by_contra hne
  have hv0 : 0 < valuation K (x : K) := by
    rw [zero_lt_iff, ne_eq, map_eq_zero]
    exact fun h => hne (Subtype.ext h)
  have hv1 : valuation K (x : K) < 1 := by
    rw [residue_eq_zero_iff, mem_maximalIdeal, mem_nonunits_iff] at h0
    exact (Valuation.Integer.not_isUnit_iff_valuation_lt_one).mp h0
  have h := pow_lt_self_of_lt_one₀ hv0 hv1 (one_lt_card_residueField K p)
  rw [← map_pow, ← Subring.coe_pow, (mem_teichmullerSubring K p).mp hx] at h
  exact lt_irrefl _ h

theorem exists_mem_teichmullerSubring_residue_eq (a : 𝓀[K]) :
    ∃ x ∈ teichmullerSubring K p, residue 𝒪[K] x = a := by
  let := IsTopologicalAddGroup.rightUniformSpace K
  have := isUniformAddGroup_of_addCommGroup (G := K)
  set q := p ^ residueExponent K p with hqdef
  have hq : 1 < q := one_lt_card_residueField K p
  have hq0 : ((q : ℕ) : 𝒪[K]) = 0 :=
    (CharP.cast_eq_zero_iff 𝒪[K] p q).mpr (dvd_pow_self p (residueExponent_pos K p).ne')
  obtain ⟨a₀, rfl⟩ := residue_surjective a
  set f : 𝒪[K][X] := X ^ q - X with hf
  have hmonic : f.Monic := monic_X_pow_sub (by rw [degree_X]; exact_mod_cast hq)
  have hroot : f.eval a₀ ∈ maximalIdeal 𝒪[K] := by
    rw [← residue_eq_zero_iff]
    simp [f, hqdef, pow_card_residueField]
  have hder : IsUnit (Ideal.Quotient.mk (maximalIdeal 𝒪[K]) (f.derivative.eval a₀)) := by
    have : f.derivative.eval a₀ = -1 := by
      simp [f, derivative_X_pow, hq0]
    rw [this, map_neg, map_one]
    exact isUnit_one.neg
  obtain ⟨x, hx, hxa⟩ := HenselianRing.is_henselian f hmonic a₀ hroot hder
  refine ⟨x, ?_, ?_⟩
  · rw [mem_teichmullerSubring]
    simpa [f, IsRoot, sub_eq_zero] using hx
  · rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
    exact hxa

noncomputable def teichmullerEquiv : teichmullerSubring K p ≃+* 𝓀[K] :=
  RingEquiv.ofBijective ((residue 𝒪[K]).comp (teichmullerSubring K p).subtype)
    ⟨(injective_iff_map_eq_zero _).mpr fun x hx =>
        Subtype.ext (eq_zero_of_mem_teichmullerSubring K p x.2 hx),
      fun a => by
        obtain ⟨x, hx, h⟩ := exists_mem_teichmullerSubring_residue_eq K p a
        exact ⟨⟨x, hx⟩, h⟩⟩

noncomputable def teichmullerHom : 𝓀[K] →+* 𝒪[K] :=
  (teichmullerSubring K p).subtype.comp (teichmullerEquiv K p).symm.toRingHom

theorem residue_teichmullerHom (a : 𝓀[K]) : residue 𝒪[K] (teichmullerHom K p a) = a :=
  (teichmullerEquiv K p).apply_symm_apply a

end EqualChar

end Sec_ExamplesTeichmuller


/-! ### ExamplesLaurent -/
section Sec_ExamplesLaurent

open scoped _root_.LaurentSeries


open ValuativeRel Polynomial IsLocalRing Topology Filter WithZero HahnSeries

theorem continuous_of_vle_iff {R S : Type*} [Field R] [ValuativeRel R] [TopologicalSpace R]
    [IsValuativeTopology R] [Field S] [ValuativeRel S] [TopologicalSpace S]
    [IsValuativeTopology S] (f : R →+* S) (hf : ∀ x y, f x ≤ᵥ f y ↔ x ≤ᵥ y)
    (hs : Function.Surjective f) : Continuous f := by
  refine continuous_of_continuousAt_zero f ?_
  rw [ContinuousAt, map_zero]
  refine ((IsValuativeTopology.hasBasis_nhds_zero' R).tendsto_iff
    (IsValuativeTopology.hasBasis_nhds_zero' S)).mpr fun γ hγ => ?_
  obtain ⟨z, rfl⟩ := ValuativeRel.valuation_surjective γ
  obtain ⟨t, rfl⟩ := hs z
  refine ⟨valuation R t, fun h => hγ ?_, fun x hx => ?_⟩
  · rw [map_eq_zero] at h
    simp [h]
  · exact ((valuation S).vlt_iff_lt.symm.trans
      ((not_congr (hf t x)).trans (valuation R).vlt_iff_lt)).mpr hx

namespace EqualChar

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

noncomputable def uniformizer : 𝒪[K] :=
  (IsDiscreteValuationRing.exists_irreducible 𝒪[K]).choose

theorem irreducible_uniformizer : Irreducible (uniformizer K) :=
  (IsDiscreteValuationRing.exists_irreducible 𝒪[K]).choose_spec

theorem uniformizer_ne_zero : (uniformizer K : K) ≠ 0 := fun h =>
  (irreducible_uniformizer K).ne_zero (Subtype.ext h)

theorem valuation_uniformizer_pos : 0 < valuation K (uniformizer K : K) := by
  rw [zero_lt_iff, ne_eq, map_eq_zero]
  exact uniformizer_ne_zero K

theorem valuation_uniformizer_lt_one : valuation K (uniformizer K : K) < 1 :=
  Valuation.Integer.not_isUnit_iff_valuation_lt_one.mp (irreducible_uniformizer K).not_isUnit

def ballIdeal (γ : (ValueGroupWithZero K)ˣ) : Ideal 𝒪[K] where
  carrier := {x | valuation K (x : K) < γ}
  add_mem' {a b} ha hb := by
    change valuation K ((a : K) + (b : K)) < γ
    exact lt_of_le_of_lt ((valuation K).map_add _ _) (max_lt ha hb)
  zero_mem' := by simp
  smul_mem' c x hx := by
    change valuation K ((c : K) * (x : K)) < γ
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' ((Valuation.mem_integer_iff _ _).mp c.2)) hx

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
theorem mem_ballIdeal {γ : (ValueGroupWithZero K)ˣ} {x : 𝒪[K]} :
    x ∈ ballIdeal K γ ↔ valuation K (x : K) < γ := Iff.rfl

theorem hasBasis_nhds_zero_integer :
    (𝓝 (0 : 𝒪[K])).HasBasis (fun _ => True)
      fun γ : (ValueGroupWithZero K)ˣ => ((ballIdeal K γ : Ideal 𝒪[K]) : Set 𝒪[K]) := by
  rw [nhds_subtype_eq_comap, ZeroMemClass.coe_zero]
  refine ((IsValuativeTopology.hasBasis_nhds_zero K).comap Subtype.val).congr
    (fun _ => Iff.rfl) fun γ _ => ?_
  ext x
  simp [mem_ballIdeal]

instance : IsLinearTopology 𝒪[K] 𝒪[K] :=
  IsLinearTopology.mk_of_hasBasis' 𝒪[K] (hasBasis_nhds_zero_integer K)
    fun I r _ hx => I.mul_mem_left r hx

theorem isTopologicallyNilpotent_uniformizer : IsTopologicallyNilpotent (uniformizer K) := by
  refine (hasBasis_nhds_zero_integer K).tendsto_right_iff.mpr fun γ _ => ?_
  obtain ⟨N, hN⟩ := exists_pow_lt₀ (valuation_uniformizer_lt_one K) γ
  filter_upwards [eventually_ge_atTop N] with n hn
  rw [SetLike.mem_coe, mem_ballIdeal, Subring.coe_pow, map_pow]
  exact lt_of_le_of_lt (pow_le_pow_of_le_one zero_le
    (valuation_uniformizer_lt_one K).le hn) hN

variable (p : ℕ) [Fact p.Prime] [CharP K p]

theorem valuation_teichmullerHom {a : 𝓀[K]} (ha : a ≠ 0) :
    valuation K (teichmullerHom K p a : K) = 1 :=
  (Valuation.integer.integers (valuation K)).isUnit_iff_valuation_eq_one.mp
    ((teichmullerHom K p).isUnit_map ha.isUnit)

section Uniform

local instance uniformSpaceK : UniformSpace K := IsTopologicalAddGroup.rightUniformSpace K

local instance isUniformAddGroupK : IsUniformAddGroup K := isUniformAddGroup_of_addCommGroup

local instance uniformSpaceResidue : UniformSpace 𝓀[K] := ⊥

local instance discreteUniformityResidue : DiscreteUniformity 𝓀[K] := ⟨rfl⟩

noncomputable def powerSeriesHom : PowerSeries 𝓀[K] →+* 𝒪[K] :=
  PowerSeries.eval₂Hom (φ := teichmullerHom K p) continuous_of_discreteTopology
    (isTopologicallyNilpotent_uniformizer K)

theorem powerSeriesHom_apply (F : PowerSeries 𝓀[K]) :
    powerSeriesHom K p F = PowerSeries.eval₂ (teichmullerHom K p) (uniformizer K) F := by
  rw [powerSeriesHom, PowerSeries.coe_eval₂Hom]

theorem powerSeriesHom_C (a : 𝓀[K]) :
    powerSeriesHom K p (PowerSeries.C a) = teichmullerHom K p a := by
  rw [powerSeriesHom_apply, PowerSeries.eval₂_C]

theorem powerSeriesHom_X : powerSeriesHom K p PowerSeries.X = uniformizer K := by
  rw [powerSeriesHom_apply, PowerSeries.eval₂_X]

theorem hasSum_powerSeriesHom (F : PowerSeries 𝓀[K]) :
    HasSum (fun d => teichmullerHom K p (PowerSeries.coeff d F) * uniformizer K ^ d)
      (powerSeriesHom K p F) := by
  rw [powerSeriesHom_apply]
  exact PowerSeries.hasSum_eval₂ continuous_of_discreteTopology
    (isTopologicallyNilpotent_uniformizer K) F

theorem powerSeriesHom_surjective : Function.Surjective (powerSeriesHom K p) := by
  intro y
  have hstep : ∀ z : 𝒪[K], ∃ w : 𝒪[K],
      z = teichmullerHom K p (residue 𝒪[K] z) + uniformizer K * w := by
    intro z
    have hm : z - teichmullerHom K p (residue 𝒪[K] z) ∈ maximalIdeal 𝒪[K] := by
      rw [← residue_eq_zero_iff, map_sub, residue_teichmullerHom, sub_self]
    rw [(irreducible_uniformizer K).maximalIdeal_eq, Ideal.mem_span_singleton'] at hm
    obtain ⟨w, hw⟩ := hm
    exact ⟨w, by rw [mul_comm, hw]; ring⟩
  choose next hnext using hstep
  obtain ⟨rem, hrem0, hremS⟩ : ∃ rem : ℕ → 𝒪[K], rem 0 = y ∧ ∀ n, rem (n + 1) = next (rem n) :=
    ⟨fun n => next^[n] y, rfl, fun n => Function.iterate_succ_apply' next n y⟩
  refine ⟨PowerSeries.mk fun n => residue 𝒪[K] (rem n), ?_⟩
  have hpartial : ∀ n, y = (∑ d ∈ Finset.range n,
      teichmullerHom K p (residue 𝒪[K] (rem d)) * uniformizer K ^ d) +
        rem n * uniformizer K ^ n := by
    intro n
    induction n with
    | zero => simp [hrem0]
    | succ n ih =>
      rw [Finset.sum_range_succ, hremS]
      linear_combination ih + uniformizer K ^ n * hnext (rem n)
  have hT1 := (hasSum_powerSeriesHom K p
    (PowerSeries.mk fun n => residue 𝒪[K] (rem n))).tendsto_sum_nat
  simp only [PowerSeries.coeff_mk] at hT1
  have h0 : Tendsto (fun n => rem n * uniformizer K ^ n) atTop (𝓝 0) :=
    IsLinearTopology.tendsto_mul_zero_of_right rem (fun n => uniformizer K ^ n)
      (isTopologicallyNilpotent_uniformizer K)
  have hT2 : Tendsto (fun n => ∑ d ∈ Finset.range n,
      teichmullerHom K p (residue 𝒪[K] (rem d)) * uniformizer K ^ d) atTop (𝓝 y) := by
    have he : (fun n => ∑ d ∈ Finset.range n,
        teichmullerHom K p (residue 𝒪[K] (rem d)) * uniformizer K ^ d) =
          fun n => y - rem n * uniformizer K ^ n :=
      funext fun n => by rw [eq_sub_iff_add_eq, ← hpartial n]
    rw [he]
    simpa using (tendsto_const_nhds (x := y)).sub h0
  exact tendsto_nhds_unique hT1 hT2

end Uniform

theorem valuation_powerSeriesHom_of_constantCoeff_ne_zero {F : PowerSeries 𝓀[K]}
    (hF : PowerSeries.constantCoeff F ≠ 0) : valuation K (powerSeriesHom K p F : K) = 1 := by
  set G : PowerSeries 𝓀[K] := PowerSeries.mk fun n => PowerSeries.coeff (n + 1) F
  have hFG : F = PowerSeries.X * G + PowerSeries.C (PowerSeries.constantCoeff F) :=
    PowerSeries.eq_X_mul_shift_add_const F
  have h1 : valuation K (teichmullerHom K p (PowerSeries.constantCoeff F) : K) = 1 :=
    valuation_teichmullerHom K p hF
  have h2 : valuation K ((uniformizer K : K) * (powerSeriesHom K p G : K)) < 1 := by
    rw [map_mul]
    calc valuation K (uniformizer K : K) * valuation K (powerSeriesHom K p G : K)
        ≤ valuation K (uniformizer K : K) * 1 := by
          gcongr
          exact (Valuation.mem_integer_iff _ _).mp (powerSeriesHom K p G).2
      _ < 1 := by simpa using valuation_uniformizer_lt_one K
  rw [hFG, map_add, map_mul, powerSeriesHom_X, powerSeriesHom_C, Subring.coe_add,
    Subring.coe_mul, Valuation.map_add_eq_of_lt_right _ (h1 ▸ h2), h1]

noncomputable def laurentHom : 𝓀[K]⸨X⸩ →+* K :=
  IsLocalization.lift (M := Submonoid.powers (PowerSeries.X : PowerSeries 𝓀[K]))
    (g := (Subring.subtype 𝒪[K]).comp (powerSeriesHom K p)) (by
      rintro ⟨_, n, rfl⟩
      simp only [RingHom.comp_apply, map_pow, powerSeriesHom_X, Subring.subtype_apply]
      exact (pow_ne_zero n (uniformizer_ne_zero K)).isUnit)

theorem laurentHom_coe (F : PowerSeries 𝓀[K]) :
    laurentHom K p (F : 𝓀[K]⸨X⸩) = powerSeriesHom K p F :=
  IsLocalization.lift_eq (M := Submonoid.powers (PowerSeries.X : PowerSeries 𝓀[K])) _ F

theorem laurentHom_single (n : ℤ) :
    laurentHom K p (single n 1) = (uniformizer K : K) ^ n := by
  rw [RatFunc.single_zpow, map_zpow₀, ← HahnSeries.ofPowerSeries_X, laurentHom_coe,
    powerSeriesHom_X]

theorem valuation_laurentHom {x : 𝓀[K]⸨X⸩} (hx : x ≠ 0) :
    valuation K (laurentHom K p x) = valuation K (uniformizer K : K) ^ x.order := by
  conv_lhs => rw [← x.single_order_mul_powerSeriesPart]
  rw [map_mul, map_mul, laurentHom_single, map_zpow₀, laurentHom_coe,
    valuation_powerSeriesHom_of_constantCoeff_ne_zero K p, mul_one]
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, LaurentSeries.powerSeriesPart_coeff,
    Nat.cast_zero, add_zero]
  exact fun h => hx (HahnSeries.coeff_order_eq_zero.mp h)

omit [Fact p.Prime] [CharP K p] in

theorem valued_le_one_iff {x : 𝓀[K]⸨X⸩} (hx : x ≠ 0) : Valued.v x ≤ 1 ↔ 0 ≤ x.order := by
  have h := LaurentSeries.valuation_le_iff_coeff_lt_eq_zero (K := 𝓀[K]) (D := 0) (f := x)
  simp only [neg_zero, exp_zero] at h
  rw [h]
  constructor
  · intro H
    by_contra hneg
    exact hx (HahnSeries.coeff_order_eq_zero.mp (H _ (not_le.mp hneg)))
  · intro H n hn
    exact HahnSeries.coeff_eq_zero_of_lt_order (lt_of_lt_of_le hn H)

theorem isEquiv_comap_laurentHom :
    ((valuation K).comap (laurentHom K p)).IsEquiv (Valued.v : Valuation 𝓀[K]⸨X⸩ ℤᵐ⁰) :=
  Valuation.isEquiv_of_val_le_one fun x => by
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    rw [Valuation.comap_apply, valuation_laurentHom K p hx,
      zpow_le_one_iff_right_of_lt_one₀ (valuation_uniformizer_pos K)
        (valuation_uniformizer_lt_one K), valued_le_one_iff K hx]

theorem laurentHom_vle_iff (x y : 𝓀[K]⸨X⸩) :
    laurentHom K p x ≤ᵥ laurentHom K p y ↔ x ≤ᵥ y := by
  rw [Valuation.Compatible.vle_iff_le (v := valuation K),
    Valuation.Compatible.vle_iff_le (v := (Valued.v : Valuation 𝓀[K]⸨X⸩ ℤᵐ⁰))]
  simpa using (isEquiv_comap_laurentHom K p).le_iff_le (x := x) (y := y)

theorem laurentHom_surjective : Function.Surjective (laurentHom K p) := by
  intro x
  rcases eq_or_ne x 0 with rfl | hx
  · exact ⟨0, map_zero _⟩
  have hvx : 0 < valuation K x := by
    rw [zero_lt_iff, ne_eq, map_eq_zero]
    exact hx
  obtain ⟨m, hm⟩ := exists_pow_lt₀ (valuation_uniformizer_lt_one K)
    (Units.mk0 (valuation K x)⁻¹ (inv_ne_zero hvx.ne'))
  have hy : valuation K ((uniformizer K : K) ^ m * x) ≤ 1 := by
    rw [map_mul, map_pow]
    have h := mul_lt_mul_of_pos_right hm hvx
    rw [Units.val_mk0, inv_mul_cancel₀ hvx.ne'] at h
    exact h.le
  obtain ⟨F, hF⟩ := powerSeriesHom_surjective K p
    ⟨(uniformizer K : K) ^ m * x, (Valuation.mem_integer_iff _ _).mpr hy⟩
  refine ⟨single (-(m : ℤ)) 1 * (F : 𝓀[K]⸨X⸩), ?_⟩
  rw [map_mul, laurentHom_single, laurentHom_coe, hF, zpow_neg, zpow_natCast, ← mul_assoc,
    inv_mul_cancel₀ (pow_ne_zero _ (uniformizer_ne_zero K)), one_mul]

noncomputable def laurentEquiv : 𝓀[K]⸨X⸩ ≃+* K :=
  RingEquiv.ofBijective (laurentHom K p) ⟨(laurentHom K p).injective, laurentHom_surjective K p⟩

theorem laurentEquiv_apply (x : 𝓀[K]⸨X⸩) : laurentEquiv K p x = laurentHom K p x := rfl

end EqualChar

theorem exists_ringEquiv_laurentSeries_of_charP (K : Type*) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] (p : ℕ) [Fact p.Prime] [CharP K p] :
    ∃ e : K ≃+* 𝓀[K]⸨X⸩, (∀ x y, e x ≤ᵥ e y ↔ x ≤ᵥ y) ∧ Continuous e ∧ Continuous e.symm := by
  set f := EqualChar.laurentEquiv K p
  have hf (x y : 𝓀[K]⸨X⸩) : f x ≤ᵥ f y ↔ x ≤ᵥ y := EqualChar.laurentHom_vle_iff K p x y
  have hfs (x y : K) : f.symm x ≤ᵥ f.symm y ↔ x ≤ᵥ y := by
    rw [← hf, f.apply_symm_apply, f.apply_symm_apply]
  refine ⟨f.symm, hfs, ?_, ?_⟩
  · exact continuous_of_vle_iff f.symm.toRingHom hfs f.symm.surjective
  · exact continuous_of_vle_iff f.toRingHom hf f.surjective

end Sec_ExamplesLaurent


/-! ### ExistsUnitFiltrationUnitsLeAndRangePowLe -/
section Sec_ExistsUnitFiltrationUnitsLeAndRangePowLe

open ValuativeRel IsLocalRing Topology Filter
open scoped WithZero

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

noncomputable def unitFiltrationUnits (n : ℕ) : Subgroup Kˣ :=
  (unitFiltration K n).map (unitsIncl K)

variable {K}

theorem unitFiltrationUnits_antitone : Antitone (unitFiltrationUnits K) :=
  fun _ _ hmn ↦ Subgroup.map_mono (unitFiltration_antitone K hmn)

theorem mem_unitFiltrationUnits_zero_iff {x : Kˣ} :
    x ∈ unitFiltrationUnits K 0 ↔ valuation K (x : K) = 1 := by
  rw [unitFiltrationUnits, unitFiltration_zero, ← MonoidHom.range_eq_map, mem_range_unitsIncl_iff,
    ← map_one (normalizedValuation K), normalizedValuation_eq_iff, map_one]

theorem mem_unitFiltrationUnits_iff {n : ℕ} (hn : 1 ≤ n) {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ)
    {x : Kˣ} :
    x ∈ unitFiltrationUnits K n ↔ valuation K ((x : K) - 1) ≤ valuation K (ϖ : K) ^ n := by
  have hset := hϖ.maximalIdeal_pow_eq_setOfPred_le_v_coe_pow (v := valuation K) n
  constructor
  · rintro ⟨u, hu, rfl⟩
    have : ((u : 𝒪[K]) - 1 : 𝒪[K]) ∈ ((𝓂[K] ^ n : Ideal 𝒪[K]) : Set 𝒪[K]) := hu
    rw [hset] at this
    simpa using this
  · intro h
    have hϖ1 : valuation K (ϖ : K) < 1 :=
      valuation_lt_one_of_mem_maximalIdeal (uniformizer_mem_maximalIdeal hϖ)
    have hlt : valuation K ((x : K) - 1) < 1 :=
      h.trans_lt (pow_lt_one₀ zero_le hϖ1 (by omega))
    have hx1 : valuation K (x : K) = 1 := by
      have := (valuation K).map_one_add_of_lt hlt
      simpa using this
    obtain ⟨u, rfl⟩ := mem_range_unitsIncl_iff.mpr (by
      rw [← map_one (normalizedValuation K), normalizedValuation_eq_iff, map_one]; exact hx1)
    refine ⟨u, ?_, rfl⟩
    show ((u : 𝒪[K]) - 1 : 𝒪[K]) ∈ ((𝓂[K] ^ n : Ideal 𝒪[K]) : Set 𝒪[K])
    rw [hset]
    simpa using h

theorem isOpen_setOf_valuation_sub_le {a : K} {γ : ValueGroupWithZero K} (hγ : γ ≠ 0) :
    IsOpen {y : K | valuation K (y - a) ≤ γ} := by
  rw [isOpen_iff_mem_nhds]
  intro y hy
  rw [IsValuativeTopology.mem_nhds_iff']
  refine ⟨Units.mk0 γ hγ, fun z hz ↦ ?_⟩
  have : z - a = (z - y) + (y - a) := by ring
  simp only [Set.mem_ofPred_eq, Units.val_mk0] at hz hy ⊢
  rw [this]
  exact (valuation K).map_add_le hz.le hy

theorem isOpen_setOf_valuation_lt {γ : ValueGroupWithZero K} :
    IsOpen {y : K | valuation K y < γ} := by
  rw [isOpen_iff_mem_nhds]
  intro y hy
  rw [IsValuativeTopology.mem_nhds_iff']
  have hγ : γ ≠ 0 := ne_bot_of_gt hy
  refine ⟨Units.mk0 γ hγ, fun z hz ↦ ?_⟩
  have : z = (z - y) + y := by ring
  simp only [Set.mem_ofPred_eq, Units.val_mk0] at hz hy ⊢
  rw [this]
  exact (valuation K).map_add_lt hz hy

theorem isOpen_setOf_valuation_eq_one : IsOpen {y : K | valuation K y = 1} := by
  rw [isOpen_iff_mem_nhds]
  intro y hy
  rw [IsValuativeTopology.mem_nhds_iff']
  refine ⟨1, fun z hz ↦ ?_⟩
  simp only [Set.mem_ofPred_eq, Units.val_one] at hz hy ⊢
  have : z = y + (z - y) := by ring
  rw [this, (valuation K).map_add_eq_of_lt_left (by rw [hy]; exact hz), hy]

theorem val_image_unitFiltrationUnits_zero :
    ((↑) : Kˣ → K) '' (unitFiltrationUnits K 0 : Set Kˣ) = {y : K | valuation K y = 1} := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact mem_unitFiltrationUnits_zero_iff.mp hx
  · intro hy
    have hy0 : y ≠ 0 := by rintro rfl; simp at hy
    exact ⟨Units.mk0 y hy0, mem_unitFiltrationUnits_zero_iff.mpr hy, rfl⟩

theorem val_image_unitFiltrationUnits {n : ℕ} (hn : 1 ≤ n) {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) :
    ((↑) : Kˣ → K) '' (unitFiltrationUnits K n : Set Kˣ) =
      {y : K | valuation K (y - 1) ≤ valuation K (ϖ : K) ^ n} := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (mem_unitFiltrationUnits_iff hn hϖ).mp hx
  · intro hy
    have hϖ1 : valuation K (ϖ : K) < 1 :=
      valuation_lt_one_of_mem_maximalIdeal (uniformizer_mem_maximalIdeal hϖ)
    have hy0 : y ≠ 0 := by
      rintro rfl
      have : valuation K ((0 : K) - 1) ≤ valuation K (ϖ : K) ^ n := hy
      simp only [zero_sub, Valuation.map_neg, map_one] at this
      exact (pow_lt_one₀ zero_le hϖ1 (by omega)).not_ge this
    exact ⟨Units.mk0 y hy0, (mem_unitFiltrationUnits_iff hn hϖ).mpr hy, rfl⟩

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
theorem valuation_uniformizer_ne_zero {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) :
    valuation K (ϖ : K) ≠ 0 := by
  rw [Ne, Valuation.zero_iff]
  exact_mod_cast hϖ.ne_zero

theorem isOpen_unitFiltrationUnits (n : ℕ) : IsOpen (unitFiltrationUnits K n : Set Kˣ) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : (unitFiltrationUnits K 0 : Set Kˣ) = (↑) ⁻¹' {y : K | valuation K y = 1} := by
      ext x; exact mem_unitFiltrationUnits_zero_iff
    rw [this]
    exact isOpen_setOf_valuation_eq_one.preimage Units.continuous_val
  · have : (unitFiltrationUnits K n : Set Kˣ) =
        (↑) ⁻¹' {y : K | valuation K (y - 1) ≤ valuation K (ϖ : K) ^ n} := by
      ext x; exact mem_unitFiltrationUnits_iff hn hϖ
    rw [this]
    exact (isOpen_setOf_valuation_sub_le
      (pow_ne_zero _ (valuation_uniformizer_ne_zero hϖ))).preimage Units.continuous_val

theorem isCompact_unitFiltrationUnits (n : ℕ) : IsCompact (unitFiltrationUnits K n : Set Kˣ) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  rw [Units.isEmbedding_val₀.isCompact_iff]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [val_image_unitFiltrationUnits_zero]
    have : {y : K | valuation K y = 1} =
        {y : K | valuation K y ≤ 1} \ {y : K | valuation K y < 1} := by
      ext y
      simp only [Set.mem_ofPred_eq, Set.mem_sdiff, not_lt]
      constructor
      · intro h; exact ⟨h.le, h.ge⟩
      · intro h; exact le_antisymm h.1 h.2
    rw [this]
    exact (IsNonarchimedeanLocalField.isCompact_closedBall K 1).diff isOpen_setOf_valuation_lt
  · rw [val_image_unitFiltrationUnits hn hϖ]
    have : {y : K | valuation K (y - 1) ≤ valuation K (ϖ : K) ^ n} =
        (Homeomorph.subRight (1 : K)) ⁻¹' {y : K | valuation K y ≤ valuation K (ϖ : K) ^ n} := by
      ext y; rfl
    rw [this, Homeomorph.isCompact_preimage]
    exact IsNonarchimedeanLocalField.isCompact_closedBall K _

theorem exists_pow_lt {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) {γ : ValueGroupWithZero K} (hγ : γ ≠ 0) :
    ∃ n, 1 ≤ n ∧ valuation K (ϖ : K) ^ n < γ := by
  obtain ⟨z, rfl⟩ := ValuativeRel.valuation_surjective γ
  have hz : z ≠ 0 := by rintro rfl; simp at hγ
  refine ⟨max 1 (ord z + 1).toNat, le_max_left _ _, ?_⟩
  rw [← map_pow, ← normalizedValuation_lt_iff, map_pow, normalizedValuation_uniformizer hϖ,
    normalizedValuation_eq_exp_ord hz, ← WithZero.exp_nsmul, WithZero.exp_lt_exp]
  simp only [nsmul_eq_mul, mul_neg, mul_one, neg_lt_neg_iff]
  have := le_max_right 1 (ord z + 1).toNat
  omega

theorem hasBasis_nhds_one_unitFiltrationUnits :
    (𝓝 (1 : Kˣ)).HasBasis (fun _ ↦ True) (fun n ↦ (unitFiltrationUnits K n : Set Kˣ)) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  rw [Filter.hasBasis_iff]
  intro t
  constructor
  · intro ht
    rw [Units.isEmbedding_val₀.isInducing.nhds_eq_comap, Filter.mem_comap] at ht
    obtain ⟨t', ht', hsub⟩ := ht
    rw [Units.val_one, IsValuativeTopology.mem_nhds_iff'] at ht'
    obtain ⟨γ, hγ⟩ := ht'
    obtain ⟨n, hn, hlt⟩ := exists_pow_lt hϖ γ.ne_zero
    refine ⟨n, trivial, fun x hx ↦ hsub (hγ ?_)⟩
    exact ((mem_unitFiltrationUnits_iff hn hϖ).mp hx).trans_lt hlt
  · rintro ⟨n, -, hn⟩
    exact Filter.mem_of_superset
      ((isOpen_unitFiltrationUnits n).mem_nhds (Subgroup.one_mem _)) hn

theorem exists_unitFiltrationUnits_le {H : Subgroup Kˣ} (hH : IsOpen (H : Set Kˣ)) :
    ∃ n, unitFiltrationUnits K n ≤ H := by
  obtain ⟨n, -, hn⟩ :=
    hasBasis_nhds_one_unitFiltrationUnits.mem_iff.mp (hH.mem_nhds (Subgroup.one_mem H))
  exact ⟨n, hn⟩

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
theorem exists_range_pow_le {H : Subgroup Kˣ} [H.FiniteIndex] :
    ∃ m, m ≠ 0 ∧ (powMonoidHom m : Kˣ →* Kˣ).range ≤ H := by
  refine ⟨H.index, Subgroup.FiniteIndex.index_ne_zero, ?_⟩
  rintro _ ⟨x, rfl⟩
  exact H.pow_index_mem x

theorem exists_unitFiltrationUnits_le_and_range_pow_le {H : Subgroup Kˣ} [H.FiniteIndex]
    (hH : IsOpen (H : Set Kˣ)) :
    (∃ n, unitFiltrationUnits K n ≤ H) ∧ ∃ m, m ≠ 0 ∧ (powMonoidHom m : Kˣ →* Kˣ).range ≤ H :=
  ⟨exists_unitFiltrationUnits_le hH, exists_range_pow_le⟩

theorem isOpen_range_pow {m : ℕ} (hm : (m : K) ≠ 0) :
    IsOpen ((powMonoidHom m : Kˣ →* Kˣ).range : Set Kˣ) := by
  obtain ⟨N, hN⟩ := exists_unitFiltration_le_range_pow hm
  refine Subgroup.isOpen_mono ?_ (isOpen_unitFiltrationUnits N)
  rintro _ ⟨u, hu, rfl⟩
  obtain ⟨x, rfl⟩ := hN hu
  exact ⟨unitsIncl K x, by simp⟩

end Sec_ExistsUnitFiltrationUnitsLeAndRangePowLe


/-! ### ExistsUnitFiltrationUnitsLeRangeNormUnits -/
section Sec_ExistsUnitFiltrationUnitsLeRangeNormUnits

open ValuativeRel IsLocalRing Topology Filter Polynomial
open scoped WithZero nonZeroDivisors

section Fields

variable (K L : Type*) [Field K] [Field L] [Algebra K L]

def normUnits : Lˣ →* Kˣ :=
  Units.map (Algebra.norm K : L →* K)

variable {K L} in
@[simp]
theorem coe_normUnits (x : Lˣ) : ((normUnits K L x : Kˣ) : K) = Algebra.norm K (x : L) :=
  rfl

theorem algebraMap_norm_eq_prod [FiniteDimensional K L] [IsGalois K L] (x : L) :
    algebraMap K L (Algebra.norm K x) = ∏ σ : L ≃ₐ[K] L, σ x :=
  Algebra.norm_eq_prod_automorphisms K x

end Fields

section Ord

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

theorem ord_zpow {x : K} (hx : x ≠ 0) (k : ℤ) : ord (x ^ k) = k * ord x := by
  have h1 := normalizedValuation_eq_exp_ord (zpow_ne_zero k hx)
  rw [map_zpow₀, normalizedValuation_eq_exp_ord hx, ← WithZero.exp_zsmul, WithZero.exp_inj,
    smul_eq_mul] at h1
  linear_combination h1

theorem ord_pow {x : K} (hx : x ≠ 0) (k : ℕ) : ord (x ^ k) = k * ord x := by
  simpa using ord_zpow hx k

@[simp]
theorem ord_zero : ord (0 : K) = 0 := by
  simp [ord]

theorem ord_unitsOfIntProd {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) (n : Multiplicative ℤ)
    (u : 𝒪[K]ˣ) : ord ((unitsOfIntProd hϖ (n, u) : Kˣ) : K) = n.toAdd := by
  simp [ord, normalizedValuation_unitsOfIntProd]

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in

theorem unitsOfIntProd_eq {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) (n : Multiplicative ℤ)
    (u : 𝒪[K]ˣ) : unitsOfIntProd hϖ (n, u) = uniformizerUnit hϖ ^ n.toAdd * unitsIncl K u := by
  simp [unitsOfIntProd, zpowersHom_apply]

theorem ord_eq_zero_iff_mem {x : Kˣ} : ord (x : K) = 0 ↔ x ∈ unitFiltrationUnits K 0 := by
  rw [mem_unitFiltrationUnits_zero_iff, ← map_one (valuation K), ← normalizedValuation_eq_iff,
    normalizedValuation_eq_exp_ord x.ne_zero, map_one, ← WithZero.exp_zero, WithZero.exp_inj,
    neg_eq_zero]

theorem setOf_ord_eq {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) (m : ℤ) :
    {y : Kˣ | ord (y : K) = m} =
      (Homeomorph.mulLeft (uniformizerUnit hϖ ^ (-m))) ⁻¹' (unitFiltrationUnits K 0 : Set Kˣ) := by
  ext y
  simp only [Set.mem_ofPred_eq, Set.mem_preimage, Homeomorph.coe_mulLeft, SetLike.mem_coe,
    ← ord_eq_zero_iff_mem, Units.val_mul, Units.val_zpow_eq_zpow_val, coe_uniformizerUnit]
  have hϖ0 : (ϖ : K) ≠ 0 := by exact_mod_cast hϖ.ne_zero
  rw [ord_mul (zpow_ne_zero _ hϖ0) y.ne_zero, ord_zpow hϖ0, ord_uniformizer hϖ]
  omega

theorem isOpen_setOf_ord_eq (m : ℤ) : IsOpen {y : Kˣ | ord (y : K) = m} := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  rw [setOf_ord_eq hϖ]
  exact (isOpen_unitFiltrationUnits 0).preimage (Homeomorph.continuous _)

theorem isCompact_setOf_ord_eq (m : ℤ) : IsCompact {y : Kˣ | ord (y : K) = m} := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  rw [setOf_ord_eq hϖ, Homeomorph.isCompact_preimage]
  exact isCompact_unitFiltrationUnits 0

variable (K) in

instance locallyCompactSpace_units : LocallyCompactSpace Kˣ :=
  (isCompact_unitFiltrationUnits 0).locallyCompactSpace_of_mem_nhds_of_group
    ((isOpen_unitFiltrationUnits 0).mem_nhds (Subgroup.one_mem _))

end Ord

section Local

variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

theorem isLocalization_integer :
    IsLocalization (Algebra.algebraMapSubmonoid 𝒪[L] 𝒪[K]⁰) L :=
  IsIntegralClosure.isLocalization 𝒪[K] K L 𝒪[L]

variable {K L}

theorem coe_norm_integer (x : 𝒪[L]) :
    ((Algebra.norm 𝒪[K] x : 𝒪[K]) : K) = Algebra.norm K (x : L) := by
  have := isLocalization_integer K L
  exact (Algebra.norm_localization (Rₘ := K) (Sₘ := L) 𝒪[K] 𝒪[K]⁰ x).symm

theorem coe_trace_integer (x : 𝒪[L]) :
    ((Algebra.trace 𝒪[K] 𝒪[L] x : 𝒪[K]) : K) = Algebra.trace K L (x : L) := by
  have := isLocalization_integer K L
  exact (Algebra.trace_localization (Rₘ := K) (Sₘ := L) 𝒪[K] 𝒪[K]⁰ x).symm

theorem norm_mem_integer {x : L} (hx : x ∈ 𝒪[L]) : Algebra.norm K x ∈ 𝒪[K] := by
  have h := coe_norm_integer (K := K) (⟨x, hx⟩ : 𝒪[L])
  rw [← h]
  exact (Algebra.norm 𝒪[K] (⟨x, hx⟩ : 𝒪[L])).2

variable (K L) in

def normIntegerUnits : 𝒪[L]ˣ →* 𝒪[K]ˣ :=
  Units.map (Algebra.norm 𝒪[K] : 𝒪[L] →* 𝒪[K])

theorem coe_normIntegerUnits (u : 𝒪[L]ˣ) :
    (((normIntegerUnits K L u : 𝒪[K]ˣ) : 𝒪[K]) : K) = Algebra.norm K ((u : 𝒪[L]) : L) :=
  coe_norm_integer _

theorem normUnits_unitsIncl (u : 𝒪[L]ˣ) :
    normUnits K L (unitsIncl L u) = unitsIncl K (normIntegerUnits K L u) := by
  ext
  simp [coe_normIntegerUnits]

theorem map_normUnits_unitFiltrationUnits_zero_le :
    (unitFiltrationUnits L 0).map (normUnits K L) ≤ unitFiltrationUnits K 0 := by
  rintro _ ⟨_, ⟨u, -, rfl⟩, rfl⟩
  exact ⟨normIntegerUnits K L u, by simp, (normUnits_unitsIncl u).symm⟩

section Valuation

theorem ord_algebraMap_uniformizer {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) :
    ord (algebraMap K L (ϖ : K)) = ramificationIndex K L := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[L]
  have h := map_maximalIdeal K L
  rw [hϖ.maximalIdeal_eq, hπ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton,
    Ideal.span_singleton_pow, Ideal.span_singleton_eq_span_singleton] at h
  obtain ⟨u, hu⟩ := h.symm
  have h2 : algebraMap K L (ϖ : K) = (π : L) ^ ramificationIndex K L * ((u : 𝒪[L]) : L) := by
    rw [← coe_algebraMap_integer, ← hu]
    push_cast
    rfl
  have hπ0 : (π : L) ≠ 0 := by exact_mod_cast hπ.ne_zero
  rw [h2, ord_mul (pow_ne_zero _ hπ0) (by simp), ord_pow hπ0, ord_uniformizer hπ, ord_unit]
  simp

theorem ord_algebraMap (a : K) : ord (algebraMap K L a) = ramificationIndex K L * ord a := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  obtain ⟨⟨n, u⟩, hx⟩ := (unitsOfIntProd_bijective hϖ).2 (Units.mk0 a ha)
  have ha' : a = (ϖ : K) ^ n.toAdd * ((u : 𝒪[K]) : K) := by
    rw [← coe_unitsOfIntProd hϖ, hx, Units.val_mk0]
  have hϖ0 : (ϖ : K) ≠ 0 := by exact_mod_cast hϖ.ne_zero
  have hϖL : algebraMap K L (ϖ : K) ≠ 0 := by simpa using hϖ0
  have hu : algebraMap K L ((u : 𝒪[K]) : K) =
      (((Units.map (algebraMap 𝒪[K] 𝒪[L]).toMonoidHom u : 𝒪[L]ˣ) : 𝒪[L]) : L) := rfl
  rw [ha', map_mul, map_zpow₀, ord_mul (zpow_ne_zero _ hϖL) (by rw [hu]; simp), ord_zpow hϖL,
    ord_algebraMap_uniformizer hϖ, hu, ord_unit, ord_mul (zpow_ne_zero _ hϖ0) (by simp),
    ord_zpow hϖ0, ord_uniformizer hϖ, ord_unit]
  ring

theorem ord_norm_units {π : 𝒪[L]} (hπ : Irreducible π) (x : Lˣ) :
    ord (Algebra.norm K (x : L)) = ord (x : L) * ord (Algebra.norm K (π : L)) := by
  obtain ⟨⟨n, u⟩, rfl⟩ := (unitsOfIntProd_bijective hπ).2 x
  rw [ord_unitsOfIntProd, ← coe_normUnits, unitsOfIntProd_eq, map_mul, map_zpow,
    normUnits_unitsIncl, Units.val_mul, Units.val_zpow_eq_zpow_val, coe_unitsIncl,
    ord_mul (zpow_ne_zero _ (Units.ne_zero _)) (by simp), ord_zpow (Units.ne_zero _), ord_unit,
    coe_normUnits, coe_uniformizerUnit]
  ring

theorem ord_norm_uniformizer {π : 𝒪[L]} (hπ : Irreducible π) :
    ord (Algebra.norm K (π : L)) = residueDegree K L := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  have hϖ0 : (ϖ : K) ≠ 0 := by exact_mod_cast hϖ.ne_zero
  have hϖL : algebraMap K L (ϖ : K) ≠ 0 := by simpa using hϖ0
  have h := ord_norm_units (K := K) hπ (Units.mk0 _ hϖL)
  rw [Units.val_mk0, Algebra.norm_algebraMap, ord_pow hϖ0, ord_uniformizer hϖ,
    ord_algebraMap_uniformizer hϖ, ← ramificationIndex_mul_residueDegree K L] at h
  have he : (ramificationIndex K L : ℤ) ≠ 0 := by
    exact_mod_cast (ramificationIndex_pos K L).ne'
  push_cast at h
  exact (mul_left_cancel₀ he (by linear_combination h)).symm

theorem ord_norm (x : L) : ord (Algebra.norm K x) = residueDegree K L * ord x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[L]
  have := ord_norm_units (K := K) hπ (Units.mk0 x hx)
  rw [Units.val_mk0, ord_norm_uniformizer hπ] at this
  rw [this, mul_comm]

theorem ord_algebraMap_norm (x : L) :
    ord (algebraMap K L (Algebra.norm K x)) = Module.finrank K L * ord x := by
  rw [ord_algebraMap, ord_norm, ← ramificationIndex_mul_residueDegree K L]
  push_cast
  ring

end Valuation

section Topology

variable (K L)

theorem continuous_algebraNorm : Continuous (Algebra.norm K : L → K) := by
  classical
  have := isModuleTopology K L
  let b := Module.finBasis K L
  have hlin : Continuous (Algebra.leftMulMatrix b : L → Matrix _ _ K) :=
    IsModuleTopology.continuous_of_linearMap (Algebra.leftMulMatrix b).toLinearMap
  have h : (Algebra.norm K : L → K) = fun x ↦ (Algebra.leftMulMatrix b x).det := by
    funext x
    exact Algebra.norm_eq_matrix_det b x
  rw [h]
  exact hlin.matrix_det

theorem continuous_normUnits : Continuous (normUnits K L) := by
  rw [Units.continuous_iff]
  refine ⟨(continuous_algebraNorm K L).comp Units.continuous_val, ?_⟩
  have h : (fun x : Lˣ ↦ (((normUnits K L x)⁻¹ : Kˣ) : K)) =
      fun x ↦ Algebra.norm K ((x⁻¹ : Lˣ) : L) := by
    funext x
    rw [← map_inv, coe_normUnits]
  rw [h]
  exact (continuous_algebraNorm K L).comp Units.continuous_coe_inv

theorem isProperMap_normUnits : IsProperMap (normUnits K L) := by
  rw [isProperMap_iff_isCompact_preimage]
  refine ⟨continuous_normUnits K L, fun C hC ↦ ?_⟩
  obtain ⟨t, ht⟩ := hC.elim_finite_subcover (fun m : ℤ ↦ {y : Kˣ | ord (y : K) = m})
    isOpen_setOf_ord_eq (fun y _ ↦ Set.mem_iUnion.2 ⟨_, rfl⟩)
  refine IsCompact.of_isClosed_subset
    (t.isCompact_biUnion fun m _ ↦ isCompact_setOf_ord_eq (m / residueDegree K L))
    (hC.isClosed.preimage (continuous_normUnits K L)) ?_
  intro x hx
  obtain ⟨m, hm, hxm⟩ := Set.mem_iUnion₂.1 (ht hx)
  refine Set.mem_iUnion₂.2 ⟨m, hm, ?_⟩
  simp only [Set.mem_ofPred_eq, coe_normUnits, ord_norm] at hxm ⊢
  have hf : (residueDegree K L : ℤ) ≠ 0 := by exact_mod_cast (residueDegree_pos K L).ne'
  rw [← hxm, Int.mul_ediv_cancel_left _ hf]

theorem isClosed_range_normUnits : IsClosed ((normUnits K L).range : Set Kˣ) := by
  rw [MonoidHom.coe_range]
  exact (isProperMap_normUnits K L).isClosedMap.isClosed_range

end Topology

theorem exists_norm_one_add_smul_eq (z : 𝒪[L]) {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) (k : ℕ)
    (ε : 𝒪[K]ˣ) (hz : Algebra.trace 𝒪[K] 𝒪[L] z = ϖ ^ k * ε) (a : 𝒪[K])
    (ha : ϖ ^ (2 * k + 1) ∣ 1 - a) : ∃ r : 𝒪[K], Algebra.norm 𝒪[K] (1 + r • z) = a := by
  classical
  let b := Module.Free.chooseBasis 𝒪[K] 𝒪[L]
  set M := Algebra.leftMulMatrix b z with hM
  set Q := (Matrix.det (1 + (X : 𝒪[K][X]) • M.map C)).divX.divX with hQ
  let f : 𝒪[K][X] := C (1 - a) + C M.trace * X + Q * X ^ 2
  have hnorm : ∀ r : 𝒪[K], Algebra.norm 𝒪[K] (1 + r • z) = 1 + M.trace * r + Q.eval r * r ^ 2 := by
    intro r
    rw [Algebra.norm_eq_matrix_det b, map_add, map_one, map_smul, Matrix.det_one_add_smul]
  have htr : M.trace = ϖ ^ k * ε := by
    rw [← hz, Algebra.trace_eq_matrix_trace b]
  have hd : f.derivative.eval 0 = ϖ ^ k * ε := by
    simp [f, htr]
  have hf0 : f.eval 0 = 1 - a := by
    simp [f]
  obtain ⟨r, hr, -⟩ := exists_root_of_dvd hϖ f 0 k ε hd (by rwa [hf0])
  refine ⟨r, ?_⟩
  rw [hnorm]
  have h0 : f.eval r = 0 := hr
  simp only [f, eval_add, eval_C, eval_mul, eval_X, eval_pow] at h0
  linear_combination h0

section Separable

variable [Algebra.IsSeparable K L]

variable (K L) in

theorem exists_trace_integer_ne_zero : ∃ z : 𝒪[L], Algebra.trace 𝒪[K] 𝒪[L] z ≠ 0 := by
  obtain ⟨w, hw⟩ : ∃ w : L, Algebra.trace K L w ≠ 0 := by
    by_contra h
    refine one_ne_zero ((traceForm_nondegenerate K L).1 1 fun w ↦ ?_)
    simp only [not_exists, not_not] at h
    simpa using h w
  have hw0 : w ≠ 0 := by rintro rfl; simp at hw
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  have h1 : valuation L (algebraMap K L (ϖ : K)) < 1 :=
    (Valuation.HasExtension.val_map_lt_one_iff (valuation K) (valuation L) _).mpr
      (valuation_lt_one_of_mem_maximalIdeal (uniformizer_mem_maximalIdeal hϖ))
  have hv0 : valuation L w ≠ 0 := by simpa using hw0
  obtain ⟨m, hm⟩ := exists_pow_lt₀ h1 (Units.mk0 (valuation L w)⁻¹ (inv_ne_zero hv0))
  have hint : algebraMap K L (ϖ : K) ^ m * w ∈ 𝒪[L] := by
    rw [Valuation.mem_integer_iff, map_mul, map_pow]
    calc valuation L (algebraMap K L (ϖ : K)) ^ m * valuation L w
        ≤ (valuation L w)⁻¹ * valuation L w := by
          gcongr
          exact hm.le
      _ = 1 := inv_mul_cancel₀ hv0
  refine ⟨⟨_, hint⟩, fun h ↦ ?_⟩
  have h2 : Algebra.trace K L (algebraMap K L (ϖ : K) ^ m * w) = 0 := by
    have h3 := coe_trace_integer (K := K) (⟨_, hint⟩ : 𝒪[L])
    rw [h, ZeroMemClass.coe_zero] at h3
    exact h3.symm
  rw [← map_pow, ← Algebra.smul_def, map_smul, smul_eq_mul] at h2
  have hϖ0 : (ϖ : K) ≠ 0 := by exact_mod_cast hϖ.ne_zero
  exact mul_ne_zero (pow_ne_zero _ hϖ0) hw h2

variable (K L) in

theorem exists_unitFiltrationUnits_le_range_normUnits :
    ∃ n, unitFiltrationUnits K n ≤ (normUnits K L).range := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  obtain ⟨z, hz⟩ := exists_trace_integer_ne_zero K L
  obtain ⟨k, hk⟩ := IsDiscreteValuationRing.associated_pow_irreducible hz hϖ
  obtain ⟨ε, hε⟩ := hk.symm
  refine ⟨2 * k + 1, ?_⟩
  rintro _ ⟨a, ha, rfl⟩
  have hdvd : ϖ ^ (2 * k + 1) ∣ 1 - (a : 𝒪[K]) := by
    rw [← dvd_neg, neg_sub]
    exact (mem_maximalIdeal_pow_iff hϖ).mp ha
  obtain ⟨r, hr⟩ := exists_norm_one_add_smul_eq z hϖ k ε hε.symm a hdvd
  have hN := coe_norm_integer (K := K) (1 + r • z)
  rw [hr] at hN
  have hne : ((1 + r • z : 𝒪[L]) : L) ≠ 0 := by
    intro h0
    rw [h0, Algebra.norm_zero] at hN
    simp at hN
  refine ⟨Units.mk0 _ hne, ?_⟩
  ext
  rw [coe_normUnits, Units.val_mk0, ← hN, coe_unitsIncl]

variable (K L) in

theorem isOpen_range_normUnits : IsOpen ((normUnits K L).range : Set Kˣ) := by
  obtain ⟨n, hn⟩ := exists_unitFiltrationUnits_le_range_normUnits K L
  exact Subgroup.isOpen_mono hn (isOpen_unitFiltrationUnits n)

variable (K L) in

theorem finiteIndex_range_normUnits : (normUnits K L).range.FiniteIndex := by
  obtain ⟨n, hn⟩ := exists_unitFiltrationUnits_le_range_normUnits K L
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  set d := Module.finrank K L with hd
  have hd0 : d ≠ 0 := Module.finrank_pos.ne'
  let P : Subgroup (Multiplicative ℤ × 𝒪[K]ˣ) :=
    (AddSubgroup.zmultiples (d : ℤ)).toSubgroup.prod (unitFiltration K n)
  have hP : P.index ≠ 0 := by
    rw [Subgroup.index_prod, AddSubgroup.index_toSubgroup, Int.index_zmultiples]
    exact mul_ne_zero (by simpa using hd0) (unitFiltration K n).index_ne_zero_of_finite
  have hle : P.comap (unitsEquivIntProd hϖ).toMonoidHom ≤ (normUnits K L).range := by
    intro x hx
    simp only [Subgroup.mem_comap, Subgroup.mem_prod, MulEquiv.coe_toMonoidHom, P] at hx
    obtain ⟨h1, h2⟩ := hx
    set p := unitsEquivIntProd hϖ x with hp
    have hxp : x = unitsOfIntProd hϖ (p.1, p.2) := by
      rw [← unitsEquivIntProd_symm_apply, Prod.mk.eta, hp, MulEquiv.symm_apply_apply]
    obtain ⟨j, hj⟩ := AddSubgroup.mem_zmultiples_iff.mp ((Multiplicative.mem_toSubgroup _ _).mp h1)
    rw [hxp, unitsOfIntProd_eq, ← hj, smul_eq_mul, mul_comm j, zpow_mul, zpow_natCast]
    refine Subgroup.mul_mem _ (Subgroup.zpow_mem _ (MonoidHom.mem_range.mpr ⟨Units.map
      (algebraMap K L : K →* L) (uniformizerUnit hϖ), ?_⟩) _) (hn (Subgroup.mem_map.mpr ⟨_, h2, rfl⟩))
    ext
    simp [Algebra.norm_algebraMap, hd]
  have : (P.comap (unitsEquivIntProd hϖ).toMonoidHom).FiniteIndex := by
    constructor
    rw [Subgroup.index_comap_of_surjective _ (unitsEquivIntProd hϖ).surjective]
    exact hP
  exact Subgroup.finiteIndex_of_le hle

end Separable

end Local

end Sec_ExistsUnitFiltrationUnitsLeRangeNormUnits


/-! ### PadicLogSeries -/
section Sec_PadicLogSeries

open ValuativeRel IsLocalRing Topology Filter
open scoped WithZero

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

section Summation

variable (K) in

theorem exists_normalizedValuation_eq (n : ℤ) :
    ∃ y : K, normalizedValuation K y = WithZero.exp n := by
  obtain ⟨y, hy⟩ := ValuativeRel.valuation_surjective
    ((IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K).symm (WithZero.exp n))
  exact ⟨y, by rw [normalizedValuation_apply, hy]; simp⟩

variable (K) in

def valBall (n : ℤ) : AddSubgroup K where
  carrier := {x | normalizedValuation K x ≤ WithZero.exp (-n)}
  zero_mem' := by simp
  add_mem' hx hy := (normalizedValuation K).map_add_le hx hy
  neg_mem' hx := by simpa using hx

theorem mem_valBall {n : ℤ} {x : K} :
    x ∈ valBall K n ↔ normalizedValuation K x ≤ WithZero.exp (-n) := Iff.rfl

theorem valBall_antitone {m n : ℤ} (h : m ≤ n) : valBall K n ≤ valBall K m := fun x hx ↦
  hx.trans (WithZero.exp_le_exp.mpr (by omega))

theorem mul_mem_valBall {m n : ℤ} {x y : K} (hx : x ∈ valBall K m) (hy : y ∈ valBall K n) :
    x * y ∈ valBall K (m + n) := by
  rw [mem_valBall, map_mul, neg_add, WithZero.exp_add]
  exact mul_le_mul' hx hy

theorem pow_mem_valBall {n : ℤ} {x : K} (hx : x ∈ valBall K n) (k : ℕ) :
    x ^ k ∈ valBall K (k * n) := by
  induction k with
  | zero => simp [mem_valBall]
  | succ k ih =>
    rw [pow_succ]
    convert mul_mem_valBall ih hx using 2
    push_cast; ring

theorem isOpen_valBall (n : ℤ) : IsOpen (valBall K n : Set K) := by
  obtain ⟨y, hy⟩ := exists_normalizedValuation_eq K (-n)
  have hy0 : valuation K y ≠ 0 := by
    intro h
    rw [normalizedValuation_apply, h, map_zero] at hy
    exact WithZero.exp_ne_zero hy.symm
  have : (valBall K n : Set K) = {z : K | valuation K (z - 0) ≤ valuation K y} := by
    ext z
    simp only [sub_zero, SetLike.mem_coe, mem_valBall, ← hy, normalizedValuation_le_iff]
    rfl
  rw [this]
  exact isOpen_setOf_valuation_sub_le hy0

theorem isClosed_valBall (n : ℤ) : IsClosed (valBall K n : Set K) :=
  AddSubgroup.isClosed_of_isOpen _ (isOpen_valBall n)

theorem valBall_mem_nhds (n : ℤ) : (valBall K n : Set K) ∈ 𝓝 (0 : K) :=
  (isOpen_valBall n).mem_nhds (zero_mem _)

private instance t2Space_local_field_instance : T2Space K := by
  let := IsTopologicalAddGroup.rightUniformSpace K
  have := isUniformAddGroup_of_addCommGroup (G := K)
  infer_instance

instance nonarchimedeanRing : NonarchimedeanRing K where
  is_nonarchimedean U hU := by
    obtain ⟨γ, -, hγ⟩ := (IsValuativeTopology.hasBasis_nhds_zero K).mem_iff.mp hU
    exact ⟨⟨(valuation K).ltAddSubgroup γ, isOpen_setOf_valuation_lt⟩, hγ⟩

theorem tendsto_zero_iff_valBall {ι : Type*} {l : Filter ι} {f : ι → K} :
    Tendsto f l (𝓝 0) ↔ ∀ N : ℤ, ∀ᶠ i in l, f i ∈ valBall K N := by
  constructor
  · intro hf N
    exact hf (valBall_mem_nhds N)
  · intro hf
    rw [(IsValuativeTopology.hasBasis_nhds_zero K).tendsto_right_iff]
    intro γ _
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
    obtain ⟨n, -, hn⟩ := exists_pow_lt hϖ γ.ne_zero
    filter_upwards [hf n] with i hi
    refine lt_of_le_of_lt ?_ hn
    rw [← map_pow, ← normalizedValuation_le_iff, map_pow, normalizedValuation_uniformizer hϖ,
      ← WithZero.exp_nsmul]
    simpa [mem_valBall] using hi

theorem summable_of_tendsto_zero {f : ℕ → K} (hf : Tendsto f atTop (𝓝 0)) : Summable f := by
  let := IsTopologicalAddGroup.rightUniformSpace K
  have := isUniformAddGroup_of_addCommGroup (G := K)
  exact NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero (by rwa [Nat.cofinite_eq_atTop])

theorem tsum_mem_valBall {f : ℕ → K} {N : ℤ} (h : ∀ k, f k ∈ valBall K N) :
    ∑' k, f k ∈ valBall K N := by
  by_cases hs : Summable f
  · exact (isClosed_valBall N).mem_of_tendsto hs.hasSum.tendsto_sum_nat
      (Eventually.of_forall fun s ↦ AddSubgroup.sum_mem _ fun k _ ↦ h k)
  · rw [tsum_eq_zero_of_not_summable hs]
    exact zero_mem _

end Summation

section Arithmetic

theorem mul_self_le_two_pow_succ (v : ℕ) : v * v ≤ 2 ^ (v + 1) := by
  induction v with
  | zero => norm_num
  | succ v ih =>
    rcases Nat.lt_or_ge v 3 with h | h
    · interval_cases v <;> norm_num
    · rw [pow_succ]; nlinarith

theorem four_mul_padicValNat_le (p : ℕ) [hp : Fact p.Prime] (c : ℕ) {n : ℕ} (hn : n ≠ 0) :
    4 * c * padicValNat p n ≤ n + 32 * c ^ 2 := by
  set v := padicValNat p n
  have h1 : 2 ^ v ≤ p ^ v := Nat.pow_le_pow_left hp.out.two_le v
  have h2 : p ^ v ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) pow_padicValNat_dvd
  have h3 := mul_self_le_two_pow_succ v
  rw [pow_succ] at h3
  rcases Nat.lt_or_ge v (8 * c) with h | h
  · nlinarith
  · nlinarith

theorem sub_one_mul_padicValNat_lt (p : ℕ) [hp : Fact p.Prime] {n : ℕ} (hn : n ≠ 0) :
    (p - 1) * padicValNat p n < n := by
  have h : padicValNat p n ≤ padicValNat p n.factorial := by
    rw [← padicValNat_dvd_iff_le (Nat.factorial_ne_zero n)]
    exact pow_padicValNat_dvd.trans (Nat.dvd_factorial (Nat.pos_of_ne_zero hn) le_rfl)
  exact lt_of_le_of_lt (Nat.mul_le_mul_left _ h)
    (sub_one_mul_padicValNat_factorial_lt_of_ne_zero p hn)

end Arithmetic

section CharZero

variable (K) in

noncomputable def absRamificationIndex : ℕ := (ord ((ringChar 𝓀[K] : ℕ) : K)).toNat

variable (p : ℕ) [hp : Fact p.Prime] [CharP 𝓀[K] p] [CharZero K]

theorem normalizedValuation_natCast_prime :
    normalizedValuation K (p : K) = WithZero.exp (-(absRamificationIndex K : ℤ)) := by
  have hp0 : (p : K) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  have hr : ringChar 𝓀[K] = p := ringChar.eq 𝓀[K] p
  have hlt : normalizedValuation K (p : K) < 1 := by
    rw [← map_one (normalizedValuation K), normalizedValuation_lt_iff, map_one]
    exact CharZero.valuation_p_lt_one K p
  rw [normalizedValuation_eq_exp_ord hp0] at hlt ⊢
  rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at hlt
  rw [absRamificationIndex, hr, Int.toNat_of_nonneg (by omega)]

include p in
theorem one_le_absRamificationIndex : 1 ≤ absRamificationIndex K := by
  have h := normalizedValuation_natCast_prime (K := K) p
  have hlt : normalizedValuation K (p : K) < 1 := by
    rw [← map_one (normalizedValuation K), normalizedValuation_lt_iff, map_one]
    exact CharZero.valuation_p_lt_one K p
  rw [h, ← WithZero.exp_zero, WithZero.exp_lt_exp] at hlt
  omega

omit hp [CharZero K] in
theorem normalizedValuation_natCast_of_not_dvd {m : ℕ} (hm : ¬ p ∣ m) :
    normalizedValuation K (m : K) = 1 := by
  rw [← map_one (normalizedValuation K), normalizedValuation_eq_iff, map_one]
  have := (CharZero.valuation_intCast_eq_one_iff K p (m : ℤ)).mpr (by exact_mod_cast hm)
  exact_mod_cast this

theorem normalizedValuation_natCast {n : ℕ} (hn : n ≠ 0) :
    normalizedValuation K (n : K) =
      WithZero.exp (-(absRamificationIndex K * padicValNat p n : ℤ)) := by
  obtain ⟨k, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn p hp.out.ne_one
  have hm0 : m ≠ 0 := by rintro rfl; exact hm (dvd_zero p)
  rw [padicValNat.mul (pow_ne_zero _ hp.out.ne_zero) hm0, padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd hm]
  push_cast
  rw [map_mul, map_pow, normalizedValuation_natCast_prime p,
    normalizedValuation_natCast_of_not_dvd p hm, mul_one, ← WithZero.exp_nsmul]
  congr 1
  simp; ring

theorem div_natCast_mem_valBall {a : ℤ} {x : K} (hx : x ∈ valBall K a) {n : ℕ} (hn : n ≠ 0) :
    x / n ∈ valBall K (a - absRamificationIndex K * padicValNat p n) := by
  rw [mem_valBall, map_div₀, normalizedValuation_natCast p hn, div_eq_mul_inv,
    ← WithZero.exp_neg, neg_neg, neg_sub, sub_eq_add_neg, WithZero.exp_add, mul_comm]
  exact mul_le_mul_right hx _

end CharZero

section Series

noncomputable def logSeries (x : K) : K := ∑' k : ℕ, (-1) ^ k * x ^ (k + 1) / ((k + 1 : ℕ) : K)

noncomputable def expSeries (x : K) : K := ∑' k : ℕ, x ^ k / (k.factorial : K)

variable (p : ℕ) [hp : Fact p.Prime] [CharP 𝓀[K] p] [CharZero K]

theorem logTerm_mem {a : ℤ} {x : K} (hx : x ∈ valBall K a) (k : ℕ) :
    (-1) ^ k * x ^ (k + 1) / ((k + 1 : ℕ) : K) ∈
      valBall K ((k + 1) * a - absRamificationIndex K * padicValNat p (k + 1)) := by
  have h1 : (-1 : K) ^ k * x ^ (k + 1) ∈ valBall K ((k + 1 : ℕ) * a) := by
    rw [mem_valBall, map_mul, map_pow, Valuation.map_neg, map_one, one_pow, one_mul]
    exact pow_mem_valBall hx (k + 1)
  have := div_natCast_mem_valBall p h1 (by omega : k + 1 ≠ 0)
  simpa only [Nat.cast_add, Nat.cast_one] using this

theorem expTerm_mem {a : ℤ} {x : K} (hx : x ∈ valBall K a) (k : ℕ) :
    x ^ k / (k.factorial : K) ∈
      valBall K (k * a - absRamificationIndex K * padicValNat p k.factorial) :=
  div_natCast_mem_valBall p (pow_mem_valBall hx k) (Nat.factorial_ne_zero k)

omit [CharP 𝓀[K] p] [CharZero K] in
theorem sub_one_mul_padicValNat_factorial_le (k : ℕ) :
    (p - 1) * padicValNat p k.factorial ≤ k :=
  (sub_one_mul_padicValNat_factorial k).le.trans (Nat.sub_le _ _)

include p in

theorem summable_logSeries {x : K} (hx : x ∈ valBall K 1) :
    Summable fun k : ℕ ↦ (-1) ^ k * x ^ (k + 1) / ((k + 1 : ℕ) : K) := by
  refine summable_of_tendsto_zero (tendsto_zero_iff_valBall.mpr fun N ↦ ?_)
  rw [eventually_atTop]
  set e := absRamificationIndex K
  refine ⟨4 * N.toNat + 32 * e ^ 2, fun k hk ↦ valBall_antitone ?_ (logTerm_mem p hx k)⟩
  have h1 := four_mul_padicValNat_le p e (Nat.succ_ne_zero k)
  have h2 : N ≤ (N.toNat : ℤ) := Int.self_le_toNat N
  have h3 : ((4 * N.toNat + 32 * e ^ 2 : ℕ) : ℤ) ≤ k := by exact_mod_cast hk
  have h4 : ((4 * e * padicValNat p (k + 1) : ℕ) : ℤ) ≤ ((k + 1 + 32 * e ^ 2 : ℕ) : ℤ) := by
    exact_mod_cast h1
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one,
    ] at h3 h4
  nlinarith

theorem one_le_of_lt_sub_one_mul {a : ℤ} (ha : (absRamificationIndex K : ℤ) < (p - 1 : ℤ) * a) :
    1 ≤ a := by
  have he := one_le_absRamificationIndex (K := K) p
  have hp2 : (2 : ℤ) ≤ p := by exact_mod_cast hp.out.two_le
  by_contra h
  push Not at h
  nlinarith

theorem logSeries_sub_self_mem {a : ℤ} {x : K} (hx : x ∈ valBall K a)
    (ha : (absRamificationIndex K : ℤ) < (p - 1 : ℤ) * a) :
    logSeries x - x ∈ valBall K (a + 1) := by
  have ha1 := one_le_of_lt_sub_one_mul p ha
  have hs := summable_logSeries p (valBall_antitone ha1 hx)
  rw [logSeries, hs.tsum_eq_zero_add]
  simp only [pow_zero, zero_add, pow_one, one_mul, Nat.cast_one, div_one, add_sub_cancel_left]
  refine tsum_mem_valBall fun k ↦ valBall_antitone ?_ (logTerm_mem p hx (k + 1))
  have h1 := sub_one_mul_padicValNat_lt p (Nat.succ_ne_zero (k + 1))
  set v := padicValNat p (k + 1 + 1)
  set e := absRamificationIndex K
  have hp2 : (2 : ℤ) ≤ p := by exact_mod_cast hp.out.two_le
  have h1' : ((p : ℤ) - 1) * v ≤ k + 1 := by
    have : ((p - 1) * v : ℕ) < k + 1 + 1 := h1
    have hp1 : ((p - 1 : ℕ) : ℤ) = (p : ℤ) - 1 := by
      rw [Nat.cast_sub hp.out.one_le]; simp
    have : (((p - 1) * v : ℕ) : ℤ) < k + 1 + 1 := by exact_mod_cast this
    push_cast [hp1] at this
    linarith
  have hv : (0 : ℤ) ≤ v := by positivity
  have he : (0 : ℤ) ≤ e := by positivity
  push_cast
  nlinarith [mul_le_mul_of_nonneg_left h1' he]

end Series

section Exp

variable (p : ℕ) [hp : Fact p.Prime] [CharP 𝓀[K] p] [CharZero K]

omit [CharP 𝓀[K] p] [CharZero K] in

theorem expTerm_order_bound {a : ℤ} (ha : (absRamificationIndex K : ℤ) < (p - 1 : ℤ) * a)
    (k : ℕ) : (k : ℤ) ≤ (p - 1 : ℤ) * (k * a - absRamificationIndex K * padicValNat p k.factorial)
    := by
  have h1 := sub_one_mul_padicValNat_factorial_le p k
  set v := padicValNat p k.factorial
  set e := absRamificationIndex K
  have hp2 : (2 : ℤ) ≤ p := by exact_mod_cast hp.out.two_le
  have h1' : ((p : ℤ) - 1) * v ≤ k := by
    have hp1 : ((p - 1 : ℕ) : ℤ) = (p : ℤ) - 1 := by
      rw [Nat.cast_sub hp.out.one_le]; simp
    have : (((p - 1) * v : ℕ) : ℤ) ≤ k := by exact_mod_cast h1
    push_cast [hp1] at this
    linarith
  have he : (0 : ℤ) ≤ e := by positivity
  have hk : (0 : ℤ) ≤ k := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h1' he, mul_le_mul_of_nonneg_left ha.le hk]

theorem summable_expSeries {a : ℤ} {x : K} (hx : x ∈ valBall K a)
    (ha : (absRamificationIndex K : ℤ) < (p - 1 : ℤ) * a) :
    Summable fun k : ℕ ↦ x ^ k / (k.factorial : K) := by
  refine summable_of_tendsto_zero (tendsto_zero_iff_valBall.mpr fun N ↦ ?_)
  rw [eventually_atTop]
  refine ⟨(p - 1) * N.toNat, fun k hk ↦ valBall_antitone ?_ (expTerm_mem p hx k)⟩
  have h1 := expTerm_order_bound p ha k
  have h2 : N ≤ (N.toNat : ℤ) := Int.self_le_toNat N
  have hp2 : (2 : ℤ) ≤ p := by exact_mod_cast hp.out.two_le
  have hp1 : ((p - 1 : ℕ) : ℤ) = (p : ℤ) - 1 := by
    rw [Nat.cast_sub hp.out.one_le]; simp
  have h3 : (((p - 1) * N.toNat : ℕ) : ℤ) ≤ k := by exact_mod_cast hk
  push_cast [hp1] at h3
  nlinarith

theorem expSeries_sub_one_sub_self_mem {a : ℤ} {x : K} (hx : x ∈ valBall K a)
    (ha : (absRamificationIndex K : ℤ) < (p - 1 : ℤ) * a) :
    expSeries x - 1 - x ∈ valBall K (a + 1) := by
  have hs := summable_expSeries p hx ha
  rw [expSeries, hs.tsum_eq_zero_add, ((summable_nat_add_iff 1).mpr hs).tsum_eq_zero_add]
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, zero_add, pow_one,
    Nat.factorial_one]
  have : ∀ t : K, 1 + (x + t) - 1 - x = t := fun t ↦ by ring
  rw [this]
  refine tsum_mem_valBall fun k ↦ valBall_antitone ?_ (expTerm_mem p hx (k + 1 + 1))
  have h1 := expTerm_order_bound p ha (k + 1 + 1)
  have h0 := sub_one_mul_padicValNat_factorial_lt_of_ne_zero p (by omega : k + 1 + 1 ≠ 0)
  set v := padicValNat p (k + 1 + 1).factorial
  set e := absRamificationIndex K
  have hp2 : (2 : ℤ) ≤ p := by exact_mod_cast hp.out.two_le
  have hp1 : ((p - 1 : ℕ) : ℤ) = (p : ℤ) - 1 := by
    rw [Nat.cast_sub hp.out.one_le]; simp
  have h0' : (((p - 1) * v : ℕ) : ℤ) < k + 1 + 1 := by exact_mod_cast h0
  push_cast [hp1] at h0' h1
  have he : (0 : ℤ) ≤ e := by positivity
  have h0'' : ((p : ℤ) - 1) * v ≤ k + 1 := by linarith
  have ha' : (e : ℤ) + 1 ≤ ((p : ℤ) - 1) * a := by linarith
  have hk : (0 : ℤ) ≤ k + 1 := by positivity
  push_cast
  nlinarith [mul_le_mul_of_nonneg_left h0'' he, mul_le_mul_of_nonneg_left ha' hk]

theorem expSeries_add {a : ℤ} {x y : K} (hx : x ∈ valBall K a) (hy : y ∈ valBall K a)
    (ha : (absRamificationIndex K : ℤ) < (p - 1 : ℤ) * a) :
    expSeries (x + y) = expSeries x * expSeries y := by
  let := IsTopologicalAddGroup.rightUniformSpace K
  have := isUniformAddGroup_of_addCommGroup (G := K)
  have hsx := summable_expSeries p hx ha
  have hsy := summable_expSeries p hy ha
  have hxy := hsx.mul_of_nonarchimedean hsy
  unfold expSeries
  rw [hsx.tsum_mul_tsum_eq_tsum_sum_antidiagonal hsy hxy]
  refine tsum_congr fun n ↦ ?_
  rw [(Commute.all x y).add_pow', Finset.sum_div]
  refine Finset.sum_congr rfl fun ij hij ↦ ?_
  obtain ⟨i, j⟩ := ij
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hij
  subst hij
  have key : ((i + j).choose i : K) * (i.factorial : K) * (j.factorial : K) =
      ((i + j).factorial : K) := by
    have h := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right i j)
    rw [Nat.add_sub_cancel_left] at h
    exact_mod_cast h
  have hi : (i.factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero i)
  have hj : (j.factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j)
  have hc : ((i + j).choose i : K) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.choose_pos (Nat.le_add_right i j)).ne'
  simp only [nsmul_eq_mul]
  rw [← key]
  field_simp

theorem expSeries_sub_one_mem {a : ℤ} {x : K} (hx : x ∈ valBall K a)
    (ha : (absRamificationIndex K : ℤ) < (p - 1 : ℤ) * a) :
    expSeries x - 1 ∈ valBall K a := by
  have h := add_mem (valBall_antitone (by omega : a ≤ a + 1)
    (expSeries_sub_one_sub_self_mem p hx ha)) hx
  simpa using h

theorem logSeries_mem_valBall {a : ℤ} {x : K} (hx : x ∈ valBall K a)
    (ha : (absRamificationIndex K : ℤ) < (p - 1 : ℤ) * a) :
    logSeries x ∈ valBall K a := by
  have h := add_mem (valBall_antitone (by omega : a ≤ a + 1) (logSeries_sub_self_mem p hx ha)) hx
  simpa using h

end Exp

end Sec_PadicLogSeries


/-! ### PadicLogHom -/
section Sec_PadicLogHom

open ValuativeRel IsLocalRing Topology Filter
open scoped WithZero

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

section Integer

theorem dvd_factorial_mul_choose_sub {m k : ℕ} (hk : k < m) :
    (m : ℤ) ∣ (k.factorial : ℤ) * (((m - 1).choose k : ℕ) - (-1) ^ k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hk' : k < m := by omega
    have h1 := Nat.choose_succ_right_eq (m - 1) k
    have hle : k ≤ m - 1 := by omega
    have h1' : (((m - 1).choose (k + 1) : ℕ) : ℤ) * (k + 1) =
        ((m - 1).choose k : ℕ) * ((m : ℤ) - 1 - k) := by
      have := congrArg (fun t : ℕ ↦ (t : ℤ)) h1
      simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] at this
      rw [this, Nat.cast_sub hle, Nat.cast_sub (by omega : 1 ≤ m)]
      push_cast; ring
    obtain ⟨t, ht⟩ := ih hk'
    refine ⟨((m : ℤ) - 1 - k) * t + (-1) ^ k * k.factorial, ?_⟩
    have e1 : ((k + 1).factorial : ℤ) * ((((m - 1).choose (k + 1) : ℕ) : ℤ) - (-1) ^ (k + 1)) =
        (k.factorial : ℤ) * ((((m - 1).choose (k + 1) : ℕ) : ℤ) * (k + 1)) +
          (-1) ^ k * (k + 1) * k.factorial := by
      push_cast [Nat.factorial_succ]; ring
    rw [e1, h1']
    linear_combination ((m : ℤ) - 1 - k) * ht

end Integer

section Limit

variable (p : ℕ) [hp : Fact p.Prime] [CharP 𝓀[K] p] [CharZero K]

omit [CharZero K] in
theorem intCast_mem_valBall_zero (z : ℤ) : (z : K) ∈ valBall K 0 := by
  rw [mem_valBall, neg_zero, WithZero.exp_zero, normalizedValuation_le_one_iff]
  exact intCast_mem _ z

omit [CharP 𝓀[K] p] [CharZero K] in

theorem logTerm_order_ge {N : ℤ} {k : ℕ} (hk : 4 * N.toNat + 32 * absRamificationIndex K ^ 2 ≤ k) :
    N ≤ (k + 1 : ℤ) - absRamificationIndex K * padicValNat p (k + 1) := by
  set e := absRamificationIndex K
  have h1 := four_mul_padicValNat_le p e (Nat.succ_ne_zero k)
  have h2 : N ≤ (N.toNat : ℤ) := Int.self_le_toNat N
  have h3 : ((4 * N.toNat + 32 * e ^ 2 : ℕ) : ℤ) ≤ k := by exact_mod_cast hk
  have h4 : ((4 * e * padicValNat p (k + 1) : ℕ) : ℤ) ≤ ((k + 1 + 32 * e ^ 2 : ℕ) : ℤ) := by
    exact_mod_cast h1
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] at h3 h4
  nlinarith

omit [CharZero K] in
theorem padicValNat_le_self' {j : ℕ} (hj : j ≠ 0) : padicValNat p j ≤ j := by
  have h1 : padicValNat p j < p ^ padicValNat p j := Nat.lt_pow_self hp.out.one_lt
  have h2 : p ^ padicValNat p j ≤ j := Nat.le_of_dvd (Nat.pos_of_ne_zero hj) pow_padicValNat_dvd
  omega

theorem natCast_prime_pow_mem_valBall (n : ℕ) :
    ((p ^ n : ℕ) : K) ∈ valBall K (absRamificationIndex K * n) := by
  rw [mem_valBall, Nat.cast_pow, map_pow, normalizedValuation_natCast_prime p,
    ← WithZero.exp_nsmul]
  simp [mul_comm]

theorem tendsto_natCast_prime_pow : Tendsto (fun n : ℕ ↦ ((p ^ n : ℕ) : K)) atTop (𝓝 0) := by
  refine tendsto_zero_iff_valBall.mpr fun N ↦ ?_
  rw [eventually_atTop]
  refine ⟨N.toNat, fun n hn ↦ valBall_antitone ?_ (natCast_prime_pow_mem_valBall p n)⟩
  have he := one_le_absRamificationIndex (K := K) p
  have h2 : N ≤ (N.toNat : ℤ) := Int.self_le_toNat N
  have h3 : (N.toNat : ℤ) ≤ n := by exact_mod_cast hn
  have he' : (1 : ℤ) ≤ absRamificationIndex K := by exact_mod_cast he
  nlinarith

omit [ValuativeRel K] [IsNonarchimedeanLocalField K] in

theorem one_add_pow_sub_one_div_eq (x : K) {m : ℕ} (hm : m ≠ 0) :
    ((1 + x) ^ m - 1) / (m : K) =
      ∑' k : ℕ, (((m - 1).choose k : ℕ) : K) * (x ^ (k + 1) / ((k + 1 : ℕ) : K)) := by
  rw [tsum_eq_sum (s := Finset.range m)]
  · rw [add_comm, add_pow, Finset.sum_range_succ']
    simp only [one_pow, mul_one, pow_zero, Nat.choose_zero_right, Nat.cast_one,
      add_sub_cancel_right]
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    have h := Nat.add_one_mul_choose_eq (m - 1) k
    rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hm)] at h
    have h' : (m : K) * ((m - 1).choose k : ℕ) = ((m.choose (k + 1) : ℕ) : K) * (k + 1 : ℕ) := by
      exact_mod_cast h
    have hm' : (m : K) ≠ 0 := Nat.cast_ne_zero.mpr hm
    have hk' : ((k + 1 : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k)
    field_simp
    linear_combination (-(x * x ^ k)) * h'
  · intro k hk
    rw [Finset.mem_range, not_lt] at hk
    rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, zero_mul]

end Limit

section Limit2

variable (p : ℕ) [hp : Fact p.Prime] [CharP 𝓀[K] p] [CharZero K]

theorem tendsto_logSeries {x : K} (hx : x ∈ valBall K 1) :
    Tendsto (fun n : ℕ ↦ ((1 + x) ^ (p ^ n) - 1) / ((p ^ n : ℕ) : K)) atTop
      (𝓝 (logSeries x)) := by
  rw [← tendsto_sub_nhds_zero_iff, tendsto_zero_iff_valBall]
  intro N
  set e := absRamificationIndex K with he_def
  set K0 := 4 * N.toNat + 32 * e ^ 2 with hK0
  have he := one_le_absRamificationIndex (K := K) p
  rw [eventually_atTop]
  refine ⟨N.toNat + 2 * K0 + 1, fun n hn ↦ ?_⟩
  have hm : p ^ n ≠ 0 := pow_ne_zero _ hp.out.ne_zero
  have hKm : K0 < p ^ n := by
    have h1 : n < 2 ^ n := Nat.lt_two_pow_self
    have h2 : 2 ^ n ≤ p ^ n := Nat.pow_le_pow_left hp.out.two_le n
    omega
  have hs1 : Summable fun k : ℕ ↦ (((p ^ n - 1).choose k : ℕ) : K) *
      (x ^ (k + 1) / ((k + 1 : ℕ) : K)) := by
    refine summable_of_ne_finset_zero (s := Finset.range (p ^ n)) fun k hk ↦ ?_
    rw [Finset.mem_range, not_lt] at hk
    rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, zero_mul]
  have hs2 := summable_logSeries p hx
  rw [one_add_pow_sub_one_div_eq x hm, logSeries, ← hs1.tsum_sub hs2]
  refine tsum_mem_valBall fun k ↦ ?_
  set T : K := x ^ (k + 1) / ((k + 1 : ℕ) : K) with hT_def
  have hT : T ∈ valBall K ((k + 1 : ℕ) * 1 - e * padicValNat p (k + 1)) :=
    div_natCast_mem_valBall p (pow_mem_valBall hx (k + 1)) (Nat.succ_ne_zero k)
  set C : ℕ := (p ^ n - 1).choose k
  have heq : (C : K) * T - (-1) ^ k * x ^ (k + 1) / ((k + 1 : ℕ) : K) =
      (((C : ℤ) - (-1) ^ k : ℤ) : K) * T := by
    rw [hT_def]; push_cast; ring
  rw [heq]
  by_cases hk : K0 ≤ k
  · have hmem := mul_mem_valBall (intCast_mem_valBall_zero ((C : ℤ) - (-1) ^ k)) hT
    refine valBall_antitone ?_ hmem
    have := logTerm_order_ge (K := K) p hk
    push_cast at this ⊢
    linarith
  · push Not at hk
    obtain ⟨t, ht⟩ := dvd_factorial_mul_choose_sub (m := p ^ n) (k := k) (by omega)
    have hkf : (k.factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
    have hc : ((((C : ℤ) - (-1) ^ k : ℤ)) : K) = ((p ^ n : ℕ) : K) * (t : K) / k.factorial := by
      rw [eq_div_iff hkf]
      have := congrArg (fun z : ℤ ↦ (z : K)) ht
      push_cast at this ⊢
      linear_combination this
    have h1 : ((p ^ n : ℕ) : K) * (t : K) ∈ valBall K (e * n + 0) :=
      mul_mem_valBall (natCast_prime_pow_mem_valBall p n) (intCast_mem_valBall_zero t)
    have h2 := div_natCast_mem_valBall p h1 (Nat.factorial_ne_zero k)
    rw [← hc] at h2
    refine valBall_antitone ?_ (mul_mem_valBall h2 hT)
    have hv1 := padicValNat_le_self' (p := p) (Nat.succ_ne_zero k)
    have hv2 := padicValNat_factorial_le (p := p) k
    have h2N : N ≤ (N.toNat : ℤ) := Int.self_le_toNat N
    have hn' : ((N.toNat + 2 * K0 + 1 : ℕ) : ℤ) ≤ n := by exact_mod_cast hn
    have hk' : (k : ℤ) < K0 := by exact_mod_cast hk
    have hv1' : (padicValNat p (k + 1) : ℤ) ≤ k + 1 := by exact_mod_cast hv1
    have hv2' : (padicValNat p k.factorial : ℤ) ≤ k := by exact_mod_cast hv2
    have he' : (1 : ℤ) ≤ e := by exact_mod_cast he
    push_cast at hn' ⊢
    nlinarith [mul_le_mul_of_nonneg_left hv1' (by positivity : (0 : ℤ) ≤ e),
      mul_le_mul_of_nonneg_left hv2' (by positivity : (0 : ℤ) ≤ e)]

end Limit2

section Hom

theorem mem_unitFiltrationUnits_iff_valBall {n : ℕ} (hn : 1 ≤ n) {x : Kˣ} :
    x ∈ unitFiltrationUnits K n ↔ (x : K) - 1 ∈ valBall K n := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  rw [mem_unitFiltrationUnits_iff hn hϖ, mem_valBall, ← map_pow, ← normalizedValuation_le_iff,
    map_pow, normalizedValuation_uniformizer hϖ, ← WithZero.exp_nsmul]
  simp

theorem sub_one_mem_valBall_one (u : unitFiltrationUnits K 1) :
    ((u : Kˣ) : K) - 1 ∈ valBall K 1 := by
  simpa using (mem_unitFiltrationUnits_iff_valBall le_rfl).mp u.2

variable (p : ℕ) [hp : Fact p.Prime] [CharP 𝓀[K] p] [CharZero K]

include p in

theorem logSeries_mul {x y : K} (hx : x ∈ valBall K 1) (hy : y ∈ valBall K 1) :
    logSeries ((1 + x) * (1 + y) - 1) = logSeries x + logSeries y := by
  have hz : (1 + x) * (1 + y) - 1 ∈ valBall K 1 := by
    have : (1 + x) * (1 + y) - 1 = x + y + x * y := by ring
    rw [this]
    exact add_mem (add_mem hx hy) (valBall_antitone (by norm_num) (mul_mem_valBall hx hy))
  have ha := tendsto_logSeries p hx
  have hb := tendsto_logSeries p hy
  have hc := tendsto_logSeries p hz
  have hm := tendsto_natCast_prime_pow (K := K) p
  have key : ∀ n : ℕ, ((1 + ((1 + x) * (1 + y) - 1)) ^ (p ^ n) - 1) / ((p ^ n : ℕ) : K) =
      ((1 + x) ^ (p ^ n) - 1) / ((p ^ n : ℕ) : K) + ((1 + y) ^ (p ^ n) - 1) / ((p ^ n : ℕ) : K) +
      ((p ^ n : ℕ) : K) * (((1 + x) ^ (p ^ n) - 1) / ((p ^ n : ℕ) : K)) *
        (((1 + y) ^ (p ^ n) - 1) / ((p ^ n : ℕ) : K)) := by
    intro n
    have h0 : ((p ^ n : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr (pow_ne_zero _ hp.out.ne_zero)
    rw [add_sub_cancel, mul_pow]
    field_simp
    ring
  have hlim := (ha.add hb).add ((hm.mul ha).mul hb)
  simp only [zero_mul, add_zero] at hlim
  exact tendsto_nhds_unique (hc.congr key) hlim

omit [CharP 𝓀[K] p] [CharZero K] in
theorem sub_one_le_of_lt {a : ℤ} (ha : (absRamificationIndex K : ℤ) < (p - 1 : ℤ) * a) {b : ℤ}
    (hab : a ≤ b) : (absRamificationIndex K : ℤ) < (p - 1 : ℤ) * b := by
  have hp2 : (2 : ℤ) ≤ p := by exact_mod_cast hp.out.two_le
  nlinarith

theorem eq_zero_of_logSeries_eq_zero {r : ℤ} (hr : (absRamificationIndex K : ℤ) < (p - 1 : ℤ) * r)
    {x : K} (hx : x ∈ valBall K r) (h : logSeries x = 0) : x = 0 := by
  by_contra hx0
  have hv := normalizedValuation_eq_exp_ord hx0
  have hxa : x ∈ valBall K (ord x) := by rw [mem_valBall, hv]
  have hxa1 : x ∉ valBall K (ord x + 1) := by
    rw [mem_valBall, hv, WithZero.exp_le_exp]; omega
  have hra : r ≤ ord x := by
    rw [mem_valBall, hv, WithZero.exp_le_exp] at hx; omega
  have := logSeries_sub_self_mem p hxa (sub_one_le_of_lt p hr hra)
  rw [h, zero_sub] at this
  exact hxa1 (by simpa using neg_mem this)

end Hom

section PadicLog

variable (K) [CharZero K]

noncomputable def padicLog : Additive (unitFiltrationUnits K 1) →+ K where
  toFun u := logSeries ((((Additive.toMul u : unitFiltrationUnits K 1) : Kˣ) : K) - 1)
  map_zero' := by simp [logSeries]
  map_add' u w := by
    have h := logSeries_mul (ringChar 𝓀[K]) (sub_one_mem_valBall_one (Additive.toMul u))
      (sub_one_mem_valBall_one (Additive.toMul w))
    simp only [add_sub_cancel] at h
    simpa only [toMul_add, Subgroup.coe_mul, Units.val_mul] using h

variable {K}

theorem padicLog_apply (u : Additive (unitFiltrationUnits K 1)) :
    padicLog K u = logSeries ((((Additive.toMul u : unitFiltrationUnits K 1) : Kˣ) : K) - 1) :=
  rfl

end PadicLog

section PadicLogProps

variable [CharZero K]

theorem continuous_padicLog : Continuous (padicLog K) := by
  refine continuous_of_continuousAt_zero (padicLog K) ?_
  rw [ContinuousAt, map_zero, tendsto_zero_iff_valBall]
  intro N
  set p := ringChar 𝓀[K]
  set e := absRamificationIndex K
  have hp2 : (2 : ℤ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).two_le
  set r : ℕ := N.toNat + e + 1 with hr_def
  have hr : (e : ℤ) < (p - 1 : ℤ) * (r : ℕ) := by
    have : (e : ℤ) + 1 ≤ r := by rw [hr_def]; push_cast; omega
    nlinarith
  have hcont : Continuous fun u : Additive (unitFiltrationUnits K 1) ↦
      ((((Additive.toMul u : unitFiltrationUnits K 1) : Kˣ) : K) - 1) :=
    (Units.continuous_val.comp (continuous_subtype_val.comp continuous_toMul)).sub
      continuous_const
  have hopen := (isOpen_valBall (r : ℤ)).preimage hcont
  filter_upwards [hopen.mem_nhds (by simp)] with u hu
  refine valBall_antitone ?_ (logSeries_mem_valBall p hu hr)
  rw [hr_def]; push_cast
  have := Int.self_le_toNat N
  omega

end PadicLogProps

end Sec_PadicLogHom


/-! ### PadicExp -/
section Sec_PadicExp

open ValuativeRel IsLocalRing Topology Filter
open scoped WithZero

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

section ExpLog

variable (p : ℕ) [hp : Fact p.Prime] [CharP 𝓀[K] p] [CharZero K]

omit [ValuativeRel K] [IsNonarchimedeanLocalField K] [CharZero K] in
theorem expSeries_zero : expSeries (0 : K) = 1 := by
  rw [expSeries, tsum_eq_single 0]
  · simp
  · intro k hk
    simp [zero_pow hk]

theorem expSeries_nsmul {a : ℤ} {x : K} (hx : x ∈ valBall K a)
    (ha : (absRamificationIndex K : ℤ) < (p - 1 : ℤ) * a) (m : ℕ) :
    expSeries (m • x) = expSeries x ^ m := by
  induction m with
  | zero => simp [expSeries_zero]
  | succ m ih =>
    rw [succ_nsmul, expSeries_add p (nsmul_mem hx m) hx ha, ih, pow_succ]

theorem expSeries_mul_sub_one_sub_mem {a d : ℤ} {x c : K} (hx : x ∈ valBall K a)
    (ha : (absRamificationIndex K : ℤ) < (p - 1 : ℤ) * a) (hc : c ∈ valBall K d) (hd : 0 ≤ d) :
    expSeries (c * x) - 1 - c * x ∈ valBall K (2 * d + a + 1) := by
  have hcx : c * x ∈ valBall K a := by
    simpa using valBall_antitone (by omega : a ≤ d + a) (mul_mem_valBall hc hx)
  have hs := summable_expSeries p hcx ha
  rw [expSeries, hs.tsum_eq_zero_add, ((summable_nat_add_iff 1).mpr hs).tsum_eq_zero_add]
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, zero_add, pow_one,
    Nat.factorial_one]
  have : ∀ t : K, 1 + (c * x + t) - 1 - c * x = t := fun t ↦ by ring
  rw [this]
  refine tsum_mem_valBall fun k ↦ ?_
  have h1 : (c * x) ^ (k + 1 + 1) / ((k + 1 + 1).factorial : K) =
      c ^ (k + 1 + 1) * (x ^ (k + 1 + 1) / ((k + 1 + 1).factorial : K)) := by
    rw [mul_pow, mul_div_assoc]
  rw [h1]
  have hxk := expTerm_mem p hx (k + 1 + 1)
  have hck := pow_mem_valBall hc (k + 1 + 1)
  refine valBall_antitone ?_ (mul_mem_valBall hck hxk)
  have h0 := sub_one_mul_padicValNat_factorial_lt_of_ne_zero p (by omega : k + 1 + 1 ≠ 0)
  set v := padicValNat p (k + 1 + 1).factorial
  set e := absRamificationIndex K
  have hp2 : (2 : ℤ) ≤ p := by exact_mod_cast hp.out.two_le
  have hp1 : ((p - 1 : ℕ) : ℤ) = (p : ℤ) - 1 := by
    rw [Nat.cast_sub hp.out.one_le]; simp
  have h0' : (((p - 1) * v : ℕ) : ℤ) < k + 1 + 1 := by exact_mod_cast h0
  push_cast [hp1] at h0'
  have he : (0 : ℤ) ≤ e := by positivity
  have h0'' : ((p : ℤ) - 1) * v ≤ k + 1 := by linarith
  have ha' : (e : ℤ) + 1 ≤ ((p : ℤ) - 1) * a := by linarith
  have hk : (0 : ℤ) ≤ k + 1 := by positivity
  have hkd : (0 : ℤ) ≤ k * d := by positivity
  push_cast
  nlinarith [mul_le_mul_of_nonneg_left h0'' he, mul_le_mul_of_nonneg_left ha' hk]

theorem logSeries_expSeries_sub_one {a : ℤ} {x : K} (hx : x ∈ valBall K a)
    (ha : (absRamificationIndex K : ℤ) < (p - 1 : ℤ) * a) :
    logSeries (expSeries x - 1) = x := by
  have ha1 := one_le_of_lt_sub_one_mul p ha
  have hy : expSeries x - 1 ∈ valBall K 1 :=
    valBall_antitone ha1 (expSeries_sub_one_mem p hx ha)
  have h1 := tendsto_logSeries p hy
  simp only [add_sub_cancel] at h1
  refine tendsto_nhds_unique h1 ?_
  rw [← tendsto_sub_nhds_zero_iff, tendsto_zero_iff_valBall]
  intro N
  rw [eventually_atTop]
  set e := absRamificationIndex K
  have he := one_le_absRamificationIndex (K := K) p
  refine ⟨N.toNat, fun k hk ↦ ?_⟩
  have hm0 : p ^ k ≠ 0 := pow_ne_zero _ hp.out.ne_zero
  have hm : ((p ^ k : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr hm0
  have heq : (expSeries x ^ (p ^ k) - 1) / ((p ^ k : ℕ) : K) - x =
      (expSeries (((p ^ k : ℕ) : K) * x) - 1 - ((p ^ k : ℕ) : K) * x) / ((p ^ k : ℕ) : K) := by
    rw [← expSeries_nsmul p hx ha, nsmul_eq_mul]
    field_simp
  rw [heq]
  have hmem := expSeries_mul_sub_one_sub_mem p hx ha (natCast_prime_pow_mem_valBall p k)
    (by positivity)
  have hdiv := div_natCast_mem_valBall p hmem hm0
  refine valBall_antitone ?_ hdiv
  rw [padicValNat.prime_pow]
  have h2 : N ≤ (N.toNat : ℤ) := Int.self_le_toNat N
  have h3 : (N.toNat : ℤ) ≤ k := by exact_mod_cast hk
  have he' : (1 : ℤ) ≤ e := by exact_mod_cast he
  nlinarith

end ExpLog

section Iso

theorem mem_maximalIdeal_pow_iff_valBall {n : ℕ} {y : 𝒪[K]} :
    y ∈ 𝓂[K] ^ n ↔ (y : K) ∈ valBall K n := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  have hset := hϖ.maximalIdeal_pow_eq_setOfPred_le_v_coe_pow (v := valuation K) n
  have : y ∈ 𝓂[K] ^ n ↔ y ∈ ((𝓂[K] ^ n : Ideal 𝒪[K]) : Set 𝒪[K]) := Iff.rfl
  rw [this, hset, mem_valBall]
  show valuation K (y : K) ≤ valuation K (ϖ : K) ^ n ↔ _
  rw [← map_pow, ← normalizedValuation_le_iff, map_pow, normalizedValuation_uniformizer hϖ,
    ← WithZero.exp_nsmul]
  simp

theorem mem_integer_of_mem_valBall {n : ℤ} (hn : 0 ≤ n) {x : K} (hx : x ∈ valBall K n) :
    x ∈ 𝒪[K] := by
  rw [← normalizedValuation_le_one_iff]
  exact hx.trans (by rw [← WithZero.exp_zero, WithZero.exp_le_exp]; omega)

variable (K) in

noncomputable def valBallEquivMaximalIdealPow (n : ℕ) :
    valBall K n ≃ₜ+ (𝓂[K] ^ n : Ideal 𝒪[K]) where
  toFun x := ⟨⟨x, mem_integer_of_mem_valBall (by positivity) x.2⟩,
    mem_maximalIdeal_pow_iff_valBall.mpr x.2⟩
  invFun y := ⟨((y : 𝒪[K]) : K), mem_maximalIdeal_pow_iff_valBall.mp y.2⟩
  left_inv x := rfl
  right_inv y := rfl
  map_add' x y := rfl
  continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
  continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

variable (p : ℕ) [hp : Fact p.Prime] [CharP 𝓀[K] p] [CharZero K]

theorem one_le_of_lt_sub_one_mul_nat {n : ℕ}
    (hn : (absRamificationIndex K : ℤ) < (p - 1 : ℤ) * n) : 1 ≤ n := by
  have := one_le_of_lt_sub_one_mul p hn
  omega

omit [CharZero K] in
theorem sub_one_mem_valBall_of_mem {n : ℕ} (hn1 : 1 ≤ n) (u : unitFiltrationUnits K n) :
    ((u : Kˣ) : K) - 1 ∈ valBall K n :=
  (mem_unitFiltrationUnits_iff_valBall hn1).mp u.2

noncomputable def logValBallHom (n : ℕ) (hn : (absRamificationIndex K : ℤ) < (p - 1 : ℤ) * n) :
    Additive (unitFiltrationUnits K n) →+ valBall K n where
  toFun u := ⟨logSeries ((((Additive.toMul u : unitFiltrationUnits K n) : Kˣ) : K) - 1),
    logSeries_mem_valBall p
      (sub_one_mem_valBall_of_mem (one_le_of_lt_sub_one_mul_nat p hn) (Additive.toMul u)) hn⟩
  map_zero' := Subtype.ext (by simp [logSeries])
  map_add' u w := by
    have h := (padicLog K).map_add
      (Additive.ofMul ⟨((Additive.toMul u : unitFiltrationUnits K n) : Kˣ),
        unitFiltrationUnits_antitone (one_le_of_lt_sub_one_mul_nat p hn) (Additive.toMul u).2⟩)
      (Additive.ofMul ⟨((Additive.toMul w : unitFiltrationUnits K n) : Kˣ),
        unitFiltrationUnits_antitone (one_le_of_lt_sub_one_mul_nat p hn) (Additive.toMul w).2⟩)
    exact Subtype.ext h

theorem coe_logValBallHom (n : ℕ) (hn : (absRamificationIndex K : ℤ) < (p - 1 : ℤ) * n)
    (u : Additive (unitFiltrationUnits K n)) :
    (logValBallHom p n hn u : K) =
      logSeries ((((Additive.toMul u : unitFiltrationUnits K n) : Kˣ) : K) - 1) := rfl

theorem logValBallHom_injective (n : ℕ) (hn : (absRamificationIndex K : ℤ) < (p - 1 : ℤ) * n) :
    Function.Injective (logValBallHom p n hn) := by
  rw [injective_iff_map_eq_zero]
  intro u hu
  have h := congrArg Subtype.val hu
  rw [coe_logValBallHom] at h
  have hx := eq_zero_of_logSeries_eq_zero p hn
    (sub_one_mem_valBall_of_mem (one_le_of_lt_sub_one_mul_nat p hn) (Additive.toMul u)) h
  apply Additive.toMul.injective
  ext
  simpa [sub_eq_zero] using hx

omit [CharZero K] in
theorem expSeries_ne_zero {n : ℕ} (hn1 : 1 ≤ n) {x : K} (hx : expSeries x - 1 ∈ valBall K n) :
    expSeries x ≠ 0 := by
  intro h
  rw [h, zero_sub, mem_valBall, Valuation.map_neg, map_one, ← WithZero.exp_zero,
    WithZero.exp_le_exp] at hx
  omega

noncomputable def expUnit (n : ℕ) (hn : (absRamificationIndex K : ℤ) < (p - 1 : ℤ) * n)
    (x : valBall K n) : unitFiltrationUnits K n :=
  ⟨Units.mk0 (expSeries (x : K))
    (expSeries_ne_zero (one_le_of_lt_sub_one_mul_nat p hn) (expSeries_sub_one_mem p x.2 hn)),
    (mem_unitFiltrationUnits_iff_valBall (one_le_of_lt_sub_one_mul_nat p hn)).mpr
      (expSeries_sub_one_mem p x.2 hn)⟩

theorem logValBallHom_expUnit (n : ℕ) (hn : (absRamificationIndex K : ℤ) < (p - 1 : ℤ) * n)
    (x : valBall K n) : logValBallHom p n hn (Additive.ofMul (expUnit p n hn x)) = x :=
  Subtype.ext (logSeries_expSeries_sub_one p x.2 hn)

theorem continuous_expSeries_valBall (n : ℕ)
    (hn : (absRamificationIndex K : ℤ) < (p - 1 : ℤ) * n) :
    Continuous fun x : valBall K n ↦ expSeries (x : K) := by
  rw [continuous_iff_continuousAt]
  intro x0
  rw [ContinuousAt, ← tendsto_sub_nhds_zero_iff, tendsto_zero_iff_valBall]
  intro N
  set r : ℤ := max N n
  have hr : (absRamificationIndex K : ℤ) < (p - 1 : ℤ) * r :=
    sub_one_le_of_lt p hn (le_max_right _ _)
  have hopen := (isOpen_valBall r).preimage
    (continuous_subtype_val.sub continuous_const : Continuous fun x : valBall K n ↦ (x : K) - x0)
  filter_upwards [hopen.mem_nhds (by simp)] with x hx
  have hx' : (x : K) - x0 ∈ valBall K r := hx
  have hxn : (x : K) - x0 ∈ valBall K n := valBall_antitone (le_max_right _ _) hx'
  have heq : expSeries (x : K) = expSeries (x0 : K) * expSeries ((x : K) - x0) := by
    rw [← expSeries_add p x0.2 hxn hn, add_sub_cancel]
  have h0 : expSeries (x0 : K) ∈ valBall K 0 := by
    have h1 := valBall_antitone (by positivity : (0 : ℤ) ≤ n) (expSeries_sub_one_mem p x0.2 hn)
    have h2 : (1 : K) ∈ valBall K 0 := by simp [mem_valBall]
    simpa using add_mem h1 h2
  rw [heq, show expSeries (x0 : K) * expSeries ((x : K) - x0) - expSeries (x0 : K) =
    expSeries (x0 : K) * (expSeries ((x : K) - x0) - 1) by ring]
  have hNr : N ≤ 0 + r := by rw [zero_add]; exact le_max_left _ _
  refine valBall_antitone hNr (mul_mem_valBall h0 ?_)
  exact expSeries_sub_one_mem p hx' hr

noncomputable def logValBallEquiv (n : ℕ) (hn : (absRamificationIndex K : ℤ) < (p - 1 : ℤ) * n) :
    Additive (unitFiltrationUnits K n) ≃ₜ+ valBall K n where
  toFun := logValBallHom p n hn
  invFun x := Additive.ofMul (expUnit p n hn x)
  left_inv u := logValBallHom_injective p n hn (logValBallHom_expUnit p n hn _)
  right_inv x := logValBallHom_expUnit p n hn x
  map_add' := map_add _
  continuous_toFun := by
    have hι : Continuous fun u : Additive (unitFiltrationUnits K n) ↦
        (Additive.ofMul (⟨((Additive.toMul u : unitFiltrationUnits K n) : Kˣ),
          unitFiltrationUnits_antitone (one_le_of_lt_sub_one_mul_nat p hn)
            (Additive.toMul u).2⟩ : unitFiltrationUnits K 1)) :=
      continuous_ofMul.comp ((continuous_subtype_val.comp continuous_toMul).subtype_mk _)
    exact (continuous_padicLog.comp hι).subtype_mk _
  continuous_invFun := by
    refine continuous_ofMul.comp (Continuous.subtype_mk ?_ _)
    rw [Units.isEmbedding_val₀.continuous_iff]
    exact continuous_expSeries_valBall p n hn

noncomputable def unitFiltrationLogEquiv (n : ℕ)
    (hn : (absRamificationIndex K : ℤ) < (p - 1 : ℤ) * n) :
    Additive (unitFiltrationUnits K n) ≃ₜ+ (𝓂[K] ^ n : Ideal 𝒪[K]) :=
  (logValBallEquiv p n hn).trans (valBallEquivMaximalIdealPow K n)

theorem expSeries_logSeries {n : ℕ} (hn : (absRamificationIndex K : ℤ) < (p - 1 : ℤ) * n)
    (u : unitFiltrationUnits K n) :
    expSeries (logSeries (((u : Kˣ) : K) - 1)) = ((u : Kˣ) : K) := by
  have := congrArg (fun v ↦ (((Additive.toMul v : unitFiltrationUnits K n) : Kˣ) : K))
    ((logValBallEquiv p n hn).symm_apply_apply (Additive.ofMul u))
  exact this

end Iso

end Sec_PadicExp


/-! ### PrincipalUnitsModule -/
section Sec_PrincipalUnitsModule

open ValuativeRel IsLocalRing Topology Filter
open scoped WithZero

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

section Filtration

variable (K) in

noncomputable def principalFiltration (k : ℕ) : AddSubgroup (Additive (unitFiltrationUnits K 1)) :=
  Subgroup.toAddSubgroup ((unitFiltrationUnits K (k + 1)).comap (unitFiltrationUnits K 1).subtype)

theorem mem_principalFiltration {k : ℕ} {u : Additive (unitFiltrationUnits K 1)} :
    u ∈ principalFiltration K k ↔
      ((((Additive.toMul u : unitFiltrationUnits K 1) : Kˣ) : K) - 1) ∈ valBall K (k + 1) := by
  have := mem_unitFiltrationUnits_iff_valBall (K := K) (n := k + 1) (by omega)
    (x := ((Additive.toMul u : unitFiltrationUnits K 1) : Kˣ))
  push_cast at this
  exact this

theorem principalFiltration_antitone : Antitone (principalFiltration K) := by
  intro j k hjk u hu
  rw [mem_principalFiltration] at hu ⊢
  exact valBall_antitone (by omega) hu

theorem principalFiltration_zero : principalFiltration K 0 = ⊤ := by
  ext u
  simp only [AddSubgroup.mem_top, iff_true, mem_principalFiltration]
  simpa using sub_one_mem_valBall_one (Additive.toMul u)

theorem normalizedValuation_eq_one_of_sub_one_mem {y : K} (hy : y - 1 ∈ valBall K 1) :
    normalizedValuation K y = 1 := by
  have h : normalizedValuation K (y - 1) < 1 := by
    refine lt_of_le_of_lt hy ?_
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
  have := Valuation.map_one_add_of_lt (normalizedValuation K) h
  simpa using this

theorem mem_valBall_zero_of_sub_one_mem {y : K} (hy : y - 1 ∈ valBall K 1) : y ∈ valBall K 0 := by
  rw [mem_valBall, normalizedValuation_eq_one_of_sub_one_mem hy]; simp

theorem eq_zero_of_forall_mem_principalFiltration {w : Additive (unitFiltrationUnits K 1)}
    (h : ∀ k, w ∈ principalFiltration K k) : w = 0 := by
  set y : K := (((Additive.toMul w : unitFiltrationUnits K 1) : Kˣ) : K) - 1
  have hy : y = 0 := by
    by_contra hy0
    have hk := mem_principalFiltration.mp (h (ord y).toNat)
    rw [mem_valBall, normalizedValuation_eq_exp_ord hy0, WithZero.exp_le_exp] at hk
    have := Int.self_le_toNat (ord y)
    omega
  apply Additive.toMul.injective
  ext
  simpa [y, sub_eq_zero] using hy

variable (p : ℕ) [hp : Fact p.Prime] [CharP 𝓀[K] p]

omit hp in
theorem natCast_prime_mem_valBall_one : (p : K) ∈ valBall K 1 := by
  have h : ((p : 𝒪[K]) : 𝒪[K]) ∈ 𝓂[K] ^ 1 := by
    rw [pow_one, ← residue_eq_zero_iff, map_natCast, CharP.cast_eq_zero]
  have := mem_maximalIdeal_pow_iff_valBall.mp h
  simpa using this

theorem pow_prime_sub_one_mem {k : ℤ} (hk : 1 ≤ k) {y : K} (hy : y - 1 ∈ valBall K k) :
    y ^ p - 1 ∈ valBall K (k + 1) := by
  set x := y - 1
  have hyx : y = x + 1 := by ring
  rw [hyx, add_pow, Finset.sum_range_succ']
  simp only [pow_zero, one_pow, mul_one, Nat.choose_zero_right, Nat.cast_one, add_sub_cancel_right]
  refine AddSubgroup.sum_mem _ fun i hi ↦ ?_
  rw [Finset.mem_range] at hi
  rcases Nat.lt_or_ge (i + 1) p with hlt | hge
  · obtain ⟨c, hc⟩ := hp.out.dvd_choose_self (Nat.succ_ne_zero i) hlt
    rw [hc, Nat.cast_mul]
    have h1 : (p : K) * (c : K) ∈ valBall K (1 + 0) :=
      mul_mem_valBall (natCast_prime_mem_valBall_one p)
        (by simpa using intCast_mem_valBall_zero (K := K) (c : ℤ))
    have h2 := mul_mem_valBall (pow_mem_valBall hy (i + 1)) h1
    refine valBall_antitone ?_ h2
    push_cast; nlinarith
  · have hi' : i + 1 = p := by omega
    rw [hi', Nat.choose_self, Nat.cast_one, mul_one]
    refine valBall_antitone ?_ (pow_mem_valBall hy p)
    have : (2 : ℤ) ≤ p := by exact_mod_cast hp.out.two_le
    nlinarith

theorem nsmul_prime_mem_principalFiltration {k : ℕ} {u : Additive (unitFiltrationUnits K 1)}
    (hu : u ∈ principalFiltration K k) : p • u ∈ principalFiltration K (k + 1) := by
  rw [mem_principalFiltration] at hu ⊢
  have := pow_prime_sub_one_mem p (by omega) hu
  simpa using this

theorem nsmul_prime_pow_mem_principalFiltration {k : ℕ} {u : Additive (unitFiltrationUnits K 1)}
    (hu : u ∈ principalFiltration K k) (j : ℕ) : p ^ j • u ∈ principalFiltration K (k + j) := by
  induction j with
  | zero => simpa using hu
  | succ j ih =>
    rw [show p ^ (j + 1) • u = p • (p ^ j • u) by rw [smul_smul, ← pow_succ'], ← add_assoc]
    exact nsmul_prime_mem_principalFiltration p ih

theorem zsmul_mem_principalFiltration_of_dvd {k : ℕ} {c : ℤ} (hc : (p ^ k : ℤ) ∣ c)
    (u : Additive (unitFiltrationUnits K 1)) : c • u ∈ principalFiltration K k := by
  obtain ⟨d, rfl⟩ := hc
  rw [mul_comm, mul_zsmul]
  refine zsmul_mem ?_ d
  have := nsmul_prime_pow_mem_principalFiltration p
    (by rw [principalFiltration_zero]; trivial : u ∈ principalFiltration K 0) k
  rw [zero_add] at this
  exact_mod_cast this

end Filtration

section Complete

theorem exists_forall_sub_mem_principalFiltration {s : ℕ → Additive (unitFiltrationUnits K 1)}
    (hs : ∀ k, s (k + 1) - s k ∈ principalFiltration K k) :
    ∃ l, ∀ k, l - s k ∈ principalFiltration K k := by
  set σ : ℕ → K := fun k ↦ (((Additive.toMul (s k) : unitFiltrationUnits K 1) : Kˣ) : K)
  have hσ1 : ∀ k, σ k - 1 ∈ valBall K 1 := fun k ↦ sub_one_mem_valBall_one (Additive.toMul (s k))
  have hσ0 : ∀ k, σ k ≠ 0 := fun k ↦ Units.ne_zero _
  have hquot : ∀ k : ℕ, σ (k + 1) / σ k - 1 ∈ valBall K (k + 1) := by
    intro k
    have := mem_principalFiltration.mp (hs k)
    simpa [σ, toMul_sub, div_eq_mul_inv] using this
  set f : ℕ → K := fun j ↦ σ (j + 1) - σ j
  have hf : ∀ j : ℕ, f j ∈ valBall K (j + 1) := by
    intro j
    have h : f j = σ j * (σ (j + 1) / σ j - 1) := by
      simp only [f]; field_simp [hσ0 j]
    rw [h]
    simpa using mul_mem_valBall (mem_valBall_zero_of_sub_one_mem (hσ1 j)) (hquot j)
  have hsum : Summable f := by
    refine summable_of_tendsto_zero (tendsto_zero_iff_valBall.mpr fun N ↦ ?_)
    rw [eventually_atTop]
    exact ⟨N.toNat, fun j hj ↦ valBall_antitone (by have := Int.self_le_toNat N; omega) (hf j)⟩
  set L := σ 0 + ∑' j, f j
  have hL : ∀ k : ℕ, L - σ k = ∑' j, f (j + k) := by
    intro k
    have h1 := hsum.sum_add_tsum_nat_add k
    have h2 : ∑ i ∈ Finset.range k, f i = σ k - σ 0 := Finset.sum_range_sub σ k
    simp only [L]
    rw [← h1, h2]
    ring
  have hLk : ∀ k : ℕ, L - σ k ∈ valBall K (k + 1) := by
    intro k
    rw [hL k]
    exact tsum_mem_valBall fun j ↦ valBall_antitone (by omega) (hf (j + k))
  have hL1 : L - 1 ∈ valBall K 1 := by
    have := add_mem (hLk 0) (hσ1 0)
    simpa using this
  have hL0 : L ≠ 0 := by
    intro h
    have := normalizedValuation_eq_one_of_sub_one_mem hL1
    rw [h, map_zero] at this
    exact zero_ne_one this
  refine ⟨Additive.ofMul ⟨Units.mk0 L hL0,
    (mem_unitFiltrationUnits_iff_valBall le_rfl).mpr (by simpa using hL1)⟩, fun k ↦ ?_⟩
  rw [mem_principalFiltration]
  have heq : (((Additive.toMul (Additive.ofMul ⟨Units.mk0 L hL0,
      (mem_unitFiltrationUnits_iff_valBall le_rfl).mpr (by simpa using hL1)⟩ - s k) :
        unitFiltrationUnits K 1) : Kˣ) : K) - 1 = (L - σ k) * (σ k)⁻¹ := by
    simp only [toMul_sub, toMul_ofMul]
    simp [σ, div_eq_mul_inv]
    field_simp [hσ0 k]
  rw [heq]
  have hinv : (σ k)⁻¹ ∈ valBall K 0 := by
    rw [mem_valBall, map_inv₀, normalizedValuation_eq_one_of_sub_one_mem (hσ1 k)]; simp
  simpa using mul_mem_valBall (hLk k) hinv

end Complete

section Module

variable (p : ℕ) [hp : Fact p.Prime]

theorem padicInt_dvd_intCast_iff {k : ℕ} {c : ℤ} :
    (p : ℤ_[p]) ^ k ∣ (c : ℤ_[p]) ↔ ((p : ℤ) ^ k) ∣ c := by
  rw [← Ideal.mem_span_singleton, ← PadicInt.norm_le_pow_iff_mem_span_pow,
    PadicInt.norm_int_le_pow_iff_dvd]

theorem intCast_dvd_sub_of_dvd_sub {k : ℕ} {a : ℤ_[p]} {c c' : ℤ} (h : (p : ℤ_[p]) ^ k ∣ a - c)
    (h' : (p : ℤ_[p]) ^ k ∣ a - c') : ((p : ℤ) ^ k) ∣ c' - c := by
  rw [← padicInt_dvd_intCast_iff]
  have := dvd_sub h h'
  push_cast
  convert this using 1
  ring

theorem dvd_sub_appr (k : ℕ) (a : ℤ_[p]) : (p : ℤ_[p]) ^ k ∣ a - ((a.appr k : ℕ) : ℤ) := by
  rw [← Ideal.mem_span_singleton]
  simpa using PadicInt.appr_spec k a

variable [CharP 𝓀[K] p]

theorem exists_padicInt_pow (a : ℤ_[p]) (u : Additive (unitFiltrationUnits K 1)) :
    ∃ l : Additive (unitFiltrationUnits K 1), ∀ (k : ℕ) (c : ℤ), (p : ℤ_[p]) ^ k ∣ a - c →
      l - c • u ∈ principalFiltration K k := by
  set s : ℕ → Additive (unitFiltrationUnits K 1) := fun k ↦ ((a.appr k : ℕ) : ℤ) • u
  have hs : ∀ k, s (k + 1) - s k ∈ principalFiltration K k := by
    intro k
    simp only [s]
    rw [show ((a.appr (k + 1) : ℕ) : ℤ) • u - ((a.appr k : ℕ) : ℤ) • u =
      (((a.appr (k + 1) : ℕ) : ℤ) - ((a.appr k : ℕ) : ℤ)) • u by rw [sub_zsmul]; abel]
    refine zsmul_mem_principalFiltration_of_dvd p ?_ u
    have h1 := dvd_sub_appr p (k + 1) a
    have h1' : (p : ℤ_[p]) ^ k ∣ a - ((a.appr (k + 1) : ℕ) : ℤ) :=
      (pow_dvd_pow _ (Nat.le_succ k)).trans h1
    have := intCast_dvd_sub_of_dvd_sub p (dvd_sub_appr p k a) h1'
    exact_mod_cast this
  obtain ⟨l, hl⟩ := exists_forall_sub_mem_principalFiltration hs
  refine ⟨l, fun k c hc ↦ ?_⟩
  have h := intCast_dvd_sub_of_dvd_sub p hc (dvd_sub_appr p k a)
  have : l - c • u = (l - s k) + (((a.appr k : ℕ) : ℤ) - c) • u := by
    simp only [s, sub_zsmul]; abel
  rw [this]
  exact add_mem (hl k) (zsmul_mem_principalFiltration_of_dvd p h u)

noncomputable def padicIntSMul (a : ℤ_[p]) (u : Additive (unitFiltrationUnits K 1)) :
    Additive (unitFiltrationUnits K 1) :=
  Classical.choose (exists_padicInt_pow p a u)

theorem padicIntSMul_spec (a : ℤ_[p]) (u : Additive (unitFiltrationUnits K 1)) {k : ℕ} {c : ℤ}
    (hc : (p : ℤ_[p]) ^ k ∣ a - c) : padicIntSMul p a u - c • u ∈ principalFiltration K k :=
  Classical.choose_spec (exists_padicInt_pow p a u) k c hc

theorem padicIntSMul_eq_of {a : ℤ_[p]} {u l : Additive (unitFiltrationUnits K 1)}
    (h : ∀ k : ℕ, ∃ c : ℤ, (p : ℤ_[p]) ^ k ∣ a - c ∧ l - c • u ∈ principalFiltration K k) :
    padicIntSMul p a u = l := by
  refine (sub_eq_zero.mp (eq_zero_of_forall_mem_principalFiltration fun k ↦ ?_))
  obtain ⟨c, hc, hl⟩ := h k
  have := sub_mem (padicIntSMul_spec p a u hc) hl
  simpa using this

noncomputable instance instModulePadicInt : Module ℤ_[p] (Additive (unitFiltrationUnits K 1)) where
  smul := padicIntSMul p
  one_smul u := padicIntSMul_eq_of p fun k ↦ ⟨1, by simp, by simp⟩
  mul_smul a b u := by
    show padicIntSMul p (a * b) u = padicIntSMul p a (padicIntSMul p b u)
    refine padicIntSMul_eq_of p fun k ↦ ⟨((a.appr k : ℕ) : ℤ) * ((b.appr k : ℕ) : ℤ), ?_, ?_⟩
    · have ha := dvd_sub_appr p k a
      have hb := dvd_sub_appr p k b
      have : a * b - (((((a.appr k : ℕ) : ℤ) * ((b.appr k : ℕ) : ℤ) : ℤ)) : ℤ_[p]) =
          a * (b - ((b.appr k : ℕ) : ℤ)) + ((b.appr k : ℕ) : ℤ) * (a - ((a.appr k : ℕ) : ℤ)) := by
        push_cast; ring
      rw [this]
      exact dvd_add (dvd_mul_of_dvd_right hb _) (dvd_mul_of_dvd_right ha _)
    · have h1 := padicIntSMul_spec p a (padicIntSMul p b u) (dvd_sub_appr p k a)
      have h2 := padicIntSMul_spec p b u (dvd_sub_appr p k b)
      have : padicIntSMul p a (padicIntSMul p b u) -
          (((a.appr k : ℕ) : ℤ) * ((b.appr k : ℕ) : ℤ)) • u =
          (padicIntSMul p a (padicIntSMul p b u) - ((a.appr k : ℕ) : ℤ) • padicIntSMul p b u) +
            ((a.appr k : ℕ) : ℤ) • (padicIntSMul p b u - ((b.appr k : ℕ) : ℤ) • u) := by
        rw [mul_zsmul, zsmul_sub]; abel
      rw [this]
      exact add_mem h1 (zsmul_mem h2 _)
  smul_zero a := padicIntSMul_eq_of p fun k ↦ ⟨((a.appr k : ℕ) : ℤ), dvd_sub_appr p k a, by simp⟩
  smul_add a u v := by
    show padicIntSMul p a (u + v) = padicIntSMul p a u + padicIntSMul p a v
    refine padicIntSMul_eq_of p fun k ↦ ⟨((a.appr k : ℕ) : ℤ), dvd_sub_appr p k a, ?_⟩
    have h1 := padicIntSMul_spec p a u (dvd_sub_appr p k a)
    have h2 := padicIntSMul_spec p a v (dvd_sub_appr p k a)
    have : padicIntSMul p a u + padicIntSMul p a v - ((a.appr k : ℕ) : ℤ) • (u + v) =
        (padicIntSMul p a u - ((a.appr k : ℕ) : ℤ) • u) +
          (padicIntSMul p a v - ((a.appr k : ℕ) : ℤ) • v) := by
      rw [zsmul_add]; abel
    rw [this]
    exact add_mem h1 h2
  add_smul a b u := by
    show padicIntSMul p (a + b) u = padicIntSMul p a u + padicIntSMul p b u
    refine padicIntSMul_eq_of p fun k ↦ ⟨((a.appr k : ℕ) : ℤ) + ((b.appr k : ℕ) : ℤ), ?_, ?_⟩
    · have := dvd_add (dvd_sub_appr p k a) (dvd_sub_appr p k b)
      convert this using 1
      push_cast; ring
    · have h1 := padicIntSMul_spec p a u (dvd_sub_appr p k a)
      have h2 := padicIntSMul_spec p b u (dvd_sub_appr p k b)
      have : padicIntSMul p a u + padicIntSMul p b u -
          (((a.appr k : ℕ) : ℤ) + ((b.appr k : ℕ) : ℤ)) • u =
          (padicIntSMul p a u - ((a.appr k : ℕ) : ℤ) • u) +
            (padicIntSMul p b u - ((b.appr k : ℕ) : ℤ) • u) := by
        rw [add_zsmul]; abel
      rw [this]
      exact add_mem h1 h2
  zero_smul u := padicIntSMul_eq_of p fun k ↦ ⟨0, by simp, by simp⟩

end Module

section ModuleProps

variable (p : ℕ) [hp : Fact p.Prime] [CharP 𝓀[K] p]

theorem padicInt_smul_def (a : ℤ_[p]) (u : Additive (unitFiltrationUnits K 1)) :
    a • u = padicIntSMul p a u := rfl

theorem smul_sub_intCast_smul_mem {a : ℤ_[p]} {k : ℕ} {c : ℤ} (hc : (p : ℤ_[p]) ^ k ∣ a - c)
    (u : Additive (unitFiltrationUnits K 1)) : a • u - c • u ∈ principalFiltration K k :=
  padicIntSMul_spec p a u hc

theorem intCast_smul (c : ℤ) (u : Additive (unitFiltrationUnits K 1)) :
    ((c : ℤ_[p])) • u = c • u :=
  padicIntSMul_eq_of p fun k ↦ ⟨c, by simp, by simp⟩

theorem natCast_smul (n : ℕ) (u : Additive (unitFiltrationUnits K 1)) :
    ((n : ℤ_[p])) • u = n • u := by
  have := intCast_smul p (n : ℤ) u
  simpa using this

theorem smul_mem_of_dvd {a : ℤ_[p]} {k : ℕ} (ha : (p : ℤ_[p]) ^ k ∣ a)
    (u : Additive (unitFiltrationUnits K 1)) : a • u ∈ principalFiltration K k := by
  have := smul_sub_intCast_smul_mem p (c := 0) (by simpa using ha) u
  simpa using this

theorem smul_mem_principalFiltration (a : ℤ_[p]) {k : ℕ} {u : Additive (unitFiltrationUnits K 1)}
    (hu : u ∈ principalFiltration K k) : a • u ∈ principalFiltration K k := by
  have h1 := smul_sub_intCast_smul_mem p (dvd_sub_appr p k a) u
  have h2 : ((a.appr k : ℕ) : ℤ) • u ∈ principalFiltration K k := zsmul_mem hu _
  simpa using add_mem h1 h2

theorem hasBasis_nhds_zero_principalFiltration :
    (𝓝 (0 : Additive (unitFiltrationUnits K 1))).HasBasis (fun _ ↦ True)
      (fun k ↦ (principalFiltration K k : Set (Additive (unitFiltrationUnits K 1)))) := by
  have h1 : 𝓝 (0 : Additive (unitFiltrationUnits K 1)) =
      Filter.comap (fun u : Additive (unitFiltrationUnits K 1) ↦
        ((Additive.toMul u : unitFiltrationUnits K 1) : Kˣ)) (𝓝 1) :=
    nhds_subtype _ (1 : unitFiltrationUnits K 1)
  rw [h1]
  refine (hasBasis_nhds_one_unitFiltrationUnits.comap _).to_hasBasis
    (fun n _ ↦ ⟨n, trivial, fun u hu ↦ unitFiltrationUnits_antitone (Nat.le_succ n) hu⟩)
    (fun k _ ↦ ⟨k + 1, trivial, fun u hu ↦ hu⟩)

theorem principalFiltration_mem_nhds (k : ℕ) :
    (principalFiltration K k : Set (Additive (unitFiltrationUnits K 1))) ∈ 𝓝 0 :=
  hasBasis_nhds_zero_principalFiltration.mem_of_mem trivial

instance continuousSMul_padicInt_principalUnits : ContinuousSMul ℤ_[p] (Additive (unitFiltrationUnits K 1)) := by
  refine ⟨continuous_iff_continuousAt.mpr fun x ↦ ?_⟩
  obtain ⟨a0, u0⟩ := x
  rw [ContinuousAt, ← tendsto_sub_nhds_zero_iff,
    hasBasis_nhds_zero_principalFiltration.tendsto_right_iff]
  intro k _
  have h1 : {a : ℤ_[p] | (p : ℤ_[p]) ^ k ∣ a - a0} ∈ 𝓝 a0 := by
    have hr : (0 : ℝ) < (p : ℝ) ^ (-(k : ℤ)) := by
      have : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
      positivity
    refine Filter.mem_of_superset (Metric.closedBall_mem_nhds a0 hr) fun a ha ↦ ?_
    rw [Metric.mem_closedBall, dist_eq_norm, PadicInt.norm_le_pow_iff_mem_span_pow,
      Ideal.mem_span_singleton] at ha
    exact ha
  have h2 : {u : Additive (unitFiltrationUnits K 1) | u - u0 ∈ principalFiltration K k} ∈ 𝓝 u0 := by
    have ht : Tendsto (fun u : Additive (unitFiltrationUnits K 1) ↦ u - u0) (𝓝 u0) (𝓝 0) := by
      have : Tendsto (fun u : Additive (unitFiltrationUnits K 1) ↦ u - u0) (𝓝 u0) (𝓝 (u0 - u0)) :=
        tendsto_id.sub tendsto_const_nhds
      rwa [sub_self] at this
    exact ht (principalFiltration_mem_nhds k)
  filter_upwards [prod_mem_nhds h1 h2] with x hx
  obtain ⟨a, u⟩ := x
  obtain ⟨ha, hu⟩ := hx
  have : a • u - a0 • u0 = (a - a0) • u + a0 • (u - u0) := by rw [sub_smul, smul_sub]; abel
  show a • u - a0 • u0 ∈ principalFiltration K k
  rw [this]
  exact add_mem (smul_mem_of_dvd p ha u) (smul_mem_principalFiltration p a0 hu)

end ModuleProps

end Sec_PrincipalUnitsModule


/-! ### PadicLogLinear -/
section Sec_PadicLogLinear

open ValuativeRel IsLocalRing Topology Filter
open scoped WithZero

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

theorem eq_zero_of_forall_mem_valBall {y : K} (h : ∀ N : ℤ, y ∈ valBall K N) : y = 0 := by
  by_contra hy
  have := h (ord y + 1)
  rw [mem_valBall, normalizedValuation_eq_exp_ord hy, WithZero.exp_le_exp] at this
  omega

theorem exists_mem_valBall (y : K) : ∃ M : ℤ, y ∈ valBall K M := by
  by_cases hy : y = 0
  · exact ⟨0, by simp [hy]⟩
  · exact ⟨ord y, by rw [mem_valBall, normalizedValuation_eq_exp_ord hy]⟩

variable (p : ℕ) [hp : Fact p.Prime] [CharP 𝓀[K] p] [CharZero K]

theorem padicHom_padicInt_mem_valBall_zero (t : ℤ_[p]) :
    CharZero.padicHom K p (t : ℚ_[p]) ∈ valBall K 0 := by
  rw [mem_valBall, neg_zero, WithZero.exp_zero, ← map_one (normalizedValuation K),
    normalizedValuation_le_iff, map_one]
  exact CharZero.valuation_padicHom_padicInt_le_one K p t

include p in

theorem padicLog_mem_valBall_of_mem {k : ℕ} (hk : absRamificationIndex K ≤ k)
    {w : Additive (unitFiltrationUnits K 1)} (hw : w ∈ principalFiltration K k) :
    padicLog K w ∈ valBall K (k + 1) := by
  rw [mem_principalFiltration] at hw
  rw [padicLog_apply]
  refine logSeries_mem_valBall p hw ?_
  have hp2 : (2 : ℤ) ≤ p := by exact_mod_cast hp.out.two_le
  have : (absRamificationIndex K : ℤ) ≤ k := by exact_mod_cast hk
  nlinarith

theorem padicLog_smul (a : ℤ_[p]) (u : Additive (unitFiltrationUnits K 1)) :
    padicLog K (a • u) = CharZero.padicHom K p (a : ℚ_[p]) * padicLog K u := by
  rw [← sub_eq_zero]
  refine eq_zero_of_forall_mem_valBall fun N ↦ ?_
  set e := absRamificationIndex K
  have he := one_le_absRamificationIndex (K := K) p
  obtain ⟨M, hM⟩ := exists_mem_valBall (padicLog K u)
  set k : ℕ := N.toNat + M.natAbs + e + 1 with hk_def
  set c : ℤ := ((a.appr k : ℕ) : ℤ)
  have hac := dvd_sub_appr p k a
  obtain ⟨t, ht⟩ := hac
  have hw := smul_sub_intCast_smul_mem p (dvd_sub_appr p k a) u
  have h1 := padicLog_mem_valBall_of_mem p (by omega : e ≤ k) hw
  rw [map_sub, map_zsmul, zsmul_eq_mul] at h1
  have h2 : CharZero.padicHom K p (a : ℚ_[p]) - (c : K) =
      ((p ^ k : ℕ) : K) * CharZero.padicHom K p (t : ℚ_[p]) := by
    have := congrArg (fun z : ℤ_[p] ↦ CharZero.padicHom K p (z : ℚ_[p])) ht
    simp only [PadicInt.coe_sub, PadicInt.coe_intCast, map_sub, map_intCast, PadicInt.coe_mul,
      PadicInt.coe_pow, PadicInt.coe_natCast, map_mul, map_pow, map_natCast] at this
    rw [this]; push_cast; ring
  have h3 : (CharZero.padicHom K p (a : ℚ_[p]) - (c : K)) * padicLog K u ∈
      valBall K (e * k + 0 + M) := by
    rw [h2]
    exact mul_mem_valBall (mul_mem_valBall (natCast_prime_pow_mem_valBall p k)
      (padicHom_padicInt_mem_valBall_zero p t)) hM
  have heq : padicLog K (a • u) - CharZero.padicHom K p (a : ℚ_[p]) * padicLog K u =
      (padicLog K (a • u) - (c : K) * padicLog K u) -
        (CharZero.padicHom K p (a : ℚ_[p]) - (c : K)) * padicLog K u := by ring
  rw [heq]
  have hNt := Int.self_le_toNat N
  have hMa := neg_abs_le M
  have hMa' := abs_nonneg M
  have hN1 : N ≤ (k : ℤ) + 1 := by rw [hk_def]; push_cast; omega
  have hN2 : N ≤ (e : ℤ) * k + 0 + M := by
    have : (k : ℤ) ≤ e * k := by
      have : (1 : ℤ) ≤ e := by exact_mod_cast he
      nlinarith [(by positivity : (0 : ℤ) ≤ k)]
    rw [hk_def] at this ⊢; push_cast at this ⊢; omega
  exact sub_mem (valBall_antitone hN1 h1) (valBall_antitone hN2 h3)

end Sec_PadicLogLinear


/-! ### PrincipalUnitsRank -/
section Sec_PrincipalUnitsRank

open ValuativeRel IsLocalRing Topology Filter
open scoped WithZero

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

namespace PadicRank

variable (p : ℕ) [hp : Fact p.Prime]

theorem mem_integer_padic_iff (x : ℚ_[p]) : x ∈ 𝒪[ℚ_[p]] ↔ ‖x‖ ≤ 1 := by
  rw [Valuation.mem_integer_iff, ← map_one (valuation ℚ_[p]), ← Valuation.vle_iff_le,
    Valuation.Compatible.vle_iff_le (v := Padic.mulValuation),
    RHDirect.CFT.LocalField.Padic.mulValuation_le_iff_norm_le, norm_one]

noncomputable def padicIntEquivInteger : ℤ_[p] ≃+* 𝒪[ℚ_[p]] where
  toFun x := ⟨x, (mem_integer_padic_iff p x).mpr x.2⟩
  invFun y := ⟨y, (mem_integer_padic_iff p y).mp y.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

variable [CharP 𝓀[K] p] [CharZero K]

variable (K) in

noncomputable def padicIntHom : ℤ_[p] →+* K :=
  (CharZero.padicHom K p).comp PadicInt.Coe.ringHom

theorem padicIntHom_mem (a : ℤ_[p]) : padicIntHom K p a ∈ 𝒪[K] :=
  CharZero.valuation_padicHom_padicInt_le_one K p a

variable (K) in

noncomputable def padicIntHomInteger : ℤ_[p] →+* 𝒪[K] :=
  (padicIntHom K p).codRestrict 𝒪[K] (padicIntHom_mem p)

variable (K) in

noncomputable abbrev algebraK : Algebra ℤ_[p] K := (padicIntHom K p).toAlgebra

variable (K) in

noncomputable abbrev algebraInteger : Algebra ℤ_[p] 𝒪[K] := (padicIntHomInteger K p).toAlgebra

attribute [local instance] algebraK algebraInteger

theorem finite_and_finrank_integer :
    Module.Finite ℤ_[p] 𝒪[K] ∧ Module.finrank ℤ_[p] 𝒪[K] =
      (letI := (CharZero.padicHom K p).toAlgebra; Module.finrank ℚ_[p] K) := by
  let := (CharZero.padicHom K p).toAlgebra
  have : ValuativeExtension ℚ_[p] K := ⟨CharZero.padicHom_vle_iff K p⟩
  have : FiniteDimensional ℚ_[p] K := CharZero.finiteDimensional_padicHom K p
  have hfin : Module.Finite 𝒪[ℚ_[p]] 𝒪[K] := finite_integer ℚ_[p] K
  have hrank := finrank_integer ℚ_[p] K
  have he : (algebraMap ℤ_[p] 𝒪[K]).comp ((padicIntEquivInteger p).symm : 𝒪[ℚ_[p]] →+* ℤ_[p]) =
      (RingEquiv.refl 𝒪[K] : 𝒪[K] →+* 𝒪[K]).comp (algebraMap 𝒪[ℚ_[p]] 𝒪[K]) := by
    ext x
    rfl
  refine ⟨Module.Finite.of_equiv_equiv (padicIntEquivInteger p).symm (RingEquiv.refl _) he, ?_⟩
  rw [← hrank]
  have := rank_eq_of_equiv_equiv (R := ℤ_[p]) (R' := 𝒪[ℚ_[p]]) (M := 𝒪[K]) (M₁ := 𝒪[K])
    (padicIntEquivInteger p) (AddEquiv.refl _) (padicIntEquivInteger p).bijective
    (fun r m ↦ rfl)
  exact congrArg Cardinal.toNat this

theorem padicIntHom_mem_valBall_zero (a : ℤ_[p]) : padicIntHom K p a ∈ valBall K 0 :=
  padicHom_padicInt_mem_valBall_zero p a

variable (K) in

noncomputable def valBallSubmodule (m : ℤ) : Submodule ℤ_[p] K where
  carrier := valBall K m
  add_mem' := add_mem
  zero_mem' := zero_mem _
  smul_mem' a x hx := by
    rw [Algebra.smul_def]
    have h := mul_mem_valBall (padicIntHom_mem_valBall_zero p a) hx
    rw [zero_add] at h
    exact h

theorem mem_valBallSubmodule {m : ℤ} {x : K} : x ∈ valBallSubmodule K p m ↔ x ∈ valBall K m :=
  Iff.rfl

variable (K) in

noncomputable def valBallSubmoduleZeroEquiv : valBallSubmodule K p 0 ≃ₗ[ℤ_[p]] 𝒪[K] where
  toFun x := ⟨x, mem_integer_of_mem_valBall le_rfl x.2⟩
  invFun y := ⟨y, by
    rw [mem_valBallSubmodule, mem_valBall, neg_zero, WithZero.exp_zero,
      normalizedValuation_le_one_iff]; exact y.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable (K) in

noncomputable def valBallSubmoduleEquiv (m : ℤ) :
    valBallSubmodule K p 0 ≃ₗ[ℤ_[p]] valBallSubmodule K p m :=
  have hy := exists_normalizedValuation_eq K (-m)
  let y := hy.choose
  have hy0 : y ≠ 0 := by
    intro h
    have := hy.choose_spec
    rw [show hy.choose = y from rfl, h, map_zero] at this
    exact WithZero.exp_ne_zero this.symm
  { toFun x := ⟨y * x, (mem_valBallSubmodule p).mpr (by
      have := mul_mem_valBall (show y ∈ valBall K m by
        rw [mem_valBall, show y = hy.choose from rfl, hy.choose_spec]) x.2
      simpa using this)⟩
    invFun x := ⟨y⁻¹ * x, (mem_valBallSubmodule p).mpr (by
      have := mul_mem_valBall (show y⁻¹ ∈ valBall K (-m) by
        rw [mem_valBall, map_inv₀, show y = hy.choose from rfl, hy.choose_spec,
          ← WithZero.exp_neg]) x.2
      simpa using this)⟩
    left_inv x := by ext; simp [hy0]
    right_inv x := by ext; simp [hy0]
    map_add' x x' := by ext; simp [mul_add]
    map_smul' a x := by
      ext
      simp only [SetLike.val_smul, Algebra.smul_def, RingHom.id_apply]
      ring }

theorem finite_and_finrank_valBallSubmodule (m : ℤ) :
    Module.Finite ℤ_[p] (valBallSubmodule K p m) ∧ Module.finrank ℤ_[p] (valBallSubmodule K p m) =
      (letI := (CharZero.padicHom K p).toAlgebra; Module.finrank ℚ_[p] K) := by
  obtain ⟨h1, h2⟩ := finite_and_finrank_integer (K := K) p
  have e := (valBallSubmoduleEquiv K p m).symm.trans (valBallSubmoduleZeroEquiv K p)
  exact ⟨Module.Finite.equiv e.symm, e.finrank_eq.trans h2⟩

theorem rank_valBallSubmodule (m : ℤ) :
    Module.rank ℤ_[p] (valBallSubmodule K p m) =
      (letI := (CharZero.padicHom K p).toAlgebra; Module.finrank ℚ_[p] K) := by
  obtain ⟨h1, h2⟩ := finite_and_finrank_valBallSubmodule (K := K) p m
  rw [← h2]
  exact (Cardinal.cast_toNat_of_lt_aleph0 (Module.rank_lt_aleph0 _ _)).symm

variable (K) in

noncomputable def padicLogLinear : Additive (unitFiltrationUnits K 1) →ₗ[ℤ_[p]] K where
  toFun := padicLog K
  map_add' := map_add _
  map_smul' a u := by
    rw [padicLog_smul p a u, RingHom.id_apply, Algebra.smul_def]
    rfl

omit [CharZero K] in
theorem mem_principalFiltration_zero (u : Additive (unitFiltrationUnits K 1)) :
    u ∈ principalFiltration K 0 := by
  rw [principalFiltration_zero]; trivial

theorem padicLog_nsmul_mem (u : Additive (unitFiltrationUnits K 1)) :
    padicLog K (p ^ absRamificationIndex K • u) ∈ valBall K (absRamificationIndex K + 1) := by
  have := nsmul_prime_pow_mem_principalFiltration p (mem_principalFiltration_zero u)
    (absRamificationIndex K)
  rw [zero_add] at this
  exact_mod_cast padicLog_mem_valBall_of_mem p le_rfl this

include p in

theorem padicLog_mem_valBall_bound (u : Additive (unitFiltrationUnits K 1)) :
    padicLog K u ∈ valBall K (absRamificationIndex K + 1 -
      absRamificationIndex K * absRamificationIndex K) := by
  set e := absRamificationIndex K
  have h := padicLog_nsmul_mem p u
  rw [map_nsmul, nsmul_eq_mul] at h
  have hp0 : ((p ^ e : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr (pow_ne_zero _ hp.out.ne_zero)
  have hinv : (((p ^ e : ℕ) : K))⁻¹ ∈ valBall K (-(e * e : ℤ)) := by
    rw [mem_valBall, map_inv₀, Nat.cast_pow, map_pow, normalizedValuation_natCast_prime p,
      ← WithZero.exp_nsmul, ← WithZero.exp_neg]
    simp
    exact le_rfl
  have := mul_mem_valBall hinv h
  push_cast at this hp0
  rw [← mul_assoc, inv_mul_cancel₀ hp0, one_mul] at this
  convert this using 2
  ring

theorem range_padicLogLinear_le : LinearMap.range (padicLogLinear K p) ≤
    valBallSubmodule K p (absRamificationIndex K + 1 -
      absRamificationIndex K * absRamificationIndex K) := by
  rintro _ ⟨u, rfl⟩
  exact padicLog_mem_valBall_bound p u

omit [CharP 𝓀[K] p] [CharZero K] in
theorem lt_sub_one_mul_succ : (absRamificationIndex K : ℤ) <
    (p - 1 : ℤ) * ((absRamificationIndex K + 1 : ℕ) : ℤ) := by
  have hp2 : (2 : ℤ) ≤ p := by exact_mod_cast hp.out.two_le
  push_cast
  nlinarith

theorem valBallSubmodule_le_range : valBallSubmodule K p ((absRamificationIndex K + 1 : ℕ) : ℤ) ≤
    LinearMap.range (padicLogLinear K p) := by
  intro y hy
  set n := absRamificationIndex K + 1
  have hn := lt_sub_one_mul_succ (K := K) p
  set w := (logValBallEquiv p n hn).symm ⟨y, hy⟩
  have h1 : 1 ≤ n := by omega
  refine ⟨Additive.ofMul ⟨((Additive.toMul w : unitFiltrationUnits K n) : Kˣ),
    unitFiltrationUnits_antitone h1 (Additive.toMul w).2⟩, ?_⟩
  have := congrArg Subtype.val ((logValBallEquiv p n hn).apply_symm_apply ⟨y, hy⟩)
  exact this

theorem nsmul_eq_zero_of_padicLog_eq_zero {u : Additive (unitFiltrationUnits K 1)}
    (hu : padicLog K u = 0) : p ^ absRamificationIndex K • u = 0 := by
  set e := absRamificationIndex K
  have hw := nsmul_prime_pow_mem_principalFiltration p (mem_principalFiltration_zero u) e
  rw [zero_add, mem_principalFiltration] at hw
  have hlog : logSeries ((((Additive.toMul (p ^ e • u) : unitFiltrationUnits K 1) : Kˣ) : K) - 1)
      = 0 := by
    rw [← padicLog_apply, map_nsmul, hu, smul_zero]
  have := eq_zero_of_logSeries_eq_zero p (by exact_mod_cast lt_sub_one_mul_succ (K := K) p) hw hlog
  apply Additive.toMul.injective
  ext
  simpa [sub_eq_zero] using this

theorem finite_ker_padicLog : Finite (LinearMap.ker (padicLogLinear K p)) := by
  set e := absRamificationIndex K
  let f : LinearMap.ker (padicLogLinear K p) → rootsOfUnity (p ^ e) K := fun u ↦
    ⟨((Additive.toMul (u : Additive (unitFiltrationUnits K 1)) : unitFiltrationUnits K 1) : Kˣ), by
      have h := nsmul_eq_zero_of_padicLog_eq_zero p (LinearMap.mem_ker.mp u.2)
      have := congrArg (fun v : Additive (unitFiltrationUnits K 1) ↦
        ((Additive.toMul v : unitFiltrationUnits K 1) : Kˣ)) h
      simpa [mem_rootsOfUnity] using this⟩
  refine Finite.of_injective f fun u v huv ↦ ?_
  have := congrArg (fun z : rootsOfUnity (p ^ e) K ↦ (z : Kˣ)) huv
  exact Subtype.ext (Additive.toMul.injective (Subtype.ext this))

theorem fg_ker_padicLogLinear : (LinearMap.ker (padicLogLinear K p)).FG := by
  have := finite_ker_padicLog (K := K) p
  have hfin : (LinearMap.ker (padicLogLinear K p) : Set (Additive (unitFiltrationUnits K 1))).Finite :=
    Set.toFinite _
  refine ⟨hfin.toFinset, ?_⟩
  rw [Set.Finite.coe_toFinset, Submodule.span_eq]

theorem fg_range_padicLogLinear : (LinearMap.range (padicLogLinear K p)).FG := by
  set c : ℤ := absRamificationIndex K + 1 - absRamificationIndex K * absRamificationIndex K
  have : Module.Finite ℤ_[p] (valBallSubmodule K p c) :=
    (finite_and_finrank_valBallSubmodule (K := K) p c).1
  have : IsNoetherian ℤ_[p] (valBallSubmodule K p c) := inferInstance
  have : IsNoetherian ℤ_[p] (LinearMap.range (padicLogLinear K p)) :=
    isNoetherian_of_le (range_padicLogLinear_le p)
  exact (Submodule.fg_top _).mp (IsNoetherian.noetherian ⊤)

end PadicRank

section Rank

open PadicRank

attribute [local instance] algebraK algebraInteger

theorem finite_principalUnits (p : ℕ) [Fact p.Prime] [CharP 𝓀[K] p] [CharZero K] :
    Module.Finite ℤ_[p] (Additive (unitFiltrationUnits K 1)) := by
  refine ⟨?_⟩
  have h := Submodule.fg_of_fg_map_of_fg_inf_ker (padicLogLinear K p)
    (s := ⊤) (by rw [Submodule.map_top]; exact fg_range_padicLogLinear p)
    (by rw [top_inf_eq]; exact fg_ker_padicLogLinear p)
  exact h

theorem finrank_principalUnits (p : ℕ) [Fact p.Prime] [CharP 𝓀[K] p] [CharZero K] :
    Module.finrank ℤ_[p] (Additive (unitFiltrationUnits K 1)) =
      (letI := (CharZero.padicHom K p).toAlgebra; Module.finrank ℚ_[p] K) := by
  set d := (letI := (CharZero.padicHom K p).toAlgebra; Module.finrank ℚ_[p] K)
  have hker : Module.rank ℤ_[p] (LinearMap.ker (padicLogLinear K p)) = 0 := by
    refine (rank_eq_zero_iff (R := ℤ_[p]) (M := LinearMap.ker (padicLogLinear K p))).mpr
      fun x ↦ ?_
    refine ⟨((p ^ absRamificationIndex K : ℕ) : ℤ_[p]), ?_, ?_⟩
    · exact_mod_cast pow_ne_zero _ (Fact.out : p.Prime).ne_zero
    · apply Subtype.ext
      rw [Submodule.coe_smul, natCast_smul, Submodule.coe_zero]
      exact nsmul_eq_zero_of_padicLog_eq_zero p (LinearMap.mem_ker.mp x.2)
  have hrange : Module.rank ℤ_[p] (LinearMap.range (padicLogLinear K p)) = d := by
    refine le_antisymm ?_ ?_
    · rw [← rank_valBallSubmodule (K := K) p (absRamificationIndex K + 1 -
        absRamificationIndex K * absRamificationIndex K)]
      exact Submodule.rank_mono (range_padicLogLinear_le p)
    · rw [← rank_valBallSubmodule (K := K) p ((absRamificationIndex K + 1 : ℕ) : ℤ)]
      exact Submodule.rank_mono (valBallSubmodule_le_range p)
  have h := (padicLogLinear K p).rank_range_add_rank_ker
  rw [hker, hrange, add_zero] at h
  rw [Module.finrank, ← h]
  simp

end Rank

end Sec_PrincipalUnitsRank


/-! ### CompleteTrivial -/
section Sec_CompleteTrivial

open Finset Filter

section Tate

variable (G M : Type*) [Group G] [Fintype G] [CommGroup M] [MulDistribMulAction G M]

def tateNorm : M →* M where
  toFun x := ∏ g : G, g • x
  map_one' := by simp
  map_mul' x y := by simp only [smul_mul', prod_mul_distrib]

theorem tateNorm_apply (x : M) : tateNorm G M x = ∏ g : G, g • x := rfl

def invariants : Subgroup M where
  carrier := {x | ∀ g : G, g • x = x}
  one_mem' g := smul_one g
  mul_mem' {x y} hx hy g := by rw [smul_mul', hx g, hy g]
  inv_mem' {x} hx g := by rw [smul_inv', hx g]

omit [Fintype G] in
theorem mem_invariants {x : M} : x ∈ invariants G M ↔ ∀ g : G, g • x = x := Iff.rfl

def augmentation : Subgroup M :=
  Subgroup.closure {y | ∃ (g : G) (x : M), g • x / x = y}

abbrev TateZero : Type _ :=
  invariants G M ⧸ (tateNorm G M).range.subgroupOf (invariants G M)

abbrev TateNegOne : Type _ :=
  (tateNorm G M).ker ⧸ (augmentation G M).subgroupOf (tateNorm G M).ker

def augMap : (G → M) →* M where
  toFun m := ∏ g : G, g • m g / m g
  map_one' := by simp
  map_mul' m m' := by
    simp only [Pi.mul_apply, smul_mul', ← prod_mul_distrib, div_mul_div_comm]

theorem augMap_apply (m : G → M) : augMap G M m = ∏ g : G, g • m g / m g := rfl

variable {G M}

theorem smul_tateNorm (g : G) (x : M) : g • tateNorm G M x = tateNorm G M x := by
  rw [tateNorm_apply, Finset.smul_prod']
  simp_rw [smul_smul]
  exact Fintype.prod_equiv (Equiv.mulLeft g) _ _ (fun _ => rfl)

theorem tateNorm_smul (g : G) (x : M) : tateNorm G M (g • x) = tateNorm G M x := by
  simp_rw [tateNorm_apply, smul_smul]
  exact Fintype.prod_equiv (Equiv.mulRight g) _ _ (fun _ => rfl)

theorem tateNorm_mem_invariants (x : M) : tateNorm G M x ∈ invariants G M :=
  fun g => smul_tateNorm g x

theorem tateNorm_augMap (m : G → M) : tateNorm G M (augMap G M m) = 1 := by
  rw [augMap_apply, map_prod]
  refine prod_eq_one fun g _ => ?_
  rw [map_div, tateNorm_smul, div_self']

theorem augmentation_eq_range : augmentation G M = (augMap G M).range := by
  classical
  apply le_antisymm
  · rw [augmentation, Subgroup.closure_le]
    rintro _ ⟨g, x, rfl⟩
    refine ⟨Pi.mulSingle g x, ?_⟩
    rw [augMap_apply, Fintype.prod_eq_single g (fun h hh => by simp [Pi.mulSingle_eq_of_ne hh])]
    simp
  · rintro _ ⟨m, rfl⟩
    exact Subgroup.prod_mem _ fun g _ => Subgroup.subset_closure ⟨g, m g, rfl⟩

theorem subsingleton_tateZero_iff :
    Subsingleton (TateZero G M) ↔ ∀ x : M, (∀ g : G, g • x = x) → ∃ y, tateNorm G M y = x := by
  rw [QuotientGroup.subsingleton_iff, Subgroup.subgroupOf_eq_top]
  exact ⟨fun h x hx => h hx, fun h x hx => h x hx⟩

theorem subsingleton_tateNegOne_iff :
    Subsingleton (TateNegOne G M) ↔ ∀ x : M, tateNorm G M x = 1 → x ∈ augmentation G M := by
  rw [QuotientGroup.subsingleton_iff, Subgroup.subgroupOf_eq_top]
  exact ⟨fun h x hx => h hx, fun h x hx => h x hx⟩

end Tate

section Filtration

structure StableFiltration (G V : Type*) [Group G] [CommGroup V] [MulDistribMulAction G V] where

  F : ℕ → Subgroup V

  antitone : Antitone F

  smul_mem : ∀ (n : ℕ) (g : G) {x : V}, x ∈ F n → g • x ∈ F n

namespace StableFiltration

variable {G V : Type*} [Group G] [CommGroup V] [MulDistribMulAction G V]
  (S : StableFiltration G V)

instance instMulDistribMulActionF (n : ℕ) : MulDistribMulAction G (S.F n) where
  smul g x := ⟨g • (x : V), S.smul_mem n g x.2⟩
  one_smul x := Subtype.ext (one_smul G (x : V))
  mul_smul g h x := Subtype.ext (mul_smul g h (x : V))
  smul_mul g x y := Subtype.ext (smul_mul' g (x : V) y)
  smul_one g := Subtype.ext (smul_one g)

@[simp]
theorem coe_smul_F {n : ℕ} (g : G) (x : S.F n) : ((g • x : S.F n) : V) = g • (x : V) := rfl

def gr (n : ℕ) : Type _ := S.F n ⧸ (S.F (n + 1)).subgroupOf (S.F n)

instance instCommGroupGr (n : ℕ) : CommGroup (S.gr n) :=
  QuotientGroup.Quotient.commGroup _

def grMk (n : ℕ) : S.F n →* S.gr n := QuotientGroup.mk' _

theorem grMk_surjective (n : ℕ) : Function.Surjective (S.grMk n) :=
  QuotientGroup.mk'_surjective _

theorem grMk_eq_one_iff {n : ℕ} (x : S.F n) : S.grMk n x = 1 ↔ (x : V) ∈ S.F (n + 1) :=
  (QuotientGroup.eq_one_iff x).trans Subgroup.mem_subgroupOf

theorem grMk_eq_grMk_iff {n : ℕ} (x y : S.F n) :
    S.grMk n x = S.grMk n y ↔ (x : V) / y ∈ S.F (n + 1) := by
  rw [← div_eq_one, ← map_div, grMk_eq_one_iff]
  rfl

def grAct (n : ℕ) (g : G) : S.gr n →* S.gr n :=
  QuotientGroup.map _ _ (MulDistribMulAction.toMonoidHom (S.F n) g) fun x hx => by
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf] at *
    exact S.smul_mem (n + 1) g hx

theorem grAct_grMk {n : ℕ} (g : G) (x : S.F n) : S.grAct n g (S.grMk n x) = S.grMk n (g • x) :=
  rfl

instance instMulDistribMulActionGr (n : ℕ) : MulDistribMulAction G (S.gr n) where
  smul g q := S.grAct n g q
  one_smul q := by
    obtain ⟨x, rfl⟩ := S.grMk_surjective n q
    exact (S.grAct_grMk 1 x).trans (congrArg _ (one_smul G x))
  mul_smul g h q := by
    obtain ⟨x, rfl⟩ := S.grMk_surjective n q
    change S.grAct n (g * h) (S.grMk n x) = S.grAct n g (S.grAct n h (S.grMk n x))
    rw [grAct_grMk, grAct_grMk, grAct_grMk, mul_smul]
  smul_mul g q r := map_mul (S.grAct n g) q r
  smul_one g := map_one (S.grAct n g)

theorem smul_grMk {n : ℕ} (g : G) (x : S.F n) : g • S.grMk n x = S.grMk n (g • x) := rfl

variable [Fintype G]

theorem coe_tateNorm_F {n : ℕ} (x : S.F n) : ((tateNorm G (S.F n) x : S.F n) : V) = tateNorm G V x := by
  rw [tateNorm_apply, tateNorm_apply, SubmonoidClass.coe_finsetProd]
  rfl

theorem coe_augMap_F {n : ℕ} (m : G → S.F n) :
    ((augMap G (S.F n) m : S.F n) : V) = augMap G V (fun g => (m g : V)) := by
  rw [augMap_apply, augMap_apply, SubmonoidClass.coe_finsetProd]
  rfl

theorem tateNorm_grMk {n : ℕ} (x : S.F n) :
    tateNorm G (S.gr n) (S.grMk n x) = S.grMk n (tateNorm G (S.F n) x) := by
  rw [tateNorm_apply, tateNorm_apply, map_prod]
  rfl

theorem augMap_grMk {n : ℕ} (m : G → S.F n) :
    augMap G (S.gr n) (fun g => S.grMk n (m g)) = S.grMk n (augMap G (S.F n) m) := by
  rw [augMap_apply, augMap_apply, map_prod]
  simp only [map_div, smul_grMk]

theorem tateNorm_mem {n : ℕ} {x : V} (hx : x ∈ S.F n) : tateNorm G V x ∈ S.F n :=
  Subgroup.prod_mem _ fun g _ => S.smul_mem n g hx

theorem augMap_mem {n : ℕ} {m : G → V} (hm : ∀ g, m g ∈ S.F n) : augMap G V m ∈ S.F n :=
  Subgroup.prod_mem _ fun g _ => Subgroup.div_mem _ (S.smul_mem n g (hm g)) (hm g)

theorem subsingleton_tateZero_gr_iff (n : ℕ) :
    Subsingleton (TateZero G (S.gr n)) ↔
      ∀ x ∈ S.F n, (∀ g : G, g • x / x ∈ S.F (n + 1)) →
        ∃ y ∈ S.F n, x / tateNorm G V y ∈ S.F (n + 1) := by
  rw [subsingleton_tateZero_iff]
  constructor
  · intro h x hx hinv
    obtain ⟨q, hq⟩ := h (S.grMk n ⟨x, hx⟩) fun g => by
      rw [smul_grMk, grMk_eq_grMk_iff]
      exact hinv g
    obtain ⟨y, rfl⟩ := S.grMk_surjective n q
    rw [tateNorm_grMk, eq_comm, grMk_eq_grMk_iff, coe_tateNorm_F] at hq
    exact ⟨y, y.2, hq⟩
  · intro h q hq
    obtain ⟨x, rfl⟩ := S.grMk_surjective n q
    obtain ⟨y, hy, hxy⟩ := h x x.2 fun g => by
      have := hq g
      rw [smul_grMk, grMk_eq_grMk_iff] at this
      exact this
    refine ⟨S.grMk n ⟨y, hy⟩, ?_⟩
    rw [tateNorm_grMk, eq_comm, grMk_eq_grMk_iff, coe_tateNorm_F]
    exact hxy

theorem subsingleton_tateNegOne_gr_iff (n : ℕ) :
    Subsingleton (TateNegOne G (S.gr n)) ↔
      ∀ x ∈ S.F n, tateNorm G V x ∈ S.F (n + 1) →
        ∃ m : G → V, (∀ g, m g ∈ S.F n) ∧ x / augMap G V m ∈ S.F (n + 1) := by
  rw [subsingleton_tateNegOne_iff, augmentation_eq_range]
  constructor
  · intro h x hx hN
    obtain ⟨q, hq⟩ := h (S.grMk n ⟨x, hx⟩) (by
      rw [tateNorm_grMk, grMk_eq_one_iff, coe_tateNorm_F]
      exact hN)
    have hl : ∀ g, ∃ y, S.grMk n y = q g := fun g => S.grMk_surjective n (q g)
    choose m hm using hl
    have e : q = fun g => S.grMk n (m g) := funext fun g => (hm g).symm
    rw [e, augMap_grMk, eq_comm, grMk_eq_grMk_iff, coe_augMap_F] at hq
    exact ⟨fun g => (m g : V), fun g => (m g).2, hq⟩
  · intro h q hq
    obtain ⟨x, rfl⟩ := S.grMk_surjective n q
    rw [tateNorm_grMk, grMk_eq_one_iff, coe_tateNorm_F] at hq
    obtain ⟨m, hm, hxm⟩ := h x x.2 hq
    refine ⟨fun g => S.grMk n ⟨m g, hm g⟩, ?_⟩
    rw [augMap_grMk, eq_comm, grMk_eq_grMk_iff, coe_augMap_F]
    exact hxm

end StableFiltration

end Filtration

section Complete

variable {V : Type*} [CommGroup V]

theorem filtrationComplete_pi {ι : Type*} [Fintype ι] {F : ℕ → Subgroup V}
    (hc : FiltrationComplete F) :
    FiltrationComplete fun n => Subgroup.pi Set.univ fun _ : ι => F n := by
  intro x hx
  have hxi : ∀ i, FiltrationCauchy F fun k => x k i := by
    intro i N
    obtain ⟨M, hM⟩ := hx N
    exact ⟨M, fun m hm n hn => (Subgroup.mem_pi _).mp (hM m hm n hn) i (Set.mem_univ i)⟩
  choose y hy using fun i => hc _ (hxi i)
  refine ⟨y, fun N => ?_⟩
  choose M hM using fun i => hy i N
  refine ⟨Finset.univ.sup M, fun n hn => (Subgroup.mem_pi _).mpr fun i _ => ?_⟩
  exact hM i n ((Finset.le_sup (Finset.mem_univ i)).trans hn)

variable {G : Type*} [Group G] [Fintype G] [MulDistribMulAction G V]

theorem subsingleton_tateZero_of_complete (S : StableFiltration G V) (h0 : S.F 0 = ⊤)
    (hc : FiltrationComplete S.F) (hs : FiltrationSeparated S.F)
    (hgr : ∀ n, Subsingleton (TateZero G (S.gr n))) : Subsingleton (TateZero G V) := by
  rw [subsingleton_tateZero_iff]
  intro x hx
  let f : V →* invariants G V := (tateNorm G V).codRestrict _ tateNorm_mem_invariants
  let E : ℕ → Subgroup (invariants G V) := fun n => (S.F n).subgroupOf (invariants G V)
  have key := map_eq_of_graded_surjective (F := S.F) (E := E) S.antitone
    (fun a b hab y hy => Subgroup.mem_subgroupOf.mpr (S.antitone hab (Subgroup.mem_subgroupOf.mp hy)))
    hc (fun y hy => Subtype.ext (hs _ fun n => Subgroup.mem_subgroupOf.mp (hy n))) f tendsto_id 0
    (fun n _ y hy => Subgroup.mem_subgroupOf.mpr (S.tateNorm_mem hy))
    (fun n _ h hh => by
      have hh' : (h : V) ∈ S.F n := Subgroup.mem_subgroupOf.mp hh
      obtain ⟨y, hy, hhy⟩ := (S.subsingleton_tateZero_gr_iff n).mp (hgr n) h hh' fun g => by
        rw [h.2 g, div_self']
        exact Subgroup.one_mem _
      exact ⟨y, hy, Subgroup.mem_subgroupOf.mpr hhy⟩)
  have hx0 : (⟨x, (mem_invariants G V).mpr hx⟩ : invariants G V) ∈ (S.F 0).map f := by
    rw [key]
    change _ ∈ E 0
    rw [Subgroup.mem_subgroupOf, h0]
    exact Subgroup.mem_top _
  obtain ⟨y, -, hy⟩ := hx0
  exact ⟨y, congrArg Subtype.val hy⟩

theorem subsingleton_tateNegOne_of_complete (S : StableFiltration G V) (h0 : S.F 0 = ⊤)
    (hc : FiltrationComplete S.F) (hs : FiltrationSeparated S.F)
    (hgr : ∀ n, Subsingleton (TateNegOne G (S.gr n))) : Subsingleton (TateNegOne G V) := by
  rw [subsingleton_tateNegOne_iff, augmentation_eq_range]
  intro x hx
  let f : (G → V) →* (tateNorm G V).ker := (augMap G V).codRestrict _ tateNorm_augMap
  let P : ℕ → Subgroup (G → V) := fun n => Subgroup.pi Set.univ fun _ : G => S.F n
  let E : ℕ → Subgroup (tateNorm G V).ker := fun n => (S.F n).subgroupOf (tateNorm G V).ker
  have key := map_eq_of_graded_surjective (F := P) (E := E)
    (fun a b hab m hm => (Subgroup.mem_pi _).mpr fun g _ =>
      S.antitone hab ((Subgroup.mem_pi _).mp hm g (Set.mem_univ g)))
    (fun a b hab y hy => Subgroup.mem_subgroupOf.mpr (S.antitone hab (Subgroup.mem_subgroupOf.mp hy)))
    (filtrationComplete_pi hc)
    (fun y hy => Subtype.ext (hs _ fun n => Subgroup.mem_subgroupOf.mp (hy n))) f tendsto_id 0
    (fun n _ m hm => Subgroup.mem_subgroupOf.mpr
      (S.augMap_mem fun g => (Subgroup.mem_pi _).mp hm g (Set.mem_univ g)))
    (fun n _ h hh => by
      have hh' : (h : V) ∈ S.F n := Subgroup.mem_subgroupOf.mp hh
      have hN : tateNorm G V h ∈ S.F (n + 1) := by
        rw [h.2]
        exact Subgroup.one_mem _
      obtain ⟨m, hm, hhm⟩ := (S.subsingleton_tateNegOne_gr_iff n).mp (hgr n) h hh' hN
      exact ⟨m, (Subgroup.mem_pi _).mpr fun g _ => hm g, Subgroup.mem_subgroupOf.mpr hhm⟩)
  have hx0 : (⟨x, MonoidHom.mem_ker.mpr hx⟩ : (tateNorm G V).ker) ∈ (P 0).map f := by
    rw [key]
    change _ ∈ E 0
    rw [Subgroup.mem_subgroupOf, h0]
    exact Subgroup.mem_top _
  obtain ⟨m, -, hm⟩ := hx0
  exact ⟨m, congrArg Subtype.val hm⟩

theorem subsingleton_tate_of_complete (S : StableFiltration G V) (h0 : S.F 0 = ⊤)
    (hc : FiltrationComplete S.F) (hs : FiltrationSeparated S.F)
    (hgr0 : ∀ n, Subsingleton (TateZero G (S.gr n)))
    (hgr1 : ∀ n, Subsingleton (TateNegOne G (S.gr n))) :
    Subsingleton (TateZero G V) ∧ Subsingleton (TateNegOne G V) :=
  ⟨subsingleton_tateZero_of_complete S h0 hc hs hgr0,
    subsingleton_tateNegOne_of_complete S h0 hc hs hgr1⟩

end Complete

end Sec_CompleteTrivial


/-! ### HilbertCyclic -/
section Sec_HilbertCyclic

open Finset

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]

section Partial

variable (σ : L ≃ₐ[K] L) (x : Lˣ)

noncomputable def partialNorm (m : ℕ) : Lˣ :=
  ∏ j ∈ range m, (σ ^ j) • x

omit [FiniteDimensional K L] in
theorem partialNorm_add (a b : ℕ) :
    partialNorm σ x (a + b) = partialNorm σ x a * (σ ^ a) • partialNorm σ x b := by
  rw [partialNorm, prod_range_add, partialNorm, partialNorm, smul_prod']
  simp_rw [pow_add, mul_smul]

omit [FiniteDimensional K L] in
theorem partialNorm_one : partialNorm σ x 1 = x := by
  rw [partialNorm, prod_range_one, pow_zero, one_smul]

variable {σ}

theorem partialNorm_orderOf (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    partialNorm σ x (orderOf σ) = tateNorm (L ≃ₐ[K] L) Lˣ x := by
  rw [partialNorm, ← Fin.prod_univ_eq_prod_range, tateNorm_apply]
  refine Fintype.prod_bijective (fun j : Fin (orderOf σ) => σ ^ (j : ℕ)) ⟨?_, ?_⟩ _ _
    (fun _ => rfl)
  · intro i j hij
    exact Fin.ext (pow_injOn_Iio_orderOf i.2 j.2 hij)
  · intro g
    obtain ⟨k, hk⟩ := (mem_powers_iff_mem_zpowers (x := σ) (y := g)).mpr (hσ g)
    refine ⟨⟨k % orderOf σ, Nat.mod_lt _ (orderOf_pos σ)⟩, ?_⟩
    change σ ^ (k % orderOf σ) = g
    rw [pow_mod_orderOf]
    exact hk

variable (hσ : ∀ g, g ∈ Subgroup.zpowers σ) {x} (hx : tateNorm (L ≃ₐ[K] L) Lˣ x = 1)
include hσ hx

theorem partialNorm_add_orderOf (m : ℕ) :
    partialNorm σ x (m + orderOf σ) = partialNorm σ x m := by
  rw [add_comm, partialNorm_add, partialNorm_orderOf x hσ, hx, pow_orderOf_eq_one, one_smul, one_mul]

theorem partialNorm_mod (m : ℕ) : partialNorm σ x (m % orderOf σ) = partialNorm σ x m := by
  conv_rhs => rw [← Nat.mod_add_div m (orderOf σ)]
  induction m / orderOf σ with
  | zero => simp
  | succ q ih => rw [mul_add, mul_one, ← add_assoc, partialNorm_add_orderOf hσ hx, ih]

theorem partialNorm_eq_of_pow_eq {a b : ℕ} (h : σ ^ a = σ ^ b) :
    partialNorm σ x a = partialNorm σ x b := by
  rw [← partialNorm_mod hσ hx a, ← partialNorm_mod hσ hx b, (pow_eq_pow_iff_modEq.mp h)]

end Partial

theorem exists_smul_div_eq_of_tateNorm_eq_one {σ : L ≃ₐ[K] L}
    (hσ : ∀ g, g ∈ Subgroup.zpowers σ) {x : Lˣ} (hx : tateNorm (L ≃ₐ[K] L) Lˣ x = 1) :
    ∃ y : Lˣ, σ • y / y = x := by
  have hk : ∀ g : L ≃ₐ[K] L, ∃ k : ℕ, σ ^ k = g := fun g => by
    obtain ⟨k, hk⟩ := (mem_powers_iff_mem_zpowers (x := σ) (y := g)).mpr (hσ g)
    exact ⟨k, hk⟩
  choose k hk using hk
  let f : (L ≃ₐ[K] L) → Lˣ := fun g => partialNorm σ x (k g)
  have hf : groupCohomology.IsMulCocycle₁ f := by
    intro g h
    have e : σ ^ k (g * h) = σ ^ (k g + k h) := by rw [hk, pow_add, hk, hk]
    change partialNorm σ x (k (g * h)) = g • partialNorm σ x (k h) * partialNorm σ x (k g)
    rw [partialNorm_eq_of_pow_eq hσ hx e, partialNorm_add, hk, mul_comm]
  obtain ⟨β, hβ⟩ := groupCohomology.isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units f hf
  refine ⟨β, ?_⟩
  rw [hβ σ]
  change partialNorm σ x (k σ) = x
  rw [partialNorm_eq_of_pow_eq hσ hx (show σ ^ k σ = σ ^ 1 by rw [hk, pow_one]), partialNorm_one]

theorem subsingleton_tateNegOne_units [IsCyclic (L ≃ₐ[K] L)] :
    Subsingleton (TateNegOne (L ≃ₐ[K] L) Lˣ) := by
  obtain ⟨σ, hσ⟩ := IsCyclic.exists_generator (α := L ≃ₐ[K] L)
  rw [subsingleton_tateNegOne_iff]
  intro x hx
  obtain ⟨y, hy⟩ := exists_smul_div_eq_of_tateNorm_eq_one hσ hx
  exact Subgroup.subset_closure ⟨σ, y, hy⟩

end Sec_HilbertCyclic


end RHDirect.CFT.LocalField
