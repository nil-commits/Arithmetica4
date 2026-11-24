import RHDirect.Stage13CFT_IdeleNormResidue
import RHDirect.CFT_ProfiniteSemilocal
import RHDirect.CFT_LocalStructure
import RHDirect.CFT_LocalRamification
import Mathlib.LinearAlgebra.Dimension.DivisionRing
import Mathlib.NumberTheory.RamificationInertia.Inertia
import Mathlib.NumberTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.Valuation.Discrete.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Frobenius
import Mathlib.RingTheory.TotallySplit

/-!
# RHDirect.CFT_GlobalCompletion

Global Class Field Theory Pillar — Completion at Places, Local-Global Norm Groups,
S-Idele Herbrand Quotients, Global First Inequality, and Splitting from First Inequality:
1. Local field bridge at finite places (`LocalFieldAtPlace`, `CompletionAtPlace.*`:
   completion maps, valuation/integers, `[L_w : K_v] = e * f`, decomposition group isomorphism
   `D_w ≃* Gal(L_w / K_v)`, inertia & Frobenius compatibility).
2. Local norm groups and everywhere-local norm characterization (`IdeleNorm`, `SplitsCompletely`).
3. S-Idele Galois decomposition and local/global Herbrand quotients (`SIdeleGroups.*`,
   `LocalHerbrand`, `LocalHerbrandInfinite`, `SIdeleHerbrand.*`).
4. **Global First Inequality** (`FirstInequality`, `firstInequality`, `cycHerbrand_ideleClassGroup`,
   `finrank_le_index_range_ideleClassNorm`): for every cyclic extension `L / K` of number fields,
   `h(C_L) = [L : K]` and `[I_K : Kˣ N_{L/K}(I_L)] ≥ [L : K]`.
5. **Splitting from the First Inequality** (`SplittingFromInequality.*`): extensions where almost all
   primes split completely are trivial; decomposition groups generate `Gal(L / K)`.
-/

noncomputable section

namespace RHDirect.CFT.Global

open RHDirect.Stage13CFT_IdeleNormResidue
open RHDirect.CFT_ProfiniteSemilocal


/-! ### 01_LocalFieldAtPlace -/
section Sec_01_LocalFieldAtPlace

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField WithZero

open scoped WithZero


section Discrete

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K] (v : HeightOneSpectrum R)

theorem isDiscreteValuationRing_adicCompletionIntegers :
    IsDiscreteValuationRing (v.adicCompletionIntegers K) :=
  inferInstance

theorem valued_adicCompletion_surjective :
    Function.Surjective (Valued.v : v.adicCompletion K → ℤᵐ⁰) :=
  valuedAdicCompletion_surjective K v

theorem valued_of_irreducible {ϖ : v.adicCompletionIntegers K} (hϖ : Irreducible ϖ) :
    Valued.v (ϖ : v.adicCompletion K) = exp (-1 : ℤ) := by
  have h : Valuation.IsUniformizer (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰)
      (ϖ : v.adicCompletion K) :=
    Valuation.isUniformizer_of_maximalIdeal_eq_span Valued.v
      ((IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ)
  rw [h.val, Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective
    (valuedAdicCompletion_surjective K v)]
  rfl

end Discrete

section AbsoluteValue

variable {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

noncomputable def normalizedAbv : AbsoluteValue (v.adicCompletion K) ℝ where
  toFun x := ‖x‖
  map_mul' := norm_mul
  nonneg' := norm_nonneg
  eq_zero' _ := norm_eq_zero
  add_le' := norm_add_le

theorem normalizedAbv_apply (x : v.adicCompletion K) : normalizedAbv v x = ‖x‖ :=
  rfl

theorem normalizedAbv_eq_toNNReal (x : v.adicCompletion K) :
    normalizedAbv v x = WithZeroMulInt.toNNReal (NumberField.HeightOneSpectrum.absNorm_ne_zero v) (Valued.v x) :=
  FinitePlace.norm_def v x

theorem normalizedAbv_eq_zpow {x : v.adicCompletion K} (hx : x ≠ 0) :
    normalizedAbv v x = (Ideal.absNorm v.asIdeal : ℝ) ^ log (Valued.v x) := by
  have hx' : Valued.v x ≠ 0 := (Valued.v).ne_zero_iff.2 hx
  have key : ∀ (y : ℤᵐ⁰) (hy : y ≠ 0), Multiplicative.toAdd (unzero hy) = log y := by
    rintro (_ | a) hy
    · exact absurd rfl hy
    · rfl
  rw [normalizedAbv_eq_toNNReal, WithZeroMulInt.toNNReal_neg_apply _ hx', key]
  simp

theorem normalizedAbv_of_irreducible {ϖ : v.adicCompletionIntegers K} (hϖ : Irreducible ϖ) :
    normalizedAbv v (ϖ : v.adicCompletion K) = (Ideal.absNorm v.asIdeal : ℝ)⁻¹ := by
  have h0 : (ϖ : v.adicCompletion K) ≠ 0 := by
    intro h
    exact hϖ.ne_zero (Subtype.ext h)
  rw [normalizedAbv_eq_zpow v h0, valued_of_irreducible v hϖ, log_exp, zpow_neg_one]

end AbsoluteValue

end Sec_01_LocalFieldAtPlace

/-! ### 02_CompletionAtPlace -/
section Sec_02_CompletionAtPlace

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField

open scoped WithZero


section Map

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]

abbrev adicCompletionMap : v.adicCompletion K →+* w.adicCompletion L :=
  SemiLocal.completionMap v w

theorem continuous_adicCompletionMap : Continuous (adicCompletionMap v w) :=
  SemiLocal.continuous_completionMap v w

theorem adicCompletionMap_algebraMap (x : K) :
    adicCompletionMap v w (algebraMap K (v.adicCompletion K) x) =
      algebraMap L (w.adicCompletion L) (algebraMap K L x) :=
  (SemiLocal.completionMap_algebraMap v w x).trans (IsScalarTower.algebraMap_apply K L _ x)

end Map

namespace AdicLiesOver

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]

scoped instance : Algebra (v.adicCompletion K) (w.adicCompletion L) :=
  SemiLocal.algebraCompletion v w

theorem algebraMap_eq : algebraMap (v.adicCompletion K) (w.adicCompletion L) =
    adicCompletionMap v w :=
  rfl

scoped instance : IsScalarTower K (v.adicCompletion K) (w.adicCompletion L) :=
  .of_algebraMap_eq fun x ↦ by
    rw [algebraMap_eq, adicCompletionMap_algebraMap, IsScalarTower.algebraMap_apply K L]

scoped instance : ContinuousSMul (v.adicCompletion K) (w.adicCompletion L) :=
  continuousSMul_of_algebraMap _ _ (continuous_adicCompletionMap v w)

end AdicLiesOver

section Extension

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
  [Algebra (v.adicCompletion K) (w.adicCompletion L)]
  [ContinuousSMul (v.adicCompletion K) (w.adicCompletion L)]
  [IsScalarTower K (v.adicCompletion K) (w.adicCompletion L)]

theorem algebraMap_adicCompletion_eq [w.asIdeal.LiesOver v.asIdeal] :
    algebraMap (v.adicCompletion K) (w.adicCompletion L) = adicCompletionMap v w := by
  have h := (denseRange_algebraMap (R := 𝓞 K) (K := K) v).equalizer
    (continuous_algebraMap (v.adicCompletion K) (w.adicCompletion L))
    (continuous_adicCompletionMap v w) (funext fun x ↦ ?_)
  · exact RingHom.ext (congrFun h)
  · simp only [Function.comp_apply]
    rw [adicCompletionMap_algebraMap, ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply K L (w.adicCompletion L)]

theorem valued_algebraMap_adicCompletion' [w.asIdeal.LiesOver v.asIdeal]
    (x : v.adicCompletion K) :
    Valued.v (algebraMap (v.adicCompletion K) (w.adicCompletion L) x) =
      Valued.v x ^ v.asIdeal.ramificationIdx' w.asIdeal := by
  have he : v.asIdeal.ramificationIdx' w.asIdeal ≠ 0 :=
    Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver w.asIdeal v.ne_bot
  rcases eq_or_ne x 0 with rfl | hx
  · simp [he]
  have hx' : Valued.v x ≠ 0 := by simpa using hx
  have hy : Valued.v (algebraMap (v.adicCompletion K) (w.adicCompletion L) x) ≠ 0 := by
    simpa using hx
  have h1 := Valued.locally_const hx'
  have h2 := (continuous_algebraMap (v.adicCompletion K) (w.adicCompletion L)).continuousAt.preimage_mem_nhds
    (Valued.locally_const hy)
  obtain ⟨k, hk1, hk2⟩ := (denseRange_algebraMap (R := 𝓞 K) (K := K) v).mem_nhds
    (Filter.inter_mem h1 h2)
  simp only [Set.mem_preimage, Set.mem_ofPred_eq] at hk1 hk2
  rw [← hk1, ← hk2, ← IsScalarTower.algebraMap_apply,
    IsScalarTower.algebraMap_apply K L (w.adicCompletion L)]
  erw [valuedAdicCompletion_eq_valuation' w, valuedAdicCompletion_eq_valuation' v]
  exact (valuation_liesOver L v w k).symm

theorem valued_algebraMap_adicCompletion [w.asIdeal.LiesOver v.asIdeal]
    (x : v.adicCompletion K) :
    Valued.v (algebraMap (v.adicCompletion K) (w.adicCompletion L) x) =
      Valued.v x ^ w.asIdeal.ramificationIdx (𝓞 K) := by
  rw [valued_algebraMap_adicCompletion',
    Ideal.ramificationIdx'_eq_ramificationIdx v.asIdeal w.asIdeal v.ne_bot]

instance valuativeExtension_adicCompletion_of_algebra [w.asIdeal.LiesOver v.asIdeal] :
    ValuativeExtension (v.adicCompletion K) (w.adicCompletion L) where
  vle_iff_vle a b := by
    have he : v.asIdeal.ramificationIdx' w.asIdeal ≠ 0 :=
      Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver w.asIdeal v.ne_bot
    rw [Valuation.Compatible.vle_iff_le (v := (Valued.v : Valuation (w.adicCompletion L) ℤᵐ⁰)),
      Valuation.Compatible.vle_iff_le (v := (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰)),
      valued_algebraMap_adicCompletion', valued_algebraMap_adicCompletion']
    exact pow_le_pow_iff_left₀ zero_le zero_le he

theorem finite_adicCompletion : Module.Finite (v.adicCompletion K) (w.adicCompletion L) :=
  inferInstance

end Extension

section Check

open AdicLiesOver

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]

example : ValuativeExtension (v.adicCompletion K) (w.adicCompletion L) := inferInstance
example : Module.Finite (v.adicCompletion K) (w.adicCompletion L) := inferInstance

end Check

end Sec_02_CompletionAtPlace

/-! ### 03_CompletionAtPlace.Integers -/
section Sec_03_CompletionAtPlace_Integers

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField ValuativeRel

open scoped WithZero




section IntegralClosure

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]
  [Algebra (v.adicCompletion K) (w.adicCompletion L)]
  [ContinuousSMul (v.adicCompletion K) (w.adicCompletion L)]
  [IsScalarTower K (v.adicCompletion K) (w.adicCompletion L)]

theorem mem_integer_of_isIntegral_general {x : w.adicCompletion L}
    (hx : IsIntegral 𝒪[v.adicCompletion K] x) : x ∈ 𝒪[w.adicCompletion L] :=
  (Valuation.integer.integers (valuation (w.adicCompletion L))).mem_of_integral
    (hx.tower_top (A := 𝒪[w.adicCompletion L]))

omit [Algebra K L] [w.asIdeal.LiesOver v.asIdeal]
  [ContinuousSMul (v.adicCompletion K) (w.adicCompletion L)]
  [IsScalarTower K (v.adicCompletion K) (w.adicCompletion L)] in

theorem isIntegral_algebraMap_ringOfIntegers_general (r : 𝓞 L) :
    IsIntegral 𝒪[v.adicCompletion K]
      (algebraMap L (w.adicCompletion L) (algebraMap (𝓞 L) L r)) := by
  obtain ⟨p, hp, hroot⟩ := RingOfIntegers.isIntegral_coe r
  refine ⟨p.map (Int.castRingHom _), hp.map _, ?_⟩
  rw [Polynomial.eval₂_map, show (algebraMap 𝒪[v.adicCompletion K] (w.adicCompletion L)).comp
      (Int.castRingHom _) = (algebraMap L (w.adicCompletion L)).comp (algebraMap ℤ L) from
      RingHom.ext_int _ _, ← Polynomial.hom_eval₂]
  exact (congrArg (algebraMap L (w.adicCompletion L)) hroot).trans (map_zero _)

omit [Algebra K L] [w.asIdeal.LiesOver v.asIdeal]
  [IsScalarTower K (v.adicCompletion K) (w.adicCompletion L)] in

theorem continuousSMul_integer_general :
    ContinuousSMul 𝒪[v.adicCompletion K] (w.adicCompletion L) := by
  refine continuousSMul_of_algebraMap _ _ ?_
  rw [IsScalarTower.algebraMap_eq 𝒪[v.adicCompletion K] (v.adicCompletion K)]
  exact (continuous_algebraMap (v.adicCompletion K) (w.adicCompletion L)).comp
    continuous_subtype_val

omit [w.asIdeal.LiesOver v.asIdeal] in
theorem isClosed_integralClosure_general :
    IsClosed ((integralClosure 𝒪[v.adicCompletion K] (w.adicCompletion L) :
      Set (w.adicCompletion L))) := by
  have : CharZero (v.adicCompletion K) :=
    charZero_of_injective_algebraMap (algebraMap K (v.adicCompletion K)).injective
  have : ContinuousSMul 𝒪[v.adicCompletion K] (w.adicCompletion L) :=
    continuousSMul_integer_general v w
  have hfin : Module.Finite 𝒪[v.adicCompletion K]
      (integralClosure 𝒪[v.adicCompletion K] (w.adicCompletion L)) :=
    IsIntegralClosure.finite 𝒪[v.adicCompletion K] (v.adicCompletion K) (w.adicCompletion L) _
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' 𝒪[v.adicCompletion K]
    (integralClosure 𝒪[v.adicCompletion K] (w.adicCompletion L))
  let g := (integralClosure 𝒪[v.adicCompletion K] (w.adicCompletion L)).val.toLinearMap ∘ₗ f
  have hg : Continuous g := LinearMap.continuous_on_pi g
  have : ((integralClosure 𝒪[v.adicCompletion K] (w.adicCompletion L) :
      Set (w.adicCompletion L))) = Set.range g := by
    ext y
    constructor
    · intro hy
      obtain ⟨c, hc⟩ := hf ⟨y, hy⟩
      exact ⟨c, by simp [g, hc]⟩
    · rintro ⟨c, rfl⟩
      exact (f c).2
  rw [this]
  exact (isCompact_range hg).isClosed

theorem isIntegral_of_mem_integer_general {x : w.adicCompletion L} (hx : x ∈ 𝒪[w.adicCompletion L]) :
    IsIntegral 𝒪[v.adicCompletion K] x := by
  have hx' : x ∈ w.adicCompletionIntegers L := (mem_valuationInteger_iff w x).1 hx
  have hsub : (Set.range fun r : 𝓞 L ↦
      algebraMap L (w.adicCompletion L) (algebraMap (𝓞 L) L r)) ⊆
      (integralClosure 𝒪[v.adicCompletion K] (w.adicCompletion L) : Set (w.adicCompletion L)) := by
    rintro _ ⟨r, rfl⟩
    exact isIntegral_algebraMap_ringOfIntegers_general v w r
  exact closure_minimal hsub (isClosed_integralClosure_general v w)
    (adicCompletionIntegers_subset_closure_ringOfIntegers w hx')

instance isIntegralClosure_integer_general :
    IsIntegralClosure 𝒪[w.adicCompletion L] 𝒪[v.adicCompletion K] (w.adicCompletion L) where
  algebraMap_injective := Subtype.val_injective
  isIntegral_iff {x} := ⟨fun hx ↦ ⟨⟨x, mem_integer_of_isIntegral_general v w hx⟩, rfl⟩,
    fun ⟨y, hy⟩ ↦ hy ▸ isIntegral_of_mem_integer_general v w y.2⟩

end IntegralClosure

section MaximalIdeal

variable {F : Type*} [Field F] [NumberField F] (u : HeightOneSpectrum (𝓞 F))

theorem integers_valued :
    (Valued.v : Valuation (u.adicCompletion F) ℤᵐ⁰).Integers 𝒪[u.adicCompletion F] where
  hom_inj a b h := Subtype.ext h
  map_le_one y := by
    have h : (y : u.adicCompletion F) ∈ u.adicCompletionIntegers F :=
      (mem_valuationInteger_iff u (y : u.adicCompletion F)).1 y.2
    exact h
  exists_of_le_one x hx := ⟨⟨x, (mem_valuationInteger_iff u x).2 hx⟩, rfl⟩

theorem mem_maximalIdeal_iff_valued_lt_one (y : 𝒪[u.adicCompletion F]) :
    y ∈ 𝓂[u.adicCompletion F] ↔ Valued.v (y : u.adicCompletion F) < 1 := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    (integers_valued u).isUnit_iff_valuation_eq_one]
  exact ⟨fun h ↦ lt_of_le_of_ne ((integers_valued u).map_le_one y) h, ne_of_lt⟩

theorem valued_of_irreducible_integer {ϖ : 𝒪[u.adicCompletion F]} (hϖ : Irreducible ϖ) :
    Valued.v (ϖ : u.adicCompletion F) = WithZero.exp (-1) := by
  apply le_antisymm
  · have h := (mem_maximalIdeal_iff_valued_lt_one u ϖ).1 hϖ.not_isUnit
    have h' : Valued.v (ϖ : u.adicCompletion F) < WithZero.exp (-1) * WithZero.exp 1 := by
      rwa [← WithZero.exp_add, neg_add_cancel, WithZero.exp_zero]
    exact (WithZero.lt_mul_exp_iff_le (by simp)).1 h'
  · have hlt : WithZero.exp (-1 : ℤ) < 1 := by
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
    obtain ⟨y, hy⟩ := valuedAdicCompletion_surjective F u (WithZero.exp (-1))
    have hy1 : Valued.v y ≤ 1 := by rw [hy]; exact hlt.le
    let y' : 𝒪[u.adicCompletion F] := ⟨y, (mem_valuationInteger_iff u y).2 hy1⟩
    have hy' : y' ∈ 𝓂[u.adicCompletion F] := by
      rw [mem_maximalIdeal_iff_valued_lt_one]
      change Valued.v y < 1
      rw [hy]; exact hlt
    rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton'] at hy'
    obtain ⟨c, hc⟩ := hy'
    rw [← hy, show y = ((c * ϖ : 𝒪[u.adicCompletion F]) : u.adicCompletion F) by rw [hc],
      Subring.coe_mul, map_mul]
    exact mul_le_of_le_one_left zero_le ((integers_valued u).map_le_one c)

theorem mem_maximalIdeal_pow_iff (y : 𝒪[u.adicCompletion F]) (n : ℕ) :
    y ∈ 𝓂[u.adicCompletion F] ^ n ↔ Valued.v (y : u.adicCompletion F) ≤ WithZero.exp (-(n : ℤ)) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[u.adicCompletion F]
  have h := (integers_valued u).maximalIdeal_pow_eq_setOfPred_le_v_algebraMap_pow hϖ n
  rw [← SetLike.mem_coe, h, Set.mem_ofPred_eq]
  change Valued.v (y : u.adicCompletion F) ≤ Valued.v (ϖ : u.adicCompletion F) ^ n ↔ _
  rw [valued_of_irreducible_integer u hϖ, ← WithZero.exp_nsmul]
  simp

end MaximalIdeal

section Degree

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]
  [Algebra (v.adicCompletion K) (w.adicCompletion L)]
  [ContinuousSMul (v.adicCompletion K) (w.adicCompletion L)]
  [IsScalarTower K (v.adicCompletion K) (w.adicCompletion L)]

instance charZero_adicCompletion {F : Type*} [Field F] [NumberField F]
    (u : HeightOneSpectrum (𝓞 F)) : CharZero (u.adicCompletion F) :=
  charZero_of_injective_algebraMap (algebraMap F (u.adicCompletion F)).injective

omit [Algebra K L] [w.asIdeal.LiesOver v.asIdeal]
  [ContinuousSMul (v.adicCompletion K) (w.adicCompletion L)]
  [IsScalarTower K (v.adicCompletion K) (w.adicCompletion L)] in
theorem isTorsionFree_integer_adicCompletion :
    Module.IsTorsionFree 𝒪[v.adicCompletion K] (w.adicCompletion L) := by
  rw [Module.isTorsionFree_iff_algebraMap_injective,
    IsScalarTower.algebraMap_eq 𝒪[v.adicCompletion K] (v.adicCompletion K) (w.adicCompletion L)]
  exact (algebraMap (v.adicCompletion K) (w.adicCompletion L)).injective.comp
    Subtype.val_injective

theorem finite_integer : Module.Finite 𝒪[v.adicCompletion K] 𝒪[w.adicCompletion L] :=
  IsIntegralClosure.finite 𝒪[v.adicCompletion K] (v.adicCompletion K) (w.adicCompletion L) _

theorem free_integer : Module.Free 𝒪[v.adicCompletion K] 𝒪[w.adicCompletion L] :=
  have := isTorsionFree_integer_adicCompletion v w
  IsIntegralClosure.module_free 𝒪[v.adicCompletion K] (v.adicCompletion K) (w.adicCompletion L) _

theorem finrank_integer :
    Module.finrank 𝒪[v.adicCompletion K] 𝒪[w.adicCompletion L] =
      Module.finrank (v.adicCompletion K) (w.adicCompletion L) :=
  have := isTorsionFree_integer_adicCompletion v w
  IsIntegralClosure.rank 𝒪[v.adicCompletion K] (v.adicCompletion K) (w.adicCompletion L) _

theorem ramificationIdx_mul_inertiaDeg_integer :
    𝓂[w.adicCompletion L].ramificationIdx 𝒪[v.adicCompletion K] *
        𝓂[w.adicCompletion L].inertiaDeg 𝒪[v.adicCompletion K] =
      Module.finrank (v.adicCompletion K) (w.adicCompletion L) := by
  have := finite_integer v w
  have := free_integer v w
  have hp0 : 𝓂[v.adicCompletion K] ≠ ⊥ := IsDiscreteValuationRing.not_a_field _
  have hset := IsLocalRing.primesOver_eq 𝒪[w.adicCompletion L] hp0
  have hmem : 𝓂[w.adicCompletion L] ∈ 𝓂[v.adicCompletion K].primesOver 𝒪[w.adicCompletion L] := by
    rw [hset]; rfl
  let : Unique (𝓂[v.adicCompletion K].primesOver 𝒪[w.adicCompletion L]) :=
    { default := ⟨_, hmem⟩
      uniq := fun q ↦ Subtype.ext ((Set.ext_iff.1 hset q).1 q.2) }
  have h := Ideal.sum_ramification_inertia_eq_finrank 𝓂[v.adicCompletion K] 𝒪[w.adicCompletion L]
  rw [Fintype.sum_unique, finrank_integer] at h
  exact h

theorem ramificationIdx_integer :
    𝓂[w.adicCompletion L].ramificationIdx 𝒪[v.adicCompletion K] =
      w.asIdeal.ramificationIdx (𝓞 K) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[v.adicCompletion K]
  have key : ∀ n : ℕ, Ideal.map (algebraMap 𝒪[v.adicCompletion K] 𝒪[w.adicCompletion L])
      𝓂[v.adicCompletion K] ≤ 𝓂[w.adicCompletion L] ^ n ↔
        n ≤ v.asIdeal.ramificationIdx' w.asIdeal := by
    intro n
    rw [hϖ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton, Ideal.span_singleton_le_iff_mem,
      mem_maximalIdeal_pow_iff, RHDirect.CFT.LocalField.coe_algebraMap_integer,
      valued_algebraMap_adicCompletion', valued_of_irreducible_integer v hϖ,
      ← WithZero.exp_nsmul, WithZero.exp_le_exp]
    simp only [smul_neg, nsmul_eq_mul, mul_one, neg_le_neg_iff, Nat.cast_le]
  have h := Ideal.ramificationIdx'_spec ((key _).2 le_rfl)
    (fun h ↦ by simpa using (key _).1 h)
  rw [← Ideal.ramificationIdx'_eq_ramificationIdx 𝓂[v.adicCompletion K] 𝓂[w.adicCompletion L]
    (IsDiscreteValuationRing.not_a_field _), h,
    Ideal.ramificationIdx'_eq_ramificationIdx v.asIdeal w.asIdeal v.ne_bot]

end Degree

end Sec_03_CompletionAtPlace_Integers

/-! ### 04_CompletionAtPlace.Degree -/
section Sec_04_CompletionAtPlace_Degree

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField ValuativeRel

open scoped WithZero


section Residue

variable {F : Type*} [Field F] [NumberField F] (u : HeightOneSpectrum (𝓞 F))

def ringOfIntegersToInteger : 𝓞 F →+* 𝒪[u.adicCompletion F] :=
  ((algebraMap F (u.adicCompletion F)).comp (algebraMap (𝓞 F) F)).codRestrict
    𝒪[u.adicCompletion F] fun r ↦ (mem_valuationInteger_iff u _).2 (coe_algebraMap_mem (𝓞 F) F u r)

@[simp]
theorem coe_ringOfIntegersToInteger (r : 𝓞 F) :
    (ringOfIntegersToInteger u r : u.adicCompletion F) =
      algebraMap F (u.adicCompletion F) (algebraMap (𝓞 F) F r) :=
  rfl

def toResidueInteger : 𝓞 F →+* 𝒪[u.adicCompletion F] ⧸ 𝓂[u.adicCompletion F] :=
  (Ideal.Quotient.mk _).comp (ringOfIntegersToInteger u)

theorem ker_toResidueInteger : RingHom.ker (toResidueInteger u) = u.asIdeal := by
  ext r
  rw [RingHom.mem_ker, toResidueInteger, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem,
    mem_maximalIdeal_iff_valued_lt_one, coe_ringOfIntegersToInteger]
  erw [valuedAdicCompletion_eq_valuation' u]
  exact valuation_lt_one_iff_mem u r

theorem toResidueInteger_surjective : Function.Surjective (toResidueInteger u) := by
  intro z
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
  have hy : (y : u.adicCompletion F) ∈ u.adicCompletionIntegers F :=
    (mem_valuationInteger_iff u _).1 y.2
  have hn : {z : u.adicCompletion F | Valued.v.restrict (z - y) <
      ((1 : (MonoidWithZeroHom.ValueGroup₀ (.ofClass (Valued.v :
        Valuation (u.adicCompletion F) ℤᵐ⁰)))ˣ) : _)} ∈ nhds (y : u.adicCompletion F) :=
    Valued.mem_nhds.2 ⟨1, subset_rfl⟩
  obtain ⟨_, hz, r, rfl⟩ := mem_closure_iff_nhds.1
    (adicCompletionIntegers_subset_closure_ringOfIntegers u hy) _ hn
  refine ⟨r, (Ideal.Quotient.eq.2 ?_)⟩
  rw [mem_maximalIdeal_iff_valued_lt_one]
  change Valued.v ((ringOfIntegersToInteger u r : u.adicCompletion F) - (y : u.adicCompletion F)) < 1
  rw [coe_ringOfIntegersToInteger]
  simpa [Valuation.restrict_lt_one_iff] using hz

def residueEquivInteger : (𝓞 F ⧸ u.asIdeal) ≃+* (𝒪[u.adicCompletion F] ⧸ 𝓂[u.adicCompletion F]) :=
  (Ideal.quotEquivOfEq (ker_toResidueInteger u).symm).trans
    (RingHom.quotientKerEquivOfSurjective (toResidueInteger_surjective u))

@[simp]
theorem residueEquivInteger_mk (r : 𝓞 F) :
    residueEquivInteger u (Ideal.Quotient.mk u.asIdeal r) =
      Ideal.Quotient.mk _ (ringOfIntegersToInteger u r) :=
  rfl

end Residue

section Degree

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]
  [Algebra (v.adicCompletion K) (w.adicCompletion L)]
  [ContinuousSMul (v.adicCompletion K) (w.adicCompletion L)]
  [IsScalarTower K (v.adicCompletion K) (w.adicCompletion L)]

theorem algebraMap_ringOfIntegersToInteger (r : 𝓞 K) :
    algebraMap 𝒪[v.adicCompletion K] 𝒪[w.adicCompletion L] (ringOfIntegersToInteger v r) =
      ringOfIntegersToInteger w (algebraMap (𝓞 K) (𝓞 L) r) := by
  apply Subtype.ext
  rw [RHDirect.CFT.LocalField.coe_algebraMap_integer, coe_ringOfIntegersToInteger,
    coe_ringOfIntegersToInteger, ← IsScalarTower.algebraMap_apply,
    IsScalarTower.algebraMap_apply K L (w.adicCompletion L)]
  rfl

theorem inertiaDeg_integer :
    𝓂[w.adicCompletion L].inertiaDeg 𝒪[v.adicCompletion K] = w.asIdeal.inertiaDeg (𝓞 K) := by
  have := w.isMaximal
  have := v.isMaximal
  rw [Ideal.inertiaDeg_eq_of_isMaximal 𝓂[v.adicCompletion K] 𝓂[w.adicCompletion L],
    Ideal.inertiaDeg_eq_of_isMaximal v.asIdeal w.asIdeal]
  refine (Algebra.finrank_eq_of_equiv_equiv (residueEquivInteger v) (residueEquivInteger w)
    ?_).symm
  apply Ideal.Quotient.ringHom_ext
  ext r
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    residueEquivInteger_mk]
  rw [Ideal.Quotient.algebraMap_mk_of_liesOver, Ideal.Quotient.algebraMap_mk_of_liesOver,
    residueEquivInteger_mk, algebraMap_ringOfIntegersToInteger]

theorem finrank_adicCompletion :
    Module.finrank (v.adicCompletion K) (w.adicCompletion L) =
      w.asIdeal.ramificationIdx (𝓞 K) * w.asIdeal.inertiaDeg (𝓞 K) := by
  rw [← ramificationIdx_mul_inertiaDeg_integer v w, ramificationIdx_integer v w,
    inertiaDeg_integer v w]

end Degree

section Check

open AdicLiesOver

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]

example : Module.finrank (v.adicCompletion K) (w.adicCompletion L) =
    w.asIdeal.ramificationIdx (𝓞 K) * w.asIdeal.inertiaDeg (𝓞 K) :=
  finrank_adicCompletion v w

end Check

end Sec_04_CompletionAtPlace_Degree

/-! ### 05_CompletionAtPlace.Galois -/
section Sec_05_CompletionAtPlace_Galois

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField

open scoped WithZero Pointwise


theorem eq_of_forall_le_exp_neg_iff {a b : ℤᵐ⁰} (ha : a ≤ 1) (hb : b ≤ 1)
    (h : ∀ n : ℕ, a ≤ WithZero.exp (-(n : ℤ)) ↔ b ≤ WithZero.exp (-(n : ℤ))) : a = b := by
  have key : ∀ a b : ℤᵐ⁰, b ≤ 1 →
      (∀ n : ℕ, b ≤ WithZero.exp (-(n : ℤ)) → a ≤ WithZero.exp (-(n : ℤ))) → a ≤ b := by
    intro a b hb h
    by_cases hb0 : b = 0
    · by_contra hab
      have ha0 : a ≠ 0 := by
        rintro rfl
        exact hab zero_le
      obtain ⟨n, hn⟩ := WithZero.exists_exp_neg_natCast_lt ha0
      exact absurd (h n (by rw [hb0]; exact zero_le)) (not_le.2 hn)
    · have hlog : WithZero.log b ≤ 0 := by
        rw [WithZero.log_le_iff_le_exp hb0, WithZero.exp_zero]
        exact hb
      have hn : (((-(WithZero.log b)).toNat : ℕ) : ℤ) = -WithZero.log b :=
        Int.toNat_of_nonneg (by omega)
      have hb' : WithZero.exp (-(((-(WithZero.log b)).toNat : ℕ) : ℤ)) = b := by
        rw [hn, neg_neg, WithZero.exp_log hb0]
      calc a ≤ _ := h _ hb'.ge
        _ = b := hb'
  exact le_antisymm (key a b hb fun n hn ↦ (h n).2 hn) (key b a ha fun n hn ↦ (h n).1 hn)

theorem uniformContinuous_of_valued_eq {R Γ₀ : Type*} [Ring R] [LinearOrderedCommGroupWithZero Γ₀]
    [Valued R Γ₀] (f : R →+* R) (hf : ∀ x, Valued.v (f x) = Valued.v x) : UniformContinuous f := by
  refine uniformContinuous_of_continuousAt_zero f ?_
  rw [ContinuousAt, map_zero]
  intro s hs
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.1 hs
  refine Valued.mem_nhds_zero.2 ⟨γ, fun x hx ↦ Set.mem_preimage.2 (hγ ?_)⟩
  simp only [Set.mem_ofPred_eq, Valuation.restrict_lt_iff_lt_embedding] at hx ⊢
  rwa [hf]

section Stabilizer

variable {K L : Type*} [Field K] [Field L] [NumberField L] [Algebra K L]
  (w : HeightOneSpectrum (𝓞 L))

omit [NumberField L] in
theorem smul_mem_asIdeal_pow_iff {σ : L ≃ₐ[K] L} (hσ : σ • w.asIdeal = w.asIdeal) (r : 𝓞 L)
    (n : ℕ) : σ • r ∈ w.asIdeal ^ n ↔ r ∈ w.asIdeal ^ n := by
  have h : σ • (w.asIdeal ^ n) = w.asIdeal ^ n := by
    rw [Ideal.pointwise_smul_def, Ideal.map_pow, ← Ideal.pointwise_smul_def, hσ]
  conv_lhs => rw [← h]
  exact Ideal.smul_mem_pointwise_smul_iff

theorem intValuation_smul {σ : L ≃ₐ[K] L} (hσ : σ • w.asIdeal = w.asIdeal) (r : 𝓞 L) :
    w.intValuation (σ • r) = w.intValuation r :=
  eq_of_forall_le_exp_neg_iff (w.intValuation_le_one _) (w.intValuation_le_one _) fun n ↦ by
    rw [intValuation_le_pow_iff_mem, intValuation_le_pow_iff_mem, smul_mem_asIdeal_pow_iff w hσ]

theorem valuation_algEquiv_apply_of_smul_eq {σ : L ≃ₐ[K] L} (hσ : σ • w.asIdeal = w.asIdeal)
    (x : L) : w.valuation L (σ x) = w.valuation L x := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 L) x
  have hs : ∀ c : 𝓞 L, σ (algebraMap (𝓞 L) L c) = algebraMap (𝓞 L) L (σ • c) := fun c ↦ rfl
  rw [map_div₀, map_div₀, map_div₀, hs, hs, valuation_of_algebraMap, valuation_of_algebraMap,
    valuation_of_algebraMap, valuation_of_algebraMap, intValuation_smul w hσ,
    intValuation_smul w hσ]

end Stabilizer

section CompletionMap

variable {K L : Type*} [Field K] [Field L] [NumberField L] [Algebra K L]
  (w : HeightOneSpectrum (𝓞 L))

def adicCompletionRingHomOf (σ : L ≃ₐ[K] L) (hσ : σ • w.asIdeal = w.asIdeal) :
    w.adicCompletion L →+* w.adicCompletion L :=
  (adicCompletion.equiv L w).symm.toRingHom.comp
    ((UniformSpace.Completion.mapRingHom
        (WithVal.map (w.valuation L) (w.valuation L) (σ : L →+* L))
        (uniformContinuous_of_valued_eq _
          fun x ↦ valuation_algEquiv_apply_of_smul_eq w hσ (WithVal.equiv _ x)).continuous).comp
      (adicCompletion.equiv L w).toRingHom)

variable {w}

theorem continuous_adicCompletionRingHomOf (σ : L ≃ₐ[K] L) (hσ : σ • w.asIdeal = w.asIdeal) :
    Continuous (adicCompletionRingHomOf w σ hσ) :=
  (adicCompletion.continuous_ofCompletion L w).comp <|
    UniformSpace.Completion.continuous_map.comp (adicCompletion.continuous_toCompletion L w)

theorem adicCompletionRingHomOf_algebraMap (σ : L ≃ₐ[K] L) (hσ : σ • w.asIdeal = w.asIdeal)
    (x : L) : adicCompletionRingHomOf w σ hσ (algebraMap L (w.adicCompletion L) x) =
      algebraMap L (w.adicCompletion L) (σ x) := by
  apply adicCompletion.ext
  change UniformSpace.Completion.mapRingHom _
    (uniformContinuous_of_valued_eq _
      fun x ↦ valuation_algEquiv_apply_of_smul_eq w hσ (WithVal.equiv _ x)).continuous
    ((algebraMap L (WithVal (w.valuation L)) x : WithVal (w.valuation L)) :
      UniformSpace.Completion (WithVal (w.valuation L))) = _
  rw [UniformSpace.Completion.mapRingHom_coe]
  rfl

variable (w) in

theorem ringHom_ext_adicCompletion {f g : w.adicCompletion L →+* w.adicCompletion L}
    (hf : Continuous f) (hg : Continuous g)
    (h : ∀ x : L, f (algebraMap L _ x) = g (algebraMap L _ x)) : f = g :=
  RingHom.ext (congrFun ((denseRange_algebraMap (R := 𝓞 L) (K := L) w).equalizer hf hg
    (funext h)))

theorem valued_adicCompletionRingHomOf (σ : L ≃ₐ[K] L) (hσ : σ • w.asIdeal = w.asIdeal)
    (y : w.adicCompletion L) : Valued.v (adicCompletionRingHomOf w σ hσ y) = Valued.v y := by
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  have hy' : Valued.v y ≠ 0 := by simpa using hy
  have hz : Valued.v (adicCompletionRingHomOf w σ hσ y) ≠ 0 := by simpa using hy
  have h1 := Valued.locally_const hy'
  have h2 := (continuous_adicCompletionRingHomOf σ hσ).continuousAt.preimage_mem_nhds
    (Valued.locally_const hz)
  obtain ⟨k, hk1, hk2⟩ := (denseRange_algebraMap (R := 𝓞 L) (K := L) w).mem_nhds
    (Filter.inter_mem h1 h2)
  simp only [Set.mem_preimage, Set.mem_ofPred_eq] at hk1 hk2
  rw [← hk1, ← hk2, adicCompletionRingHomOf_algebraMap]
  erw [valuedAdicCompletion_eq_valuation' w, valuedAdicCompletion_eq_valuation' w]
  exact valuation_algEquiv_apply_of_smul_eq w hσ k

end CompletionMap

section Decomposition

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]
  [Algebra (v.adicCompletion K) (w.adicCompletion L)]
  [ContinuousSMul (v.adicCompletion K) (w.adicCompletion L)]
  [IsScalarTower K (v.adicCompletion K) (w.adicCompletion L)]

omit [w.asIdeal.LiesOver v.asIdeal] in

theorem adicCompletionRingHomOf_algebraMap_adicCompletion (σ : L ≃ₐ[K] L)
    (hσ : σ • w.asIdeal = w.asIdeal) (c : v.adicCompletion K) :
    adicCompletionRingHomOf w σ hσ (algebraMap (v.adicCompletion K) (w.adicCompletion L) c) =
      algebraMap (v.adicCompletion K) (w.adicCompletion L) c := by
  have h := (denseRange_algebraMap (R := 𝓞 K) (K := K) v).equalizer
    ((continuous_adicCompletionRingHomOf σ hσ).comp
      (continuous_algebraMap (v.adicCompletion K) (w.adicCompletion L)))
    (continuous_algebraMap (v.adicCompletion K) (w.adicCompletion L)) (funext fun k ↦ ?_)
  · exact congrFun h c
  · simp only [Function.comp_apply]
    rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply K L (w.adicCompletion L),
      adicCompletionRingHomOf_algebraMap, AlgEquiv.commutes]

omit [NumberField K] [NumberField L] in
theorem smul_asIdeal_of_mem_stabilizer (σ : MulAction.stabilizer Gal(L/K) w.asIdeal) :
    (σ : Gal(L/K)) • w.asIdeal = w.asIdeal :=
  MulAction.mem_stabilizer_iff.1 σ.2

def decompositionAlgEquiv (σ : MulAction.stabilizer Gal(L/K) w.asIdeal) :
    w.adicCompletion L ≃ₐ[v.adicCompletion K] w.adicCompletion L :=
  AlgEquiv.ofRingEquiv (f := RingEquiv.ofRingHom (adicCompletionRingHomOf w σ.1 (smul_asIdeal_of_mem_stabilizer w σ))
    (adicCompletionRingHomOf w (σ⁻¹).1 (smul_asIdeal_of_mem_stabilizer w σ⁻¹))
    (ringHom_ext_adicCompletion w
      ((continuous_adicCompletionRingHomOf σ.1 (smul_asIdeal_of_mem_stabilizer w σ)).comp
      (continuous_adicCompletionRingHomOf (σ⁻¹).1 (smul_asIdeal_of_mem_stabilizer w σ⁻¹)))
      continuous_id fun x ↦ by
        rw [RingHom.comp_apply, adicCompletionRingHomOf_algebraMap,
          adicCompletionRingHomOf_algebraMap]
        simp)
    (ringHom_ext_adicCompletion w
      ((continuous_adicCompletionRingHomOf (σ⁻¹).1 (smul_asIdeal_of_mem_stabilizer w σ⁻¹)).comp
      (continuous_adicCompletionRingHomOf σ.1 (smul_asIdeal_of_mem_stabilizer w σ)))
      continuous_id fun x ↦ by
        rw [RingHom.comp_apply, adicCompletionRingHomOf_algebraMap,
          adicCompletionRingHomOf_algebraMap]
        simp))
    (adicCompletionRingHomOf_algebraMap_adicCompletion v w σ.1 (smul_asIdeal_of_mem_stabilizer w σ))

omit [w.asIdeal.LiesOver v.asIdeal] in
@[simp]
theorem decompositionAlgEquiv_algebraMap (σ : MulAction.stabilizer Gal(L/K) w.asIdeal) (x : L) :
    decompositionAlgEquiv v w σ (algebraMap L (w.adicCompletion L) x) =
      algebraMap L (w.adicCompletion L) ((σ : Gal(L/K)) x) :=
  adicCompletionRingHomOf_algebraMap σ.1 (smul_asIdeal_of_mem_stabilizer w σ) x

omit [w.asIdeal.LiesOver v.asIdeal] in
theorem continuous_decompositionAlgEquiv (σ : MulAction.stabilizer Gal(L/K) w.asIdeal) :
    Continuous (decompositionAlgEquiv v w σ) :=
  continuous_adicCompletionRingHomOf σ.1 (smul_asIdeal_of_mem_stabilizer w σ)

omit [w.asIdeal.LiesOver v.asIdeal] in

theorem valued_decompositionAlgEquiv (σ : MulAction.stabilizer Gal(L/K) w.asIdeal)
    (y : w.adicCompletion L) : Valued.v (decompositionAlgEquiv v w σ y) = Valued.v y :=
  valued_adicCompletionRingHomOf σ.1 (smul_asIdeal_of_mem_stabilizer w σ) y

omit [Algebra K L] [w.asIdeal.LiesOver v.asIdeal]
  [ContinuousSMul (v.adicCompletion K) (w.adicCompletion L)]
  [IsScalarTower K (v.adicCompletion K) (w.adicCompletion L)] in
theorem algEquiv_ext_adicCompletion {f g : w.adicCompletion L ≃ₐ[v.adicCompletion K]
    w.adicCompletion L} (hf : Continuous f) (hg : Continuous g)
    (h : ∀ x : L, f (algebraMap L _ x) = g (algebraMap L _ x)) : f = g :=
  AlgEquiv.ext fun y ↦ congrFun (congrArg DFunLike.coe
    (ringHom_ext_adicCompletion w (f := (f : w.adicCompletion L →+* w.adicCompletion L))
      (g := (g : w.adicCompletion L →+* w.adicCompletion L)) hf hg h)) y

def decompositionToLocal :
    MulAction.stabilizer Gal(L/K) w.asIdeal →* Gal(w.adicCompletion L/v.adicCompletion K) where
  toFun := decompositionAlgEquiv v w
  map_one' := algEquiv_ext_adicCompletion v w (continuous_decompositionAlgEquiv v w 1)
    continuous_id fun x ↦ by simp
  map_mul' σ τ := algEquiv_ext_adicCompletion v w (continuous_decompositionAlgEquiv v w _)
    ((continuous_decompositionAlgEquiv v w σ).comp (continuous_decompositionAlgEquiv v w τ))
    fun x ↦ by simp

omit [w.asIdeal.LiesOver v.asIdeal] in
@[simp]
theorem decompositionToLocal_algebraMap (σ : MulAction.stabilizer Gal(L/K) w.asIdeal) (x : L) :
    decompositionToLocal v w σ (algebraMap L (w.adicCompletion L) x) =
      algebraMap L (w.adicCompletion L) ((σ : Gal(L/K)) x) :=
  decompositionAlgEquiv_algebraMap v w σ x

omit [w.asIdeal.LiesOver v.asIdeal] in

theorem decompositionToLocal_injective : Function.Injective (decompositionToLocal v w) := by
  rw [injective_iff_map_eq_one]
  intro σ hσ
  apply Subtype.ext
  apply AlgEquiv.ext
  intro x
  have := congrArg (fun f : Gal(w.adicCompletion L/v.adicCompletion K) ↦
    f (algebraMap L (w.adicCompletion L) x)) hσ
  simp only [decompositionToLocal_algebraMap, AlgEquiv.one_apply] at this
  exact (algebraMap L (w.adicCompletion L)).injective this

end Decomposition

section Galois

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]
  [Algebra (v.adicCompletion K) (w.adicCompletion L)]
  [ContinuousSMul (v.adicCompletion K) (w.adicCompletion L)]
  [IsScalarTower K (v.adicCompletion K) (w.adicCompletion L)]

omit [Algebra (v.adicCompletion K) (w.adicCompletion L)]
  [ContinuousSMul (v.adicCompletion K) (w.adicCompletion L)]
  [IsScalarTower K (v.adicCompletion K) (w.adicCompletion L)] in
include v in

theorem card_decompositionGroup :
    Nat.card (MulAction.stabilizer Gal(L/K) w.asIdeal) =
      w.asIdeal.ramificationIdx (𝓞 K) * w.asIdeal.inertiaDeg (𝓞 K) := by
  rw [Ideal.card_stabilizer_eq v.asIdeal w.asIdeal,
    Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal w.asIdeal Gal(L/K),
    Ideal.inertiaDegIn_eq_inertiaDeg v.asIdeal w.asIdeal Gal(L/K)]

theorem decompositionToLocal_bijective : Function.Bijective (decompositionToLocal v w) := by
  refine (decompositionToLocal_injective v w).bijective_of_nat_card_le ?_
  rw [card_decompositionGroup v w, ← finrank_adicCompletion v w, Nat.card_eq_fintype_card]
  exact AlgEquiv.card_le

def decompositionMulEquiv :
    MulAction.stabilizer Gal(L/K) w.asIdeal ≃* Gal(w.adicCompletion L/v.adicCompletion K) :=
  MulEquiv.ofBijective (decompositionToLocal v w) (decompositionToLocal_bijective v w)

@[simp]
theorem decompositionMulEquiv_apply (σ : MulAction.stabilizer Gal(L/K) w.asIdeal) :
    decompositionMulEquiv v w σ = decompositionToLocal v w σ :=
  rfl

instance isGalois_adicCompletion : IsGalois (v.adicCompletion K) (w.adicCompletion L) :=
  IsGalois.of_card_aut_eq_finrank _ _ (by
    rw [← Nat.card_congr (decompositionMulEquiv v w).toEquiv, card_decompositionGroup v w,
      finrank_adicCompletion v w])

end Galois

end Sec_05_CompletionAtPlace_Galois

/-! ### 06_CompletionAtPlace.Inertia -/
section Sec_06_CompletionAtPlace_Inertia

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField ValuativeRel
  RHDirect.CFT.LocalField

open scoped WithZero Pointwise


section Residue

variable {F : Type*} [Field F] [NumberField F] (u : HeightOneSpectrum (𝓞 F))

theorem exists_sub_ringOfIntegersToInteger_mem (x : 𝒪[u.adicCompletion F]) :
    ∃ r : 𝓞 F, x - ringOfIntegersToInteger u r ∈ 𝓂[u.adicCompletion F] := by
  obtain ⟨r, hr⟩ := toResidueInteger_surjective u (Ideal.Quotient.mk _ x)
  exact ⟨r, Ideal.Quotient.eq.1 hr.symm⟩

theorem ringOfIntegersToInteger_mem_maximalIdeal_iff (r : 𝓞 F) :
    ringOfIntegersToInteger u r ∈ 𝓂[u.adicCompletion F] ↔ r ∈ u.asIdeal := by
  rw [← ker_toResidueInteger u, RingHom.mem_ker, toResidueInteger, RingHom.comp_apply,
    Ideal.Quotient.eq_zero_iff_mem]

theorem natCard_residueField_integer :
    Nat.card 𝓀[u.adicCompletion F] = Nat.card (𝓞 F ⧸ u.asIdeal) :=
  (Nat.card_congr (residueEquivInteger u).toEquiv).symm

end Residue

section Inertia

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]
  [Algebra (v.adicCompletion K) (w.adicCompletion L)]
  [ContinuousSMul (v.adicCompletion K) (w.adicCompletion L)]
  [IsScalarTower K (v.adicCompletion K) (w.adicCompletion L)]

theorem integerAlgEquiv_ringOfIntegersToInteger (σ : MulAction.stabilizer Gal(L/K) w.asIdeal)
    (r : 𝓞 L) :
    integerAlgEquiv (v.adicCompletion K) (w.adicCompletion L) (decompositionToLocal v w σ)
        (ringOfIntegersToInteger w r) = ringOfIntegersToInteger w ((σ : Gal(L/K)) • r) := by
  apply Subtype.ext
  rw [coe_integerAlgEquiv_apply, coe_ringOfIntegersToInteger, coe_ringOfIntegersToInteger,
    decompositionToLocal_algebraMap]
  rfl

theorem integerAlgEquiv_mem_maximalIdeal_iff (τ : Gal(w.adicCompletion L/v.adicCompletion K))
    (x : 𝒪[w.adicCompletion L]) :
    integerAlgEquiv (v.adicCompletion K) (w.adicCompletion L) τ x ∈ 𝓂[w.adicCompletion L] ↔
      x ∈ 𝓂[w.adicCompletion L] := by
  simp [integerAlgEquiv_mem_maximalIdeal_pow_iff τ 1 x]

theorem mem_inertia_iff_decompositionToLocal_mem (σ : MulAction.stabilizer Gal(L/K) w.asIdeal) :
    (σ : Gal(L/K)) ∈ w.asIdeal.inertia Gal(L/K) ↔
      decompositionToLocal v w σ ∈
        lowerRamificationGroup (v.adicCompletion K) (w.adicCompletion L) 0 := by
  have h0 : ((0 : ℕ) : ℤ) = 0 := rfl
  rw [← h0, mem_lowerRamificationGroup_natCast_iff, zero_add, pow_one]
  change (∀ r : 𝓞 L, (σ : Gal(L/K)) • r - r ∈ w.asIdeal) ↔ _
  constructor
  · intro h x
    obtain ⟨r, hr⟩ := exists_sub_ringOfIntegersToInteger_mem w x
    have h1 := (integerAlgEquiv_mem_maximalIdeal_iff v w (decompositionToLocal v w σ) _).2 hr
    have h2 : integerAlgEquiv (v.adicCompletion K) (w.adicCompletion L)
        (decompositionToLocal v w σ) (ringOfIntegersToInteger w r) -
          ringOfIntegersToInteger w r ∈ 𝓂[w.adicCompletion L] := by
      rw [integerAlgEquiv_ringOfIntegersToInteger, ← map_sub,
        ringOfIntegersToInteger_mem_maximalIdeal_iff]
      exact h r
    rw [map_sub] at h1
    have : integerAlgEquiv (v.adicCompletion K) (w.adicCompletion L)
        (decompositionToLocal v w σ) x - x =
        (integerAlgEquiv (v.adicCompletion K) (w.adicCompletion L)
          (decompositionToLocal v w σ) x - integerAlgEquiv (v.adicCompletion K)
            (w.adicCompletion L) (decompositionToLocal v w σ) (ringOfIntegersToInteger w r)) +
        (integerAlgEquiv (v.adicCompletion K) (w.adicCompletion L)
          (decompositionToLocal v w σ) (ringOfIntegersToInteger w r) -
            ringOfIntegersToInteger w r) - (x - ringOfIntegersToInteger w r) := by
      ring
    rw [this]
    exact sub_mem (add_mem h1 h2) hr
  · intro h r
    have := h (ringOfIntegersToInteger w r)
    rwa [integerAlgEquiv_ringOfIntegersToInteger, ← map_sub,
      ringOfIntegersToInteger_mem_maximalIdeal_iff] at this

end Inertia

section Frobenius

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]
  [Algebra (v.adicCompletion K) (w.adicCompletion L)]
  [ContinuousSMul (v.adicCompletion K) (w.adicCompletion L)]
  [IsScalarTower K (v.adicCompletion K) (w.adicCompletion L)]

def arithFrobAtDecomposition : MulAction.stabilizer Gal(L/K) w.asIdeal :=
  ⟨arithFrobAt (𝓞 K) Gal(L/K) w.asIdeal, IsArithFrobAt.arithFrobAt_mem_stabilizer (𝓞 K) Gal(L/K) w.asIdeal⟩

omit [NumberField L] [IsGalois K L] [Algebra (v.adicCompletion K) (w.adicCompletion L)]
  [ContinuousSMul (v.adicCompletion K) (w.adicCompletion L)]
  [IsScalarTower K (v.adicCompletion K) (w.adicCompletion L)] in
include v in

theorem natCard_residueField_eq_under :
    Nat.card 𝓀[v.adicCompletion K] = Nat.card (𝓞 K ⧸ w.asIdeal.under (𝓞 K)) := by
  rw [natCard_residueField_integer v, ← Ideal.over_def w.asIdeal v.asIdeal]

omit [IsGalois K L] in
theorem isArithFrobAt_iff_decompositionToLocal (σ : MulAction.stabilizer Gal(L/K) w.asIdeal) :
    IsArithFrobAt (𝓞 K) (σ : Gal(L/K)) w.asIdeal ↔
      ∀ x : 𝒪[w.adicCompletion L], integerAlgEquiv (v.adicCompletion K) (w.adicCompletion L)
        (decompositionToLocal v w σ) x - x ^ Nat.card 𝓀[v.adicCompletion K] ∈
          𝓂[w.adicCompletion L] := by
  rw [natCard_residueField_eq_under v w]
  change (∀ r : 𝓞 L, (σ : Gal(L/K)) • r - r ^ Nat.card (𝓞 K ⧸ w.asIdeal.under (𝓞 K)) ∈
    w.asIdeal) ↔ _
  constructor
  · intro h x
    obtain ⟨r, hr⟩ := exists_sub_ringOfIntegersToInteger_mem w x
    set q := Nat.card (𝓞 K ⧸ w.asIdeal.under (𝓞 K))
    have h1 := (integerAlgEquiv_mem_maximalIdeal_iff v w (decompositionToLocal v w σ) _).2 hr
    rw [map_sub] at h1
    have h2 : integerAlgEquiv (v.adicCompletion K) (w.adicCompletion L)
        (decompositionToLocal v w σ) (ringOfIntegersToInteger w r) -
          ringOfIntegersToInteger w r ^ q ∈ 𝓂[w.adicCompletion L] := by
      rw [integerAlgEquiv_ringOfIntegersToInteger, ← map_pow, ← map_sub,
        ringOfIntegersToInteger_mem_maximalIdeal_iff]
      exact h r
    have h3 : ringOfIntegersToInteger w r ^ q - x ^ q ∈ 𝓂[w.adicCompletion L] := by
      rw [← Ideal.Quotient.eq, map_pow, map_pow, Ideal.Quotient.eq.2 hr]
    have : integerAlgEquiv (v.adicCompletion K) (w.adicCompletion L)
        (decompositionToLocal v w σ) x - x ^ q =
        (integerAlgEquiv (v.adicCompletion K) (w.adicCompletion L)
          (decompositionToLocal v w σ) x - integerAlgEquiv (v.adicCompletion K)
            (w.adicCompletion L) (decompositionToLocal v w σ) (ringOfIntegersToInteger w r)) +
        (integerAlgEquiv (v.adicCompletion K) (w.adicCompletion L)
          (decompositionToLocal v w σ) (ringOfIntegersToInteger w r) -
            ringOfIntegersToInteger w r ^ q) + (ringOfIntegersToInteger w r ^ q - x ^ q) := by
      ring
    rw [this]
    exact add_mem (add_mem h1 h2) h3
  · intro h r
    have := h (ringOfIntegersToInteger w r)
    rwa [integerAlgEquiv_ringOfIntegersToInteger, ← map_pow, ← map_sub,
      ringOfIntegersToInteger_mem_maximalIdeal_iff] at this

theorem decompositionToLocal_arithFrobAt (x : 𝒪[w.adicCompletion L]) :
    integerAlgEquiv (v.adicCompletion K) (w.adicCompletion L)
        (decompositionToLocal v w (arithFrobAtDecomposition w)) x -
      x ^ Nat.card 𝓀[v.adicCompletion K] ∈ 𝓂[w.adicCompletion L] :=
  (isArithFrobAt_iff_decompositionToLocal v w _).1 (IsArithFrobAt.arithFrobAt _ _ _) x

omit [Algebra (v.adicCompletion K) (w.adicCompletion L)]
  [ContinuousSMul (v.adicCompletion K) (w.adicCompletion L)]
  [IsScalarTower K (v.adicCompletion K) (w.adicCompletion L)] in
include v in

theorem natCard_inertia :
    Nat.card (w.asIdeal.inertia Gal(L/K)) = w.asIdeal.ramificationIdx (𝓞 K) := by
  rw [Ideal.card_inertia_eq_ramificationIdxIn (G := Gal(L/K)) v.asIdeal w.asIdeal,
    Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal w.asIdeal Gal(L/K)]

theorem eq_decompositionToLocal_arithFrobAt (he : w.asIdeal.ramificationIdx (𝓞 K) = 1)
    (τ : Gal(w.adicCompletion L/v.adicCompletion K))
    (hτ : ∀ x : 𝒪[w.adicCompletion L], integerAlgEquiv (v.adicCompletion K) (w.adicCompletion L)
      τ x - x ^ Nat.card 𝓀[v.adicCompletion K] ∈ 𝓂[w.adicCompletion L]) :
    τ = decompositionToLocal v w (arithFrobAtDecomposition w) := by
  obtain ⟨σ, rfl⟩ := (decompositionToLocal_bijective v w).2 τ
  congr 1
  have hσ : IsArithFrobAt (𝓞 K) (σ : Gal(L/K)) w.asIdeal :=
    (isArithFrobAt_iff_decompositionToLocal v w σ).2 hτ
  have hmem := hσ.mul_inv_mem_inertia (IsArithFrobAt.arithFrobAt (𝓞 K) Gal(L/K) w.asIdeal)
  have hbot : w.asIdeal.inertia Gal(L/K) = ⊥ :=
    Subgroup.eq_bot_of_card_eq _ ((natCard_inertia v w).trans he)
  rw [hbot, Subgroup.mem_bot, mul_inv_eq_one] at hmem
  exact Subtype.ext hmem

end Frobenius

section InertiaGalois

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]
  [Algebra (v.adicCompletion K) (w.adicCompletion L)]
  [ContinuousSMul (v.adicCompletion K) (w.adicCompletion L)]
  [IsScalarTower K (v.adicCompletion K) (w.adicCompletion L)]

theorem map_inertia_decompositionMulEquiv :
    ((w.asIdeal.inertia Gal(L/K)).subgroupOf (MulAction.stabilizer Gal(L/K) w.asIdeal)).map
        (decompositionMulEquiv v w).toMonoidHom =
      lowerRamificationGroup (v.adicCompletion K) (w.adicCompletion L) 0 := by
  ext τ
  obtain ⟨σ, rfl⟩ := (decompositionMulEquiv v w).surjective τ
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨σ', hσ', h⟩
    rw [← h]
    exact (mem_inertia_iff_decompositionToLocal_mem v w σ').1 (Subgroup.mem_subgroupOf.1 hσ')
  · intro h
    exact ⟨σ, Subgroup.mem_subgroupOf.2 ((mem_inertia_iff_decompositionToLocal_mem v w σ).2 h),
      rfl⟩

end InertiaGalois

end Sec_06_CompletionAtPlace_Inertia

/-! ### 07_KummerTheory.Splitting -/
section Sec_07_KummerTheory_Splitting

open IsDedekindDomain NumberField Module
open scoped TensorProduct

section Algebra

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

theorem mem_range_algebraMap_of_surjective_pi {ι : Type*} [Fintype ι]
    (f : (ι → F) →ₐ[F] E) (hf : Function.Surjective f) (e : E) :
    e ∈ Set.range (algebraMap F E) := by
  obtain ⟨y, rfl⟩ := hf e
  have h0 : ∏ i, (y - algebraMap F (ι → F) (y i)) = 0 := by
    funext j
    rw [Finset.prod_apply]
    exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp)
  have h1 : ∏ i, (f y - algebraMap F E (y i)) = 0 := by
    simpa [map_prod, map_sub, AlgHom.commutes] using congrArg f h0
  obtain ⟨i, -, hi⟩ := Finset.prod_eq_zero_iff.mp h1
  exact ⟨y i, (sub_eq_zero.mp hi).symm⟩

theorem finrank_eq_one_of_surjective_pi {ι : Type*} [Fintype ι]
    (f : (ι → F) →ₐ[F] E) (hf : Function.Surjective f) : finrank F E = 1 := by
  rw [← Subalgebra.bot_eq_top_iff_finrank_eq_one]
  exact eq_top_iff.2 fun e _ ↦ Algebra.mem_bot.2 (mem_range_algebraMap_of_surjective_pi f hf e)

def algEquivOfFinrankEqOne (h : finrank F E = 1) : F ≃ₐ[F] E :=
  AlgEquiv.ofBijective (Algebra.ofId F E) (Algebra.finrank_eq_one_iff_bijective_algebraMap.1 h)

theorem isFiniteSplit_pi_iff {ι : Type*} [Finite ι] {E : ι → Type*} [∀ i, Field (E i)]
    [∀ i, Algebra F (E i)] :
    Algebra.IsFiniteSplit F (∀ i, E i) ↔ ∀ i, finrank F (E i) = 1 := by
  constructor
  · intro h i
    obtain ⟨n, ⟨e⟩⟩ := Algebra.IsFiniteSplit.nonempty_algEquiv_fun F (∀ i, E i)
    refine finrank_eq_one_of_surjective_pi ((Pi.evalAlgHom F E i).comp e.symm.toAlgHom) ?_
    exact (Function.surjective_eval i).comp e.symm.surjective
  · intro h
    exact .of_algEquiv (AlgEquiv.piCongrRight fun i ↦ algEquivOfFinrankEqOne (h i))

end Algebra

section Finite

open SemiLocal

variable {K : Type*} [Field K] [NumberField K] (L : Type*) [Field L] [NumberField L] [Algebra K L]

def SplitsCompletely (v : HeightOneSpectrum (𝓞 K)) : Prop :=
  ∀ w : HeightOneSpectrum (𝓞 L), w.asIdeal.LiesOver v.asIdeal →
    w.asIdeal.ramificationIdx (𝓞 K) = 1 ∧ w.asIdeal.inertiaDeg (𝓞 K) = 1

variable {L} (v : HeightOneSpectrum (𝓞 K))

theorem splitsCompletely_iff_forall_finrank :
    SplitsCompletely L v ↔
      ∀ w : PlacesOver L v, finrank (v.adicCompletion K) (w.1.adicCompletion L) = 1 := by
  constructor
  · intro h w
    obtain ⟨h1, h2⟩ := h w.1 w.2
    rw [finrank_eq_ramificationIdx_mul_inertiaDeg L v w.1, h1, h2]
  · intro h w hw
    have := h ⟨w, hw⟩
    rw [finrank_eq_ramificationIdx_mul_inertiaDeg L v w] at this
    exact mul_eq_one.mp this

theorem splitsCompletely_iff_isFiniteSplit :
    SplitsCompletely L v ↔
      Algebra.IsFiniteSplit (v.adicCompletion K) (v.adicCompletion K ⊗[K] L) := by
  rw [splitsCompletely_iff_forall_finrank, ← isFiniteSplit_pi_iff]
  exact ⟨fun h ↦ .of_algEquiv (tensorEquiv L v).symm, fun h ↦ .of_algEquiv (tensorEquiv L v)⟩

variable (L) in

theorem nonempty_placesOver : Nonempty (PlacesOver L v) := by
  by_contra h
  rw [not_nonempty_iff] at h
  have := sum_finrank_eq L v
  rw [Finset.univ_eq_empty, Finset.sum_empty] at this
  exact (Module.finrank_pos (R := K) (M := L)).ne this

theorem finrank_eq_of_isGalois [IsGalois K L] (w w' : PlacesOver L v) :
    finrank (v.adicCompletion K) (w.1.adicCompletion L) =
      finrank (v.adicCompletion K) (w'.1.adicCompletion L) := by
  obtain ⟨σ, hσ⟩ := MulAction.exists_smul_eq (L ≃ₐ[K] L) w w'
  exact (galEquiv v σ w.1 w'.1 (congrArg Subtype.val hσ.symm)).toLinearEquiv.finrank_eq

theorem splitsCompletely_iff_exists_finrank [IsGalois K L] :
    SplitsCompletely L v ↔
      ∃ w : PlacesOver L v, finrank (v.adicCompletion K) (w.1.adicCompletion L) = 1 := by
  rw [splitsCompletely_iff_forall_finrank]
  refine ⟨fun h ↦ ?_, fun ⟨w, hw⟩ w' ↦ (finrank_eq_of_isGalois v w w').symm.trans hw⟩
  obtain ⟨w⟩ := nonempty_placesOver L v
  exact ⟨w, h w⟩

end Finite

end Sec_07_KummerTheory_Splitting

/-! ### 08_IdeleGroups.LocalNorms -/
section Sec_08_IdeleGroups_LocalNorms

open IsDedekindDomain NumberField Filter
open AdeleBaseChange SemiLocal
open scoped NumberField.AdeleRing NumberField.LiesOver


namespace IdeleNorm

variable {K : Type*} [Field K] [NumberField K] (L : Type*) [Field L] [NumberField L]
  [Algebra K L]

def finiteLocalNorm (v : HeightOneSpectrum (𝓞 K)) :
    ((w : PlacesOver L v) → (w.1.adicCompletion L)ˣ) →* (v.adicCompletion K)ˣ where
  toFun y := ∏ w, Units.map (Algebra.norm (v.adicCompletion K) :
    w.1.adicCompletion L →* v.adicCompletion K) (y w)
  map_one' := by simp
  map_mul' y z := by simp only [Pi.mul_apply, map_mul, Finset.prod_mul_distrib]

variable {L} in

theorem coe_finiteLocalNorm (v : HeightOneSpectrum (𝓞 K))
    (y : (w : PlacesOver L v) → (w.1.adicCompletion L)ˣ) :
    ((finiteLocalNorm L v y : (v.adicCompletion K)ˣ) : v.adicCompletion K) =
      ∏ w, Algebra.norm (v.adicCompletion K) (y w : w.1.adicCompletion L) := by
  simp [finiteLocalNorm, Units.coe_prod]

def integerUnitsOver (v : HeightOneSpectrum (𝓞 K)) :
    Subgroup ((w : PlacesOver L v) → (w.1.adicCompletion L)ˣ) :=
  Subgroup.pi Set.univ fun w ↦ (Submonoid.ofClass (w.1.adicCompletionIntegers L)).units

omit [NumberField K] in
variable {L} in

theorem mem_integerUnitsOver {v : HeightOneSpectrum (𝓞 K)}
    {y : (w : PlacesOver L v) → (w.1.adicCompletion L)ˣ} :
    y ∈ integerUnitsOver L v ↔
      ∀ w, y w ∈ (Submonoid.ofClass (w.1.adicCompletionIntegers L)).units := by
  simp [integerUnitsOver, Subgroup.mem_pi]

open scoped Classical in

def infiniteLocalNorm (v : InfinitePlace K) :
    ((w : v.placesOver L) → ((w : InfinitePlace L).Completion)ˣ) →* (v.Completion)ˣ where
  toFun y := ∏ w : v.placesOver L, Units.map (Algebra.norm v.Completion :
    (w : InfinitePlace L).Completion →* v.Completion) (y w)
  map_one' := by simp
  map_mul' y z := by simp only [Pi.mul_apply, map_mul, Finset.prod_mul_distrib]

omit [NumberField K] in
open scoped Classical in
variable {L} in

theorem coe_infiniteLocalNorm (v : InfinitePlace K)
    (y : (w : v.placesOver L) → ((w : InfinitePlace L).Completion)ˣ) :
    ((infiniteLocalNorm L v y : (v.Completion)ˣ) : v.Completion) =
      ∏ w : v.placesOver L, Algebra.norm v.Completion (y w : (w : InfinitePlace L).Completion) := by
  simp [infiniteLocalNorm, Units.coe_prod]

variable {L}

theorem finiteProj_ideleNorm (y : IdeleGroup L) (v : HeightOneSpectrum (𝓞 K)) :
    IdeleGroup.finiteProj v (ideleNorm K L y) =
      finiteLocalNorm L v (fun w ↦ IdeleGroup.finiteProj w.1 y) := by
  ext
  rw [IdeleGroup.coe_finiteProj, coe_finiteLocalNorm, ideleNorm_snd]
  simp only [IdeleGroup.coe_finiteProj]

theorem infiniteProj_ideleNorm (y : IdeleGroup L) (v : InfinitePlace K) :
    IdeleGroup.infiniteProj v (ideleNorm K L y) =
      infiniteLocalNorm L v (fun w ↦ IdeleGroup.infiniteProj (w : InfinitePlace L) y) := by
  classical
  apply Units.ext
  rw [IdeleGroup.coe_infiniteProj, coe_infiniteLocalNorm, ideleNorm_fst]
  simp only [IdeleGroup.coe_infiniteProj]

theorem eventually_finiteProj_mem (y : IdeleGroup L) :
    ∀ᶠ w in cofinite,
      IdeleGroup.finiteProj w y ∈ (Submonoid.ofClass (w.adicCompletionIntegers L)).units := by
  refine (IdeleGroup.prodRestrictedEquiv L y).2.2.mono fun w hw ↦ ?_
  have e : IdeleGroup.finiteProj w y = (IdeleGroup.prodRestrictedEquiv L y).2 w :=
    Units.ext (by simp)
  rw [e]
  exact hw

omit [NumberField K] [NumberField L] in
variable (K) in

theorem eventually_forall_placesOver {P : HeightOneSpectrum (𝓞 L) → Prop}
    (h : ∀ᶠ w in cofinite, P w) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 K) in cofinite, ∀ w : PlacesOver L v, P w.1 := by
  rw [eventually_cofinite] at h ⊢
  refine (h.image (below K)).subset fun v hv ↦ ?_
  simp only [Set.mem_ofPred_eq, not_forall] at hv
  obtain ⟨w, hw⟩ := hv
  exact ⟨w.1, hw, (below_eq_iff w.1 v).2 w.2⟩

omit [NumberField K] in

theorem placesOver_congr (yf : ∀ v : HeightOneSpectrum (𝓞 K),
      (w : PlacesOver L v) → (w.1.adicCompletion L)ˣ)
    {v v' : HeightOneSpectrum (𝓞 K)} (h : v' = v) (w : HeightOneSpectrum (𝓞 L))
    (hw : w.asIdeal.LiesOver v.asIdeal) (hw' : w.asIdeal.LiesOver v'.asIdeal) :
    yf v' ⟨w, hw'⟩ = yf v ⟨w, hw⟩ := by
  subst h
  rfl

omit [NumberField K] [NumberField L] in

theorem infinitePlacesOver_congr (yi : ∀ v : InfinitePlace K,
      (w : v.placesOver L) → ((w : InfinitePlace L).Completion)ˣ)
    {v v' : InfinitePlace K} (h : v' = v) (w : InfinitePlace L)
    (hw : w ∈ v.placesOver L) (hw' : w ∈ v'.placesOver L) :
    yi v' ⟨w, hw'⟩ = yi v ⟨w, hw⟩ := by
  subst h
  rfl

def glue (yf : ∀ v : HeightOneSpectrum (𝓞 K), (w : PlacesOver L v) → (w.1.adicCompletion L)ˣ)
    (hyf : ∀ᶠ v in cofinite, yf v ∈ integerUnitsOver L v)
    (yi : ∀ v : InfinitePlace K, (w : v.placesOver L) → ((w : InfinitePlace L).Completion)ˣ) :
    IdeleGroup L :=
  (IdeleGroup.prodRestrictedEquiv L).symm
    (MulEquiv.piUnits.symm fun w : InfinitePlace L ↦
        yi (w.comap (algebraMap K L)) ⟨w, (inferInstance : w.LiesOver (w.comap (algebraMap K L)))⟩,
      ⟨fun w ↦ yf (below K w) ⟨w, inferInstance⟩,
        ((tendsto_below (K := K) (L := L)).eventually hyf).mono fun w hw ↦
          mem_integerUnitsOver.1 hw ⟨w, inferInstance⟩⟩)

theorem glue_snd (yf : ∀ v : HeightOneSpectrum (𝓞 K),
      (w : PlacesOver L v) → (w.1.adicCompletion L)ˣ)
    (hyf : ∀ᶠ v in cofinite, yf v ∈ integerUnitsOver L v)
    (yi : ∀ v : InfinitePlace K, (w : v.placesOver L) → ((w : InfinitePlace L).Completion)ˣ)
    (v : HeightOneSpectrum (𝓞 K)) (w : PlacesOver L v) :
    ((glue yf hyf yi : 𝔸[L]).2 w.1) = (yf v w : w.1.adicCompletion L) := by
  rw [← IdeleGroup.prodRestrictedEquiv_apply_snd, glue, ContinuousMulEquiv.apply_symm_apply]
  exact congrArg Units.val (placesOver_congr yf ((below_eq_iff w.1 v).2 w.2) w.1 w.2 _)

theorem glue_fst (yf : ∀ v : HeightOneSpectrum (𝓞 K),
      (w : PlacesOver L v) → (w.1.adicCompletion L)ˣ)
    (hyf : ∀ᶠ v in cofinite, yf v ∈ integerUnitsOver L v)
    (yi : ∀ v : InfinitePlace K, (w : v.placesOver L) → ((w : InfinitePlace L).Completion)ˣ)
    (v : InfinitePlace K) (w : v.placesOver L) :
    ((glue yf hyf yi : 𝔸[L]).1 w) = (yi v w : (w : InfinitePlace L).Completion) := by
  rw [← IdeleGroup.prodRestrictedEquiv_apply_fst, glue, ContinuousMulEquiv.apply_symm_apply]
  have := infinitePlacesOver_congr yi (InfinitePlace.LiesOver.comap_eq (w : InfinitePlace L) v)
    (w : InfinitePlace L) w.2
    (inferInstance : (w : InfinitePlace L).LiesOver ((w : InfinitePlace L).comap (algebraMap K L)))
  exact congrArg Units.val this

theorem ideleNorm_glue (yf : ∀ v : HeightOneSpectrum (𝓞 K),
      (w : PlacesOver L v) → (w.1.adicCompletion L)ˣ)
    (hyf : ∀ᶠ v in cofinite, yf v ∈ integerUnitsOver L v)
    (yi : ∀ v : InfinitePlace K, (w : v.placesOver L) → ((w : InfinitePlace L).Completion)ˣ)
    {x : IdeleGroup K} (hf : ∀ v, finiteLocalNorm L v (yf v) = IdeleGroup.finiteProj v x)
    (hi : ∀ v, infiniteLocalNorm L v (yi v) = IdeleGroup.infiniteProj v x) :
    ideleNorm K L (glue yf hyf yi) = x := by
  classical
  apply Units.ext
  refine Prod.ext (funext fun v ↦ ?_) (FiniteAdeleRing.ext (K := K) fun v ↦ ?_)
  · rw [ideleNorm_fst, ← IdeleGroup.coe_infiniteProj, ← hi v, coe_infiniteLocalNorm]
    exact Finset.prod_congr rfl fun w _ ↦ by rw [glue_fst]
  · rw [ideleNorm_snd, ← IdeleGroup.coe_finiteProj, ← hf v, coe_finiteLocalNorm]
    exact Finset.prod_congr rfl fun w _ ↦ by rw [glue_snd]

theorem mem_range_ideleNorm (x : IdeleGroup K)
    (hfin : ∀ v, IdeleGroup.finiteProj v x ∈ (finiteLocalNorm L v).range)
    (hinf : ∀ v, IdeleGroup.infiniteProj v x ∈ (infiniteLocalNorm L v).range)
    (hint : ∀ᶠ v in cofinite,
      IdeleGroup.finiteProj v x ∈ (integerUnitsOver L v).map (finiteLocalNorm L v)) :
    x ∈ (ideleNorm K L).range := by
  classical
  let yf : ∀ v : HeightOneSpectrum (𝓞 K), (w : PlacesOver L v) → (w.1.adicCompletion L)ˣ :=
    fun v ↦ if h : IdeleGroup.finiteProj v x ∈ (integerUnitsOver L v).map (finiteLocalNorm L v)
      then (Subgroup.mem_map.1 h).choose else (MonoidHom.mem_range.1 (hfin v)).choose
  have hyf_int : ∀ᶠ v in cofinite, yf v ∈ integerUnitsOver L v := hint.mono fun v h ↦ by
    simp only [yf, dif_pos h]
    exact (Subgroup.mem_map.1 h).choose_spec.1
  have hyf : ∀ v, finiteLocalNorm L v (yf v) = IdeleGroup.finiteProj v x := by
    intro v
    by_cases h : IdeleGroup.finiteProj v x ∈ (integerUnitsOver L v).map (finiteLocalNorm L v)
    · simp only [yf, dif_pos h]
      exact (Subgroup.mem_map.1 h).choose_spec.2
    · simp only [yf, dif_neg h]
      exact (MonoidHom.mem_range.1 (hfin v)).choose_spec
  exact ⟨glue yf hyf_int (fun v ↦ (MonoidHom.mem_range.1 (hinf v)).choose),
    ideleNorm_glue _ _ _ hyf fun v ↦ (MonoidHom.mem_range.1 (hinf v)).choose_spec⟩

theorem mem_range_ideleNorm_iff (x : IdeleGroup K) :
    x ∈ (ideleNorm K L).range ↔
      (∀ v, IdeleGroup.finiteProj v x ∈ (finiteLocalNorm L v).range) ∧
      (∀ v, IdeleGroup.infiniteProj v x ∈ (infiniteLocalNorm L v).range) ∧
      ∀ᶠ v in cofinite,
        IdeleGroup.finiteProj v x ∈ (integerUnitsOver L v).map (finiteLocalNorm L v) := by
  refine ⟨?_, fun ⟨h1, h2, h3⟩ ↦ mem_range_ideleNorm x h1 h2 h3⟩
  rintro ⟨y, rfl⟩
  refine ⟨fun v ↦ ⟨_, (finiteProj_ideleNorm y v).symm⟩,
    fun v ↦ ⟨_, (infiniteProj_ideleNorm y v).symm⟩, ?_⟩
  refine (eventually_forall_placesOver K (eventually_finiteProj_mem y)).mono fun v hv ↦ ?_
  exact ⟨_, mem_integerUnitsOver.2 hv, (finiteProj_ideleNorm y v).symm⟩

end IdeleNorm

end Sec_08_IdeleGroups_LocalNorms

/-! ### 09_IdeleGroups.LocalNormGroups -/
section Sec_09_IdeleGroups_LocalNormGroups

open IsDedekindDomain NumberField Filter Topology ValuativeRel
open AdeleBaseChange SemiLocal
open scoped NumberField.LiesOver TensorProduct


namespace IdeleNorm

variable {K : Type*} [Field K] [NumberField K] {L : Type*} [Field L] [NumberField L] [Algebra K L]

theorem finiteLocalNorm_mulSingle (v : HeightOneSpectrum (𝓞 K)) [DecidableEq (PlacesOver L v)]
    (w : PlacesOver L v) (z : (w.1.adicCompletion L)ˣ) :
    finiteLocalNorm L v (Pi.mulSingle w z) =
      RHDirect.CFT.LocalField.normUnits (v.adicCompletion K) (w.1.adicCompletion L) z := by
  ext
  rw [coe_finiteLocalNorm, Fintype.prod_eq_single w fun w' hw' ↦ by
    rw [Pi.mulSingle_eq_of_ne hw', Units.val_one, map_one], Pi.mulSingle_eq_same,
    RHDirect.CFT.LocalField.coe_normUnits]

omit [NumberField K] in
open scoped Classical in

theorem infiniteLocalNorm_mulSingle (v : InfinitePlace K) (w : v.placesOver L)
    (z : ((w : InfinitePlace L).Completion)ˣ) :
    infiniteLocalNorm L v (Pi.mulSingle w z) =
      RHDirect.CFT.LocalField.normUnits v.Completion (w : InfinitePlace L).Completion z := by
  ext
  rw [coe_infiniteLocalNorm, Fintype.prod_eq_single w fun w' hw' ↦ by
    rw [Pi.mulSingle_eq_of_ne hw', Units.val_one, map_one], Pi.mulSingle_eq_same,
    RHDirect.CFT.LocalField.coe_normUnits]

variable (L) in

theorem nonempty_infinitePlacesOver (v : InfinitePlace K) : Nonempty (v.placesOver L) := by
  obtain ⟨w, hw⟩ : ∃ w : InfinitePlace L, w.comap (algebraMap K L) = v :=
    InfinitePlace.comap_surjective v
  subst hw
  exact ⟨⟨w, (inferInstance : w.LiesOver (w.comap (algebraMap K L)))⟩⟩

theorem isOpen_range_finiteLocalNorm (v : HeightOneSpectrum (𝓞 K)) :
    IsOpen ((finiteLocalNorm L v).range : Set (v.adicCompletion K)ˣ) := by
  classical
  obtain ⟨w⟩ := nonempty_placesOver L v
  refine Subgroup.isOpen_mono ?_
    (RHDirect.CFT.LocalField.isOpen_range_normUnits (v.adicCompletion K) (w.1.adicCompletion L))
  rintro _ ⟨z, rfl⟩
  exact ⟨Pi.mulSingle w z, finiteLocalNorm_mulSingle v w z⟩

theorem pow_mem_nhds_one (v : InfinitePlace K) {d : ℕ} (hd : d ≠ 0) :
    {u : v.Completion | ∃ a : v.Completion, a ≠ 0 ∧ a ^ d = u} ∈ 𝓝 (1 : v.Completion) := by
  have : CharZero v.Completion :=
    charZero_of_injective_algebraMap (algebraMap K v.Completion).injective
  have h := (hasStrictDerivAt_pow d (1 : v.Completion)).map_nhds_eq (by simpa using hd)
  rw [one_pow] at h
  rw [← h, Filter.mem_map]
  filter_upwards [compl_singleton_mem_nhds (one_ne_zero' v.Completion)] with a ha
  exact ⟨a, ha, rfl⟩

theorem isOpen_range_infiniteLocalNorm (v : InfinitePlace K) :
    IsOpen ((infiniteLocalNorm L v).range : Set (v.Completion)ˣ) := by
  classical
  obtain ⟨w⟩ := nonempty_infinitePlacesOver L v
  have hd : Module.finrank v.Completion (w : InfinitePlace L).Completion ≠ 0 :=
    Module.finrank_pos.ne'
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
  have h := (Units.continuous_val (M := v.Completion)).tendsto 1
  rw [Units.val_one] at h
  refine Filter.mem_of_superset (h (pow_mem_nhds_one v hd)) fun u hu ↦ ?_
  obtain ⟨a, ha, hau⟩ := hu
  refine ⟨Pi.mulSingle w (Units.map (algebraMap v.Completion (w : InfinitePlace L).Completion :
    v.Completion →* (w : InfinitePlace L).Completion) (Units.mk0 a ha)), ?_⟩
  rw [infiniteLocalNorm_mulSingle]
  apply Units.ext
  rw [RHDirect.CFT.LocalField.coe_normUnits, Units.coe_map, Units.val_mk0]
  exact (Algebra.norm_algebraMap a).trans hau

theorem finiteLocalNorm_mem_integers {v : HeightOneSpectrum (𝓞 K)}
    {y : (w : PlacesOver L v) → (w.1.adicCompletion L)ˣ} (hy : y ∈ integerUnitsOver L v) :
    (finiteLocalNorm L v y : v.adicCompletion K) ∈ v.adicCompletionIntegers K := by
  rw [coe_finiteLocalNorm]
  refine prod_mem fun w _ ↦ ?_
  have h := (Submonoid.mem_units_iff _ _).1 (mem_integerUnitsOver.1 hy w)
  rw [← mem_valuationInteger_iff]
  exact RHDirect.CFT.LocalField.norm_mem_integer ((mem_valuationInteger_iff w.1 _).2 h.1)

theorem map_integerUnitsOver_le (v : HeightOneSpectrum (𝓞 K)) :
    (integerUnitsOver L v).map (finiteLocalNorm L v) ≤
      (Submonoid.ofClass (v.adicCompletionIntegers K)).units := by
  rintro _ ⟨y, hy, rfl⟩
  refine (Submonoid.mem_units_iff _ _).2 ⟨finiteLocalNorm_mem_integers hy, ?_⟩
  rw [← map_inv]
  exact finiteLocalNorm_mem_integers (inv_mem hy)

theorem finiteLocalNorm_mulSingle_algebraMap (v : HeightOneSpectrum (𝓞 K))
    [DecidableEq (PlacesOver L v)] (w : PlacesOver L v) (a : (v.adicCompletion K)ˣ) :
    finiteLocalNorm L v (Pi.mulSingle w (Units.map (algebraMap (v.adicCompletion K)
      (w.1.adicCompletion L) : v.adicCompletion K →* w.1.adicCompletion L) a)) =
        a ^ Module.finrank (v.adicCompletion K) (w.1.adicCompletion L) := by
  rw [finiteLocalNorm_mulSingle]
  apply Units.ext
  rw [RHDirect.CFT.LocalField.coe_normUnits, Units.coe_map, Units.val_pow_eq_pow_val]
  exact Algebra.norm_algebraMap (S := w.1.adicCompletion L) (a : v.adicCompletion K)

theorem range_finiteLocalNorm_eq_top_of_isFiniteSplit (v : HeightOneSpectrum (𝓞 K))
    (h : Algebra.IsFiniteSplit (v.adicCompletion K) (v.adicCompletion K ⊗[K] L)) :
    (finiteLocalNorm L v).range = ⊤ := by
  classical
  have hw := (splitsCompletely_iff_forall_finrank v).1 ((splitsCompletely_iff_isFiniteSplit v).2 h)
  obtain ⟨w⟩ := nonempty_placesOver L v
  refine eq_top_iff.2 fun a _ ↦ ⟨_, finiteLocalNorm_mulSingle_algebraMap v w a |>.trans ?_⟩
  rw [hw w, pow_one]

theorem exists_norm_eq_of_ramificationIdx_eq_one (v : HeightOneSpectrum (𝓞 K))
    (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]
    (he : w.asIdeal.ramificationIdx (𝓞 K) = 1) {u : (v.adicCompletion K)ˣ}
    (hu : u ∈ (Submonoid.ofClass (v.adicCompletionIntegers K)).units) :
    ∃ y ∈ (Submonoid.ofClass (w.adicCompletionIntegers L)).units,
      Algebra.norm (v.adicCompletion K) (y : w.adicCompletion L) = u := by
  have : RHDirect.CFT.LocalField.IsUnramified (v.adicCompletion K) (w.adicCompletion L) :=
    ⟨(ramificationIdx_integer v w).trans he⟩
  rw [Submonoid.mem_units_iff] at hu
  let u' : 𝒪[v.adicCompletion K]ˣ :=
    ⟨⟨u, (mem_valuationInteger_iff v _).2 hu.1⟩, ⟨_, (mem_valuationInteger_iff v _).2 hu.2⟩,
      Subtype.ext u.mul_inv, Subtype.ext u.inv_mul⟩
  obtain ⟨g, hg⟩ := RHDirect.CFT.LocalField.normIntegerUnits_surjective
    (K := v.adicCompletion K) (L := w.adicCompletion L) u'
  refine ⟨RHDirect.CFT.LocalField.unitsIncl _ g, (Submonoid.mem_units_iff _ _).2
    ⟨(mem_valuationInteger_iff w _).1 (g : 𝒪[w.adicCompletion L]).2, ?_⟩, ?_⟩
  · rw [← map_inv, RHDirect.CFT.LocalField.coe_unitsIncl]
    exact (mem_valuationInteger_iff w _).1 ((g⁻¹ : 𝒪[w.adicCompletion L]ˣ) :
      𝒪[w.adicCompletion L]).2
  · rw [RHDirect.CFT.LocalField.coe_unitsIncl, ← RHDirect.CFT.LocalField.coe_normIntegerUnits, hg]

end IdeleNorm

end Sec_09_IdeleGroups_LocalNormGroups

/-! ### 10_IdeleGroups.LocalNormsEverywhere -/
section Sec_10_IdeleGroups_LocalNormsEverywhere

open IsDedekindDomain NumberField Filter
open AdeleBaseChange SemiLocal


namespace IdeleNorm

variable {K : Type*} [Field K] [NumberField K] {L : Type*} [Field L] [NumberField L] [Algebra K L]

attribute [local instance] FractionRing.liftAlgebra in
variable (K L) in

theorem eventually_ramificationIdx_eq_one :
    ∀ᶠ w : HeightOneSpectrum (𝓞 L) in cofinite, w.asIdeal.ramificationIdx (𝓞 K) = 1 := by
  rw [eventually_cofinite]
  refine (Ideal.finite_factors (differentIdeal_ne_bot (A := 𝓞 K) (B := 𝓞 L))).subset
    fun w hw ↦ ?_
  by_contra h
  have := w.isPrime
  have := not_dvd_differentIdeal_iff.1 h
  exact hw (Ideal.ramificationIdx_eq_one w.asIdeal (𝓞 K))

theorem map_integerUnitsOver_eq_of_ramificationIdx_eq_one (v : HeightOneSpectrum (𝓞 K))
    (w : PlacesOver L v) (he : w.1.asIdeal.ramificationIdx (𝓞 K) = 1) :
    (integerUnitsOver L v).map (finiteLocalNorm L v) =
      (Submonoid.ofClass (v.adicCompletionIntegers K)).units := by
  classical
  refine le_antisymm (map_integerUnitsOver_le v) fun u hu ↦ ?_
  obtain ⟨y, hy, hyu⟩ := exists_norm_eq_of_ramificationIdx_eq_one v w.1 he hu
  refine ⟨Pi.mulSingle w y, mem_integerUnitsOver.2 fun w' ↦ ?_, ?_⟩
  · by_cases h : w' = w
    · subst h
      rw [Pi.mulSingle_eq_same]
      exact hy
    · rw [Pi.mulSingle_eq_of_ne h]
      exact one_mem _
  · rw [finiteLocalNorm_mulSingle]
    exact Units.ext hyu

variable (L) in

theorem eventually_map_integerUnitsOver_eq :
    ∀ᶠ v : HeightOneSpectrum (𝓞 K) in cofinite,
      (integerUnitsOver L v).map (finiteLocalNorm L v) =
        (Submonoid.ofClass (v.adicCompletionIntegers K)).units := by
  refine (eventually_forall_placesOver K (eventually_ramificationIdx_eq_one K L)).mono
    fun v hv ↦ ?_
  obtain ⟨w⟩ := nonempty_placesOver L v
  exact map_integerUnitsOver_eq_of_ramificationIdx_eq_one v w (hv w)

variable (L) in

theorem mem_range_ideleNorm_iff_forall (x : IdeleGroup K) :
    x ∈ (ideleNorm K L).range ↔
      (∀ v, IdeleGroup.finiteProj v x ∈ (finiteLocalNorm L v).range) ∧
      ∀ v, IdeleGroup.infiniteProj v x ∈ (infiniteLocalNorm L v).range := by
  rw [mem_range_ideleNorm_iff]
  refine ⟨fun h ↦ ⟨h.1, h.2.1⟩, fun h ↦ ⟨h.1, h.2, ?_⟩⟩
  filter_upwards [eventually_finiteProj_mem (L := K) x, eventually_map_integerUnitsOver_eq L]
    with v hv hv'
  rw [hv']
  exact hv

theorem mem_range_ideleNorm_of_forall (x : IdeleGroup K)
    (hfin : ∀ v, IdeleGroup.finiteProj v x ∈ (finiteLocalNorm L v).range)
    (hinf : ∀ v, IdeleGroup.infiniteProj v x ∈ (infiniteLocalNorm L v).range) :
    x ∈ (ideleNorm K L).range :=
  (mem_range_ideleNorm_iff_forall L x).2 ⟨hfin, hinf⟩

end IdeleNorm

end Sec_10_IdeleGroups_LocalNormsEverywhere

/-! ### 11_IdeleGroups.SIdeleGroups.Galois -/
section Sec_11_IdeleGroups_SIdeleGroups_Galois

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero AdeleBaseChange
open scoped NumberField.AdeleRing


variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

namespace AdeleBaseChange
open RHDirect.CFT_ProfiniteSemilocal.AdeleBaseChange

theorem continuous_finiteCompletionMap {M M' : Type*} [Field M] [NumberField M] [Field M']
    [NumberField M'] (τ : M ≃+* M') (w' : HeightOneSpectrum (𝓞 M')) :
    Continuous (finiteCompletionMap τ w') :=
  letI : Algebra M M' := (τ : M →+* M').toAlgebra
  SemiLocal.continuous_completionMap (below M w') w'

omit [NumberField K] in

theorem valued_finiteCompletionMap (σ : L ≃ₐ[K] L) (w : HeightOneSpectrum (𝓞 L))
    (y : (comapPrime (σ : L ≃+* L) w).adicCompletion L) :
    Valued.v (finiteCompletionMap (σ : L ≃+* L) w y) = Valued.v y := by
  have hL : ∀ l : L, Valued.v (finiteCompletionMap (σ : L ≃+* L) w
      (algebraMap L ((comapPrime (σ : L ≃+* L) w).adicCompletion L) l)) =
        Valued.v (algebraMap L ((comapPrime (σ : L ≃+* L) w).adicCompletion L) l) := by
    intro l
    rw [finiteCompletionMap_algebraMap]
    simp only [HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
      Algebra.algebraMap_self, RingHom.id_apply, valuedAdicCompletion_eq_valuation']
    rw [comapPrime_eq_inv_smul]
    conv_lhs => rw [← smul_inv_smul σ w]
    exact SemiLocal.valuation_smul σ (σ⁻¹ • w) l
  have hclosed : IsClosed {y : (comapPrime (σ : L ≃+* L) w).adicCompletion L |
      Valued.v (finiteCompletionMap (σ : L ≃+* L) w y) = Valued.v y} := by
    rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro y0 hy0
    have h0 : y0 ≠ 0 := by
      rintro rfl
      simp at hy0
    have h1 : Valued.v y0 ≠ 0 := (Valuation.ne_zero_iff _).2 h0
    have h2 : Valued.v (finiteCompletionMap (σ : L ≃+* L) w y0) ≠ 0 :=
      (Valuation.ne_zero_iff _).2
        ((map_ne_zero_iff _ (finiteCompletionMap (σ : L ≃+* L) w).injective).2 h0)
    filter_upwards [Valued.locally_const h1,
      (continuous_finiteCompletionMap _ w).continuousAt.preimage_mem_nhds
        (Valued.locally_const h2)] with y hy hy'
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_compl_iff] at hy hy' hy0 ⊢
    rwa [hy, hy']
  exact (HeightOneSpectrum.denseRange_algebraMap L (comapPrime (σ : L ≃+* L) w)).induction_on
    (p := fun y ↦ Valued.v (finiteCompletionMap (σ : L ≃+* L) w y) = Valued.v y) y hclosed hL

omit [NumberField K] [NumberField L] in

theorem below_smul (σ : L ≃ₐ[K] L) (w : HeightOneSpectrum (𝓞 L)) :
    below K (σ • w) = below K w :=
  HeightOneSpectrum.ext (Ideal.under_smul (𝓞 K) w.asIdeal σ)

end AdeleBaseChange

namespace IdeleGroup
open RHDirect.Stage13CFT_IdeleNormResidue.IdeleGroup

omit [NumberField K] in

theorem ord_smul (σ : L ≃ₐ[K] L) (x : IdeleGroup L) (w : HeightOneSpectrum (𝓞 L)) :
    ord w (σ • x) = ord (σ⁻¹ • w) x := by
  simp only [ord]
  rw [coe_smul_idele, smul_snd, AdeleBaseChange.valued_finiteCompletionMap, comapPrime_eq_inv_smul]

variable (L) in

def placesAbove (S : Set (HeightOneSpectrum (𝓞 K))) : Set (HeightOneSpectrum (𝓞 L)) :=
  below K ⁻¹' S

omit [NumberField K] [NumberField L] in
theorem mem_placesAbove {S : Set (HeightOneSpectrum (𝓞 K))} {w : HeightOneSpectrum (𝓞 L)} :
    w ∈ placesAbove L S ↔ below K w ∈ S :=
  Iff.rfl

omit [NumberField K] [NumberField L] in
theorem placesAbove_mono {S T : Set (HeightOneSpectrum (𝓞 K))} (h : S ⊆ T) :
    placesAbove L S ⊆ placesAbove L T :=
  fun _ hw ↦ h hw

theorem placesAbove_finite {S : Set (HeightOneSpectrum (𝓞 K))} (hS : S.Finite) :
    (placesAbove L S).Finite :=
  hS.preimage' fun v _ ↦
    (Set.finite_range (Subtype.val : SemiLocal.PlacesOver L v → HeightOneSpectrum (𝓞 L))).subset
      fun w hw ↦ ⟨⟨w, (below_eq_iff w v).1 hw⟩, rfl⟩

omit [NumberField K] [NumberField L] in

theorem smul_mem_placesAbove_iff (S : Set (HeightOneSpectrum (𝓞 K))) (σ : L ≃ₐ[K] L)
    (w : HeightOneSpectrum (𝓞 L)) : σ • w ∈ placesAbove L S ↔ w ∈ placesAbove L S := by
  rw [mem_placesAbove, mem_placesAbove, AdeleBaseChange.below_smul]

variable (S : Set (HeightOneSpectrum (𝓞 K)))

omit [NumberField K] in

theorem smul_mem_sIdeles_placesAbove (σ : L ≃ₐ[K] L) {x : IdeleGroup L}
    (hx : x ∈ sIdeles (placesAbove L S)) : σ • x ∈ sIdeles (placesAbove L S) := fun w hw ↦ by
  rw [ord_smul]
  exact hx _ fun h ↦ hw ((smul_mem_placesAbove_iff S σ⁻¹ w).1 h)

instance : MulDistribMulAction (L ≃ₐ[K] L) (sIdeles (placesAbove L S)) where
  smul σ x := ⟨σ • (x : IdeleGroup L), smul_mem_sIdeles_placesAbove S σ x.2⟩
  one_smul x := Subtype.ext (one_smul _ (x : IdeleGroup L))
  mul_smul σ τ x := Subtype.ext (mul_smul σ τ (x : IdeleGroup L))
  smul_mul σ x y := Subtype.ext (smul_mul' σ (x : IdeleGroup L) y)
  smul_one σ := Subtype.ext (smul_one σ)

omit [NumberField K] in
@[simp]
theorem coe_smul_sIdeles (σ : L ≃ₐ[K] L) (x : sIdeles (placesAbove L S)) :
    ((σ • x : sIdeles (placesAbove L S)) : IdeleGroup L) = σ • (x : IdeleGroup L) :=
  rfl

omit [NumberField K] in

theorem sIdelesToIdeleClassGroup_smul (σ : L ≃ₐ[K] L) (x : sIdeles (placesAbove L S)) :
    sIdelesToIdeleClassGroup (placesAbove L S) (σ • x) =
      σ • sIdelesToIdeleClassGroup (placesAbove L S) x := by
  rw [sIdelesToIdeleClassGroup_apply, sIdelesToIdeleClassGroup_apply, smul_mk, coe_smul_sIdeles]

omit [NumberField K] in

theorem exists_finset_superset_sup_sIdeles_placesAbove_eq_top
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 K)), S₀ ⊆ S ∧
      (diagonal L).range ⊔ sIdeles (placesAbove L (S : Set (HeightOneSpectrum (𝓞 K)))) = ⊤ := by
  classical
  obtain ⟨T, hT⟩ := exists_finset_sup_sIdeles_eq_top (K := L)
  refine ⟨S₀ ∪ T.image (below K), Finset.subset_union_left,
    sup_sIdeles_eq_top_of_subset (fun w hw ↦ ?_) hT⟩
  exact Finset.mem_coe.2
    (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_coe.1 hw)))

omit [NumberField K] in

theorem sUnits_sIdeles_placesAbove_exact
    (h : (diagonal L).range ⊔ sIdeles (placesAbove L S) = ⊤) :
    Function.Injective (sUnitsToSIdeles (placesAbove L S)) ∧
      (sUnitsToSIdeles (placesAbove L S)).range =
        (sIdelesToIdeleClassGroup (placesAbove L S)).ker ∧
      Function.Surjective (sIdelesToIdeleClassGroup (placesAbove L S)) :=
  sUnits_sIdeles_exact _ h

end IdeleGroup

end Sec_11_IdeleGroups_SIdeleGroups_Galois

/-! ### 12_IdeleGroups.SIdeleGroups.Places -/
section Sec_12_IdeleGroups_SIdeleGroups_Places

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum AdeleBaseChange SemiLocal
open scoped NumberField.AdeleRing RestrictedProduct


variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

namespace AdeleBaseChange
open RHDirect.CFT_ProfiniteSemilocal.AdeleBaseChange

omit [NumberField K] in

theorem finiteCompletionMap_eq_galHom (σ : L ≃ₐ[K] L) (w' : HeightOneSpectrum (𝓞 L))
    (h : w' = σ • comapPrime (σ : L ≃+* L) w') :
    finiteCompletionMap (σ : L ≃+* L) w' = galHom σ (comapPrime (σ : L ≃+* L) w') w' h := by
  have := (HeightOneSpectrum.denseRange_algebraMap L (comapPrime (σ : L ≃+* L) w')).equalizer
    (continuous_finiteCompletionMap _ w') (continuous_galHom σ _ w' h)
    (funext fun l ↦ by
      simp only [Function.comp_apply, finiteCompletionMap_algebraMap, galHom_algebraMap]
      rfl)
  exact RingHom.ext (congrFun this)

omit [NumberField K] in

theorem smul_snd_eq_galHom (σ : L ≃ₐ[K] L) (a : 𝔸[L]) (w w' : HeightOneSpectrum (𝓞 L))
    (h : w' = σ • w) : (σ • a).2 w' = galHom σ w w' h (a.2 w) := by
  obtain rfl : w = comapPrime (σ : L ≃+* L) w' := by
    rw [comapPrime_eq_inv_smul, h, inv_smul_smul]
  rw [smul_snd, finiteCompletionMap_eq_galHom σ w' h]

end AdeleBaseChange

namespace IdeleGroup
open RHDirect.Stage13CFT_IdeleNormResidue.IdeleGroup

section Finite

variable (v : HeightOneSpectrum (𝓞 K))

theorem finite_setOf_liesOver :
    {w : HeightOneSpectrum (𝓞 L) | w.asIdeal.LiesOver v.asIdeal}.Finite :=
  (Set.finite_range (Subtype.val : PlacesOver L v → HeightOneSpectrum (𝓞 L))).subset
    fun w hw ↦ ⟨⟨w, hw⟩, rfl⟩

open Classical in

def finiteAdeleAboveFun (a : (w : PlacesOver L v) → w.1.adicCompletion L)
    (w : HeightOneSpectrum (𝓞 L)) : w.adicCompletion L :=
  if h : w.asIdeal.LiesOver v.asIdeal then a ⟨w, h⟩ else 1

omit [NumberField K] in
theorem finiteAdeleAboveFun_apply (a : (w : PlacesOver L v) → w.1.adicCompletion L)
    (w : PlacesOver L v) : finiteAdeleAboveFun v a w.1 = a w := by
  rw [finiteAdeleAboveFun, dif_pos w.2]

omit [NumberField K] in
theorem finiteAdeleAboveFun_apply_of_not (a : (w : PlacesOver L v) → w.1.adicCompletion L)
    {w : HeightOneSpectrum (𝓞 L)} (h : ¬ w.asIdeal.LiesOver v.asIdeal) :
    finiteAdeleAboveFun v a w = 1 := by
  rw [finiteAdeleAboveFun, dif_neg h]

theorem finiteAdeleAboveFun_eventually (a : (w : PlacesOver L v) → w.1.adicCompletion L) :
    ∀ᶠ w in Filter.cofinite, finiteAdeleAboveFun v a w ∈ w.adicCompletionIntegers L := by
  refine Filter.eventually_cofinite.2 ((finite_setOf_liesOver (L := L) v).subset fun w hw ↦ ?_)
  by_contra h
  apply hw
  rw [finiteAdeleAboveFun_apply_of_not v a h]
  exact (w.adicCompletionIntegers L).one_mem

omit [NumberField K] in
theorem finiteAdeleAboveFun_one :
    finiteAdeleAboveFun v (1 : (w : PlacesOver L v) → w.1.adicCompletion L) = 1 := by
  funext w
  by_cases h : w.asIdeal.LiesOver v.asIdeal
  · exact finiteAdeleAboveFun_apply v 1 ⟨w, h⟩
  · exact finiteAdeleAboveFun_apply_of_not v 1 h

omit [NumberField K] in
theorem finiteAdeleAboveFun_mul (a b : (w : PlacesOver L v) → w.1.adicCompletion L) :
    finiteAdeleAboveFun v (a * b) = finiteAdeleAboveFun v a * finiteAdeleAboveFun v b := by
  funext w
  rw [Pi.mul_apply]
  by_cases h : w.asIdeal.LiesOver v.asIdeal
  · rw [finiteAdeleAboveFun_apply v _ ⟨w, h⟩, finiteAdeleAboveFun_apply v _ ⟨w, h⟩,
      finiteAdeleAboveFun_apply v _ ⟨w, h⟩, Pi.mul_apply]
  · rw [finiteAdeleAboveFun_apply_of_not v _ h, finiteAdeleAboveFun_apply_of_not v _ h,
      finiteAdeleAboveFun_apply_of_not v _ h, mul_one]

def finiteAdeleAbove : ((w : PlacesOver L v) → w.1.adicCompletion L) →* FiniteAdeleRing (𝓞 L) L where
  toFun a := (⟨finiteAdeleAboveFun v a, finiteAdeleAboveFun_eventually v a⟩ :
    Πʳ w : HeightOneSpectrum (𝓞 L), [w.adicCompletion L, w.adicCompletionIntegers L])
  map_one' := Subtype.ext (finiteAdeleAboveFun_one v)
  map_mul' a b := Subtype.ext (finiteAdeleAboveFun_mul v a b)

theorem finiteAdeleAbove_apply (a : (w : PlacesOver L v) → w.1.adicCompletion L)
    (w : PlacesOver L v) : finiteAdeleAbove v a w.1 = a w :=
  finiteAdeleAboveFun_apply v a w

theorem finiteAdeleAbove_apply_of_not (a : (w : PlacesOver L v) → w.1.adicCompletion L)
    {w : HeightOneSpectrum (𝓞 L)} (h : ¬ w.asIdeal.LiesOver v.asIdeal) :
    finiteAdeleAbove v a w = 1 :=
  finiteAdeleAboveFun_apply_of_not v a h

theorem adele_ext {a b : 𝔸[L]} (h₁ : a.1 = b.1) (h₂ : ∀ w : HeightOneSpectrum (𝓞 L), a.2 w = b.2 w) :
    a = b :=
  Prod.ext h₁ (Subtype.ext (funext h₂))

def finiteEmbedAbove : ((w : PlacesOver L v) → (w.1.adicCompletion L)ˣ) →* IdeleGroup L :=
  (Units.map (MonoidHom.prod 1 (finiteAdeleAbove v) :
      ((w : PlacesOver L v) → w.1.adicCompletion L) →*
        InfiniteAdeleRing L × FiniteAdeleRing (𝓞 L) L)).comp
    (MulEquiv.piUnits (M := fun w : PlacesOver L v ↦ w.1.adicCompletion L)).symm.toMonoidHom

theorem coe_finiteEmbedAbove_fst (y : (w : PlacesOver L v) → (w.1.adicCompletion L)ˣ) :
    ((finiteEmbedAbove v y : IdeleGroup L) : 𝔸[L]).1 = 1 :=
  rfl

theorem coe_finiteEmbedAbove_snd (y : (w : PlacesOver L v) → (w.1.adicCompletion L)ˣ)
    (w : PlacesOver L v) :
    ((finiteEmbedAbove v y : IdeleGroup L) : 𝔸[L]).2 w.1 = y w :=
  finiteAdeleAbove_apply v _ w

theorem coe_finiteEmbedAbove_snd_of_not (y : (w : PlacesOver L v) → (w.1.adicCompletion L)ˣ)
    {w : HeightOneSpectrum (𝓞 L)} (h : ¬ w.asIdeal.LiesOver v.asIdeal) :
    ((finiteEmbedAbove v y : IdeleGroup L) : 𝔸[L]).2 w = 1 :=
  finiteAdeleAbove_apply_of_not v _ h

def finiteProjAbove : IdeleGroup L →* ((w : PlacesOver L v) → (w.1.adicCompletion L)ˣ) :=
  MonoidHom.pi fun w ↦ finiteProj w.1

omit [NumberField K] in
@[simp]
theorem coe_finiteProjAbove_apply (x : IdeleGroup L) (w : PlacesOver L v) :
    ((finiteProjAbove v x w : (w.1.adicCompletion L)ˣ) : w.1.adicCompletion L) =
      (x : 𝔸[L]).2 w.1 :=
  rfl

theorem finiteProjAbove_finiteEmbedAbove (y : (w : PlacesOver L v) → (w.1.adicCompletion L)ˣ) :
    finiteProjAbove v (finiteEmbedAbove v y) = y :=
  funext fun w ↦ Units.ext (coe_finiteEmbedAbove_snd v y w)

omit [NumberField K] [NumberField L] in
theorem comapPrime_liesOver (σ : L ≃ₐ[K] L) (w : PlacesOver L v) :
    (comapPrime (σ : L ≃+* L) w.1).asIdeal.LiesOver v.asIdeal := by
  rw [comapPrime_eq_inv_smul]
  exact (σ⁻¹ • w).2

omit [NumberField K] in

theorem finiteProjAbove_smul_congr (σ : L ≃ₐ[K] L) {x y : IdeleGroup L}
    (h : finiteProjAbove v x = finiteProjAbove v y) :
    finiteProjAbove v (σ • x) = finiteProjAbove v (σ • y) := by
  funext u
  refine Units.ext ?_
  rw [coe_finiteProjAbove_apply, coe_finiteProjAbove_apply, coe_smul_idele, coe_smul_idele,
    smul_snd, smul_snd]
  congr 1
  have := congrArg (fun f : (w : PlacesOver L v) → (w.1.adicCompletion L)ˣ ↦
    ((f ⟨comapPrime (σ : L ≃+* L) u.1, comapPrime_liesOver v σ u⟩ : _) :
      (comapPrime (σ : L ≃+* L) u.1).adicCompletion L)) h
  exact this

instance finiteUnitsAboveAction :
    MulDistribMulAction (L ≃ₐ[K] L) ((w : PlacesOver L v) → (w.1.adicCompletion L)ˣ) where
  smul σ y := finiteProjAbove v (σ • finiteEmbedAbove v y)
  one_smul y := by
    change finiteProjAbove v ((1 : L ≃ₐ[K] L) • finiteEmbedAbove v y) = y
    rw [one_smul, finiteProjAbove_finiteEmbedAbove]
  mul_smul σ τ y := by
    change finiteProjAbove v ((σ * τ) • finiteEmbedAbove v y) =
      finiteProjAbove v (σ • finiteEmbedAbove v (finiteProjAbove v (τ • finiteEmbedAbove v y)))
    rw [mul_smul]
    exact finiteProjAbove_smul_congr v σ (finiteProjAbove_finiteEmbedAbove v _).symm
  smul_mul σ y z := by
    change finiteProjAbove v (σ • finiteEmbedAbove v (y * z)) =
      finiteProjAbove v (σ • finiteEmbedAbove v y) * finiteProjAbove v (σ • finiteEmbedAbove v z)
    rw [map_mul, smul_mul', map_mul]
  smul_one σ := by
    change finiteProjAbove v (σ • finiteEmbedAbove v 1) = 1
    rw [map_one, smul_one, map_one]

theorem finiteUnitsAbove_smul_def (σ : L ≃ₐ[K] L)
    (y : (w : PlacesOver L v) → (w.1.adicCompletion L)ˣ) :
    σ • y = finiteProjAbove v (σ • finiteEmbedAbove v y) :=
  rfl

theorem finiteProjAbove_smul (σ : L ≃ₐ[K] L) (x : IdeleGroup L) :
    finiteProjAbove v (σ • x) = σ • finiteProjAbove v x :=
  finiteProjAbove_smul_congr v σ (finiteProjAbove_finiteEmbedAbove v _).symm

omit [NumberField K] [NumberField L] in
theorem liesOver_of_smul_liesOver (σ : L ≃ₐ[K] L) {w : HeightOneSpectrum (𝓞 L)}
    (h : (σ • w).asIdeal.LiesOver v.asIdeal) : w.asIdeal.LiesOver v.asIdeal := by
  have := (σ⁻¹ • (⟨σ • w, h⟩ : PlacesOver L v)).2
  rwa [coe_smul_placesOver, inv_smul_smul] at this

theorem finiteEmbedAbove_smul (σ : L ≃ₐ[K] L)
    (y : (w : PlacesOver L v) → (w.1.adicCompletion L)ˣ) :
    finiteEmbedAbove v (σ • y) = σ • finiteEmbedAbove v y := by
  refine Units.ext (adele_ext ?_ fun u ↦ ?_)
  · funext u
    rw [coe_finiteEmbedAbove_fst, coe_smul_idele, smul_fst, coe_finiteEmbedAbove_fst]
    exact (map_one (infiniteCompletionMap _ u)).symm
  · by_cases h : u.asIdeal.LiesOver v.asIdeal
    · rw [coe_finiteEmbedAbove_snd v _ ⟨u, h⟩, finiteUnitsAbove_smul_def,
        coe_finiteProjAbove_apply]
    · rw [coe_finiteEmbedAbove_snd_of_not v _ h, coe_smul_idele, smul_snd,
        coe_finiteEmbedAbove_snd_of_not v _ ?_, map_one]
      rw [comapPrime_eq_inv_smul]
      intro h'
      exact h (liesOver_of_smul_liesOver v σ⁻¹ h')

theorem finiteProjAbove_finiteEmbedAbove_of_ne {v v' : HeightOneSpectrum (𝓞 K)} (h : v' ≠ v)
    (y : (w : PlacesOver L v) → (w.1.adicCompletion L)ˣ) :
    finiteProjAbove v' (finiteEmbedAbove v y) = 1 := by
  funext u
  refine Units.ext ?_
  rw [coe_finiteProjAbove_apply, coe_finiteEmbedAbove_snd_of_not v y]
  · rfl
  · intro hu
    exact h ((below_eq_iff u.1 v').2 u.2 ▸ (below_eq_iff u.1 v).2 hu)

theorem finiteUnitsAbove_smul_apply (σ : L ≃ₐ[K] L)
    (y : (w : PlacesOver L v) → (w.1.adicCompletion L)ˣ) (w : PlacesOver L v) :
    (((σ • y) (σ • w) : ((σ • w).1.adicCompletion L)ˣ) : (σ • w).1.adicCompletion L) =
      galEquiv v σ w.1 (σ • w).1 rfl (y w) := by
  rw [finiteUnitsAbove_smul_def, coe_finiteProjAbove_apply, coe_smul_idele,
    smul_snd_eq_galHom σ _ w.1 (σ • w).1 rfl, coe_finiteEmbedAbove_snd, galEquiv_apply]

end Finite

end IdeleGroup

end Sec_12_IdeleGroups_SIdeleGroups_Places

/-! ### 13_IdeleGroups.SIdeleGroups.IntegerUnits -/
section Sec_13_IdeleGroups_SIdeleGroups_IntegerUnits

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum AdeleBaseChange SemiLocal
open scoped NumberField.AdeleRing


variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

namespace IdeleGroup
open RHDirect.Stage13CFT_IdeleNormResidue.IdeleGroup

omit [NumberField K] in

theorem smul_mem_standardOpenSubgroup (σ : L ≃ₐ[K] L) {x : IdeleGroup L}
    (hx : x ∈ standardOpenSubgroup L) : σ • x ∈ standardOpenSubgroup L := by
  rw [mem_standardOpenSubgroup_iff_ord] at hx ⊢
  intro w
  rw [ord_smul]
  exact hx _

variable (v : HeightOneSpectrum (𝓞 K))

def integerUnitsAboveIncl :
    ((w : PlacesOver L v) → (w.1.adicCompletionIntegers L)ˣ) →*
      ((w : PlacesOver L v) → (w.1.adicCompletion L)ˣ) :=
  MonoidHom.pi fun w ↦
    (Units.map (w.1.adicCompletionIntegers L).subtype.toMonoidHom).comp (Pi.evalMonoidHom _ w)

omit [NumberField K] in
@[simp]
theorem coe_integerUnitsAboveIncl_apply
    (z : (w : PlacesOver L v) → (w.1.adicCompletionIntegers L)ˣ) (w : PlacesOver L v) :
    ((integerUnitsAboveIncl v z w : (w.1.adicCompletion L)ˣ) : w.1.adicCompletion L) =
      ((z w : w.1.adicCompletionIntegers L) : w.1.adicCompletion L) :=
  rfl

omit [NumberField K] in
theorem integerUnitsAboveIncl_injective :
    Function.Injective (integerUnitsAboveIncl (L := L) v) := fun _ _ h ↦
  funext fun w ↦ Units.ext (Subtype.ext (congrArg (fun y ↦ ((y w : (w.1.adicCompletion L)ˣ) :
    w.1.adicCompletion L)) h))

omit [NumberField K] in

theorem mem_range_integerUnitsAboveIncl_iff (y : (w : PlacesOver L v) → (w.1.adicCompletion L)ˣ) :
    y ∈ (integerUnitsAboveIncl v).range ↔ ∀ w : PlacesOver L v,
      (y w : w.1.adicCompletion L) ∈ w.1.adicCompletionIntegers L ∧
        ((y w)⁻¹ : (w.1.adicCompletion L)ˣ).val ∈ w.1.adicCompletionIntegers L := by
  constructor
  · rintro ⟨z, rfl⟩ w
    exact ⟨(z w : w.1.adicCompletionIntegers L).2,
      (((z w)⁻¹ : (w.1.adicCompletionIntegers L)ˣ) : w.1.adicCompletionIntegers L).2⟩
  · intro h
    refine ⟨fun w ↦ ⟨⟨y w, (h w).1⟩, ⟨((y w)⁻¹ : (w.1.adicCompletion L)ˣ), (h w).2⟩,
      Subtype.ext (y w).mul_inv, Subtype.ext (y w).inv_mul⟩, ?_⟩
    funext w
    exact Units.ext rfl

theorem finiteEmbedAbove_integerUnitsAboveIncl_mem
    (z : (w : PlacesOver L v) → (w.1.adicCompletionIntegers L)ˣ) :
    finiteEmbedAbove v (integerUnitsAboveIncl v z) ∈ standardOpenSubgroup L := by
  refine (mem_standardOpenSubgroup L).2 fun w ↦ ?_
  rw [← map_inv]
  by_cases h : w.asIdeal.LiesOver v.asIdeal
  · rw [coe_finiteEmbedAbove_snd v _ ⟨w, h⟩, coe_finiteEmbedAbove_snd v _ ⟨w, h⟩]
    exact ⟨(z ⟨w, h⟩ : w.adicCompletionIntegers L).2,
      (((z ⟨w, h⟩)⁻¹ : (w.adicCompletionIntegers L)ˣ) : w.adicCompletionIntegers L).2⟩
  · rw [coe_finiteEmbedAbove_snd_of_not v _ h, coe_finiteEmbedAbove_snd_of_not v _ h]
    exact ⟨(w.adicCompletionIntegers L).one_mem, (w.adicCompletionIntegers L).one_mem⟩

def integerUnitsAboveSmul (σ : L ≃ₐ[K] L)
    (z : (w : PlacesOver L v) → (w.1.adicCompletionIntegers L)ˣ) :
    (w : PlacesOver L v) → (w.1.adicCompletionIntegers L)ˣ :=
  fun w ↦ localIntegerUnit w.1 ⟨σ • finiteEmbedAbove v (integerUnitsAboveIncl v z),
    smul_mem_standardOpenSubgroup σ (finiteEmbedAbove_integerUnitsAboveIncl_mem v z)⟩

instance : SMul (L ≃ₐ[K] L) ((w : PlacesOver L v) → (w.1.adicCompletionIntegers L)ˣ) :=
  ⟨integerUnitsAboveSmul v⟩

theorem integerUnitsAboveIncl_smul (σ : L ≃ₐ[K] L)
    (z : (w : PlacesOver L v) → (w.1.adicCompletionIntegers L)ˣ) :
    integerUnitsAboveIncl v (σ • z) = σ • integerUnitsAboveIncl v z :=
  funext fun _ ↦ Units.ext rfl

instance integerUnitsAboveAction :
    MulDistribMulAction (L ≃ₐ[K] L) ((w : PlacesOver L v) → (w.1.adicCompletionIntegers L)ˣ) :=
  (integerUnitsAboveIncl_injective v).mulDistribMulAction (integerUnitsAboveIncl v)
    (integerUnitsAboveIncl_smul v)

theorem integerUnitsAbove_smul_apply (σ : L ≃ₐ[K] L)
    (z : (w : PlacesOver L v) → (w.1.adicCompletionIntegers L)ˣ) (w : PlacesOver L v) :
    ((((σ • z) (σ • w) : ((σ • w).1.adicCompletionIntegers L)ˣ) :
      (σ • w).1.adicCompletionIntegers L) : (σ • w).1.adicCompletion L) =
      galEquiv v σ w.1 (σ • w).1 rfl ((z w : w.1.adicCompletionIntegers L) :
        w.1.adicCompletion L) := by
  rw [← coe_integerUnitsAboveIncl_apply, integerUnitsAboveIncl_smul, finiteUnitsAbove_smul_apply,
    coe_integerUnitsAboveIncl_apply]

end IdeleGroup

end Sec_13_IdeleGroups_SIdeleGroups_IntegerUnits

/-! ### 14_IdeleGroups.SIdeleGroups.InfinitePlaces -/
section Sec_14_IdeleGroups_SIdeleGroups_InfinitePlaces

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum AdeleBaseChange SemiLocal
open scoped NumberField.AdeleRing


variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

namespace IdeleGroup
open RHDirect.Stage13CFT_IdeleNormResidue.IdeleGroup

section Infinite

variable (v : InfinitePlace K)

open Classical in

def infiniteAdeleAboveFun (a : (w : v.placesOver L) → w.1.Completion) (w : InfinitePlace L) :
    w.Completion :=
  if h : w ∈ v.placesOver L then a ⟨w, h⟩ else 1

omit [NumberField K] [NumberField L] in
theorem infiniteAdeleAboveFun_apply (a : (w : v.placesOver L) → w.1.Completion)
    (w : v.placesOver L) : infiniteAdeleAboveFun v a w.1 = a w := by
  rw [infiniteAdeleAboveFun, dif_pos w.2]

omit [NumberField K] [NumberField L] in
theorem infiniteAdeleAboveFun_apply_of_not (a : (w : v.placesOver L) → w.1.Completion)
    {w : InfinitePlace L} (h : w ∉ v.placesOver L) : infiniteAdeleAboveFun v a w = 1 := by
  rw [infiniteAdeleAboveFun, dif_neg h]

omit [NumberField K] [NumberField L] in
theorem infiniteAdeleAboveFun_one :
    infiniteAdeleAboveFun v (1 : (w : v.placesOver L) → w.1.Completion) = 1 := by
  funext w
  by_cases h : w ∈ v.placesOver L
  · exact infiniteAdeleAboveFun_apply v 1 ⟨w, h⟩
  · exact infiniteAdeleAboveFun_apply_of_not v 1 h

omit [NumberField K] [NumberField L] in
theorem infiniteAdeleAboveFun_mul (a b : (w : v.placesOver L) → w.1.Completion) :
    infiniteAdeleAboveFun v (a * b) = infiniteAdeleAboveFun v a * infiniteAdeleAboveFun v b := by
  funext w
  rw [Pi.mul_apply]
  by_cases h : w ∈ v.placesOver L
  · rw [infiniteAdeleAboveFun_apply v _ ⟨w, h⟩, infiniteAdeleAboveFun_apply v _ ⟨w, h⟩,
      infiniteAdeleAboveFun_apply v _ ⟨w, h⟩, Pi.mul_apply]
  · rw [infiniteAdeleAboveFun_apply_of_not v _ h, infiniteAdeleAboveFun_apply_of_not v _ h,
      infiniteAdeleAboveFun_apply_of_not v _ h, mul_one]

def infiniteAdeleAbove : ((w : v.placesOver L) → w.1.Completion) →* InfiniteAdeleRing L where
  toFun a := infiniteAdeleAboveFun v a
  map_one' := infiniteAdeleAboveFun_one v
  map_mul' a b := infiniteAdeleAboveFun_mul v a b

def infiniteEmbedAbove : ((w : v.placesOver L) → (w.1.Completion)ˣ) →* IdeleGroup L :=
  (Units.map (MonoidHom.prod (infiniteAdeleAbove v) 1 :
      ((w : v.placesOver L) → w.1.Completion) →*
        InfiniteAdeleRing L × FiniteAdeleRing (𝓞 L) L)).comp
    (MulEquiv.piUnits (M := fun w : v.placesOver L ↦ w.1.Completion)).symm.toMonoidHom

omit [NumberField K] in
theorem coe_infiniteEmbedAbove_snd (y : (w : v.placesOver L) → (w.1.Completion)ˣ) :
    ((infiniteEmbedAbove v y : IdeleGroup L) : 𝔸[L]).2 = 1 :=
  rfl

omit [NumberField K] in
theorem coe_infiniteEmbedAbove_fst (y : (w : v.placesOver L) → (w.1.Completion)ˣ)
    (w : v.placesOver L) : ((infiniteEmbedAbove v y : IdeleGroup L) : 𝔸[L]).1 w.1 = y w :=
  infiniteAdeleAboveFun_apply v _ w

omit [NumberField K] in
theorem coe_infiniteEmbedAbove_fst_of_not (y : (w : v.placesOver L) → (w.1.Completion)ˣ)
    {w : InfinitePlace L} (h : w ∉ v.placesOver L) :
    ((infiniteEmbedAbove v y : IdeleGroup L) : 𝔸[L]).1 w = 1 :=
  infiniteAdeleAboveFun_apply_of_not v _ h

def infiniteProjAbove : IdeleGroup L →* ((w : v.placesOver L) → (w.1.Completion)ˣ) :=
  MonoidHom.pi fun w ↦ infiniteProj w.1

omit [NumberField K] in
@[simp]
theorem coe_infiniteProjAbove_apply (x : IdeleGroup L) (w : v.placesOver L) :
    ((infiniteProjAbove v x w : (w.1.Completion)ˣ) : w.1.Completion) = (x : 𝔸[L]).1 w.1 :=
  rfl

omit [NumberField K] in
theorem infiniteProjAbove_infiniteEmbedAbove (y : (w : v.placesOver L) → (w.1.Completion)ˣ) :
    infiniteProjAbove v (infiniteEmbedAbove v y) = y :=
  funext fun w ↦ Units.ext (coe_infiniteEmbedAbove_fst v y w)

omit [NumberField K] [NumberField L] in

theorem comap_mem_placesOver (σ : L ≃ₐ[K] L) (w : v.placesOver L) :
    w.1.comap ((σ : L ≃+* L) : L →+* L) ∈ v.placesOver L := by
  rw [comap_eq_inv_smul]
  exact (σ⁻¹ • w).2

omit [NumberField K] [NumberField L] in
theorem mem_placesOver_of_smul_mem (σ : L ≃ₐ[K] L) {w : InfinitePlace L}
    (h : σ • w ∈ v.placesOver L) : w ∈ v.placesOver L := by
  have := (σ⁻¹ • (⟨σ • w, h⟩ : v.placesOver L)).2
  rwa [RHDirect.CFT_ProfiniteSemilocal.InfinitePlace.coe_smul_placesOver, inv_smul_smul] at this

omit [NumberField K] in

theorem infiniteProjAbove_smul_congr (σ : L ≃ₐ[K] L) {x y : IdeleGroup L}
    (h : infiniteProjAbove v x = infiniteProjAbove v y) :
    infiniteProjAbove v (σ • x) = infiniteProjAbove v (σ • y) := by
  funext u
  refine Units.ext ?_
  rw [coe_infiniteProjAbove_apply, coe_infiniteProjAbove_apply, coe_smul_idele, coe_smul_idele,
    smul_fst, smul_fst]
  congr 1
  exact congrArg (fun f : (w : v.placesOver L) → (w.1.Completion)ˣ ↦
    ((f ⟨u.1.comap ((σ : L ≃+* L) : L →+* L), comap_mem_placesOver v σ u⟩ : _) :
      (u.1.comap ((σ : L ≃+* L) : L →+* L)).Completion)) h

instance infiniteUnitsAboveAction :
    MulDistribMulAction (L ≃ₐ[K] L) ((w : v.placesOver L) → (w.1.Completion)ˣ) where
  smul σ y := infiniteProjAbove v (σ • infiniteEmbedAbove v y)
  one_smul y := by
    change infiniteProjAbove v ((1 : L ≃ₐ[K] L) • infiniteEmbedAbove v y) = y
    rw [one_smul, infiniteProjAbove_infiniteEmbedAbove]
  mul_smul σ τ y := by
    change infiniteProjAbove v ((σ * τ) • infiniteEmbedAbove v y) =
      infiniteProjAbove v
        (σ • infiniteEmbedAbove v (infiniteProjAbove v (τ • infiniteEmbedAbove v y)))
    rw [mul_smul]
    exact infiniteProjAbove_smul_congr v σ (infiniteProjAbove_infiniteEmbedAbove v _).symm
  smul_mul σ y z := by
    change infiniteProjAbove v (σ • infiniteEmbedAbove v (y * z)) =
      infiniteProjAbove v (σ • infiniteEmbedAbove v y) *
        infiniteProjAbove v (σ • infiniteEmbedAbove v z)
    rw [map_mul, smul_mul', map_mul]
  smul_one σ := by
    change infiniteProjAbove v (σ • infiniteEmbedAbove v 1) = 1
    rw [map_one, smul_one, map_one]

omit [NumberField K] in
theorem infiniteUnitsAbove_smul_def (σ : L ≃ₐ[K] L)
    (y : (w : v.placesOver L) → (w.1.Completion)ˣ) :
    σ • y = infiniteProjAbove v (σ • infiniteEmbedAbove v y) :=
  rfl

omit [NumberField K] in
theorem infiniteProjAbove_smul (σ : L ≃ₐ[K] L) (x : IdeleGroup L) :
    infiniteProjAbove v (σ • x) = σ • infiniteProjAbove v x :=
  infiniteProjAbove_smul_congr v σ (infiniteProjAbove_infiniteEmbedAbove v _).symm

theorem infiniteEmbedAbove_smul (σ : L ≃ₐ[K] L) (y : (w : v.placesOver L) → (w.1.Completion)ˣ) :
    infiniteEmbedAbove v (σ • y) = σ • infiniteEmbedAbove v y := by
  refine Units.ext (adele_ext ?_ fun u ↦ ?_)
  · funext u
    by_cases h : u ∈ v.placesOver L
    · rw [coe_infiniteEmbedAbove_fst v _ ⟨u, h⟩, infiniteUnitsAbove_smul_def,
        coe_infiniteProjAbove_apply]
    · rw [coe_infiniteEmbedAbove_fst_of_not v _ h, coe_smul_idele, smul_fst,
        coe_infiniteEmbedAbove_fst_of_not v _ ?_, map_one]
      rw [comap_eq_inv_smul]
      intro h'
      exact h (mem_placesOver_of_smul_mem v σ⁻¹ h')
  · rw [coe_infiniteEmbedAbove_snd, coe_smul_idele, smul_snd, coe_infiniteEmbedAbove_snd]
    exact (map_one (finiteCompletionMap _ u)).symm

omit [NumberField K] in

theorem infiniteProjAbove_infiniteEmbedAbove_of_ne {v v' : InfinitePlace K} (h : v' ≠ v)
    (y : (w : v.placesOver L) → (w.1.Completion)ˣ) :
    infiniteProjAbove v' (infiniteEmbedAbove v y) = 1 := by
  funext u
  refine Units.ext ?_
  rw [coe_infiniteProjAbove_apply, coe_infiniteEmbedAbove_fst_of_not v y]
  · rfl
  · intro hu
    apply h
    rw [← (RHDirect.CFT_ProfiniteSemilocal.InfinitePlace.liesOver_iff_comap_eq v' u.1).1 u.2,
      (RHDirect.CFT_ProfiniteSemilocal.InfinitePlace.liesOver_iff_comap_eq v u.1).1 hu]

omit [NumberField K] in

theorem finiteProjAbove_infiniteEmbedAbove (v' : HeightOneSpectrum (𝓞 K))
    (y : (w : v.placesOver L) → (w.1.Completion)ˣ) :
    finiteProjAbove v' (infiniteEmbedAbove v y) = 1 :=
  funext fun _ ↦ Units.ext rfl

theorem infiniteProjAbove_finiteEmbedAbove (v' : HeightOneSpectrum (𝓞 K))
    (y : (w : PlacesOver L v') → (w.1.adicCompletion L)ˣ) :
    infiniteProjAbove v (finiteEmbedAbove v' y) = 1 :=
  funext fun _ ↦ Units.ext rfl

theorem infiniteUnitsAbove_smul_apply (σ : L ≃ₐ[K] L)
    (y : (w : v.placesOver L) → (w.1.Completion)ˣ) (w : v.placesOver L) :
    (((σ • y) w : (w.1.Completion)ˣ) : w.1.Completion) =
      infiniteCompletionMap (σ : L ≃+* L) w.1
        (y ⟨w.1.comap ((σ : L ≃+* L) : L →+* L), comap_mem_placesOver v σ w⟩) := by
  rw [infiniteUnitsAbove_smul_def, coe_infiniteProjAbove_apply, coe_smul_idele, smul_fst,
    coe_infiniteEmbedAbove_fst v y ⟨_, comap_mem_placesOver v σ w⟩]

end Infinite

end IdeleGroup

end Sec_14_IdeleGroups_SIdeleGroups_InfinitePlaces

/-! ### 15_IdeleGroups.SIdeleGroups.Decomposition -/
section Sec_15_IdeleGroups_SIdeleGroups_Decomposition

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum AdeleBaseChange SemiLocal
open scoped NumberField.AdeleRing RestrictedProduct


variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

namespace IdeleGroup
open RHDirect.Stage13CFT_IdeleNormResidue.IdeleGroup

variable (S : Set (HeightOneSpectrum (𝓞 K)))

variable (L) in

abbrev SIdelesProduct : Type _ :=
  ((v : InfinitePlace K) → (w : v.placesOver L) → (w.1.Completion)ˣ) ×
    ((v : S) → (w : PlacesOver L v.1) → (w.1.adicCompletion L)ˣ) ×
      ((v : ↥Sᶜ) → (w : PlacesOver L v.1) → (w.1.adicCompletionIntegers L)ˣ)

def integerUnitAt (w : HeightOneSpectrum (𝓞 L)) (x : IdeleGroup L) (hx : ord w x = 0) :
    (w.adicCompletionIntegers L)ˣ where
  val := ⟨(x : 𝔸[L]).2 w, ((ord_eq_zero_iff w x).1 hx).1⟩
  inv := ⟨((x⁻¹ : IdeleGroup L) : 𝔸[L]).2 w, ((ord_eq_zero_iff w x).1 hx).2⟩
  val_inv := Subtype.ext (congrArg (fun y : 𝔸[L] ↦ y.2 w) x.mul_inv)
  inv_val := Subtype.ext (congrArg (fun y : 𝔸[L] ↦ y.2 w) x.inv_mul)

omit [NumberField K] in
theorem ord_eq_zero_of_mem_sIdeles_placesAbove {x : IdeleGroup L}
    (hx : x ∈ sIdeles (placesAbove L S)) {v : HeightOneSpectrum (𝓞 K)} (hv : v ∉ S)
    (w : PlacesOver L v) : ord w.1 x = 0 :=
  hx w.1 fun h ↦ hv (by rwa [mem_placesAbove, (below_eq_iff w.1 v).2 w.2] at h)

def sIdelesIntegerPart :
    sIdeles (placesAbove L S) →* ((v : ↥Sᶜ) → (w : PlacesOver L v.1) →
      (w.1.adicCompletionIntegers L)ˣ) where
  toFun x v w := integerUnitAt w.1 x (ord_eq_zero_of_mem_sIdeles_placesAbove S x.2 v.2 w)
  map_one' := funext fun _ ↦ funext fun _ ↦ Units.ext (Subtype.ext rfl)
  map_mul' _ _ := funext fun _ ↦ funext fun _ ↦ Units.ext (Subtype.ext rfl)

omit [NumberField K] in
theorem integerUnitsAboveIncl_sIdelesIntegerPart (x : sIdeles (placesAbove L S)) (v : ↥Sᶜ) :
    integerUnitsAboveIncl v.1 (sIdelesIntegerPart S x v) = finiteProjAbove v.1 (x : IdeleGroup L) :=
  funext fun _ ↦ Units.ext rfl

def sIdelesToProduct : sIdeles (placesAbove L S) →* SIdelesProduct L S :=
  MonoidHom.prod ((MonoidHom.pi fun v ↦ infiniteProjAbove v).comp (sIdeles _).subtype)
    (MonoidHom.prod ((MonoidHom.pi fun v : S ↦ finiteProjAbove v.1).comp (sIdeles _).subtype)
      (sIdelesIntegerPart S))

omit [NumberField K] in
theorem sIdelesToProduct_snd_snd (x : sIdeles (placesAbove L S)) (v : ↥Sᶜ) :
    (sIdelesToProduct S x).2.2 v = sIdelesIntegerPart S x v :=
  rfl

theorem sIdelesToProduct_smul (σ : L ≃ₐ[K] L) (x : sIdeles (placesAbove L S)) :
    sIdelesToProduct S (σ • x) = σ • sIdelesToProduct S x := by
  refine Prod.ext (funext fun v ↦ ?_) (Prod.ext (funext fun v ↦ ?_) (funext fun v ↦ ?_))
  · exact infiniteProjAbove_smul v σ (x : IdeleGroup L)
  · exact finiteProjAbove_smul v.1 σ (x : IdeleGroup L)
  · apply integerUnitsAboveIncl_injective v.1
    change integerUnitsAboveIncl v.1 (sIdelesIntegerPart S (σ • x) v) =
      integerUnitsAboveIncl v.1 (σ • sIdelesIntegerPart S x v)
    rw [integerUnitsAboveIncl_smul, integerUnitsAboveIncl_sIdelesIntegerPart,
      integerUnitsAboveIncl_sIdelesIntegerPart, coe_smul_sIdeles]
    exact finiteProjAbove_smul v.1 σ (x : IdeleGroup L)

omit [NumberField K] [NumberField L] in
theorem mem_placesOver_comap (u : InfinitePlace L) :
    u ∈ (u.comap (algebraMap K L)).placesOver L :=
  (RHDirect.CFT_ProfiniteSemilocal.InfinitePlace.liesOver_iff_comap_eq _ u).2 rfl

omit [NumberField K] in

theorem sIdelesToProduct_injective : Function.Injective (sIdelesToProduct (L := L) S) := by
  intro x y h
  refine Subtype.ext (Units.ext (adele_ext (funext fun u ↦ ?_) fun u ↦ ?_))
  · exact congrArg (fun p : SIdelesProduct L S ↦ ((p.1 (u.comap (algebraMap K L))
      ⟨u, mem_placesOver_comap u⟩ : (u.Completion)ˣ) : u.Completion)) h
  · by_cases hu : below K u ∈ S
    · exact congrArg (fun p : SIdelesProduct L S ↦ ((p.2.1 ⟨below K u, hu⟩
        ⟨u, inferInstance⟩ : (u.adicCompletion L)ˣ) : u.adicCompletion L)) h
    · exact congrArg (fun p : SIdelesProduct L S ↦ (((p.2.2 ⟨below K u, hu⟩
        ⟨u, inferInstance⟩ : (u.adicCompletionIntegers L)ˣ) : u.adicCompletionIntegers L) :
          u.adicCompletion L)) h

variable {S}

def assembleInfinite (p : SIdelesProduct L S) (u : InfinitePlace L) : (u.Completion)ˣ :=
  p.1 (u.comap (algebraMap K L)) ⟨u, mem_placesOver_comap u⟩

open Classical in

def assembleFinite (p : SIdelesProduct L S) (u : HeightOneSpectrum (𝓞 L)) :
    (u.adicCompletion L)ˣ :=
  if h : below K u ∈ S then p.2.1 ⟨below K u, h⟩ ⟨u, inferInstance⟩
  else integerUnitsAboveIncl (below K u) (p.2.2 ⟨below K u, h⟩) ⟨u, inferInstance⟩

omit [NumberField K] in
theorem assembleInfinite_eq (p : SIdelesProduct L S) (v : InfinitePlace K) (w : v.placesOver L) :
    assembleInfinite p w.1 = p.1 v w := by
  obtain ⟨u, hu⟩ := w
  have e : u.comap (algebraMap K L) = v := (RHDirect.CFT_ProfiniteSemilocal.InfinitePlace.liesOver_iff_comap_eq v u).1 hu
  subst e
  rfl

omit [NumberField K] in
theorem assembleFinite_eq_of_mem (p : SIdelesProduct L S) (v : S) (w : PlacesOver L v.1) :
    assembleFinite p w.1 = p.2.1 v w := by
  obtain ⟨u, hu⟩ := w
  obtain ⟨v, hv⟩ := v
  have e : below K u = v := (below_eq_iff u v).2 hu
  subst e
  rw [assembleFinite, dif_pos hv]

omit [NumberField K] in
theorem assembleFinite_eq_of_not_mem (p : SIdelesProduct L S) (v : ↥Sᶜ) (w : PlacesOver L v.1) :
    assembleFinite p w.1 = integerUnitsAboveIncl v.1 (p.2.2 v) w := by
  obtain ⟨u, hu⟩ := w
  obtain ⟨v, hv⟩ := v
  have e : below K u = v := (below_eq_iff u v).2 hu
  subst e
  rw [assembleFinite, dif_neg hv]

omit [NumberField K] in
theorem assembleFinite_mem (p : SIdelesProduct L S) {u : HeightOneSpectrum (𝓞 L)}
    (hu : u ∉ placesAbove L S) :
    (assembleFinite p u : u.adicCompletion L) ∈ u.adicCompletionIntegers L ∧
      ((assembleFinite p u)⁻¹ : (u.adicCompletion L)ˣ).val ∈ u.adicCompletionIntegers L := by
  rw [assembleFinite_eq_of_not_mem p ⟨below K u, hu⟩ ⟨u, inferInstance⟩]
  exact (mem_range_integerUnitsAboveIncl_iff (below K u) _).1 ⟨_, rfl⟩ ⟨u, inferInstance⟩

theorem assembleFinite_eventually (hS : S.Finite) (p : SIdelesProduct L S) :
    ∀ᶠ u in Filter.cofinite,
      (assembleFinite p u : u.adicCompletion L) ∈ u.adicCompletionIntegers L :=
  Filter.eventually_cofinite.2 ((placesAbove_finite hS).subset fun _ hu ↦
    Classical.byContradiction fun h ↦ hu (assembleFinite_mem p h).1)

theorem assembleFinite_inv_eventually (hS : S.Finite) (p : SIdelesProduct L S) :
    ∀ᶠ u in Filter.cofinite,
      ((assembleFinite p u)⁻¹ : (u.adicCompletion L)ˣ).val ∈ u.adicCompletionIntegers L :=
  Filter.eventually_cofinite.2 ((placesAbove_finite hS).subset fun _ hu ↦
    Classical.byContradiction fun h ↦ hu (assembleFinite_mem p h).2)

def assemble (hS : S.Finite) (p : SIdelesProduct L S) : IdeleGroup L where
  val := ((fun u ↦ (assembleInfinite p u : u.Completion) : (u : InfinitePlace L) → u.Completion),
    (⟨fun u ↦ (assembleFinite p u : u.adicCompletion L), assembleFinite_eventually hS p⟩ :
      Πʳ u : HeightOneSpectrum (𝓞 L), [u.adicCompletion L, u.adicCompletionIntegers L]))
  inv := ((fun u ↦ ((assembleInfinite p u)⁻¹ : (u.Completion)ˣ).val :
      (u : InfinitePlace L) → u.Completion),
    (⟨fun u ↦ ((assembleFinite p u)⁻¹ : (u.adicCompletion L)ˣ).val,
        assembleFinite_inv_eventually hS p⟩ :
      Πʳ u : HeightOneSpectrum (𝓞 L), [u.adicCompletion L, u.adicCompletionIntegers L]))
  val_inv := adele_ext (funext fun u ↦ (assembleInfinite p u).mul_inv)
    fun u ↦ (assembleFinite p u).mul_inv
  inv_val := adele_ext (funext fun u ↦ (assembleInfinite p u).inv_mul)
    fun u ↦ (assembleFinite p u).inv_mul

theorem assemble_mem (hS : S.Finite) (p : SIdelesProduct L S) :
    assemble hS p ∈ sIdeles (placesAbove L S) :=
  fun u hu ↦ (ord_eq_zero_iff u _).2 (assembleFinite_mem p hu)

theorem sIdelesToProduct_assemble (hS : S.Finite) (p : SIdelesProduct L S) :
    sIdelesToProduct S ⟨assemble hS p, assemble_mem hS p⟩ = p := by
  refine Prod.ext (funext fun v ↦ funext fun w ↦ ?_)
    (Prod.ext (funext fun v ↦ funext fun w ↦ ?_) (funext fun v ↦ ?_))
  · exact Units.ext (congrArg Units.val (assembleInfinite_eq p v w))
  · exact Units.ext (congrArg Units.val (assembleFinite_eq_of_mem p v w))
  · apply integerUnitsAboveIncl_injective v.1
    rw [sIdelesToProduct_snd_snd, integerUnitsAboveIncl_sIdelesIntegerPart]
    funext w
    exact Units.ext (congrArg Units.val (assembleFinite_eq_of_not_mem p v w))

variable (S)

theorem sIdelesToProduct_surjective (hS : S.Finite) :
    Function.Surjective (sIdelesToProduct (L := L) S) :=
  fun p ↦ ⟨⟨assemble hS p, assemble_mem hS p⟩, sIdelesToProduct_assemble hS p⟩

def sIdelesEquivProduct (hS : S.Finite) : sIdeles (placesAbove L S) ≃* SIdelesProduct L S :=
  MulEquiv.ofBijective (sIdelesToProduct S)
    ⟨sIdelesToProduct_injective S, sIdelesToProduct_surjective S hS⟩

theorem sIdelesEquivProduct_smul (hS : S.Finite) (σ : L ≃ₐ[K] L) (x : sIdeles (placesAbove L S)) :
    sIdelesEquivProduct S hS (σ • x) = σ • sIdelesEquivProduct S hS x :=
  sIdelesToProduct_smul S σ x

end IdeleGroup

end Sec_15_IdeleGroups_SIdeleGroups_Decomposition

/-! ### 16_IdeleGroups.LocalHerbrand -/
section Sec_16_IdeleGroups_LocalHerbrand

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField ValuativeRel RHDirect.Stage13CFT_IdeleNormResidue

open scoped Pointwise


section ChangeOfGroup

variable {k H G V W : Type*} [CommRing k] [Group H] [Group G] [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W] {ρ' : Representation k H V} {ρ : Representation k G W}

theorem cycSubOne_mulEquiv (e : H →* G) (f : V ≃+ W) (hf : ∀ h x, f (ρ' h x) = ρ (e h) (f x))
    (τ : H) (x : V) : f (cycSubOne ρ' τ x) = cycSubOne ρ (e τ) (f x) := by
  rw [cycSubOne_apply, cycSubOne_apply, map_sub, hf]

variable [Fintype H] [Fintype G]

theorem cycNorm_mulEquiv (e : H ≃* G) (f : V ≃+ W) (hf : ∀ h x, f (ρ' h x) = ρ (e h) (f x))
    (x : V) : f (cycNorm ρ' x) = cycNorm ρ (f x) := by
  rw [cycNorm_apply, cycNorm_apply, map_sum]
  simp_rw [hf]
  exact Fintype.sum_equiv e.toEquiv _ _ fun _ ↦ rfl

def cycTateZeroEquivOfMulEquiv (e : H ≃* G) (f : V ≃+ W) (hf : ∀ h x, f (ρ' h x) = ρ (e h) (f x))
    (τ : H) : CycTateZero ρ' τ ≃+ CycTateZero ρ (e τ) :=
  kerModRangeCongr f (cycSubOne_mulEquiv e.toMonoidHom f hf τ) (cycNorm_mulEquiv e f hf)

def cycTateNegOneEquivOfMulEquiv (e : H ≃* G) (f : V ≃+ W)
    (hf : ∀ h x, f (ρ' h x) = ρ (e h) (f x)) (τ : H) :
    CycTateNegOne ρ' τ ≃+ CycTateNegOne ρ (e τ) :=
  kerModRangeCongr f (cycNorm_mulEquiv e f hf) (cycSubOne_mulEquiv e.toMonoidHom f hf τ)

theorem cycHerbrand_eq_of_mulEquiv (e : H ≃* G) (f : V ≃+ W)
    (hf : ∀ h x, f (ρ' h x) = ρ (e h) (f x)) (τ : H) :
    (HasHerbrandQuotient (cycSubOne ρ' τ) (cycNorm ρ') ↔
      HasHerbrandQuotient (cycSubOne ρ (e τ)) (cycNorm ρ)) ∧
    cycHerbrand ρ' τ = cycHerbrand ρ (e τ) := by
  have e0 := (cycTateZeroEquivOfMulEquiv e f hf τ).toEquiv
  have e1 := (cycTateNegOneEquivOfMulEquiv e f hf τ).toEquiv
  refine ⟨?_, ?_⟩
  · exact ⟨fun h ↦ ⟨Finite.of_equiv _ e0 (h := h.1), Finite.of_equiv _ e1 (h := h.2)⟩,
      fun h ↦ ⟨Finite.of_equiv _ e0.symm (h := h.1), Finite.of_equiv _ e1.symm (h := h.2)⟩⟩
  · rw [cycHerbrand_eq, cycHerbrand_eq, Nat.card_congr e0, Nat.card_congr e1]

omit [Fintype H] [Fintype G] in

theorem mem_zpowers_mulEquiv (e : H ≃* G) {τ : H} (hτ : ∀ h, h ∈ Subgroup.zpowers τ) (g : G) :
    g ∈ Subgroup.zpowers (e τ) := by
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 (hτ (e.symm g))
  refine Subgroup.mem_zpowers_iff.2 ⟨n, ?_⟩
  rw [← map_zpow, hn, MulEquiv.apply_symm_apply]

end ChangeOfGroup

section DecompositionAction

variable {K L : Type*} [Field K] [Field L] [NumberField L] [Algebra K L]
  (w : HeightOneSpectrum (𝓞 L))

instance decompositionMulSemiringAction :
    MulSemiringAction (MulAction.stabilizer Gal(L/K) w.asIdeal) (w.adicCompletion L) where
  smul σ x := adicCompletionRingHomOf w σ.1 (smul_asIdeal_of_mem_stabilizer w σ) x
  one_smul x := by
    change adicCompletionRingHomOf w 1 _ x = RingHom.id _ x
    congr 1
    exact ringHom_ext_adicCompletion w (continuous_adicCompletionRingHomOf _ _) continuous_id
      fun y ↦ by rw [adicCompletionRingHomOf_algebraMap]; rfl
  mul_smul σ τ x := by
    change adicCompletionRingHomOf w (σ * τ).1 (smul_asIdeal_of_mem_stabilizer w (σ * τ)) x =
      ((adicCompletionRingHomOf w σ.1 (smul_asIdeal_of_mem_stabilizer w σ)).comp
        (adicCompletionRingHomOf w τ.1 (smul_asIdeal_of_mem_stabilizer w τ))) x
    congr 1
    exact ringHom_ext_adicCompletion w (continuous_adicCompletionRingHomOf _ _)
      ((continuous_adicCompletionRingHomOf σ.1 (smul_asIdeal_of_mem_stabilizer w σ)).comp
        (continuous_adicCompletionRingHomOf τ.1 (smul_asIdeal_of_mem_stabilizer w τ)))
      fun y ↦ by
        rw [RingHom.comp_apply, adicCompletionRingHomOf_algebraMap,
          adicCompletionRingHomOf_algebraMap, adicCompletionRingHomOf_algebraMap]
        rfl
  smul_zero σ := map_zero _
  smul_add σ := map_add _
  smul_one σ := map_one _
  smul_mul σ := map_mul _

variable {w}

theorem decomposition_smul_def (σ : MulAction.stabilizer Gal(L/K) w.asIdeal)
    (x : w.adicCompletion L) :
    σ • x = adicCompletionRingHomOf w σ.1 (smul_asIdeal_of_mem_stabilizer w σ) x :=
  rfl

theorem valued_decomposition_smul (σ : MulAction.stabilizer Gal(L/K) w.asIdeal)
    (x : w.adicCompletion L) : Valued.v (σ • x) = Valued.v x :=
  valued_adicCompletionRingHomOf _ _ x

variable (w)

instance decompositionMulSemiringActionIntegers :
    MulSemiringAction (MulAction.stabilizer Gal(L/K) w.asIdeal) (w.adicCompletionIntegers L) where
  smul σ x := ⟨σ • (x : w.adicCompletion L), by
    rw [mem_adicCompletionIntegers, valued_decomposition_smul]
    exact x.2⟩
  one_smul x := Subtype.ext (one_smul _ (x : w.adicCompletion L))
  mul_smul σ τ x := Subtype.ext (mul_smul σ τ (x : w.adicCompletion L))
  smul_zero σ := Subtype.ext (smul_zero σ)
  smul_add σ x y := Subtype.ext (smul_add σ (x : w.adicCompletion L) y)
  smul_one σ := Subtype.ext (smul_one σ)
  smul_mul σ x y := Subtype.ext (MulSemiringAction.smul_mul σ (x : w.adicCompletion L) y)

variable {w} in
@[simp]
theorem coe_decomposition_smul_integers (σ : MulAction.stabilizer Gal(L/K) w.asIdeal)
    (x : w.adicCompletionIntegers L) :
    ((σ • x : w.adicCompletionIntegers L) : w.adicCompletion L) = σ • (x : w.adicCompletion L) :=
  rfl

instance decompositionUnitsAction :
    MulDistribMulAction (MulAction.stabilizer Gal(L/K) w.asIdeal) (w.adicCompletion L)ˣ :=
  Units.mulDistribMulActionRight

instance decompositionIntegerUnitsAction :
    MulDistribMulAction (MulAction.stabilizer Gal(L/K) w.asIdeal) (w.adicCompletionIntegers L)ˣ :=
  Units.mulDistribMulActionRight

variable {w}

@[simp]
theorem coe_decomposition_smul_units (σ : MulAction.stabilizer Gal(L/K) w.asIdeal)
    (u : (w.adicCompletion L)ˣ) : ((σ • u : (w.adicCompletion L)ˣ) : w.adicCompletion L) =
      σ • (u : w.adicCompletion L) :=
  rfl

@[simp]
theorem coe_decomposition_smul_integerUnits (σ : MulAction.stabilizer Gal(L/K) w.asIdeal)
    (u : (w.adicCompletionIntegers L)ˣ) :
    (((σ • u : (w.adicCompletionIntegers L)ˣ) : w.adicCompletionIntegers L) :
      w.adicCompletion L) = σ • ((u : w.adicCompletionIntegers L) : w.adicCompletion L) :=
  rfl

end DecompositionAction

section Units

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]
  [Algebra (v.adicCompletion K) (w.adicCompletion L)]
  [ContinuousSMul (v.adicCompletion K) (w.adicCompletion L)]
  [IsScalarTower K (v.adicCompletion K) (w.adicCompletion L)]

theorem ofMulDistribMulAction_decomposition_units (σ : MulAction.stabilizer Gal(L/K) w.asIdeal)
    (x : Additive (w.adicCompletion L)ˣ) :
    Representation.ofMulDistribMulAction (MulAction.stabilizer Gal(L/K) w.asIdeal)
        (w.adicCompletion L)ˣ σ x =
      Representation.ofMulDistribMulAction Gal(w.adicCompletion L/v.adicCompletion K)
        (w.adicCompletion L)ˣ (decompositionMulEquiv v w σ) x := by
  apply Additive.toMul.injective
  apply Units.ext
  rfl

theorem cycHerbrand_adicCompletion_units [Fintype (MulAction.stabilizer Gal(L/K) w.asIdeal)]
    (τ : MulAction.stabilizer Gal(L/K) w.asIdeal) (hτ : ∀ σ, σ ∈ Subgroup.zpowers τ) :
    HasHerbrandQuotient
        (cycSubOne (Representation.ofMulDistribMulAction (MulAction.stabilizer Gal(L/K) w.asIdeal)
          (w.adicCompletion L)ˣ) τ)
        (cycNorm (Representation.ofMulDistribMulAction (MulAction.stabilizer Gal(L/K) w.asIdeal)
          (w.adicCompletion L)ˣ)) ∧
      cycHerbrand (Representation.ofMulDistribMulAction (MulAction.stabilizer Gal(L/K) w.asIdeal)
          (w.adicCompletion L)ˣ) τ =
        Module.finrank (v.adicCompletion K) (w.adicCompletion L) := by
  obtain ⟨h1, h2⟩ := cycHerbrand_eq_of_mulEquiv
    (ρ' := Representation.ofMulDistribMulAction (MulAction.stabilizer Gal(L/K) w.asIdeal)
      (w.adicCompletion L)ˣ)
    (ρ := Representation.ofMulDistribMulAction Gal(w.adicCompletion L/v.adicCompletion K)
      (w.adicCompletion L)ˣ)
    (decompositionMulEquiv v w) (AddEquiv.refl _)
    (fun σ x ↦ ofMulDistribMulAction_decomposition_units v w σ x) τ
  obtain ⟨h3, h4⟩ := RHDirect.CFT.LocalField.cycHerbrand_units_eq_finrank
    (K := v.adicCompletion K) (L := w.adicCompletion L)
    (mem_zpowers_mulEquiv (decompositionMulEquiv v w) hτ)
  exact ⟨h1.2 h3, h2.trans h4⟩

end Units

section UnitsCard

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]

def adicCompletionIntegersEquivInteger :
    w.adicCompletionIntegers L ≃+* 𝒪[w.adicCompletion L] where
  toFun x := ⟨x, (mem_valuationInteger_iff w (x : w.adicCompletion L)).2 x.2⟩
  invFun y := ⟨y, (mem_valuationInteger_iff w (y : w.adicCompletion L)).1 y.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

def integerUnitsAddEquiv :
    Additive (w.adicCompletionIntegers L)ˣ ≃+ Additive 𝒪[w.adicCompletion L]ˣ :=
  MulEquiv.toAdditive (Units.mapEquiv (adicCompletionIntegersEquivInteger w).toMulEquiv)

@[simp]
theorem coe_integerUnitsAddEquiv (x : Additive (w.adicCompletionIntegers L)ˣ) :
    ((((integerUnitsAddEquiv w x).toMul : 𝒪[w.adicCompletion L]ˣ) : 𝒪[w.adicCompletion L]) :
      w.adicCompletion L) = ((x.toMul : w.adicCompletionIntegers L) : w.adicCompletion L) :=
  rfl

variable [Algebra (v.adicCompletion K) (w.adicCompletion L)]
  [ContinuousSMul (v.adicCompletion K) (w.adicCompletion L)]
  [IsScalarTower K (v.adicCompletion K) (w.adicCompletion L)]

theorem integerUnitsAddEquiv_decomposition (σ : MulAction.stabilizer Gal(L/K) w.asIdeal)
    (x : Additive (w.adicCompletionIntegers L)ˣ) :
    integerUnitsAddEquiv w (Representation.ofMulDistribMulAction
        (MulAction.stabilizer Gal(L/K) w.asIdeal) (w.adicCompletionIntegers L)ˣ σ x) =
      Representation.ofMulDistribMulAction Gal(w.adicCompletion L/v.adicCompletion K)
        𝒪[w.adicCompletion L]ˣ (decompositionMulEquiv v w σ) (integerUnitsAddEquiv w x) := by
  apply Additive.toMul.injective
  apply Units.ext
  apply Subtype.ext
  change σ • ((x.toMul : w.adicCompletionIntegers L) : w.adicCompletion L) =
    ((RHDirect.CFT.LocalField.integerAlgEquiv (v.adicCompletion K) (w.adicCompletion L)
      (decompositionMulEquiv v w σ) _ : 𝒪[w.adicCompletion L]) : w.adicCompletion L)
  rw [RHDirect.CFT.LocalField.coe_integerAlgEquiv_apply]
  rfl

omit [IsGalois K L] in

theorem isUnramified_adicCompletion (he : w.asIdeal.ramificationIdx (𝓞 K) = 1) :
    RHDirect.CFT.LocalField.IsUnramified (v.adicCompletion K) (w.adicCompletion L) :=
  (RHDirect.CFT.LocalField.isUnramified_iff _ _).2 (by
    rw [RHDirect.CFT.LocalField.ramificationIndex, ramificationIdx_integer v w, he])

end UnitsCard

section Unramified

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]

open AdicLiesOver in
include v in

theorem subsingleton_cycTateZero_adicCompletionIntegers_units
    (he : w.asIdeal.ramificationIdx (𝓞 K) = 1)
    [Fintype (MulAction.stabilizer Gal(L/K) w.asIdeal)]
    (τ : MulAction.stabilizer Gal(L/K) w.asIdeal) (hτ : ∀ σ, σ ∈ Subgroup.zpowers τ) :
    Subsingleton (CycTateZero (Representation.ofMulDistribMulAction
      (MulAction.stabilizer Gal(L/K) w.asIdeal) (w.adicCompletionIntegers L)ˣ) τ) := by
  have := isUnramified_adicCompletion v w he
  have hgen := mem_zpowers_mulEquiv (decompositionMulEquiv v w) hτ
  have : Subsingleton (RHDirect.CFT.LocalField.TateZero Gal(w.adicCompletion L/v.adicCompletion K)
      𝒪[w.adicCompletion L]ˣ) := RHDirect.CFT.LocalField.subsingleton_tateZero_integerUnits
  have h1 : Nat.card (RHDirect.CFT.LocalField.TateZero Gal(w.adicCompletion L/v.adicCompletion K)
      𝒪[w.adicCompletion L]ˣ) = 1 := Nat.card_eq_one_iff_unique.2 ⟨inferInstance, ⟨1⟩⟩
  rw [RHDirect.CFT.LocalField.natCard_tateZero_eq hgen, ← Nat.card_congr
    (cycTateZeroEquivOfMulEquiv (decompositionMulEquiv v w) (integerUnitsAddEquiv w)
      (integerUnitsAddEquiv_decomposition v w) τ).toEquiv] at h1
  exact (Nat.card_eq_one_iff_unique.1 h1).1

open AdicLiesOver in
include v in

theorem subsingleton_cycTateNegOne_adicCompletionIntegers_units
    (he : w.asIdeal.ramificationIdx (𝓞 K) = 1)
    [Fintype (MulAction.stabilizer Gal(L/K) w.asIdeal)]
    (τ : MulAction.stabilizer Gal(L/K) w.asIdeal) (hτ : ∀ σ, σ ∈ Subgroup.zpowers τ) :
    Subsingleton (CycTateNegOne (Representation.ofMulDistribMulAction
      (MulAction.stabilizer Gal(L/K) w.asIdeal) (w.adicCompletionIntegers L)ˣ) τ) := by
  have := isUnramified_adicCompletion v w he
  have hgen := mem_zpowers_mulEquiv (decompositionMulEquiv v w) hτ
  have : IsCyclic Gal(w.adicCompletion L/v.adicCompletion K) :=
    ⟨⟨decompositionMulEquiv v w τ, fun g ↦ Subgroup.mem_zpowers_iff.1 (hgen g)⟩⟩
  have : Subsingleton (RHDirect.CFT.LocalField.TateNegOne Gal(w.adicCompletion L/v.adicCompletion K)
      𝒪[w.adicCompletion L]ˣ) := RHDirect.CFT.LocalField.subsingleton_tateNegOne_integerUnits
  have h1 : Nat.card (RHDirect.CFT.LocalField.TateNegOne Gal(w.adicCompletion L/v.adicCompletion K)
      𝒪[w.adicCompletion L]ˣ) = 1 := Nat.card_eq_one_iff_unique.2 ⟨inferInstance, ⟨1⟩⟩
  rw [RHDirect.CFT.LocalField.natCard_tateNegOne_eq hgen, ← Nat.card_congr
    (cycTateNegOneEquivOfMulEquiv (decompositionMulEquiv v w) (integerUnitsAddEquiv w)
      (integerUnitsAddEquiv_decomposition v w) τ).toEquiv] at h1
  exact (Nat.card_eq_one_iff_unique.1 h1).1

end Unramified

end Sec_16_IdeleGroups_LocalHerbrand

/-! ### 17_IdeleGroups.LocalHerbrandInfinite -/
section Sec_17_IdeleGroups_LocalHerbrandInfinite

open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion RHDirect.Stage13CFT_IdeleNormResidue

open scoped NumberField.LiesOver


section NeZero

variable {k G V : Type*} [CommRing k] [Group G] [Fintype G] [AddCommGroup V] [Module k V]

theorem hasHerbrandQuotient_of_cycHerbrand_ne_zero {ρ : Representation k G V} {σ : G}
    (h : cycHerbrand ρ σ ≠ 0) : HasHerbrandQuotient (cycSubOne ρ σ) (cycNorm ρ) := by
  rw [cycHerbrand_eq] at h
  have h0 : Nat.card (CycTateZero ρ σ) ≠ 0 := fun h' ↦ h (by rw [h', Nat.cast_zero, zero_div])
  have h1 : Nat.card (CycTateNegOne ρ σ) ≠ 0 := fun h' ↦ h (by rw [h', Nat.cast_zero, div_zero])
  exact ⟨Nat.finite_of_card_ne_zero h0, Nat.finite_of_card_ne_zero h1⟩

end NeZero

section Action

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (w : InfinitePlace L)

theorem apply_algEquiv_of_mem_stabilizer {σ : Gal(L/K)}
    (hσ : σ ∈ MulAction.stabilizer Gal(L/K) w) (x : L) : w (σ x) = w x := by
  have h := congrArg (fun u : InfinitePlace L ↦ u (σ x)) (MulAction.mem_stabilizer_iff.1 hσ)
  simp only [InfinitePlace.smul_apply, AlgEquiv.symm_apply_apply] at h
  exact h.symm

def withAbsMapOf (σ : Gal(L/K)) : WithAbs w.1 →+* WithAbs w.1 :=
  WithAbs.map w.1 w.1 (σ : L →+* L)

theorem ofAbs_withAbsMapOf (σ : Gal(L/K)) (x : WithAbs w.1) :
    (withAbsMapOf w σ x).ofAbs = σ x.ofAbs :=
  rfl

variable {w}

theorem isometry_withAbsMapOf {σ : Gal(L/K)} (hσ : σ ∈ MulAction.stabilizer Gal(L/K) w) :
    Isometry (withAbsMapOf w σ) :=
  AddMonoidHomClass.isometry_of_norm _ fun x ↦ by
    rw [WithAbs.norm_eq_apply_ofAbs, WithAbs.norm_eq_apply_ofAbs, ofAbs_withAbsMapOf]
    exact apply_algEquiv_of_mem_stabilizer w hσ x.ofAbs

def completionRingHomOf {σ : Gal(L/K)} (hσ : σ ∈ MulAction.stabilizer Gal(L/K) w) :
    w.Completion →+* w.Completion :=
  ((Completion.equiv w).symm.toRingHom.comp (isometry_withAbsMapOf hσ).mapRingHom).comp
    (Completion.equiv w).toRingHom

theorem continuous_completionRingHomOf {σ : Gal(L/K)}
    (hσ : σ ∈ MulAction.stabilizer Gal(L/K) w) : Continuous (completionRingHomOf hσ) :=
  (continuous_ofCompletion w).comp <|
    UniformSpace.Completion.continuous_map.comp (continuous_toCompletion w)

theorem completionRingHomOf_coe {σ : Gal(L/K)} (hσ : σ ∈ MulAction.stabilizer Gal(L/K) w)
    (x : WithAbs w.1) :
    completionRingHomOf hσ (x : w.Completion) = ((withAbsMapOf w σ x : WithAbs w.1) :
      w.Completion) :=
  Completion.ext <| (isometry_withAbsMapOf hσ).mapRingHom_coe x

variable (w) in

theorem ringHom_ext_completion {f g : w.Completion →+* w.Completion} (hf : Continuous f)
    (hg : Continuous g) (h : ∀ x : WithAbs w.1, f (x : w.Completion) = g (x : w.Completion)) :
    f = g :=
  RingHom.ext (congrFun ((denseRange_coe w).equalizer hf hg (funext h)))

variable (w)

instance infiniteDecompositionMulSemiringAction :
    MulSemiringAction (MulAction.stabilizer Gal(L/K) w) w.Completion where
  smul σ x := completionRingHomOf σ.2 x
  one_smul x := by
    change completionRingHomOf (1 : MulAction.stabilizer Gal(L/K) w).2 x = RingHom.id _ x
    congr 1
    exact ringHom_ext_completion w (continuous_completionRingHomOf _) continuous_id fun y ↦ by
      rw [completionRingHomOf_coe]
      rfl
  mul_smul σ τ x := by
    change completionRingHomOf (σ * τ).2 x =
      ((completionRingHomOf σ.2).comp (completionRingHomOf τ.2)) x
    congr 1
    exact ringHom_ext_completion w (continuous_completionRingHomOf _)
      ((continuous_completionRingHomOf σ.2).comp (continuous_completionRingHomOf τ.2)) fun y ↦ by
        rw [RingHom.comp_apply, completionRingHomOf_coe, completionRingHomOf_coe,
          completionRingHomOf_coe]
        rfl
  smul_zero σ := map_zero _
  smul_add σ := map_add _
  smul_one σ := map_one _
  smul_mul σ := map_mul _

instance infiniteDecompositionUnitsAction :
    MulDistribMulAction (MulAction.stabilizer Gal(L/K) w) w.Completionˣ :=
  Units.mulDistribMulActionRight

variable {w}

theorem infiniteDecomposition_smul_def (σ : MulAction.stabilizer Gal(L/K) w) (x : w.Completion) :
    σ • x = completionRingHomOf σ.2 x :=
  rfl

theorem infiniteDecomposition_smul_coe (σ : MulAction.stabilizer Gal(L/K) w) (x : WithAbs w.1) :
    σ • (x : w.Completion) =
      ((withAbsMapOf w (σ : Gal(L/K)) x : WithAbs w.1) : w.Completion) :=
  completionRingHomOf_coe σ.2 x

theorem continuous_infiniteDecomposition_smul (σ : MulAction.stabilizer Gal(L/K) w) :
    Continuous fun x : w.Completion ↦ σ • x :=
  continuous_completionRingHomOf σ.2

end Action

section Local

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (v : InfinitePlace K)
  (w : InfinitePlace L) [w.LiesOver v]

theorem infiniteDecomposition_smul_algebraMap (σ : MulAction.stabilizer Gal(L/K) w)
    (c : v.Completion) :
    σ • algebraMap v.Completion w.Completion c = algebraMap v.Completion w.Completion c := by
  have h := (denseRange_coe v).equalizer
    ((continuous_infiniteDecomposition_smul σ).comp
      (continuous_algebraMap v.Completion w.Completion))
    (continuous_algebraMap v.Completion w.Completion) (funext fun x ↦ ?_)
  · exact congrFun h c
  · simp only [Function.comp_apply]
    rw [Completion.algebraMap_coe, infiniteDecomposition_smul_coe]
    congr 2
    apply (WithAbs.equiv w.1).injective
    change σ.1 (algebraMap (WithAbs v.1) (WithAbs w.1) x).ofAbs =
      (algebraMap (WithAbs v.1) (WithAbs w.1) x).ofAbs
    rw [WithAbs.ofAbs_algebraMap, AlgEquiv.commutes]

def infiniteDecompositionAlgEquiv (σ : MulAction.stabilizer Gal(L/K) w) :
    Gal(w.Completion/v.Completion) :=
  AlgEquiv.ofRingEquiv (f := MulSemiringAction.toRingEquiv _ w.Completion σ)
    (infiniteDecomposition_smul_algebraMap v w σ)

@[simp]
theorem infiniteDecompositionAlgEquiv_apply (σ : MulAction.stabilizer Gal(L/K) w)
    (x : w.Completion) : infiniteDecompositionAlgEquiv v w σ x = σ • x :=
  rfl

def infiniteDecompositionToLocal :
    MulAction.stabilizer Gal(L/K) w →* Gal(w.Completion/v.Completion) where
  toFun := infiniteDecompositionAlgEquiv v w
  map_one' := AlgEquiv.ext fun x ↦ one_smul (MulAction.stabilizer Gal(L/K) w) x
  map_mul' σ τ := AlgEquiv.ext fun x ↦ mul_smul σ τ x

@[simp]
theorem infiniteDecompositionToLocal_apply (σ : MulAction.stabilizer Gal(L/K) w)
    (x : w.Completion) : infiniteDecompositionToLocal v w σ x = σ • x :=
  rfl

theorem infiniteDecompositionToLocal_injective :
    Function.Injective (infiniteDecompositionToLocal v w) := by
  rw [injective_iff_map_eq_one]
  intro σ hσ
  apply Subtype.ext
  apply AlgEquiv.ext
  intro x
  have h := congrArg (fun f : Gal(w.Completion/v.Completion) ↦
    f ((WithAbs.toAbs w.1 x : WithAbs w.1) : w.Completion)) hσ
  simp only [AlgEquiv.one_apply] at h
  rw [infiniteDecompositionToLocal_apply, infiniteDecomposition_smul_coe] at h
  have h' := UniformSpace.Completion.coe_injective (WithAbs w.1)
    (congrArg Completion.toCompletion h)
  rw [OneMemClass.coe_one, AlgEquiv.one_apply]
  exact congrArg WithAbs.ofAbs h'

variable [IsGalois K L]

theorem natCard_infiniteDecompositionGroup :
    Nat.card (MulAction.stabilizer Gal(L/K) w) = Module.finrank v.Completion w.Completion := by
  rw [NumberField.InfinitePlace.card_stabilizer]
  by_cases h : w.IsUnramified K
  · rw [if_pos h, h.finrank_eq_one v]
  · rw [if_neg h, NumberField.InfinitePlace.IsRamified.finrank_eq_two v h]

theorem infiniteDecompositionToLocal_bijective :
    Function.Bijective (infiniteDecompositionToLocal v w) := by
  refine (infiniteDecompositionToLocal_injective v w).bijective_of_nat_card_le ?_
  rw [natCard_infiniteDecompositionGroup v w, RHDirect.CFT_ProfiniteSemilocal.InfinitePlace.natCard_gal_completion w]

def infiniteDecompositionMulEquiv :
    MulAction.stabilizer Gal(L/K) w ≃* Gal(w.Completion/v.Completion) :=
  MulEquiv.ofBijective (infiniteDecompositionToLocal v w)
    (infiniteDecompositionToLocal_bijective v w)

@[simp]
theorem infiniteDecompositionMulEquiv_apply (σ : MulAction.stabilizer Gal(L/K) w)
    (x : w.Completion) : infiniteDecompositionMulEquiv v w σ x = σ • x :=
  rfl

end Local

section Herbrand

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (v : InfinitePlace K)
  (w : InfinitePlace L) [w.LiesOver v]

theorem ofMulDistribMulAction_gal_completion_units (σ : Gal(w.Completion/v.Completion))
    (x : Additive w.Completionˣ) :
    Representation.ofMulDistribMulAction Gal(w.Completion/v.Completion) w.Completionˣ σ x =
      RHDirect.CFT_ProfiniteSemilocal.InfinitePlace.unitsRep v w σ x := by
  apply Additive.toMul.injective
  apply Units.ext
  rfl

theorem cycHerbrand_gal_completion_units (σ : Gal(w.Completion/v.Completion))
    (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    HasHerbrandQuotient
        (cycSubOne (Representation.ofMulDistribMulAction Gal(w.Completion/v.Completion)
          w.Completionˣ) σ)
        (cycNorm (Representation.ofMulDistribMulAction Gal(w.Completion/v.Completion)
          w.Completionˣ)) ∧
      cycHerbrand (Representation.ofMulDistribMulAction Gal(w.Completion/v.Completion)
          w.Completionˣ) σ = Module.finrank v.Completion w.Completion := by
  have h1 := (cycHerbrand_eq_of_mulEquiv
    (ρ' := Representation.ofMulDistribMulAction Gal(w.Completion/v.Completion) w.Completionˣ)
    (ρ := RHDirect.CFT_ProfiniteSemilocal.InfinitePlace.unitsRep v w) (MulEquiv.refl _) (AddEquiv.refl _)
    (fun g x ↦ ofMulDistribMulAction_gal_completion_units v w g x) σ).2
  have h2 : cycHerbrand (RHDirect.CFT_ProfiniteSemilocal.InfinitePlace.unitsRep v w) σ = Module.finrank v.Completion w.Completion :=
    RHDirect.CFT_ProfiniteSemilocal.InfinitePlace.cyclicHerbrand_unitsRep_eq_finrank v w σ hσ
  have h3 : cycHerbrand (Representation.ofMulDistribMulAction Gal(w.Completion/v.Completion)
      w.Completionˣ) σ = Module.finrank v.Completion w.Completion := h1.trans h2
  refine ⟨hasHerbrandQuotient_of_cycHerbrand_ne_zero ?_, h3⟩
  rw [h3, Nat.cast_ne_zero]
  exact Module.finrank_pos.ne'

variable [IsGalois K L]

theorem ofMulDistribMulAction_infiniteDecomposition_units
    (σ : MulAction.stabilizer Gal(L/K) w) (x : Additive w.Completionˣ) :
    Representation.ofMulDistribMulAction (MulAction.stabilizer Gal(L/K) w) w.Completionˣ σ x =
      Representation.ofMulDistribMulAction Gal(w.Completion/v.Completion) w.Completionˣ
        (infiniteDecompositionMulEquiv v w σ) x := by
  apply Additive.toMul.injective
  apply Units.ext
  rfl

theorem cycHerbrand_infiniteCompletion_units [Fintype (MulAction.stabilizer Gal(L/K) w)]
    (τ : MulAction.stabilizer Gal(L/K) w) (hτ : ∀ σ, σ ∈ Subgroup.zpowers τ) :
    HasHerbrandQuotient
        (cycSubOne (Representation.ofMulDistribMulAction (MulAction.stabilizer Gal(L/K) w)
          w.Completionˣ) τ)
        (cycNorm (Representation.ofMulDistribMulAction (MulAction.stabilizer Gal(L/K) w)
          w.Completionˣ)) ∧
      cycHerbrand (Representation.ofMulDistribMulAction (MulAction.stabilizer Gal(L/K) w)
          w.Completionˣ) τ = Module.finrank v.Completion w.Completion := by
  obtain ⟨h1, h2⟩ := cycHerbrand_eq_of_mulEquiv
    (ρ' := Representation.ofMulDistribMulAction (MulAction.stabilizer Gal(L/K) w) w.Completionˣ)
    (ρ := Representation.ofMulDistribMulAction Gal(w.Completion/v.Completion) w.Completionˣ)
    (infiniteDecompositionMulEquiv v w) (AddEquiv.refl _)
    (fun σ x ↦ ofMulDistribMulAction_infiniteDecomposition_units v w σ x) τ
  obtain ⟨h3, h4⟩ := cycHerbrand_gal_completion_units v w _
    (mem_zpowers_mulEquiv (infiniteDecompositionMulEquiv v w) hτ)
  exact ⟨h1.2 h3, h2.trans h4⟩

end Herbrand

end Sec_17_IdeleGroups_LocalHerbrandInfinite

/-! ### 18_IdeleGroups.SIdeleHerbrand.Product -/
section Sec_18_IdeleGroups_SIdeleHerbrand_Product

open RHDirect.Stage13CFT_IdeleNormResidue


section KerModRangeProd

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]

def kerModRangeProdEquiv (F G : A × B →+ A × B) (fA gA : A →+ A) (fB gB : B →+ B)
    (hF : ∀ x, F x = (fA x.1, fB x.2)) (hG : ∀ x, G x = (gA x.1, gB x.2)) :
    KerModRange F G ≃+ KerModRange fA gA × KerModRange fB gB :=
  kerModRangeEquivOfSurjective
    (AddMonoidHom.prod
      ((QuotientAddGroup.mk' _).comp
        (((AddMonoidHom.fst A B).comp F.ker.subtype).codRestrict fA.ker fun x ↦
          AddMonoidHom.mem_ker.2 (congrArg Prod.fst ((hF x).symm.trans (AddMonoidHom.mem_ker.1 x.2)))))
      ((QuotientAddGroup.mk' _).comp
        (((AddMonoidHom.snd A B).comp F.ker.subtype).codRestrict fB.ker fun x ↦
          AddMonoidHom.mem_ker.2 (congrArg Prod.snd ((hF x).symm.trans (AddMonoidHom.mem_ker.1 x.2))))))
    (by
      rintro ⟨y₁, y₂⟩
      obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective y₁
      obtain ⟨b, rfl⟩ := QuotientAddGroup.mk_surjective y₂
      refine ⟨⟨((a : A), (b : B)), AddMonoidHom.mem_ker.2 ?_⟩, rfl⟩
      rw [hF, AddMonoidHom.mem_ker.1 a.2, AddMonoidHom.mem_ker.1 b.2, Prod.mk_zero_zero])
    (by
      intro x
      constructor
      · intro h
        have h1 : (x : A × B).1 ∈ gA.range :=
          (KerModRange.mk_eq_zero_iff (g := gA) _).1 (congrArg Prod.fst h)
        have h2 : (x : A × B).2 ∈ gB.range :=
          (KerModRange.mk_eq_zero_iff (g := gB) _).1 (congrArg Prod.snd h)
        obtain ⟨a, ha⟩ := AddMonoidHom.mem_range.1 h1
        obtain ⟨b, hb⟩ := AddMonoidHom.mem_range.1 h2
        exact AddMonoidHom.mem_range.2 ⟨(a, b), by rw [hG, ha, hb]⟩
      · intro h
        obtain ⟨y, hy⟩ := AddMonoidHom.mem_range.1 h
        rw [hG] at hy
        exact Prod.ext
          ((KerModRange.mk_eq_zero_iff (g := gA) _).2
            (AddMonoidHom.mem_range.2 ⟨y.1, congrArg Prod.fst hy⟩))
          ((KerModRange.mk_eq_zero_iff (g := gB) _).2
            (AddMonoidHom.mem_range.2 ⟨y.2, congrArg Prod.snd hy⟩)))

end KerModRangeProd

section Prod

variable {k G V W : Type*} [CommRing k] [Group G] [AddCommGroup V] [Module k V] [AddCommGroup W]
  [Module k W]

theorem cycSubOne_prod_apply (ρ : Representation k G V) (ρ' : Representation k G W) (σ : G)
    (x : V × W) : cycSubOne (ρ.prod ρ') σ x = (cycSubOne ρ σ x.1, cycSubOne ρ' σ x.2) := by
  rw [cycSubOne_apply, cycSubOne_apply, cycSubOne_apply]
  rfl

variable [Fintype G]

theorem cycNorm_prod_apply (ρ : Representation k G V) (ρ' : Representation k G W)
    (x : V × W) : cycNorm (ρ.prod ρ') x = (cycNorm ρ x.1, cycNorm ρ' x.2) := by
  rw [cycNorm_apply, cycNorm_apply, cycNorm_apply]
  exact Prod.ext (by rw [Prod.fst_sum]; rfl) (by rw [Prod.snd_sum]; rfl)

def cycTateZeroProdEquiv (ρ : Representation k G V) (ρ' : Representation k G W) (σ : G) :
    CycTateZero (ρ.prod ρ') σ ≃+ CycTateZero ρ σ × CycTateZero ρ' σ :=
  kerModRangeProdEquiv _ _ _ _ _ _ (cycSubOne_prod_apply ρ ρ' σ) (cycNorm_prod_apply ρ ρ')

def cycTateNegOneProdEquiv (ρ : Representation k G V) (ρ' : Representation k G W) (σ : G) :
    CycTateNegOne (ρ.prod ρ') σ ≃+ CycTateNegOne ρ σ × CycTateNegOne ρ' σ :=
  kerModRangeProdEquiv _ _ _ _ _ _ (cycNorm_prod_apply ρ ρ') (cycSubOne_prod_apply ρ ρ' σ)

theorem cycHerbrand_prod_eq_mul (ρ : Representation k G V) (ρ' : Representation k G W) (σ : G) :
    cycHerbrand (ρ.prod ρ') σ = cycHerbrand ρ σ * cycHerbrand ρ' σ := by
  simp only [cycHerbrand_eq]
  rw [Nat.card_congr (cycTateZeroProdEquiv ρ ρ' σ).toEquiv,
    Nat.card_congr (cycTateNegOneProdEquiv ρ ρ' σ).toEquiv, Nat.card_prod, Nat.card_prod,
    Nat.cast_mul, Nat.cast_mul, mul_div_mul_comm]

end Prod

section Mul

variable {G : Type*} [Group G]

def additiveProdEquiv (M N : Type*) [CommGroup M] [CommGroup N] :
    Additive (M × N) ≃+ Additive M × Additive N where
  toFun x := (Additive.ofMul x.toMul.1, Additive.ofMul x.toMul.2)
  invFun y := Additive.ofMul (y.1.toMul, y.2.toMul)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

def additivePiEquiv {ι : Type*} (M : ι → Type*) [∀ i, CommGroup (M i)] :
    Additive (∀ i, M i) ≃+ ∀ i, Additive (M i) where
  toFun x i := Additive.ofMul (x.toMul i)
  invFun y := Additive.ofMul fun i ↦ (y i).toMul
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

section Prod

variable (M N : Type*) [CommGroup M] [CommGroup N] [MulDistribMulAction G M]
  [MulDistribMulAction G N] [Fintype G]

def cycTateZeroMulProdEquiv (σ : G) :
    CycTateZero (Representation.ofMulDistribMulAction G (M × N)) σ ≃+
      CycTateZero (Representation.ofMulDistribMulAction G M) σ ×
        CycTateZero (Representation.ofMulDistribMulAction G N) σ :=
  (cycTateZeroCongr (ρ' := (Representation.ofMulDistribMulAction G M).prod
      (Representation.ofMulDistribMulAction G N)) (additiveProdEquiv M N) (fun _ _ ↦ rfl) σ).trans
    (cycTateZeroProdEquiv _ _ σ)

def cycTateNegOneMulProdEquiv (σ : G) :
    CycTateNegOne (Representation.ofMulDistribMulAction G (M × N)) σ ≃+
      CycTateNegOne (Representation.ofMulDistribMulAction G M) σ ×
        CycTateNegOne (Representation.ofMulDistribMulAction G N) σ :=
  (cycTateNegOneCongr (ρ' := (Representation.ofMulDistribMulAction G M).prod
      (Representation.ofMulDistribMulAction G N)) (additiveProdEquiv M N) (fun _ _ ↦ rfl) σ).trans
    (cycTateNegOneProdEquiv _ _ σ)

theorem cycHerbrand_mulProd (σ : G) :
    cycHerbrand (Representation.ofMulDistribMulAction G (M × N)) σ =
      cycHerbrand (Representation.ofMulDistribMulAction G M) σ *
        cycHerbrand (Representation.ofMulDistribMulAction G N) σ := by
  rw [cycHerbrand_congr (ρ' := (Representation.ofMulDistribMulAction G M).prod
      (Representation.ofMulDistribMulAction G N)) (additiveProdEquiv M N) (fun _ _ ↦ rfl) σ,
    cycHerbrand_prod_eq_mul]

end Prod

section Pi

variable {ι : Type*} (M : ι → Type*) [∀ i, CommGroup (M i)] [∀ i, MulDistribMulAction G (M i)]
  [Fintype G]

def cycTateZeroMulPiEquiv (σ : G) :
    CycTateZero (Representation.ofMulDistribMulAction G (∀ i, M i)) σ ≃+
      ∀ i, CycTateZero (Representation.ofMulDistribMulAction G (M i)) σ :=
  (cycTateZeroCongr (ρ' := piRep fun i ↦ Representation.ofMulDistribMulAction G (M i))
      (additivePiEquiv M) (fun _ _ ↦ rfl) σ).trans (cycTateZeroPiEquiv _ σ)

def cycTateNegOneMulPiEquiv (σ : G) :
    CycTateNegOne (Representation.ofMulDistribMulAction G (∀ i, M i)) σ ≃+
      ∀ i, CycTateNegOne (Representation.ofMulDistribMulAction G (M i)) σ :=
  (cycTateNegOneCongr (ρ' := piRep fun i ↦ Representation.ofMulDistribMulAction G (M i))
      (additivePiEquiv M) (fun _ _ ↦ rfl) σ).trans (cycTateNegOnePiEquiv _ σ)

theorem cycHerbrand_mulPi [Fintype ι] (σ : G) :
    cycHerbrand (Representation.ofMulDistribMulAction G (∀ i, M i)) σ =
      ∏ i, cycHerbrand (Representation.ofMulDistribMulAction G (M i)) σ := by
  rw [cycHerbrand_congr (ρ' := piRep fun i ↦ Representation.ofMulDistribMulAction G (M i))
      (additivePiEquiv M) (fun _ _ ↦ rfl) σ, cycHerbrand_pi]

end Pi

section Orbit

variable {X : Type*} {U : X → Type*} [∀ x, CommGroup (U x)] [MulDistribMulAction G (∀ x, U x)]

variable (G U) in

def mulPiRep : Representation ℤ G (∀ x, Additive (U x)) where
  toFun g := AddMonoidHom.toIntLinearMap ((additivePiEquiv U).toAddMonoidHom.comp
    ((Representation.ofMulDistribMulAction G (∀ x, U x) g).toAddMonoidHom.comp
      (additivePiEquiv U).symm.toAddMonoidHom))
  map_one' := LinearMap.ext fun y ↦ funext fun x ↦
    congrArg (fun f : ∀ x, U x ↦ Additive.ofMul (f x)) (one_smul G fun x ↦ (y x).toMul)
  map_mul' g h := LinearMap.ext fun y ↦ funext fun x ↦
    congrArg (fun f : ∀ x, U x ↦ Additive.ofMul (f x)) (mul_smul g h fun x ↦ (y x).toMul)

variable [MulAction G X]

theorem permutesFactors_mulPiRep
    (h : ∀ (g : G) (f : ∀ x, U x) (x : X), f x = 1 → (g • f) (g • x) = 1) :
    PermutesFactors (mulPiRep G U) := fun g f x hf ↦
  congrArg Additive.ofMul (h g (fun x ↦ (f x).toMul) x hf)

variable [Fintype G] [MulAction.IsPretransitive G X]

def cycTateZeroMulOrbitEquiv
    (hU : ∀ (g : G) (f : ∀ x, U x) (x : X), f x = 1 → (g • f) (g • x) = 1) (x₀ : X)
    (D : Subgroup G) [Fintype D] (hD : ∀ g, g ∈ D ↔ g • x₀ = x₀) [MulDistribMulAction D (U x₀)]
    (hU₀ : ∀ (d : D) (f : ∀ x, U x), ((d : G) • f) x₀ = d • f x₀) (σ : G)
    (hσ : ∀ g, g ∈ Subgroup.zpowers σ) (τ : D) (hτ : ∀ d, d ∈ Subgroup.zpowers τ) :
    CycTateZero (Representation.ofMulDistribMulAction G (∀ x, U x)) σ ≃+
      CycTateZero (Representation.ofMulDistribMulAction D (U x₀)) τ :=
  (cycTateZeroCongr (ρ' := mulPiRep G U) (additivePiEquiv U) (fun _ _ ↦ rfl) σ).trans
    (cycTateZeroOrbitEquiv (mulPiRep G U) (permutesFactors_mulPiRep hU) x₀ D hD
      (Representation.ofMulDistribMulAction D (U x₀))
      (fun d f ↦ congrArg Additive.ofMul (hU₀ d fun x ↦ (f x).toMul)) σ hσ τ hτ)

def cycTateNegOneMulOrbitEquiv
    (hU : ∀ (g : G) (f : ∀ x, U x) (x : X), f x = 1 → (g • f) (g • x) = 1) (x₀ : X)
    (D : Subgroup G) [Fintype D] (hD : ∀ g, g ∈ D ↔ g • x₀ = x₀) [MulDistribMulAction D (U x₀)]
    (hU₀ : ∀ (d : D) (f : ∀ x, U x), ((d : G) • f) x₀ = d • f x₀) (σ : G)
    (hσ : ∀ g, g ∈ Subgroup.zpowers σ) (τ : D) (hτ : ∀ d, d ∈ Subgroup.zpowers τ) :
    CycTateNegOne (Representation.ofMulDistribMulAction G (∀ x, U x)) σ ≃+
      CycTateNegOne (Representation.ofMulDistribMulAction D (U x₀)) τ :=
  (cycTateNegOneCongr (ρ' := mulPiRep G U) (additivePiEquiv U) (fun _ _ ↦ rfl) σ).trans
    (cycTateNegOneOrbitEquiv (mulPiRep G U) (permutesFactors_mulPiRep hU) x₀ D hD
      (Representation.ofMulDistribMulAction D (U x₀))
      (fun d f ↦ congrArg Additive.ofMul (hU₀ d fun x ↦ (f x).toMul)) σ hσ τ hτ)

theorem cycHerbrand_mulOrbit
    (hU : ∀ (g : G) (f : ∀ x, U x) (x : X), f x = 1 → (g • f) (g • x) = 1) (x₀ : X)
    (D : Subgroup G) [Fintype D] (hD : ∀ g, g ∈ D ↔ g • x₀ = x₀) [MulDistribMulAction D (U x₀)]
    (hU₀ : ∀ (d : D) (f : ∀ x, U x), ((d : G) • f) x₀ = d • f x₀) (σ : G)
    (hσ : ∀ g, g ∈ Subgroup.zpowers σ) (τ : D) (hτ : ∀ d, d ∈ Subgroup.zpowers τ) :
    cycHerbrand (Representation.ofMulDistribMulAction G (∀ x, U x)) σ =
      cycHerbrand (Representation.ofMulDistribMulAction D (U x₀)) τ := by
  rw [cycHerbrand_eq, cycHerbrand_eq,
    Nat.card_congr (cycTateZeroMulOrbitEquiv hU x₀ D hD hU₀ σ hσ τ hτ).toEquiv,
    Nat.card_congr (cycTateNegOneMulOrbitEquiv hU x₀ D hD hU₀ σ hσ τ hτ).toEquiv]

end Orbit

end Mul

end Sec_18_IdeleGroups_SIdeleHerbrand_Product

/-! ### 19_IdeleGroups.SIdeleHerbrand.Places -/
section Sec_19_IdeleGroups_SIdeleHerbrand_Places

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum RHDirect.Stage13CFT_IdeleNormResidue
  AdeleBaseChange SemiLocal

open scoped Pointwise NumberField.LiesOver


namespace IdeleGroup
open RHDirect.Stage13CFT_IdeleNormResidue.IdeleGroup

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

section Finite

variable (v : HeightOneSpectrum (𝓞 K))

omit [NumberField K] [NumberField L] in

theorem mem_stabilizer_iff_smul_placesOver (w : PlacesOver L v) (σ : Gal(L/K)) :
    σ ∈ MulAction.stabilizer Gal(L/K) w.1.asIdeal ↔ σ • w = w := by
  rw [MulAction.mem_stabilizer_iff, Subtype.ext_iff, coe_smul_placesOver,
    HeightOneSpectrum.ext_iff, smul_asIdeal]

theorem finiteUnitsAbove_smul_apply_of_eq (σ : Gal(L/K))
    (y : (w : PlacesOver L v) → (w.1.adicCompletion L)ˣ) (w w' : PlacesOver L v)
    (h : w' = σ • w) :
    (((σ • y) w' : (w'.1.adicCompletion L)ˣ) : w'.1.adicCompletion L) =
      galEquiv v σ w.1 w'.1 (by rw [h]; rfl) (y w) := by
  subst h
  exact finiteUnitsAbove_smul_apply v σ y w

omit [NumberField K] in

theorem galHom_eq_decomposition_smul (w : PlacesOver L v)
    (σ : MulAction.stabilizer Gal(L/K) w.1.asIdeal) (h : w.1 = (σ : Gal(L/K)) • w.1)
    (x : w.1.adicCompletion L) : galHom (σ : Gal(L/K)) w.1 w.1 h x = σ • x := by
  rw [decomposition_smul_def]
  exact congrFun (congrArg DFunLike.coe (ringHom_ext_adicCompletion w.1
    (continuous_galHom _ _ _ h) (continuous_adicCompletionRingHomOf _ _) fun y ↦ by
      rw [galHom_algebraMap, adicCompletionRingHomOf_algebraMap])) x

theorem finiteUnitsAbove_smul_apply_self (w : PlacesOver L v)
    (σ : MulAction.stabilizer Gal(L/K) w.1.asIdeal)
    (y : (w : PlacesOver L v) → (w.1.adicCompletion L)ˣ) : ((σ : Gal(L/K)) • y) w = σ • y w := by
  have hw : w = (σ : Gal(L/K)) • w :=
    ((mem_stabilizer_iff_smul_placesOver v w σ).1 σ.2).symm
  apply Units.ext
  rw [finiteUnitsAbove_smul_apply_of_eq v _ y w w hw, galEquiv_apply,
    galHom_eq_decomposition_smul]
  rfl

theorem finiteUnitsAbove_smul_apply_eq_one (σ : Gal(L/K))
    (y : (w : PlacesOver L v) → (w.1.adicCompletion L)ˣ) (w : PlacesOver L v) (hy : y w = 1) :
    (σ • y) (σ • w) = 1 :=
  Units.ext (by rw [finiteUnitsAbove_smul_apply, hy, Units.val_one, map_one, Units.val_one])

theorem integerUnitsAbove_smul_apply_self (w : PlacesOver L v)
    (σ : MulAction.stabilizer Gal(L/K) w.1.asIdeal)
    (z : (w : PlacesOver L v) → (w.1.adicCompletionIntegers L)ˣ) :
    ((σ : Gal(L/K)) • z) w = σ • z w := by
  apply Units.ext
  apply Subtype.ext
  rw [coe_decomposition_smul_integerUnits, ← coe_integerUnitsAboveIncl_apply,
    integerUnitsAboveIncl_smul, finiteUnitsAbove_smul_apply_self, coe_decomposition_smul_units,
    coe_integerUnitsAboveIncl_apply]

theorem integerUnitsAbove_smul_apply_eq_one (σ : Gal(L/K))
    (z : (w : PlacesOver L v) → (w.1.adicCompletionIntegers L)ˣ) (w : PlacesOver L v)
    (hz : z w = 1) : (σ • z) (σ • w) = 1 := by
  apply Units.ext
  apply Subtype.ext
  rw [integerUnitsAbove_smul_apply, hz, Units.val_one, OneMemClass.coe_one, map_one,
    Units.val_one, OneMemClass.coe_one]

variable [IsGalois K L] [Fintype Gal(L/K)]

open AdicLiesOver in

theorem cycHerbrand_finiteUnitsAbove (σ : Gal(L/K)) (hσ : ∀ g, g ∈ Subgroup.zpowers σ)
    (w : PlacesOver L v) :
    cycHerbrand (Representation.ofMulDistribMulAction Gal(L/K)
        ((u : PlacesOver L v) → (u.1.adicCompletion L)ˣ)) σ =
      Module.finrank (v.adicCompletion K) (w.1.adicCompletion L) := by
  have : IsCyclic Gal(L/K) := ⟨⟨σ, fun g ↦ Subgroup.mem_zpowers_iff.1 (hσ g)⟩⟩
  obtain ⟨τ, hτ⟩ := IsCyclic.exists_generator (α := MulAction.stabilizer Gal(L/K) w.1.asIdeal)
  let _ : Fintype (MulAction.stabilizer Gal(L/K) w.1.asIdeal) := Fintype.ofFinite _
  rw [cycHerbrand_mulOrbit (U := fun u : PlacesOver L v ↦ (u.1.adicCompletion L)ˣ)
    (finiteUnitsAbove_smul_apply_eq_one v) w _ (mem_stabilizer_iff_smul_placesOver v w)
    (finiteUnitsAbove_smul_apply_self v w) σ hσ τ hτ]
  exact (cycHerbrand_adicCompletion_units v w.1 τ hτ).2

theorem subsingleton_cycTateZero_integerUnitsAbove (σ : Gal(L/K))
    (hσ : ∀ g, g ∈ Subgroup.zpowers σ) (w : PlacesOver L v)
    (he : w.1.asIdeal.ramificationIdx (𝓞 K) = 1) :
    Subsingleton (CycTateZero (Representation.ofMulDistribMulAction Gal(L/K)
      ((u : PlacesOver L v) → (u.1.adicCompletionIntegers L)ˣ)) σ) := by
  have : IsCyclic Gal(L/K) := ⟨⟨σ, fun g ↦ Subgroup.mem_zpowers_iff.1 (hσ g)⟩⟩
  obtain ⟨τ, hτ⟩ := IsCyclic.exists_generator (α := MulAction.stabilizer Gal(L/K) w.1.asIdeal)
  let _ : Fintype (MulAction.stabilizer Gal(L/K) w.1.asIdeal) := Fintype.ofFinite _
  have := subsingleton_cycTateZero_adicCompletionIntegers_units v w.1 he τ hτ
  exact (cycTateZeroMulOrbitEquiv (U := fun u : PlacesOver L v ↦ (u.1.adicCompletionIntegers L)ˣ)
    (integerUnitsAbove_smul_apply_eq_one v) w _ (mem_stabilizer_iff_smul_placesOver v w)
    (integerUnitsAbove_smul_apply_self v w) σ hσ τ hτ).toEquiv.subsingleton

theorem subsingleton_cycTateNegOne_integerUnitsAbove (σ : Gal(L/K))
    (hσ : ∀ g, g ∈ Subgroup.zpowers σ) (w : PlacesOver L v)
    (he : w.1.asIdeal.ramificationIdx (𝓞 K) = 1) :
    Subsingleton (CycTateNegOne (Representation.ofMulDistribMulAction Gal(L/K)
      ((u : PlacesOver L v) → (u.1.adicCompletionIntegers L)ˣ)) σ) := by
  have : IsCyclic Gal(L/K) := ⟨⟨σ, fun g ↦ Subgroup.mem_zpowers_iff.1 (hσ g)⟩⟩
  obtain ⟨τ, hτ⟩ := IsCyclic.exists_generator (α := MulAction.stabilizer Gal(L/K) w.1.asIdeal)
  let _ : Fintype (MulAction.stabilizer Gal(L/K) w.1.asIdeal) := Fintype.ofFinite _
  have := subsingleton_cycTateNegOne_adicCompletionIntegers_units v w.1 he τ hτ
  exact (cycTateNegOneMulOrbitEquiv
    (U := fun u : PlacesOver L v ↦ (u.1.adicCompletionIntegers L)ˣ)
    (integerUnitsAbove_smul_apply_eq_one v) w _ (mem_stabilizer_iff_smul_placesOver v w)
    (integerUnitsAbove_smul_apply_self v w) σ hσ τ hτ).toEquiv.subsingleton

end Finite

section Infinite

def infiniteCompletionCongr {u u' : InfinitePlace L} (h : u = u') :
    u.Completion ≃+* u'.Completion :=
  h ▸ RingEquiv.refl _

omit [NumberField L] in
theorem continuous_infiniteCompletionCongr {u u' : InfinitePlace L} (h : u = u') :
    Continuous (infiniteCompletionCongr h) := by
  subst h
  exact continuous_id

omit [NumberField L] in
theorem infiniteCompletionCongr_algebraMap {u u' : InfinitePlace L} (h : u = u') (x : L) :
    infiniteCompletionCongr h (algebraMap L u.Completion x) = algebraMap L u'.Completion x := by
  subst h
  rfl

theorem continuous_infiniteCompletionMap {M M' : Type*} [Field M] [NumberField M] [Field M']
    [NumberField M'] (τ : M ≃+* M') (w' : InfinitePlace M') :
    Continuous (infiniteCompletionMap τ w') := by
  let _ : Algebra M M' := (τ : M →+* M').toAlgebra
  exact NumberField.LiesOver.continuous_completionMap

variable (v : InfinitePlace K)

theorem infiniteUnitsAbove_smul_apply_of_eq (σ : Gal(L/K))
    (y : (w : v.placesOver L) → (w.1.Completion)ˣ) (u w : v.placesOver L)
    (h : u.1 = w.1.comap ((σ : L ≃+* L) : L →+* L)) :
    (((σ • y) w : (w.1.Completion)ˣ) : w.1.Completion) =
      infiniteCompletionMap (σ : L ≃+* L) w.1 (infiniteCompletionCongr h (y u)) := by
  obtain rfl : u = ⟨w.1.comap ((σ : L ≃+* L) : L →+* L), comap_mem_placesOver v σ w⟩ :=
    Subtype.ext h
  exact infiniteUnitsAbove_smul_apply v σ y w

omit [NumberField K] [NumberField L] in
theorem eq_comap_smul_placesOver (σ : Gal(L/K)) (w : v.placesOver L) :
    w.1 = (σ • w).1.comap ((σ : L ≃+* L) : L →+* L) := by
  rw [comap_eq_inv_smul, RHDirect.CFT_ProfiniteSemilocal.InfinitePlace.coe_smul_placesOver, inv_smul_smul]

theorem infiniteUnitsAbove_smul_apply_eq_one (σ : Gal(L/K))
    (y : (w : v.placesOver L) → (w.1.Completion)ˣ) (w : v.placesOver L) (hy : y w = 1) :
    (σ • y) (σ • w) = 1 := by
  apply Units.ext
  rw [infiniteUnitsAbove_smul_apply_of_eq v σ y w (σ • w) (eq_comap_smul_placesOver v σ w), hy,
    Units.val_one, map_one, map_one, Units.val_one]

omit [NumberField K] [NumberField L] in

theorem mem_stabilizer_iff_smul_placesOver_infinite (w : v.placesOver L) (σ : Gal(L/K)) :
    σ ∈ MulAction.stabilizer Gal(L/K) w.1 ↔ σ • w = w := by
  rw [MulAction.mem_stabilizer_iff, Subtype.ext_iff, RHDirect.CFT_ProfiniteSemilocal.InfinitePlace.coe_smul_placesOver]

omit [NumberField K] in

theorem infiniteCompletionMap_eq_decomposition_smul (w : v.placesOver L)
    (σ : MulAction.stabilizer Gal(L/K) w.1)
    (h : w.1 = w.1.comap (((σ : Gal(L/K)) : L ≃+* L) : L →+* L)) (x : w.1.Completion) :
    infiniteCompletionMap ((σ : Gal(L/K)) : L ≃+* L) w.1 (infiniteCompletionCongr h x) =
      σ • x := by
  rw [infiniteDecomposition_smul_def]
  have := ringHom_ext_completion w.1
    (f := (infiniteCompletionMap ((σ : Gal(L/K)) : L ≃+* L) w.1).comp
      (infiniteCompletionCongr h).toRingHom)
    ((continuous_infiniteCompletionMap _ _).comp (continuous_infiniteCompletionCongr h))
    (continuous_completionRingHomOf σ.2) fun y ↦ by
      rw [completionRingHomOf_coe]
      change infiniteCompletionMap _ w.1
          (infiniteCompletionCongr h (algebraMap L w.1.Completion y.ofAbs)) =
        algebraMap L w.1.Completion (withAbsMapOf w.1 (σ : Gal(L/K)) y).ofAbs
      rw [infiniteCompletionCongr_algebraMap, infiniteCompletionMap_algebraMap,
        ofAbs_withAbsMapOf]
      rfl
  exact congrFun (congrArg DFunLike.coe this) x

theorem infiniteUnitsAbove_smul_apply_self (w : v.placesOver L)
    (σ : MulAction.stabilizer Gal(L/K) w.1) (y : (w : v.placesOver L) → (w.1.Completion)ˣ) :
    ((σ : Gal(L/K)) • y) w = σ • y w := by
  have hw : w = (σ : Gal(L/K)) • w :=
    ((mem_stabilizer_iff_smul_placesOver_infinite v w σ).1 σ.2).symm
  have h : w.1 = w.1.comap (((σ : Gal(L/K)) : L ≃+* L) : L →+* L) := by
    have h' := eq_comap_smul_placesOver v (σ : Gal(L/K)) w
    rwa [← hw] at h'
  apply Units.ext
  rw [infiniteUnitsAbove_smul_apply_of_eq v (σ : Gal(L/K)) y w w h,
    infiniteCompletionMap_eq_decomposition_smul]
  rfl

variable [IsGalois K L] [Fintype Gal(L/K)]

theorem cycHerbrand_infiniteUnitsAbove (σ : Gal(L/K)) (hσ : ∀ g, g ∈ Subgroup.zpowers σ)
    (w : v.placesOver L) :
    cycHerbrand (Representation.ofMulDistribMulAction Gal(L/K)
        ((u : v.placesOver L) → (u.1.Completion)ˣ)) σ =
      Module.finrank v.Completion w.1.Completion := by
  have : IsCyclic Gal(L/K) := ⟨⟨σ, fun g ↦ Subgroup.mem_zpowers_iff.1 (hσ g)⟩⟩
  obtain ⟨τ, hτ⟩ := IsCyclic.exists_generator (α := MulAction.stabilizer Gal(L/K) w.1)
  let _ : Fintype (MulAction.stabilizer Gal(L/K) w.1) := Fintype.ofFinite _
  rw [cycHerbrand_mulOrbit (U := fun u : v.placesOver L ↦ (u.1.Completion)ˣ)
    (infiniteUnitsAbove_smul_apply_eq_one v) w _ (mem_stabilizer_iff_smul_placesOver_infinite v w)
    (infiniteUnitsAbove_smul_apply_self v w) σ hσ τ hτ]
  exact (cycHerbrand_infiniteCompletion_units v w.1 τ hτ).2

end Infinite

end IdeleGroup

end Sec_19_IdeleGroups_SIdeleHerbrand_Places

/-! ### 20_IdeleGroups.SIdeleHerbrand -/
section Sec_20_IdeleGroups_SIdeleHerbrand

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum RHDirect.Stage13CFT_IdeleNormResidue

open scoped NumberField.LiesOver

open RHDirect.Stage13CFT_IdeleNormResidue.SemiLocal (PlacesOver)


namespace IdeleGroup
open RHDirect.Stage13CFT_IdeleNormResidue.IdeleGroup

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

open SemiLocal in

theorem nonempty_placesOver_of_finite (v : HeightOneSpectrum (𝓞 K)) :
    Nonempty (PlacesOver L v) := by
  by_contra h
  rw [not_nonempty_iff] at h
  have := sum_finrank_eq L v
  rw [Finset.univ_eq_empty, Finset.sum_empty] at this
  exact (Module.finrank_pos (R := K) (M := L)).ne this

variable [IsGalois K L] [Fintype Gal(L/K)]

theorem subsingleton_cycTateZero_integerUnitsOutside (S : Set (HeightOneSpectrum (𝓞 K)))
    (hS : ∀ v ∉ S, ∀ w : PlacesOver L v, w.1.asIdeal.ramificationIdx (𝓞 K) = 1)
    (σ : Gal(L/K)) (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    Subsingleton (CycTateZero (Representation.ofMulDistribMulAction Gal(L/K)
      ((v : ↥Sᶜ) → (w : PlacesOver L v.1) → (w.1.adicCompletionIntegers L)ˣ)) σ) := by
  have h : ∀ v : ↥Sᶜ, Subsingleton (CycTateZero (Representation.ofMulDistribMulAction Gal(L/K)
      ((w : PlacesOver L v.1) → (w.1.adicCompletionIntegers L)ˣ)) σ) := fun v ↦ by
    obtain ⟨w⟩ := nonempty_placesOver_of_finite (L := L) v.1
    exact subsingleton_cycTateZero_integerUnitsAbove v.1 σ hσ w (hS v.1 v.2 w)
  exact (cycTateZeroMulPiEquiv
    (fun v : ↥Sᶜ ↦ (w : PlacesOver L v.1) → (w.1.adicCompletionIntegers L)ˣ) σ).toEquiv.subsingleton

theorem subsingleton_cycTateNegOne_integerUnitsOutside (S : Set (HeightOneSpectrum (𝓞 K)))
    (hS : ∀ v ∉ S, ∀ w : PlacesOver L v, w.1.asIdeal.ramificationIdx (𝓞 K) = 1)
    (σ : Gal(L/K)) (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    Subsingleton (CycTateNegOne (Representation.ofMulDistribMulAction Gal(L/K)
      ((v : ↥Sᶜ) → (w : PlacesOver L v.1) → (w.1.adicCompletionIntegers L)ˣ)) σ) := by
  have h : ∀ v : ↥Sᶜ, Subsingleton (CycTateNegOne (Representation.ofMulDistribMulAction Gal(L/K)
      ((w : PlacesOver L v.1) → (w.1.adicCompletionIntegers L)ˣ)) σ) := fun v ↦ by
    obtain ⟨w⟩ := nonempty_placesOver_of_finite (L := L) v.1
    exact subsingleton_cycTateNegOne_integerUnitsAbove v.1 σ hσ w (hS v.1 v.2 w)
  exact (cycTateNegOneMulPiEquiv
    (fun v : ↥Sᶜ ↦ (w : PlacesOver L v.1) → (w.1.adicCompletionIntegers L)ˣ) σ).toEquiv.subsingleton

theorem cycHerbrand_integerUnitsOutside (S : Set (HeightOneSpectrum (𝓞 K)))
    (hS : ∀ v ∉ S, ∀ w : PlacesOver L v, w.1.asIdeal.ramificationIdx (𝓞 K) = 1)
    (σ : Gal(L/K)) (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    cycHerbrand (Representation.ofMulDistribMulAction Gal(L/K)
      ((v : ↥Sᶜ) → (w : PlacesOver L v.1) → (w.1.adicCompletionIntegers L)ˣ)) σ = 1 := by
  have h0 := subsingleton_cycTateZero_integerUnitsOutside S hS σ hσ
  have h1 := subsingleton_cycTateNegOne_integerUnitsOutside S hS σ hσ
  rw [cycHerbrand_eq, Nat.card_eq_one_iff_unique.2 ⟨h0, ⟨0⟩⟩,
    Nat.card_eq_one_iff_unique.2 ⟨h1, ⟨0⟩⟩]
  norm_num

open AdicLiesOver in

theorem cycHerbrand_sIdeles (S : Set (HeightOneSpectrum (𝓞 K))) (hSf : S.Finite)
    (hS : ∀ v ∉ S, ∀ w : PlacesOver L v, w.1.asIdeal.ramificationIdx (𝓞 K) = 1)
    (σ : Gal(L/K)) (hσ : ∀ g, g ∈ Subgroup.zpowers σ)
    (wInf : ∀ v : InfinitePlace K, v.placesOver L) (wFin : ∀ v : HeightOneSpectrum (𝓞 K), PlacesOver L v) :
    HasHerbrandQuotient
        (cycSubOne (Representation.ofMulDistribMulAction Gal(L/K) (sIdeles (placesAbove L S))) σ)
        (cycNorm (Representation.ofMulDistribMulAction Gal(L/K) (sIdeles (placesAbove L S)))) ∧
      cycHerbrand (Representation.ofMulDistribMulAction Gal(L/K) (sIdeles (placesAbove L S))) σ =
        (∏ v : InfinitePlace K, (Module.finrank v.Completion (wInf v).1.Completion : ℚ)) *
          ∏ v ∈ hSf.toFinset,
            (Module.finrank (v.adicCompletion K) ((wFin v).1.adicCompletion L) : ℚ) := by
  let _ : Fintype S := hSf.fintype
  have key : cycHerbrand (Representation.ofMulDistribMulAction Gal(L/K)
      (sIdeles (placesAbove L S))) σ =
        (∏ v : InfinitePlace K, (Module.finrank v.Completion (wInf v).1.Completion : ℚ)) *
          ∏ v ∈ hSf.toFinset,
            (Module.finrank (v.adicCompletion K) ((wFin v).1.adicCompletion L) : ℚ) := by
    have hcompat : ∀ (g : Gal(L/K)) (x : Additive (sIdeles (placesAbove L S))),
        (sIdelesEquivProduct S hSf).toAdditive
            (Representation.ofMulDistribMulAction Gal(L/K) (sIdeles (placesAbove L S)) g x) =
          Representation.ofMulDistribMulAction Gal(L/K) (SIdelesProduct L S) g
            ((sIdelesEquivProduct S hSf).toAdditive x) := fun g x ↦ by
      apply Additive.toMul.injective
      exact sIdelesEquivProduct_smul S hSf g x.toMul
    rw [cycHerbrand_congr (sIdelesEquivProduct S hSf).toAdditive hcompat σ]
    rw [cycHerbrand_mulProd, cycHerbrand_mulProd, cycHerbrand_integerUnitsOutside S hS σ hσ,
      mul_one, cycHerbrand_mulPi, cycHerbrand_mulPi,
      Finset.prod_subtype hSf.toFinset (fun v ↦ hSf.mem_toFinset)]
    congr 1
    · exact Finset.prod_congr rfl fun v _ ↦ cycHerbrand_infiniteUnitsAbove v σ hσ (wInf v)
    · exact Finset.prod_congr rfl fun v _ ↦ cycHerbrand_finiteUnitsAbove v.1 σ hσ (wFin v.1)
  refine ⟨hasHerbrandQuotient_of_cycHerbrand_ne_zero ?_, key⟩
  rw [key]
  refine mul_ne_zero (Finset.prod_ne_zero_iff.2 fun v _ ↦ ?_)
    (Finset.prod_ne_zero_iff.2 fun v _ ↦ ?_)
  · exact Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  · exact Nat.cast_ne_zero.2 Module.finrank_pos.ne'

end IdeleGroup

end Sec_20_IdeleGroups_SIdeleHerbrand

/-! ### 21_FirstInequalityStatement -/
section Sec_21_FirstInequalityStatement

open NumberField

def FirstInequality.{u} : Prop :=
  ∀ (K L : Type u) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)],
    (Module.finrank K L : ℕ∞) ≤ ENat.card (IdeleClassGroup K ⧸ (ideleClassNorm K L).range)

section

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem ideleClassNorm_range_eq_top_iff :
    (ideleClassNorm K L).range = ⊤ ↔
      (ideleNorm K L).range ⊔ (IdeleGroup.diagonal K).range = ⊤ := by
  constructor
  · intro h
    rw [eq_top_iff]
    intro x _
    obtain ⟨c, hc⟩ := (MonoidHom.mem_range).1 (h ▸ Subgroup.mem_top (IdeleClassGroup.mk K x))
    obtain ⟨y, rfl⟩ := IdeleClassGroup.mk_surjective L c
    rw [ideleClassNorm_mk] at hc
    have hd : (ideleNorm K L y)⁻¹ * x ∈ (IdeleGroup.diagonal K).range :=
      QuotientGroup.eq.1 hc
    have : x = ideleNorm K L y * ((ideleNorm K L y)⁻¹ * x) := by group
    rw [this]
    exact Subgroup.mul_mem_sup ⟨y, rfl⟩ hd
  · intro h
    rw [eq_top_iff]
    intro c _
    obtain ⟨x, rfl⟩ := IdeleClassGroup.mk_surjective K c
    obtain ⟨_, ⟨y, rfl⟩, z, hz, hyz⟩ := Subgroup.mem_sup.1 (h ▸ Subgroup.mem_top x)
    refine ⟨IdeleClassGroup.mk L y, ?_⟩
    rw [ideleClassNorm_mk, ← hyz]
    refine QuotientGroup.eq.2 ?_
    simpa using hz

end

section

universe u

variable {K L : Type u} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)]

theorem FirstInequality.finrank_eq_one_of_range_eq_top (hFI : FirstInequality.{u})
    (h : (ideleClassNorm K L).range = ⊤) : Module.finrank K L = 1 := by
  have hle := hFI K L
  rw [h] at hle
  have := QuotientGroup.subsingleton_quotient_top (G := IdeleClassGroup K)
  have h1 : ENat.card (IdeleClassGroup K ⧸ (⊤ : Subgroup (IdeleClassGroup K))) ≤ 1 :=
    (ENat.card_le_one_iff_subsingleton _).2 inferInstance
  have h2 : (Module.finrank K L : ℕ∞) ≤ 1 := hle.trans h1
  have hpos : 0 < Module.finrank K L := Module.finrank_pos
  have h3 : Module.finrank K L ≤ 1 := by exact_mod_cast h2
  omega

theorem FirstInequality.finrank_eq_one_of_sup_eq_top (hFI : FirstInequality.{u})
    (h : (ideleNorm K L).range ⊔ (IdeleGroup.diagonal K).range = ⊤) :
    Module.finrank K L = 1 :=
  hFI.finrank_eq_one_of_range_eq_top (ideleClassNorm_range_eq_top_iff.2 h)

end

end Sec_21_FirstInequalityStatement

/-! ### 22_FirstInequality.HerbrandClass -/
section Sec_22_FirstInequality_HerbrandClass

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum RHDirect.Stage13CFT_IdeleNormResidue Module

open scoped NumberField.LiesOver

open RHDirect.Stage13CFT_IdeleNormResidue.SemiLocal (PlacesOver)


section Equivariant

variable {G A B : Type*} [Group G] [AddCommGroup A] [AddCommGroup B]

theorem map_cycSubOne {ρA : Representation ℤ G A} {ρB : Representation ℤ G B} {f : A →+ B}
    (hf : ∀ g a, f (ρA g a) = ρB g (f a)) (σ : G) (a : A) :
    f (cycSubOne ρA σ a) = cycSubOne ρB σ (f a) := by
  rw [cycSubOne_apply, cycSubOne_apply, map_sub, hf]

theorem map_cycNorm [Fintype G] {ρA : Representation ℤ G A} {ρB : Representation ℤ G B}
    {f : A →+ B} (hf : ∀ g a, f (ρA g a) = ρB g (f a)) (a : A) :
    f (cycNorm ρA a) = cycNorm ρB (f a) := by
  rw [cycNorm_apply, cycNorm_apply, map_sum]
  simp only [hf]

end Equivariant

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

namespace IdeleGroup
open RHDirect.Stage13CFT_IdeleNormResidue.IdeleGroup

omit [NumberField K] [NumberField L] in
open scoped Classical in

theorem finrank_infiniteCompletion_eq_ite [IsGalois K L] (v : InfinitePlace K)
    (w : InfinitePlace L) [w.LiesOver v] :
    (finrank v.Completion w.Completion : ℚ) = if v.IsUnramifiedIn L then 1 else 2 := by
  have hv : w.comap (algebraMap K L) = v := NumberField.InfinitePlace.LiesOver.comap_eq w v
  have hiff : v.IsUnramifiedIn L ↔ w.IsUnramified K := by
    rw [← hv]
    exact NumberField.InfinitePlace.isUnramifiedIn_comap
  rcases w.isUnramified_or_isRamified K with h | h
  · rw [if_pos (hiff.2 h), h.finrank_eq_one v, Nat.cast_one]
  · have hn : ¬ v.IsUnramifiedIn L := fun h' ↦ by
      have := hiff.1 h'
      rw [NumberField.InfinitePlace.IsRamified] at h
      exact h this
    rw [if_neg hn, h.finrank_eq_two v, Nat.cast_ofNat]

open AdicLiesOver in

theorem finrank_adicCompletion_eq_ramificationIdxIn_mul [IsGalois K L]
    (v : HeightOneSpectrum (𝓞 K)) (w : PlacesOver L v) :
    finrank (v.adicCompletion K) (w.1.adicCompletion L) =
      v.asIdeal.ramificationIdxIn (𝓞 L) * v.asIdeal.inertiaDegIn (𝓞 L) := by
  rw [finrank_adicCompletion v w.1,
    Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal w.1.asIdeal Gal(L/K),
    Ideal.inertiaDegIn_eq_inertiaDeg v.asIdeal w.1.asIdeal Gal(L/K)]

end IdeleGroup

namespace IdeleGroup
open RHDirect.Stage13CFT_IdeleNormResidue.IdeleGroup

open AdeleBaseChange in

theorem exists_finset_unramified_sup_sIdeles_eq_top :
    ∃ S : Finset (HeightOneSpectrum (𝓞 K)),
      (∀ v ∉ (S : Set (HeightOneSpectrum (𝓞 K))), ∀ w : PlacesOver L v,
        w.1.asIdeal.ramificationIdx (𝓞 K) = 1) ∧
      (diagonal L).range ⊔ sIdeles (placesAbove L (S : Set (HeightOneSpectrum (𝓞 K)))) = ⊤ := by
  classical
  have hfin := Filter.eventually_cofinite.1 (IdeleNorm.eventually_ramificationIdx_eq_one K L)
  obtain ⟨S, hS₀, htop⟩ := exists_finset_superset_sup_sIdeles_placesAbove_eq_top (L := L)
    (hfin.toFinset.image (below K))
  refine ⟨S, fun v hv w ↦ ?_, htop⟩
  by_contra h
  apply hv
  apply hS₀
  rw [Finset.mem_image]
  exact ⟨w.1, hfin.mem_toFinset.2 h, (below_eq_iff w.1 v).2 inferInstance⟩

variable [IsGalois K L]

open AdeleBaseChange AdicLiesOver in

theorem cycHerbrand_ideleClassGroup (σ : Gal(L/K)) (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    HasHerbrandQuotient
        (cycSubOne (Representation.ofMulDistribMulAction Gal(L/K) (IdeleClassGroup L)) σ)
        (cycNorm (Representation.ofMulDistribMulAction Gal(L/K) (IdeleClassGroup L))) ∧
      cycHerbrand (Representation.ofMulDistribMulAction Gal(L/K) (IdeleClassGroup L)) σ =
        finrank K L := by
  classical
  obtain ⟨S, hram, htop⟩ := exists_finset_unramified_sup_sIdeles_eq_top (K := K) (L := L)
  set T := placesAbove L (S : Set (HeightOneSpectrum (𝓞 K))) with hTdef
  have hT : ∀ (g : L ≃ₐ[K] L), ∀ w ∈ T, g • w ∈ T := fun g w hw ↦
    (smul_mem_placesAbove_iff _ g w).2 hw
  have : Finite T := (placesAbove_finite S.finite_toSet).to_subtype
  set ρA := sUnitRep T hT
  set ρB := Representation.ofMulDistribMulAction Gal(L/K) (sIdeles T)
  set ρC := Representation.ofMulDistribMulAction Gal(L/K) (IdeleClassGroup L)
  obtain ⟨hinj, hrange, hsurj⟩ :=
    sUnits_sIdeles_placesAbove_exact (L := L) (S : Set (HeightOneSpectrum (𝓞 K))) htop
  let i : Additive (T.unit L) →+ Additive (sIdeles T) := (sUnitsToSIdeles T).toAdditive
  let p : Additive (sIdeles T) →+ Additive (IdeleClassGroup L) :=
    (sIdelesToIdeleClassGroup T).toAdditive
  have hi : Function.Injective i := fun a b h ↦ hinj h
  have hp : Function.Surjective p := hsurj
  have hex : Function.Exact i p := by
    intro b
    have := SetLike.ext_iff.1 hrange b.toMul
    rw [MonoidHom.mem_ker, MonoidHom.mem_range] at this
    exact this.symm
  have hiG : ∀ g a, i (ρA g a) = ρB g (i a) := fun g a ↦ by
    apply Additive.toMul.injective
    apply Subtype.ext
    change diagonal L ((sUnitMap T hT g a.toMul : T.unit L) : Lˣ) =
      g • diagonal L ((a.toMul : T.unit L) : Lˣ)
    rw [smul_diagonal]
    exact congrArg (diagonal L) (Units.ext rfl)
  have hpG : ∀ g b, p (ρB g b) = ρC g (p b) := fun g b ↦
    sIdelesToIdeleClassGroup_smul (S : Set (HeightOneSpectrum (𝓞 K))) g b.toMul
  have hA := hasHerbrandQuotient_sUnitRep (K := K) T hT hσ
  have hiS := map_cycSubOne hiG σ
  have hiN := map_cycNorm hiG
  have hpS : ∀ b, p (cycSubOne ρB σ b) = cycSubOne ρC σ (p b) := fun b ↦ by
    rw [cycSubOne_apply, cycSubOne_apply, map_sub, hpG]
  have hpN : ∀ b, p (cycNorm ρB b) = cycNorm ρC (p b) := fun b ↦ by
    rw [cycNorm_apply, cycNorm_apply, map_sum]
    simp only [hpG]
  obtain ⟨wFin⟩ : Nonempty (∀ v : HeightOneSpectrum (𝓞 K), PlacesOver L v) :=
    ⟨fun v ↦ (nonempty_placesOver_of_finite (L := L) v).some⟩
  obtain ⟨wInf⟩ : Nonempty (∀ v : InfinitePlace K, v.placesOver L) :=
    ⟨fun v ↦ ⟨(InfinitePlace.comap_surjective (K := L) v).choose,
      (RHDirect.CFT_ProfiniteSemilocal.InfinitePlace.liesOver_iff_comap_eq v _).2
        (InfinitePlace.comap_surjective (K := L) v).choose_spec⟩⟩
  obtain ⟨hB, hBval⟩ :=
    cycHerbrand_sIdeles (S : Set (HeightOneSpectrum (𝓞 K))) S.finite_toSet hram σ hσ wInf wFin
  have hC := HasHerbrandQuotient.of_shortExact_left_mid (C := Additive (IdeleClassGroup L)) (p := p) hi hp hex hiS hiN hpS hpN (cycSubOne_cycNorm ρB σ)
    (cycNorm_cycSubOne ρB σ) hA hB
  refine ⟨hC, ?_⟩
  have hmul : cycHerbrand ρB σ = cycHerbrand ρA σ * cycHerbrand ρC σ :=
    herbrandQuotient_eq_mul_of_shortExact (C := Additive (IdeleClassGroup L)) (p := p) hi hp hex hiS hiN hpS hpN (cycSubOne_cycNorm ρB σ)
      (cycNorm_cycSubOne ρB σ) hA hC
  have hInf : ∏ v : InfinitePlace K, (finrank v.Completion (wInf v).1.Completion : ℚ) =
      ∏ v : InfinitePlace K, (if v.IsUnramifiedIn L then 1 else 2 : ℚ) :=
    Finset.prod_congr rfl fun v _ ↦ by
      exact finrank_infiniteCompletion_eq_ite v (wInf v).1
  have hFin : (∏ᶠ (v : HeightOneSpectrum (𝓞 K)) (_ : ∃ w ∈ T, w.asIdeal.LiesOver v.asIdeal),
        ((v.asIdeal.ramificationIdxIn (𝓞 L) * v.asIdeal.inertiaDegIn (𝓞 L) : ℕ) : ℚ)) =
      ∏ v ∈ S.finite_toSet.toFinset,
        (finrank (v.adicCompletion K) ((wFin v).1.adicCompletion L) : ℚ) := by
    rw [Finset.finite_toSet_toFinset]
    rw [finprod_cond_eq_prod_of_cond_iff _ (t := S) fun {v} _ ↦ ?_]
    · exact Finset.prod_congr rfl fun v _ ↦ by
        rw [finrank_adicCompletion_eq_ramificationIdxIn_mul v (wFin v)]
    · constructor
      · rintro ⟨w, hw, hlies⟩
        have := (below_eq_iff w v).2 hlies
        rw [← this]
        exact hw
      · intro hv
        refine ⟨(wFin v).1, ?_, inferInstance⟩
        rw [hTdef, mem_placesAbove, (below_eq_iff (wFin v).1 v).2 inferInstance]
        exact hv
  rw [hBval, cycHerbrand_sUnitRep T hT hσ, hFin, hInf] at hmul
  have hI : (∏ v : InfinitePlace K, (if v.IsUnramifiedIn L then 1 else 2 : ℚ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun v _ ↦ by split_ifs <;> norm_num
  have hP : (∏ v ∈ S.finite_toSet.toFinset,
      (finrank (v.adicCompletion K) ((wFin v).1.adicCompletion L) : ℚ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun v _ ↦ Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  have hn : (finrank K L : ℚ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  field_simp at hmul
  exact hmul.symm

end IdeleGroup

end Sec_22_FirstInequality_HerbrandClass

/-! ### 23_FirstInequality -/
section Sec_23_FirstInequality

open NumberField RHDirect.Stage13CFT_IdeleNormResidue Module


variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

variable (K L) in

def ideleClassToCycTateZero (σ : Gal(L/K)) :
    Additive (IdeleClassGroup K) →+
      CycTateZero (Representation.ofMulDistribMulAction Gal(L/K) (IdeleClassGroup L)) σ :=
  (QuotientAddGroup.mk' _).comp ((ideleClassMap K L).toAdditive.codRestrict _ fun c ↦ by
    rw [AddMonoidHom.mem_ker, cycSubOne_apply, Representation.ofMulDistribMulAction_apply_apply,
      sub_eq_zero]
    exact congrArg Additive.ofMul (smul_ideleClassMap σ _))

theorem ideleClassToCycTateZero_apply (σ : Gal(L/K)) (c : Additive (IdeleClassGroup K)) :
    ideleClassToCycTateZero K L σ c = QuotientAddGroup.mk ⟨Additive.ofMul (ideleClassMap K L c.toMul),
      by
        rw [AddMonoidHom.mem_ker, cycSubOne_apply, Representation.ofMulDistribMulAction_apply_apply,
          sub_eq_zero]
        exact congrArg Additive.ofMul (smul_ideleClassMap σ _)⟩ :=
  rfl

section Galois

variable [IsGalois K L]

theorem cycNorm_ideleClassGroup (c : Additive (IdeleClassGroup L)) :
    cycNorm (Representation.ofMulDistribMulAction Gal(L/K) (IdeleClassGroup L)) c =
      Additive.ofMul (ideleClassMap K L (ideleClassNorm K L c.toMul)) := by
  rw [cycNorm_apply, ideleClassMap_ideleClassNorm]
  simp only [Representation.ofMulDistribMulAction_apply_apply]
  rfl

theorem ideleClassToCycTateZero_surjective (σ : Gal(L/K))
    (hσ : ∀ g, g ∈ Subgroup.zpowers σ) : Function.Surjective (ideleClassToCycTateZero K L σ) := by
  intro x
  induction x using QuotientAddGroup.induction_on with
  | H y =>
  obtain ⟨y, hy⟩ := y
  have hfix := (mem_ker_cycSubOne_iff _ hσ y).1 hy
  obtain ⟨c, hc⟩ := (forall_smul_eq_iff_mem_range_ideleClassMap (K := K) y.toMul).1 fun g ↦
    congrArg Additive.toMul (hfix g)
  refine ⟨Additive.ofMul c, ?_⟩
  rw [ideleClassToCycTateZero_apply]
  congr 1
  exact Subtype.ext (by simp [hc])

theorem ker_ideleClassToCycTateZero (σ : Gal(L/K)) :
    (ideleClassToCycTateZero K L σ).ker = Subgroup.toAddSubgroup (ideleClassNorm K L).range := by
  ext c
  rw [AddMonoidHom.mem_ker, ideleClassToCycTateZero_apply, KerModRange.mk_eq_zero_iff]
  change _ ↔ c.toMul ∈ (ideleClassNorm K L).range
  rw [AddMonoidHom.mem_range, MonoidHom.mem_range]
  constructor
  · rintro ⟨d, hd⟩
    rw [cycNorm_ideleClassGroup] at hd
    exact ⟨d.toMul, ideleClassMap_injective (congrArg Additive.toMul hd)⟩
  · rintro ⟨d, hd⟩
    refine ⟨Additive.ofMul d, ?_⟩
    rw [cycNorm_ideleClassGroup]
    simp [hd]

theorem natCard_cycTateZero_ideleClassGroup (σ : Gal(L/K)) (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    Nat.card (CycTateZero (Representation.ofMulDistribMulAction Gal(L/K) (IdeleClassGroup L)) σ) =
      (ideleClassNorm K L).range.index := by
  rw [← Subgroup.index_toAddSubgroup, ← ker_ideleClassToCycTateZero σ, AddSubgroup.index]
  exact (Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective _
    (ideleClassToCycTateZero_surjective σ hσ)).toEquiv).symm

theorem index_range_ideleClassNorm (σ : Gal(L/K)) (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    (ideleClassNorm K L).range.index = finrank K L *
      Nat.card (CycTateNegOne (Representation.ofMulDistribMulAction Gal(L/K) (IdeleClassGroup L)) σ) ∧
    Nat.card (CycTateNegOne (Representation.ofMulDistribMulAction Gal(L/K) (IdeleClassGroup L)) σ)
      ≠ 0 := by
  obtain ⟨hH, hval⟩ := IdeleGroup.cycHerbrand_ideleClassGroup (K := K) (L := L) σ hσ
  have := hH.2
  have hpos : Nat.card (CycTateNegOne (Representation.ofMulDistribMulAction Gal(L/K)
      (IdeleClassGroup L)) σ) ≠ 0 := Nat.card_pos.ne'
  refine ⟨?_, hpos⟩
  rw [cycHerbrand_eq, natCard_cycTateZero_ideleClassGroup σ hσ,
    div_eq_iff (Nat.cast_ne_zero.2 hpos)] at hval
  exact_mod_cast hval

theorem finrank_le_index_range_ideleClassNorm [IsCyclic Gal(L/K)] :
    finrank K L ≤ (ideleClassNorm K L).range.index ∧ (ideleClassNorm K L).range.index ≠ 0 := by
  obtain ⟨σ, hσ⟩ := IsCyclic.exists_generator (α := Gal(L/K))
  obtain ⟨h, hpos⟩ := index_range_ideleClassNorm σ hσ
  rw [h]
  exact ⟨Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hpos),
    mul_ne_zero Module.finrank_pos.ne' hpos⟩

end Galois

theorem firstInequality.{u} : FirstInequality.{u} := by
  intro K L _ _ _ _ _ _ _
  obtain ⟨hle, hne⟩ := finrank_le_index_range_ideleClassNorm (K := K) (L := L)
  have : (ideleClassNorm K L).range.FiniteIndex := ⟨hne⟩
  have : Finite (IdeleClassGroup K ⧸ (ideleClassNorm K L).range) :=
    Subgroup.finite_quotient_of_finiteIndex
  let := Fintype.ofFinite (IdeleClassGroup K ⧸ (ideleClassNorm K L).range)
  rw [ENat.card_eq_coe_fintype_card, Fintype.card_eq_nat_card]
  exact_mod_cast hle

end Sec_23_FirstInequality

/-! ### 24_SplittingFromInequality -/
section Sec_24_SplittingFromInequality

open IsDedekindDomain NumberField Filter Topology
open SemiLocal IdeleNorm


section Approximation

variable {K : Type*} [Field K] [NumberField K] {L : Type*} [Field L] [NumberField L] [Algebra K L]

theorem IdeleGroup.finiteProj_diagonal (v : HeightOneSpectrum (𝓞 K)) (a : Kˣ) :
    IdeleGroup.finiteProj v (IdeleGroup.diagonal K a) =
      Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom a :=
  Units.ext (IdeleGroup.coe_finiteProj_diagonal v a)

theorem IdeleGroup.infiniteProj_diagonal (w : InfinitePlace K) (a : Kˣ) :
    IdeleGroup.infiniteProj w (IdeleGroup.diagonal K a) =
      Units.map (algebraMap K w.Completion).toMonoidHom a :=
  Units.ext (IdeleGroup.coe_infiniteProj_diagonal w a)

variable (L) in

theorem exists_diagonal_mul_mem_localNorms (S : Finset (HeightOneSpectrum (𝓞 K)))
    (x : IdeleGroup K) :
    ∃ a : Kˣ, (∀ v ∈ S, IdeleGroup.finiteProj v (IdeleGroup.diagonal K a * x) ∈
        (finiteLocalNorm L v).range) ∧
      ∀ w, IdeleGroup.infiniteProj w (IdeleGroup.diagonal K a * x) ∈
        (infiniteLocalNorm L w).range := by
  classical
  let U : Set (((v : S) → (v.1.adicCompletion K)ˣ) ×
      ((w : (Finset.univ : Finset (InfinitePlace K))) → (w.1.Completion)ˣ)) :=
    {p | (∀ v : S, p.1 v * IdeleGroup.finiteProj v.1 x ∈ (finiteLocalNorm L v.1).range) ∧
      ∀ w : (Finset.univ : Finset (InfinitePlace K)),
        p.2 w * IdeleGroup.infiniteProj w.1 x ∈ (infiniteLocalNorm L w.1).range}
  have hU : IsOpen U := by
    simp only [U, Set.ofPred_and, Set.ofPred_forall]
    exact (isOpen_iInter_of_finite fun v : S ↦ (isOpen_range_finiteLocalNorm v.1).preimage
        (((continuous_apply v).comp continuous_fst).mul continuous_const)).inter
      (isOpen_iInter_of_finite fun w ↦ (isOpen_range_infiniteLocalNorm w.1).preimage
        (((continuous_apply w).comp continuous_snd).mul continuous_const))
  have hne : U.Nonempty := by
    refine ⟨(fun v ↦ (IdeleGroup.finiteProj v.1 x)⁻¹, fun w ↦ (IdeleGroup.infiniteProj w.1 x)⁻¹),
      fun v ↦ ?_, fun w ↦ ?_⟩
    · rw [inv_mul_cancel]
      exact one_mem _
    · rw [inv_mul_cancel]
      exact one_mem _
  obtain ⟨a, ha⟩ := (denseRange_units_prod_pi S Finset.univ).exists_mem_open hU hne
  refine ⟨a, fun v hv ↦ ?_, fun w ↦ ?_⟩
  · rw [map_mul, IdeleGroup.finiteProj_diagonal]
    exact ha.1 ⟨v, hv⟩
  · rw [map_mul, IdeleGroup.infiniteProj_diagonal]
    exact ha.2 ⟨w, Finset.mem_univ w⟩

theorem ideleNorm_range_sup_eq_top_of_eventually_splitsCompletely
    (h : ∀ᶠ v : HeightOneSpectrum (𝓞 K) in cofinite, SplitsCompletely L v) :
    (ideleNorm K L).range ⊔ (IdeleGroup.diagonal K).range = ⊤ := by
  classical
  refine eq_top_iff.2 fun x _ ↦ ?_
  set S := (eventually_cofinite.1 h).toFinset
  obtain ⟨a, hfin, hinf⟩ := exists_diagonal_mul_mem_localNorms L S x
  have hmem : IdeleGroup.diagonal K a * x ∈ (ideleNorm K L).range := by
    refine mem_range_ideleNorm_of_forall _ (fun v ↦ ?_) hinf
    by_cases hv : v ∈ S
    · exact hfin v hv
    · have hv' : SplitsCompletely L v := by simpa [S] using hv
      rw [range_finiteLocalNorm_eq_top_of_isFiniteSplit v
        ((splitsCompletely_iff_isFiniteSplit v).1 hv')]
      exact Subgroup.mem_top _
  have hx : x = (IdeleGroup.diagonal K a * x) * (IdeleGroup.diagonal K a)⁻¹ := by
    rw [mul_comm, inv_mul_cancel_left]
  rw [hx]
  exact Subgroup.mul_mem_sup hmem (inv_mem ⟨a, rfl⟩)

end Approximation

section Cyclic

universe u

variable {K L : Type u} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] [IsCyclic Gal(L/K)]

theorem FirstInequality.finrank_eq_one_of_eventually_splitsCompletely (hFI : FirstInequality.{u})
    (h : ∀ᶠ v : HeightOneSpectrum (𝓞 K) in cofinite, SplitsCompletely L v) :
    Module.finrank K L = 1 :=
  hFI.finrank_eq_one_of_sup_eq_top (ideleNorm_range_sup_eq_top_of_eventually_splitsCompletely h)

theorem FirstInequality.finrank_eq_one_of_splitsCompletely_of_finite (hFI : FirstInequality.{u})
    {T : Set (HeightOneSpectrum (𝓞 K))} (hT : T.Finite) (h : ∀ v ∉ T, SplitsCompletely L v) :
    Module.finrank K L = 1 :=
  hFI.finrank_eq_one_of_eventually_splitsCompletely
    (eventually_cofinite.2 (hT.subset fun v hv ↦ by_contra fun hvT ↦ hv (h v hvT)))

end Cyclic

end Sec_24_SplittingFromInequality

/-! ### 25_SplittingFromInequality.Galois -/
section Sec_25_SplittingFromInequality_Galois

open IsDedekindDomain NumberField Filter Module AdeleBaseChange


section Tower

variable {K K' L : Type*} [Field K] [NumberField K] [Field K'] [NumberField K'] [Field L]
  [NumberField L] [Algebra K K'] [Algebra K' L] [Algebra K L] [IsScalarTower K K' L]

omit [NumberField K] [NumberField L] in

theorem SplitsCompletely.of_liesOver {v : HeightOneSpectrum (𝓞 K)} (hv : SplitsCompletely L v)
    (v' : HeightOneSpectrum (𝓞 K')) [v'.asIdeal.LiesOver v.asIdeal] : SplitsCompletely L v' := by
  intro w hw
  have : w.asIdeal.LiesOver v.asIdeal := Ideal.LiesOver.trans w.asIdeal v'.asIdeal v.asIdeal
  obtain ⟨he, hf⟩ := hv w this
  rw [Ideal.ramificationIdx_tower (R := 𝓞 K) v'.asIdeal w.asIdeal] at he
  rw [Ideal.inertiaDeg_tower (R := 𝓞 K) v'.asIdeal w.asIdeal] at hf
  exact ⟨(mul_eq_one.1 he).2, (mul_eq_one.1 hf).2⟩

variable (K) in

omit [NumberField L] in
theorem eventually_splitsCompletely_of_tower
    (h : ∀ᶠ v : HeightOneSpectrum (𝓞 K) in cofinite, SplitsCompletely L v) :
    ∀ᶠ v' : HeightOneSpectrum (𝓞 K') in cofinite, SplitsCompletely L v' :=
  ((tendsto_below (K := K) (L := K')).eventually h).mono fun v' hv' ↦ hv'.of_liesOver v'

end Tower

section Galois

universe u

variable {K L : Type u} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]

theorem FirstInequality.finrank_eq_one_of_eventually_splitsCompletely_of_isGalois
    (hFI : FirstInequality.{u})
    (h : ∀ᶠ v : HeightOneSpectrum (𝓞 K) in cofinite, SplitsCompletely L v) :
    finrank K L = 1 := by
  by_contra hne
  have hnt : Nontrivial Gal(L/K) := by
    rw [← Finite.one_lt_card_iff_nontrivial, IsGalois.card_aut_eq_finrank]
    have := finrank_pos (R := K) (M := L)
    omega
  obtain ⟨σ, hσ⟩ := exists_ne (1 : Gal(L/K))
  let H := Subgroup.zpowers σ
  have : IsCyclic Gal(L/IntermediateField.fixedField H) := by
    have e : H ≃* Gal(L/IntermediateField.fixedField H) :=
      (MulEquiv.subgroupCongr (IntermediateField.fixingSubgroup_fixedField H).symm).trans
        (IntermediateField.fixingSubgroupEquiv _)
    have : IsCyclic H := Subgroup.isCyclic_zpowers σ
    exact isCyclic_of_surjective e.toMonoidHom e.surjective
  have h1 := hFI.finrank_eq_one_of_eventually_splitsCompletely
    (eventually_splitsCompletely_of_tower K (K' := IntermediateField.fixedField H) h)
  rw [IntermediateField.finrank_fixedField_eq_card, Subgroup.card_eq_one] at h1
  exact hσ (Subgroup.mem_bot.1 (h1 ▸ Subgroup.mem_zpowers σ))

theorem FirstInequality.finrank_eq_one_of_splitsCompletely_of_finite_of_isGalois
    (hFI : FirstInequality.{u}) {T : Set (HeightOneSpectrum (𝓞 K))} (hT : T.Finite)
    (h : ∀ v ∉ T, SplitsCompletely L v) :
    finrank K L = 1 :=
  hFI.finrank_eq_one_of_eventually_splitsCompletely_of_isGalois
    (eventually_cofinite.2 (hT.subset fun v hv ↦ by_contra fun hvT ↦ hv (h v hvT)))

end Galois

end Sec_25_SplittingFromInequality_Galois

/-! ### 26_SplittingFromInequality.Decomposition -/
section Sec_26_SplittingFromInequality_Decomposition

open IsDedekindDomain NumberField Filter Module AdeleBaseChange SemiLocal IntermediateField
open scoped Pointwise


section FixedField

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]

omit [NumberField K] [NumberField L] [IsGalois K L] in

theorem card_stabilizer_fixedField_eq (H : Subgroup Gal(L/K)) (w : HeightOneSpectrum (𝓞 L))
    (hD : MulAction.stabilizer Gal(L/K) w.asIdeal ≤ H) [FiniteDimensional K L] :
    Nat.card (MulAction.stabilizer Gal(L/fixedField H) w.asIdeal) =
      Nat.card (MulAction.stabilizer Gal(L/K) w.asIdeal) := by
  refine Nat.card_congr (Equiv.ofBijective
    (fun σ ↦ ⟨(σ : Gal(L/fixedField H)).restrictScalars K, σ.2⟩) ⟨?_, ?_⟩)
  · intro σ τ h
    exact Subtype.ext (AlgEquiv.restrictScalars_injective K (congrArg Subtype.val h))
  · rintro ⟨τ, hτ⟩
    have hτH : τ ∈ fixingSubgroup (fixedField H) := (fixingSubgroup_fixedField H).symm ▸ hD hτ
    exact ⟨⟨fixingSubgroupEquiv (fixedField H) ⟨τ, hτH⟩, hτ⟩, Subtype.ext (AlgEquiv.ext fun _ ↦ rfl)⟩

theorem ramificationIdx_eq_one_and_inertiaDeg_eq_one_of_stabilizer_le (H : Subgroup Gal(L/K))
    (v : HeightOneSpectrum (𝓞 K)) (w' : HeightOneSpectrum (𝓞 (fixedField H)))
    (w : HeightOneSpectrum (𝓞 L)) [w'.asIdeal.LiesOver v.asIdeal] [w.asIdeal.LiesOver w'.asIdeal]
    (hD : MulAction.stabilizer Gal(L/K) w.asIdeal ≤ H) :
    w'.asIdeal.ramificationIdx (𝓞 K) = 1 ∧ w'.asIdeal.inertiaDeg (𝓞 K) = 1 := by
  have : w.asIdeal.LiesOver v.asIdeal := Ideal.LiesOver.trans w.asIdeal w'.asIdeal v.asIdeal
  have h1 := card_decompositionGroup v w
  have h2 := card_decompositionGroup w' w
  rw [card_stabilizer_fixedField_eq H w hD] at h2
  rw [Ideal.ramificationIdx_tower (R := 𝓞 K) w'.asIdeal w.asIdeal,
    Ideal.inertiaDeg_tower (R := 𝓞 K) w'.asIdeal w.asIdeal, h2] at h1
  have hpos : 0 < w.asIdeal.ramificationIdx (𝓞 (fixedField H)) *
      w.asIdeal.inertiaDeg (𝓞 (fixedField H)) := by
    rw [← h2]
    exact Nat.card_pos
  have key : w'.asIdeal.ramificationIdx (𝓞 K) * w'.asIdeal.inertiaDeg (𝓞 K) *
      (w.asIdeal.ramificationIdx (𝓞 (fixedField H)) * w.asIdeal.inertiaDeg (𝓞 (fixedField H))) =
      1 * (w.asIdeal.ramificationIdx (𝓞 (fixedField H)) *
        w.asIdeal.inertiaDeg (𝓞 (fixedField H))) := by
    rw [one_mul]
    conv_rhs => rw [h1]
    ring
  exact mul_eq_one.1 (Nat.eq_of_mul_eq_mul_right hpos key)

theorem splitsCompletely_fixedField_of_stabilizer_le (H : Subgroup Gal(L/K))
    (v : HeightOneSpectrum (𝓞 K))
    (hD : ∀ w : HeightOneSpectrum (𝓞 L), w.asIdeal.LiesOver v.asIdeal →
      MulAction.stabilizer Gal(L/K) w.asIdeal ≤ H) :
    SplitsCompletely (fixedField H) v := by
  intro w' hw'
  obtain ⟨w⟩ := nonempty_placesOver L w'
  have : w.1.asIdeal.LiesOver v.asIdeal := Ideal.LiesOver.trans w.1.asIdeal w'.asIdeal v.asIdeal
  exact ramificationIdx_eq_one_and_inertiaDeg_eq_one_of_stabilizer_le H v w' w.1 (hD w.1 this)

omit [NumberField K] [NumberField L] [IsGalois K L] in

theorem below_smul (σ : Gal(L/K)) (w : HeightOneSpectrum (𝓞 L)) : below K (σ • w) = below K w :=
  (below_eq_iff (σ • w) (below K w)).2 (by rw [smul_asIdeal]; infer_instance)

end FixedField

section Generation

universe u

variable {K L : Type u} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]

theorem FirstInequality.closure_stabilizer_eq_top (hFI : FirstInequality.{u})
    {T : Set (HeightOneSpectrum (𝓞 K))} (hT : T.Finite) :
    Subgroup.closure (⋃ (w : HeightOneSpectrum (𝓞 L)) (_ : below K w ∉ T),
      (MulAction.stabilizer Gal(L/K) w.asIdeal : Set Gal(L/K))) = ⊤ := by
  set S : Set Gal(L/K) := ⋃ (w : HeightOneSpectrum (𝓞 L)) (_ : below K w ∉ T),
    (MulAction.stabilizer Gal(L/K) w.asIdeal : Set Gal(L/K)) with hS
  set H := Subgroup.closure S
  have hconj : ∀ g : Gal(L/K), (MulAut.conj g).toMonoidHom '' S ⊆ S := by
    rintro g _ ⟨σ, hσ, rfl⟩
    obtain ⟨w, hw, hσ⟩ := Set.mem_iUnion₂.1 hσ
    refine Set.mem_iUnion₂.2 ⟨g • w, by rwa [below_smul], ?_⟩
    have hσ' : σ • w.asIdeal = w.asIdeal := hσ
    change (g * σ * g⁻¹) • (g • w).asIdeal = (g • w).asIdeal
    rw [smul_asIdeal, mul_smul, mul_smul, inv_smul_smul, hσ']
  have hH : H.Normal := ⟨fun n hn g ↦ by
    have : (MulAut.conj g).toMonoidHom n ∈ H.map (MulAut.conj g).toMonoidHom := ⟨n, hn, rfl⟩
    rw [MonoidHom.map_closure] at this
    exact Subgroup.closure_mono (hconj g) this⟩
  have hsplit : ∀ v ∉ T, SplitsCompletely (fixedField H) v := fun v hv ↦
    splitsCompletely_fixedField_of_stabilizer_le H v fun w hw _ hσ ↦
      Subgroup.subset_closure (Set.mem_iUnion₂.2 ⟨w, by rwa [(below_eq_iff w v).2 hw], hσ⟩)
  have h1 := hFI.finrank_eq_one_of_splitsCompletely_of_finite_of_isGalois
    (L := fixedField H) hT hsplit
  rw [IntermediateField.finrank_eq_one_iff] at h1
  rw [← fixingSubgroup_fixedField H, h1, fixingSubgroup_bot]

end Generation

section Frobenius

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]

open AdicLiesOver in

theorem stabilizer_eq_zpowers_arithFrobAt (v : HeightOneSpectrum (𝓞 K))
    (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]
    (he : w.asIdeal.ramificationIdx (𝓞 K) = 1) :
    MulAction.stabilizer Gal(L/K) w.asIdeal =
      Subgroup.zpowers (arithFrobAt (𝓞 K) Gal(L/K) w.asIdeal) := by
  have h : RHDirect.CFT.LocalField.ramificationIndex (v.adicCompletion K) (w.adicCompletion L) = 1 := by
    rw [RHDirect.CFT.LocalField.ramificationIndex, ramificationIdx_integer v w, he]
  have hfr : decompositionToLocal v w (arithFrobAtDecomposition w) =
      RHDirect.CFT.LocalField.frobenius _ _ h :=
    (eq_decompositionToLocal_arithFrobAt v w he _
      (RHDirect.CFT.LocalField.frobenius_sub_pow_mem_maximalIdeal _ _ h)).symm
  have htop : Subgroup.zpowers (arithFrobAtDecomposition (K := K) w) = ⊤ := by
    refine eq_top_iff.2 fun σ _ ↦ ?_
    have hmem : decompositionToLocal v w σ ∈
        (Subgroup.zpowers (arithFrobAtDecomposition (K := K) w)).map (decompositionToLocal v w) := by
      rw [MonoidHom.map_zpowers, hfr, RHDirect.CFT.LocalField.zpowers_frobenius]
      exact Subgroup.mem_top _
    obtain ⟨τ, hτ, hτσ⟩ := hmem
    rwa [← decompositionToLocal_injective v w hτσ]
  refine le_antisymm (fun σ hσ ↦ ?_) ((Subgroup.zpowers_le).2
    (IsArithFrobAt.arithFrobAt_mem_stabilizer (𝓞 K) Gal(L/K) w.asIdeal))
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1
    (htop ▸ Subgroup.mem_top (⟨σ, hσ⟩ : MulAction.stabilizer Gal(L/K) w.asIdeal))
  have hk' := congrArg Subtype.val hk
  rw [Subgroup.coe_zpow] at hk'
  exact Subgroup.mem_zpowers_iff.2 ⟨k, hk'⟩

end Frobenius

section FrobeniusGeneration

universe u

variable {K L : Type u} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]

end FrobeniusGeneration

end Sec_26_SplittingFromInequality_Decomposition

end RHDirect.CFT.Global
