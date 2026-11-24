import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.FieldTheory.KrullTopology
import Mathlib.FieldTheory.Separable
import Mathlib.FieldTheory.SeparableClosure
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.AdicCompletion.RingHom
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.FormalGroup.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.MvPowerSeries.Order
import Mathlib.RingTheory.MvPowerSeries.Substitution
import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
import Mathlib.RingTheory.Polynomial.Eisenstein.Distinguished
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.WeierstrassPreparation
import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
import Mathlib.Tactic.Group
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Algebra.Ring.Compact
import RHDirect.CFT_FormalGroups
import RHDirect.CFT_AbstractLocalReciprocity
import RHDirect.CFT_LocalStructure
import RHDirect.CFT_LocalRamification

/-!
# RHDirect.CFT_LubinTateTower

Lubin–Tate Formal Modules, Torsion Points, Totally Ramified Abelian Towers `K_π`,
Galois Action on Lubin–Tate Torsion, Local Class Field Axiom (`localClassFieldTheory`),
and Explicit Lubin–Tate Reciprocity Law (`namespace RHDirect.CFT.LocalField`).
-/

noncomputable section


/-! ### LubinTatePoints -/
section Sec_LubinTatePoints


namespace RHDirect.CFT.LocalField

open ValuativeRel MvPowerSeries Topology Filter

section Term

variable {K : Type*} [Field K] [ValuativeRel K] {σ M M' : Type*} [CommRing M] [Algebra K M]
  [CommRing M'] [Algebra K M']

def psTerm (f : MvPowerSeries σ 𝒪[K]) (x : σ → M) (d : σ →₀ ℕ) : M :=
  algebraMap K M ((coeff d f : 𝒪[K]) : K) * d.prod fun i k => x i ^ k

def psEval [TopologicalSpace M] (f : MvPowerSeries σ 𝒪[K]) (x : σ → M) : M :=
  ∑' d, psTerm f x d

theorem map_psTerm (ρ : M →ₐ[K] M') (f : MvPowerSeries σ 𝒪[K]) (x : σ → M) (d : σ →₀ ℕ) :
    ρ (psTerm f x d) = psTerm f (fun i => ρ (x i)) d := by
  simp only [psTerm, map_mul, AlgHom.commutes, Finsupp.prod, map_prod, map_pow]

theorem map_psEval [TopologicalSpace M] [TopologicalSpace M'] [T2Space M'] (ρ : M →ₐ[K] M')
    (hρ : Continuous ρ) {f : MvPowerSeries σ 𝒪[K]} {x : σ → M}
    (h : HasSum (psTerm f x) (psEval f x)) :
    ρ (psEval f x) = psEval f fun i => ρ (x i) := by
  have h' := h.map ρ.toRingHom.toAddMonoidHom hρ
  refine (HasSum.tsum_eq ?_).symm
  convert h' using 1
  · funext d
    exact (map_psTerm ρ f x d).symm
  · rfl

end Term

section Local

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {L : Type*} [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L]

theorem mem_maximalIdeal_integer_iff {x : 𝒪[L]} : x ∈ 𝓂[L] ↔ valuation L (x : L) < 1 := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  exact Valuation.Integer.not_isUnit_iff_valuation_lt_one

variable (L) in

theorem isClosed_maximalIdeal_integer : IsClosed ((𝓂[L] : Ideal 𝒪[L]) : Set 𝒪[L]) := by
  have hopen : IsOpen ((𝓂[L] : Ideal 𝒪[L]) : Set 𝒪[L]) := by
    refine (𝓂[L]).toAddSubgroup.isOpen_of_mem_nhds (g := 0) ?_
    refine (EqualChar.hasBasis_nhds_zero_integer L).mem_iff.mpr ⟨1, trivial, fun x hx => ?_⟩
    rw [SetLike.mem_coe, EqualChar.mem_ballIdeal] at hx
    exact mem_maximalIdeal_integer_iff.mpr hx
  exact AddSubgroup.isClosed_of_isOpen (𝓂[L]).toAddSubgroup hopen

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] in
theorem coe_psTerm_integer {σ : Type*} (f : MvPowerSeries σ 𝒪[K]) (a : σ → 𝒪[L]) (d : σ →₀ ℕ) :
    ((algebraMap 𝒪[K] 𝒪[L] (coeff d f) * d.prod fun s e => a s ^ e : 𝒪[L]) : L) =
      psTerm f (fun i => (a i : L)) d := by
  simp [psTerm, Finsupp.prod]

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] [Algebra K L] [ValuativeExtension K L] in

theorem hasEval_of_mem_maximalIdeal {σ : Type*} [Finite σ] {a : σ → 𝒪[L]} (ha : ∀ i, a i ∈ 𝓂[L]) :
    HasEval a := by
  refine ⟨fun i => ?_, ?_⟩
  · refine (EqualChar.hasBasis_nhds_zero_integer L).tendsto_right_iff.mpr fun γ _ => ?_
    obtain ⟨N, hN⟩ := exists_pow_lt₀ (mem_maximalIdeal_integer_iff.mp (ha i)) γ
    filter_upwards [eventually_ge_atTop N] with n hn
    rw [SetLike.mem_coe, EqualChar.mem_ballIdeal, SubmonoidClass.coe_pow, map_pow]
    exact lt_of_le_of_lt (pow_le_pow_of_le_one zero_le
      (mem_maximalIdeal_integer_iff.mp (ha i)).le hn) hN
  · rw [Filter.cofinite_eq_bot]
    exact tendsto_bot

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in

theorem hasSum_psTerm_eval₂ {σ : Type*} [Finite σ] (f : MvPowerSeries σ 𝒪[K]) (a : σ → 𝒪[L])
    (ha : ∀ i, a i ∈ 𝓂[L]) :
    letI : UniformSpace 𝒪[K] := ⊥
    letI : UniformSpace L := IsTopologicalAddGroup.rightUniformSpace L
    HasSum (psTerm f fun i => (a i : L))
      ((MvPowerSeries.eval₂ (algebraMap 𝒪[K] 𝒪[L]) a f : 𝒪[L]) : L) := by
  let _ : UniformSpace L := IsTopologicalAddGroup.rightUniformSpace L
  have _ : IsUniformAddGroup L := isUniformAddGroup_of_addCommGroup
  let _ : UniformSpace 𝒪[K] := ⊥
  have _ : DiscreteUniformity 𝒪[K] := ⟨rfl⟩
  have hφ : Continuous[(⊥ : UniformSpace 𝒪[K]).toTopologicalSpace, _]
      (algebraMap 𝒪[K] 𝒪[L]) := by
    rw [UniformSpace.toTopologicalSpace_bot]
    exact continuous_bot
  have hs := hasSum_eval₂ hφ (hasEval_of_mem_maximalIdeal ha) f
  have h2 : HasSum (fun d => ((algebraMap 𝒪[K] 𝒪[L] (coeff d f) *
      d.prod fun s e => a s ^ e : 𝒪[L]) : L))
      ((MvPowerSeries.eval₂ (algebraMap 𝒪[K] 𝒪[L]) a f : 𝒪[L]) : L) :=
    hs.map (AddSubmonoidClass.subtype 𝒪[L]) continuous_subtype_val
  simpa only [coe_psTerm_integer] using h2

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in

theorem hasSum_psEval {σ : Type*} [Finite σ] (f : MvPowerSeries σ 𝒪[K]) (a : σ → 𝒪[L])
    (ha : ∀ i, a i ∈ 𝓂[L]) :
    HasSum (psTerm f fun i => (a i : L)) (psEval f fun i => (a i : L)) :=
  (hasSum_psTerm_eval₂ f a ha).summable.hasSum

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
theorem psEval_eq_eval₂ {σ : Type*} [Finite σ] (f : MvPowerSeries σ 𝒪[K]) (a : σ → 𝒪[L])
    (ha : ∀ i, a i ∈ 𝓂[L]) :
    letI : UniformSpace 𝒪[K] := ⊥
    letI : UniformSpace L := IsTopologicalAddGroup.rightUniformSpace L
    psEval f (fun i => (a i : L)) =
      ((MvPowerSeries.eval₂ (algebraMap 𝒪[K] 𝒪[L]) a f : 𝒪[L]) : L) :=
  have := t2Space_of_isNonarchimedeanLocalField L
  (hasSum_psTerm_eval₂ f a ha).tsum_eq

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in

theorem psEval_mem_integer {σ : Type*} [Finite σ] (f : MvPowerSeries σ 𝒪[K]) (a : σ → 𝒪[L])
    (ha : ∀ i, a i ∈ 𝓂[L]) :
    psEval f (fun i => (a i : L)) ∈ 𝒪[L] := by
  rw [psEval_eq_eval₂ f a ha]
  exact SetLike.coe_mem _

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
theorem valuation_psEval_lt_one {σ : Type*} [Finite σ] {f : MvPowerSeries σ 𝒪[K]}
    (hf : constantCoeff f = 0) (a : σ → 𝒪[L]) (ha : ∀ i, a i ∈ 𝓂[L]) :
    valuation L (psEval f fun i => (a i : L)) < 1 := by
  let y : 𝒪[L] := ⟨_, psEval_mem_integer f a ha⟩
  change valuation L (y : L) < 1
  refine mem_maximalIdeal_integer_iff.mp ?_
  refine (isClosed_maximalIdeal_integer L).mem_of_tendsto
    (b := (SummationFilter.unconditional (σ →₀ ℕ)).filter)
    (f := fun s : Finset (σ →₀ ℕ) => ∑ d ∈ s, (⟨psTerm f (fun i => (a i : L)) d, ?_⟩ : 𝒪[L]))
    ?_ (Eventually.of_forall fun s => ?_)
  · rw [← coe_psTerm_integer]
    exact SetLike.coe_mem _
  · have h := hasSum_psEval f a ha
    rw [HasSum] at h
    rw [(Topology.IsInducing.subtypeVal).tendsto_nhds_iff]
    convert h using 1
    funext s
    simp
  · refine Ideal.sum_mem _ fun d _ => ?_
    have he : (⟨psTerm f (fun i => (a i : L)) d, by
        rw [← coe_psTerm_integer]; exact SetLike.coe_mem _⟩ : 𝒪[L]) =
        algebraMap 𝒪[K] 𝒪[L] (coeff d f) * d.prod fun s e => a s ^ e :=
      Subtype.ext (coe_psTerm_integer f a d).symm
    rw [he]
    by_cases hd : d = 0
    · subst hd
      simp [hf]
    · obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp hd
      refine Ideal.mul_mem_left _ _ ?_
      rw [Finsupp.prod]
      refine Ideal.prod_mem _ (i := i) (Finsupp.mem_support_iff.mpr hi) ?_
      exact Ideal.pow_mem_of_mem _ (ha i) _ (Nat.pos_of_ne_zero hi)

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in

theorem psEval_subst {σ τ : Type*} [Finite σ] [Finite τ] {g : σ → MvPowerSeries τ 𝒪[K]}
    (hg : ∀ s, constantCoeff (g s) = 0) (f : MvPowerSeries σ 𝒪[K]) (a : τ → 𝒪[L])
    (ha : ∀ i, a i ∈ 𝓂[L]) :
    psEval (subst g f) (fun i => (a i : L)) =
      psEval f (fun s => psEval (g s) fun i => (a i : L)) := by
  let b : σ → 𝒪[L] := fun s => ⟨_, psEval_mem_integer (g s) a ha⟩
  have hb : ∀ s, b s ∈ 𝓂[L] := fun s =>
    mem_maximalIdeal_integer_iff.mpr (valuation_psEval_lt_one (hg s) a ha)
  change _ = psEval f fun s => (b s : L)
  let _ : UniformSpace L := IsTopologicalAddGroup.rightUniformSpace L
  have _ : IsUniformAddGroup L := isUniformAddGroup_of_addCommGroup
  let _ : UniformSpace 𝒪[K] := ⊥
  have _ : DiscreteUniformity 𝒪[K] := ⟨rfl⟩
  rw [psEval_eq_eval₂ f b hb, psEval_eq_eval₂ _ a ha]
  have hsub : HasSubst g := hasSubst_of_constantCoeff_zero hg
  rw [eval₂_subst hsub (hasEval_of_mem_maximalIdeal ha)]
  congr 3
  funext s
  apply Subtype.ext
  exact (psEval_eq_eval₂ (g s) a ha).symm

end Local

section Algebraic

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]

variable (Ω) in

theorem t2Space_of_isValuativeTopology : T2Space Ω := by
  refine IsTopologicalAddGroup.t2Space_of_zero_sep fun x hx => ?_
  refine ⟨{z | valuation Ω z < valuation Ω x}, ?_, fun h => lt_irrefl (valuation Ω x) h⟩
  exact (IsValuativeTopology.hasBasis_nhds_zero Ω).mem_of_mem
    (i := Units.mk0 _ ((valuation Ω).ne_zero_iff.mpr hx)) trivial

variable [Algebra K Ω] [ValuativeExtension K Ω]

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [TopologicalSpace Ω]
  [IsValuativeTopology Ω] [ValuativeExtension K Ω] in

theorem valuation_coe_lt_one_iff (E : IntermediateField K Ω) (x : E) :
    valuation Ω (x : Ω) < 1 ↔ valuation E x < 1 := by
  rw [← map_one (valuation Ω), ← (valuation Ω).vlt_iff_lt, ← map_one (valuation E),
    ← (valuation E).vlt_iff_lt]
  exact not_congr (by simpa using IntermediateField.coe_vle_coe_iff (1 : E) x)

variable [Algebra.IsAlgebraic K Ω]

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeRel Ω]
  [TopologicalSpace Ω] [IsValuativeTopology Ω] [ValuativeExtension K Ω] in

theorem finiteDimensional_adjoin_range {σ : Type*} [Finite σ] (x : σ → Ω) :
    FiniteDimensional K (IntermediateField.adjoin K (Set.range x)) :=
  have : Finite (Set.range x) := Set.finite_range x
  IntermediateField.finiteDimensional_adjoin fun y _ => (Algebra.IsAlgebraic.isAlgebraic y).isIntegral

theorem hasSum_psEval_coe (E : IntermediateField K Ω) [FiniteDimensional K E] {σ : Type*}
    [Finite σ] (f : MvPowerSeries σ 𝒪[K]) (x : σ → E) (hx : ∀ i, valuation Ω (x i : Ω) < 1) :
    HasSum (psTerm f fun i => (x i : Ω)) ((psEval f x : E) : Ω) := by
  let a : σ → 𝒪[E] := fun i => ⟨x i, ((valuation_coe_lt_one_iff E (x i)).mp (hx i)).le⟩
  have ha : ∀ i, a i ∈ 𝓂[E] := fun i =>
    mem_maximalIdeal_integer_iff.mpr ((valuation_coe_lt_one_iff E (x i)).mp (hx i))
  have hE : HasSum (psTerm f x) (psEval f x) := hasSum_psEval f a ha
  have h := hE.map E.val.toRingHom.toAddMonoidHom continuous_subtype_val
  convert h using 1
  · funext d
    exact (map_psTerm E.val f x d).symm
  · rfl

theorem psEval_coe (E : IntermediateField K Ω) [FiniteDimensional K E] {σ : Type*} [Finite σ]
    (f : MvPowerSeries σ 𝒪[K]) (x : σ → E) (hx : ∀ i, valuation Ω (x i : Ω) < 1) :
    psEval f (fun i => (x i : Ω)) = ((psEval f x : E) : Ω) :=
  have := t2Space_of_isValuativeTopology Ω
  (hasSum_psEval_coe E f x hx).tsum_eq

theorem hasSum_psEval' {σ : Type*} [Finite σ] (f : MvPowerSeries σ 𝒪[K]) (x : σ → Ω)
    (hx : ∀ i, valuation Ω (x i) < 1) :
    HasSum (psTerm f x) (psEval f x) := by
  let E := IntermediateField.adjoin K (Set.range x)
  have := finiteDimensional_adjoin_range (K := K) x
  let xE : σ → E := fun i => ⟨x i, IntermediateField.subset_adjoin K _ ⟨i, rfl⟩⟩
  have h := hasSum_psEval_coe E f xE hx
  rwa [← psEval_coe E f xE hx] at h

theorem psEval_mem {σ : Type*} [Finite σ] (f : MvPowerSeries σ 𝒪[K]) (E : IntermediateField K Ω)
    [FiniteDimensional K E] {x : σ → Ω} (hxE : ∀ i, x i ∈ E) (hx : ∀ i, valuation Ω (x i) < 1) :
    psEval f x ∈ E := by
  have h := psEval_coe E f (fun i => ⟨x i, hxE i⟩) hx
  change psEval f x = _ at h
  rw [h]
  exact SetLike.coe_mem _

theorem valuation_psEval_lt_one' {σ : Type*} [Finite σ] {f : MvPowerSeries σ 𝒪[K]}
    (hf : constantCoeff f = 0) (x : σ → Ω) (hx : ∀ i, valuation Ω (x i) < 1) :
    valuation Ω (psEval f x) < 1 := by
  let E := IntermediateField.adjoin K (Set.range x)
  have := finiteDimensional_adjoin_range (K := K) x
  let xE : σ → E := fun i => ⟨x i, IntermediateField.subset_adjoin K _ ⟨i, rfl⟩⟩
  let a : σ → 𝒪[E] := fun i => ⟨xE i, ((valuation_coe_lt_one_iff E (xE i)).mp (hx i)).le⟩
  have ha : ∀ i, a i ∈ 𝓂[E] := fun i =>
    mem_maximalIdeal_integer_iff.mpr ((valuation_coe_lt_one_iff E (xE i)).mp (hx i))
  have h := psEval_coe E f xE hx
  change psEval f x = _ at h
  rw [h, valuation_coe_lt_one_iff]
  exact valuation_psEval_lt_one hf a ha

theorem psEval_subst' {σ τ : Type*} [Finite σ] [Finite τ] {g : σ → MvPowerSeries τ 𝒪[K]}
    (hg : ∀ s, constantCoeff (g s) = 0) (f : MvPowerSeries σ 𝒪[K]) (x : τ → Ω)
    (hx : ∀ i, valuation Ω (x i) < 1) :
    psEval (subst g f) x = psEval f fun s => psEval (g s) x := by
  let E := IntermediateField.adjoin K (Set.range x)
  have := finiteDimensional_adjoin_range (K := K) x
  let xE : τ → E := fun i => ⟨x i, IntermediateField.subset_adjoin K _ ⟨i, rfl⟩⟩
  let a : τ → 𝒪[E] := fun i => ⟨xE i, ((valuation_coe_lt_one_iff E (xE i)).mp (hx i)).le⟩
  have ha : ∀ i, a i ∈ 𝓂[E] := fun i =>
    mem_maximalIdeal_integer_iff.mpr ((valuation_coe_lt_one_iff E (xE i)).mp (hx i))
  have h1 : psEval (subst g f) x = _ := psEval_coe E (subst g f) xE hx
  have h2 : ∀ s, psEval (g s) x = _ := fun s => psEval_coe E (g s) xE hx
  have hy : ∀ s, valuation Ω ((psEval (g s) xE : E) : Ω) < 1 := fun s => by
    rw [valuation_coe_lt_one_iff]
    exact valuation_psEval_lt_one (hg s) a ha
  have h3 := psEval_coe E f (fun s => psEval (g s) xE) hy
  rw [h1, funext h2, h3, psEval_subst hg f a ha]

theorem algEquiv_psEval (τ : Ω ≃ₐ[K] Ω) {σ : Type*} [Finite σ] (f : MvPowerSeries σ 𝒪[K])
    (x : σ → Ω) (hx : ∀ i, valuation Ω (x i) < 1) :
    τ (psEval f x) = psEval f fun i => τ (x i) :=
  have := t2Space_of_isValuativeTopology Ω
  map_psEval (τ : Ω →ₐ[K] Ω) (continuous_algEquiv_of_isAlgebraic τ) (hasSum_psEval' f x hx)

end Algebraic

section Basic

variable {K : Type*} [Field K] [ValuativeRel K] {σ M : Type*} [CommRing M] [Algebra K M]
  [TopologicalSpace M] [T2Space M]

omit [T2Space M] in

@[simp]
theorem psEval_zero (x : σ → M) : psEval (0 : MvPowerSeries σ 𝒪[K]) x = 0 := by
  simp [psEval, psTerm]

omit [T2Space M] in

@[simp]
theorem psEval_X (x : σ → M) (i : σ) : psEval (X i : MvPowerSeries σ 𝒪[K]) x = x i := by
  classical
  rw [psEval, tsum_eq_single (Finsupp.single i 1)]
  · simp [psTerm, coeff_X]
  · intro d hd
    simp [psTerm, coeff_X, hd]

end Basic

namespace FormalGroup
open RHDirect.CFT.FormalGroups

section Points

variable {K : Type*} [Field K] [ValuativeRel K] {Ω : Type*} [Field Ω] [ValuativeRel Ω]

variable (Ω) in

def IdealPoint (_F : _root_.FormalGroup 𝒪[K]) : Type _ := {x : Ω // valuation Ω x < 1}

variable {F G H : _root_.FormalGroup 𝒪[K]}

namespace IdealPoint

def val (x : IdealPoint Ω F) : Ω := Subtype.val x

theorem valuation_lt_one (x : IdealPoint Ω F) : valuation Ω x.val < 1 := x.2

def mk (x : Ω) (hx : valuation Ω x < 1) : IdealPoint Ω F := ⟨x, hx⟩

@[simp]
theorem val_mk (x : Ω) (hx : valuation Ω x < 1) : (mk x hx : IdealPoint Ω F).val = x := rfl

@[ext]
theorem ext {x y : IdealPoint Ω F} (h : x.val = y.val) : x = y := Subtype.ext h

theorem val_injective : Function.Injective (val : IdealPoint Ω F → Ω) := fun _ _ => ext

end IdealPoint

instance : Zero (IdealPoint Ω F) := ⟨IdealPoint.mk 0 (by simp)⟩

@[simp]
theorem IdealPoint.val_zero : (0 : IdealPoint Ω F).val = 0 := rfl

variable [TopologicalSpace K] [IsNonarchimedeanLocalField K] [TopologicalSpace Ω]
  [IsValuativeTopology Ω] [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω]

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] [TopologicalSpace Ω]
  [IsValuativeTopology Ω] [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω] in
theorem constantCoeff_point_val {σ : Type*} (p : F.Point σ) : constantCoeff p.val = 0 :=
  IsNilpotent.eq_zero p.prop

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] [TopologicalSpace Ω]
  [IsValuativeTopology Ω] [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω] in
theorem constantCoeff_inv_mv : constantCoeff (inv F : MvPowerSeries Unit 𝒪[K]) = 0 :=
  RHDirect.CFT.FormalGroups.constantCoeff_inv F

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] [TopologicalSpace Ω]
  [IsValuativeTopology Ω] [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω] in
theorem fin_two_valuation_lt_one (x y : IdealPoint Ω F) :
    ∀ i, valuation Ω ((![x.val, y.val] : Fin 2 → Ω) i) < 1 := by
  intro i
  fin_cases i
  exacts [x.valuation_lt_one, y.valuation_lt_one]

instance : Add (IdealPoint Ω F) where
  add x y := IdealPoint.mk (psEval F.toPowerSeries ![x.val, y.val])
    (valuation_psEval_lt_one' F.zero_constantCoeff _ (fin_two_valuation_lt_one x y))

instance : Neg (IdealPoint Ω F) where
  neg x := IdealPoint.mk (psEval (inv F : MvPowerSeries Unit 𝒪[K]) fun _ => x.val)
    (valuation_psEval_lt_one' constantCoeff_inv_mv _ fun _ => x.valuation_lt_one)

theorem IdealPoint.val_add (x y : IdealPoint Ω F) :
    (x + y).val = psEval F.toPowerSeries ![x.val, y.val] := rfl

theorem IdealPoint.val_neg (x : IdealPoint Ω F) :
    (-x).val = psEval (inv F : MvPowerSeries Unit 𝒪[K]) fun _ => x.val := rfl

def evalPoint {σ : Type*} [Finite σ] (x : σ → IdealPoint Ω F) (p : F.Point σ) :
    IdealPoint Ω F :=
  IdealPoint.mk (psEval p.val fun i => (x i).val)
    (valuation_psEval_lt_one' (constantCoeff_point_val p) _ fun i => (x i).valuation_lt_one)

theorem evalPoint_val {σ : Type*} [Finite σ] (x : σ → IdealPoint Ω F) (p : F.Point σ) :
    (evalPoint x p).val = psEval p.val fun i => (x i).val := rfl

def pointVar {σ : Type*} (i : σ) : F.Point σ :=
  ⟨X i, by simp [PowerSeries.HasSubst]⟩

theorem evalPoint_pointVar {σ : Type*} [Finite σ] (x : σ → IdealPoint Ω F) (i : σ) :
    evalPoint x (pointVar i) = x i :=
  IdealPoint.ext (psEval_X _ i)

theorem evalPoint_zero {σ : Type*} [Finite σ] (x : σ → IdealPoint Ω F) :
    evalPoint x (0 : F.Point σ) = 0 :=
  IdealPoint.ext (psEval_zero _)

theorem evalPoint_add {σ : Type*} [Finite σ] (x : σ → IdealPoint Ω F) (p q : F.Point σ) :
    evalPoint x (p + q) = evalPoint x p + evalPoint x q := by
  apply IdealPoint.ext
  rw [evalPoint_val, FormalGroup.add_apply, psEval_subst' _ F.toPowerSeries _
    fun i => (x i).valuation_lt_one]
  · rw [IdealPoint.val_add]
    congr 1
    funext i
    fin_cases i <;> rfl
  · intro i
    fin_cases i
    exacts [constantCoeff_point_val p, constantCoeff_point_val q]

theorem evalPoint_neg {σ : Type*} [Finite σ] (x : σ → IdealPoint Ω F) (p : F.Point σ) :
    evalPoint x (-p) = -evalPoint x p := by
  apply IdealPoint.ext
  rw [evalPoint_val, RHDirect.CFT.FormalGroups.neg_point_val, PowerSeries.subst,
    psEval_subst' (fun _ => constantCoeff_point_val p) _ _ fun i => (x i).valuation_lt_one]
  rfl

theorem psEval_apply_val {σ : Type*} [Finite σ] (φ : Hom F G) (p : F.Point σ) (x : σ → Ω)
    (hx : ∀ i, valuation Ω (x i) < 1) :
    psEval (φ.apply p).val x = psEval φ.toPowerSeries fun _ => psEval p.val x := by
  rw [Hom.apply_val, PowerSeries.subst,
    psEval_subst' (fun _ => constantCoeff_point_val p) _ _ hx]

instance instAddGroup : AddGroup (IdealPoint Ω F) where
  add_assoc a b c := by
    have h := congrArg (evalPoint ![a, b, c])
      (add_assoc (pointVar 0 : F.Point (Fin 3)) (pointVar 1) (pointVar 2))
    simpa [evalPoint_add, evalPoint_pointVar] using h
  zero_add a := by
    have h := congrArg (evalPoint fun _ : Unit => a) (zero_add (pointVar () : F.Point Unit))
    simpa only [evalPoint_add, evalPoint_pointVar, evalPoint_zero] using h
  add_zero a := by
    have h := congrArg (evalPoint fun _ : Unit => a) (add_zero (pointVar () : F.Point Unit))
    simpa only [evalPoint_add, evalPoint_pointVar, evalPoint_zero] using h
  neg_add_cancel a := by
    have h := congrArg (evalPoint fun _ : Unit => a) (neg_add_cancel (pointVar () : F.Point Unit))
    simpa only [evalPoint_add, evalPoint_neg, evalPoint_pointVar, evalPoint_zero] using h
  nsmul := nsmulRec
  zsmul := zsmulRec

instance instAddCommGroup [F.IsComm] : AddCommGroup (IdealPoint Ω F) where
  add_comm a b := by
    have h := congrArg (evalPoint ![a, b])
      (add_comm (pointVar 0 : F.Point (Fin 2)) (pointVar 1))
    simpa [evalPoint_add, evalPoint_pointVar] using h

theorem psEval_powerSeries_subst {σ : Type*} [Finite σ] {a : MvPowerSeries σ 𝒪[K]}
    (ha : constantCoeff a = 0) (φ : PowerSeries 𝒪[K]) (x : σ → Ω)
    (hx : ∀ i, valuation Ω (x i) < 1) :
    psEval (PowerSeries.subst a φ) x = psEval φ fun _ => psEval a x := by
  rw [PowerSeries.subst, psEval_subst' (fun _ => ha) _ _ hx]

def _root_.RHDirect.CFT.FormalGroups.Hom.pointMap (φ : Hom F G) : IdealPoint Ω F →+ IdealPoint Ω G :=
  AddMonoidHom.mk' (fun x => IdealPoint.mk (psEval φ.toPowerSeries fun _ => x.val)
      (valuation_psEval_lt_one' φ.constantCoeff_eq_zero' _ fun _ => x.valuation_lt_one))
    fun a b => by
      apply IdealPoint.ext
      simp only [IdealPoint.val_mk, IdealPoint.val_add]
      have hx := fin_two_valuation_lt_one a b
      rw [← psEval_powerSeries_subst F.zero_constantCoeff _ _ hx, φ.map_add,
        psEval_subst' _ _ _ hx]
      · congr 1
        funext i
        fin_cases i
        · simp [psEval_powerSeries_subst (constantCoeff_X 0) _ _ hx]
        · simp [psEval_powerSeries_subst (constantCoeff_X 1) _ _ hx]
      · intro i
        fin_cases i
        · exact PowerSeries.constantCoeff_subst_eq_zero (constantCoeff_X _) _
            φ.constantCoeff_eq_zero
        · exact PowerSeries.constantCoeff_subst_eq_zero (constantCoeff_X _) _
            φ.constantCoeff_eq_zero

theorem _root_.RHDirect.CFT.FormalGroups.Hom.pointMap_val (φ : Hom F G) (x : IdealPoint Ω F) :
    (φ.pointMap x).val = psEval φ.toPowerSeries fun _ => x.val := rfl

theorem _root_.RHDirect.CFT.FormalGroups.Hom.pointMap_comp (g : Hom G H) (f : Hom F G) (x : IdealPoint Ω F) :
    (g.comp f).pointMap x = g.pointMap (f.pointMap x) := by
  apply IdealPoint.ext
  rw [Hom.pointMap_val, Hom.toPowerSeries_comp,
    psEval_powerSeries_subst f.constantCoeff_eq_zero' _ _ fun _ => x.valuation_lt_one]
  rfl

theorem _root_.RHDirect.CFT.FormalGroups.Hom.pointMap_id (x : IdealPoint Ω F) : (Hom.id F).pointMap x = x := by
  apply IdealPoint.ext
  rw [Hom.pointMap_val, Hom.toPowerSeries_id]
  exact psEval_X _ ()

theorem _root_.RHDirect.CFT.FormalGroups.Hom.pointMap_zero (x : IdealPoint Ω F) : (0 : Hom F G).pointMap x = 0 := by
  apply IdealPoint.ext
  rw [Hom.pointMap_val, Hom.toPowerSeries_zero]
  exact psEval_zero _

theorem _root_.RHDirect.CFT.FormalGroups.Hom.pointMap_add [G.IsComm] (f g : Hom F G) (x : IdealPoint Ω F) :
    (f + g).pointMap x = f.pointMap x + g.pointMap x := by
  apply IdealPoint.ext
  rw [Hom.pointMap_val, Hom.toPowerSeries_add, psEval_subst' _ _ _ fun _ => x.valuation_lt_one]
  · rw [IdealPoint.val_add]
    congr 1
    funext i
    fin_cases i <;> rfl
  · intro i
    fin_cases i
    exacts [f.constantCoeff_eq_zero', g.constantCoeff_eq_zero']

variable (Ω F) in

def endPointMap [F.IsComm] : Hom F F →+* AddMonoid.End (IdealPoint Ω F) where
  toFun φ := φ.pointMap
  map_one' := AddMonoidHom.ext fun x => Hom.pointMap_id x
  map_mul' f g := AddMonoidHom.ext fun x => by
    rw [Hom.mul_def, Hom.pointMap_comp]
    rfl
  map_zero' := AddMonoidHom.ext fun x => Hom.pointMap_zero x
  map_add' f g := AddMonoidHom.ext fun x => Hom.pointMap_add f g x

theorem endPointMap_apply [F.IsComm] (φ : Hom F F) (x : IdealPoint Ω F) :
    endPointMap Ω F φ x = φ.pointMap x := rfl

def _root_.RHDirect.CFT.FormalGroups.Iso.pointEquiv (e : Iso F G) : IdealPoint Ω F ≃+ IdealPoint Ω G where
  toFun := e.hom.pointMap
  invFun := e.inv.pointMap
  left_inv x := by
    rw [← Hom.pointMap_comp, e.inv_comp_hom, Hom.pointMap_id]
  right_inv x := by
    rw [← Hom.pointMap_comp, e.hom_comp_inv, Hom.pointMap_id]
  map_add' := map_add _

def galPointMap (τ : Ω ≃ₐ[K] Ω) : IdealPoint Ω F →+ IdealPoint Ω F :=
  AddMonoidHom.mk' (fun x => IdealPoint.mk (τ x.val)
      (by rw [valuation_algEquiv_apply_of_isAlgebraic]; exact x.valuation_lt_one))
    fun a b => by
      apply IdealPoint.ext
      simp only [IdealPoint.val_mk, IdealPoint.val_add]
      rw [algEquiv_psEval τ _ _ (fin_two_valuation_lt_one a b)]
      congr 1
      funext i
      fin_cases i <;> rfl

theorem galPointMap_val (τ : Ω ≃ₐ[K] Ω) (x : IdealPoint Ω F) :
    (galPointMap τ x).val = τ x.val := rfl

theorem galPointMap_pointMap (τ : Ω ≃ₐ[K] Ω) (φ : Hom F G) (x : IdealPoint Ω F) :
    galPointMap τ (φ.pointMap x) = φ.pointMap (galPointMap τ x) := by
  apply IdealPoint.ext
  rw [galPointMap_val, Hom.pointMap_val, algEquiv_psEval τ _ _ fun _ => x.valuation_lt_one]
  rfl

end Points

section LubinTate

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω]
variable {π : 𝒪[K]} {hπ : Irreducible π} {f g : PowerSeries 𝒪[K]}

noncomputable instance instModuleLubinTate {hf : IsLubinTateSeries π f} :
    Module 𝒪[K] (IdealPoint Ω (lubinTateFormalGroup hπ hf)) :=
  Module.compHom _ ((endPointMap Ω _).comp (lubinTateEndRingHom hπ hf))

theorem lubinTate_smul_eq (hf : IsLubinTateSeries π f) (a : 𝒪[K])
    (x : IdealPoint Ω (lubinTateFormalGroup hπ hf)) :
    a • x = (lubinTateHom hπ hf hf a).pointMap x := rfl

theorem lubinTate_smul_val (hf : IsLubinTateSeries π f) (a : 𝒪[K])
    (x : IdealPoint Ω (lubinTateFormalGroup hπ hf)) :
    (a • x).val = psEval (lubinTateHom hπ hf hf a).toPowerSeries fun _ => x.val := rfl

theorem lubinTate_uniformizer_smul_val (hf : IsLubinTateSeries π f)
    (x : IdealPoint Ω (lubinTateFormalGroup hπ hf)) :
    (π • x).val = psEval f fun _ => x.val := by
  rw [lubinTate_smul_val, lubinTateHom_self_uniformizer]

noncomputable def lubinTatePointEquiv (hf : IsLubinTateSeries π f) (hg : IsLubinTateSeries π g) :
    IdealPoint Ω (lubinTateFormalGroup hπ hg) ≃ₗ[𝒪[K]] IdealPoint Ω (lubinTateFormalGroup hπ hf) :=
  { (lubinTateIso hπ hf hg 1).pointEquiv with
    map_smul' a x := by
      change (lubinTateHom hπ hf hg 1).pointMap ((lubinTateHom hπ hg hg a).pointMap x) =
        (lubinTateHom hπ hf hf a).pointMap ((lubinTateHom hπ hf hg 1).pointMap x)
      rw [← Hom.pointMap_comp, ← Hom.pointMap_comp, ← lubinTateHom_mul hπ hf hg hg,
        ← lubinTateHom_mul hπ hf hf hg, one_mul, mul_one] }

theorem lubinTatePointEquiv_val (hf : IsLubinTateSeries π f) (hg : IsLubinTateSeries π g)
    (x : IdealPoint Ω (lubinTateFormalGroup hπ hg)) :
    (lubinTatePointEquiv hf hg x).val =
      psEval (lubinTateHom hπ hf hg 1).toPowerSeries fun _ => x.val := rfl

noncomputable def lubinTateGalPointMap (hf : IsLubinTateSeries π f) (τ : Ω ≃ₐ[K] Ω) :
    IdealPoint Ω (lubinTateFormalGroup hπ hf) →ₗ[𝒪[K]] IdealPoint Ω (lubinTateFormalGroup hπ hf) :=
  { galPointMap τ with
    map_smul' a x := galPointMap_pointMap τ (lubinTateHom hπ hf hf a) x }

theorem lubinTateGalPointMap_val (hf : IsLubinTateSeries π f) (τ : Ω ≃ₐ[K] Ω)
    (x : IdealPoint Ω (lubinTateFormalGroup hπ hf)) :
    (lubinTateGalPointMap hf τ x).val = τ x.val := rfl

variable (Ω) in

noncomputable def lubinTateTorsion (hf : IsLubinTateSeries π f) (n : ℕ) :
    Submodule 𝒪[K] (IdealPoint Ω (lubinTateFormalGroup hπ hf)) :=
  Submodule.torsionBy 𝒪[K] _ (π ^ n)

theorem mem_lubinTateTorsion (hf : IsLubinTateSeries π f) (n : ℕ)
    (x : IdealPoint Ω (lubinTateFormalGroup hπ hf)) :
    x ∈ lubinTateTorsion Ω hf n ↔ π ^ n • x = 0 :=
  Submodule.mem_torsionBy_iff _ _

end LubinTate

end FormalGroup

end RHDirect.CFT.LocalField
end Sec_LubinTatePoints


/-! ### LubinTateTorsion -/
section Sec_LubinTateTorsion


namespace RHDirect.CFT.LocalField

open ValuativeRel Polynomial

namespace FormalGroup
open RHDirect.CFT.FormalGroups

section Poly

variable {K : Type*} [Field K] [ValuativeRel K]

theorem psEval_polynomial {M : Type*} [CommRing M] [Algebra K M] [TopologicalSpace M]
    [T2Space M] (p : 𝒪[K][X]) (x : M) :
    psEval (p : PowerSeries 𝒪[K]) (fun _ => x) = aeval x (p.map (algebraMap 𝒪[K] K)) := by
  classical
  let e : (Unit →₀ ℕ) ≃ ℕ := Finsupp.equivFunOnFinite.trans (Equiv.funUnique Unit ℕ)
  have hterm : ∀ d : Unit →₀ ℕ, psTerm (p : PowerSeries 𝒪[K]) (fun _ => x) d =
      algebraMap K M (p.coeff (e d)) * x ^ (e d) := by
    intro d
    have hd : d = Finsupp.single () (e d) := by
      ext
      simp [e]
    rw [psTerm, hd]
    simp only [Finsupp.prod_single_index, pow_zero, e]
    congr 2
    simp [Finsupp.equivFunOnFinite, Equiv.funUnique]
  rw [psEval, ← e.symm.tsum_eq]
  simp only [hterm, Equiv.apply_symm_apply]
  rw [tsum_eq_sum (s := p.support) fun n hn => by simp [Polynomial.notMem_support_iff.mp hn]]
  rw [aeval_def, eval₂_eq_sum, Polynomial.sum_def,
    support_map_of_injective _ (FaithfulSMul.algebraMap_injective 𝒪[K] K)]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [coeff_map, ← IsScalarTower.algebraMap_apply]
  rfl

end Poly

section LTPoly

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

variable (K) in

theorem one_lt_card_residueField' : 1 < Nat.card 𝓀[K] := Finite.one_lt_card

def ltPoly (π : 𝒪[K]) : 𝒪[K][X] := C π * X + X ^ Nat.card 𝓀[K]

def ltPolyIter (π : 𝒪[K]) : ℕ → 𝒪[K][X]
  | 0 => X
  | n + 1 => (ltPoly π).comp (ltPolyIter π n)

theorem ltPolyIter_zero (π : 𝒪[K]) : ltPolyIter π 0 = X := rfl

theorem ltPolyIter_succ (π : 𝒪[K]) (n : ℕ) :
    ltPolyIter π (n + 1) = (ltPoly π).comp (ltPolyIter π n) := rfl

theorem coeff_ltPoly_sub (π : 𝒪[K]) (n : ℕ) :
    PowerSeries.coeff n ((ltPoly π : PowerSeries 𝒪[K]) - PowerSeries.X ^ Nat.card 𝓀[K]) =
      (C π * X : 𝒪[K][X]).coeff n := by
  rw [ltPoly, Polynomial.coe_add, Polynomial.coe_pow, Polynomial.coe_X, add_sub_cancel_right,
    Polynomial.coeff_coe]

theorem isLubinTateSeries_ltPoly (π : 𝒪[K]) :
    IsLubinTateSeries π (ltPoly π : PowerSeries 𝒪[K]) where
  constantCoeff_eq_zero := by
    have hq := one_lt_card_residueField' K
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe, ltPoly]
    simp only [coeff_add, coeff_C_mul_X, coeff_X_pow]
    simp
    omega
  coeff_one := by
    have hq := one_lt_card_residueField' K
    rw [Polynomial.coeff_coe, ltPoly]
    simp only [coeff_add, coeff_C_mul_X, coeff_X_pow]
    simp
    omega
  dvd_coeff_sub n := by
    rw [coeff_ltPoly_sub, coeff_C_mul_X]
    split_ifs
    · exact dvd_rfl
    · exact dvd_zero π

theorem ltPoly_monic (π : 𝒪[K]) : (ltPoly π).Monic := by
  have hq := one_lt_card_residueField' K
  rw [ltPoly, add_comm]
  refine monic_X_pow_add ?_
  calc degree (C π * X) ≤ 1 := degree_C_mul_X_le π
    _ < Nat.card 𝓀[K] := by exact_mod_cast hq

theorem natDegree_ltPoly (π : 𝒪[K]) : (ltPoly π).natDegree = Nat.card 𝓀[K] := by
  have hq := one_lt_card_residueField' K
  rw [ltPoly, add_comm, natDegree_add_eq_left_of_degree_lt, natDegree_X_pow]
  rw [degree_X_pow]
  calc degree (C π * X) ≤ 1 := degree_C_mul_X_le π
    _ < Nat.card 𝓀[K] := by exact_mod_cast hq

theorem ltPolyIter_monic (π : 𝒪[K]) (n : ℕ) : (ltPolyIter π n).Monic ∧
    (ltPolyIter π n).natDegree = Nat.card 𝓀[K] ^ n := by
  induction n with
  | zero => exact ⟨monic_X, by simp [ltPolyIter_zero]⟩
  | succ n ih =>
    have hq := one_lt_card_residueField' K
    have hd : (ltPolyIter π n).natDegree ≠ 0 := by
      rw [ih.2]
      exact pow_ne_zero _ (by omega)
    refine ⟨(ltPoly_monic π).comp ih.1 hd, ?_⟩
    rw [ltPolyIter_succ, natDegree_comp, natDegree_ltPoly, ih.2, pow_succ, mul_comm]

end LTPoly

section Valuation

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {L : Type*} [Field L] [ValuativeRel L] [Algebra K L] [ValuativeExtension K L]
variable {π : 𝒪[K]}

omit [ValuativeRel L] [ValuativeExtension K L] in
theorem aeval_ltPoly (z : L) :
    aeval z ((ltPoly π).map (algebraMap 𝒪[K] K)) =
      algebraMap K L (π : K) * z + z ^ Nat.card 𝓀[K] := by
  simp only [ltPoly, Polynomial.map_add, Polynomial.map_mul, map_C, Polynomial.map_X,
    Polynomial.map_pow, map_add, map_mul, aeval_C, aeval_X, map_pow]
  rfl

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
theorem valuation_algebraMap_integer_le_one (c : 𝒪[K]) :
    valuation L (algebraMap K L (c : K)) ≤ 1 :=
  (Valuation.HasExtension.val_map_le_one_iff (valuation K) (valuation L) _).mpr c.2

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
theorem valuation_algebraMap_lt_one_of_irreducible (hπ : Irreducible π) :
    valuation L (algebraMap K L (π : K)) < 1 :=
  (Valuation.HasExtension.val_map_lt_one_iff (valuation K) (valuation L) _).mpr
    (Valuation.Integer.not_isUnit_iff_valuation_lt_one.mp hπ.not_isUnit)

theorem valuation_aeval_ltPoly_lt_one {z : L} (hz : valuation L z < 1) :
    valuation L (aeval z ((ltPoly π).map (algebraMap 𝒪[K] K))) < 1 := by
  have hq := one_lt_card_residueField' K
  rw [aeval_ltPoly]
  refine Valuation.map_add_lt _ ?_ ?_
  · rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' (valuation_algebraMap_integer_le_one π)) hz
  · rw [map_pow]
    exact pow_lt_one₀ zero_le hz (by omega)

theorem valuation_aeval_ltPoly_of_one_le (hπ : Irreducible π) {z : L} (hz : 1 ≤ valuation L z) :
    valuation L (aeval z ((ltPoly π).map (algebraMap 𝒪[K] K))) = valuation L z ^ Nat.card 𝓀[K] := by
  have hq := one_lt_card_residueField' K
  rw [aeval_ltPoly, Valuation.map_add_eq_of_lt_right, map_pow]
  rw [map_mul, map_pow]
  calc valuation L (algebraMap K L (π : K)) * valuation L z < valuation L z :=
        mul_lt_of_lt_one_left (lt_of_lt_of_le zero_lt_one hz)
          (valuation_algebraMap_lt_one_of_irreducible hπ)
    _ ≤ valuation L z ^ Nat.card 𝓀[K] := le_self_pow₀ hz (by omega)

omit [ValuativeRel L] [ValuativeExtension K L] in
theorem aeval_derivative_ltPoly (z : L) :
    aeval z (derivative ((ltPoly π).map (algebraMap 𝒪[K] K))) =
      algebraMap K L (π : K) + (Nat.card 𝓀[K] : L) * z ^ (Nat.card 𝓀[K] - 1) := by
  simp only [ltPoly, Polynomial.map_add, Polynomial.map_mul, map_C, Polynomial.map_X,
    Polynomial.map_pow, derivative_C_mul_X, derivative_X_pow, map_add, aeval_C,
    map_mul, map_pow, aeval_X, map_natCast]
  rfl

theorem exists_card_residueField_eq (hπ : Irreducible π) :
    ∃ c : 𝒪[K], (Nat.card 𝓀[K] : 𝒪[K]) = π * c := by
  have h : (Nat.card 𝓀[K] : 𝒪[K]) ∈ IsLocalRing.maximalIdeal 𝒪[K] := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_natCast]
    have := Fintype.ofFinite 𝓀[K]
    rw [Nat.card_eq_fintype_card]
    exact FiniteField.cast_card_eq_zero 𝓀[K]
  rw [hπ.maximalIdeal_eq, Ideal.mem_span_singleton] at h
  exact h

theorem aeval_derivative_ltPoly_ne_zero (hπ : Irreducible π) {z : L} (hz : valuation L z < 1) :
    aeval z (derivative ((ltPoly π).map (algebraMap 𝒪[K] K))) ≠ 0 := by
  have hq := one_lt_card_residueField' K
  obtain ⟨c, hc⟩ := exists_card_residueField_eq hπ
  have hcL : (Nat.card 𝓀[K] : L) = algebraMap K L (π : K) * algebraMap K L (c : K) := by
    rw [← map_mul, ← Subring.coe_mul, ← hc]
    simp
  rw [aeval_derivative_ltPoly, hcL, mul_assoc, ← mul_one_add]
  refine mul_ne_zero ?_ ?_
  · rw [ne_eq, map_eq_zero_iff _ (algebraMap K L).injective]
    exact fun h => hπ.ne_zero (Subtype.ext h)
  · refine (Valuation.ne_zero_iff (valuation L)).mp ?_
    rw [Valuation.map_one_add_of_lt]
    · exact one_ne_zero
    · rw [map_mul, map_pow]
      exact lt_of_le_of_lt (mul_le_of_le_one_left' (valuation_algebraMap_integer_le_one c))
        (pow_lt_one₀ zero_le hz (by omega))

theorem valuation_aeval_ltPolyIter_lt_one (n : ℕ) {z : L}
    (hz : valuation L z < 1) :
    valuation L (aeval z ((ltPolyIter π n).map (algebraMap 𝒪[K] K))) < 1 := by
  induction n with
  | zero => simpa [ltPolyIter_zero] using hz
  | succ n ih =>
    rw [ltPolyIter_succ, Polynomial.map_comp, aeval_comp]
    exact valuation_aeval_ltPoly_lt_one ih

theorem one_le_valuation_aeval_ltPolyIter (hπ : Irreducible π) (n : ℕ) {z : L}
    (hz : 1 ≤ valuation L z) :
    1 ≤ valuation L (aeval z ((ltPolyIter π n).map (algebraMap 𝒪[K] K))) := by
  induction n with
  | zero => simpa [ltPolyIter_zero] using hz
  | succ n ih =>
    rw [ltPolyIter_succ, Polynomial.map_comp, aeval_comp, valuation_aeval_ltPoly_of_one_le hπ ih]
    exact one_le_pow₀ ih

theorem valuation_lt_one_of_aeval_ltPolyIter_eq_zero (hπ : Irreducible π) (n : ℕ) {z : L}
    (hz : aeval z ((ltPolyIter π n).map (algebraMap 𝒪[K] K)) = 0) : valuation L z < 1 := by
  by_contra h
  have := one_le_valuation_aeval_ltPolyIter hπ n (not_lt.mp h)
  rw [hz, map_zero] at this
  exact not_le.mpr zero_lt_one this

theorem aeval_derivative_ltPolyIter_ne_zero (hπ : Irreducible π) (n : ℕ) {z : L}
    (hz : valuation L z < 1) :
    aeval z (derivative ((ltPolyIter π n).map (algebraMap 𝒪[K] K))) ≠ 0 := by
  induction n with
  | zero => simp [ltPolyIter_zero]
  | succ n ih =>
    rw [ltPolyIter_succ, Polynomial.map_comp, derivative_comp, map_mul, aeval_comp]
    exact mul_ne_zero ih
      (aeval_derivative_ltPoly_ne_zero hπ (valuation_aeval_ltPolyIter_lt_one n hz))

end Valuation

section Separable

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {π : 𝒪[K]}

theorem separable_ltPolyIter (hπ : Irreducible π) (n : ℕ) :
    ((ltPolyIter π n).map (algebraMap 𝒪[K] K)).Separable := by
  rw [separable_def]
  let _ := algebraicValuativeRel K (AlgebraicClosure K)
  have _ := algebraicValuativeRel_valuativeExtension K (AlgebraicClosure K)
  refine (isCoprime_iff_aeval_ne_zero_of_isAlgClosed K (AlgebraicClosure K) _ _).mpr fun a => ?_
  by_cases ha : valuation (AlgebraicClosure K) a < 1
  · exact Or.inr (aeval_derivative_ltPolyIter_ne_zero hπ n ha)
  · exact Or.inl fun h => ha (valuation_lt_one_of_aeval_ltPolyIter_eq_zero hπ n h)

end Separable

section Module

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {π : 𝒪[K]}

theorem card_quotient_span_pow (hπ : Irreducible π) (n : ℕ) :
    Nat.card (𝒪[K] ⧸ Ideal.span {π ^ n}) = Nat.card 𝓀[K] ^ n := by
  have h : Ideal.span {π ^ n} = IsLocalRing.maximalIdeal 𝒪[K] ^ n := by
    rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow]
  rw [h, ← Submodule.cardQuot_apply, cardQuot_pow_of_prime
    (IsDiscreteValuationRing.not_a_field 𝒪[K]), Submodule.cardQuot_apply]
  rfl

variable {M : Type*} [AddCommGroup M] [Module 𝒪[K] M]

theorem exists_generator_torsionBy (hπ : Irreducible π)
    (hcard : ∀ k, Nat.card (Submodule.torsionBy 𝒪[K] M (π ^ k)) = Nat.card 𝓀[K] ^ k) (n : ℕ) :
    ∃ l : M, l ∈ Submodule.torsionBy 𝒪[K] M (π ^ n) ∧
      (∀ a : 𝒪[K], a • l = 0 ↔ a ∈ Ideal.span {π ^ n}) ∧
      ∀ m ∈ Submodule.torsionBy 𝒪[K] M (π ^ n), ∃ a : 𝒪[K], a • l = m := by
  cases n with
  | zero =>
    refine ⟨0, Submodule.zero_mem _, fun a => by simp, fun m hm => ⟨0, ?_⟩⟩
    rw [Submodule.mem_torsionBy_iff, pow_zero, one_smul] at hm
    rw [hm, smul_zero]
  | succ m =>
    have hq := one_lt_card_residueField' K
    set T := Submodule.torsionBy 𝒪[K] M (π ^ (m + 1))
    have hle : Submodule.torsionBy 𝒪[K] M (π ^ m) ≤ T :=
      Submodule.torsionBy_le_torsionBy_of_dvd _ _ (pow_dvd_pow π m.le_succ)
    have hfin : Finite T := Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
    obtain ⟨l, hlT, hlm⟩ : ∃ l ∈ T, l ∉ Submodule.torsionBy 𝒪[K] M (π ^ m) := by
      by_contra! h
      have heq : T = Submodule.torsionBy 𝒪[K] M (π ^ m) := le_antisymm h hle
      have := hcard (m + 1)
      change Nat.card T = _ at this
      rw [heq, hcard m] at this
      exact absurd this (Nat.pow_lt_pow_right hq m.lt_succ_self).ne
    have hann : ∀ a : 𝒪[K], a • l = 0 ↔ a ∈ Ideal.span {π ^ (m + 1)} := by
      intro a
      constructor
      · intro ha
        by_cases ha0 : a = 0
        · rw [ha0]
          exact Ideal.zero_mem _
        obtain ⟨k, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha0 hπ
        by_cases hk : m + 1 ≤ k
        · rw [Ideal.mem_span_singleton]
          exact Dvd.dvd.mul_left (pow_dvd_pow π hk) _
        · exfalso
          refine hlm ?_
          rw [Submodule.mem_torsionBy_iff]
          have hk' : π ^ k • l = 0 := by
            have : (↑u⁻¹ : 𝒪[K]) • ((↑u * π ^ k) • l) = 0 := by rw [ha, smul_zero]
            rwa [smul_smul, ← mul_assoc, Units.inv_mul, one_mul] at this
          have : π ^ m = π ^ (m - k) * π ^ k := by
            rw [← pow_add]
            congr 1
            omega
          rw [this, mul_smul, hk', smul_zero]
      · intro ha
        obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
        rw [mul_smul, (Submodule.mem_torsionBy_iff _ _).mp hlT, smul_zero]
    refine ⟨l, hlT, hann, fun x hx => ?_⟩
    let ψ : 𝒪[K] →ₗ[𝒪[K]] T :=
      (LinearMap.toSpanSingleton 𝒪[K] M l).codRestrict T fun a => T.smul_mem a hlT
    have hker : LinearMap.ker ψ = Ideal.span {π ^ (m + 1)} := by
      ext a
      rw [LinearMap.mem_ker, ← hann a]
      exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
    have hcardr : Nat.card (LinearMap.range ψ) = Nat.card T := by
      rw [← Nat.card_congr (LinearMap.quotKerEquivRange ψ).toEquiv, hker,
        card_quotient_span_pow hπ, hcard]
    have hbij := (Subtype.val_injective : Function.Injective
      (Subtype.val : LinearMap.range ψ → T)).bijective_of_nat_card_le hcardr.ge
    obtain ⟨⟨_, ⟨a, rfl⟩⟩, hr⟩ := hbij.2 ⟨x, hx⟩
    exact ⟨a, congrArg Subtype.val hr⟩

end Module

section Torsion

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω]
variable {π : 𝒪[K]} {hπ : Irreducible π}

theorem ltPoly_pow_smul_val (n : ℕ)
    (x : IdealPoint Ω (lubinTateFormalGroup hπ (isLubinTateSeries_ltPoly π))) :
    (π ^ n • x).val = aeval x.val ((ltPolyIter π n).map (algebraMap 𝒪[K] K)) := by
  have := t2Space_of_isValuativeTopology Ω
  induction n with
  | zero => simp [ltPolyIter_zero]
  | succ n ih =>
    rw [pow_succ', mul_smul, lubinTate_uniformizer_smul_val, psEval_polynomial, ih,
      ltPolyIter_succ, Polynomial.map_comp, aeval_comp]

theorem mem_lubinTateTorsion_ltPoly_iff (n : ℕ)
    (x : IdealPoint Ω (lubinTateFormalGroup hπ (isLubinTateSeries_ltPoly π))) :
    x ∈ lubinTateTorsion Ω (isLubinTateSeries_ltPoly π) n ↔
      aeval x.val ((ltPolyIter π n).map (algebraMap 𝒪[K] K)) = 0 := by
  rw [mem_lubinTateTorsion, ← ltPoly_pow_smul_val]
  exact ⟨fun h => by rw [h]; rfl, fun h => IdealPoint.ext h⟩

variable [IsSepClosed Ω]

theorem card_lubinTateTorsion_ltPoly (n : ℕ) :
    Nat.card (lubinTateTorsion Ω (hπ := hπ) (isLubinTateSeries_ltPoly π) n) =
      Nat.card 𝓀[K] ^ n := by
  classical
  set p := (ltPolyIter π n).map (algebraMap 𝒪[K] K)
  have hp0 : p ≠ 0 := ((ltPolyIter_monic π n).1.map _).ne_zero
  have hsep : p.Separable := separable_ltPolyIter hπ n
  have hcard : Fintype.card (p.rootSet Ω) = Nat.card 𝓀[K] ^ n := by
    rw [card_rootSet_eq_natDegree hsep (IsSepClosed.splits_codomain p hsep),
      natDegree_map_eq_of_injective (FaithfulSMul.algebraMap_injective 𝒪[K] K),
      (ltPolyIter_monic π n).2]
  rw [← hcard, ← Nat.card_eq_fintype_card]
  refine Nat.card_congr (Equiv.ofBijective (fun x => ⟨x.1.val, ?_⟩) ⟨?_, ?_⟩)
  · rw [mem_rootSet' (p := p)]
    exact ⟨Polynomial.map_ne_zero hp0, (mem_lubinTateTorsion_ltPoly_iff n x.1).mp x.2⟩
  · intro x y h
    exact Subtype.ext (IdealPoint.ext (by simpa using congrArg Subtype.val h))
  · rintro ⟨z, hz⟩
    rw [mem_rootSet' (p := p)] at hz
    refine ⟨⟨IdealPoint.mk z (valuation_lt_one_of_aeval_ltPolyIter_eq_zero hπ n hz.2), ?_⟩, rfl⟩
    exact (mem_lubinTateTorsion_ltPoly_iff n _).mpr hz.2

variable {f : PowerSeries 𝒪[K]}

omit [IsSepClosed Ω] in

theorem lubinTatePointEquiv_mem_torsion_iff {g : PowerSeries 𝒪[K]} (hf : IsLubinTateSeries π f)
    (hg : IsLubinTateSeries π g) (n : ℕ) (x : IdealPoint Ω (lubinTateFormalGroup hπ hg)) :
    lubinTatePointEquiv hf hg x ∈ lubinTateTorsion Ω hf n ↔ x ∈ lubinTateTorsion Ω hg n := by
  rw [mem_lubinTateTorsion, mem_lubinTateTorsion, ← map_smul,
    LinearEquiv.map_eq_zero_iff]

theorem card_lubinTateTorsion (hf : IsLubinTateSeries π f) (n : ℕ) :
    Nat.card (lubinTateTorsion Ω (hπ := hπ) hf n) = Nat.card 𝓀[K] ^ n := by
  rw [← card_lubinTateTorsion_ltPoly (Ω := Ω) (hπ := hπ) n]
  exact Nat.card_congr ((lubinTatePointEquiv hf (isLubinTateSeries_ltPoly π)).toEquiv.subtypeEquiv
    fun x => (lubinTatePointEquiv_mem_torsion_iff hf _ n x).symm).symm

theorem exists_generator_lubinTateTorsion (hf : IsLubinTateSeries π f) (n : ℕ) :
    ∃ l ∈ lubinTateTorsion Ω (hπ := hπ) hf n,
      (∀ a : 𝒪[K], a • l = 0 ↔ a ∈ Ideal.span {π ^ n}) ∧
      ∀ m ∈ lubinTateTorsion Ω (hπ := hπ) hf n, ∃ a : 𝒪[K], a • l = m :=
  exists_generator_torsionBy hπ (card_lubinTateTorsion (hπ := hπ) hf) n

theorem nonempty_linearEquiv_lubinTateTorsion (hf : IsLubinTateSeries π f) (n : ℕ) :
    Nonempty ((𝒪[K] ⧸ Ideal.span {π ^ n}) ≃ₗ[𝒪[K]] lubinTateTorsion Ω (hπ := hπ) hf n) := by
  obtain ⟨l, hl, hann, hgen⟩ := exists_generator_lubinTateTorsion (Ω := Ω) (hπ := hπ) hf n
  let ψ : 𝒪[K] →ₗ[𝒪[K]] lubinTateTorsion Ω (hπ := hπ) hf n :=
    (LinearMap.toSpanSingleton 𝒪[K] _ l).codRestrict _ fun a => Submodule.smul_mem _ a hl
  have hker : LinearMap.ker ψ = Ideal.span {π ^ n} := by
    ext a
    rw [LinearMap.mem_ker, ← hann a]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  have hsurj : Function.Surjective ψ := fun ⟨m, hm⟩ => by
    obtain ⟨a, ha⟩ := hgen m hm
    exact ⟨a, Subtype.ext ha⟩
  exact ⟨(Submodule.quotEquivOfEq _ _ hker.symm).trans (ψ.quotKerEquivOfSurjective hsurj)⟩

end Torsion

section Eisenstein

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {π : 𝒪[K]}

theorem map_residue_ltPolyIter (π : 𝒪[K]) (hπ : Irreducible π) (n : ℕ) :
    (ltPolyIter π n).map (IsLocalRing.residue 𝒪[K]) = X ^ Nat.card 𝓀[K] ^ n := by
  have hres : IsLocalRing.residue 𝒪[K] π = 0 :=
    (IsLocalRing.residue_eq_zero_iff _).mpr ((IsLocalRing.mem_maximalIdeal _).mpr hπ.not_isUnit)
  induction n with
  | zero => simp [ltPolyIter_zero]
  | succ n ih =>
    rw [ltPolyIter_succ, Polynomial.map_comp, ih, ltPoly]
    simp [hres, ← pow_mul, pow_succ]

theorem coeff_zero_ltPolyIter (π : 𝒪[K]) (n : ℕ) : (ltPolyIter π n).coeff 0 = 0 := by
  have hq := one_lt_card_residueField' K
  induction n with
  | zero => simp [ltPolyIter_zero]
  | succ n ih =>
    rw [ltPolyIter_succ, coeff_zero_eq_eval_zero, eval_comp, ← coeff_zero_eq_eval_zero, ih, ltPoly]
    simp
    omega

def ltEisenstein (π : 𝒪[K]) (n : ℕ) : 𝒪[K][X] :=
  C π + ltPolyIter π n ^ (Nat.card 𝓀[K] - 1)

theorem ltEisenstein_monic (π : 𝒪[K]) (n : ℕ) : (ltEisenstein π n).Monic ∧
    (ltEisenstein π n).natDegree = (Nat.card 𝓀[K] - 1) * Nat.card 𝓀[K] ^ n := by
  have hq := one_lt_card_residueField' K
  have hm := (ltPolyIter_monic π n).1.pow (Nat.card 𝓀[K] - 1)
  have hd : (ltPolyIter π n ^ (Nat.card 𝓀[K] - 1)).natDegree =
      (Nat.card 𝓀[K] - 1) * Nat.card 𝓀[K] ^ n := by
    rw [natDegree_pow, (ltPolyIter_monic π n).2]
  have hpos : 0 < (ltPolyIter π n ^ (Nat.card 𝓀[K] - 1)).natDegree := by
    rw [hd]
    exact Nat.mul_pos (by omega) (pow_pos (by omega) n)
  have hlt : degree (C π) < degree (ltPolyIter π n ^ (Nat.card 𝓀[K] - 1)) :=
    lt_of_le_of_lt degree_C_le (by rw [degree_eq_natDegree hm.ne_zero]; exact_mod_cast hpos)
  refine ⟨hm.add_of_right hlt, ?_⟩
  rw [ltEisenstein, natDegree_add_eq_right_of_degree_lt hlt, hd]

theorem map_residue_ltEisenstein (hπ : Irreducible π) (n : ℕ) :
    (ltEisenstein π n).map (IsLocalRing.residue 𝒪[K]) =
      X ^ ((Nat.card 𝓀[K] - 1) * Nat.card 𝓀[K] ^ n) := by
  have hres : IsLocalRing.residue 𝒪[K] π = 0 :=
    (IsLocalRing.residue_eq_zero_iff _).mpr ((IsLocalRing.mem_maximalIdeal _).mpr hπ.not_isUnit)
  rw [ltEisenstein, Polynomial.map_add, map_C, hres, C_0, zero_add, Polynomial.map_pow,
    map_residue_ltPolyIter π hπ, ← pow_mul, mul_comm]

theorem isEisensteinAt_ltEisenstein (hπ : Irreducible π) (n : ℕ) :
    (ltEisenstein π n).IsEisensteinAt (IsLocalRing.maximalIdeal 𝒪[K]) where
  leading := by
    rw [(ltEisenstein_monic π n).1.leadingCoeff]
    exact fun h => (IsLocalRing.maximalIdeal.isMaximal 𝒪[K]).ne_top
      ((Ideal.eq_top_iff_one _).mpr h)
  mem {k} hk := by
    rw [← IsLocalRing.residue_eq_zero_iff, ← coeff_map, map_residue_ltEisenstein hπ, coeff_X_pow]
    rw [(ltEisenstein_monic π n).2] at hk
    simp [hk.ne]
  notMem := by
    have hq := one_lt_card_residueField' K
    have h0 : (ltEisenstein π n).coeff 0 = π := by
      rw [ltEisenstein, coeff_add, coeff_C_zero, coeff_zero_eq_eval_zero, eval_pow,
        ← coeff_zero_eq_eval_zero, coeff_zero_ltPolyIter, zero_pow (by omega), add_zero]
    rw [h0, hπ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    rintro ⟨c, hc⟩
    have : (1 : 𝒪[K]) = π * c := by
      refine mul_left_cancel₀ hπ.ne_zero ?_
      calc π * 1 = π := mul_one π
        _ = π ^ 2 * c := hc
        _ = π * (π * c) := by ring
    exact hπ.not_isUnit (Units.mkOfMulEqOne π c this.symm).isUnit

theorem aeval_ltEisenstein_eq_zero {L : Type*} [Field L] [Algebra K L] {n : ℕ} {z : L}
    (h1 : aeval z ((ltPolyIter π (n + 1)).map (algebraMap 𝒪[K] K)) = 0)
    (h0 : aeval z ((ltPolyIter π n).map (algebraMap 𝒪[K] K)) ≠ 0) :
    aeval z ((ltEisenstein π n).map (algebraMap 𝒪[K] K)) = 0 := by
  have hq := one_lt_card_residueField' K
  set μ := aeval z ((ltPolyIter π n).map (algebraMap 𝒪[K] K))
  rw [ltPolyIter_succ, Polynomial.map_comp, aeval_comp, aeval_ltPoly] at h1
  have h2 : μ * (algebraMap K L (π : K) + μ ^ (Nat.card 𝓀[K] - 1)) = 0 := by
    rw [mul_add, ← pow_succ', Nat.sub_add_cancel hq.le, mul_comm]
    exact h1
  have h3 := (mul_eq_zero.mp h2).resolve_left h0
  rw [ltEisenstein, Polynomial.map_add, map_C, Polynomial.map_pow, map_add, aeval_C, map_pow]
  exact h3

end Eisenstein

end FormalGroup

end RHDirect.CFT.LocalField
end Sec_LubinTateTorsion


/-! ### LubinTateTower -/
section Sec_LubinTateTower


open _root_.IntermediateField

namespace RHDirect.CFT.LocalField

open ValuativeRel Polynomial

namespace FormalGroup
open RHDirect.CFT.FormalGroups

section Tower

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω]
variable {π : 𝒪[K]} {f g : PowerSeries 𝒪[K]}

variable (Ω) in

def lubinTateField (hπ : Irreducible π) (hf : IsLubinTateSeries π f) (n : ℕ) :
    IntermediateField K Ω :=
  adjoin K (IdealPoint.val ''
    (lubinTateTorsion Ω hf n : Set (IdealPoint Ω (lubinTateFormalGroup hπ hf))))

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeRel Ω]
  [TopologicalSpace Ω] [IsValuativeTopology Ω] [ValuativeExtension K Ω] in

theorem finiteDimensional_adjoin_simple (x : Ω) : FiniteDimensional K K⟮x⟯ :=
  adjoin.finiteDimensional (Algebra.IsAlgebraic.isAlgebraic x).isIntegral

theorem val_mem_lubinTateField (hπ : Irreducible π) (hf : IsLubinTateSeries π f) {n : ℕ}
    {x : IdealPoint Ω (lubinTateFormalGroup hπ hf)} (hx : x ∈ lubinTateTorsion Ω hf n) :
    x.val ∈ lubinTateField Ω hπ hf n :=
  subset_adjoin K _ (Set.mem_image_of_mem IdealPoint.val (SetLike.mem_coe.mpr hx))

theorem psEval_mem_adjoin_simple (φ : PowerSeries 𝒪[K]) {x : Ω} (hx : valuation Ω x < 1) :
    psEval φ (fun _ => x) ∈ K⟮x⟯ :=
  have := finiteDimensional_adjoin_simple (K := K) x
  psEval_mem φ K⟮x⟯ (fun _ => mem_adjoin_simple_self K x) fun _ => hx

variable (hπ : Irreducible π)

section SepClosed

variable [IsSepClosed Ω]

theorem exists_lubinTateField_eq_adjoin (hf : IsLubinTateSeries π f) (n : ℕ) :
    ∃ l ∈ lubinTateTorsion Ω (hπ := hπ) hf n,
      (∀ a : 𝒪[K], a • l = 0 ↔ a ∈ Ideal.span {π ^ n}) ∧
      (∀ m ∈ lubinTateTorsion Ω (hπ := hπ) hf n, ∃ a : 𝒪[K], a • l = m) ∧
      lubinTateField Ω hπ hf n = K⟮l.val⟯ := by
  obtain ⟨l, hl, hann, hgen⟩ := exists_generator_lubinTateTorsion (Ω := Ω) (hπ := hπ) hf n
  refine ⟨l, hl, hann, hgen, le_antisymm ?_ ?_⟩
  · rw [lubinTateField, adjoin_le_iff]
    rintro _ ⟨m, hm, rfl⟩
    obtain ⟨a, rfl⟩ := hgen m hm
    rw [lubinTate_smul_val]
    exact psEval_mem_adjoin_simple _ l.valuation_lt_one
  · rw [adjoin_simple_le_iff]
    exact subset_adjoin K _ (Set.mem_image_of_mem IdealPoint.val (SetLike.mem_coe.mpr hl))

instance finiteDimensional_lubinTateField (hf : IsLubinTateSeries π f) (n : ℕ) :
    FiniteDimensional K (lubinTateField Ω hπ hf n) := by
  obtain ⟨l, -, -, -, h⟩ := exists_lubinTateField_eq_adjoin (Ω := Ω) hπ hf n
  rw [h]
  exact finiteDimensional_adjoin_simple _

theorem lubinTateField_eq (hf : IsLubinTateSeries π f) (hg : IsLubinTateSeries π g) (n : ℕ) :
    lubinTateField Ω hπ hf n = lubinTateField Ω hπ hg n := by
  have key : ∀ {f g : PowerSeries 𝒪[K]} (hf : IsLubinTateSeries π f)
      (hg : IsLubinTateSeries π g), lubinTateField Ω hπ hf n ≤ lubinTateField Ω hπ hg n := by
    intro f g hf hg
    rw [lubinTateField, adjoin_le_iff]
    rintro _ ⟨m, hm, rfl⟩
    obtain ⟨m', rfl⟩ := (lubinTatePointEquiv hf hg).surjective m
    have hm' : m' ∈ lubinTateTorsion Ω hg n :=
      (lubinTatePointEquiv_mem_torsion_iff hf hg n m').mp hm
    rw [SetLike.mem_coe, lubinTatePointEquiv_val]
    exact psEval_mem _ _ (fun _ => val_mem_lubinTateField hπ hg hm')
      fun _ => m'.valuation_lt_one
  exact le_antisymm (key hf hg) (key hg hf)

omit [IsSepClosed Ω] in

theorem image_val_lubinTateTorsion_ltPoly (n : ℕ) :
    IdealPoint.val '' (lubinTateTorsion Ω (isLubinTateSeries_ltPoly π) n :
      Set (IdealPoint Ω (lubinTateFormalGroup hπ (isLubinTateSeries_ltPoly π)))) =
      ((ltPolyIter π n).map (algebraMap 𝒪[K] K)).rootSet Ω := by
  have hp0 : (ltPolyIter π n).map (algebraMap 𝒪[K] K) ≠ 0 :=
    ((ltPolyIter_monic π n).1.map _).ne_zero
  ext z
  rw [mem_rootSet']
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨Polynomial.map_ne_zero hp0, (mem_lubinTateTorsion_ltPoly_iff n x).mp hx⟩
  · rintro ⟨-, hz⟩
    exact ⟨IdealPoint.mk z (valuation_lt_one_of_aeval_ltPolyIter_eq_zero hπ n hz),
      (mem_lubinTateTorsion_ltPoly_iff n _).mpr hz, rfl⟩

instance isGalois_lubinTateField (hf : IsLubinTateSeries π f) (n : ℕ) :
    IsGalois K (lubinTateField Ω hπ hf n) := by
  rw [lubinTateField_eq hπ hf (isLubinTateSeries_ltPoly π), lubinTateField,
    image_val_lubinTateTorsion_ltPoly hπ n]
  have hsep := separable_ltPolyIter hπ n
  have := adjoin_rootSet_isSplittingField (IsSepClosed.splits_codomain _ hsep)
    (L := Ω) (K := K)
  exact IsGalois.of_separable_splitting_field hsep

theorem exists_lubinTateField_eq_adjoin_eisenstein (hf : IsLubinTateSeries π f) (n : ℕ) :
    ∃ α : Ω, lubinTateField Ω hπ hf (n + 1) = K⟮α⟯ ∧
      aeval α ((ltEisenstein π n).map (algebraMap 𝒪[K] K)) = 0 := by
  obtain ⟨l, hl, hann, -, hE⟩ :=
    exists_lubinTateField_eq_adjoin (Ω := Ω) hπ (isLubinTateSeries_ltPoly π) (n + 1)
  refine ⟨l.val, (lubinTateField_eq hπ hf (isLubinTateSeries_ltPoly π) _).trans hE, ?_⟩
  refine aeval_ltEisenstein_eq_zero ((mem_lubinTateTorsion_ltPoly_iff _ l).mp hl) fun h => ?_
  have h1 : π ^ n • l = 0 := (mem_lubinTateTorsion _ _ _).mp
    ((mem_lubinTateTorsion_ltPoly_iff n l).mpr h)
  rw [hann, Ideal.mem_span_singleton, pow_dvd_pow_iff hπ.ne_zero hπ.not_isUnit] at h1
  omega

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeRel Ω]
  [TopologicalSpace Ω] [IsValuativeTopology Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω]
  [IsSepClosed Ω] in

theorem adjoin_simple_eq_top_of_eq {E : IntermediateField K Ω} {a : Ω} (hE : E = K⟮a⟯) :
    K⟮(⟨a, hE ▸ mem_adjoin_simple_self K a⟩ : E)⟯ = ⊤ := by
  rw [eq_top_iff]
  rintro y -
  have hy : (y : Ω) ∈ (K⟮(⟨a, hE ▸ mem_adjoin_simple_self K a⟩ : E)⟯).map E.val := by
    rw [adjoin_map, Set.image_singleton]
    change (y : Ω) ∈ K⟮a⟯
    rw [← hE]
    exact y.2
  rw [IntermediateField.mem_map] at hy
  obtain ⟨z, hz, hzy⟩ := hy
  rwa [show z = y from Subtype.ext hzy] at hz

theorem finrank_and_ramificationIndex_lubinTateField_succ (hf : IsLubinTateSeries π f) (n : ℕ) :
    Module.finrank K (lubinTateField Ω hπ hf (n + 1)) = (Nat.card 𝓀[K] - 1) * Nat.card 𝓀[K] ^ n ∧
      ramificationIndex K (lubinTateField Ω hπ hf (n + 1)) =
        (Nat.card 𝓀[K] - 1) * Nat.card 𝓀[K] ^ n := by
  obtain ⟨a, hE, ha⟩ := exists_lubinTateField_eq_adjoin_eisenstein (Ω := Ω) hπ hf n
  set E := lubinTateField Ω hπ hf (n + 1)
  set α : E := ⟨a, hE ▸ mem_adjoin_simple_self K a⟩
  have hgen : K⟮α⟯ = ⊤ := adjoin_simple_eq_top_of_eq hE
  have hα : aeval α (ltEisenstein π n) = 0 := by
    refine Subtype.val_injective ?_
    have h2 := aeval_algHom_apply (E.val.restrictScalars 𝒪[K]) α (ltEisenstein π n)
    simp only [AlgHom.coe_restrictScalars', coe_val] at h2
    rw [ZeroMemClass.coe_zero, ← h2]
    change aeval a (ltEisenstein π n) = 0
    rwa [← aeval_map_algebraMap K]
  have hq := one_lt_card_residueField' K
  have hn : 0 < (ltEisenstein π n).natDegree := by
    rw [(ltEisenstein_monic π n).2]
    exact Nat.mul_pos (by omega) (pow_pos (by omega) n)
  have hEis := isEisensteinAt_ltEisenstein hπ n
  rw [← (ltEisenstein_monic π n).2]
  exact ⟨finrank_eq_natDegree_of_isEisensteinAt hEis hn hα hgen,
    ramificationIndex_eq_natDegree_of_isEisensteinAt hEis hn hα hgen⟩

end SepClosed

end Tower

section Units

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {π : 𝒪[K]}

theorem card_units_quotient_span_pow_succ (hπ : Irreducible π) (n : ℕ) :
    Nat.card (𝒪[K] ⧸ Ideal.span {π ^ (n + 1)})ˣ = (Nat.card 𝓀[K] - 1) * Nat.card 𝓀[K] ^ n := by
  set I := Ideal.span {π ^ (n + 1)}
  have hI : I = 𝓂[K] ^ (n + 1) := by rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow]
  have hIm : I ≤ 𝓂[K] := by
    rw [hI]
    exact Ideal.pow_le_self (Nat.succ_ne_zero n)
  let ψ : 𝒪[K]ˣ →* (𝒪[K] ⧸ I)ˣ := Units.map (Ideal.Quotient.mk I : 𝒪[K] →* 𝒪[K] ⧸ I)
  have hsurj : Function.Surjective ψ := by
    intro w
    obtain ⟨u, hu⟩ := Ideal.Quotient.mk_surjective (w : 𝒪[K] ⧸ I)
    obtain ⟨v, hv⟩ := Ideal.Quotient.mk_surjective (↑w⁻¹ : 𝒪[K] ⧸ I)
    have huv : u * v - 1 ∈ I := by
      rw [← Ideal.Quotient.eq, map_mul, hu, hv, map_one, Units.mul_inv]
    have hunit : IsUnit (u * v) := by
      by_contra h
      have h1 : u * v ∈ 𝓂[K] := (IsLocalRing.mem_maximalIdeal _).mpr h
      have h2 : (1 : 𝒪[K]) ∈ 𝓂[K] := by
        have := Ideal.sub_mem _ h1 (hIm huv)
        rwa [sub_sub_cancel] at this
      exact (IsLocalRing.maximalIdeal.isMaximal 𝒪[K]).ne_top ((Ideal.eq_top_iff_one _).mpr h2)
    refine ⟨(isUnit_of_mul_isUnit_left hunit).unit, Units.ext ?_⟩
    change Ideal.Quotient.mk I u = _
    exact hu
  have hker : ψ.ker = unitFiltration K (n + 1) := by
    ext u
    rw [MonoidHom.mem_ker, mem_unitFiltration, ← hI, ← Ideal.Quotient.eq, Units.ext_iff]
    rfl
  rw [← Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ψ hsurj).toEquiv, hker,
    ← Subgroup.index, index_unitFiltration K (by omega), Nat.add_sub_cancel]

end Units

section Galois

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω]
variable {π : 𝒪[K]} {hπ : Irreducible π} {f : PowerSeries 𝒪[K]}

def galPoint {F : _root_.FormalGroup 𝒪[K]} {E : IntermediateField K Ω} [FiniteDimensional K E]
    (σ : E ≃ₐ[K] E) (x : IdealPoint Ω F) (hx : x.val ∈ E) : IdealPoint Ω F :=
  IdealPoint.mk ((σ ⟨x.val, hx⟩ : E) : Ω) (by
    rw [valuation_coe_lt_one_iff, valuation_algEquiv_apply_of_isAlgebraic,
      ← valuation_coe_lt_one_iff]
    exact x.valuation_lt_one)

omit [TopologicalSpace Ω] [IsValuativeTopology Ω] in

theorem galPoint_val {F : _root_.FormalGroup 𝒪[K]} {E : IntermediateField K Ω}
    [FiniteDimensional K E] (σ : E ≃ₐ[K] E) (x : IdealPoint Ω F) (hx : x.val ∈ E) :
    (galPoint σ x hx).val = ((σ ⟨x.val, hx⟩ : E) : Ω) := rfl

theorem galPoint_smul {E : IntermediateField K Ω} [FiniteDimensional K E] (hf : IsLubinTateSeries π f)
    (σ : E ≃ₐ[K] E) (a : 𝒪[K]) (x : IdealPoint Ω (lubinTateFormalGroup hπ hf)) (hx : x.val ∈ E)
    (hax : (a • x).val ∈ E) :
    galPoint σ (a • x) hax = a • galPoint σ x hx := by
  set xE : E := ⟨x.val, hx⟩
  set φ := (lubinTateHom hπ hf hf a).toPowerSeries
  have hxE : ∀ _ : Unit, valuation Ω ((xE : E) : Ω) < 1 := fun _ => x.valuation_lt_one
  have h1 : (⟨(a • x).val, hax⟩ : E) = psEval φ fun _ => xE :=
    Subtype.ext (psEval_coe E φ (fun _ => xE) hxE)
  have hσ : ∀ _ : Unit, valuation Ω (((σ xE : E)) : Ω) < 1 := fun _ =>
    (galPoint σ x hx).valuation_lt_one
  apply IdealPoint.ext
  rw [galPoint_val, h1, algEquiv_psEval σ φ (fun _ => xE) fun _ => by
      rw [← valuation_coe_lt_one_iff]; exact x.valuation_lt_one,
    lubinTate_smul_val]
  exact (psEval_coe E φ (fun _ => σ xE) hσ).symm

variable [IsSepClosed Ω]

theorem card_units_quotient_eq_finrank (hf : IsLubinTateSeries π f) (n : ℕ) :
    Nat.card (𝒪[K] ⧸ Ideal.span {π ^ n})ˣ = Module.finrank K (lubinTateField Ω hπ hf n) := by
  cases n with
  | zero =>
    obtain ⟨l, hl, -, -, hE⟩ := exists_lubinTateField_eq_adjoin (Ω := Ω) hπ hf 0
    rw [mem_lubinTateTorsion, pow_zero, one_smul] at hl
    rw [hE, hl, IdealPoint.val_zero, adjoin_zero, IntermediateField.finrank_bot, pow_zero,
      Ideal.span_singleton_one]
    have : Subsingleton (𝒪[K] ⧸ (⊤ : Ideal 𝒪[K])) := Ideal.Quotient.subsingleton_iff.mpr rfl
    exact Nat.card_unique
  | succ n =>
    rw [card_units_quotient_span_pow_succ hπ, (finrank_and_ramificationIndex_lubinTateField_succ
      hπ hf n).1]

theorem exists_galEquiv_lubinTateField (hf : IsLubinTateSeries π f) (n : ℕ) :
    ∃ χ : (lubinTateField Ω hπ hf n ≃ₐ[K] lubinTateField Ω hπ hf n) ≃*
        (𝒪[K] ⧸ Ideal.span {π ^ n})ˣ,
      ∀ (σ : lubinTateField Ω hπ hf n ≃ₐ[K] lubinTateField Ω hπ hf n)
        (x : IdealPoint Ω (lubinTateFormalGroup hπ hf)) (hx : x ∈ lubinTateTorsion Ω hf n)
        (a : 𝒪[K]), Ideal.Quotient.mk _ a = (χ σ : 𝒪[K] ⧸ Ideal.span {π ^ n}) →
          ((σ ⟨x.val, val_mem_lubinTateField hπ hf hx⟩ : lubinTateField Ω hπ hf n) : Ω) =
            (a • x).val := by
  obtain ⟨l, hl, hann, hgen, hE⟩ := exists_lubinTateField_eq_adjoin (Ω := Ω) hπ hf n
  set E := lubinTateField Ω hπ hf n
  set Λ := lubinTateTorsion Ω (hπ := hπ) hf n
  set I := Ideal.span {π ^ n}
  have hmem : ∀ {x}, x ∈ Λ → x.val ∈ E := fun hx => val_mem_lubinTateField hπ hf hx
  have hgalΛ : ∀ (σ : E ≃ₐ[K] E) (x) (hx : x ∈ Λ), galPoint σ x (hmem hx) ∈ Λ := by
    intro σ x hx
    rw [mem_lubinTateTorsion, ← galPoint_smul hf σ _ x (hmem hx) (hmem (Λ.smul_mem _ hx))]
    apply IdealPoint.ext
    rw [galPoint_val]
    have h0 : (⟨(π ^ n • x).val, hmem (Λ.smul_mem _ hx)⟩ : E) = 0 :=
      Subtype.ext (show (π ^ n • x).val = ((0 : E) : Ω) by
        rw [(mem_lubinTateTorsion _ _ _).mp hx]; rfl)
    rw [h0, map_zero]
    rfl
  choose c hc using fun σ : E ≃ₐ[K] E => hgen _ (hgalΛ σ l hl)
  have hmk : ∀ a b : 𝒪[K], a • l = b • l ↔ Ideal.Quotient.mk I a = Ideal.Quotient.mk I b := by
    intro a b
    rw [Ideal.Quotient.eq, ← hann, sub_smul, sub_eq_zero]
  have hgal : ∀ (σ : E ≃ₐ[K] E) (x) (hx : x ∈ Λ), galPoint σ x (hmem hx) = c σ • x := by
    intro σ x hx
    obtain ⟨b, rfl⟩ := hgen x hx
    rw [galPoint_smul hf σ b l (hmem hl), ← hc, smul_comm]
  have hmul : ∀ σ τ : E ≃ₐ[K] E, c (σ * τ) • l = (c σ * c τ) • l := by
    intro σ τ
    rw [hc, mul_smul, hc]
    have h1 : galPoint (σ * τ) l (hmem hl) = galPoint σ (galPoint τ l (hmem hl))
        (hmem (hgalΛ τ l hl)) := rfl
    rw [h1, hgal σ _ (hgalΛ τ l hl), ← hc]
  have hone : c 1 • l = (1 : 𝒪[K]) • l := by
    rw [hc, one_smul]
    rfl
  let χ₀ : (E ≃ₐ[K] E) →* 𝒪[K] ⧸ I :=
    { toFun := fun σ => Ideal.Quotient.mk I (c σ)
      map_one' := by rw [(hmk _ _).mp hone, map_one]
      map_mul' := fun σ τ => by rw [(hmk _ _).mp (hmul σ τ), map_mul] }
  let χ := χ₀.toHomUnits
  have hχ : ∀ σ, (χ σ : 𝒪[K] ⧸ I) = Ideal.Quotient.mk I (c σ) := fun σ => rfl
  have hinj : Function.Injective χ := by
    rw [injective_iff_map_eq_one]
    intro σ hσ
    have h1 : c σ • l = (1 : 𝒪[K]) • l := by
      rw [hmk, map_one, ← hχ, hσ, Units.val_one]
    rw [one_smul, hc] at h1
    have hfix : σ ⟨l.val, hmem hl⟩ = ⟨l.val, hmem hl⟩ := Subtype.ext (congrArg IdealPoint.val h1)
    have htop : Algebra.adjoin K {(⟨l.val, hmem hl⟩ : E)} = ⊤ := by
      rw [← adjoin_simple_toSubalgebra_of_isAlgebraic (Algebra.IsAlgebraic.isAlgebraic _),
        adjoin_simple_eq_top_of_eq hE, top_toSubalgebra]
    have h2 := AlgHom.ext_of_adjoin_eq_top htop (φ₁ := (σ : E →ₐ[K] E)) (φ₂ := AlgHom.id K E)
      (by rintro _ rfl; exact hfix)
    exact AlgEquiv.ext fun y => congrArg (fun φ : E →ₐ[K] E => φ y) h2
  have hcard : Nat.card (E ≃ₐ[K] E) = Nat.card (𝒪[K] ⧸ I)ˣ := by
    rw [IsGalois.card_aut_eq_finrank, card_units_quotient_eq_finrank (Ω := Ω) hf n]
  have hfin : Finite (𝒪[K] ⧸ I)ˣ := Nat.finite_of_card_ne_zero (by
    rw [← hcard, IsGalois.card_aut_eq_finrank]
    exact Module.finrank_pos.ne')
  refine ⟨MulEquiv.ofBijective χ (hinj.bijective_of_nat_card_le hcard.ge), ?_⟩
  intro σ x hx a ha
  rw [MulEquiv.ofBijective_apply, hχ, ← hmk] at ha
  obtain ⟨b, rfl⟩ := hgen x hx
  rw [← galPoint_val σ (b • l) (hmem hx), hgal σ _ hx, smul_comm, ← ha, smul_comm]

variable (hπ) in

def lubinTateGalEquiv (hf : IsLubinTateSeries π f) (n : ℕ) :
    (lubinTateField Ω hπ hf n ≃ₐ[K] lubinTateField Ω hπ hf n) ≃* (𝒪[K] ⧸ Ideal.span {π ^ n})ˣ :=
  Classical.choose (exists_galEquiv_lubinTateField (Ω := Ω) (hπ := hπ) hf n)

theorem lubinTateGalEquiv_spec (hf : IsLubinTateSeries π f) (n : ℕ)
    (σ : lubinTateField Ω hπ hf n ≃ₐ[K] lubinTateField Ω hπ hf n)
    (x : IdealPoint Ω (lubinTateFormalGroup hπ hf)) (hx : x ∈ lubinTateTorsion Ω hf n) (a : 𝒪[K])
    (ha : Ideal.Quotient.mk _ a = (lubinTateGalEquiv hπ hf n σ : 𝒪[K] ⧸ Ideal.span {π ^ n})) :
    ((σ ⟨x.val, val_mem_lubinTateField hπ hf hx⟩ : lubinTateField Ω hπ hf n) : Ω) = (a • x).val :=
  Classical.choose_spec (exists_galEquiv_lubinTateField (Ω := Ω) (hπ := hπ) hf n) σ x hx a ha

end Galois

section Main

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω] [IsSepClosed Ω]
variable {π : 𝒪[K]} (hπ : Irreducible π) {f : PowerSeries 𝒪[K]}

theorem finrank_lubinTateField (hf : IsLubinTateSeries π f) {n : ℕ} (hn : 0 < n) :
    Module.finrank K (lubinTateField Ω hπ hf n) = (Nat.card 𝓀[K] - 1) * Nat.card 𝓀[K] ^ (n - 1) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hn.ne'
  exact (finrank_and_ramificationIndex_lubinTateField_succ hπ hf m).1

theorem ramificationIndex_lubinTateField (hf : IsLubinTateSeries π f) {n : ℕ} (hn : 0 < n) :
    ramificationIndex K (lubinTateField Ω hπ hf n) =
      Module.finrank K (lubinTateField Ω hπ hf n) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hn.ne'
  rw [(finrank_and_ramificationIndex_lubinTateField_succ hπ hf m).1,
    (finrank_and_ramificationIndex_lubinTateField_succ hπ hf m).2]

theorem residueDegree_lubinTateField (hf : IsLubinTateSeries π f) {n : ℕ} (hn : 0 < n) :
    residueDegree K (lubinTateField Ω hπ hf n) = 1 :=
  residueDegree_eq_one_of_ramificationIndex_eq_finrank K _
    (ramificationIndex_lubinTateField hπ hf hn)

theorem exists_isEisensteinAt_lubinTateField (hf : IsLubinTateSeries π f) {n : ℕ} (hn : 0 < n) :
    ∃ (p : 𝒪[K][X]) (α : Ω), p.IsEisensteinAt (IsLocalRing.maximalIdeal 𝒪[K]) ∧
      p.natDegree = (Nat.card 𝓀[K] - 1) * Nat.card 𝓀[K] ^ (n - 1) ∧
      aeval α (p.map (algebraMap 𝒪[K] K)) = 0 ∧ lubinTateField Ω hπ hf n = K⟮α⟯ := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hn.ne'
  obtain ⟨α, hE, hα⟩ := exists_lubinTateField_eq_adjoin_eisenstein (Ω := Ω) hπ hf m
  exact ⟨ltEisenstein π m, α, isEisensteinAt_ltEisenstein hπ m, (ltEisenstein_monic π m).2, hα,
    hE⟩

theorem coeff_zero_ltEisenstein (π : 𝒪[K]) (n : ℕ) : (ltEisenstein π n).coeff 0 = π := by
  have hq := one_lt_card_residueField' K
  rw [ltEisenstein, coeff_add, coeff_C_zero, coeff_zero_eq_eval_zero, eval_pow,
    ← coeff_zero_eq_eval_zero, coeff_zero_ltPolyIter, zero_pow (by omega), add_zero]

theorem exists_norm_eq_uniformizer (hf : IsLubinTateSeries π f) {n : ℕ} (hn : 0 < n) :
    ∃ x : lubinTateField Ω hπ hf n, Algebra.norm K x = (π : K) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hn.ne'
  have hfin := (finrank_and_ramificationIndex_lubinTateField_succ (Ω := Ω) hπ hf m).1
  obtain ⟨a, hE, ha⟩ := exists_lubinTateField_eq_adjoin_eisenstein (Ω := Ω) hπ hf m
  rw [hE] at hfin ⊢
  set p := (ltEisenstein π m).map (algebraMap 𝒪[K] K)
  have hpm : p.Monic := (ltEisenstein_monic π m).1.map _
  have hint : IsIntegral K a := (Algebra.IsAlgebraic.isAlgebraic a).isIntegral
  have hmin : minpoly K a = p := by
    refine (Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) hpm
      (minpoly.dvd K a ha) ?_).symm
    rw [← adjoin.finrank hint, hfin, natDegree_map_eq_of_injective
      (FaithfulSMul.algebraMap_injective 𝒪[K] K), (ltEisenstein_monic π m).2]
  set pb := adjoin.powerBasis hint
  have hdim : pb.dim = Module.finrank K K⟮a⟯ := by
    rw [adjoin.powerBasis_dim, adjoin.finrank hint]
  have hnorm : Algebra.norm K pb.gen = (-1) ^ Module.finrank K K⟮a⟯ * (π : K) := by
    rw [Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly, hdim, adjoin.powerBasis_gen,
      minpoly_gen, hmin, coeff_map, coeff_zero_ltEisenstein]
    rfl
  refine ⟨-pb.gen, ?_⟩
  have h1 : (-1 : K⟮a⟯) = algebraMap K K⟮a⟯ (-1) := by simp
  rw [neg_eq_neg_one_mul, h1, map_mul, Algebra.norm_algebraMap,
    hnorm, ← mul_assoc, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_mul]

end Main

section SeparableClosure

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {π : 𝒪[K]} (hπ : Irreducible π) {f : PowerSeries 𝒪[K]} (hf : IsLubinTateSeries π f)

example {n : ℕ} (hn : 0 < n) :
    Module.finrank K (lubinTateField (SeparableClosure K) hπ hf n) =
      (Nat.card 𝓀[K] - 1) * Nat.card 𝓀[K] ^ (n - 1) :=
  finrank_lubinTateField hπ hf hn

example (n : ℕ) : IsGalois K (lubinTateField (SeparableClosure K) hπ hf n) := inferInstance

example (n : ℕ) :
    (lubinTateField (SeparableClosure K) hπ hf n ≃ₐ[K] lubinTateField (SeparableClosure K) hπ hf n)
      ≃* (𝒪[K] ⧸ Ideal.span {π ^ n})ˣ :=
  lubinTateGalEquiv hπ hf n

end SeparableClosure

end FormalGroup

end RHDirect.CFT.LocalField
end Sec_LubinTateTower


/-! ### LubinTatePrimitive -/
section Sec_LubinTatePrimitive


open _root_.IntermediateField

namespace RHDirect.CFT.LocalField

open ValuativeRel Polynomial Topology

namespace FormalGroup
open RHDirect.CFT.FormalGroups

section Associated

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {L : Type*} [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L]

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in

theorem associated_psEval {φ : PowerSeries 𝒪[K]} (h0 : PowerSeries.constantCoeff φ = 0)
    (h1 : IsUnit (PowerSeries.coeff 1 φ)) (a : 𝒪[L]) (ha : a ∈ 𝓂[L]) :
    Associated a ⟨psEval φ (fun _ => (a : L)), psEval_mem_integer φ (fun _ => a) fun _ => ha⟩ := by
  let _ : UniformSpace L := IsTopologicalAddGroup.rightUniformSpace L
  have _ : IsUniformAddGroup L := isUniformAddGroup_of_addCommGroup
  let _ : UniformSpace 𝒪[K] := ⊥
  have _ : DiscreteUniformity 𝒪[K] := ⟨rfl⟩
  have hφc : Continuous[(⊥ : UniformSpace 𝒪[K]).toTopologicalSpace, _]
      (algebraMap 𝒪[K] 𝒪[L]) := by
    rw [UniformSpace.toTopologicalSpace_bot]
    exact continuous_bot
  have hev := hasEval_of_mem_maximalIdeal (a := fun _ : Unit => a) fun _ => ha
  set ε := MvPowerSeries.eval₂Hom hφc hev
  have hval : (⟨psEval φ (fun _ => (a : L)), psEval_mem_integer φ (fun _ => a) fun _ => ha⟩ : 𝒪[L])
      = ε φ := by
    apply Subtype.ext
    rw [MvPowerSeries.coe_eval₂Hom]
    exact psEval_eq_eval₂ φ (fun _ => a) fun _ => ha
  have hεX : ε PowerSeries.X = a := by
    rw [MvPowerSeries.coe_eval₂Hom]
    exact MvPowerSeries.eval₂_X _ _ _
  have hεC : ∀ c : 𝒪[K], ε (PowerSeries.C c) = algebraMap 𝒪[K] 𝒪[L] c := by
    intro c
    rw [MvPowerSeries.coe_eval₂Hom]
    exact MvPowerSeries.eval₂_C _ _ _
  obtain ⟨ψ, hψ⟩ := PowerSeries.X_dvd_iff.mpr h0
  set c := PowerSeries.constantCoeff ψ
  have hc : c = PowerSeries.coeff 1 φ := by
    rw [hψ, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_zero_eq_constantCoeff_apply]
  obtain ⟨χ, hχ⟩ := PowerSeries.X_dvd_iff.mpr
    (show PowerSeries.constantCoeff (ψ - PowerSeries.C c) = 0 by simp [c])
  have hψ' : ψ = PowerSeries.C c + PowerSeries.X * χ := by
    rw [← hχ]
    ring
  have hunit : IsUnit (ε ψ) := by
    rw [hψ', map_add, map_mul, hεX, hεC]
    by_contra hnu
    have hm : algebraMap 𝒪[K] 𝒪[L] c + a * ε χ ∈ 𝓂[L] := (IsLocalRing.mem_maximalIdeal _).mpr hnu
    have hm' : algebraMap 𝒪[K] 𝒪[L] c ∈ 𝓂[L] := by
      have := Ideal.sub_mem _ hm (Ideal.mul_mem_right (ε χ) _ ha)
      rwa [add_sub_cancel_right] at this
    rw [hc] at hm'
    exact (IsLocalRing.mem_maximalIdeal _).mp hm' (h1.map _)
  rw [hval, hψ, map_mul, hεX]
  exact ⟨hunit.unit, rfl⟩

end Associated

section Torsion

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω]
variable {π : 𝒪[K]} (hπ : Irreducible π) {f g : PowerSeries 𝒪[K]}

theorem lubinTateTorsion_mono (hf : IsLubinTateSeries π f) {m n : ℕ} (h : m ≤ n) :
    lubinTateTorsion Ω (hπ := hπ) hf m ≤ lubinTateTorsion Ω (hπ := hπ) hf n :=
  Submodule.torsionBy_le_torsionBy_of_dvd _ _ (pow_dvd_pow π h)

theorem lubinTateField_mono (hf : IsLubinTateSeries π f) {m n : ℕ} (h : m ≤ n) :
    lubinTateField Ω hπ hf m ≤ lubinTateField Ω hπ hf n := by
  rw [lubinTateField, adjoin_le_iff]
  rintro _ ⟨x, hx, rfl⟩
  exact val_mem_lubinTateField hπ hf (lubinTateTorsion_mono hπ hf h hx)

theorem lubinTateField_le_succ (hf : IsLubinTateSeries π f) (n : ℕ) :
    lubinTateField Ω hπ hf n ≤ lubinTateField Ω hπ hf (n + 1) :=
  lubinTateField_mono hπ hf n.le_succ

theorem lubinTatePointEquiv_primitive_iff (hf : IsLubinTateSeries π f) (hg : IsLubinTateSeries π g)
    (n : ℕ) (x : IdealPoint Ω (lubinTateFormalGroup hπ hg)) :
    (lubinTatePointEquiv hf hg x ∈ lubinTateTorsion Ω hf n ∧
        lubinTatePointEquiv hf hg x ∉ lubinTateTorsion Ω hf (n - 1)) ↔
      (x ∈ lubinTateTorsion Ω hg n ∧ x ∉ lubinTateTorsion Ω hg (n - 1)) := by
  rw [lubinTatePointEquiv_mem_torsion_iff, lubinTatePointEquiv_mem_torsion_iff]

theorem aeval_ltEisenstein_of_primitive {k : ℕ}
    {l : IdealPoint Ω (lubinTateFormalGroup hπ (isLubinTateSeries_ltPoly π))}
    (hl : l ∈ lubinTateTorsion Ω (isLubinTateSeries_ltPoly π) (k + 1))
    (hl' : l ∉ lubinTateTorsion Ω (isLubinTateSeries_ltPoly π) k) :
    aeval l.val ((ltEisenstein π k).map (algebraMap 𝒪[K] K)) = 0 :=
  aeval_ltEisenstein_eq_zero ((mem_lubinTateTorsion_ltPoly_iff _ l).mp hl)
    fun h => hl' ((mem_lubinTateTorsion_ltPoly_iff k l).mpr h)

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [TopologicalSpace Ω]
  [IsValuativeTopology Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω] in

theorem exists_integer_eq {E : IntermediateField K Ω} {x : Ω} (hxE : x ∈ E)
    (hx : valuation Ω x < 1) : ∃ y : 𝒪[E], ((y : E) : Ω) = x :=
  ⟨⟨⟨x, hxE⟩, ((valuation_coe_lt_one_iff E ⟨x, hxE⟩).mp hx).le⟩, rfl⟩

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeRel Ω] [TopologicalSpace Ω]
  [IsValuativeTopology Ω] [ValuativeExtension K Ω] in

theorem norm_neg_eq_coeff_zero {E : IntermediateField K Ω} {a : Ω} (hE : E = K⟮a⟯) (ha : a ∈ E)
    {p : 𝒪[K][X]} (hpm : p.Monic) (hfin : Module.finrank K E = p.natDegree)
    (hp : aeval a (p.map (algebraMap 𝒪[K] K)) = 0) :
    Algebra.norm K (-(⟨a, ha⟩ : E)) = ((p.coeff 0 : 𝒪[K]) : K) := by
  subst hE
  have hint : IsIntegral K a := (Algebra.IsAlgebraic.isAlgebraic a).isIntegral
  have hqm : (p.map (algebraMap 𝒪[K] K)).Monic := hpm.map _
  have hmin : minpoly K a = p.map (algebraMap 𝒪[K] K) := by
    refine (Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) hqm
      (minpoly.dvd K a hp) ?_).symm
    rw [← adjoin.finrank hint, hfin, natDegree_map_eq_of_injective
      (FaithfulSMul.algebraMap_injective 𝒪[K] K)]
  set pb := adjoin.powerBasis hint
  have hgen : (⟨a, ha⟩ : K⟮a⟯) = pb.gen := by
    rw [adjoin.powerBasis_gen]
    rfl
  have hdim : pb.dim = Module.finrank K K⟮a⟯ := by
    rw [adjoin.powerBasis_dim, adjoin.finrank hint]
  have hnorm : Algebra.norm K pb.gen =
      (-1) ^ Module.finrank K K⟮a⟯ * ((p.coeff 0 : 𝒪[K]) : K) := by
    rw [Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly, hdim, adjoin.powerBasis_gen,
      minpoly_gen, hmin, coeff_map]
    rfl
  rw [hgen]
  have h1 : (-1 : K⟮a⟯) = algebraMap K K⟮a⟯ (-1) := by simp
  rw [neg_eq_neg_one_mul, h1, map_mul, Algebra.norm_algebraMap,
    hnorm, ← mul_assoc, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_mul]

theorem irreducible_of_eq_adjoin_of_isEisensteinAt {E : IntermediateField K Ω} [FiniteDimensional K E]
    {a : Ω} (hE : E = K⟮a⟯) {p : 𝒪[K][X]} (hp : p.IsEisensteinAt (IsLocalRing.maximalIdeal 𝒪[K]))
    (hn : 0 < p.natDegree) (ha : aeval a (p.map (algebraMap 𝒪[K] K)) = 0) {x : 𝒪[E]}
    (hx : ((x : E) : Ω) = a) : Irreducible x := by
  have haE : a ∈ E := hx ▸ (x : E).2
  set α : E := ⟨a, haE⟩
  have hgen : K⟮α⟯ = ⊤ := adjoin_simple_eq_top_of_eq hE
  have hα : aeval α p = 0 := by
    refine Subtype.val_injective ?_
    have h2 := aeval_algHom_apply (E.val.restrictScalars 𝒪[K]) α p
    simp only [AlgHom.coe_restrictScalars', coe_val] at h2
    rw [ZeroMemClass.coe_zero, ← h2]
    change aeval a p = 0
    rwa [← aeval_map_algebraMap K]
  have := irreducible_of_isEisensteinAt_root hp hn hα hgen
  convert this
  exact Subtype.ext hx

variable [IsSepClosed Ω]

theorem val_mem_lubinTateField_of_mem (hf : IsLubinTateSeries π f) (hg : IsLubinTateSeries π g)
    {n : ℕ} {x : IdealPoint Ω (lubinTateFormalGroup hπ hg)} (hx : x ∈ lubinTateTorsion Ω hg n) :
    x.val ∈ lubinTateField Ω hπ hf n :=
  lubinTateField_eq (Ω := Ω) hπ hg hf n ▸ val_mem_lubinTateField hπ hg hx

theorem primitive_spec (hf : IsLubinTateSeries π f) {n : ℕ}
    {l : IdealPoint Ω (lubinTateFormalGroup hπ hf)} (hl : l ∈ lubinTateTorsion Ω hf n)
    (hl' : l ∉ lubinTateTorsion Ω hf (n - 1)) :
    (∀ a : 𝒪[K], a • l = 0 ↔ a ∈ Ideal.span {π ^ n}) ∧
      ∀ m ∈ lubinTateTorsion Ω (hπ := hπ) hf n, ∃ a : 𝒪[K], a • l = m := by
  obtain ⟨l₀, -, hann, hgen⟩ := exists_generator_lubinTateTorsion (Ω := Ω) (hπ := hπ) hf n
  obtain ⟨b, rfl⟩ := hgen l hl
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := by
    cases n with
    | zero => exact absurd hl hl'
    | succ k => exact ⟨k, rfl⟩
  have hb : IsUnit b := by
    by_contra hb
    apply hl'
    have hmem := (IsLocalRing.mem_maximalIdeal b).mpr hb
    rw [hπ.maximalIdeal_eq, Ideal.mem_span_singleton] at hmem
    obtain ⟨c, rfl⟩ := hmem
    rw [Nat.add_sub_cancel, mem_lubinTateTorsion, smul_smul, (hann _).mpr]
    exact Ideal.mem_span_singleton.mpr ⟨c, by ring⟩
  obtain ⟨u, rfl⟩ := hb
  refine ⟨fun a => ?_, fun m hm => ?_⟩
  · rw [smul_smul, hann]
    exact Ideal.mul_unit_mem_iff_mem _ u.isUnit
  · obtain ⟨a, rfl⟩ := hgen m hm
    exact ⟨a * ↑u⁻¹, by rw [smul_smul, mul_assoc, Units.inv_mul, mul_one]⟩

theorem exists_primitive (hf : IsLubinTateSeries π f) {n : ℕ} (hn : 0 < n) :
    ∃ l ∈ lubinTateTorsion Ω (hπ := hπ) hf n, l ∉ lubinTateTorsion Ω (hπ := hπ) hf (n - 1) := by
  obtain ⟨l, hl, hann, -⟩ := exists_generator_lubinTateTorsion (Ω := Ω) (hπ := hπ) hf n
  refine ⟨l, hl, fun h => ?_⟩
  rw [mem_lubinTateTorsion, hann, Ideal.mem_span_singleton,
    pow_dvd_pow_iff hπ.ne_zero hπ.not_isUnit] at h
  omega

theorem lubinTateField_eq_adjoin_of_primitive (hf : IsLubinTateSeries π f) {n : ℕ}
    {l : IdealPoint Ω (lubinTateFormalGroup hπ hf)} (hl : l ∈ lubinTateTorsion Ω hf n)
    (hl' : l ∉ lubinTateTorsion Ω hf (n - 1)) :
    lubinTateField Ω hπ hf n = K⟮l.val⟯ := by
  obtain ⟨-, hgen⟩ := primitive_spec hπ hf hl hl'
  refine le_antisymm ?_ ?_
  · rw [lubinTateField, adjoin_le_iff]
    rintro _ ⟨m, hm, rfl⟩
    obtain ⟨a, rfl⟩ := hgen m hm
    rw [lubinTate_smul_val]
    exact psEval_mem_adjoin_simple _ l.valuation_lt_one
  · rw [adjoin_simple_le_iff]
    exact val_mem_lubinTateField hπ hf hl

theorem irreducible_of_primitive_ltPoly (hf : IsLubinTateSeries π f) {n : ℕ}
    {l : IdealPoint Ω (lubinTateFormalGroup hπ (isLubinTateSeries_ltPoly π))}
    (hl : l ∈ lubinTateTorsion Ω (isLubinTateSeries_ltPoly π) n)
    (hl' : l ∉ lubinTateTorsion Ω (isLubinTateSeries_ltPoly π) (n - 1))
    {x : 𝒪[lubinTateField Ω hπ hf n]} (hx : ((x : lubinTateField Ω hπ hf n) : Ω) = l.val) :
    Irreducible x := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := by
    cases n with
    | zero => exact absurd hl hl'
    | succ k => exact ⟨k, rfl⟩
  rw [Nat.add_sub_cancel] at hl'
  have hE : lubinTateField Ω hπ hf (k + 1) = K⟮l.val⟯ :=
    (lubinTateField_eq hπ hf (isLubinTateSeries_ltPoly π) _).trans
      (lubinTateField_eq_adjoin_of_primitive hπ _ hl (by rwa [Nat.add_sub_cancel]))
  have hq := one_lt_card_residueField' K
  have hdeg : 0 < (ltEisenstein π k).natDegree := by
    rw [(ltEisenstein_monic π k).2]
    exact Nat.mul_pos (by omega) (pow_pos (by omega) k)
  exact irreducible_of_eq_adjoin_of_isEisensteinAt hE (isEisensteinAt_ltEisenstein hπ k) hdeg
    (aeval_ltEisenstein_of_primitive hπ hl hl') hx

theorem irreducible_of_primitive (hf : IsLubinTateSeries π f) {n : ℕ}
    {l : IdealPoint Ω (lubinTateFormalGroup hπ hf)} (hl : l ∈ lubinTateTorsion Ω hf n)
    (hl' : l ∉ lubinTateTorsion Ω hf (n - 1))
    {x : 𝒪[lubinTateField Ω hπ hf n]} (hx : ((x : lubinTateField Ω hπ hf n) : Ω) = l.val) :
    Irreducible x := by
  have hg₀ : IsLubinTateSeries π (ltPoly π : PowerSeries 𝒪[K]) := isLubinTateSeries_ltPoly π
  obtain ⟨m, rfl⟩ := (lubinTatePointEquiv hf hg₀).surjective l
  replace hl := (lubinTatePointEquiv_mem_torsion_iff hf hg₀ n m).mp hl
  replace hl' := fun h => hl' ((lubinTatePointEquiv_mem_torsion_iff hf hg₀ (n - 1) m).mpr h)
  have hmE : m.val ∈ lubinTateField Ω hπ hf n := val_mem_lubinTateField_of_mem hπ hf hg₀ hl
  obtain ⟨y, hy⟩ := exists_integer_eq hmE m.valuation_lt_one
  have hyirr : Irreducible y := irreducible_of_primitive_ltPoly hπ hf hl hl' hy
  have hym : y ∈ 𝓂[lubinTateField Ω hπ hf n] := hyirr.not_isUnit
  set φ := (lubinTateHom hπ hf hg₀ 1).toPowerSeries
  have hassoc := associated_psEval (K := K) (L := lubinTateField Ω hπ hf n) (φ := φ)
    (lubinTateHom hπ hf hg₀ 1).constantCoeff_eq_zero'
    (by rw [coeff_one_lubinTateHom]; exact isUnit_one) y hym
  have hxe : x = ⟨_, psEval_mem_integer φ (fun _ => y) fun _ => hym⟩ := by
    apply Subtype.ext
    apply Subtype.ext
    rw [hx, lubinTatePointEquiv_val]
    change psEval φ (fun _ => m.val) =
      ((psEval φ (fun _ => (y : lubinTateField Ω hπ hf n)) : lubinTateField Ω hπ hf n) : Ω)
    rw [← psEval_coe _ φ (fun _ => (y : lubinTateField Ω hπ hf n)) (fun _ => by rw [hy]; exact m.valuation_lt_one), hy]
  rw [hxe]
  exact hassoc.irreducible hyirr

theorem norm_neg_eq_uniformizer_of_primitive (hf : IsLubinTateSeries π f) {n : ℕ}
    {l : IdealPoint Ω (lubinTateFormalGroup hπ (isLubinTateSeries_ltPoly π))}
    (hl : l ∈ lubinTateTorsion Ω (isLubinTateSeries_ltPoly π) n)
    (hl' : l ∉ lubinTateTorsion Ω (isLubinTateSeries_ltPoly π) (n - 1)) :
    Algebra.norm K (-(⟨l.val, val_mem_lubinTateField_of_mem hπ hf (isLubinTateSeries_ltPoly π) hl⟩ :
      lubinTateField Ω hπ hf n)) = (π : K) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := by
    cases n with
    | zero => exact absurd hl hl'
    | succ k => exact ⟨k, rfl⟩
  rw [Nat.add_sub_cancel] at hl'
  have hE : lubinTateField Ω hπ hf (k + 1) = K⟮l.val⟯ :=
    (lubinTateField_eq hπ hf (isLubinTateSeries_ltPoly π) _).trans
      (lubinTateField_eq_adjoin_of_primitive hπ _ hl (by rwa [Nat.add_sub_cancel]))
  rw [norm_neg_eq_coeff_zero hE _ (ltEisenstein_monic π k).1 ?_
    (aeval_ltEisenstein_of_primitive hπ hl hl'), coeff_zero_ltEisenstein]
  rw [(finrank_and_ramificationIndex_lubinTateField_succ hπ hf k).1, (ltEisenstein_monic π k).2]

end Torsion

end FormalGroup

end RHDirect.CFT.LocalField
end Sec_LubinTatePrimitive


/-! ### LubinTateTowerMaps -/
section Sec_LubinTateTowerMaps


open _root_.IntermediateField

namespace RHDirect.CFT.LocalField

open ValuativeRel

section Restrict

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]

def restrictAutFun {E F : IntermediateField K Ω} (h : F ≤ E) [Normal K F] (σ : E ≃ₐ[K] E) :
    F ≃ₐ[K] F :=
  AlgHom.restrictNormal' ((E.val.comp (σ : E →ₐ[K] E)).comp (inclusion h)) F

theorem restrictAutFun_apply {E F : IntermediateField K Ω} (h : F ≤ E) [Normal K F]
    (σ : E ≃ₐ[K] E) (x : F) : ((restrictAutFun h σ x : F) : Ω) = σ ⟨x, h x.2⟩ := by
  have := AlgHom.restrictNormal_commutes ((E.val.comp (σ : E →ₐ[K] E)).comp (inclusion h)) F x
  simp only [restrictAutFun, AlgHom.restrictNormal', AlgEquiv.coe_ofBijective]
  exact this

def restrictAut {E F : IntermediateField K Ω} (h : F ≤ E) [Normal K F] :
    (E ≃ₐ[K] E) →* (F ≃ₐ[K] F) where
  toFun := restrictAutFun h
  map_one' := AlgEquiv.ext fun x => Subtype.ext (by rw [restrictAutFun_apply]; rfl)
  map_mul' σ τ := AlgEquiv.ext fun x => Subtype.ext (by
    rw [AlgEquiv.mul_apply, restrictAutFun_apply, restrictAutFun_apply]
    have : (⟨(restrictAutFun h τ x : Ω), h (restrictAutFun h τ x).2⟩ : E) = τ ⟨x, h x.2⟩ :=
      Subtype.ext (restrictAutFun_apply h τ x)
    rw [this]
    rfl)

theorem restrictAut_apply {E F : IntermediateField K Ω} (h : F ≤ E) [Normal K F]
    (σ : E ≃ₐ[K] E) (x : F) : ((restrictAut h σ x : F) : Ω) = σ ⟨x, h x.2⟩ :=
  restrictAutFun_apply h σ x

theorem restrictAut_restrictAut {E F G : IntermediateField K Ω} (h₁ : F ≤ E) (h₂ : G ≤ F)
    [Normal K F] [Normal K G] (σ : E ≃ₐ[K] E) :
    restrictAut h₂ (restrictAut h₁ σ) = restrictAut (h₂.trans h₁) σ :=
  AlgEquiv.ext fun x => Subtype.ext (by
    rw [restrictAut_apply, restrictAut_apply, restrictAut_apply])

theorem restrictAut_self {E : IntermediateField K Ω} [Normal K E] (σ : E ≃ₐ[K] E) :
    restrictAut le_rfl σ = σ :=
  AlgEquiv.ext fun x => Subtype.ext (by rw [restrictAut_apply])

theorem algEquiv_ext_of_restrictAut {ι : Type*} {F : ι → IntermediateField K Ω}
    [∀ n, Normal K (F n)] {E : IntermediateField K Ω} (hle : ∀ n, F n ≤ E)
    (hE : ∀ x ∈ E, ∃ n, x ∈ F n) {σ σ' : E ≃ₐ[K] E}
    (h : ∀ n, restrictAut (hle n) σ = restrictAut (hle n) σ') : σ = σ' := by
  refine AlgEquiv.ext fun x => Subtype.ext ?_
  obtain ⟨n, hn⟩ := hE x x.2
  have := congrArg (fun τ : F n ≃ₐ[K] F n => ((τ ⟨x, hn⟩ : F n) : Ω)) (h n)
  simp only [restrictAut_apply] at this
  exact this

theorem exists_algEquiv_of_compatible {F : ℕ → IntermediateField K Ω} (hF : Monotone F)
    [∀ n, Normal K (F n)] {E : IntermediateField K Ω} [Algebra.IsAlgebraic K E]
    (hle : ∀ n, F n ≤ E) (hE : ∀ x ∈ E, ∃ n, x ∈ F n) (τ : ∀ n, F n ≃ₐ[K] F n)
    (hτ : ∀ m n (h : m ≤ n), restrictAut (hF h) (τ n) = τ m) :
    ∃ σ : E ≃ₐ[K] E, ∀ n, restrictAut (hle n) σ = τ n := by
  have hτ' : ∀ i j (x : Ω) (hi : x ∈ F i) (hj : x ∈ F j),
      ((τ i ⟨x, hi⟩ : F i) : Ω) = ((τ j ⟨x, hj⟩ : F j) : Ω) := by
    intro i j x hi hj
    rcases le_total i j with h | h
    · rw [← hτ i j h, restrictAut_apply]
    · rw [← hτ j i h, restrictAut_apply]
  let S : ℕ → Subalgebra K Ω := fun n => (F n).toSubalgebra
  have hS : Monotone S := fun _ _ h => hF h
  let f : ∀ n, S n →ₐ[K] Ω := fun n => (F n).val.comp (τ n : F n →ₐ[K] F n)
  have hf : ∀ (i j : ℕ) (h : S i ≤ S j), f i = (f j).comp (Subalgebra.inclusion h) := by
    intro i j h
    ext x
    exact hτ' i j x x.2 (h x.2)
  have hT : E.toSubalgebra ≤ iSup S := fun x hx => by
    obtain ⟨n, hn⟩ := hE x hx
    exact (le_iSup S n) hn
  let g := Subalgebra.iSupLift S hS.directed_le f hf E.toSubalgebra hT
  have hg : ∀ (x : E) (n : ℕ) (hn : (x : Ω) ∈ F n), g x = ((τ n ⟨x, hn⟩ : F n) : Ω) :=
    fun x n hn => Subalgebra.iSupLift_of_mem (K := S) x hn
  have hgE : ∀ x : E, g x ∈ E := fun x => by
    obtain ⟨n, hn⟩ := hE x x.2
    rw [hg x n hn]
    exact hle n (τ n ⟨x, hn⟩).2
  let g' : E →ₐ[K] E := g.codRestrict E.toSubalgebra hgE
  refine ⟨AlgEquiv.ofBijective g' (Algebra.IsAlgebraic.algHom_bijective _), fun n => ?_⟩
  refine AlgEquiv.ext fun x => Subtype.ext ?_
  rw [restrictAut_apply, AlgEquiv.ofBijective_apply]
  exact hg ⟨x, hle n x.2⟩ n x.2

end Restrict

namespace FormalGroup
open RHDirect.CFT.FormalGroups

section Reduce

variable {K : Type*} [Field K] [ValuativeRel K]

def unitsReduce (π : 𝒪[K]) {m n : ℕ} (h : m ≤ n) :
    (𝒪[K] ⧸ Ideal.span {π ^ n})ˣ →* (𝒪[K] ⧸ Ideal.span {π ^ m})ˣ :=
  Units.map (Ideal.Quotient.factor
    (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow π h))).toMonoidHom

theorem coe_unitsReduce (π : 𝒪[K]) {m n : ℕ} (h : m ≤ n) (u : (𝒪[K] ⧸ Ideal.span {π ^ n})ˣ)
    (a : 𝒪[K]) (ha : Ideal.Quotient.mk _ a = (u : 𝒪[K] ⧸ Ideal.span {π ^ n})) :
    (unitsReduce π h u : 𝒪[K] ⧸ Ideal.span {π ^ m}) = Ideal.Quotient.mk _ a := by
  rw [unitsReduce, Units.coe_map, ← ha]
  exact Ideal.Quotient.factor_mk _ a

def unitsMk (π : 𝒪[K]) (n : ℕ) : 𝒪[K]ˣ →* (𝒪[K] ⧸ Ideal.span {π ^ n})ˣ :=
  Units.map (Ideal.Quotient.mk (Ideal.span {π ^ n})).toMonoidHom

theorem coe_unitsMk (π : 𝒪[K]) (n : ℕ) (u : 𝒪[K]ˣ) :
    (unitsMk π n u : 𝒪[K] ⧸ Ideal.span {π ^ n}) = Ideal.Quotient.mk _ (u : 𝒪[K]) := rfl

theorem unitsReduce_unitsMk (π : 𝒪[K]) {m n : ℕ} (h : m ≤ n) (u : 𝒪[K]ˣ) :
    unitsReduce π h (unitsMk π n u) = unitsMk π m u :=
  Units.ext (coe_unitsReduce π h _ _ rfl)

end Reduce

section Char

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω]
variable {π : 𝒪[K]} (hπ : Irreducible π) {f g : PowerSeries 𝒪[K]}

theorem algEquiv_psEval_coe {E : IntermediateField K Ω} [FiniteDimensional K E]
    (τ : E ≃ₐ[K] E) (φ : PowerSeries 𝒪[K]) (z : E) (hz : valuation Ω (z : Ω) < 1)
    (hmem : psEval φ (fun _ => (z : Ω)) ∈ E) :
    ((τ ⟨psEval φ (fun _ => (z : Ω)), hmem⟩ : E) : Ω) = psEval φ (fun _ => ((τ z : E) : Ω)) := by
  have h1 : (⟨psEval φ (fun _ => (z : Ω)), hmem⟩ : E) = psEval φ (fun _ => z) :=
    Subtype.ext (psEval_coe E φ (fun _ => z) fun _ => hz)
  have hτ : valuation Ω ((τ z : E) : Ω) < 1 := by
    rw [valuation_coe_lt_one_iff, valuation_algEquiv_apply_of_isAlgebraic,
      ← valuation_coe_lt_one_iff]
    exact hz
  rw [h1, algEquiv_psEval τ φ (fun _ => z) fun _ => by rw [← valuation_coe_lt_one_iff]; exact hz]
  exact (psEval_coe E φ (fun _ => τ z) fun _ => hτ).symm

variable [IsSepClosed Ω]

def lubinTateChar (hf : IsLubinTateSeries π f) (n : ℕ) {E : IntermediateField K Ω}
    (hE : lubinTateField Ω hπ hf n ≤ E) : (E ≃ₐ[K] E) →* (𝒪[K] ⧸ Ideal.span {π ^ n})ˣ :=
  (lubinTateGalEquiv hπ hf n).toMonoidHom.comp (restrictAut hE)

theorem lubinTateChar_spec (hf : IsLubinTateSeries π f) {n : ℕ} {E : IntermediateField K Ω}
    (hE : lubinTateField Ω hπ hf n ≤ E) (σ : E ≃ₐ[K] E)
    {x : IdealPoint Ω (lubinTateFormalGroup hπ hf)} (hx : x ∈ lubinTateTorsion Ω hf n) (a : 𝒪[K])
    (ha : Ideal.Quotient.mk _ a = (lubinTateChar hπ hf n hE σ : 𝒪[K] ⧸ Ideal.span {π ^ n})) :
    ((σ ⟨x.val, hE (val_mem_lubinTateField hπ hf hx)⟩ : E) : Ω) = (a • x).val :=
  (restrictAut_apply hE σ ⟨x.val, val_mem_lubinTateField hπ hf hx⟩).symm.trans
    (lubinTateGalEquiv_spec hf n (restrictAut hE σ) x hx a ha)

theorem lubinTateChar_eq_of_apply (hf : IsLubinTateSeries π f) {n : ℕ} {E : IntermediateField K Ω}
    (hE : lubinTateField Ω hπ hf n ≤ E) (σ : E ≃ₐ[K] E) (a : 𝒪[K])
    (h : ∀ (x) (hx : x ∈ lubinTateTorsion Ω (hπ := hπ) hf n),
      ((σ ⟨x.val, hE (val_mem_lubinTateField hπ hf hx)⟩ : E) : Ω) = (a • x).val) :
    (lubinTateChar hπ hf n hE σ : 𝒪[K] ⧸ Ideal.span {π ^ n}) = Ideal.Quotient.mk _ a := by
  obtain ⟨l, hl, hann, -⟩ := exists_generator_lubinTateTorsion (Ω := Ω) (hπ := hπ) hf n
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective
    (lubinTateChar hπ hf n hE σ : 𝒪[K] ⧸ Ideal.span {π ^ n})
  have h1 := lubinTateChar_spec hπ hf hE σ hl b hb
  rw [h l hl] at h1
  have h2 : b • l = a • l := (IdealPoint.ext h1).symm
  rw [← hb, Ideal.Quotient.eq, ← hann, sub_smul, sub_eq_zero]
  exact h2

theorem lubinTateChar_reduce (hf : IsLubinTateSeries π f) {m n : ℕ} (hmn : m ≤ n)
    {E : IntermediateField K Ω} (hE : lubinTateField Ω hπ hf n ≤ E) (σ : E ≃ₐ[K] E) :
    lubinTateChar hπ hf m ((lubinTateField_mono hπ hf hmn).trans hE) σ =
      unitsReduce π hmn (lubinTateChar hπ hf n hE σ) := by
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective
    (lubinTateChar hπ hf n hE σ : 𝒪[K] ⧸ Ideal.span {π ^ n})
  apply Units.ext
  rw [coe_unitsReduce π hmn _ a ha, lubinTateChar_eq_of_apply hπ hf _ σ a]
  intro x hx
  exact lubinTateChar_spec hπ hf hE σ (lubinTateTorsion_mono hπ hf hmn hx) a ha

theorem lubinTateGalEquiv_restrictAut (hf : IsLubinTateSeries π f) {m n : ℕ} (hmn : m ≤ n)
    (σ : lubinTateField Ω hπ hf n ≃ₐ[K] lubinTateField Ω hπ hf n) :
    lubinTateGalEquiv hπ hf m (restrictAut (lubinTateField_mono hπ hf hmn) σ) =
      unitsReduce π hmn (lubinTateGalEquiv hπ hf n σ) := by
  have := lubinTateChar_reduce hπ hf hmn le_rfl σ
  simp only [lubinTateChar, MonoidHom.coe_comp, Function.comp_apply, restrictAut_self] at this
  exact this

theorem lubinTateChar_eq (hf : IsLubinTateSeries π f) (hg : IsLubinTateSeries π g) {n : ℕ}
    {E : IntermediateField K Ω} (hEf : lubinTateField Ω hπ hf n ≤ E)
    (hEg : lubinTateField Ω hπ hg n ≤ E) (σ : E ≃ₐ[K] E) :
    lubinTateChar hπ hf n hEf σ = lubinTateChar hπ hg n hEg σ := by
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective
    (lubinTateChar hπ hf n hEf σ : 𝒪[K] ⧸ Ideal.span {π ^ n})
  apply Units.ext
  rw [← ha, lubinTateChar_eq_of_apply hπ hg hEg σ a]
  intro y hy
  obtain ⟨x, rfl⟩ := (lubinTatePointEquiv hg hf).surjective y
  have hx : x ∈ lubinTateTorsion Ω hf n := (lubinTatePointEquiv_mem_torsion_iff hg hf n x).mp hy
  set τ := restrictAut hEf σ
  have hyF : (lubinTatePointEquiv hg hf x).val ∈ lubinTateField Ω hπ hf n :=
    val_mem_lubinTateField_of_mem hπ hf hg hy
  have h1 : ((σ ⟨(lubinTatePointEquiv hg hf x).val, hEg (val_mem_lubinTateField hπ hg hy)⟩ : E) : Ω)
      = ((τ ⟨(lubinTatePointEquiv hg hf x).val, hyF⟩ : lubinTateField Ω hπ hf n) : Ω) :=
    (restrictAut_apply hEf σ ⟨_, hyF⟩).symm
  rw [h1]
  have h2 := algEquiv_psEval_coe τ (lubinTateHom hπ hg hf 1).toPowerSeries
    ⟨x.val, val_mem_lubinTateField hπ hf hx⟩ x.valuation_lt_one hyF
  refine h2.trans ?_
  rw [← map_smul, lubinTatePointEquiv_val]
  congr 2
  funext _
  rw [restrictAut_apply]
  exact lubinTateChar_spec hπ hf hEf σ hx a ha

end Char

end FormalGroup

end RHDirect.CFT.LocalField
end Sec_LubinTateTowerMaps


/-! ### LubinTateLimitGalois -/
section Sec_LubinTateLimitGalois


open _root_.IntermediateField Topology Filter

namespace RHDirect.CFT.LocalField

open ValuativeRel

section Finite

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

theorem exists_le_of_finiteDimensional {F : ℕ → IntermediateField K L} (hF : Monotone F)
    {E : IntermediateField K L} [FiniteDimensional K E] (hE : ∀ x ∈ E, ∃ n, x ∈ F n) :
    ∃ n, E ≤ F n := by
  classical
  let b := Module.finBasis K E
  choose N hN using fun i => hE (b i) (b i).2
  refine ⟨Finset.univ.sup N, fun x hx => ?_⟩
  have hx' : x = ∑ i, b.repr ⟨x, hx⟩ i • (b i : L) := by
    have h := congrArg Subtype.val (b.sum_repr ⟨x, hx⟩)
    simp only [IntermediateField.coe_sum, IntermediateField.coe_smul] at h
    exact h.symm
  rw [hx']
  exact sum_mem fun i _ =>
    IntermediateField.smul_mem _ (hF (Finset.le_sup (Finset.mem_univ i)) (hN i))

end Finite

section UnitsTopology

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

theorem exists_maximalIdeal_pow_subset {A : Set 𝒪[K]} (hA : A ∈ 𝓝 (1 : 𝒪[K])) :
    ∃ n, ∀ y : 𝒪[K], y - 1 ∈ 𝓂[K] ^ n → y ∈ A := by
  have h0 : (fun z => z + 1) ⁻¹' A ∈ 𝓝 (0 : 𝒪[K]) := by
    have h := (continuous_add_const (1 : 𝒪[K])).continuousAt (x := 0)
    rw [ContinuousAt, zero_add] at h
    exact h hA
  obtain ⟨γ, -, hγ⟩ := (EqualChar.hasBasis_nhds_zero_integer K).mem_iff.mp h0
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  have hϖ1 : valuation K (ϖ : K) < 1 :=
    valuation_lt_one_of_mem_maximalIdeal (uniformizer_mem_maximalIdeal hϖ)
  obtain ⟨n, hn⟩ := exists_pow_lt₀ hϖ1 γ
  refine ⟨n, fun y hy => ?_⟩
  rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hy
  obtain ⟨c, hc⟩ := hy
  have hc1 : valuation K (c : K) ≤ 1 := c.2
  have hmem : y - 1 ∈ EqualChar.ballIdeal K γ := by
    rw [EqualChar.mem_ballIdeal]
    calc valuation K ((y - 1 : 𝒪[K]) : K) = valuation K (ϖ : K) ^ n * valuation K (c : K) := by
          rw [hc]; push_cast; rw [map_mul, map_pow]
      _ ≤ valuation K (ϖ : K) ^ n := mul_le_of_le_one_right' hc1
      _ < γ := hn
  simpa using hγ hmem

theorem FormalGroup.unitsMk_eq_one_iff {π : 𝒪[K]} (hπ : Irreducible π) {n : ℕ} {u : 𝒪[K]ˣ} :
    FormalGroup.unitsMk π n u = 1 ↔ u ∈ unitFiltration K n := by
  rw [mem_unitFiltration, ← Units.val_eq_one, FormalGroup.coe_unitsMk, ← map_one (Ideal.Quotient.mk _),
    Ideal.Quotient.eq, hπ.maximalIdeal_eq, Ideal.span_singleton_pow]

theorem isOpen_unitFiltration (n : ℕ) : IsOpen (unitFiltration K n : Set 𝒪[K]ˣ) := by
  have h : (unitFiltration K n : Set 𝒪[K]ˣ) = (fun u : 𝒪[K]ˣ => (u : 𝒪[K]) - 1) ⁻¹'
      ((IsLocalRing.maximalIdeal 𝒪[K] ^ n : Ideal 𝒪[K]) : Set 𝒪[K]) := rfl
  rw [h]
  exact (IsLocalRing.isOpen_maximalIdeal_pow 𝒪[K] n).preimage
    (Units.continuous_val.sub continuous_const)

theorem exists_unitFiltration_subset {t : Set 𝒪[K]ˣ} (ht : t ∈ 𝓝 1) :
    ∃ n, (unitFiltration K n : Set 𝒪[K]ˣ) ⊆ t := by
  rw [Units.isInducing_embedProduct.nhds_eq_comap, mem_comap] at ht
  obtain ⟨s, hs, hst⟩ := ht
  have hs' : s ∈ 𝓝 ((1 : 𝒪[K]), (1 : 𝒪[K]ᵐᵒᵖ)) := by
    rw [Prod.mk_one_one]
    rwa [map_one] at hs
  obtain ⟨A, hA, B, hB, hAB⟩ := mem_nhds_prod_iff.mp hs'
  have hB' : MulOpposite.op ⁻¹' B ∈ 𝓝 (1 : 𝒪[K]) :=
    MulOpposite.continuous_op.continuousAt.preimage_mem_nhds hB
  obtain ⟨n, hn⟩ := exists_maximalIdeal_pow_subset (inter_mem hA hB')
  refine ⟨n, fun u hu => hst (hAB ?_)⟩
  exact ⟨(hn u hu).1, (hn _ (inv_mem (show u ∈ unitFiltration K n from hu))).2⟩

end UnitsTopology

namespace FormalGroup
open RHDirect.CFT.FormalGroups

theorem eq_zero_of_forall_pow_dvd {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] {π : 𝒪[K]} (hπ : Irreducible π) {x : 𝒪[K]}
    (h : ∀ n, π ^ n ∣ x) : x = 0 := by
  by_contra hx
  obtain ⟨k, w, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hπ
  obtain ⟨c, hc⟩ := h (k + 1)
  have h1 : (w : 𝒪[K]) * π ^ k = (π * c) * π ^ k := by rw [hc]; ring
  have h2 := mul_right_cancel₀ (pow_ne_zero k hπ.ne_zero) h1
  exact hπ.not_isUnit (isUnit_of_mul_isUnit_left (h2 ▸ w.isUnit))

section Limit

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω]
variable {π : 𝒪[K]} (hπ : Irreducible π) {f g : PowerSeries 𝒪[K]}

variable (Ω) in

def lubinTateLimit (hπ : Irreducible π) : IntermediateField K Ω :=
  ⨆ n, lubinTateField Ω hπ (isLubinTateSeries_ltPoly π) n

theorem monotone_lubinTateField (hf : IsLubinTateSeries π f) :
    Monotone (lubinTateField Ω hπ hf) :=
  fun _ _ h => lubinTateField_mono hπ hf h

variable [IsSepClosed Ω]

theorem lubinTateLimit_eq (hf : IsLubinTateSeries π f) :
    lubinTateLimit Ω hπ = ⨆ n, lubinTateField Ω hπ hf n := by
  simp_rw [lubinTateLimit, lubinTateField_eq hπ (isLubinTateSeries_ltPoly π) hf]

theorem lubinTateField_le_lubinTateLimit (hf : IsLubinTateSeries π f) (n : ℕ) :
    lubinTateField Ω hπ hf n ≤ lubinTateLimit Ω hπ := by
  rw [lubinTateLimit_eq hπ hf]
  exact le_iSup (fun n => lubinTateField Ω hπ hf n) n

theorem mem_lubinTateLimit_iff (hf : IsLubinTateSeries π f) {x : Ω} :
    x ∈ lubinTateLimit Ω hπ ↔ ∃ n, x ∈ lubinTateField Ω hπ hf n := by
  rw [lubinTateLimit_eq hπ hf, ← SetLike.mem_coe,
    IntermediateField.coe_iSup_of_directed (monotone_lubinTateField hπ hf).directed_le]
  simp only [Set.mem_iUnion, SetLike.mem_coe]

instance isGalois_lubinTateLimit : IsGalois K (lubinTateLimit Ω hπ) := by
  unfold lubinTateLimit
  exact isGalois_iff.mpr ⟨inferInstance, inferInstance⟩

theorem lubinTateLimit_ext (hf : IsLubinTateSeries π f)
    {σ σ' : lubinTateLimit Ω hπ ≃ₐ[K] lubinTateLimit Ω hπ}
    (h : ∀ n, lubinTateChar hπ hf n (lubinTateField_le_lubinTateLimit hπ hf n) σ =
      lubinTateChar hπ hf n (lubinTateField_le_lubinTateLimit hπ hf n) σ') : σ = σ' :=
  algEquiv_ext_of_restrictAut (lubinTateField_le_lubinTateLimit hπ hf)
    (fun _ hx => (mem_lubinTateLimit_iff hπ hf).mp hx)
    fun n => (lubinTateGalEquiv hπ hf n).injective (h n)

theorem exists_lubinTateLimitAut (hf : IsLubinTateSeries π f) (u : 𝒪[K]ˣ) :
    ∃ σ : lubinTateLimit Ω hπ ≃ₐ[K] lubinTateLimit Ω hπ, ∀ n,
      restrictAut (lubinTateField_le_lubinTateLimit hπ hf n) σ =
        (lubinTateGalEquiv hπ hf n).symm (unitsMk π n u) :=
  exists_algEquiv_of_compatible (monotone_lubinTateField hπ hf)
    (lubinTateField_le_lubinTateLimit hπ hf) (fun _ hx => (mem_lubinTateLimit_iff hπ hf).mp hx) _
    fun m n h => by
      apply (lubinTateGalEquiv hπ hf m).injective
      rw [lubinTateGalEquiv_restrictAut hπ hf h, MulEquiv.apply_symm_apply,
        MulEquiv.apply_symm_apply, unitsReduce_unitsMk]

def lubinTateLimitAut (hf : IsLubinTateSeries π f) (u : 𝒪[K]ˣ) :
    lubinTateLimit Ω hπ ≃ₐ[K] lubinTateLimit Ω hπ :=
  Classical.choose (exists_lubinTateLimitAut hπ hf u)

theorem lubinTateChar_lubinTateLimitAut (hf : IsLubinTateSeries π f) (u : 𝒪[K]ˣ) (n : ℕ) :
    lubinTateChar hπ hf n (lubinTateField_le_lubinTateLimit hπ hf n)
      (lubinTateLimitAut (Ω := Ω) hπ hf u) = unitsMk π n u := by
  rw [lubinTateChar, MonoidHom.comp_apply, lubinTateLimitAut,
    Classical.choose_spec (exists_lubinTateLimitAut hπ hf u) n]
  exact MulEquiv.apply_symm_apply _ _

def lubinTateLimitAutHom (hf : IsLubinTateSeries π f) :
    𝒪[K]ˣ →* (lubinTateLimit Ω hπ ≃ₐ[K] lubinTateLimit Ω hπ) where
  toFun := lubinTateLimitAut hπ hf
  map_one' := lubinTateLimit_ext hπ hf fun n => by
    rw [lubinTateChar_lubinTateLimitAut, map_one, map_one]
  map_mul' u v := lubinTateLimit_ext hπ hf fun n => by
    rw [map_mul (lubinTateChar hπ hf n _), lubinTateChar_lubinTateLimitAut,
      lubinTateChar_lubinTateLimitAut, lubinTateChar_lubinTateLimitAut, map_mul]

theorem lubinTateLimitAutHom_injective (hf : IsLubinTateSeries π f) :
    Function.Injective (lubinTateLimitAutHom (Ω := Ω) hπ hf) := by
  rw [injective_iff_map_eq_one]
  intro u hu
  have h : ∀ n, unitsMk π n u = 1 := fun n => by
    rw [← lubinTateChar_lubinTateLimitAut (Ω := Ω) hπ hf u n]
    change lubinTateChar hπ hf n _ (lubinTateLimitAutHom hπ hf u) = 1
    rw [hu, map_one]
  apply Units.ext
  rw [Units.val_one, ← sub_eq_zero]
  refine eq_zero_of_forall_pow_dvd hπ fun n => ?_
  have := congrArg Units.val (h n)
  rw [coe_unitsMk, Units.val_one, ← map_one (Ideal.Quotient.mk _), Ideal.Quotient.eq,
    Ideal.mem_span_singleton] at this
  exact this

theorem lubinTateLimitAutHom_surjective (hf : IsLubinTateSeries π f) :
    Function.Surjective (lubinTateLimitAutHom (Ω := Ω) hπ hf) := by
  intro σ
  set a : ∀ n, (𝒪[K] ⧸ Ideal.span {π ^ n})ˣ := fun n =>
    lubinTateChar hπ hf n (lubinTateField_le_lubinTateLimit hπ hf n) σ with ha_def
  have ha : ∀ m n (h : m ≤ n), unitsReduce π h (a n) = a m := fun m n h =>
    (lubinTateChar_reduce hπ hf h (lubinTateField_le_lubinTateLimit hπ hf n) σ).symm
  choose r hr using fun n => Ideal.Quotient.mk_surjective (a n : 𝒪[K] ⧸ Ideal.span {π ^ n})
  have hI : ∀ n, ((IsLocalRing.maximalIdeal 𝒪[K]) ^ n • ⊤ : Submodule 𝒪[K] 𝒪[K]) =
      Ideal.span {π ^ n} := by
    intro n
    rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top]
  have hcomp : IsAdicComplete (IsLocalRing.maximalIdeal 𝒪[K]) 𝒪[K] := by
    let := IsTopologicalAddGroup.rightUniformSpace K
    have := isUniformAddGroup_of_addCommGroup (G := K)
    infer_instance
  have hrm : ∀ {m n : ℕ}, m ≤ n →
      r m ≡ r n [SMOD ((IsLocalRing.maximalIdeal 𝒪[K]) ^ m • ⊤ : Submodule 𝒪[K] 𝒪[K])] := by
    intro m n h
    rw [hI, SModEq.sub_mem, ← Ideal.Quotient.eq, hr m, ← ha m n h,
      coe_unitsReduce π h (a n) (r n) (hr n)]
  obtain ⟨c, hc⟩ := hcomp.toIsPrecomplete.prec hrm
  have hcn : ∀ n, Ideal.Quotient.mk (Ideal.span {π ^ n}) c = a n := fun n => by
    have := hc n
    rw [hI, SModEq.sub_mem, ← Ideal.Quotient.eq, hr n] at this
    exact this.symm
  have hcu : IsUnit c := by
    by_contra hnu
    have : Nontrivial (𝒪[K] ⧸ Ideal.span {π ^ 1}) := Ideal.Quotient.nontrivial_iff.mpr (by
      rw [Ne, Ideal.span_singleton_eq_top, pow_one]
      exact hπ.not_isUnit)
    have hm : c ∈ Ideal.span {π ^ 1} := by
      rw [pow_one, ← hπ.maximalIdeal_eq]
      exact hnu
    have h1 := hcn 1
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hm] at h1
    exact (a 1).ne_zero h1.symm
  refine ⟨hcu.unit, lubinTateLimit_ext hπ hf fun n => ?_⟩
  change lubinTateChar hπ hf n _ (lubinTateLimitAut hπ hf hcu.unit) = a n
  rw [lubinTateChar_lubinTateLimitAut]
  exact Units.ext (hcn n)

theorem restrictAut_lubinTateLimitAut_eq_one_iff (hf : IsLubinTateSeries π f) (u : 𝒪[K]ˣ) (n : ℕ) :
    restrictAut (lubinTateField_le_lubinTateLimit hπ hf n) (lubinTateLimitAut (Ω := Ω) hπ hf u) = 1
      ↔ u ∈ unitFiltration K n := by
  rw [← unitsMk_eq_one_iff hπ, ← lubinTateChar_lubinTateLimitAut (Ω := Ω) hπ hf u n, lubinTateChar,
    MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff]

theorem lubinTateLimitAutHom_apply (hf : IsLubinTateSeries π f) (u : 𝒪[K]ˣ) :
    lubinTateLimitAutHom (Ω := Ω) hπ hf u = lubinTateLimitAut hπ hf u := rfl

theorem mem_fixingSubgroup_restrict_iff (hf : IsLubinTateSeries π f) (n : ℕ)
    (σ : lubinTateLimit Ω hπ ≃ₐ[K] lubinTateLimit Ω hπ) :
    σ ∈ (IntermediateField.restrict (lubinTateField_le_lubinTateLimit hπ hf n)).fixingSubgroup ↔
      restrictAut (lubinTateField_le_lubinTateLimit hπ hf n) σ = 1 := by
  rw [IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro h
    refine AlgEquiv.ext fun x => Subtype.ext ?_
    rw [restrictAut_apply, AlgEquiv.one_apply]
    exact congrArg Subtype.val (h _ ((mem_restrict _ _).mpr x.2))
  · intro h x hx
    apply Subtype.ext
    have h2 := restrictAut_apply (lubinTateField_le_lubinTateLimit hπ hf n) σ
      ⟨x, (mem_restrict _ x).mp hx⟩
    rw [h, AlgEquiv.one_apply] at h2
    exact h2.symm

theorem continuous_lubinTateLimitAutHom (hf : IsLubinTateSeries π f) :
    Continuous (lubinTateLimitAutHom (Ω := Ω) hπ hf) := by
  refine continuous_of_continuousAt_one _ ?_
  rw [ContinuousAt, map_one]
  intro s hs
  obtain ⟨E, hE, hEs⟩ := (krullTopology_mem_nhds_one_iff K _ s).mp hs
  obtain ⟨N, hN⟩ := exists_le_of_finiteDimensional
    (F := fun n => IntermediateField.restrict (lubinTateField_le_lubinTateLimit (Ω := Ω) hπ hf n))
    (fun _ _ h x hx => (mem_restrict _ x).mpr (lubinTateField_mono hπ hf h ((mem_restrict _ x).mp hx)))
    (E := E) fun x _ => by
      obtain ⟨n, hn⟩ := (mem_lubinTateLimit_iff hπ hf).mp x.2
      exact ⟨n, (mem_restrict _ x).mpr hn⟩
  refine Filter.mem_map.mpr
    (mem_of_superset ((isOpen_unitFiltration N).mem_nhds (one_mem _)) fun u hu => hEs ?_)
  rw [SetLike.mem_coe, lubinTateLimitAutHom_apply]
  refine IntermediateField.fixingSubgroup_antitone hN ?_
  rw [mem_fixingSubgroup_restrict_iff]
  exact (restrictAut_lubinTateLimitAut_eq_one_iff (Ω := Ω) hπ hf u N).mpr hu

def lubinTateLimitGalEquiv (hf : IsLubinTateSeries π f) :
    𝒪[K]ˣ ≃ₜ* (lubinTateLimit Ω hπ ≃ₐ[K] lubinTateLimit Ω hπ) :=
  let e := MulEquiv.ofBijective (lubinTateLimitAutHom (Ω := Ω) hπ hf)
    ⟨lubinTateLimitAutHom_injective hπ hf, lubinTateLimitAutHom_surjective hπ hf⟩
  { e with
    continuous_toFun := continuous_lubinTateLimitAutHom hπ hf
    continuous_invFun := by
      refine continuous_of_continuousAt_one e.symm ?_
      rw [ContinuousAt, map_one]
      intro t ht
      obtain ⟨N, hN⟩ := exists_unitFiltration_subset ht
      have : FiniteDimensional K
          (IntermediateField.restrict (lubinTateField_le_lubinTateLimit (Ω := Ω) hπ hf N)) :=
        (restrictAlgEquiv (lubinTateField_le_lubinTateLimit (Ω := Ω) hπ hf N)).toLinearEquiv.finiteDimensional
      refine Filter.mem_map.mpr (mem_of_superset ((IntermediateField.restrict
        (lubinTateField_le_lubinTateLimit (Ω := Ω) hπ hf N)).fixingSubgroup_isOpen.mem_nhds
          (one_mem _)) fun σ hσ => hN ?_)
      obtain ⟨u, rfl⟩ := e.surjective σ
      show e.symm (e u) ∈ _
      rw [e.symm_apply_apply, SetLike.mem_coe,
        ← restrictAut_lubinTateLimitAut_eq_one_iff (Ω := Ω) hπ hf u N,
        ← mem_fixingSubgroup_restrict_iff]
      exact hσ }

theorem lubinTateLimitGalEquiv_apply' (hf : IsLubinTateSeries π f) (u : 𝒪[K]ˣ) :
    lubinTateLimitGalEquiv (Ω := Ω) hπ hf u = lubinTateLimitAut hπ hf u := rfl

theorem lubinTateChar_lubinTateLimitGalEquiv (hf : IsLubinTateSeries π f) (u : 𝒪[K]ˣ) (n : ℕ) :
    lubinTateChar hπ hf n (lubinTateField_le_lubinTateLimit hπ hf n)
      (lubinTateLimitGalEquiv (Ω := Ω) hπ hf u) = unitsMk π n u :=
  lubinTateChar_lubinTateLimitAut hπ hf u n

theorem lubinTateLimitGalEquiv_apply (hf : IsLubinTateSeries π f) (u : 𝒪[K]ˣ) {n : ℕ}
    {x : IdealPoint Ω (lubinTateFormalGroup hπ hf)} (hx : x ∈ lubinTateTorsion Ω hf n) :
    ((lubinTateLimitGalEquiv hπ hf u
      ⟨x.val, lubinTateField_le_lubinTateLimit hπ hf n (val_mem_lubinTateField hπ hf hx)⟩ :
        lubinTateLimit Ω hπ) : Ω) = ((u : 𝒪[K]) • x).val :=
  lubinTateChar_spec hπ hf _ _ hx (u : 𝒪[K]) (by
    rw [lubinTateChar_lubinTateLimitGalEquiv, coe_unitsMk])

theorem lubinTateLimitGalEquiv_eq_iff (hf : IsLubinTateSeries π f) (u : 𝒪[K]ˣ)
    (σ : lubinTateLimit Ω hπ ≃ₐ[K] lubinTateLimit Ω hπ) :
    lubinTateLimitGalEquiv hπ hf u = σ ↔
      ∀ (n : ℕ) (x : IdealPoint Ω (lubinTateFormalGroup hπ hf)) (hx : x ∈ lubinTateTorsion Ω hf n),
        ((σ ⟨x.val, lubinTateField_le_lubinTateLimit hπ hf n (val_mem_lubinTateField hπ hf hx)⟩ :
          lubinTateLimit Ω hπ) : Ω) = ((u : 𝒪[K]) • x).val := by
  constructor
  · rintro rfl n x hx
    exact lubinTateLimitGalEquiv_apply hπ hf u hx
  · intro h
    refine lubinTateLimit_ext hπ hf fun n => Units.ext ?_
    rw [lubinTateChar_lubinTateLimitGalEquiv, coe_unitsMk,
      lubinTateChar_eq_of_apply hπ hf _ σ _ fun x hx => h n x hx]

theorem lubinTateLimitGalEquiv_eq (hf : IsLubinTateSeries π f) (hg : IsLubinTateSeries π g) :
    lubinTateLimitGalEquiv (Ω := Ω) hπ hf = lubinTateLimitGalEquiv hπ hg := by
  ext u : 1
  refine lubinTateLimit_ext hπ hg fun n => ?_
  rw [← lubinTateChar_eq hπ hf hg (lubinTateField_le_lubinTateLimit hπ hf n),
    lubinTateChar_lubinTateLimitGalEquiv, lubinTateChar_lubinTateLimitGalEquiv]

end Limit

end FormalGroup

end RHDirect.CFT.LocalField
end Sec_LubinTateLimitGalois


/-! ### LubinTateUnramified -/
section Sec_LubinTateUnramified


open _root_.IntermediateField Topology Filter

namespace RHDirect.CFT.LocalField

open ValuativeRel

section Sup

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]

theorem algEquiv_ext_sup {F₁ F₂ : IntermediateField K Ω} [Normal K F₁] [Normal K F₂]
    {σ σ' : (F₁ ⊔ F₂ : IntermediateField K Ω) ≃ₐ[K] (F₁ ⊔ F₂ : IntermediateField K Ω)}
    (h₁ : restrictAut le_sup_left σ = restrictAut le_sup_left σ')
    (h₂ : restrictAut le_sup_right σ = restrictAut le_sup_right σ') : σ = σ' := by
  have key : ((F₁ ⊔ F₂ : IntermediateField K Ω).val.comp σ.toAlgHom) =
      ((F₁ ⊔ F₂ : IntermediateField K Ω).val.comp σ'.toAlgHom) := by
    refine algHom_ext_of_eq_adjoin K (sup_def F₁ F₂) fun x hx => ?_
    rcases hx with hx | hx
    · have := congrArg (fun τ : F₁ ≃ₐ[K] F₁ => ((τ ⟨x, hx⟩ : F₁) : Ω)) h₁
      simp only [restrictAut_apply] at this
      exact this
    · have := congrArg (fun τ : F₂ ≃ₐ[K] F₂ => ((τ ⟨x, hx⟩ : F₂) : Ω)) h₂
      simp only [restrictAut_apply] at this
      exact this
  exact AlgEquiv.ext fun x => Subtype.ext (congrArg (fun φ => φ x) key)

theorem continuous_restrictAut {E F : IntermediateField K Ω} (h : F ≤ E) [Normal K F] :
    Continuous (restrictAut h) := by
  refine continuous_of_continuousAt_one _ ?_
  rw [ContinuousAt, map_one]
  intro s hs
  obtain ⟨E', hE', hE's⟩ := (krullTopology_mem_nhds_one_iff K F s).mp hs
  let E'' : IntermediateField K E := E'.map (IntermediateField.inclusion h)
  have : FiniteDimensional K E'' := (E'.equivMap (IntermediateField.inclusion h)).toLinearEquiv.finiteDimensional
  refine Filter.mem_map.mpr (mem_of_superset (E''.fixingSubgroup_isOpen.mem_nhds (one_mem _))
    fun σ hσ => hE's ?_)
  rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff] at hσ ⊢
  intro y hy
  apply Subtype.ext
  rw [restrictAut_apply]
  exact congrArg Subtype.val (hσ ⟨y, h y.2⟩ (by rw [IntermediateField.mem_map]; exact ⟨y, hy, rfl⟩))

end Sup

section Tower

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω]

theorem ramificationIndex_dvd_of_le {F E : IntermediateField K Ω} [FiniteDimensional K F]
    [FiniteDimensional K E] (h : F ≤ E) : ramificationIndex K F ∣ ramificationIndex K E := by
  let : Algebra F E := (IntermediateField.inclusion h).toRingHom.toAlgebra
  have : IsScalarTower K F E := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : ValuativeExtension F E := valuativeExtension_algHom (K := K) (IntermediateField.inclusion h)
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite K F E
  exact Dvd.intro _ (ramificationIndex_tower K F E).symm

theorem residueDegree_dvd_of_le {F E : IntermediateField K Ω} [FiniteDimensional K F]
    [FiniteDimensional K E] (h : F ≤ E) : residueDegree K F ∣ residueDegree K E := by
  let : Algebra F E := (IntermediateField.inclusion h).toRingHom.toAlgebra
  have : IsScalarTower K F E := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : ValuativeExtension F E := valuativeExtension_algHom (K := K) (IntermediateField.inclusion h)
  exact Dvd.intro _ (residueDegree_tower K F E).symm

end Tower

namespace FormalGroup
open RHDirect.CFT.FormalGroups

section Unramified

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω] [IsSepClosed Ω]
variable {π : 𝒪[K]} (hπ : Irreducible π) {f : PowerSeries 𝒪[K]}

instance isGalois_sup (E₁ E₂ : IntermediateField K Ω) [IsGalois K E₁] [IsGalois K E₂] :
    IsGalois K (E₁ ⊔ E₂ : IntermediateField K Ω) :=
  isGalois_iff.mpr ⟨inferInstance, inferInstance⟩

variable (hf : IsLubinTateSeries π f) {n : ℕ} (hn : 0 < n) {E : IntermediateField K Ω}
  (hE : IsUnramifiedSubextension E)

include hE hn in

theorem bijective_restrictAut_prod :
    haveI := hE.isGalois
    Function.Bijective ((restrictAut (le_sup_left (a := lubinTateField Ω hπ hf n) (b := E))).prod
      (restrictAut (le_sup_right (a := lubinTateField Ω hπ hf n) (b := E)))) := by
  have := hE.1
  have := hE.isGalois
  set M := lubinTateField Ω hπ hf n ⊔ E
  set Φ := (restrictAut (le_sup_left (a := lubinTateField Ω hπ hf n) (b := E))).prod
    (restrictAut (le_sup_right (a := lubinTateField Ω hπ hf n) (b := E)))
  have hinj : Function.Injective Φ := fun σ σ' h =>
    algEquiv_ext_sup (congrArg Prod.fst h) (congrArg Prod.snd h)
  refine hinj.bijective_of_nat_card_le ?_
  rw [Nat.card_prod, IsGalois.card_aut_eq_finrank, IsGalois.card_aut_eq_finrank,
    IsGalois.card_aut_eq_finrank]
  have he := ramificationIndex_dvd_of_le (le_sup_left (a := lubinTateField Ω hπ hf n) (b := E))
  have hf' := residueDegree_dvd_of_le (le_sup_right (a := lubinTateField Ω hπ hf n) (b := E))
  rw [ramificationIndex_lubinTateField hπ hf hn] at he
  rw [residueDegree_eq_finrank_of_unramified K E hE.ramificationIndex_eq_one] at hf'
  rw [← ramificationIndex_mul_residueDegree K M]
  exact Nat.mul_le_mul (Nat.le_of_dvd (ramificationIndex_pos K M) he)
    (Nat.le_of_dvd (residueDegree_pos K M) hf')

variable [FiniteDimensional K E] {m : ℕ} (hEm : Module.finrank K E = m)

omit [IsSepClosed Ω] in
include hE hEm in

theorem frobenius_generates :
    (∀ σ : E ≃ₐ[K] E, σ ∈ Subgroup.zpowers (frobenius K E hE.ramificationIndex_eq_one)) ∧
      Nat.card (E ≃ₐ[K] E) = m := by
  refine ⟨fun σ => ?_, ?_⟩
  · rw [zpowers_frobenius]
    exact Subgroup.mem_top σ
  · rw [card_algEquiv_of_unramified K E hE.ramificationIndex_eq_one, hEm]

def lubinTateUnramifiedGalEquiv :
    ((lubinTateField Ω hπ hf n ⊔ E : IntermediateField K Ω) ≃ₐ[K]
        (lubinTateField Ω hπ hf n ⊔ E : IntermediateField K Ω)) ≃*
      (𝒪[K] ⧸ Ideal.span {π ^ n})ˣ × Multiplicative (ZMod m) :=
  haveI := hE.isGalois
  (MulEquiv.ofBijective _ (bijective_restrictAut_prod hπ hf hn hE)).trans
    (MulEquiv.prodCongr (lubinTateGalEquiv hπ hf n)
      (zmodMulEquivOfGenerator (frobenius_generates hE hEm).1
        (frobenius_generates hE hEm).2).symm)

include hn hE in

theorem lubinTateUnramified_mul_comm
    (σ τ : (lubinTateField Ω hπ hf n ⊔ E : IntermediateField K Ω) ≃ₐ[K]
      (lubinTateField Ω hπ hf n ⊔ E : IntermediateField K Ω)) :
    σ * τ = τ * σ :=
  (lubinTateUnramifiedGalEquiv hπ hf hn hE (m := Module.finrank K E) rfl).injective (by
    rw [map_mul, map_mul]
    refine Prod.ext ?_ ?_
    · rw [Prod.fst_mul, Prod.fst_mul]
      exact mul_comm (G := (𝒪[K] ⧸ Ideal.span {π ^ n})ˣ) _ _
    · rw [Prod.snd_mul, Prod.snd_mul]
      exact mul_comm (G := Multiplicative (ZMod (Module.finrank K E))) _ _)

end Unramified

end FormalGroup

end RHDirect.CFT.LocalField
end Sec_LubinTateUnramified


/-! ### LubinTateLimit -/
section Sec_LubinTateLimit


open _root_.IntermediateField Topology Filter

namespace RHDirect.CFT.LocalField

open ValuativeRel RHDirect.CFT_AbstractLocalReciprocity

namespace FormalGroup
open RHDirect.CFT.FormalGroups

section UnramifiedTower

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {Ω : Type*} [Field Ω] [Algebra K Ω] [IsSepClosed Ω]

variable (K Ω) in

def unramifiedTowerRoot (k : ℕ) : Ω :=
  Classical.choose (exists_isPrimitiveRoot_card_pow_sub_one (K := K) (Ksep := Ω)
    (Nat.factorial_ne_zero (k + 1)))

theorem isPrimitiveRoot_unramifiedTowerRoot (k : ℕ) :
    IsPrimitiveRoot (unramifiedTowerRoot K Ω k) (Nat.card 𝓀[K] ^ (k + 1).factorial - 1) := by
  unfold unramifiedTowerRoot
  exact Classical.choose_spec (exists_isPrimitiveRoot_card_pow_sub_one (K := K) (Ksep := Ω)
    (Nat.factorial_ne_zero (k + 1)))

variable (K Ω) in

def unramifiedTower (k : ℕ) : IntermediateField K Ω := K⟮unramifiedTowerRoot K Ω k⟯

theorem isUnramifiedSubextension_unramifiedTower (k : ℕ) :
    IsUnramifiedSubextension (unramifiedTower K Ω k) :=
  (isUnramifiedSubextension_adjoin (Nat.factorial_ne_zero _)
    (isPrimitiveRoot_unramifiedTowerRoot (K := K) (Ω := Ω) k)).1

theorem finrank_unramifiedTower (k : ℕ) :
    Module.finrank K (unramifiedTower K Ω k) = (k + 1).factorial :=
  (isUnramifiedSubextension_adjoin (Nat.factorial_ne_zero _)
    (isPrimitiveRoot_unramifiedTowerRoot (K := K) (Ω := Ω) k)).2

theorem le_unramifiedTower_of_isUnramifiedSubextension {E : IntermediateField K Ω}
    (hE : IsUnramifiedSubextension E) {k : ℕ} (hk : Module.finrank K E ≤ k + 1) :
    E ≤ unramifiedTower K Ω k := by
  have := hE.1
  exact hE.le_adjoin (Nat.factorial_ne_zero _)
    (Nat.dvd_factorial Module.finrank_pos hk) (isPrimitiveRoot_unramifiedTowerRoot k)

theorem monotone_unramifiedTower : Monotone (unramifiedTower K Ω) := fun j k h => by
  have := (isUnramifiedSubextension_unramifiedTower (K := K) (Ω := Ω) j).1
  exact (isUnramifiedSubextension_unramifiedTower j).le_adjoin (Nat.factorial_ne_zero _)
    (by rw [finrank_unramifiedTower]; exact Nat.factorial_dvd_factorial (Nat.succ_le_succ h))
    (isPrimitiveRoot_unramifiedTowerRoot k)

theorem unramifiedTower_le_maximalUnramifiedExtension (k : ℕ) :
    unramifiedTower K Ω k ≤ maximalUnramifiedExtension K Ω :=
  (isUnramifiedSubextension_unramifiedTower k).le_maximalUnramifiedExtension

theorem exists_mem_unramifiedTower {x : Ω} (hx : x ∈ maximalUnramifiedExtension K Ω) :
    ∃ k, x ∈ unramifiedTower K Ω k := by
  obtain ⟨E, hE, hxE⟩ := mem_maximalUnramifiedExtension_iff.mp hx
  exact ⟨Module.finrank K E, le_unramifiedTower_of_isUnramifiedSubextension hE (Nat.le_succ _) hxE⟩

instance (k : ℕ) : IsGalois K (unramifiedTower K Ω k) :=
  (isUnramifiedSubextension_unramifiedTower k).isGalois

end UnramifiedTower

section MaxUnramified

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω] [IsSepClosed Ω]
variable {π : 𝒪[K]} (hπ : Irreducible π) {f : PowerSeries 𝒪[K]}

abbrev towerSup (hf : IsLubinTateSeries π f) (k : ℕ) : IntermediateField K Ω :=
  lubinTateField Ω hπ hf (k + 1) ⊔ unramifiedTower K Ω k

theorem monotone_towerSup (hf : IsLubinTateSeries π f) : Monotone (towerSup (Ω := Ω) hπ hf) :=
  fun _ _ h => sup_le_sup (lubinTateField_mono hπ hf (Nat.succ_le_succ h))
    (monotone_unramifiedTower h)

variable (Ω) in

abbrev lubinTateMaxUnramified (hπ : Irreducible π) : IntermediateField K Ω :=
  lubinTateLimit Ω hπ ⊔ maximalUnramifiedExtension K Ω

theorem towerSup_le (hf : IsLubinTateSeries π f) (k : ℕ) :
    towerSup (Ω := Ω) hπ hf k ≤ lubinTateMaxUnramified Ω hπ :=
  sup_le_sup (lubinTateField_le_lubinTateLimit hπ hf _) (unramifiedTower_le_maximalUnramifiedExtension k)

theorem exists_mem_towerSup (hf : IsLubinTateSeries π f) {x : Ω}
    (hx : x ∈ lubinTateMaxUnramified Ω hπ) : ∃ k, x ∈ towerSup hπ hf k := by
  have hle : lubinTateMaxUnramified Ω hπ ≤ ⨆ k, towerSup hπ hf k := by
    refine sup_le ?_ ?_
    · rw [lubinTateLimit_eq hπ hf]
      refine iSup_le fun n => ?_
      exact (lubinTateField_mono hπ hf n.le_succ).trans
        ((le_sup_left : _ ≤ towerSup hπ hf n).trans (le_iSup (towerSup hπ hf) n))
    · intro y hy
      obtain ⟨k, hk⟩ := exists_mem_unramifiedTower hy
      exact (le_iSup (towerSup hπ hf) k) ((le_sup_right : _ ≤ towerSup hπ hf k) hk)
  have := hle hx
  rw [← SetLike.mem_coe, IntermediateField.coe_iSup_of_directed
    (monotone_towerSup hπ hf).directed_le] at this
  simpa only [Set.mem_iUnion, SetLike.mem_coe] using this

def lubinTateMaxUnramifiedRestrict :
    (lubinTateMaxUnramified Ω hπ ≃ₐ[K] lubinTateMaxUnramified Ω hπ) →*
      (lubinTateLimit Ω hπ ≃ₐ[K] lubinTateLimit Ω hπ) ×
        (maximalUnramifiedExtension K Ω ≃ₐ[K] maximalUnramifiedExtension K Ω) :=
  (restrictAut le_sup_left).prod (restrictAut le_sup_right)

theorem lubinTateMaxUnramifiedRestrict_injective :
    Function.Injective (lubinTateMaxUnramifiedRestrict (Ω := Ω) hπ) := fun _ _ h =>
  algEquiv_ext_sup (congrArg Prod.fst h) (congrArg Prod.snd h)

theorem lubinTateMaxUnramifiedRestrict_surjective (hf : IsLubinTateSeries π f) :
    Function.Surjective (lubinTateMaxUnramifiedRestrict (Ω := Ω) hπ) := by
  rintro ⟨τ₁, τ₂⟩
  have hK : ∀ k, lubinTateField Ω hπ hf (k + 1) ≤ lubinTateLimit Ω hπ := fun k =>
    lubinTateField_le_lubinTateLimit hπ hf _
  have hE : ∀ k, unramifiedTower K Ω k ≤ maximalUnramifiedExtension K Ω :=
    unramifiedTower_le_maximalUnramifiedExtension
  have hσ := fun k => (bijective_restrictAut_prod hπ hf (Nat.succ_pos k)
    (isUnramifiedSubextension_unramifiedTower (K := K) (Ω := Ω) k)).2
      (restrictAut (hK k) τ₁, restrictAut (hE k) τ₂)
  choose σ hσ using hσ
  have hσ₁ : ∀ k, restrictAut le_sup_left (σ k) = restrictAut (hK k) τ₁ := fun k =>
    congrArg Prod.fst (hσ k)
  have hσ₂ : ∀ k, restrictAut le_sup_right (σ k) = restrictAut (hE k) τ₂ := fun k =>
    congrArg Prod.snd (hσ k)
  have hcompat : ∀ j k (h : j ≤ k), restrictAut (monotone_towerSup hπ hf h) (σ k) = σ j := by
    intro j k h
    apply algEquiv_ext_sup
    · rw [restrictAut_restrictAut, hσ₁ j,
        ← restrictAut_restrictAut (le_sup_left : _ ≤ towerSup hπ hf k)
          (lubinTateField_mono hπ hf (Nat.succ_le_succ h)),
        hσ₁ k, restrictAut_restrictAut]
    · rw [restrictAut_restrictAut, hσ₂ j,
        ← restrictAut_restrictAut (le_sup_right : _ ≤ towerSup hπ hf k)
          (monotone_unramifiedTower h), hσ₂ k, restrictAut_restrictAut]
  obtain ⟨ρ, hρ⟩ := exists_algEquiv_of_compatible (monotone_towerSup hπ hf) (towerSup_le hπ hf)
    (fun _ hx => exists_mem_towerSup hπ hf hx) σ hcompat
  refine ⟨ρ, Prod.ext ?_ ?_⟩
  · refine algEquiv_ext_of_restrictAut (F := fun k => lubinTateField Ω hπ hf (k + 1)) hK
      (fun x hx => ?_) fun k => ?_
    · obtain ⟨n, hn⟩ := (mem_lubinTateLimit_iff hπ hf).mp hx
      exact ⟨n, lubinTateField_mono hπ hf n.le_succ hn⟩
    · change restrictAut (hK k) (restrictAut le_sup_left ρ) = _
      rw [restrictAut_restrictAut,
        ← restrictAut_restrictAut (towerSup_le hπ hf k) (le_sup_left : _ ≤ towerSup hπ hf k),
        hρ k, hσ₁ k]
  · refine algEquiv_ext_of_restrictAut (F := unramifiedTower K Ω) hE
      (fun x hx => exists_mem_unramifiedTower hx) fun k => ?_
    change restrictAut (hE k) (restrictAut le_sup_right ρ) = _
    rw [restrictAut_restrictAut,
      ← restrictAut_restrictAut (towerSup_le hπ hf k) (le_sup_right : _ ≤ towerSup hπ hf k),
      hρ k, hσ₂ k]

variable [IsGalois K Ω]

def lubinTateMaxUnramifiedGalEquiv (hf : IsLubinTateSeries π f) :
    (lubinTateMaxUnramified Ω hπ ≃ₐ[K] lubinTateMaxUnramified Ω hπ) ≃ₜ*
      𝒪[K]ˣ × Multiplicative ℤ̂ :=
  let e := (MulEquiv.ofBijective (lubinTateMaxUnramifiedRestrict (Ω := Ω) hπ)
    ⟨lubinTateMaxUnramifiedRestrict_injective hπ, lubinTateMaxUnramifiedRestrict_surjective hπ hf⟩).trans
      (MulEquiv.prodCongr (lubinTateLimitGalEquiv hπ hf).symm.toMulEquiv
        (maximalUnramifiedExtensionGaloisEquiv K Ω).toMulEquiv)
  have hc : Continuous e :=
    (((lubinTateLimitGalEquiv hπ hf).symm.continuous.comp (continuous_restrictAut le_sup_left)).prodMk
      ((maximalUnramifiedExtensionGaloisEquiv K Ω).continuous.comp
        (continuous_restrictAut le_sup_right)))
  { e with
    continuous_toFun := hc
    continuous_invFun := (hc.homeoOfEquivCompactToT2 (f := e.toEquiv)).symm.continuous }

end MaxUnramified

end FormalGroup

end RHDirect.CFT.LocalField
end Sec_LubinTateLimit


/-! ### LubinTateReciprocity.RootEval -/
section Sec_LubinTateReciprocity_RootEval


namespace RHDirect.CFT.LocalField

open PowerSeries

section HomExt

variable {B S : Type*} [CommRing B] [CommRing S]

theorem powerSeries_ringHom_ext {J : Ideal S} (hJ : ∀ z : S, (∀ k : ℕ, z ∈ J ^ k) → z = 0)
    {Φ₁ Φ₂ : B⟦X⟧ →+* S} (hC : ∀ b : B, Φ₁ (C b) = Φ₂ (C b)) (hX : Φ₁ X = Φ₂ X)
    (hXJ : Φ₁ X ∈ J) : Φ₁ = Φ₂ := by
  have hpoly : Φ₁.comp (Polynomial.coeToPowerSeries.ringHom (R := B)) =
      Φ₂.comp (Polynomial.coeToPowerSeries.ringHom (R := B)) := by
    apply Polynomial.ringHom_ext
    · intro b
      simpa using hC b
    · simpa using hX
  have hp : ∀ p : Polynomial B, Φ₁ (p : B⟦X⟧) = Φ₂ (p : B⟦X⟧) := fun p =>
    congrArg (fun Φ : Polynomial B →+* S => Φ p) hpoly
  ext F
  refine sub_eq_zero.mp (hJ _ fun k => ?_)
  set G : B⟦X⟧ := PowerSeries.mk fun i => coeff (i + k) F
  have hF : Φ₁ F - Φ₂ F = Φ₁ X ^ k * (Φ₁ G - Φ₂ G) := by
    conv_lhs => rw [F.eq_X_pow_mul_shift_add_trunc k]
    rw [map_add, map_add, map_mul, map_mul, map_pow, map_pow, hp, ← hX]
    ring
  rw [hF]
  exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hXJ k)

end HomExt

section RootEval

variable {B : Type*} [CommRing B] {I : Ideal B} {P : Polynomial B}

variable [IsAdicComplete I B] (hP : P.IsDistinguishedAt I)

def rootEval : B⟦X⟧ →ₐ[B] AdjoinRoot P :=
  (hP.algEquivQuotient.symm.toAlgHom : B⟦X⟧ ⧸ Ideal.span {(P : B⟦X⟧)} →ₐ[B] AdjoinRoot P).comp
    (Ideal.Quotient.mkₐ B _)

theorem rootEval_coe (p : Polynomial B) : rootEval hP (p : B⟦X⟧) = AdjoinRoot.mk P p := by
  apply hP.algEquivQuotient.injective
  change hP.algEquivQuotient (hP.algEquivQuotient.symm _) = _
  rw [AlgEquiv.apply_symm_apply]
  rfl

@[simp]
theorem rootEval_X : rootEval hP X = AdjoinRoot.root P := by
  rw [← Polynomial.coe_X, rootEval_coe]
  rfl

@[simp]
theorem rootEval_C (b : B) : rootEval hP (C b) = AdjoinRoot.of P b := by
  rw [← Polynomial.coe_C, rootEval_coe, AdjoinRoot.mk_C]

theorem rootEval_eq_zero_iff (F : B⟦X⟧) :
    rootEval hP F = 0 ↔ F ∈ Ideal.span {(P : B⟦X⟧)} := by
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  change hP.algEquivQuotient.symm _ = 0 ↔ _
  rw [map_eq_zero_iff _ hP.algEquivQuotient.symm.injective]
  rfl

theorem rootEval_eq_rootEval_iff (F G : B⟦X⟧) :
    rootEval hP F = rootEval hP G ↔ F - G ∈ Ideal.span {(P : B⟦X⟧)} := by
  rw [← rootEval_eq_zero_iff hP, map_sub, sub_eq_zero]

theorem rootEval_self : rootEval hP (P : B⟦X⟧) = 0 := by
  rw [rootEval_coe, AdjoinRoot.mk_self]

theorem rootEval_subst_coe {G : B⟦X⟧} (hG : constantCoeff G = 0) (p : Polynomial B) :
    rootEval hP (subst G (p : B⟦X⟧)) = Polynomial.aeval (rootEval hP G) p := by
  rw [subst_coe (HasSubst.of_constantCoeff_zero' hG), Polynomial.aeval_algHom_apply]

theorem rootEval_mem_span_root {G : B⟦X⟧} (hG : constantCoeff G = 0) :
    rootEval hP G ∈ Ideal.span {AdjoinRoot.root P} := by
  obtain ⟨H, rfl⟩ := PowerSeries.X_dvd_iff.mpr hG
  rw [map_mul, rootEval_X]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

theorem isUnit_rootEval {G : B⟦X⟧} (hG : IsUnit (constantCoeff G)) :
    IsUnit (rootEval hP G) :=
  (PowerSeries.isUnit_iff_constantCoeff.mpr hG).map _

end RootEval

section Hausdorff

variable {B : Type*} [CommRing B] {I : Ideal B} {P : Polynomial B}

theorem root_pow_mem_map (hP : P.IsDistinguishedAt I) :
    AdjoinRoot.root P ^ P.natDegree ∈ I.map (AdjoinRoot.of P) := by
  have h : Polynomial.eval₂ (AdjoinRoot.of P) (AdjoinRoot.root P)
      (Polynomial.X ^ P.natDegree +
        ∑ i ∈ Finset.range P.natDegree, Polynomial.C (P.coeff i) * Polynomial.X ^ i) = 0 := by
    rw [← hP.monic.as_sum]
    exact AdjoinRoot.eval₂_root P
  rw [Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_finsetSum] at h
  rw [eq_neg_of_add_eq_zero_left h, neg_mem_iff]
  refine Ideal.sum_mem _ fun i hi => ?_
  rw [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X_pow]
  exact Ideal.mul_mem_right _ _
    (Ideal.mem_map_of_mem _ (hP.mem (Finset.mem_range.mp hi)))

theorem repr_mem_of_mem_map (hP : P.Monic) (J : Ideal B) {z : AdjoinRoot P}
    (hz : z ∈ J.map (AdjoinRoot.of P)) (i : Fin (AdjoinRoot.powerBasis' hP).dim) :
    (AdjoinRoot.powerBasis' hP).basis.repr z i ∈ J := by
  have hz' : z ∈ J • (⊤ : Submodule B (AdjoinRoot P)) := by
    rw [Ideal.smul_top_eq_map]
    exact hz
  refine Submodule.smul_induction_on hz' (fun a ha m _ => ?_) (fun x y hx hy => ?_)
  · rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
    exact J.mul_mem_right _ ha
  · rw [map_add, Finsupp.add_apply]
    exact J.add_mem hx hy

theorem eq_zero_of_forall_mem_span_root_pow [IsHausdorff I B] (hP : P.IsDistinguishedAt I)
    {z : AdjoinRoot P} (hz : ∀ k : ℕ, z ∈ Ideal.span {AdjoinRoot.root P} ^ k) : z = 0 := by
  set pb := AdjoinRoot.powerBasis' hP.monic
  have hmem : ∀ k : ℕ, z ∈ (I ^ k).map (AdjoinRoot.of P) := by
    intro k
    have h := hz (P.natDegree * k)
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h
    obtain ⟨w, hw⟩ := h
    rw [hw, pow_mul, Ideal.map_pow]
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow (root_pow_mem_map hP) k)
  apply pb.basis.repr.injective
  ext i
  rw [map_zero, Finsupp.zero_apply]
  refine IsHausdorff.haus' (I := I) _ fun k => ?_
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
  exact repr_mem_of_mem_map hP.monic _ (hmem k) i

theorem rootEval_ringHom_ext [IsHausdorff I B] (hP : P.IsDistinguishedAt I)
    {Φ₁ Φ₂ : B⟦X⟧ →+* AdjoinRoot P}
    (hC : ∀ b : B, Φ₁ (C b) = Φ₂ (C b)) (hX : Φ₁ X = Φ₂ X)
    (hXJ : Φ₁ X ∈ Ideal.span {AdjoinRoot.root P}) : Φ₁ = Φ₂ :=
  powerSeries_ringHom_ext (fun _ hz => eq_zero_of_forall_mem_span_root_pow hP hz) hC hX hXJ

end Hausdorff

section Coordinates

variable {B : Type*} [CommRing B] {P : Polynomial B}

theorem eq_zero_of_of_mul_eq_zero (hP : P.Monic) {b : B} (hb : ∀ c : B, b * c = 0 → c = 0)
    {z : AdjoinRoot P} (h : AdjoinRoot.of P b * z = 0) : z = 0 := by
  set pb := AdjoinRoot.powerBasis' hP
  have h' : b • z = 0 := by
    rw [Algebra.smul_def]
    exact h
  apply pb.basis.repr.injective
  ext i
  have := congrArg (fun w => pb.basis.repr w i) h'
  simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, map_zero, Finsupp.zero_apply] at this
  rw [map_zero, Finsupp.zero_apply]
  exact hb _ this

theorem eq_zero_of_mul_eq_zero_of_pow_eq (hP : P.Monic) {b : B}
    (hb : ∀ c : B, b * c = 0 → c = 0) {y : AdjoinRoot P} {k : ℕ} (hk : k ≠ 0)
    (hy : y ^ k = AdjoinRoot.of P b) {z : AdjoinRoot P} (h : y * z = 0) : z = 0 := by
  refine eq_zero_of_of_mul_eq_zero hP hb ?_
  rw [← hy]
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
  rw [pow_succ, mul_assoc, h, mul_zero]

end Coordinates

end RHDirect.CFT.LocalField
end Sec_LubinTateReciprocity_RootEval


/-! ### LubinTateReciprocity.TwistedPoint -/
section Sec_LubinTateReciprocity_TwistedPoint


open PowerSeries IsLocalRing ValuativeRel RHDirect.CFT.FormalGroups RHDirect.CFT.LocalField.FormalGroup

namespace RHDirect.CFT.LocalField

section Series

variable {R : Type*} [CommRing R]

theorem coe_comp_eq_subst (p q : Polynomial R) (hq : q.coeff 0 = 0) :
    ((p.comp q : Polynomial R) : R⟦X⟧) = subst (q : R⟦X⟧) (p : R⟦X⟧) := by
  rw [subst_coe (HasSubst.of_constantCoeff_zero' (by rw [Polynomial.constantCoeff_coe, hq])),
    Polynomial.comp_eq_aeval]
  have h := Polynomial.aeval_algHom_apply (Polynomial.coeToPowerSeries.algHom R) q p
  simp only [Polynomial.coeToPowerSeries.algHom_apply, Algebra.algebraMap_self, map_id] at h
  exact h.symm

theorem map_coe_polynomial {S : Type*} [CommRing S] (φ : R →+* S) (p : Polynomial R) :
    PowerSeries.map φ (p : R⟦X⟧) = ((p.map φ : Polynomial S) : S⟦X⟧) := by
  ext n
  simp

theorem constantCoeff_subst_of_constantCoeff_eq_zero {G : R⟦X⟧} (hG : constantCoeff G = 0)
    (F : R⟦X⟧) : constantCoeff (subst G F : R⟦X⟧) = constantCoeff F := by
  have hs := HasSubst.of_constantCoeff_zero' hG
  conv_lhs => rw [F.eq_X_mul_shift_add_const]
  rw [← coe_substAlgHom hs, map_add, map_mul, coe_substAlgHom hs, subst_X hs, subst_C]
  change constantCoeff (G * _ + PowerSeries.C _) = _
  rw [map_add, map_mul, hG, zero_mul, zero_add, constantCoeff_C]

theorem exists_subst_eq_mul {G W : R⟦X⟧} (hG : constantCoeff G = 0) (hW : constantCoeff W = 0) :
    ∃ V : R⟦X⟧, (subst G W : R⟦X⟧) = G * V ∧ constantCoeff V = coeff 1 W := by
  obtain ⟨W', rfl⟩ := PowerSeries.X_dvd_iff.mpr hW
  have hs := HasSubst.of_constantCoeff_zero' hG
  refine ⟨subst G W', ?_, ?_⟩
  · rw [← coe_substAlgHom hs, map_mul, coe_substAlgHom hs, subst_X hs]
  · rw [constantCoeff_subst_of_constantCoeff_eq_zero hG, ← coeff_zero_eq_constantCoeff_apply,
      ← coeff_succ_X_mul]

end Series

section Iterates

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {π : 𝒪[K]}

theorem ltPolyIter_succ_eq_mul (π : 𝒪[K]) (k : ℕ) :
    ltPolyIter π (k + 1) = ltPolyIter π k * ltEisenstein π k := by
  have hq := one_lt_card_residueField' K
  rw [ltPolyIter_succ, ltPoly, ltEisenstein, Polynomial.add_comp, Polynomial.mul_comp,
    Polynomial.C_comp, Polynomial.X_comp, Polynomial.X_pow_comp, mul_add, ← pow_succ',
    Nat.sub_add_cancel hq.le]
  ring

variable (hπ : Irreducible π)

theorem coe_ltPolyIter (k : ℕ) :
    ((ltPolyIter π k : Polynomial 𝒪[K]) : 𝒪[K]⟦X⟧) =
      (lubinTateHom hπ (isLubinTateSeries_ltPoly π) (isLubinTateSeries_ltPoly π)
        (π ^ k)).toPowerSeries := by
  induction k with
  | zero =>
    rw [pow_zero, lubinTateHom_self_one, Hom.toPowerSeries_id, ltPolyIter_zero, Polynomial.coe_X]
  | succ k ih =>
    rw [ltPolyIter_succ, coe_comp_eq_subst _ _ (coeff_zero_ltPolyIter π k), ih, pow_succ',
      lubinTateHom_mul hπ (isLubinTateSeries_ltPoly π) (isLubinTateSeries_ltPoly π)
        (isLubinTateSeries_ltPoly π), Hom.toPowerSeries_comp, lubinTateHom_self_uniformizer]

variable (B : Type*) [CommRing B] [Algebra 𝒪[K] B]

def ltSeries (a : 𝒪[K]) : B⟦X⟧ :=
  PowerSeries.map (algebraMap 𝒪[K] B)
    (lubinTateHom hπ (isLubinTateSeries_ltPoly π) (isLubinTateSeries_ltPoly π) a).toPowerSeries

variable {B}

theorem constantCoeff_ltSeries (a : 𝒪[K]) : constantCoeff (ltSeries hπ B a) = 0 := by
  rw [ltSeries, powerSeries_constantCoeff_map, Hom.constantCoeff_eq_zero, map_zero]

theorem coeff_one_ltSeries (a : 𝒪[K]) : coeff 1 (ltSeries hπ B a) = algebraMap 𝒪[K] B a := by
  rw [ltSeries, coeff_map, coeff_one_lubinTateHom]

theorem subst_ltSeries (a b : 𝒪[K]) :
    (subst (ltSeries hπ B b) (ltSeries hπ B a) : B⟦X⟧) = ltSeries hπ B (a * b) := by
  rw [ltSeries, ltSeries, ltSeries, lubinTateHom_mul hπ (isLubinTateSeries_ltPoly π)
    (isLubinTateSeries_ltPoly π) (isLubinTateSeries_ltPoly π), Hom.toPowerSeries_comp]
  exact (map_subst (HasSubst.of_constantCoeff_zero' (Hom.constantCoeff_eq_zero _)) _).symm

theorem map_ltSeries (φ : B →ₐ[𝒪[K]] B) (a : 𝒪[K]) :
    PowerSeries.map (φ : B →+* B) (ltSeries hπ B a) = ltSeries hπ B a :=
  powerSeries_map_sigma_map_algebraMap φ _

theorem ltSeries_one : ltSeries hπ B 1 = X := by
  rw [ltSeries, lubinTateHom_self_one, Hom.toPowerSeries_id, map_X]

theorem ltSeries_uniformizer_pow (k : ℕ) :
    ltSeries hπ B (π ^ k) = (((ltPolyIter π k).map (algebraMap 𝒪[K] B) : Polynomial B) : B⟦X⟧) := by
  rw [ltSeries, ← coe_ltPolyIter hπ, map_coe_polynomial]

end Iterates

section Root

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {π : 𝒪[K]} (hπ : Irreducible π)
  {B : Type*} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra 𝒪[K] B]
  (hunr : (maximalIdeal 𝒪[K]).map (algebraMap 𝒪[K] B) = maximalIdeal B)

variable (π B) in

abbrev ltEisB (m : ℕ) : Polynomial B :=
  (ltEisenstein π m).map (algebraMap 𝒪[K] B)

variable (π B) in
omit [IsDomain B] [IsDiscreteValuationRing B] in
theorem monic_ltEisB (m : ℕ) : (ltEisB π B m).Monic :=
  (ltEisenstein_monic π m).1.map _

omit [IsDomain B] [IsDiscreteValuationRing B] in
theorem ltEisB_eq (m : ℕ) :
    ltEisB π B m = Polynomial.C (algebraMap 𝒪[K] B π) +
      ((ltPolyIter π m).map (algebraMap 𝒪[K] B)) ^ (Nat.card 𝓀[K] - 1) := by
  rw [ltEisB, ltEisenstein, Polynomial.map_add, Polynomial.map_C, Polynomial.map_pow]

include hπ hunr in

theorem isDistinguishedAt_ltEisB (m : ℕ) : (ltEisB π B m).IsDistinguishedAt (maximalIdeal B) := by
  have hmon := (ltEisenstein_monic π m).1
  refine ⟨⟨fun {n} hn => ?_⟩, hmon.map _⟩
  rw [hmon.natDegree_map] at hn
  rw [Polynomial.coeff_map, ← hunr]
  exact Ideal.mem_map_of_mem _ ((isEisensteinAt_ltEisenstein hπ m).mem hn)

include hπ hunr in

theorem algebraMap_uniformizer_mul_eq_zero {c : B} (h : algebraMap 𝒪[K] B π * c = 0) : c = 0 := by
  have hπB := irreducible_algebraMap hunr hπ
  exact (mul_eq_zero.mp h).resolve_left hπB.ne_zero

end Root

section Coordinates

variable {B : Type*} [CommRing B] {P : Polynomial B}

theorem repr_ringHom_eq (T : AdjoinRoot P →+* AdjoinRoot P) (ψ : B → B)
    (hof : ∀ b : B, T (AdjoinRoot.of P b) = AdjoinRoot.of P (ψ b))
    (hroot : T (AdjoinRoot.root P) = AdjoinRoot.root P) (pb : PowerBasis B (AdjoinRoot P))
    (hgen : pb.gen = AdjoinRoot.root P) (z : AdjoinRoot P) (i : Fin pb.dim) :
    pb.basis.repr (T z) i = ψ (pb.basis.repr z i) := by
  have hTz : T z = ∑ j, ψ (pb.basis.repr z j) • pb.basis j := by
    conv_lhs => rw [← pb.basis.sum_repr z]
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, PowerBasis.coe_basis, map_pow, hgen,
      AdjoinRoot.algebraMap_eq, hof, hroot]
  rw [hTz, map_sum]
  simp only [map_smul, Module.Basis.repr_self, Finsupp.coe_finsetSum, Finset.sum_apply,
    Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

end Coordinates

section Twist

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {π : 𝒪[K]} (hπ : Irreducible π)
  {B : Type*} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra 𝒪[K] B]
  [IsAdicComplete (maximalIdeal B) B]
  (hunr : (maximalIdeal 𝒪[K]).map (algebraMap 𝒪[K] B) = maximalIdeal B) (m : ℕ)

include hπ hunr

theorem rootEval_subst_ltSeries_uniformizer_pow_succ {F : B⟦X⟧} (hF : constantCoeff F = 0) :
    rootEval (isDistinguishedAt_ltEisB hπ hunr m) (subst (ltSeries hπ B (π ^ (m + 1))) F) = 0 := by
  obtain ⟨V, hV, -⟩ := exists_subst_eq_mul (constantCoeff_ltSeries hπ (π ^ (m + 1))) hF
  rw [hV, map_mul, ltSeries_uniformizer_pow, ltPolyIter_succ_eq_mul, Polynomial.map_mul,
    Polynomial.coe_mul, map_mul, rootEval_self, mul_zero, zero_mul]

omit hπ hunr [IsDomain B] [IsDiscreteValuationRing B] [IsAdicComplete (maximalIdeal B) B] in

theorem aeval_root_ltPolyIter_pow :
    Polynomial.aeval (AdjoinRoot.root (ltEisB π B m)) ((ltPolyIter π m).map (algebraMap 𝒪[K] B)) ^ (Nat.card 𝓀[K] - 1) =
      AdjoinRoot.of (ltEisB π B m) (-algebraMap 𝒪[K] B π) := by
  have h : Polynomial.aeval (AdjoinRoot.root (ltEisB π B m))
      (Polynomial.C (algebraMap 𝒪[K] B π) +
        ((ltPolyIter π m).map (algebraMap 𝒪[K] B)) ^ (Nat.card 𝓀[K] - 1)) = 0 := by
    rw [← ltEisB_eq, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  rw [map_add, Polynomial.aeval_C, map_pow] at h
  rw [map_neg, eq_neg_of_add_eq_zero_right h]
  rfl

omit [IsAdicComplete (maximalIdeal B) B] in

theorem eq_zero_of_aeval_root_ltPolyIter_mul {z : AdjoinRoot (ltEisB π B m)}
    (h : Polynomial.aeval (AdjoinRoot.root (ltEisB π B m)) ((ltPolyIter π m).map (algebraMap 𝒪[K] B)) * z = 0) : z = 0 := by
  have hq := one_lt_card_residueField' K
  refine eq_zero_of_mul_eq_zero_of_pow_eq (monic_ltEisB π B m)
    (b := -algebraMap 𝒪[K] B π) (fun c hc => ?_) (by omega)
    (aeval_root_ltPolyIter_pow m) h
  rw [neg_mul, neg_eq_zero] at hc
  exact algebraMap_uniformizer_mul_eq_zero hπ hunr hc

theorem eq_zero_of_rootEval_subst_mul {W : B⟦X⟧} (hW : constantCoeff W = 0)
    (hW1 : IsUnit (coeff 1 W)) {z : AdjoinRoot (ltEisB π B m)}
    (h : rootEval (isDistinguishedAt_ltEisB hπ hunr m) (subst (ltSeries hπ B (π ^ m)) W) * z = 0) : z = 0 := by
  obtain ⟨V, hV, hV0⟩ := exists_subst_eq_mul (constantCoeff_ltSeries hπ (π ^ m)) hW
  rw [hV, map_mul, ltSeries_uniformizer_pow, rootEval_coe, ← AdjoinRoot.aeval_eq] at h
  have hu : IsUnit (rootEval (isDistinguishedAt_ltEisB hπ hunr m) V) := isUnit_rootEval _ (hV0 ▸ hW1)
  have h' := eq_zero_of_aeval_root_ltPolyIter_mul hπ hunr m (z := rootEval (isDistinguishedAt_ltEisB hπ hunr m) V * z) (by rw [← mul_assoc, h])
  exact (hu.mul_right_eq_zero).mp h'

theorem aeval_rootEval_ltSeries_eq_zero {a : 𝒪[K]} (ha : IsUnit a) :
    Polynomial.aeval (rootEval (isDistinguishedAt_ltEisB hπ hunr m) (ltSeries hπ B a)) (ltEisB π B m) = 0 := by
  have hs := constantCoeff_ltSeries (B := B) hπ a
  have h1 : Polynomial.aeval (rootEval (isDistinguishedAt_ltEisB hπ hunr m) (ltSeries hπ B a))
      ((ltPolyIter π (m + 1)).map (algebraMap 𝒪[K] B)) = 0 := by
    rw [← rootEval_subst_coe _ hs, ← ltSeries_uniformizer_pow hπ, subst_ltSeries, mul_comm,
      ← subst_ltSeries]
    exact rootEval_subst_ltSeries_uniformizer_pow_succ hπ hunr m hs
  have h2 : Polynomial.aeval (rootEval (isDistinguishedAt_ltEisB hπ hunr m) (ltSeries hπ B a)) ((ltPolyIter π m).map (algebraMap 𝒪[K] B)) =
      rootEval (isDistinguishedAt_ltEisB hπ hunr m) (subst (ltSeries hπ B (π ^ m)) (ltSeries hπ B a)) := by
    rw [← rootEval_subst_coe _ hs, ← ltSeries_uniformizer_pow hπ, subst_ltSeries, subst_ltSeries,
      mul_comm]
  rw [ltPolyIter_succ_eq_mul, Polynomial.map_mul, map_mul, h2] at h1
  exact eq_zero_of_rootEval_subst_mul hπ hunr m (constantCoeff_ltSeries hπ a)
    (by rw [coeff_one_ltSeries]; exact ha.map _) h1

omit hπ hunr [IsDomain B] [IsDiscreteValuationRing B] [IsAdicComplete (maximalIdeal B) B] in

theorem map_map_ltEisB (φ : B →ₐ[𝒪[K]] B) :
    (ltEisB π B m).map (φ : B →+* B) = ltEisB π B m := by
  rw [ltEisB, Polynomial.map_map, AlgHom.comp_algebraMap_of_tower]

variable (φ : B →ₐ[𝒪[K]] B) (u : 𝒪[K]ˣ)

def twistFrob : AdjoinRoot (ltEisB π B m) →+* AdjoinRoot (ltEisB π B m) :=
  AdjoinRoot.lift ((AdjoinRoot.of (ltEisB π B m)).comp (φ : B →+* B)) (rootEval (isDistinguishedAt_ltEisB hπ hunr m) (ltSeries hπ B ((u⁻¹ : 𝒪[K]ˣ) : 𝒪[K])))
    (by
      rw [← Polynomial.eval₂_map, map_map_ltEisB (K := K) (π := π) m φ]
      exact aeval_rootEval_ltSeries_eq_zero hπ hunr m (Units.isUnit _))

theorem twistFrob_of (b : B) :
    twistFrob hπ hunr m φ u (AdjoinRoot.of (ltEisB π B m) b) = AdjoinRoot.of (ltEisB π B m) (φ b) :=
  AdjoinRoot.lift_of _

theorem twistFrob_root :
    twistFrob hπ hunr m φ u (AdjoinRoot.root (ltEisB π B m)) = rootEval (isDistinguishedAt_ltEisB hπ hunr m) (ltSeries hπ B ((u⁻¹ : 𝒪[K]ˣ) : 𝒪[K])) :=
  AdjoinRoot.lift_root _

theorem twistFrob_rootEval (F : B⟦X⟧) :
    twistFrob hπ hunr m φ u (rootEval (isDistinguishedAt_ltEisB hπ hunr m) F) =
      rootEval (isDistinguishedAt_ltEisB hπ hunr m) (subst (ltSeries hπ B ((u⁻¹ : 𝒪[K]ˣ) : 𝒪[K])) (PowerSeries.map (φ : B →+* B) F)) := by
  have hs := HasSubst.of_constantCoeff_zero'
    (constantCoeff_ltSeries (B := B) hπ ((u⁻¹ : 𝒪[K]ˣ) : 𝒪[K]))
  have key : (twistFrob hπ hunr m φ u).comp (rootEval (isDistinguishedAt_ltEisB hπ hunr m) : B⟦X⟧ →ₐ[B] AdjoinRoot (ltEisB π B m)).toRingHom =
      (rootEval (isDistinguishedAt_ltEisB hπ hunr m) : B⟦X⟧ →ₐ[B] AdjoinRoot (ltEisB π B m)).toRingHom.comp
        ((substAlgHom hs : B⟦X⟧ →ₐ[B] B⟦X⟧).toRingHom.comp (PowerSeries.map (φ : B →+* B))) := by
    refine rootEval_ringHom_ext (isDistinguishedAt_ltEisB hπ hunr m)
      (fun b => ?_) ?_ ?_
    · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, rootEval_C,
        twistFrob_of, map_C, coe_substAlgHom, subst_C]
      exact (rootEval_C _ (φ b)).symm
    · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, rootEval_X,
        twistFrob_root, map_X, coe_substAlgHom, subst_X hs]
    · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, rootEval_X,
        twistFrob_root]
      exact rootEval_mem_span_root _ (constantCoeff_ltSeries hπ _)
  have := congrArg (fun Φ : B⟦X⟧ →+* AdjoinRoot (ltEisB π B m) => Φ F) key
  simpa [coe_substAlgHom] using this

theorem twistFrob_iterate_root (k : ℕ) :
    (twistFrob hπ hunr m φ u)^[k] (AdjoinRoot.root (ltEisB π B m)) = rootEval (isDistinguishedAt_ltEisB hπ hunr m) (ltSeries hπ B (((u⁻¹ : 𝒪[K]ˣ) : 𝒪[K]) ^ k)) := by
  induction k with
  | zero => rw [Function.iterate_zero, id, pow_zero, ltSeries_one, rootEval_X]
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, twistFrob_rootEval, map_ltSeries, subst_ltSeries,
      pow_succ]

theorem twistFrob_iterate_of (k : ℕ) (b : B) :
    (twistFrob hπ hunr m φ u)^[k] (AdjoinRoot.of (ltEisB π B m) b) = AdjoinRoot.of (ltEisB π B m) ((⇑φ)^[k] b) := by
  induction k generalizing b with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply, twistFrob_of, ih, ← Function.iterate_succ_apply]

theorem repr_twistFrob_iterate {N : ℕ} (hN : (twistFrob hπ hunr m φ u)^[N] (AdjoinRoot.root (ltEisB π B m)) =
      AdjoinRoot.root (ltEisB π B m))
    (z : AdjoinRoot (ltEisB π B m)) (i : Fin (AdjoinRoot.powerBasis' (monic_ltEisB π B m)).dim) :
    (AdjoinRoot.powerBasis' (monic_ltEisB π B m)).basis.repr
        ((twistFrob hπ hunr m φ u)^[N] z) i =
      (⇑φ)^[N] ((AdjoinRoot.powerBasis' (monic_ltEisB π B m)).basis.repr z i) := by
  have hTc : ⇑(twistFrob hπ hunr m φ u ^ N) = (twistFrob hπ hunr m φ u)^[N] := RingHom.coe_pow _ N
  have h := repr_ringHom_eq (twistFrob hπ hunr m φ u ^ N) ((⇑φ)^[N])
    (fun b => by rw [hTc, twistFrob_iterate_of]) (by rw [hTc, hN])
    (AdjoinRoot.powerBasis' (monic_ltEisB π B m)) (AdjoinRoot.powerBasis'_gen _) z i
  rwa [hTc] at h

end Twist

section Theta

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {π : 𝒪[K]} (hπ : Irreducible π)
  {B : Type*} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra 𝒪[K] B]
  [IsAdicComplete (maximalIdeal B) B] [IsAlgClosed (ResidueField B)]
  (hunr : (maximalIdeal 𝒪[K]).map (algebraMap 𝒪[K] B) = maximalIdeal B) (m : ℕ)
  (φ : B →ₐ[𝒪[K]] B) (hφ : ∀ x : B, residue B (φ x) = residue B x ^ Nat.card 𝓀[K])
  (u : 𝒪[K]ˣ)

include hφ in

theorem exists_twistFrob_fixed_root :
    ∃ x : AdjoinRoot (ltEisB π B m), twistFrob hπ hunr m φ u x = x ∧
      Polynomial.aeval x (ltEisB ((u : 𝒪[K]) * π) B m) = 0 := by
  have hπ' : Irreducible ((u : 𝒪[K]) * π) := (irreducible_units_mul u).2 hπ
  obtain ⟨θ, hθ1, -, hθφ, hθcomm, -⟩ := exists_iso_lubinTateFormalGroup hunr φ hφ hπ u
    (isLubinTateSeries_ltPoly π) (isLubinTateSeries_ltPoly ((u : 𝒪[K]) * π))
  set t := θ.hom.toPowerSeries with ht
  have ht0 : constantCoeff t = 0 := θ.hom.constantCoeff_eq_zero
  have hmap : PowerSeries.map (φ : B →+* B) t = subst (ltSeries hπ B (u : 𝒪[K])) t := hθφ
  have hcomm : ∀ a : 𝒪[K], (subst (ltSeries hπ B a) t : B⟦X⟧) = subst t (ltSeries hπ' B a) :=
    fun a => congrArg Hom.toPowerSeries (hθcomm a)
  have hs : ∀ a : 𝒪[K], HasSubst (ltSeries hπ B a) := fun a =>
    HasSubst.of_constantCoeff_zero' (constantCoeff_ltSeries hπ a)
  have hsub0 : ∀ a : 𝒪[K], constantCoeff (subst (ltSeries hπ B a) t : B⟦X⟧) = 0 := fun a => by
    rw [constantCoeff_subst_of_constantCoeff_eq_zero (constantCoeff_ltSeries hπ a), ht0]

  have hval : ∀ k : ℕ, Polynomial.aeval (rootEval (isDistinguishedAt_ltEisB hπ hunr m) t)
      ((ltPolyIter ((u : 𝒪[K]) * π) k).map (algebraMap 𝒪[K] B)) =
      rootEval (isDistinguishedAt_ltEisB hπ hunr m)
        (subst (ltSeries hπ B (π ^ k)) (subst (ltSeries hπ B ((u : 𝒪[K]) ^ k)) t)) := by
    intro k
    rw [← rootEval_subst_coe _ ht0, ← ltSeries_uniformizer_pow hπ', ← hcomm, mul_pow,
      ← subst_ltSeries, subst_comp_subst_apply (hs _) (hs _)]
  refine ⟨rootEval (isDistinguishedAt_ltEisB hπ hunr m) t, ?_, ?_⟩
  · rw [twistFrob_rootEval, hmap, subst_comp_subst_apply (hs _) (hs _), subst_ltSeries,
      Units.mul_inv, ltSeries_one, X_subst]
  · have h1 := hval (m + 1)
    rw [rootEval_subst_ltSeries_uniformizer_pow_succ hπ hunr m (hsub0 _), ltPolyIter_succ_eq_mul,
      Polynomial.map_mul, map_mul, hval m] at h1
    refine eq_zero_of_rootEval_subst_mul hπ hunr m (hsub0 _) ?_ h1
    rw [coeff_one_subst ht0 (constantCoeff_ltSeries hπ _), coeff_one_ltSeries]
    exact hθ1.mul ((u.isUnit.pow m).map _)

end Theta

end RHDirect.CFT.LocalField
end Sec_LubinTateReciprocity_TwistedPoint


/-! ### LubinTateReciprocity.Descent -/
section Sec_LubinTateReciprocity_Descent


open PowerSeries IsLocalRing ValuativeRel RHDirect.CFT.FormalGroups RHDirect.CFT.LocalField.FormalGroup
open scoped Topology

namespace RHDirect.CFT.LocalField

section PsEval

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω]

theorem psEval_add' {σ : Type*} [Finite σ] (F G : MvPowerSeries σ 𝒪[K]) (x : σ → Ω)
    (hx : ∀ i, valuation Ω (x i) < 1) :
    psEval (F + G) x = psEval F x + psEval G x := by
  have := t2Space_of_isValuativeTopology Ω
  have h := (hasSum_psEval' F x hx).add (hasSum_psEval' G x hx)
  have e : (fun d => psTerm F x d + psTerm G x d) = psTerm (F + G) x := by
    funext d
    simp [psTerm, add_mul]
  rw [e] at h
  exact h.tsum_eq

theorem psEval_mul' {σ : Type*} [Finite σ] (F G : MvPowerSeries σ 𝒪[K]) (x : σ → Ω)
    (hx : ∀ i, valuation Ω (x i) < 1) :
    psEval (F * G) x = psEval F x * psEval G x := by
  let E := IntermediateField.adjoin K (Set.range x)
  have := finiteDimensional_adjoin_range (K := K) x
  let xE : σ → E := fun i => ⟨x i, IntermediateField.subset_adjoin K _ ⟨i, rfl⟩⟩
  let a : σ → 𝒪[E] := fun i => ⟨xE i, ((valuation_coe_lt_one_iff E (xE i)).mp (hx i)).le⟩
  have ha : ∀ i, a i ∈ 𝓂[E] := fun i =>
    mem_maximalIdeal_integer_iff.mpr ((valuation_coe_lt_one_iff E (xE i)).mp (hx i))
  have h1 : psEval (F * G) x = _ := psEval_coe E (F * G) xE hx
  have h2 : psEval F x = _ := psEval_coe E F xE hx
  have h3 : psEval G x = _ := psEval_coe E G xE hx
  rw [h1, h2, h3]
  change ((psEval (F * G) fun i => (a i : E) : E) : Ω) =
    ((psEval F fun i => (a i : E) : E) : Ω) * ((psEval G fun i => (a i : E) : E) : Ω)
  let _ : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  have _ : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  let _ : UniformSpace 𝒪[K] := ⊥
  have _ : DiscreteUniformity 𝒪[K] := ⟨rfl⟩
  have hφ : Continuous[(⊥ : UniformSpace 𝒪[K]).toTopologicalSpace, _]
      (algebraMap 𝒪[K] 𝒪[E]) := by
    rw [UniformSpace.toTopologicalSpace_bot]
    exact continuous_bot
  rw [psEval_eq_eval₂ _ a ha, psEval_eq_eval₂ _ a ha, psEval_eq_eval₂ _ a ha,
    ← MvPowerSeries.coe_eval₂Hom hφ (hasEval_of_mem_maximalIdeal ha), map_mul]
  push_cast
  rfl

theorem psEval_eq_aeval_of_sub_mem {P h : Polynomial 𝒪[K]} {G : 𝒪[K]⟦X⟧}
    (hG : G - (h : 𝒪[K]⟦X⟧) ∈ Ideal.span {(P : 𝒪[K]⟦X⟧)}) {x : Ω} (hx : valuation Ω x < 1)
    (hP : Polynomial.aeval x (P.map (algebraMap 𝒪[K] K)) = 0) :
    psEval G (fun _ => x) = Polynomial.aeval x (h.map (algebraMap 𝒪[K] K)) := by
  have := t2Space_of_isValuativeTopology Ω
  obtain ⟨D, hD⟩ := Ideal.mem_span_singleton'.mp hG
  have hGe : G = (h : 𝒪[K]⟦X⟧) + D * (P : 𝒪[K]⟦X⟧) := by rw [hD]; ring
  rw [hGe, psEval_add' _ _ _ fun _ => hx, psEval_mul' _ _ _ fun _ => hx, psEval_polynomial,
    psEval_polynomial, hP, mul_zero, add_zero]

end PsEval

section Weierstrass

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {π : 𝒪[K]} (hπ : Irreducible π) (m : ℕ)

include hπ in

theorem isDistinguishedAt_ltEisenstein : (ltEisenstein π m).IsDistinguishedAt 𝓂[K] :=
  ⟨⟨fun hn => (isEisensteinAt_ltEisenstein hπ m).mem hn⟩, (ltEisenstein_monic π m).1⟩

include hπ in

theorem exists_sub_coe_mem_span_ltEisenstein (G : 𝒪[K]⟦X⟧) :
    ∃ h : Polynomial 𝒪[K], G - (h : 𝒪[K]⟦X⟧) ∈ Ideal.span {((ltEisenstein π m : Polynomial 𝒪[K]) :
      𝒪[K]⟦X⟧)} := by
  have := isAdicComplete_integer K
  have hP := isDistinguishedAt_ltEisenstein hπ m
  obtain ⟨h, hh⟩ := AdjoinRoot.mk_surjective (rootEval hP G)
  exact ⟨h, (rootEval_eq_rootEval_iff hP G h).mp (by rw [rootEval_coe, hh])⟩

variable {L : Type*} [Field L] [Algebra K L]

include hπ in

theorem ltEisenstein_dvd_of_aeval_eq_zero {x : L}
    (hx : Polynomial.aeval x ((ltEisenstein π m).map (algebraMap 𝒪[K] K)) = 0) {p : Polynomial 𝒪[K]}
    (hp : Polynomial.aeval x (p.map (algebraMap 𝒪[K] K)) = 0) : ltEisenstein π m ∣ p := by
  have hmon := (ltEisenstein_monic π m).1
  have hq := one_lt_card_residueField' K
  have hdeg : 0 < (ltEisenstein π m).natDegree := by
    rw [(ltEisenstein_monic π m).2]
    exact Nat.mul_pos (by omega) (pow_pos (by omega) m)
  have hirr := irreducible_map_of_isEisensteinAt (isEisensteinAt_ltEisenstein hπ m) hdeg
  have hint : IsIntegral K x := ⟨_, hmon.map _, hx⟩
  have hmin : minpoly K x = (ltEisenstein π m).map (algebraMap 𝒪[K] K) :=
    (minpoly.eq_of_irreducible_of_monic hirr hx (hmon.map _)).symm
  have hdvd : (ltEisenstein π m).map (algebraMap 𝒪[K] K) ∣ p.map (algebraMap 𝒪[K] K) :=
    hmin ▸ minpoly.dvd K x hp
  rw [← Polynomial.modByMonic_eq_zero_iff_dvd hmon]
  apply Polynomial.map_injective (algebraMap 𝒪[K] K) (IsFractionRing.injective 𝒪[K] K)
  rw [Polynomial.map_modByMonic _ hmon, Polynomial.map_zero,
    Polynomial.modByMonic_eq_zero_iff_dvd (hmon.map _)]
  exact hdvd

end Weierstrass

section Iterate

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω]
  {π : 𝒪[K]} (hπ : Irreducible π)

theorem pow_apply_eq_psEval (σ : Ω ≃ₐ[K] Ω) (a : 𝒪[K]) {x : Ω} (hx : valuation Ω x < 1)
    (hσ : σ x = psEval (lubinTateHom hπ (isLubinTateSeries_ltPoly π) (isLubinTateSeries_ltPoly π)
      a).toPowerSeries fun _ => x) (k : ℕ) :
    (σ ^ k) x = psEval (lubinTateHom hπ (isLubinTateSeries_ltPoly π) (isLubinTateSeries_ltPoly π)
      (a ^ k)).toPowerSeries fun _ => x := by
  induction k with
  | zero =>
    rw [pow_zero, pow_zero, lubinTateHom_self_one, Hom.toPowerSeries_id, AlgEquiv.one_apply]
    exact (psEval_X (K := K) (fun _ : Unit => x) ()).symm
  | succ k ih =>
    rw [pow_succ', AlgEquiv.mul_apply, ih, algEquiv_psEval σ _ _ fun _ => hx, hσ, pow_succ,
      lubinTateHom_mul hπ (isLubinTateSeries_ltPoly π) (isLubinTateSeries_ltPoly π)
        (isLubinTateSeries_ltPoly π), Hom.toPowerSeries_comp, PowerSeries.subst_def,
      psEval_subst' (fun _ => Hom.constantCoeff_eq_zero' _) _ _ fun _ => hx]

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeRel Ω]
  [TopologicalSpace Ω] [IsValuativeTopology Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω] in

theorem exists_pow_apply_eq_self (σ : Ω ≃ₐ[K] Ω) {p : Polynomial K} (hp : p ≠ 0) {x : Ω}
    (hx : Polynomial.aeval x p = 0) : ∃ N : ℕ, 0 < N ∧ (σ ^ N) x = x :=
  _root_.RHDirect.CFT_AbstractLocalReciprocity.PowerSubgroups.exists_pow_apply_eq_self_of_aeval_eq_zero σ hp hx

end Iterate

section Maps

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {B : Type*} [CommRing B] [Algebra 𝒪[K] B]

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in

theorem map_sub_coe_mem_span {P h : Polynomial 𝒪[K]} {G : 𝒪[K]⟦X⟧}
    (hG : G - (h : 𝒪[K]⟦X⟧) ∈ Ideal.span {(P : 𝒪[K]⟦X⟧)}) :
    PowerSeries.map (algebraMap 𝒪[K] B) G - ((h.map (algebraMap 𝒪[K] B) : Polynomial B) : B⟦X⟧) ∈
      Ideal.span {((P.map (algebraMap 𝒪[K] B) : Polynomial B) : B⟦X⟧)} := by
  have := Ideal.mem_map_of_mem (PowerSeries.map (algebraMap 𝒪[K] B)) hG
  rwa [Ideal.map_span, Set.image_singleton, map_sub, map_coe_polynomial, map_coe_polynomial] at this

theorem adjoinRoot_ringHom_ext {R S : Type*} [CommRing R] [CommRing S] {p : Polynomial R}
    {f g : AdjoinRoot p →+* S} (hof : ∀ r : R, f (AdjoinRoot.of p r) = g (AdjoinRoot.of p r))
    (hroot : f (AdjoinRoot.root p) = g (AdjoinRoot.root p)) : f = g := by
  apply Ideal.Quotient.ringHom_ext
  apply Polynomial.ringHom_ext
  · intro r
    exact hof r
  · exact hroot

end Maps

section Unramified

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω] [HasUnramifiedRoots K Ω]
  [IsGalois K Ω]

theorem apply_coe_eq_frobenius (σ : Ω ≃ₐ[K] Ω) (hσ : unramifiedDegree K Ω σ = Multiplicative.ofAdd 1)
    {L : IntermediateField K Ω} (hL : IsUnramifiedSubextension L) (y : L) :
    letI := hL.1
    σ (y : Ω) = ((frobenius K L hL.ramificationIndex_eq_one y : L) : Ω) := by
  have := hL.1
  have hr := (restrictNormal_eq_maximalUnramifiedExtensionFrobenius_iff σ).mpr hσ
  rw [← maximalUnramifiedExtensionFrobenius_inclusion hL y, ← hr]
  exact (AlgEquiv.restrictNormal_commutes σ (maximalUnramifiedExtension K Ω)
    (IntermediateField.inclusion hL.le_maximalUnramifiedExtension y)).symm

theorem completedFrobenius_iterate_integerToCompleted {L : IntermediateField K Ω}
    (hL : IsUnramifiedSubextension L) (k : ℕ) (c : 𝒪[L]) :
    letI := hL.1
    (completedFrobenius K Ω)^[k] (integerToCompleted K Ω hL.le_maximalUnramifiedExtension c) =
      integerToCompleted K Ω hL.le_maximalUnramifiedExtension
        (integerAlgEquiv K L (frobenius K L hL.ramificationIndex_eq_one ^ k) c) := by
  have := hL.1
  induction k with
  | zero => rw [Function.iterate_zero, id, pow_zero, map_one, AlgEquiv.one_apply]
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, completedFrobenius_integerToCompleted hL, pow_succ',
      map_mul, AlgEquiv.mul_apply]

theorem residue_completedFrobenius_iterate (k : ℕ) (x : CompletedUnramifiedIntegers K Ω) :
    residue _ ((completedFrobenius K Ω)^[k] x) = residue _ x ^ (Nat.card 𝓀[K] ^ k) := by
  induction k with
  | zero => rw [Function.iterate_zero, id, pow_zero, pow_one]
  | succ k ih =>
    rw [Function.iterate_succ_apply', residue_completedFrobenius, ih, ← pow_mul, ← pow_succ]

theorem exists_integerToCompleted_eq_of_iterate {L : IntermediateField K Ω}
    (hL : IsUnramifiedSubextension L) {b : CompletedUnramifiedIntegers K Ω}
    (hb : (completedFrobenius K Ω)^[Module.finrank K L] b = b) :
    ∃ c : 𝒪[L], integerToCompleted K Ω hL.le_maximalUnramifiedExtension c = b := by
  have := hL.1
  have h := hL.ramificationIndex_eq_one
  have := isAdicComplete_integer L
  set ι := integerToCompleted K Ω hL.le_maximalUnramifiedExtension with hι
  let _ : Algebra 𝒪[L] (CompletedUnramifiedIntegers K Ω) := ι.toRingHom.toAlgebra
  have hιa : ∀ c : 𝒪[L], algebraMap 𝒪[L] (CompletedUnramifiedIntegers K Ω) c = ι c := fun _ => rfl
  set N := Module.finrank K L with hN
  have hfrobN : frobenius K L h ^ N = 1 := by
    rw [hN, ← orderOf_frobenius K L h]
    exact pow_orderOf_eq_one _
  let T : CompletedUnramifiedIntegers K Ω →+* CompletedUnramifiedIntegers K Ω :=
    (completedFrobenius K Ω).toAlgHom.toRingHom ^ N
  have hT : ∀ x, T x = (completedFrobenius K Ω)^[N] x := fun x => by
    rw [RingHom.coe_pow]
    rfl
  have hTc : ∀ c : 𝒪[L], T (algebraMap 𝒪[L] (CompletedUnramifiedIntegers K Ω) c) =
      algebraMap 𝒪[L] (CompletedUnramifiedIntegers K Ω) c := fun c => by
    rw [hT, hιa, hι, completedFrobenius_iterate_integerToCompleted hL, hfrobN, map_one,
      AlgEquiv.one_apply]
  let σN : CompletedUnramifiedIntegers K Ω →ₐ[𝒪[L]] CompletedUnramifiedIntegers K Ω :=
    { toRingHom := T, commutes' := hTc }
  have hσN : ∀ x, σN x = (completedFrobenius K Ω)^[N] x := hT
  have hres : ∀ x, residue _ (σN x) = residue _ x ^ Nat.card (ResidueField 𝒪[L]) := fun x => by
    rw [hσN, residue_completedFrobenius_iterate, card_residueField_of_unramified K L h]
  have hunrL : (maximalIdeal 𝒪[L]).map (algebraMap 𝒪[L] (CompletedUnramifiedIntegers K Ω)) =
      maximalIdeal (CompletedUnramifiedIntegers K Ω) := by
    refine le_antisymm (Ideal.map_le_iff_le_comap.mpr fun x hx => ?_) ?_
    · rw [Ideal.mem_comap, hιa, hι, integerToCompleted_apply, mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      exact (mem_maximalIdeal x).mp hx (isUnit_of_map_unit _ _ (isUnit_of_map_unit _ _ hu))
    · rw [← map_maximalIdeal_completedUnramifiedIntegers K Ω]
      have hcomp : algebraMap 𝒪[K] (CompletedUnramifiedIntegers K Ω) =
          (algebraMap 𝒪[L] (CompletedUnramifiedIntegers K Ω)).comp (algebraMap 𝒪[K] 𝒪[L]) :=
        (ι.comp_algebraMap).symm
      rw [hcomp, ← Ideal.map_map]
      exact Ideal.map_mono (Ideal.map_le_iff_le_comap.mpr fun x hx =>
        map_nonunit (algebraMap 𝒪[K] 𝒪[L]) x hx)
  obtain ⟨c, hc⟩ := (mem_range_algebraMap_iff_fixed hunrL σN hres b).mpr (by rw [hσN]; exact hb)
  exact ⟨c, hc⟩

end Unramified

section Descent

variable {R : Type*} [CommRing R]

theorem eval₂_of_mk (f p q : Polynomial R) :
    Polynomial.eval₂ (AdjoinRoot.of f) (AdjoinRoot.mk f q) p = AdjoinRoot.mk f (p.comp q) :=
  (Polynomial.hom_eval₂ p Polynomial.C (AdjoinRoot.mk f) q).symm

theorem adjoinRoot_map_mk {S : Type*} [CommRing S] (ι : R →+* S) (p : Polynomial R) (q : Polynomial S)
    (h : q ∣ p.map ι) (g : Polynomial R) :
    AdjoinRoot.map ι p q h (AdjoinRoot.mk p g) = AdjoinRoot.mk q (g.map ι) := by
  have key : (AdjoinRoot.map ι p q h).comp (AdjoinRoot.mk p) =
      (AdjoinRoot.mk q).comp (Polynomial.mapRingHom ι) := by
    apply Polynomial.ringHom_ext
    · intro c
      simp
    · simp
  exact congrArg (fun F : Polynomial R →+* AdjoinRoot q => F g) key

theorem adjoinRoot_map_injective {S : Type*} [CommRing S] {ι : R →+* S} (hι : Function.Injective ι)
    {p : Polynomial R} (hp : p.Monic) {q : Polynomial S} (hq : q ∣ p.map ι) (hpq : p.map ι = q) :
    Function.Injective (AdjoinRoot.map ι p q hq) := by
  subst hpq
  rw [injective_iff_map_eq_zero]
  intro w hw
  obtain ⟨g, rfl⟩ := AdjoinRoot.mk_surjective w
  rw [adjoinRoot_map_mk, AdjoinRoot.mk_eq_zero, ← Polynomial.modByMonic_eq_zero_iff_dvd (hp.map ι),
    ← Polynomial.map_modByMonic ι hp] at hw
  rw [AdjoinRoot.mk_eq_zero, ← Polynomial.modByMonic_eq_zero_iff_dvd hp]
  exact Polynomial.map_injective ι hι (by rw [hw, Polynomial.map_zero])

theorem exists_adjoinRoot_twist (p : Polynomial R) (ψ : R →+* R) (hψ : p.map ψ = p) (g : Polynomial R)
    (hg : p ∣ p.comp g) :
    ∃ τ : AdjoinRoot p →+* AdjoinRoot p, (∀ c, τ (AdjoinRoot.of p c) = AdjoinRoot.of p (ψ c)) ∧
      τ (AdjoinRoot.root p) = AdjoinRoot.mk p g := by
  refine ⟨AdjoinRoot.lift ((AdjoinRoot.of p).comp ψ) (AdjoinRoot.mk p g) ?_,
    fun c => AdjoinRoot.lift_of _, AdjoinRoot.lift_root _⟩
  rw [← Polynomial.eval₂_map, hψ, eval₂_of_mk, AdjoinRoot.mk_eq_zero]
  exact hg

theorem exists_adjoinRoot_lift {S : Type*} [CommRing S] (p : Polynomial R) (jc : R →+* S) (x : S)
    (hx : p.eval₂ jc x = 0) :
    ∃ j : AdjoinRoot p →+* S, (∀ c, j (AdjoinRoot.of p c) = jc c) ∧ j (AdjoinRoot.root p) = x ∧
      ∀ g, j (AdjoinRoot.mk p g) = g.eval₂ jc x :=
  ⟨AdjoinRoot.lift jc x hx, fun _ => AdjoinRoot.lift_of _, AdjoinRoot.lift_root _,
    fun _ => AdjoinRoot.lift_mk _ _⟩

theorem exists_adjoinRoot_map_eq {S : Type*} [CommRing S] (ι : R →+* S) (p : Polynomial R)
    {q : Polynomial S} (hq : q ∣ p.map ι) (hqm : q.Monic) (z : AdjoinRoot q)
    (d : Fin (AdjoinRoot.powerBasis' hqm).dim → R)
    (hd : ∀ i, ι (d i) = (AdjoinRoot.powerBasis' hqm).basis.repr z i) :
    ∃ y : AdjoinRoot p, AdjoinRoot.map ι p q hq y = z := by
  refine ⟨∑ i, AdjoinRoot.of p (d i) * AdjoinRoot.root p ^ (i : ℕ), ?_⟩
  conv_rhs => rw [← (AdjoinRoot.powerBasis' hqm).basis.sum_repr z]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, map_pow, AdjoinRoot.map_of, AdjoinRoot.map_root, hd, Algebra.smul_def,
    PowerBasis.coe_basis, AdjoinRoot.powerBasis'_gen, AdjoinRoot.algebraMap_eq]

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω] [HasUnramifiedRoots K Ω]
  [IsGalois K Ω] [IsSepClosed Ω]
  {π : 𝒪[K]} (hπ : Irreducible π) (u : 𝒪[K]ˣ) (m : ℕ)

set_option maxHeartbeats 1000000 in
include hπ in

theorem exists_fixed_root_ltEisenstein (σ : Ω ≃ₐ[K] Ω)
    (hσ : unramifiedDegree K Ω σ = Multiplicative.ofAdd 1) {l : Ω}
    (hl : Polynomial.aeval l ((ltEisenstein π m).map (algebraMap 𝒪[K] K)) = 0)
    (hσl : σ l = psEval (lubinTateHom hπ (isLubinTateSeries_ltPoly π) (isLubinTateSeries_ltPoly π)
      ((u⁻¹ : 𝒪[K]ˣ) : 𝒪[K])).toPowerSeries fun _ => l) :
    ∃ x : Ω, Polynomial.aeval x ((ltEisenstein ((u : 𝒪[K]) * π) m).map (algebraMap 𝒪[K] K)) = 0 ∧
      σ x = x ∧ ∀ τ : Ω ≃ₐ[K] Ω, (∀ y ∈ maximalUnramifiedExtension K Ω, τ y = y) → τ l = l →
        τ x = x := by
  classical
  have hPmon : (ltEisenstein π m).Monic := (ltEisenstein_monic π m).1

  have hlv : valuation Ω l < 1 := by
    refine valuation_lt_one_of_aeval_ltPolyIter_eq_zero hπ (m + 1) ?_
    rw [ltPolyIter_succ_eq_mul, Polynomial.map_mul, map_mul, hl, mul_zero]

  obtain ⟨h, hh⟩ := exists_sub_coe_mem_span_ltEisenstein hπ m
    (lubinTateHom hπ (isLubinTateSeries_ltPoly π) (isLubinTateSeries_ltPoly π) ((u⁻¹ : 𝒪[K]ˣ) : 𝒪[K])).toPowerSeries
  have hσl' : σ l = Polynomial.aeval l (h.map (algebraMap 𝒪[K] K)) :=
    hσl.trans (psEval_eq_aeval_of_sub_mem hh hlv hl)

  obtain ⟨N, hN0, hNl⟩ := exists_pow_apply_eq_self σ ((hPmon.map (algebraMap 𝒪[K] K)).ne_zero) hl
  obtain ⟨hN', hhN'⟩ := exists_sub_coe_mem_span_ltEisenstein hπ m
    (lubinTateHom hπ (isLubinTateSeries_ltPoly π) (isLubinTateSeries_ltPoly π) (((u⁻¹ : 𝒪[K]ˣ) : 𝒪[K]) ^ N)).toPowerSeries
  have haevalN : Polynomial.aeval l (hN'.map (algebraMap 𝒪[K] K)) = l := by
    rw [← psEval_eq_aeval_of_sub_mem hhN' hlv hl, ← pow_apply_eq_psEval hπ σ _ hlv hσl N, hNl]
  have hdvdN : (ltEisenstein π m) ∣ hN' - Polynomial.X := by
    refine ltEisenstein_dvd_of_aeval_eq_zero hπ m hl ?_
    rw [Polynomial.map_sub, Polynomial.map_X, map_sub, haevalN, Polynomial.aeval_X, sub_self]
  have hGN : (lubinTateHom hπ (isLubinTateSeries_ltPoly π) (isLubinTateSeries_ltPoly π) (((u⁻¹ : 𝒪[K]ˣ) : 𝒪[K]) ^ N)).toPowerSeries -
      ((Polynomial.X : Polynomial 𝒪[K]) : 𝒪[K]⟦X⟧) ∈ Ideal.span {((ltEisenstein π m) : 𝒪[K]⟦X⟧)} := by
    obtain ⟨q, hq⟩ := hdvdN
    have e : (lubinTateHom hπ (isLubinTateSeries_ltPoly π) (isLubinTateSeries_ltPoly π) (((u⁻¹ : 𝒪[K]ˣ) : 𝒪[K]) ^ N)).toPowerSeries -
        ((Polynomial.X : Polynomial 𝒪[K]) : 𝒪[K]⟦X⟧) =
        ((lubinTateHom hπ (isLubinTateSeries_ltPoly π) (isLubinTateSeries_ltPoly π) (((u⁻¹ : 𝒪[K]ˣ) : 𝒪[K]) ^ N)).toPowerSeries - (hN' : 𝒪[K]⟦X⟧)) +
          ((ltEisenstein π m) : 𝒪[K]⟦X⟧) * (q : 𝒪[K]⟦X⟧) := by
      rw [← Polynomial.coe_mul, ← hq, Polynomial.coe_sub]
      ring
    rw [e]
    exact add_mem hhN' (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))

  have hunr := map_maximalIdeal_completedUnramifiedIntegers K Ω
  obtain ⟨z, hzfix, hzroot⟩ := exists_twistFrob_fixed_root hπ hunr m
    (completedFrobenius K Ω).toAlgHom residue_completedFrobenius u
  set T := twistFrob hπ hunr m (completedFrobenius K Ω).toAlgHom u with hT
  have hP := isDistinguishedAt_ltEisB hπ hunr m
  have hTN : T^[N] (AdjoinRoot.root (ltEisB π (CompletedUnramifiedIntegers K Ω) m)) =
      AdjoinRoot.root (ltEisB π (CompletedUnramifiedIntegers K Ω) m) := by
    rw [hT, twistFrob_iterate_root, ← rootEval_X hP, rootEval_eq_rootEval_iff]
    have := map_sub_coe_mem_span (B := CompletedUnramifiedIntegers K Ω) hGN
    rwa [Polynomial.map_X, Polynomial.coe_X] at this

  have hzN : T^[N] z = z := Function.iterate_fixed hzfix N
  obtain ⟨L, ⟨hL, hLN⟩, -⟩ := existsUnique_isUnramifiedSubextension (K := K) (Ksep := Ω) hN0.ne'
  have := hL.1
  have hcoord : ∀ i, ∃ d : 𝒪[L], integerToCompleted K Ω hL.le_maximalUnramifiedExtension d =
      (AdjoinRoot.powerBasis' (monic_ltEisB π (CompletedUnramifiedIntegers K Ω) m)).basis.repr z i :=
      fun i => by
    refine exists_integerToCompleted_eq_of_iterate hL ?_
    rw [hLN]
    have := repr_twistFrob_iterate hπ hunr m (completedFrobenius K Ω).toAlgHom u hTN z i
    rw [← hT, hzN] at this
    exact this.symm
  choose d hd using hcoord

  have hPLmap : ((ltEisenstein π m).map (algebraMap 𝒪[K] 𝒪[L])).map
      (integerToCompleted K Ω hL.le_maximalUnramifiedExtension : 𝒪[L] →+* _) =
      ltEisB π (CompletedUnramifiedIntegers K Ω) m := by
    rw [Polynomial.map_map, AlgHom.comp_algebraMap]
  have hdvd : ltEisB π (CompletedUnramifiedIntegers K Ω) m ∣ ((ltEisenstein π m).map (algebraMap 𝒪[K] 𝒪[L])).map
      (integerToCompleted K Ω hL.le_maximalUnramifiedExtension : 𝒪[L] →+* _) := hPLmap ▸ dvd_rfl
  have hιinj : Function.Injective
      (integerToCompleted K Ω hL.le_maximalUnramifiedExtension : 𝒪[L] →+* CompletedUnramifiedIntegers K Ω) :=
    integerToCompleted_injective _
  have hinj := adjoinRoot_map_injective hιinj (hPmon.map (algebraMap 𝒪[K] 𝒪[L])) hdvd hPLmap
  obtain ⟨y, hy⟩ := exists_adjoinRoot_map_eq
    (integerToCompleted K Ω hL.le_maximalUnramifiedExtension : 𝒪[L] →+* CompletedUnramifiedIntegers K Ω)
    ((ltEisenstein π m).map (algebraMap 𝒪[K] 𝒪[L])) hdvd (monic_ltEisB π (CompletedUnramifiedIntegers K Ω) m) z d hd
  generalize hiM : AdjoinRoot.map
    (integerToCompleted K Ω hL.le_maximalUnramifiedExtension : 𝒪[L] →+* CompletedUnramifiedIntegers K Ω)
    ((ltEisenstein π m).map (algebraMap 𝒪[K] 𝒪[L])) (ltEisB π (CompletedUnramifiedIntegers K Ω) m) hdvd = iM at hinj hy
  have hiMof : ∀ c : 𝒪[L], iM (AdjoinRoot.of _ c) = AdjoinRoot.of _
      (integerToCompleted K Ω hL.le_maximalUnramifiedExtension c) := fun c => by
    rw [← hiM, AdjoinRoot.map_of]
    rfl
  have hiMroot : iM (AdjoinRoot.root _) = AdjoinRoot.root _ := by
    rw [← hiM, AdjoinRoot.map_root]
  have hiMmk : ∀ g : Polynomial 𝒪[L], iM (AdjoinRoot.mk _ g) = AdjoinRoot.mk _
      (g.map (integerToCompleted K Ω hL.le_maximalUnramifiedExtension : 𝒪[L] →+* _)) := fun g => by
    rw [← hiM, adjoinRoot_map_mk]

  have hPcomp : (ltEisenstein π m) ∣ (ltEisenstein π m).comp h := by
    refine ltEisenstein_dvd_of_aeval_eq_zero hπ m hl ?_
    rw [Polynomial.map_comp, Polynomial.aeval_comp, ← hσl']
    have e := Polynomial.aeval_algHom_apply (σ : Ω →ₐ[K] Ω) l ((ltEisenstein π m).map (algebraMap 𝒪[K] K))
    change Polynomial.aeval (σ l) _ = 0
    rw [show ((σ : Ω →ₐ[K] Ω) l) = σ l from rfl] at e
    rw [e, hl, map_zero]
  have hfrPL : ((ltEisenstein π m).map (algebraMap 𝒪[K] 𝒪[L])).map
      (integerAlgEquiv K L (frobenius K L hL.ramificationIndex_eq_one)).toAlgHom.toRingHom =
      (ltEisenstein π m).map (algebraMap 𝒪[K] 𝒪[L]) := by
    rw [Polynomial.map_map]
    congr 1
    exact RingHom.ext fun c => (integerAlgEquiv K L (frobenius K L hL.ramificationIndex_eq_one)).commutes c
  have hPcompL : (ltEisenstein π m).map (algebraMap 𝒪[K] 𝒪[L]) ∣
      ((ltEisenstein π m).map (algebraMap 𝒪[K] 𝒪[L])).comp (h.map (algebraMap 𝒪[K] 𝒪[L])) := by
    rw [← Polynomial.map_comp (f := algebraMap 𝒪[K] 𝒪[L])]
    exact Polynomial.map_dvd _ hPcomp
  obtain ⟨σL, hσLof, hσLroot⟩ := exists_adjoinRoot_twist ((ltEisenstein π m).map (algebraMap 𝒪[K] 𝒪[L]))
    (integerAlgEquiv K L (frobenius K L hL.ramificationIndex_eq_one)).toAlgHom.toRingHom hfrPL
    (h.map (algebraMap 𝒪[K] 𝒪[L])) hPcompL

  have hφι : ∀ c : 𝒪[L], (completedFrobenius K Ω).toAlgHom
      (integerToCompleted K Ω hL.le_maximalUnramifiedExtension c) =
      integerToCompleted K Ω hL.le_maximalUnramifiedExtension
        ((integerAlgEquiv K L (frobenius K L hL.ramificationIndex_eq_one)).toAlgHom.toRingHom c) :=
    fun c => completedFrobenius_integerToCompleted hL c
  have hsq1 : iM.comp σL = T.comp iM := by
    refine adjoinRoot_ringHom_ext (fun c => ?_) ?_
    · change iM (σL _) = T (iM _)
      rw [hσLof, hiMof, hiMof, hT, twistFrob_of, hφι]
    · change iM (σL _) = T (iM _)
      rw [hσLroot, hiMmk, hiMroot, hT, twistFrob_root,
        Polynomial.map_map, AlgHom.comp_algebraMap, ← rootEval_coe hP]
      exact ((rootEval_eq_rootEval_iff hP _ _).mpr (map_sub_coe_mem_span hh)).symm

  have hσLy : σL y = y := by
    apply hinj
    change (iM.comp σL) y = iM y
    rw [hsq1]
    change T (iM y) = iM y
    rw [hy, hzfix]

  have hiMofc : iM.comp (AdjoinRoot.of ((ltEisenstein π m).map (algebraMap 𝒪[K] 𝒪[L]))) =
      (AdjoinRoot.of (ltEisB π (CompletedUnramifiedIntegers K Ω) m)).comp
        (integerToCompleted K Ω hL.le_maximalUnramifiedExtension : 𝒪[L] →+* _) :=
    RingHom.ext hiMof
  have hy' : Polynomial.eval₂ (AdjoinRoot.of ((ltEisenstein π m).map (algebraMap 𝒪[K] 𝒪[L]))) y
      ((ltEisenstein ((u : 𝒪[K]) * π) m).map (algebraMap 𝒪[K] 𝒪[L])) = 0 := by
    apply hinj
    rw [map_zero, Polynomial.hom_eval₂, hiMofc, hy, ← Polynomial.eval₂_map, Polynomial.map_map,
      AlgHom.comp_algebraMap]
    exact hzroot

  have hjc : ((algebraMap L Ω).comp (algebraMap 𝒪[L] L)).comp (algebraMap 𝒪[K] 𝒪[L]) =
      (algebraMap K Ω).comp (algebraMap 𝒪[K] K) := by
    refine RingHom.ext fun c => ?_
    change algebraMap L Ω (algebraMap K L (c : K)) = algebraMap K Ω (c : K)
    exact (IsScalarTower.algebraMap_apply K L Ω (c : K)).symm
  obtain ⟨j, hjof, hjroot, hjmk⟩ := exists_adjoinRoot_lift
    ((ltEisenstein π m).map (algebraMap 𝒪[K] 𝒪[L])) ((algebraMap L Ω).comp (algebraMap 𝒪[L] L)) l
    (by rw [Polynomial.eval₂_map, hjc, ← Polynomial.eval₂_map]; exact hl)
  have hjc' : j.comp (AdjoinRoot.of ((ltEisenstein π m).map (algebraMap 𝒪[K] 𝒪[L]))) =
      (algebraMap L Ω).comp (algebraMap 𝒪[L] L) := RingHom.ext hjof

  have hsq2 : (σ : Ω →+* Ω).comp j = j.comp σL := by
    refine adjoinRoot_ringHom_ext (fun c => ?_) ?_
    · change σ (j _) = j (σL _)
      rw [hσLof, hjof, hjof]
      change σ ((c : L) : Ω) = (((integerAlgEquiv K L (frobenius K L hL.ramificationIndex_eq_one) c :
        𝒪[L]) : L) : Ω)
      rw [coe_integerAlgEquiv_apply]
      exact apply_coe_eq_frobenius σ hσ hL (c : L)
    · change σ (j _) = j (σL _)
      rw [hσLroot, hjmk, hjroot, hσl', Polynomial.eval₂_map, hjc, ← Polynomial.eval₂_map]
      rfl
  refine ⟨j y, ?_, ?_, ?_⟩
  · change Polynomial.eval₂ (algebraMap K Ω) (j y)
      ((ltEisenstein ((u : 𝒪[K]) * π) m).map (algebraMap 𝒪[K] K)) = 0
    rw [Polynomial.eval₂_map, ← hjc, ← Polynomial.eval₂_map, ← hjc', ← Polynomial.hom_eval₂, hy',
      map_zero]
  · change ((σ : Ω →+* Ω).comp j) y = j y
    rw [hsq2]
    change j (σL y) = j y
    rw [hσLy]
  · intro τ hτ hτl
    have hτj : (τ : Ω →+* Ω).comp j = j := by
      refine adjoinRoot_ringHom_ext (fun c => ?_) ?_
      · change τ (j _) = j _
        rw [hjof]
        exact hτ _ (hL.le_maximalUnramifiedExtension (c : L).2)
      · change τ (j _) = j _
        rw [hjroot]
        exact hτl
    change ((τ : Ω →+* Ω).comp j) y = j y
    rw [hτj]

end Descent

end RHDirect.CFT.LocalField
end Sec_LubinTateReciprocity_Descent


/-! ### LocalAxiomTransport -/
section Sec_LocalAxiomTransport

namespace RHDirect.CFT_AbstractLocalReciprocity

open RHDirect.CFT.LocalField (tateNorm invariants mem_invariants TateZero TateNegOne)

section Model

variable {G : Type*} [Group G] (A : Type*) [CommGroup A] [MulDistribMulAction G A]
  (K L : Subgroup G) (Γ : Type*) [Group Γ] (M : Type*) [CommGroup M] [MulDistribMulAction Γ M]

structure TateModel where
  le : L ≤ K

  hom : K →* Γ
  surjective_hom : Function.Surjective hom
  ker_hom : hom.ker = L.subgroupOf K

  equiv : fixedModule A L ≃* M

  coe_equiv_symm_smul : ∀ (σ : K) (a : fixedModule A L),
    ((equiv.symm (hom σ • equiv a) : fixedModule A L) : A) = (σ : G) • (a : A)

namespace TateModel

variable {A K L Γ M} (T : TateModel A K L Γ M)

include T in

theorem normal : (L.subgroupOf K).Normal :=
  T.ker_hom ▸ T.hom.normal_ker

theorem equiv_smul (σ : K) (a : fixedModule A L) (h : (σ : G) • (a : A) ∈ fixedModule A L) :
    T.equiv ⟨(σ : G) • (a : A), h⟩ = T.hom σ • T.equiv a := by
  rw [← T.equiv.apply_symm_apply (T.hom σ • T.equiv a)]
  congr 1
  exact Subtype.ext (T.coe_equiv_symm_smul σ a).symm

theorem mem_fixedModule_iff (a : fixedModule A L) :
    (a : A) ∈ fixedModule A K ↔ T.equiv a ∈ invariants Γ M := by
  constructor
  · intro ha γ
    obtain ⟨σ, rfl⟩ := T.surjective_hom γ
    have h : T.equiv.symm (T.hom σ • T.equiv a) = a :=
      Subtype.ext ((T.coe_equiv_symm_smul σ a).trans (ha σ σ.2))
    rw [← T.equiv.apply_symm_apply (T.hom σ • T.equiv a), h]
  · intro ha σ hσ
    rw [← T.coe_equiv_symm_smul ⟨σ, hσ⟩ a, ha, MulEquiv.symm_apply_apply]

def fixedModuleEquiv : fixedModule A K ≃* invariants Γ M where
  toFun a := ⟨T.equiv ⟨a, fixedModule_anti T.le a.2⟩,
    (T.mem_fixedModule_iff ⟨a, fixedModule_anti T.le a.2⟩).1 a.2⟩
  invFun m := ⟨T.equiv.symm m, (T.mem_fixedModule_iff _).2 (by simp [m.2])⟩
  left_inv a := by simp
  right_inv m := by simp
  map_mul' a b := by
    ext
    simp only [Subgroup.coe_mul]
    rw [← map_mul]
    rfl

@[simp]
theorem coe_fixedModuleEquiv (a : fixedModule A K) :
    (T.fixedModuleEquiv a : M) = T.equiv ⟨a, fixedModule_anti T.le a.2⟩ :=
  rfl

variable [(L.subgroupOf K).Normal]

noncomputable def quotientEquiv : K ⧸ L.subgroupOf K ≃* Γ :=
  (QuotientGroup.quotientMulEquivOfEq T.ker_hom.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective T.hom T.surjective_hom)

@[simp]
theorem quotientEquiv_mk (σ : K) : T.quotientEquiv (σ : K ⧸ L.subgroupOf K) = T.hom σ :=
  rfl

include T in

theorem relIndex_eq_natCard : L.relIndex K = Nat.card Γ :=
  Nat.card_congr T.quotientEquiv.toEquiv

theorem exists_cosetSMul (a : fixedModule A L) (q : K ⧸ L.subgroupOf K) :
    ∃ h : cosetSMul A K L a q ∈ fixedModule A L,
      T.equiv ⟨cosetSMul A K L a q, h⟩ = T.quotientEquiv q • T.equiv a := by
  induction q using QuotientGroup.induction_on with
  | H σ =>
    have h := smul_mem_fixedModule_of_normal T.le σ.2 a.2
    exact ⟨h, T.equiv_smul σ a h⟩

theorem norm_eq [Fintype Γ] [(L.subgroupOf K).FiniteIndex] (a : fixedModule A L) :
    T.equiv ⟨norm A K L a, fixedModule_anti T.le (norm A K L a).2⟩ = tateNorm Γ M (T.equiv a) := by
  classical
  let _ := Fintype.ofFinite (K ⧸ L.subgroupOf K)
  choose hmem hval using T.exists_cosetSMul a
  have hprod : (⟨norm A K L a, fixedModule_anti T.le (norm A K L a).2⟩ : fixedModule A L) =
      ∏ q, (⟨cosetSMul A K L a q, hmem q⟩ : fixedModule A L) := by
    ext
    rw [coe_norm, finprod_eq_prod_of_fintype, Subgroup.val_finsetProd]
  rw [hprod, map_prod, RHDirect.CFT.LocalField.tateNorm_apply]
  simp_rw [hval]
  exact Fintype.prod_equiv T.quotientEquiv.toEquiv _ _ fun _ => rfl

theorem map_range_norm [Fintype Γ] [(L.subgroupOf K).FiniteIndex] :
    (norm A K L).range.map T.fixedModuleEquiv.toMonoidHom =
      (tateNorm Γ M).range.subgroupOf (invariants Γ M) := by
  ext m
  simp only [Subgroup.mem_map, MonoidHom.mem_range, MulEquiv.coe_toMonoidHom,
    Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
    exact ⟨T.equiv a, by rw [coe_fixedModuleEquiv, T.norm_eq]⟩
  · rintro ⟨x, hx⟩
    refine ⟨_, ⟨T.equiv.symm x, rfl⟩, Subtype.ext ?_⟩
    rw [coe_fixedModuleEquiv, T.norm_eq, MulEquiv.apply_symm_apply, hx]

noncomputable def tateZeroEquiv [Fintype Γ] [(L.subgroupOf K).FiniteIndex] :
    tateZero A K L ≃* TateZero Γ M :=
  QuotientGroup.congr _ _ T.fixedModuleEquiv T.map_range_norm

include T in
theorem natCard_tateZero [Fintype Γ] [(L.subgroupOf K).FiniteIndex] :
    Nat.card (tateZero A K L) = Nat.card (TateZero Γ M) :=
  Nat.card_congr T.tateZeroEquiv.toEquiv

theorem norm_eq_one_iff [Fintype Γ] [(L.subgroupOf K).FiniteIndex] (a : fixedModule A L) :
    norm A K L a = 1 ↔ tateNorm Γ M (T.equiv a) = 1 := by
  rw [← T.norm_eq, MulEquiv.map_eq_one_iff]
  constructor
  · intro h
    ext
    simp [h]
  · intro h
    exact Subtype.ext (by simpa using congrArg Subtype.val h)

theorem map_ker_norm [Fintype Γ] [(L.subgroupOf K).FiniteIndex] :
    (norm A K L).ker.map T.equiv.toMonoidHom = (tateNorm Γ M).ker := by
  ext m
  simp only [Subgroup.mem_map, MonoidHom.mem_ker, MulEquiv.coe_toMonoidHom]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact (T.norm_eq_one_iff a).1 ha
  · intro hm
    exact ⟨T.equiv.symm m, (T.norm_eq_one_iff _).2 (by simpa using hm), by simp⟩

omit [(L.subgroupOf K).Normal] in

theorem augmentation_eq_map :
    augmentation A K L =
      (RHDirect.CFT.LocalField.augmentation Γ M).map
        ((fixedModule A L).subtype.comp T.equiv.symm.toMonoidHom) := by
  rw [augmentation, RHDirect.CFT.LocalField.augmentation, MonoidHom.map_closure]
  congr 1
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_image, MonoidHom.coe_comp, Subgroup.coe_subtype,
    MulEquiv.coe_toMonoidHom, Function.comp_apply]
  constructor
  · rintro ⟨g, hg, a, ha, rfl⟩
    refine ⟨T.hom ⟨g, hg⟩ • T.equiv ⟨a, ha⟩ / T.equiv ⟨a, ha⟩, ⟨_, _, rfl⟩, ?_⟩
    rw [map_div, Subgroup.coe_div, T.coe_equiv_symm_smul, MulEquiv.symm_apply_apply]
  · rintro ⟨_, ⟨γ, m, rfl⟩, rfl⟩
    obtain ⟨σ, rfl⟩ := T.surjective_hom γ
    refine ⟨σ, σ.2, T.equiv.symm m, (T.equiv.symm m).2, ?_⟩
    have h := T.coe_equiv_symm_smul σ (T.equiv.symm m)
    rw [MulEquiv.apply_symm_apply] at h
    rw [map_div, Subgroup.coe_div, h]

omit [(L.subgroupOf K).Normal] in

theorem mem_augmentation_iff (a : fixedModule A L) :
    (a : A) ∈ augmentation A K L ↔ T.equiv a ∈ RHDirect.CFT.LocalField.augmentation Γ M := by
  rw [T.augmentation_eq_map]
  constructor
  · rintro ⟨m, hm, h⟩
    have : T.equiv.symm m = a := Subtype.ext h
    rw [← this, MulEquiv.apply_symm_apply]
    exact hm
  · intro h
    exact ⟨T.equiv a, h, by simp⟩

noncomputable def kerEquiv [Fintype Γ] [(L.subgroupOf K).FiniteIndex] :
    (norm A K L).ker ≃* (tateNorm Γ M).ker :=
  (T.equiv.subgroupMap (norm A K L).ker).trans (MulEquiv.subgroupCongr T.map_ker_norm)

@[simp]
theorem coe_kerEquiv [Fintype Γ] [(L.subgroupOf K).FiniteIndex] (a : (norm A K L).ker) :
    (T.kerEquiv a : M) = T.equiv a :=
  rfl

noncomputable def tateNegOneEquiv [Fintype Γ] [(L.subgroupOf K).FiniteIndex] :
    tateNegOne A K L ≃* TateNegOne Γ M :=
  QuotientGroup.congr _ _ T.kerEquiv <| by
    ext m
    obtain ⟨a, rfl⟩ := T.kerEquiv.surjective m
    simp only [Subgroup.mem_map, Subgroup.mem_comap, Subgroup.mem_subgroupOf, MonoidHom.coe_comp,
      Subgroup.coe_subtype, Function.comp_apply, coe_kerEquiv]
    constructor
    · rintro ⟨x, hx, hxa⟩
      rw [T.kerEquiv.injective hxa] at hx
      exact (T.mem_augmentation_iff _).1 hx
    · intro h
      exact ⟨a, (T.mem_augmentation_iff _).2 h, rfl⟩

include T in
theorem natCard_tateNegOne [Fintype Γ] [(L.subgroupOf K).FiniteIndex] :
    Nat.card (tateNegOne A K L) = Nat.card (TateNegOne Γ M) :=
  Nat.card_congr T.tateNegOneEquiv.toEquiv

end TateModel

end Model

end RHDirect.CFT_AbstractLocalReciprocity
end Sec_LocalAxiomTransport


/-! ### LocalAxiomDictionary -/
section Sec_LocalAxiomDictionary

namespace RHDirect.CFT.LocalField

open RHDirect.CFT_AbstractLocalReciprocity _root_.IntermediateField

section Embeddings

variable (K L Ω : Type*) [Field K] [Field L] [Field Ω] [Algebra K L] [Algebra K Ω]
  [FiniteDimensional K L] [Algebra.IsSeparable K L]

theorem algebraMap_norm_eq_prod_embeddings_of_splits
    (hL : ∀ x : L, ((minpoly K x).map (algebraMap K Ω)).Splits) (x : L) :
    haveI : Fintype (L →ₐ[K] Ω) := Fintype.ofFinite _
    algebraMap K Ω (Algebra.norm K x) = ∏ τ : L →ₐ[K] Ω, τ x := by
  classical
  let _ : Fintype (L →ₐ[K] Ω) := Fintype.ofFinite _
  let ι : Ω →ₐ[K] AlgebraicClosure Ω := IsScalarTower.toAlgHom K Ω (AlgebraicClosure Ω)
  let c : (L →ₐ[K] Ω) → (L →ₐ[K] AlgebraicClosure Ω) := fun τ => ι.comp τ
  have hc : Function.Injective c := fun τ τ' h =>
    AlgHom.ext fun y => ι.toRingHom.injective (AlgHom.congr_fun h y)
  have hcard : Nat.card (L →ₐ[K] Ω) = Nat.card (L →ₐ[K] AlgebraicClosure Ω) := by
    rw [AlgHom.natCard_of_splits K L Ω hL, AlgHom.natCard_of_splits K L _
      (fun _ => IsAlgClosed.splits _)]
  have hbij : Function.Bijective c := by
    refine (Function.Injective.bijective_of_nat_card_le hc hcard.ge)
  apply ι.toRingHom.injective
  change ι (algebraMap K Ω _) = ι (∏ τ : L →ₐ[K] Ω, τ x)
  rw [AlgHom.commutes, map_prod, Algebra.norm_eq_prod_embeddings K (AlgebraicClosure Ω) x]
  exact (Fintype.prod_bijective c hbij _ _ fun τ => rfl).symm

end Embeddings

section Fields

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]

local notation "G" => Ω ≃ₐ[K] Ω

def fixingOpenSubgroup (L : IntermediateField K Ω) [FiniteDimensional K L] : OpenSubgroup G :=
  ⟨L.fixingSubgroup, L.fixingSubgroup_isOpen⟩

@[simp]
theorem coe_fixingOpenSubgroup (L : IntermediateField K Ω) [FiniteDimensional K L] :
    (fixingOpenSubgroup L : Subgroup G) = L.fixingSubgroup :=
  rfl

variable [IsGalois K Ω]

theorem fixingSubgroup_fixedField_openSubgroup (U : OpenSubgroup G) :
    (fixedField (U : Subgroup G)).fixingSubgroup = U :=
  InfiniteGalois.fixingSubgroup_fixedField (⟨(U : Subgroup G), U.isClosed⟩ : ClosedSubgroup G)

instance finiteDimensional_fixedField_openSubgroup (U : OpenSubgroup G) :
    FiniteDimensional K (fixedField (U : Subgroup G)) :=
  (InfiniteGalois.isOpen_iff_finite _).1 (by
    rw [fixingSubgroup_fixedField_openSubgroup]
    exact U.isOpen)

theorem fixedField_fixingOpenSubgroup (L : IntermediateField K Ω) [FiniteDimensional K L] :
    fixedField (fixingOpenSubgroup L : Subgroup G) = L :=
  InfiniteGalois.fixedField_fixingSubgroup L

theorem fixingOpenSubgroup_fixedField (U : OpenSubgroup G) :
    fixingOpenSubgroup (fixedField (U : Subgroup G)) = U :=
  OpenSubgroup.ext fun σ => by
    rw [← OpenSubgroup.mem_toSubgroup, coe_fixingOpenSubgroup,
      fixingSubgroup_fixedField_openSubgroup]
    rfl

theorem fixingSubgroup_le_fixingSubgroup_iff {L L' : IntermediateField K Ω} :
    L.fixingSubgroup ≤ L'.fixingSubgroup ↔ L' ≤ L := by
  constructor
  · intro h
    rw [← InfiniteGalois.fixedField_fixingSubgroup L, ← InfiniteGalois.fixedField_fixingSubgroup L']
    exact IntermediateField.fixedField_antitone h
  · intro h
    exact IntermediateField.fixingSubgroup_antitone h

theorem mem_iff_forall_fixingSubgroup (L : IntermediateField K Ω) (x : Ω) :
    x ∈ L ↔ ∀ σ ∈ L.fixingSubgroup, σ x = x := by
  conv_lhs => rw [← InfiniteGalois.fixedField_fixingSubgroup L]
  rw [IntermediateField.mem_fixedField_iff]

end Fields

section Units

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]

local notation "G" => Ω ≃ₐ[K] Ω

omit [IsGalois K Ω] in

theorem mem_fixedModule_units_iff' (H : Subgroup G) (a : Ωˣ) :
    a ∈ fixedModule Ωˣ H ↔ ∀ σ ∈ H, σ (a : Ω) = a := by
  rw [mem_fixedModule]
  refine forall₂_congr fun σ _ => ?_
  rw [Units.ext_iff]
  rfl

def unitsEquivOfForall {k : Type*} [Field k] [Algebra k Ω] (H : Subgroup G)
    (F : IntermediateField k Ω) (hF : ∀ x : Ω, x ∈ F ↔ ∀ σ ∈ H, σ x = x) :
    fixedModule Ωˣ H ≃* Fˣ where
  toFun a :=
    ⟨⟨((a : Ωˣ) : Ω), (hF _).2 ((mem_fixedModule_units_iff' H a).1 a.2)⟩,
      ⟨((a⁻¹ : fixedModule Ωˣ H) : Ωˣ), (hF _).2 ((mem_fixedModule_units_iff' H _).1 (a⁻¹).2)⟩,
      Subtype.ext (by simp), Subtype.ext (by simp)⟩
  invFun u := ⟨Units.map (algebraMap F Ω : F →* Ω) u,
    (mem_fixedModule_units_iff' H _).2 ((hF _).1 (by simp))⟩
  left_inv a := by
    ext
    rfl
  right_inv u := by
    ext
    rfl
  map_mul' a b := by
    ext
    rfl

omit [IsGalois K Ω] in
@[simp]
theorem coe_unitsEquivOfForall {k : Type*} [Field k] [Algebra k Ω] (H : Subgroup G)
    (F : IntermediateField k Ω) (hF : ∀ x : Ω, x ∈ F ↔ ∀ σ ∈ H, σ x = x) (a : fixedModule Ωˣ H) :
    (((unitsEquivOfForall H F hF a : Fˣ) : F) : Ω) = ((a : Ωˣ) : Ω) :=
  rfl

omit [IsGalois K Ω] in
@[simp]
theorem coe_unitsEquivOfForall_symm {k : Type*} [Field k] [Algebra k Ω] (H : Subgroup G)
    (F : IntermediateField k Ω) (hF : ∀ x : Ω, x ∈ F ↔ ∀ σ ∈ H, σ x = x) (u : Fˣ) :
    ((((unitsEquivOfForall H F hF).symm u : fixedModule Ωˣ H) : Ωˣ) : Ω) = ((u : F) : Ω) :=
  rfl

theorem mem_fixedModule_units_iff (L : IntermediateField K Ω) (a : Ωˣ) :
    a ∈ fixedModule Ωˣ L.fixingSubgroup ↔ (a : Ω) ∈ L := by
  rw [mem_iff_forall_fixingSubgroup, mem_fixedModule]
  refine forall₂_congr fun σ _ => ?_
  rw [Units.ext_iff]
  rfl

def fixedModuleUnitsEquiv (L : IntermediateField K Ω) : fixedModule Ωˣ L.fixingSubgroup ≃* Lˣ :=
  unitsEquivOfForall L.fixingSubgroup L (mem_iff_forall_fixingSubgroup L)

@[simp]
theorem coe_fixedModuleUnitsEquiv (L : IntermediateField K Ω)
    (a : fixedModule Ωˣ L.fixingSubgroup) :
    (((fixedModuleUnitsEquiv L a : Lˣ) : L) : Ω) = ((a : Ωˣ) : Ω) :=
  rfl

@[simp]
theorem coe_fixedModuleUnitsEquiv_symm (L : IntermediateField K Ω) (u : Lˣ) :
    ((((fixedModuleUnitsEquiv L).symm u : fixedModule Ωˣ L.fixingSubgroup) : Ωˣ) : Ω) =
      ((u : L) : Ω) :=
  rfl

noncomputable def baseUnitsEquiv : fixedModule Ωˣ (⊤ : Subgroup G) ≃* Kˣ :=
  (MulEquiv.subgroupCongr (by rw [IntermediateField.fixingSubgroup_bot])).trans <|
    (fixedModuleUnitsEquiv (⊥ : IntermediateField K Ω)).trans
      (Units.mapEquiv (IntermediateField.botEquiv K Ω).toMulEquiv)

omit [IsGalois K Ω] in
theorem algebraMap_botEquiv (y : (⊥ : IntermediateField K Ω)) :
    algebraMap K Ω (IntermediateField.botEquiv K Ω y) = (y : Ω) := by
  conv_rhs => rw [← (IntermediateField.botEquiv K Ω).symm_apply_apply y]
  rw [IntermediateField.botEquiv_symm]
  rfl

@[simp]
theorem algebraMap_baseUnitsEquiv (a : fixedModule Ωˣ (⊤ : Subgroup G)) :
    algebraMap K Ω (baseUnitsEquiv a : Kˣ) = ((a : Ωˣ) : Ω) := by
  simp only [baseUnitsEquiv, MulEquiv.trans_apply, Units.coe_mapEquiv]
  exact algebraMap_botEquiv _

theorem isDiscreteModule_units : IsDiscreteModule G Ωˣ := by
  rw [isDiscreteModule_iff]
  intro a
  have : FiniteDimensional K (IntermediateField.adjoin K {(a : Ω)}) :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral _)
  exact ⟨fixingOpenSubgroup (IntermediateField.adjoin K {(a : Ω)}),
    (mem_fixedModule_units_iff _ a).2 (IntermediateField.subset_adjoin K _ rfl)⟩

end Units

section Norm

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]

local notation "G" => Ω ≃ₐ[K] Ω

variable (L : IntermediateField K Ω)

def restrictEmbedding (σ : G) : L →ₐ[K] Ω :=
  (σ : Ω →ₐ[K] Ω).comp L.val

omit [IsGalois K Ω] in
@[simp]
theorem restrictEmbedding_apply (σ : G) (x : L) : restrictEmbedding L σ x = σ x :=
  rfl

omit [IsGalois K Ω] in

theorem restrictEmbedding_eq_iff (σ τ : G) :
    restrictEmbedding L σ = restrictEmbedding L τ ↔ σ⁻¹ * τ ∈ L.fixingSubgroup := by
  rw [IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro h x hx
    have h' : σ x = τ x := AlgHom.congr_fun h ⟨x, hx⟩
    rw [AlgEquiv.mul_apply, ← h', AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply]
  · intro h
    ext x
    have h' := h x x.2
    rw [AlgEquiv.mul_apply, AlgEquiv.aut_inv, AlgEquiv.symm_apply_eq] at h'
    exact h'.symm

theorem restrictEmbedding_surjective : Function.Surjective (restrictEmbedding L) := by
  intro τ
  let σ₀ : Ω →ₐ[K] Ω := τ.liftNormal Ω
  refine ⟨AlgEquiv.ofBijective σ₀ (Algebra.IsAlgebraic.algHom_bijective σ₀), ?_⟩
  ext x
  simp only [restrictEmbedding_apply, AlgEquiv.coe_ofBijective]
  exact τ.liftNormal_commutes Ω x

noncomputable def cosetEmbeddingEquiv :
    (⊤ : Subgroup G) ⧸ L.fixingSubgroup.subgroupOf ⊤ ≃ (L →ₐ[K] Ω) :=
  Equiv.ofBijective
    (Quotient.lift (fun σ : (⊤ : Subgroup G) => restrictEmbedding L σ) fun σ τ h => by
      have h' : σ⁻¹ * τ ∈ L.fixingSubgroup.subgroupOf ⊤ := QuotientGroup.leftRel_apply.mp h
      rw [Subgroup.mem_subgroupOf] at h'
      exact (restrictEmbedding_eq_iff L σ τ).2 (by simpa using h'))
    ⟨fun p q h => by
      induction p using QuotientGroup.induction_on with
      | H σ =>
      induction q using QuotientGroup.induction_on with
      | H τ =>
        rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
        simpa using (restrictEmbedding_eq_iff L σ τ).1 h,
     fun τ => by
      obtain ⟨σ, rfl⟩ := restrictEmbedding_surjective L τ
      exact ⟨((⟨σ, Subgroup.mem_top σ⟩ : (⊤ : Subgroup G)) : _ ⧸ _), rfl⟩⟩

@[simp]
theorem cosetEmbeddingEquiv_mk (σ : (⊤ : Subgroup G)) :
    cosetEmbeddingEquiv L (σ : (⊤ : Subgroup G) ⧸ L.fixingSubgroup.subgroupOf ⊤) =
      restrictEmbedding L σ :=
  rfl

variable [FiniteDimensional K L]

theorem coe_norm_top [(L.fixingSubgroup.subgroupOf ⊤).FiniteIndex]
    (a : fixedModule Ωˣ L.fixingSubgroup) :
    (((norm Ωˣ ⊤ L.fixingSubgroup a : fixedModule Ωˣ (⊤ : Subgroup G)) : Ωˣ) : Ω) =
      algebraMap K Ω (Algebra.norm K ((fixedModuleUnitsEquiv L a : Lˣ) : L)) := by
  classical
  have : Algebra.IsSeparable K L := Algebra.isSeparable_tower_bot_of_isSeparable K L Ω
  let _ := Fintype.ofFinite ((⊤ : Subgroup G) ⧸ L.fixingSubgroup.subgroupOf ⊤)
  let _ : Fintype (L →ₐ[K] Ω) := Fintype.ofFinite _
  have hsplit : ∀ x : L, ((minpoly K x).map (algebraMap K Ω)).Splits := fun x => by
    rw [← minpoly.algebraMap_eq (algebraMap L Ω).injective x]
    exact Normal.splits inferInstance _
  rw [algebraMap_norm_eq_prod_embeddings_of_splits K L Ω hsplit, coe_norm,
    finprod_eq_prod_of_fintype, Units.coe_prod]
  refine Fintype.prod_equiv (cosetEmbeddingEquiv L) _ _ fun q => ?_
  induction q using QuotientGroup.induction_on with
  | H σ => rfl

theorem baseUnitsEquiv_norm [(L.fixingSubgroup.subgroupOf ⊤).FiniteIndex]
    (a : fixedModule Ωˣ L.fixingSubgroup) :
    baseUnitsEquiv (norm Ωˣ ⊤ L.fixingSubgroup a) = normUnits K L (fixedModuleUnitsEquiv L a) := by
  ext
  apply (algebraMap K Ω).injective
  rw [algebraMap_baseUnitsEquiv, coe_norm_top, coe_normUnits]

end Norm

section Normal

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]

variable (K' L' : Subgroup (Ω ≃ₐ[K] Ω)) {E F : IntermediateField K Ω} (hEF : E ≤ F)
  (hK : E.fixingSubgroup = K') (hL : F.fixingSubgroup = L')

include hK hL in

theorem normal_extendScalars [(L'.subgroupOf K').Normal] :
    Normal E (extendScalars hEF) := by
  subst hK hL
  refine IntermediateField.normal_iff_forall_map_le'.2 fun σ' => ?_
  rintro _ ⟨x, hx, rfl⟩
  replace hx : ∀ τ ∈ F.fixingSubgroup, τ x = x := (mem_iff_forall_fixingSubgroup F x).1 hx
  show σ' x ∈ F
  rw [mem_iff_forall_fixingSubgroup]
  let σ : E.fixingSubgroup := (IntermediateField.fixingSubgroupEquiv E).symm σ'
  have hσ : ∀ y, (σ : Ω ≃ₐ[K] Ω) y = σ' y := fun _ => rfl
  intro τ hτ
  have hc : (σ : Ω ≃ₐ[K] Ω)⁻¹ * τ * σ ∈ F.fixingSubgroup := by
    have hτE : τ ∈ E.fixingSubgroup := IntermediateField.fixingSubgroup_antitone hEF hτ
    have := (inferInstance : (F.fixingSubgroup.subgroupOf E.fixingSubgroup).Normal).conj_mem
      ⟨τ, hτE⟩ (by simpa [Subgroup.mem_subgroupOf] using hτ) σ⁻¹
    simpa [Subgroup.mem_subgroupOf, mul_assoc] using this
  have h1 := hx _ hc
  simp only [AlgEquiv.mul_apply] at h1
  change τ (σ' x) = σ' x
  have h2 := congrArg (σ : Ω ≃ₐ[K] Ω) h1
  rwa [AlgEquiv.aut_inv, AlgEquiv.apply_symm_apply] at h2

instance isSeparable_extendScalars : Algebra.IsSeparable E (extendScalars hEF) :=
  have : Algebra.IsSeparable E Ω := Algebra.isSeparable_tower_top_of_isSeparable K E Ω
  Algebra.isSeparable_tower_bot_of_isSeparable E (extendScalars hEF) Ω

omit [IsGalois K Ω] in

theorem finiteDimensional_extendScalars [FiniteDimensional K F] :
    FiniteDimensional E (extendScalars hEF) :=
  have : FiniteDimensional K (extendScalars hEF) := inferInstanceAs (FiniteDimensional K F)
  Module.Finite.of_restrictScalars_finite K E (extendScalars hEF)

include hL in
theorem mem_extendScalars_iff_forall (x : Ω) : x ∈ extendScalars hEF ↔ ∀ σ ∈ L', σ x = x := by
  rw [IntermediateField.mem_extendScalars, mem_iff_forall_fixingSubgroup, hL]

variable [Normal E (extendScalars hEF)]

noncomputable def restrictHom : K' →* (extendScalars hEF ≃ₐ[E] extendScalars hEF) :=
  (AlgEquiv.restrictNormalHom (extendScalars hEF)).comp
    ((IntermediateField.fixingSubgroupEquiv E).toMonoidHom.comp
      (MulEquiv.subgroupCongr hK.symm).toMonoidHom)

omit [IsGalois K Ω] in
theorem coe_restrictHom_apply (σ : K') (x : extendScalars hEF) :
    ((restrictHom K' hEF hK σ x : extendScalars hEF) : Ω) = (σ : Ω ≃ₐ[K] Ω) x :=
  AlgEquiv.restrictNormal_commutes _ _ x

omit [IsGalois K Ω] in
include hL in
theorem ker_restrictHom : (restrictHom K' hEF hK).ker = L'.subgroupOf K' := by
  ext σ
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← hL, IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro h x hx
    have := congrArg
      (fun τ : (extendScalars hEF ≃ₐ[E] extendScalars hEF) =>
        ((τ ⟨x, hx⟩ : extendScalars hEF) : Ω)) h
    simpa [coe_restrictHom_apply] using this
  · intro h
    ext x
    rw [coe_restrictHom_apply]
    exact h x x.2

theorem restrictHom_surjective : Function.Surjective (restrictHom K' hEF hK) := by
  have : Normal E Ω := Normal.tower_top_of_normal K E Ω
  refine (AlgEquiv.restrictNormalHom_surjective (F := E) (K₁ := extendScalars hEF) (E := Ω)).comp ?_
  exact (IntermediateField.fixingSubgroupEquiv E).surjective.comp
    (MulEquiv.subgroupCongr hK.symm).surjective

noncomputable def galoisTateModel :
    TateModel Ωˣ K' L' (extendScalars hEF ≃ₐ[E] extendScalars hEF) (extendScalars hEF)ˣ where
  le := hK ▸ hL ▸ IntermediateField.fixingSubgroup_antitone hEF
  hom := restrictHom K' hEF hK
  surjective_hom := restrictHom_surjective K' hEF hK
  ker_hom := ker_restrictHom K' L' hEF hK hL
  equiv := unitsEquivOfForall L' (extendScalars hEF) (mem_extendScalars_iff_forall L' hEF hL)
  coe_equiv_symm_smul σ a := by
    ext
    rw [coe_unitsEquivOfForall_symm]
    change ((restrictHom K' hEF hK σ _ : extendScalars hEF) : Ω) = _
    rw [coe_restrictHom_apply]
    rfl

@[simp]
theorem coe_galoisTateModel_equiv (a : fixedModule Ωˣ L') :
    ((((galoisTateModel K' L' hEF hK hL).equiv a : (extendScalars hEF)ˣ) : extendScalars hEF) : Ω) =
      ((a : Ωˣ) : Ω) :=
  rfl

end Normal

section Relative

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]

variable (K' L' : Subgroup (Ω ≃ₐ[K] Ω)) {E F : IntermediateField K Ω} (hEF : E ≤ F)
  (hK : E.fixingSubgroup = K') (hL : F.fixingSubgroup = L')

include hK in
theorem mem_iff_forall_of_fixingSubgroup_eq (x : Ω) : x ∈ E ↔ ∀ σ ∈ K', σ x = x := by
  rw [mem_iff_forall_fixingSubgroup, hK]

def restrictEmbeddingRel (σ : K') : extendScalars hEF →ₐ[E] Ω :=
  ((IntermediateField.fixingSubgroupEquiv E ⟨σ, hK ▸ σ.2⟩ : Ω ≃ₐ[E] Ω) : Ω →ₐ[E] Ω).comp
    (extendScalars hEF).val

omit [IsGalois K Ω] in
@[simp]
theorem restrictEmbeddingRel_apply (σ : K') (x : extendScalars hEF) :
    restrictEmbeddingRel K' hEF hK σ x = (σ : Ω ≃ₐ[K] Ω) x :=
  rfl

omit [IsGalois K Ω] in
include hL in
theorem restrictEmbeddingRel_eq_iff (σ τ : K') :
    restrictEmbeddingRel K' hEF hK σ = restrictEmbeddingRel K' hEF hK τ ↔
      σ⁻¹ * τ ∈ L'.subgroupOf K' := by
  rw [Subgroup.mem_subgroupOf, ← hL, IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro h x hx
    have h' : (σ : Ω ≃ₐ[K] Ω) x = (τ : Ω ≃ₐ[K] Ω) x := AlgHom.congr_fun h ⟨x, hx⟩
    rw [Subgroup.coe_mul, Subgroup.coe_inv, AlgEquiv.mul_apply, ← h', AlgEquiv.aut_inv,
      AlgEquiv.symm_apply_apply]
  · intro h
    ext x
    have h' := h x x.2
    rw [Subgroup.coe_mul, Subgroup.coe_inv, AlgEquiv.mul_apply, AlgEquiv.aut_inv,
      AlgEquiv.symm_apply_eq] at h'
    exact h'.symm

theorem restrictEmbeddingRel_surjective : Function.Surjective (restrictEmbeddingRel K' hEF hK) := by
  intro τ
  have : Normal E Ω := Normal.tower_top_of_normal K E Ω
  have : Algebra.IsAlgebraic E Ω := Algebra.IsAlgebraic.tower_top (K := K) E
  let σ₀ : Ω →ₐ[E] Ω := τ.liftNormal Ω
  let σ' : Ω ≃ₐ[E] Ω := AlgEquiv.ofBijective σ₀ (Algebra.IsAlgebraic.algHom_bijective σ₀)
  let σ : E.fixingSubgroup := (IntermediateField.fixingSubgroupEquiv E).symm σ'
  refine ⟨⟨σ, hK ▸ σ.2⟩, ?_⟩
  ext x
  exact τ.liftNormal_commutes Ω x

noncomputable def cosetEmbeddingEquivRel : K' ⧸ L'.subgroupOf K' ≃ (extendScalars hEF →ₐ[E] Ω) :=
  Equiv.ofBijective
    (Quotient.lift (restrictEmbeddingRel K' hEF hK) fun σ τ h =>
      (restrictEmbeddingRel_eq_iff K' L' hEF hK hL σ τ).2 (QuotientGroup.leftRel_apply.mp h))
    ⟨fun p q h => by
      induction p using QuotientGroup.induction_on with
      | H σ =>
      induction q using QuotientGroup.induction_on with
      | H τ =>
        exact QuotientGroup.eq.2 ((restrictEmbeddingRel_eq_iff K' L' hEF hK hL σ τ).1 h),
     fun τ => by
      obtain ⟨σ, rfl⟩ := restrictEmbeddingRel_surjective K' hEF hK τ
      exact ⟨(σ : K' ⧸ L'.subgroupOf K'), rfl⟩⟩

include hK in

theorem coe_norm_eq_algebraMap_norm [FiniteDimensional K F] [(L'.subgroupOf K').FiniteIndex]
    (a : fixedModule Ωˣ L') :
    (((norm Ωˣ K' L' a : fixedModule Ωˣ K') : Ωˣ) : Ω) =
      algebraMap E Ω (Algebra.norm E
        ((unitsEquivOfForall L' (extendScalars hEF) (mem_extendScalars_iff_forall L' hEF hL) a :
          (extendScalars hEF)ˣ) : extendScalars hEF)) := by
  classical
  have := finiteDimensional_extendScalars hEF
  have : Normal E Ω := Normal.tower_top_of_normal K E Ω
  let _ := Fintype.ofFinite (K' ⧸ L'.subgroupOf K')
  let _ : Fintype (extendScalars hEF →ₐ[E] Ω) := Fintype.ofFinite _
  have hsplit : ∀ x : extendScalars hEF, ((minpoly E x).map (algebraMap E Ω)).Splits := fun x => by
    rw [← minpoly.algebraMap_eq (algebraMap (extendScalars hEF) Ω).injective x]
    exact Normal.splits inferInstance _
  rw [algebraMap_norm_eq_prod_embeddings_of_splits E (extendScalars hEF) Ω hsplit, coe_norm,
    finprod_eq_prod_of_fintype, Units.coe_prod]
  refine Fintype.prod_equiv (cosetEmbeddingEquivRel K' L' hEF hK hL) _ _ fun q => ?_
  induction q using QuotientGroup.induction_on with
  | H σ => rfl

theorem unitsEquivOfForall_norm [FiniteDimensional K F] [(L'.subgroupOf K').FiniteIndex]
    (a : fixedModule Ωˣ L') :
    unitsEquivOfForall K' E (mem_iff_forall_of_fixingSubgroup_eq K' hK) (norm Ωˣ K' L' a) =
      normUnits E (extendScalars hEF)
        (unitsEquivOfForall L' (extendScalars hEF) (mem_extendScalars_iff_forall L' hEF hL) a) := by
  ext
  change _ = algebraMap E Ω ((normUnits E (extendScalars hEF) _ : Eˣ) : E)
  rw [coe_normUnits, ← coe_norm_eq_algebraMap_norm K' L' hEF hK hL a]
  rfl

end Relative

end RHDirect.CFT.LocalField
end Sec_LocalAxiomDictionary


/-! ### LocalAxiom -/
section Sec_LocalAxiom

namespace RHDirect.CFT.LocalField

open RHDirect.CFT_AbstractLocalReciprocity ValuativeRel

section Valuation

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

noncomputable def ordUnitsHom : Kˣ →* Multiplicative ℤ̂ where
  toFun x := Multiplicative.ofAdd ((ord (x : K) : ℤ) : ℤ̂)
  map_one' := by
    rw [Units.val_one, ord_one, Int.cast_zero, ofAdd_zero]
  map_mul' x y := by
    rw [Units.val_mul, ord_mul x.ne_zero y.ne_zero, Int.cast_add, ofAdd_add]

@[simp]
theorem toAdd_ordUnitsHom (x : Kˣ) :
    (ordUnitsHom K x).toAdd = ((ord (x : K) : ℤ) : ℤ̂) :=
  rfl

variable {K} in

theorem exists_ordUnitsHom_eq (n : ℤ) :
    ∃ x : Kˣ, ordUnitsHom K x = Multiplicative.ofAdd (n : ℤ̂) := by
  obtain ⟨x, hx, h⟩ := exists_ord_eq K n
  refine ⟨Units.mk0 x hx, Multiplicative.toAdd.injective ?_⟩
  rw [toAdd_ordUnitsHom, Units.val_mk0, h, toAdd_ofAdd]

end Valuation

section Data

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (Ω : Type*) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

noncomputable def localValuation : fixedModule Ωˣ (⊤ : Subgroup (Ω ≃ₐ[K] Ω)) →* Multiplicative ℤ̂ :=
  (ordUnitsHom K).comp baseUnitsEquiv.toMonoidHom

theorem localValuation_apply (a : fixedModule Ωˣ (⊤ : Subgroup (Ω ≃ₐ[K] Ω))) :
    localValuation K Ω a = ordUnitsHom K (baseUnitsEquiv a) :=
  rfl

variable {K Ω}

theorem range_localValuation_comp_norm_of_eq (H : Subgroup (Ω ≃ₐ[K] Ω))
    [(H.subgroupOf ⊤).FiniteIndex] (L : IntermediateField K Ω) [FiniteDimensional K L]
    (hL : L.fixingSubgroup = H) :
    ((localValuation K Ω).comp (norm Ωˣ ⊤ H)).range =
      (localValuation K Ω).range.map (powMonoidHom (inertiaDegree (unramifiedDegree K Ω) H)) := by
  subst hL
  let := algebraicValuativeRel K Ω
  let := algebraicTopology K Ω
  have := algebraicValuativeRel_valuativeExtension K Ω
  have := algebraicTopology_isValuativeTopology K Ω
  have hsc : IsSepClosed Ω := IsSepClosure.sep_closed K
  rw [inertiaDegree_unramifiedDegree_fixingSubgroup]
  have key : ∀ u : Lˣ, ordUnitsHom K (normUnits K L u) =
      Multiplicative.ofAdd (((residueDegree K L : ℤ) * ord (u : L) : ℤ) : ℤ̂) := fun u => by
    apply Multiplicative.toAdd.injective
    rw [toAdd_ordUnitsHom, coe_normUnits, ord_norm, toAdd_ofAdd]
  ext z
  simp only [MonoidHom.mem_range, Subgroup.mem_map, MonoidHom.comp_apply, powMonoidHom_apply]
  constructor
  · rintro ⟨a, rfl⟩
    obtain ⟨x, hx⟩ := exists_ordUnitsHom_eq (K := K) (ord ((fixedModuleUnitsEquiv L a : Lˣ) : L))
    refine ⟨_, ⟨baseUnitsEquiv.symm x, rfl⟩, ?_⟩
    rw [localValuation_apply, localValuation_apply, MulEquiv.apply_symm_apply, hx,
      baseUnitsEquiv_norm, key]
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_ofAdd, toAdd_ofAdd, Int.cast_mul,
      Int.cast_natCast, nsmul_eq_mul]
  · rintro ⟨_, ⟨b, rfl⟩, rfl⟩
    obtain ⟨y, hy, hy'⟩ := exists_ord_eq L (ord ((baseUnitsEquiv b : Kˣ) : K))
    refine ⟨(fixedModuleUnitsEquiv L).symm (Units.mk0 y hy), ?_⟩
    rw [localValuation_apply, localValuation_apply, baseUnitsEquiv_norm, MulEquiv.apply_symm_apply,
      key, Units.val_mk0, hy']
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_ordUnitsHom, toAdd_ofAdd, Int.cast_mul,
      Int.cast_natCast, nsmul_eq_mul]

theorem intCast_mem_range_localValuation (n : ℤ) :
    Multiplicative.ofAdd (n : ℤ̂) ∈ (localValuation K Ω).range := by
  obtain ⟨x, hx⟩ := exists_ordUnitsHom_eq (K := K) n
  exact ⟨baseUnitsEquiv.symm x, by rw [localValuation_apply, MulEquiv.apply_symm_apply, hx]⟩

variable (K Ω)

noncomputable def localClassFieldData : ClassFieldData (Ω ≃ₐ[K] Ω) Ωˣ where
  deg := unramifiedDegree K Ω
  continuous_deg := unramifiedDegree_spec.1
  surjective_deg := unramifiedDegree_spec.2.1
  val := localValuation K Ω
  intCast_mem_range_val := intCast_mem_range_localValuation
  exists_eq_intCast_add_nsmul n _ a := by
    refine ⟨ord ((baseUnitsEquiv a : Kˣ) : K), 1, ?_⟩
    rw [map_one, toAdd_one, smul_zero, add_zero]
    rfl
  range_val_comp_norm U :=
    range_localValuation_comp_norm_of_eq (U : Subgroup (Ω ≃ₐ[K] Ω))
      (IntermediateField.fixedField (U : Subgroup (Ω ≃ₐ[K] Ω)))
      (fixingSubgroup_fixedField_openSubgroup U)

@[simp]
theorem localClassFieldData_deg : (localClassFieldData K Ω).deg = unramifiedDegree K Ω :=
  rfl

@[simp]
theorem localClassFieldData_val : (localClassFieldData K Ω).val = localValuation K Ω :=
  rfl

end Data

section Axiom

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

theorem natCard_tate_of_isCyclic (K' L' : Subgroup (Ω ≃ₐ[K] Ω)) [(L'.subgroupOf K').Normal]
    [(L'.subgroupOf K').FiniteIndex] (E F : IntermediateField K Ω) [FiniteDimensional K E]
    [FiniteDimensional K F] (hEF : E ≤ F) (hK : E.fixingSubgroup = K') (hL : F.fixingSubgroup = L')
    (hcyc : IsCyclic (K' ⧸ L'.subgroupOf K')) :
    Nat.card (tateZero Ωˣ K' L') = L'.relIndex K' ∧ Nat.card (tateNegOne Ωˣ K' L') = 1 := by
  let := algebraicValuativeRel K Ω
  let := algebraicTopology K Ω
  have := algebraicValuativeRel_valuativeExtension K Ω
  have := algebraicTopology_isValuativeTopology K Ω
  have : Algebra.IsAlgebraic E Ω := Algebra.IsAlgebraic.tower_top (K := K) E
  have := normal_extendScalars K' L' hEF hK hL
  have := finiteDimensional_extendScalars hEF
  have : IsGalois E (IntermediateField.extendScalars hEF) :=
    isGalois_iff.2 ⟨inferInstance, inferInstance⟩
  let T := galoisTateModel K' L' hEF hK hL
  have : IsCyclic (IntermediateField.extendScalars hEF ≃ₐ[E] IntermediateField.extendScalars hEF) :=
    isCyclic_of_surjective T.quotientEquiv.toMonoidHom T.quotientEquiv.surjective
  refine ⟨?_, ?_⟩
  · rw [T.natCard_tateZero, natCard_tateZero_units, T.relIndex_eq_natCard,
      IsGalois.card_aut_eq_finrank]
  · rw [T.natCard_tateNegOne, natCard_tateNegOne_units]

variable (K Ω) in

theorem classFieldAxiom_units : ClassFieldAxiom (Ω ≃ₐ[K] Ω) Ωˣ := by
  intro U V hVU _ hcyc
  exact natCard_tate_of_isCyclic (U : Subgroup (Ω ≃ₐ[K] Ω)) (V : Subgroup (Ω ≃ₐ[K] Ω))
    (IntermediateField.fixedField (U : Subgroup (Ω ≃ₐ[K] Ω)))
    (IntermediateField.fixedField (V : Subgroup (Ω ≃ₐ[K] Ω)))
    (IntermediateField.fixedField_antitone hVU) (fixingSubgroup_fixedField_openSubgroup U)
    (fixingSubgroup_fixedField_openSubgroup V) hcyc

end Axiom

section Theory

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (Ω : Type*) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

noncomputable def localClassFieldTheory : ClassFieldTheory (Ω ≃ₐ[K] Ω) Ωˣ where
  toClassFieldData := localClassFieldData K Ω
  isDiscreteModule := isDiscreteModule_units
  classFieldAxiom := classFieldAxiom_units K Ω

@[simp]
theorem localClassFieldTheory_deg : (localClassFieldTheory K Ω).deg = unramifiedDegree K Ω :=
  rfl

@[simp]
theorem localClassFieldTheory_val : (localClassFieldTheory K Ω).val = localValuation K Ω :=
  rfl

theorem localClassFieldTheory_val_apply (a : fixedModule Ωˣ (⊤ : Subgroup (Ω ≃ₐ[K] Ω))) :
    ((localClassFieldTheory K Ω).val a).toAdd = ((ord ((baseUnitsEquiv a : Kˣ) : K) : ℤ) : ℤ̂) :=
  rfl

end Theory

end RHDirect.CFT.LocalField
end Sec_LocalAxiom


/-! ### LubinTateReciprocity -/
section Sec_LubinTateReciprocity


open PowerSeries IsLocalRing ValuativeRel RHDirect.CFT.FormalGroups RHDirect.CFT.LocalField.FormalGroup _root_.IntermediateField

namespace RHDirect.CFT.LocalField

open RHDirect.CFT_AbstractLocalReciprocity

section Units

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {π : 𝒪[K]}

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in

theorem coe_ne_zero_of_irreducible (hπ : Irreducible π) : (π : K) ≠ 0 :=
  fun h => hπ.ne_zero (Subtype.ext h)

def unitUniformizerPow (hπ : Irreducible π) (u : 𝒪[K]ˣ) (k : ℤ) : Kˣ :=
  Units.map (algebraMap 𝒪[K] K : 𝒪[K] →* K) u * Units.mk0 (π : K) (coe_ne_zero_of_irreducible hπ) ^ k

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in

theorem coe_unitUniformizerPow_one (hπ : Irreducible π) (u : 𝒪[K]ˣ) :
    ((unitUniformizerPow hπ u 1 : Kˣ) : K) = (((u : 𝒪[K]) * π : 𝒪[K]) : K) := by
  rw [unitUniformizerPow, zpow_one, Units.val_mul, Units.coe_map, Units.val_mk0, Subring.coe_mul]
  rfl

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in

theorem unitUniformizerPow_mul (hπ : Irreducible π) (u : 𝒪[K]ˣ) (j : ℤ) :
    unitUniformizerPow hπ u 1 * unitUniformizerPow hπ 1 1 ^ j = unitUniformizerPow hπ u (1 + j) := by
  simp only [unitUniformizerPow, map_one, one_mul, zpow_one, mul_assoc]
  rw [zpow_add, zpow_one]

theorem ord_unitUniformizerPow_one (hπ : Irreducible π) (u : 𝒪[K]ˣ) :
    ord ((unitUniformizerPow hπ u 1 : Kˣ) : K) = 1 := by
  rw [coe_unitUniformizerPow_one, Subring.coe_mul, ord_mul (by simp) (coe_ne_zero_of_irreducible hπ),
    ord_unit, ord_uniformizer hπ, zero_add]

end Units

section Main

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [IsSepClosure K Ω]
  {π : 𝒪[K]} (hπ : Irreducible π) {f : PowerSeries 𝒪[K]} (hf : IsLubinTateSeries π f)

attribute [local instance] isDiscreteModule_units

include hπ hf in

theorem exists_lubinTate_frobenius {n : ℕ} (hn : 0 < n) (w : 𝒪[K]ˣ) :
    ∃ σ : Ω ≃ₐ[K] Ω, unramifiedDegree K Ω σ = Multiplicative.ofAdd 1 ∧
      ∀ x ∈ lubinTateTorsion Ω (hπ := hπ) hf n,
        lubinTateGalPointMap (hπ := hπ) hf σ x = ((w⁻¹ : 𝒪[K]ˣ) : 𝒪[K]) • x := by
  have : IsSepClosed Ω := IsSepClosure.sep_closed K
  let ρ0 : lubinTateField Ω hπ hf n ≃ₐ[K] lubinTateField Ω hπ hf n :=
    (lubinTateGalEquiv hπ hf n).symm
      (Units.map (Ideal.Quotient.mk (Ideal.span {π ^ n})).toMonoidHom w⁻¹)
  have hτ0 : ∀ y : lubinTateField Ω hπ hf n, ρ0.liftNormal Ω (y : Ω) = (ρ0 y : Ω) :=
    fun y => ρ0.liftNormal_commutes Ω y
  have hmap := map_unramifiedDegree_fixingSubgroup (K := K) (Ω := Ω) (lubinTateField Ω hπ hf n)
  rw [residueDegree_lubinTateField hπ hf hn] at hmap
  have hmem : (unramifiedDegree K Ω (ρ0.liftNormal Ω))⁻¹ * Multiplicative.ofAdd 1 ∈
      (lubinTateField Ω hπ hf n).fixingSubgroup.map (unramifiedDegree K Ω) := by
    rw [hmap]
    exact ⟨_, pow_one _⟩
  obtain ⟨ρ1, hρ1, hρ1d⟩ := Subgroup.mem_map.mp hmem
  refine ⟨ρ0.liftNormal Ω * ρ1, by rw [map_mul, hρ1d, mul_inv_cancel_left], fun x hx => ?_⟩
  apply IdealPoint.ext
  have hxE := val_mem_lubinTateField hπ hf hx
  rw [lubinTateGalPointMap_val, AlgEquiv.mul_apply,
    (mem_fixingSubgroup_iff (K := lubinTateField Ω hπ hf n) ρ1).mp hρ1 _ hxE]
  change ρ0.liftNormal Ω ((⟨x.val, hxE⟩ : lubinTateField Ω hπ hf n) : Ω) = _
  rw [hτ0]
  refine lubinTateGalEquiv_spec hf n ρ0 x hx _ ?_
  simp [ρ0]

include hπ hf in

theorem apply_root_eq_psEval (m : ℕ) (w : 𝒪[K]ˣ) (σ : Ω ≃ₐ[K] Ω)
    (hσ : ∀ x ∈ lubinTateTorsion Ω (hπ := hπ) hf (m + 1),
      lubinTateGalPointMap (hπ := hπ) hf σ x = ((w⁻¹ : 𝒪[K]ˣ) : 𝒪[K]) • x) {l : Ω}
    (hl : Polynomial.aeval l ((ltEisenstein π m).map (algebraMap 𝒪[K] K)) = 0) :
    σ l = psEval (lubinTateHom hπ (isLubinTateSeries_ltPoly π) (isLubinTateSeries_ltPoly π)
      ((w⁻¹ : 𝒪[K]ˣ) : 𝒪[K])).toPowerSeries fun _ => l := by
  have hl' : Polynomial.aeval l ((ltPolyIter π (m + 1)).map (algebraMap 𝒪[K] K)) = 0 := by
    rw [ltPolyIter_succ_eq_mul, Polynomial.map_mul, map_mul, hl, mul_zero]
  let lpt : IdealPoint Ω (lubinTateFormalGroup hπ (isLubinTateSeries_ltPoly π)) :=
    IdealPoint.mk l (valuation_lt_one_of_aeval_ltPolyIter_eq_zero hπ (m + 1) hl')
  have hlt : lpt ∈ lubinTateTorsion Ω (isLubinTateSeries_ltPoly π) (m + 1) :=
    (mem_lubinTateTorsion_ltPoly_iff (m + 1) lpt).mpr hl'
  have he := (lubinTatePointEquiv_mem_torsion_iff hf (isLubinTateSeries_ltPoly π) (m + 1) lpt).mpr hlt
  have h1 := hσ _ he
  have hcomm : lubinTateGalPointMap hf σ (lubinTatePointEquiv hf (isLubinTateSeries_ltPoly π) lpt) =
      lubinTatePointEquiv hf (isLubinTateSeries_ltPoly π)
        (lubinTateGalPointMap (isLubinTateSeries_ltPoly π) σ lpt) := by
    apply IdealPoint.ext
    rw [lubinTateGalPointMap_val, lubinTatePointEquiv_val, lubinTatePointEquiv_val,
      lubinTateGalPointMap_val, algEquiv_psEval σ _ _ fun _ => lpt.valuation_lt_one]
  have h2 := (lubinTatePointEquiv hf (isLubinTateSeries_ltPoly π)).injective
    (hcomm.symm.trans (h1.trans (map_smul _ _ _).symm))
  have h3 := congrArg IdealPoint.val h2
  rwa [lubinTateGalPointMap_val, lubinTate_smul_val] at h3

end Main

section Frobenius

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [IsSepClosure K Ω]
  {π : 𝒪[K]} (hπ : Irreducible π) {f : PowerSeries 𝒪[K]} (hf : IsLubinTateSeries π f)

attribute [local instance] isDiscreteModule_units

omit [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω] [ValuativeExtension K Ω] in

theorem inertiaDegree_unramifiedDegree_top :
    inertiaDegree (unramifiedDegree K Ω) (⊤ : Subgroup (Ω ≃ₐ[K] Ω)) = 1 := by
  rw [inertiaDegree, ← MonoidHom.range_eq_map,
    MonoidHom.range_eq_top_of_surjective _ unramifiedDegree_surjective, Subgroup.index_top]

include hπ hf in

theorem ramificationIndex_fixingSubgroup_lubinTateField {n : ℕ} (hn : 0 < n) :
    RHDirect.CFT_AbstractLocalReciprocity.ramificationIndex (unramifiedDegree K Ω) (lubinTateField Ω hπ hf n).fixingSubgroup =
      Module.finrank K (lubinTateField Ω hπ hf n) := by
  have : IsSepClosed Ω := IsSepClosure.sep_closed K
  have h := index_eq_mul unramifiedDegree_surjective (lubinTateField Ω hπ hf n).fixingSubgroup
  rw [inertiaDegree_unramifiedDegree_fixingSubgroup, residueDegree_lubinTateField hπ hf hn,
    mul_one, ← finrank_eq_fixingSubgroup_index] at h
  exact h.symm

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeRel Ω]
  [TopologicalSpace Ω] [IsValuativeTopology Ω] [IsSepClosure K Ω] in

theorem norm_neg_gen_eq_coeff_zero {x : Ω} (hint : IsIntegral K x) :
    Algebra.norm K (-AdjoinSimple.gen K x) = (minpoly K x).coeff 0 := by
  set pb := adjoin.powerBasis hint
  have hdim : pb.dim = (minpoly K x).natDegree := by
    rw [adjoin.powerBasis_dim]
  have hnorm : Algebra.norm K pb.gen = (-1) ^ (minpoly K x).natDegree * (minpoly K x).coeff 0 := by
    rw [Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly, hdim, adjoin.powerBasis_gen,
      minpoly_gen]
  have h1 : (-1 : K⟮x⟯) = algebraMap K K⟮x⟯ (-1) := by simp
  rw [← adjoin.powerBasis_gen hint, neg_eq_neg_one_mul, h1, map_mul, Algebra.norm_algebraMap, hnorm,
    ← adjoin.finrank hint, ← mul_assoc, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_mul]

include hπ hf in
set_option maxHeartbeats 1000000 in

theorem reciprocity_frobenius_lubinTate (m : ℕ) (U : OpenSubgroup (Ω ≃ₐ[K] Ω))
    [((U : Subgroup (Ω ≃ₐ[K] Ω)).subgroupOf
      ((⊤ : OpenSubgroup (Ω ≃ₐ[K] Ω)) : Subgroup (Ω ≃ₐ[K] Ω))).Normal]
    (hUH : (U : Subgroup (Ω ≃ₐ[K] Ω)) ≤ (lubinTateField Ω hπ hf (m + 1)).fixingSubgroup)
    (hHU : (lubinTateField Ω hπ hf (m + 1)).fixingSubgroup ⊓ (unramifiedDegree K Ω).ker ≤ U)
    (w : 𝒪[K]ˣ) (σ : Ω ≃ₐ[K] Ω) (hσd : unramifiedDegree K Ω σ = Multiplicative.ofAdd 1)
    (hσ : ∀ x ∈ lubinTateTorsion Ω (hπ := hπ) hf (m + 1),
      lubinTateGalPointMap (hπ := hπ) hf σ x = ((w⁻¹ : 𝒪[K]ˣ) : 𝒪[K]) • x) :
    (localClassFieldTheory K Ω).reciprocity (le_top : U ≤ ⊤)
        (localClassFieldTheory K Ω).classFieldAxiom (QuotientGroup.mk ⟨σ, by simp⟩) =
      QuotientGroup.mk (baseUnitsEquiv.symm (unitUniformizerPow hπ w 1)) := by
  have : IsSepClosed Ω := IsSepClosure.sep_closed K

  have hinert : inertiaDegree (localClassFieldTheory K Ω).deg
      ((⊤ : OpenSubgroup (Ω ≃ₐ[K] Ω)) : Subgroup (Ω ≃ₐ[K] Ω)) = 1 := by
    rw [localClassFieldTheory_deg]
    exact inertiaDegree_unramifiedDegree_top
  let s : (localClassFieldTheory K Ω).FrobeniusLift ⊤ :=
    { elt := σ
      mem := by simp
      deg := 1
      deg_pos := one_pos
      deg_eq := by rw [hinert, localClassFieldTheory_deg, hσd]; simp }

  obtain ⟨l, hlE, hl⟩ := exists_lubinTateField_eq_adjoin_eisenstein (Ω := Ω) hπ hf m
  obtain ⟨x, hxP, hσx, hτx⟩ := exists_fixed_root_ltEisenstein hπ w m σ hσd hl
    (apply_root_eq_psEval hπ hf m w σ hσ hl)
  have hwπ : ((w : 𝒪[K]) * π : 𝒪[K]) ≠ 0 := mul_ne_zero w.ne_zero hπ.ne_zero
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [Polynomial.aeval_def, Polynomial.eval₂_at_zero, Polynomial.coeff_map,
      coeff_zero_ltEisenstein, map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective K Ω),
      map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective 𝒪[K] K)] at hxP
    exact hwπ hxP

  have hy : (-(Units.mk0 x hx0) : Ωˣ) ∈
      fixedModule Ωˣ ((s.field U le_top : OpenSubgroup (Ω ≃ₐ[K] Ω)) : Subgroup (Ω ≃ₐ[K] Ω)) := by
    rw [ClassFieldData.FrobeniusLift.coe_field]
    refine mem_fixedModule_frobeniusClosure.mpr ⟨?_, ?_⟩
    · rw [mem_fixedModule_units_iff']
      intro g hg
      obtain ⟨hgU, hgk⟩ := Subgroup.mem_inf.mp hg
      have hgker : g ∈ (maximalUnramifiedExtension K Ω).fixingSubgroup := by
        rw [← ker_unramifiedDegree]
        exact hgk
      have hgl : g l = l := (mem_fixingSubgroup_iff _ g).mp (hUH hgU) l
        (hlE ▸ mem_adjoin_simple_self K l)
      have hgx := hτx g (fun y hy => (mem_fixingSubgroup_iff _ g).mp hgker y hy) hgl
      rw [Units.val_neg, Units.val_mk0, map_neg, hgx]
    · apply Units.ext
      change σ ((-(Units.mk0 x hx0) : Ωˣ) : Ω) = ((-(Units.mk0 x hx0) : Ωˣ) : Ω)
      rw [Units.val_neg, Units.val_mk0, map_neg, hσx]

  set S := s.field U le_top with hS
  have hFfix : (fixedField ((S : OpenSubgroup (Ω ≃ₐ[K] Ω)) : Subgroup (Ω ≃ₐ[K] Ω))).fixingSubgroup =
      (S : Subgroup (Ω ≃ₐ[K] Ω)) :=
    fixingSubgroup_fixedField_openSubgroup S
  have hxF : x ∈ fixedField ((S : OpenSubgroup (Ω ≃ₐ[K] Ω)) : Subgroup (Ω ≃ₐ[K] Ω)) := by
    rw [mem_fixedField_iff]
    intro g hg
    have h1 := (mem_fixedModule_units_iff' _ _).mp hy g hg
    rw [Units.val_neg, Units.val_mk0, map_neg, neg_inj] at h1
    exact h1
  have hπ' : Irreducible ((w : 𝒪[K]) * π) := (irreducible_units_mul w).2 hπ
  have hq := one_lt_card_residueField' K
  have hdeg : 0 < (ltEisenstein ((w : 𝒪[K]) * π) m).natDegree := by
    rw [(ltEisenstein_monic _ m).2]
    exact Nat.mul_pos (by omega) (pow_pos (by omega) m)
  have hmon := (ltEisenstein_monic ((w : 𝒪[K]) * π) m).1
  have hint : IsIntegral K x := ⟨_, hmon.map _, hxP⟩
  have hmin : minpoly K x = (ltEisenstein ((w : 𝒪[K]) * π) m).map (algebraMap 𝒪[K] K) :=
    (minpoly.eq_of_irreducible_of_monic
      (irreducible_map_of_isEisensteinAt (isEisensteinAt_ltEisenstein hπ' m) hdeg) hxP
      (hmon.map _)).symm
  have hindex : (S : Subgroup (Ω ≃ₐ[K] Ω)).index = (ltEisenstein ((w : 𝒪[K]) * π) m).natDegree := by
    have hinf : (U : Subgroup (Ω ≃ₐ[K] Ω)) ⊓ (unramifiedDegree K Ω).ker =
        (lubinTateField Ω hπ hf (m + 1)).fixingSubgroup ⊓ (unramifiedDegree K Ω).ker :=
      le_antisymm (inf_le_inf_right _ hUH) (le_inf hHU inf_le_right)
    have hSk := ClassFieldData.FrobeniusLift.field_inf_ker le_top s (L := U)
    rw [localClassFieldTheory_deg] at hSk
    rw [index_eq_mul (localClassFieldTheory K Ω).surjective_deg,
      ClassFieldData.FrobeniusLift.inertiaDegree_field, hinert, mul_one, mul_one,
      RHDirect.CFT_AbstractLocalReciprocity.ramificationIndex, localClassFieldTheory_deg, ← Subgroup.inf_relIndex_right, hSk, hinf,
      Subgroup.inf_relIndex_right, ← RHDirect.CFT_AbstractLocalReciprocity.ramificationIndex,
      ramificationIndex_fixingSubgroup_lubinTateField hπ hf (Nat.succ_pos m),
      finrank_lubinTateField hπ hf (Nat.succ_pos m), (ltEisenstein_monic _ m).2, Nat.succ_sub_one]
  have hFeq : K⟮x⟯ = fixedField ((S : OpenSubgroup (Ω ≃ₐ[K] Ω)) : Subgroup (Ω ≃ₐ[K] Ω)) := by
    refine eq_of_le_of_finrank_eq (adjoin_simple_le_iff.mpr hxF) ?_
    rw [adjoin.finrank hint, hmin, Polynomial.natDegree_map_eq_of_injective
      (FaithfulSMul.algebraMap_injective 𝒪[K] K), finrank_eq_fixingSubgroup_index, hFfix, hindex]

  have hnegxF : -x ∈ fixedField ((S : OpenSubgroup (Ω ≃ₐ[K] Ω)) : Subgroup (Ω ≃ₐ[K] Ω)) :=
    neg_mem hxF
  have hnormF : Algebra.norm K
      (⟨-x, hnegxF⟩ : fixedField ((S : OpenSubgroup (Ω ≃ₐ[K] Ω)) : Subgroup (Ω ≃ₐ[K] Ω))) =
      (((w : 𝒪[K]) * π : 𝒪[K]) : K) := by
    have he : IntermediateField.equivOfEq hFeq (-AdjoinSimple.gen K x) = ⟨-x, hnegxF⟩ :=
      Subtype.ext (by simp)
    rw [← he, Algebra.norm_eq_of_algEquiv, norm_neg_gen_eq_coeff_zero hint, hmin,
      Polynomial.coeff_map, coeff_zero_ltEisenstein]
    rfl
  have hfi : ((fixedField ((S : OpenSubgroup (Ω ≃ₐ[K] Ω)) :
      Subgroup (Ω ≃ₐ[K] Ω))).fixingSubgroup.subgroupOf ⊤).FiniteIndex := by
    rw [hFfix]
    infer_instance
  let a : fixedModule Ωˣ ((S : OpenSubgroup (Ω ≃ₐ[K] Ω)) : Subgroup (Ω ≃ₐ[K] Ω)) :=
    ⟨-(Units.mk0 x hx0), hy⟩
  have hnorm : baseUnitsEquiv (norm Ωˣ (⊤ : Subgroup (Ω ≃ₐ[K] Ω))
      ((S : OpenSubgroup (Ω ≃ₐ[K] Ω)) : Subgroup (Ω ≃ₐ[K] Ω)) a) = unitUniformizerPow hπ w 1 := by
    apply Units.ext
    apply (algebraMap K Ω).injective
    rw [algebraMap_baseUnitsEquiv, coe_norm_congr rfl hFfix.symm, coe_norm_top,
      coe_unitUniformizerPow_one, ← hnormF]
    congr 2

  have hval : (localClassFieldTheory K Ω).valuation S a = Multiplicative.ofAdd 1 := by
    rw [ClassFieldData.valuation_eq_iff, ClassFieldData.FrobeniusLift.inertiaDegree_field, hinert]
    apply Multiplicative.toAdd.injective
    rw [localClassFieldTheory_val_apply, hnorm, ord_unitUniformizerPow_one]
    simp [s]
  have key := (localClassFieldTheory K Ω).reciprocity_mk_eq_norm (le_top : U ≤ ⊤)
    (localClassFieldTheory K Ω).classFieldAxiom s hval
  refine key.trans ?_
  congr 1
  apply baseUnitsEquiv.injective
  rw [MulEquiv.apply_symm_apply]
  exact hnorm

include hπ hf in

theorem reciprocity_lubinTate {n : ℕ} (hn : 0 < n) (U : OpenSubgroup (Ω ≃ₐ[K] Ω))
    [((U : Subgroup (Ω ≃ₐ[K] Ω)).subgroupOf
      ((⊤ : OpenSubgroup (Ω ≃ₐ[K] Ω)) : Subgroup (Ω ≃ₐ[K] Ω))).Normal]
    (hUH : (U : Subgroup (Ω ≃ₐ[K] Ω)) ≤ (lubinTateField Ω hπ hf n).fixingSubgroup)
    (hHU : (lubinTateField Ω hπ hf n).fixingSubgroup ⊓ (unramifiedDegree K Ω).ker ≤ U)
    (u : 𝒪[K]ˣ) (k : ℤ) (τ : Ω ≃ₐ[K] Ω)
    (hτd : unramifiedDegree K Ω τ = Multiplicative.ofAdd (k : ℤ̂))
    (hτ : ∀ x ∈ lubinTateTorsion Ω (hπ := hπ) hf n,
      lubinTateGalPointMap (hπ := hπ) hf τ x = ((u⁻¹ : 𝒪[K]ˣ) : 𝒪[K]) • x) :
    (localClassFieldTheory K Ω).reciprocity (le_top : U ≤ ⊤)
        (localClassFieldTheory K Ω).classFieldAxiom (QuotientGroup.mk ⟨τ, by simp⟩) =
      QuotientGroup.mk (baseUnitsEquiv.symm (unitUniformizerPow hπ u k)) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hn.ne'
  obtain ⟨σu, hσud, hσu⟩ := exists_lubinTate_frobenius (Ω := Ω) hπ hf hn u
  obtain ⟨σ1, hσ1d, hσ1⟩ := exists_lubinTate_frobenius (Ω := Ω) hπ hf hn 1

  have hσ1H : σ1 ∈ (lubinTateField Ω hπ hf (m + 1)).fixingSubgroup := by
    rw [lubinTateField, mem_fixingSubgroup_adjoin_iff]
    rintro _ ⟨x, hx, rfl⟩
    have h := congrArg IdealPoint.val (hσ1 x hx)
    rwa [lubinTateGalPointMap_val, inv_one, Units.val_one, one_smul] at h

  have hcls : (QuotientGroup.mk ⟨τ, by simp⟩ : ((⊤ : OpenSubgroup (Ω ≃ₐ[K] Ω)) : Subgroup (Ω ≃ₐ[K] Ω)) ⧸
      (U : Subgroup (Ω ≃ₐ[K] Ω)).subgroupOf ((⊤ : OpenSubgroup (Ω ≃ₐ[K] Ω)) : Subgroup (Ω ≃ₐ[K] Ω))) =
      QuotientGroup.mk ⟨σu, by simp⟩ * (QuotientGroup.mk ⟨σ1, by simp⟩) ^ (k - 1) := by
    rw [← QuotientGroup.mk_zpow, ← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    apply hHU
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_zpow]
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [lubinTateField, mem_fixingSubgroup_adjoin_iff]
      rintro _ ⟨x, hx, rfl⟩
      have hxE := val_mem_lubinTateField hπ hf hx
      have h1 : (σ1 ^ (k - 1)) x.val = x.val :=
        (mem_fixingSubgroup_iff _ _).mp (Subgroup.zpow_mem _ hσ1H (k - 1)) x.val hxE
      have h2 : τ x.val = σu x.val := by
        have e1 := congrArg IdealPoint.val (hτ x hx)
        have e2 := congrArg IdealPoint.val (hσu x hx)
        rw [lubinTateGalPointMap_val] at e1 e2
        rw [e1, e2]
      rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, h1, ← h2]
      exact τ.symm_apply_apply x.val
    · rw [MonoidHom.mem_ker, map_mul, map_mul, map_inv, map_zpow, hτd, hσud, hσ1d]
      apply Multiplicative.toAdd.injective
      simp only [toAdd_mul, toAdd_inv, toAdd_zpow, toAdd_ofAdd, toAdd_one, zsmul_eq_mul]
      push_cast
      ring
  rw [hcls, map_mul, map_zpow,
    reciprocity_frobenius_lubinTate hπ hf m U hUH hHU u σu hσud hσu,
    reciprocity_frobenius_lubinTate hπ hf m U hUH hHU 1 σ1 hσ1d hσ1,
    ← QuotientGroup.mk_zpow, ← QuotientGroup.mk_mul, ← map_zpow, ← map_mul, unitUniformizerPow_mul,
    add_sub_cancel]

include hπ hf in

theorem exists_lubinTate_action {n : ℕ} (hn : 0 < n) (u : 𝒪[K]ˣ) (k : ℤ) :
    ∃ τ : Ω ≃ₐ[K] Ω, unramifiedDegree K Ω τ = Multiplicative.ofAdd (k : ℤ̂) ∧
      ∀ x ∈ lubinTateTorsion Ω (hπ := hπ) hf n,
        lubinTateGalPointMap (hπ := hπ) hf τ x = ((u⁻¹ : 𝒪[K]ˣ) : 𝒪[K]) • x := by
  obtain ⟨σu, hσud, hσu⟩ := exists_lubinTate_frobenius (Ω := Ω) hπ hf hn u
  obtain ⟨σ1, hσ1d, hσ1⟩ := exists_lubinTate_frobenius (Ω := Ω) hπ hf hn 1
  have hσ1x : ∀ x ∈ lubinTateTorsion Ω (hπ := hπ) hf n, σ1 x.val = x.val := fun x hx => by
    have h := congrArg IdealPoint.val (hσ1 x hx)
    rwa [lubinTateGalPointMap_val, inv_one, Units.val_one, one_smul] at h
  have hσ1H : σ1 ∈ (lubinTateField Ω hπ hf n).fixingSubgroup := by
    rw [lubinTateField, mem_fixingSubgroup_adjoin_iff]
    rintro _ ⟨x, hx, rfl⟩
    exact hσ1x x hx
  refine ⟨σu * σ1 ^ (k - 1), ?_, fun x hx => ?_⟩
  · rw [map_mul, map_zpow, hσud, hσ1d]
    apply Multiplicative.toAdd.injective
    simp only [toAdd_mul, toAdd_zpow, toAdd_ofAdd, zsmul_eq_mul]
    push_cast
    ring
  · apply IdealPoint.ext
    have h1 : (σ1 ^ (k - 1)) x.val = x.val :=
      (mem_fixingSubgroup_iff _ _).mp (Subgroup.zpow_mem _ hσ1H (k - 1)) x.val
        (val_mem_lubinTateField hπ hf hx)
    have e := congrArg IdealPoint.val (hσu x hx)
    rw [lubinTateGalPointMap_val] at e ⊢
    rw [AlgEquiv.mul_apply, h1, e]

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeRel Ω]
  [TopologicalSpace Ω] [IsValuativeTopology Ω] [ValuativeExtension K Ω] in

theorem normal_subgroupOf_fixingOpenSubgroup (M : IntermediateField K Ω) [FiniteDimensional K M]
    [IsGalois K M] :
    ((fixingOpenSubgroup M : Subgroup (Ω ≃ₐ[K] Ω)).subgroupOf
      ((⊤ : OpenSubgroup (Ω ≃ₐ[K] Ω)) : Subgroup (Ω ≃ₐ[K] Ω))).Normal := by
  rw [coe_fixingOpenSubgroup]
  infer_instance

include hπ hf in

theorem reciprocity_lubinTate_sup {n : ℕ} (hn : 0 < n) (E : IntermediateField K Ω)
    [FiniteDimensional K E] [IsGalois K E] (hE : E ≤ maximalUnramifiedExtension K Ω)
    (u : 𝒪[K]ˣ) (k : ℤ) (τ : Ω ≃ₐ[K] Ω)
    (hτd : unramifiedDegree K Ω τ = Multiplicative.ofAdd (k : ℤ̂))
    (hτ : ∀ x ∈ lubinTateTorsion Ω (hπ := hπ) hf n,
      lubinTateGalPointMap (hπ := hπ) hf τ x = ((u⁻¹ : 𝒪[K]ˣ) : 𝒪[K]) • x) :
    have : IsSepClosed Ω := IsSepClosure.sep_closed K
    have := normal_subgroupOf_fixingOpenSubgroup (lubinTateField Ω hπ hf n ⊔ E)
    (localClassFieldTheory K Ω).reciprocity
        (le_top : fixingOpenSubgroup (lubinTateField Ω hπ hf n ⊔ E) ≤ ⊤)
        (localClassFieldTheory K Ω).classFieldAxiom (QuotientGroup.mk ⟨τ, by simp⟩) =
      QuotientGroup.mk (baseUnitsEquiv.symm (unitUniformizerPow hπ u k)) := by
  intro _ _
  refine reciprocity_lubinTate hπ hf hn _ ?_ ?_ u k τ hτd hτ
  · rw [coe_fixingOpenSubgroup]
    exact fixingSubgroup_antitone le_sup_left
  · rw [coe_fixingOpenSubgroup, fixingSubgroup_sup, ker_unramifiedDegree]
    exact inf_le_inf_left _ (fixingSubgroup_antitone hE)

end Frobenius

end RHDirect.CFT.LocalField
end Sec_LubinTateReciprocity

end
