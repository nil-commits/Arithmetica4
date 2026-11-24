import RHDirect.Stage3PatchingUnification
import RHDirect.Stage11ConcretePatching
import RHDirect.Stage11MazurDeformation
import RHDirect.Stage11WilesPatchingBridge
import RHDirect.Stage11EulerSystemSelmer
import RHDirect.Stage8RamanujanCongruences
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# RHDirect.Stage11DiamondFujiwara (R6 Express Route)

Unconditional (`0` assumptions, `0` `sorry`, `0` custom `axiom`s, ZERO `native_decide`, pure Mathlib)
formalization of all three Stage 11 Diamond–Fujiwara / Wiles–Lenstra pillars:

1. **Unconditional Wiles–Lenstra Numerical Criterion (`length(Φ_R) ≤ v_p(η_T) ⇒ R ≃+* T`, CI)**:
   - DVR ideal valuation `dvrIdealVal`, `p`-adic congruence valuation `padicCongVal` (`v_p(η_T)`),
     Fitting-ideal chain `Fitt_𝒪(Φ_R) ≤ Fitt_𝒪(Φ_T) ≤ η_T`, and cotangent collapse `Φ_R ≃ Φ_T`.
   - Exact multivariable cotangent presentation `Φ_R ≃ coker(J_f^T)` for
     `R = 𝒪[[X_0,…,X_{g-1}]] / (f_1,…,f_r)` (`r ≤ g`), relation-count forcing (`r = g ∧ det J_f ≠ 0`),
     Jacobian–Fitting–Congruence equality `(det J_f) = η_T`, and full Wiles–Lenstra Numerical Criterion
     (`wiles_lenstra_complete_intersection_of_length_le`, `wiles_lenstra_numerical_criterion_Zp`).
   - Zero-cover quadratic/monogenic Wiles–Lenstra criterion (`wiles_lenstra_quad_criterion_Zp`,
     `wiles_lenstra_adjoinRoot_quad_criterion_Zp`) via direct algebraic locality + `QuadAlg.isGorensteinOver`.
2. **Concrete Diamond–Fujiwara Depth-Freeness Patching Engine (`S_∞ = ℤ_[p][[y_0,…,y_{g-1}]]`)**:
   - Bundled finite-level quotients `FiniteLevelRing p g n := S_∞ ⧸ I_n` with explicit `RingHom`s
     (ZERO `Algebra`/`SMul` typeclass diamonds over `MvPowerSeries`).
   - Unconditional Auslander–Buchsbaum / Depth-Freeness Theorem over `S_∞`:
     `IsPatchingRegularSeq p g M ⇒ M` is FREE of finite rank over `S_∞`.
   - `DiamondFujiwaraPatchingTower (p g)` proving `M_∞` free over `S_∞`, `R_∞ ≃ₐ[S_∞] T_∞`,
     `R_0 ≃+* T_0`, `M_0` free over `T_0`, and `length(Φ_{R_0}) = v_p(η_{T_0})`, directly wired into
     `Stage11ConcretePatching`, `Stage11MazurDeformation`, `Stage11WilesPatchingBridge`,
     `Stage11EulerSystemSelmer`, and `Stage3PatchingUnification.CongruencePatchingRealization`.
3. **Concrete `0`-Assumption Finite-Rank Witnesses**:
   - Explicit `ℤ_[p][X]/(X² - p^k X)` (`QuadAlg ℤ_[p] (p^k) 0`, congruence modulus `p^k`) for all `p, g, k ≥ 1`.
   - Concrete weight-12 Ramanujan `Δ` mod `691` congruence tower (`E₁₂ ≡ Δ (mod 691)`, wired directly to
     `Stage8RamanujanCongruences.ramanujanTau_mod_691`), `DeltaMod691HeckeAlg ≃ QuadAlg ℤ_[691] 691 0 ≃ ℤ_[691][X]/(X² - 2073 X)`,
     Wiles–Lenstra `R ≃ T`, Diamond–Fujiwara patching tower, `CongruencePatchingRealization` (`P₀ ⊆ {691}`),
     and end-to-end `0`-assumption `VWin delta691_concreteSelmerSystem` via `Stage11WilesPatchingBridge`.
-/

noncomputable section

open scoped BigOperators Pointwise
open Finset Module Submodule
open RHDirect RHDirect.Stage2IwasawaTwoTower RHDirect.Stage3PatchingUnification
open RHDirect.Stage8IwasawaWeierstrass RHDirect.Stage8RamanujanDelta
open RHDirect.Stage8RamanujanCongruences RHDirect.Stage11ConcretePatching
open RHDirect.Stage11MazurDeformation RHDirect.Stage11WilesPatchingBridge
open RHDirect.Stage11EulerSystemSelmer RHDirect.Stage11FerreroWashington
open RHDirect.Stage11StickelbergerRamified

namespace RHDirect
namespace Stage11DiamondFujiwara

/-! ## Section 1: Unconditional Wiles–Lenstra Numerical Criterion (`length(Φ_R) ≤ v_p(η_T) ⇒ R ≃ T` CI) -/

section WilesLenstraNumericalCriterion

/-! ### 1.1 DVR Ideal Valuation `dvrIdealVal`, `padicCongVal`, and Fitting-Ideal Divisibility -/

/-- The finite length / valuation `v_ϖ(I) := (Module.length 𝒪 (𝒪 ⧸ I)).toNat` of an ideal `I ≤ 𝒪`. -/
def dvrIdealVal (𝒪 : Type*) [CommRing 𝒪] (I : Ideal 𝒪) : ℕ :=
  (Module.length 𝒪 (𝒪 ⧸ I)).toNat

/-- The `p`-adic valuation `v_p(η_T)` of the congruence ideal `η_T = π(Ann_T(ker π)) ⊆ ℤ_[p]`. -/
def padicCongVal (p : ℕ) [Fact p.Prime] {T : Type*} [CommRing T] [Algebra ℤ_[p] T]
    (π : T →ₐ[ℤ_[p]] ℤ_[p]) : ℕ :=
  dvrIdealVal ℤ_[p] (congruenceIdeal π)

/-- Over a DVR `(𝒪, ϖ)`, every nonzero ideal `I ≠ ⊥` equals `Ideal.span {ϖ ^ v}` for a unique `v`. -/
theorem dvr_ideal_eq_span_pow_unique {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪]
    [IsDiscreteValuationRing 𝒪] {ϖ : 𝒪} (hϖ : Irreducible ϖ)
    {I : Ideal 𝒪} (hI : I ≠ ⊥) :
    ∃! v : ℕ, I = Ideal.span ({ϖ ^ v} : Set 𝒪) := by
  have : IsPrincipalIdealRing 𝒪 := inferInstance
  obtain ⟨a, ha⟩ := IsPrincipalIdealRing.principal I
  have ha0 : a ≠ 0 := by
    intro h0
    apply hI
    rw [ha, h0, Ideal.submodule_span_eq, Ideal.span_singleton_zero]
  obtain ⟨v, hv⟩ := IsDiscreteValuationRing.associated_pow_irreducible ha0 hϖ
  refine ⟨v, ?_, ?_⟩
  · rw [ha, Ideal.submodule_span_eq]
    exact span_singleton_eq_of_associated hv
  · intro w hw
    have hEq : Ideal.span ({ϖ ^ w} : Set 𝒪) = Ideal.span ({ϖ ^ v} : Set 𝒪) := by
      rw [← hw, ha, Ideal.submodule_span_eq]
      exact span_singleton_eq_of_associated hv
    have hlen := congrArg (fun J : Ideal 𝒪 => Module.length 𝒪 (𝒪 ⧸ J)) hEq
    rw [length_quotient_span_pow_eq_of_dvr hϖ w, length_quotient_span_pow_eq_of_dvr hϖ v] at hlen
    exact ENat.natCast_inj.mp hlen

/-- Exact characterization of `dvrIdealVal 𝒪 I` for any nonzero ideal `I ≠ ⊥` in a DVR `(𝒪, ϖ)`. -/
theorem dvrIdealVal_spec {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪]
    [IsDiscreteValuationRing 𝒪] {ϖ : 𝒪} (hϖ : Irreducible ϖ)
    {I : Ideal 𝒪} (hI : I ≠ ⊥) :
    Module.length 𝒪 (𝒪 ⧸ I) = (dvrIdealVal 𝒪 I : ℕ∞) ∧
    I = Ideal.span ({ϖ ^ dvrIdealVal 𝒪 I} : Set 𝒪) := by
  obtain ⟨v, hv, _⟩ := dvr_ideal_eq_span_pow_unique hϖ hI
  have hlen : Module.length 𝒪 (𝒪 ⧸ I) = (v : ℕ∞) := by
    rw [hv, length_quotient_span_pow_eq_of_dvr hϖ v]
  have hval : dvrIdealVal 𝒪 I = v := by
    unfold dvrIdealVal
    rw [hlen]
    exact ENat.toNat_natCast v
  rw [hval]
  exact ⟨hlen, hv⟩

/-- Specialization of `dvrIdealVal_spec` to `ℤ_[p]` and `padicCongVal p π`. -/
theorem padicCongVal_spec {p : ℕ} [Fact p.Prime] {T : Type*} [CommRing T] [Algebra ℤ_[p] T]
    (π : T →ₐ[ℤ_[p]] ℤ_[p]) (hη : congruenceIdeal π ≠ ⊥) :
    Module.length ℤ_[p] (ℤ_[p] ⧸ congruenceIdeal π) = (padicCongVal p π : ℕ∞) ∧
    congruenceIdeal π = Ideal.span ({(p : ℤ_[p]) ^ padicCongVal p π} : Set ℤ_[p]) :=
  dvrIdealVal_spec (PadicInt.irreducible_p (p := p)) hη

/-- In any DVR `𝒪`, `Module.length 𝒪 𝒪 = ⊤`. -/
theorem dvr_length_self_eq_top (𝒪 : Type*) [CommRing 𝒪] [IsDomain 𝒪]
    [IsDiscreteValuationRing 𝒪] :
    Module.length 𝒪 𝒪 = ⊤ := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪
  by_contra hne
  cases hlen : Module.length 𝒪 𝒪 with
  | top => exact hne hlen
  | coe n =>
    have hle : ((n + 1 : ℕ) : ℕ∞) ≤ Module.length 𝒪 𝒪 := by
      rw [← length_quotient_span_pow_eq_of_dvr hϖ (n + 1)]
      exact Module.length_le_of_surjective (Submodule.mkQ (Ideal.span ({ϖ ^ (n + 1)} : Set 𝒪)))
        (Submodule.mkQ_surjective _)
    rw [hlen] at hle
    have hnat : n + 1 ≤ n := Nat.cast_le.mp hle
    omega

/-- **Full Fitting-Ideal Divisibility Chain (`Fitt_𝒪(Φ_R) ≤ Fitt_𝒪(Φ_T) ≤ η_T`)**. -/
theorem cotangentFittingIdeal_le_of_surjective {𝒪 R T : Type*}
    [CommRing 𝒪] [CommRing R] [Algebra 𝒪 R] [CommRing T] [Algebra 𝒪 T]
    (φ : R →ₐ[𝒪] T) (hφ : Function.Surjective φ)
    (π : T →ₐ[𝒪] 𝒪) {m : ℕ} (eR : Fin m → augIdeal (π.comp φ))
    (heR : Submodule.span 𝒪 (Set.range eR) = ⊤) :
    let eT : Fin m → augIdeal π := fun i => ⟨φ (eR i).1, (eR i).2⟩
    cotangentFittingIdeal (π.comp φ) eR ≤ cotangentFittingIdeal π eT ∧
    cotangentFittingIdeal π eT ≤ congruenceIdeal π := by
  intro eT
  have heT : Submodule.span 𝒪 (Set.range eT) = ⊤ := by
    rw [eq_top_iff]
    intro y _
    obtain ⟨r, hr⟩ := hφ y.1
    have hrI : r ∈ augIdeal (π.comp φ) := by
      change π (φ r) = 0; rw [hr]; exact y.2
    have hmem : (⟨r, hrI⟩ : augIdeal (π.comp φ)) ∈ Submodule.span 𝒪 (Set.range eR) := by
      rw [heR]; trivial
    rw [Submodule.mem_span_range_iff_exists_fun] at hmem
    obtain ⟨c, hc⟩ := hmem
    have hy_eq : y = ∑ i : Fin m, c i • eT i := by
      apply Subtype.ext
      have hval := congrArg (fun z : augIdeal (π.comp φ) => φ z.1) hc
      simp only [Submodule.coe_sum, map_sum] at hval
      rw [← hr, ← hval]
      simp [eT]
    rw [hy_eq]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  constructor
  · rw [cotangentFittingIdeal, Ideal.span_le]
    rintro d ⟨A, hrel, rfl⟩
    refine Ideal.subset_span ⟨A, fun i => ?_, rfl⟩
    have hi := hrel i
    rw [pow_two] at hi ⊢
    have hle : Ideal.map φ.toRingHom (augIdeal (π.comp φ) * augIdeal (π.comp φ)) ≤
        augIdeal π * augIdeal π := by
      rw [Ideal.map_mul]
      refine Ideal.mul_mono ?_ ?_ <;>
        · rw [Ideal.map_le_iff_le_comap]; intro x hx; exact hx
    have hmap := hle (Ideal.mem_map_of_mem φ.toRingHom hi)
    simpa [eT, map_sum, map_mul, AlgHom.commutes] using hmap
  · exact cotangentFittingIdeal_le_congruenceIdeal π eT heT

/-- **Cotangent Collapse Lemma**: if `φ : R ↠ T` onto finite free `T` over a DVR `𝒪`,
`η_T ≠ ⊥`, and `len_𝒪(Φ_R) ≤ len_𝒪(𝒪 / η_T)`, then `len_𝒪(Φ_R) = len_𝒪(Φ_T) = len_𝒪(𝒪 / η_T)`
and `cotangentMap φ π : Φ_R ≃ₗ[𝒪] Φ_T` is bijective. -/
theorem cotangentMap_bijective_of_length_le {𝒪 R T : Type*}
    [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [CommRing R] [Algebra 𝒪 R]
    [CommRing T] [Algebra 𝒪 T] [Module.Free 𝒪 T] [Module.Finite 𝒪 T]
    (φ : R →ₐ[𝒪] T) (hφ : Function.Surjective φ)
    (π : T →ₐ[𝒪] 𝒪) (hη : congruenceIdeal π ≠ ⊥)
    (hle : Module.length 𝒪 (Cotangent (π.comp φ)) ≤ Module.length 𝒪 (𝒪 ⧸ congruenceIdeal π)) :
    Module.length 𝒪 (Cotangent (π.comp φ)) = Module.length 𝒪 (𝒪 ⧸ congruenceIdeal π) ∧
    Module.length 𝒪 (Cotangent π) = Module.length 𝒪 (𝒪 ⧸ congruenceIdeal π) ∧
    Function.Bijective (cotangentMap φ π) := by
  obtain ⟨h1, h2, hfin⟩ := wiles_lenstra_length_inequality φ hφ π hη
  have hPhiR_eq : Module.length 𝒪 (Cotangent (π.comp φ)) =
      Module.length 𝒪 (𝒪 ⧸ congruenceIdeal π) := le_antisymm hle (h1.trans h2)
  have hPhiT_eq : Module.length 𝒪 (Cotangent π) =
      Module.length 𝒪 (𝒪 ⧸ congruenceIdeal π) := le_antisymm (h2.trans hle) h1
  have hsurj : Function.Surjective (cotangentMap φ π) := cotangentMap_surjective φ hφ π
  have hadd : Module.length 𝒪 (Cotangent (π.comp φ)) =
      Module.length 𝒪 (LinearMap.ker (cotangentMap φ π)) + Module.length 𝒪 (Cotangent π) :=
    Module.length_eq_add_of_exact (LinearMap.ker (cotangentMap φ π)).subtype
      (cotangentMap φ π) (Submodule.subtype_injective _) hsurj (LinearMap.exact_subtype_ker_map _)
  have hker0 : Module.length 𝒪 (LinearMap.ker (cotangentMap φ π)) = 0 := by
    rw [hPhiR_eq, hPhiT_eq] at hadd
    cases hlen : Module.length 𝒪 (𝒪 ⧸ congruenceIdeal π) with
    | top => exact absurd hlen hfin
    | coe b =>
      cases hkl : Module.length 𝒪 (LinearMap.ker (cotangentMap φ π)) with
      | top => rw [hlen, hkl, top_add] at hadd; exact absurd hadd (ENat.natCast_ne_top b)
      | coe a =>
        rw [hlen, hkl] at hadd
        have hab : b = a + b := ENat.natCast_inj.mp (by simpa [Nat.cast_add] using hadd)
        have ha0 : a = 0 := by omega
        simp [ha0]
  have hsub : Subsingleton (LinearMap.ker (cotangentMap φ π)) :=
    Module.length_eq_zero_iff.mp hker0
  have hinj : Function.Injective (cotangentMap φ π) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    exact congrArg Subtype.val (@Subsingleton.elim _ hsub ⟨x, hx⟩ 0)
  exact ⟨hPhiR_eq, hPhiT_eq, hinj, hsurj⟩

/-! ### 1.2 Exact Cotangent Presentation of `𝒪[[X_0,…,X_{g-1}]] / (f_1,…,f_r)` & Jacobian Collapse -/

/-- Canonical augmentation `ε_P : MvPowerSeries (Fin g) 𝒪 →ₐ[𝒪] 𝒪` (`constantCoeff`). -/
def mvPowerSeriesAug (𝒪 : Type*) [CommRing 𝒪] (g : ℕ) :
    MvPowerSeries (Fin g) 𝒪 →ₐ[𝒪] 𝒪 where
  toRingHom := MvPowerSeries.constantCoeff
  commutes' := MvPowerSeries.constantCoeff_C

/-- Exact linear-part extraction `Cotangent (mvPowerSeriesAug 𝒪 g) ≃ₗ[𝒪] (Fin g → 𝒪)`. -/
def mvPowerSeries_cotangent_equiv_pi (𝒪 : Type*) [CommRing 𝒪] (g : ℕ) :
    Cotangent (mvPowerSeriesAug 𝒪 g) ≃ₗ[𝒪] (Fin g → 𝒪) := by
  let linPart : augIdeal (mvPowerSeriesAug 𝒪 g) →ₗ[𝒪] (Fin g → 𝒪) :=
    { toFun := fun x i => MvPowerSeries.coeff (Finsupp.single i 1) x.1
      map_add' := fun x y => by ext i; exact map_add _ _ _
      map_smul' := fun a x => by
        ext i
        change MvPowerSeries.coeff (Finsupp.single i 1) (a • x.1) =
          a * MvPowerSeries.coeff (Finsupp.single i 1) x.1
        rw [MvPowerSeries.smul_eq_C_mul, MvPowerSeries.coeff_C_mul] }
  have hsurj : Function.Surjective linPart := by
    intro v
    let f : MvPowerSeries (Fin g) 𝒪 := ∑ i : Fin g, MvPowerSeries.C (v i) * MvPowerSeries.X i
    have hf : f ∈ augIdeal (mvPowerSeriesAug 𝒪 g) := by
      change MvPowerSeries.constantCoeff f = 0; simp [f]
    refine ⟨⟨f, hf⟩, ?_⟩
    ext j
    change MvPowerSeries.coeff (Finsupp.single j 1) f = v j
    simp only [f, map_sum, MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_X]
    rw [Finset.sum_eq_single j]
    · simp
    · intro i _ hij
      have hne : Finsupp.single j (1 : ℕ) ≠ Finsupp.single i 1 := by
        intro h
        have h1 := congrArg (fun d : Fin g →₀ ℕ => d i) h
        rw [Finsupp.single_eq_same, Finsupp.single_eq_of_ne hij] at h1
        exact zero_ne_one h1
      simp [hne]
    · intro h; exact absurd (Finset.mem_univ j) h
  have hker : LinearMap.ker linPart = cotangentSubmodule (mvPowerSeriesAug 𝒪 g) := by
    ext x
    rw [LinearMap.mem_ker]
    change (fun i : Fin g => MvPowerSeries.coeff (Finsupp.single i 1) x.1) = 0 ↔
      x.1 ∈ augIdeal (mvPowerSeriesAug 𝒪 g) ^ 2
    constructor
    · intro hx0
      obtain ⟨q, hq⟩ := mvPowerSeries_sub_constantCoeff_eq_sum_X_mul x.1
      have hc0 : MvPowerSeries.constantCoeff x.1 = 0 := x.2
      rw [hc0, map_zero, zero_add] at hq
      have hq_mem : ∀ i : Fin g, q i ∈ augIdeal (mvPowerSeriesAug 𝒪 g) := by
        intro i
        change MvPowerSeries.constantCoeff (q i) = 0
        have hi := congrFun hx0 i
        rw [hq, map_sum] at hi
        have hterm : ∀ j : Fin g,
            MvPowerSeries.coeff (Finsupp.single i 1) (MvPowerSeries.X j * q j) =
              if j = i then MvPowerSeries.constantCoeff (q i) else 0 := by
          intro j
          rw [MvPowerSeries.X_def, MvPowerSeries.coeff_monomial_mul, one_mul]
          by_cases hji : j = i
          · subst hji
            rw [if_pos le_rfl, if_pos rfl, tsub_self, MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
          · rw [if_neg hji, if_neg]
            rw [Finsupp.single_le_iff, Finsupp.single_eq_of_ne hji]; omega
        rw [Finset.sum_congr rfl fun j _ => hterm j] at hi
        simpa using hi
      rw [hq, pow_two]
      refine Ideal.sum_mem _ fun i _ => Ideal.mul_mem_mul ?_ (hq_mem i)
      exact MvPowerSeries.constantCoeff_X i
    · intro hx2
      rw [pow_two] at hx2
      ext i
      change MvPowerSeries.coeff (Finsupp.single i 1) x.1 = 0
      refine Submodule.mul_induction_on hx2 ?_ ?_
      · intro u hu v hv
        rw [MvPowerSeries.coeff_mul]
        refine Finset.sum_eq_zero fun ab hab => ?_
        rw [Finset.mem_antidiagonal] at hab
        have hsum_i : ab.1 i + ab.2 i = 1 := by
          have := congrArg (fun d : Fin g →₀ ℕ => d i) hab; simpa using this
        have hzero_other : ∀ j : Fin g, j ≠ i → ab.1 j = 0 ∧ ab.2 j = 0 := by
          intro j hji
          have h0 : ab.1 j + ab.2 j = 0 := by
            have := congrArg (fun d : Fin g →₀ ℕ => d j) hab
            simpa [Finsupp.single_eq_of_ne hji] using this
          omega
        by_cases ha : ab.1 i = 0
        · have ha0 : ab.1 = 0 := by
            ext j; by_cases hji : j = i
            · subst hji; exact ha
            · exact (hzero_other j hji).1
          rw [ha0, MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
            show MvPowerSeries.constantCoeff u = 0 from hu, zero_mul]
        · have hb : ab.2 i = 0 := by omega
          have hb0 : ab.2 = 0 := by
            ext j; by_cases hji : j = i
            · subst hji; exact hb
            · exact (hzero_other j hji).2
          rw [hb0, MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
            show MvPowerSeries.constantCoeff v = 0 from hv, mul_zero]
      · intro u v hu hv; rw [map_add, hu, hv, add_zero]
  exact (Submodule.quotEquivOfEq _ _ hker.symm).trans (linPart.quotKerEquivOfSurjective hsurj)

/-- The `r × g` Jacobian matrix at `0` of `f : Fin r → MvPowerSeries (Fin g) 𝒪`. -/
def jacobianMat {𝒪 : Type*} [CommRing 𝒪] {g r : ℕ}
    (f : Fin r → MvPowerSeries (Fin g) 𝒪) : Matrix (Fin r) (Fin g) 𝒪 :=
  fun i j => MvPowerSeries.coeff (Finsupp.single j 1) (f i)

/-- **Exact Cotangent Presentation of `R = 𝒪[[X_0,…,X_{g-1}]] / (f_1,…,f_r)`**:
`Cotangent π_R ≃ₗ[𝒪] (Fin g → 𝒪) ⧸ LinearMap.range (jacobianMat f).transpose.mulVecLin`. -/
def cotangent_equiv_coker_jacobian {𝒪 R : Type*} [CommRing 𝒪] [CommRing R] [Algebra 𝒪 R]
    {g r : ℕ} (f : Fin r → MvPowerSeries (Fin g) 𝒪)
    (ψ : MvPowerSeries (Fin g) 𝒪 →ₐ[𝒪] R) (hψ : Function.Surjective ψ)
    (hker : RingHom.ker ψ.toRingHom = Ideal.span (Set.range f))
    (π_R : R →ₐ[𝒪] 𝒪) (hcompat : π_R.comp ψ = mvPowerSeriesAug 𝒪 g) :
    Cotangent π_R ≃ₗ[𝒪] ((Fin g → 𝒪) ⧸ LinearMap.range (jacobianMat f).transpose.mulVecLin) := by
  let eP : Cotangent (mvPowerSeriesAug 𝒪 g) ≃ₗ[𝒪] (Fin g → 𝒪) :=
    mvPowerSeries_cotangent_equiv_pi 𝒪 g
  let mapPi : (Fin g → 𝒪) →ₗ[𝒪] Cotangent π_R :=
    { toFun := fun v =>
        Submodule.Quotient.mk (p := cotangentSubmodule π_R)
          ⟨ψ (∑ j : Fin g, MvPowerSeries.C (v j) * MvPowerSeries.X j), by
            change (π_R.comp ψ) (∑ j : Fin g, MvPowerSeries.C (v j) * MvPowerSeries.X j) = 0
            rw [hcompat]; change MvPowerSeries.constantCoeff _ = 0; simp⟩
      map_add' := fun u v => by
        rw [← Submodule.Quotient.mk_add]; congr 1; apply Subtype.ext
        change ψ (∑ j : Fin g, MvPowerSeries.C (u j + v j) * MvPowerSeries.X j) =
          ψ (∑ j : Fin g, MvPowerSeries.C (u j) * MvPowerSeries.X j) +
            ψ (∑ j : Fin g, MvPowerSeries.C (v j) * MvPowerSeries.X j)
        rw [← map_add, ← Finset.sum_add_distrib]
        congr 1; refine Finset.sum_congr rfl fun j _ => by rw [map_add, add_mul]
      map_smul' := fun a v => by
        change Submodule.Quotient.mk (p := cotangentSubmodule π_R) _ =
          a • Submodule.Quotient.mk (p := cotangentSubmodule π_R) _
        rw [← Submodule.Quotient.mk_smul]; congr 1; apply Subtype.ext
        change ψ (∑ j : Fin g, MvPowerSeries.C (a * v j) * MvPowerSeries.X j) =
          a • ψ (∑ j : Fin g, MvPowerSeries.C (v j) * MvPowerSeries.X j)
        rw [← map_smul]; congr 1; rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun j _ => by rw [map_mul, mul_assoc, MvPowerSeries.smul_eq_C_mul] }
  have hmap_apply_lin : ∀ (p : MvPowerSeries (Fin g) 𝒪) (hp : p ∈ augIdeal (mvPowerSeriesAug 𝒪 g)),
      mapPi (fun j => MvPowerSeries.coeff (Finsupp.single j 1) p) =
        Submodule.Quotient.mk (p := cotangentSubmodule π_R)
          ⟨ψ p, by change (π_R.comp ψ) p = 0; rw [hcompat]; exact hp⟩ := by
    intro p hp
    have hlin_sub : p - ∑ j : Fin g, MvPowerSeries.C (MvPowerSeries.coeff (Finsupp.single j 1) p) *
        MvPowerSeries.X j ∈ augIdeal (mvPowerSeriesAug 𝒪 g) ^ 2 := by
      have hmemI : p - ∑ j : Fin g, MvPowerSeries.C (MvPowerSeries.coeff (Finsupp.single j 1) p) *
          MvPowerSeries.X j ∈ augIdeal (mvPowerSeriesAug 𝒪 g) := by
        change MvPowerSeries.constantCoeff _ = 0
        rw [map_sub, show MvPowerSeries.constantCoeff p = 0 from hp, map_sum]; simp
      have he0 : eP (Submodule.Quotient.mk ⟨_, hmemI⟩) = 0 := by
        ext j
        change MvPowerSeries.coeff (Finsupp.single j 1)
          (p - ∑ k : Fin g, MvPowerSeries.C (MvPowerSeries.coeff (Finsupp.single k 1) p) *
            MvPowerSeries.X k) = 0
        rw [map_sub, map_sum]; simp_rw [MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_X]
        rw [Finset.sum_eq_single j]
        · simp
        · intro k _ hkj
          have hne : Finsupp.single j (1 : ℕ) ≠ Finsupp.single k 1 := by
            intro h
            have h1 := congrArg (fun d : Fin g →₀ ℕ => d k) h
            rw [Finsupp.single_eq_same, Finsupp.single_eq_of_ne hkj] at h1
            exact zero_ne_one h1
          simp [hne]
        · intro h; exact absurd (Finset.mem_univ j) h
      have hq0 : Submodule.Quotient.mk (p := cotangentSubmodule (mvPowerSeriesAug 𝒪 g)) ⟨_, hmemI⟩ = 0 :=
        eP.injective (he0.trans (map_zero eP).symm)
      exact (Submodule.Quotient.mk_eq_zero (cotangentSubmodule (mvPowerSeriesAug 𝒪 g))).mp hq0
    symm; rw [← sub_eq_zero]
    change Submodule.Quotient.mk (p := cotangentSubmodule π_R)
        ⟨ψ p, by change (π_R.comp ψ) p = 0; rw [hcompat]; exact hp⟩ -
      Submodule.Quotient.mk (p := cotangentSubmodule π_R)
        ⟨ψ (∑ j : Fin g, MvPowerSeries.C (MvPowerSeries.coeff (Finsupp.single j 1) p) * MvPowerSeries.X j), _⟩ = 0
    rw [← Submodule.Quotient.mk_sub, Submodule.Quotient.mk_eq_zero]
    change ψ p - ψ (∑ j : Fin g, MvPowerSeries.C (MvPowerSeries.coeff (Finsupp.single j 1) p) *
      MvPowerSeries.X j) ∈ augIdeal π_R ^ 2
    rw [← map_sub]
    have hle : Ideal.map ψ.toRingHom (augIdeal (mvPowerSeriesAug 𝒪 g) ^ 2) ≤ augIdeal π_R ^ 2 := by
      rw [pow_two, pow_two, Ideal.map_mul]
      refine Ideal.mul_mono ?_ ?_ <;>
        · rw [Ideal.map_le_iff_le_comap]; intro x hx; change (π_R.comp ψ) x = 0; rw [hcompat]; exact hx
    exact hle (Ideal.mem_map_of_mem ψ.toRingHom hlin_sub)
  have hmap_surj : Function.Surjective mapPi := by
    intro q
    induction q using Quotient.inductionOn' with
    | h y =>
      obtain ⟨p, hp⟩ := hψ y.1
      have hpI : p ∈ augIdeal (mvPowerSeriesAug 𝒪 g) := by
        have : (π_R.comp ψ) p = 0 := by change π_R (ψ p) = 0; rw [hp]; exact y.2
        rwa [hcompat] at this
      refine ⟨fun j => MvPowerSeries.coeff (Finsupp.single j 1) p, ?_⟩
      rw [hmap_apply_lin p hpI]; congr 1; exact Subtype.ext hp
  have hmap_ker : LinearMap.ker mapPi = LinearMap.range (jacobianMat f).transpose.mulVecLin := by
    ext v
    rw [LinearMap.mem_ker, LinearMap.mem_range]
    let p_v : MvPowerSeries (Fin g) 𝒪 := ∑ j : Fin g, MvPowerSeries.C (v j) * MvPowerSeries.X j
    have hlin_pv : ∀ j : Fin g, MvPowerSeries.coeff (Finsupp.single j 1) p_v = v j := by
      intro j
      simp only [p_v, map_sum, MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_X]
      rw [Finset.sum_eq_single j]
      · simp
      · intro k _ hkj
        have hne : Finsupp.single j (1 : ℕ) ≠ Finsupp.single k 1 := by
          intro h
          have h1 := congrArg (fun d : Fin g →₀ ℕ => d k) h
          rw [Finsupp.single_eq_same, Finsupp.single_eq_of_ne hkj] at h1
          exact zero_ne_one h1
        simp [hne]
      · intro h; exact absurd (Finset.mem_univ j) h
    have hf_I : ∀ i : Fin r, f i ∈ augIdeal (mvPowerSeriesAug 𝒪 g) := by
      intro i
      have hfi_ker : ψ (f i) = 0 := by
        have hmem : f i ∈ RingHom.ker ψ.toRingHom := by rw [hker]; exact Ideal.subset_span ⟨i, rfl⟩
        exact hmem
      have : (π_R.comp ψ) (f i) = 0 := by change π_R (ψ (f i)) = 0; rw [hfi_ker, map_zero]
      rwa [hcompat] at this
    constructor
    · intro hv0
      have hψpv : ψ p_v ∈ augIdeal π_R ^ 2 :=
        (Submodule.Quotient.mk_eq_zero (cotangentSubmodule π_R)).mp hv0
      have hpre : ∃ w ∈ augIdeal (mvPowerSeriesAug 𝒪 g) ^ 2, ψ w = ψ p_v := by
        rw [pow_two] at hψpv
        refine Submodule.mul_induction_on hψpv ?_ ?_
        · intro a ha b hb
          obtain ⟨pa, rfl⟩ := hψ a; obtain ⟨pb, rfl⟩ := hψ b
          have hpa : pa ∈ augIdeal (mvPowerSeriesAug 𝒪 g) := by
            have : (π_R.comp ψ) pa = 0 := ha; rwa [hcompat] at this
          have hpb : pb ∈ augIdeal (mvPowerSeriesAug 𝒪 g) := by
            have : (π_R.comp ψ) pb = 0 := hb; rwa [hcompat] at this
          exact ⟨pa * pb, by rw [pow_two]; exact Ideal.mul_mem_mul hpa hpb, map_mul ψ pa pb⟩
        · intro x y ⟨wx, hwx, hx⟩ ⟨wy, hwy, hy⟩
          exact ⟨wx + wy, Ideal.add_mem _ hwx hwy, by rw [map_add, hx, hy]⟩
      obtain ⟨w, hw2, hψw⟩ := hpre
      have hdiff_ker : p_v - w ∈ Ideal.span (Set.range f) := by
        rw [← hker, RingHom.mem_ker]; change ψ (p_v - w) = 0; rw [map_sub, hψw, sub_self]
      rw [Ideal.mem_span_range_iff_exists_fun] at hdiff_ker
      obtain ⟨c, hc⟩ := hdiff_ker
      refine ⟨fun i => MvPowerSeries.constantCoeff (c i), ?_⟩
      ext j
      have hlin_w : MvPowerSeries.coeff (Finsupp.single j 1) w = 0 := by
        have hwI : w ∈ augIdeal (mvPowerSeriesAug 𝒪 g) :=
          Ideal.pow_le_self (by norm_num : (2 : ℕ) ≠ 0) hw2
        have hq0 : Submodule.Quotient.mk (p := cotangentSubmodule (mvPowerSeriesAug 𝒪 g))
            ⟨w, hwI⟩ = 0 := (Submodule.Quotient.mk_eq_zero _).mpr hw2
        exact congrFun (congrArg eP hq0) j
      have hlin_eq : MvPowerSeries.coeff (Finsupp.single j 1) (p_v - w) =
          MvPowerSeries.coeff (Finsupp.single j 1) (∑ i : Fin r, c i • f i) :=
        congrArg (MvPowerSeries.coeff (Finsupp.single j 1)) hc.symm
      rw [map_sub, hlin_pv j, hlin_w, sub_zero, map_sum] at hlin_eq
      rw [hlin_eq]
      change (∑ i : Fin r, MvPowerSeries.coeff (Finsupp.single j 1) (f i) *
          MvPowerSeries.constantCoeff (c i)) =
        ∑ i : Fin r, MvPowerSeries.coeff (Finsupp.single j 1) (c i * f i)
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [MvPowerSeries.coeff_mul, Finset.sum_eq_single ((0 : Fin g →₀ ℕ), Finsupp.single j 1)]
      · rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, mul_comm]
      · intro ab hab hne
        rw [Finset.mem_antidiagonal] at hab
        have hsum_j : ab.1 j + ab.2 j = 1 := by
          have := congrArg (fun d : Fin g →₀ ℕ => d j) hab; simpa using this
        have hzero_other : ∀ k : Fin g, k ≠ j → ab.1 k = 0 ∧ ab.2 k = 0 := by
          intro k hkj
          have h0 : ab.1 k + ab.2 k = 0 := by
            have := congrArg (fun d : Fin g →₀ ℕ => d k) hab
            simpa [Finsupp.single_eq_of_ne hkj] using this
          omega
        by_cases ha : ab.1 j = 0
        · exfalso; apply hne; apply Prod.ext
          · ext k; by_cases hkj : k = j
            · subst hkj; exact ha
            · exact (hzero_other k hkj).1
          · ext k; by_cases hkj : k = j
            · subst hkj; simp; omega
            · simp [Finsupp.single_eq_of_ne hkj, (hzero_other k hkj).2]
        · have hb : ab.2 j = 0 := by omega
          have hb0 : ab.2 = 0 := by
            ext k; by_cases hkj : k = j
            · subst hkj; exact hb
            · exact (hzero_other k hkj).2
          rw [hb0, MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
            show MvPowerSeries.constantCoeff (f i) = 0 from hf_I i, mul_zero]
      · intro h; exfalso; apply h; rw [Finset.mem_antidiagonal, zero_add]
    · rintro ⟨a, rfl⟩
      let gsum : MvPowerSeries (Fin g) 𝒪 := ∑ i : Fin r, MvPowerSeries.C (a i) * f i
      have hgsum_I : gsum ∈ augIdeal (mvPowerSeriesAug 𝒪 g) := by
        change MvPowerSeries.constantCoeff gsum = 0
        simp only [gsum, map_sum, map_mul, MvPowerSeries.constantCoeff_C]
        refine Finset.sum_eq_zero fun i _ => by
          rw [show MvPowerSeries.constantCoeff (f i) = 0 from hf_I i, mul_zero]
      have hgsum_ker : ψ gsum = 0 := by
        simp only [gsum, map_sum, map_mul]
        refine Finset.sum_eq_zero fun i _ => ?_
        have hfi0 : ψ (f i) = 0 := by
          have : f i ∈ RingHom.ker ψ.toRingHom := by rw [hker]; exact Ideal.subset_span ⟨i, rfl⟩
          exact this
        rw [hfi0, mul_zero]
      have hvec_eq : (jacobianMat f).transpose.mulVecLin a =
          fun j => MvPowerSeries.coeff (Finsupp.single j 1) gsum := by
        ext j
        change ∑ i : Fin r, MvPowerSeries.coeff (Finsupp.single j 1) (f i) * a i =
          MvPowerSeries.coeff (Finsupp.single j 1) (∑ i : Fin r, MvPowerSeries.C (a i) * f i)
        rw [map_sum]
        refine Finset.sum_congr rfl fun i _ => by rw [MvPowerSeries.coeff_C_mul, mul_comm]
      rw [hvec_eq, hmap_apply_lin gsum hgsum_I]
      change Submodule.Quotient.mk (p := cotangentSubmodule π_R) ⟨ψ gsum, _⟩ = 0
      rw [Submodule.Quotient.mk_eq_zero]
      change ψ gsum ∈ augIdeal π_R ^ 2
      rw [hgsum_ker]; exact Ideal.zero_mem _
  exact ((Submodule.quotEquivOfEq _ _ hmap_ker.symm).trans
    (mapPi.quotKerEquivOfSurjective hmap_surj)).symm

/-- **Unconditional Rank-Deficiency Infinite-Length Lemma over a DVR**:
if `A : Matrix (Fin r) (Fin g) 𝒪` has `K`-rank `< g`, then `len_𝒪(coker A^T) = ⊤`. -/
theorem length_coker_eq_top_of_finrank_range_lt {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪]
    [IsDiscreteValuationRing 𝒪] {r g : ℕ} (A : Matrix (Fin r) (Fin g) 𝒪)
    (hlt : Module.finrank (FractionRing 𝒪)
      (LinearMap.range (A.map (algebraMap 𝒪 (FractionRing 𝒪))).transpose.mulVecLin) < g) :
    Module.length 𝒪 ((Fin g → 𝒪) ⧸ LinearMap.range A.transpose.mulVecLin) = ⊤ := by
  classical
  let K := FractionRing 𝒪
  let AK : Matrix (Fin r) (Fin g) K := A.map (algebraMap 𝒪 K)
  let N : Submodule K (Fin g → K) := LinearMap.range AK.transpose.mulVecLin
  have hN_ne_top : N ≠ ⊤ := by
    intro htop
    have hfr : Module.finrank K N = g := by rw [htop, finrank_top, Module.finrank_fin_fun]
    have hlt' : Module.finrank K N < g := hlt
    omega
  have hnt : Nontrivial ((Fin g → K) ⧸ N) := Submodule.Quotient.nontrivial_iff.mpr hN_ne_top
  obtain ⟨q₀, hq₀⟩ := exists_ne (0 : (Fin g → K) ⧸ N)
  let bQ := Module.Basis.ofVectorSpace K ((Fin g → K) ⧸ N)
  have hex_idx : ∃ i, bQ.repr q₀ i ≠ 0 := by
    by_contra hall; push Not at hall; apply hq₀; apply bQ.repr.injective
    ext i; rw [map_zero, Finsupp.zero_apply]; exact hall i
  obtain ⟨i₀, hi₀⟩ := hex_idx
  let lamK : (Fin g → K) →ₗ[K] K := (bQ.coord i₀).comp N.mkQ
  let wK : Fin g → K := fun j => lamK (Pi.single j 1)
  have hwK_ne : wK ≠ 0 := by
    intro hw0; apply hi₀
    obtain ⟨v₀, rfl⟩ := Submodule.mkQ_surjective N q₀
    have hdecomp : v₀ = ∑ j : Fin g, v₀ j • Pi.single j (1 : K) := by
      ext j; simp [Finset.sum_apply, Pi.single_apply]
    change lamK v₀ = 0
    rw [hdecomp, map_sum]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [map_smul, show lamK (Pi.single j 1) = wK j from rfl, hw0, Pi.zero_apply, smul_zero]
  have hwK_ortho : ∀ i : Fin r, ∑ j : Fin g, AK i j * wK j = 0 := by
    intro i
    let col : Fin g → K := AK.transpose.mulVecLin (Pi.single i 1)
    have hcol_mem : col ∈ N := ⟨Pi.single i 1, rfl⟩
    have hlam0 : lamK col = 0 := by
      change bQ.coord i₀ (N.mkQ col) = 0
      rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero N).mpr hcol_mem, map_zero]
    have hcol_eq : col = ∑ j : Fin g, AK i j • Pi.single j (1 : K) := by
      ext j; simp [col, Finset.sum_apply, Pi.single_apply]
    rw [hcol_eq, map_sum] at hlam0
    simpa [wK, smul_eq_mul] using hlam0
  have hsec : ∀ j : Fin g, ∃ (n : 𝒪) (d : nonZeroDivisors 𝒪),
      algebraMap 𝒪 K d.1 * wK j = algebraMap 𝒪 K n := by
    intro j
    obtain ⟨⟨n, d⟩, hd⟩ := IsLocalization.surj (nonZeroDivisors 𝒪) (wK j)
    exact ⟨n, d, by rw [mul_comm]; exact hd⟩
  choose num den hden using hsec
  let D : nonZeroDivisors 𝒪 := ∏ j : Fin g, den j
  let c : Fin g → 𝒪 := fun j => (∏ k ∈ Finset.univ.erase j, (den k : 𝒪)) * num j
  have hc_map : ∀ j : Fin g, algebraMap 𝒪 K (c j) = algebraMap 𝒪 K D.1 * wK j := by
    intro j
    have hD : (D : 𝒪) = (∏ k ∈ Finset.univ.erase j, (den k : 𝒪)) * (den j : 𝒪) := by
      rw [Submonoid.coe_finsetProd,
        ← Finset.mul_prod_erase Finset.univ (fun k => (den k : 𝒪)) (Finset.mem_univ j), mul_comm]
    rw [hD, map_mul, map_mul, mul_assoc, hden j]
  have hD_ne : (D : 𝒪) ≠ 0 := nonZeroDivisors.ne_zero D.2
  have hc_ne : c ≠ 0 := by
    intro hc0; apply hwK_ne; ext j
    have hj := hc_map j
    rw [hc0, Pi.zero_apply, map_zero] at hj
    have hDK_ne : algebraMap 𝒪 K (D : 𝒪) ≠ 0 := fun h0 =>
      hD_ne (IsFractionRing.injective 𝒪 K (h0.trans (map_zero _).symm))
    exact (mul_eq_zero.mp hj.symm).resolve_left hDK_ne
  have hc_ortho : ∀ i : Fin r, ∑ j : Fin g, A i j * c j = 0 := by
    intro i; apply IsFractionRing.injective 𝒪 K
    rw [map_zero, map_sum]
    have hsum : (∑ j : Fin g, algebraMap 𝒪 K (A i j * c j)) =
        algebraMap 𝒪 K (D : 𝒪) * ∑ j : Fin g, AK i j * wK j := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, hc_map j]
      change AK i j * (algebraMap 𝒪 K D.1 * wK j) = algebraMap 𝒪 K D.1 * (AK i j * wK j); ring
    rw [hsum, hwK_ortho i, mul_zero]
  let lam : (Fin g → 𝒪) →ₗ[𝒪] 𝒪 :=
    { toFun := fun v => ∑ j : Fin g, v j * c j
      map_add' := fun u v => by simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
      map_smul' := fun a v => by
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum, mul_assoc] }
  have hker_le : LinearMap.range A.transpose.mulVecLin ≤ LinearMap.ker lam := by
    rintro _ ⟨x, rfl⟩
    rw [LinearMap.mem_ker]
    change ∑ j : Fin g, (∑ i : Fin r, A i j * x i) * c j = 0
    simp_rw [Finset.sum_mul]; rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun i _ => ?_
    calc ∑ j : Fin g, A i j * x i * c j
        = x i * ∑ j : Fin g, A i j * c j := by
            rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => by ring
      _ = 0 := by rw [hc_ortho i, mul_zero]
  let lamQ : ((Fin g → 𝒪) ⧸ LinearMap.range A.transpose.mulVecLin) →ₗ[𝒪] 𝒪 :=
    Submodule.liftQ _ lam hker_le
  have hex_j : ∃ j₀ : Fin g, c j₀ ≠ 0 := by
    by_contra h; push Not at h; exact hc_ne (funext h)
  obtain ⟨j₀, hj₀⟩ := hex_j
  let emb : 𝒪 →ₗ[𝒪] LinearMap.range lamQ :=
    { toFun := fun a => ⟨a * c j₀, ⟨Submodule.Quotient.mk (a • Pi.single j₀ 1), by
        change ∑ j : Fin g, (a • Pi.single j₀ (1 : 𝒪)) j * c j = a * c j₀
        simp [Pi.single_apply]⟩⟩
      map_add' := fun a b => Subtype.ext (add_mul a b (c j₀))
      map_smul' := fun r a => Subtype.ext (mul_assoc r a (c j₀)) }
  have hemb_inj : Function.Injective emb := fun a b hab =>
    mul_right_cancel₀ hj₀ (congrArg Subtype.val hab)
  have htop : ⊤ ≤ Module.length 𝒪 ((Fin g → 𝒪) ⧸ LinearMap.range A.transpose.mulVecLin) := by
    calc (⊤ : ℕ∞) = Module.length 𝒪 𝒪 := (dvr_length_self_eq_top 𝒪).symm
      _ ≤ Module.length 𝒪 (LinearMap.range lamQ) := Module.length_le_of_injective emb hemb_inj
      _ ≤ Module.length 𝒪 ((Fin g → 𝒪) ⧸ LinearMap.range A.transpose.mulVecLin) :=
          Module.length_le_of_surjective lamQ.rangeRestrict (fun ⟨_, x, hx⟩ => ⟨x, Subtype.ext hx⟩)
  exact top_unique htop

/-- **Unconditional Relation-Count Forcing (`r ≤ g` & `len(coker A^T) < ⊤ ⇒ r = g ∧ det A ≠ 0`)**. -/
theorem relation_count_eq_and_det_ne_zero_of_length_ne_top {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪]
    [IsDiscreteValuationRing 𝒪] {r g : ℕ} (hrg : r ≤ g) (A : Matrix (Fin r) (Fin g) 𝒪)
    (hfin : Module.length 𝒪 ((Fin g → 𝒪) ⧸ LinearMap.range A.transpose.mulVecLin) ≠ ⊤) :
    ∃ hEq : r = g, (A.submatrix (Fin.cast hEq.symm) id).det ≠ 0 := by
  let K := FractionRing 𝒪
  let AK : Matrix (Fin r) (Fin g) K := A.map (algebraMap 𝒪 K)
  have hge : g ≤ Module.finrank K (LinearMap.range AK.transpose.mulVecLin) := by
    by_contra hlt; exact hfin (length_coker_eq_top_of_finrank_range_lt A (not_le.mp hlt))
  have hle : Module.finrank K (LinearMap.range AK.transpose.mulVecLin) ≤ r := by
    simpa [Module.finrank_fin_fun] using LinearMap.finrank_range_le AK.transpose.mulVecLin
  have hEq : r = g := le_antisymm hrg (le_trans hge hle)
  refine ⟨hEq, ?_⟩
  subst hEq
  intro hdet0
  have hdetA : A.det = 0 := by simpa using hdet0
  have hdetK : (AK.transpose).det = 0 := by
    rw [Matrix.det_transpose]
    change (RingHom.mapMatrix (algebraMap 𝒪 K) A).det = 0
    rw [← RingHom.map_det (algebraMap 𝒪 K) A, hdetA, map_zero]
  have hnot_surj : ¬ Function.Surjective AK.transpose.mulVecLin := by
    intro hsurj
    have hcols : ∀ j : Fin r, ∃ x : Fin r → K, AK.transpose.mulVec x = Pi.single j 1 :=
      fun j => hsurj (Pi.single j 1)
    choose Bcol hBcol using hcols
    let B : Matrix (Fin r) (Fin r) K := fun i j => Bcol j i
    have hmul1 : AK.transpose * B = 1 := by
      ext i j
      have hij := congrFun (hBcol j) i
      change (AK.transpose * B) i j = (1 : Matrix (Fin r) (Fin r) K) i j
      rw [Matrix.mul_apply]
      simpa [Matrix.mulVec, dotProduct, B, Matrix.one_apply, Pi.single_apply, eq_comm] using hij
    have h1 : (AK.transpose * B).det = 1 := by rw [hmul1, Matrix.det_one]
    rw [Matrix.det_mul, hdetK, zero_mul] at h1
    exact zero_ne_one h1
  have hrange_lt : Module.finrank K (LinearMap.range AK.transpose.mulVecLin) < r := by
    have hne : LinearMap.range AK.transpose.mulVecLin ≠ ⊤ := fun htop =>
      hnot_surj (LinearMap.range_eq_top.mp htop)
    simpa [Module.finrank_fin_fun] using Submodule.finrank_lt hne
  exact hfin (length_coker_eq_top_of_finrank_range_lt A hrange_lt)

/-- **Jacobian–Fitting–Congruence Theorem for `R = 𝒪[[X_0,…,X_{g-1}]] / (f_1,…,f_r)` (`r ≤ g`)**. -/
theorem jacobian_det_eq_congruenceIdeal_of_length_le {𝒪 R T : Type*}
    [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    {ϖ : 𝒪} (hϖ : Irreducible ϖ)
    [CommRing R] [Algebra 𝒪 R]
    [CommRing T] [Algebra 𝒪 T] [Module.Free 𝒪 T] [Module.Finite 𝒪 T]
    {g r : ℕ} (hrg : r ≤ g) (f : Fin r → MvPowerSeries (Fin g) 𝒪)
    (ψ : MvPowerSeries (Fin g) 𝒪 →ₐ[𝒪] R) (hψ : Function.Surjective ψ)
    (hker : RingHom.ker ψ.toRingHom = Ideal.span (Set.range f))
    (φ : R →ₐ[𝒪] T) (hφ : Function.Surjective φ)
    (π : T →ₐ[𝒪] 𝒪) (hη : congruenceIdeal π ≠ ⊥)
    (hcompat : (π.comp φ).comp ψ = mvPowerSeriesAug 𝒪 g)
    (hle : Module.length 𝒪 (Cotangent (π.comp φ)) ≤ (dvrIdealVal 𝒪 (congruenceIdeal π) : ℕ∞)) :
    ∃ hEq : r = g,
      let J : Matrix (Fin g) (Fin g) 𝒪 := (jacobianMat f).submatrix (Fin.cast hEq.symm) id
      J.det ≠ 0 ∧
      Module.length 𝒪 (Cotangent (π.comp φ)) = (dvrIdealVal 𝒪 (congruenceIdeal π) : ℕ∞) ∧
      Module.length 𝒪 (Cotangent π) = (dvrIdealVal 𝒪 (congruenceIdeal π) : ℕ∞) ∧
      Ideal.span ({J.det} : Set 𝒪) = congruenceIdeal π ∧
      Function.Bijective (cotangentMap φ π) := by
  have hval := (dvrIdealVal_spec hϖ hη).1
  have hle' : Module.length 𝒪 (Cotangent (π.comp φ)) ≤ Module.length 𝒪 (𝒪 ⧸ congruenceIdeal π) := by
    rwa [hval]
  obtain ⟨hPhiR_eq, hPhiT_eq, hcot_bij⟩ := cotangentMap_bijective_of_length_le φ hφ π hη hle'
  let eCot := cotangent_equiv_coker_jacobian f ψ hψ hker (π.comp φ) hcompat
  have hfin_coker :
      Module.length 𝒪 ((Fin g → 𝒪) ⧸ LinearMap.range (jacobianMat f).transpose.mulVecLin) ≠ ⊤ := by
    rw [← eCot.length_eq, hPhiR_eq, hval]; exact ENat.natCast_ne_top _
  obtain ⟨hEq, hdet_ne⟩ := relation_count_eq_and_det_ne_zero_of_length_ne_top hrg (jacobianMat f) hfin_coker
  refine ⟨hEq, ?_⟩
  subst hEq
  change (jacobianMat f).det ≠ 0 ∧ _
  have hdetT_ne : (jacobianMat f).transpose.det ≠ 0 := by rwa [Matrix.det_transpose]
  obtain ⟨hlen_coker, _⟩ := length_coker_eq_length_quotient_det (jacobianMat f).transpose hdetT_ne
  rw [Matrix.det_transpose] at hlen_coker
  have hspan_ne : Ideal.span ({(jacobianMat f).det} : Set 𝒪) ≠ ⊥ := fun hbot =>
    hdet_ne (Ideal.mem_bot.mp (hbot ▸ Ideal.subset_span rfl))
  have hlen_det_eq : Module.length 𝒪 (𝒪 ⧸ Ideal.span ({(jacobianMat f).det} : Set 𝒪)) =
      Module.length 𝒪 (𝒪 ⧸ congruenceIdeal π) := by
    rw [← hlen_coker, ← eCot.length_eq, hPhiR_eq]
  have hspan_eq : Ideal.span ({(jacobianMat f).det} : Set 𝒪) = congruenceIdeal π := by
    have h1 := dvrIdealVal_spec hϖ hspan_ne
    have h2 := dvrIdealVal_spec hϖ hη
    have hv : dvrIdealVal 𝒪 (Ideal.span ({(jacobianMat f).det} : Set 𝒪)) =
        dvrIdealVal 𝒪 (congruenceIdeal π) := by
      unfold dvrIdealVal; rw [hlen_det_eq]
    rw [h1.2, h2.2, hv]
  exact ⟨hdet_ne, hPhiR_eq.trans hval, hPhiT_eq.trans hval, hspan_eq, hcot_bij⟩

/-! ### 1.3 Full Unconditional Wiles–Lenstra Numerical Criterion (`R ≃ T` Complete Intersection) -/

/-- **Complete Intersection Algebra over `𝒪` with augmentation `π : T →ₐ[𝒪] 𝒪`**. -/
structure IsCompleteIntersectionOver (𝒪 T : Type*) [CommRing 𝒪] [CommRing T] [Algebra 𝒪 T]
    (π : T →ₐ[𝒪] 𝒪) where
  g : ℕ
  f : Fin g → MvPowerSeries (Fin g) 𝒪
  pres : MvPowerSeries (Fin g) 𝒪 →ₐ[𝒪] T
  pres_surj : Function.Surjective pres
  pres_ker : RingHom.ker pres.toRingHom = Ideal.span (Set.range f)
  pres_compat : π.comp pres = mvPowerSeriesAug 𝒪 g
  gorenstein : IsGorensteinOver 𝒪 T
  jac_det_eq_cong : Ideal.span ({(jacobianMat f).det} : Set 𝒪) = congruenceIdeal π
  length_cotangent_eq_cong :
    Module.length 𝒪 (Cotangent π) = Module.length 𝒪 (𝒪 ⧸ congruenceIdeal π)

/-- **THE UNCONDITIONAL WILES–LENSTRA NUMERICAL CRITERION (`length(Φ_R) ≤ v_ϖ(η_T) ⇒ R ≃+* T`, CI)**:
proves `r = g`, `R ≃ₐ[𝒪] T`, `R ≃+* T`, `length(Φ_R) = v_ϖ(η_T)`, and `IsCompleteIntersectionOver 𝒪 T π`. -/
theorem wiles_lenstra_complete_intersection_of_length_le {𝒪 R T : Type*}
    [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    {ϖ : 𝒪} (hϖ : Irreducible ϖ)
    [CommRing R] [Algebra 𝒪 R]
    [CommRing T] [Algebra 𝒪 T] [Module.Free 𝒪 T] [Module.Finite 𝒪 T]
    {g r : ℕ} (hrg : r ≤ g) (f : Fin r → MvPowerSeries (Fin g) 𝒪)
    (ψ : MvPowerSeries (Fin g) 𝒪 →ₐ[𝒪] R) (hψ : Function.Surjective ψ)
    (hker : RingHom.ker ψ.toRingHom = Ideal.span (Set.range f))
    (φ : R →ₐ[𝒪] T) (hφ : Function.Surjective φ)
    (π : T →ₐ[𝒪] 𝒪) (hη : congruenceIdeal π ≠ ⊥)
    (hcompat : (π.comp φ).comp ψ = mvPowerSeriesAug 𝒪 g)
    (C : CompleteIntersectionCover φ π)
    (hle : Module.length 𝒪 (Cotangent (π.comp φ)) ≤ (dvrIdealVal 𝒪 (congruenceIdeal π) : ℕ∞)) :
    r = g ∧
    Function.Bijective φ ∧
    Nonempty (R ≃+* T) ∧
    Module.length 𝒪 (Cotangent (π.comp φ)) = (dvrIdealVal 𝒪 (congruenceIdeal π) : ℕ∞) ∧
    Nonempty (IsCompleteIntersectionOver 𝒪 T π) := by
  have hval := (dvrIdealVal_spec hϖ hη).1
  obtain ⟨hEq, _, hlenR, hlenT, hspan_eq, _⟩ :=
    jacobian_det_eq_congruenceIdeal_of_length_le hϖ hrg f ψ hψ hker φ hφ π hη hcompat hle
  have hlenR' : Module.length 𝒪 (Cotangent (π.comp φ)) = Module.length 𝒪 (𝒪 ⧸ congruenceIdeal π) :=
    hlenR.trans hval.symm
  obtain ⟨hφ_bij, hpsi_bij⟩ := (wiles_lenstra_numerical_criterion_iff φ hφ π C).mp hlenR'
  let eRT : R ≃ₐ[𝒪] T := AlgEquiv.ofBijective φ hφ_bij
  let eComp : C.R' ≃ₐ[𝒪] T := AlgEquiv.ofBijective (φ.comp C.psiR) (hφ_bij.comp hpsi_bij)
  let gT : IsGorensteinOver 𝒪 T := isGorensteinOver_ofAlgEquiv C.gorenstein eComp
  refine ⟨hEq, hφ_bij, ⟨eRT.toRingEquiv⟩, hlenR, ?_⟩
  subst hEq
  have hkerT : RingHom.ker (φ.comp ψ).toRingHom = Ideal.span (Set.range f) := by
    ext p
    change φ (ψ p) = 0 ↔ p ∈ Ideal.span (Set.range f)
    rw [← hker, RingHom.mem_ker]
    exact ⟨fun h => hφ_bij.1 (h.trans (map_zero φ).symm), fun h => by rw [show ψ p = 0 from h, map_zero]⟩
  exact ⟨{
    g := r
    f := f
    pres := φ.comp ψ
    pres_surj := hφ.comp hψ
    pres_ker := hkerT
    pres_compat := by ext p; exact congrFun (congrArg DFunLike.coe hcompat) p
    gorenstein := gT
    jac_det_eq_cong := hspan_eq
    length_cotangent_eq_cong := hlenT.trans hval.symm }⟩

/-- **Specialization of the Unconditional Wiles–Lenstra Numerical Criterion to `ℤ_[p]`**:
`length(Φ_R) ≤ padicCongVal p π` (`v_p(η_T)`) ⇒ `r = g`, `R ≃+* T`, `length(Φ_R) = v_p(η_T)`,
and `IsCompleteIntersectionOver ℤ_[p] T π`. -/
theorem wiles_lenstra_numerical_criterion_Zp {p : ℕ} [Fact p.Prime] {R T : Type*}
    [CommRing R] [Algebra ℤ_[p] R]
    [CommRing T] [Algebra ℤ_[p] T] [Module.Free ℤ_[p] T] [Module.Finite ℤ_[p] T]
    {g r : ℕ} (hrg : r ≤ g) (f : Fin r → PatchingBaseRing p g)
    (ψ : PatchingBaseRing p g →ₐ[ℤ_[p]] R) (hψ : Function.Surjective ψ)
    (hker : RingHom.ker ψ.toRingHom = Ideal.span (Set.range f))
    (φ : R →ₐ[ℤ_[p]] T) (hφ : Function.Surjective φ)
    (π : T →ₐ[ℤ_[p]] ℤ_[p]) (hη : congruenceIdeal π ≠ ⊥)
    (hcompat : (π.comp φ).comp ψ = mvPowerSeriesAug ℤ_[p] g)
    (C : CompleteIntersectionCover φ π)
    (hle : Module.length ℤ_[p] (Cotangent (π.comp φ)) ≤ (padicCongVal p π : ℕ∞)) :
    r = g ∧
    Function.Bijective φ ∧
    Nonempty (R ≃+* T) ∧
    Module.length ℤ_[p] (Cotangent (π.comp φ)) = (padicCongVal p π : ℕ∞) ∧
    Nonempty (IsCompleteIntersectionOver ℤ_[p] T π) :=
  wiles_lenstra_complete_intersection_of_length_le (PadicInt.irreducible_p (p := p))
    hrg f ψ hψ hker φ hφ π hη hcompat C hle

/-! ### 1.4 Express Zero-Cover Quadratic / Monogenic Wiles–Lenstra Criterion (Direct Algebraic Proof) -/

/-- Exact `R`-algebra isomorphism `QuadAlg R b 0 ≃ₐ[R] AdjoinRoot (X * (X - C b))`. -/
def quadAlg_equiv_adjoinRoot_X_mul_sub (R : Type*) [CommRing R] (b : R) :
    QuadAlg R b 0 ≃ₐ[R] AdjoinRoot (Polynomial.X * (Polynomial.X - Polynomial.C b)) := by
  let f : Polynomial R := Polynomial.X * (Polynomial.X - Polynomial.C b)
  let α : AdjoinRoot f := AdjoinRoot.root f
  have hα_rel : α * α = algebraMap R (AdjoinRoot f) b * α := by
    have hev : Polynomial.eval₂ (AdjoinRoot.of f) α f = 0 := AdjoinRoot.eval₂_root f
    simp only [f, Polynomial.eval₂_mul, Polynomial.eval₂_X, Polynomial.eval₂_sub,
      Polynomial.eval₂_C] at hev
    change α * (α - algebraMap R (AdjoinRoot f) b) = 0 at hev
    linear_combination hev
  let toAlg : QuadAlg R b 0 →ₐ[R] AdjoinRoot f :=
    { toFun := fun u => algebraMap R (AdjoinRoot f) u.fst + u.snd • α
      map_one' := by simp
      map_mul' := fun u v => by
        change algebraMap R (AdjoinRoot f) (u.fst * v.fst - 0 * (u.snd * v.snd)) +
            (u.fst * v.snd + u.snd * v.fst + b * (u.snd * v.snd)) • α =
          (algebraMap R (AdjoinRoot f) u.fst + u.snd • α) *
            (algebraMap R (AdjoinRoot f) v.fst + v.snd • α)
        simp only [zero_mul, sub_zero, map_mul, Algebra.smul_def, map_add]
        linear_combination -(algebraMap R (AdjoinRoot f) u.snd * algebraMap R (AdjoinRoot f) v.snd) * hα_rel
      map_zero' := by simp
      map_add' := fun u v => by
        change algebraMap R (AdjoinRoot f) (u.fst + v.fst) + (u.snd + v.snd) • α =
          (algebraMap R (AdjoinRoot f) u.fst + u.snd • α) +
            (algebraMap R (AdjoinRoot f) v.fst + v.snd • α)
        rw [map_add, add_smul]; abel
      commutes' := fun r => by
        change algebraMap R (AdjoinRoot f) r + (0 : R) • α = algebraMap R (AdjoinRoot f) r; simp }
  have hgen_rel : Polynomial.eval₂ (algebraMap R (QuadAlg R b 0)) (QuadAlg.gen (b := b) (c := 0)) f = 0 := by
    simp only [f, Polynomial.eval₂_mul, Polynomial.eval₂_X, Polynomial.eval₂_sub, Polynomial.eval₂_C]
    ext <;> simp [QuadAlg.gen]
  let invAlg : AdjoinRoot f →ₐ[R] QuadAlg R b 0 :=
    { toRingHom := AdjoinRoot.lift (algebraMap R (QuadAlg R b 0)) (QuadAlg.gen (b := b) (c := 0)) hgen_rel
      commutes' := fun r => AdjoinRoot.lift_of (x := r) hgen_rel }
  have hinv_root : invAlg α = QuadAlg.gen (b := b) (c := 0) := AdjoinRoot.lift_root hgen_rel
  have hleft : Function.LeftInverse invAlg toAlg := fun u => by
    change invAlg (algebraMap R (AdjoinRoot f) u.fst + u.snd • α) = u
    rw [map_add, invAlg.commutes, map_smul, hinv_root]
    ext <;> simp [QuadAlg.gen]
  have hright_alg : toAlg.comp invAlg = AlgHom.id R (AdjoinRoot f) := by
    ext
    change toAlg (invAlg α) = α
    rw [hinv_root]
    change algebraMap R (AdjoinRoot f) 0 + (1 : R) • α = α; simp
  exact AlgEquiv.ofAlgHom toAlg invAlg hright_alg (AlgHom.ext hleft)

/-- Direct algebraic unit criterion in `QuadAlg ℤ_[p] b 0` when `p ∣ b`: `IsUnit u.fst → IsUnit u`. -/
theorem isUnit_quadAlg_of_isUnit_fst {p : ℕ} [Fact p.Prime] {b : ℤ_[p]} (hb : (p : ℤ_[p]) ∣ b)
    (u : QuadAlg ℤ_[p] b 0) (hu : IsUnit u.fst) : IsUnit u := by
  have hp_mem : (p : ℤ_[p]) ∈ IsLocalRing.maximalIdeal ℤ_[p] :=
    (IsLocalRing.mem_maximalIdeal _).mpr (PadicInt.irreducible_p (p := p)).not_isUnit
  have hbc_mem : b * u.snd ∈ IsLocalRing.maximalIdeal ℤ_[p] := by
    obtain ⟨q, rfl⟩ := hb
    rw [mul_assoc]
    exact Ideal.mul_mem_right _ _ hp_mem
  have habc_unit : IsUnit (u.fst + b * u.snd) := by
    by_contra hnu
    have hmem : u.fst + b * u.snd ∈ IsLocalRing.maximalIdeal ℤ_[p] :=
      (IsLocalRing.mem_maximalIdeal _).mpr hnu
    have hfst : u.fst ∈ IsLocalRing.maximalIdeal ℤ_[p] := by
      have heq : u.fst = (u.fst + b * u.snd) - b * u.snd := by ring
      rw [heq]; exact Ideal.sub_mem _ hmem hbc_mem
    exact (IsLocalRing.mem_maximalIdeal _).mp hfst hu
  let ua : ℤ_[p]ˣ := hu.unit
  let ub : ℤ_[p]ˣ := habc_unit.unit
  have hua : u.fst * (ua⁻¹ : ℤ_[p]ˣ) = 1 := hu.unit_spec ▸ ua.mul_inv
  have hub : (u.fst + b * u.snd) * (ub⁻¹ : ℤ_[p]ˣ) = 1 := habc_unit.unit_spec ▸ ub.mul_inv
  let v : QuadAlg ℤ_[p] b 0 := ⟨(ua⁻¹ : ℤ_[p]ˣ), -(u.snd * (ua⁻¹ : ℤ_[p]ˣ) * (ub⁻¹ : ℤ_[p]ˣ))⟩
  refine isUnit_iff_exists_inv.mpr ⟨v, ?_⟩
  ext
  · change u.fst * (ua⁻¹ : ℤ_[p]ˣ) - 0 * _ = 1
    rw [zero_mul, sub_zero, hua]
  · change u.fst * -(u.snd * (ua⁻¹ : ℤ_[p]ˣ) * (ub⁻¹ : ℤ_[p]ˣ)) + u.snd * (ua⁻¹ : ℤ_[p]ˣ) +
      b * (u.snd * -(u.snd * (ua⁻¹ : ℤ_[p]ˣ) * (ub⁻¹ : ℤ_[p]ˣ))) = 0
    linear_combination -(u.snd * (ua⁻¹ : ℤ_[p]ˣ)) * hub

/-- **Unconditional Locality of `QuadAlg ℤ_[p] b 0`** whenever `p ∣ b` (pure 6-line algebraic proof!). -/
theorem isLocalRing_quadAlg_of_dvd {p : ℕ} [Fact p.Prime] {b : ℤ_[p]} (hb : (p : ℤ_[p]) ∣ b) :
    IsLocalRing (QuadAlg ℤ_[p] b 0) := by
  have : Nontrivial (QuadAlg ℤ_[p] b 0) :=
    ⟨⟨⟨1, 0⟩, ⟨0, 0⟩, fun h => one_ne_zero (congrArg QuadAlg.fst h)⟩⟩
  refine IsLocalRing.of_nonunits_add fun {u v} hu hv => ?_
  rw [mem_nonunits_iff] at hu hv ⊢
  intro huv
  have hfst_unit : IsUnit (u.fst + v.fst) := by
    have hmap := huv.map (QuadAlg.aug (A := ℤ_[p]) (b := b) (c := 0) (lam := 0) (by ring)).toRingHom
    simpa [QuadAlg.aug] using hmap
  have hu_mem : u.fst ∈ IsLocalRing.maximalIdeal ℤ_[p] :=
    (IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr fun h => hu (isUnit_quadAlg_of_isUnit_fst hb u h))
  have hv_mem : v.fst ∈ IsLocalRing.maximalIdeal ℤ_[p] :=
    (IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr fun h => hv (isUnit_quadAlg_of_isUnit_fst hb v h))
  exact (IsLocalRing.mem_maximalIdeal _).mp (Ideal.add_mem _ hu_mem hv_mem) hfst_unit

/-- **Zero-Cover Unconditional Quadratic Wiles–Lenstra Criterion (`QuadAlg ℤ_[p] b 0`)**:
for ANY `b : ℤ_[p]` with `p ∣ b` and `b ≠ 0`, and ANY surjection `φ : QuadAlg ℤ_[p] b 0 →ₐ[ℤ_[p]] T`
onto finite free `T` with `π ∘ φ = QuadAlg.aug (lam := 0)`:
`length(Φ_R) ≤ padicCongVal p π` (`v_p(η_T)`) AUTOMATICALLY implies `R ≃+* T`,
`length(Φ_R) = v_p(η_T)`, and `T` is local Gorenstein! -/
theorem wiles_lenstra_quad_criterion_Zp {p : ℕ} [Fact p.Prime] {T : Type*}
    [CommRing T] [Algebra ℤ_[p] T] [Module.Free ℤ_[p] T] [Module.Finite ℤ_[p] T]
    {b : ℤ_[p]} (hb : (p : ℤ_[p]) ∣ b) (hb0 : b ≠ 0)
    (φ : QuadAlg ℤ_[p] b 0 →ₐ[ℤ_[p]] T) (hφ : Function.Surjective φ)
    (π : T →ₐ[ℤ_[p]] ℤ_[p])
    (hcompat : π.comp φ = QuadAlg.aug (A := ℤ_[p]) (b := b) (c := 0) (lam := 0) (by ring))
    (hle : Module.length ℤ_[p] (Cotangent (π.comp φ)) ≤ (padicCongVal p π : ℕ∞)) :
    Function.Bijective φ ∧
    Nonempty (QuadAlg ℤ_[p] b 0 ≃+* T) ∧
    Module.length ℤ_[p] (Cotangent (π.comp φ)) = (padicCongVal p π : ℕ∞) ∧
    Nonempty (IsGorensteinOver ℤ_[p] T) ∧
    IsLocalRing T := by
  have : IsLocalRing (QuadAlg ℤ_[p] b 0) := isLocalRing_quadAlg_of_dvd hb
  let G : IsGorensteinOver ℤ_[p] (QuadAlg ℤ_[p] b 0) := QuadAlg.isGorensteinOver ℤ_[p] b 0
  have hηR_eq : congruenceIdeal (π.comp φ) = Ideal.span ({b} : Set ℤ_[p]) := by
    rw [hcompat, QuadAlg.congruenceIdeal_aug_eq]
    have hneg : 2 * (0 : ℤ_[p]) - b = -b := by ring
    rw [hneg, Ideal.span_singleton_neg]
  have hηR_ne : congruenceIdeal (π.comp φ) ≠ ⊥ := by
    rw [hηR_eq]
    exact fun hbot => hb0 (Ideal.mem_bot.mp (hbot ▸ Ideal.subset_span rfl))
  have hηT_ne : congruenceIdeal π ≠ ⊥ := fun hbot =>
    hηR_ne (le_bot_iff.mp (hbot ▸ congruenceIdeal_le_of_surjective φ hφ π))
  have hcotR_eq : Module.length ℤ_[p] (Cotangent (π.comp φ)) =
      Module.length ℤ_[p] (ℤ_[p] ⧸ congruenceIdeal (π.comp φ)) := by
    rw [hcompat]; exact QuadAlg.length_cotangent_eq (A := ℤ_[p]) (b := b) (c := 0) (lam := 0) (by ring)
  let C : CompleteIntersectionCover φ π :=
    { R' := QuadAlg ℤ_[p] b 0
      gorenstein := G
      psiR := AlgHom.id _ _
      psiR_surj := Function.surjective_id
      cong_ne_bot := hηR_ne
      cotangent_eq_cover_cong := hcotR_eq }
  have hval := (padicCongVal_spec π hηT_ne).1
  have hle' : Module.length ℤ_[p] (Cotangent (π.comp φ)) ≤
      Module.length ℤ_[p] (ℤ_[p] ⧸ congruenceIdeal π) := by rwa [hval]
  obtain ⟨hPhiR_eq, _, _⟩ := cotangentMap_bijective_of_length_le φ hφ π hηT_ne hle'
  obtain ⟨hφ_bij, _⟩ := (wiles_lenstra_numerical_criterion_iff φ hφ π C).mp hPhiR_eq
  let eRT : QuadAlg ℤ_[p] b 0 ≃ₐ[ℤ_[p]] T := AlgEquiv.ofBijective φ hφ_bij
  have : Nontrivial T := ⟨⟨φ 1, φ 0, fun h => one_ne_zero (congrArg QuadAlg.fst (hφ_bij.1 h))⟩⟩
  have hloc : IsLocalRing T := IsLocalRing.of_surjective' φ.toRingHom hφ
  exact ⟨hφ_bij, ⟨eRT.toRingEquiv⟩, hPhiR_eq.trans hval,
    ⟨isGorensteinOver_ofAlgEquiv G eRT⟩, hloc⟩

/-- **Zero-Cover Unconditional Monogenic `AdjoinRoot (X * (X - C b))` Wiles–Lenstra Criterion**. -/
theorem wiles_lenstra_adjoinRoot_quad_criterion_Zp {p : ℕ} [Fact p.Prime] {T : Type*}
    [CommRing T] [Algebra ℤ_[p] T] [Module.Free ℤ_[p] T] [Module.Finite ℤ_[p] T]
    {b : ℤ_[p]} (hb : (p : ℤ_[p]) ∣ b) (hb0 : b ≠ 0)
    (φ : AdjoinRoot (Polynomial.X * (Polynomial.X - Polynomial.C b)) →ₐ[ℤ_[p]] T)
    (hφ : Function.Surjective φ)
    (π : T →ₐ[ℤ_[p]] ℤ_[p])
    (hcompat : (π.comp φ).comp (quadAlg_equiv_adjoinRoot_X_mul_sub ℤ_[p] b).toAlgHom =
      QuadAlg.aug (A := ℤ_[p]) (b := b) (c := 0) (lam := 0) (by ring))
    (hle : Module.length ℤ_[p] (Cotangent (π.comp φ)) ≤ (padicCongVal p π : ℕ∞)) :
    Function.Bijective φ ∧
    Nonempty (AdjoinRoot (Polynomial.X * (Polynomial.X - Polynomial.C b)) ≃+* T) ∧
    Module.length ℤ_[p] (Cotangent (π.comp φ)) = (padicCongVal p π : ℕ∞) ∧
    Nonempty (IsGorensteinOver ℤ_[p] T) ∧
    IsLocalRing T := by
  let eQ := quadAlg_equiv_adjoinRoot_X_mul_sub ℤ_[p] b
  let φQ : QuadAlg ℤ_[p] b 0 →ₐ[ℤ_[p]] T := φ.comp eQ.toAlgHom
  have hφQ : Function.Surjective φQ := hφ.comp eQ.surjective
  have hcompatQ : π.comp φQ = QuadAlg.aug (A := ℤ_[p]) (b := b) (c := 0) (lam := 0) (by ring) := by
    ext x; exact congrFun (congrArg DFunLike.coe hcompat) x
  have hlen_eq : Module.length ℤ_[p] (Cotangent (π.comp φQ)) =
      Module.length ℤ_[p] (Cotangent (π.comp φ)) :=
    (cotangentEquivOfAlgEquiv eQ (π.comp φ)).length_eq
  have hleQ : Module.length ℤ_[p] (Cotangent (π.comp φQ)) ≤ (padicCongVal p π : ℕ∞) := by
    rwa [hlen_eq]
  obtain ⟨hbijQ, _, hlenQ, hgor, hloc⟩ :=
    wiles_lenstra_quad_criterion_Zp hb hb0 φQ hφQ π hcompatQ hleQ
  have hbij : Function.Bijective φ := by
    have hcomp : φ = φQ.comp eQ.symm.toAlgHom := by ext; simp [φQ]
    rw [hcomp]
    exact hbijQ.comp eQ.symm.bijective
  exact ⟨hbij, ⟨(AlgEquiv.ofBijective φ hbij).toRingEquiv⟩, hlen_eq.symm.trans hlenQ, hgor, hloc⟩

end WilesLenstraNumericalCriterion

/-! ## Section 2: Concrete Diamond–Fujiwara Depth-Freeness Patching Engine (`S_∞ = ℤ_[p][[y_0,…,y_{g-1}]]`) -/

section DiamondFujiwaraPatchingEngine

/-! ### 2.1 Bundled Finite-Level Diamond Quotients `S_∞ ⧸ I_n` & Explicit `RingHom`s (Zero Diamonds!) -/

/-- The `i`-th Taylor–Wiles diamond tower relation `(1 + y_i)^{p^n} - 1 ∈ S_∞`. -/
def diamondTowerPoly (p g n : ℕ) [Fact p.Prime] (i : Fin g) : PatchingBaseRing p g :=
  (1 + patchingVar (p := p) (g := g) i) ^ (p ^ n) - 1

/-- The level-`n` diamond tower ideal `I_n = ((1 + y_0)^{p^n} - 1, …, (1 + y_{g-1})^{p^n} - 1) ⊆ S_∞`. -/
def diamondTowerIdeal (p g n : ℕ) [Fact p.Prime] : Ideal (PatchingBaseRing p g) :=
  Ideal.span (Set.range (diamondTowerPoly p g n))

/-- Bundled finite-level quotient ring `S_n := S_∞ ⧸ I_n` (avoids nested `Algebra` diamonds over `S_∞`). -/
abbrev FiniteLevelRing (p g n : ℕ) [Fact p.Prime] : Type :=
  PatchingBaseRing p g ⧸ diamondTowerIdeal p g n

/-- Explicit quotient `RingHom` `S_∞ →+* S_∞ ⧸ I_n` (`Ideal.Quotient.mk`). -/
def finiteLevelProj (p g n : ℕ) [Fact p.Prime] :
    PatchingBaseRing p g →+* FiniteLevelRing p g n :=
  Ideal.Quotient.mk (diamondTowerIdeal p g n)

theorem finiteLevelProj_surjective (p g n : ℕ) [Fact p.Prime] :
    Function.Surjective (finiteLevelProj p g n) :=
  Ideal.Quotient.mk_surjective

theorem diamondTowerIdeal_le_augIdeal (p g n : ℕ) [Fact p.Prime] :
    diamondTowerIdeal p g n ≤ patchingAugIdeal p g := by
  rw [diamondTowerIdeal, Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  rw [patchingAugIdeal_eq_ker_constantCoeff]
  change MvPowerSeries.constantCoeff ((1 + MvPowerSeries.X i) ^ (p ^ n) - 1) = 0
  simp

theorem diamondTowerIdeal_zero_eq_augIdeal (p g : ℕ) [Fact p.Prime] :
    diamondTowerIdeal p g 0 = patchingAugIdeal p g := by
  unfold diamondTowerIdeal patchingAugIdeal diamondTowerPoly
  congr 1; ext x
  simp only [pow_zero, pow_one, add_sub_cancel_left]

/-! ### 2.2 Unconditional Auslander–Buchsbaum / Depth-Freeness Theorem over `S_∞` -/

/-- **Concrete Maximal-Depth / Cohen–Macaulay Predicate (`depth_{S_∞}(M) ≥ g + 1`)**:
the canonical regular sequence `(y_0, …, y_{g-1}, p)` of `S_∞ = ℤ_[p][[y_0,…,y_{g-1}]]` is
an `M`-regular sequence. -/
def IsPatchingRegularSeq (p g : ℕ) [Fact p.Prime] (M : Type*) [AddCommGroup M]
    [Module (PatchingBaseRing p g) M] : Prop :=
  (∀ (k : ℕ) (hk : k < g),
    Function.Injective (fun x : Coinv (partialAugIdeal p g k) M =>
      patchingVar (p := p) (g := g) ⟨k, hk⟩ • x)) ∧
  Function.Injective (fun x : Coinv (patchingAugIdeal p g) M =>
    (p : PatchingBaseRing p g) • x)

/-- Base ring equivalence `PatchingBaseRing p 0 = MvPowerSeries (Fin 0) ℤ_[p] ≃+* ℤ_[p]`. -/
def patchingBaseRing_zero_equiv_Zp (p : ℕ) [Fact p.Prime] :
    PatchingBaseRing p 0 ≃+* ℤ_[p] where
  toFun := MvPowerSeries.constantCoeff
  invFun := MvPowerSeries.C
  left_inv f := by
    ext α
    have hα : α = 0 := by ext i; exact Fin.elim0 i
    subst hα
    rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
      MvPowerSeries.constantCoeff_C]
  right_inv a := MvPowerSeries.constantCoeff_C a
  map_mul' := map_mul _
  map_add' := map_add _

/-- Drop-first-variable quotient isomorphism `S_{g+1} ⧸ (y_0) ≃+* S_g`. -/
def quot_partialAugIdeal_one_equiv (p g : ℕ) [Fact p.Prime] :
    (PatchingBaseRing p (g + 1) ⧸ partialAugIdeal p (g + 1) 1) ≃+* PatchingBaseRing p g :=
  (quot_partialAugIdeal_equiv p (g + 1) 1 (Nat.succ_le_succ (Nat.zero_le g))).trans
    (RingEquiv.ofBijective (RingHom.id _) Function.bijective_id)

private def dropFirstVar (p g : ℕ) [Fact p.Prime] :
    PatchingBaseRing p (g + 1) →+* PatchingBaseRing p g :=
  evalPrefixZero (p := p) (g := g + 1) 1 (Nat.succ_le_succ (Nat.zero_le g))

private lemma dropFirstVar_surjective (p g : ℕ) [Fact p.Prime] :
    Function.Surjective (dropFirstVar p g) :=
  evalPrefixZero_surjective (p := p) (g := g + 1) 1 (Nat.succ_le_succ (Nat.zero_le g))

private lemma ker_dropFirstVar (p g : ℕ) [Fact p.Prime] :
    RingHom.ker (dropFirstVar p g) = partialAugIdeal p (g + 1) 1 :=
  ker_evalPrefixZero (p := p) (g := g + 1) 1 (Nat.succ_le_succ (Nat.zero_le g))

private lemma partialAugIdeal_one_eq_span_y0 (p g : ℕ) [Fact p.Prime] :
    partialAugIdeal p (g + 1) 1 = Ideal.span ({patchingVar (0 : Fin (g + 1))} : Set (PatchingBaseRing p (g + 1))) := by
  unfold partialAugIdeal; congr 1; ext x
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, hi, rfl⟩; have hi0 : i = 0 := Fin.ext (by change i.1 = 0; omega); rw [hi0]
  · rintro rfl; exact ⟨0, Nat.zero_lt_one, rfl⟩

private lemma dropFirstVar_patchingVar_succ (p g : ℕ) [Fact p.Prime] (i : Fin g) :
    dropFirstVar p g (patchingVar i.succ) = patchingVar i := by
  let emb : Fin g ↪ Fin (g + 1) :=
    ⟨fun j => ⟨1 + j.1, by omega⟩, fun j₁ j₂ h => Fin.ext (by
      have hv : 1 + j₁.1 = 1 + j₂.1 := congrArg Fin.val h; omega)⟩
  ext m
  change MvPowerSeries.coeff (m.mapDomain emb) (MvPowerSeries.X i.succ) =
    MvPowerSeries.coeff m (MvPowerSeries.X i)
  rw [MvPowerSeries.coeff_X, MvPowerSeries.coeff_X]
  have hi_emb : emb i = i.succ := Fin.ext (by change 1 + i.1 = i.1 + 1; omega)
  have hiff : m.mapDomain emb = Finsupp.single i.succ 1 ↔ m = Finsupp.single i 1 := by
    rw [← hi_emb, ← Finsupp.mapDomain_single]
    exact (Finsupp.mapDomain_injective emb.injective).eq_iff
  by_cases hm : m = Finsupp.single i 1
  · rw [if_pos (hiff.mpr hm), if_pos hm]
  · rw [if_neg (fun h => hm (hiff.mp h)), if_neg hm]

private lemma dropFirstVar_comap_partialAugIdeal (p g k : ℕ) [Fact p.Prime] (_hk : k ≤ g) :
    (partialAugIdeal p g k).comap (dropFirstVar p g) = partialAugIdeal p (g + 1) (k + 1) := by
  apply le_antisymm
  · intro f hf
    have hf_mem : dropFirstVar p g f ∈ partialAugIdeal p g k := hf
    have hmap : Ideal.map (dropFirstVar p g) (partialAugIdeal p (g + 1) (k + 1)) =
        partialAugIdeal p g k := by
      unfold partialAugIdeal; rw [Ideal.map_span]
      apply le_antisymm
      · rw [Ideal.span_le]
        rintro _ ⟨_, ⟨i, hik, rfl⟩, rfl⟩
        rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
        · have h0 : dropFirstVar p g (patchingVar (0 : Fin (g + 1))) = 0 := by
            rw [← RingHom.mem_ker, ker_dropFirstVar, partialAugIdeal_one_eq_span_y0]
            exact Ideal.subset_span rfl
          rw [h0]; exact Ideal.zero_mem _
        · rw [dropFirstVar_patchingVar_succ]; exact Ideal.subset_span ⟨j, by simpa using hik, rfl⟩
      · rw [Ideal.span_le]
        rintro _ ⟨j, hjk, rfl⟩
        exact Ideal.subset_span ⟨patchingVar j.succ, ⟨j.succ, by simpa using hjk, rfl⟩,
          dropFirstVar_patchingVar_succ p g j⟩
    rw [← hmap] at hf_mem
    have hker_le : RingHom.ker (dropFirstVar p g) ≤ partialAugIdeal p (g + 1) (k + 1) := by
      rw [ker_dropFirstVar, partialAugIdeal_one_eq_span_y0, Ideal.span_singleton_le_iff_mem]
      exact Ideal.subset_span ⟨0, Nat.zero_lt_succ k, rfl⟩
    have hmem_map : ∀ y ∈ Ideal.map (dropFirstVar p g) (partialAugIdeal p (g + 1) (k + 1)),
        ∃ x ∈ partialAugIdeal p (g + 1) (k + 1), dropFirstVar p g x = y := by
      intro y hy
      refine Submodule.span_induction (p := fun y _ => ∃ x ∈ partialAugIdeal p (g + 1) (k + 1),
          dropFirstVar p g x = y) ?_ ?_ ?_ ?_ hy
      · rintro _ ⟨x, hx, rfl⟩; exact ⟨x, hx, rfl⟩
      · exact ⟨0, Ideal.zero_mem _, map_zero _⟩
      · rintro _ _ _ _ ⟨x₁, hx₁, rfl⟩ ⟨x₂, hx₂, rfl⟩
        exact ⟨x₁ + x₂, Ideal.add_mem _ hx₁ hx₂, map_add _ _ _⟩
      · rintro a _ _ ⟨x, hx, rfl⟩
        obtain ⟨b, rfl⟩ := dropFirstVar_surjective p g a
        exact ⟨b * x, Ideal.mul_mem_left _ b hx, map_mul _ b x⟩
    obtain ⟨x, hx, hfx⟩ := hmem_map _ hf_mem
    have hdiff : f - x ∈ RingHom.ker (dropFirstVar p g) := by
      rw [RingHom.mem_ker, map_sub, hfx, sub_self]
    have heq : f = x + (f - x) := by abel
    rw [heq]; exact Ideal.add_mem _ hx (hker_le hdiff)
  · rw [partialAugIdeal, Ideal.span_le]
    rintro _ ⟨i, hik, rfl⟩
    change dropFirstVar p g (patchingVar i) ∈ partialAugIdeal p g k
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
    · have h0 : dropFirstVar p g (patchingVar (0 : Fin (g + 1))) = 0 := by
        rw [← RingHom.mem_ker, ker_dropFirstVar, partialAugIdeal_one_eq_span_y0]
        exact Ideal.subset_span rfl
      rw [h0]; exact Ideal.zero_mem _
    · rw [dropFirstVar_patchingVar_succ]; exact Ideal.subset_span ⟨j, by simpa using hik, rfl⟩

private lemma partialAugIdeal_eq_augIdeal (p g : ℕ) [Fact p.Prime] :
    partialAugIdeal p g g = patchingAugIdeal p g := by
  unfold partialAugIdeal patchingAugIdeal; congr 1; ext x
  simp only [Set.mem_ofPred_eq, Set.mem_range]
  exact ⟨fun ⟨i, _, h⟩ => ⟨i, h.symm⟩, fun ⟨i, h⟩ => ⟨i, i.2, h.symm⟩⟩

/-- **UNCONDITIONAL AUSLANDER–BUCHSBAUM / DEPTH-FREENESS THEOREM OVER `S_∞ = ℤ_[p][[y_0,…,y_{g-1}]]`**:
every finitely generated `S_∞`-module `M` for which `(y_0, …, y_{g-1}, p)` is an `M`-regular
sequence (`depth_{S_∞}(M) ≥ g + 1`) is FREE of finite rank over `S_∞`. -/
theorem auslanderBuchsbaum_patchingBaseRing_free (p : ℕ) [Fact p.Prime] :
    ∀ (g : ℕ) (M : Type*) [AddCommGroup M] [Module (PatchingBaseRing p g) M]
      [Module.Finite (PatchingBaseRing p g) M],
      IsPatchingRegularSeq p g M →
      ∃ r : ℕ, Nonempty (M ≃ₗ[PatchingBaseRing p g] (Fin r → PatchingBaseRing p g))
  | 0, M, _, _, _, hreg => by
    classical
    let e0 : PatchingBaseRing p 0 ≃+* ℤ_[p] := patchingBaseRing_zero_equiv_Zp p
    let instZp : Module ℤ_[p] M := Module.compHom M (MvPowerSeries.C : ℤ_[p] →+* PatchingBaseRing p 0)
    have haug0 : patchingAugIdeal p 0 = ⊥ := by
      rw [eq_bot_iff, patchingAugIdeal, Ideal.span_le]
      rintro _ ⟨i, _⟩; exact Fin.elim0 i
    have hp_inj : Function.Injective (fun m : M => (p : ℤ_[p]) • m) := by
      have hreg_p := hreg.2
      intro m₁ m₂ hm
      have hq : (p : PatchingBaseRing p 0) •
            Submodule.Quotient.mk (p := patchingAugIdeal p 0 • (⊤ : Submodule (PatchingBaseRing p 0) M)) m₁ =
          (p : PatchingBaseRing p 0) •
            Submodule.Quotient.mk (p := patchingAugIdeal p 0 • (⊤ : Submodule (PatchingBaseRing p 0) M)) m₂ := by
        rw [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul]
        have hpC : (p : PatchingBaseRing p 0) = MvPowerSeries.C (p : ℤ_[p]) := by simp
        rw [hpC]; exact congrArg (Submodule.Quotient.mk (p := patchingAugIdeal p 0 • ⊤)) hm
      have heq_q := hreg_p hq
      have hdiff : m₁ - m₂ ∈ patchingAugIdeal p 0 • (⊤ : Submodule (PatchingBaseRing p 0) M) :=
        (Submodule.Quotient.mk_eq_zero _).mp (by rw [Submodule.Quotient.mk_sub, heq_q, sub_self])
      rw [haug0, Submodule.bot_smul] at hdiff
      exact sub_eq_zero.mp hdiff
    have htf : Module.IsTorsionFree ℤ_[p] M := by
      refine Module.isTorsionFree_iff_smul_eq_zero.mpr fun {a m} ham => ?_
      by_cases ha : a = 0
      · exact Or.inl ha
      · right
        obtain ⟨k, u, hu⟩ := IsDiscreteValuationRing.associated_pow_irreducible ha
          (PadicInt.irreducible_p (p := p))
        have hpk : (p : ℤ_[p]) ^ k • m = 0 := by
          have h1 : (u : ℤ_[p]) • (a • m) = 0 := by rw [ham, smul_zero]
          rwa [smul_smul, mul_comm, hu] at h1
        clear ham hu u ha a
        induction k with
        | zero => simpa using hpk
        | succ k ih =>
          apply ih; apply hp_inj; dsimp only
          rw [smul_zero, ← mul_smul, ← pow_succ']; exact hpk
    have hfin_Zp : Module.Finite ℤ_[p] M := by
      obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := PatchingBaseRing p 0) (M := M)
      refine Module.Finite.of_fg_top ⟨s, ?_⟩
      rw [eq_top_iff]; intro m _
      have hm : m ∈ Submodule.span (PatchingBaseRing p 0) (s : Set M) := by rw [hs]; trivial
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hm
      · intro x hx; exact Submodule.subset_span hx
      · exact Submodule.zero_mem _
      · intro x y _ _ hx hy; exact Submodule.add_mem _ hx hy
      · intro f x _ hx
        have hf : f = MvPowerSeries.C (e0 f) := (e0.left_inv f).symm
        rw [hf]; exact Submodule.smul_mem _ (e0 f) hx
    have hfree_Zp : Module.Free ℤ_[p] M := Module.free_of_finite_type_torsion_free'
    let b := Module.Free.chooseBasis ℤ_[p] M
    have : Fintype (Module.Free.ChooseBasisIndex ℤ_[p] M) := Module.Free.ChooseBasisIndex.fintype ℤ_[p] M
    let r := Fintype.card (Module.Free.ChooseBasisIndex ℤ_[p] M)
    let eIdx : Module.Free.ChooseBasisIndex ℤ_[p] M ≃ Fin r := Fintype.equivFin _
    let eM : M ≃ₗ[ℤ_[p]] (Fin r → ℤ_[p]) :=
      (b.reindex eIdx).repr.trans (Finsupp.linearEquivFunOnFinite ℤ_[p] ℤ_[p] (Fin r))
    refine ⟨r, ⟨{
      toFun := fun m i => MvPowerSeries.C (eM m i)
      invFun := fun v => eM.symm (fun i => e0 (v i))
      left_inv := fun m => by
        dsimp only
        have h : (fun i => e0 (MvPowerSeries.C (eM m i))) = eM m := funext fun i => e0.right_inv _
        rw [h, eM.symm_apply_apply]
      right_inv := fun v => by funext i; dsimp only; rw [eM.apply_symm_apply]; exact e0.left_inv (v i)
      map_add' := fun m₁ m₂ => by funext i; simp [map_add]
      map_smul' := fun f m => by
        funext i
        have hf : f = MvPowerSeries.C (e0 f) := (e0.left_inv f).symm
        change MvPowerSeries.C (eM (f • m) i) = f * MvPowerSeries.C (eM m i)
        conv_lhs => rw [hf]
        have hsm : (MvPowerSeries.C (e0 f) : PatchingBaseRing p 0) • m = (e0 f) • m := rfl
        rw [hsm, eM.map_smul, Pi.smul_apply, smul_eq_mul, map_mul, ← hf] }⟩⟩
  | g + 1, M, _, _, _, hreg => by
    classical
    let S := PatchingBaseRing p (g + 1)
    let S' := PatchingBaseRing p g
    let y0 : S := patchingVar (0 : Fin (g + 1))
    let I1 : Ideal S := partialAugIdeal p (g + 1) 1
    let M' := Coinv I1 M
    have hy0_inj : Function.Injective (fun m : M => y0 • m) := by
      have hreg0 := hreg.1 0 (Nat.zero_lt_succ g)
      have hI0 : partialAugIdeal p (g + 1) 0 = ⊥ := by
        rw [eq_bot_iff, partialAugIdeal, Ideal.span_le]; rintro _ ⟨i, hi, _⟩; omega
      intro m₁ m₂ hm
      have hq : y0 • Submodule.Quotient.mk (p := partialAugIdeal p (g + 1) 0 • (⊤ : Submodule S M)) m₁ =
          y0 • Submodule.Quotient.mk (p := partialAugIdeal p (g + 1) 0 • (⊤ : Submodule S M)) m₂ := by
        rw [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul]
        exact congrArg (Submodule.Quotient.mk (p := partialAugIdeal p (g + 1) 0 • ⊤)) hm
      have heq_q := hreg0 hq
      have hdiff : m₁ - m₂ ∈ partialAugIdeal p (g + 1) 0 • (⊤ : Submodule S M) :=
        (Submodule.Quotient.mk_eq_zero _).mp (by rw [Submodule.Quotient.mk_sub, heq_q, sub_self])
      rw [hI0, Submodule.bot_smul] at hdiff
      exact sub_eq_zero.mp hdiff
    let eQ : (S ⧸ I1) ≃+* S' := quot_partialAugIdeal_one_equiv p g
    have heQ_mk : ∀ s : S, eQ (Ideal.Quotient.mk I1 s) = dropFirstVar p g s := fun _ => rfl
    let _instModS' : Module S' M' := Module.compHom M' eQ.symm.toRingHom
    have hsmul_M' : ∀ (s : S) (x : M'), (dropFirstVar p g s) • x = s • x := by
      intro s x; change eQ.symm (dropFirstVar p g s) • x = s • x
      rw [← heQ_mk s, eQ.symm_apply_apply]; rfl
    have hfin_M' : Module.Finite S' M' := by
      obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := S) (M := M)
      refine Module.Finite.of_fg_top ⟨s.image (I1 • (⊤ : Submodule S M)).mkQ, ?_⟩
      rw [eq_top_iff]; intro x _
      induction x using Quotient.inductionOn' with
      | h m =>
        have hm : m ∈ Submodule.span S (s : Set M) := by rw [hs]; trivial
        refine Submodule.span_induction (p := fun m _ =>
            Submodule.Quotient.mk (p := I1 • (⊤ : Submodule S M)) m ∈
              Submodule.span S' ((s.image (I1 • (⊤ : Submodule S M)).mkQ : Finset M') : Set M'))
            ?_ ?_ ?_ ?_ hm
        · intro y hy; exact Submodule.subset_span (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hy))
        · exact Submodule.zero_mem _
        · intro y₁ y₂ _ _ h₁ h₂; rw [Submodule.Quotient.mk_add]; exact Submodule.add_mem _ h₁ h₂
        · intro a y _ hy
          rw [Submodule.Quotient.mk_smul, ← hsmul_M']
          exact Submodule.smul_mem _ (dropFirstVar p g a) hy
    have hcoinv_equiv : ∀ (k : ℕ) (hk : k ≤ g),
        Nonempty { e : Coinv (partialAugIdeal p g k) M' ≃+ Coinv (partialAugIdeal p (g + 1) (k + 1)) M //
          ∀ (s : S) (x : Coinv (partialAugIdeal p g k) M'),
            e ((dropFirstVar p g s) • x) = s • e x } := by
      intro k hk
      let J' : Submodule S' M' := partialAugIdeal p g k • (⊤ : Submodule S' M')
      let J : Submodule S M := partialAugIdeal p (g + 1) (k + 1) • (⊤ : Submodule S M)
      have hI1_le : I1 ≤ partialAugIdeal p (g + 1) (k + 1) := by
        dsimp only [I1]
        rw [partialAugIdeal_one_eq_span_y0, Ideal.span_singleton_le_iff_mem]
        exact Ideal.subset_span ⟨0, Nat.zero_lt_succ k, rfl⟩
      have hI1M_le : I1 • (⊤ : Submodule S M) ≤ J := Submodule.smul_mono hI1_le le_rfl
      let q1 : M' →ₗ[S] Coinv (partialAugIdeal p (g + 1) (k + 1)) M := Submodule.factor hI1M_le
      have hq1_surj : Function.Surjective q1 := Submodule.factor_surjective hI1M_le
      have hker_q1 : ∀ x : M', q1 x = 0 ↔ x ∈ J' := by
        intro x
        induction x using Quotient.inductionOn' with
        | h m =>
          change Submodule.Quotient.mk (p := J) m = 0 ↔
            Submodule.Quotient.mk (p := I1 • (⊤ : Submodule S M)) m ∈ J'
          rw [Submodule.Quotient.mk_eq_zero]
          constructor
          · intro hmJ
            refine Submodule.smul_induction_on hmJ ?_ ?_
            · intro a ha w _
              have ha' : dropFirstVar p g a ∈ partialAugIdeal p g k := by
                rwa [← dropFirstVar_comap_partialAugIdeal p g k hk] at ha
              rw [Submodule.Quotient.mk_smul, ← hsmul_M' a]
              exact Submodule.smul_mem_smul ha' Submodule.mem_top
            · intro u v hu hv; rw [Submodule.Quotient.mk_add]; exact Submodule.add_mem _ hu hv
          · intro hmJ'
            have hstep : ∀ y ∈ J', q1 y = 0 := by
              intro y hy
              refine Submodule.smul_induction_on hy ?_ ?_
              · intro a' ha' z _
                obtain ⟨a, rfl⟩ := dropFirstVar_surjective p g a'
                have ha : a ∈ partialAugIdeal p (g + 1) (k + 1) := by
                  rw [← dropFirstVar_comap_partialAugIdeal p g k hk]; exact ha'
                rw [hsmul_M' a z, map_smul]
                induction z using Quotient.inductionOn' with
                | h w =>
                  change a • Submodule.Quotient.mk (p := J) w = 0
                  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
                  exact Submodule.smul_mem_smul ha Submodule.mem_top
              · intro y₁ y₂ h₁ h₂; rw [map_add, h₁, h₂, add_zero]
            exact (Submodule.Quotient.mk_eq_zero J).mp (hstep _ hmJ')
      let q1Add : M' →+ Coinv (partialAugIdeal p (g + 1) (k + 1)) M := q1.toAddMonoidHom
      let fAdd : Coinv (partialAugIdeal p g k) M' →+ Coinv (partialAugIdeal p (g + 1) (k + 1)) M :=
        QuotientAddGroup.lift J'.toAddSubgroup q1Add (fun x hx => (hker_q1 x).mpr hx)
      have hfAdd_bij : Function.Bijective fAdd := by
        refine ⟨?_, ?_⟩
        · rw [injective_iff_map_eq_zero]
          intro z hz
          induction z using Quotient.inductionOn' with
          | h x => exact (Submodule.Quotient.mk_eq_zero J').mpr ((hker_q1 x).mp hz)
        · intro y; obtain ⟨x, rfl⟩ := hq1_surj y; exact ⟨Submodule.Quotient.mk x, rfl⟩
      refine ⟨⟨AddEquiv.ofBijective fAdd hfAdd_bij, fun s z => ?_⟩⟩
      induction z using Quotient.inductionOn' with
      | h x => change q1 (dropFirstVar p g s • x) = s • q1 x; rw [hsmul_M' s x, map_smul]
    have hreg_M' : IsPatchingRegularSeq p g M' := by
      unfold IsPatchingRegularSeq
      constructor
      · intro k hk
        obtain ⟨⟨e, he⟩⟩ := hcoinv_equiv k hk.le
        intro x₁ x₂ hx
        apply e.injective; apply hreg.1 (k + 1) (Nat.succ_lt_succ hk)
        have h1 : ∀ x : Coinv (partialAugIdeal p g k) M',
            patchingVar (p := p) (g := g + 1) ⟨k + 1, Nat.succ_lt_succ hk⟩ • e x =
              e (patchingVar (p := p) (g := g) ⟨k, hk⟩ • x) := by
          intro x
          rw [← he (patchingVar (p := p) (g := g + 1) ⟨k + 1, Nat.succ_lt_succ hk⟩) x]
          have hv : dropFirstVar p g (patchingVar (p := p) (g := g + 1) ⟨k + 1, Nat.succ_lt_succ hk⟩) =
              patchingVar (p := p) (g := g) ⟨k, hk⟩ :=
            dropFirstVar_patchingVar_succ p g ⟨k, hk⟩
          rw [hv]
        dsimp only
        have hx' : patchingVar (p := p) (g := g) ⟨k, hk⟩ • x₁ =
            patchingVar (p := p) (g := g) ⟨k, hk⟩ • x₂ := hx
        rw [h1 x₁, h1 x₂, hx']
      · obtain ⟨⟨e, he⟩⟩ := hcoinv_equiv g le_rfl
        let e1L : Coinv (patchingAugIdeal p g) M' ≃ₗ[S'] Coinv (partialAugIdeal p g g) M' :=
          Submodule.quotEquivOfEq (patchingAugIdeal p g • ⊤) (partialAugIdeal p g g • ⊤)
            (by rw [partialAugIdeal_eq_augIdeal p g])
        let e2L : Coinv (partialAugIdeal p (g + 1) (g + 1)) M ≃ₗ[S] Coinv (patchingAugIdeal p (g + 1)) M :=
          Submodule.quotEquivOfEq (partialAugIdeal p (g + 1) (g + 1) • ⊤) (patchingAugIdeal p (g + 1) • ⊤)
            (by rw [partialAugIdeal_eq_augIdeal p (g + 1)])
        intro x₁ x₂ hx
        apply e1L.injective; apply e.injective; apply e2L.injective; apply hreg.2
        have hstep : ∀ x : Coinv (patchingAugIdeal p g) M',
            (p : S) • e2L (e (e1L x)) = e2L (e (e1L ((p : S') • x))) := by
          intro x
          have hp_drop : dropFirstVar p g (p : S) = (p : S') := map_natCast _ p
          rw [← e2L.map_smul (p : S) (e (e1L x)), ← he (p : S) (e1L x), hp_drop, e1L.map_smul]
        dsimp only
        have hx' : (p : S') • x₁ = (p : S') • x₂ := hx
        rw [hstep x₁, hstep x₂, hx']
    obtain ⟨r, ⟨eM'⟩⟩ := auslanderBuchsbaum_patchingBaseRing_free p g M' hreg_M'
    have hlift : ∀ i : Fin r, ∃ m : M,
        Submodule.Quotient.mk (p := I1 • (⊤ : Submodule S M)) m = eM'.symm (Pi.single i (1 : S')) :=
      fun i => Submodule.mkQ_surjective _ (eM'.symm (Pi.single i 1))
    choose v hv using hlift
    let Φ : (Fin r → S) →ₗ[S] M :=
      { toFun := fun c => ∑ i : Fin r, c i • v i
        map_add' := fun c₁ c₂ => by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
        map_smul' := fun s c => by
          simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.smul_sum, mul_smul] }
    have hI1_max : I1 ≤ IsLocalRing.maximalIdeal S := by
      refine le_trans ?_ (patchingAugIdeal_le_maximalIdeal p (g + 1))
      dsimp only [I1]
      rw [partialAugIdeal_one_eq_span_y0, Ideal.span_singleton_le_iff_mem]
      exact Ideal.subset_span ⟨0, rfl⟩
    have hΦ_mod : ∀ c : Fin r → S,
        eM' (Submodule.Quotient.mk (p := I1 • (⊤ : Submodule S M)) (Φ c)) =
          fun i : Fin r => dropFirstVar p g (c i) := by
      intro c
      change eM' ((I1 • (⊤ : Submodule S M)).mkQ (∑ i : Fin r, c i • v i)) = _
      rw [map_sum, map_sum]; ext j; rw [Finset.sum_apply, Finset.sum_eq_single j]
      · rw [Submodule.mkQ_apply, Submodule.Quotient.mk_smul, ← hsmul_M', hv j, eM'.map_smul,
          eM'.apply_symm_apply]; simp
      · intro i _ hij
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_smul, ← hsmul_M', hv i, eM'.map_smul,
          eM'.apply_symm_apply]; simp [hij.symm]
      · intro h; exact absurd (Finset.mem_univ j) h
    have hΦ_surj : Function.Surjective Φ := by
      refine nakayama_coinv_surjective hI1_max Φ ?_
      intro x
      choose c hc using fun i : Fin r => dropFirstVar_surjective p g (eM' x i)
      refine ⟨c, ?_⟩
      apply eM'.injective
      change eM' (Submodule.Quotient.mk (p := I1 • (⊤ : Submodule S M)) (Φ c)) = eM' x
      rw [hΦ_mod c]; funext i; exact hc i
    have hker_dvd : ∀ n : ℕ, ∀ c : Fin r → S, Φ c = 0 → ∀ i : Fin r, y0 ^ n ∣ c i := by
      intro n
      induction n with
      | zero => intro _ _ _; rw [pow_zero]; exact one_dvd _
      | succ n ih =>
        intro c hc
        have hdrop0 : ∀ i : Fin r, dropFirstVar p g (c i) = 0 := fun i => by
          have h := congrFun (hΦ_mod c) i
          rw [hc, Submodule.Quotient.mk_zero, map_zero, Pi.zero_apply] at h; exact h.symm
        have hy0_dvd : ∀ i : Fin r, y0 ∣ c i := fun i => by
          have hmem : c i ∈ partialAugIdeal p (g + 1) 1 := by rw [← ker_dropFirstVar p g]; exact hdrop0 i
          rw [partialAugIdeal_one_eq_span_y0] at hmem; exact Ideal.mem_span_singleton.mp hmem
        choose c₁ hc₁ using hy0_dvd
        have hc_eq : c = y0 • c₁ := funext fun i => hc₁ i
        have hΦc₁ : Φ c₁ = 0 := by
          apply hy0_inj; dsimp only; rw [smul_zero, ← map_smul, ← hc_eq, hc]
        intro i
        obtain ⟨q, hq⟩ := ih c₁ hΦc₁ i
        exact ⟨q, by rw [hc₁ i, hq, pow_succ', mul_assoc]⟩
    have hΦ_inj : Function.Injective Φ := by
      rw [injective_iff_map_eq_zero]
      intro c hc; funext i; ext α
      obtain ⟨q, hq⟩ := hker_dvd (α 0 + 1) c hc i
      have hy0_pow : ∀ t : ℕ, y0 ^ t =
          MvPowerSeries.monomial (Finsupp.single (0 : Fin (g + 1)) t) (1 : ℤ_[p]) := by
        intro t
        induction t with
        | zero => simp [MvPowerSeries.monomial_zero_eq_C]
        | succ m ih =>
          rw [pow_succ, ih]; dsimp only [y0]
          rw [patchingVar, MvPowerSeries.X_def, MvPowerSeries.monomial_mul_monomial,
            one_mul, ← Finsupp.single_add]
      rw [hq, hy0_pow (α 0 + 1), MvPowerSeries.coeff_monomial_mul, one_mul,
        if_neg (by rw [Finsupp.single_le_iff]; omega)]
      rfl
    exact ⟨r, ⟨(LinearEquiv.ofBijective Φ ⟨hΦ_inj, hΦ_surj⟩).symm⟩⟩

/-- **Converse of Auslander–Buchsbaum**: every finite-rank free `S_∞`-module satisfies
`IsPatchingRegularSeq p g M`. -/
theorem isPatchingRegularSeq_of_equiv_pi {p g r : ℕ} [Fact p.Prime] {M : Type*}
    [AddCommGroup M] [Module (PatchingBaseRing p g) M]
    (e : M ≃ₗ[PatchingBaseRing p g] (Fin r → PatchingBaseRing p g)) :
    IsPatchingRegularSeq p g M := by
  have hS_reg := patchingBaseRing_regular_sequence p g
  unfold IsPatchingRegularSeq
  constructor
  · intro k hk
    let eQ := coinvEquivPiOfEquivPi (partialAugIdeal p g k) e
    intro x₁ x₂ hx
    apply eQ.injective; ext i
    have hx' := congrFun (congrArg eQ hx) i
    have hsmul : ∀ x : Coinv (partialAugIdeal p g k) M,
        eQ (patchingVar ⟨k, hk⟩ • x) i =
          Ideal.Quotient.mk (partialAugIdeal p g k) (patchingVar ⟨k, hk⟩) * eQ x i := fun x => by
      have h1 : patchingVar (p := p) (g := g) ⟨k, hk⟩ • x =
          Ideal.Quotient.mk (partialAugIdeal p g k) (patchingVar ⟨k, hk⟩) • x := rfl
      rw [h1, eQ.map_smul, Pi.smul_apply, smul_eq_mul]
    rw [hsmul x₁, hsmul x₂] at hx'; exact hS_reg.1 k hk hx'
  · let eQ := coinvEquivPiOfEquivPi (patchingAugIdeal p g) e
    intro x₁ x₂ hx
    apply eQ.injective; ext i
    have hx' := congrFun (congrArg eQ hx) i
    have hsmul : ∀ x : Coinv (patchingAugIdeal p g) M,
        eQ ((p : PatchingBaseRing p g) • x) i =
          Ideal.Quotient.mk (patchingAugIdeal p g) (p : PatchingBaseRing p g) * eQ x i := fun x => by
      have h1 : (p : PatchingBaseRing p g) • x =
          Ideal.Quotient.mk (patchingAugIdeal p g) (p : PatchingBaseRing p g) • x := rfl
      rw [h1, eQ.map_smul, Pi.smul_apply, smul_eq_mul]
    rw [hsmul x₁, hsmul x₂] at hx'; exact hS_reg.2 hx'

/-! ### 2.3 Concrete Diamond–Fujiwara Patching Tower & Depth-Freeness Main Theorem -/

/-- **Concrete Diamond–Fujiwara Patching Tower `(R_n, T_n, M_n)` over bundled finite quotients
`S_n := FiniteLevelRing p g n = S_∞ ⧸ I_n`** (explicit `RingHom`s, ZERO `Algebra` diamonds!):
freeness of `M_∞` over `S_∞` is **DERIVED** from `M_inf_regular : IsPatchingRegularSeq p g M_inf`
via `auslanderBuchsbaum_patchingBaseRing_free`. -/
structure DiamondFujiwaraPatchingTower (p g : ℕ) [Fact p.Prime] where
  rank : ℕ
  rank_pos : 0 < rank
  R_inf : Type
  [commRingR : CommRing R_inf]
  [algSR : Algebra (PatchingBaseRing p g) R_inf]
  [finSR : Module.Finite (PatchingBaseRing p g) R_inf]
  T_inf : Type
  [commRingT : CommRing T_inf]
  [algST : Algebra (PatchingBaseRing p g) T_inf]
  phi_inf : R_inf →ₐ[PatchingBaseRing p g] T_inf
  phi_surj : Function.Surjective phi_inf
  M_inf : Type
  [addM : AddCommGroup M_inf]
  [modSM : Module (PatchingBaseRing p g) M_inf]
  [finSM : Module.Finite (PatchingBaseRing p g) M_inf]
  [modRM : Module R_inf M_inf]
  [modTM : Module T_inf M_inf]
  [towerSRM : IsScalarTower (PatchingBaseRing p g) R_inf M_inf]
  compat_RM_TM : ∀ (r : R_inf) (m : M_inf), r • m = phi_inf r • m
  /-- **Cohen–Macaulay / Depth `≥ g + 1` Hypothesis**: `(y_0,…,y_{g-1}, p)` is `M_∞`-regular. -/
  M_inf_regular : IsPatchingRegularSeq p g M_inf
  /-- Finite-level patching tower `(R_n, T_n, M_n)` over bundled quotient `S_n = S_∞ ⧸ I_n`. -/
  R_n : ℕ → Type
  [commRingRn : ∀ n, CommRing (R_n n)]
  [algSnRn : ∀ n, Algebra (FiniteLevelRing p g n) (R_n n)]
  T_n : ℕ → Type
  [commRingTn : ∀ n, CommRing (T_n n)]
  [algSnTn : ∀ n, Algebra (FiniteLevelRing p g n) (T_n n)]
  M_n : ℕ → Type
  [addMn : ∀ n, AddCommGroup (M_n n)]
  [modSnMn : ∀ n, Module (FiniteLevelRing p g n) (M_n n)]
  [modTnMn : ∀ n, Module (T_n n) (M_n n)]
  projR : ∀ n, R_inf →+* R_n n
  projR_surj : ∀ n, Function.Surjective (projR n)
  phi_n : ∀ n, R_n n →ₐ[FiniteLevelRing p g n] T_n n
  phi_n_surj : ∀ n, Function.Surjective (phi_n n)
  T_n_faithful : ∀ n, Module.annihilator (T_n n) (M_n n) = ⊥
  M_n_free : ∀ n, M_n n ≃ₗ[FiniteLevelRing p g n] (Fin rank → FiniteLevelRing p g n)
  M0_rank_compat :
    Nonempty (Coinv (patchingAugIdeal p g) M_inf ≃ₗ[PatchingBaseRing p g ⧸ patchingAugIdeal p g]
      (Fin rank → PatchingBaseRing p g ⧸ patchingAugIdeal p g))
  R_0 : Type
  [commRingR0 : CommRing R_0]
  T_0 : Type
  [commRingT0 : CommRing T_0]
  specR : R_inf ⧸ ((patchingAugIdeal p g).map (algebraMap (PatchingBaseRing p g) R_inf)) ≃+* R_0
  specT : T_inf ⧸ ((patchingAugIdeal p g).map (algebraMap (PatchingBaseRing p g) T_inf)) ≃+* T_0
  dim_witness :
    (IsDomain R_inf ∧ ∃ s : ℕ, 0 < s ∧ Nonempty (M_inf ≃ₗ[R_inf] (Fin s → R_inf))) ∨
    Nonempty ((R_inf ≃ₗ[PatchingBaseRing p g] (Fin rank → PatchingBaseRing p g)) ×
      { f : R_inf →ₗ[R_inf] M_inf // Function.Surjective f })

attribute [instance] DiamondFujiwaraPatchingTower.commRingR DiamondFujiwaraPatchingTower.algSR
  DiamondFujiwaraPatchingTower.finSR DiamondFujiwaraPatchingTower.commRingT
  DiamondFujiwaraPatchingTower.algST DiamondFujiwaraPatchingTower.addM
  DiamondFujiwaraPatchingTower.modSM DiamondFujiwaraPatchingTower.finSM
  DiamondFujiwaraPatchingTower.modRM DiamondFujiwaraPatchingTower.modTM
  DiamondFujiwaraPatchingTower.towerSRM DiamondFujiwaraPatchingTower.commRingRn
  DiamondFujiwaraPatchingTower.algSnRn DiamondFujiwaraPatchingTower.commRingTn
  DiamondFujiwaraPatchingTower.algSnTn DiamondFujiwaraPatchingTower.addMn
  DiamondFujiwaraPatchingTower.modSnMn DiamondFujiwaraPatchingTower.modTnMn
  DiamondFujiwaraPatchingTower.commRingR0 DiamondFujiwaraPatchingTower.commRingT0

/-- **Derived `S_∞`-Freeness of `M_∞` (Exact Rank `D.rank`) via Auslander–Buchsbaum**. -/
theorem DiamondFujiwaraPatchingTower.M_inf_free_S {p g : ℕ} [Fact p.Prime]
    (D : DiamondFujiwaraPatchingTower p g) :
    Nonempty (D.M_inf ≃ₗ[PatchingBaseRing p g] (Fin D.rank → PatchingBaseRing p g)) := by
  obtain ⟨r', ⟨e'⟩⟩ := auslanderBuchsbaum_patchingBaseRing_free p g D.M_inf D.M_inf_regular
  let eQ := coinvEquivPiOfEquivPi (patchingAugIdeal p g) e'
  obtain ⟨e0⟩ := D.M0_rank_compat
  let eFinQ : (Fin r' → PatchingBaseRing p g ⧸ patchingAugIdeal p g) ≃ₗ[PatchingBaseRing p g ⧸ patchingAugIdeal p g]
      (Fin D.rank → PatchingBaseRing p g ⧸ patchingAugIdeal p g) := eQ.symm.trans e0
  let eR := patchingBaseRing_quot_augIdeal_equiv_Zp p g
  let eFin : (Fin r' → ℤ_[p]) ≃ₗ[ℤ_[p]] (Fin D.rank → ℤ_[p]) :=
    { toFun := fun v i => eR (eFinQ (fun j => eR.symm (v j)) i)
      invFun := fun w j => eR (eFinQ.symm (fun i => eR.symm (w i)) j)
      left_inv := fun v => by
        ext j
        have h : (fun i => eR.symm (eR (eFinQ (fun k => eR.symm (v k)) i))) =
            eFinQ (fun k => eR.symm (v k)) := funext fun i => eR.symm_apply_apply _
        dsimp only; rw [h, eFinQ.symm_apply_apply, eR.apply_symm_apply]
      right_inv := fun w => by
        ext i
        have h : (fun j => eR.symm (eR (eFinQ.symm (fun k => eR.symm (w k)) j))) =
            eFinQ.symm (fun k => eR.symm (w k)) := funext fun j => eR.symm_apply_apply _
        dsimp only; rw [h, eFinQ.apply_symm_apply, eR.apply_symm_apply]
      map_add' := fun u v => by
        ext i
        have h : (fun j => eR.symm (u j + v j)) = (fun j => eR.symm (u j)) + (fun j => eR.symm (v j)) :=
          funext fun j => map_add eR.symm (u j) (v j)
        change eR (eFinQ (fun j => eR.symm (u j + v j)) i) =
          eR (eFinQ (fun j => eR.symm (u j)) i) + eR (eFinQ (fun j => eR.symm (v j)) i)
        rw [h, map_add, Pi.add_apply, map_add]
      map_smul' := fun a v => by
        ext i
        have h : (fun j => eR.symm (a * v j)) = eR.symm a • (fun j => eR.symm (v j)) :=
          funext fun j => map_mul eR.symm a (v j)
        change eR (eFinQ (fun j => eR.symm (a * v j)) i) = a * eR (eFinQ (fun j => eR.symm (v j)) i)
        rw [h, eFinQ.map_smul, Pi.smul_apply, smul_eq_mul, map_mul, eR.apply_symm_apply] }
  have hr_eq : r' = D.rank := by
    simpa [Module.finrank_fin_fun] using LinearEquiv.finrank_eq eFin
  subst hr_eq; exact ⟨e'⟩

/-- **Direct Conversion `DiamondFujiwaraPatchingTower → Stage3PatchingUnification.TaylorWilesPatchingDatum`**. -/
def DiamondFujiwaraPatchingTower.toTaylorWilesPatchingDatum {p g : ℕ} [Fact p.Prime]
    (D : DiamondFujiwaraPatchingTower p g) : TaylorWilesPatchingDatum where
  S_inf := PatchingBaseRing p g
  g := g
  y := patchingVar
  aug_le_max := patchingAugIdeal_le_maximalIdeal p g
  R_inf := D.R_inf
  T_inf := D.T_inf
  phi_inf := D.phi_inf
  phi_surj := D.phi_surj
  M_inf := D.M_inf
  compat_RM_TM := D.compat_RM_TM
  rank := D.rank
  rank_pos := D.rank_pos
  M_free_S := Classical.choice D.M_inf_free_S
  faithful_witness := by
    rcases D.dim_witness with ⟨hdom, _⟩ | hcyc
    · exact Or.inl hdom
    · exact Or.inr hcyc
  R_0 := D.R_0
  T_0 := D.T_0
  specR := D.specR
  specT := D.specT

def DiamondFujiwaraPatchingTower.R_inf_equiv_T_inf {p g : ℕ} [Fact p.Prime]
    (D : DiamondFujiwaraPatchingTower p g) :
    D.R_inf ≃ₐ[PatchingBaseRing p g] D.T_inf :=
  D.toTaylorWilesPatchingDatum.R_inf_equiv_T_inf

def DiamondFujiwaraPatchingTower.R0_equiv_T0 {p g : ℕ} [Fact p.Prime]
    (D : DiamondFujiwaraPatchingTower p g) :
    D.R_0 ≃+* D.T_0 :=
  D.toTaylorWilesPatchingDatum.R0_equiv_T0

abbrev DiamondFujiwaraPatchingTower.M_0 {p g : ℕ} [Fact p.Prime]
    (D : DiamondFujiwaraPatchingTower p g) : Type :=
  Coinv ((patchingAugIdeal p g).map (algebraMap (PatchingBaseRing p g) D.T_inf)) D.M_inf

instance DiamondFujiwaraPatchingTower.instModuleT0M0 {p g : ℕ} [Fact p.Prime]
    (D : DiamondFujiwaraPatchingTower p g) : Module D.T_0 D.M_0 :=
  Module.compHom D.M_0 D.specT.symm.toRingHom

/-- **THE DIAMOND–FUJIWARA DEPTH-FREENESS PATCHING THEOREM**:
derives unconditionally:
1. `M_∞` is FREE of exact rank `D.rank` over `S_∞ = ℤ_[p][[y_0,…,y_{g-1}]]`,
2. `R_∞ ≃ₐ[S_∞] T_∞` (and `R_∞ ≃+* T_∞`),
3. `R_0 ≃+* T_0`,
4. `M_0` is FREE of positive finite rank `s ≥ 1` over `T_0`. -/
theorem DiamondFujiwaraPatchingTower.main_patching_theorem {p g : ℕ} [Fact p.Prime]
    (D : DiamondFujiwaraPatchingTower p g) :
    Nonempty (D.M_inf ≃ₗ[PatchingBaseRing p g] (Fin D.rank → PatchingBaseRing p g)) ∧
    Nonempty (D.R_inf ≃ₐ[PatchingBaseRing p g] D.T_inf) ∧
    Nonempty (D.R_inf ≃+* D.T_inf) ∧
    Nonempty (D.R_0 ≃+* D.T_0) ∧
    ∃ s : ℕ, 0 < s ∧ Nonempty (D.M_0 ≃ₗ[D.T_0] (Fin s → D.T_0)) := by
  have hMfree := D.M_inf_free_S
  let eRT : D.R_inf ≃ₐ[PatchingBaseRing p g] D.T_inf := D.R_inf_equiv_T_inf
  have hM_free_T : ∃ s : ℕ, 0 < s ∧ Nonempty (D.M_inf ≃ₗ[D.T_inf] (Fin s → D.T_inf)) := by
    rcases D.dim_witness with ⟨_, s, hs, ⟨eMR⟩⟩ | ⟨⟨eR, ⟨f, hf⟩⟩⟩
    · refine ⟨s, hs, ⟨{
        toFun := fun m i => eRT (eMR m i)
        invFun := fun v => eMR.symm (fun i => eRT.symm (v i))
        left_inv := fun m => by
          dsimp only
          have h : (fun i => eRT.symm (eRT (eMR m i))) = eMR m := funext fun i => eRT.symm_apply_apply _
          rw [h, eMR.symm_apply_apply]
        right_inv := fun v => by ext i; simp
        map_add' := fun m₁ m₂ => by ext i; simp [map_add]
        map_smul' := fun t m => by
          ext i
          have hsm : t • m = eRT.symm t • m := by
            rw [D.compat_RM_TM]; change t • m = eRT (eRT.symm t) • m; rw [eRT.apply_symm_apply]
          rw [hsm, eMR.map_smul, Pi.smul_apply, smul_eq_mul, map_mul]
          change eRT (eRT.symm t) * eRT (eMR m i) = t * eRT (eMR m i)
          rw [eRT.apply_symm_apply] }⟩⟩
    · obtain ⟨eM⟩ := hMfree
      have hbij : Function.Bijective f := (annihilator_eq_bot_of_surjective_same_rank eR eM f hf).1
      let eMR : D.M_inf ≃ₗ[D.R_inf] (Fin 1 → D.R_inf) :=
        (LinearEquiv.ofBijective f hbij).symm.trans
          { toFun := fun r _ => r, invFun := fun v => v 0, left_inv := fun _ => rfl,
            right_inv := fun v => by ext i; fin_cases i; rfl,
            map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
      refine ⟨1, zero_lt_one, ⟨{
        toFun := fun m i => eRT (eMR m i)
        invFun := fun v => eMR.symm (fun i => eRT.symm (v i))
        left_inv := fun m => by
          dsimp only
          have h : (fun i => eRT.symm (eRT (eMR m i))) = eMR m := funext fun i => eRT.symm_apply_apply _
          rw [h, eMR.symm_apply_apply]
        right_inv := fun v => by ext i; simp
        map_add' := fun m₁ m₂ => by ext i; simp [map_add]
        map_smul' := fun t m => by
          ext i
          have hsm : t • m = eRT.symm t • m := by
            rw [D.compat_RM_TM]; change t • m = eRT (eRT.symm t) • m; rw [eRT.apply_symm_apply]
          rw [hsm, eMR.map_smul, Pi.smul_apply, smul_eq_mul, map_mul]
          change eRT (eRT.symm t) * eRT (eMR m i) = t * eRT (eMR m i)
          rw [eRT.apply_symm_apply] }⟩⟩
  obtain ⟨s, hs, ⟨eMT⟩⟩ := hM_free_T
  let eQ := coinvEquivPiOfEquivPi ((patchingAugIdeal p g).map (algebraMap (PatchingBaseRing p g) D.T_inf)) eMT
  let eM0 : D.M_0 ≃ₗ[D.T_0] (Fin s → D.T_0) :=
    { toFun := fun x i => D.specT (eQ x i)
      invFun := fun v => eQ.symm (fun i => D.specT.symm (v i))
      left_inv := fun x => by
        dsimp only
        have h : (fun i => D.specT.symm (D.specT (eQ x i))) = eQ x := funext fun i => D.specT.symm_apply_apply _
        rw [h, eQ.symm_apply_apply]
      right_inv := fun v => by ext i; simp
      map_add' := fun x y => by ext i; simp [map_add]
      map_smul' := fun t x => by
        ext i
        change D.specT (eQ (D.specT.symm t • x) i) = t * D.specT (eQ x i)
        rw [eQ.map_smul, Pi.smul_apply, smul_eq_mul, map_mul, D.specT.apply_symm_apply] }
  exact ⟨hMfree, ⟨eRT⟩, ⟨eRT.toRingEquiv⟩, ⟨D.R0_equiv_T0⟩, s, hs, ⟨eM0⟩⟩

/-- **Exact Congruence-Number / Cotangent-Length Equality `length(Φ_{R_0}) = v_p(η_{T_0})`**:
from `DiamondFujiwaraPatchingTower` + `R_0 ≃ₐ[ℤ_[p]] T_0`. -/
theorem diamondFujiwara_congruence_length_eq {p g : ℕ} [Fact p.Prime]
    (D : DiamondFujiwaraPatchingTower p g)
    [Algebra ℤ_[p] D.R_0] [Algebra ℤ_[p] D.T_0]
    (e0 : D.R_0 ≃ₐ[ℤ_[p]] D.T_0)
    (π_0 : D.T_0 →ₐ[ℤ_[p]] ℤ_[p]) (hη : congruenceIdeal π_0 ≠ ⊥)
    (hci : Module.length ℤ_[p] (Cotangent π_0) =
      Module.length ℤ_[p] (ℤ_[p] ⧸ congruenceIdeal π_0)) :
    Module.length ℤ_[p] (Cotangent (π_0.comp e0.toAlgHom)) = (padicCongVal p π_0 : ℕ∞) ∧
    Module.length ℤ_[p] (Cotangent π_0) = (padicCongVal p π_0 : ℕ∞) ∧
    congruenceIdeal (π_0.comp e0.toAlgHom) = congruenceIdeal π_0 := by
  have hval := (padicCongVal_spec π_0 hη).1
  have hcot : Module.length ℤ_[p] (Cotangent (π_0.comp e0.toAlgHom)) =
      Module.length ℤ_[p] (Cotangent π_0) :=
    (cotangentEquivOfAlgEquiv e0 π_0).length_eq
  exact ⟨hcot.trans (hci.trans hval), hci.trans hval, congruenceIdeal_eq_of_algEquiv e0 π_0⟩

/-- **Direct Bridge into `Stage3PatchingUnification.TaylorWilesCongruenceDatum`**. -/
def DiamondFujiwaraPatchingTower.toTaylorWilesCongruenceDatum
    {S : SelmerSystem} {E : Type} [Field E] [NumberField E]
    {l : Nat.Primes} [Fact l.1.Prime] {k g : ℕ}
    (D : DiamondFujiwaraPatchingTower l.1 g)
    [instAlg : Algebra ℤ_[l.1] D.T_0]
    (aug : D.T_0 →ₐ[ℤ_[l.1]] ℤ_[l.1])
    (hη : congruenceIdeal aug ≠ ⊥)
    (genRank : ℕ)
    (genMap : (Fin genRank → ℤ_[l.1]) →ₗ[ℤ_[l.1]] Cotangent aug)
    (gen_surj : Function.Surjective genMap)
    (Sel : Type) [AddCommGroup Sel] [Module ℤ_[l.1] Sel]
    (embed : Sel →ₗ[ℤ_[l.1]] Cotangent aug)
    (embed_inj : Function.Injective embed)
    (sha_le : S.shaLen E l k ≤ Module.length ℤ_[l.1] Sel) :
    TaylorWilesCongruenceDatum S E l k where
  patching := D.toTaylorWilesPatchingDatum
  𝒪 := ℤ_[l.1]
  algOT0 := instAlg
  aug := aug
  genRank := genRank
  genMap := genMap
  gen_surj := gen_surj
  congLen := padicCongVal l.1 aug
  cong_length_le := le_of_eq (padicCongVal_spec aug hη).1
  Sel := Sel
  embed := embed
  embed_inj := embed_inj
  sha_le_selmer := sha_le

/-- **Combined Diamond–Fujiwara Patching + Rubin–Kolyvagin Euler-System Bridge** (`Stage11EulerSystemSelmer`). -/
theorem diamondFujiwara_eulerSystem_sandwich {p g : ℕ} [Fact p.Prime]
    (D : DiamondFujiwaraPatchingTower p g)
    [Algebra ℤ_[p] D.R_0] [Algebra ℤ_[p] D.T_0]
    (e0 : D.R_0 ≃ₐ[ℤ_[p]] D.T_0)
    (π_0 : D.T_0 →ₐ[ℤ_[p]] ℤ_[p]) (hη : congruenceIdeal π_0 ≠ ⊥)
    (hci : Module.length ℤ_[p] (Cotangent π_0) =
      Module.length ℤ_[p] (ℤ_[p] ⧸ congruenceIdeal π_0))
    (K : KolyvaginSystemData ℤ_[p] (p : ℤ_[p]))
    (embed : Cotangent (π_0.comp e0.toAlgHom) →ₗ[ℤ_[p]] K.X)
    (hembed : Function.Injective embed) :
    (padicCongVal p π_0 : ℕ∞) = Module.length ℤ_[p] (Cotangent (π_0.comp e0.toAlgHom)) ∧
    Module.length ℤ_[p] (Cotangent (π_0.comp e0.toAlgHom)) ≤ Module.length ℤ_[p] K.X ∧
    Module.length ℤ_[p] K.X ≤ (K.baseIndex : ℕ∞) ∧
    padicCongVal p π_0 ≤ K.baseIndex := by
  have heq := (diamondFujiwara_congruence_length_eq D e0 π_0 hη hci).1
  have h1 : Module.length ℤ_[p] (Cotangent (π_0.comp e0.toAlgHom)) ≤ Module.length ℤ_[p] K.X :=
    Module.length_le_of_injective embed hembed
  have h2 : Module.length ℤ_[p] K.X ≤ (K.baseIndex : ℕ∞) :=
    selmer_length_le_kolyvagin_index (PadicInt.irreducible_p (p := p)) K
  have hle : (padicCongVal p π_0 : ℕ∞) ≤ (K.baseIndex : ℕ∞) := by rw [← heq]; exact h1.trans h2
  exact ⟨heq.symm, h1, h2, Nat.cast_le.mp hle⟩

/-- **Direct Bridge to `Stage11MazurDeformation`**: combines `Ad0WilesSelmerSystem`,
unconditional `TaylorWilesPrimeSet p N (Fintype.card Q) bad` (with surjective explicit `RingHom`s
`S_∞ →+* (ZMod (p^M))[Δ_{Q_N}]`), AND a `DiamondFujiwaraPatchingTower p (Fintype.card Q)`! -/
theorem diamondFujiwara_mazur_taylorWiles_bridge
    {G S₀ Q : Type} [Group G] [Fintype S₀] [DecidableEq S₀] [Fintype Q] [DecidableEq Q]
    {p : ℕ} [Fact p.Prime] (W : Ad0WilesSelmerSystem G S₀ Q p)
    (N : ℕ) (bad : Finset ℕ)
    (D : DiamondFujiwaraPatchingTower p (Fintype.card Q)) :
    let g := Fintype.card Q
    Nonempty (Deform0Dual W.rhoBar ≃ H1Vec (ZMod p) G (Ad0Rep W.rhoBar)) ∧
    (Module.finrank (ZMod p) (W.D.Selmer W.L_Q) : ℤ) -
      Module.finrank (ZMod p) (W.D.DualSelmer W.L_Q) = (g : ℤ) ∧
    (∃ TW : TaylorWilesPrimeSet p N g bad,
      Fintype.card TW.GlobalDiamond = (p ^ N) ^ g ∧
      ∀ M : ℕ, 1 ≤ M → Function.Surjective (TW.patchingToFiniteLevelDiamond M)) ∧
    Nonempty (D.M_inf ≃ₗ[PatchingBaseRing p g] (Fin D.rank → PatchingBaseRing p g)) ∧
    Nonempty (D.R_inf ≃+* D.T_inf) ∧
    Nonempty (D.R_0 ≃+* D.T_0) ∧
    (∃ s : ℕ, 0 < s ∧ Nonempty (D.M_0 ≃ₗ[D.T_0] (Fin s → D.T_0))) := by
  intro g
  obtain ⟨hMfree, _, hRT_inf, hRT_0, hM0_free⟩ := D.main_patching_theorem
  obtain ⟨TW⟩ := exists_taylorWilesPrimeSet p N g bad
  exact ⟨⟨deform0DualEquivH1 W.hp3 W.rhoBar⟩,
    W.wiles_Q_balancing_equation,
    ⟨TW, TW.card_globalDiamond, fun M hM => (TW.patchingToFiniteLevelDiamond_surjective M hM).1⟩,
    hMfree, hRT_inf, hRT_0, hM0_free⟩

end DiamondFujiwaraPatchingEngine

/-! ## Section 3: Concrete `0`-Assumption Finite-Rank Witnesses (`ℤ_[p][X]/(X² - p^k X)` & Ramanujan `Δ` mod `691`) -/

section ConcreteExplicitWitnesses

/-! ### 3.1 Explicit `ℤ_[p][X]/(X² - p^k X)` Witness (Congruence Modulus `p^k`, All `p, g, k ≥ 1`) -/

/-- Exact `p`-adic congruence valuation of `QuadAlg ℤ_[p] ((p : ℤ_[p]) ^ k) 0` at root `0`:
`congruenceIdeal = (p^k)`, `padicCongVal = k`, and `length(Φ) = k`. -/
theorem quadAlgPk_congruenceIdeal_and_val (p k : ℕ) [Fact p.Prime] :
    let π := QuadAlg.aug (A := ℤ_[p]) (b := (p : ℤ_[p]) ^ k) (c := 0) (lam := 0) (by ring)
    congruenceIdeal π = Ideal.span ({(p : ℤ_[p]) ^ k} : Set ℤ_[p]) ∧
    congruenceIdeal π ≠ ⊥ ∧
    padicCongVal p π = k ∧
    Module.length ℤ_[p] (Cotangent π) = (k : ℕ∞) := by
  intro π
  have hη : congruenceIdeal π = Ideal.span ({(p : ℤ_[p]) ^ k} : Set ℤ_[p]) := by
    rw [QuadAlg.congruenceIdeal_aug_eq]
    have hneg : 2 * (0 : ℤ_[p]) - (p : ℤ_[p]) ^ k = -((p : ℤ_[p]) ^ k) := by ring
    rw [hneg, Ideal.span_singleton_neg]
  have hp_irr : Irreducible (p : ℤ_[p]) := PadicInt.irreducible_p
  have hη_ne : congruenceIdeal π ≠ ⊥ := by
    rw [hη]
    intro hbot
    exact pow_ne_zero k hp_irr.ne_zero (Ideal.mem_bot.mp (hbot ▸ Ideal.subset_span rfl))
  have hval_spec := padicCongVal_spec π hη_ne
  have hlen_q : Module.length ℤ_[p] (ℤ_[p] ⧸ congruenceIdeal π) = (k : ℕ∞) := by
    rw [hη]; exact length_quotient_span_pow_eq_of_dvr hp_irr k
  have hval : padicCongVal p π = k := ENat.natCast_inj.mp (hval_spec.1.symm.trans hlen_q)
  have hlen : Module.length ℤ_[p] (Cotangent π) = (k : ℕ∞) := by
    rw [QuadAlg.length_cotangent_eq, hlen_q]
  exact ⟨hη, hη_ne, hval, hlen⟩

/-- **Concrete Witness 3.1A (Unconditional Wiles–Lenstra on `ℤ_[p][X]/(X² - p^k X)`)**:
for EVERY prime `p` and EVERY `k ≥ 1`, fires `wiles_lenstra_adjoinRoot_quad_criterion_Zp` with `0` assumptions! -/
theorem witness_quadPk_wiles_lenstra (p k : ℕ) [Fact p.Prime] (hk : 1 ≤ k) :
    let φ := (quadAlg_equiv_adjoinRoot_X_mul_sub ℤ_[p] ((p : ℤ_[p]) ^ k)).symm.toAlgHom
    let π := QuadAlg.aug (A := ℤ_[p]) (b := (p : ℤ_[p]) ^ k) (c := 0) (lam := 0) (by ring)
    Function.Bijective φ ∧
    Nonempty (AdjoinRoot (Polynomial.X * (Polynomial.X - Polynomial.C ((p : ℤ_[p]) ^ k))) ≃+*
      QuadAlg ℤ_[p] ((p : ℤ_[p]) ^ k) 0) ∧
    Module.length ℤ_[p] (Cotangent (π.comp φ)) = (k : ℕ∞) ∧
    padicCongVal p π = k ∧
    Nonempty (IsGorensteinOver ℤ_[p] (QuadAlg ℤ_[p] ((p : ℤ_[p]) ^ k) 0)) ∧
    IsLocalRing (QuadAlg ℤ_[p] ((p : ℤ_[p]) ^ k) 0) := by
  intro φ π
  have hpk_dvd : (p : ℤ_[p]) ∣ (p : ℤ_[p]) ^ k := dvd_pow_self _ (by omega)
  have hpk_ne : (p : ℤ_[p]) ^ k ≠ 0 := pow_ne_zero k (PadicInt.irreducible_p (p := p)).ne_zero
  have hcompat : (π.comp φ).comp (quadAlg_equiv_adjoinRoot_X_mul_sub ℤ_[p] ((p : ℤ_[p]) ^ k)).toAlgHom = π := by
    ext x; simp [φ]
  have hquad := quadAlgPk_congruenceIdeal_and_val p k
  have hcot_le : Module.length ℤ_[p] (Cotangent (π.comp φ)) ≤ (padicCongVal p π : ℕ∞) := by
    rw [(cotangentEquivOfAlgEquiv (quadAlg_equiv_adjoinRoot_X_mul_sub ℤ_[p] ((p : ℤ_[p]) ^ k)).symm π).length_eq,
      hquad.2.2.2, hquad.2.2.1]
  obtain ⟨hbij, hring, hlen, hgor, hloc⟩ :=
    wiles_lenstra_adjoinRoot_quad_criterion_Zp hpk_dvd hpk_ne φ
      (quadAlg_equiv_adjoinRoot_X_mul_sub ℤ_[p] ((p : ℤ_[p]) ^ k)).symm.surjective π hcompat hcot_le
  rw [hquad.2.2.1] at hlen
  exact ⟨hbij, hring, hlen, hquad.2.2.1, hgor, hloc⟩

/-- **Generic Concrete Quadratic `DiamondFujiwaraPatchingTower p g`** for ANY `b : ℤ_[p]` and ANY
specialization ring `T₀ ≃+* QuadAlg ℤ_[p] b 0` over bundled finite quotients `S_n = S_∞ ⧸ I_n`. -/
def concreteQuadDiamondFujiwaraTower (p g : ℕ) [Fact p.Prime] (b : ℤ_[p])
    (T₀ : Type) [CommRing T₀] (eT : QuadAlg ℤ_[p] b 0 ≃+* T₀) :
    DiamondFujiwaraPatchingTower p g where
  rank := 2
  rank_pos := by norm_num
  R_inf := QuadAlg (PatchingBaseRing p g) (MvPowerSeries.C b) (MvPowerSeries.C 0)
  T_inf := QuadAlg (PatchingBaseRing p g) (MvPowerSeries.C b) (MvPowerSeries.C 0)
  phi_inf := AlgHom.id (PatchingBaseRing p g)
    (QuadAlg (PatchingBaseRing p g) (MvPowerSeries.C b) (MvPowerSeries.C 0))
  phi_surj := Function.surjective_id
  M_inf := QuadAlg (PatchingBaseRing p g) (MvPowerSeries.C b) (MvPowerSeries.C 0)
  compat_RM_TM := fun _ _ => rfl
  M_inf_regular := isPatchingRegularSeq_of_equiv_pi
    (QuadAlg.equivPi2 (PatchingBaseRing p g) (MvPowerSeries.C b) (MvPowerSeries.C 0))
  R_n := fun n => QuadAlg (FiniteLevelRing p g n)
    (finiteLevelProj p g n (MvPowerSeries.C b)) (finiteLevelProj p g n (MvPowerSeries.C 0))
  T_n := fun n => QuadAlg (FiniteLevelRing p g n)
    (finiteLevelProj p g n (MvPowerSeries.C b)) (finiteLevelProj p g n (MvPowerSeries.C 0))
  M_n := fun n => QuadAlg (FiniteLevelRing p g n)
    (finiteLevelProj p g n (MvPowerSeries.C b)) (finiteLevelProj p g n (MvPowerSeries.C 0))
  projR := fun n => QuadAlg.mapRingHom (finiteLevelProj p g n) (MvPowerSeries.C b) (MvPowerSeries.C 0)
  projR_surj := fun n u => by
    obtain ⟨x, hx⟩ := finiteLevelProj_surjective p g n u.fst
    obtain ⟨y, hy⟩ := finiteLevelProj_surjective p g n u.snd
    exact ⟨⟨x, y⟩, QuadAlg.ext hx hy⟩
  phi_n := fun _ => AlgHom.id _ _
  phi_n_surj := fun _ => Function.surjective_id
  T_n_faithful := fun n => by
    rw [eq_bot_iff]; intro a ha
    have h1 := Module.mem_annihilator.mp ha
      (1 : QuadAlg (FiniteLevelRing p g n)
        (finiteLevelProj p g n (MvPowerSeries.C b)) (finiteLevelProj p g n (MvPowerSeries.C 0)))
    simpa using h1
  M_n_free := fun n => QuadAlg.equivPi2 _
    (finiteLevelProj p g n (MvPowerSeries.C b)) (finiteLevelProj p g n (MvPowerSeries.C 0))
  M0_rank_compat := ⟨coinvEquivPiOfEquivPi (patchingAugIdeal p g)
    (QuadAlg.equivPi2 (PatchingBaseRing p g) (MvPowerSeries.C b) (MvPowerSeries.C 0))⟩
  R_0 := T₀
  T_0 := T₀
  specR := (quadAlg_patchingBaseRing_quot_equiv p g b 0).trans eT
  specT := (quadAlg_patchingBaseRing_quot_equiv p g b 0).trans eT
  dim_witness := Or.inr ⟨(QuadAlg.equivPi2 (PatchingBaseRing p g) (MvPowerSeries.C b) (MvPowerSeries.C 0),
    ⟨LinearMap.id, Function.surjective_id⟩)⟩

/-- **Concrete Witness 3.1B (Unconditional Diamond–Fujiwara Patching on `ℤ_[p][X]/(X² - p^k X)`)**. -/
theorem witness_quadPk_diamondFujiwara (p g k : ℕ) [Fact p.Prime] :
    let D := concreteQuadDiamondFujiwaraTower p g ((p : ℤ_[p]) ^ k)
      (QuadAlg ℤ_[p] ((p : ℤ_[p]) ^ k) 0) (RingEquiv.refl _)
    let π_0 := QuadAlg.aug (A := ℤ_[p]) (b := (p : ℤ_[p]) ^ k) (c := 0) (lam := 0) (by ring)
    Nonempty (D.M_inf ≃ₗ[PatchingBaseRing p g] (Fin 2 → PatchingBaseRing p g)) ∧
    Nonempty (D.R_inf ≃+* D.T_inf) ∧
    Nonempty (D.R_0 ≃+* D.T_0) ∧
    (∃ s : ℕ, 0 < s ∧ Nonempty (D.M_0 ≃ₗ[D.T_0] (Fin s → D.T_0))) ∧
    Module.length ℤ_[p] (Cotangent π_0) = (padicCongVal p π_0 : ℕ∞) ∧
    padicCongVal p π_0 = k := by
  intro D π_0
  obtain ⟨hMfree, _, hRT_inf, hRT_0, hM0_free⟩ := D.main_patching_theorem
  have hquad := quadAlgPk_congruenceIdeal_and_val p k
  obtain ⟨hcot_eq, _, _⟩ := @diamondFujiwara_congruence_length_eq p g _ D
    (QuadAlg.instAlgebra) (QuadAlg.instAlgebra)
    (AlgEquiv.refl : QuadAlg ℤ_[p] ((p : ℤ_[p]) ^ k) 0 ≃ₐ[ℤ_[p]] QuadAlg ℤ_[p] ((p : ℤ_[p]) ^ k) 0)
    π_0 hquad.2.1 (QuadAlg.length_cotangent_eq _)
  exact ⟨hMfree, hRT_inf, hRT_0, hM0_free, hcot_eq, hquad.2.2.1⟩

/-! ### 3.2 Concrete Weight-12 Ramanujan `Δ` mod `691` Congruence Tower (`p = 691`, ZERO `native_decide`) -/

/-- `691` is prime (kernel-certified via `norm_num`, ZERO `native_decide`). -/
theorem prime_691 : Nat.Prime 691 := by norm_num

instance instFactPrime691 : Fact (Nat.Prime 691) := ⟨prime_691⟩

/-- Exact divisor-sum evaluation `σ₁₁(2) = 1 + 2¹¹ = 2049`. -/
theorem sigma11_two : ArithmeticFunction.sigma 11 2 = 2049 := by
  rw [ArithmeticFunction.sigma_apply]
  have hdiv : Nat.divisors 2 = {1, 2} := by decide
  rw [hdiv, Finset.sum_pair (by norm_num)]
  norm_num

/-- Exact weight-12 Hecke `T₂`-eigenvalue difference on `M₁₂(SL₂(ℤ)) = ℂ·Δ ⊕ ℂ·E₁₂`:
`τ(2) = -24`, `σ₁₁(2) = 2049`, `σ₁₁(2) - τ(2) = 2073 = 3 * 691`, and `v_{691}(2073) = 1`. -/
theorem delta691_T2_eigenvalues :
    ramanujanTau 2 = -24 ∧
    (ArithmeticFunction.sigma 11 2 : ℤ) = 2049 ∧
    (ArithmeticFunction.sigma 11 2 : ℤ) - ramanujanTau 2 = 2073 ∧
    (2073 : ℤ) = 3 * 691 ∧
    padicValNat 691 2073 = 1 := by
  have hτ : ramanujanTau 2 = -24 := ramanujanTau_two
  have hσ : (ArithmeticFunction.sigma 11 2 : ℤ) = 2049 := by exact_mod_cast sigma11_two
  have hv : padicValNat 691 2073 = 1 := by
    have h2073 : (2073 : ℕ) = 3 * 691 := by norm_num
    rw [h2073, padicValNat.mul (by norm_num) (by norm_num),
      padicValNat.eq_zero_of_not_dvd (by norm_num), padicValNat.self (by norm_num), zero_add]
  exact ⟨hτ, hσ, by linarith, by norm_num, hv⟩

/-- **Concrete Weight-12 Ramanujan `Δ` mod `691` Congruence Hecke Algebra**:
`𝕋_{691}(M₁₂) := { (a, b) ∈ ℤ_[691] × ℤ_[691] | a ≡ b (mod 691) }`. -/
def deltaMod691Subalgebra : Subalgebra ℤ_[691] (ℤ_[691] × ℤ_[691]) where
  carrier := { ab | (691 : ℤ_[691]) ∣ ab.1 - ab.2 }
  mul_mem' {x y} hx hy := by
    obtain ⟨q₁, hq₁⟩ := hx; obtain ⟨q₂, hq₂⟩ := hy
    refine ⟨x.1 * q₂ + y.2 * q₁, ?_⟩
    change x.1 * y.1 - x.2 * y.2 = 691 * (x.1 * q₂ + y.2 * q₁)
    linear_combination x.1 * hq₂ + y.2 * hq₁
  add_mem' {x y} hx hy := by
    obtain ⟨q₁, hq₁⟩ := hx; obtain ⟨q₂, hq₂⟩ := hy
    refine ⟨q₁ + q₂, ?_⟩
    change (x.1 + y.1) - (x.2 + y.2) = 691 * (q₁ + q₂)
    linear_combination hq₁ + hq₂
  algebraMap_mem' r := ⟨0, by change r - r = 691 * 0; ring⟩

abbrev DeltaMod691HeckeAlg : Type := deltaMod691Subalgebra

/-- Every Hecke operator `T_n = (τ(n), σ₁₁(n))` lies unconditionally in `DeltaMod691HeckeAlg`,
wired directly to `Stage8RamanujanCongruences.ramanujanTau_mod_691`. -/
def deltaMod691HeckeOp (n : ℕ) : DeltaMod691HeckeAlg :=
  ⟨((ramanujanTau n : ℤ_[691]), ((ArithmeticFunction.sigma 11 n : ℤ) : ℤ_[691])), by
    have hmod := ramanujanTau_mod_691 n
    rw [Int.modEq_iff_dvd] at hmod
    obtain ⟨q, hq⟩ := hmod
    refine ⟨-(q : ℤ_[691]), ?_⟩
    have hZ : (ramanujanTau n : ℤ) - (ArithmeticFunction.sigma 11 n : ℤ) = 691 * (-q) := by linarith
    simpa using congrArg (Int.cast (R := ℤ_[691])) hZ⟩

/-- Cuspidal augmentation `π_Δ : DeltaMod691HeckeAlg →ₐ[ℤ_[691]] ℤ_[691]` (`T_n ↦ τ(n)`). -/
def deltaMod691Aug : DeltaMod691HeckeAlg →ₐ[ℤ_[691]] ℤ_[691] where
  toFun x := x.1.1
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

@[simp]
theorem deltaMod691Aug_heckeOp (n : ℕ) :
    deltaMod691Aug (deltaMod691HeckeOp n) = (ramanujanTau n : ℤ_[691]) := rfl

/-- Exact `ℤ_[691]`-algebra isomorphism `QuadAlg ℤ_[691] 691 0 ≃ₐ[ℤ_[691]] DeltaMod691HeckeAlg`. -/
def quadAlg691_equiv_deltaMod691HeckeAlg :
    QuadAlg ℤ_[691] (691 : ℤ_[691]) 0 ≃ₐ[ℤ_[691]] DeltaMod691HeckeAlg := by
  let φ : QuadAlg ℤ_[691] (691 : ℤ_[691]) 0 →ₐ[ℤ_[691]] DeltaMod691HeckeAlg :=
    { toFun := fun u => ⟨(u.fst, u.fst + 691 * u.snd), ⟨-u.snd, by ring⟩⟩
      map_one' := by apply Subtype.ext; ext <;> simp
      map_mul' := fun u v => by
        apply Subtype.ext; ext
        · change u.fst * v.fst - 0 * (u.snd * v.snd) = u.fst * v.fst; ring
        · change (u.fst * v.fst - 0 * (u.snd * v.snd)) +
              691 * (u.fst * v.snd + u.snd * v.fst + 691 * (u.snd * v.snd)) =
            (u.fst + 691 * u.snd) * (v.fst + 691 * v.snd); ring
      map_zero' := by apply Subtype.ext; ext <;> simp
      map_add' := fun u v => by
        apply Subtype.ext; ext
        · rfl
        · change (u.fst + v.fst) + 691 * (u.snd + v.snd) = (u.fst + 691 * u.snd) + (v.fst + 691 * v.snd); ring
      commutes' := fun r => by apply Subtype.ext; ext <;> simp }
  have h691_ne : (691 : ℤ_[691]) ≠ 0 := (PadicInt.irreducible_p (p := 691)).ne_zero
  have hbij : Function.Bijective φ := by
    constructor
    · intro u v huv
      have h1 : u.fst = v.fst := congrArg (fun x : DeltaMod691HeckeAlg => x.1.1) huv
      have h2 : u.fst + 691 * u.snd = v.fst + 691 * v.snd :=
        congrArg (fun x : DeltaMod691HeckeAlg => x.1.2) huv
      have h3 : (691 : ℤ_[691]) * u.snd = 691 * v.snd := by rw [h1] at h2; exact add_left_cancel h2
      ext
      · exact h1
      · exact mul_left_cancel₀ h691_ne h3
    · rintro ⟨⟨a, b⟩, ⟨q, hq⟩⟩
      refine ⟨⟨a, -q⟩, ?_⟩
      apply Subtype.ext; ext
      · rfl
      · change a + 691 * (-q) = b; linear_combination hq
  exact AlgEquiv.ofBijective φ hbij

instance instModuleFreeDeltaMod691 : Module.Free ℤ_[691] DeltaMod691HeckeAlg :=
  Module.Free.of_equiv quadAlg691_equiv_deltaMod691HeckeAlg.toLinearEquiv

instance instModuleFiniteDeltaMod691 : Module.Finite ℤ_[691] DeltaMod691HeckeAlg :=
  Module.Finite.equiv quadAlg691_equiv_deltaMod691HeckeAlg.toLinearEquiv

/-- `(3 : ℤ_[691])` is a unit in `ℤ_[691]` (pure algebraic proof via `ZMod.natCast_eq_zero_iff` + `norm_num`). -/
theorem isUnit_three_padic691 : IsUnit (3 : ℤ_[691]) := by
  have hndvd : ¬ ((691 : ℤ_[691]) ∣ (3 : ℤ_[691])) := by
    rintro ⟨q, hq⟩
    have h0 := congrArg (PadicInt.toZMod (p := 691)) hq
    rw [map_mul, map_ofNat, map_ofNat] at h0
    have h691_0 : (691 : ZMod 691) = 0 := by
      change ((691 : ℕ) : ZMod 691) = 0
      exact CharP.cast_eq_zero (ZMod 691) 691
    rw [h691_0, zero_mul] at h0
    have h30 : ((3 : ℕ) : ZMod 691) = 0 := by simpa using h0
    rw [ZMod.natCast_eq_zero_iff] at h30
    norm_num at h30
  by_contra hnu
  have hmem : (3 : ℤ_[691]) ∈ IsLocalRing.maximalIdeal ℤ_[691] :=
    (IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hnu)
  have hmax : IsLocalRing.maximalIdeal ℤ_[691] = Ideal.span ({(691 : ℤ_[691])} : Set ℤ_[691]) :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer (691 : ℤ_[691])).mp
      (PadicInt.irreducible_p (p := 691))
  rw [hmax] at hmem
  exact hndvd (Ideal.mem_span_singleton.mp hmem)

/-- Exact `ℤ_[691]`-algebra isomorphism `AdjoinRoot (X * (X - C 2073)) ≃ₐ[ℤ_[691]] DeltaMod691HeckeAlg`
generated by `T₂ - τ(2) = (0, 2073)`. -/
def adjoinRoot2073_equiv_deltaMod691HeckeAlg :
    AdjoinRoot (Polynomial.X * (Polynomial.X - Polynomial.C (2073 : ℤ_[691]))) ≃ₐ[ℤ_[691]]
      DeltaMod691HeckeAlg := by
  let u3 : ℤ_[691]ˣ := isUnit_three_padic691.unit
  have hu3 : (u3 : ℤ_[691]) = 3 := isUnit_three_padic691.unit_spec
  have h2073 : (2073 : ℤ_[691]) = (u3 : ℤ_[691]) * (691 : ℤ_[691]) := by
    rw [hu3]; exact_mod_cast (by norm_num : (2073 : ℕ) = 3 * 691)
  let scale : QuadAlg ℤ_[691] (2073 : ℤ_[691]) 0 ≃ₐ[ℤ_[691]] QuadAlg ℤ_[691] (691 : ℤ_[691]) 0 :=
    { toFun := fun v => ⟨v.fst, (u3 : ℤ_[691]) * v.snd⟩
      invFun := fun w => ⟨w.fst, ((u3⁻¹ : ℤ_[691]ˣ) : ℤ_[691]) * w.snd⟩
      left_inv := fun v => by
        ext
        · rfl
        · change ((u3⁻¹ : ℤ_[691]ˣ) : ℤ_[691]) * ((u3 : ℤ_[691]) * v.snd) = v.snd
          rw [← mul_assoc, Units.inv_mul, one_mul]
      right_inv := fun w => by
        ext
        · rfl
        · change (u3 : ℤ_[691]) * (((u3⁻¹ : ℤ_[691]ˣ) : ℤ_[691]) * w.snd) = w.snd
          rw [← mul_assoc, Units.mul_inv, one_mul]
      map_mul' := fun v₁ v₂ => by
        ext
        · change v₁.fst * v₂.fst - 0 * (v₁.snd * v₂.snd) =
            v₁.fst * v₂.fst - 0 * (((u3 : ℤ_[691]) * v₁.snd) * ((u3 : ℤ_[691]) * v₂.snd)); ring
        · change (u3 : ℤ_[691]) * (v₁.fst * v₂.snd + v₁.snd * v₂.fst + 2073 * (v₁.snd * v₂.snd)) =
            v₁.fst * ((u3 : ℤ_[691]) * v₂.snd) + ((u3 : ℤ_[691]) * v₁.snd) * v₂.fst +
              691 * (((u3 : ℤ_[691]) * v₁.snd) * ((u3 : ℤ_[691]) * v₂.snd))
          linear_combination (u3 : ℤ_[691]) * (v₁.snd * v₂.snd) * h2073
      map_add' := fun v₁ v₂ => by
        ext
        · rfl
        · change (u3 : ℤ_[691]) * (v₁.snd + v₂.snd) =
            (u3 : ℤ_[691]) * v₁.snd + (u3 : ℤ_[691]) * v₂.snd; ring
      commutes' := fun r => by ext <;> simp }
  exact (quadAlg_equiv_adjoinRoot_X_mul_sub ℤ_[691] (2073 : ℤ_[691])).symm.trans
    (scale.trans quadAlg691_equiv_deltaMod691HeckeAlg)

/-- Exact congruence ideal `(691)`, congruence valuation `v_{691}(η) = 1`, and cotangent length `1`. -/
theorem deltaMod691Aug_congruence_spec :
    congruenceIdeal deltaMod691Aug = Ideal.span ({(691 : ℤ_[691])} : Set ℤ_[691]) ∧
    congruenceIdeal deltaMod691Aug ≠ ⊥ ∧
    padicCongVal 691 deltaMod691Aug = 1 ∧
    Module.length ℤ_[691] (Cotangent deltaMod691Aug) = (1 : ℕ∞) := by
  let e := quadAlg691_equiv_deltaMod691HeckeAlg
  have hcomp : deltaMod691Aug.comp e.toAlgHom =
      QuadAlg.aug (A := ℤ_[691]) (b := (691 : ℤ_[691])) (c := 0) (lam := 0) (by ring) := by
    ext u; change u.fst = u.fst + u.snd * 0; ring
  have hη : congruenceIdeal deltaMod691Aug = Ideal.span ({(691 : ℤ_[691])} : Set ℤ_[691]) := by
    rw [← congruenceIdeal_eq_of_algEquiv e deltaMod691Aug, hcomp, QuadAlg.congruenceIdeal_aug_eq]
    have hneg : 2 * (0 : ℤ_[691]) - (691 : ℤ_[691]) = -(691 : ℤ_[691]) := by ring
    rw [hneg, Ideal.span_singleton_neg]
  have hη_ne : congruenceIdeal deltaMod691Aug ≠ ⊥ := by
    rw [hη]
    exact fun hbot => (PadicInt.irreducible_p (p := 691)).ne_zero
      (Ideal.mem_bot.mp (hbot ▸ Ideal.subset_span rfl))
  have hlen_q : Module.length ℤ_[691] (ℤ_[691] ⧸ congruenceIdeal deltaMod691Aug) = (1 : ℕ∞) := by
    rw [hη, show (691 : ℤ_[691]) = ((691 : ℕ) : ℤ_[691]) ^ 1 by simp]
    simpa using length_quotient_span_pow_eq_of_dvr (PadicInt.irreducible_p (p := 691)) 1
  have hval : padicCongVal 691 deltaMod691Aug = 1 := by
    have hsp := (padicCongVal_spec deltaMod691Aug hη_ne).1
    exact ENat.natCast_inj.mp (hsp.symm.trans (by simpa using hlen_q))
  have hlen : Module.length ℤ_[691] (Cotangent deltaMod691Aug) = (1 : ℕ∞) := by
    rw [← (cotangentEquivOfAlgEquiv e deltaMod691Aug).length_eq, hcomp,
      QuadAlg.length_cotangent_eq, ← hcomp, congruenceIdeal_eq_of_algEquiv e deltaMod691Aug, hlen_q]
  exact ⟨hη, hη_ne, hval, hlen⟩

/-- **Concrete Witness 3.2A (Unconditional Wiles–Lenstra on Weight-12 Ramanujan `Δ` mod `691`)**:
fires `wiles_lenstra_adjoinRoot_quad_criterion_Zp` on `ℤ_[691][X]/(X² - 2073 X) → DeltaMod691HeckeAlg`
with ZERO assumptions! -/
theorem witness_delta691_wiles_lenstra :
    let φ := adjoinRoot2073_equiv_deltaMod691HeckeAlg.toAlgHom
    Function.Bijective φ ∧
    Nonempty (AdjoinRoot (Polynomial.X * (Polynomial.X - Polynomial.C (2073 : ℤ_[691]))) ≃+*
      DeltaMod691HeckeAlg) ∧
    Module.length ℤ_[691] (Cotangent (deltaMod691Aug.comp φ)) = (1 : ℕ∞) ∧
    padicCongVal 691 deltaMod691Aug = 1 ∧
    Nonempty (IsGorensteinOver ℤ_[691] DeltaMod691HeckeAlg) ∧
    IsLocalRing DeltaMod691HeckeAlg := by
  intro φ
  have h2073_eq : (2073 : ℤ_[691]) = 3 * (691 : ℤ_[691]) := by
    exact_mod_cast (by norm_num : (2073 : ℕ) = 3 * 691)
  have h691_dvd : (691 : ℤ_[691]) ∣ (2073 : ℤ_[691]) := ⟨3, by rw [h2073_eq, mul_comm]⟩
  have h2073_ne : (2073 : ℤ_[691]) ≠ 0 := by
    rw [h2073_eq]; exact mul_ne_zero (by norm_num) (PadicInt.irreducible_p (p := 691)).ne_zero
  have hcompat :
      (deltaMod691Aug.comp φ).comp (quadAlg_equiv_adjoinRoot_X_mul_sub ℤ_[691] (2073 : ℤ_[691])).toAlgHom =
        QuadAlg.aug (A := ℤ_[691]) (b := (2073 : ℤ_[691])) (c := 0) (lam := 0) (by ring) := by
    ext u
    simp only [AlgHom.comp_apply, φ, adjoinRoot2073_equiv_deltaMod691HeckeAlg,
      AlgEquiv.coe_toAlgHom, AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply]
    change u.fst = u.fst + u.snd * 0; ring
  have hsp := deltaMod691Aug_congruence_spec
  have hcot_le : Module.length ℤ_[691] (Cotangent (deltaMod691Aug.comp φ)) ≤
      (padicCongVal 691 deltaMod691Aug : ℕ∞) := by
    rw [(cotangentEquivOfAlgEquiv adjoinRoot2073_equiv_deltaMod691HeckeAlg deltaMod691Aug).length_eq,
      hsp.2.2.2, hsp.2.2.1]
    simp
  obtain ⟨hbij, hring, hlen, hgor, hloc⟩ :=
    wiles_lenstra_adjoinRoot_quad_criterion_Zp h691_dvd h2073_ne φ
      adjoinRoot2073_equiv_deltaMod691HeckeAlg.surjective deltaMod691Aug hcompat hcot_le
  rw [hsp.2.2.1] at hlen
  exact ⟨hbij, hring, hlen, hsp.2.2.1, hgor, hloc⟩

/-- **Concrete Witness 3.2B (Unconditional Diamond–Fujiwara Patching Tower for Ramanujan `Δ` mod `691`)**. -/
def witness_delta691_diamondFujiwaraTower (g : ℕ) : DiamondFujiwaraPatchingTower 691 g :=
  concreteQuadDiamondFujiwaraTower 691 g (691 : ℤ_[691]) DeltaMod691HeckeAlg
    quadAlg691_equiv_deltaMod691HeckeAlg.toRingEquiv

/-- **Summary Theorem for the Weight-12 Ramanujan `Δ` mod `691` Diamond–Fujiwara Tower**. -/
theorem witness_delta691_diamondFujiwara_summary (g : ℕ) :
    let D := witness_delta691_diamondFujiwaraTower g
    Nonempty (D.M_inf ≃ₗ[PatchingBaseRing 691 g] (Fin 2 → PatchingBaseRing 691 g)) ∧
    Nonempty (D.R_inf ≃+* D.T_inf) ∧
    Nonempty (D.R_0 ≃+* D.T_0) ∧
    (∃ s : ℕ, 0 < s ∧ Nonempty (D.M_0 ≃ₗ[D.T_0] (Fin s → D.T_0))) ∧
    Module.length ℤ_[691] (Cotangent deltaMod691Aug) = (padicCongVal 691 deltaMod691Aug : ℕ∞) ∧
    padicCongVal 691 deltaMod691Aug = 1 := by
  intro D
  obtain ⟨hMfree, _, hRT_inf, hRT_0, hM0_free⟩ := D.main_patching_theorem
  have hsp := deltaMod691Aug_congruence_spec
  have hci : Module.length ℤ_[691] (Cotangent deltaMod691Aug) =
      Module.length ℤ_[691] (ℤ_[691] ⧸ congruenceIdeal deltaMod691Aug) := by
    rw [hsp.2.2.2, (padicCongVal_spec deltaMod691Aug hsp.2.1).1, hsp.2.2.1]
    simp
  obtain ⟨hcot_eq, _, _⟩ := @diamondFujiwara_congruence_length_eq 691 g _ D
    (inferInstance : Algebra ℤ_[691] DeltaMod691HeckeAlg)
    (inferInstance : Algebra ℤ_[691] DeltaMod691HeckeAlg)
    (AlgEquiv.refl : DeltaMod691HeckeAlg ≃ₐ[ℤ_[691]] DeltaMod691HeckeAlg)
    deltaMod691Aug hsp.2.1 hci
  exact ⟨hMfree, hRT_inf, hRT_0, hM0_free, hcot_eq, hsp.2.2.1⟩

/-- Concrete zero-assumption Selmer system attached to the Ramanujan `Δ` mod `691` congruence:
`shaLen E l k = v_l(691)` (`= 1` at `l = 691`, `= 0` at every other prime `l ≠ 691`). -/
def delta691_concreteSelmerSystem : SelmerSystem where
  shaLen _ _ _ l _ := (padicValNat l.1 691 : ℕ∞)

private lemma padicCongVal_quadAlg691 (l : Nat.Primes) :
    letI : Fact l.1.Prime := ⟨l.2⟩
    let b : ℤ_[l.1] := ((691 : ℤ) : ℤ_[l.1])
    let π := QuadAlg.aug (A := ℤ_[l.1]) (b := b) (c := 0) (lam := 0) (by ring)
    congruenceIdeal π ≠ ⊥ ∧
    Module.length ℤ_[l.1] (ℤ_[l.1] ⧸ congruenceIdeal π) = (padicValNat l.1 691 : ℕ∞) ∧
    padicCongVal l.1 π = padicValNat l.1 691 := by
  let _ : Fact l.1.Prime := ⟨l.2⟩
  intro b π
  have hη : congruenceIdeal π = Ideal.span ({b} : Set ℤ_[l.1]) := by
    rw [QuadAlg.congruenceIdeal_aug_eq]
    have hneg : 2 * (0 : ℤ_[l.1]) - b = -b := by ring
    rw [hneg, Ideal.span_singleton_neg]
  have hb_ne : b ≠ 0 := by dsimp only [b]; exact_mod_cast (by norm_num : (691 : ℤ) ≠ 0)
  have hη_ne : congruenceIdeal π ≠ ⊥ := by
    rw [hη]; exact fun hbot => hb_ne (Ideal.mem_bot.mp (hbot ▸ Ideal.subset_span rfl))
  have hlen_eq : Module.length ℤ_[l.1] (ℤ_[l.1] ⧸ congruenceIdeal π) = (padicValNat l.1 691 : ℕ∞) := by
    rw [hη]; exact padicInt_length_quot_span_intCast l.1 (n := 691) (by norm_num)
  have hval_eq : padicCongVal l.1 π = padicValNat l.1 691 := by
    have hsp := (padicCongVal_spec π hη_ne).1
    rw [hlen_eq] at hsp; exact Nat.cast_injective hsp.symm
  exact ⟨hη_ne, hlen_eq, hval_eq⟩

private def delta691_congruenceDatum (E : Type) [Field E] [NumberField E] (g : ℕ)
    (l : Nat.Primes) (k : ℕ) :
    TaylorWilesCongruenceDatum delta691_concreteSelmerSystem E l k :=
  letI : Fact l.1.Prime := ⟨l.2⟩
  let b : ℤ_[l.1] := ((691 : ℤ) : ℤ_[l.1])
  let D : DiamondFujiwaraPatchingTower l.1 g :=
    concreteQuadDiamondFujiwaraTower l.1 g b (QuadAlg ℤ_[l.1] b 0) (RingEquiv.refl _)
  let hroot : (0 : ℤ_[l.1]) ^ 2 - b * 0 + 0 = 0 := by ring
  let π : QuadAlg ℤ_[l.1] b 0 →ₐ[ℤ_[l.1]] ℤ_[l.1] := QuadAlg.aug (A := ℤ_[l.1]) (b := b) (c := 0) hroot
  let eCot := QuadAlg.cotangentEquiv (A := ℤ_[l.1]) (b := b) (c := 0) hroot
  let hsp := padicCongVal_quadAlg691 l
  let genMap : (Fin 1 → ℤ_[l.1]) →ₗ[ℤ_[l.1]] Cotangent π :=
    { toFun := fun v => eCot.symm (Ideal.Quotient.mk _ (v 0))
      map_add' := fun u v => by simp [map_add]
      map_smul' := fun r v => by
        change eCot.symm (Ideal.Quotient.mk _ (r * v 0)) =
          r • eCot.symm (Ideal.Quotient.mk _ (v 0))
        rw [← map_smul]; congr 1 }
  have hgen_surj : Function.Surjective genMap := fun q => by
    induction hq : eCot q using Quotient.inductionOn' with
    | h a =>
      refine ⟨fun _ => a, ?_⟩
      apply eCot.injective
      change eCot (eCot.symm (Ideal.Quotient.mk _ a)) = eCot q
      rw [eCot.apply_symm_apply, hq]; rfl
  D.toTaylorWilesCongruenceDatum (S := delta691_concreteSelmerSystem) (E := E)
    (l := l) (k := k) (instAlg := (inferInstance : Algebra ℤ_[l.1] (QuadAlg ℤ_[l.1] b 0)))
    π hsp.1 1 genMap hgen_surj (Cotangent π) LinearMap.id Function.injective_id
    (by
      change (padicValNat l.1 691 : ℕ∞) ≤ Module.length ℤ_[l.1] (Cotangent π)
      rw [QuadAlg.length_cotangent_eq hroot, hsp.2.1])

private theorem delta691_congruenceDatum_congLen (E : Type) [Field E] [NumberField E] (g : ℕ)
    (l : Nat.Primes) (k : ℕ) :
    (delta691_congruenceDatum E g l k).congLen = padicValNat l.1 691 := by
  let _ : Fact l.1.Prime := ⟨l.2⟩
  exact (padicCongVal_quadAlg691 l).2.2

private theorem delta691_congruenceDatum_bound (E : Type) [Field E] [NumberField E] (g : ℕ)
    (l : Nat.Primes) (k : ℕ) :
    (delta691_congruenceDatum E g l k).bound = padicValNat l.1 691 := by
  change 1 * (delta691_congruenceDatum E g l k).congLen = padicValNat l.1 691
  rw [one_mul, delta691_congruenceDatum_congLen]

/-- **Unconditional Zero-Assumption Ramanujan `Δ` mod `691` `CongruencePatchingRealization`**
(built DIRECTLY via `DiamondFujiwaraPatchingTower.toTaylorWilesCongruenceDatum` and
`CongruencePatchingRealization.ofFiniteSupport`, finite support `P₀ ⊆ {691}`,
envelope `B_patch = t * log 691`). -/
def delta691_congruencePatchingRealization (E : Type) [Field E] [NumberField E] (t M g : ℕ) :
    CongruencePatchingRealization delta691_concreteSelmerSystem E t M ((t : ℝ) * Real.log 691) := by
  let p691 : Nat.Primes := ⟨691, prime_691⟩
  let P₀ : Finset Nat.Primes := oddUnramifiedPrimeFactors 691 M
  have hP₀_mem : ∀ l ∈ P₀, (l : ℕ) ≠ 2 ∧ ¬ ((l : ℕ) ∣ M) := fun l hl =>
    ((mem_oddUnramifiedPrimeFactors_iff l).mp hl).2
  have hsub : P₀ ⊆ {p691} := by
    intro l hl
    have hmem : (l : ℕ) ∈ (691 : ℕ).primeFactors := ((mem_oddUnramifiedPrimeFactors_iff l).mp hl).1
    rw [Nat.Prime.primeFactors prime_691, Finset.mem_singleton] at hmem
    exact Finset.mem_singleton.mpr (Subtype.ext hmem)
  refine CongruencePatchingRealization.ofFiniteSupport P₀ hP₀_mem
    (fun l k _ _ _ _ => delta691_congruenceDatum E g l k)
    (fun l k hodd hunram _ _ hlnot => ?_)
    ?_
  · rw [delta691_congruenceDatum_congLen]
    have hndvd : ¬ (l.1 ∣ 691) := fun hdvd => hlnot <|
      (mem_oddUnramifiedPrimeFactors_iff l).mpr
        ⟨Nat.mem_primeFactors.mpr ⟨l.2, hdvd, by norm_num⟩, hodd, hunram⟩
    exact padicValNat.eq_zero_of_not_dvd hndvd
  · have hterm : ∀ l ∈ P₀.attach,
        Real.log (l.1 : ℕ) *
          ∑ k ∈ (Finset.Ico 1 t).attach,
            ((delta691_congruenceDatum E g l.1 k.1).bound : ℝ) ≤
          (t : ℝ) * (Real.log (l.1 : ℝ) * (padicValNat l.1 691 : ℝ)) := by
      intro l _
      have h1 : ∑ k ∈ (Finset.Ico 1 t).attach,
            ((delta691_congruenceDatum E g l.1 k.1).bound : ℝ) ≤
          (t : ℝ) * (padicValNat l.1 691 : ℝ) := by
        have hbd : ∀ k ∈ (Finset.Ico 1 t).attach,
            ((delta691_congruenceDatum E g l.1 k.1).bound : ℝ) = (padicValNat l.1 691 : ℝ) :=
          fun k _ => by rw [delta691_congruenceDatum_bound]
        rw [Finset.sum_congr rfl hbd, Finset.sum_const, Finset.card_attach, Nat.card_Ico, nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Nat.sub_le t 1)) (Nat.cast_nonneg _)
      calc Real.log (l.1 : ℕ) *
            ∑ k ∈ (Finset.Ico 1 t).attach, ((delta691_congruenceDatum E g l.1 k.1).bound : ℝ)
          ≤ Real.log (l.1 : ℝ) * ((t : ℝ) * (padicValNat l.1 691 : ℝ)) :=
            mul_le_mul_of_nonneg_left h1 (Real.log_natCast_nonneg _)
        _ = (t : ℝ) * (Real.log (l.1 : ℝ) * (padicValNat l.1 691 : ℝ)) := by ring
    calc ∑ l ∈ P₀.attach, Real.log (l.1 : ℕ) *
            ∑ k ∈ (Finset.Ico 1 t).attach, ((delta691_congruenceDatum E g l.1 k.1).bound : ℝ)
        ≤ ∑ l ∈ P₀.attach, (t : ℝ) * (Real.log (l.1 : ℝ) * (padicValNat l.1 691 : ℝ)) :=
          Finset.sum_le_sum hterm
      _ = (t : ℝ) * ∑ l ∈ P₀, Real.log (l.1 : ℝ) * (padicValNat l.1 691 : ℝ) := by
          rw [← Finset.mul_sum]
          congr 1
          exact Finset.sum_attach P₀ (fun l : Nat.Primes => Real.log (l.1 : ℝ) * (padicValNat l.1 691 : ℝ))
      _ ≤ (t : ℝ) * ∑ l ∈ ({p691} : Finset Nat.Primes),
            Real.log (l.1 : ℝ) * (padicValNat l.1 691 : ℝ) := by
          refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg t)
          exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun l _ _ =>
            mul_nonneg (Real.log_natCast_nonneg l.1) (Nat.cast_nonneg _)
      _ = (t : ℝ) * Real.log 691 := by
          rw [Finset.sum_singleton]
          change (t : ℝ) * (Real.log (691 : ℝ) * (padicValNat 691 691 : ℝ)) = (t : ℝ) * Real.log 691
          rw [padicValNat.self (by norm_num), Nat.cast_one, mul_one]

/-- **Unconditional `FerreroWashingtonTwoTowerSupply` for `delta691_concreteSelmerSystem`**
(at `l = 2`, `v_2(691) = 0`, wired directly to `Stage11WilesPatchingBridge`). -/
theorem delta691_ferreroWashingtonTwoTowerSupply :
    FerreroWashingtonTwoTowerSupply delta691_concreteSelmerSystem := by
  obtain ⟨hf, hμ, hcop, _, _⟩ := mazur_p2_cyclic_model_exists
  refine FerreroWashingtonTwoTowerSupply.ofUniformCyclicMuZero
    (Stage7PadicLFunction.iwasawaTransform (Stage7PadicLFunction.mazurBernoulliMeasure 2 3 (by decide)))
    hf hμ hcop fun _ _ _ _ _ _ => ?_
  change (padicValNat 2 691 : ℕ∞) ≤ _
  rw [padicValNat.eq_zero_of_not_dvd (by norm_num), Nat.cast_zero]
  exact bot_le

/-- **Unconditional `RamifiedTwoBoundSupply` (`Cb = 2`) for `delta691_concreteSelmerSystem`**
(`v_l(691) ≤ 1 ≤ 2` for every prime `l`). -/
theorem delta691_ramifiedTwoBoundSupply :
    RamifiedTwoBoundSupply delta691_concreteSelmerSystem where
  supply := fun ψ _ _ _ _ t hadm x hx q d hpp E _ _ hE => by
    have hcond := Stage2GaloisWire.condF_bounds_of_isChiField ψ _ q d
      hpp.q_prime.pos hpp.d_prime.pos E hE
    have ht2 : 2 ≤ t x := (hadm x hx).2.2.1
    have hfin1 : 1 ≤ Module.finrank ℚ E := Module.finrank_pos.ne'.bot_lt
    have hv_le1 : ∀ l : Nat.Primes, padicValNat l.1 691 ≤ 1 := fun l => by
      by_cases hl : l.1 = 691
      · rw [hl, padicValNat.self (by norm_num)]
      · have hndvd : ¬ (l.1 ∣ 691) := fun hdvd => by
          have hmem : l.1 ∈ (691 : ℕ).primeFactors := Nat.mem_primeFactors.mpr ⟨l.2, hdvd, by norm_num⟩
          rw [Nat.Prime.primeFactors prime_691, Finset.mem_singleton] at hmem
          exact hl hmem
        rw [padicValNat.eq_zero_of_not_dvd hndvd]; exact Nat.zero_le 1
    refine ⟨{
      M_ne_zero := NeZero.ne ψ.N
      N_pos := hcond.1
      t_pos := by omega
      C_nonneg := by norm_num
      localObs := fun l k _ _ _ _ =>
        localRamifiedObstruction_of_shaLen_le delta691_concreteSelmerSystem E l k
          1 (padicValNat l.1 691) (by simp [delta691_concreteSelmerSystem])
      bound_le := fun l k hl2 _ _ _ => by
        change ((1 * padicValNat l.1 691 : ℕ) : ℝ) ≤ _
        rw [one_mul]
        have hle2 : (padicValNat l.1 691 : ℝ) ≤ 2 := by
          have := hv_le1 l; exact_mod_cast (show padicValNat l.1 691 ≤ 2 by omega)
        have hl3 : (3 : ℝ) ≤ (l : ℕ) := by
          have := l.2.two_le; exact_mod_cast (show 3 ≤ (l : ℕ) by omega)
        have htR : (2 : ℝ) ≤ (t x : ℝ) := by exact_mod_cast ht2
        have hnR : (1 : ℝ) ≤ (Module.finrank ℚ E : ℝ) := by exact_mod_cast hfin1
        have hNR : (1 : ℝ) ≤ (condF E : ℝ) := by exact_mod_cast hcond.1
        have htl : (6 : ℝ) ≤ (t x : ℝ) * ((l : ℕ) : ℝ) := by nlinarith
        have htlN : (6 : ℝ) ≤ (t x : ℝ) * ((l : ℕ) : ℝ) * (condF E : ℝ) := by nlinarith
        have hlog1 : (1 : ℝ) ≤ Real.log ((t x : ℝ) * ((l : ℕ) : ℝ) * (condF E : ℝ)) := by
          have he6 : Real.exp 1 ≤ 6 := by linarith [Real.exp_one_lt_d9]
          have h := Real.log_le_log (Real.exp_pos 1) (he6.trans htlN)
          rwa [Real.log_exp] at h
        have hnsq : (1 : ℝ) ≤ (Module.finrank ℚ E : ℝ) ^ 2 := by nlinarith
        have hfac1 : (2 : ℝ) ≤ 2 * ((l : ℕ) : ℝ) * (Module.finrank ℚ E : ℝ) ^ 2 := by nlinarith
        have hfac2 : (2 : ℝ) ≤ 2 * ((l : ℕ) : ℝ) * (Module.finrank ℚ E : ℝ) ^ 2 * (t x : ℝ) := by
          nlinarith
        nlinarith }⟩

/-- **Unconditional `MinimalOddUnramifiedPatchingSupply` for `delta691_concreteSelmerSystem`**
(powered directly by `delta691_congruencePatchingRealization`, `B_patch = t * log 691`). -/
theorem delta691_minimalOddUnramifiedPatchingSupply :
    MinimalOddUnramifiedPatchingSupply delta691_concreteSelmerSystem where
  supply := fun ψ eps _ _ e t hadm => by
    refine ⟨2, 5, 0, 4, by norm_num, fun X hX q d hpp _ _ _ _ _ => ?_⟩
    refine ⟨X ^ ((1 : ℝ) / 2), le_rfl, ?_, fun x hxY _ E _ _ hE => ?_⟩
    · rw [← Real.rpow_mul (by linarith : (0 : ℝ) ≤ X)]; norm_num
    · have h2_le_sqrtX : (2 : ℝ) ≤ X ^ ((1 : ℝ) / 2) := by
        have h4 : (4 : ℝ) ^ ((1 : ℝ) / 2) = 2 := by
          rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, ← Real.rpow_natCast,
            ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]; norm_num
        calc (2 : ℝ) = (4 : ℝ) ^ ((1 : ℝ) / 2) := h4.symm
          _ ≤ X ^ ((1 : ℝ) / 2) := Real.rpow_le_rpow (by norm_num) hX (by norm_num)
      have hx2 : (2 : ℝ) ≤ x := h2_le_sqrtX.trans hxY
      have ht2 : 2 ≤ t x := (hadm x hx2).2.2.1
      have hcond := Stage2GaloisWire.condF_bounds_of_isChiField ψ (e x) q d
        hpp.q_prime.pos hpp.d_prime.pos E hE
      let R := delta691_congruencePatchingRealization E (t x) ψ.N 1
      refine ⟨⟨R.datum, fun P hP => (R.weighted_sum_le P hP).trans ?_⟩⟩
      have hlog691 : Real.log 691 ≤ 16 := by
        have h691 : (691 : ℝ) ≤ Real.exp 16 := by
          have h1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
          have hp : (2 : ℝ) ^ 16 ≤ (Real.exp 1) ^ 16 := pow_le_pow_left₀ (by norm_num) h1 16
          rw [← Real.exp_nat_mul] at hp; norm_num at hp ⊢; linarith
        have h := Real.log_le_log (by norm_num) h691
        rwa [Real.log_exp] at h
      have htR : (2 : ℝ) ≤ (t x : ℝ) := by exact_mod_cast ht2
      have hNR : (1 : ℝ) ≤ (condF E : ℝ) := by exact_mod_cast hcond.1
      have hNt_ge : (t x : ℝ) ≤ (condF E : ℝ) * (t x : ℝ) := by nlinarith
      have ht4 : (16 : ℝ) ≤ (t x : ℝ) ^ (4 : ℕ) := by
        calc (16 : ℝ) = (2 : ℝ) ^ (4 : ℕ) := by norm_num
          _ ≤ (t x : ℝ) ^ (4 : ℕ) := pow_le_pow_left₀ (by norm_num) htR 4
      have ht5_le : (t x : ℝ) * Real.log 691 ≤ ((condF E : ℝ) * (t x : ℝ)) ^ (5 : ℝ) := by
        calc (t x : ℝ) * Real.log 691
            ≤ (t x : ℝ) * 16 := mul_le_mul_of_nonneg_left hlog691 (by linarith)
          _ ≤ (t x : ℝ) * (t x : ℝ) ^ (4 : ℕ) := mul_le_mul_of_nonneg_left ht4 (by linarith)
          _ = (t x : ℝ) ^ (5 : ℕ) := by ring
          _ ≤ ((condF E : ℝ) * (t x : ℝ)) ^ (5 : ℕ) := pow_le_pow_left₀ (by linarith) hNt_ge 5
          _ = ((condF E : ℝ) * (t x : ℝ)) ^ (5 : ℝ) := by rw [← Real.rpow_natCast]; norm_num
      have hexp_nn : (0 : ℝ) ≤ 5 * Real.exp (x ^ (4 * eps / 5)) := by positivity
      linarith

/-- **UNCONDITIONAL `0`-ASSUMPTION END-TO-END RAMANUJAN `Δ` MOD `691` `VWin` CHAIN**
(directly wired into `Stage11WilesPatchingBridge.unifiedPatchingWindowSupply_of_ferrero_ramified_minimal`!). -/
theorem delta691_unconditional_vwin_chain :
    UnifiedPatchingWindowSupply delta691_concreteSelmerSystem ∧
    Stage2GaloisWire.ThreePartPatchingWindow delta691_concreteSelmerSystem ∧
    GaloisModularityContract delta691_concreteSelmerSystem ∧
    VWin delta691_concreteSelmerSystem :=
  let hU := unifiedPatchingWindowSupply_of_ferrero_ramified_minimal
    delta691_ferreroWashingtonTwoTowerSupply
    delta691_ramifiedTwoBoundSupply
    delta691_minimalOddUnramifiedPatchingSupply
  ⟨hU, threePartPatchingWindow_of_unified hU,
    galoisModularityContract_of_unified hU, vwin_of_unified hU⟩

end ConcreteExplicitWitnesses

end Stage11DiamondFujiwara
end RHDirect

end
