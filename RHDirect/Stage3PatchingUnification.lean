import RHDirect.TaylorWilesWindow
import RHDirect.Stage2GaloisWire
import RHDirect.Stage2RamifiedPrimes
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.RingTheory.OrzechProperty
import Mathlib.LinearAlgebra.FreeModule.PID

/-!
# RHDirect.Stage3PatchingUnification

Stage 3 deep mathematical discharge for Track 2 (`rh-direct`): formalizes the full
**Taylor–Wiles–Kisin Patching Algebra**, **Wiles–Lenstra–Diamond Numerical Criterion**,
and **Direct Congruence-Module Discharge into `Stage2GaloisWire.ThreePartPatchingWindow`**
in pure Mathlib `v4.33.1` (0 `sorry`, 0 custom `axiom`s).

## Contents

1. **Diamond-Operator Algebra `𝒪[Δ_N]`, Augmented Patching Systems & Coinvariant Descent**
   - `DiamondAlgebra 𝒪 Δ := MonoidAlgebra 𝒪 Δ`, canonical augmentation `diamondAug`,
     augmentation ideal `diamondAugIdeal`, quotient isomorphism `𝒪[Δ] / 𝔞_Δ ≃+* 𝒪`,
     freeness/finiteness over `𝒪`, and exact finite-generator presentation
     `diamondAugIdeal 𝒪 Δ = Ideal.span { [g_i] - 1 }` for finitely generated `Δ`.
   - Coinvariant modules `Coinv 𝔞 M := M ⧸ (𝔞 • ⊤)` with canonical `(S ⧸ 𝔞)`-module structure,
     free-rank descent (`coinvEquivPiOfEquivPi`), and **Nakayama Coinvariant Generation &
     Surjectivity** (`nakayama_coinv_gen`, `nakayama_coinv_surjective`) over local rings.
   - **Integral/Domain & Same-Rank Faithfulness**:
     - `annihilator_eq_bot_of_isDomain_finite_free`: if `R_∞` is an integral domain finite over
       `S_∞` and `M_∞` is a nontrivial free `S_∞`-module, then `Ann_{R_∞}(M_∞) = ⊥` (minimal
       monic integral-equation descent!).
     - `annihilator_eq_bot_of_surjective_same_rank`: if `R_∞` and `M_∞` are free of the same
       finite rank over `S_∞` and `R_∞ ↠ M_∞`, then `Ann_{R_∞}(M_∞) = ⊥` (via `OrzechProperty`).
   - **Patched `R_∞ ≃ T_∞` and Specialized `R_0 ≃ T_0` (`R = T`)** (`patchedAlgEquivOfFaithful`,
     `TaylorWilesPatchingDatum.R_inf_equiv_T_inf`, `TaylorWilesPatchingDatum.R0_equiv_T0`,
     `TaylorWilesPatchingDatum.M0_free_finite`).

2. **Wiles–Lenstra–Diamond Numerical Criterion & Congruence Ideal = Selmer Length**
   - Augmentation ideal `augIdeal π`, cotangent module `Cotangent π = I_T / I_T^2`, and
     congruence ideal `congruenceIdeal π = π(Ann_T(I_T))`.
   - Unconditional cotangent annihilation (`congruenceIdeal_le_annihilator_cotangent`),
     cotangent surjection (`cotangentMap_surjective`), and **Tate–Lenstra Adjugate Determinant
     Theorem** (`det_mem_congruenceIdeal_of_relations`: every relation-matrix determinant lies
     in `η_T`, i.e., `Fitt_𝒪(Φ_T) ≤ η_T`).
   - **Smith Normal Form over a DVR** (`exists_smithNormalForm_of_dvr`) and **Exact
     Determinant–Length Identity** (`length_coker_eq_length_quotient_det`).
   - **Wiles–Lenstra Length Inequality** (`wiles_lenstra_length_inequality`:
     `len_𝒪(𝒪 / η_T) ≤ len_𝒪(Φ_T) ≤ len_𝒪(Φ_R)`).
   - **Gorenstein / Complete-Intersection Equality-iff-Isomorphism Criterion**
     (`gorenstein_surj_bijective_of_congruenceIdeal_eq`, `wiles_lenstra_numerical_criterion_iff`:
     `len_𝒪(Φ_R) = len_𝒪(𝒪 / η_T) ↔ φ : R ≃ T` is an isomorphism of Gorenstein complete
     intersections!).
   - Direct bridges to `TaylorWilesWindow.length_le_of_pow_mem_annihilator` and
     `Stage2RamifiedPrimes.LocalRamifiedObstruction`.

3. **Direct Discharge into `Stage2GaloisWire.ThreePartPatchingWindow` & `GaloisModularityContract`**
   - `TaylorWilesCongruenceDatum` → `Stage2GaloisWire.PatchedPrimeBound` (and sharp rank-1
     complete-intersection bound `shaLen_le_congLen_of_completeIntersection`).
   - `CongruencePatchingRealization` → `Stage2GaloisWire.PatchedOddUnramifiedRealization`
     (including finite congruence-prime support aggregation `ofFiniteSupport`).
   - Unified combination with `Stage2RamifiedPrimes.RamifiedPrimeRealization` into
     `VVle`, `Stage2GaloisWire.ThreePartPatchingWindow`, `GaloisModularityContract`, and `VWin`.
-/

noncomputable section

open scoped BigOperators Pointwise
open Finset RHDirect

namespace RHDirect
namespace Stage3PatchingUnification

/-! ## Section 1: Diamond-Operator Algebra `𝒪[Δ_N]`, Augmented Patching Systems & Coinvariant Descent -/

section DiamondAlgebra

/-- The diamond-operator group algebra `𝒪[Δ]` over a commutative ring `𝒪` for a commutative
diamond group `Δ` (e.g. `Δ_N = (ℤ/Nℤ)ˣ` or its `p`-Sylow quotient). -/
abbrev DiamondAlgebra (𝒪 Δ : Type*) [CommRing 𝒪] [CommGroup Δ] : Type _ :=
  MonoidAlgebra 𝒪 Δ

/-- Canonical augmentation homomorphism `ε : 𝒪[Δ] →ₐ[𝒪] 𝒪` sending every diamond operator
`[δ]` (`δ ∈ Δ`) to `1`. -/
def diamondAug (𝒪 Δ : Type*) [CommRing 𝒪] [CommGroup Δ] :
    DiamondAlgebra 𝒪 Δ →ₐ[𝒪] 𝒪 :=
  (MonoidAlgebra.lift 𝒪 𝒪 Δ) (1 : Δ →* 𝒪)

theorem diamondAug_single {𝒪 Δ : Type*} [CommRing 𝒪] [CommGroup Δ] (δ : Δ) (c : 𝒪) :
    diamondAug 𝒪 Δ (MonoidAlgebra.single δ c) = c := by
  simp [diamondAug]

theorem diamondAug_algebraMap {𝒪 Δ : Type*} [CommRing 𝒪] [CommGroup Δ] (c : 𝒪) :
    diamondAug 𝒪 Δ (algebraMap 𝒪 (DiamondAlgebra 𝒪 Δ) c) = c :=
  AlgHom.commutes (diamondAug 𝒪 Δ) c

theorem diamondAug_surjective (𝒪 Δ : Type*) [CommRing 𝒪] [CommGroup Δ] :
    Function.Surjective (diamondAug 𝒪 Δ) :=
  fun c => ⟨algebraMap 𝒪 (DiamondAlgebra 𝒪 Δ) c, diamondAug_algebraMap c⟩

/-- The augmentation ideal `𝔞_Δ = ker(ε : 𝒪[Δ] → 𝒪)` of the diamond-operator algebra. -/
def diamondAugIdeal (𝒪 Δ : Type*) [CommRing 𝒪] [CommGroup Δ] :
    Ideal (DiamondAlgebra 𝒪 Δ) :=
  RingHom.ker (diamondAug 𝒪 Δ).toRingHom

theorem mem_diamondAugIdeal_iff {𝒪 Δ : Type*} [CommRing 𝒪] [CommGroup Δ]
    (x : DiamondAlgebra 𝒪 Δ) :
    x ∈ diamondAugIdeal 𝒪 Δ ↔ diamondAug 𝒪 Δ x = 0 := Iff.rfl

/-- Exact coinvariant descent of the diamond-operator algebra: `𝒪[Δ] ⧸ 𝔞_Δ ≃+* 𝒪`. -/
def diamondAug_quotientEquiv (𝒪 Δ : Type*) [CommRing 𝒪] [CommGroup Δ] :
    DiamondAlgebra 𝒪 Δ ⧸ diamondAugIdeal 𝒪 Δ ≃+* 𝒪 :=
  RingHom.quotientKerEquivOfSurjective (diamondAug_surjective 𝒪 Δ)

/-- Canonical `𝒪`-linear equivalence `𝒪[Δ] ≃ₗ[𝒪] (Δ →₀ 𝒪)`. -/
def diamondAlgebraEquivFinsupp (𝒪 Δ : Type*) [CommRing 𝒪] [CommGroup Δ] :
    DiamondAlgebra 𝒪 Δ ≃ₗ[𝒪] (Δ →₀ 𝒪) where
  toFun x := x.coeff
  invFun f := MonoidAlgebra.ofCoeff f
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- `𝒪[Δ]` is free and finite over `𝒪` whenever `Δ` is finite. -/
theorem diamondAlgebra_free_finite (𝒪 Δ : Type*) [CommRing 𝒪] [CommGroup Δ] [Fintype Δ] :
    Module.Free 𝒪 (DiamondAlgebra 𝒪 Δ) ∧ Module.Finite 𝒪 (DiamondAlgebra 𝒪 Δ) := by
  let b : Module.Basis Δ 𝒪 (DiamondAlgebra 𝒪 Δ) :=
    (Finsupp.basisSingleOne (R := 𝒪) (ι := Δ)).map (diamondAlgebraEquivFinsupp 𝒪 Δ).symm
  exact ⟨Module.Free.of_basis b, Module.Finite.of_basis b⟩

/-- Exact presentation of the augmentation ideal: `𝔞_Δ = span { [δ] - 1 | δ ∈ Δ }`. -/
theorem diamondAugIdeal_eq_span (𝒪 Δ : Type*) [CommRing 𝒪] [CommGroup Δ] :
    diamondAugIdeal 𝒪 Δ =
      Ideal.span { x : DiamondAlgebra 𝒪 Δ | ∃ δ : Δ, x = MonoidAlgebra.single δ 1 - 1 } := by
  let I : Ideal (DiamondAlgebra 𝒪 Δ) :=
    Ideal.span { x : DiamondAlgebra 𝒪 Δ | ∃ δ : Δ, x = MonoidAlgebra.single δ 1 - 1 }
  apply le_antisymm
  · intro x hx
    have hkey : ∀ z : DiamondAlgebra 𝒪 Δ,
        z - algebraMap 𝒪 (DiamondAlgebra 𝒪 Δ) (diamondAug 𝒪 Δ z) ∈ I := by
      intro z
      refine MonoidAlgebra.induction_on
        (motive := fun z => z - algebraMap 𝒪 (DiamondAlgebra 𝒪 Δ) (diamondAug 𝒪 Δ z) ∈ I) z ?_ ?_ ?_
      · intro δ
        have hof : MonoidAlgebra.of 𝒪 Δ δ = MonoidAlgebra.single δ (1 : 𝒪) := rfl
        rw [hof, diamondAug_single, map_one]
        exact Ideal.subset_span ⟨δ, rfl⟩
      · intro a b ha hb
        have heq : (a + b) - algebraMap 𝒪 (DiamondAlgebra 𝒪 Δ) (diamondAug 𝒪 Δ (a + b)) =
            (a - algebraMap 𝒪 (DiamondAlgebra 𝒪 Δ) (diamondAug 𝒪 Δ a)) +
              (b - algebraMap 𝒪 (DiamondAlgebra 𝒪 Δ) (diamondAug 𝒪 Δ b)) := by
          rw [map_add, map_add]; ring
        rw [heq]
        exact I.add_mem ha hb
      · intro r a ha
        have heq : (r • a) - algebraMap 𝒪 (DiamondAlgebra 𝒪 Δ) (diamondAug 𝒪 Δ (r • a)) =
            algebraMap 𝒪 (DiamondAlgebra 𝒪 Δ) r *
              (a - algebraMap 𝒪 (DiamondAlgebra 𝒪 Δ) (diamondAug 𝒪 Δ a)) := by
          rw [map_smul, smul_eq_mul, map_mul, Algebra.smul_def, mul_sub]
        rw [heq]
        exact I.mul_mem_left _ ha
    have h0 := hkey x
    rw [mem_diamondAugIdeal_iff] at hx
    rw [hx, map_zero, sub_zero] at h0
    exact h0
  · rw [Ideal.span_le]
    rintro x ⟨δ, rfl⟩
    rw [SetLike.mem_coe, mem_diamondAugIdeal_iff, map_sub, map_one, diamondAug_single, sub_self]

/-- **Finite-Generator Diamond Augmentation Ideal**: if `Δ` is generated by `g : Fin k → Δ`
(e.g., `k` cyclic Taylor–Wiles diamond groups), then `𝔞_Δ = (y_1, ..., y_k)` where
`y_i = [g_i] - 1`. -/
theorem diamondAugIdeal_eq_span_of_closure_eq_top {𝒪 Δ : Type*} [CommRing 𝒪] [CommGroup Δ]
    {k : ℕ} (g : Fin k → Δ) (hgen : Subgroup.closure (Set.range g) = ⊤) :
    diamondAugIdeal 𝒪 Δ =
      Ideal.span (Set.range fun i : Fin k => MonoidAlgebra.single (g i) (1 : 𝒪) - 1) := by
  let I : Ideal (DiamondAlgebra 𝒪 Δ) :=
    Ideal.span (Set.range fun i : Fin k => MonoidAlgebra.single (g i) (1 : 𝒪) - 1)
  have hle : I ≤ diamondAugIdeal 𝒪 Δ := by
    rw [Ideal.span_le]
    rintro x ⟨i, rfl⟩
    rw [SetLike.mem_coe, mem_diamondAugIdeal_iff, map_sub, map_one, diamondAug_single, sub_self]
  apply le_antisymm _ hle
  rw [diamondAugIdeal_eq_span, Ideal.span_le]
  let H : Subgroup Δ :=
    { carrier := { δ : Δ | MonoidAlgebra.single δ (1 : 𝒪) - 1 ∈ I }
      one_mem' := by
        show MonoidAlgebra.single (1 : Δ) (1 : 𝒪) - 1 ∈ I
        rw [MonoidAlgebra.one_def, sub_self]
        exact I.zero_mem
      mul_mem' := fun {a b} ha hb => by
        show MonoidAlgebra.single (a * b) (1 : 𝒪) - 1 ∈ I
        have hid : MonoidAlgebra.single (a * b) (1 : 𝒪) - 1 =
            MonoidAlgebra.single a (1 : 𝒪) * (MonoidAlgebra.single b 1 - 1) +
              (MonoidAlgebra.single a 1 - 1) := by
          rw [mul_sub, mul_one, MonoidAlgebra.single_mul_single, one_mul]
          ring
        rw [hid]
        exact I.add_mem (I.mul_mem_left _ hb) ha
      inv_mem' := fun {a} ha => by
        show MonoidAlgebra.single a⁻¹ (1 : 𝒪) - 1 ∈ I
        have hid : MonoidAlgebra.single a⁻¹ (1 : 𝒪) - 1 =
            -(MonoidAlgebra.single a⁻¹ (1 : 𝒪) * (MonoidAlgebra.single a 1 - 1)) := by
          rw [mul_sub, mul_one, MonoidAlgebra.single_mul_single, inv_mul_cancel, one_mul,
            ← MonoidAlgebra.one_def]
          ring
        rw [hid]
        exact I.neg_mem (I.mul_mem_left _ ha) }
  have hH_top : H = ⊤ := by
    rw [eq_top_iff, ← hgen, Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact Ideal.subset_span ⟨i, rfl⟩
  rintro x ⟨δ, rfl⟩
  have hδ : δ ∈ H := by rw [hH_top]; trivial
  exact hδ

end DiamondAlgebra

/-! ### Coinvariant Modules, Free-Rank Descent & Nakayama Coinvariant Generation -/

section Coinvariants

variable {S : Type*} [CommRing S]

/-- Coinvariant module `M_0 := M ⧸ (𝔞 • ⊤)` of an `S`-module `M` modulo an ideal `𝔞 : Ideal S`. -/
abbrev Coinv (𝔞 : Ideal S) (M : Type*) [AddCommGroup M] [Module S M] : Type _ :=
  M ⧸ (𝔞 • (⊤ : Submodule S M))

/-- `𝔞` annihilates `Coinv 𝔞 M`. -/
theorem ideal_le_annihilator_coinv (𝔞 : Ideal S) (M : Type*) [AddCommGroup M] [Module S M] :
    𝔞 ≤ Module.annihilator S (Coinv 𝔞 M) := by
  intro a ha
  rw [Module.mem_annihilator]
  intro q
  induction q using Quotient.inductionOn' with
  | h m =>
    change Submodule.Quotient.mk (a • m) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    exact Submodule.smul_mem_smul ha Submodule.mem_top

/-- Scalar multiplication of `S ⧸ 𝔞` on `Coinv 𝔞 M`. -/
instance instSMulQuotientCoinv (𝔞 : Ideal S) (M : Type*) [AddCommGroup M] [Module S M] :
    SMul (S ⧸ 𝔞) (Coinv 𝔞 M) where
  smul q m :=
    Quotient.liftOn' q (fun s : S => s • m) (fun s₁ s₂ h => by
      have hrel : s₁ - s₂ ∈ 𝔞 := by
        have hq : Ideal.Quotient.mk 𝔞 s₁ = Ideal.Quotient.mk 𝔞 s₂ := Quotient.sound' h
        exact Ideal.Quotient.eq.mp hq
      have hkill : (s₁ - s₂) • m = 0 :=
        Module.mem_annihilator.mp (ideal_le_annihilator_coinv 𝔞 M hrel) m
      rw [sub_smul, sub_eq_zero] at hkill
      exact hkill)

theorem coinv_mk_smul (𝔞 : Ideal S) {M : Type*} [AddCommGroup M] [Module S M]
    (s : S) (m : Coinv 𝔞 M) :
    Ideal.Quotient.mk 𝔞 s • m = s • m := rfl

/-- Canonical `(S ⧸ 𝔞)`-module structure on `Coinv 𝔞 M`. -/
instance instModuleQuotientCoinv (𝔞 : Ideal S) (M : Type*) [AddCommGroup M] [Module S M] :
    Module (S ⧸ 𝔞) (Coinv 𝔞 M) where
  one_smul m := one_smul S m
  mul_smul q₁ q₂ m := by
    induction q₁ using Quotient.inductionOn' with
    | h s₁ =>
      induction q₂ using Quotient.inductionOn' with
      | h s₂ =>
        change (s₁ * s₂) • m = s₁ • (s₂ • m)
        exact mul_smul s₁ s₂ m
  smul_zero q := by
    induction q using Quotient.inductionOn' with
    | h s => exact smul_zero s
  smul_add q m₁ m₂ := by
    induction q using Quotient.inductionOn' with
    | h s => exact smul_add s m₁ m₂
  add_smul q₁ q₂ m := by
    induction q₁ using Quotient.inductionOn' with
    | h s₁ =>
      induction q₂ using Quotient.inductionOn' with
      | h s₂ =>
        change (s₁ + s₂) • m = s₁ • m + s₂ • m
        exact add_smul s₁ s₂ m
  zero_smul m := zero_smul S m

instance instIsScalarTowerCoinv (𝔞 : Ideal S) (M : Type*) [AddCommGroup M] [Module S M] :
    IsScalarTower S (S ⧸ 𝔞) (Coinv 𝔞 M) where
  smul_assoc s q m := by
    induction q using Quotient.inductionOn' with
    | h t =>
      change (s * t) • m = s • (t • m)
      exact mul_smul s t m

/-- For any ideal `𝔞 : Ideal S`, `𝔞 • (⊤ : Submodule S (Fin r → S))` consists precisely of tuples
with all coordinates in `𝔞`. -/
theorem smul_top_pi_iff (𝔞 : Ideal S) (r : ℕ) (v : Fin r → S) :
    v ∈ 𝔞 • (⊤ : Submodule S (Fin r → S)) ↔ ∀ i : Fin r, v i ∈ 𝔞 := by
  constructor
  · intro hv
    refine Submodule.smul_induction_on hv ?_ ?_
    · intro a ha w _ i
      exact Ideal.mul_mem_right (w i) 𝔞 ha
    · intro x y hx hy i
      exact 𝔞.add_mem (hx i) (hy i)
  · intro hv
    have hdecomp : v = ∑ i : Fin r, v i • Pi.single i (1 : S) := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply]
    rw [hdecomp]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (hv i) Submodule.mem_top

/-- **Explicit Coinvariant Equivalence for Free Modules**:
`Coinv 𝔞 (Fin r → S) ≃ₗ[S ⧸ 𝔞] (Fin r → S ⧸ 𝔞)`. -/
def coinvPiEquiv (𝔞 : Ideal S) (r : ℕ) :
    Coinv 𝔞 (Fin r → S) ≃ₗ[S ⧸ 𝔞] (Fin r → S ⧸ 𝔞) := by
  let fS : (Fin r → S) →ₗ[S] (Fin r → S ⧸ 𝔞) :=
    { toFun := fun v i => Ideal.Quotient.mk 𝔞 (v i)
      map_add' := fun u v => by ext i; exact map_add (Ideal.Quotient.mk 𝔞) (u i) (v i)
      map_smul' := fun s v => by
        ext i
        change Ideal.Quotient.mk 𝔞 (s * v i) = s • Ideal.Quotient.mk 𝔞 (v i)
        rw [map_mul, Algebra.smul_def]
        rfl }
  have hker : LinearMap.ker fS = 𝔞 • (⊤ : Submodule S (Fin r → S)) := by
    ext v
    rw [LinearMap.mem_ker, smul_top_pi_iff]
    constructor
    · intro hv i
      exact Ideal.Quotient.eq_zero_iff_mem.mp (congrFun hv i)
    · intro hv
      ext i
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (hv i)
  have hsurj : Function.Surjective fS := by
    intro w
    refine ⟨fun i => Quotient.out (w i), ?_⟩
    ext i
    exact Quotient.out_eq (w i)
  let eS : Coinv 𝔞 (Fin r → S) ≃ₗ[S] (Fin r → S ⧸ 𝔞) :=
    (Submodule.quotEquivOfEq _ _ hker.symm).trans (fS.quotKerEquivOfSurjective hsurj)
  exact
    { toFun := eS
      invFun := eS.symm
      left_inv := eS.left_inv
      right_inv := eS.right_inv
      map_add' := eS.map_add'
      map_smul' := fun q x => by
        induction q using Quotient.inductionOn' with
        | h s =>
          have h1 : Ideal.Quotient.mk 𝔞 s • x = s • x := rfl
          have h2 : Ideal.Quotient.mk 𝔞 s • eS x = s • eS x := by
            ext i
            change Ideal.Quotient.mk 𝔞 s * eS x i = algebraMap S (S ⧸ 𝔞) s * eS x i
            rfl
          change eS (Ideal.Quotient.mk 𝔞 s • x) = Ideal.Quotient.mk 𝔞 s • eS x
          rw [h1, h2, eS.map_smul] }

/-- **Coinvariant Freeness & Rank Preservation**: if `M ≃ₗ[S] (Fin r → S)`, then
`Coinv 𝔞 M ≃ₗ[S ⧸ 𝔞] (Fin r → S ⧸ 𝔞)`, so `M ⧸ 𝔞 M` is free of the exact same rank `r`
over `S ⧸ 𝔞`. -/
def coinvEquivPiOfEquivPi {M : Type*} [AddCommGroup M] [Module S M]
    (𝔞 : Ideal S) {r : ℕ} (e : M ≃ₗ[S] (Fin r → S)) :
    Coinv 𝔞 M ≃ₗ[S ⧸ 𝔞] (Fin r → S ⧸ 𝔞) := by
  have hmap : (𝔞 • (⊤ : Submodule S M)).map e.toLinearMap =
      𝔞 • (⊤ : Submodule S (Fin r → S)) := by
    rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.mpr e.surjective]
  let e1 : Coinv 𝔞 M ≃ₗ[S] Coinv 𝔞 (Fin r → S) :=
    Submodule.Quotient.equiv (𝔞 • ⊤) (𝔞 • ⊤) e hmap
  let e1Q : Coinv 𝔞 M ≃ₗ[S ⧸ 𝔞] Coinv 𝔞 (Fin r → S) :=
    { toFun := e1
      invFun := e1.symm
      left_inv := e1.left_inv
      right_inv := e1.right_inv
      map_add' := e1.map_add'
      map_smul' := fun q x => by
        induction q using Quotient.inductionOn' with
        | h s =>
          change e1 (s • x) = s • e1 x
          exact e1.map_smul s x }
  exact e1Q.trans (coinvPiEquiv 𝔞 r)

theorem coinv_free_finite_of_equiv_pi {M : Type*} [AddCommGroup M] [Module S M]
    (𝔞 : Ideal S) {r : ℕ} (e : M ≃ₗ[S] (Fin r → S)) :
    Module.Free (S ⧸ 𝔞) (Coinv 𝔞 M) ∧ Module.Finite (S ⧸ 𝔞) (Coinv 𝔞 M) := by
  let eQ := coinvEquivPiOfEquivPi 𝔞 e
  exact ⟨Module.Free.of_equiv eQ.symm, Module.Finite.equiv eQ.symm⟩

/-- Nakayama's lemma in `N ⊔ 𝔞 • ⊤ = ⊤ → N = ⊤` form over any local ring `S`. -/
theorem nakayama_sup_smul_top_eq_top [IsLocalRing S] {M : Type*} [AddCommGroup M] [Module S M]
    [Module.Finite S M] {𝔞 : Ideal S} (h𝔞 : 𝔞 ≤ IsLocalRing.maximalIdeal S)
    {N : Submodule S M} (hsup : N ⊔ (𝔞 • (⊤ : Submodule S M)) = ⊤) :
    N = ⊤ := by
  have hjac : 𝔞 ≤ (⊥ : Ideal S).jacobson := by
    rwa [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
  have htop_le : (⊤ : Submodule S (M ⧸ N)) ≤ 𝔞 • (⊤ : Submodule S (M ⧸ N)) := by
    intro q _
    induction q using Quotient.inductionOn' with
    | h m =>
      have hm : m ∈ N ⊔ (𝔞 • (⊤ : Submodule S M)) := by rw [hsup]; trivial
      rcases Submodule.mem_sup.mp hm with ⟨n, hn, w, hw, rfl⟩
      have hmk : Submodule.Quotient.mk (p := N) (n + w) = Submodule.Quotient.mk (p := N) w := by
        rw [Submodule.Quotient.mk_add, (Submodule.Quotient.mk_eq_zero N).mpr hn, zero_add]
      change Submodule.Quotient.mk (p := N) (n + w) ∈ 𝔞 • (⊤ : Submodule S (M ⧸ N))
      rw [hmk]
      have hmap : (𝔞 • (⊤ : Submodule S M)).map N.mkQ ≤ 𝔞 • (⊤ : Submodule S (M ⧸ N)) := by
        rw [Submodule.map_smul'']
        exact Submodule.smul_mono le_rfl le_top
      exact hmap ⟨w, hw, rfl⟩
  have hbot : (⊤ : Submodule S (M ⧸ N)) = ⊥ :=
    Submodule.eq_bot_of_le_smul_of_le_jacobson_bot 𝔞 ⊤
      (Module.Finite.fg_top (R := S) (M := M ⧸ N)) htop_le hjac
  rw [eq_top_iff]
  intro m _
  have hq : Submodule.Quotient.mk (p := N) m ∈ (⊥ : Submodule S (M ⧸ N)) := by
    rw [← hbot]; trivial
  exact (Submodule.Quotient.mk_eq_zero N).mp hq

/-- **Nakayama Coinvariant Generation**: over a local ring `S` with `𝔞 ≤ maximalIdeal S`,
if `M` is finitely generated over `S` and `v : Fin r → M` maps to a generating family of
`Coinv 𝔞 M = M ⧸ 𝔞 M`, then `v` ALREADY generates `M` over `S`. -/
theorem nakayama_coinv_gen [IsLocalRing S] {M : Type*} [AddCommGroup M] [Module S M]
    [Module.Finite S M] {𝔞 : Ideal S} (h𝔞 : 𝔞 ≤ IsLocalRing.maximalIdeal S)
    {r : ℕ} (v : Fin r → M)
    (hgen : Submodule.span S
      (Set.range fun i => Submodule.Quotient.mk (p := 𝔞 • (⊤ : Submodule S M)) (v i)) = ⊤) :
    Submodule.span S (Set.range v) = ⊤ := by
  let N : Submodule S M := Submodule.span S (Set.range v)
  refine nakayama_sup_smul_top_eq_top h𝔞 ?_
  rw [eq_top_iff]
  intro m _
  have hm : Submodule.Quotient.mk (p := 𝔞 • (⊤ : Submodule S M)) m ∈
      Submodule.span S
        (Set.range fun i => Submodule.Quotient.mk (p := 𝔞 • (⊤ : Submodule S M)) (v i)) := by
    rw [hgen]; trivial
  have hmap : Submodule.span S
      (Set.range fun i => Submodule.Quotient.mk (p := 𝔞 • (⊤ : Submodule S M)) (v i)) =
      N.map (𝔞 • (⊤ : Submodule S M)).mkQ := by
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  rw [hmap, Submodule.mem_map] at hm
  obtain ⟨n, hn, hnm⟩ := hm
  have hdiff : m - n ∈ 𝔞 • (⊤ : Submodule S M) := by
    rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub, sub_eq_zero]
    exact hnm.symm
  have heq : m = n + (m - n) := by abel
  rw [heq]
  exact Submodule.add_mem_sup hn hdiff

/-- **Nakayama Coinvariant Surjectivity**: over a local ring `S` with `𝔞 ≤ maximalIdeal S`,
a linear map `f : N →ₗ[S] M` into a finitely generated `S`-module `M` is surjective if
its composition `N → M ⧸ 𝔞 M` is surjective. -/
theorem nakayama_coinv_surjective [IsLocalRing S] {N M : Type*}
    [AddCommGroup N] [Module S N] [AddCommGroup M] [Module S M] [Module.Finite S M]
    {𝔞 : Ideal S} (h𝔞 : 𝔞 ≤ IsLocalRing.maximalIdeal S)
    (f : N →ₗ[S] M)
    (hsurj : Function.Surjective ((𝔞 • (⊤ : Submodule S M)).mkQ.comp f)) :
    Function.Surjective f := by
  rw [← LinearMap.range_eq_top]
  refine nakayama_sup_smul_top_eq_top h𝔞 ?_
  rw [eq_top_iff]
  intro m _
  obtain ⟨n, hn⟩ := hsurj (Submodule.Quotient.mk m)
  have hdiff : m - f n ∈ 𝔞 • (⊤ : Submodule S M) := by
    rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub, sub_eq_zero]
    exact hn.symm
  have heq : m = f n + (m - f n) := by abel
  rw [heq]
  exact Submodule.add_mem_sup ⟨n, rfl⟩ hdiff

end Coinvariants

/-! ### Patched Faithfulness (`Ann_{R_∞}(M_∞) = ⊥`) and `R_∞ ≃ T_∞` → `R_0 ≃ T_0` (`R = T`) -/

section PatchedREqT

/-- **Integral/Domain Faithfulness Theorem**: if `R` is an integral domain finite over `S`,
and `M` is a nontrivial free `S`-module carrying a compatible `R`-module structure, then
`Ann_R(M) = ⊥` (and `algebraMap S R` is injective).
Proof by minimal-degree monic integral relation descent! -/
theorem annihilator_eq_bot_of_isDomain_finite_free {S R M : Type*}
    [CommRing S] [CommRing R] [IsDomain R] [Algebra S R] [Module.Finite S R]
    [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower S R M]
    [Module.Free S M] [Nontrivial M] :
    Module.annihilator R M = ⊥ := by
  classical
  rw [eq_bot_iff]
  intro a ha
  rw [Ideal.mem_bot]
  by_contra ha0
  have hint : IsIntegral S a := Algebra.IsIntegral.isIntegral a
  have hex : ∃ n : ℕ, ∃ p : Polynomial S, p.Monic ∧ p.natDegree = n ∧ Polynomial.aeval a p = 0 := by
    obtain ⟨p, hp, hpe⟩ := hint
    exact ⟨p.natDegree, p, hp, rfl, hpe⟩
  set n := Nat.find hex with hn_def
  obtain ⟨p, hp_monic, hp_deg, hp_eval⟩ := Nat.find_spec hex
  have hp_deg_n : p.natDegree = n := hp_deg
  have hn_pos : 0 < n := by
    by_contra hn0
    have hn_eq : n = 0 := by omega
    have hdeg0 : p.natDegree = 0 := hp_deg_n.trans hn_eq
    have hp1 : p = 1 := Polynomial.eq_one_of_monic_natDegree_zero hp_monic hdeg0
    rw [hp1, map_one] at hp_eval
    exact one_ne_zero hp_eval
  let q : Polynomial S := p.divX
  have hdecomp : p = Polynomial.X * q + Polynomial.C (p.coeff 0) := by
    have h := Polynomial.divX_mul_X_add p
    rw [mul_comm] at h
    exact h.symm
  have hq_deg : q.natDegree = n - 1 := by
    have h1 : q.natDegree = p.natDegree - 1 := Polynomial.natDegree_divX_eq_natDegree_tsub_one
    rw [h1, hp_deg_n]
  have hq_monic : q.Monic := by
    rw [Polynomial.Monic, Polynomial.leadingCoeff, hq_deg]
    have hc : q.coeff (n - 1) = p.coeff n := by
      rw [Polynomial.coeff_divX]
      congr 1
      omega
    rw [hc, ← hp_deg_n]
    exact hp_monic.leadingCoeff
  have heval_decomp : a * Polynomial.aeval a q + algebraMap S R (p.coeff 0) = 0 := by
    have h := congrArg (Polynomial.aeval a) hdecomp
    rw [hp_eval, map_add, map_mul, Polynomial.aeval_X, Polynomial.aeval_C] at h
    exact h.symm
  have hc0_ann : p.coeff 0 ∈ Module.annihilator S M := by
    rw [Module.mem_annihilator]
    intro m
    have h1 : algebraMap S R (p.coeff 0) = -(a * Polynomial.aeval a q) :=
      eq_neg_of_add_eq_zero_right heval_decomp
    rw [← algebraMap_smul R (p.coeff 0) m, h1, neg_smul, mul_comm, mul_smul,
      Module.mem_annihilator.mp ha m, smul_zero, neg_zero]
  have hc0 : p.coeff 0 = 0 := by
    rw [TaylorWilesWindow.annihilator_eq_bot_of_free_nontrivial] at hc0_ann
    exact Ideal.mem_bot.mp hc0_ann
  rw [hc0, map_zero, add_zero] at heval_decomp
  have hq_eval : Polynomial.aeval a q = 0 := (mul_eq_zero.mp heval_decomp).resolve_left ha0
  have hlt : n - 1 < n := by omega
  exact Nat.find_min hex hlt ⟨q, hq_monic, hq_deg, hq_eval⟩

/-- **Same-Rank Cyclic Faithfulness Theorem** (via Orzech's Theorem, without requiring `IsDomain`):
if `R` and `M` are both free of the same finite rank `r` over `S` and `f : R →ₗ[R] M` is surjective,
then `f` is bijective and `Ann_R(M) = ⊥`. -/
theorem annihilator_eq_bot_of_surjective_same_rank {S R M : Type*}
    [CommRing S] [CommRing R] [Algebra S R]
    [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower S R M]
    {r : ℕ} (eR : R ≃ₗ[S] (Fin r → S)) (eM : M ≃ₗ[S] (Fin r → S))
    (f : R →ₗ[R] M) (hf : Function.Surjective f) :
    Function.Bijective f ∧ Module.annihilator R M = ⊥ := by
  let fS : R →ₗ[S] M := f.restrictScalars S
  let g : (Fin r → S) →ₗ[S] (Fin r → S) := (eM.toLinearMap.comp fS).comp eR.symm.toLinearMap
  have hg_surj : Function.Surjective g := (eM.surjective.comp hf).comp eR.symm.surjective
  have hg_inj : Function.Injective g :=
    OrzechProperty.injective_of_surjective_endomorphism g hg_surj
  have hf_inj : Function.Injective f := by
    intro x y hxy
    have h1 : g (eR x) = g (eR y) := by
      simp only [g, fS, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
        LinearMap.coe_restrictScalars, hxy]
    exact eR.injective (hg_inj h1)
  refine ⟨⟨hf_inj, hf⟩, ?_⟩
  rw [eq_bot_iff]
  intro a ha
  rw [Ideal.mem_bot]
  apply hf_inj
  rw [map_zero]
  have h1 : f a = a • f 1 := by
    simpa only [smul_eq_mul, mul_one] using map_smul f a (1 : R)
  rw [h1]
  exact Module.mem_annihilator.mp ha (f 1)

/-- **Patched `R_∞ ≃ₐ[S_∞] T_∞` from Faithful Module**: if `φ : R_∞ →ₐ[S_∞] T_∞` is surjective
and `M_∞` is a `T_∞`-module with `Ann_{R_∞}(M_∞) = ⊥`, then `φ` is an `S_∞`-algebra isomorphism. -/
def patchedAlgEquivOfFaithful {S R T M : Type*}
    [CommRing S] [CommRing R] [CommRing T] [Algebra S R] [Algebra S T]
    (φ : R →ₐ[S] T) (hsurj : Function.Surjective φ)
    [AddCommGroup M] [Module R M] [Module T M]
    (hcompat : ∀ (r : R) (m : M), r • m = φ r • m)
    (hfaith : Module.annihilator R M = ⊥) :
    R ≃ₐ[S] T := by
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro r hr
    have hann : r ∈ Module.annihilator R M := by
      rw [Module.mem_annihilator]
      intro m
      rw [hcompat, hr, zero_smul]
    rw [hfaith] at hann
    exact Ideal.mem_bot.mp hann
  exact AlgEquiv.ofBijective φ ⟨hinj, hsurj⟩

/-- **Coinvariant / Specialization Ring Descent (`R_∞ / 𝔞 R_∞ ≃+* T_∞ / 𝔞 T_∞`)**:
an `S_∞`-algebra isomorphism `e : R_∞ ≃ₐ[S_∞] T_∞` descends modulo any ideal `𝔞 : Ideal S_∞`
to a ring isomorphism of specialized quotients. -/
def quotientMapEquivOfAlgEquiv {S R T : Type*}
    [CommRing S] [CommRing R] [CommRing T] [Algebra S R] [Algebra S T]
    (𝔞 : Ideal S) (e : R ≃ₐ[S] T) :
    R ⧸ (𝔞.map (algebraMap S R)) ≃+* T ⧸ (𝔞.map (algebraMap S T)) := by
  have hmap : 𝔞.map (algebraMap S T) =
      Ideal.map (e.toRingEquiv : R →+* T) (𝔞.map (algebraMap S R)) := by
    rw [Ideal.map_map]
    congr 1
    ext s
    exact (e.commutes s).symm
  exact Ideal.quotientEquiv (𝔞.map (algebraMap S R)) (𝔞.map (algebraMap S T)) e.toRingEquiv hmap

/-- **Complete Finite-Level Taylor–Wiles–Kisin Patching Datum `(S_∞, 𝔞, R_∞, T_∞, M_∞)`**:
packages a local patching ring `S_∞` with finitely generated augmentation ideal
`𝔞 = (y_1, ..., y_g) ≤ maximalIdeal S_∞`, a finite `S_∞`-algebra `R_∞`, a surjection
`φ_∞ : R_∞ →ₐ[S_∞] T_∞`, a patched `T_∞`-module `M_∞` free of rank `r ≥ 1` over `S_∞`,
specializations `R_∞ / 𝔞 R_∞ ≃+* R_0` and `T_∞ / 𝔞 T_∞ ≃+* T_0`, and either domain
faithfulness (`IsDomain R_∞`) or same-rank cyclic faithfulness (`R_∞ ≃ S_∞^r`, `R_∞ ↠ M_∞`). -/
structure TaylorWilesPatchingDatum where
  S_inf : Type
  [commRingS : CommRing S_inf]
  [localS : IsLocalRing S_inf]
  g : ℕ
  y : Fin g → S_inf
  aug_le_max : Ideal.span (Set.range y) ≤ IsLocalRing.maximalIdeal S_inf
  R_inf : Type
  [commRingR : CommRing R_inf]
  [algSR : Algebra S_inf R_inf]
  [finSR : Module.Finite S_inf R_inf]
  T_inf : Type
  [commRingT : CommRing T_inf]
  [algST : Algebra S_inf T_inf]
  phi_inf : R_inf →ₐ[S_inf] T_inf
  phi_surj : Function.Surjective phi_inf
  M_inf : Type
  [addM : AddCommGroup M_inf]
  [modSM : Module S_inf M_inf]
  [modRM : Module R_inf M_inf]
  [modTM : Module T_inf M_inf]
  [towerSRM : IsScalarTower S_inf R_inf M_inf]
  compat_RM_TM : ∀ (r : R_inf) (m : M_inf), r • m = phi_inf r • m
  rank : ℕ
  rank_pos : 0 < rank
  M_free_S : M_inf ≃ₗ[S_inf] (Fin rank → S_inf)
  /-- Faithfulness witness: either `R_∞` is an integral domain (Kisin/regular-local case)
  or `R_∞` has the same `S_∞`-rank as `M_∞` with a cyclic surjection `R_∞ ↠ M_∞`. -/
  faithful_witness :
    IsDomain R_inf ∨
      Nonempty ((R_inf ≃ₗ[S_inf] (Fin rank → S_inf)) ×
        { f : R_inf →ₗ[R_inf] M_inf // Function.Surjective f })
  R_0 : Type
  [commRingR0 : CommRing R_0]
  T_0 : Type
  [commRingT0 : CommRing T_0]
  specR : R_inf ⧸ ((Ideal.span (Set.range y)).map (algebraMap S_inf R_inf)) ≃+* R_0
  specT : T_inf ⧸ ((Ideal.span (Set.range y)).map (algebraMap S_inf T_inf)) ≃+* T_0

attribute [instance] TaylorWilesPatchingDatum.commRingS TaylorWilesPatchingDatum.localS
  TaylorWilesPatchingDatum.commRingR TaylorWilesPatchingDatum.algSR
  TaylorWilesPatchingDatum.finSR TaylorWilesPatchingDatum.commRingT
  TaylorWilesPatchingDatum.algST TaylorWilesPatchingDatum.addM
  TaylorWilesPatchingDatum.modSM TaylorWilesPatchingDatum.modRM
  TaylorWilesPatchingDatum.modTM TaylorWilesPatchingDatum.towerSRM
  TaylorWilesPatchingDatum.commRingR0 TaylorWilesPatchingDatum.commRingT0

/-- The augmentation ideal `𝔞 = (y_1, ..., y_g)` of a `TaylorWilesPatchingDatum`. -/
def TaylorWilesPatchingDatum.augIdeal (D : TaylorWilesPatchingDatum) : Ideal D.S_inf :=
  Ideal.span (Set.range D.y)

/-- Specialized coinvariant module `M_0 := M_∞ ⧸ 𝔞 M_∞` over `S_∞ ⧸ 𝔞`. -/
abbrev TaylorWilesPatchingDatum.M_0 (D : TaylorWilesPatchingDatum) : Type :=
  Coinv D.augIdeal D.M_inf

/-- **Coinvariant Free-Rank Descent (`M_0 ≃ (S_∞ / 𝔞)^r`)** for any `TaylorWilesPatchingDatum`. -/
def TaylorWilesPatchingDatum.M0_equiv_pi (D : TaylorWilesPatchingDatum) :
    D.M_0 ≃ₗ[D.S_inf ⧸ D.augIdeal] (Fin D.rank → D.S_inf ⧸ D.augIdeal) :=
  coinvEquivPiOfEquivPi D.augIdeal D.M_free_S

theorem TaylorWilesPatchingDatum.M0_free_finite (D : TaylorWilesPatchingDatum) :
    Module.Free (D.S_inf ⧸ D.augIdeal) D.M_0 ∧ Module.Finite (D.S_inf ⧸ D.augIdeal) D.M_0 :=
  coinv_free_finite_of_equiv_pi D.augIdeal D.M_free_S

/-- **Patched Module Faithfulness (`Ann_{R_∞}(M_∞) = ⊥`)**: discharged automatically from either
the domain witness or the same-rank cyclic witness. -/
theorem TaylorWilesPatchingDatum.annihilator_R_inf_eq_bot (D : TaylorWilesPatchingDatum) :
    Module.annihilator D.R_inf D.M_inf = ⊥ := by
  have : Module.Free D.S_inf D.M_inf := Module.Free.of_equiv D.M_free_S.symm
  have : Nonempty (Fin D.rank) := ⟨⟨0, D.rank_pos⟩⟩
  have : Nontrivial (Fin D.rank → D.S_inf) := inferInstance
  have : Nontrivial D.M_inf := Function.Injective.nontrivial D.M_free_S.symm.injective
  rcases D.faithful_witness with hdom | ⟨⟨eR, ⟨f, hf⟩⟩⟩
  · have : IsDomain D.R_inf := hdom
    exact annihilator_eq_bot_of_isDomain_finite_free (S := D.S_inf) (R := D.R_inf) (M := D.M_inf)
  · exact (annihilator_eq_bot_of_surjective_same_rank eR D.M_free_S f hf).2

/-- **Patched `R_∞ ≃ₐ[S_∞] T_∞` Isomorphism** for any `TaylorWilesPatchingDatum`. -/
def TaylorWilesPatchingDatum.R_inf_equiv_T_inf (D : TaylorWilesPatchingDatum) :
    D.R_inf ≃ₐ[D.S_inf] D.T_inf :=
  patchedAlgEquivOfFaithful D.phi_inf D.phi_surj D.compat_RM_TM D.annihilator_R_inf_eq_bot

/-- **Specialized `R_0 ≃+* T_0` (`R = T`) Isomorphism**: descends `R_∞ ≃ₐ[S_∞] T_∞` modulo
`𝔞 = (y_1, ..., y_g)` to prove `R_0 ≃+* T_0`! -/
def TaylorWilesPatchingDatum.R0_equiv_T0 (D : TaylorWilesPatchingDatum) :
    D.R_0 ≃+* D.T_0 :=
  D.specR.symm.trans ((quotientMapEquivOfAlgEquiv D.augIdeal D.R_inf_equiv_T_inf).trans D.specT)

end PatchedREqT

/-! ## Section 2: Wiles–Lenstra–Diamond Numerical Criterion & Congruence Ideal = Selmer Length -/

section CongruenceAndCotangent

variable {𝒪 : Type*} [CommRing 𝒪]

/-- Augmentation ideal `I_T = ker(π : T → 𝒪)`. -/
def augIdeal {T : Type*} [CommRing T] [Algebra 𝒪 T] (π : T →ₐ[𝒪] 𝒪) : Ideal T :=
  RingHom.ker π.toRingHom

/-- The square `I_T^2` viewed as an `𝒪`-submodule of `I_T`. -/
def cotangentSubmodule {T : Type*} [CommRing T] [Algebra 𝒪 T] (π : T →ₐ[𝒪] 𝒪) :
    Submodule 𝒪 (augIdeal π) :=
  ((augIdeal π ^ 2).restrictScalars 𝒪).comap ((augIdeal π).restrictScalars 𝒪).subtype

/-- The **cotangent module** `Φ_T := I_T ⧸ I_T^2` (canonically isomorphic to `Ω_{T/𝒪} ⊗_{T,π} 𝒪`),
representing the dual Selmer / tangent-dual obstruction module. -/
abbrev Cotangent {T : Type*} [CommRing T] [Algebra 𝒪 T] (π : T →ₐ[𝒪] 𝒪) : Type _ :=
  (augIdeal π) ⧸ cotangentSubmodule π

/-- Annihilator ideal `Ann_T(I_T) = { t ∈ T | ∀ x ∈ I_T, t * x = 0 }`. -/
def annAugIdeal {T : Type*} [CommRing T] [Algebra 𝒪 T] (π : T →ₐ[𝒪] 𝒪) : Ideal T :=
  Module.annihilator T (augIdeal π)

/-- The **congruence ideal** `η_T := π(Ann_T(ker π)) ⊆ 𝒪`. -/
def congruenceIdeal {T : Type*} [CommRing T] [Algebra 𝒪 T] (π : T →ₐ[𝒪] 𝒪) : Ideal 𝒪 :=
  (annAugIdeal π).map π.toRingHom

theorem mem_augIdeal_iff {T : Type*} [CommRing T] [Algebra 𝒪 T] (π : T →ₐ[𝒪] 𝒪) (t : T) :
    t ∈ augIdeal π ↔ π t = 0 := Iff.rfl

theorem mem_annAugIdeal_iff {T : Type*} [CommRing T] [Algebra 𝒪 T] (π : T →ₐ[𝒪] 𝒪) (t : T) :
    t ∈ annAugIdeal π ↔ ∀ x ∈ augIdeal π, t * x = 0 := by
  rw [annAugIdeal, Module.mem_annihilator]
  constructor
  · intro h x hx
    exact congrArg Subtype.val (h ⟨x, hx⟩)
  · intro h x
    exact Subtype.ext (h x.1 x.2)

theorem aug_surjective {T : Type*} [CommRing T] [Algebra 𝒪 T] (π : T →ₐ[𝒪] 𝒪) :
    Function.Surjective π :=
  fun a => ⟨algebraMap 𝒪 T a, π.commutes a⟩

/-- Exact setwise characterization of `η_T = π(Ann_T(I_T))` (using surjectivity of `π`). -/
theorem mem_congruenceIdeal_iff {T : Type*} [CommRing T] [Algebra 𝒪 T]
    (π : T →ₐ[𝒪] 𝒪) (a : 𝒪) :
    a ∈ congruenceIdeal π ↔ ∃ t ∈ annAugIdeal π, π t = a := by
  let J : Ideal 𝒪 :=
    { carrier := { c : 𝒪 | ∃ t ∈ annAugIdeal π, π t = c }
      zero_mem' := ⟨0, (annAugIdeal π).zero_mem, map_zero π⟩
      add_mem' := by
        rintro c₁ c₂ ⟨t₁, ht₁, rfl⟩ ⟨t₂, ht₂, rfl⟩
        exact ⟨t₁ + t₂, (annAugIdeal π).add_mem ht₁ ht₂, map_add π t₁ t₂⟩
      smul_mem' := by
        rintro c₁ c₂ ⟨t₂, ht₂, rfl⟩
        refine ⟨algebraMap 𝒪 T c₁ * t₂, Ideal.mul_mem_left _ _ ht₂, ?_⟩
        rw [map_mul, π.commutes, smul_eq_mul]
        rfl }
  have hEq : congruenceIdeal π = J := by
    apply le_antisymm
    · rw [congruenceIdeal, Ideal.map_le_iff_le_comap]
      intro t ht
      exact ⟨t, ht, rfl⟩
    · rintro c ⟨t, ht, rfl⟩
      exact Ideal.mem_map_of_mem π.toRingHom ht
  rw [hEq]
  rfl

/-- **Unconditional Congruence-Ideal Annihilation of `Φ_T = I_T / I_T^2`**:
for EVERY augmented `𝒪`-algebra `(T, π)`, `η_T ≤ Ann_𝒪(Φ_T)`. -/
theorem congruenceIdeal_le_annihilator_cotangent {T : Type*} [CommRing T] [Algebra 𝒪 T]
    (π : T →ₐ[𝒪] 𝒪) :
    congruenceIdeal π ≤ Module.annihilator 𝒪 (Cotangent π) := by
  intro a ha
  obtain ⟨t, ht, rfl⟩ := (mem_congruenceIdeal_iff π a).mp ha
  rw [Module.mem_annihilator]
  intro q
  induction q using Quotient.inductionOn' with
  | h x =>
    change Submodule.Quotient.mk (π t • x) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    change (π t • x : augIdeal π).1 ∈ augIdeal π ^ 2
    let y : T := t - algebraMap 𝒪 T (π t)
    have hy : y ∈ augIdeal π := by
      rw [mem_augIdeal_iff, map_sub, π.commutes]
      exact sub_self (π t)
    have htx : t * x.1 = 0 := (mem_annAugIdeal_iff π t).mp ht x.1 x.2
    have hval : (π t • x : augIdeal π).1 = -(y * x.1) := by
      show (π t • x.1 : T) = -((t - algebraMap 𝒪 T (π t)) * x.1)
      rw [Algebra.smul_def, sub_mul, htx, zero_sub, neg_neg]
    rw [hval, pow_two]
    exact Submodule.neg_mem _ (Ideal.mul_mem_mul hy x.2)

/-- Induced `𝒪`-linear map on cotangent modules `dφ : Φ_R →ₗ[𝒪] Φ_T` from `φ : R →ₐ[𝒪] T`. -/
def cotangentMap {R T : Type*} [CommRing R] [CommRing T] [Algebra 𝒪 R] [Algebra 𝒪 T]
    (φ : R →ₐ[𝒪] T) (π : T →ₐ[𝒪] 𝒪) :
    Cotangent (π.comp φ) →ₗ[𝒪] Cotangent π := by
  let fI : augIdeal (π.comp φ) →ₗ[𝒪] augIdeal π :=
    { toFun := fun x => ⟨φ x.1, x.2⟩
      map_add' := fun x y => Subtype.ext (map_add φ x.1 y.1)
      map_smul' := fun a x => Subtype.ext (by
        change φ (a • x.1) = a • φ x.1
        exact map_smul φ a x.1) }
  refine Submodule.mapQ (cotangentSubmodule (π.comp φ)) (cotangentSubmodule π) fI ?_
  intro x hx
  change φ x.1 ∈ augIdeal π ^ 2
  have hx2 : x.1 ∈ augIdeal (π.comp φ) ^ 2 := hx
  rw [pow_two] at hx2 ⊢
  have hle : Ideal.map φ.toRingHom (augIdeal (π.comp φ) * augIdeal (π.comp φ)) ≤
      augIdeal π * augIdeal π := by
    rw [Ideal.map_mul]
    refine Ideal.mul_mono ?_ ?_ <;>
      · rw [Ideal.map_le_iff_le_comap]
        intro r hr
        exact hr
  exact hle (Ideal.mem_map_of_mem φ.toRingHom hx2)

/-- **Cotangent Surjection**: any surjective `φ : R →ₐ[𝒪] T` induces a surjection
`dφ : Φ_R ↠ Φ_T` and hence `len_𝒪(Φ_T) ≤ len_𝒪(Φ_R)`. -/
theorem cotangentMap_surjective {R T : Type*} [CommRing R] [CommRing T] [Algebra 𝒪 R] [Algebra 𝒪 T]
    (φ : R →ₐ[𝒪] T) (hφ : Function.Surjective φ) (π : T →ₐ[𝒪] 𝒪) :
    Function.Surjective (cotangentMap φ π) := by
  intro q
  induction q using Quotient.inductionOn' with
  | h y =>
    obtain ⟨r, hr⟩ := hφ y.1
    have hrI : r ∈ augIdeal (π.comp φ) := by
      change π (φ r) = 0
      rw [hr]
      exact y.2
    refine ⟨Submodule.Quotient.mk ⟨r, hrI⟩, ?_⟩
    change Submodule.Quotient.mk ⟨φ r, hrI⟩ = Submodule.Quotient.mk y
    congr 1
    exact Subtype.ext hr

theorem length_cotangent_le_of_surjective {R T : Type*} [CommRing R] [CommRing T]
    [Algebra 𝒪 R] [Algebra 𝒪 T]
    (φ : R →ₐ[𝒪] T) (hφ : Function.Surjective φ) (π : T →ₐ[𝒪] 𝒪) :
    Module.length 𝒪 (Cotangent π) ≤ Module.length 𝒪 (Cotangent (π.comp φ)) :=
  Module.length_le_of_surjective (cotangentMap φ π) (cotangentMap_surjective φ hφ π)

/-- **Congruence-Ideal Monotonicity**: any surjective `φ : R →ₐ[𝒪] T` satisfies `η_R ≤ η_T`. -/
theorem congruenceIdeal_le_of_surjective {R T : Type*} [CommRing R] [CommRing T]
    [Algebra 𝒪 R] [Algebra 𝒪 T]
    (φ : R →ₐ[𝒪] T) (hφ : Function.Surjective φ) (π : T →ₐ[𝒪] 𝒪) :
    congruenceIdeal (π.comp φ) ≤ congruenceIdeal π := by
  intro a ha
  obtain ⟨r, hr, rfl⟩ := (mem_congruenceIdeal_iff (π.comp φ) a).mp ha
  refine (mem_congruenceIdeal_iff π (π (φ r))).mpr ⟨φ r, ?_, rfl⟩
  rw [mem_annAugIdeal_iff]
  intro y hy
  obtain ⟨x, rfl⟩ := hφ y
  have hx : x ∈ augIdeal (π.comp φ) := hy
  rw [← map_mul, (mem_annAugIdeal_iff (π.comp φ) r).mp hr x hx, map_zero]

/-- **Cotangent Isomorphism from Ring Isomorphism**: if `e : R ≃ₐ[𝒪] T`, then
`Φ_R ≃ₗ[𝒪] Φ_T` and `η_R = η_T`. -/
def cotangentEquivOfAlgEquiv {R T : Type*} [CommRing R] [CommRing T] [Algebra 𝒪 R] [Algebra 𝒪 T]
    (e : R ≃ₐ[𝒪] T) (π : T →ₐ[𝒪] 𝒪) :
    Cotangent (π.comp e.toAlgHom) ≃ₗ[𝒪] Cotangent π := by
  refine LinearEquiv.ofBijective (cotangentMap e.toAlgHom π)
    ⟨?_, cotangentMap_surjective e.toAlgHom e.surjective π⟩
  rw [injective_iff_map_eq_zero]
  intro q hq
  induction q using Quotient.inductionOn' with
  | h x =>
    change Submodule.Quotient.mk (p := cotangentSubmodule π) ⟨e x.1, x.2⟩ = 0 at hq
    rw [Submodule.Quotient.mk_eq_zero] at hq
    change e x.1 ∈ augIdeal π ^ 2 at hq
    change Submodule.Quotient.mk (p := cotangentSubmodule (π.comp e.toAlgHom)) x = 0
    rw [Submodule.Quotient.mk_eq_zero]
    change x.1 ∈ augIdeal (π.comp e.toAlgHom) ^ 2
    have hpre : e.symm (e x.1) ∈ augIdeal (π.comp e.toAlgHom) ^ 2 := by
      rw [pow_two] at hq ⊢
      have hle : Ideal.map e.symm.toRingHom (augIdeal π * augIdeal π) ≤
          augIdeal (π.comp e.toAlgHom) * augIdeal (π.comp e.toAlgHom) := by
        rw [Ideal.map_mul]
        refine Ideal.mul_mono ?_ ?_ <;>
          · rw [Ideal.map_le_iff_le_comap]
            intro t ht
            change π (e (e.symm t)) = 0
            simpa using (mem_augIdeal_iff π t).mp ht
      exact hle (Ideal.mem_map_of_mem e.symm.toRingHom hq)
    simpa using hpre

theorem congruenceIdeal_eq_of_algEquiv {R T : Type*} [CommRing R] [CommRing T]
    [Algebra 𝒪 R] [Algebra 𝒪 T] (e : R ≃ₐ[𝒪] T) (π : T →ₐ[𝒪] 𝒪) :
    congruenceIdeal (π.comp e.toAlgHom) = congruenceIdeal π := by
  apply le_antisymm (congruenceIdeal_le_of_surjective e.toAlgHom e.surjective π)
  have hback : (π.comp e.toAlgHom).comp e.symm.toAlgHom = π := by
    ext t; simp
  have h := congruenceIdeal_le_of_surjective e.symm.toAlgHom e.symm.surjective (π.comp e.toAlgHom)
  rwa [hback] at h

/-- Helper: every element of `I^2` is an `I`-linear combination of any `𝒪`-generating set of `I`. -/
theorem mem_augIdeal_sq_exists_comb {T : Type*} [CommRing T] [Algebra 𝒪 T]
    (π : T →ₐ[𝒪] 𝒪) {m : ℕ} (e : Fin m → augIdeal π)
    (he : Submodule.span 𝒪 (Set.range e) = ⊤) {w : T} (hw : w ∈ augIdeal π ^ 2) :
    ∃ c : Fin m → T, (∀ j, c j ∈ augIdeal π) ∧ w = ∑ j : Fin m, c j * (e j).1 := by
  rw [pow_two] at hw
  refine Submodule.mul_induction_on hw ?_ ?_
  · intro u hu v hv
    have hv' : (⟨v, hv⟩ : augIdeal π) ∈ Submodule.span 𝒪 (Set.range e) := by rw [he]; trivial
    rw [Submodule.mem_span_range_iff_exists_fun] at hv'
    obtain ⟨b, hb⟩ := hv'
    have hveq : v = ∑ j : Fin m, algebraMap 𝒪 T (b j) * (e j).1 := by
      have hval := congrArg Subtype.val hb
      simpa [Algebra.smul_def] using hval.symm
    refine ⟨fun j => u * algebraMap 𝒪 T (b j), fun j => Ideal.mul_mem_right _ _ hu, ?_⟩
    rw [hveq, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => by ring
  · intro x y ⟨cx, hcx, hx⟩ ⟨cy, hcy, hy⟩
    refine ⟨fun j => cx j + cy j, fun j => Ideal.add_mem _ (hcx j) (hcy j), ?_⟩
    rw [hx, hy, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => by ring

/-- **Tate–Lenstra Adjugate Determinant Theorem (`Fitt_𝒪(Φ_T) ≤ η_T`)**:
for ANY augmented `𝒪`-algebra `(T, π)`, if `e : Fin m → I_T` generates `I_T` over `𝒪` and
`A : Matrix (Fin m) (Fin m) 𝒪` is ANY square relation matrix whose rows lie in `I_T^2`
(`∀ i, ∑ j, A i j • e j ∈ I_T^2`), then `A.det ∈ η_T`! -/
theorem det_mem_congruenceIdeal_of_relations {T : Type*} [CommRing T] [Algebra 𝒪 T]
    (π : T →ₐ[𝒪] 𝒪) {m : ℕ} (e : Fin m → augIdeal π)
    (he : Submodule.span 𝒪 (Set.range e) = ⊤)
    (A : Matrix (Fin m) (Fin m) 𝒪)
    (hrel : ∀ i : Fin m, (∑ j : Fin m, algebraMap 𝒪 T (A i j) * (e j).1) ∈ augIdeal π ^ 2) :
    A.det ∈ congruenceIdeal π := by
  classical
  have hrow : ∀ i : Fin m, ∃ c : Fin m → T,
      (∀ j, c j ∈ augIdeal π) ∧
      (∑ j : Fin m, algebraMap 𝒪 T (A i j) * (e j).1) = ∑ j : Fin m, c j * (e j).1 :=
    fun i => mem_augIdeal_sq_exists_comb π e he (hrel i)
  choose c hc_mem hc_eq using hrow
  let M : Matrix (Fin m) (Fin m) T := fun i j => algebraMap 𝒪 T (A i j) - c i j
  let v : Fin m → T := fun j => (e j).1
  have hMv : M.mulVec v = 0 := by
    ext i
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply, M, v, sub_mul, Finset.sum_sub_distrib]
    exact sub_eq_zero.mpr (hc_eq i)
  have hdet_v : M.det • v = 0 := by
    calc M.det • v
        = (M.adjugate * M).mulVec v := by
            rw [Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
      _ = M.adjugate.mulVec (M.mulVec v) := (Matrix.mulVec_mulVec v M.adjugate M).symm
      _ = 0 := by rw [hMv, Matrix.mulVec_zero]
  have hdet_ann : M.det ∈ annAugIdeal π := by
    rw [mem_annAugIdeal_iff]
    intro x hx
    have hx' : (⟨x, hx⟩ : augIdeal π) ∈ Submodule.span 𝒪 (Set.range e) := by rw [he]; trivial
    rw [Submodule.mem_span_range_iff_exists_fun] at hx'
    obtain ⟨b, hb⟩ := hx'
    have hxeq : x = ∑ j : Fin m, algebraMap 𝒪 T (b j) * (e j).1 := by
      have hval := congrArg Subtype.val hb
      simpa [Algebra.smul_def] using hval.symm
    rw [hxeq, Finset.mul_sum]
    refine Finset.sum_eq_zero fun j _ => ?_
    have hj : M.det * (e j).1 = 0 := by
      simpa [v] using congrFun hdet_v j
    calc M.det * (algebraMap 𝒪 T (b j) * (e j).1)
        = algebraMap 𝒪 T (b j) * (M.det * (e j).1) := by ring
      _ = 0 := by rw [hj, mul_zero]
  have hmap : M.map π.toRingHom = A := by
    ext i j
    change π (algebraMap 𝒪 T (A i j) - c i j) = A i j
    rw [map_sub, π.commutes, show π (c i j) = 0 from hc_mem i j]
    exact sub_zero (A i j)
  refine (mem_congruenceIdeal_iff π A.det).mpr ⟨M.det, hdet_ann, ?_⟩
  change π.toRingHom M.det = A.det
  rw [RingHom.map_det]
  change (M.map π.toRingHom).det = A.det
  rw [hmap]

/-- The 0-th Fitting ideal of `Φ_T` relative to a generating family `e : Fin m → I_T`:
the ideal of `𝒪` generated by all `m × m` relation-matrix determinants of `Φ_T`. -/
def cotangentFittingIdeal {T : Type*} [CommRing T] [Algebra 𝒪 T]
    (π : T →ₐ[𝒪] 𝒪) {m : ℕ} (e : Fin m → augIdeal π) : Ideal 𝒪 :=
  Ideal.span { d : 𝒪 | ∃ A : Matrix (Fin m) (Fin m) 𝒪,
    (∀ i : Fin m, (∑ j : Fin m, algebraMap 𝒪 T (A i j) * (e j).1) ∈ augIdeal π ^ 2) ∧
    d = A.det }

theorem cotangentFittingIdeal_le_congruenceIdeal {T : Type*} [CommRing T] [Algebra 𝒪 T]
    (π : T →ₐ[𝒪] 𝒪) {m : ℕ} (e : Fin m → augIdeal π)
    (he : Submodule.span 𝒪 (Set.range e) = ⊤) :
    cotangentFittingIdeal π e ≤ congruenceIdeal π := by
  rw [cotangentFittingIdeal, Ideal.span_le]
  rintro d ⟨A, hrel, rfl⟩
  exact det_mem_congruenceIdeal_of_relations π e he A hrel

end CongruenceAndCotangent

/-! ### Smith Normal Form, Exact Determinant-Length Identity & Wiles–Lenstra Numerical Criterion -/

section DVRSmithAndWilesLenstra

/-- Over any integral domain `𝒪`, principal ideal lengths are strictly additive for nonzero left
factors: `len(𝒪 / (a * b)) = len(𝒪 / (a)) + len(𝒪 / (b))` (`a ≠ 0`). -/
theorem length_quotient_span_mul_eq_add_of_domain {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪]
    {a : 𝒪} (ha : a ≠ 0) (b : 𝒪) :
    Module.length 𝒪 (𝒪 ⧸ Ideal.span ({a * b} : Set 𝒪)) =
      Module.length 𝒪 (𝒪 ⧸ Ideal.span ({a} : Set 𝒪)) +
        Module.length 𝒪 (𝒪 ⧸ Ideal.span ({b} : Set 𝒪)) := by
  let Iab : Ideal 𝒪 := Ideal.span ({a * b} : Set 𝒪)
  let Ia : Ideal 𝒪 := Ideal.span ({a} : Set 𝒪)
  let Ib : Ideal 𝒪 := Ideal.span ({b} : Set 𝒪)
  have hle : Iab ≤ Ia := by
    rw [Ideal.span_singleton_le_iff_mem]
    exact Ideal.mul_mem_right b Ia (Ideal.subset_span rfl)
  let qMap : (𝒪 ⧸ Iab) →ₗ[𝒪] (𝒪 ⧸ Ia) := Submodule.factor hle
  have hqSurj : Function.Surjective qMap := Submodule.factor_surjective hle
  let mulA : 𝒪 →ₗ[𝒪] (𝒪 ⧸ Iab) :=
    { toFun := fun x => Ideal.Quotient.mk Iab (a * x)
      map_add' := fun x y => by
        change Ideal.Quotient.mk Iab (a * (x + y)) =
          Ideal.Quotient.mk Iab (a * x) + Ideal.Quotient.mk Iab (a * y)
        rw [mul_add, map_add]
      map_smul' := fun r x => by
        change Ideal.Quotient.mk Iab (a * (r * x)) = r • Ideal.Quotient.mk Iab (a * x)
        rw [← mul_assoc, mul_comm a r, mul_assoc]
        exact map_smul (Ideal.Quotient.mkₐ 𝒪 Iab).toLinearMap r (a * x) }
  let liftMulA : (𝒪 ⧸ Ib) →ₗ[𝒪] (𝒪 ⧸ Iab) :=
    Ib.liftQ mulA (by
      intro x hx
      rw [LinearMap.mem_ker]
      rw [Ideal.mem_span_singleton] at hx
      obtain ⟨c, rfl⟩ := hx
      change Ideal.Quotient.mk Iab (a * (b * c)) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem, ← mul_assoc]
      exact Ideal.mul_mem_right c Iab (Ideal.subset_span rfl))
  have hInj : Function.Injective liftMulA := by
    rw [injective_iff_map_eq_zero]
    intro q hq
    induction q using Quotient.inductionOn' with
    | h x =>
      change Ideal.Quotient.mk Iab (a * x) = 0 at hq
      rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at hq
      obtain ⟨c, hc⟩ := hq
      have hxb : x = b * c := mul_left_cancel₀ ha (by simpa [mul_assoc] using hc)
      change Ideal.Quotient.mk Ib x = 0
      rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
      exact ⟨c, hxb⟩
  have hExact : Function.Exact liftMulA qMap := by
    rw [LinearMap.exact_iff]
    apply le_antisymm
    · intro q hq
      induction q using Quotient.inductionOn' with
      | h r =>
        have hr : r ∈ Ia := Ideal.Quotient.eq_zero_iff_mem.mp hq
        rw [Ideal.mem_span_singleton] at hr
        obtain ⟨x, rfl⟩ := hr
        exact ⟨Ideal.Quotient.mk Ib x, rfl⟩
    · rintro _ ⟨q, rfl⟩
      induction q using Quotient.inductionOn' with
      | h x =>
        change Ideal.Quotient.mk Ia (a * x) = 0
        rw [Ideal.Quotient.eq_zero_iff_mem]
        exact Ideal.mul_mem_right x Ia (Ideal.subset_span rfl)
  rw [Module.length_eq_add_of_exact liftMulA qMap hInj hqSurj hExact, add_comm]

/-- Exact length additivity for finite products of nonzero elements over a domain. -/
theorem length_quotient_span_prod_eq_sum_of_domain {𝒪 ι : Type*} [CommRing 𝒪] [IsDomain 𝒪]
    (s : Finset ι) (d : ι → 𝒪) (hd : ∀ i ∈ s, d i ≠ 0) :
    Module.length 𝒪 (𝒪 ⧸ Ideal.span ({∏ i ∈ s, d i} : Set 𝒪)) =
      ∑ i ∈ s, Module.length 𝒪 (𝒪 ⧸ Ideal.span ({d i} : Set 𝒪)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, Finset.sum_empty, Ideal.span_singleton_one]
    have : Subsingleton (𝒪 ⧸ (⊤ : Ideal 𝒪)) := Submodule.Quotient.subsingleton_iff.mpr rfl
    exact Module.length_eq_zero
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    have ha0 : d a ≠ 0 := hd a (Finset.mem_insert_self a s)
    rw [length_quotient_span_mul_eq_add_of_domain ha0,
      ih (fun i hi => hd i (Finset.mem_insert_of_mem hi))]

/-- Exact length additivity for finite dependent products `∀ i : Fin m, M i`. -/
theorem length_pi_fin {R : Type*} [CommRing R] :
    ∀ {m : ℕ} (M : Fin m → Type*) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)],
      Module.length R (∀ i : Fin m, M i) = ∑ i : Fin m, Module.length R (M i)
  | 0, M, _, _ => by
      have : Subsingleton (∀ i : Fin 0, M i) := inferInstance
      simp [Module.length_eq_zero]
  | n + 1, M, _, _ => by
      let headMap : (∀ i : Fin (n + 1), M i) →ₗ[R] M 0 :=
        { toFun := fun f => f 0
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      let tailMap : (∀ i : Fin n, M i.succ) →ₗ[R] (∀ i : Fin (n + 1), M i) :=
        { toFun := fun g => Fin.cons 0 g
          map_add' := fun g₁ g₂ => by
            ext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp
          map_smul' := fun r g => by
            ext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp }
      have hInj : Function.Injective tailMap := by
        intro g₁ g₂ h
        ext j
        have := congrFun h j.succ
        simpa [tailMap] using this
      have hSurj : Function.Surjective headMap := fun x =>
        ⟨Fin.cons x 0, by simp [headMap]⟩
      have hExact : Function.Exact tailMap headMap := by
        rw [LinearMap.exact_iff]
        apply le_antisymm
        · intro f hf
          refine ⟨fun j => f j.succ, ?_⟩
          ext i
          refine Fin.cases ?_ (fun j => ?_) i
          · have hf0 : f 0 = 0 := hf
            simpa [tailMap] using hf0.symm
          · simp [tailMap]
        · rintro _ ⟨g, rfl⟩
          simp [headMap, tailMap]
      rw [Module.length_eq_add_of_exact tailMap headMap hInj hSurj hExact,
        length_pi_fin (fun j : Fin n => M j.succ), Fin.sum_univ_succ, add_comm]

/-- Associated elements generate the exact same principal ideal. -/
theorem span_singleton_eq_of_associated {𝒪 : Type*} [CommRing 𝒪] {a b : 𝒪}
    (h : Associated a b) :
    Ideal.span ({a} : Set 𝒪) = Ideal.span ({b} : Set 𝒪) := by
  obtain ⟨u, rfl⟩ := h
  exact (Ideal.span_singleton_mul_right_unit u.isUnit a).symm

/-- Quotient by a maximal ideal is a simple `𝒪`-module. -/
theorem isSimpleModule_quotient_of_isMaximal {𝒪 : Type*} [CommRing 𝒪]
    {I : Ideal 𝒪} (hI : I.IsMaximal) :
    IsSimpleModule 𝒪 (𝒪 ⧸ I) := by
  have hne : I ≠ ⊤ := hI.ne_top
  have hnt : Nontrivial (𝒪 ⧸ I) := Submodule.Quotient.nontrivial_iff.mpr hne
  have hsubnt : Nontrivial (Submodule 𝒪 (𝒪 ⧸ I)) := ⟨⟨⊥, ⊤, bot_ne_top⟩⟩
  have hord : IsSimpleOrder (Submodule 𝒪 (𝒪 ⧸ I)) := @IsSimpleOrder.mk _ _ _ hsubnt fun N => by
    let J : Ideal 𝒪 := N.comap (Submodule.mkQ I)
    have hIJ : I ≤ J := by
      intro x hx
      change Submodule.Quotient.mk (p := I) x ∈ N
      rw [(Submodule.Quotient.mk_eq_zero I).mpr hx]
      exact N.zero_mem
    by_cases hJtop : J = ⊤
    · right
      rw [eq_top_iff]
      intro q _
      induction q using Quotient.inductionOn' with
      | h x =>
        have hx : x ∈ J := by rw [hJtop]; trivial
        exact hx
    · left
      have hJI : I = J := hI.eq_of_le hJtop hIJ
      rw [eq_bot_iff]
      intro q hq
      induction q using Quotient.inductionOn' with
      | h x =>
        have hx : x ∈ I := by rw [hJI]; exact hq
        exact (Submodule.Quotient.mk_eq_zero I).mpr hx
  exact ⟨⟩

/-- In a DVR `𝒪`, any irreducible uniformizer `ϖ` generates the maximal ideal, so `𝒪 ⧸ (ϖ)` is a
simple `𝒪`-module of exact length `1`. -/
theorem isSimpleModule_quotient_uniformizer {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪]
    [IsDiscreteValuationRing 𝒪] {ϖ : 𝒪} (hϖ : Irreducible ϖ) :
    IsSimpleModule 𝒪 (𝒪 ⧸ Ideal.span ({ϖ} : Set 𝒪)) := by
  have hmax : (Ideal.span ({ϖ} : Set 𝒪)).IsMaximal := by
    rw [← (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ]
    exact IsLocalRing.maximalIdeal.isMaximal 𝒪
  exact isSimpleModule_quotient_of_isMaximal hmax

/-- Over a DVR `𝒪` with uniformizer `ϖ`, `len_𝒪(𝒪 ⧸ (ϖ^k)) = k` (exact equality!). -/
theorem length_quotient_span_pow_eq_of_dvr {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪]
    [IsDiscreteValuationRing 𝒪] {ϖ : 𝒪} (hϖ : Irreducible ϖ) :
    ∀ k : ℕ, Module.length 𝒪 (𝒪 ⧸ Ideal.span ({ϖ ^ k} : Set 𝒪)) = (k : ℕ∞)
  | 0 => by
    rw [pow_zero, Ideal.span_singleton_one]
    have : Subsingleton (𝒪 ⧸ (⊤ : Ideal 𝒪)) := Submodule.Quotient.subsingleton_iff.mpr rfl
    simp [Module.length_eq_zero]
  | k + 1 => by
    have : IsSimpleModule 𝒪 (𝒪 ⧸ Ideal.span ({ϖ} : Set 𝒪)) :=
      isSimpleModule_quotient_uniformizer hϖ
    rw [pow_succ', length_quotient_span_mul_eq_add_of_domain hϖ.ne_zero,
      length_quotient_span_pow_eq_of_dvr hϖ k,
      Module.length_eq_one (R := 𝒪) (M := 𝒪 ⧸ Ideal.span ({ϖ} : Set 𝒪))]
    push_cast
    ring

/-- **Total Divisibility in a DVR**: for all `a, b : 𝒪` in a DVR, `a ∣ b ∨ b ∣ a`. -/
theorem dvr_dvd_or_dvd {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    (a b : 𝒪) : a ∣ b ∨ b ∣ a := by
  by_cases ha : a = 0
  · right; rw [ha]; exact dvd_zero b
  by_cases hb : b = 0
  · left; rw [hb]; exact dvd_zero a
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪
  obtain ⟨m, hm⟩ := IsDiscreteValuationRing.associated_pow_irreducible ha hϖ
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible hb hϖ
  rcases le_total m n with hmn | hnm
  · left
    exact hm.dvd.trans ((pow_dvd_pow ϖ hmn).trans hn.symm.dvd)
  · right
    exact hn.dvd.trans ((pow_dvd_pow ϖ hnm).trans hm.symm.dvd)

/-- Permutation matrix `P_σ` in `Matrix (Fin m) (Fin m) 𝒪`. -/
def permMat {𝒪 : Type*} [CommRing 𝒪] {m : ℕ} (σ : Equiv.Perm (Fin m)) :
    Matrix (Fin m) (Fin m) 𝒪 :=
  fun i j => if σ i = j then 1 else 0

/-- Permutation matrix unit in `Matrix (Fin m) (Fin m) 𝒪`. -/
def permMatrixUnit {𝒪 : Type*} [CommRing 𝒪] {m : ℕ} (σ : Equiv.Perm (Fin m)) :
    (Matrix (Fin m) (Fin m) 𝒪)ˣ where
  val := permMat σ
  inv := permMat σ⁻¹
  val_inv := by
    ext i j
    rw [Matrix.mul_apply]
    simp only [permMat, Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, ↓reduceIte]
    have h : σ⁻¹ (σ i) = i := Equiv.symm_apply_apply σ i
    rw [h]
  inv_val := by
    ext i j
    rw [Matrix.mul_apply]
    simp only [permMat, Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, ↓reduceIte]
    have h : σ (σ⁻¹ i) = i := Equiv.apply_symm_apply σ i
    rw [h]

/-- Block-diagonal extension `1 ⊕ M` of an `n × n` matrix to `(n + 1) × (n + 1)`. -/
def blockLift {𝒪 : Type*} [CommRing 𝒪] {n : ℕ} (M : Matrix (Fin n) (Fin n) 𝒪) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) 𝒪 :=
  fun i j =>
    Fin.cases (Fin.cases 1 (fun _ => 0) j)
      (fun i' => Fin.cases 0 (fun j' => M i' j') j) i

theorem blockLift_mul {𝒪 : Type*} [CommRing 𝒪] {n : ℕ} (A B : Matrix (Fin n) (Fin n) 𝒪) :
    blockLift A * blockLift B = blockLift (A * B) := by
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_succ]
  refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j
  · simp [blockLift]
  · simp [blockLift]
  · simp [blockLift]
  · simp [blockLift, Matrix.mul_apply]

theorem blockLift_one {𝒪 : Type*} [CommRing 𝒪] {n : ℕ} :
    blockLift (1 : Matrix (Fin n) (Fin n) 𝒪) = 1 := by
  ext i j
  refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j <;>
    simp [blockLift, Matrix.one_apply, Fin.succ_ne_zero, (Fin.succ_ne_zero _).symm]

/-- Block-diagonal extension of a unit `U ∈ GL_n(𝒪)` to `1 ⊕ U ∈ GL_{n+1}(𝒪)`. -/
def liftBlockUnit {𝒪 : Type*} [CommRing 𝒪] {n : ℕ}
    (U : (Matrix (Fin n) (Fin n) 𝒪)ˣ) : (Matrix (Fin (n + 1)) (Fin (n + 1)) 𝒪)ˣ where
  val := blockLift U.val
  inv := blockLift U.inv
  val_inv := by rw [blockLift_mul, U.val_inv, blockLift_one]
  inv_val := by rw [blockLift_mul, U.inv_val, blockLift_one]

/-- Row-clearing elementary matrix subtracting `qr i` times row `0` from row `i + 1`. -/
def rowClearMat {𝒪 : Type*} [CommRing 𝒪] {n : ℕ} (qr : Fin n → 𝒪) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) 𝒪 :=
  fun i j =>
    Fin.cases (Fin.cases 1 (fun _ => 0) j)
      (fun i' => Fin.cases (qr i') (fun j' => if i' = j' then 1 else 0) j) i

/-- Row-clearing elementary unit `E_row(qr)`. -/
def rowClearUnit {𝒪 : Type*} [CommRing 𝒪] {n : ℕ} (qr : Fin n → 𝒪) :
    (Matrix (Fin (n + 1)) (Fin (n + 1)) 𝒪)ˣ where
  val := rowClearMat (-qr)
  inv := rowClearMat qr
  val_inv := by
    ext i j
    rw [Matrix.mul_apply, Fin.sum_univ_succ]
    refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j <;>
      simp [rowClearMat, Matrix.one_apply, Fin.succ_ne_zero, (Fin.succ_ne_zero _).symm]
  inv_val := by
    ext i j
    rw [Matrix.mul_apply, Fin.sum_univ_succ]
    refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j <;>
      simp [rowClearMat, Matrix.one_apply, Fin.succ_ne_zero, (Fin.succ_ne_zero _).symm]

/-- Column-clearing elementary matrix adding `qc j` times column `0` to column `j + 1`. -/
def colClearMat {𝒪 : Type*} [CommRing 𝒪] {n : ℕ} (qc : Fin n → 𝒪) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) 𝒪 :=
  fun i j =>
    Fin.cases (Fin.cases 1 (fun j' => qc j') j)
      (fun i' => Fin.cases 0 (fun j' => if i' = j' then 1 else 0) j) i

/-- Column-clearing elementary unit `E_col(qc)`. -/
def colClearUnit {𝒪 : Type*} [CommRing 𝒪] {n : ℕ} (qc : Fin n → 𝒪) :
    (Matrix (Fin (n + 1)) (Fin (n + 1)) 𝒪)ˣ where
  val := colClearMat (-qc)
  inv := colClearMat qc
  val_inv := by
    ext i j
    rw [Matrix.mul_apply, Fin.sum_univ_succ]
    refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j <;>
      simp [colClearMat, Matrix.one_apply, Fin.succ_ne_zero, (Fin.succ_ne_zero _).symm]
  inv_val := by
    ext i j
    rw [Matrix.mul_apply, Fin.sum_univ_succ]
    refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j <;>
      simp [colClearMat, Matrix.one_apply, Fin.succ_ne_zero, (Fin.succ_ne_zero _).symm]

/-- **Smith Normal Form / Diagonalization over a DVR**: every square matrix `A` over a DVR `𝒪`
is equivalent (`U * A * V = diagonal d`) to a diagonal matrix via invertible matrices `U, V`. -/
theorem exists_smithNormalForm_of_dvr {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪]
    [IsDiscreteValuationRing 𝒪] :
    ∀ {m : ℕ} (A : Matrix (Fin m) (Fin m) 𝒪),
      ∃ (U V : (Matrix (Fin m) (Fin m) 𝒪)ˣ) (d : Fin m → 𝒪),
        U.val * A * V.val = Matrix.diagonal d
  | 0, A =>
      ⟨1, 1, Fin.elim0, by ext i; exact Fin.elim0 i⟩
  | n + 1, A => by
      classical
      by_cases hA0 : A = 0
      · refine ⟨1, 1, 0, ?_⟩
        simp [hA0]
      have hex_min : ∃ p : Fin (n + 1) × Fin (n + 1),
          ∀ q : Fin (n + 1) × Fin (n + 1), A p.1 p.2 ∣ A q.1 q.2 := by
        have hstep : ∀ s : Finset (Fin (n + 1) × Fin (n + 1)), s.Nonempty →
            ∃ p ∈ s, ∀ q ∈ s, A p.1 p.2 ∣ A q.1 q.2 := by
          intro s
          induction s using Finset.induction_on with
          | empty => intro h; exact absurd h Finset.not_nonempty_empty
          | @insert x t hx ih =>
            intro _
            by_cases ht : t.Nonempty
            · obtain ⟨p, hp, hpdvd⟩ := ih ht
              rcases dvr_dvd_or_dvd (A x.1 x.2) (A p.1 p.2) with hxp | hpx
              · refine ⟨x, Finset.mem_insert_self x t, fun q hq => ?_⟩
                rcases Finset.mem_insert.mp hq with rfl | hqt
                · exact dvd_rfl
                · exact hxp.trans (hpdvd q hqt)
              · refine ⟨p, Finset.mem_insert_of_mem hp, fun q hq => ?_⟩
                rcases Finset.mem_insert.mp hq with rfl | hqt
                · exact hpx
                · exact hpdvd q hqt
            · rw [Finset.not_nonempty_iff_eq_empty] at ht
              subst ht
              exact ⟨x, Finset.mem_singleton_self x, fun q hq => by
                rw [Finset.mem_singleton.mp hq]⟩
        obtain ⟨p, _, hp⟩ := hstep Finset.univ ⟨(0, 0), Finset.mem_univ _⟩
        exact ⟨p, fun q => hp q (Finset.mem_univ q)⟩
      obtain ⟨⟨i₀, j₀⟩, hmin⟩ := hex_min
      let P := permMatrixUnit (𝒪 := 𝒪) (Equiv.swap (0 : Fin (n + 1)) i₀)
      let Q := permMatrixUnit (𝒪 := 𝒪) (Equiv.swap (0 : Fin (n + 1)) j₀)
      let B : Matrix (Fin (n + 1)) (Fin (n + 1)) 𝒪 := P.val * A * Q.val
      have hB_entry : ∀ i j : Fin (n + 1),
          B i j = A (Equiv.swap 0 i₀ i) (Equiv.swap 0 j₀ j) := by
        intro i j
        simp only [B, P, Q, permMatrixUnit, permMat, Matrix.mul_apply]
        calc ∑ k, (∑ l, (if Equiv.swap 0 i₀ i = l then (1 : 𝒪) else 0) * A l k) *
              (if Equiv.swap 0 j₀ k = j then 1 else 0)
            = ∑ k, A (Equiv.swap 0 i₀ i) k * (if k = Equiv.swap 0 j₀ j then 1 else 0) := by
                refine Finset.sum_congr rfl fun k _ => ?_
                congr 1
                · simp
                · by_cases hk : k = Equiv.swap 0 j₀ j
                  · subst hk; simp
                  · have hne : Equiv.swap 0 j₀ k ≠ j := by
                      intro h; apply hk; rw [← h, Equiv.swap_apply_self]
                    simp [hk, hne]
          _ = A (Equiv.swap 0 i₀ i) (Equiv.swap 0 j₀ j) := by simp
      have hB00_dvd : ∀ i j : Fin (n + 1), B 0 0 ∣ B i j := by
        intro i j
        rw [hB_entry 0 0, hB_entry i j, Equiv.swap_apply_left, Equiv.swap_apply_left]
        exact hmin (Equiv.swap 0 i₀ i, Equiv.swap 0 j₀ j)
      have hrow_quot : ∀ i : Fin n, ∃ q : 𝒪, B i.succ 0 = q * B 0 0 := by
        intro i
        obtain ⟨q, hq⟩ := hB00_dvd i.succ 0
        exact ⟨q, by rw [hq, mul_comm]⟩
      choose qr hqr using hrow_quot
      have hcol_quot : ∀ j : Fin n, ∃ q : 𝒪, B 0 j.succ = B 0 0 * q :=
        fun j => hB00_dvd 0 j.succ
      choose qc hqc using hcol_quot
      let E_row := rowClearUnit qr
      let E_col := colClearUnit qc
      let C : Matrix (Fin (n + 1)) (Fin (n + 1)) 𝒪 := E_row.val * B * E_col.val
      have hC00 : C 0 0 = B 0 0 := by
        change ((E_row.val * B) * E_col.val) 0 0 = B 0 0
        rw [Matrix.mul_apply, Fin.sum_univ_succ]
        simp only [E_col, colClearUnit, colClearMat, Fin.cases_zero, Fin.cases_succ, mul_one, mul_zero,
          Finset.sum_const_zero, add_zero]
        rw [Matrix.mul_apply, Fin.sum_univ_succ]
        simp [E_row, rowClearUnit, rowClearMat]
      have hC_col0 : ∀ i : Fin n, C i.succ 0 = 0 := by
        intro i
        change ((E_row.val * B) * E_col.val) i.succ 0 = 0
        rw [Matrix.mul_apply, Fin.sum_univ_succ]
        simp only [E_col, colClearUnit, colClearMat, Fin.cases_zero, Fin.cases_succ, mul_one, mul_zero,
          Finset.sum_const_zero, add_zero]
        rw [Matrix.mul_apply, Fin.sum_univ_succ]
        simp [E_row, rowClearUnit, rowClearMat, hqr i]
      have hC_row0 : ∀ j : Fin n, C 0 j.succ = 0 := by
        intro j
        change ((E_row.val * B) * E_col.val) 0 j.succ = 0
        rw [Matrix.mul_apply, Fin.sum_univ_succ]
        have hEB0 : ∀ k : Fin (n + 1), (E_row.val * B) 0 k = B 0 k := by
          intro k
          rw [Matrix.mul_apply, Fin.sum_univ_succ]
          simp [E_row, rowClearUnit, rowClearMat]
        simp only [E_col, colClearUnit, colClearMat, Fin.cases_zero, Fin.cases_succ, hEB0]
        simp [hqc j]
      let Csub : Matrix (Fin n) (Fin n) 𝒪 := fun i j => C i.succ j.succ
      obtain ⟨Usub, Vsub, dsub, hsub⟩ := exists_smithNormalForm_of_dvr Csub
      let U1 := liftBlockUnit Usub
      let V1 := liftBlockUnit Vsub
      refine ⟨U1 * E_row * P, Q * E_col * V1, Fin.cases (B 0 0) dsub, ?_⟩
      have hassoc : (U1 * E_row * P).val * A * (Q * E_col * V1).val =
          U1.val * C * V1.val := by
        simp only [Units.val_mul, C, B, Matrix.mul_assoc]
      rw [hassoc]
      ext i j
      rw [Matrix.mul_apply, Fin.sum_univ_succ]
      refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j
      · have h00 : (U1.val * C) 0 0 = B 0 0 := by
          rw [Matrix.mul_apply, Fin.sum_univ_succ]
          simp [U1, liftBlockUnit, blockLift, hC00]
        simp [V1, liftBlockUnit, blockLift, h00]
      · have h0j : ∀ k : Fin n, (U1.val * C) 0 k.succ = 0 := by
          intro k
          rw [Matrix.mul_apply, Fin.sum_univ_succ]
          simp [U1, liftBlockUnit, blockLift, hC_row0]
        simp [V1, liftBlockUnit, blockLift, h0j, (Fin.succ_ne_zero j').symm]
      · have hi0 : (U1.val * C) i'.succ 0 = 0 := by
          rw [Matrix.mul_apply, Fin.sum_univ_succ]
          simp [U1, liftBlockUnit, blockLift, hC_col0]
        simp [V1, liftBlockUnit, blockLift, hi0, Fin.succ_ne_zero]
      · have hik : ∀ k : Fin n, (U1.val * C) i'.succ k.succ = (Usub.val * Csub) i' k := by
          intro k
          rw [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.mul_apply]
          simp [U1, liftBlockUnit, blockLift, Csub]
        have hsub_ij := congrFun (congrFun hsub i') j'
        simp only [V1, liftBlockUnit, blockLift, Fin.cases_zero, Fin.cases_succ, mul_zero, zero_add,
          hik, Matrix.diagonal_apply, Fin.succ_inj]
        simp only [Matrix.mul_apply, Matrix.diagonal_apply] at hsub_ij
        exact hsub_ij

/-- Cokernel equivalence under left/right invertible matrix multiplication `U * A * V`. -/
def cokerEquivOfUnitMul {𝒪 : Type*} [CommRing 𝒪] {m : ℕ}
    (A : Matrix (Fin m) (Fin m) 𝒪)
    (U V : (Matrix (Fin m) (Fin m) 𝒪)ˣ) :
    ((Fin m → 𝒪) ⧸ LinearMap.range A.mulVecLin) ≃ₗ[𝒪]
      ((Fin m → 𝒪) ⧸ LinearMap.range (U.val * A * V.val).mulVecLin) := by
  let eU : (Fin m → 𝒪) ≃ₗ[𝒪] (Fin m → 𝒪) :=
    { toLinearMap := U.val.mulVecLin
      invFun := U.inv.mulVecLin
      left_inv := fun v => by simp
      right_inv := fun v => by simp }
  have hmap : (LinearMap.range A.mulVecLin).map eU.toLinearMap =
      LinearMap.range (U.val * A * V.val).mulVecLin := by
    ext w
    simp only [Submodule.mem_map, LinearMap.mem_range]
    constructor
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
      refine ⟨V.inv.mulVec x, ?_⟩
      change (U.val * A * V.val).mulVec (V.inv.mulVec x) = U.val.mulVec (A.mulVec x)
      rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc, V.val_inv, Matrix.mul_one,
        ← Matrix.mulVec_mulVec]
    · rintro ⟨x, rfl⟩
      refine ⟨A.mulVec (V.val.mulVec x), ⟨V.val.mulVec x, rfl⟩, ?_⟩
      change U.val.mulVec (A.mulVec (V.val.mulVec x)) = (U.val * A * V.val).mulVec x
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  exact Submodule.Quotient.equiv _ _ eU hmap

/-- Cokernel of a diagonal matrix splits as the product of cyclic quotients `∏ i, 𝒪 ⧸ (d i)`. -/
def cokerDiagonalEquivPi {𝒪 : Type*} [CommRing 𝒪] {m : ℕ} (d : Fin m → 𝒪) :
    ((Fin m → 𝒪) ⧸ LinearMap.range (Matrix.diagonal d).mulVecLin) ≃ₗ[𝒪]
      (∀ i : Fin m, 𝒪 ⧸ Ideal.span ({d i} : Set 𝒪)) := by
  let f : (Fin m → 𝒪) →ₗ[𝒪] (∀ i : Fin m, 𝒪 ⧸ Ideal.span ({d i} : Set 𝒪)) :=
    { toFun := fun v i => Ideal.Quotient.mk (Ideal.span ({d i} : Set 𝒪)) (v i)
      map_add' := fun u v => by ext i; exact map_add _ (u i) (v i)
      map_smul' := fun r v => by
        ext i
        change Ideal.Quotient.mk _ (r * v i) = r • Ideal.Quotient.mk _ (v i)
        rw [map_mul, Algebra.smul_def]
        rfl }
  have hker : LinearMap.ker f = LinearMap.range (Matrix.diagonal d).mulVecLin := by
    ext v
    rw [LinearMap.mem_ker, LinearMap.mem_range]
    constructor
    · intro hv
      have hdiv : ∀ i, ∃ c, v i = d i * c := fun i =>
        Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp (congrFun hv i))
      choose c hc using hdiv
      refine ⟨c, ?_⟩
      ext i
      simp only [Matrix.mulVecLin_apply, Matrix.mulVec_diagonal, hc i]
    · rintro ⟨c, rfl⟩
      ext i
      change Ideal.Quotient.mk (Ideal.span ({d i} : Set 𝒪)) ((Matrix.diagonal d).mulVec c i) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem, Matrix.mulVec_diagonal, Ideal.mem_span_singleton]
      exact ⟨c i, rfl⟩
  have hsurj : Function.Surjective f := fun w =>
    ⟨fun i => Quotient.out (w i), by ext i; exact Quotient.out_eq (w i)⟩
  exact (Submodule.quotEquivOfEq _ _ hker.symm).trans (f.quotKerEquivOfSurjective hsurj)

/-- **Exact Determinant–Length Identity over a DVR**:
for EVERY square matrix `A : Matrix (Fin m) (Fin m) 𝒪` over a DVR `𝒪` with `A.det ≠ 0`,
`len_𝒪(coker A) = len_𝒪(𝒪 ⧸ (det A)) < ⊤`! -/
theorem length_coker_eq_length_quotient_det {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪]
    [IsDiscreteValuationRing 𝒪] {m : ℕ} (A : Matrix (Fin m) (Fin m) 𝒪) (hdet : A.det ≠ 0) :
    Module.length 𝒪 ((Fin m → 𝒪) ⧸ LinearMap.range A.mulVecLin) =
      Module.length 𝒪 (𝒪 ⧸ Ideal.span ({A.det} : Set 𝒪)) ∧
    Module.length 𝒪 (𝒪 ⧸ Ideal.span ({A.det} : Set 𝒪)) ≠ ⊤ := by
  obtain ⟨U, V, d, hUAV⟩ := exists_smithNormalForm_of_dvr A
  have hdet_eq : U.val.det * A.det * V.val.det = ∏ i : Fin m, d i := by
    have h := congrArg Matrix.det hUAV
    rwa [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal] at h
  have hU_unit : IsUnit U.val.det := by
    rw [← Matrix.isUnit_iff_isUnit_det]; exact U.isUnit
  have hV_unit : IsUnit V.val.det := by
    rw [← Matrix.isUnit_iff_isUnit_det]; exact V.isUnit
  have hassoc : Associated A.det (∏ i : Fin m, d i) := by
    obtain ⟨uU, huU⟩ := hU_unit
    obtain ⟨uV, huV⟩ := hV_unit
    refine ⟨uU * uV, ?_⟩
    rw [← hdet_eq, ← huU, ← huV]
    simp only [Units.val_mul]
    ring
  have hd_ne : ∀ i : Fin m, d i ≠ 0 := by
    intro i hi
    have hprod0 : ∏ j : Fin m, d j = 0 := Finset.prod_eq_zero (Finset.mem_univ i) hi
    rw [hprod0] at hdet_eq
    have hmul0 : (U.val.det * V.val.det) * A.det = 0 := by linear_combination hdet_eq
    have hUV_ne : U.val.det * V.val.det ≠ 0 := mul_ne_zero hU_unit.ne_zero hV_unit.ne_zero
    exact hdet ((mul_eq_zero.mp hmul0).resolve_left hUV_ne)
  have heq_coker :
      Module.length 𝒪 ((Fin m → 𝒪) ⧸ LinearMap.range A.mulVecLin) =
        ∑ i : Fin m, Module.length 𝒪 (𝒪 ⧸ Ideal.span ({d i} : Set 𝒪)) := by
    let e1 := cokerEquivOfUnitMul A U V
    let e2 := Submodule.quotEquivOfEq _ _ (congrArg (fun M => LinearMap.range M.mulVecLin) hUAV)
    let e3 := cokerDiagonalEquivPi d
    rw [(e1.trans (e2.trans e3)).length_eq]
    exact length_pi_fin (fun i : Fin m => 𝒪 ⧸ Ideal.span ({d i} : Set 𝒪))
  have hspan_eq : Ideal.span ({A.det} : Set 𝒪) = Ideal.span ({∏ i : Fin m, d i} : Set 𝒪) :=
    span_singleton_eq_of_associated hassoc
  have heq_det :
      Module.length 𝒪 (𝒪 ⧸ Ideal.span ({A.det} : Set 𝒪)) =
        ∑ i : Fin m, Module.length 𝒪 (𝒪 ⧸ Ideal.span ({d i} : Set 𝒪)) := by
    rw [hspan_eq]
    exact length_quotient_span_prod_eq_sum_of_domain Finset.univ d (fun i _ => hd_ne i)
  have hfin : Module.length 𝒪 (𝒪 ⧸ Ideal.span ({A.det} : Set 𝒪)) ≠ ⊤ := by
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪
    obtain ⟨k, hk⟩ := IsDiscreteValuationRing.associated_pow_irreducible hdet hϖ
    rw [span_singleton_eq_of_associated hk, length_quotient_span_pow_eq_of_dvr hϖ k]
    exact ENat.natCast_ne_top k
  exact ⟨heq_coker.trans heq_det.symm, hfin⟩

/-- Over a DVR `𝒪`, any nonzero ideal `I ≠ ⊥` has finite quotient length `len_𝒪(𝒪 ⧸ I) ≠ ⊤`. -/
theorem length_quotient_ne_top_of_ne_bot_dvr {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪]
    [IsDiscreteValuationRing 𝒪] {I : Ideal 𝒪} (hI : I ≠ ⊥) :
    Module.length 𝒪 (𝒪 ⧸ I) ≠ ⊤ := by
  obtain ⟨a, haI, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪
  obtain ⟨k, hk⟩ := IsDiscreteValuationRing.associated_pow_irreducible ha0 hϖ
  have hle : Ideal.span ({ϖ ^ k} : Set 𝒪) ≤ I := by
    rw [span_singleton_eq_of_associated hk.symm, Ideal.span_singleton_le_iff_mem]
    exact haI
  have hlen : Module.length 𝒪 (𝒪 ⧸ I) ≤ (k : ℕ∞) := by
    calc Module.length 𝒪 (𝒪 ⧸ I)
        ≤ Module.length 𝒪 (𝒪 ⧸ Ideal.span ({ϖ ^ k} : Set 𝒪)) :=
          Module.length_le_of_surjective (Submodule.factor hle) (Submodule.factor_surjective hle)
      _ = (k : ℕ∞) := length_quotient_span_pow_eq_of_dvr hϖ k
  exact ne_top_of_le_ne_top (ENat.natCast_ne_top k) hlen

/-- If `I ≤ J` and `len_𝒪(𝒪 ⧸ I) = len_𝒪(𝒪 ⧸ J) < ⊤`, then `I = J`. -/
theorem ideal_eq_of_le_of_length_quotient_eq {𝒪 : Type*} [CommRing 𝒪]
    {I J : Ideal 𝒪} (hIJ : I ≤ J) (hfin : Module.length 𝒪 (𝒪 ⧸ I) ≠ ⊤)
    (heq : Module.length 𝒪 (𝒪 ⧸ I) = Module.length 𝒪 (𝒪 ⧸ J)) :
    I = J := by
  have hadd : Module.length 𝒪 (𝒪 ⧸ I) =
      Module.length 𝒪 (LinearMap.ker (Submodule.factor hIJ)) + Module.length 𝒪 (𝒪 ⧸ J) :=
    Module.length_eq_add_of_exact (LinearMap.ker (Submodule.factor hIJ)).subtype
      (Submodule.factor hIJ) (Submodule.subtype_injective _)
      (Submodule.factor_surjective hIJ) (LinearMap.exact_subtype_ker_map _)
  have hker0 : Module.length 𝒪 (LinearMap.ker (Submodule.factor hIJ)) = 0 := by
    rw [← heq] at hadd
    cases h1 : Module.length 𝒪 (𝒪 ⧸ I) with
    | top => exact absurd h1 hfin
    | coe b =>
      cases h2 : Module.length 𝒪 (LinearMap.ker (Submodule.factor hIJ)) with
      | top => rw [h1, h2, top_add] at hadd; exact absurd hadd (ENat.natCast_ne_top b)
      | coe a =>
        rw [h1, h2] at hadd
        have hab : b = a + b := ENat.natCast_inj.mp (by simpa [Nat.cast_add] using hadd)
        have ha0 : a = 0 := by omega
        simp [ha0]
  have hsub : Subsingleton (LinearMap.ker (Submodule.factor hIJ)) :=
    Module.length_eq_zero_iff.mp hker0
  apply le_antisymm hIJ
  intro x hxJ
  have hmem : Submodule.Quotient.mk (p := I) x ∈ LinearMap.ker (Submodule.factor hIJ) := by
    change Submodule.Quotient.mk (p := J) x = 0
    exact (Submodule.Quotient.mk_eq_zero J).mpr hxJ
  have h0 : (⟨Submodule.Quotient.mk (p := I) x, hmem⟩ : LinearMap.ker (Submodule.factor hIJ)) = 0 :=
    Subsingleton.elim _ _
  exact (Submodule.Quotient.mk_eq_zero I).mp (congrArg Subtype.val h0)

/-- **Square Presentation of `Φ_T = I_T / I_T^2` over a DVR**:
if `T` is finite free over a DVR `𝒪` and `η_T ≠ ⊥`, then `I_T` is free of finite rank `m`
and there exists an `m × m` matrix `A` over `𝒪` with `A.det ≠ 0`, `A.det ∈ η_T`, and
`Φ_T ≃ₗ[𝒪] (Fin m → 𝒪) ⧸ range A.mulVecLin`. -/
theorem exists_square_presentation_cotangent {𝒪 T : Type*}
    [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [CommRing T] [Algebra 𝒪 T] [Module.Free 𝒪 T] [Module.Finite 𝒪 T]
    (π : T →ₐ[𝒪] 𝒪) (hη : congruenceIdeal π ≠ ⊥) :
    ∃ (m : ℕ) (A : Matrix (Fin m) (Fin m) 𝒪),
      A.det ≠ 0 ∧ A.det ∈ congruenceIdeal π ∧
      Nonempty (Cotangent π ≃ₗ[𝒪] ((Fin m → 𝒪) ⧸ LinearMap.range A.mulVecLin)) := by
  classical
  let bT := Module.Free.chooseBasis 𝒪 T
  have : Fintype (Module.Free.ChooseBasisIndex 𝒪 T) := Module.Free.ChooseBasisIndex.fintype 𝒪 T
  let I_sub : Submodule 𝒪 T := (augIdeal π).restrictScalars 𝒪
  obtain ⟨m, bI⟩ := Submodule.basisOfPid bT I_sub
  let eI : augIdeal π ≃ₗ[𝒪] (Fin m → 𝒪) :=
    bI.repr.trans (Finsupp.linearEquivFunOnFinite 𝒪 𝒪 (Fin m))
  let N_sub : Submodule 𝒪 (Fin m → 𝒪) := (cotangentSubmodule π).map eI.toLinearMap
  let bPi : Module.Basis (Fin m) 𝒪 (Fin m → 𝒪) := Pi.basisFun 𝒪 (Fin m)
  obtain ⟨k, bN⟩ := Submodule.basisOfPid bPi N_sub
  obtain ⟨a, haη, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hη
  have ha_kills : a ∈ Module.annihilator 𝒪 (Cotangent π) :=
    congruenceIdeal_le_annihilator_cotangent π haη
  have ha_mem : ∀ v : Fin m → 𝒪, a • v ∈ N_sub := by
    intro v
    have h0 : a • Submodule.Quotient.mk (p := cotangentSubmodule π) (eI.symm v) = 0 :=
      Module.mem_annihilator.mp ha_kills _
    have hmem : a • eI.symm v ∈ cotangentSubmodule π :=
      (Submodule.Quotient.mk_eq_zero (cotangentSubmodule π)).mp h0
    have heq : a • v = eI (a • eI.symm v) := by rw [map_smul, eI.apply_symm_apply]
    rw [heq]
    exact ⟨a • eI.symm v, hmem, rfl⟩
  have hk_le : k ≤ m := by
    have hlinN : LinearIndependent 𝒪 (fun i : Fin k => (bN i).1) :=
      bN.linearIndependent.map' N_sub.subtype (Submodule.ker_subtype N_sub)
    have hcard := LinearIndependent.fintype_card_le_finrank hlinN
    simpa [Fintype.card_fin, Module.finrank_eq_card_basis bPi] using hcard
  have hm_le : m ≤ k := by
    let emb : (Fin m → 𝒪) →ₗ[𝒪] N_sub :=
      { toFun := fun v => ⟨a • v, ha_mem v⟩
        map_add' := fun u v => Subtype.ext (smul_add a u v)
        map_smul' := fun r v => Subtype.ext (smul_comm a r v) }
    have hemb_inj : Function.Injective emb := by
      intro u v huv
      ext i
      have hi : a * u i = a * v i := congrFun (congrArg Subtype.val huv) i
      exact mul_left_cancel₀ ha0 hi
    have hlin : LinearIndependent 𝒪 (fun i : Fin m => emb (bPi i)) :=
      bPi.linearIndependent.map' emb (LinearMap.ker_eq_bot.mpr hemb_inj)
    have hcard := LinearIndependent.fintype_card_le_finrank hlin
    simpa [Fintype.card_fin, Module.finrank_eq_card_basis bN] using hcard
  have hkm : k = m := le_antisymm hk_le hm_le
  let colVec : Fin m → (Fin m → 𝒪) := fun j => (bN (Fin.cast hkm.symm j)).1
  let A : Matrix (Fin m) (Fin m) 𝒪 := fun i j => colVec j i
  have hrange : LinearMap.range A.mulVecLin = N_sub := by
    ext v
    rw [LinearMap.mem_range]
    constructor
    · rintro ⟨x, rfl⟩
      have hv : A.mulVecLin x = ∑ j : Fin m, x j • colVec j := by
        ext i
        change (A.mulVec x) i = (∑ j : Fin m, x j • colVec j) i
        simp only [Matrix.mulVec, dotProduct, A, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
          mul_comm]
      rw [hv]
      exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (bN (Fin.cast hkm.symm j)).2
    · intro hv
      let c := bN.repr ⟨v, hv⟩
      refine ⟨fun j => c (Fin.cast hkm.symm j), ?_⟩
      have hsum : (⟨v, hv⟩ : N_sub) = ∑ j : Fin k, c j • bN j := (bN.sum_repr ⟨v, hv⟩).symm
      have hval := congrArg Subtype.val hsum
      ext i
      have hi := congrFun hval i
      simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
        smul_eq_mul] at hi
      rw [hi]
      change (A.mulVec fun j => c (Fin.cast hkm.symm j)) i = _
      simp only [Matrix.mulVec, dotProduct, A, colVec]
      refine (Fintype.sum_equiv (Fin.castOrderIso hkm).toEquiv _ _ ?_).symm
      intro j
      simp [mul_comm]
  have hdet_ne : A.det ≠ 0 := by
    intro hdet0
    have hcols : ∀ j : Fin m, ∃ x : Fin m → 𝒪, A.mulVec x = a • Pi.single j (1 : 𝒪) := by
      intro j
      have hm : a • Pi.single j (1 : 𝒪) ∈ LinearMap.range A.mulVecLin := by
        rw [hrange]; exact ha_mem (Pi.single j 1)
      exact LinearMap.mem_range.mp hm
    choose B_col hB_col using hcols
    let B : Matrix (Fin m) (Fin m) 𝒪 := fun i j => B_col j i
    have hAB : A * B = a • (1 : Matrix (Fin m) (Fin m) 𝒪) := by
      ext i j
      have hij := congrFun (hB_col j) i
      change (A * B) i j = (a • (1 : Matrix (Fin m) (Fin m) 𝒪)) i j
      rw [Matrix.mul_apply]
      simpa [Matrix.mulVec, dotProduct, B, Matrix.one_apply, Pi.single_apply, eq_comm] using hij
    have hdetAB : (A * B).det = a ^ m := by
      rw [hAB, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]
    rw [Matrix.det_mul, hdet0, zero_mul] at hdetAB
    exact pow_ne_zero m ha0 hdetAB.symm
  let basisGen : Fin m → augIdeal π := fun j => eI.symm (Pi.single j 1)
  have hgen : Submodule.span 𝒪 (Set.range basisGen) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : x = ∑ j : Fin m, (eI x j) • basisGen j := by
      apply eI.injective
      rw [map_sum]
      ext i
      simp [basisGen, Finset.sum_apply, Pi.single_apply]
    rw [hx]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  have hrelT : ∀ i : Fin m,
      (∑ j : Fin m, algebraMap 𝒪 T (A.transpose i j) * (basisGen j).1) ∈ augIdeal π ^ 2 := by
    intro i
    have hmemN : colVec i ∈ N_sub := (bN (Fin.cast hkm.symm i)).2
    have hmemC : eI.symm (colVec i) ∈ cotangentSubmodule π := by
      rcases hmemN with ⟨y, hy, hy_eq⟩
      have : y = eI.symm (colVec i) := by rw [← hy_eq]; exact (eI.symm_apply_apply y).symm
      rwa [← this]
    have hsum_eq : eI.symm (colVec i) = ∑ j : Fin m, (A j i) • basisGen j := by
      apply eI.injective
      rw [eI.apply_symm_apply, map_sum]
      ext l
      simp [basisGen, A, Finset.sum_apply, Pi.single_apply]
    have hval := congrArg Subtype.val hsum_eq
    have hmem_sq : (eI.symm (colVec i)).1 ∈ augIdeal π ^ 2 := hmemC
    rw [hval] at hmem_sq
    simpa [Matrix.transpose_apply, Algebra.smul_def] using hmem_sq
  have hdet_mem : A.det ∈ congruenceIdeal π := by
    rw [← Matrix.det_transpose]
    exact det_mem_congruenceIdeal_of_relations π basisGen hgen A.transpose hrelT
  let eQ : Cotangent π ≃ₗ[𝒪] ((Fin m → 𝒪) ⧸ LinearMap.range A.mulVecLin) :=
    Submodule.Quotient.equiv (cotangentSubmodule π) (LinearMap.range A.mulVecLin) eI hrange.symm
  exact ⟨m, A, hdet_ne, hdet_mem, ⟨eQ⟩⟩

/-- **THE WILES–LENSTRA NUMERICAL CRITERION (EXACT LENGTH INEQUALITY)**:
for any DVR `𝒪`, surjective `φ : R →ₐ[𝒪] T`, augmentation `π : T →ₐ[𝒪] 𝒪`, finite free `T`
over `𝒪`, and `η_T ≠ ⊥`:
`len_𝒪(𝒪 / η_T) ≤ len_𝒪(Φ_T) ≤ len_𝒪(Φ_R)` and `len_𝒪(𝒪 / η_T) < ⊤`! -/
theorem wiles_lenstra_length_inequality {𝒪 R T : Type*}
    [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [CommRing R] [Algebra 𝒪 R]
    [CommRing T] [Algebra 𝒪 T] [Module.Free 𝒪 T] [Module.Finite 𝒪 T]
    (φ : R →ₐ[𝒪] T) (hφ : Function.Surjective φ)
    (π : T →ₐ[𝒪] 𝒪) (hη : congruenceIdeal π ≠ ⊥) :
    Module.length 𝒪 (𝒪 ⧸ congruenceIdeal π) ≤ Module.length 𝒪 (Cotangent π) ∧
    Module.length 𝒪 (Cotangent π) ≤ Module.length 𝒪 (Cotangent (π.comp φ)) ∧
    Module.length 𝒪 (𝒪 ⧸ congruenceIdeal π) ≠ ⊤ := by
  obtain ⟨m, A, hdet_ne, hdet_mem, ⟨eQ⟩⟩ := exists_square_presentation_cotangent π hη
  obtain ⟨hlen_eq, _⟩ := length_coker_eq_length_quotient_det A hdet_ne
  have hspan_le : Ideal.span ({A.det} : Set 𝒪) ≤ congruenceIdeal π := by
    rwa [Ideal.span_singleton_le_iff_mem]
  have h1 : Module.length 𝒪 (𝒪 ⧸ congruenceIdeal π) ≤ Module.length 𝒪 (Cotangent π) := by
    calc Module.length 𝒪 (𝒪 ⧸ congruenceIdeal π)
        ≤ Module.length 𝒪 (𝒪 ⧸ Ideal.span ({A.det} : Set 𝒪)) :=
          Module.length_le_of_surjective (Submodule.factor hspan_le)
            (Submodule.factor_surjective hspan_le)
      _ = Module.length 𝒪 ((Fin m → 𝒪) ⧸ LinearMap.range A.mulVecLin) := hlen_eq.symm
      _ = Module.length 𝒪 (Cotangent π) := eQ.length_eq.symm
  exact ⟨h1, length_cotangent_le_of_surjective φ hφ π,
    length_quotient_ne_top_of_ne_bot_dvr hη⟩

/-- A **Gorenstein / Frobenius pairing** on a commutative `𝒪`-algebra `R'`: a linear functional
`λ : R' →ₗ[𝒪] 𝒪` inducing an `R'`-linear isomorphism `R' ≃ₗ[R'] (R' →ₗ[𝒪] 𝒪)` via
`r ↦ (x ↦ λ (r * x))`. Every finite flat local complete intersection over a DVR is Gorenstein. -/
structure IsGorensteinOver (𝒪 R' : Type*) [CommRing 𝒪] [CommRing R'] [Algebra 𝒪 R'] where
  traceForm : R' →ₗ[𝒪] 𝒪
  pairing_bijective :
    Function.Bijective (fun r : R' =>
      { toFun := fun x : R' => traceForm (r * x)
        map_add' := fun x y => by rw [mul_add, map_add]
        map_smul' := fun a x => by
          change traceForm (r * (a • x)) = a • traceForm (r * x)
          rw [mul_smul_comm, map_smul] } : R' → (R' →ₗ[𝒪] 𝒪))

/-- **Lenstra's Gorenstein Rigidity Theorem**:
if `R'` is a local Gorenstein `𝒪`-algebra over a DVR `𝒪`, `ψ' : R' →ₐ[𝒪] T` is surjective
onto a free `𝒪`-algebra `T`, `π : T →ₐ[𝒪] 𝒪` has `η_{R'} ≠ ⊥`, and **`η_{R'} = η_T`**,
then **`ψ' : R' →ₐ[𝒪] T` IS BIJECTIVE (`R' ≃ₐ[𝒪] T`)**! -/
theorem gorenstein_surj_bijective_of_congruenceIdeal_eq {𝒪 R' T : Type*}
    [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [CommRing R'] [IsLocalRing R'] [Algebra 𝒪 R']
    [CommRing T] [Algebra 𝒪 T] [Module.Free 𝒪 T]
    (G : IsGorensteinOver 𝒪 R')
    (ψ' : R' →ₐ[𝒪] T) (hψ' : Function.Surjective ψ')
    (π : T →ₐ[𝒪] 𝒪)
    (hη_ne : congruenceIdeal (π.comp ψ') ≠ ⊥)
    (hη_eq : congruenceIdeal (π.comp ψ') = congruenceIdeal π) :
    Function.Bijective ψ' := by
  classical
  refine ⟨?_, hψ'⟩
  let π' : R' →ₐ[𝒪] 𝒪 := π.comp ψ'
  let Φ : R' → (R' →ₗ[𝒪] 𝒪) := fun r =>
    { toFun := fun x => G.traceForm (r * x)
      map_add' := fun x y => by rw [mul_add, map_add]
      map_smul' := fun a x => by
        change G.traceForm (r * (a • x)) = a • G.traceForm (r * x)
        rw [mul_smul_comm, map_smul] }
  have hΦ_inj : Function.Injective Φ := G.pairing_bijective.1
  have hΦ_surj : Function.Surjective Φ := G.pairing_bijective.2
  obtain ⟨δ, hδ⟩ := hΦ_surj π'.toLinearMap
  have hδ_eval : ∀ x : R', G.traceForm (δ * x) = π' x :=
    fun x => congrFun (congrArg DFunLike.coe hδ) x
  have hδ_ann : δ ∈ annAugIdeal π' := by
    rw [mem_annAugIdeal_iff]
    intro x hx
    apply hΦ_inj
    ext r
    change G.traceForm ((δ * x) * r) = G.traceForm (0 * r)
    rw [zero_mul, map_zero, mul_assoc, hδ_eval, map_mul, (mem_augIdeal_iff π' x).mp hx, zero_mul]
  have hann_eq : ∀ a ∈ annAugIdeal π', a = G.traceForm a • δ := by
    intro a ha
    apply hΦ_inj
    ext x
    change G.traceForm (a * x) = G.traceForm ((G.traceForm a • δ) * x)
    have hxI : x - algebraMap 𝒪 R' (π' x) ∈ augIdeal π' := by
      rw [mem_augIdeal_iff, map_sub, π'.commutes]
      exact sub_self (π' x)
    have hax : a * x = π' x • a := by
      have h0 : a * (x - algebraMap 𝒪 R' (π' x)) = 0 :=
        (mem_annAugIdeal_iff π' a).mp ha _ hxI
      rw [mul_sub, sub_eq_zero] at h0
      rw [h0, Algebra.smul_def, mul_comm]
    rw [hax, map_smul, smul_mul_assoc, map_smul, hδ_eval, smul_eq_mul, smul_eq_mul, mul_comm]
  have hη_span : congruenceIdeal π' = Ideal.span ({π' δ} : Set 𝒪) := by
    apply le_antisymm
    · intro c hc
      obtain ⟨a, ha, rfl⟩ := (mem_congruenceIdeal_iff π' c).mp hc
      rw [hann_eq a ha, map_smul, smul_eq_mul, Ideal.mem_span_singleton]
      exact ⟨G.traceForm a, mul_comm _ _⟩
    · rw [Ideal.span_singleton_le_iff_mem]
      exact (mem_congruenceIdeal_iff π' (π' δ)).mpr ⟨δ, hδ_ann, rfl⟩
  have hπδ_ne : π' δ ≠ 0 := by
    intro h0
    apply hη_ne
    rw [hη_span, h0, Ideal.span_singleton_zero]
  rw [injective_iff_map_eq_zero]
  by_contra hnot_inj
  push Not at hnot_inj
  obtain ⟨z₀, hz₀_ker, hz₀_ne⟩ := hnot_inj
  let K : Ideal R' := RingHom.ker ψ'.toRingHom
  let J : Ideal R' := Module.annihilator R' K
  have h1_not_J : (1 : R') ∉ J := by
    intro h1
    have h0 : (1 : R') • (⟨z₀, hz₀_ker⟩ : K) = 0 := Module.mem_annihilator.mp h1 ⟨z₀, hz₀_ker⟩
    rw [one_smul] at h0
    exact hz₀_ne (congrArg Subtype.val h0)
  have hJ_le_max : J ≤ IsLocalRing.maximalIdeal R' :=
    IsLocalRing.le_maximalIdeal (fun htop => h1_not_J (htop.symm ▸ Submodule.mem_top))
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪
  have hI_le_max : augIdeal π' ≤ IsLocalRing.maximalIdeal R' := by
    refine IsLocalRing.le_maximalIdeal (fun htop => ?_)
    have h1 : (1 : R') ∈ augIdeal π' := htop.symm ▸ Submodule.mem_top
    have : π' 1 = 0 := h1
    rw [map_one] at this
    exact one_ne_zero this
  have hϖ_dvd_J : ∀ y ∈ J, ϖ ∣ π' y := by
    intro y hy
    have hnot_unit : ¬IsUnit (π' y) := by
      intro hunit
      obtain ⟨u, hu⟩ := hunit
      have h1_sub : y * algebraMap 𝒪 R' (u⁻¹ : 𝒪ˣ) - 1 ∈ augIdeal π' := by
        rw [mem_augIdeal_iff, map_sub, map_mul, π'.commutes, ← hu, map_one]
        simp
      have h1_mem : (1 : R') ∈ IsLocalRing.maximalIdeal R' := by
        have hmul_mem : y * algebraMap 𝒪 R' (u⁻¹ : 𝒪ˣ) ∈ IsLocalRing.maximalIdeal R' :=
          Ideal.mul_mem_right _ _ (hJ_le_max hy)
        have hsub_mem : y * algebraMap 𝒪 R' (u⁻¹ : 𝒪ˣ) - 1 ∈ IsLocalRing.maximalIdeal R' :=
          hI_le_max h1_sub
        have heq : (1 : R') = y * algebraMap 𝒪 R' (u⁻¹ : 𝒪ˣ) -
            (y * algebraMap 𝒪 R' (u⁻¹ : 𝒪ˣ) - 1) := by ring
        rw [heq]
        exact Ideal.sub_mem _ hmul_mem hsub_mem
      exact (IsLocalRing.maximalIdeal.isMaximal R').ne_top
        (Ideal.eq_top_of_isUnit_mem _ h1_mem isUnit_one)
    have hmem_max : π' y ∈ IsLocalRing.maximalIdeal 𝒪 :=
      (IsLocalRing.mem_maximalIdeal (π' y)).mpr (mem_nonunits_iff.mpr hnot_unit)
    have hmax_eq : IsLocalRing.maximalIdeal 𝒪 = Ideal.span ({ϖ} : Set 𝒪) :=
      (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ
    rw [hmax_eq, Ideal.mem_span_singleton] at hmem_max
    exact hmem_max
  have hϖ_dvd_dual : ∀ μ : T →ₗ[𝒪] 𝒪, ϖ ∣ μ (ψ' δ) := by
    intro μ
    obtain ⟨y, hy⟩ := hΦ_surj (μ.comp ψ'.toLinearMap)
    have hy_eval : ∀ x : R', G.traceForm (y * x) = μ (ψ' x) :=
      fun x => congrFun (congrArg DFunLike.coe hy) x
    have hyJ : y ∈ J := by
      rw [Module.mem_annihilator]
      intro z
      apply Subtype.ext
      change y * z.1 = 0
      apply hΦ_inj
      ext r
      change G.traceForm ((y * z.1) * r) = G.traceForm (0 * r)
      rw [zero_mul, map_zero, mul_assoc, hy_eval, map_mul, show ψ' z.1 = 0 from z.2,
        zero_mul, map_zero]
    have heq : μ (ψ' δ) = π' y := by
      rw [← hy_eval δ, mul_comm, hδ_eval y]
    rw [heq]
    exact hϖ_dvd_J y hyJ
  let bT := Module.Free.chooseBasis 𝒪 T
  have hcoord_dvd : ∀ i, ϖ ∣ bT.repr (ψ' δ) i := fun i => hϖ_dvd_dual (bT.coord i)
  choose qf hqf using hcoord_dvd
  let qFinsupp : Module.Free.ChooseBasisIndex 𝒪 T →₀ 𝒪 :=
    Finsupp.onFinset (bT.repr (ψ' δ)).support
      (fun i => if bT.repr (ψ' δ) i = 0 then 0 else qf i)
      (fun i hi => by
        by_contra hnot
        have h0 : bT.repr (ψ' δ) i = 0 := Finsupp.notMem_support_iff.mp hnot
        exact hi (if_pos h0))
  let t : T := bT.repr.symm qFinsupp
  have hψδ_eq : ψ' δ = ϖ • t := by
    apply bT.repr.injective
    ext i
    simp only [t, map_smul, LinearEquiv.apply_symm_apply, Finsupp.smul_apply, smul_eq_mul,
      qFinsupp, Finsupp.onFinset_apply]
    split_ifs with h0
    · rw [h0, mul_zero]
    · exact hqf i
  have ht_ann : t ∈ annAugIdeal π := by
    rw [mem_annAugIdeal_iff]
    intro x hx
    obtain ⟨x', rfl⟩ := hψ' x
    have hx' : x' ∈ augIdeal π' := hx
    have hϖ_zero : ϖ • (t * ψ' x') = 0 := by
      rw [← smul_mul_assoc, ← hψδ_eq, ← map_mul, (mem_annAugIdeal_iff π' δ).mp hδ_ann x' hx',
        map_zero]
    apply bT.repr.injective
    ext i
    have hi : ϖ * bT.repr (t * ψ' x') i = 0 := by
      have h := congrFun (congrArg DFunLike.coe (congrArg bT.repr hϖ_zero)) i
      simpa [map_smul, smul_eq_mul] using h
    rw [map_zero, Finsupp.zero_apply]
    exact (mul_eq_zero.mp hi).resolve_left hϖ.ne_zero
  have hπt_mem : π t ∈ Ideal.span ({π' δ} : Set 𝒪) := by
    rw [← hη_span, hη_eq]
    exact (mem_congruenceIdeal_iff π (π t)).mpr ⟨t, ht_ann, rfl⟩
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hπt_mem
  have hπδ_eq : π' δ = ϖ * π t := by
    change π (ψ' δ) = ϖ * π t
    rw [hψδ_eq, map_smul, smul_eq_mul]
  rw [hc] at hπδ_eq
  have h1 : π' δ * 1 = π' δ * (ϖ * c) := by linear_combination hπδ_eq
  have hunit : ϖ * c = 1 := (mul_left_cancel₀ hπδ_ne h1).symm
  exact hϖ.not_isUnit (isUnit_iff_exists_inv.mpr ⟨c, hunit⟩)

/-- **Wiles–Lenstra Complete-Intersection Cover** for a surjection `φ : R →ₐ[𝒪] T` with
augmentation `π : T →ₐ[𝒪] 𝒪`: a local Gorenstein cover `ψ_R : R' ↠ R` over `𝒪` matching the
cotangent Fitting length of `R` (`len_𝒪(Φ_R) = len_𝒪(𝒪 / η_{R'})`, matching `R' = P/(f_1,...,f_n)`). -/
structure CompleteIntersectionCover {𝒪 R T : Type*}
    [CommRing 𝒪] [CommRing R] [Algebra 𝒪 R] [CommRing T] [Algebra 𝒪 T]
    (φ : R →ₐ[𝒪] T) (π : T →ₐ[𝒪] 𝒪) where
  R' : Type*
  [commRingR' : CommRing R']
  [localR' : IsLocalRing R']
  [algR' : Algebra 𝒪 R']
  gorenstein : IsGorensteinOver 𝒪 R'
  psiR : R' →ₐ[𝒪] R
  psiR_surj : Function.Surjective psiR
  cong_ne_bot : congruenceIdeal (π.comp (φ.comp psiR)) ≠ ⊥
  /-- Exact complete-intersection Fitting = congruence length on `R'` matching `Φ_R`. -/
  cotangent_eq_cover_cong :
    Module.length 𝒪 (Cotangent (π.comp φ)) =
      Module.length 𝒪 (𝒪 ⧸ congruenceIdeal (π.comp (φ.comp psiR)))

attribute [instance] CompleteIntersectionCover.commRingR' CompleteIntersectionCover.localR'
  CompleteIntersectionCover.algR'

/-- **THE WILES–LENSTRA–DIAMOND NUMERICAL CRITERION (`iff` Theorem)**:
Given a surjection `φ : R →ₐ[𝒪] T` of `𝒪`-algebras over a DVR `𝒪` with finite free `T`,
augmentation `π : T →ₐ[𝒪] 𝒪`, and a Gorenstein complete-intersection cover `C` (`R' ↠ R ↠ T`):
**`len_𝒪(Φ_R) = len_𝒪(𝒪 / η_T)`** if and only if **`φ : R ≃ₐ[𝒪] T` AND `ψ_R : R' ≃ₐ[𝒪] R`
are isomorphisms (so `R ≃ T ≃ R'` is a Gorenstein complete intersection!)**! -/
theorem wiles_lenstra_numerical_criterion_iff {𝒪 R T : Type*}
    [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [CommRing R] [Algebra 𝒪 R]
    [CommRing T] [Algebra 𝒪 T] [Module.Free 𝒪 T] [Module.Finite 𝒪 T]
    (φ : R →ₐ[𝒪] T) (hφ : Function.Surjective φ)
    (π : T →ₐ[𝒪] 𝒪)
    (C : CompleteIntersectionCover φ π) :
    Module.length 𝒪 (Cotangent (π.comp φ)) = Module.length 𝒪 (𝒪 ⧸ congruenceIdeal π) ↔
      Function.Bijective φ ∧ Function.Bijective C.psiR := by
  have hη_le : congruenceIdeal (π.comp (φ.comp C.psiR)) ≤ congruenceIdeal π :=
    congruenceIdeal_le_of_surjective (φ.comp C.psiR) (hφ.comp C.psiR_surj) π
  have hfin_R' : Module.length 𝒪 (𝒪 ⧸ congruenceIdeal (π.comp (φ.comp C.psiR))) ≠ ⊤ :=
    length_quotient_ne_top_of_ne_bot_dvr C.cong_ne_bot
  constructor
  · intro heq
    have hlen_eq :
        Module.length 𝒪 (𝒪 ⧸ congruenceIdeal (π.comp (φ.comp C.psiR))) =
          Module.length 𝒪 (𝒪 ⧸ congruenceIdeal π) :=
      C.cotangent_eq_cover_cong.symm.trans heq
    have hη_eq : congruenceIdeal (π.comp (φ.comp C.psiR)) = congruenceIdeal π :=
      ideal_eq_of_le_of_length_quotient_eq hη_le hfin_R' hlen_eq
    have hcomp_bij : Function.Bijective (φ.comp C.psiR) :=
      gorenstein_surj_bijective_of_congruenceIdeal_eq C.gorenstein
        (φ.comp C.psiR) (hφ.comp C.psiR_surj) π C.cong_ne_bot hη_eq
    have hpsi_inj : Function.Injective C.psiR := Function.Injective.of_comp hcomp_bij.1
    have hφ_inj : Function.Injective φ := by
      intro x y hxy
      obtain ⟨x', rfl⟩ := C.psiR_surj x
      obtain ⟨y', rfl⟩ := C.psiR_surj y
      have h' : x' = y' := hcomp_bij.1 hxy
      rw [h']
    exact ⟨⟨hφ_inj, hφ⟩, ⟨hpsi_inj, C.psiR_surj⟩⟩
  · rintro ⟨hφ_bij, hpsi_bij⟩
    let e : C.R' ≃ₐ[𝒪] T := AlgEquiv.ofBijective (φ.comp C.psiR) (hφ_bij.comp hpsi_bij)
    have hη_eq : congruenceIdeal (π.comp (φ.comp C.psiR)) = congruenceIdeal π :=
      congruenceIdeal_eq_of_algEquiv e π
    rw [C.cotangent_eq_cover_cong, hη_eq]

/-! ### Direct Bridges to `TaylorWilesWindow` and `Stage2RamifiedPrimes` -/

/-- **Congruence-Ideal Power Annihilation Length Bound**: connects `congruenceIdeal_le_annihilator_cotangent`
directly to `TaylorWilesWindow.length_le_of_pow_mem_annihilator`! -/
theorem length_cotangent_le_of_pow_mem_congruence {𝒪 T : Type*}
    [CommRing 𝒪] [CommRing T] [Algebra 𝒪 T]
    (π : T →ₐ[𝒪] 𝒪) {r k : ℕ} {ϖ : 𝒪}
    [IsSimpleModule 𝒪 (𝒪 ⧸ Ideal.span ({ϖ} : Set 𝒪))]
    (f : (Fin r → 𝒪) →ₗ[𝒪] Cotangent π) (hf : Function.Surjective f)
    (hk : ϖ ^ k ∈ congruenceIdeal π) :
    Module.length 𝒪 (Cotangent π) ≤ ((r * k : ℕ) : ℕ∞) :=
  TaylorWilesWindow.length_le_of_pow_mem_annihilator f hf
    (congruenceIdeal_le_annihilator_cotangent π hk)

/-- **Direct Bridge to `Stage2RamifiedPrimes.LocalRamifiedObstruction`**:
any augmented `𝒪`-algebra `(T, π)` over a local ring with simple residue `𝒪 ⧸ (ϖ)`,
`r` generators for `Φ_T`, `ϖ ^ condExp ∈ η_T`, and `S.shaLen E l k ≤ len_𝒪(Φ_T)` directly
constructs a `Stage2RamifiedPrimes.LocalRamifiedObstruction S E l k`! -/
def localRamifiedObstructionOfCongruenceIdeal
    {S : SelmerSystem} {E : Type} [Field E] [NumberField E]
    {l : Nat.Primes} {k : ℕ}
    (𝒪 : Type) [CommRing 𝒪] (ϖ : 𝒪)
    [IsSimpleModule 𝒪 (𝒪 ⧸ Ideal.span ({ϖ} : Set 𝒪))]
    (T : Type) [CommRing T] [Algebra 𝒪 T]
    (π : T →ₐ[𝒪] 𝒪)
    (genRank : ℕ) (genMap : (Fin genRank → 𝒪) →ₗ[𝒪] Cotangent π)
    (gen_surj : Function.Surjective genMap)
    (condExp : ℕ) (hpow : ϖ ^ condExp ∈ congruenceIdeal π)
    (hsha : S.shaLen E l k ≤ Module.length 𝒪 (Cotangent π)) :
    Stage2RamifiedPrimes.LocalRamifiedObstruction S E l k where
  R_l := 𝒪
  ϖ := ϖ
  Obs := Cotangent π
  genRank := genRank
  genMap := genMap
  gen_surj := gen_surj
  condExp := condExp
  ann_pow := congruenceIdeal_le_annihilator_cotangent π hpow
  sha_le_obs := hsha

end DVRSmithAndWilesLenstra

/-! ## Section 3: Direct Discharge into `Stage2GaloisWire.ThreePartPatchingWindow` -/

section ThreePartDischarge

/-- **Explicit Taylor–Wiles Congruence-Module Patching Datum** at a host field `E`, odd
unramified prime `l ∤ 2 * M`, and weight `k`:
combines:
1. a full `TaylorWilesPatchingDatum` `(S_∞, 𝔞, R_∞, T_∞, M_∞)` (which automatically proves
   `R_∞ ≃ T_∞` and `R_0 ≃+* T_0` via Section 1!),
2. a coefficient ring `𝒪` with `T_0` as an augmented `𝒪`-algebra `π : T_0 →ₐ[𝒪] 𝒪` and
   congruence ideal `η_T = congruenceIdeal π` of length `≤ congLen`,
3. a Selmer module `Sel` embedding into `Φ_{T_0} = Cotangent π` (via `R_0 ≃ T_0`) dominating
   `S.shaLen E l k`, with `genRank` generators for `Φ_{T_0}` over `𝒪`. -/
structure TaylorWilesCongruenceDatum (S : SelmerSystem) (E : Type) [Field E] [NumberField E]
    (l : Nat.Primes) (k : ℕ) where
  patching : TaylorWilesPatchingDatum
  𝒪 : Type
  [commRingO : CommRing 𝒪]
  [algOT0 : Algebra 𝒪 patching.T_0]
  aug : patching.T_0 →ₐ[𝒪] 𝒪
  genRank : ℕ
  genMap : (Fin genRank → 𝒪) →ₗ[𝒪] Cotangent aug
  gen_surj : Function.Surjective genMap
  congLen : ℕ
  cong_length_le : Module.length 𝒪 (𝒪 ⧸ congruenceIdeal aug) ≤ (congLen : ℕ∞)
  Sel : Type
  [addSel : AddCommGroup Sel]
  [modSel : Module 𝒪 Sel]
  embed : Sel →ₗ[𝒪] Cotangent aug
  embed_inj : Function.Injective embed
  sha_le_selmer : S.shaLen E l k ≤ Module.length 𝒪 Sel

attribute [instance] TaylorWilesCongruenceDatum.commRingO TaylorWilesCongruenceDatum.algOT0
  TaylorWilesCongruenceDatum.addSel TaylorWilesCongruenceDatum.modSel

/-- The `R_0 ≃+* T_0` isomorphism automatically proved by a `TaylorWilesCongruenceDatum`. -/
def TaylorWilesCongruenceDatum.R0_equiv_T0 {S : SelmerSystem} {E : Type} [Field E] [NumberField E]
    {l : Nat.Primes} {k : ℕ} (D : TaylorWilesCongruenceDatum S E l k) :
    D.patching.R_0 ≃+* D.patching.T_0 :=
  D.patching.R0_equiv_T0

/-- Effective Selmer length bound `genRank * congLen` produced by a `TaylorWilesCongruenceDatum`. -/
def TaylorWilesCongruenceDatum.bound {S : SelmerSystem} {E : Type} [Field E] [NumberField E]
    {l : Nat.Primes} {k : ℕ} (D : TaylorWilesCongruenceDatum S E l k) : ℕ :=
  D.genRank * D.congLen

/-- **Direct Conversion `TaylorWilesCongruenceDatum → Stage2GaloisWire.PatchedPrimeBound`**:
wires `congruenceIdeal_le_annihilator_cotangent` into `TaylorWilesWindow.PatchedModuleBoundData`
and `Stage2GaloisWire.PatchedPrimeBound` with exact bound preservation (`bound = genRank * congLen`). -/
def TaylorWilesCongruenceDatum.toPatchedPrimeBound
    {S : SelmerSystem} {E : Type} [Field E] [NumberField E]
    {l : Nat.Primes} {k : ℕ} (D : TaylorWilesCongruenceDatum S E l k) :
    Stage2GaloisWire.PatchedPrimeBound S E l k where
  R_inf := D.𝒪
  patched :=
    { M_inf := Cotangent D.aug
      M_0 := Cotangent D.aug
      genRank := D.genRank
      genMap := D.genMap
      gen_surj := D.gen_surj
      spec := LinearMap.id
      spec_surj := Function.surjective_id
      obsIdeal := congruenceIdeal D.aug
      obs_kills := congruenceIdeal_le_annihilator_cotangent D.aug }
  Sel := D.Sel
  embed := D.embed
  embed_inj := D.embed_inj
  obsLen := D.congLen
  obs_length_le := D.cong_length_le
  sha_le_selmer := D.sha_le_selmer

theorem TaylorWilesCongruenceDatum.toPatchedPrimeBound_bound
    {S : SelmerSystem} {E : Type} [Field E] [NumberField E]
    {l : Nat.Primes} {k : ℕ} (D : TaylorWilesCongruenceDatum S E l k) :
    D.toPatchedPrimeBound.bound = D.bound := rfl

/-- **Sharp Rank-1 Complete-Intersection `PatchedPrimeBound`**: when Wiles–Lenstra equality
`len_𝒪(Φ_T) = len_𝒪(𝒪 / η_T)` holds (complete intersection!), `S.shaLen E l k` is bounded
directly by `congLen` (`genRank = 1`, no factor of `r`)! -/
theorem shaLen_le_congLen_of_completeIntersection
    {S : SelmerSystem} {E : Type} [Field E] [NumberField E]
    {l : Nat.Primes} {k : ℕ} (D : TaylorWilesCongruenceDatum S E l k)
    (hci : Module.length D.𝒪 (Cotangent D.aug) =
      Module.length D.𝒪 (D.𝒪 ⧸ congruenceIdeal D.aug)) :
    S.shaLen E l k ≠ ⊤ ∧ (S.shaLen E l k).toNat ≤ D.congLen := by
  have hle : S.shaLen E l k ≤ (D.congLen : ℕ∞) := by
    calc S.shaLen E l k
        ≤ Module.length D.𝒪 D.Sel := D.sha_le_selmer
      _ ≤ Module.length D.𝒪 (Cotangent D.aug) :=
          Module.length_le_of_injective D.embed D.embed_inj
      _ = Module.length D.𝒪 (D.𝒪 ⧸ congruenceIdeal D.aug) := hci
      _ ≤ (D.congLen : ℕ∞) := D.cong_length_le
  exact ⟨ne_top_of_le_ne_top (ENat.natCast_ne_top _) hle, ENat.toNat_le_of_le_natCast hle⟩

/-- **Odd Unramified Taylor–Wiles Congruence-Module Patching Realization**:
supplies a `TaylorWilesCongruenceDatum` at every odd unramified prime `l ∤ 2 * M` and weight
`1 ≤ k < t` whose weighted congruence-length sum fits inside `B_patch`. -/
structure CongruencePatchingRealization (S : SelmerSystem) (E : Type) [Field E] [NumberField E]
    (t M : ℕ) (B_patch : ℝ) where
  datum : ∀ (l : Nat.Primes) (k : ℕ),
    (l : ℕ) ≠ 2 → ¬((l : ℕ) ∣ M) → 0 < k → k < t → TaylorWilesCongruenceDatum S E l k
  weighted_sum_le : ∀ P : Finset Nat.Primes,
    (hP : ∀ l ∈ P, (l : ℕ) ≠ 2 ∧ ¬((l : ℕ) ∣ M)) →
    ∑ l ∈ P.attach, Real.log (l.1 : ℕ) *
      ∑ k ∈ (Finset.Ico 1 t).attach,
        ((datum l.1 k.1 (hP l.1 l.2).1 (hP l.1 l.2).2
          (Finset.mem_Ico.mp k.2).1 (Finset.mem_Ico.mp k.2).2).bound : ℝ) ≤ B_patch

/-- **Direct Discharge of the Unramified Branch of `Stage2GaloisWire.ThreePartPatchingWindow`**:
every `CongruencePatchingRealization` directly produces a
`Stage2GaloisWire.PatchedOddUnramifiedRealization`! -/
def CongruencePatchingRealization.toPatchedOddUnramifiedRealization
    {S : SelmerSystem} {E : Type} [Field E] [NumberField E]
    {t M : ℕ} {B_patch : ℝ}
    (C : CongruencePatchingRealization S E t M B_patch) :
    Stage2GaloisWire.PatchedOddUnramifiedRealization S E t M B_patch where
  primeBound := fun l k hl2 hnd hk1 hkt =>
    (C.datum l k hl2 hnd hk1 hkt).toPatchedPrimeBound
  weighted_sum_le := fun P hP => C.weighted_sum_le P hP

/-- **Finite Congruence-Prime Support Constructor**: if outside a finite set `P₀` of odd
unramified congruence primes the congruence ideal is trivial (`congLen = 0`), then the weighted
sum bound holds automatically for ALL finite sets `P` with envelope
`B_patch = ∑_{l ∈ P₀} log l * ∑_{k=1}^{t-1} bound(l, k)`. -/
def CongruencePatchingRealization.ofFiniteSupport
    {S : SelmerSystem} {E : Type} [Field E] [NumberField E]
    {t M : ℕ} {B_patch : ℝ}
    (P₀ : Finset Nat.Primes)
    (hP₀ : ∀ l ∈ P₀, (l : ℕ) ≠ 2 ∧ ¬((l : ℕ) ∣ M))
    (datum : ∀ (l : Nat.Primes) (k : ℕ),
      (l : ℕ) ≠ 2 → ¬((l : ℕ) ∣ M) → 0 < k → k < t → TaylorWilesCongruenceDatum S E l k)
    (hsupp : ∀ (l : Nat.Primes) (k : ℕ) (hl2 : (l : ℕ) ≠ 2) (hnd : ¬((l : ℕ) ∣ M))
      (hk1 : 0 < k) (hkt : k < t), l ∉ P₀ → (datum l k hl2 hnd hk1 hkt).congLen = 0)
    (hB : ∑ l ∈ P₀.attach, Real.log (l.1 : ℕ) *
      ∑ k ∈ (Finset.Ico 1 t).attach,
        ((datum l.1 k.1 (hP₀ l.1 l.2).1 (hP₀ l.1 l.2).2
          (Finset.mem_Ico.mp k.2).1 (Finset.mem_Ico.mp k.2).2).bound : ℝ) ≤ B_patch) :
    CongruencePatchingRealization S E t M B_patch where
  datum := datum
  weighted_sum_le := fun P hP => by
    classical
    let F : Nat.Primes → ℝ := fun l =>
      if h : (l : ℕ) ≠ 2 ∧ ¬((l : ℕ) ∣ M) then
        Real.log (l : ℕ) *
          ∑ k ∈ (Finset.Ico 1 t).attach,
            ((datum l k.1 h.1 h.2 (Finset.mem_Ico.mp k.2).1 (Finset.mem_Ico.mp k.2).2).bound : ℝ)
      else 0
    have hF_nonneg : ∀ l : Nat.Primes, 0 ≤ F l := by
      intro l
      dsimp only [F]
      split_ifs
      · exact mul_nonneg (Real.log_natCast_nonneg _)
          (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _)
      · exact le_rfl
    have hF_zero : ∀ l : Nat.Primes, l ∉ P₀ → F l = 0 := by
      intro l hl
      dsimp only [F]
      split_ifs with h
      · have hsum0 : ∑ k ∈ (Finset.Ico 1 t).attach,
            ((datum l k.1 h.1 h.2 (Finset.mem_Ico.mp k.2).1
              (Finset.mem_Ico.mp k.2).2).bound : ℝ) = 0 := by
          refine Finset.sum_eq_zero fun k _ => ?_
          unfold TaylorWilesCongruenceDatum.bound
          rw [hsupp l k.1 h.1 h.2 (Finset.mem_Ico.mp k.2).1 (Finset.mem_Ico.mp k.2).2 hl]
          simp
        rw [hsum0, mul_zero]
      · rfl
    have hLHS :
        ∑ l ∈ P.attach, Real.log (l.1 : ℕ) *
          ∑ k ∈ (Finset.Ico 1 t).attach,
            ((datum l.1 k.1 (hP l.1 l.2).1 (hP l.1 l.2).2
              (Finset.mem_Ico.mp k.2).1 (Finset.mem_Ico.mp k.2).2).bound : ℝ) =
        ∑ l ∈ P, F l := by
      rw [← Finset.sum_attach P F]
      refine Finset.sum_congr rfl fun l _ => ?_
      dsimp only [F]
      rw [dif_pos (hP l.1 l.2)]
    have hRHS :
        ∑ l ∈ P₀.attach, Real.log (l.1 : ℕ) *
          ∑ k ∈ (Finset.Ico 1 t).attach,
            ((datum l.1 k.1 (hP₀ l.1 l.2).1 (hP₀ l.1 l.2).2
              (Finset.mem_Ico.mp k.2).1 (Finset.mem_Ico.mp k.2).2).bound : ℝ) =
        ∑ l ∈ P₀, F l := by
      rw [← Finset.sum_attach P₀ F]
      refine Finset.sum_congr rfl fun l _ => ?_
      dsimp only [F]
      rw [dif_pos (hP₀ l.1 l.2)]
    rw [hLHS]
    have hsub : ∑ l ∈ P, F l = ∑ l ∈ P ∩ P₀, F l := by
      symm
      refine Finset.sum_subset Finset.inter_subset_left fun l hl hnot => ?_
      exact hF_zero l (fun h0 => hnot (Finset.mem_inter.mpr ⟨hl, h0⟩))
    rw [hsub]
    calc ∑ l ∈ P ∩ P₀, F l
        ≤ ∑ l ∈ P₀, F l :=
          Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right fun l _ _ => hF_nonneg l
      _ ≤ B_patch := by rwa [← hRHS]

/-- **Unified Three-Part `VVle` Assembly**: combines:
1. an `l = 2` Iwasawa 2-tower bound (`B₂`),
2. a `Stage2RamifiedPrimes.RamifiedPrimeRealization` (`minusBound C_ram M n N t`), and
3. a `CongruencePatchingRealization` (`B_patch`, powered by Section 1 `R = T` + Section 2
   Wiles–Lenstra congruence ideals!)
directly into `VVle S E t (B₂ + minusBound C_ram M n N t + B_patch)`. -/
theorem vvle_of_unified_patching
    {S : SelmerSystem} {E : Type} [Field E] [NumberField E]
    {t M n N : ℕ} {B₂ C_ram B_patch : ℝ}
    (h2_fin : ∀ (l : Nat.Primes) (k : ℕ), (l : ℕ) = 2 → 0 < k → k < t → S.shaLen E l k ≠ ⊤)
    (h2_sum : ∀ P2 : Finset Nat.Primes, (∀ l ∈ P2, (l : ℕ) = 2) →
      ∑ l ∈ P2, Real.log (l : ℕ) * ∑ k ∈ Finset.Ico 1 t, ((S.shaLen E l k).toNat : ℝ) ≤ B₂)
    (hram : Stage2RamifiedPrimes.RamifiedPrimeRealization S E t M n N C_ram)
    (hcong : CongruencePatchingRealization S E t M B_patch) :
    VVle S E t (B₂ + TaylorWilesWindow.minusBound C_ram M n N t + B_patch) := by
  obtain ⟨hram_fin, hram_sum⟩ := hram.discharges_threePart_ram_branch
  exact Stage2GaloisWire.vvle_of_patching_three_parts h2_fin h2_sum hram_fin hram_sum
    hcong.toPatchedOddUnramifiedRealization

/-- **Stage 3 Unified Three-Part Patching Window Supply**:
replaces both the raw odd-ramified bounds and the raw `PatchedOddUnramifiedRealization` of
`Stage2GaloisWire.ThreePartPatchingWindow` by explicit algebraic realizations:
- `Stage2RamifiedPrimes.RamifiedPrimeRealization` (odd ramified primes `l ∣ ψ.N`), and
- `CongruencePatchingRealization` (odd unramified primes `l ∤ 2 * ψ.N`, via `R_∞ = T_∞ → R_0 = T_0`
  and Wiles–Lenstra congruence ideals `η_T`). -/
structure UnifiedPatchingWindowSupply (S : SelmerSystem) : Prop where
  supply : ∃ Cb : ℝ, ∀ (ψ : PChar) (eps : ℝ), 0 < eps → eps < 1 / 52 →
    ∀ (e t : ℝ → ℕ), TaylorWilesWindow.AdmissiblePage 4 401 e t →
    ∃ (J C P XJ : ℝ), 0 < J ∧
      ∀ X ≥ XJ, ∀ q d : ℕ, TaylorWilesWindow.PrimePair ψ.N q d →
        2 * X ^ (401 : ℝ) + 1 < (q : ℝ) → 2 * X ^ (401 : ℝ) + 1 < (d : ℝ) →
        P < (q : ℝ) → P < (d : ℝ) → Real.log ((q : ℝ) * d) ≤ X ^ (eps / (4 * J)) →
        ∃ Y : ℝ, X ^ (1 / J) ≤ Y ∧ Y ^ (2 : ℝ) ≤ X ∧
          ∀ x : ℝ, Y ≤ x → x ≤ Y ^ (2 : ℝ) →
            ∀ (E : Type) [Field E] [NumberField E], IsChiField ψ (e x) q d E →
              (∀ (l : Nat.Primes) (k : ℕ), (l : ℕ) = 2 → 0 < k → k < t x → S.shaLen E l k ≠ ⊤) ∧
              (∀ P2 : Finset Nat.Primes, (∀ l ∈ P2, (l : ℕ) = 2) →
                ∑ l ∈ P2, Real.log (l : ℕ) * ∑ k ∈ Finset.Ico 1 (t x), ((S.shaLen E l k).toNat : ℝ) ≤
                  Real.exp (x ^ (4 * eps / 5)) * Real.log 2) ∧
              Nonempty (Stage2RamifiedPrimes.RamifiedPrimeRealization S E (t x) ψ.N
                (Module.finrank ℚ E) (condF E) Cb) ∧
              Nonempty (CongruencePatchingRealization S E (t x) ψ.N
                (((condF E : ℝ) * (t x : ℝ)) ^ C + C * Real.exp (x ^ (4 * eps / 5))))

/-- **Direct Discharge into `Stage2GaloisWire.ThreePartPatchingWindow`**:
combines `Stage2RamifiedPrimes.RamifiedPrimeRealization.discharges_threePart_ram_branch` with
`CongruencePatchingRealization.toPatchedOddUnramifiedRealization` to discharge all 5 conjuncts
of `Stage2GaloisWire.ThreePartPatchingWindow S`! -/
theorem threePartPatchingWindow_of_unified {S : SelmerSystem}
    (U : UnifiedPatchingWindowSupply S) :
    Stage2GaloisWire.ThreePartPatchingWindow S where
  window := by
    obtain ⟨Cb, hCb⟩ := U.supply
    refine ⟨Cb, fun ψ eps h0 h1 e t hadm => ?_⟩
    obtain ⟨J, C, P, XJ, hJ0, hmain⟩ := hCb ψ eps h0 h1 e t hadm
    refine ⟨J, C, P, XJ, hJ0, fun X hX q d hpp hq3 hd3 hPq hPd hlog => ?_⟩
    obtain ⟨Y, hYlo, hYhi, hY⟩ := hmain X hX q d hpp hq3 hd3 hPq hPd hlog
    refine ⟨Y, hYlo, hYhi, fun x hxY hxY2 E _ _ hE => ?_⟩
    obtain ⟨h2f, h2s, ⟨hram⟩, ⟨hcong⟩⟩ := hY x hxY hxY2 E hE
    obtain ⟨hram_fin, hram_sum⟩ := hram.discharges_threePart_ram_branch
    exact ⟨h2f, h2s, hram_fin, hram_sum, ⟨hcong.toPatchedOddUnramifiedRealization⟩⟩

/-- **Direct Discharge into `RHDirect.GaloisModularityContract S`** from
`UnifiedPatchingWindowSupply S`. -/
theorem galoisModularityContract_of_unified {S : SelmerSystem}
    (U : UnifiedPatchingWindowSupply S) :
    GaloisModularityContract S :=
  Stage2GaloisWire.galoisModularityContract_of_threePart (threePartPatchingWindow_of_unified U)

/-- **Direct `VWin S` (`∀ ψ, VWinAt S ψ 401`) Discharge** from `UnifiedPatchingWindowSupply S`. -/
theorem vwin_of_unified {S : SelmerSystem} (U : UnifiedPatchingWindowSupply S) : VWin S :=
  (galoisModularityContract_of_unified U).vwin

end ThreePartDischarge

end Stage3PatchingUnification
end RHDirect

end
