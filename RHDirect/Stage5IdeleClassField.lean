import RHDirect.Stage4ClassFieldTheory
import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.FractionalIdeal.Inverse
import Mathlib.RingTheory.FractionalIdeal.Operations
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.NumberField.Ideal.Basic
import Mathlib.Data.ZMod.QuotientRing

/-!
# RHDirect.Stage5IdeleClassField

Self-contained, zero-`sorry`, zero-custom-`axiom` Lean 4 formalization of **Concrete Idele-Class
Field Theory, Finite Ray Class Groups, Strong Approximation for `𝕀_ℚ`, and the Exact Idelic
Hecke Character ↔ Classical Dirichlet Character ↔ Cyclotomic Galois Character Equivalence**
directly on Mathlib's `NumberField`, `NumberField.RingOfIntegers`, `ClassGroup`,
`IsDedekindDomain.FiniteAdeleRing`, `IsDedekindDomain.HeightOneSpectrum`, `FractionalIdeal`,
and `DirichletCharacter` (`v4.33.1`).

## Contents
1. **Concrete Finite-Idele Group & Exact Ideal-Class Isomorphism**:
   - `FinIdele K := (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)ˣ` with integral-unit subgroup
     `finUnitSubgroup K ≃* ∏_v (v.adicCompletionIntegers K)ˣ` and principal subgroup
     `principalSubgroup K := (diagFinIdele K).range`.
   - Exact surjective content homomorphism
     `ideleToFractionalIdeal K : FinIdele K →* (FractionalIdeal (nonZeroDivisors (𝓞 K)) K)ˣ`
     sending `x ↦ ∏'_v v^{ord_v(x_v)}`, with exact kernel `finUnitSubgroup K` and exact
     compatibility `(ideleToFractionalIdeal K).comp (diagFinIdele K) = toPrincipalIdeal (𝓞 K) K`.
   - Canonical group isomorphism
     `ideleClassEquivClassGroup K : FinIdele K ⧸ (principalSubgroup K ⊔ finUnitSubgroup K) ≃* ClassGroup (𝓞 K)`,
     unconditional finiteness `finite_ideleClassQuotient K`, and exact order
     `Nat.card = NumberField.classNumber K`.
2. **Concrete Ray Class Groups `RayClassGroup K 𝔪` & Exact Ray-Class Sequence**:
   - Local approximation in `v.adicCompletionIntegers K`, local reduction
     `localQuotUnitsMap : (v.adicCompletionIntegers K)ˣ →* (𝓞 K ⧸ v.asIdeal ^ n)ˣ`, and Chinese
     Remainder Theorem reduction `finUnitToQuotUnits : finUnitSubgroup K →* (𝓞 K ⧸ 𝔪)ˣ` with
     exact kernel `rayUnitSubgroup K 𝔪`.
   - Exact ray-class short exact sequence
     `(𝓞 K)ˣ → (𝓞 K ⧸ 𝔪)ˣ → RayClassGroup K 𝔪 → ClassGroup (𝓞 K) → 1`.
   - Unconditional finiteness `finite_rayClassGroup K 𝔪 h𝔪` and exact cardinality identity
     `Nat.card (RayClassGroup K 𝔪) * Nat.card (globalUnitsToQuotUnits 𝔪).range =
        Nat.card (𝓞 K ⧸ 𝔪)ˣ * Nat.card (ClassGroup (𝓞 K))`.
3. **Strong Approximation for `𝕀_ℚ` & Exact Idelic Hecke ↔ Dirichlet ↔ Galois Character Triangle**:
   - Full rational idele group `RatIdele := ℝˣ × FinIdele ℚ`, trivial class group `ClassGroup (𝓞 ℚ)`,
     and unconditional Strong Approximation:
     `ratPrincipalSubgroup ⊔ ratUnitSubgroup = ⊤` and `ratPrincipalSubgroup ⊓ ratUnitSubgroup = ⊥`
     (giving the exact direct-product decomposition `RatIdele ≃* ℚˣ × (ℝ_{>0} × U_{ℚ,f})`).
   - Exact congruence quotient isomorphism
     `ratIdeleClassEquivZModUnits m : RatIdele ⧸ (ratPrincipalSubgroup ⊔ ratCongruenceSubgroup m) ≃* (ZMod m)ˣ`
     sending prime uniformizer ideles `ϖ_p` (`p ∤ m`) to `p mod m` and `(-1_∞, 1)` to `-1 mod m`.
   - Exact group isomorphisms
     `idelicHeckeCharEquivDirichlet m : IdelicHeckeChar m ≃* DirichletCharacter ℂ m` and
     `idelicHeckeCharEquivGalChar m : IdelicHeckeChar m ≃* Stage4ClassFieldTheory.GalChar m`
     making the full CFT triangle commute identically and matching local Euler factors and
     global `L`-functions at every unramified prime `p ∤ m`.

Zero `sorry`, zero custom `axiom`s.
-/

noncomputable section

open Complex DirichletCharacter IsDedekindDomain NumberField RHDirect
open scoped NumberField

namespace RHDirect.Stage5IdeleClassField

/-! ## Section 1: Concrete Finite-Idele Group & Exact Isomorphism with `ClassGroup (𝓞 K)` -/

section FiniteIdeles

variable (K : Type*) [Field K] [NumberField K]

/-- The concrete finite-idele group `𝕀_{K,f}` of a number field `K`, realized as the unit group
of Mathlib's `IsDedekindDomain.FiniteAdeleRing (𝓞 K) K`. -/
abbrev FinIdele : Type _ :=
  (FiniteAdeleRing (𝓞 K) K)ˣ

/-- The canonical diagonal embedding `Kˣ →* 𝕀_{K,f}` sending `k` to its principal finite idele. -/
def diagFinIdele : Kˣ →* FinIdele K :=
  Units.map (FiniteAdeleRing.algebraMap (𝓞 K) K).toMonoidHom

/-- The subgroup of principal finite ideles `P_K = im(Kˣ → 𝕀_{K,f})`. -/
def principalSubgroup : Subgroup (FinIdele K) :=
  (diagFinIdele K).range

variable {K}

private theorem finAdele_ext {a b : FiniteAdeleRing (𝓞 K) K}
    (h : ∀ v : HeightOneSpectrum (𝓞 K), a v = b v) : a = b :=
  DFunLike.ext _ _ h

private theorem finAdele_one_apply (v : HeightOneSpectrum (𝓞 K)) :
    (1 : FiniteAdeleRing (𝓞 K) K) v = 1 := rfl

private theorem finAdele_mul_apply (a b : FiniteAdeleRing (𝓞 K) K) (v : HeightOneSpectrum (𝓞 K)) :
    (a * b) v = a v * b v := rfl

private theorem valued_algebraMap_int (v : HeightOneSpectrum (𝓞 K)) (r : 𝓞 K) :
    Valued.v (algebraMap (𝓞 K) (v.adicCompletion K) r) = v.intValuation r := by
  have h1 := HeightOneSpectrum.valuedAdicCompletion_eq_valuation (R := 𝓞 K) (K := K) v r
  rw [HeightOneSpectrum.valuation_of_algebraMap] at h1
  exact h1

private theorem valued_algebraMap_K (v : HeightOneSpectrum (𝓞 K)) (k : K) :
    Valued.v (algebraMap K (v.adicCompletion K) k) = v.valuation K k := by
  have h1 := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (R := 𝓞 K) (K := K) v k
  have h2 : algebraMap K (v.adicCompletion K) k =
      HeightOneSpectrum.adicCompletion.ofCompletion ((WithVal.equiv (v.valuation K)).symm k) := by
    have h := congrFun (HeightOneSpectrum.algebraMap_adicCompletion (𝓞 K) K (S := K) v) k
    simpa using h
  rw [h2]
  exact h1

private theorem finAdele_algebraMap_int_apply (r : 𝓞 K) (v : HeightOneSpectrum (𝓞 K)) :
    (FiniteAdeleRing.algebraMap (𝓞 K) K (algebraMap (𝓞 K) K r)) v =
      algebraMap (𝓞 K) (v.adicCompletion K) r := by
  have h1 : (FiniteAdeleRing.algebraMap (𝓞 K) K (algebraMap (𝓞 K) K r)) v =
      HeightOneSpectrum.adicCompletion.ofCompletion
        ((WithVal.equiv (v.valuation K)).symm (algebraMap (𝓞 K) K r)) := rfl
  have h2 : algebraMap K (v.adicCompletion K) (algebraMap (𝓞 K) K r) =
      HeightOneSpectrum.adicCompletion.ofCompletion
        ((WithVal.equiv (v.valuation K)).symm (algebraMap (𝓞 K) K r)) := by
    have h := congrFun (HeightOneSpectrum.algebraMap_adicCompletion (𝓞 K) K (S := K) v)
      (algebraMap (𝓞 K) K r)
    simpa using h
  rw [h1, ← h2, ← IsScalarTower.algebraMap_apply (𝓞 K) K (v.adicCompletion K)]

private theorem valued_finAdele_algebraMap (k : K) (v : HeightOneSpectrum (𝓞 K)) :
    Valued.v ((FiniteAdeleRing.algebraMap (𝓞 K) K k) v) = v.valuation K k := by
  rw [show (FiniteAdeleRing.algebraMap (𝓞 K) K k) v =
      HeightOneSpectrum.adicCompletion.ofCompletion
        ((WithVal.equiv (v.valuation K)).symm k) from rfl]
  exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v k

theorem finIdele_apply_mul_inv (x : FinIdele K) (v : HeightOneSpectrum (𝓞 K)) :
    x.val v * x.inv v = 1 := by
  rw [← finAdele_mul_apply, x.val_inv, finAdele_one_apply]

theorem finIdele_apply_inv_mul (x : FinIdele K) (v : HeightOneSpectrum (𝓞 K)) :
    x.inv v * x.val v = 1 := by
  rw [← finAdele_mul_apply, x.inv_val, finAdele_one_apply]

theorem finIdele_apply_ne_zero (x : FinIdele K) (v : HeightOneSpectrum (𝓞 K)) :
    x.val v ≠ 0 := by
  intro h0
  have h := finIdele_apply_mul_inv x v
  rw [h0, zero_mul] at h
  exact zero_ne_one h

theorem finIdele_val_ne_zero (x : FinIdele K) (v : HeightOneSpectrum (𝓞 K)) :
    Valued.v (x.val v) ≠ 0 := by
  intro h0
  exact finIdele_apply_ne_zero x v ((Valuation.zero_iff _).mp h0)

theorem finIdele_val_mul_inv (x : FinIdele K) (v : HeightOneSpectrum (𝓞 K)) :
    Valued.v (x.val v) * Valued.v (x.inv v) = 1 := by
  rw [← map_mul, finIdele_apply_mul_inv, map_one]

/-- The integral finite-idele unit subgroup `U_{K,f} = {x ∈ 𝕀_{K,f} | ∀ v, |x_v|_v = 1}`. -/
def finUnitSubgroup (K : Type*) [Field K] [NumberField K] : Subgroup (FinIdele K) where
  carrier := {x : FinIdele K | ∀ v : HeightOneSpectrum (𝓞 K), Valued.v (x.val v) = 1}
  one_mem' v := by
    change Valued.v ((1 : FiniteAdeleRing (𝓞 K) K) v) = 1
    rw [finAdele_one_apply, map_one]
  mul_mem' {x y} hx hy v := by
    change Valued.v ((x.val * y.val) v) = 1
    rw [finAdele_mul_apply, map_mul, hx v, hy v, mul_one]
  inv_mem' {x} hx v := by
    have hmul := finIdele_val_mul_inv x v
    rw [hx v, one_mul] at hmul
    exact hmul

theorem mem_finUnitSubgroup_iff {x : FinIdele K} :
    x ∈ finUnitSubgroup K ↔ ∀ v : HeightOneSpectrum (𝓞 K), Valued.v (x.val v) = 1 :=
  Iff.rfl

/-- Extract the local unit `x_v ∈ (v.adicCompletionIntegers K)ˣ` from a global finite-idele unit
`u ∈ U_{K,f}`. -/
def finUnitAt (u : finUnitSubgroup K) (v : HeightOneSpectrum (𝓞 K)) :
    (v.adicCompletionIntegers K)ˣ where
  val := ⟨u.1.val v, (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 K) K v).mpr (le_of_eq (u.2 v))⟩
  inv := ⟨u.1.inv v, (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 K) K v).mpr (by
    have h := finIdele_val_mul_inv u.1 v
    rw [u.2 v, one_mul] at h
    exact le_of_eq h)⟩
  val_inv := Subtype.ext (finIdele_apply_mul_inv u.1 v)
  inv_val := Subtype.ext (finIdele_apply_inv_mul u.1 v)

/-- **Concrete Identification `U_{K,f} ≃* ∏_v 𝒪_vˣ`**: the finite-idele unit subgroup is
canonically isomorphic to the full direct product of local unit groups. -/
def finUnitSubgroupEquivProdUnits (K : Type*) [Field K] [NumberField K] :
    finUnitSubgroup K ≃* ((v : HeightOneSpectrum (𝓞 K)) → (v.adicCompletionIntegers K)ˣ) where
  toFun u v := finUnitAt u v
  invFun f :=
    ⟨{ val := RestrictedProduct.mk (fun v => (f v).val.val)
          (Filter.Eventually.of_forall fun v => (f v).val.2)
       inv := RestrictedProduct.mk (fun v => (f v).inv.val)
          (Filter.Eventually.of_forall fun v => (f v).inv.2)
       val_inv := finAdele_ext fun v => congrArg Subtype.val (f v).val_inv
       inv_val := finAdele_ext fun v => congrArg Subtype.val (f v).inv_val },
      fun v => by
        have hle1 : Valued.v (f v).val.val ≤ 1 :=
          (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 K) K v).mp (f v).val.2
        have hle2 : Valued.v (f v).inv.val ≤ 1 :=
          (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 K) K v).mp (f v).inv.2
        have hmul : Valued.v (f v).val.val * Valued.v (f v).inv.val = 1 := by
          rw [← map_mul, show (f v).val.val * (f v).inv.val = 1 from
            congrArg Subtype.val (f v).val_inv, map_one]
        apply le_antisymm hle1
        have h1 : Valued.v (f v).val.val * Valued.v (f v).inv.val ≤ Valued.v (f v).val.val * 1 :=
          mul_le_mul' le_rfl hle2
        rw [hmul, mul_one] at h1
        exact h1⟩
  left_inv u := by
    apply Subtype.ext
    apply Units.ext
    exact finAdele_ext fun _ => rfl
  right_inv f := by
    ext v
    rfl
  map_mul' u₁ u₂ := by
    ext v
    rfl

/-- The local additive valuation exponent `ord_v(x_v) ∈ ℤ` of a finite idele `x` at `v`,
normalized so that `ord_v(π_v) = +1` for a uniformizer `π_v` of `v`. -/
def ideleOrd (x : FinIdele K) (v : HeightOneSpectrum (𝓞 K)) : ℤ :=
  -(WithZero.log (Valued.v (x.val v)))

theorem ideleOrd_one (v : HeightOneSpectrum (𝓞 K)) : ideleOrd (1 : FinIdele K) v = 0 := by
  unfold ideleOrd
  change -(WithZero.log (Valued.v ((1 : FiniteAdeleRing (𝓞 K) K) v))) = 0
  rw [finAdele_one_apply, map_one, WithZero.log_one, neg_zero]

theorem ideleOrd_mul (x y : FinIdele K) (v : HeightOneSpectrum (𝓞 K)) :
    ideleOrd (x * y) v = ideleOrd x v + ideleOrd y v := by
  unfold ideleOrd
  change -(WithZero.log (Valued.v ((x.val * y.val) v))) = _
  rw [finAdele_mul_apply, map_mul,
    WithZero.log_mul (finIdele_val_ne_zero x v) (finIdele_val_ne_zero y v), neg_add]

theorem ideleOrd_inv (x : FinIdele K) (v : HeightOneSpectrum (𝓞 K)) :
    ideleOrd x⁻¹ v = -ideleOrd x v := by
  have h := ideleOrd_mul x x⁻¹ v
  rw [mul_inv_cancel, ideleOrd_one] at h
  omega

theorem ideleOrd_eq_zero_iff (x : FinIdele K) (v : HeightOneSpectrum (𝓞 K)) :
    ideleOrd x v = 0 ↔ Valued.v (x.val v) = 1 := by
  unfold ideleOrd
  constructor
  · intro h
    have hlog : WithZero.log (Valued.v (x.val v)) = 0 := by omega
    rw [← WithZero.exp_log (finIdele_val_ne_zero x v), hlog, WithZero.exp_zero]
  · intro h
    rw [h, WithZero.log_one, neg_zero]

theorem ideleOrd_finite_support (x : FinIdele K) :
    Set.Finite {v : HeightOneSpectrum (𝓞 K) | ideleOrd x v ≠ 0} := by
  have h1 : ∀ᶠ v in Filter.cofinite, Valued.v (x.val v) ≤ 1 := by
    filter_upwards [x.val.2] with v hv
    exact (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 K) K v).mp hv
  have h2 : ∀ᶠ v in Filter.cofinite, Valued.v (x.inv v) ≤ 1 := by
    filter_upwards [x.inv.2] with v hv
    exact (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 K) K v).mp hv
  have h3 : ∀ᶠ v in Filter.cofinite, ideleOrd x v = 0 := by
    filter_upwards [h1, h2] with v hv1 hv2
    rw [ideleOrd_eq_zero_iff]
    apply le_antisymm hv1
    have hmul := finIdele_val_mul_inv x v
    have hle : Valued.v (x.val v) * Valued.v (x.inv v) ≤ Valued.v (x.val v) * 1 :=
      mul_le_mul' le_rfl hv2
    rw [hmul, mul_one] at hle
    exact hle
  simpa only [Filter.Eventually, Filter.mem_cofinite, Set.compl_ofPred] using h3

/-- The unit of `(FractionalIdeal (nonZeroDivisors (𝓞 K)) K)ˣ` attached to a nonzero integral
ideal `I ≠ ⊥`. -/
def coeIdealUnit (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) :
    (FractionalIdeal (nonZeroDivisors (𝓞 K)) K)ˣ :=
  Units.mk0 (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)
    ((FractionalIdeal.coeIdeal_ne_zero (R := 𝓞 K) (K := K)).mpr hI)

theorem coeIdealUnit_val (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) :
    (coeIdealUnit I hI : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) =
      (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) := rfl

theorem coeIdealUnit_mul {I J : Ideal (𝓞 K)} (hI : I ≠ ⊥) (hJ : J ≠ ⊥) :
    coeIdealUnit (I * J) (mul_ne_zero hI hJ) = coeIdealUnit I hI * coeIdealUnit J hJ := by
  apply Units.ext
  exact FractionalIdeal.coeIdeal_mul I J

theorem coeIdealUnit_pow {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) (n : ℕ) :
    coeIdealUnit (I ^ n) (pow_ne_zero n hI) = (coeIdealUnit I hI) ^ n := by
  apply Units.ext
  exact FractionalIdeal.coeIdeal_pow (nonZeroDivisors (𝓞 K)) K I n

/-- The fractional-ideal unit attached to a height-one prime `v : HeightOneSpectrum (𝓞 K)`. -/
def primeFracUnit (K : Type*) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) :
    (FractionalIdeal (nonZeroDivisors (𝓞 K)) K)ˣ :=
  coeIdealUnit v.asIdeal v.ne_bot

/-- Helper: coercion of a finite product of prime-ideal powers matches `∏ v ∈ S, v.asIdeal ^ e v`. -/
private theorem coe_finset_prod_primeFracUnit (S : Finset (HeightOneSpectrum (𝓞 K)))
    (e : HeightOneSpectrum (𝓞 K) → ℕ) :
    ((∏ v ∈ S, primeFracUnit K v ^ e v : (FractionalIdeal (nonZeroDivisors (𝓞 K)) K)ˣ) :
        FractionalIdeal (nonZeroDivisors (𝓞 K)) K) =
      ((∏ v ∈ S, v.asIdeal ^ e v : Ideal (𝓞 K)) :
        FractionalIdeal (nonZeroDivisors (𝓞 K)) K) := by
  have h1 := map_prod (Units.coeHom (FractionalIdeal (nonZeroDivisors (𝓞 K)) K))
    (fun v => primeFracUnit K v ^ e v) S
  have h2 := map_prod (FractionalIdeal.coeIdealHom (nonZeroDivisors (𝓞 K)) K)
    (fun v => v.asIdeal ^ e v) S
  change Units.coeHom _ (∏ v ∈ S, primeFracUnit K v ^ e v) =
    FractionalIdeal.coeIdealHom (nonZeroDivisors (𝓞 K)) K (∏ v ∈ S, v.asIdeal ^ e v)
  rw [h1, h2]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [map_pow, map_pow]
  rfl

/-- **Finite-Idele Content Homomorphism**:
`ideleToFractionalIdeal K : 𝕀_{K,f} →* (FractionalIdeal (𝓞 K)⁰ K)ˣ` sending an idele `(x_v)` to
the finite product `∏'_v v^{ord_v(x_v)}`. -/
def ideleToFractionalIdeal (K : Type*) [Field K] [NumberField K] :
    FinIdele K →* (FractionalIdeal (nonZeroDivisors (𝓞 K)) K)ˣ where
  toFun x := ∏ᶠ (v : HeightOneSpectrum (𝓞 K)), primeFracUnit K v ^ ideleOrd x v
  map_one' := by
    have hfun : (fun v : HeightOneSpectrum (𝓞 K) => primeFracUnit K v ^ ideleOrd (1 : FinIdele K) v) =
        fun _ => 1 := by
      funext v
      rw [ideleOrd_one, zpow_zero]
    rw [hfun, finprod_one]
  map_mul' x y := by
    have hx : Function.HasFiniteMulSupport (fun v : HeightOneSpectrum (𝓞 K) =>
        primeFracUnit K v ^ ideleOrd x v) := by
      refine (ideleOrd_finite_support x).subset fun v hv => ?_
      intro h0
      exact hv (by simp [h0])
    have hy : Function.HasFiniteMulSupport (fun v : HeightOneSpectrum (𝓞 K) =>
        primeFracUnit K v ^ ideleOrd y v) := by
      refine (ideleOrd_finite_support y).subset fun v hv => ?_
      intro h0
      exact hv (by simp [h0])
    rw [← finprod_mul_distrib hx hy]
    congr 1
    funext v
    rw [ideleOrd_mul, zpow_add]

/-- Multiplicity `ord_v(I) ∈ ℕ` of a height-one prime `v` in an integral ideal `I : Ideal (𝓞 K)`. -/
def idealOrd {K : Type*} [Field K] [NumberField K] (I : Ideal (𝓞 K))
    (v : HeightOneSpectrum (𝓞 K)) : ℕ :=
  (Associates.mk v.asIdeal).count (Associates.mk I).factors

theorem idealOrd_finite_support {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) :
    Set.Finite {v : HeightOneSpectrum (𝓞 K) | idealOrd I v ≠ 0} := by
  classical
  have hfin : Set.Finite (HeightOneSpectrum.asIdeal ⁻¹'
      (↑(UniqueFactorizationMonoid.normalizedFactors I).toFinset : Set (Ideal (𝓞 K)))) :=
    ((UniqueFactorizationMonoid.normalizedFactors I).toFinset.finite_toSet).preimage
      (fun _ _ _ _ h => HeightOneSpectrum.ext h)
  refine hfin.subset fun v hv => ?_
  show v.asIdeal ∈ (UniqueFactorizationMonoid.normalizedFactors I).toFinset
  have hcnt := Ideal.count_associates_factors_eq (R := 𝓞 K) hI v.isPrime v.ne_bot
  have hv' : (Associates.mk v.asIdeal).count (Associates.mk I).factors ≠ 0 := hv
  rw [hcnt] at hv'
  exact Multiset.mem_toFinset.mpr (Multiset.count_pos.mp (Nat.pos_of_ne_zero hv'))

theorem idealOrd_one (w : HeightOneSpectrum (𝓞 K)) :
    idealOrd (1 : Ideal (𝓞 K)) w = 0 := by
  by_contra hnz
  have hdvd : w.asIdeal ∣ (1 : Ideal (𝓞 K)) :=
    (Associates.count_ne_zero_iff_dvd one_ne_zero
      (Ideal.prime_of_isPrime w.ne_bot w.isPrime).irreducible).mp hnz
  have hle : (⊤ : Ideal (𝓞 K)) ≤ w.asIdeal := by
    rw [← Ideal.one_eq_top]
    exact Ideal.dvd_iff_le.mp hdvd
  exact w.isPrime.ne_top (top_le_iff.mp hle)

open Classical in
theorem idealOrd_prod_prime_pow (S : Finset (HeightOneSpectrum (𝓞 K)))
    (e : HeightOneSpectrum (𝓞 K) → ℕ) (w : HeightOneSpectrum (𝓞 K)) :
    idealOrd (∏ v ∈ S, v.asIdeal ^ e v) w = if w ∈ S then e w else 0 := by
  induction S using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, if_neg (Finset.notMem_empty w)]
    exact idealOrd_one w
  | @insert a s ha ih =>
    have hne_s : (∏ v ∈ s, v.asIdeal ^ e v) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun v _ => pow_ne_zero _ v.ne_bot
    have hne_a : a.asIdeal ^ e a ≠ 0 := pow_ne_zero _ a.ne_bot
    have hirr_w : Irreducible (Associates.mk w.asIdeal) :=
      Associates.irreducible_mk.mpr (Ideal.prime_of_isPrime w.ne_bot w.isPrime).irreducible
    have hne_as : Associates.mk (∏ v ∈ s, v.asIdeal ^ e v) ≠ 0 :=
      Associates.mk_ne_zero.mpr hne_s
    have hne_aa : Associates.mk (a.asIdeal ^ e a) ≠ 0 :=
      Associates.mk_ne_zero.mpr hne_a
    have hpow_cnt :
        idealOrd (a.asIdeal ^ e a) w = if w = a then e a else 0 := by
      induction e a with
      | zero =>
        rw [pow_zero, idealOrd_one w]
        split_ifs <;> rfl
      | succ n ihn =>
        unfold idealOrd at ihn ⊢
        have h1 : Associates.mk (a.asIdeal ^ (n + 1)) =
            Associates.mk a.asIdeal * Associates.mk (a.asIdeal ^ n) := by
          rw [pow_succ', Associates.mk_mul_mk]
        rw [h1, Associates.count_mul (Associates.mk_ne_zero.mpr a.ne_bot)
          (Associates.mk_ne_zero.mpr (pow_ne_zero n a.ne_bot)) hirr_w, ihn]
        by_cases hwa : w = a
        · subst hwa
          rw [if_pos rfl, if_pos rfl, Associates.count_self hirr_w]
          omega
        · rw [if_neg hwa, if_neg hwa, add_zero]
          by_contra hnz
          have hdvd : w.asIdeal ∣ a.asIdeal :=
            (Associates.count_ne_zero_iff_dvd a.ne_bot
              (Ideal.prime_of_isPrime w.ne_bot w.isPrime).irreducible).mp hnz
          have hle : a.asIdeal ≤ w.asIdeal := Ideal.dvd_iff_le.mp hdvd
          have heq : a.asIdeal = w.asIdeal := a.isMaximal.eq_of_le w.isPrime.ne_top hle
          exact hwa (HeightOneSpectrum.ext heq.symm)
    rw [Finset.prod_insert ha]
    unfold idealOrd
    rw [← Associates.mk_mul_mk, Associates.count_mul hne_aa hne_as hirr_w]
    change idealOrd (a.asIdeal ^ e a) w + idealOrd (∏ v ∈ s, v.asIdeal ^ e v) w = _
    rw [hpow_cnt, ih]
    by_cases hwa : w = a
    · subst hwa
      rw [if_pos rfl, if_neg ha, if_pos (Finset.mem_insert_self w s), add_zero]
    · simp [hwa]

/-- Helper: every nonzero integral ideal `I : Ideal (𝓞 K)` equals the finite product of
`v.asIdeal ^ idealOrd I v` over its finite support `S`. -/
theorem eq_prod_prime_pow_idealOrd {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) :
    I = ∏ v ∈ (idealOrd_finite_support hI).toFinset, v.asIdeal ^ idealOrd I v := by
  classical
  have hfac := Ideal.finprod_heightOneSpectrum_factorization hI
  conv_lhs => rw [← hfac]
  rw [finprod_eq_prod_of_mulSupport_subset _ (s := (idealOrd_finite_support hI).toFinset)]
  · rfl
  · intro v hv
    rw [Finset.mem_coe, Set.Finite.mem_toFinset]
    intro h0
    apply hv
    change v.asIdeal ^ idealOrd I v = 1
    rw [h0, pow_zero]

/-- **Exact Kernel Theorem**: `ker(ideleToFractionalIdeal K) = U_{K,f}`. -/
theorem ideleToFractionalIdeal_ker (K : Type*) [Field K] [NumberField K] :
    (ideleToFractionalIdeal K).ker = finUnitSubgroup K := by
  classical
  ext x
  rw [MonoidHom.mem_ker, mem_finUnitSubgroup_iff]
  constructor
  · intro hker v
    rw [← ideleOrd_eq_zero_iff]
    set S : Finset (HeightOneSpectrum (𝓞 K)) := (ideleOrd_finite_support x).toFinset
    have hprod1 : ∏ w ∈ S, primeFracUnit K w ^ ideleOrd x w = 1 := by
      have h1 : ideleToFractionalIdeal K x = ∏ w ∈ S, primeFracUnit K w ^ ideleOrd x w := by
        change ∏ᶠ w, primeFracUnit K w ^ ideleOrd x w = _
        rw [finprod_eq_prod_of_mulSupport_subset _ (s := S)]
        intro w hw
        rw [Finset.mem_coe, Set.Finite.mem_toFinset]
        intro h0
        exact hw (by simp [h0])
      rw [← h1, hker]
    set Spos := S.filter (fun w => 0 ≤ ideleOrd x w)
    set Sneg := S.filter (fun w => ideleOrd x w < 0)
    have hsplit : S = Spos ∪ Sneg := by
      ext w
      simp only [Spos, Sneg, Finset.mem_union, Finset.mem_filter]
      constructor
      · intro hw; by_cases h : 0 ≤ ideleOrd x w <;> [exact Or.inl ⟨hw, h⟩; exact Or.inr ⟨hw, by omega⟩]
      · rintro (⟨hw, _⟩ | ⟨hw, _⟩) <;> exact hw
    have hdisj : Disjoint Spos Sneg := by
      rw [Finset.disjoint_filter]
      intro w _ h1 h2; omega
    rw [hsplit, Finset.prod_union hdisj] at hprod1
    have heq_u :
        ∏ w ∈ Spos, primeFracUnit K w ^ (ideleOrd x w).toNat =
          ∏ w ∈ Sneg, primeFracUnit K w ^ (-ideleOrd x w).toNat := by
      have hpos :
          ∏ w ∈ Spos, primeFracUnit K w ^ ideleOrd x w =
            ∏ w ∈ Spos, primeFracUnit K w ^ (ideleOrd x w).toNat := by
        refine Finset.prod_congr rfl fun w hw => ?_
        have hnn : 0 ≤ ideleOrd x w := (Finset.mem_filter.mp hw).2
        rw [← zpow_natCast, Int.toNat_of_nonneg hnn]
      have hneg :
          ∏ w ∈ Sneg, primeFracUnit K w ^ ideleOrd x w =
            (∏ w ∈ Sneg, primeFracUnit K w ^ (-ideleOrd x w).toNat)⁻¹ := by
        rw [← Finset.prod_inv_distrib]
        refine Finset.prod_congr rfl fun w hw => ?_
        have hlt : ideleOrd x w < 0 := (Finset.mem_filter.mp hw).2
        have hnn : 0 ≤ -ideleOrd x w := by omega
        rw [← zpow_natCast, Int.toNat_of_nonneg hnn, zpow_neg, inv_inv]
      rw [hpos, hneg] at hprod1
      exact mul_inv_eq_one.mp hprod1
    have heq_id :
        ∏ w ∈ Spos, w.asIdeal ^ (ideleOrd x w).toNat =
          ∏ w ∈ Sneg, w.asIdeal ^ (-ideleOrd x w).toNat := by
      apply FractionalIdeal.coeIdeal_injective (R := 𝓞 K) (K := K)
      dsimp only
      rw [← coe_finset_prod_primeFracUnit Spos (fun w => (ideleOrd x w).toNat),
        ← coe_finset_prod_primeFracUnit Sneg (fun w => (-ideleOrd x w).toNat)]
      exact congrArg Units.val heq_u
    have hcnt := congrArg (fun I => idealOrd I v) heq_id
    rw [idealOrd_prod_prime_pow, idealOrd_prod_prime_pow] at hcnt
    by_cases hv : v ∈ S
    · by_cases hnn : 0 ≤ ideleOrd x v
      · have hmem1 : v ∈ Spos := Finset.mem_filter.mpr ⟨hv, hnn⟩
        have hmem2 : v ∉ Sneg := fun h => by have := (Finset.mem_filter.mp h).2; omega
        rw [if_pos hmem1, if_neg hmem2] at hcnt
        omega
      · have hmem1 : v ∉ Spos := fun h => hnn (Finset.mem_filter.mp h).2
        have hmem2 : v ∈ Sneg := Finset.mem_filter.mpr ⟨hv, by omega⟩
        rw [if_neg hmem1, if_pos hmem2] at hcnt
        omega
    · rw [Set.Finite.mem_toFinset] at hv
      simpa using hv
  · intro hv
    change ∏ᶠ w, primeFracUnit K w ^ ideleOrd x w = 1
    have hfun : (fun w : HeightOneSpectrum (𝓞 K) => primeFracUnit K w ^ ideleOrd x w) = fun _ => 1 := by
      funext w
      rw [(ideleOrd_eq_zero_iff x w).mpr (hv w), zpow_zero]
    rw [hfun, finprod_one]

/-- Helper: every nonzero integral ideal `I : Ideal (𝓞 K)` lies in the range of
`ideleToFractionalIdeal K`. -/
theorem exists_finIdele_ideleToFractionalIdeal_coeIdeal {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) :
    ∃ x : FinIdele K, ideleToFractionalIdeal K x = coeIdealUnit I hI := by
  classical
  choose π hπ using fun v : HeightOneSpectrum (𝓞 K) => v.intValuation_exists_uniformizer
  have hπ_val : ∀ v : HeightOneSpectrum (𝓞 K),
      Valued.v (algebraMap (𝓞 K) (v.adicCompletion K) (π v)) = WithZero.exp (-1) := by
    intro v
    rw [valued_algebraMap_int, hπ v]
  have hπ_ne : ∀ v : HeightOneSpectrum (𝓞 K),
      algebraMap (𝓞 K) (v.adicCompletion K) (π v) ≠ 0 := by
    intro v h0
    have hv := hπ_val v
    rw [h0, map_zero] at hv
    exact WithZero.zero_ne_coe hv
  have hfin : ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, idealOrd I v = 0 := by
    simpa only [Filter.Eventually, Filter.mem_cofinite, Set.compl_ofPred] using idealOrd_finite_support hI
  let x : FinIdele K :=
    { val := RestrictedProduct.mk
        (fun v => if idealOrd I v = 0 then (1 : v.adicCompletion K)
          else (algebraMap (𝓞 K) (v.adicCompletion K) (π v)) ^ idealOrd I v)
        (by
          filter_upwards [hfin] with v hv
          simp only [hv, ↓reduceIte]
          exact (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 K) K v).mpr (by rw [map_one]))
      inv := RestrictedProduct.mk
        (fun v => if idealOrd I v = 0 then (1 : v.adicCompletion K)
          else ((algebraMap (𝓞 K) (v.adicCompletion K) (π v)) ^ idealOrd I v)⁻¹)
        (by
          filter_upwards [hfin] with v hv
          simp only [hv, ↓reduceIte]
          exact (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 K) K v).mpr (by rw [map_one]))
      val_inv := finAdele_ext fun v => by
        change (if idealOrd I v = 0 then (1 : v.adicCompletion K) else _) *
          (if idealOrd I v = 0 then (1 : v.adicCompletion K) else _) = 1
        split_ifs with h0
        · exact one_mul 1
        · exact mul_inv_cancel₀ (pow_ne_zero _ (hπ_ne v))
      inv_val := finAdele_ext fun v => by
        change (if idealOrd I v = 0 then (1 : v.adicCompletion K) else _) *
          (if idealOrd I v = 0 then (1 : v.adicCompletion K) else _) = 1
        split_ifs with h0
        · exact one_mul 1
        · exact inv_mul_cancel₀ (pow_ne_zero _ (hπ_ne v)) }
  refine ⟨x, ?_⟩
  have hord : ∀ v : HeightOneSpectrum (𝓞 K), ideleOrd x v = (idealOrd I v : ℤ) := by
    intro v
    unfold ideleOrd
    change -(WithZero.log (Valued.v (if idealOrd I v = 0 then (1 : v.adicCompletion K)
      else (algebraMap (𝓞 K) (v.adicCompletion K) (π v)) ^ idealOrd I v))) = _
    split_ifs with h0
    · rw [map_one, WithZero.log_one, neg_zero, h0, Nat.cast_zero]
    · rw [map_pow, hπ_val v, ← WithZero.exp_nsmul, smul_neg, nsmul_eq_mul, mul_one,
        WithZero.log_exp, neg_neg]
  set S : Finset (HeightOneSpectrum (𝓞 K)) := (idealOrd_finite_support hI).toFinset
  have hprod_x :
      ideleToFractionalIdeal K x = ∏ v ∈ S, primeFracUnit K v ^ (idealOrd I v) := by
    change ∏ᶠ v, primeFracUnit K v ^ ideleOrd x v = _
    rw [finprod_eq_prod_of_mulSupport_subset _ (s := S)]
    · refine Finset.prod_congr rfl fun v _ => ?_
      rw [hord v, zpow_natCast]
    · intro v hv
      rw [Finset.mem_coe, Set.Finite.mem_toFinset]
      intro h0
      exact hv (by simp [hord v, h0])
  have hprod_I : I = ∏ v ∈ S, v.asIdeal ^ idealOrd I v := eq_prod_prime_pow_idealOrd hI
  apply Units.ext
  rw [hprod_x, coeIdealUnit_val]
  conv_rhs => rw [hprod_I]
  exact coe_finset_prod_primeFracUnit S (idealOrd I)

/-- **Surjectivity Theorem**: `ideleToFractionalIdeal K : 𝕀_{K,f} →* (FractionalIdeal (𝓞 K)⁰ K)ˣ`
is surjective onto the entire group of nonzero fractional ideals. -/
theorem ideleToFractionalIdeal_surjective (K : Type*) [Field K] [NumberField K] :
    Function.Surjective (ideleToFractionalIdeal K) := by
  intro J
  obtain ⟨a, I, ha, hJ⟩ := FractionalIdeal.exists_eq_spanSingleton_mul J.val
  have hI : I ≠ ⊥ := by
    intro hbot
    rw [hbot, FractionalIdeal.coeIdeal_bot, mul_zero] at hJ
    exact J.ne_zero hJ
  have ha_span : Ideal.span {a} ≠ ⊥ := by
    rw [ne_eq, Ideal.span_singleton_eq_bot]
    exact ha
  obtain ⟨xI, hxI⟩ := exists_finIdele_ideleToFractionalIdeal_coeIdeal (K := K) hI
  obtain ⟨xa, hxa⟩ := exists_finIdele_ideleToFractionalIdeal_coeIdeal (K := K) ha_span
  refine ⟨xI * xa⁻¹, ?_⟩
  rw [map_mul, map_inv, hxI, hxa]
  apply Units.ext
  rw [Units.val_mul, Units.val_inv_eq_inv_val, coeIdealUnit_val, coeIdealUnit_val,
    FractionalIdeal.coeIdeal_span_singleton, hJ, mul_comm,
    ← FractionalIdeal.spanSingleton_inv]

/-- **Principal Compatibility Theorem**: on principal ideles `diagFinIdele K`, the content
homomorphism `ideleToFractionalIdeal K` coincides identically with `toPrincipalIdeal (𝓞 K) K`. -/
theorem ideleToFractionalIdeal_comp_diagFinIdele (K : Type*) [Field K] [NumberField K] :
    (ideleToFractionalIdeal K).comp (diagFinIdele K) = toPrincipalIdeal (𝓞 K) K := by
  classical
  have h_int : ∀ (r : 𝓞 K) (hr : r ≠ 0),
      ideleToFractionalIdeal K (diagFinIdele K
        (Units.mk0 (algebraMap (𝓞 K) K r)
          (by simpa [map_eq_zero_iff _ (IsFractionRing.injective (𝓞 K) K)] using hr))) =
        toPrincipalIdeal (𝓞 K) K
          (Units.mk0 (algebraMap (𝓞 K) K r)
            (by simpa [map_eq_zero_iff _ (IsFractionRing.injective (𝓞 K) K)] using hr)) := by
    intro r hr
    set kr : Kˣ := Units.mk0 (algebraMap (𝓞 K) K r)
      (by simpa [map_eq_zero_iff _ (IsFractionRing.injective (𝓞 K) K)] using hr)
    have hord : ∀ v : HeightOneSpectrum (𝓞 K),
        ideleOrd (diagFinIdele K kr) v = (idealOrd (Ideal.span {r}) v : ℤ) := by
      intro v
      unfold ideleOrd idealOrd
      have hval : Valued.v ((diagFinIdele K kr).val v) = v.intValuation r := by
        change Valued.v ((FiniteAdeleRing.algebraMap (𝓞 K) K (algebraMap (𝓞 K) K r)) v) = _
        rw [valued_finAdele_algebraMap, HeightOneSpectrum.valuation_of_algebraMap]
      rw [hval, HeightOneSpectrum.intValuation_apply, HeightOneSpectrum.intValuationDef_if_neg v hr,
        WithZero.log_exp, neg_neg]
    have hspan_ne : Ideal.span {r} ≠ ⊥ := by
      rw [ne_eq, Ideal.span_singleton_eq_bot]; exact hr
    set S : Finset (HeightOneSpectrum (𝓞 K)) := (idealOrd_finite_support hspan_ne).toFinset
    have hprod_x :
        ideleToFractionalIdeal K (diagFinIdele K kr) =
          ∏ v ∈ S, primeFracUnit K v ^ (idealOrd (Ideal.span {r}) v) := by
      change ∏ᶠ v, primeFracUnit K v ^ ideleOrd (diagFinIdele K kr) v = _
      rw [finprod_eq_prod_of_mulSupport_subset _ (s := S)]
      · refine Finset.prod_congr rfl fun v _ => ?_
        rw [hord v, zpow_natCast]
      · intro v hv
        rw [Finset.mem_coe, Set.Finite.mem_toFinset]
        intro h0
        exact hv (by simp [hord v, h0])
    have hprod_I : Ideal.span {r} = ∏ v ∈ S, v.asIdeal ^ idealOrd (Ideal.span {r}) v :=
      eq_prod_prime_pow_idealOrd hspan_ne
    symm
    rw [toPrincipalIdeal_eq_iff, hprod_x]
    change FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (algebraMap (𝓞 K) K r) = _
    rw [← FractionalIdeal.coeIdeal_span_singleton]
    conv_lhs => rw [hprod_I]
    exact (coe_finset_prod_primeFracUnit S (idealOrd (Ideal.span {r}))).symm
  apply MonoidHom.ext
  intro k
  obtain ⟨⟨a, s⟩, hks⟩ := IsLocalization.surj (nonZeroDivisors (𝓞 K)) k.val
  have hs_ne : (s : 𝓞 K) ≠ 0 := nonZeroDivisors.ne_zero s.2
  have ha_ne : a ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hks
    have hsK : algebraMap (𝓞 K) K (s : 𝓞 K) ≠ 0 := by
      simp [map_eq_zero_iff _ (IsFractionRing.injective (𝓞 K) K), hs_ne]
    exact k.ne_zero ((mul_eq_zero.mp hks).resolve_right hsK)
  set ka : Kˣ := Units.mk0 (algebraMap (𝓞 K) K a)
    (by simp [map_eq_zero_iff _ (IsFractionRing.injective (𝓞 K) K), ha_ne])
  set ks : Kˣ := Units.mk0 (algebraMap (𝓞 K) K (s : 𝓞 K))
    (by simp [map_eq_zero_iff _ (IsFractionRing.injective (𝓞 K) K), hs_ne])
  have hk_eq : k = ka * ks⁻¹ := by
    apply Units.ext
    have hsK : algebraMap (𝓞 K) K (s : 𝓞 K) ≠ 0 := ks.ne_zero
    calc k.val = k.val * algebraMap (𝓞 K) K (s : 𝓞 K) * (algebraMap (𝓞 K) K (s : 𝓞 K))⁻¹ := by
          rw [mul_inv_cancel_right₀ hsK]
      _ = algebraMap (𝓞 K) K a * (algebraMap (𝓞 K) K (s : 𝓞 K))⁻¹ := by rw [hks]
      _ = (ka * ks⁻¹).val := rfl
  rw [hk_eq, MonoidHom.comp_apply, map_mul, map_inv, map_mul, map_inv, map_mul, map_inv,
    h_int a ha_ne, h_int (s : 𝓞 K) hs_ne]

/-- The canonical surjective homomorphism `𝕀_{K,f} →* ClassGroup (𝓞 K)` composing
`ideleToFractionalIdeal K` with `ClassGroup.mk K`. -/
def ideleToClassGroup (K : Type*) [Field K] [NumberField K] :
    FinIdele K →* ClassGroup (𝓞 K) :=
  (ClassGroup.mk K).comp (ideleToFractionalIdeal K)

theorem ideleToClassGroup_surjective (K : Type*) [Field K] [NumberField K] :
    Function.Surjective (ideleToClassGroup K) := by
  have hmk : Function.Surjective (ClassGroup.mk (R := 𝓞 K) K) := by
    intro c
    obtain ⟨J, hJ⟩ := QuotientGroup.mk'_surjective (toPrincipalIdeal (𝓞 K) K).range
      (ClassGroup.equiv K c)
    let e : (FractionalIdeal (nonZeroDivisors (𝓞 K)) K)ˣ ≃*
        (FractionalIdeal (nonZeroDivisors (𝓞 K)) K)ˣ :=
      Units.mapEquiv (FractionalIdeal.canonicalEquiv (nonZeroDivisors (𝓞 K)) K K : _ ≃* _)
    refine ⟨e.symm J, ?_⟩
    apply (ClassGroup.equiv K).injective
    rw [ClassGroup.equiv_mk]
    change QuotientGroup.mk' (toPrincipalIdeal (𝓞 K) K).range (e (e.symm J)) = _
    rw [e.apply_symm_apply]
    exact hJ
  exact hmk.comp (ideleToFractionalIdeal_surjective K)

/-- **Exact Kernel of `ideleToClassGroup K`**: `ker(𝕀_{K,f} →* ClassGroup (𝓞 K)) = Kˣ · U_{K,f}`. -/
theorem ideleToClassGroup_ker (K : Type*) [Field K] [NumberField K] :
    (ideleToClassGroup K).ker = principalSubgroup K ⊔ finUnitSubgroup K := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_sup]
  constructor
  · intro hx
    have hprin : Submodule.IsPrincipal
        ((ideleToFractionalIdeal K x).val : Submodule (𝓞 K) K) :=
      (ClassGroup.mk_eq_one_iff (R := 𝓞 K) (K := K)).mp hx
    obtain ⟨a, ha⟩ := hprin
    have ha_frac : (ideleToFractionalIdeal K x).val =
        FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) a := by
      apply FractionalIdeal.coeToSubmodule_injective
      change ((ideleToFractionalIdeal K x).val : Submodule (𝓞 K) K) =
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) a : Submodule (𝓞 K) K)
      rw [ha, FractionalIdeal.coe_spanSingleton]
    have ha_ne : a ≠ 0 := by
      intro h0
      rw [h0, FractionalIdeal.spanSingleton_zero] at ha_frac
      exact (ideleToFractionalIdeal K x).ne_zero ha_frac
    set k : Kˣ := Units.mk0 a ha_ne
    have hk : toPrincipalIdeal (𝓞 K) K k = ideleToFractionalIdeal K x :=
      (toPrincipalIdeal_eq_iff (R := 𝓞 K) (K := K)).mpr ha_frac.symm
    have hcomp := congrFun (congrArg DFunLike.coe (ideleToFractionalIdeal_comp_diagFinIdele K)) k
    simp only [MonoidHom.comp_apply] at hcomp
    have hker : (diagFinIdele K k)⁻¹ * x ∈ (ideleToFractionalIdeal K).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hcomp, hk, inv_mul_cancel]
    rw [ideleToFractionalIdeal_ker] at hker
    refine ⟨diagFinIdele K k, ⟨k, rfl⟩, (diagFinIdele K k)⁻¹ * x, hker, ?_⟩
    rw [mul_inv_cancel_left]
  · rintro ⟨p, ⟨k, rfl⟩, u, hu, rfl⟩
    change ClassGroup.mk K (ideleToFractionalIdeal K (diagFinIdele K k * u)) = 1
    rw [map_mul]
    have hu1 : ideleToFractionalIdeal K u = 1 := by
      rw [← MonoidHom.mem_ker, ideleToFractionalIdeal_ker]
      exact hu
    rw [hu1, mul_one]
    have hcomp := congrFun (congrArg DFunLike.coe (ideleToFractionalIdeal_comp_diagFinIdele K)) k
    simp only [MonoidHom.comp_apply] at hcomp
    rw [hcomp, ClassGroup.mk_eq_one_iff]
    refine ⟨k.val, ?_⟩
    rw [← FractionalIdeal.coe_spanSingleton (nonZeroDivisors (𝓞 K)) k.val]
    exact congrArg (fun I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K => (I : Submodule (𝓞 K) K))
      ((toPrincipalIdeal_eq_iff (R := 𝓞 K) (K := K) (x := k)
        (I := toPrincipalIdeal (𝓞 K) K k)).mp rfl).symm

/-- **Canonical Idele-Class ↔ Ideal-Class Group Isomorphism**:
`FinIdele K ⧸ (principalSubgroup K ⊔ finUnitSubgroup K) ≃* ClassGroup (𝓞 K)`. -/
def ideleClassEquivClassGroup (K : Type*) [Field K] [NumberField K] :
    FinIdele K ⧸ (principalSubgroup K ⊔ finUnitSubgroup K) ≃* ClassGroup (𝓞 K) :=
  (QuotientGroup.quotientMulEquivOfEq (ideleToClassGroup_ker K).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (ideleToClassGroup K)
      (ideleToClassGroup_surjective K))

/-- **Unconditional Finiteness of the Idele-Class Quotient** directly from Mathlib's
`Fintype (ClassGroup (𝓞 K))`. -/
theorem finite_ideleClassQuotient (K : Type*) [Field K] [NumberField K] :
    Finite (FinIdele K ⧸ (principalSubgroup K ⊔ finUnitSubgroup K)) :=
  Finite.of_equiv (ClassGroup (𝓞 K)) (ideleClassEquivClassGroup K).symm.toEquiv

/-- **Exact Order of the Idele-Class Quotient**:
`Nat.card (𝕀_{K,f} / (Kˣ · U_{K,f})) = NumberField.classNumber K`. -/
theorem card_ideleClassQuotient_eq_classNumber (K : Type*) [Field K] [NumberField K] :
    Nat.card (FinIdele K ⧸ (principalSubgroup K ⊔ finUnitSubgroup K)) =
      NumberField.classNumber K := by
  rw [Nat.card_congr (ideleClassEquivClassGroup K).toEquiv, Nat.card_eq_fintype_card]
  rfl

/-- Canonical embedding of global units `(𝓞 K)ˣ` into `Kˣ`. -/
def intUnitsToFieldUnits (K : Type*) [Field K] [NumberField K] : (𝓞 K)ˣ →* Kˣ :=
  Units.map (algebraMap (𝓞 K) K).toMonoidHom

/-- Canonical embedding of global units `(𝓞 K)ˣ` into `U_{K,f}`. -/
def intUnitsToFinUnits (K : Type*) [Field K] [NumberField K] : (𝓞 K)ˣ →* finUnitSubgroup K where
  toFun ε :=
    ⟨diagFinIdele K (intUnitsToFieldUnits K ε), fun v => by
      change Valued.v ((FiniteAdeleRing.algebraMap (𝓞 K) K (algebraMap (𝓞 K) K ε.val)) v) = 1
      rw [valued_finAdele_algebraMap, HeightOneSpectrum.valuation_of_algebraMap,
        HeightOneSpectrum.intValuation_eq_one_iff]
      intro hmem
      have htop : v.asIdeal = ⊤ := v.asIdeal.eq_top_of_isUnit_mem hmem ε.isUnit
      exact v.isPrime.ne_top htop⟩
  map_one' := by
    apply Subtype.ext
    simp [intUnitsToFieldUnits]
  map_mul' ε₁ ε₂ := by
    apply Subtype.ext
    simp [intUnitsToFieldUnits]

/-- **Exact Intersection `Kˣ ∩ U_{K,f} = (𝓞 K)ˣ`**: a principal finite idele `diag(k)` is a unit
at every finite place iff `k` comes from a global unit `ε ∈ (𝓞 K)ˣ`. -/
theorem diagFinIdele_mem_finUnitSubgroup_iff (k : Kˣ) :
    diagFinIdele K k ∈ finUnitSubgroup K ↔ ∃ ε : (𝓞 K)ˣ, intUnitsToFieldUnits K ε = k := by
  constructor
  · intro hk
    have h1 : ideleToFractionalIdeal K (diagFinIdele K k) = 1 := by
      rw [← MonoidHom.mem_ker, ideleToFractionalIdeal_ker]
      exact hk
    have hcomp := congrFun (congrArg DFunLike.coe (ideleToFractionalIdeal_comp_diagFinIdele K)) k
    simp only [MonoidHom.comp_apply] at hcomp
    rw [hcomp] at h1
    have hspan : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) k.val = 1 :=
      (toPrincipalIdeal_eq_iff (R := 𝓞 K) (K := K)).mp h1
    have hmem1 : k.val ∈ (1 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) := by
      rw [← hspan]
      exact FractionalIdeal.mem_spanSingleton_self (nonZeroDivisors (𝓞 K)) k.val
    have hspan_inv : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) k.inv = 1 := by
      have := congrArg (fun I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K => I⁻¹) hspan
      simpa [FractionalIdeal.spanSingleton_inv] using this
    have hmem2 : k.inv ∈ (1 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) := by
      rw [← hspan_inv]
      exact FractionalIdeal.mem_spanSingleton_self (nonZeroDivisors (𝓞 K)) k.inv
    rw [FractionalIdeal.mem_one_iff] at hmem1 hmem2
    obtain ⟨a, ha⟩ := hmem1
    obtain ⟨b, hb⟩ := hmem2
    have hab : a * b = 1 := by
      apply IsFractionRing.injective (𝓞 K) K
      rw [map_mul, map_one, ha, hb, k.val_inv]
    have hba : b * a = 1 := mul_comm a b ▸ hab
    refine ⟨⟨a, b, hab, hba⟩, ?_⟩
    apply Units.ext
    exact ha
  · rintro ⟨ε, rfl⟩
    exact (intUnitsToFinUnits K ε).2

end FiniteIdeles

/-! ## Section 2: Concrete Ray Class Groups `Cl_𝔪(K)` & Exact Ray-Class Sequence -/

section RayClassGroups

variable {K : Type*} [Field K] [NumberField K]

/-- Every element `k ∈ K` with `v(k) ≤ 1` can be written as `a / b` with `a, b ∈ 𝓞 K` and
`b ∉ v.asIdeal`. -/
theorem exists_div_not_mem_of_valuation_le_one (v : HeightOneSpectrum (𝓞 K)) {k : K}
    (hk : v.valuation K k ≤ 1) :
    ∃ a b : 𝓞 K, b ∉ v.asIdeal ∧ k * algebraMap (𝓞 K) K b = algebraMap (𝓞 K) K a := by
  by_cases hk0 : k = 0
  · exact ⟨0, 1, fun h => v.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h isUnit_one),
      by simp [hk0]⟩
  obtain ⟨⟨a, s⟩, hks⟩ := IsLocalization.surj (nonZeroDivisors (𝓞 K)) k
  set b : 𝓞 K := s.1
  have hb_ne : b ≠ 0 := nonZeroDivisors.ne_zero s.2
  have ha_ne : a ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hks
    have hbK : algebraMap (𝓞 K) K b ≠ 0 := by
      simp [map_eq_zero_iff _ (IsFractionRing.injective (𝓞 K) K), hb_ne]
    exact hk0 ((mul_eq_zero.mp hks).resolve_right hbK)
  have hval_le : v.intValuation a ≤ v.intValuation b := by
    have h1 := congrArg (v.valuation K) hks
    rw [map_mul, HeightOneSpectrum.valuation_of_algebraMap,
      HeightOneSpectrum.valuation_of_algebraMap] at h1
    rw [← h1]
    have hle : v.valuation K k * v.intValuation b ≤ 1 * v.intValuation b :=
      mul_le_mul' hk le_rfl
    simpa only [one_mul] using hle
  set D : Ideal (𝓞 K) := Ideal.span {a} ⊔ Ideal.span {b}
  have hD_ne : D ≠ 0 := by
    intro h0
    have hle : Ideal.span {b} ≤ D := le_sup_right
    rw [h0] at hle
    exact hb_ne (Ideal.span_singleton_eq_bot.mp (le_bot_iff.mp hle))
  obtain ⟨I₁, hI₁⟩ := Ideal.dvd_iff_le.mpr (le_sup_left : Ideal.span {a} ≤ D)
  obtain ⟨I₂, hI₂⟩ := Ideal.dvd_iff_le.mpr (le_sup_right : Ideal.span {b} ≤ D)
  have hsup : I₁ ⊔ I₂ = ⊤ := by
    have hmul : D * (I₁ ⊔ I₂) = D * ⊤ := by
      rw [Ideal.mul_sup, ← hI₁, ← hI₂, Ideal.mul_top]
    exact mul_left_cancel₀ hD_ne hmul
  have hI₂_not_le : ¬ I₂ ≤ v.asIdeal := by
    intro hle2
    have hI₁_ne : I₁ ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hI₁
      exact ha_ne (Ideal.span_singleton_eq_bot.mp hI₁)
    have hI₂_ne : I₂ ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hI₂
      exact hb_ne (Ideal.span_singleton_eq_bot.mp hI₂)
    have hirr : Irreducible (Associates.mk v.asIdeal) :=
      Associates.irreducible_mk.mpr (Ideal.prime_of_isPrime v.ne_bot v.isPrime).irreducible
    have hcnt_a : idealOrd (Ideal.span {a}) v = idealOrd D v + idealOrd I₁ v := by
      unfold idealOrd
      rw [hI₁, ← Associates.mk_mul_mk,
        Associates.count_mul (Associates.mk_ne_zero.mpr hD_ne)
          (Associates.mk_ne_zero.mpr hI₁_ne) hirr]
    have hcnt_b : idealOrd (Ideal.span {b}) v = idealOrd D v + idealOrd I₂ v := by
      unfold idealOrd
      rw [hI₂, ← Associates.mk_mul_mk,
        Associates.count_mul (Associates.mk_ne_zero.mpr hD_ne)
          (Associates.mk_ne_zero.mpr hI₂_ne) hirr]
    have hcnt_ge : idealOrd (Ideal.span {b}) v ≤ idealOrd (Ideal.span {a}) v := by
      rw [HeightOneSpectrum.intValuation_apply, HeightOneSpectrum.intValuation_apply,
        HeightOneSpectrum.intValuationDef_if_neg v ha_ne,
        HeightOneSpectrum.intValuationDef_if_neg v hb_ne, WithZero.exp_le_exp] at hval_le
      change (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {b})).factors ≤
        (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {a})).factors
      omega
    have hcnt2_pos : 0 < idealOrd I₂ v := by
      apply Nat.pos_of_ne_zero
      exact (Associates.count_ne_zero_iff_dvd hI₂_ne
        (Ideal.prime_of_isPrime v.ne_bot v.isPrime).irreducible).mpr (Ideal.dvd_iff_le.mpr hle2)
    have hcnt1_pos : 0 < idealOrd I₁ v := by omega
    have hle1 : I₁ ≤ v.asIdeal := Ideal.dvd_iff_le.mp <|
      (Associates.count_ne_zero_iff_dvd hI₁_ne
        (Ideal.prime_of_isPrime v.ne_bot v.isPrime).irreducible).mp hcnt1_pos.ne'
    have htop : (⊤ : Ideal (𝓞 K)) ≤ v.asIdeal := by
      rw [← hsup]
      exact sup_le hle1 hle2
    exact v.isPrime.ne_top (top_le_iff.mp htop)
  obtain ⟨b', hb'I₂, hb'v⟩ := SetLike.not_le_iff_exists.mp hI₂_not_le
  have hmem_span_b : b' * a ∈ Ideal.span {b} := by
    have h1 : Ideal.span {b' * a} ≤ Ideal.span {b} := by
      calc Ideal.span {b' * a}
          = Ideal.span {b'} * Ideal.span {a} := by rw [Ideal.span_singleton_mul_span_singleton]
        _ = Ideal.span {b'} * (D * I₁) := by rw [hI₁]
        _ ≤ I₂ * (D * I₁) := Ideal.mul_le.mpr fun x hx y hy =>
            Ideal.mul_mem_mul ((Ideal.span_singleton_le_iff_mem _).mpr hb'I₂ hx) hy
        _ = (D * I₂) * I₁ := by ring
        _ = Ideal.span {b} * I₁ := by rw [hI₂]
        _ ≤ Ideal.span {b} := Ideal.mul_le_left
    exact (Ideal.span_singleton_le_iff_mem _).mp h1
  obtain ⟨a', ha'⟩ := Ideal.mem_span_singleton.mp hmem_span_b
  refine ⟨a', b', hb'v, ?_⟩
  have hbK : algebraMap (𝓞 K) K b ≠ 0 := by
    simp [map_eq_zero_iff _ (IsFractionRing.injective (𝓞 K) K), hb_ne]
  apply mul_right_cancel₀ hbK
  calc k * algebraMap (𝓞 K) K b' * algebraMap (𝓞 K) K b
      = k * algebraMap (𝓞 K) K b * algebraMap (𝓞 K) K b' := by ring
    _ = algebraMap (𝓞 K) K a * algebraMap (𝓞 K) K b' := by rw [hks]
    _ = algebraMap (𝓞 K) K (b' * a) := by rw [map_mul, mul_comm]
    _ = algebraMap (𝓞 K) K (b * a') := by rw [ha']
    _ = algebraMap (𝓞 K) K a' * algebraMap (𝓞 K) K b := by rw [map_mul, mul_comm]

/-- Helper: density of `K` in `v.adicCompletion K`. -/
private theorem local_approx_field (v : HeightOneSpectrum (𝓞 K)) (x : v.adicCompletion K) (n : ℕ) :
    ∃ k : K, Valued.v (x - algebraMap K (v.adicCompletion K) k) ≤ WithZero.exp (-(n : ℤ)) := by
  obtain ⟨π, hπ⟩ := v.intValuation_exists_uniformizer
  let πK : K := algebraMap (𝓞 K) K (π ^ n)
  let πC : (v.valuation K).Completion :=
    ((WithVal.equiv (v.valuation K)).symm πK : WithVal (v.valuation K))
  have hπC_val : Valued.v πC = WithZero.exp (-(n : ℤ)) := by
    have h1 := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (R := 𝓞 K) (K := K) v πK
    change Valued.v πC = v.valuation K πK at h1
    rw [h1, HeightOneSpectrum.valuation_of_algebraMap, map_pow, hπ, ← WithZero.exp_nsmul,
      smul_neg, nsmul_eq_mul, mul_one]
  let r₀ := Valued.v.restrict (R := (v.valuation K).Completion) πC
  have hr₀_ne : r₀ ≠ 0 := by
    intro h0
    have h1 : Valued.v πC = 0 :=
      (Valuation.restrict_eq_zero_iff (v := Valued.v (R := (v.valuation K).Completion))
        (x := πC)).mp h0
    rw [hπC_val] at h1
    exact WithZero.coe_ne_zero h1
  have hopen0 : IsOpen {z : (v.valuation K).Completion | Valued.v.restrict z ≤ r₀} :=
    Valued.isOpen_closedBall _ hr₀_ne
  have hopen :
      IsOpen {y : (v.valuation K).Completion | Valued.v.restrict (y - x.toCompletion) ≤ r₀} :=
    hopen0.preimage (continuous_id.sub continuous_const)
  have hne :
      {y : (v.valuation K).Completion | Valued.v.restrict (y - x.toCompletion) ≤ r₀}.Nonempty :=
    ⟨x.toCompletion, by simp⟩
  obtain ⟨kw, hkw⟩ := UniformSpace.Completion.denseRange_coe.exists_mem_open hopen hne
  let k : K := (WithVal.equiv (v.valuation K)) kw
  refine ⟨k, ?_⟩
  have hle : Valued.v ((kw : (v.valuation K).Completion) - x.toCompletion) ≤ Valued.v πC :=
    (Valuation.restrict_le_iff (v := Valued.v (R := (v.valuation K).Completion))).mp hkw
  rw [hπC_val] at hle
  have hsub : x - algebraMap K (v.adicCompletion K) k =
      -(algebraMap K (v.adicCompletion K) k - x) := by ring
  rw [hsub, Valuation.map_neg]
  have hkw_eq :
      (algebraMap K (v.adicCompletion K) k).toCompletion = (kw : (v.valuation K).Completion) := by
    have h := congrFun (HeightOneSpectrum.algebraMap_adicCompletion (𝓞 K) K (S := K) v) k
    have h' : (algebraMap K (v.adicCompletion K) k).toCompletion =
        ((WithVal.equiv (v.valuation K)).symm k : WithVal (v.valuation K)) := by
      simpa using congrArg HeightOneSpectrum.adicCompletion.toCompletion h
    rw [h']
    exact congrArg UniformSpace.Completion.coe' ((WithVal.equiv (v.valuation K)).symm_apply_apply kw)
  change Valued.v ((algebraMap K (v.adicCompletion K) k).toCompletion - x.toCompletion) ≤ _
  rw [hkw_eq]
  exact hle

/-- **Local Density Approximation in `v.adicCompletionIntegers K`**:
for every `x ∈ 𝒪_v` and every `n : ℕ`, there exists an integral element `r ∈ 𝓞 K` such that
`Valued.v (x - r) ≤ WithZero.exp (-n)`. -/
theorem local_approx_int (v : HeightOneSpectrum (𝓞 K)) (x : v.adicCompletionIntegers K) (n : ℕ) :
    ∃ r : 𝓞 K,
      Valued.v (x.val - algebraMap (𝓞 K) (v.adicCompletion K) r) ≤ WithZero.exp (-(n : ℤ)) := by
  obtain ⟨k, hdist_k⟩ := local_approx_field v x.val n
  have hk_le_one : v.valuation K k ≤ 1 := by
    rw [← valued_algebraMap_K v k]
    have hx_le : Valued.v x.val ≤ 1 :=
      (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 K) K v).mp x.2
    have hne_exp : WithZero.exp (-(n : ℤ)) ≤ 1 := by
      rw [← WithZero.exp_zero, WithZero.exp_le_exp]; omega
    have hrew : algebraMap K (v.adicCompletion K) k =
        x.val - (x.val - algebraMap K (v.adicCompletion K) k) := by ring
    rw [hrew]
    exact le_trans (Valuation.map_sub _ _ _) (max_le hx_le (le_trans hdist_k hne_exp))
  obtain ⟨a, b, hbv, hkab⟩ := exists_div_not_mem_of_valuation_le_one v hk_le_one
  have hcop1 : IsCoprime (Ideal.span {b}) v.asIdeal := by
    rw [Ideal.isCoprime_iff_sup_eq]
    by_contra hne_top
    have hle : Ideal.span {b} ⊔ v.asIdeal = v.asIdeal :=
      (v.isMaximal.eq_of_le hne_top le_sup_right).symm
    exact hbv ((Ideal.span_singleton_le_iff_mem _).mp (le_sup_left.trans hle.le))
  have hcop : IsCoprime (Ideal.span {b}) (v.asIdeal ^ n) := hcop1.pow_right
  rw [Ideal.isCoprime_iff_sup_eq, Ideal.eq_top_iff_one, Submodule.mem_sup] at hcop
  obtain ⟨u, hu, t, ht, hut⟩ := hcop
  obtain ⟨s, rfl⟩ := Ideal.mem_span_singleton.mp hu
  refine ⟨a * s, ?_⟩
  have hdiff_k : Valued.v (algebraMap K (v.adicCompletion K) (k - algebraMap (𝓞 K) K (a * s))) ≤
      WithZero.exp (-(n : ℤ)) := by
    rw [valued_algebraMap_K]
    have hbv1 : v.intValuation b = 1 := HeightOneSpectrum.intValuation_eq_one_iff.mpr hbv
    have hmul_b : (k - algebraMap (𝓞 K) K (a * s)) * algebraMap (𝓞 K) K b =
        algebraMap (𝓞 K) K (a * t) := by
      have ht1 : 1 - b * s = t := by rw [← hut]; ring
      calc (k - algebraMap (𝓞 K) K (a * s)) * algebraMap (𝓞 K) K b
          = k * algebraMap (𝓞 K) K b - algebraMap (𝓞 K) K (a * (b * s)) := by
            simp only [sub_mul, map_mul]; ring
        _ = algebraMap (𝓞 K) K a - algebraMap (𝓞 K) K (a * (b * s)) := by rw [hkab]
        _ = algebraMap (𝓞 K) K (a * (1 - b * s)) := by
            simp only [map_mul, map_sub, map_one]; ring
        _ = algebraMap (𝓞 K) K (a * t) := by rw [ht1]
    have hval_mul := congrArg (v.valuation K) hmul_b
    rw [map_mul, HeightOneSpectrum.valuation_of_algebraMap,
      HeightOneSpectrum.valuation_of_algebraMap, hbv1, mul_one] at hval_mul
    rw [hval_mul, map_mul]
    have ht_le : v.intValuation t ≤ WithZero.exp (-(n : ℤ)) :=
      (HeightOneSpectrum.intValuation_le_pow_iff_dvd v t n).mpr
        (Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr ht))
    calc v.intValuation a * v.intValuation t
        ≤ 1 * WithZero.exp (-(n : ℤ)) :=
          mul_le_mul' (HeightOneSpectrum.intValuation_le_one v a) ht_le
      _ = WithZero.exp (-(n : ℤ)) := one_mul _
  have hsplit : x.val - algebraMap (𝓞 K) (v.adicCompletion K) (a * s) =
      (x.val - algebraMap K (v.adicCompletion K) k) +
        algebraMap K (v.adicCompletion K) (k - algebraMap (𝓞 K) K (a * s)) := by
    rw [map_sub, IsScalarTower.algebraMap_apply (𝓞 K) K (v.adicCompletion K)]
    ring
  rw [hsplit]
  exact le_trans (Valuation.map_add _ _ _) (max_le hdist_k hdiff_k)

/-- Helper: if two integral elements `r₁, r₂ ∈ 𝓞 K` agree in `v.adicCompletion K` up to
`WithZero.exp (-n)`, they are congruent modulo `v.asIdeal ^ n`. -/
private theorem quotient_mk_eq_of_valued_sub_le (v : HeightOneSpectrum (𝓞 K)) (n : ℕ)
    {r₁ r₂ : 𝓞 K}
    (h : Valued.v (algebraMap (𝓞 K) (v.adicCompletion K) r₁ -
      algebraMap (𝓞 K) (v.adicCompletion K) r₂) ≤ WithZero.exp (-(n : ℤ))) :
    Ideal.Quotient.mk (v.asIdeal ^ n) r₁ = Ideal.Quotient.mk (v.asIdeal ^ n) r₂ := by
  rw [← map_sub, valued_algebraMap_int] at h
  have hmem : r₁ - r₂ ∈ v.asIdeal ^ n :=
    (Ideal.span_singleton_le_iff_mem _).mp
      (Ideal.dvd_iff_le.mp ((HeightOneSpectrum.intValuation_le_pow_iff_dvd v (r₁ - r₂) n).mp h))
  exact Ideal.Quotient.eq.mpr hmem

private theorem add_approx_identity {A : Type*} [CommRing A] (a b c d e : A) :
    a - (b + c) = ((d - b) + (e - c)) - ((d + e) - a) := by ring

private theorem mul_approx_identity {A : Type*} [CommRing A] (a b c d e : A) :
    a - b * c = (d * (e - c) + (d - b) * c) - (d * e - a) := by ring

/-- Local reduction ring homomorphism `𝒪_v →+* 𝓞 K ⧸ v^n`, constructed via `local_approx_int`. -/
def localQuotMap (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    v.adicCompletionIntegers K →+* 𝓞 K ⧸ (v.asIdeal ^ n) where
  toFun x := Ideal.Quotient.mk (v.asIdeal ^ n) (local_approx_int v x n).choose
  map_one' := by
    have hr := (local_approx_int v (1 : v.adicCompletionIntegers K) n).choose_spec
    have h1 : (1 : v.adicCompletionIntegers K).val =
        algebraMap (𝓞 K) (v.adicCompletion K) 1 := by simp
    have hr' : Valued.v (algebraMap (𝓞 K) (v.adicCompletion K) 1 -
        algebraMap (𝓞 K) (v.adicCompletion K)
          (local_approx_int v (1 : v.adicCompletionIntegers K) n).choose) ≤
        WithZero.exp (-(n : ℤ)) := by
      rwa [← h1]
    exact (quotient_mk_eq_of_valued_sub_le v n hr').symm
  map_zero' := by
    have hr := (local_approx_int v (0 : v.adicCompletionIntegers K) n).choose_spec
    have h0 : (0 : v.adicCompletionIntegers K).val =
        algebraMap (𝓞 K) (v.adicCompletion K) 0 := by simp
    have hr' : Valued.v (algebraMap (𝓞 K) (v.adicCompletion K) 0 -
        algebraMap (𝓞 K) (v.adicCompletion K)
          (local_approx_int v (0 : v.adicCompletionIntegers K) n).choose) ≤
        WithZero.exp (-(n : ℤ)) := by
      rwa [← h0]
    exact (quotient_mk_eq_of_valued_sub_le v n hr').symm
  map_add' x y := by
    have hrx := (local_approx_int v x n).choose_spec
    have hry := (local_approx_int v y n).choose_spec
    have hrxy := (local_approx_int v (x + y) n).choose_spec
    rw [← map_add (Ideal.Quotient.mk (v.asIdeal ^ n))]
    apply quotient_mk_eq_of_valued_sub_le v n
    rw [map_add, add_approx_identity _ _ _ x.val y.val]
    exact le_trans (Valuation.map_sub _ _ _)
      (max_le (le_trans (Valuation.map_add _ _ _) (max_le hrx hry)) hrxy)
  map_mul' x y := by
    have hrx := (local_approx_int v x n).choose_spec
    have hry := (local_approx_int v y n).choose_spec
    have hrxy := (local_approx_int v (x * y) n).choose_spec
    have hx_le : Valued.v x.val ≤ 1 :=
      (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 K) K v).mp x.2
    have hry_le :
        Valued.v (algebraMap (𝓞 K) (v.adicCompletion K) (local_approx_int v y n).choose) ≤ 1 := by
      rw [valued_algebraMap_int]
      exact HeightOneSpectrum.intValuation_le_one v _
    rw [← map_mul (Ideal.Quotient.mk (v.asIdeal ^ n))]
    apply quotient_mk_eq_of_valued_sub_le v n
    rw [map_mul, mul_approx_identity _ _ _ x.val y.val]
    refine le_trans (Valuation.map_sub _ _ _) (max_le ?_ hrxy)
    refine le_trans (Valuation.map_add _ _ _) (max_le ?_ ?_)
    · rw [map_mul]
      simpa only [one_mul] using mul_le_mul' hx_le hry
    · rw [map_mul]
      simpa only [mul_one] using mul_le_mul' hrx hry_le

theorem localQuotMap_algebraMap (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) (r : 𝓞 K) :
    localQuotMap v n (algebraMap (𝓞 K) (v.adicCompletionIntegers K) r) =
      Ideal.Quotient.mk (v.asIdeal ^ n) r := by
  have hr' := (local_approx_int v (algebraMap (𝓞 K) (v.adicCompletionIntegers K) r) n).choose_spec
  have halg : (algebraMap (𝓞 K) (v.adicCompletionIntegers K) r).val =
      algebraMap (𝓞 K) (v.adicCompletion K) r := rfl
  have hr'' : Valued.v (algebraMap (𝓞 K) (v.adicCompletion K) r -
      algebraMap (𝓞 K) (v.adicCompletion K)
        (local_approx_int v (algebraMap (𝓞 K) (v.adicCompletionIntegers K) r) n).choose) ≤
      WithZero.exp (-(n : ℤ)) := by
    rwa [← halg]
  exact (quotient_mk_eq_of_valued_sub_le v n hr'').symm

theorem localQuotMap_eq_one_iff (v : HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (x : v.adicCompletionIntegers K) :
    localQuotMap v n x = 1 ↔ Valued.v (x.val - 1) ≤ WithZero.exp (-(n : ℤ)) := by
  have hr := (local_approx_int v x n).choose_spec
  set r := (local_approx_int v x n).choose with hr_def
  change Ideal.Quotient.mk (v.asIdeal ^ n) r = Ideal.Quotient.mk (v.asIdeal ^ n) 1 ↔ _
  rw [Ideal.Quotient.eq]
  constructor
  · intro hmem
    have hv : v.intValuation (r - 1) ≤ WithZero.exp (-(n : ℤ)) :=
      (HeightOneSpectrum.intValuation_le_pow_iff_dvd v (r - 1) n).mpr
        (Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hmem))
    have h2 : Valued.v (algebraMap (𝓞 K) (v.adicCompletion K) r - 1) ≤ WithZero.exp (-(n : ℤ)) := by
      rw [← map_one (algebraMap (𝓞 K) (v.adicCompletion K)), ← map_sub, valued_algebraMap_int]
      exact hv
    have hsplit : x.val - 1 = (x.val - algebraMap (𝓞 K) (v.adicCompletion K) r) +
        (algebraMap (𝓞 K) (v.adicCompletion K) r - 1) := by ring
    rw [hsplit]
    exact le_trans (Valuation.map_add _ _ _) (max_le hr h2)
  · intro hle
    have hdiff : Valued.v (algebraMap (𝓞 K) (v.adicCompletion K) (r - 1)) ≤ WithZero.exp (-(n : ℤ)) := by
      have hrew : algebraMap (𝓞 K) (v.adicCompletion K) (r - 1) =
          (x.val - 1) - (x.val - algebraMap (𝓞 K) (v.adicCompletion K) r) := by
        rw [map_sub, map_one]; ring
      rw [hrew]
      exact le_trans (Valuation.map_sub _ _ _) (max_le hle hr)
    rw [valued_algebraMap_int] at hdiff
    exact (Ideal.span_singleton_le_iff_mem _).mp
      (Ideal.dvd_iff_le.mp ((HeightOneSpectrum.intValuation_le_pow_iff_dvd v (r - 1) n).mp hdiff))

/-- Local unit reduction homomorphism `(𝒪_v)ˣ →* (𝓞 K ⧸ v^n)ˣ`. -/
def localQuotUnitsMap (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    (v.adicCompletionIntegers K)ˣ →* (𝓞 K ⧸ (v.asIdeal ^ n))ˣ :=
  Units.map (localQuotMap v n).toMonoidHom

theorem localQuotUnitsMap_surjective (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    Function.Surjective (localQuotUnitsMap v n) := by
  intro u
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨1, ?_⟩
    apply Units.ext
    have htop : v.asIdeal ^ 0 = ⊤ := by rw [pow_zero, Ideal.one_eq_top]
    obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective u.val
    rw [← hr, map_one, Units.val_one, ← map_one (Ideal.Quotient.mk _), Ideal.Quotient.eq]
    rw [htop]; trivial
  · obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective u.val
    obtain ⟨s, hs⟩ := Ideal.Quotient.mk_surjective u.inv
    have hrs : r * s - 1 ∈ v.asIdeal ^ n := by
      rw [← Ideal.Quotient.eq, map_mul, map_one, hr, hs, u.val_inv]
    have hrv : r ∉ v.asIdeal := by
      intro hmem
      have hle : v.asIdeal ^ n ≤ v.asIdeal := Ideal.pow_le_self hn.ne'
      have h1 : 1 ∈ v.asIdeal := by
        have h2 : r * s ∈ v.asIdeal := v.asIdeal.mul_mem_right s hmem
        have h3 : r * s - (r * s - 1) ∈ v.asIdeal := v.asIdeal.sub_mem h2 (hle hrs)
        simpa using h3
      exact v.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h1 isUnit_one)
    have hval1 : Valued.v (algebraMap (𝓞 K) (v.adicCompletion K) r) = 1 := by
      rw [valued_algebraMap_int, HeightOneSpectrum.intValuation_eq_one_iff]
      exact hrv
    have hr_ne : algebraMap (𝓞 K) (v.adicCompletion K) r ≠ 0 := by
      intro h0
      rw [h0, map_zero] at hval1
      exact zero_ne_one hval1
    have hinv_mem : (algebraMap (𝓞 K) (v.adicCompletion K) r)⁻¹ ∈ v.adicCompletionIntegers K := by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hval1, inv_one]
    let y : (v.adicCompletionIntegers K)ˣ :=
      { val := algebraMap (𝓞 K) (v.adicCompletionIntegers K) r
        inv := ⟨(algebraMap (𝓞 K) (v.adicCompletion K) r)⁻¹, hinv_mem⟩
        val_inv := Subtype.ext (mul_inv_cancel₀ hr_ne)
        inv_val := Subtype.ext (inv_mul_cancel₀ hr_ne) }
    refine ⟨y, ?_⟩
    apply Units.ext
    change localQuotMap v n (algebraMap (𝓞 K) (v.adicCompletionIntegers K) r) = u.val
    rw [localQuotMap_algebraMap, hr]

/-- The ray-unit congruence subgroup `U_𝔪 ≤ U_{K,f} ≤ 𝕀_{K,f}` attached to an integral ideal
`𝔪 : Ideal (𝓞 K)`: finite-idele units `u ∈ U_{K,f}` satisfying `u_v ≡ 1 (mod v^{ord_v(𝔪)})`
at every prime `v ∣ 𝔪`. -/
def rayUnitSubgroup (K : Type*) [Field K] [NumberField K] (𝔪 : Ideal (𝓞 K)) :
    Subgroup (FinIdele K) where
  carrier := {x : FinIdele K | x ∈ finUnitSubgroup K ∧
    ∀ v : HeightOneSpectrum (𝓞 K), idealOrd 𝔪 v ≠ 0 →
      Valued.v (x.val v - 1) ≤ WithZero.exp (-(idealOrd 𝔪 v : ℤ))}
  one_mem' := ⟨(finUnitSubgroup K).one_mem, fun v _ => by
    change Valued.v ((1 : FiniteAdeleRing (𝓞 K) K) v - 1) ≤ _
    rw [finAdele_one_apply, sub_self, map_zero]
    exact zero_le⟩
  mul_mem' {x y} hx hy := ⟨(finUnitSubgroup K).mul_mem hx.1 hy.1, fun v hv => by
    change Valued.v ((x.val * y.val) v - 1) ≤ _
    rw [finAdele_mul_apply]
    have hrew : x.val v * y.val v - 1 = x.val v * (y.val v - 1) + (x.val v - 1) := by ring
    rw [hrew]
    refine le_trans (Valuation.map_add _ _ _) (max_le ?_ (hx.2 v hv))
    rw [map_mul, hx.1 v, one_mul]
    exact hy.2 v hv⟩
  inv_mem' {x} hx := ⟨(finUnitSubgroup K).inv_mem hx.1, fun v hv => by
    change Valued.v (x.inv v - 1) ≤ _
    have hrew : x.inv v - 1 = -(x.inv v * (x.val v - 1)) := by
      rw [mul_sub, finIdele_apply_inv_mul, mul_one]; ring
    rw [hrew, Valuation.map_neg, map_mul]
    have hinv1 : Valued.v (x.inv v) = 1 := by
      have hmul := finIdele_val_mul_inv x v
      rw [hx.1 v, one_mul] at hmul
      exact hmul
    rw [hinv1, one_mul]
    exact hx.2 v hv⟩

theorem rayUnitSubgroup_le_finUnitSubgroup (K : Type*) [Field K] [NumberField K]
    (𝔪 : Ideal (𝓞 K)) :
    rayUnitSubgroup K 𝔪 ≤ finUnitSubgroup K :=
  fun _ hx => hx.1

/-- **Concrete Ray Class Group `Cl_𝔪(K)`** attached to a modulus `𝔪 : Ideal (𝓞 K)`:
`RayClassGroup K 𝔪 := 𝕀_{K,f} ⧸ (Kˣ · U_𝔪)`. -/
abbrev RayClassGroup (K : Type*) [Field K] [NumberField K] (𝔪 : Ideal (𝓞 K)) : Type _ :=
  FinIdele K ⧸ (principalSubgroup K ⊔ rayUnitSubgroup K 𝔪)

omit [NumberField K] in
/-- Helper: product of pairwise coprime ideals over a `Finset` equals their infimum. -/
theorem finset_prod_eq_iInf_of_pairwise_isCoprime {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → Ideal (𝓞 K))
    (hcop : Set.Pairwise (↑s : Set ι) (fun i j => IsCoprime (f i) (f j))) :
    ∏ i ∈ s, f i = ⨅ i ∈ s, f i := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a t ha ih =>
    rw [Finset.prod_insert ha, Finset.iInf_insert]
    have ht : Set.Pairwise (↑t : Set ι) (fun i j => IsCoprime (f i) (f j)) :=
      hcop.mono (Finset.coe_subset.mpr (Finset.subset_insert a t))
    rw [ih ht]
    have hca : IsCoprime (f a) (∏ i ∈ t, f i) := by
      refine IsCoprime.prod_right fun i hi => ?_
      exact hcop (Finset.mem_coe.mpr (Finset.mem_insert_self a t))
        (Finset.mem_coe.mpr (Finset.mem_insert_of_mem hi)) (fun h => ha (h ▸ hi))
    rw [← ih ht]
    exact Ideal.mul_eq_inf_of_isCoprime hca

/-- The finite set of height-one primes dividing a nonzero integral ideal `𝔪`. -/
def idealSupport (𝔪 : Ideal (𝓞 K)) (h𝔪 : 𝔪 ≠ ⊥) : Finset (HeightOneSpectrum (𝓞 K)) :=
  (idealOrd_finite_support h𝔪).toFinset

private theorem idealSupport_pairwise_coprime (𝔪 : Ideal (𝓞 K)) (h𝔪 : 𝔪 ≠ ⊥) :
    Pairwise (Function.onFun IsCoprime
      (fun v : idealSupport 𝔪 h𝔪 => v.1.asIdeal ^ idealOrd 𝔪 v.1)) := by
  intro v w hne
  have hne' : v.1.asIdeal ≠ w.1.asIdeal := fun h => hne (Subtype.ext (HeightOneSpectrum.ext h))
  have hcop1 : IsCoprime v.1.asIdeal w.1.asIdeal := by
    rw [Ideal.isCoprime_iff_sup_eq]
    exact Ideal.IsMaximal.coprime_of_ne v.1.isMaximal w.1.isMaximal hne'
  exact hcop1.pow

private theorem ideal_eq_iInf_idealSupport (𝔪 : Ideal (𝓞 K)) (h𝔪 : 𝔪 ≠ ⊥) :
    𝔪 = ⨅ v : idealSupport 𝔪 h𝔪, v.1.asIdeal ^ idealOrd 𝔪 v.1 := by
  classical
  have hpair := idealSupport_pairwise_coprime 𝔪 h𝔪
  have h1 : 𝔪 = ⨅ v ∈ idealSupport 𝔪 h𝔪, v.asIdeal ^ idealOrd 𝔪 v := by
    calc 𝔪 = ∏ v ∈ idealSupport 𝔪 h𝔪, v.asIdeal ^ idealOrd 𝔪 v := eq_prod_prime_pow_idealOrd h𝔪
      _ = ⨅ v ∈ idealSupport 𝔪 h𝔪, v.asIdeal ^ idealOrd 𝔪 v :=
          finset_prod_eq_iInf_of_pairwise_isCoprime (idealSupport 𝔪 h𝔪)
            (fun v => v.asIdeal ^ idealOrd 𝔪 v)
            (fun v hv w hw hne => hpair (i := ⟨v, hv⟩) (j := ⟨w, hw⟩)
              (fun h => hne (congrArg Subtype.val h)))
  conv_lhs => rw [h1]
  refine le_antisymm ?_ ?_
  · exact le_iInf fun v => iInf₂_le v.1 v.2
  · exact le_iInf fun v => le_iInf fun hv =>
      iInf_le (fun w : idealSupport 𝔪 h𝔪 => w.1.asIdeal ^ idealOrd 𝔪 w.1) ⟨v, hv⟩

/-- Chinese Remainder Theorem ring isomorphism
`𝓞 K ⧸ 𝔪 ≃+* ∏_{v ∣ 𝔪} (𝓞 K ⧸ v^{ord_v(𝔪)})` for any nonzero ideal `𝔪 ≠ ⊥`. -/
def crtQuotRingEquiv (𝔪 : Ideal (𝓞 K)) (h𝔪 : 𝔪 ≠ ⊥) :
    𝓞 K ⧸ 𝔪 ≃+* ((v : idealSupport 𝔪 h𝔪) → 𝓞 K ⧸ (v.1.asIdeal ^ idealOrd 𝔪 v.1)) :=
  (Ideal.quotientEquivAlgOfEq (𝓞 K) (ideal_eq_iInf_idealSupport 𝔪 h𝔪)).toRingEquiv.trans
    (Ideal.quotientInfRingEquivPiQuotient
      (fun v : idealSupport 𝔪 h𝔪 => v.1.asIdeal ^ idealOrd 𝔪 v.1)
      (idealSupport_pairwise_coprime 𝔪 h𝔪))

theorem crtQuotRingEquiv_mk (𝔪 : Ideal (𝓞 K)) (h𝔪 : 𝔪 ≠ ⊥) (r : 𝓞 K)
    (v : idealSupport 𝔪 h𝔪) :
    crtQuotRingEquiv 𝔪 h𝔪 (Ideal.Quotient.mk 𝔪 r) v =
      Ideal.Quotient.mk (v.1.asIdeal ^ idealOrd 𝔪 v.1) r := by
  simp [crtQuotRingEquiv]
  rfl

/-- Chinese Remainder Theorem unit-group isomorphism
`(𝓞 K ⧸ 𝔪)ˣ ≃* ∏_{v ∣ 𝔪} (𝓞 K ⧸ v^{ord_v(𝔪)})ˣ`. -/
def crtQuotUnitsEquiv (𝔪 : Ideal (𝓞 K)) (h𝔪 : 𝔪 ≠ ⊥) :
    (𝓞 K ⧸ 𝔪)ˣ ≃* ((v : idealSupport 𝔪 h𝔪) → (𝓞 K ⧸ (v.1.asIdeal ^ idealOrd 𝔪 v.1))ˣ) :=
  (Units.mapEquiv (crtQuotRingEquiv 𝔪 h𝔪).toMulEquiv).trans MulEquiv.piUnits

/-- Canonical surjective reduction homomorphism `U_{K,f} →* (𝓞 K ⧸ 𝔪)ˣ` for any nonzero ideal
`𝔪 ≠ ⊥`. -/
def finUnitToQuotUnits {𝔪 : Ideal (𝓞 K)} (h𝔪 : 𝔪 ≠ ⊥) :
    finUnitSubgroup K →* (𝓞 K ⧸ 𝔪)ˣ where
  toFun u := (crtQuotUnitsEquiv 𝔪 h𝔪).symm (fun v =>
    localQuotUnitsMap v.1 (idealOrd 𝔪 v.1) (finUnitAt u v.1))
  map_one' := by
    apply (crtQuotUnitsEquiv 𝔪 h𝔪).injective
    rw [MulEquiv.apply_symm_apply, map_one]
    funext v
    have h1 : finUnitAt (1 : finUnitSubgroup K) v.1 = 1 :=
      congrFun (map_one (finUnitSubgroupEquivProdUnits K)) v.1
    rw [h1, map_one]
    rfl
  map_mul' u₁ u₂ := by
    apply (crtQuotUnitsEquiv 𝔪 h𝔪).injective
    rw [map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
    funext v
    have hm : finUnitAt (u₁ * u₂) v.1 = finUnitAt u₁ v.1 * finUnitAt u₂ v.1 := rfl
    rw [hm, map_mul]
    rfl

/-- **Surjectivity of `finUnitToQuotUnits`**: `U_{K,f} →* (𝓞 K ⧸ 𝔪)ˣ` is surjective. -/
theorem finUnitToQuotUnits_surjective {𝔪 : Ideal (𝓞 K)} (h𝔪 : 𝔪 ≠ ⊥) :
    Function.Surjective (finUnitToQuotUnits h𝔪) := by
  classical
  intro w
  set S := idealSupport 𝔪 h𝔪
  set f := crtQuotUnitsEquiv 𝔪 h𝔪 w
  choose y hy using fun v : S => localQuotUnitsMap_surjective v.1 (idealOrd 𝔪 v.1) (f v)
  let g : (v : HeightOneSpectrum (𝓞 K)) → (v.adicCompletionIntegers K)ˣ :=
    fun v => if hv : v ∈ S then y ⟨v, hv⟩ else 1
  set u : finUnitSubgroup K := (finUnitSubgroupEquivProdUnits K).symm g
  refine ⟨u, ?_⟩
  apply (crtQuotUnitsEquiv 𝔪 h𝔪).injective
  change (crtQuotUnitsEquiv 𝔪 h𝔪) ((crtQuotUnitsEquiv 𝔪 h𝔪).symm _) = f
  rw [MulEquiv.apply_symm_apply]
  funext v
  have hu : finUnitAt u v.1 = g v.1 :=
    congrFun ((finUnitSubgroupEquivProdUnits K).apply_symm_apply g) v.1
  rw [hu]
  change localQuotUnitsMap v.1 (idealOrd 𝔪 v.1) (if hv : v.1 ∈ S then y ⟨v.1, hv⟩ else 1) = f v
  rw [dif_pos v.2]
  exact hy v

/-- **Exact Kernel of `finUnitToQuotUnits`**: `ker(U_{K,f} →* (𝓞 K ⧸ 𝔪)ˣ) = U_𝔪`. -/
theorem finUnitToQuotUnits_ker {𝔪 : Ideal (𝓞 K)} (h𝔪 : 𝔪 ≠ ⊥) :
    (finUnitToQuotUnits h𝔪).ker = (rayUnitSubgroup K 𝔪).subgroupOf (finUnitSubgroup K) := by
  ext u
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  change (crtQuotUnitsEquiv 𝔪 h𝔪).symm _ = 1 ↔ u.1 ∈ rayUnitSubgroup K 𝔪
  rw [MulEquiv.symm_apply_eq, map_one]
  constructor
  · intro h
    refine ⟨u.2, fun v hv => ?_⟩
    have hvS : v ∈ (idealOrd_finite_support h𝔪).toFinset :=
      (Set.Finite.mem_toFinset _).mpr hv
    have h1 := congrFun h ⟨v, hvS⟩
    have hval : localQuotMap v (idealOrd 𝔪 v) (finUnitAt u v).val = 1 :=
      congrArg Units.val h1
    exact (localQuotMap_eq_one_iff v (idealOrd 𝔪 v) (finUnitAt u v).val).mp hval
  · intro hu
    funext v
    apply Units.ext
    have hv : idealOrd 𝔪 v.1 ≠ 0 := (Set.Finite.mem_toFinset _).mp v.2
    exact (localQuotMap_eq_one_iff v.1 (idealOrd 𝔪 v.1) (finUnitAt u v.1).val).mpr (hu.2 v.1 hv)

/-- **Exact Congruence-Unit Quotient Isomorphism**: `U_{K,f} ⧸ U_𝔪 ≃* (𝓞 K ⧸ 𝔪)ˣ`. -/
def finUnitQuotEquivQuotUnits {𝔪 : Ideal (𝓞 K)} (h𝔪 : 𝔪 ≠ ⊥) :
    finUnitSubgroup K ⧸ (rayUnitSubgroup K 𝔪).subgroupOf (finUnitSubgroup K) ≃* (𝓞 K ⧸ 𝔪)ˣ :=
  (QuotientGroup.quotientMulEquivOfEq (finUnitToQuotUnits_ker h𝔪).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (finUnitToQuotUnits h𝔪)
      (finUnitToQuotUnits_surjective h𝔪))

/-- The canonical global-unit reduction homomorphism `(𝓞 K)ˣ →* (𝓞 K ⧸ 𝔪)ˣ`. -/
def globalUnitsToQuotUnits (𝔪 : Ideal (𝓞 K)) : (𝓞 K)ˣ →* (𝓞 K ⧸ 𝔪)ˣ :=
  Units.map (Ideal.Quotient.mk 𝔪).toMonoidHom

/-- **Compatibility of `finUnitToQuotUnits` with global units `(𝓞 K)ˣ`**:
reducing a global unit via `U_{K,f} → (𝓞 K ⧸ 𝔪)ˣ` agrees identically with `(𝓞 K)ˣ → (𝓞 K ⧸ 𝔪)ˣ`. -/
theorem finUnitToQuotUnits_comp_intUnits {𝔪 : Ideal (𝓞 K)} (h𝔪 : 𝔪 ≠ ⊥) :
    (finUnitToQuotUnits h𝔪).comp (intUnitsToFinUnits K) = globalUnitsToQuotUnits 𝔪 := by
  apply MonoidHom.ext
  intro ε
  apply (crtQuotUnitsEquiv 𝔪 h𝔪).injective
  rw [MonoidHom.comp_apply]
  have hL : crtQuotUnitsEquiv 𝔪 h𝔪 (finUnitToQuotUnits h𝔪 (intUnitsToFinUnits K ε)) =
      fun v : idealSupport 𝔪 h𝔪 =>
        localQuotUnitsMap v.1 (idealOrd 𝔪 v.1) (finUnitAt (intUnitsToFinUnits K ε) v.1) :=
    (crtQuotUnitsEquiv 𝔪 h𝔪).apply_symm_apply _
  rw [hL]
  funext v
  apply Units.ext
  have hrhs : ((crtQuotUnitsEquiv 𝔪 h𝔪 (globalUnitsToQuotUnits 𝔪 ε)) v).val =
      Ideal.Quotient.mk (v.1.asIdeal ^ idealOrd 𝔪 v.1) ε.val :=
    crtQuotRingEquiv_mk 𝔪 h𝔪 ε.val v
  rw [hrhs]
  change localQuotMap v.1 (idealOrd 𝔪 v.1) (finUnitAt (intUnitsToFinUnits K ε) v.1).val =
    Ideal.Quotient.mk (v.1.asIdeal ^ idealOrd 𝔪 v.1) ε.val
  have heq : (finUnitAt (intUnitsToFinUnits K ε) v.1).val =
      algebraMap (𝓞 K) (v.1.adicCompletionIntegers K) ε.val :=
    Subtype.ext (finAdele_algebraMap_int_apply ε.val v.1)
  rw [heq, localQuotMap_algebraMap]

/-- The canonical surjective projection `RayClassGroup K 𝔪 →* ClassGroup (𝓞 K)`. -/
def rayToClassGroup (K : Type*) [Field K] [NumberField K] (𝔪 : Ideal (𝓞 K)) :
    RayClassGroup K 𝔪 →* ClassGroup (𝓞 K) :=
  QuotientGroup.lift (principalSubgroup K ⊔ rayUnitSubgroup K 𝔪) (ideleToClassGroup K) (by
    rw [ideleToClassGroup_ker]
    exact sup_le_sup_left (rayUnitSubgroup_le_finUnitSubgroup K 𝔪) _)

theorem rayToClassGroup_surjective (K : Type*) [Field K] [NumberField K] (𝔪 : Ideal (𝓞 K)) :
    Function.Surjective (rayToClassGroup K 𝔪) := by
  intro c
  obtain ⟨x, rfl⟩ := ideleToClassGroup_surjective K c
  exact ⟨QuotientGroup.mk x, rfl⟩

/-- Helper homomorphism `U_{K,f} →* RayClassGroup K 𝔪` sending `u ↦ [u]`. -/
def finUnitToRayClass (K : Type*) [Field K] [NumberField K] (𝔪 : Ideal (𝓞 K)) :
    finUnitSubgroup K →* RayClassGroup K 𝔪 :=
  (QuotientGroup.mk' (principalSubgroup K ⊔ rayUnitSubgroup K 𝔪)).comp (finUnitSubgroup K).subtype

/-- The canonical map `(𝓞 K ⧸ 𝔪)ˣ →* RayClassGroup K 𝔪` in the ray-class exact sequence. -/
def quotUnitsToRayClass {𝔪 : Ideal (𝓞 K)} (h𝔪 : 𝔪 ≠ ⊥) :
    (𝓞 K ⧸ 𝔪)ˣ →* RayClassGroup K 𝔪 :=
  (QuotientGroup.lift ((rayUnitSubgroup K 𝔪).subgroupOf (finUnitSubgroup K))
    (finUnitToRayClass K 𝔪) (by
      intro u hu
      rw [MonoidHom.mem_ker]
      change (QuotientGroup.mk u.1 : RayClassGroup K 𝔪) = 1
      rw [QuotientGroup.eq_one_iff]
      exact Subgroup.mem_sup_right hu)).comp (finUnitQuotEquivQuotUnits h𝔪).symm.toMonoidHom

theorem quotUnitsToRayClass_finUnitToQuotUnits {𝔪 : Ideal (𝓞 K)} (h𝔪 : 𝔪 ≠ ⊥)
    (u : finUnitSubgroup K) :
    quotUnitsToRayClass h𝔪 (finUnitToQuotUnits h𝔪 u) =
      QuotientGroup.mk' (principalSubgroup K ⊔ rayUnitSubgroup K 𝔪) u.1 := by
  have h1 : (finUnitQuotEquivQuotUnits h𝔪).symm (finUnitToQuotUnits h𝔪 u) =
      QuotientGroup.mk u := by
    apply (finUnitQuotEquivQuotUnits h𝔪).injective
    rw [MulEquiv.apply_symm_apply]
    rfl
  unfold quotUnitsToRayClass
  rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, h1, QuotientGroup.lift_mk]
  rfl

/-- **Exactness at `(𝓞 K ⧸ 𝔪)ˣ`**:
`ker((𝓞 K ⧸ 𝔪)ˣ →* RayClassGroup K 𝔪) = im((𝓞 K)ˣ →* (𝓞 K ⧸ 𝔪)ˣ)`. -/
theorem quotUnitsToRayClass_ker {𝔪 : Ideal (𝓞 K)} (h𝔪 : 𝔪 ≠ ⊥) :
    (quotUnitsToRayClass h𝔪).ker = (globalUnitsToQuotUnits 𝔪).range := by
  ext w
  obtain ⟨u, rfl⟩ := finUnitToQuotUnits_surjective h𝔪 w
  rw [MonoidHom.mem_ker, quotUnitsToRayClass_finUnitToQuotUnits]
  change (QuotientGroup.mk u.1 : RayClassGroup K 𝔪) = 1 ↔ _
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_sup]
  constructor
  · rintro ⟨p, ⟨k, rfl⟩, r, hr, hpr⟩
    have hk_unit : diagFinIdele K k ∈ finUnitSubgroup K := by
      have heq : diagFinIdele K k = u.1 * r⁻¹ := by rw [← hpr, mul_inv_cancel_right]
      rw [heq]
      exact (finUnitSubgroup K).mul_mem u.2 ((finUnitSubgroup K).inv_mem hr.1)
    obtain ⟨ε, hε⟩ := (diagFinIdele_mem_finUnitSubgroup_iff k).mp hk_unit
    refine ⟨ε, ?_⟩
    rw [← finUnitToQuotUnits_comp_intUnits h𝔪, MonoidHom.comp_apply]
    have hdiff : (intUnitsToFinUnits K ε)⁻¹ * u ∈ (finUnitToQuotUnits h𝔪).ker := by
      rw [finUnitToQuotUnits_ker h𝔪, Subgroup.mem_subgroupOf]
      have hval : ((intUnitsToFinUnits K ε)⁻¹ * u).1 = r := by
        change (diagFinIdele K (intUnitsToFieldUnits K ε))⁻¹ * u.1 = r
        rw [hε, ← hpr, inv_mul_cancel_left]
      rw [hval]
      exact hr
    rw [MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one] at hdiff
    exact hdiff
  · rintro ⟨ε, hε⟩
    rw [← finUnitToQuotUnits_comp_intUnits h𝔪, MonoidHom.comp_apply] at hε
    have hker : (intUnitsToFinUnits K ε)⁻¹ * u ∈ (finUnitToQuotUnits h𝔪).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hε, inv_mul_cancel]
    rw [finUnitToQuotUnits_ker h𝔪, Subgroup.mem_subgroupOf] at hker
    refine ⟨(intUnitsToFinUnits K ε).1, ⟨intUnitsToFieldUnits K ε, rfl⟩,
      ((intUnitsToFinUnits K ε)⁻¹ * u).1, hker, ?_⟩
    change (intUnitsToFinUnits K ε).1 * ((intUnitsToFinUnits K ε).1⁻¹ * u.1) = u.1
    rw [mul_inv_cancel_left]

/-- **Exactness at `RayClassGroup K 𝔪`**:
`ker(RayClassGroup K 𝔪 →* ClassGroup (𝓞 K)) = im((𝓞 K ⧸ 𝔪)ˣ →* RayClassGroup K 𝔪)`. -/
theorem rayToClassGroup_ker {𝔪 : Ideal (𝓞 K)} (h𝔪 : 𝔪 ≠ ⊥) :
    (rayToClassGroup K 𝔪).ker = (quotUnitsToRayClass h𝔪).range := by
  ext c
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (principalSubgroup K ⊔ rayUnitSubgroup K 𝔪) c
  rw [MonoidHom.mem_ker]
  change ideleToClassGroup K x = 1 ↔ _
  rw [← MonoidHom.mem_ker, ideleToClassGroup_ker, Subgroup.mem_sup]
  constructor
  · rintro ⟨p, hp, u, hu, rfl⟩
    refine ⟨finUnitToQuotUnits h𝔪 ⟨u, hu⟩, ?_⟩
    rw [quotUnitsToRayClass_finUnitToQuotUnits]
    apply (QuotientGroup.eq).mpr
    have heq : u⁻¹ * (p * u) = p := by
      rw [mul_comm p u, inv_mul_cancel_left]
    rw [heq]
    exact Subgroup.mem_sup_left hp
  · rintro ⟨w, hw⟩
    obtain ⟨u, rfl⟩ := finUnitToQuotUnits_surjective h𝔪 w
    rw [quotUnitsToRayClass_finUnitToQuotUnits] at hw
    have hmem : u.1⁻¹ * x ∈ principalSubgroup K ⊔ rayUnitSubgroup K 𝔪 :=
      QuotientGroup.eq.mp hw
    obtain ⟨p, hp, r, hr, hpr⟩ := Subgroup.mem_sup.mp hmem
    refine ⟨p, hp, u.1 * r, (finUnitSubgroup K).mul_mem u.2 hr.1, ?_⟩
    have hx : x = u.1 * (p * r) := by
      rw [hpr, mul_inv_cancel_left]
    rw [hx, mul_left_comm]

/-- Canonical isomorphism `(𝓞 K ⧸ 𝔪)ˣ ⧸ im((𝓞 K)ˣ) ≃* ker(RayClassGroup K 𝔪 →* ClassGroup (𝓞 K))`. -/
def quotUnitsModGlobalUnitsEquivRayKer {𝔪 : Ideal (𝓞 K)} (h𝔪 : 𝔪 ≠ ⊥) :
    (𝓞 K ⧸ 𝔪)ˣ ⧸ (globalUnitsToQuotUnits 𝔪).range ≃* (rayToClassGroup K 𝔪).ker :=
  (QuotientGroup.quotientMulEquivOfEq (quotUnitsToRayClass_ker h𝔪).symm).trans
    ((QuotientGroup.quotientKerEquivRange (quotUnitsToRayClass h𝔪)).trans
      (MulEquiv.subgroupCongr (rayToClassGroup_ker h𝔪).symm))

/-- Canonical isomorphism `RayClassGroup K 𝔪 ⧸ ker(rayToClassGroup) ≃* ClassGroup (𝓞 K)`. -/
def rayModKerEquivClassGroup (K : Type*) [Field K] [NumberField K] (𝔪 : Ideal (𝓞 K)) :
    RayClassGroup K 𝔪 ⧸ (rayToClassGroup K 𝔪).ker ≃* ClassGroup (𝓞 K) :=
  QuotientGroup.quotientKerEquivOfSurjective (rayToClassGroup K 𝔪)
    (rayToClassGroup_surjective K 𝔪)

/-- **Unconditional Finiteness of `(𝓞 K ⧸ 𝔪)ˣ`** for every nonzero ideal `𝔪 ≠ ⊥`. -/
theorem finite_quotUnits {𝔪 : Ideal (𝓞 K)} (h𝔪 : 𝔪 ≠ ⊥) : Finite (𝓞 K ⧸ 𝔪)ˣ := by
  have : Finite (𝓞 K ⧸ 𝔪) := Ideal.finiteQuotientOfFreeOfNeBot 𝔪 h𝔪
  exact Finite.of_injective Units.val Units.val_injective

/-- **Unconditional Finiteness of the Ray Class Group `Cl_𝔪(K)`** for every nonzero modulus
`𝔪 : Ideal (𝓞 K)`. -/
theorem finite_rayClassGroup (K : Type*) [Field K] [NumberField K] {𝔪 : Ideal (𝓞 K)}
    (h𝔪 : 𝔪 ≠ ⊥) :
    Finite (RayClassGroup K 𝔪) := by
  have : Finite (𝓞 K ⧸ 𝔪)ˣ := finite_quotUnits h𝔪
  have : Finite ((𝓞 K ⧸ 𝔪)ˣ ⧸ (globalUnitsToQuotUnits 𝔪).range) := Quotient.finite _
  have : Finite (rayToClassGroup K 𝔪).ker :=
    Finite.of_equiv _ (quotUnitsModGlobalUnitsEquivRayKer h𝔪).toEquiv
  have : Finite (RayClassGroup K 𝔪 ⧸ (rayToClassGroup K 𝔪).ker) :=
    Finite.of_equiv (ClassGroup (𝓞 K)) (rayModKerEquivClassGroup K 𝔪).symm.toEquiv
  have hbij := Subgroup.groupEquivQuotientProdSubgroup (s := (rayToClassGroup K 𝔪).ker)
  exact Finite.of_equiv _ hbij.symm

/-- **Exact Ray-Class Cardinality Identity**:
`|Cl_𝔪(K)| · |im((𝓞 K)ˣ → (𝓞 K ⧸ 𝔪)ˣ)| = |(𝓞 K ⧸ 𝔪)ˣ| · |Cl(K)|`. -/
theorem card_rayClassGroup_mul_card_imgUnits (K : Type*) [Field K] [NumberField K]
    {𝔪 : Ideal (𝓞 K)} (h𝔪 : 𝔪 ≠ ⊥) :
    Nat.card (RayClassGroup K 𝔪) * Nat.card (globalUnitsToQuotUnits 𝔪).range =
      Nat.card (𝓞 K ⧸ 𝔪)ˣ * Nat.card (ClassGroup (𝓞 K)) := by
  have h1 : Nat.card (rayToClassGroup K 𝔪).ker * Nat.card (ClassGroup (𝓞 K)) =
      Nat.card (RayClassGroup K 𝔪) := by
    have hlag := Subgroup.card_mul_index (rayToClassGroup K 𝔪).ker
    rw [Subgroup.index_eq_card, Nat.card_congr (rayModKerEquivClassGroup K 𝔪).toEquiv] at hlag
    exact hlag
  have h2 : Nat.card (globalUnitsToQuotUnits 𝔪).range * Nat.card (rayToClassGroup K 𝔪).ker =
      Nat.card (𝓞 K ⧸ 𝔪)ˣ := by
    have hlag := Subgroup.card_mul_index (globalUnitsToQuotUnits 𝔪).range
    rw [Subgroup.index_eq_card,
      Nat.card_congr (quotUnitsModGlobalUnitsEquivRayKer h𝔪).toEquiv] at hlag
    exact hlag
  calc Nat.card (RayClassGroup K 𝔪) * Nat.card (globalUnitsToQuotUnits 𝔪).range
      = (Nat.card (rayToClassGroup K 𝔪).ker * Nat.card (ClassGroup (𝓞 K))) *
          Nat.card (globalUnitsToQuotUnits 𝔪).range := by rw [← h1]
    _ = (Nat.card (globalUnitsToQuotUnits 𝔪).range * Nat.card (rayToClassGroup K 𝔪).ker) *
          Nat.card (ClassGroup (𝓞 K)) := by ring
    _ = Nat.card (𝓞 K ⧸ 𝔪)ˣ * Nat.card (ClassGroup (𝓞 K)) := by rw [h2]

/-- **Explicit Upper Bound on the Ray Class Number**:
`|Cl_𝔪(K)| ≤ |(𝓞 K ⧸ 𝔪)ˣ| · h_K`. -/
theorem card_rayClassGroup_le (K : Type*) [Field K] [NumberField K]
    {𝔪 : Ideal (𝓞 K)} (h𝔪 : 𝔪 ≠ ⊥) :
    Nat.card (RayClassGroup K 𝔪) ≤ Nat.card (𝓞 K ⧸ 𝔪)ˣ * NumberField.classNumber K := by
  have : Finite (𝓞 K ⧸ 𝔪)ˣ := finite_quotUnits h𝔪
  have hpos : 0 < Nat.card (globalUnitsToQuotUnits 𝔪).range := Nat.card_pos
  have h := card_rayClassGroup_mul_card_imgUnits K h𝔪
  rw [Nat.card_eq_fintype_card (α := ClassGroup (𝓞 K))] at h
  change Nat.card (RayClassGroup K 𝔪) * Nat.card (globalUnitsToQuotUnits 𝔪).range =
    Nat.card (𝓞 K ⧸ 𝔪)ˣ * NumberField.classNumber K at h
  calc Nat.card (RayClassGroup K 𝔪)
      = Nat.card (RayClassGroup K 𝔪) * 1 := (mul_one _).symm
    _ ≤ Nat.card (RayClassGroup K 𝔪) * Nat.card (globalUnitsToQuotUnits 𝔪).range :=
        Nat.mul_le_mul_left _ hpos
    _ = Nat.card (𝓞 K ⧸ 𝔪)ˣ * NumberField.classNumber K := h

end RayClassGroups

/-! ## Section 3: Strong Approximation for `𝕀_ℚ` & Exact Idelic Hecke ↔ Dirichlet ↔ Galois Triangle -/

section RationalIdeles

/-- The full idele group `𝕀_ℚ = ℝˣ × 𝕀_{ℚ,f}` of `ℚ`. -/
abbrev RatIdele : Type := ℝˣ × FinIdele ℚ

/-- Diagonal principal embedding `ℚˣ →* 𝕀_ℚ`, sending `q ↦ (q_∞, diag(q)_f)`. -/
def diagRatIdele : ℚˣ →* RatIdele where
  toFun q := (Units.map (Rat.castHom ℝ).toMonoidHom q, diagFinIdele ℚ q)
  map_one' := by simp
  map_mul' q₁ q₂ := by simp

/-- The principal idele subgroup `ℚˣ ↪ 𝕀_ℚ`. -/
def ratPrincipalSubgroup : Subgroup RatIdele :=
  diagRatIdele.range

/-- The connected archimedean component `ℝ_{>0} ≤ ℝˣ`. -/
def posRealSubgroup : Subgroup ℝˣ where
  carrier := {y : ℝˣ | (0 : ℝ) < (y : ℝ)}
  one_mem' := by change (0 : ℝ) < (1 : ℝ); exact zero_lt_one
  mul_mem' {a b} ha hb := by
    change (0 : ℝ) < ((a * b : ℝˣ) : ℝ)
    rw [Units.val_mul]
    exact mul_pos ha hb
  inv_mem' {a} ha := by
    change (0 : ℝ) < ((a⁻¹ : ℝˣ) : ℝ)
    rw [Units.val_inv_eq_inv_val]
    exact inv_pos.mpr ha

theorem mem_posRealSubgroup_iff {y : ℝˣ} : y ∈ posRealSubgroup ↔ (0 : ℝ) < (y : ℝ) := Iff.rfl

/-- The full unit-positive subgroup `ℝ_{>0} × U_{ℚ,f} ≤ 𝕀_ℚ`. -/
def ratUnitSubgroup : Subgroup RatIdele :=
  posRealSubgroup.prod (finUnitSubgroup ℚ)

/-- The integral modulus ideal `(m) ⊆ 𝓞 ℚ` for `m : ℕ`. -/
def ratModIdeal (m : ℕ) : Ideal (𝓞 ℚ) :=
  Ideal.span {(m : 𝓞 ℚ)}

theorem ratModIdeal_ne_bot (m : ℕ) [NeZero m] : ratModIdeal m ≠ ⊥ := by
  unfold ratModIdeal
  rw [ne_eq, Ideal.span_singleton_eq_bot]
  exact Nat.cast_ne_zero.mpr (NeZero.ne m)

/-- The congruence subgroup `ℝ_{>0} × U_m ≤ 𝕀_ℚ` of level `m`. -/
def ratCongruenceSubgroup (m : ℕ) : Subgroup RatIdele :=
  posRealSubgroup.prod (rayUnitSubgroup ℚ (ratModIdeal m))

/-- `𝓞 ℚ` is a principal ideal domain (via `Rat.ringOfIntegersEquiv : 𝓞 ℚ ≃+* ℤ`). -/
instance ratRingOfIntegers_isPrincipalIdealRing : IsPrincipalIdealRing (𝓞 ℚ) where
  principal I := by
    have hZ : (Ideal.map Rat.ringOfIntegersEquiv.toRingHom I).IsPrincipal :=
      IsPrincipalIdealRing.principal _
    obtain ⟨a, ha⟩ := hZ
    have ha' : Ideal.map Rat.ringOfIntegersEquiv.toRingHom I = Ideal.span {a} := ha
    refine ⟨⟨Rat.ringOfIntegersEquiv.symm a, ?_⟩⟩
    ext x
    change x ∈ I ↔ x ∈ Ideal.span {Rat.ringOfIntegersEquiv.symm a}
    constructor
    · intro hx
      have hx' : Rat.ringOfIntegersEquiv x ∈ Ideal.span {a} := by
        rw [← ha']
        exact Ideal.mem_map_of_mem _ hx
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hx'
      apply Ideal.mem_span_singleton.mpr
      refine ⟨Rat.ringOfIntegersEquiv.symm c, ?_⟩
      apply Rat.ringOfIntegersEquiv.injective
      rw [map_mul, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
      exact hc
    · intro hx
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.mp hx
      have hmem : a ∈ Ideal.map Rat.ringOfIntegersEquiv.toRingHom I := by
        rw [ha']
        exact Ideal.subset_span (Set.mem_singleton a)
      have hcomp_id :
          Rat.ringOfIntegersEquiv.symm.toRingHom.comp Rat.ringOfIntegersEquiv.toRingHom =
            RingHom.id (𝓞 ℚ) :=
        RingHom.ext fun y => Rat.ringOfIntegersEquiv.symm_apply_apply y
      have hsymm : Rat.ringOfIntegersEquiv.symm a ∈ I := by
        have h1 : Ideal.comap Rat.ringOfIntegersEquiv.toRingHom
            (Ideal.map Rat.ringOfIntegersEquiv.toRingHom I) = I := by
          ext y
          simp only [Ideal.mem_comap]
          constructor
          · intro hy
            have hy2 : Rat.ringOfIntegersEquiv.symm (Rat.ringOfIntegersEquiv y) ∈
                Ideal.map Rat.ringOfIntegersEquiv.symm.toRingHom
                  (Ideal.map Rat.ringOfIntegersEquiv.toRingHom I) :=
              Ideal.mem_map_of_mem _ hy
            rw [Ideal.map_map, hcomp_id, Ideal.map_id, RingEquiv.symm_apply_apply] at hy2
            exact hy2
          · exact Ideal.mem_map_of_mem _
        rw [← h1, Ideal.mem_comap]
        change Rat.ringOfIntegersEquiv (Rat.ringOfIntegersEquiv.symm a) ∈ _
        rw [RingEquiv.apply_symm_apply]
        exact hmem
      exact I.mul_mem_right c hsymm

/-- `ClassGroup (𝓞 ℚ)` is trivial (`h_ℚ = 1`). -/
theorem classGroup_rat_eq_one (c : ClassGroup (𝓞 ℚ)) : c = 1 := by
  obtain ⟨J, rfl⟩ := (ideleToClassGroup_surjective ℚ) c
  obtain ⟨a, I, _, hJ⟩ := FractionalIdeal.exists_eq_spanSingleton_mul (ideleToFractionalIdeal ℚ J).val
  obtain ⟨b, hb⟩ := IsPrincipalIdealRing.principal I
  have hb' : I = Ideal.span {b} := hb
  have hfrac : (ideleToFractionalIdeal ℚ J).val =
      FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 ℚ))
        ((algebraMap (𝓞 ℚ) ℚ a)⁻¹ * algebraMap (𝓞 ℚ) ℚ b) := by
    rw [hJ, hb', FractionalIdeal.coeIdeal_span_singleton,
      FractionalIdeal.spanSingleton_mul_spanSingleton]
  have hprin : Submodule.IsPrincipal ((ideleToFractionalIdeal ℚ J).val : Submodule (𝓞 ℚ) ℚ) := by
    refine ⟨(algebraMap (𝓞 ℚ) ℚ a)⁻¹ * algebraMap (𝓞 ℚ) ℚ b, ?_⟩
    rw [← FractionalIdeal.coe_spanSingleton (nonZeroDivisors (𝓞 ℚ))]
    exact congrArg (fun F : FractionalIdeal (nonZeroDivisors (𝓞 ℚ)) ℚ => (F : Submodule (𝓞 ℚ) ℚ))
      hfrac
  exact (ClassGroup.mk_eq_one_iff (R := 𝓞 ℚ) (K := ℚ)).mpr hprin

/-- `FinIdele ℚ = P_ℚ · U_{ℚ,f}` (since `h_ℚ = 1`). -/
theorem rat_finIdele_eq_principal_sup_units :
    principalSubgroup ℚ ⊔ finUnitSubgroup ℚ = ⊤ := by
  rw [← ideleToClassGroup_ker ℚ]
  ext x
  simp only [MonoidHom.mem_ker, Subgroup.mem_top, iff_true]
  exact classGroup_rat_eq_one _

/-- Every global unit of `𝓞 ℚ` is `±1`. -/
theorem ratRingOfIntegers_units_eq_one_or_neg_one (ε : (𝓞 ℚ)ˣ) : ε = 1 ∨ ε = -1 := by
  have h := Int.units_eq_one_or (Units.map Rat.ringOfIntegersEquiv.toMonoidHom ε)
  rcases h with h1 | hneg
  · left
    apply Units.ext
    apply Rat.ringOfIntegersEquiv.injective
    simpa using congrArg Units.val h1
  · right
    apply Units.ext
    apply Rat.ringOfIntegersEquiv.injective
    simpa using congrArg Units.val hneg

private theorem diagRatIdele_fst_val (q : ℚˣ) : ((diagRatIdele q).1 : ℝ) = (q : ℚ) := rfl

/-- **Strong Approximation for `𝕀_ℚ`**: `𝕀_ℚ = ℚˣ · (ℝ_{>0} × U_{ℚ,f})`. -/
theorem ratIdele_strong_approximation :
    ratPrincipalSubgroup ⊔ ratUnitSubgroup = ⊤ := by
  ext ⟨xInf, xf⟩
  simp only [Subgroup.mem_top, iff_true]
  have hxf : xf ∈ principalSubgroup ℚ ⊔ finUnitSubgroup ℚ := by
    rw [rat_finIdele_eq_principal_sup_units]
    trivial
  obtain ⟨p, ⟨q, rfl⟩, u, hu, hqu⟩ := Subgroup.mem_sup.mp hxf
  set r : ℝ := (xInf : ℝ) * ((q : ℚ) : ℝ)⁻¹
  have hqR : ((q : ℚ) : ℝ) ≠ 0 := Rat.cast_ne_zero.mpr q.ne_zero
  have hr_ne : r ≠ 0 := mul_ne_zero xInf.ne_zero (inv_ne_zero hqR)
  rcases lt_or_gt_of_ne hr_ne with hr_neg | hr_pos
  · refine Subgroup.mem_sup.mpr ⟨diagRatIdele (-q), ⟨-q, rfl⟩,
      (Units.mk0 (-r) (neg_pos.mpr hr_neg).ne', diagFinIdele ℚ (-1) * u), ?_, ?_⟩
    · refine ⟨neg_pos.mpr hr_neg, (finUnitSubgroup ℚ).mul_mem ?_ hu⟩
      exact (diagFinIdele_mem_finUnitSubgroup_iff (-1)).mpr
        ⟨-1, by apply Units.ext; simp [intUnitsToFieldUnits]⟩
    · apply Prod.ext
      · apply Units.ext
        rw [Prod.fst_mul, Units.val_mul, diagRatIdele_fst_val, Units.val_neg, Rat.cast_neg,
          Units.val_mk0]
        dsimp only [r]
        field_simp [hqR]
      · change diagFinIdele ℚ (-q) * (diagFinIdele ℚ (-1) * u) = xf
        have hnegq : (-q : ℚˣ) = q * (-1 : ℚˣ) := by apply Units.ext; simp
        rw [hnegq, map_mul, mul_assoc, ← mul_assoc (diagFinIdele ℚ (-1)), ← map_mul,
          show (-1 : ℚˣ) * (-1 : ℚˣ) = 1 by apply Units.ext; simp, map_one, one_mul, hqu]
  · refine Subgroup.mem_sup.mpr ⟨diagRatIdele q, ⟨q, rfl⟩, (Units.mk0 r hr_pos.ne', u),
      ⟨hr_pos, hu⟩, ?_⟩
    apply Prod.ext
    · apply Units.ext
      rw [Prod.fst_mul, Units.val_mul, diagRatIdele_fst_val, Units.val_mk0]
      dsimp only [r]
      field_simp [hqR]
    · exact hqu

/-- **Disjointness in Strong Approximation**: `ℚˣ ∩ (ℝ_{>0} × U_{ℚ,f}) = {1}`. -/
theorem ratPrincipal_inf_ratUnit :
    ratPrincipalSubgroup ⊓ ratUnitSubgroup = ⊥ := by
  ext x
  rw [Subgroup.mem_inf, Subgroup.mem_bot]
  constructor
  · rintro ⟨⟨q, rfl⟩, hpos, hunit⟩
    obtain ⟨ε, hε⟩ := (diagFinIdele_mem_finUnitSubgroup_iff q).mp hunit
    rcases ratRingOfIntegers_units_eq_one_or_neg_one ε with rfl | rfl
    · have hq1 : q = 1 := by rw [← hε]; exact map_one _
      rw [hq1, map_one]
    · have hqneg : q = -1 := by
        rw [← hε]
        apply Units.ext
        simp [intUnitsToFieldUnits]
      rw [hqneg] at hpos
      have hpos' : (0 : ℝ) < ((diagRatIdele (-1)).1 : ℝ) := hpos
      change (0 : ℝ) < ((-1 : ℚ) : ℝ) at hpos'
      norm_num at hpos'
  · rintro rfl
    exact ⟨ratPrincipalSubgroup.one_mem, ratUnitSubgroup.one_mem⟩

/-- **Exact Direct-Product Decomposition of `𝕀_ℚ`**:
`𝕀_ℚ ≃* ℚˣ × (ℝ_{>0} × U_{ℚ,f})`. -/
def ratIdeleDecompEquiv :
    RatIdele ≃* ℚˣ × (posRealSubgroup × finUnitSubgroup ℚ) := by
  let φ : ℚˣ × (posRealSubgroup × finUnitSubgroup ℚ) →* RatIdele :=
    { toFun := fun ⟨q, y, u⟩ => diagRatIdele q * (y.1, u.1)
      map_one' := by simp
      map_mul' := fun ⟨q₁, y₁, u₁⟩ ⟨q₂, y₂, u₂⟩ => by
        change diagRatIdele (q₁ * q₂) * ((y₁ * y₂).1, (u₁ * u₂).1) =
          (diagRatIdele q₁ * (y₁.1, u₁.1)) * (diagRatIdele q₂ * (y₂.1, u₂.1))
        rw [map_mul]
        apply Prod.ext <;> simp [mul_assoc, mul_left_comm, mul_comm] }
  have hbij : Function.Bijective φ := by
    constructor
    · rintro ⟨q₁, y₁, u₁⟩ ⟨q₂, y₂, u₂⟩ h
      have hcomm : ∀ {G : Type} [CommGroup G] (a b c d : G),
          a * c = b * d → a * b⁻¹ = d * c⁻¹ := fun a b c d hab => by
        calc a * b⁻¹ = (a * c) * b⁻¹ * c⁻¹ := by rw [mul_right_comm, mul_inv_cancel_right]
          _ = (b * d) * b⁻¹ * c⁻¹ := by rw [hab]
          _ = d * c⁻¹ := by rw [mul_comm b d, mul_inv_cancel_right]
      have hdiff : diagRatIdele (q₁ * q₂⁻¹) = ((y₂ * y₁⁻¹).1, (u₂ * u₁⁻¹).1) := by
        rw [map_mul, map_inv]
        exact hcomm (G := RatIdele) (diagRatIdele q₁) (diagRatIdele q₂) (y₁.1, u₁.1) (y₂.1, u₂.1) h
      have hmem : diagRatIdele (q₁ * q₂⁻¹) ∈ ratPrincipalSubgroup ⊓ ratUnitSubgroup :=
        ⟨⟨q₁ * q₂⁻¹, rfl⟩, by rw [hdiff]; exact ⟨(y₂ * y₁⁻¹).2, (u₂ * u₁⁻¹).2⟩⟩
      rw [ratPrincipal_inf_ratUnit, Subgroup.mem_bot] at hmem
      have hq : q₁ = q₂ := by
        have hq1 : (diagRatIdele (q₁ * q₂⁻¹)).1 = 1 := congrArg Prod.fst hmem
        have hqR : (((q₁ * q₂⁻¹ : ℚˣ) : ℚ) : ℝ) = (1 : ℚ) := by
          simpa [diagRatIdele] using congrArg Units.val hq1
        have hqQ : ((q₁ * q₂⁻¹ : ℚˣ) : ℚ) = 1 := Rat.cast_injective (α := ℝ) hqR
        exact mul_inv_eq_one.mp (Units.ext hqQ)
      subst hq
      have h2 : ((y₂ * y₁⁻¹).1, (u₂ * u₁⁻¹).1) = 1 := by
        rw [← hdiff, mul_inv_cancel, map_one]
      have hy : y₁ = y₂ := Subtype.ext (mul_inv_eq_one.mp (congrArg Prod.fst h2)).symm
      have hu : u₁ = u₂ := Subtype.ext (mul_inv_eq_one.mp (congrArg Prod.snd h2)).symm
      exact Prod.ext rfl (Prod.ext hy hu)
    · intro x
      have hx : x ∈ ratPrincipalSubgroup ⊔ ratUnitSubgroup := by
        rw [ratIdele_strong_approximation]; trivial
      obtain ⟨p, ⟨q, rfl⟩, ⟨y, u⟩, ⟨hy, hu⟩, hxy⟩ := Subgroup.mem_sup.mp hx
      exact ⟨⟨q, ⟨y, hy⟩, ⟨u, hu⟩⟩, hxy⟩
  exact (MulEquiv.ofBijective φ hbij).symm

theorem ratIdeleDecompEquiv_symm_apply (q : ℚˣ) (y : posRealSubgroup) (u : finUnitSubgroup ℚ) :
    ratIdeleDecompEquiv.symm (q, y, u) = diagRatIdele q * (y.1, u.1) := rfl

/-- Ring isomorphism `𝓞 ℚ ⧸ (m) ≃+* ZMod m`. -/
def ratQuotModEquivZMod (m : ℕ) : 𝓞 ℚ ⧸ ratModIdeal m ≃+* ZMod m :=
  (Ideal.quotientEquiv (ratModIdeal m) (Ideal.span {(m : ℤ)}) Rat.ringOfIntegersEquiv (by
    unfold ratModIdeal
    rw [Ideal.map_span, Set.image_singleton, map_natCast])).trans
    (Int.quotientSpanNatEquivZMod m)

/-- Unit-group isomorphism `(𝓞 ℚ ⧸ (m))ˣ ≃* (ZMod m)ˣ`. -/
def ratQuotUnitsEquivZModUnits (m : ℕ) : (𝓞 ℚ ⧸ ratModIdeal m)ˣ ≃* (ZMod m)ˣ :=
  Units.mapEquiv (ratQuotModEquivZMod m).toMulEquiv

/-- The Artin-normalized finite-idele-to-`(ZMod m)ˣ` projection on `𝕀_ℚ`:
for `x = diag(q) * (y_∞, u_f)` with `y_∞ > 0, u_f ∈ U_{ℚ,f}`, maps `x ↦ (u_f mod m)⁻¹`.
This normalization ensures that every unramified prime uniformizer `ϖ_p` (`p ∤ m`) maps to
`p mod m` (matching Frobenius `σ_p ∈ Gal(ℚ(ζ_m)/ℚ)`) and `(-1_∞, 1)` maps to `-1 mod m`. -/
def ratIdeleToZModUnits (m : ℕ) [NeZero m] : RatIdele →* (ZMod m)ˣ where
  toFun x := (ratQuotUnitsEquivZModUnits m
    (finUnitToQuotUnits (ratModIdeal_ne_bot m) (ratIdeleDecompEquiv x).2.2))⁻¹
  map_one' := by simp
  map_mul' x y := by
    rw [map_mul, Prod.snd_mul, Prod.snd_mul, map_mul, map_mul, mul_inv_rev, mul_comm]

theorem ratIdeleToZModUnits_apply_decomp (m : ℕ) [NeZero m]
    (q : ℚˣ) (y : posRealSubgroup) (u : finUnitSubgroup ℚ) :
    ratIdeleToZModUnits m (diagRatIdele q * (y.1, u.1)) =
      (ratQuotUnitsEquivZModUnits m (finUnitToQuotUnits (ratModIdeal_ne_bot m) u))⁻¹ := by
  have h : ratIdeleDecompEquiv (diagRatIdele q * (y.1, u.1)) = (q, y, u) :=
    ratIdeleDecompEquiv.apply_symm_apply (q, y, u)
  change (ratQuotUnitsEquivZModUnits m
    (finUnitToQuotUnits (ratModIdeal_ne_bot m) (ratIdeleDecompEquiv _).2.2))⁻¹ = _
  rw [h]

theorem ratIdeleToZModUnits_surjective (m : ℕ) [NeZero m] :
    Function.Surjective (ratIdeleToZModUnits m) := by
  intro w
  obtain ⟨u, hu⟩ := finUnitToQuotUnits_surjective (ratModIdeal_ne_bot m)
    ((ratQuotUnitsEquivZModUnits m).symm w⁻¹)
  refine ⟨(1, u.1), ?_⟩
  have h := ratIdeleToZModUnits_apply_decomp m 1 1 u
  simp only [map_one, one_mul, Subgroup.coe_one] at h
  rw [h, hu, MulEquiv.apply_symm_apply, inv_inv]

/-- **Exact Kernel of `ratIdeleToZModUnits m`**:
`ker(𝕀_ℚ →* (ZMod m)ˣ) = ℚˣ · (ℝ_{>0} × U_m)`. -/
theorem ratIdeleToZModUnits_ker (m : ℕ) [NeZero m] :
    (ratIdeleToZModUnits m).ker = ratPrincipalSubgroup ⊔ ratCongruenceSubgroup m := by
  ext x
  obtain ⟨⟨q, y, u⟩, rfl⟩ := ratIdeleDecompEquiv.symm.surjective x
  rw [ratIdeleDecompEquiv_symm_apply, MonoidHom.mem_ker, ratIdeleToZModUnits_apply_decomp,
    inv_eq_one, MulEquiv.map_eq_one_iff]
  change u ∈ (finUnitToQuotUnits (ratModIdeal_ne_bot m)).ker ↔ _
  rw [finUnitToQuotUnits_ker (ratModIdeal_ne_bot m), Subgroup.mem_subgroupOf]
  constructor
  · intro hu
    exact Subgroup.mem_sup.mpr ⟨diagRatIdele q, ⟨q, rfl⟩, (y.1, u.1), ⟨y.2, hu⟩, rfl⟩
  · intro hmem
    obtain ⟨p, ⟨q', rfl⟩, ⟨y', u'⟩, ⟨hy', hu'⟩, hEq⟩ := Subgroup.mem_sup.mp hmem
    have h1 : ratIdeleDecompEquiv (diagRatIdele q * (y.1, u.1)) =
        ratIdeleDecompEquiv (diagRatIdele q' * (y', u')) := congrArg ratIdeleDecompEquiv hEq.symm
    have hL : ratIdeleDecompEquiv (diagRatIdele q * (y.1, u.1)) = (q, y, u) :=
      ratIdeleDecompEquiv.apply_symm_apply (q, y, u)
    have hR : ratIdeleDecompEquiv (diagRatIdele q' * (y', u')) = (q', ⟨y', hy'⟩, ⟨u', hu'.1⟩) :=
      ratIdeleDecompEquiv.apply_symm_apply (q', ⟨y', hy'⟩, ⟨u', hu'.1⟩)
    rw [hL, hR] at h1
    have hu_eq : u = ⟨u', hu'.1⟩ := congrArg (fun t => t.2.2) h1
    rw [hu_eq]
    exact hu'

/-- **Strong-Approximation Quotient Isomorphism over `ℚ`**:
`𝕀_ℚ ⧸ (ℚˣ · (ℝ_{>0} × U_m)) ≃* (ZMod m)ˣ`. -/
def ratIdeleClassEquivZModUnits (m : ℕ) [NeZero m] :
    RatIdele ⧸ (ratPrincipalSubgroup ⊔ ratCongruenceSubgroup m) ≃* (ZMod m)ˣ :=
  (QuotientGroup.quotientMulEquivOfEq (ratIdeleToZModUnits_ker m).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (ratIdeleToZModUnits m)
      (ratIdeleToZModUnits_surjective m))

/-- The height-one prime ideal `v_p : HeightOneSpectrum (𝓞 ℚ)` corresponding to a rational prime
`p : ℕ`. -/
def ratPrimePlace {p : ℕ} (hp : p.Prime) : HeightOneSpectrum (𝓞 ℚ) where
  asIdeal := Ideal.span {(p : 𝓞 ℚ)}
  isPrime := by
    have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
    have hpO : Prime (p : 𝓞 ℚ) := by
      have hEq : Rat.ringOfIntegersEquiv.symm (p : ℤ) = (p : 𝓞 ℚ) := map_natCast _ p
      rw [← hEq]
      refine ⟨?_, ?_, ?_⟩
      · intro h0
        exact hpZ.ne_zero (Rat.ringOfIntegersEquiv.symm.injective (by simpa using h0))
      · intro hu
        have hu' : IsUnit (Rat.ringOfIntegersEquiv (Rat.ringOfIntegersEquiv.symm (p : ℤ))) :=
          hu.map Rat.ringOfIntegersEquiv.toRingHom
        rw [RingEquiv.apply_symm_apply] at hu'
        exact hpZ.not_isUnit hu'
      · intro a b hdvd
        obtain ⟨c, hc⟩ := hdvd
        have hdvdZ : (p : ℤ) ∣ Rat.ringOfIntegersEquiv a * Rat.ringOfIntegersEquiv b := by
          refine ⟨Rat.ringOfIntegersEquiv c, ?_⟩
          have := congrArg Rat.ringOfIntegersEquiv hc
          simpa [map_mul, RingEquiv.apply_symm_apply] using this
        rcases hpZ.dvd_or_dvd hdvdZ with ⟨d, hd⟩ | ⟨d, hd⟩
        · left
          refine ⟨Rat.ringOfIntegersEquiv.symm d, ?_⟩
          apply Rat.ringOfIntegersEquiv.injective
          simpa [map_mul, RingEquiv.apply_symm_apply] using hd
        · right
          refine ⟨Rat.ringOfIntegersEquiv.symm d, ?_⟩
          apply Rat.ringOfIntegersEquiv.injective
          simpa [map_mul, RingEquiv.apply_symm_apply] using hd
    exact (Ideal.span_singleton_prime hpO.ne_zero).mpr hpO
  ne_bot := by
    rw [ne_eq, Ideal.span_singleton_eq_bot]
    exact Nat.cast_ne_zero.mpr hp.ne_zero

open Classical in
/-- The **prime uniformizer idele** `ϖ_p ∈ 𝕀_ℚ` at a prime `p`, equal to `1` at `∞` and all
places `v ≠ v_p`, and equal to `p` at the place `v_p`. -/
def ratPrimeUniformizer (p : ℕ) (hp : p.Prime) : RatIdele :=
  let vp := ratPrimePlace hp
  have hp_ne : ∀ v : HeightOneSpectrum (𝓞 ℚ),
      algebraMap (𝓞 ℚ) (v.adicCompletion ℚ) (p : 𝓞 ℚ) ≠ 0 := by
    intro v h0
    have hpQ : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
    have h1 : algebraMap (𝓞 ℚ) (v.adicCompletion ℚ) (p : 𝓞 ℚ) =
        algebraMap ℚ (v.adicCompletion ℚ) (p : ℚ) := by
      rw [IsScalarTower.algebraMap_apply (𝓞 ℚ) ℚ (v.adicCompletion ℚ), map_natCast]
    rw [h1] at h0
    exact hpQ ((algebraMap ℚ (v.adicCompletion ℚ)).injective (by simpa using h0))
  have hmem_val : ∀ᶠ v : HeightOneSpectrum (𝓞 ℚ) in Filter.cofinite,
      (if v = vp then algebraMap (𝓞 ℚ) (v.adicCompletion ℚ) (p : 𝓞 ℚ) else 1) ∈
        (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) :=
    Filter.mem_cofinite.mpr ((Set.finite_singleton vp).subset fun v hv => by
      by_contra hne
      have hne' : v ≠ vp := hne
      exact hv (show (if v = vp then algebraMap (𝓞 ℚ) (v.adicCompletion ℚ) (p : 𝓞 ℚ) else 1) ∈
          (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) by
        rw [if_neg hne']
        exact (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).mpr (by rw [map_one])))
  have hmem_inv : ∀ᶠ v : HeightOneSpectrum (𝓞 ℚ) in Filter.cofinite,
      (if v = vp then (algebraMap (𝓞 ℚ) (v.adicCompletion ℚ) (p : 𝓞 ℚ))⁻¹ else 1) ∈
        (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) :=
    Filter.mem_cofinite.mpr ((Set.finite_singleton vp).subset fun v hv => by
      by_contra hne
      have hne' : v ≠ vp := hne
      exact hv (show (if v = vp then (algebraMap (𝓞 ℚ) (v.adicCompletion ℚ) (p : 𝓞 ℚ))⁻¹ else 1) ∈
          (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) by
        rw [if_neg hne']
        exact (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).mpr (by rw [map_one])))
  (1,
    { val := RestrictedProduct.mk
        (fun v => if v = vp then algebraMap (𝓞 ℚ) (v.adicCompletion ℚ) (p : 𝓞 ℚ) else 1)
        hmem_val
      inv := RestrictedProduct.mk
        (fun v => if v = vp then (algebraMap (𝓞 ℚ) (v.adicCompletion ℚ) (p : 𝓞 ℚ))⁻¹ else 1)
        hmem_inv
      val_inv := finAdele_ext fun v => by
        change (if v = vp then algebraMap (𝓞 ℚ) (v.adicCompletion ℚ) (p : 𝓞 ℚ) else 1) *
          (if v = vp then (algebraMap (𝓞 ℚ) (v.adicCompletion ℚ) (p : 𝓞 ℚ))⁻¹ else 1) = 1
        split_ifs with hv
        · exact mul_inv_cancel₀ (hp_ne v)
        · exact one_mul 1
      inv_val := finAdele_ext fun v => by
        change (if v = vp then (algebraMap (𝓞 ℚ) (v.adicCompletion ℚ) (p : 𝓞 ℚ))⁻¹ else 1) *
          (if v = vp then algebraMap (𝓞 ℚ) (v.adicCompletion ℚ) (p : 𝓞 ℚ) else 1) = 1
        split_ifs with hv
        · exact inv_mul_cancel₀ (hp_ne v)
        · exact one_mul 1 })

private theorem ratPrimeUniformizer_apply_self {p : ℕ} (hp : p.Prime) :
    (ratPrimeUniformizer p hp).2.val (ratPrimePlace hp) =
      algebraMap (𝓞 ℚ) ((ratPrimePlace hp).adicCompletion ℚ) (p : 𝓞 ℚ) := by
  classical
  change (if ratPrimePlace hp = ratPrimePlace hp then
    algebraMap (𝓞 ℚ) ((ratPrimePlace hp).adicCompletion ℚ) (p : 𝓞 ℚ) else 1) = _
  exact if_pos rfl

private theorem ratPrimeUniformizer_apply_ne {p : ℕ} (hp : p.Prime)
    {v : HeightOneSpectrum (𝓞 ℚ)} (hv : v ≠ ratPrimePlace hp) :
    (ratPrimeUniformizer p hp).2.val v = 1 := by
  classical
  change (if v = ratPrimePlace hp then
    algebraMap (𝓞 ℚ) (v.adicCompletion ℚ) (p : 𝓞 ℚ) else 1) = 1
  exact if_neg hv

/-- **Exact Uniformizer Reciprocity Evaluation**:
for every unramified prime `p ∤ m`, `ratIdeleToZModUnits m (ratPrimeUniformizer p hp) = p mod m`. -/
theorem ratIdeleToZModUnits_primeUniformizer {m p : ℕ} [NeZero m] (hp : p.Prime)
    (hndvd : ¬ p ∣ m) :
    ratIdeleToZModUnits m (ratPrimeUniformizer p hp) =
      ZMod.unitOfCoprime p ((Nat.Prime.coprime_iff_not_dvd hp).mpr hndvd) := by
  classical
  set vp := ratPrimePlace hp
  have hpQ : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hpR : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr hp.pos
  set qp : ℚˣ := Units.mk0 (p : ℚ) hpQ
  set yp : posRealSubgroup :=
    ⟨Units.mk0 ((p : ℝ)⁻¹) (inv_pos.mpr hpR).ne', by
      change (0 : ℝ) < (p : ℝ)⁻¹
      exact inv_pos.mpr hpR⟩
  have hup_mem : (diagFinIdele ℚ qp)⁻¹ * (ratPrimeUniformizer p hp).2 ∈ finUnitSubgroup ℚ := by
    intro v
    change Valued.v (((diagFinIdele ℚ qp)⁻¹).val v * (ratPrimeUniformizer p hp).2.val v) = 1
    rw [map_mul]
    have hdiag_inv : Valued.v (((diagFinIdele ℚ qp)⁻¹).val v) = (v.intValuation (p : 𝓞 ℚ))⁻¹ := by
      have hmul := finIdele_val_mul_inv (diagFinIdele ℚ qp) v
      have hdiag : Valued.v ((diagFinIdele ℚ qp).val v) = v.intValuation (p : 𝓞 ℚ) := by
        change Valued.v ((FiniteAdeleRing.algebraMap (𝓞 ℚ) ℚ (algebraMap (𝓞 ℚ) ℚ (p : 𝓞 ℚ))) v) = _
        rw [valued_finAdele_algebraMap, HeightOneSpectrum.valuation_of_algebraMap]
      have hne : v.intValuation (p : 𝓞 ℚ) ≠ 0 := by
        rw [← hdiag]
        exact finIdele_val_ne_zero (diagFinIdele ℚ qp) v
      rw [hdiag] at hmul
      change Valued.v ((diagFinIdele ℚ qp).inv v) = _
      exact mul_left_cancel₀ hne (by rw [hmul, mul_inv_cancel₀ hne])
    rw [hdiag_inv]
    by_cases hv : v = vp
    · subst hv
      have h2 : Valued.v ((ratPrimeUniformizer p hp).2.val vp) = vp.intValuation (p : 𝓞 ℚ) := by
        rw [ratPrimeUniformizer_apply_self hp, valued_algebraMap_int]
      have hne : vp.intValuation (p : 𝓞 ℚ) ≠ 0 := by
        have h1 : (p : 𝓞 ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
        rw [HeightOneSpectrum.intValuation_apply, HeightOneSpectrum.intValuationDef_if_neg vp h1]
        exact WithZero.coe_ne_zero
      rw [h2, inv_mul_cancel₀ hne]
    · have h2 : Valued.v ((ratPrimeUniformizer p hp).2.val v) = 1 := by
        rw [ratPrimeUniformizer_apply_ne hp hv, map_one]
      have hnotmem : (p : 𝓞 ℚ) ∉ v.asIdeal := by
        intro hmem
        have hle : vp.asIdeal ≤ v.asIdeal := (Ideal.span_singleton_le_iff_mem _).mpr hmem
        exact hv (HeightOneSpectrum.ext (vp.isMaximal.eq_of_le v.isPrime.ne_top hle)).symm
      rw [h2, mul_one, HeightOneSpectrum.intValuation_eq_one_iff.mpr hnotmem, inv_one]
  set up : finUnitSubgroup ℚ := ⟨(diagFinIdele ℚ qp)⁻¹ * (ratPrimeUniformizer p hp).2, hup_mem⟩
  have hdecomp : ratPrimeUniformizer p hp = diagRatIdele qp * (yp.1, up.1) := by
    apply Prod.ext
    · apply Units.ext
      change (1 : ℝ) = (p : ℝ) * (p : ℝ)⁻¹
      exact (mul_inv_cancel₀ hpR.ne').symm
    · change (ratPrimeUniformizer p hp).2 = diagFinIdele ℚ qp * ((diagFinIdele ℚ qp)⁻¹ * _)
      rw [mul_inv_cancel_left]
  rw [hdecomp, ratIdeleToZModUnits_apply_decomp]
  have hvp_not_dvd : idealOrd (ratModIdeal m) vp = 0 := by
    by_contra hnz
    have hdvd : vp.asIdeal ∣ ratModIdeal m :=
      (Associates.count_ne_zero_iff_dvd (ratModIdeal_ne_bot m)
        (Ideal.prime_of_isPrime vp.ne_bot vp.isPrime).irreducible).mp hnz
    have hmem : (m : 𝓞 ℚ) ∈ vp.asIdeal :=
      (Ideal.span_singleton_le_iff_mem _).mp (Ideal.dvd_iff_le.mp hdvd)
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hmem
    have hZ : (p : ℤ) ∣ (m : ℤ) := by
      refine ⟨Rat.ringOfIntegersEquiv c, ?_⟩
      have := congrArg Rat.ringOfIntegersEquiv hc
      simpa [map_mul, map_natCast] using this
    exact hndvd (Int.ofNat_dvd.mp hZ)
  have hcop : p.Coprime m := (Nat.Prime.coprime_iff_not_dvd hp).mpr hndvd
  have hup_mul_p : finUnitToQuotUnits (ratModIdeal_ne_bot m) up *
      ((ratQuotUnitsEquivZModUnits m).symm (ZMod.unitOfCoprime p hcop)) = 1 := by
    apply (crtQuotUnitsEquiv (ratModIdeal m) (ratModIdeal_ne_bot m)).injective
    rw [map_mul, map_one]
    funext v
    have hv_ne : v.1 ≠ vp := by
      intro hEq
      have hnz : idealOrd (ratModIdeal m) v.1 ≠ 0 := (Set.Finite.mem_toFinset _).mp v.2
      rw [hEq] at hnz
      exact hnz hvp_not_dvd
    apply Units.ext
    have hL : ((crtQuotUnitsEquiv (ratModIdeal m) (ratModIdeal_ne_bot m))
        (finUnitToQuotUnits (ratModIdeal_ne_bot m) up) v).val =
        localQuotMap v.1 (idealOrd (ratModIdeal m) v.1) (finUnitAt up v.1).val := by
      have h := (crtQuotUnitsEquiv (ratModIdeal m) (ratModIdeal_ne_bot m)).apply_symm_apply
        (fun w : idealSupport (ratModIdeal m) (ratModIdeal_ne_bot m) =>
          localQuotUnitsMap w.1 (idealOrd (ratModIdeal m) w.1) (finUnitAt up w.1))
      exact congrArg (fun f => (f v).val) h
    have hR : ((crtQuotUnitsEquiv (ratModIdeal m) (ratModIdeal_ne_bot m))
        ((ratQuotUnitsEquivZModUnits m).symm (ZMod.unitOfCoprime p hcop)) v).val =
        Ideal.Quotient.mk (v.1.asIdeal ^ idealOrd (ratModIdeal m) v.1) (p : 𝓞 ℚ) := by
      have hmk : ((ratQuotUnitsEquivZModUnits m).symm (ZMod.unitOfCoprime p hcop)).val =
          Ideal.Quotient.mk (ratModIdeal m) (p : 𝓞 ℚ) := by
        apply (ratQuotModEquivZMod m).injective
        have h1 : ratQuotModEquivZMod m
            ((ratQuotUnitsEquivZModUnits m).symm (ZMod.unitOfCoprime p hcop)).val =
            ((ZMod.unitOfCoprime p hcop : (ZMod m)ˣ) : ZMod m) :=
          congrArg Units.val ((ratQuotUnitsEquivZModUnits m).apply_symm_apply _)
        rw [h1, ZMod.coe_unitOfCoprime]
        have h2 : ratQuotModEquivZMod m (Ideal.Quotient.mk (ratModIdeal m) (p : 𝓞 ℚ)) = (p : ZMod m) := by
          have hnat : (Ideal.Quotient.mk (ratModIdeal m) (p : 𝓞 ℚ)) = (p : 𝓞 ℚ ⧸ ratModIdeal m) :=
            map_natCast (Ideal.Quotient.mk (ratModIdeal m)) p
          rw [hnat, map_natCast]
        exact h2.symm
      change crtQuotRingEquiv (ratModIdeal m) (ratModIdeal_ne_bot m)
        ((ratQuotUnitsEquivZModUnits m).symm (ZMod.unitOfCoprime p hcop)).val v = _
      rw [hmk, crtQuotRingEquiv_mk]
    change ((crtQuotUnitsEquiv (ratModIdeal m) (ratModIdeal_ne_bot m))
        (finUnitToQuotUnits (ratModIdeal_ne_bot m) up) v).val *
      ((crtQuotUnitsEquiv (ratModIdeal m) (ratModIdeal_ne_bot m))
        ((ratQuotUnitsEquivZModUnits m).symm (ZMod.unitOfCoprime p hcop)) v).val = 1
    rw [hL, hR, ← localQuotMap_algebraMap v.1 (idealOrd (ratModIdeal m) v.1) (p : 𝓞 ℚ), ← map_mul]
    have hprod1 :
        (finUnitAt up v.1).val * algebraMap (𝓞 ℚ) (v.1.adicCompletionIntegers ℚ) (p : 𝓞 ℚ) = 1 := by
      apply Subtype.ext
      change ((diagFinIdele ℚ qp)⁻¹).val v.1 * (ratPrimeUniformizer p hp).2.val v.1 *
        algebraMap (𝓞 ℚ) (v.1.adicCompletion ℚ) (p : 𝓞 ℚ) = 1
      have h1 : (ratPrimeUniformizer p hp).2.val v.1 = 1 :=
        ratPrimeUniformizer_apply_ne hp hv_ne
      have h2 :
          algebraMap (𝓞 ℚ) (v.1.adicCompletion ℚ) (p : 𝓞 ℚ) = (diagFinIdele ℚ qp).val v.1 := by
        have h := (finAdele_algebraMap_int_apply (p : 𝓞 ℚ) v.1).symm
        simpa [diagFinIdele, qp] using h
      rw [h1, mul_one, h2]
      exact finIdele_apply_inv_mul (diagFinIdele ℚ qp) v.1
    rw [hprod1, map_one]
  have heq_u : finUnitToQuotUnits (ratModIdeal_ne_bot m) up =
      ((ratQuotUnitsEquivZModUnits m).symm (ZMod.unitOfCoprime p hcop))⁻¹ :=
    eq_inv_of_mul_eq_one_left hup_mul_p
  rw [heq_u, map_inv, MulEquiv.apply_symm_apply, inv_inv]

/-- **Exact Archimedean Sign Evaluation**:
`ratIdeleToZModUnits m (-1, 1) = -1` (complex conjugation at `∞`). -/
theorem ratIdeleToZModUnits_neg_one_arch (m : ℕ) [NeZero m] :
    ratIdeleToZModUnits m ((-1 : ℝˣ), (1 : FinIdele ℚ)) = -1 := by
  have hdecomp : ((-1 : ℝˣ), (1 : FinIdele ℚ)) =
      diagRatIdele (-1) * ((1 : posRealSubgroup).1, (intUnitsToFinUnits ℚ (-1)).1) := by
    apply Prod.ext
    · apply Units.ext
      simp [diagRatIdele]
    · change (1 : FinIdele ℚ) = diagFinIdele ℚ (-1) * diagFinIdele ℚ (intUnitsToFieldUnits ℚ (-1))
      have h1 : intUnitsToFieldUnits ℚ (-1) = (-1 : ℚˣ) := by
        apply Units.ext; simp [intUnitsToFieldUnits]
      rw [h1, ← map_mul, show (-1 : ℚˣ) * (-1 : ℚˣ) = 1 by apply Units.ext; simp, map_one]
  rw [hdecomp, ratIdeleToZModUnits_apply_decomp]
  have h2 := congrFun (congrArg DFunLike.coe
    (finUnitToQuotUnits_comp_intUnits (ratModIdeal_ne_bot m))) (-1)
  simp only [MonoidHom.comp_apply] at h2
  rw [h2]
  have hneg : globalUnitsToQuotUnits (ratModIdeal m) (-1) = -1 := by
    apply Units.ext
    simp [globalUnitsToQuotUnits]
  rw [hneg]
  apply Units.ext
  have hmap : ratQuotUnitsEquivZModUnits m (-1) = -1 := by
    apply Units.ext
    change ratQuotModEquivZMod m (-1) = -1
    rw [map_neg, map_one]
  rw [hmap]
  simp

/-- **Concrete Idelic Hecke Characters of `𝕀_ℚ / ℚˣ` of Conductor Dividing `m`**:
finite-order complex characters `ω : 𝕀_ℚ →* ℂˣ` trivial on `ℚˣ`, `ℝ_{>0}`, and `U_m`. -/
structure IdelicHeckeChar (m : ℕ) [NeZero m] where
  toHom : RatIdele →* ℂˣ
  trivial_principal : ∀ q : ℚˣ, toHom (diagRatIdele q) = 1
  trivial_arch : ∀ y : ℝˣ, (0 : ℝ) < (y : ℝ) → toHom (y, 1) = 1
  trivial_cong : ∀ u ∈ rayUnitSubgroup ℚ (ratModIdeal m), toHom (1, u) = 1

namespace IdelicHeckeChar

variable {m : ℕ} [NeZero m]

@[ext]
theorem ext {ω₁ ω₂ : IdelicHeckeChar m} (h : ω₁.toHom = ω₂.toHom) : ω₁ = ω₂ := by
  cases ω₁; cases ω₂; congr

instance : CommGroup (IdelicHeckeChar m) where
  one := ⟨1, fun _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩
  mul ω₁ ω₂ :=
    ⟨ω₁.toHom * ω₂.toHom,
      fun q => by simp [ω₁.trivial_principal, ω₂.trivial_principal],
      fun y hy => by simp [ω₁.trivial_arch y hy, ω₂.trivial_arch y hy],
      fun u hu => by simp [ω₁.trivial_cong u hu, ω₂.trivial_cong u hu]⟩
  inv ω :=
    ⟨ω.toHom⁻¹,
      fun q => by simp [ω.trivial_principal],
      fun y hy => by simp [ω.trivial_arch y hy],
      fun u hu => by simp [ω.trivial_cong u hu]⟩
  mul_assoc a b c := IdelicHeckeChar.ext (MonoidHom.ext fun x => mul_assoc (a.toHom x) (b.toHom x) (c.toHom x))
  one_mul a := IdelicHeckeChar.ext (MonoidHom.ext fun x => one_mul (a.toHom x))
  mul_one a := IdelicHeckeChar.ext (MonoidHom.ext fun x => mul_one (a.toHom x))
  inv_mul_cancel a := IdelicHeckeChar.ext (MonoidHom.ext fun x => inv_mul_cancel (a.toHom x))
  mul_comm a b := IdelicHeckeChar.ext (MonoidHom.ext fun x => mul_comm (a.toHom x) (b.toHom x))

theorem trivial_on_kernel (ω : IdelicHeckeChar m) :
    ratPrincipalSubgroup ⊔ ratCongruenceSubgroup m ≤ ω.toHom.ker := by
  refine sup_le ?_ ?_
  · rintro _ ⟨q, rfl⟩
    exact ω.trivial_principal q
  · rintro ⟨y, u⟩ ⟨hy, hu⟩
    rw [MonoidHom.mem_ker]
    have hy' : (0 : ℝ) < (y : ℝ) := hy
    have hsplit : (y, u) = (y, (1 : FinIdele ℚ)) * ((1 : ℝˣ), u) :=
      Prod.ext (mul_one y).symm (one_mul u).symm
    rw [hsplit, map_mul, ω.trivial_arch y hy', ω.trivial_cong u hu, one_mul]

/-- The descended homomorphism on `𝕀_ℚ ⧸ (ℚˣ · (ℝ_{>0} × U_m))`. -/
def toQuotHom (ω : IdelicHeckeChar m) :
    RatIdele ⧸ (ratPrincipalSubgroup ⊔ ratCongruenceSubgroup m) →* ℂˣ :=
  QuotientGroup.lift (ratPrincipalSubgroup ⊔ ratCongruenceSubgroup m) ω.toHom ω.trivial_on_kernel

end IdelicHeckeChar

/-- Helper: `MulChar.ofUnitHom` preserves multiplication. -/
private theorem ofUnitHom_mul_local {R R' : Type*} [CommMonoid R] [CommMonoidWithZero R']
    (f g : Rˣ →* R'ˣ) :
    MulChar.ofUnitHom (f * g) = MulChar.ofUnitHom f * MulChar.ofUnitHom g := by
  ext u
  simp

/-- **Exact Idelic Hecke Character ↔ Classical `DirichletCharacter ℂ m` Group Isomorphism**:
`idelicHeckeCharEquivDirichlet m : IdelicHeckeChar m ≃* DirichletCharacter ℂ m`. -/
def idelicHeckeCharEquivDirichlet (m : ℕ) [NeZero m] :
    IdelicHeckeChar m ≃* DirichletCharacter ℂ m where
  toFun ω := MulChar.ofUnitHom
    (ω.toQuotHom.comp (ratIdeleClassEquivZModUnits m).symm.toMonoidHom)
  invFun χ :=
    { toHom := (MulChar.toUnitHom χ).comp (ratIdeleToZModUnits m)
      trivial_principal := fun q => by
        rw [MonoidHom.comp_apply]
        have h1 : diagRatIdele q ∈ (ratIdeleToZModUnits m).ker := by
          rw [ratIdeleToZModUnits_ker]
          exact Subgroup.mem_sup_left ⟨q, rfl⟩
        rw [MonoidHom.mem_ker.mp h1, map_one]
      trivial_arch := fun y hy => by
        rw [MonoidHom.comp_apply]
        have h1 : (y, (1 : FinIdele ℚ)) ∈ (ratIdeleToZModUnits m).ker := by
          rw [ratIdeleToZModUnits_ker]
          exact Subgroup.mem_sup_right
            ⟨(mem_posRealSubgroup_iff.mpr hy), (rayUnitSubgroup ℚ (ratModIdeal m)).one_mem⟩
        rw [MonoidHom.mem_ker.mp h1, map_one]
      trivial_cong := fun u hu => by
        rw [MonoidHom.comp_apply]
        have h1 : ((1 : ℝˣ), u) ∈ (ratIdeleToZModUnits m).ker := by
          rw [ratIdeleToZModUnits_ker]
          exact Subgroup.mem_sup_right ⟨posRealSubgroup.one_mem, hu⟩
        rw [MonoidHom.mem_ker.mp h1, map_one] }
  left_inv ω := by
    ext x
    change ((MulChar.toUnitHom (MulChar.ofUnitHom
      (ω.toQuotHom.comp (ratIdeleClassEquivZModUnits m).symm.toMonoidHom)))
      (ratIdeleToZModUnits m x) : ℂ) = (ω.toHom x : ℂ)
    rw [MulChar.coe_toUnitHom, MulChar.ofUnitHom_coe, MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom]
    have hq : (ratIdeleClassEquivZModUnits m).symm (ratIdeleToZModUnits m x) =
        QuotientGroup.mk x := by
      apply (ratIdeleClassEquivZModUnits m).injective
      rw [MulEquiv.apply_symm_apply]
      rfl
    rw [hq]
    rfl
  right_inv χ := by
    ext u
    change (MulChar.ofUnitHom (_)) (u : ZMod m) = χ (u : ZMod m)
    rw [MulChar.ofUnitHom_coe, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    obtain ⟨x, hx⟩ := ratIdeleToZModUnits_surjective m u
    have hq : (ratIdeleClassEquivZModUnits m).symm u = QuotientGroup.mk x := by
      apply (ratIdeleClassEquivZModUnits m).injective
      rw [MulEquiv.apply_symm_apply]
      exact hx.symm
    rw [hq]
    change ((MulChar.toUnitHom χ) (ratIdeleToZModUnits m x) : ℂ) = χ (u : ZMod m)
    rw [hx, MulChar.coe_toUnitHom]
  map_mul' ω₁ ω₂ := by
    have hcomp :
        (ω₁ * ω₂).toQuotHom.comp (ratIdeleClassEquivZModUnits m).symm.toMonoidHom =
          ω₁.toQuotHom.comp (ratIdeleClassEquivZModUnits m).symm.toMonoidHom *
            ω₂.toQuotHom.comp (ratIdeleClassEquivZModUnits m).symm.toMonoidHom := by
      ext u
      obtain ⟨x, hx⟩ := ratIdeleToZModUnits_surjective m u
      have hq : (ratIdeleClassEquivZModUnits m).symm u = QuotientGroup.mk x := by
        apply (ratIdeleClassEquivZModUnits m).injective
        rw [MulEquiv.apply_symm_apply]
        exact hx.symm
      simp only [MonoidHom.comp_apply, MonoidHom.mul_apply, MulEquiv.coe_toMonoidHom, hq,
        IdelicHeckeChar.toQuotHom, QuotientGroup.lift_mk]
      rfl
    exact hcomp ▸ ofUnitHom_mul_local _ _

/-- **Exact Uniformizer-to-Dirichlet Value Identity**:
for every `ω : IdelicHeckeChar m` and every unramified prime `p ∤ m`,
`(idelicHeckeCharEquivDirichlet m ω) p = ω(ϖ_p)`. -/
theorem idelicHeckeCharEquivDirichlet_apply_prime {m p : ℕ} [NeZero m]
    (ω : IdelicHeckeChar m) (hp : p.Prime) (hndvd : ¬ p ∣ m) :
    idelicHeckeCharEquivDirichlet m ω (p : ZMod m) = (ω.toHom (ratPrimeUniformizer p hp) : ℂ) := by
  have hcop : p.Coprime m := (Nat.Prime.coprime_iff_not_dvd hp).mpr hndvd
  have hu : (ZMod.unitOfCoprime p hcop : ZMod m) = (p : ZMod m) := ZMod.coe_unitOfCoprime p hcop
  rw [← hu]
  simp only [idelicHeckeCharEquivDirichlet, MulEquiv.coe_mk, Equiv.coe_fn_mk,
    MulChar.ofUnitHom_coe, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  have hq : (ratIdeleClassEquivZModUnits m).symm (ZMod.unitOfCoprime p hcop) =
      QuotientGroup.mk (ratPrimeUniformizer p hp) := by
    apply (ratIdeleClassEquivZModUnits m).injective
    rw [MulEquiv.apply_symm_apply]
    exact (ratIdeleToZModUnits_primeUniformizer hp hndvd).symm
  rw [hq]
  rfl

/-- **Exact Archimedean Sign Identity**:
`(idelicHeckeCharEquivDirichlet m ω) (-1) = ω(-1_∞, 1)`. -/
theorem idelicHeckeCharEquivDirichlet_apply_neg_one {m : ℕ} [NeZero m]
    (ω : IdelicHeckeChar m) :
    idelicHeckeCharEquivDirichlet m ω (-1 : ZMod m) = (ω.toHom ((-1 : ℝˣ), (1 : FinIdele ℚ)) : ℂ) := by
  have hu : ((-1 : (ZMod m)ˣ) : ZMod m) = (-1 : ZMod m) := rfl
  rw [← hu]
  simp only [idelicHeckeCharEquivDirichlet, MulEquiv.coe_mk, Equiv.coe_fn_mk,
    MulChar.ofUnitHom_coe, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  have hq : (ratIdeleClassEquivZModUnits m).symm (-1) =
      QuotientGroup.mk ((-1 : ℝˣ), (1 : FinIdele ℚ)) := by
    apply (ratIdeleClassEquivZModUnits m).injective
    rw [MulEquiv.apply_symm_apply]
    exact (ratIdeleToZModUnits_neg_one_arch m).symm
  rw [hq]
  rfl

/-- **Idelic Artin Reciprocity Isomorphism over `ℚ`**:
`𝕀_ℚ ⧸ (ℚˣ · (ℝ_{>0} × U_m)) ≃* Gal(ℚ(ζ_m)/ℚ)`. -/
def idelicArtinMap (m : ℕ) [NeZero m] :
    RatIdele ⧸ (ratPrincipalSubgroup ⊔ ratCongruenceSubgroup m) ≃*
      Stage4ClassFieldTheory.CycGal m :=
  (ratIdeleClassEquivZModUnits m).trans (Stage4ClassFieldTheory.artinMap m)

/-- **Idelic Artin Reciprocity on Prime Uniformizers**:
for every unramified prime `p ∤ m`, `idelicArtinMap m ⟦ϖ_p⟧ = frobPrime m hp hndvd`. -/
theorem idelicArtinMap_primeUniformizer {m p : ℕ} [NeZero m] (hp : p.Prime) (hndvd : ¬ p ∣ m) :
    idelicArtinMap m (QuotientGroup.mk (ratPrimeUniformizer p hp)) =
      Stage4ClassFieldTheory.frobPrime m hp hndvd := by
  change Stage4ClassFieldTheory.artinMap m (ratIdeleToZModUnits m (ratPrimeUniformizer p hp)) = _
  rw [ratIdeleToZModUnits_primeUniformizer hp hndvd]
  rfl

/-- **Idelic Hecke Character ↔ Cyclotomic Galois Character Isomorphism**:
`IdelicHeckeChar m ≃* GalChar m`. -/
def idelicHeckeCharEquivGalChar (m : ℕ) [NeZero m] :
    IdelicHeckeChar m ≃* Stage4ClassFieldTheory.GalChar m :=
  (idelicHeckeCharEquivDirichlet m).trans (Stage4ClassFieldTheory.galCharEquivDirichlet m).symm

/-- **Exact Commutative CFT Triangle (Galois ↔ Dirichlet ↔ Idelic Hecke)**:
composing `idelicHeckeCharEquivGalChar m` with `Stage4ClassFieldTheory.galCharEquivDirichlet m`
recovers `idelicHeckeCharEquivDirichlet m` identically! -/
theorem cft_triangle_commutes (m : ℕ) [NeZero m] (ω : IdelicHeckeChar m) :
    Stage4ClassFieldTheory.galCharEquivDirichlet m (idelicHeckeCharEquivGalChar m ω) =
      idelicHeckeCharEquivDirichlet m ω :=
  (Stage4ClassFieldTheory.galCharEquivDirichlet m).apply_symm_apply _

/-- **Exact Pointwise Commutativity on Unramified Primes `p ∤ m`**:
`ω(ϖ_p) = χ_ω(p) = ρ_ω(σ_p)` across all three vertices of the CFT triangle! -/
theorem cft_triangle_prime_values {m p : ℕ} [NeZero m] (ω : IdelicHeckeChar m)
    (hp : p.Prime) (hndvd : ¬ p ∣ m) :
    (ω.toHom (ratPrimeUniformizer p hp) : ℂ) =
      idelicHeckeCharEquivDirichlet m ω (p : ZMod m) ∧
    idelicHeckeCharEquivDirichlet m ω (p : ZMod m) =
      ((idelicHeckeCharEquivGalChar m ω) (Stage4ClassFieldTheory.frobPrime m hp hndvd) : ℂ) := by
  have h1 := (idelicHeckeCharEquivDirichlet_apply_prime ω hp hndvd).symm
  have hcop : p.Coprime m := (Nat.Prime.coprime_iff_not_dvd hp).mpr hndvd
  have h2 := Stage4ClassFieldTheory.dirichletOfGal_apply_coprime
    (idelicHeckeCharEquivGalChar m ω) hcop
  change Stage4ClassFieldTheory.galCharEquivDirichlet m (idelicHeckeCharEquivGalChar m ω)
    (p : ZMod m) = _ at h2
  rw [cft_triangle_commutes] at h2
  exact ⟨h1, h2⟩

/-- The local idelic Hecke Euler factor at `p`: `(1 - ω(ϖ_p) p^{-s})⁻¹` if `p` is prime and
`p ∤ m`, and `1` otherwise. -/
def idelicHeckeEulerFactor {m : ℕ} [NeZero m] (ω : IdelicHeckeChar m) (p : ℕ) (s : ℂ) : ℂ :=
  if h : p.Prime ∧ ¬ p ∣ m then
    (1 - (ω.toHom (ratPrimeUniformizer p h.1) : ℂ) * (p : ℂ) ^ (-s))⁻¹
  else 1

/-- **Exact Three-Way Local Euler-Factor Identity**: at every prime `p`,
`idelicHeckeEulerFactor ω p s = dirichletEulerFactor χ_ω p s = artinEulerFactor ρ_ω p s`. -/
theorem cft_triangle_eulerFactor {m p : ℕ} [NeZero m] (ω : IdelicHeckeChar m)
    (hp : p.Prime) (s : ℂ) :
    idelicHeckeEulerFactor ω p s =
      Stage4ClassFieldTheory.dirichletEulerFactor (idelicHeckeCharEquivDirichlet m ω) p s ∧
    Stage4ClassFieldTheory.dirichletEulerFactor (idelicHeckeCharEquivDirichlet m ω) p s =
      Stage4ClassFieldTheory.artinEulerFactor (idelicHeckeCharEquivGalChar m ω) p s := by
  have h2 : Stage4ClassFieldTheory.dirichletEulerFactor (idelicHeckeCharEquivDirichlet m ω) p s =
      Stage4ClassFieldTheory.artinEulerFactor (idelicHeckeCharEquivGalChar m ω) p s := by
    have h := Stage4ClassFieldTheory.artinEulerFactor_eq_dirichletEulerFactor
      (idelicHeckeCharEquivGalChar m ω) p s
    change _ = Stage4ClassFieldTheory.dirichletEulerFactor
      (Stage4ClassFieldTheory.galCharEquivDirichlet m (idelicHeckeCharEquivGalChar m ω)) p s at h
    rw [cft_triangle_commutes] at h
    exact h.symm
  refine ⟨?_, h2⟩
  unfold idelicHeckeEulerFactor Stage4ClassFieldTheory.dirichletEulerFactor
  by_cases hndvd : ¬ p ∣ m
  · rw [dif_pos ⟨hp, hndvd⟩, idelicHeckeCharEquivDirichlet_apply_prime ω hp hndvd]
  · rw [dif_neg (fun h => hndvd h.2)]
    have hncop : ¬ p.Coprime m := by
      rw [Nat.Prime.coprime_iff_not_dvd hp]
      exact hndvd
    have h0 : idelicHeckeCharEquivDirichlet m ω (p : ZMod m) = 0 := by
      have hnu : ¬ IsUnit (p : ZMod m) := fun hu => hncop ((ZMod.isUnit_iff_coprime p m).mp hu)
      exact MulChar.map_nonunit _ hnu
    rw [h0, zero_mul, sub_zero, inv_one]

/-- **Exact Global Three-Way `L`-Function Identity** on `Re(s) > 1`:
`∏'_p L_p(s, ω) = L(s, χ_ω) = L(s, ρ_ω)`. -/
theorem cft_triangle_LFunction {m : ℕ} [NeZero m] (ω : IdelicHeckeChar m) {s : ℂ}
    (hs : 1 < s.re) :
    ∏' (p : Nat.Primes), idelicHeckeEulerFactor ω (p : ℕ) s =
      DirichletCharacter.LFunction (idelicHeckeCharEquivDirichlet m ω) s ∧
    DirichletCharacter.LFunction (idelicHeckeCharEquivDirichlet m ω) s =
      Stage4ClassFieldTheory.artinLSeries (idelicHeckeCharEquivGalChar m ω) s := by
  have hcongr :
      (fun p : Nat.Primes => idelicHeckeEulerFactor ω (p : ℕ) s) =
        (fun p : Nat.Primes =>
          Stage4ClassFieldTheory.artinEulerFactor (idelicHeckeCharEquivGalChar m ω) (p : ℕ) s) := by
    funext p
    have h := cft_triangle_eulerFactor ω p.2 s
    exact h.1.trans h.2
  have hArt := Stage4ClassFieldTheory.artinLSeries_eq_LFunction
    (idelicHeckeCharEquivGalChar m ω) hs
  change Stage4ClassFieldTheory.artinLSeries (idelicHeckeCharEquivGalChar m ω) s =
    DirichletCharacter.LFunction
      (Stage4ClassFieldTheory.galCharEquivDirichlet m (idelicHeckeCharEquivGalChar m ω)) s at hArt
  rw [cft_triangle_commutes] at hArt
  refine ⟨?_, hArt.symm⟩
  rw [hcongr, Stage4ClassFieldTheory.artinLSeries_eulerProduct_tprod _ hs, hArt]

end RationalIdeles

/-! ## Section 4: Unified Unconditional Stage 5 Idele Class Field Summary -/

/-- **Unified Unconditional Stage 5 Idele Class Field Theory Theorem** (`0` assumptions):
bundles the finite-idele ideal-class isomorphism and finiteness for every `NumberField K`,
the finite ray-class exact sequence and cardinality identity for every nonzero modulus `𝔪`,
Strong Approximation for `𝕀_ℚ`, and the exact commutative CFT triangle
`Gal(ℚ(ζ_m)/ℚ)^∨ ≃ DirichletCharacter ℂ m ≃ IdelicHeckeChar m`. -/
theorem stage5_ideleClassField_unconditional :
    (∀ (K : Type) [Field K] [NumberField K],
      Nonempty (FinIdele K ⧸ (principalSubgroup K ⊔ finUnitSubgroup K) ≃* ClassGroup (𝓞 K)) ∧
      Finite (FinIdele K ⧸ (principalSubgroup K ⊔ finUnitSubgroup K)) ∧
      Nat.card (FinIdele K ⧸ (principalSubgroup K ⊔ finUnitSubgroup K)) =
        NumberField.classNumber K) ∧
    (∀ (K : Type) [Field K] [NumberField K] (𝔪 : Ideal (𝓞 K)) (h𝔪 : 𝔪 ≠ ⊥),
      Finite (RayClassGroup K 𝔪) ∧
      (quotUnitsToRayClass h𝔪).ker = (globalUnitsToQuotUnits 𝔪).range ∧
      (rayToClassGroup K 𝔪).ker = (quotUnitsToRayClass h𝔪).range ∧
      Nat.card (RayClassGroup K 𝔪) * Nat.card (globalUnitsToQuotUnits 𝔪).range =
        Nat.card (𝓞 K ⧸ 𝔪)ˣ * Nat.card (ClassGroup (𝓞 K))) ∧
    (ratPrincipalSubgroup ⊔ ratUnitSubgroup = ⊤ ∧
      ratPrincipalSubgroup ⊓ ratUnitSubgroup = ⊥) ∧
    (∀ (m : ℕ) [NeZero m] (ω : IdelicHeckeChar m),
      Stage4ClassFieldTheory.galCharEquivDirichlet m (idelicHeckeCharEquivGalChar m ω) =
        idelicHeckeCharEquivDirichlet m ω ∧
      ∀ (p : ℕ) (hp : p.Prime), ¬ p ∣ m →
        (ω.toHom (ratPrimeUniformizer p hp) : ℂ) =
          idelicHeckeCharEquivDirichlet m ω (p : ZMod m)) :=
  ⟨fun K _ _ => ⟨⟨ideleClassEquivClassGroup K⟩, finite_ideleClassQuotient K,
      card_ideleClassQuotient_eq_classNumber K⟩,
   fun K _ _ _ h𝔪 => ⟨finite_rayClassGroup K h𝔪, quotUnitsToRayClass_ker h𝔪,
      rayToClassGroup_ker h𝔪, card_rayClassGroup_mul_card_imgUnits K h𝔪⟩,
   ⟨ratIdele_strong_approximation, ratPrincipal_inf_ratUnit⟩,
   fun m _ ω => ⟨cft_triangle_commutes m ω,
      fun _ hp hndvd => (cft_triangle_prime_values ω hp hndvd).1⟩⟩

end RHDirect.Stage5IdeleClassField

end
