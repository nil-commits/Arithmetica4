import RHDirect.Stage2GaloisCohomology
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.RingTheory.DedekindDomain.SInteger
import Mathlib.RingTheory.DedekindDomain.SelmerGroup
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.ClassGroup.Basic
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.GroupTheory.Finiteness

/-!
# RHDirect.Stage5NumberFieldCohom

Compact, self-contained, zero-`sorry`, zero-custom-`axiom` Lean 4 formalization of
**Concrete Global Number-Field Kummer Selmer Theory, Dirichlet's `S`-Unit Theorem,
Unconditional `S`-Class-Group & `S`-Unit Finiteness, Hilbert's Theorem 90, Concrete
`H¹(Gal(L/K), μ_m(L))` Kummer Isomorphism, and Direct Bridge to
`Stage2GaloisCohomology`** on Mathlib's ACTUAL `NumberField` in pure Mathlib `v4.33.1`.

## Contents

1. **Concrete `S`-Integers, `S`-Units `𝒪_{K,S}ˣ`, `v`-adic Valuation & `S`-Class Group `Cl_S(K)`**:
   - `SIntegers K S`, `SUnits K S`, `SClassGroup K S`, `SClassGroupTorsion K S m`, and `adicVal K v`.
   - Unconditional finiteness `Finite (SClassGroup K S)` and divisibility
     `Nat.card (SClassGroup K S) ∣ Nat.card (ClassGroup (𝒪_K))`.
2. **Dirichlet's `S`-Unit Theorem & Finiteness of `SUnits K S ⧸ (SUnits K S)^m`**:
   - Exact unit–valuation sequence `1 → (𝒪_K)ˣ → SUnits K S → ℤ^S`.
   - Full Dirichlet `S`-unit structure isomorphism
     `SUnits K S ≃* NumberField.Units.torsion K × Multiplicative (Fin (rank K + S.card) → ℤ)`.
   - Unconditional finite generation `Monoid.FG (SUnits K S)`, `Group.FG (SUnits K S)`,
     `Module.Finite ℤ (Additive (SUnits K S))`, exact rank
     `Module.finrank ℤ (Additive (SUnits K S)) = NumberField.Units.rank K + S.card`,
     and unconditional finiteness & exact order formula
     `Nat.card (SUnitsQuot K S m) = Nat.gcd (torsionOrder K) m * m ^ (rank K + S.card)`.
3. **Concrete Global Kummer Selmer Group `K(S, m)` & Exact Unit–Class Short Exact Sequence**:
   - `KummerSelmer K S m` (Mathlib's `IsDedekindDomain.selmerGroup`) with explicit characterization
     `x̄ ∈ KummerSelmer K S m ↔ ∀ v ∉ S, (m : ℤ) ∣ adicVal K v x`.
   - Exact global Kummer short exact sequence
     `1 → SUnitsQuot K S m → KummerSelmer K S m → SClassGroupTorsion K S m → 1`.
   - Unconditional finiteness `Finite (KummerSelmer K S m)` and exact order formula
     `Nat.card (KummerSelmer K S m) = Nat.card (SUnitsQuot K S m) * Nat.card (SClassGroupTorsion K S m)`
     wired directly through `Stage2GaloisCohomology.kummer_unramified_finite`.
4. **Hilbert's Theorem 90 & Concrete Galois Kummer Isomorphism `H¹(Gal(L/K), μ_m(L))`**:
   - `hilbert90_cocycle_eq_coboundary` and `hilbert90_H1_subsingleton` for every finite Galois
     extension `L/K`.
   - Concrete Kummer homomorphism `kummerMap K L m : Additive (KummerDomain K L m) →+ H¹(Gal(L/K), μ_m(L))`,
     with injectivity (`kummer_map_injective`), surjectivity (`kummer_map_surjective`), and full
     additive isomorphism `kummerEquivH1`.
5. **Bridge to `Stage2GaloisCohomology` & Global Unramified-Outside-`S` Selmer Finiteness**:
   - Concrete unramified-outside-`S` cohomology subgroup `H1Unram K L S m` with explicit upper bound
     `Nat.card (H1Unram K L S m) ≤ Nat.card (KummerSelmer K S m)`.
   - Direct wiring into `Stage2GaloisCohomology.global_selmer_unramified_outside_S_finite` via
     `KummerSelmer L S_L m` and `KummerUnramGal L S_L m`.

Zero `sorry`, zero custom `axiom`s.
-/

noncomputable section

open scoped BigOperators
open Finset IsDedekindDomain RHDirect.Stage2GaloisCohomology

namespace RHDirect.Stage5NumberFieldCohom

/-! ## Section 1: Concrete `S`-Integers, `S`-Units, `v`-adic Valuation & `S`-Class Group -/

section SUnitsAndClassGroup

variable (K : Type*) [Field K] [NumberField K]

/-- Abbreviation for the ring of integers `𝒪_K` of a number field `K`. -/
abbrev OK : Type _ := NumberField.RingOfIntegers K

/-- Abbreviation for a finite place (height-one prime spectrum) of `𝒪_K`. -/
abbrev Place : Type _ := IsDedekindDomain.HeightOneSpectrum (OK K)

/-- Concrete `S`-integers `𝒪_{K,S} = {x ∈ K | ∀ v ∉ S, v(x) ≤ 1}` as a subalgebra of `K`. -/
abbrev SIntegers (S : Finset (Place K)) : Subalgebra (OK K) K :=
  (S : Set (Place K)).integer K

/-- Concrete `S`-units `𝒪_{K,S}ˣ = {x ∈ Kˣ | ∀ v ∉ S, v(x) = 1}` as a subgroup of `Kˣ`. -/
abbrev SUnits (S : Finset (Place K)) : Subgroup Kˣ :=
  (S : Set (Place K)).unit K

/-- Explicit membership criterion for `SUnits K S`. -/
theorem mem_sUnits_iff (S : Finset (Place K)) (x : Kˣ) :
    x ∈ SUnits K S ↔ ∀ v : Place K, v ∉ S → v.valuation K (x : K) = 1 := by
  change x ∈ ((S : Set (Place K)).unit K : Set Kˣ) ↔ _
  rw [Set.coe_unit]
  simp

/-- The prime fractional ideal `(v.asIdeal : FractionalIdeal (nonZeroDivisors (OK K)) K)ˣ`. -/
def primeFracIdeal (v : Place K) : (FractionalIdeal (nonZeroDivisors (OK K)) K)ˣ :=
  FractionalIdeal.mk0 K ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩

theorem coe_primeFracIdeal (v : Place K) :
    (primeFracIdeal K v : FractionalIdeal (nonZeroDivisors (OK K)) K) =
      (v.asIdeal : FractionalIdeal (nonZeroDivisors (OK K)) K) :=
  FractionalIdeal.coe_mk0 K ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩

/-- The ideal class `[v]` in `ClassGroup (𝒪_K)` of a finite place `v`. -/
def mkPrimeClass (v : Place K) : ClassGroup (OK K) :=
  ClassGroup.mk0 ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩

theorem classGroup_mk_primeFracIdeal (v : Place K) :
    ClassGroup.mk K (primeFracIdeal K v) = mkPrimeClass K v :=
  ClassGroup.mk_mk0 K ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩

/-- The subgroup of `ClassGroup (𝒪_K)` generated by the classes of primes in `S`. -/
def SClassSubgroup (S : Finset (Place K)) : Subgroup (ClassGroup (OK K)) :=
  Subgroup.closure ((S : Set (Place K)).image (mkPrimeClass K))

/-- Concrete **`S`-Class Group** `Cl_S(K) := ClassGroup (𝒪_K) ⧸ ⟨[v] : v ∈ S⟩`. -/
abbrev SClassGroup (S : Finset (Place K)) : Type _ :=
  ClassGroup (OK K) ⧸ SClassSubgroup K S

/-- The `m`-torsion subgroup `Cl_S(K)[m] = {c ∈ Cl_S(K) | c ^ m = 1}`. -/
def SClassGroupTorsion (S : Finset (Place K)) (m : ℕ) : Subgroup (SClassGroup K S) :=
  (powMonoidHom m).ker

@[simp]
theorem mem_sClassGroupTorsion_iff (S : Finset (Place K)) (m : ℕ) (c : SClassGroup K S) :
    c ∈ SClassGroupTorsion K S m ↔ c ^ m = 1 :=
  Iff.rfl

/-- **Unconditional Finiteness of the `S`-Class Group `Cl_S(K)`** for every number field `K`
and every finite set of places `S`. -/
instance sClassGroup_finite (S : Finset (Place K)) : Finite (SClassGroup K S) :=
  Finite.of_surjective _ (QuotientGroup.mk'_surjective (SClassSubgroup K S))

/-- **Exact Divisibility `|Cl_S(K)| ∣ |Cl(K)|`** for every number field `K` and finite set `S`. -/
theorem card_sClassGroup_dvd (S : Finset (Place K)) :
    Nat.card (SClassGroup K S) ∣ Nat.card (ClassGroup (OK K)) := by
  have h := Subgroup.card_mul_index (SClassSubgroup K S)
  exact ⟨Nat.card (SClassSubgroup K S), by rw [← h, mul_comm]; rfl⟩

/-- **Unconditional Finiteness of `Cl_S(K)[m]`**. -/
instance sClassGroupTorsion_finite (S : Finset (Place K)) (m : ℕ) :
    Finite (SClassGroupTorsion K S m) :=
  Subtype.finite

/-- Exact divisibility `|Cl_S(K)[m]| ∣ |Cl_S(K)|`. -/
theorem card_sClassGroupTorsion_dvd (S : Finset (Place K)) (m : ℕ) :
    Nat.card (SClassGroupTorsion K S m) ∣ Nat.card (SClassGroup K S) :=
  Subgroup.card_subgroup_dvd_card (SClassGroupTorsion K S m)

/-- Helper: a fractional ideal unit with trivial class in `ClassGroup (𝒪_K)` equals
`toPrincipalIdeal (OK K) K x` for some `x : Kˣ`. -/
theorem exists_toPrincipalIdeal_of_classGroup_mk_eq_one
    {I : (FractionalIdeal (nonZeroDivisors (OK K)) K)ˣ}
    (hI : ClassGroup.mk K I = 1) :
    ∃ x : Kˣ, I = toPrincipalIdeal (OK K) K x := by
  obtain ⟨α, hα⟩ := (ClassGroup.mk_eq_one_iff).mp hI
  have hspan : (I : FractionalIdeal (nonZeroDivisors (OK K)) K) =
      FractionalIdeal.spanSingleton (nonZeroDivisors (OK K)) α := by
    apply FractionalIdeal.coeToSubmodule_injective
    dsimp only
    rw [FractionalIdeal.coe_spanSingleton]
    exact hα
  have hα0 : α ≠ 0 := by
    intro h0
    rw [h0, FractionalIdeal.spanSingleton_zero] at hspan
    exact I.ne_zero hspan
  refine ⟨Units.mk0 α hα0, Units.ext ?_⟩
  rw [coe_toPrincipalIdeal, Units.val_mk0]
  exact hspan

/-- Helper: `ClassGroup.mk K (toPrincipalIdeal (OK K) K x) = 1`. -/
theorem classGroup_mk_toPrincipalIdeal (x : Kˣ) :
    ClassGroup.mk K (toPrincipalIdeal (OK K) K x) = 1 := by
  rw [ClassGroup.mk_eq_one_iff]
  refine ⟨(x : K), ?_⟩
  rw [← FractionalIdeal.coe_spanSingleton (nonZeroDivisors (OK K))]
  exact congrArg (fun I : FractionalIdeal (nonZeroDivisors (OK K)) K => (I : Submodule (OK K) K))
    (coe_toPrincipalIdeal x)

/-- The concrete additive `v`-adic valuation `ord_v : Kˣ → ℤ`, defined as the exponent of `v` in
the fractional ideal factorization of `(x)`. -/
def adicVal (v : Place K) (x : Kˣ) : ℤ :=
  FractionalIdeal.count K v (FractionalIdeal.spanSingleton (nonZeroDivisors (OK K)) (x : K))

theorem adicVal_eq_count_toPrincipalIdeal (v : Place K) (x : Kˣ) :
    adicVal K v x =
      FractionalIdeal.count K v
        (toPrincipalIdeal (OK K) K x : FractionalIdeal (nonZeroDivisors (OK K)) K) := by
  rw [coe_toPrincipalIdeal, adicVal]

@[simp]
theorem adicVal_one (v : Place K) : adicVal K v 1 = 0 := by
  rw [adicVal, Units.val_one, FractionalIdeal.spanSingleton_one, FractionalIdeal.count_one]

theorem adicVal_mul (v : Place K) (x y : Kˣ) :
    adicVal K v (x * y) = adicVal K v x + adicVal K v y := by
  unfold adicVal
  rw [Units.val_mul, ← FractionalIdeal.spanSingleton_mul_spanSingleton]
  exact FractionalIdeal.count_mul K v
    (FractionalIdeal.spanSingleton_ne_zero_iff.mpr x.ne_zero)
    (FractionalIdeal.spanSingleton_ne_zero_iff.mpr y.ne_zero)

theorem adicVal_inv (v : Place K) (x : Kˣ) :
    adicVal K v x⁻¹ = -adicVal K v x := by
  have h := adicVal_mul K v x x⁻¹
  rw [mul_inv_cancel, adicVal_one] at h
  omega

theorem adicVal_pow (v : Place K) (x : Kˣ) (n : ℕ) :
    adicVal K v (x ^ n) = n * adicVal K v x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, adicVal_mul, ih, Nat.cast_add, Nat.cast_one]
    ring

theorem adicVal_zpow (v : Place K) (x : Kˣ) (n : ℤ) :
    adicVal K v (x ^ n) = n * adicVal K v x := by
  cases n with
  | ofNat n =>
    simp only [Int.ofNat_eq_natCast, zpow_natCast, adicVal_pow]
  | negSucc n =>
    rw [zpow_negSucc, adicVal_inv, adicVal_pow, Int.negSucc_eq]
    push_cast
    ring

/-- The additive `v`-adic valuation as a group homomorphism `Kˣ →* Multiplicative ℤ`. -/
def adicValHom (v : Place K) : Kˣ →* Multiplicative ℤ where
  toFun x := Multiplicative.ofAdd (adicVal K v x)
  map_one' := by simp [adicVal_one]
  map_mul' x y := by simp [adicVal_mul]

/-- Exact sign relation between `adicVal K v x` and Mathlib's `v.valuationOfNeZero x`:
`v.valuationOfNeZero x = Multiplicative.ofAdd (-adicVal K v x)`. -/
theorem valuationOfNeZero_eq_adicVal (v : Place K) (x : Kˣ) :
    v.valuationOfNeZero x = Multiplicative.ofAdd (-adicVal K v x) := by
  have h1 : v.valuationOfNeZero x = v.valuationOfNeZeroToFun x := rfl
  rw [h1, HeightOneSpectrum.valuationOfNeZeroToFun.eq_1]
  have hsec := IsLocalization.sec_spec (nonZeroDivisors (OK K)) (x : K)
  set a := (IsLocalization.sec (nonZeroDivisors (OK K)) (x : K)).1
  set s := (IsLocalization.sec (nonZeroDivisors (OK K)) (x : K)).2
  have hs0 : (algebraMap (OK K) K) (s : OK K) ≠ 0 := by
    intro h0
    have hs_ne : (s : OK K) ≠ 0 := nonZeroDivisors.ne_zero s.2
    exact hs_ne (IsFractionRing.injective (OK K) K (by rw [h0, map_zero]))
  have hx_eq : (x : K) = ((algebraMap (OK K) K) (s : OK K))⁻¹ * (algebraMap (OK K) K) a := by
    apply mul_left_cancel₀ hs0
    rw [mul_comm _ (x : K), hsec, ← mul_assoc, mul_inv_cancel₀ hs0, one_mul]
  have hspan :
      FractionalIdeal.spanSingleton (nonZeroDivisors (OK K)) (x : K) =
        FractionalIdeal.spanSingleton (nonZeroDivisors (OK K)) ((algebraMap (OK K) K) (s : OK K))⁻¹ *
          ((Ideal.span {a} : Ideal (OK K)) : FractionalIdeal (nonZeroDivisors (OK K)) K) := by
    rw [hx_eq, ← FractionalIdeal.spanSingleton_mul_spanSingleton,
      FractionalIdeal.coeIdeal_span_singleton]
  have hcount :
      adicVal K v x =
        ↑((Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {a})).factors) -
          ↑((Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {(s : OK K)})).factors) := by
    unfold adicVal
    exact FractionalIdeal.count_well_defined K v
      (FractionalIdeal.spanSingleton_ne_zero_iff.mpr x.ne_zero) hspan
  rw [hcount]
  congr 1
  ring

theorem adicVal_eq_neg_toAdd_valuationOfNeZero (v : Place K) (x : Kˣ) :
    adicVal K v x = -Multiplicative.toAdd (v.valuationOfNeZero x) := by
  rw [valuationOfNeZero_eq_adicVal]
  simp

theorem adicVal_eq_zero_iff_valuation_eq_one (v : Place K) (x : Kˣ) :
    adicVal K v x = 0 ↔ v.valuation K (x : K) = 1 := by
  rw [← HeightOneSpectrum.valuationOfNeZero_eq v x, valuationOfNeZero_eq_adicVal]
  constructor
  · intro h
    rw [h, neg_zero]
    rfl
  · intro h
    have h1 : (Multiplicative.ofAdd (-adicVal K v x) : Multiplicative ℤ) = 1 :=
      WithZero.coe_inj.mp h
    have h2 : -adicVal K v x = 0 := by simpa using congrArg Multiplicative.toAdd h1
    omega

theorem adicVal_finite_support (x : Kˣ) :
    ∀ᶠ v : Place K in Filter.cofinite, adicVal K v x = 0 :=
  FractionalIdeal.finite_factors (FractionalIdeal.spanSingleton (nonZeroDivisors (OK K)) (x : K))

theorem adicVal_unit_eq_zero (v : Place K) (u : (OK K)ˣ) :
    adicVal K v (Units.map (algebraMap (OK K) K : OK K →* K) u) = 0 := by
  rw [adicVal_eq_neg_toAdd_valuationOfNeZero, HeightOneSpectrum.valuation_of_unit_eq]
  simp

/-- Helper: every element of `SClassSubgroup K S` is a finite `ℤ`-product of `mkPrimeClass K v`
over `v ∈ S`. -/
theorem mem_sClassSubgroup_iff_exists_prod (S : Finset (Place K)) (c : ClassGroup (OK K)) :
    c ∈ SClassSubgroup K S ↔ ∃ e : Place K → ℤ, c = ∏ v ∈ S, mkPrimeClass K v ^ e v := by
  classical
  let φ : (S → Multiplicative ℤ) →* ClassGroup (OK K) :=
    { toFun := fun f => ∏ v ∈ S.attach, mkPrimeClass K v.1 ^ Multiplicative.toAdd (f v)
      map_one' := by simp
      map_mul' := fun f g => by
        rw [← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun v _ => ?_
        change mkPrimeClass K v.1 ^ (Multiplicative.toAdd (f v) + Multiplicative.toAdd (g v)) = _
        rw [zpow_add] }
  have hrange : φ.range = SClassSubgroup K S := by
    apply le_antisymm
    · rintro _ ⟨f, rfl⟩
      refine Subgroup.prod_mem _ fun v _ => Subgroup.zpow_mem _ ?_ _
      exact Subgroup.subset_closure ⟨v.1, v.2, rfl⟩
    · rw [SClassSubgroup, Subgroup.closure_le]
      rintro _ ⟨v, hv, rfl⟩
      refine ⟨fun w : S => if w.1 = v then Multiplicative.ofAdd (1 : ℤ) else 1, ?_⟩
      change ∏ w ∈ S.attach, mkPrimeClass K w.1 ^
          Multiplicative.toAdd (if w.1 = v then Multiplicative.ofAdd (1 : ℤ) else 1) =
        mkPrimeClass K v
      rw [Finset.prod_eq_single (⟨v, hv⟩ : S)]
      · simp
      · intro w _ hw
        have hne : w.1 ≠ v := fun h => hw (Subtype.ext h)
        simp [hne]
      · intro h; exact absurd (Finset.mem_attach S ⟨v, hv⟩) h
  constructor
  · intro hc
    rw [← hrange] at hc
    obtain ⟨f, rfl⟩ := hc
    refine ⟨fun v => if hv : v ∈ S then Multiplicative.toAdd (f ⟨v, hv⟩) else 0, ?_⟩
    change ∏ v ∈ S.attach, mkPrimeClass K v.1 ^ Multiplicative.toAdd (f v) = _
    rw [← Finset.prod_attach S
      (fun v => mkPrimeClass K v ^ (if hv : v ∈ S then Multiplicative.toAdd (f ⟨v, hv⟩) else 0))]
    refine Finset.prod_congr rfl fun v _ => ?_
    simp [v.2]
  · rintro ⟨e, rfl⟩
    refine Subgroup.prod_mem _ fun v hv => Subgroup.zpow_mem _ ?_ _
    exact Subgroup.subset_closure ⟨v, hv, rfl⟩

/-- Two units of `FractionalIdeal (nonZeroDivisors (OK K)) K` with identical `FractionalIdeal.count`
at all finite places `v : Place K` are equal. -/
theorem fracIdeal_units_ext_count
    {I J : (FractionalIdeal (nonZeroDivisors (OK K)) K)ˣ}
    (h : ∀ v : Place K, FractionalIdeal.count K v (I : FractionalIdeal _ K) =
      FractionalIdeal.count K v (J : FractionalIdeal _ K)) :
    I = J := by
  apply Units.ext
  have hI0 : (I : FractionalIdeal (nonZeroDivisors (OK K)) K) ≠ 0 := I.ne_zero
  have hJ0 : (J : FractionalIdeal (nonZeroDivisors (OK K)) K) ≠ 0 := J.ne_zero
  rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' K hI0,
    ← FractionalIdeal.finprod_heightOneSpectrum_factorization' K hJ0]
  congr 1
  funext v
  rw [h v]

/-- `FractionalIdeal.count` on a finite product of `primeFracIdeal K v ^ e v` over `S` at `w ∈ S`. -/
theorem count_finset_prod_primeFracIdeal_mem (S : Finset (Place K)) (e : Place K → ℤ)
    {w : Place K} (hw : w ∈ S) :
    FractionalIdeal.count K w
      ((∏ v ∈ S, primeFracIdeal K v ^ e v : (FractionalIdeal (nonZeroDivisors (OK K)) K)ˣ) :
        FractionalIdeal (nonZeroDivisors (OK K)) K) = e w := by
  classical
  have hcoe :
      ((∏ v ∈ S, primeFracIdeal K v ^ e v : (FractionalIdeal (nonZeroDivisors (OK K)) K)ˣ) :
        FractionalIdeal (nonZeroDivisors (OK K)) K) =
      ∏ v ∈ S, ((v.asIdeal : FractionalIdeal (nonZeroDivisors (OK K)) K) ^ e v) := by
    rw [← Units.coeHom_apply, map_prod]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [Units.coeHom_apply, Units.val_zpow_eq_zpow_val, coe_primeFracIdeal]
  rw [hcoe, FractionalIdeal.count_prod K w S _ (fun v _ =>
    zpow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.mpr v.ne_bot))]
  rw [Finset.sum_eq_single w]
  · rw [FractionalIdeal.count_zpow, FractionalIdeal.count_self, mul_one]
  · intro v _ hvw
    rw [FractionalIdeal.count_zpow, FractionalIdeal.count_maximal_coprime K w hvw, mul_zero]
  · intro h; exact absurd hw h

/-- `FractionalIdeal.count` on a finite product of `primeFracIdeal K v ^ e v` over `S` at `w ∉ S`. -/
theorem count_finset_prod_primeFracIdeal_not_mem (S : Finset (Place K)) (e : Place K → ℤ)
    {w : Place K} (hw : w ∉ S) :
    FractionalIdeal.count K w
      ((∏ v ∈ S, primeFracIdeal K v ^ e v : (FractionalIdeal (nonZeroDivisors (OK K)) K)ˣ) :
        FractionalIdeal (nonZeroDivisors (OK K)) K) = 0 := by
  classical
  have hcoe :
      ((∏ v ∈ S, primeFracIdeal K v ^ e v : (FractionalIdeal (nonZeroDivisors (OK K)) K)ˣ) :
        FractionalIdeal (nonZeroDivisors (OK K)) K) =
      ∏ v ∈ S, ((v.asIdeal : FractionalIdeal (nonZeroDivisors (OK K)) K) ^ e v) := by
    rw [← Units.coeHom_apply, map_prod]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [Units.coeHom_apply, Units.val_zpow_eq_zpow_val, coe_primeFracIdeal]
  rw [hcoe, FractionalIdeal.count_prod K w S _ (fun v _ =>
    zpow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.mpr v.ne_bot))]
  refine Finset.sum_eq_zero fun v hv => ?_
  have hvw : v ≠ w := fun h => hw (h ▸ hv)
  rw [FractionalIdeal.count_zpow, FractionalIdeal.count_maximal_coprime K w hvw, mul_zero]

/-- Helper: building a fractional ideal unit with prescribed finitely supported exponents `e : Place K → ℤ`. -/
def fracIdealOfExps (e : Place K → ℤ) : (FractionalIdeal (nonZeroDivisors (OK K)) K)ˣ :=
  ∏ᶠ v : Place K, primeFracIdeal K v ^ e v

/-- `FractionalIdeal.count` of `fracIdealOfExps K e` equals `e w` when `e` is finitely supported. -/
theorem count_fracIdealOfExps (e : Place K → ℤ)
    (hfin : ∀ᶠ v : Place K in Filter.cofinite, e v = 0) (w : Place K) :
    FractionalIdeal.count K w
      (fracIdealOfExps K e : FractionalIdeal (nonZeroDivisors (OK K)) K) = e w := by
  classical
  have hsupp : (Function.mulSupport fun v : Place K => primeFracIdeal K v ^ e v).Finite := by
    refine Set.Finite.subset hfin ?_
    intro v hv
    change e v ≠ 0
    intro h0
    apply hv
    change primeFracIdeal K v ^ e v = 1
    rw [h0, zpow_zero]
  set T : Finset (Place K) := hsupp.toFinset
  have heq : fracIdealOfExps K e = ∏ v ∈ T, primeFracIdeal K v ^ e v := by
    unfold fracIdealOfExps
    exact finprod_eq_prod_of_mulSupport_toFinset_subset _ hsupp (Finset.Subset.refl _)
  rw [heq]
  by_cases hw : w ∈ T
  · exact count_finset_prod_primeFracIdeal_mem K T e hw
  · rw [count_finset_prod_primeFracIdeal_not_mem K T e hw]
    have hnot : w ∉ Function.mulSupport fun v : Place K => primeFracIdeal K v ^ e v := by
      simpa [T] using hw
    have hpow1 : primeFracIdeal K w ^ e w = 1 := by simpa [Function.mem_mulSupport] using hnot
    have hcnt := congrArg (fun I : (FractionalIdeal (nonZeroDivisors (OK K)) K)ˣ =>
      FractionalIdeal.count K w (I : FractionalIdeal _ K)) hpow1
    simp only [Units.val_zpow_eq_zpow_val, coe_primeFracIdeal, Units.val_one,
      FractionalIdeal.count_zpow, FractionalIdeal.count_self, mul_one,
      FractionalIdeal.count_one] at hcnt
    exact hcnt.symm

end SUnitsAndClassGroup

/-! ## Section 2: Dirichlet's `S`-Unit Theorem & Unconditional Finiteness of `SUnits / m` -/

section DirichletSUnits

variable (K : Type*) [Field K] [NumberField K]

/-- Canonical inclusion `(𝒪_K)ˣ →* SUnits K S` of global units into `S`-units. -/
def unitsToSUnits (S : Finset (Place K)) : (OK K)ˣ →* SUnits K S where
  toFun u := ⟨Units.map (algebraMap (OK K) K : OK K →* K) u, by
    rw [mem_sUnits_iff]
    intro v _
    rw [← adicVal_eq_zero_iff_valuation_eq_one]
    exact adicVal_unit_eq_zero K v u⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' u₁ u₂ := Subtype.ext (map_mul _ u₁ u₂)

theorem unitsToSUnits_injective (S : Finset (Place K)) :
    Function.Injective (unitsToSUnits K S) := by
  intro u₁ u₂ h
  have h1 : (algebraMap (OK K) K) (u₁ : OK K) = (algebraMap (OK K) K) (u₂ : OK K) := by
    have := congrArg (fun x : SUnits K S => (x.1 : K)) h
    simpa [unitsToSUnits] using this
  exact Units.ext (IsFractionRing.injective (OK K) K h1)

/-- Valuation homomorphism `SUnits K S →* (S → Multiplicative ℤ)` recording `ord_v(x)` at `v ∈ S`. -/
def sUnitsValMap (S : Finset (Place K)) : SUnits K S →* (S → Multiplicative ℤ) where
  toFun x v := Multiplicative.ofAdd (adicVal K v.1 x.1)
  map_one' := by ext v; simp [adicVal_one]
  map_mul' x y := by ext v; simp [adicVal_mul]

/-- Additive `ℤ`-linear valuation map `Additive (SUnits K S) →ₗ[ℤ] (S → ℤ)`. -/
def sUnitsValLinear (S : Finset (Place K)) : Additive (SUnits K S) →ₗ[ℤ] (S → ℤ) :=
  AddMonoidHom.toIntLinearMap
    { toFun := fun x v => adicVal K v.1 (Additive.toMul x).1
      map_zero' := by ext v; exact adicVal_one K v.1
      map_add' := fun x y => by ext v; exact adicVal_mul K v.1 (Additive.toMul x).1 (Additive.toMul y).1 }

/-- **Exact Unit–Valuation Sequence**: `ker(sUnitsValMap) = range(unitsToSUnits)`, i.e.,
`1 → (𝒪_K)ˣ → 𝒪_{K,S}ˣ → ℤ^S` is exact! -/
theorem ker_sUnitsValMap_eq_range (S : Finset (Place K)) :
    (sUnitsValMap K S).ker = (unitsToSUnits K S).range := by
  ext x
  simp only [MonoidHom.mem_ker, MonoidHom.mem_range]
  constructor
  · intro hx
    have hall : ∀ v : Place K, v.valuation K (x.1 : K) = 1 := by
      intro v
      by_cases hv : v ∈ S
      · rw [← adicVal_eq_zero_iff_valuation_eq_one]
        have hxv := congrFun hx ⟨v, hv⟩
        simpa [sUnitsValMap] using congrArg Multiplicative.toAdd hxv
      · exact (mem_sUnits_iff K S x.1).mp x.2 v hv
    have hx_empty : (x.1 : K) ∈ (∅ : Set (Place K)).integer K := by
      change (x.1 : K) ∈ ((∅ : Set (Place K)).integer K : Set K)
      rw [Set.coe_integer]
      intro v _
      rw [hall v]
    have hxinv_empty : ((x.1⁻¹ : Kˣ) : K) ∈ (∅ : Set (Place K)).integer K := by
      change ((x.1⁻¹ : Kˣ) : K) ∈ ((∅ : Set (Place K)).integer K : Set K)
      rw [Set.coe_integer]
      intro v _
      have hinv : v.valuation K ((x.1⁻¹ : Kˣ) : K) = (v.valuation K (x.1 : K))⁻¹ := by
        rw [Units.val_inv_eq_inv_val, map_inv₀]
      rw [hinv, hall v, inv_one]
    rw [IsDedekindDomain.integer_empty] at hx_empty hxinv_empty
    obtain ⟨a, ha⟩ := Algebra.mem_bot.mp hx_empty
    obtain ⟨b, hb⟩ := Algebra.mem_bot.mp hxinv_empty
    have hab : a * b = 1 := by
      apply IsFractionRing.injective (OK K) K
      rw [map_mul, map_one, ha, hb, Units.val_inv_eq_inv_val, mul_inv_cancel₀ x.1.ne_zero]
    have hba : b * a = 1 := mul_comm a b ▸ hab
    refine ⟨⟨a, b, hab, hba⟩, ?_⟩
    apply Subtype.ext
    apply Units.ext
    simpa [unitsToSUnits] using ha
  · rintro ⟨u, rfl⟩
    ext v
    change Multiplicative.ofAdd (adicVal K v.1 (Units.map (algebraMap (OK K) K : OK K →* K) u)) = 1
    rw [adicVal_unit_eq_zero]
    rfl

/-- Exactness of the additive `ℤ`-linear unit–valuation sequence:
`ker(sUnitsValLinear K S) = range(unitsToSUnits)`! -/
theorem ker_sUnitsValLinear_eq_range (S : Finset (Place K)) :
    LinearMap.ker (sUnitsValLinear K S) =
      LinearMap.range (AddMonoidHom.toIntLinearMap (MonoidHom.toAdditive (unitsToSUnits K S))) := by
  ext x
  simp only [LinearMap.mem_ker, LinearMap.mem_range, AddMonoidHom.coe_toIntLinearMap]
  have h1 : sUnitsValLinear K S x = 0 ↔ Additive.toMul x ∈ (sUnitsValMap K S).ker := by
    constructor
    · intro hx
      ext v
      have hxv : adicVal K v.1 (Additive.toMul x).1 = 0 := congrFun hx v
      change Multiplicative.ofAdd (adicVal K v.1 (Additive.toMul x).1) = 1
      rw [hxv]; rfl
    · intro hx
      ext v
      have hxv := congrFun hx v
      change adicVal K v.1 (Additive.toMul x).1 = 0
      simpa [sUnitsValMap] using congrArg Multiplicative.toAdd hxv
  rw [h1, ker_sUnitsValMap_eq_range, MonoidHom.mem_range]
  constructor
  · rintro ⟨u, hu⟩
    exact ⟨Additive.ofMul u, congrArg Additive.ofMul hu⟩
  · rintro ⟨u, hu⟩
    exact ⟨Additive.toMul u, congrArg Additive.toMul hu⟩

/-- **Existence of an `S`-unit with pure `v`-valuation equal to the class number `h_K`**:
for every finite place `v ∈ S`, there exists `π ∈ SUnits K S` with `ord_v(π) = h_K` and
`ord_w(π) = 0` for all `w ≠ v`. -/
theorem exists_sUnit_single_val (S : Finset (Place K)) (v : S) :
    ∃ π : SUnits K S,
      adicVal K v.1 π.1 = (Fintype.card (ClassGroup (OK K)) : ℤ) ∧
        ∀ w : Place K, w ≠ v.1 → adicVal K w π.1 = 0 := by
  classical
  let h : ℕ := Fintype.card (ClassGroup (OK K))
  have hpow1 : ClassGroup.mk K (primeFracIdeal K v.1 ^ h) = 1 := by
    rw [map_pow, classGroup_mk_primeFracIdeal]
    exact pow_card_eq_one
  obtain ⟨x, hx⟩ := exists_toPrincipalIdeal_of_classGroup_mk_eq_one K hpow1
  have hcount : ∀ w : Place K, adicVal K w x = if w = v.1 then (h : ℤ) else 0 := by
    intro w
    rw [adicVal_eq_count_toPrincipalIdeal, ← hx, Units.val_pow_eq_pow_val, coe_primeFracIdeal,
      FractionalIdeal.count_pow]
    by_cases hw : w = v.1
    · subst hw
      rw [if_pos rfl, FractionalIdeal.count_self, mul_one]
    · rw [if_neg hw, FractionalIdeal.count_maximal_coprime K w (Ne.symm hw), mul_zero]
  have hxS : x ∈ SUnits K S := by
    rw [mem_sUnits_iff]
    intro w hw
    rw [← adicVal_eq_zero_iff_valuation_eq_one, hcount w,
      if_neg (fun (heq : w = v.1) => hw (heq ▸ v.2))]
  refine ⟨⟨x, hxS⟩, ?_, ?_⟩
  · rw [hcount v.1, if_pos rfl]
  · intro w hw
    rw [hcount w, if_neg hw]

/-- Helper: any submodule `N ≤ (ι → ℤ)` containing `h • ⊤` (for `h > 0`) is free of rank `|ι|`. -/
private theorem finrank_submodule_of_smul_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (N : Submodule ℤ (ι → ℤ)) {h : ℕ} (hh : 0 < h)
    (hsub : ∀ i : ι, Pi.single (M := fun _ => ℤ) i (h : ℤ) ∈ N) :
    Module.finrank ℤ N = Fintype.card ι := by
  let b := Pi.basisFun ℤ ι
  let ⟨n, bN⟩ := Submodule.basisOfPid b N
  have hfinN : Module.finrank ℤ N = n := by simpa using Module.finrank_eq_card_basis bN
  have hle1 : n ≤ Fintype.card ι := by
    rw [← hfinN]
    calc Module.finrank ℤ N
        ≤ Module.finrank ℤ (ι → ℤ) := Submodule.finrank_le N
      _ = Fintype.card ι := Module.finrank_pi ℤ
  let f : (ι → ℤ) →ₗ[ℤ] N :=
    { toFun := fun v => ⟨(h : ℤ) • v, by
        have hv : (h : ℤ) • v = ∑ i : ι, v i • Pi.single (M := fun _ => ℤ) i (h : ℤ) := by
          ext j
          simp [Finset.sum_apply, Pi.single_apply, mul_comm]
        rw [hv]
        exact N.sum_mem fun i _ => N.smul_mem (v i) (hsub i)⟩
      map_add' := fun u v => Subtype.ext (smul_add (h : ℤ) u v)
      map_smul' := fun c v => Subtype.ext (by
        simp only [RingHom.id_apply]
        ext i; simp; ring) }
  have hfinj : Function.Injective f := by
    intro u v huv
    have h1 : (h : ℤ) • u = (h : ℤ) • v := congrArg Subtype.val huv
    ext i
    have hi : (h : ℤ) * u i = (h : ℤ) * v i := congrFun h1 i
    have hh0 : (h : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr hh.ne'
    exact mul_left_cancel₀ hh0 hi
  have hle2 : Fintype.card ι ≤ n := by
    have hrank_le : Module.rank ℤ (ι → ℤ) ≤ Module.rank ℤ N :=
      LinearMap.rank_le_of_injective f hfinj
    have h1 : Module.rank ℤ (ι → ℤ) = (Fintype.card ι : Cardinal) := by
      rw [rank_fun']
    have h2 : Module.rank ℤ N = (n : Cardinal) := by
      have hlift := bN.equivFun.lift_rank_eq
      rw [rank_fun', Fintype.card_fin] at hlift
      simpa using hlift
    rw [h1, h2] at hrank_le
    exact Nat.cast_le.mp hrank_le
  omega

/-- The image of `sUnitsValLinear K S` inside `S → ℤ` is a free `ℤ`-module of rank `S.card`. -/
def sUnitsValRangeBasis (S : Finset (Place K)) :
    Module.Basis (Fin S.card) ℤ (LinearMap.range (sUnitsValLinear K S)) := by
  classical
  let b := Pi.basisFun ℤ S
  let N := LinearMap.range (sUnitsValLinear K S)
  let ⟨n, bN⟩ := Submodule.basisOfPid b N
  have hn : n = S.card := by
    have h1 : Module.finrank ℤ N = n := by simpa using Module.finrank_eq_card_basis bN
    have h2 : Module.finrank ℤ N = Fintype.card S :=
      finrank_submodule_of_smul_le N (Fintype.card_pos (α := ClassGroup (OK K))) fun v => by
        obtain ⟨π, hπv, hπw⟩ := exists_sUnit_single_val K S v
        refine ⟨Additive.ofMul π, ?_⟩
        ext w
        change adicVal K w.1 π.1 = Pi.single (M := fun _ => ℤ) v (Fintype.card (ClassGroup (OK K)) : ℤ) w
        by_cases hw : w = v
        · subst hw; rw [hπv, Pi.single_eq_same]
        · rw [hπw w.1 (fun h => hw (Subtype.ext h)), Pi.single_eq_of_ne hw]
    rw [Fintype.card_coe] at h2
    omega
  exact bN.reindex (finCongr hn)

/-- Exact rank of the valuation image `im(𝒪_{K,S}ˣ → ℤ^S)`: `finrank ℤ = S.card`. -/
theorem finrank_range_sUnitsValLinear (S : Finset (Place K)) :
    Module.finrank ℤ (LinearMap.range (sUnitsValLinear K S)) = S.card := by
  have h := Module.finrank_eq_card_basis (sUnitsValRangeBasis K S)
  simpa using h

/-- Helper: splitting a `ℤ`-linear surjection `p : M →ₗ[ℤ] (Fin r → ℤ)` with `ker p = range i`
and injective `i : A →ₗ[ℤ] M` into `M ≃ₗ[ℤ] A × (Fin r → ℤ)`. -/
private def splitFreeQuotient {A M : Type*} [AddCommGroup A] [AddCommGroup M] {r : ℕ}
    (iMap : A →ₗ[ℤ] M) (p : M →ₗ[ℤ] (Fin r → ℤ))
    (hi : Function.Injective iMap)
    (hker : LinearMap.ker p = LinearMap.range iMap)
    (s : (Fin r → ℤ) →ₗ[ℤ] M)
    (hps : ∀ v : Fin r → ℤ, p (s v) = v) :
    M ≃ₗ[ℤ] A × (Fin r → ℤ) :=
  let eKer : LinearMap.ker p ≃ₗ[ℤ] A :=
    (LinearEquiv.ofEq _ _ hker).trans (LinearEquiv.ofInjective iMap hi).symm
  have hi_eKer : ∀ (x : LinearMap.ker p), iMap (eKer x) = x.1 := fun x => by
    change iMap ((LinearEquiv.ofInjective iMap hi).symm ⟨x.1, hker ▸ x.2⟩) = x.1
    have := (LinearEquiv.ofInjective iMap hi).apply_symm_apply ⟨x.1, hker ▸ x.2⟩
    exact congrArg Subtype.val this
  { toFun := fun x =>
      (eKer ⟨x - s (p x), by rw [LinearMap.mem_ker, map_sub, hps, sub_self]⟩, p x)
    invFun := fun y => iMap y.1 + s y.2
    map_add' := fun x₁ x₂ => by
      refine Prod.ext ?_ (map_add p x₁ x₂)
      dsimp only [Prod.fst_add]
      rw [← map_add]
      congr 1
      apply Subtype.ext
      simp only [Submodule.coe_add, map_add]
      abel
    map_smul' := fun c x => by
      refine Prod.ext ?_ (map_smul p c x)
      dsimp only [RingHom.id_apply, Prod.smul_fst]
      rw [← map_smul]
      congr 1
      apply Subtype.ext
      change c • x - s (p (c • x)) = c • (x - s (p x))
      rw [map_smul, map_smul, smul_sub]
    left_inv := fun x => by
      dsimp only
      rw [hi_eKer, sub_add_cancel]
    right_inv := fun ⟨u, v⟩ => by
      have hpu : p (iMap u) = 0 := by
        rw [← LinearMap.mem_ker, hker]
        exact ⟨u, rfl⟩
      have hp_uv : p (iMap u + s v) = v := by
        rw [map_add, hpu, zero_add, hps]
      refine Prod.ext ?_ hp_uv
      dsimp only
      apply hi
      rw [hi_eKer]
      change iMap u + s v - s (p (iMap u + s v)) = iMap u
      rw [hp_uv, add_sub_cancel_right] }

/-- **Exact Splitting of `Additive (SUnits K S)` over `ℤ`**:
`Additive (SUnits K S) ≃ₗ[ℤ] Additive (𝒪_K)ˣ × (Fin S.card → ℤ)`. -/
def additiveSUnitsSplitEquiv (S : Finset (Place K)) :
    Additive (SUnits K S) ≃ₗ[ℤ] Additive (OK K)ˣ × (Fin S.card → ℤ) := by
  let bN := sUnitsValRangeBasis K S
  let p : Additive (SUnits K S) →ₗ[ℤ] (Fin S.card → ℤ) :=
    bN.equivFun.toLinearMap.comp (sUnitsValLinear K S).rangeRestrict
  have hp_surj : Function.Surjective p :=
    bN.equivFun.surjective.comp (fun ⟨_, x, hx⟩ => ⟨x, Subtype.ext hx⟩)
  let s : (Fin S.card → ℤ) →ₗ[ℤ] Additive (SUnits K S) :=
    (Pi.basisFun ℤ (Fin S.card)).constr ℤ fun i => Classical.choose (hp_surj (Pi.single i 1))
  have hps : ∀ v : Fin S.card → ℤ, p (s v) = v := by
    intro v
    have hcomp : p.comp s = LinearMap.id := by
      apply (Pi.basisFun ℤ (Fin S.card)).ext
      intro i
      rw [LinearMap.comp_apply, LinearMap.id_apply, Module.Basis.constr_basis,
        Pi.basisFun_apply]
      exact Classical.choose_spec (hp_surj (Pi.single i 1))
    exact LinearMap.congr_fun hcomp v
  let iMap : Additive (OK K)ˣ →ₗ[ℤ] Additive (SUnits K S) :=
    AddMonoidHom.toIntLinearMap (MonoidHom.toAdditive (unitsToSUnits K S))
  have hi_inj : Function.Injective iMap := fun a b hab => by
    have h1 := unitsToSUnits_injective K S (show unitsToSUnits K S (Additive.toMul a) =
      unitsToSUnits K S (Additive.toMul b) from hab)
    exact Additive.toMul.injective h1
  have hker_p : LinearMap.ker p = LinearMap.range iMap := by
    ext x
    rw [LinearMap.mem_ker, ← ker_sUnitsValLinear_eq_range K S, LinearMap.mem_ker]
    change bN.equivFun ⟨sUnitsValLinear K S x, ⟨x, rfl⟩⟩ = 0 ↔ sUnitsValLinear K S x = 0
    rw [map_eq_zero_iff _ bN.equivFun.injective]
    exact Subtype.ext_iff
  exact splitFreeQuotient iMap p hi_inj hker_p s hps

/-- **Dirichlet's Unit Structure Theorem (in `Additive` form)** from Mathlib's `basisModTorsion`:
`Additive (𝒪_K)ˣ ≃ₗ[ℤ] Additive (NumberField.Units.torsion K) × (Fin (rank K) → ℤ)`. -/
def additiveUnitsSplitEquiv :
    Additive (OK K)ˣ ≃ₗ[ℤ]
      Additive (NumberField.Units.torsion K) × (Fin (NumberField.Units.rank K) → ℤ) := by
  let b := NumberField.Units.basisModTorsion K
  let q : Additive (OK K)ˣ →ₗ[ℤ] (Fin (NumberField.Units.rank K) → ℤ) :=
    b.equivFun.toLinearMap.comp
      (AddMonoidHom.toIntLinearMap (MonoidHom.toAdditive (QuotientGroup.mk' (NumberField.Units.torsion K))))
  let s : (Fin (NumberField.Units.rank K) → ℤ) →ₗ[ℤ] Additive (OK K)ˣ :=
    (Pi.basisFun ℤ (Fin (NumberField.Units.rank K))).constr ℤ fun i =>
      Additive.ofMul (NumberField.Units.fundSystem K i)
  have hqs : ∀ v : Fin (NumberField.Units.rank K) → ℤ, q (s v) = v := by
    intro v
    have hcomp : q.comp s = LinearMap.id := by
      apply (Pi.basisFun ℤ (Fin (NumberField.Units.rank K))).ext
      intro i
      rw [LinearMap.comp_apply, LinearMap.id_apply, Module.Basis.constr_basis, Pi.basisFun_apply]
      ext j
      change b.equivFun (Additive.ofMul (QuotientGroup.mk (NumberField.Units.fundSystem K i))) j =
        Pi.single (M := fun _ => ℤ) i 1 j
      rw [NumberField.Units.fundSystem_mk K i, b.equivFun_self]
      by_cases hji : j = i
      · subst hji; simp
      · simp [hji, Ne.symm hji]
    exact LinearMap.congr_fun hcomp v
  let iT : Additive (NumberField.Units.torsion K) →ₗ[ℤ] Additive (OK K)ˣ :=
    AddMonoidHom.toIntLinearMap (MonoidHom.toAdditive (NumberField.Units.torsion K).subtype)
  have hiT_inj : Function.Injective iT := fun a b hab => by
    have h1 : (Additive.toMul a : NumberField.Units.torsion K).1 =
        (Additive.toMul b : NumberField.Units.torsion K).1 := hab
    exact Additive.toMul.injective (Subtype.ext h1)
  have hker_q : LinearMap.ker q = LinearMap.range iT := by
    ext x
    rw [LinearMap.mem_ker, LinearMap.mem_range]
    change b.equivFun (Additive.ofMul (QuotientGroup.mk (Additive.toMul x))) = 0 ↔ _
    rw [map_eq_zero_iff _ b.equivFun.injective]
    change (QuotientGroup.mk (Additive.toMul x) : (OK K)ˣ ⧸ NumberField.Units.torsion K) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff]
    constructor
    · intro hx
      exact ⟨Additive.ofMul ⟨Additive.toMul x, hx⟩, rfl⟩
    · rintro ⟨t, ht⟩
      have : Additive.toMul x = (Additive.toMul t).1 := ht.symm
      rw [this]
      exact (Additive.toMul t).2
  exact splitFreeQuotient iT q hiT_inj hker_q s hqs

/-- Helper: `(Fin a → ℤ) × (Fin b → ℤ) ≃ₗ[ℤ] (Fin (a + b) → ℤ)`. -/
private def prodFinIntEquiv (a b : ℕ) :
    ((Fin a → ℤ) × (Fin b → ℤ)) ≃ₗ[ℤ] (Fin (a + b) → ℤ) where
  toFun p i := Fin.addCases p.1 p.2 i
  invFun f := (fun i => f (Fin.castAdd b i), fun j => f (Fin.natAdd a j))
  map_add' p q := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp
  map_smul' c p := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp
  left_inv p := by
    refine Prod.ext ?_ ?_ <;> funext i <;> simp
  right_inv f := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp

/-- **Dirichlet's `S`-Unit Theorem (Additive `ℤ`-Linear Form)**:
`Additive (SUnits K S) ≃ₗ[ℤ] Additive (NumberField.Units.torsion K) × (Fin (rank K + S.card) → ℤ)`. -/
def dirichletSUnitAdditiveEquiv (S : Finset (Place K)) :
    Additive (SUnits K S) ≃ₗ[ℤ]
      Additive (NumberField.Units.torsion K) × (Fin (NumberField.Units.rank K + S.card) → ℤ) :=
  (additiveSUnitsSplitEquiv K S).trans
    ((LinearEquiv.prodCongr (additiveUnitsSplitEquiv K) (LinearEquiv.refl ℤ _)).trans
      ((LinearEquiv.prodAssoc ℤ _ _ _).trans
        (LinearEquiv.prodCongr (LinearEquiv.refl ℤ _)
          (prodFinIntEquiv (NumberField.Units.rank K) S.card))))

/-- **Dirichlet's `S`-Unit Theorem (Multiplicative Form)**:
`SUnits K S ≃* NumberField.Units.torsion K × Multiplicative (Fin (rank K + S.card) → ℤ)`. -/
def dirichletSUnitEquiv (S : Finset (Place K)) :
    SUnits K S ≃*
      NumberField.Units.torsion K × Multiplicative (Fin (NumberField.Units.rank K + S.card) → ℤ) :=
  let e := (dirichletSUnitAdditiveEquiv K S).toAddEquiv
  { toFun := fun x =>
      (Additive.toMul (e (Additive.ofMul x)).1, Multiplicative.ofAdd (e (Additive.ofMul x)).2)
    invFun := fun y => Additive.toMul (e.symm (Additive.ofMul y.1, Multiplicative.toAdd y.2))
    left_inv := fun x => by
      have h := e.symm_apply_apply (Additive.ofMul x)
      exact congrArg Additive.toMul h
    right_inv := fun ⟨t, v⟩ => by
      have h := e.apply_symm_apply (Additive.ofMul t, Multiplicative.toAdd v)
      exact Prod.ext (congrArg (fun p => Additive.toMul p.1) h)
        (congrArg (fun p => Multiplicative.ofAdd p.2) h)
    map_mul' := fun x y => by
      have h := e.map_add (Additive.ofMul x) (Additive.ofMul y)
      exact Prod.ext (congrArg (fun p => Additive.toMul p.1) h)
        (congrArg (fun p => Multiplicative.ofAdd p.2) h) }

/-- **Unconditional Finite Generation of `SUnits K S`** as a `ℤ`-module. -/
instance sUnits_module_finite (S : Finset (Place K)) :
    Module.Finite ℤ (Additive (SUnits K S)) :=
  Module.Finite.equiv (additiveSUnitsSplitEquiv K S).symm

/-- Helper: `Multiplicative (Fin r → ℤ)` is finitely generated as a monoid. -/
private theorem monoid_fg_multiplicative_pi_int (r : ℕ) :
    Monoid.FG (Multiplicative (Fin r → ℤ)) := by
  classical
  let posGen : Fin r → Multiplicative (Fin r → ℤ) :=
    fun i => Multiplicative.ofAdd (Pi.single (M := fun _ => ℤ) i 1)
  let negGen : Fin r → Multiplicative (Fin r → ℤ) :=
    fun i => Multiplicative.ofAdd (Pi.single (M := fun _ => ℤ) i (-1))
  refine ⟨Finset.univ.image posGen ∪ Finset.univ.image negGen, ?_⟩
  rw [eq_top_iff]
  intro x _
  have hx : Multiplicative.toAdd x =
      ∑ i : Fin r, Multiplicative.toAdd x i • Pi.single (M := fun _ => ℤ) i (1 : ℤ) := by
    ext j; simp [Finset.sum_apply, Pi.single_apply]
  have hx_prod : x = ∏ i : Fin r, posGen i ^ Multiplicative.toAdd x i := by
    apply Multiplicative.toAdd.injective
    rw [toAdd_prod]
    conv_lhs => rw [hx]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [toAdd_zpow]
    rfl
  rw [hx_prod]
  refine Submonoid.prod_mem _ fun i _ => ?_
  cases Multiplicative.toAdd x i with
  | ofNat n =>
    rw [Int.ofNat_eq_natCast, zpow_natCast]
    refine Submonoid.pow_mem _ (Submonoid.subset_closure ?_) n
    exact Finset.mem_coe.mpr (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
  | negSucc n =>
    have hneg : posGen i ^ Int.negSucc n = negGen i ^ (n + 1) := by
      apply Multiplicative.toAdd.injective
      rw [toAdd_zpow, toAdd_pow]
      ext j
      change (Int.negSucc n : ℤ) * Pi.single (M := fun _ => ℤ) i (1 : ℤ) j =
        ((n + 1 : ℕ) : ℤ) * Pi.single (M := fun _ => ℤ) i (-1 : ℤ) j
      by_cases hj : j = i
      · subst hj; simp [Int.negSucc_eq]
      · simp [Pi.single_eq_of_ne hj]
    rw [hneg]
    refine Submonoid.pow_mem _ (Submonoid.subset_closure ?_) (n + 1)
    exact Finset.mem_coe.mpr (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)))

/-- **Unconditional Finite Generation of `SUnits K S`** as a multiplicative monoid (`Monoid.FG`). -/
instance sUnits_monoid_fg (S : Finset (Place K)) : Monoid.FG (SUnits K S) := by
  have : Monoid.FG (NumberField.Units.torsion K) := Monoid.fg_of_finite
  have : Monoid.FG (Multiplicative (Fin (NumberField.Units.rank K + S.card) → ℤ)) :=
    monoid_fg_multiplicative_pi_int _
  exact Monoid.fg_of_surjective (dirichletSUnitEquiv K S).symm.toMonoidHom
    (dirichletSUnitEquiv K S).symm.surjective

/-- **Unconditional Finite Generation of `SUnits K S`** as a group (`Group.FG`). -/
instance sUnits_group_fg (S : Finset (Place K)) : Group.FG (SUnits K S) :=
  Group.fg_iff_monoid_fg.mpr (sUnits_monoid_fg K S)

/-- Helper: `Module.rank ℤ (T × (Fin n → ℤ)) = n` for any finite `ℤ`-module `T`. -/
private theorem rank_prod_finite_free.{u} {T : Type u} [AddCommGroup T] [Finite T] (n : ℕ) :
    Module.rank ℤ (T × (Fin n → ℤ)) = (n : Cardinal.{u}) := by
  have hge : (n : Cardinal.{u}) ≤ Module.rank ℤ (T × (Fin n → ℤ)) := by
    let v : Fin n → T × (Fin n → ℤ) := fun i => (0, Pi.single (M := fun _ => ℤ) i 1)
    have hv : LinearIndependent ℤ v := by
      rw [linearIndependent_iff']
      intro s g hg i hi
      have h2 := congrFun (congrArg Prod.snd hg) i
      simp only [Prod.snd_sum, Prod.snd_zero, Pi.zero_apply, Finset.sum_apply, v] at h2
      rw [Finset.sum_eq_single i] at h2
      · simpa using h2
      · intro j _ hji
        simp [Pi.single_eq_of_ne (Ne.symm hji)]
      · intro h; exact absurd hi h
    have hle := hv.cardinal_lift_le_rank
    simpa [Cardinal.mk_fintype, Fintype.card_fin] using hle
  have hle : Module.rank ℤ (T × (Fin n → ℤ)) ≤ (n : Cardinal.{u}) := by
    rw [Module.rank_def]
    refine ciSup_le fun ⟨s, hs⟩ => ?_
    have hs_snd : LinearIndependent ℤ (fun i : s => (i.1.2 : Fin n → ℤ)) := by
      rw [linearIndependent_iff']
      intro t g hg i hi
      let hT : ℕ := Nat.card T
      have hT_pos : 0 < hT := Nat.card_pos
      have hsum0 : ∑ j ∈ t, ((hT : ℤ) * g j) • (j.1 : T × (Fin n → ℤ)) = 0 := by
        refine Prod.ext ?_ ?_
        · rw [Prod.fst_sum, Prod.fst_zero]
          refine Finset.sum_eq_zero fun j _ => ?_
          rw [Prod.smul_fst, mul_smul]
          have hord : (hT : ℤ) • j.1.1 = 0 := by
            have hnat : hT • j.1.1 = 0 :=
              addOrderOf_dvd_iff_nsmul_eq_zero.mp (addOrderOf_dvd_natCard (x := j.1.1))
            simpa [natCast_zsmul] using hnat
          rw [smul_comm (hT : ℤ) (g j), hord, smul_zero]
        · rw [Prod.snd_sum, Prod.snd_zero]
          have : ∑ j ∈ t, (((hT : ℤ) * g j) • j.1).2 = (hT : ℤ) • ∑ j ∈ t, g j • j.1.2 := by
            rw [Finset.smul_sum]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [Prod.smul_snd, mul_smul]
          rw [this, hg, smul_zero]
      have hgi : (hT : ℤ) * g i = 0 :=
        linearIndependent_iff'.mp hs t (fun j => (hT : ℤ) * g j) hsum0 i hi
      exact (mul_eq_zero.mp hgi).resolve_left (Nat.cast_ne_zero.mpr hT_pos.ne')
    have hcard := hs_snd.cardinal_lift_le_rank
    rw [rank_fun', Fintype.card_fin] at hcard
    simpa using hcard
  exact le_antisymm hle hge

/-- **Exact Dirichlet `S`-Unit Rank Formula**:
`rk(𝒪_{K,S}ˣ) = rk((𝒪_K)ˣ) + |S|`! -/
theorem sUnits_finrank_eq (S : Finset (Place K)) :
    Module.finrank ℤ (Additive (SUnits K S)) = NumberField.Units.rank K + S.card := by
  rw [(dirichletSUnitAdditiveEquiv K S).finrank_eq]
  exact Module.finrank_eq_of_rank_eq (rank_prod_finite_free (NumberField.Units.rank K + S.card))

/-- The quotient `SUnits K S ⧸ (SUnits K S)^m` of `S`-units modulo `m`-th powers. -/
abbrev SUnitsQuot (S : Finset (Place K)) (m : ℕ) : Type _ :=
  SUnits K S ⧸ (powMonoidHom (α := SUnits K S) m).range

/-- Helper: for any finite cyclic group `C`, `Nat.card (C ⧸ C^m) = Nat.gcd (Nat.card C) m`. -/
private theorem card_quotient_pow_of_isCyclic {C : Type*} [CommGroup C] [Finite C] [IsCyclic C]
    (m : ℕ) :
    Nat.card (C ⧸ (powMonoidHom (α := C) m).range) = Nat.gcd (Nat.card C) m := by
  classical
  have := Fintype.ofFinite C
  let f : C →* C := powMonoidHom m
  have h1 : Nat.card C = Nat.card f.range * Nat.card (C ⧸ f.range) := by
    rw [← Subgroup.card_mul_index f.range]; rfl
  have h2 : Nat.card C = Nat.card f.ker * Nat.card f.range := by
    have heq := Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv
    have hlag := Subgroup.card_mul_index f.ker
    rw [← hlag, ← heq]; rfl
  have hpos : 0 < Nat.card f.range := Nat.card_pos
  have hquot_eq_ker : Nat.card (C ⧸ f.range) = Nat.card f.ker := by
    apply Nat.eq_of_mul_eq_mul_left hpos
    rw [← h1, mul_comm, ← h2]
  rw [hquot_eq_ker]
  obtain ⟨g, hg⟩ := ‹IsCyclic C›
  let n : ℕ := Nat.card C
  have hn_pos : 0 < n := Nat.card_pos
  have hord : orderOf g = n := orderOf_eq_card_of_forall_mem_zpowers hg
  let d : ℕ := Nat.gcd n m
  have hd_pos : 0 < d := Nat.gcd_pos_of_pos_left m hn_pos
  have hd_dvd_n : d ∣ n := Nat.gcd_dvd_left n m
  let h : C := g ^ (n / d)
  have hker_eq : f.ker = Subgroup.zpowers h := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_zpowers_iff]
    obtain ⟨k, rfl⟩ := hg x
    change (g ^ k) ^ m = 1 ↔ ∃ j : ℤ, h ^ j = g ^ k
    rw [← zpow_natCast, ← zpow_mul, ← orderOf_dvd_iff_zpow_eq_one, hord]
    constructor
    · intro hdvd
      have hd_dvd_m : d ∣ m := Nat.gcd_dvd_right n m
      have hcop : Nat.Coprime (n / d) (m / d) := Nat.coprime_div_gcd_div_gcd hd_pos
      have hn_eq : (n : ℤ) = (d : ℤ) * ((n / d : ℕ) : ℤ) := by
        exact_mod_cast (Nat.mul_div_cancel' hd_dvd_n).symm
      have hm_eq : (m : ℤ) = (d : ℤ) * ((m / d : ℕ) : ℤ) := by
        exact_mod_cast (Nat.mul_div_cancel' hd_dvd_m).symm
      have hdiv1 : ((n / d : ℕ) : ℤ) ∣ k * ((m / d : ℕ) : ℤ) := by
        rw [hn_eq, hm_eq] at hdvd
        have hd0 : (d : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr hd_pos.ne'
        obtain ⟨c, hc⟩ := hdvd
        refine ⟨c, ?_⟩
        apply mul_left_cancel₀ hd0
        linarith
      have hcopZ : IsCoprime ((n / d : ℕ) : ℤ) ((m / d : ℕ) : ℤ) :=
        Int.isCoprime_iff_gcd_eq_one.mpr (by rw [Int.gcd_natCast_natCast]; exact hcop)
      have hdiv2 : ((n / d : ℕ) : ℤ) ∣ k := hcopZ.dvd_of_dvd_mul_right hdiv1
      obtain ⟨j, hj⟩ := hdiv2
      refine ⟨j, ?_⟩
      change (g ^ (n / d)) ^ j = g ^ k
      rw [← zpow_natCast, ← zpow_mul, hj]
    · rintro ⟨j, hj⟩
      have h1 : g ^ ((((n / d : ℕ) : ℤ) * j) - k) = 1 := by
        rw [zpow_sub, zpow_mul, zpow_natCast]
        change h ^ j * (g ^ k)⁻¹ = 1
        rw [hj, mul_inv_cancel]
      have hdvd_diff : (n : ℤ) ∣ ((n / d : ℕ) : ℤ) * j - k := by
        have h0 : (orderOf g : ℤ) ∣ ((n / d : ℕ) : ℤ) * j - k :=
          orderOf_dvd_iff_zpow_eq_one.mpr h1
        rwa [hord] at h0
      have hmul : (n : ℤ) ∣ (((n / d : ℕ) : ℤ) * j) * (m : ℤ) := by
        have hd_dvd_m : d ∣ m := Nat.gcd_dvd_right n m
        refine ⟨j * ((m / d : ℕ) : ℤ), ?_⟩
        have hnm : (n : ℤ) * ((m / d : ℕ) : ℤ) = ((n / d : ℕ) : ℤ) * (m : ℤ) := by
          have : n * (m / d) = (n / d) * m := by
            calc n * (m / d) = ((n / d) * d) * (m / d) := by rw [Nat.div_mul_cancel hd_dvd_n]
              _ = (n / d) * (d * (m / d)) := by ring
              _ = (n / d) * m := by rw [Nat.mul_div_cancel' hd_dvd_m]
          exact_mod_cast this
        calc (((n / d : ℕ) : ℤ) * j) * (m : ℤ)
            = (((n / d : ℕ) : ℤ) * (m : ℤ)) * j := by ring
          _ = ((n : ℤ) * ((m / d : ℕ) : ℤ)) * j := by rw [← hnm]
          _ = (n : ℤ) * (j * ((m / d : ℕ) : ℤ)) := by ring
      have hdiff_m : (n : ℤ) ∣ (((n / d : ℕ) : ℤ) * j - k) * (m : ℤ) :=
        dvd_mul_of_dvd_left hdvd_diff (m : ℤ)
      have := dvd_sub hmul hdiff_m
      simpa [sub_mul] using this
  rw [hker_eq, Nat.card_zpowers]
  change orderOf (g ^ (n / d)) = d
  rw [orderOf_pow, hord, Nat.gcd_eq_right (Nat.div_dvd_of_dvd hd_dvd_n)]
  exact Nat.div_div_self hd_dvd_n hn_pos.ne'

/-- Helper: `(Fin r → ℤ) ⧸ m • (Fin r → ℤ) ≃* Multiplicative (Fin r → ZMod m)` for `m ≠ 0`. -/
private def piIntQuotEquivZMod (r m : ℕ) [NeZero m] :
    (Multiplicative (Fin r → ℤ) ⧸ (powMonoidHom (α := Multiplicative (Fin r → ℤ)) m).range) ≃*
      Multiplicative (Fin r → ZMod m) := by
  let φ : Multiplicative (Fin r → ℤ) →* Multiplicative (Fin r → ZMod m) :=
    { toFun := fun x => Multiplicative.ofAdd (fun i => ((Multiplicative.toAdd x i : ℤ) : ZMod m))
      map_one' := by
        change Multiplicative.ofAdd (fun _ : Fin r => ((0 : ℤ) : ZMod m)) = 1
        simp only [Int.cast_zero]; rfl
      map_mul' := fun x y => by
        change Multiplicative.ofAdd (fun i =>
          ((Multiplicative.toAdd x i + Multiplicative.toAdd y i : ℤ) : ZMod m)) = _
        simp only [Int.cast_add]; rfl }
  have hsurj : Function.Surjective φ := by
    intro y
    refine ⟨Multiplicative.ofAdd (fun i => ((Multiplicative.toAdd y i).val : ℤ)), ?_⟩
    change Multiplicative.ofAdd (fun i => (((Multiplicative.toAdd y i).val : ℤ) : ZMod m)) = y
    have hfun : (fun i => (((Multiplicative.toAdd y i).val : ℤ) : ZMod m)) = Multiplicative.toAdd y := by
      funext i
      rw [Int.cast_natCast, ZMod.natCast_zmod_val]
    rw [hfun]; rfl
  have hker : φ.ker = (powMonoidHom (α := Multiplicative (Fin r → ℤ)) m).range := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_range]
    constructor
    · intro hx
      have hdiv : ∀ i : Fin r, (m : ℤ) ∣ Multiplicative.toAdd x i := by
        intro i
        have hi : ((Multiplicative.toAdd x i : ℤ) : ZMod m) = 0 :=
          congrFun (congrArg Multiplicative.toAdd hx) i
        exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ m).mp hi
      refine ⟨Multiplicative.ofAdd (fun i => Classical.choose (hdiv i)), ?_⟩
      apply Multiplicative.toAdd.injective
      funext i
      change m • Classical.choose (hdiv i) = Multiplicative.toAdd x i
      rw [nsmul_eq_mul]
      exact (Classical.choose_spec (hdiv i)).symm
    · rintro ⟨y, rfl⟩
      apply Multiplicative.toAdd.injective
      funext i
      change ((m • Multiplicative.toAdd y i : ℤ) : ZMod m) = 0
      rw [nsmul_eq_mul, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, zero_mul]
  exact (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective φ hsurj)

/-- Helper: `(A × B) ⧸ (A × B)^m ≃* (A ⧸ A^m) × (B ⧸ B^m)`. -/
private def prodQuotPowEquiv {A B : Type*} [CommGroup A] [CommGroup B] (m : ℕ) :
    ((A × B) ⧸ (powMonoidHom (α := A × B) m).range) ≃*
      (A ⧸ (powMonoidHom (α := A) m).range) × (B ⧸ (powMonoidHom (α := B) m).range) := by
  let φ : A × B →* (A ⧸ (powMonoidHom (α := A) m).range) × (B ⧸ (powMonoidHom (α := B) m).range) :=
    MonoidHom.prod ((QuotientGroup.mk' _).comp (MonoidHom.fst A B))
      ((QuotientGroup.mk' _).comp (MonoidHom.snd A B))
  have hsurj : Function.Surjective φ := by
    rintro ⟨qa, qb⟩
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective _ qa
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective _ qb
    exact ⟨(a, b), rfl⟩
  have hker : φ.ker = (powMonoidHom (α := A × B) m).range := by
    ext ⟨a, b⟩
    simp only [MonoidHom.mem_ker, MonoidHom.mem_range, φ, MonoidHom.prod_apply,
      MonoidHom.comp_apply, Prod.mk_eq_one, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    constructor
    · rintro ⟨⟨a', ha'⟩, ⟨b', hb'⟩⟩
      exact ⟨(a', b'), Prod.ext ha' hb'⟩
    · rintro ⟨⟨a', b'⟩, h⟩
      exact ⟨⟨a', congrArg Prod.fst h⟩, ⟨b', congrArg Prod.snd h⟩⟩
  exact (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective φ hsurj)

/-- Helper: `e : G₁ ≃* G₂` induces `(G₁ ⧸ G₁^m) ≃* (G₂ ⧸ G₂^m)`. -/
private def quotPowCongr {G₁ G₂ : Type*} [CommGroup G₁] [CommGroup G₂] (e : G₁ ≃* G₂) (m : ℕ) :
    (G₁ ⧸ (powMonoidHom (α := G₁) m).range) ≃* (G₂ ⧸ (powMonoidHom (α := G₂) m).range) :=
  QuotientGroup.congr _ _ e (by
    ext y
    simp only [Subgroup.mem_map, MonoidHom.mem_range]
    constructor
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
      refine ⟨e x, ?_⟩
      change (e x) ^ m = e (x ^ m)
      exact (map_pow e x m).symm
    · rintro ⟨x, rfl⟩
      refine ⟨e.symm x ^ m, ⟨e.symm x, rfl⟩, ?_⟩
      change e (e.symm x ^ m) = x ^ m
      rw [map_pow, e.apply_symm_apply])

/-- **Concrete Decomposition of `SUnits K S ⧸ (SUnits K S)^m`**:
`SUnitsQuot K S m ≃* (torsion K ⧸ (torsion K)^m) × Multiplicative (Fin (rank K + S.card) → ZMod m)`. -/
def sUnitsQuotEquiv (S : Finset (Place K)) (m : ℕ) [NeZero m] :
    SUnitsQuot K S m ≃*
      (NumberField.Units.torsion K ⧸ (powMonoidHom (α := NumberField.Units.torsion K) m).range) ×
        Multiplicative (Fin (NumberField.Units.rank K + S.card) → ZMod m) :=
  (quotPowCongr (dirichletSUnitEquiv K S) m).trans
    ((prodQuotPowEquiv m).trans
      (MulEquiv.prodCongr (MulEquiv.refl _) (piIntQuotEquivZMod (NumberField.Units.rank K + S.card) m)))

/-- **Unconditional Finiteness of `SUnits K S ⧸ (SUnits K S)^m`** for every `m ≥ 1`. -/
theorem sUnitsQuot_finite (S : Finset (Place K)) {m : ℕ} (hm : 0 < m) :
    Finite (SUnitsQuot K S m) := by
  have : NeZero m := ⟨hm.ne'⟩
  have : Finite (NumberField.Units.torsion K ⧸
      (powMonoidHom (α := NumberField.Units.torsion K) m).range) :=
    Finite.of_surjective _ (QuotientGroup.mk'_surjective _)
  exact Finite.of_equiv _ (sUnitsQuotEquiv K S m).symm.toEquiv

/-- **Exact Cardinality Formula for `S`-Units Modulo `m`-th Powers**:
`|𝒪_{K,S}ˣ / (𝒪_{K,S}ˣ)^m| = gcd(w_K, m) * m ^ (rk((𝒪_K)ˣ) + |S|)`! -/
theorem card_sUnitsQuot_eq (S : Finset (Place K)) {m : ℕ} (hm : 0 < m) :
    Nat.card (SUnitsQuot K S m) =
      Nat.gcd (NumberField.Units.torsionOrder K) m * m ^ (NumberField.Units.rank K + S.card) := by
  have : NeZero m := ⟨hm.ne'⟩
  rw [Nat.card_congr (sUnitsQuotEquiv K S m).toEquiv, Nat.card_prod]
  have h1 :
      Nat.card (NumberField.Units.torsion K ⧸
        (powMonoidHom (α := NumberField.Units.torsion K) m).range) =
      Nat.gcd (NumberField.Units.torsionOrder K) m := by
    rw [card_quotient_pow_of_isCyclic m]
    rfl
  have h2 :
      Nat.card (Multiplicative (Fin (NumberField.Units.rank K + S.card) → ZMod m)) =
        m ^ (NumberField.Units.rank K + S.card) := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_eq_fintype_card, Fintype.card_fun,
      ZMod.card m, Fintype.card_fin]
  rw [h1, h2]

end DirichletSUnits

/-! ## Section 3: Concrete Global Kummer Selmer Group `K(S, m)` & Exact Unit–Class SES -/

section GlobalKummerSelmer

variable (K : Type*) [Field K] [NumberField K]

/-- Concrete **Global Unramified-Outside-`S` Kummer Selmer Group** `K(S, m) ≤ Kˣ ⧸ (Kˣ)^m`,
instantiated directly as Mathlib's `IsDedekindDomain.selmerGroup` on `NumberField.RingOfIntegers K`. -/
abbrev KummerSelmer (S : Finset (Place K)) (m : ℕ) :
    Subgroup (Kˣ ⧸ (powMonoidHom (α := Kˣ) m).range) :=
  IsDedekindDomain.selmerGroup (R := OK K) (K := K) (S := (S : Set (Place K))) (n := m)

/-- Helper: `v.valuationOfNeZeroMod m (QuotientGroup.mk x) = 1 ↔ (m : ℤ) ∣ adicVal K v x`. -/
theorem valuationOfNeZeroMod_eq_one_iff (v : Place K) (m : ℕ) (x : Kˣ) :
    v.valuationOfNeZeroMod m (QuotientGroup.mk x) = 1 ↔ (m : ℤ) ∣ adicVal K v x := by
  change (AddEquiv.toMultiplicative (Int.quotientZMultiplesNatEquivZMod m))
      (Multiplicative.ofAdd (QuotientAddGroup.mk (Multiplicative.toAdd (v.valuationOfNeZero x)))) = 1 ↔ _
  rw [map_eq_one_iff _ (AddEquiv.toMultiplicative _).injective]
  change (QuotientAddGroup.mk (Multiplicative.toAdd (v.valuationOfNeZero x)) :
      ℤ ⧸ AddSubgroup.zmultiples (m : ℤ)) = 0 ↔ _
  rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_zmultiples_iff,
    adicVal_eq_neg_toAdd_valuationOfNeZero]
  constructor
  · rintro ⟨k, hk⟩
    rw [zsmul_eq_mul, Int.cast_id] at hk
    exact ⟨-k, by linarith⟩
  · rintro ⟨k, hk⟩
    exact ⟨-k, by rw [zsmul_eq_mul, Int.cast_id]; linarith⟩

/-- **Explicit Valuation Divisibility Characterization of `KummerSelmer K S m`**:
`x̄ ∈ K(S, m) ↔ ∀ v ∉ S, (m : ℤ) ∣ ord_v(x)`. -/
theorem mem_kummerSelmer_iff (S : Finset (Place K)) (m : ℕ) (x : Kˣ) :
    (QuotientGroup.mk x : Kˣ ⧸ (powMonoidHom (α := Kˣ) m).range) ∈ KummerSelmer K S m ↔
      ∀ v : Place K, v ∉ S → (m : ℤ) ∣ adicVal K v x := by
  change (∀ v : Place K, v ∉ (S : Set (Place K)) →
      v.valuationOfNeZeroMod m (QuotientGroup.mk x) = 1) ↔ _
  refine forall_congr' fun v => ?_
  simp only [Finset.mem_coe, valuationOfNeZeroMod_eq_one_iff]

/-- First arrow `ι : SUnitsQuot K S m →* KummerSelmer K S m` of the exact Kummer sequence. -/
def sUnitsQuotToKummerSelmer (S : Finset (Place K)) (m : ℕ) :
    SUnitsQuot K S m →* KummerSelmer K S m :=
  QuotientGroup.lift (powMonoidHom (α := SUnits K S) m).range
    { toFun := fun u => ⟨QuotientGroup.mk u.1, by
        rw [mem_kummerSelmer_iff]
        intro v hv
        have h0 : adicVal K v u.1 = 0 :=
          (adicVal_eq_zero_iff_valuation_eq_one K v u.1).mpr ((mem_sUnits_iff K S u.1).mp u.2 v hv)
        rw [h0]
        exact dvd_zero _⟩
      map_one' := Subtype.ext rfl
      map_mul' := fun _ _ => Subtype.ext rfl }
    (by
      rintro _ ⟨u, rfl⟩
      apply Subtype.ext
      change (QuotientGroup.mk (u.1 ^ m) : Kˣ ⧸ (powMonoidHom (α := Kˣ) m).range) = 1
      rw [QuotientGroup.eq_one_iff]
      exact ⟨u.1, rfl⟩)

/-- **Injectivity of `SUnitsQuot K S m →* KummerSelmer K S m`** for every `m ≥ 1`. -/
theorem sUnitsQuotToKummerSelmer_injective (S : Finset (Place K)) {m : ℕ} (hm : 0 < m) :
    Function.Injective (sUnitsQuotToKummerSelmer K S m) := by
  rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
  intro q hq
  induction q using QuotientGroup.induction_on with
  | H u =>
    have h1 : (QuotientGroup.mk u.1 : Kˣ ⧸ (powMonoidHom (α := Kˣ) m).range) = 1 :=
      congrArg Subtype.val hq
    rw [QuotientGroup.eq_one_iff] at h1
    obtain ⟨y, hy⟩ := h1
    have hyS : y ∈ SUnits K S := by
      rw [mem_sUnits_iff]
      intro v hv
      rw [← adicVal_eq_zero_iff_valuation_eq_one]
      have h0 : adicVal K v u.1 = 0 :=
        (adicVal_eq_zero_iff_valuation_eq_one K v u.1).mpr ((mem_sUnits_iff K S u.1).mp u.2 v hv)
      have hpow : adicVal K v (y ^ m) = (m : ℤ) * adicVal K v y := adicVal_pow K v y m
      change y ^ m = u.1 at hy
      rw [hy, h0] at hpow
      exact (mul_eq_zero.mp hpow.symm).resolve_left (Nat.cast_ne_zero.mpr hm.ne')
    change (QuotientGroup.mk u : SUnitsQuot K S m) = 1
    rw [QuotientGroup.eq_one_iff]
    exact ⟨⟨y, hyS⟩, Subtype.ext hy⟩

/-- Helper: the preimage subgroup of `Kˣ` consisting of elements with `m ∣ ord_v(x)` for `v ∉ S`. -/
private def kummerPreimage (S : Finset (Place K)) (m : ℕ) : Subgroup Kˣ :=
  (KummerSelmer K S m).comap (QuotientGroup.mk' (powMonoidHom (α := Kˣ) m).range)

private theorem mem_kummerPreimage_iff (S : Finset (Place K)) (m : ℕ) (x : Kˣ) :
    x ∈ kummerPreimage K S m ↔ ∀ v : Place K, v ∉ S → (m : ℤ) ∣ adicVal K v x :=
  mem_kummerSelmer_iff K S m x

private def kummerPreimageProj (S : Finset (Place K)) (m : ℕ) :
    kummerPreimage K S m →* KummerSelmer K S m where
  toFun x := ⟨QuotientGroup.mk x.1, x.2⟩
  map_one' := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl

private theorem kummerPreimageProj_surjective (S : Finset (Place K)) (m : ℕ) :
    Function.Surjective (kummerPreimageProj K S m) := by
  rintro ⟨q, hq⟩
  induction q using QuotientGroup.induction_on with
  | H x => exact ⟨⟨x, hq⟩, rfl⟩

/-- Helper: the `m`-th root ideal outside `S` attached to `x ∈ kummerPreimage K S m`:
`I_S(x) = ∏_{v ∉ S} v^{ord_v(x) / m}`. -/
private def kummerRootIdeal (S : Finset (Place K)) (m : ℕ) (x : Kˣ) :
    (FractionalIdeal (nonZeroDivisors (OK K)) K)ˣ :=
  open Classical in
  fracIdealOfExps K (fun v => if v ∈ S then 0 else adicVal K v x / (m : ℤ))

private theorem count_kummerRootIdeal_mem (S : Finset (Place K)) (m : ℕ) (x : Kˣ)
    {v : Place K} (hv : v ∈ S) :
    FractionalIdeal.count K v
      (kummerRootIdeal K S m x : FractionalIdeal (nonZeroDivisors (OK K)) K) = 0 := by
  classical
  have hfin : ∀ᶠ w : Place K in Filter.cofinite,
      (if w ∈ S then 0 else adicVal K w x / (m : ℤ)) = 0 := by
    filter_upwards [adicVal_finite_support K x] with w hw
    split_ifs <;> simp [hw]
  unfold kummerRootIdeal
  rw [count_fracIdealOfExps K _ hfin v, if_pos hv]

private theorem count_kummerRootIdeal_not_mem (S : Finset (Place K)) (m : ℕ) (x : Kˣ)
    {v : Place K} (hv : v ∉ S) :
    FractionalIdeal.count K v
      (kummerRootIdeal K S m x : FractionalIdeal (nonZeroDivisors (OK K)) K) =
      adicVal K v x / (m : ℤ) := by
  classical
  have hfin : ∀ᶠ w : Place K in Filter.cofinite,
      (if w ∈ S then 0 else adicVal K w x / (m : ℤ)) = 0 := by
    filter_upwards [adicVal_finite_support K x] with w hw
    split_ifs <;> simp [hw]
  unfold kummerRootIdeal
  rw [count_fracIdealOfExps K _ hfin v, if_neg hv]

private theorem kummerRootIdeal_pow_mul_S (S : Finset (Place K)) (m : ℕ)
    {x : Kˣ} (hx : x ∈ kummerPreimage K S m) :
    kummerRootIdeal K S m x ^ m * (∏ v ∈ S, primeFracIdeal K v ^ adicVal K v x) =
      toPrincipalIdeal (OK K) K x := by
  apply fracIdeal_units_ext_count K
  intro w
  rw [Units.val_mul, FractionalIdeal.count_mul K w (kummerRootIdeal K S m x ^ m).ne_zero
    (∏ v ∈ S, primeFracIdeal K v ^ adicVal K v x).ne_zero,
    Units.val_pow_eq_pow_val, FractionalIdeal.count_pow, ← adicVal_eq_count_toPrincipalIdeal]
  by_cases hw : w ∈ S
  · rw [count_kummerRootIdeal_mem K S m x hw, count_finset_prod_primeFracIdeal_mem K S _ hw]
    ring
  · rw [count_kummerRootIdeal_not_mem K S m x hw, count_finset_prod_primeFracIdeal_not_mem K S _ hw,
      add_zero]
    have hdvd : (m : ℤ) ∣ adicVal K w x := (mem_kummerPreimage_iff K S m x).mp hx w hw
    exact Int.mul_ediv_cancel' hdvd

/-- Helper: `kummerRootIdeal` is multiplicative on `kummerPreimage K S m`. -/
private theorem kummerRootIdeal_mul (S : Finset (Place K)) (m : ℕ)
    {x y : Kˣ} (hx : x ∈ kummerPreimage K S m) :
    kummerRootIdeal K S m (x * y) = kummerRootIdeal K S m x * kummerRootIdeal K S m y := by
  apply fracIdeal_units_ext_count K
  intro w
  rw [Units.val_mul, FractionalIdeal.count_mul K w (kummerRootIdeal K S m x).ne_zero
    (kummerRootIdeal K S m y).ne_zero]
  by_cases hw : w ∈ S
  · rw [count_kummerRootIdeal_mem K S m (x * y) hw, count_kummerRootIdeal_mem K S m x hw,
      count_kummerRootIdeal_mem K S m y hw, add_zero]
  · rw [count_kummerRootIdeal_not_mem K S m (x * y) hw, count_kummerRootIdeal_not_mem K S m x hw,
      count_kummerRootIdeal_not_mem K S m y hw, adicVal_mul]
    have hdx : (m : ℤ) ∣ adicVal K w x := (mem_kummerPreimage_iff K S m x).mp hx w hw
    exact Int.add_ediv_of_dvd_left hdx

private def kummerPreimageToSClassGroupTorsion (S : Finset (Place K)) (m : ℕ) :
    kummerPreimage K S m →* SClassGroupTorsion K S m where
  toFun x :=
    ⟨QuotientGroup.mk (ClassGroup.mk K (kummerRootIdeal K S m x.1)), by
      rw [mem_sClassGroupTorsion_iff]
      change (QuotientGroup.mk (ClassGroup.mk K (kummerRootIdeal K S m x.1) ^ m) :
        SClassGroup K S) = 1
      rw [QuotientGroup.eq_one_iff, ← map_pow]
      have hrel := kummerRootIdeal_pow_mul_S K S m x.2
      have hcls := congrArg (ClassGroup.mk K) hrel
      rw [map_mul, map_prod, classGroup_mk_toPrincipalIdeal] at hcls
      have hinv : ClassGroup.mk K (kummerRootIdeal K S m x.1 ^ m) =
          ∏ v ∈ S, mkPrimeClass K v ^ (-adicVal K v x.1) := by
        apply mul_right_cancel (b := ∏ v ∈ S, ClassGroup.mk K (primeFracIdeal K v ^ adicVal K v x.1))
        rw [hcls, ← Finset.prod_mul_distrib]
        symm
        refine Finset.prod_eq_one fun v _ => ?_
        rw [map_zpow, classGroup_mk_primeFracIdeal, ← zpow_add, neg_add_cancel, zpow_zero]
      rw [hinv]
      exact (mem_sClassSubgroup_iff_exists_prod K S _).mpr ⟨fun v => -adicVal K v x.1, rfl⟩⟩
  map_one' := by
    apply Subtype.ext
    have h1 : kummerRootIdeal K S m 1 = 1 := by
      apply fracIdeal_units_ext_count K
      intro w
      rw [Units.val_one, FractionalIdeal.count_one]
      by_cases hw : w ∈ S
      · exact count_kummerRootIdeal_mem K S m 1 hw
      · rw [count_kummerRootIdeal_not_mem K S m 1 hw, adicVal_one, Int.zero_ediv]
    simp [h1]
  map_mul' x y := by
    apply Subtype.ext
    change (QuotientGroup.mk (ClassGroup.mk K (kummerRootIdeal K S m (x.1 * y.1))) : SClassGroup K S) =
      QuotientGroup.mk (ClassGroup.mk K (kummerRootIdeal K S m x.1)) *
        QuotientGroup.mk (ClassGroup.mk K (kummerRootIdeal K S m y.1))
    rw [kummerRootIdeal_mul K S m x.2, map_mul]
    rfl

private theorem kummerPreimageProj_ker_le (S : Finset (Place K)) {m : ℕ} (hm : 0 < m) :
    (kummerPreimageProj K S m).ker ≤ (kummerPreimageToSClassGroupTorsion K S m).ker := by
  intro x hx
  rw [MonoidHom.mem_ker] at hx ⊢
  have h1 : (QuotientGroup.mk x.1 : Kˣ ⧸ (powMonoidHom (α := Kˣ) m).range) = 1 :=
    congrArg Subtype.val hx
  rw [QuotientGroup.eq_one_iff] at h1
  obtain ⟨y, hy⟩ := h1
  change y ^ m = x.1 at hy
  have hideal : kummerRootIdeal K S m x.1 * (∏ v ∈ S, primeFracIdeal K v ^ adicVal K v y) =
      toPrincipalIdeal (OK K) K y := by
    apply fracIdeal_units_ext_count K
    intro w
    rw [Units.val_mul, FractionalIdeal.count_mul K w (kummerRootIdeal K S m x.1).ne_zero
      (∏ v ∈ S, primeFracIdeal K v ^ adicVal K v y).ne_zero,
      ← adicVal_eq_count_toPrincipalIdeal]
    by_cases hw : w ∈ S
    · rw [count_kummerRootIdeal_mem K S m x.1 hw, count_finset_prod_primeFracIdeal_mem K S _ hw,
        zero_add]
    · rw [count_kummerRootIdeal_not_mem K S m x.1 hw,
        count_finset_prod_primeFracIdeal_not_mem K S _ hw, add_zero, ← hy, adicVal_pow]
      exact Int.mul_ediv_cancel_left _ (Nat.cast_ne_zero.mpr hm.ne')
  apply Subtype.ext
  change (QuotientGroup.mk (ClassGroup.mk K (kummerRootIdeal K S m x.1)) : SClassGroup K S) = 1
  rw [QuotientGroup.eq_one_iff]
  have hcls := congrArg (ClassGroup.mk K) hideal
  rw [map_mul, map_prod, classGroup_mk_toPrincipalIdeal] at hcls
  have hinv : ClassGroup.mk K (kummerRootIdeal K S m x.1) =
      ∏ v ∈ S, mkPrimeClass K v ^ (-adicVal K v y) := by
    apply mul_right_cancel (b := ∏ v ∈ S, ClassGroup.mk K (primeFracIdeal K v ^ adicVal K v y))
    rw [hcls, ← Finset.prod_mul_distrib]
    symm
    refine Finset.prod_eq_one fun v _ => ?_
    rw [map_zpow, classGroup_mk_primeFracIdeal, ← zpow_add, neg_add_cancel, zpow_zero]
  rw [hinv]
  exact (mem_sClassSubgroup_iff_exists_prod K S _).mpr ⟨fun v => -adicVal K v y, rfl⟩

/-- Second arrow `φ : KummerSelmer K S m →* SClassGroupTorsion K S m` of the exact Kummer sequence,
sending `x̄ ↦ [∏_{v ∉ S} v^{ord_v(x)/m}] ∈ Cl_S(K)[m]`. -/
def kummerSelmerToSClassGroupTorsion (S : Finset (Place K)) {m : ℕ} (hm : 0 < m) :
    KummerSelmer K S m →* SClassGroupTorsion K S m :=
  (QuotientGroup.lift (kummerPreimageProj K S m).ker
      (kummerPreimageToSClassGroupTorsion K S m) (kummerPreimageProj_ker_le K S hm)).comp
    (QuotientGroup.quotientKerEquivOfSurjective
      (kummerPreimageProj K S m) (kummerPreimageProj_surjective K S m)).symm.toMonoidHom

/-- Evaluation of `kummerSelmerToSClassGroupTorsion` on a coset `QuotientGroup.mk x`. -/
theorem kummerSelmerToSClassGroupTorsion_apply (S : Finset (Place K)) {m : ℕ} (hm : 0 < m)
    {x : Kˣ} (hx : (QuotientGroup.mk x : Kˣ ⧸ (powMonoidHom (α := Kˣ) m).range) ∈ KummerSelmer K S m) :
    (kummerSelmerToSClassGroupTorsion K S hm ⟨QuotientGroup.mk x, hx⟩ : SClassGroup K S) =
      QuotientGroup.mk (ClassGroup.mk K (kummerRootIdeal K S m x)) := by
  let e := QuotientGroup.quotientKerEquivOfSurjective
    (kummerPreimageProj K S m) (kummerPreimageProj_surjective K S m)
  have hsymm : e.symm ⟨QuotientGroup.mk x, hx⟩ = QuotientGroup.mk (⟨x, hx⟩ : kummerPreimage K S m) := by
    apply e.injective
    rw [e.apply_symm_apply]
    rfl
  change ((QuotientGroup.lift (kummerPreimageProj K S m).ker
      (kummerPreimageToSClassGroupTorsion K S m) (kummerPreimageProj_ker_le K S hm)
      (e.symm ⟨QuotientGroup.mk x, hx⟩) : SClassGroupTorsion K S m) : SClassGroup K S) = _
  rw [hsymm]
  rfl

/-- **Exactness at `KummerSelmer K S m`**:
`ker(kummerSelmerToSClassGroupTorsion) = range(sUnitsQuotToKummerSelmer)`! -/
theorem ker_kummerSelmerToSClassGroupTorsion_eq_range (S : Finset (Place K)) {m : ℕ} (hm : 0 < m) :
    (kummerSelmerToSClassGroupTorsion K S hm).ker = (sUnitsQuotToKummerSelmer K S m).range := by
  ext ⟨q, hq⟩
  rw [MonoidHom.mem_ker, MonoidHom.mem_range]
  induction q using QuotientGroup.induction_on with
  | H x =>
    constructor
    · intro hker
      have hcls1 : (QuotientGroup.mk (ClassGroup.mk K (kummerRootIdeal K S m x)) : SClassGroup K S) = 1 := by
        have := congrArg Subtype.val hker
        rwa [kummerSelmerToSClassGroupTorsion_apply K S hm hq] at this
      rw [QuotientGroup.eq_one_iff] at hcls1
      obtain ⟨e, he⟩ := (mem_sClassSubgroup_iff_exists_prod K S _).mp hcls1
      let J : (FractionalIdeal (nonZeroDivisors (OK K)) K)ˣ :=
        kummerRootIdeal K S m x * (∏ v ∈ S, primeFracIdeal K v ^ (-e v))
      have hJ1 : ClassGroup.mk K J = 1 := by
        rw [map_mul, he, map_prod, ← Finset.prod_mul_distrib]
        refine Finset.prod_eq_one fun v _ => ?_
        rw [map_zpow, classGroup_mk_primeFracIdeal, ← zpow_add, add_neg_cancel, zpow_zero]
      obtain ⟨y, hy⟩ := exists_toPrincipalIdeal_of_classGroup_mk_eq_one K hJ1
      let u : Kˣ := x * (y ^ m)⁻¹
      have huS : u ∈ SUnits K S := by
        rw [mem_sUnits_iff]
        intro w hw
        rw [← adicVal_eq_zero_iff_valuation_eq_one]
        have hy_val : adicVal K w y = adicVal K w x / (m : ℤ) := by
          rw [adicVal_eq_count_toPrincipalIdeal, ← hy, Units.val_mul,
            FractionalIdeal.count_mul K w (kummerRootIdeal K S m x).ne_zero
              (∏ v ∈ S, primeFracIdeal K v ^ (-e v)).ne_zero,
            count_kummerRootIdeal_not_mem K S m x hw,
            count_finset_prod_primeFracIdeal_not_mem K S _ hw, add_zero]
        have hdvd : (m : ℤ) ∣ adicVal K w x := (mem_kummerSelmer_iff K S m x).mp hq w hw
        rw [adicVal_mul, adicVal_inv, adicVal_pow, hy_val, Int.mul_ediv_cancel' hdvd, add_neg_cancel]
      refine ⟨QuotientGroup.mk ⟨u, huS⟩, ?_⟩
      apply Subtype.ext
      change (QuotientGroup.mk u : Kˣ ⧸ (powMonoidHom (α := Kˣ) m).range) = QuotientGroup.mk x
      rw [QuotientGroup.eq]
      refine ⟨y, ?_⟩
      change y ^ m = u⁻¹ * x
      simp [u]
    · rintro ⟨qu, hqu⟩
      induction qu using QuotientGroup.induction_on with
      | H u =>
        have hsub : (⟨QuotientGroup.mk x, hq⟩ : KummerSelmer K S m) =
            sUnitsQuotToKummerSelmer K S m (QuotientGroup.mk u) := hqu.symm
        rw [hsub]
        apply Subtype.ext
        change ((kummerSelmerToSClassGroupTorsion K S hm ⟨QuotientGroup.mk u.1, _⟩ :
          SClassGroupTorsion K S m) : SClassGroup K S) = 1
        rw [kummerSelmerToSClassGroupTorsion_apply K S hm]
        have h1 : kummerRootIdeal K S m u.1 = 1 := by
          apply fracIdeal_units_ext_count K
          intro w
          rw [Units.val_one, FractionalIdeal.count_one]
          by_cases hw : w ∈ S
          · exact count_kummerRootIdeal_mem K S m u.1 hw
          · rw [count_kummerRootIdeal_not_mem K S m u.1 hw]
            have h0 : adicVal K w u.1 = 0 :=
              (adicVal_eq_zero_iff_valuation_eq_one K w u.1).mpr ((mem_sUnits_iff K S u.1).mp u.2 w hw)
            rw [h0, Int.zero_ediv]
        simp [h1]

/-- **Surjectivity of `KummerSelmer K S m →* SClassGroupTorsion K S m`** for every `m ≥ 1`. -/
theorem kummerSelmerToSClassGroupTorsion_surjective (S : Finset (Place K)) {m : ℕ} (hm : 0 < m) :
    Function.Surjective (kummerSelmerToSClassGroupTorsion K S hm) := by
  rintro ⟨c, hc⟩
  induction c using QuotientGroup.induction_on with
  | H cl =>
    refine ClassGroup.induction K (P := fun cl =>
      ∀ hcl : (QuotientGroup.mk cl : SClassGroup K S) ∈ SClassGroupTorsion K S m,
        ∃ a : KummerSelmer K S m,
          kummerSelmerToSClassGroupTorsion K S hm a = ⟨QuotientGroup.mk cl, hcl⟩) ?_ cl hc
    intro J hJm
    let J' : (FractionalIdeal (nonZeroDivisors (OK K)) K)ˣ :=
      J * (∏ v ∈ S, primeFracIdeal K v ^ (-FractionalIdeal.count K v (J : FractionalIdeal _ K)))
    have hJ'_cls : (QuotientGroup.mk (ClassGroup.mk K J') : SClassGroup K S) =
        QuotientGroup.mk (ClassGroup.mk K J) := by
      rw [QuotientGroup.eq]
      have hmul : (ClassGroup.mk K J')⁻¹ * ClassGroup.mk K J =
          ∏ v ∈ S, mkPrimeClass K v ^ FractionalIdeal.count K v (J : FractionalIdeal _ K) := by
        apply mul_left_cancel (a := ClassGroup.mk K J')
        rw [← mul_assoc, mul_inv_cancel, one_mul]
        dsimp only [J']
        rw [map_mul, map_prod, mul_assoc, ← Finset.prod_mul_distrib]
        have h1 : ∏ v ∈ S, ClassGroup.mk K (primeFracIdeal K v ^ (-FractionalIdeal.count K v (J : FractionalIdeal _ K))) *
            mkPrimeClass K v ^ FractionalIdeal.count K v (J : FractionalIdeal _ K) = 1 := by
          refine Finset.prod_eq_one fun v _ => ?_
          rw [map_zpow, classGroup_mk_primeFracIdeal, ← zpow_add, neg_add_cancel, zpow_zero]
        rw [h1, mul_one]
      rw [hmul]
      exact (mem_sClassSubgroup_iff_exists_prod K S _).mpr ⟨_, rfl⟩
    have hJ'_mem : ∀ v ∈ S, FractionalIdeal.count K v (J' : FractionalIdeal _ K) = 0 := by
      intro v hv
      rw [Units.val_mul, FractionalIdeal.count_mul K v J.ne_zero
        (∏ w ∈ S, primeFracIdeal K w ^ (-FractionalIdeal.count K w (J : FractionalIdeal _ K))).ne_zero,
        count_finset_prod_primeFracIdeal_mem K S _ hv, add_neg_cancel]
    have hJ'_pow : (QuotientGroup.mk (ClassGroup.mk K (J' ^ m)) : SClassGroup K S) = 1 := by
      rw [map_pow]
      change (QuotientGroup.mk (ClassGroup.mk K J') : SClassGroup K S) ^ m = 1
      rw [hJ'_cls]
      exact hJm
    rw [QuotientGroup.eq_one_iff] at hJ'_pow
    obtain ⟨d, hd⟩ := (mem_sClassSubgroup_iff_exists_prod K S _).mp hJ'_pow
    let P : (FractionalIdeal (nonZeroDivisors (OK K)) K)ˣ :=
      J' ^ m * (∏ v ∈ S, primeFracIdeal K v ^ (-d v))
    have hP1 : ClassGroup.mk K P = 1 := by
      rw [map_mul, hd, map_prod, ← Finset.prod_mul_distrib]
      refine Finset.prod_eq_one fun v _ => ?_
      rw [map_zpow, classGroup_mk_primeFracIdeal, ← zpow_add, add_neg_cancel, zpow_zero]
    obtain ⟨x, hx⟩ := exists_toPrincipalIdeal_of_classGroup_mk_eq_one K hP1
    have hx_val : ∀ w : Place K, w ∉ S →
        adicVal K w x = (m : ℤ) * FractionalIdeal.count K w (J' : FractionalIdeal _ K) := by
      intro w hw
      rw [adicVal_eq_count_toPrincipalIdeal, ← hx, Units.val_mul,
        FractionalIdeal.count_mul K w (J' ^ m).ne_zero
          (∏ v ∈ S, primeFracIdeal K v ^ (-d v)).ne_zero,
        Units.val_pow_eq_pow_val, FractionalIdeal.count_pow,
        count_finset_prod_primeFracIdeal_not_mem K S _ hw, add_zero]
    have hx_sel : (QuotientGroup.mk x : Kˣ ⧸ (powMonoidHom (α := Kˣ) m).range) ∈ KummerSelmer K S m := by
      rw [mem_kummerSelmer_iff]
      intro w hw
      rw [hx_val w hw]
      exact dvd_mul_right _ _
    have hroot : kummerRootIdeal K S m x = J' := by
      apply fracIdeal_units_ext_count K
      intro w
      by_cases hw : w ∈ S
      · rw [count_kummerRootIdeal_mem K S m x hw, hJ'_mem w hw]
      · rw [count_kummerRootIdeal_not_mem K S m x hw, hx_val w hw]
        exact Int.mul_ediv_cancel_left _ (Nat.cast_ne_zero.mpr hm.ne')
    refine ⟨⟨QuotientGroup.mk x, hx_sel⟩, Subtype.ext ?_⟩
    rw [kummerSelmerToSClassGroupTorsion_apply K S hm hx_sel, hroot, hJ'_cls]

/-- **Exact Global Kummer Short Exact Sequence (in `Additive` form, ready for `Stage2GaloisCohomology`)**:
`0 → Additive (SUnitsQuot K S m) → Additive (KummerSelmer K S m) → Additive (SClassGroupTorsion K S m) → 0`! -/
theorem exact_kummer_short_exact_sequence (S : Finset (Place K)) {m : ℕ} (hm : 0 < m) :
    Function.Injective (MonoidHom.toAdditive (sUnitsQuotToKummerSelmer K S m)) ∧
      Function.Surjective (MonoidHom.toAdditive (kummerSelmerToSClassGroupTorsion K S hm)) ∧
      Function.Exact (MonoidHom.toAdditive (sUnitsQuotToKummerSelmer K S m))
        (MonoidHom.toAdditive (kummerSelmerToSClassGroupTorsion K S hm)) := by
  refine ⟨sUnitsQuotToKummerSelmer_injective K S hm,
    kummerSelmerToSClassGroupTorsion_surjective K S hm, ?_⟩
  intro x
  change Additive.toMul x ∈ (kummerSelmerToSClassGroupTorsion K S hm).ker ↔ _
  rw [ker_kummerSelmerToSClassGroupTorsion_eq_range K S hm, MonoidHom.mem_range]
  constructor
  · rintro ⟨u, hu⟩
    exact ⟨Additive.ofMul u, congrArg Additive.ofMul hu⟩
  · rintro ⟨u, hu⟩
    exact ⟨Additive.toMul u, congrArg Additive.toMul hu⟩

/-- **Unconditional Global Kummer Selmer Finiteness & Exact Order Formula** (wired DIRECTLY through
`Stage2GaloisCohomology.kummer_unramified_finite`!):
for EVERY number field `K`, EVERY finite set of places `S`, and EVERY `m ≥ 1`:
`Finite (KummerSelmer K S m)` AND
`Nat.card (KummerSelmer K S m) = Nat.card (SUnitsQuot K S m) * Nat.card (SClassGroupTorsion K S m)`! -/
theorem kummerSelmer_finite_and_card (S : Finset (Place K)) {m : ℕ} (hm : 0 < m) :
    Finite (KummerSelmer K S m) ∧
      Nat.card (KummerSelmer K S m) =
        Nat.card (SUnitsQuot K S m) * Nat.card (SClassGroupTorsion K S m) := by
  have : Finite (SUnitsQuot K S m) := sUnitsQuot_finite K S hm
  have : Finite (Additive (SUnitsQuot K S m)) := Finite.of_equiv _ Additive.ofMul
  have : Finite (Additive (SClassGroupTorsion K S m)) := Finite.of_equiv _ Additive.ofMul
  obtain ⟨hi, hp, hex⟩ := exact_kummer_short_exact_sequence K S hm
  obtain ⟨hfinAdd, hcardAdd⟩ :=
    Stage2GaloisCohomology.kummer_unramified_finite
      (MonoidHom.toAdditive (sUnitsQuotToKummerSelmer K S m))
      (MonoidHom.toAdditive (kummerSelmerToSClassGroupTorsion K S hm))
      hi hp hex
  refine ⟨Finite.of_equiv _ Additive.toMul, ?_⟩
  rw [Nat.card_congr Additive.ofMul, hcardAdd, ← Nat.card_congr Additive.ofMul,
    ← Nat.card_congr Additive.ofMul]

/-- **Unconditional Finiteness of `KummerSelmer K S m`** for every number field `K`, finite `S`,
and `m ≥ 1`. -/
theorem kummerSelmer_finite (S : Finset (Place K)) {m : ℕ} (hm : 0 < m) :
    Finite (KummerSelmer K S m) :=
  (kummerSelmer_finite_and_card K S hm).1

/-- **Exact Order Formula for `KummerSelmer K S m`**:
`|K(S, m)| = |𝒪_{K,S}ˣ / (𝒪_{K,S}ˣ)^m| * |Cl_S(K)[m]|`. -/
theorem card_kummerSelmer_eq (S : Finset (Place K)) {m : ℕ} (hm : 0 < m) :
    Nat.card (KummerSelmer K S m) =
      Nat.card (SUnitsQuot K S m) * Nat.card (SClassGroupTorsion K S m) :=
  (kummerSelmer_finite_and_card K S hm).2

/-- **Full Explicit Global Kummer Selmer Cardinality Formula** combining Dirichlet's `S`-Unit
Theorem and the Exact Kummer Sequence:
`|K(S, m)| = gcd(w_K, m) * m ^ (rk((𝒪_K)ˣ) + |S|) * |Cl_S(K)[m]|`! -/
theorem card_kummerSelmer_exact_formula (S : Finset (Place K)) {m : ℕ} (hm : 0 < m) :
    Nat.card (KummerSelmer K S m) =
      Nat.gcd (NumberField.Units.torsionOrder K) m * m ^ (NumberField.Units.rank K + S.card) *
        Nat.card (SClassGroupTorsion K S m) := by
  rw [card_kummerSelmer_eq K S hm, card_sUnitsQuot_eq K S hm]

end GlobalKummerSelmer

/-! ## Section 4: Hilbert's Theorem 90 & Concrete Galois Kummer Cohomology `H¹(Gal(L/K), μ_m(L))` -/

section Hilbert90AndKummerCohomology

variable (K L : Type*) [Field K] [Field L] [Algebra K L]

/-- Galois action of `L ≃ₐ[K] L` on `Additive Lˣ`: `σ • ofMul u = ofMul (Units.map σ u)`. -/
instance galActionAdditiveUnits : DistribMulAction (L ≃ₐ[K] L) (Additive Lˣ) where
  smul σ u := Additive.ofMul (Units.map σ.toMonoidHom (Additive.toMul u))
  one_smul u := by
    apply Additive.toMul.injective
    apply Units.ext
    rfl
  mul_smul σ τ u := by
    apply Additive.toMul.injective
    apply Units.ext
    rfl
  smul_zero σ := by
    apply Additive.toMul.injective
    apply Units.ext
    exact map_one σ
  smul_add σ u v := by
    apply Additive.toMul.injective
    apply Units.ext
    exact map_mul σ _ _

/-- Galois action of `L ≃ₐ[K] L` on `Additive (rootsOfUnity m L)`. -/
instance galActionAdditiveRootsOfUnity (m : ℕ) :
    DistribMulAction (L ≃ₐ[K] L) (Additive (rootsOfUnity m L)) where
  smul σ ζ := Additive.ofMul
    ⟨Units.map σ.toMonoidHom (Additive.toMul ζ).1, by
      rw [mem_rootsOfUnity]
      have hζ : (Additive.toMul ζ).1 ^ m = 1 := (mem_rootsOfUnity m _).mp (Additive.toMul ζ).2
      rw [← map_pow, hζ, map_one]⟩
  one_smul ζ := by
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Units.ext
    rfl
  mul_smul σ τ ζ := by
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Units.ext
    rfl
  smul_zero σ := by
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Units.ext
    exact map_one σ
  smul_add σ ζ₁ ζ₂ := by
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Units.ext
    exact map_mul σ _ _

/-- Helper: in any finite Galois extension `L/K`, elements fixed by all `σ : L ≃ₐ[K] L` lie in
the image of `algebraMap K L`. -/
theorem exists_algebraMap_of_gal_fixed [FiniteDimensional K L] [IsGalois K L]
    {x : L} (hx : ∀ σ : L ≃ₐ[K] L, σ x = x) :
    ∃ y : K, algebraMap K L y = x := by
  have htop : IntermediateField.fixedField (⊤ : Subgroup (L ≃ₐ[K] L)) = ⊥ :=
    (IsGalois.tfae.out 0 1).mp ‹IsGalois K L›
  have hmem : x ∈ IntermediateField.fixedField (⊤ : Subgroup (L ≃ₐ[K] L)) := by
    rw [IntermediateField.mem_fixedField_iff]
    intro σ _
    exact hx σ
  rw [htop, IntermediateField.mem_bot] at hmem
  exact hmem

/-- **Hilbert's Theorem 90 (Cocycle Form)**:
for every finite Galois extension `L/K`, EVERY 1-cocycle `c : Cocycle1 (L ≃ₐ[K] L) (Additive Lˣ)`
is a 1-coboundary! -/
theorem hilbert90_cocycle_eq_coboundary [FiniteDimensional K L] [IsGalois K L]
    (c : Cocycle1 (L ≃ₐ[K] L) (Additive Lˣ)) :
    ∃ a : Additive Lˣ, c = coboundary1 (L ≃ₐ[K] L) (Additive Lˣ) a := by
  classical
  have : Fintype (L ≃ₐ[K] L) := Fintype.ofFinite (L ≃ₐ[K] L)
  have hlin : LinearIndependent L (fun σ : L ≃ₐ[K] L => σ.toAlgHom.toLinearMap) :=
    (linearIndependent_algHom_toLinearMap K L L).comp AlgEquiv.toAlgHom
      AlgEquiv.coe_toAlgHom_injective
  let f : L →ₗ[K] L :=
    ∑ σ : L ≃ₐ[K] L, ((Additive.toMul (c σ) : Lˣ) : L) • σ.toAlgHom.toLinearMap
  have hf_ne : f ≠ 0 := by
    intro hf0
    have h1 := linearIndependent_iff'.mp hlin Finset.univ
      (fun σ => ((Additive.toMul (c σ) : Lˣ) : L)) hf0 (1 : L ≃ₐ[K] L) (Finset.mem_univ _)
    exact (Additive.toMul (c 1)).ne_zero h1
  have hex : ∃ z : L, f z ≠ 0 := by
    by_contra h
    push Not at h
    exact hf_ne (LinearMap.ext h)
  obtain ⟨z, hz⟩ := hex
  set b : L := f z with hb_def
  have hb_eq : b = ∑ σ : L ≃ₐ[K] L, ((Additive.toMul (c σ) : Lˣ) : L) * σ z := by
    simp [hb_def, f, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  let bu : Lˣ := Units.mk0 b hz
  refine ⟨Additive.ofMul bu⁻¹, ?_⟩
  apply Cocycle1.ext
  intro τ
  apply Additive.toMul.injective
  apply Units.ext
  have hτb : τ b = ((Additive.toMul (c τ) : Lˣ) : L)⁻¹ * b := by
    rw [hb_eq, map_sum]
    have hterm : ∀ σ : L ≃ₐ[K] L,
        τ (((Additive.toMul (c σ) : Lˣ) : L) * σ z) =
          ((Additive.toMul (c τ) : Lˣ) : L)⁻¹ *
            (((Additive.toMul (c (τ * σ)) : Lˣ) : L) * (τ * σ) z) := by
      intro σ
      rw [map_mul]
      have hcoc := congrArg (fun u : Additive Lˣ => ((Additive.toMul u : Lˣ) : L)) (c.map_mul τ σ)
      change ((Additive.toMul (c (τ * σ)) : Lˣ) : L) =
        ((Additive.toMul (c τ) : Lˣ) : L) * τ ((Additive.toMul (c σ) : Lˣ) : L) at hcoc
      have hmul_app : (τ * σ) z = τ (σ z) := rfl
      rw [hcoc, hmul_app, ← mul_assoc, ← mul_assoc,
        inv_mul_cancel₀ (Additive.toMul (c τ)).ne_zero, one_mul]
    calc ∑ σ : L ≃ₐ[K] L, τ (((Additive.toMul (c σ) : Lˣ) : L) * σ z)
        = ∑ σ : L ≃ₐ[K] L, ((Additive.toMul (c τ) : Lˣ) : L)⁻¹ *
            (((Additive.toMul (c (τ * σ)) : Lˣ) : L) * (τ * σ) z) :=
          Finset.sum_congr rfl fun σ _ => hterm σ
      _ = ((Additive.toMul (c τ) : Lˣ) : L)⁻¹ *
            ∑ σ : L ≃ₐ[K] L, ((Additive.toMul (c (τ * σ)) : Lˣ) : L) * (τ * σ) z := by
          rw [← Finset.mul_sum]
      _ = ((Additive.toMul (c τ) : Lˣ) : L)⁻¹ *
            ∑ σ : L ≃ₐ[K] L, ((Additive.toMul (c σ) : Lˣ) : L) * σ z := by
          congr 1
          exact Fintype.sum_equiv (Equiv.mulLeft τ) _ _ fun _ => rfl
  simp only [coboundary1, AddMonoidHom.coe_mk, ZeroHom.coe_mk, toMul_sub]
  change ((Additive.toMul (c τ) : Lˣ) : L) =
    (((Units.map τ.toMonoidHom bu⁻¹ / bu⁻¹ : Lˣ)) : L)
  simp only [div_eq_mul_inv, Units.val_mul, Units.val_inv_eq_inv_val, Units.coe_map,
    Units.val_mk0, bu]
  change ((Additive.toMul (c τ) : Lˣ) : L) = τ b⁻¹ * (b⁻¹)⁻¹
  rw [map_inv₀, inv_inv, hτb, mul_inv, inv_inv, mul_assoc, inv_mul_cancel₀ hz, mul_one]

/-- **Hilbert's Theorem 90 (`H¹(Gal(L/K), Lˣ) = 0`)**:
for every finite Galois extension `L/K`, `H1Group (L ≃ₐ[K] L) (Additive Lˣ)` is trivial! -/
theorem hilbert90_H1_subsingleton [FiniteDimensional K L] [IsGalois K L] :
    Subsingleton (H1Group (L ≃ₐ[K] L) (Additive Lˣ)) := by
  refine ⟨fun x y => ?_⟩
  have hzero : ∀ q : H1Group (L ≃ₐ[K] L) (Additive Lˣ), q = 0 := by
    intro q
    induction q using Quotient.inductionOn' with
    | h c =>
      change (QuotientAddGroup.mk c : H1Group (L ≃ₐ[K] L) (Additive Lˣ)) = 0
      rw [QuotientAddGroup.eq_zero_iff]
      obtain ⟨a, ha⟩ := hilbert90_cocycle_eq_coboundary K L c
      exact ⟨a, ha.symm⟩
  rw [hzero x, hzero y]

/-- The subgroup `(Lˣ)^m ∩ Kˣ` of elements in `Kˣ` that are `m`-th powers in `Lˣ`. -/
def kummerSubgroup (m : ℕ) : Subgroup Kˣ :=
  (powMonoidHom (α := Lˣ) m).range.comap (Units.map (algebraMap K L : K →* L))

theorem mem_kummerSubgroup_iff (m : ℕ) (x : Kˣ) :
    x ∈ kummerSubgroup K L m ↔ ∃ α : Lˣ, α ^ m = Units.map (algebraMap K L : K →* L) x :=
  Iff.rfl

/-- Concrete Kummer domain `((Lˣ)^m ∩ Kˣ) ⧸ (Kˣ)^m` as a subgroup of `Kˣ ⧸ (Kˣ)^m`. -/
def KummerDomain (m : ℕ) : Subgroup (Kˣ ⧸ (powMonoidHom (α := Kˣ) m).range) :=
  (kummerSubgroup K L m).map (QuotientGroup.mk' (powMonoidHom (α := Kˣ) m).range)

theorem mem_kummerDomain_iff (m : ℕ) (x : Kˣ) :
    (QuotientGroup.mk x : Kˣ ⧸ (powMonoidHom (α := Kˣ) m).range) ∈ KummerDomain K L m ↔
      ∃ α : Lˣ, α ^ m = Units.map (algebraMap K L : K →* L) x := by
  rw [KummerDomain, Subgroup.mem_map]
  constructor
  · rintro ⟨x', hx', hqx⟩
    obtain ⟨α, hα⟩ := hx'
    change α ^ m = Units.map (algebraMap K L : K →* L) x' at hα
    have h1 : (QuotientGroup.mk x' : Kˣ ⧸ (powMonoidHom (α := Kˣ) m).range) = QuotientGroup.mk x := hqx
    rw [QuotientGroup.eq] at h1
    obtain ⟨y, hy⟩ := h1
    change y ^ m = x'⁻¹ * x at hy
    refine ⟨α * Units.map (algebraMap K L : K →* L) y, ?_⟩
    rw [mul_pow, hα, ← map_pow, ← map_mul, show x' * y ^ m = x by rw [hy]; group]
  · rintro ⟨α, hα⟩
    exact ⟨x, ⟨α, hα⟩, rfl⟩

/-- **Concrete Galois Kummer 1-Cocycle**: for `α ∈ Lˣ` with `α^m = algebraMap K L x`,
`σ ↦ σ(α) / α` is a 1-cocycle in `Z¹(Gal(L/K), μ_m(L))`. -/
def kummerCocycle (m : ℕ) {x : Kˣ} (α : Lˣ)
    (hα : α ^ m = Units.map (algebraMap K L : K →* L) x) :
    Cocycle1 (L ≃ₐ[K] L) (Additive (rootsOfUnity m L)) where
  toFun σ := Additive.ofMul
    ⟨Units.map σ.toMonoidHom α * α⁻¹, by
      rw [mem_rootsOfUnity, mul_pow, inv_pow, ← map_pow, hα]
      have hfix : Units.map σ.toMonoidHom (Units.map (algebraMap K L : K →* L) x) =
          Units.map (algebraMap K L : K →* L) x := by
        apply Units.ext
        exact σ.commutes (x : K)
      rw [hfix, mul_inv_cancel]⟩
  cocycle' σ τ := by
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Units.ext
    simp only [toMul_add, Subgroup.coe_mul, Units.val_mul]
    change (((Units.map (σ * τ).toMonoidHom α * α⁻¹ : Lˣ)) : L) =
      (((Units.map σ.toMonoidHom α * α⁻¹ : Lˣ)) : L) *
        (((Units.map σ.toMonoidHom (Units.map τ.toMonoidHom α * α⁻¹) : Lˣ)) : L)
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.coe_map]
    change (σ * τ) (α : L) * (α : L)⁻¹ =
      (σ (α : L) * (α : L)⁻¹) * σ (τ (α : L) * (α : L)⁻¹)
    rw [map_mul, map_inv₀]
    have hmul : (σ * τ) (α : L) = σ (τ (α : L)) := rfl
    have hσα : σ (α : L) ≠ 0 := by
      intro h0
      exact α.ne_zero (σ.injective (by rw [h0, map_zero]))
    rw [hmul]
    field_simp [α.ne_zero, hσα]

/-- Independence of choice of `m`-th root: changing `α` to `β` with `β^m = α^m` shifts
`kummerCocycle` by the 1-coboundary of `β / α ∈ μ_m(L)`. -/
theorem kummerCocycle_mk_eq_of_pow_eq (m : ℕ) {x : Kˣ} {α β : Lˣ}
    (hα : α ^ m = Units.map (algebraMap K L : K →* L) x)
    (hβ : β ^ m = Units.map (algebraMap K L : K →* L) x) :
    (QuotientAddGroup.mk (kummerCocycle K L m α hα) :
        H1Group (L ≃ₐ[K] L) (Additive (rootsOfUnity m L))) =
      QuotientAddGroup.mk (kummerCocycle K L m β hβ) := by
  rw [QuotientAddGroup.eq]
  let ζ : rootsOfUnity m L := ⟨β * α⁻¹, by
    rw [mem_rootsOfUnity, mul_pow, inv_pow, hβ, hα, mul_inv_cancel]⟩
  refine ⟨Additive.ofMul ζ, ?_⟩
  apply Cocycle1.ext
  intro σ
  apply Additive.toMul.injective
  apply Subtype.ext
  apply Units.ext
  simp only [coboundary1, kummerCocycle, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    Cocycle1.add_apply, Cocycle1.neg_apply, toMul_sub, toMul_add, toMul_neg,
    div_eq_mul_inv, Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul,
    Units.val_inv_eq_inv_val]
  change ((Units.map σ.toMonoidHom ζ.1 : Lˣ) : L) * ((ζ.1 : Lˣ) : L)⁻¹ =
    (((Units.map σ.toMonoidHom α * α⁻¹ : Lˣ)) : L)⁻¹ *
      (((Units.map σ.toMonoidHom β * β⁻¹ : Lˣ)) : L)
  simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.coe_map, ζ]
  change σ ((β : L) * (α : L)⁻¹) * ((β : L) * (α : L)⁻¹)⁻¹ =
    (σ (α : L) * (α : L)⁻¹)⁻¹ * (σ (β : L) * (β : L)⁻¹)
  rw [map_mul, map_inv₀]
  have hσα : σ (α : L) ≠ 0 := fun h0 => α.ne_zero (σ.injective (by rw [h0, map_zero]))
  have hσβ : σ (β : L) ≠ 0 := fun h0 => β.ne_zero (σ.injective (by rw [h0, map_zero]))
  field_simp [α.ne_zero, β.ne_zero, hσα, hσβ]

private def kummerSubgroupToH1 (m : ℕ) :
    kummerSubgroup K L m →* Multiplicative (H1Group (L ≃ₐ[K] L) (Additive (rootsOfUnity m L))) where
  toFun x :=
    Multiplicative.ofAdd
      (QuotientAddGroup.mk (kummerCocycle K L m
        (Classical.choose ((mem_kummerSubgroup_iff K L m x.1).mp x.2))
        (Classical.choose_spec ((mem_kummerSubgroup_iff K L m x.1).mp x.2))))
  map_one' := by
    apply Multiplicative.toAdd.injective
    change (QuotientAddGroup.mk (kummerCocycle K L m _ _) :
      H1Group (L ≃ₐ[K] L) (Additive (rootsOfUnity m L))) = 0
    have h1 : (1 : Lˣ) ^ m = Units.map (algebraMap K L : K →* L) 1 := by simp
    rw [kummerCocycle_mk_eq_of_pow_eq K L m _ h1, QuotientAddGroup.eq_zero_iff]
    refine ⟨0, ?_⟩
    apply Cocycle1.ext
    intro σ
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Units.ext
    simp [coboundary1, kummerCocycle]
  map_mul' x y := by
    apply Multiplicative.toAdd.injective
    change (QuotientAddGroup.mk (kummerCocycle K L m _ _) :
      H1Group (L ≃ₐ[K] L) (Additive (rootsOfUnity m L))) =
      QuotientAddGroup.mk (kummerCocycle K L m
        (Classical.choose ((mem_kummerSubgroup_iff K L m x.1).mp x.2))
        (Classical.choose_spec ((mem_kummerSubgroup_iff K L m x.1).mp x.2))) +
      QuotientAddGroup.mk (kummerCocycle K L m
        (Classical.choose ((mem_kummerSubgroup_iff K L m y.1).mp y.2))
        (Classical.choose_spec ((mem_kummerSubgroup_iff K L m y.1).mp y.2)))
    have hxy :
        (Classical.choose ((mem_kummerSubgroup_iff K L m x.1).mp x.2) *
          Classical.choose ((mem_kummerSubgroup_iff K L m y.1).mp y.2)) ^ m =
        Units.map (algebraMap K L : K →* L) (x.1 * y.1) := by
      rw [mul_pow, Classical.choose_spec ((mem_kummerSubgroup_iff K L m x.1).mp x.2),
        Classical.choose_spec ((mem_kummerSubgroup_iff K L m y.1).mp y.2), map_mul]
    rw [kummerCocycle_mk_eq_of_pow_eq K L m _ hxy]
    change QuotientAddGroup.mk (kummerCocycle K L m _ hxy) =
      QuotientAddGroup.mk (kummerCocycle K L m _ _ + kummerCocycle K L m _ _)
    congr 1
    apply Cocycle1.ext
    intro σ
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Units.ext
    set α := Classical.choose ((mem_kummerSubgroup_iff K L m x.1).mp x.2)
    set β := Classical.choose ((mem_kummerSubgroup_iff K L m y.1).mp y.2)
    simp only [kummerCocycle, Cocycle1.add_apply, toMul_add, Subgroup.coe_mul, Units.val_mul]
    change (((Units.map σ.toMonoidHom (α * β) * (α * β)⁻¹ : Lˣ)) : L) =
      (((Units.map σ.toMonoidHom α * α⁻¹ : Lˣ)) : L) *
        (((Units.map σ.toMonoidHom β * β⁻¹ : Lˣ)) : L)
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.coe_map]
    change σ ((α : L) * (β : L)) * ((α : L) * (β : L))⁻¹ =
      (σ (α : L) * (α : L)⁻¹) * (σ (β : L) * (β : L)⁻¹)
    rw [map_mul]
    field_simp [α.ne_zero, β.ne_zero]

private def kummerSubgroupProj (m : ℕ) : kummerSubgroup K L m →* KummerDomain K L m where
  toFun x := ⟨QuotientGroup.mk x.1, ⟨x.1, x.2, rfl⟩⟩
  map_one' := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl

private theorem kummerSubgroupProj_surjective (m : ℕ) :
    Function.Surjective (kummerSubgroupProj K L m) := by
  rintro ⟨_, x, hx, rfl⟩
  exact ⟨⟨x, hx⟩, rfl⟩

private theorem kummerSubgroupProj_ker_le (m : ℕ) :
    (kummerSubgroupProj K L m).ker ≤ (kummerSubgroupToH1 K L m).ker := by
  intro x hx
  rw [MonoidHom.mem_ker] at hx ⊢
  have h1 : (QuotientGroup.mk x.1 : Kˣ ⧸ (powMonoidHom (α := Kˣ) m).range) = 1 :=
    congrArg Subtype.val hx
  rw [QuotientGroup.eq_one_iff] at h1
  obtain ⟨y, hy⟩ := h1
  change y ^ m = x.1 at hy
  have hy_pow : (Units.map (algebraMap K L : K →* L) y) ^ m =
      Units.map (algebraMap K L : K →* L) x.1 := by
    rw [← map_pow, hy]
  apply Multiplicative.toAdd.injective
  change (QuotientAddGroup.mk (kummerCocycle K L m _ _) :
    H1Group (L ≃ₐ[K] L) (Additive (rootsOfUnity m L))) = 0
  rw [kummerCocycle_mk_eq_of_pow_eq K L m _ hy_pow, QuotientAddGroup.eq_zero_iff]
  refine ⟨0, ?_⟩
  apply Cocycle1.ext
  intro σ
  apply Additive.toMul.injective
  apply Subtype.ext
  apply Units.ext
  simp only [coboundary1, kummerCocycle, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    smul_zero, sub_self, toMul_zero, OneMemClass.coe_one, Units.val_one]
  change (1 : L) = (((Units.map σ.toMonoidHom (Units.map (algebraMap K L : K →* L) y) *
    (Units.map (algebraMap K L : K →* L) y)⁻¹ : Lˣ)) : L)
  simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.coe_map, MonoidHom.coe_coe]
  change (1 : L) = σ (algebraMap K L (y : K)) * (algebraMap K L (y : K))⁻¹
  rw [σ.commutes, mul_inv_cancel₀ ((map_ne_zero (algebraMap K L)).mpr y.ne_zero)]

/-- **Concrete Galois Kummer Homomorphism**
`δ : Additive (KummerDomain K L m) →+ H¹(Gal(L/K), μ_m(L))`,
sending `[x]` (`x = α^m`) to the cohomology class `[σ ↦ σ(α)/α]`. -/
def kummerMap (m : ℕ) :
    Additive (KummerDomain K L m) →+ H1Group (L ≃ₐ[K] L) (Additive (rootsOfUnity m L)) :=
  let mulHom : KummerDomain K L m →*
      Multiplicative (H1Group (L ≃ₐ[K] L) (Additive (rootsOfUnity m L))) :=
    (QuotientGroup.lift (kummerSubgroupProj K L m).ker
        (kummerSubgroupToH1 K L m) (kummerSubgroupProj_ker_le K L m)).comp
      (QuotientGroup.quotientKerEquivOfSurjective
        (kummerSubgroupProj K L m) (kummerSubgroupProj_surjective K L m)).symm.toMonoidHom
  { toFun := fun q => Multiplicative.toAdd (mulHom (Additive.toMul q))
    map_zero' := by change Multiplicative.toAdd (mulHom 1) = 0; rw [map_one]; rfl
    map_add' := fun a b => by
      change Multiplicative.toAdd (mulHom (Additive.toMul a * Additive.toMul b)) = _
      rw [map_mul]; rfl }

/-- Exact evaluation formula for `kummerMap K L m` on `x = α^m`. -/
theorem kummerMap_apply (m : ℕ) {x : Kˣ} (α : Lˣ)
    (hα : α ^ m = Units.map (algebraMap K L : K →* L) x) :
    kummerMap K L m (Additive.ofMul ⟨QuotientGroup.mk x, (mem_kummerDomain_iff K L m x).mpr ⟨α, hα⟩⟩) =
      QuotientAddGroup.mk (kummerCocycle K L m α hα) := by
  let e := QuotientGroup.quotientKerEquivOfSurjective
    (kummerSubgroupProj K L m) (kummerSubgroupProj_surjective K L m)
  have hsymm : e.symm ⟨QuotientGroup.mk x, (mem_kummerDomain_iff K L m x).mpr ⟨α, hα⟩⟩ =
      QuotientGroup.mk (⟨x, ⟨α, hα⟩⟩ : kummerSubgroup K L m) := by
    apply e.injective
    rw [e.apply_symm_apply]
    rfl
  change Multiplicative.toAdd (QuotientGroup.lift (kummerSubgroupProj K L m).ker
      (kummerSubgroupToH1 K L m) (kummerSubgroupProj_ker_le K L m)
      (e.symm ⟨QuotientGroup.mk x, (mem_kummerDomain_iff K L m x).mpr ⟨α, hα⟩⟩)) = _
  rw [hsymm]
  exact kummerCocycle_mk_eq_of_pow_eq K L m _ hα

/-- **Injectivity of the Galois Kummer Homomorphism** (`kummer_map_injective`):
for every finite Galois extension `L/K`, `δ : ((Lˣ)^m ∩ Kˣ) / (Kˣ)^m → H¹(Gal(L/K), μ_m(L))`
is INJECTIVE! -/
theorem kummer_map_injective [FiniteDimensional K L] [IsGalois K L] (m : ℕ) :
    Function.Injective (kummerMap K L m) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  rcases a with ⟨q, hq⟩
  induction q using QuotientGroup.induction_on with
  | H x =>
    obtain ⟨α, hα⟩ := (mem_kummerDomain_iff K L m x).mp hq
    have hmk0 : (QuotientAddGroup.mk (kummerCocycle K L m α hα) :
        H1Group (L ≃ₐ[K] L) (Additive (rootsOfUnity m L))) = 0 := by
      rw [← kummerMap_apply K L m α hα]
      exact ha
    rw [QuotientAddGroup.eq_zero_iff] at hmk0
    obtain ⟨ζa, hζa⟩ := hmk0
    let ζ : rootsOfUnity m L := Additive.toMul ζa
    have hfix : ∀ σ : L ≃ₐ[K] L, σ ((α : L) * ((ζ.1 : Lˣ) : L)⁻¹) = (α : L) * ((ζ.1 : Lˣ) : L)⁻¹ := by
      intro σ
      have hσ := congrArg (fun c : Cocycle1 (L ≃ₐ[K] L) (Additive (rootsOfUnity m L)) =>
        ((Additive.toMul (c σ)).1 : L)) hζa
      have hσ' : σ ((ζ.1 : Lˣ) : L) * ((ζ.1 : Lˣ) : L)⁻¹ = σ (α : L) * (α : L)⁻¹ := by
        simp only [coboundary1, kummerCocycle, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
          toMul_sub, div_eq_mul_inv, Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul,
          Units.val_inv_eq_inv_val] at hσ
        change (((Units.map σ.toMonoidHom ζ.1 : Lˣ) : L) * ((ζ.1 : Lˣ) : L)⁻¹) =
          (((Units.map σ.toMonoidHom α * α⁻¹ : Lˣ)) : L) at hσ
        simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.coe_map] at hσ
        exact hσ
      rw [map_mul, map_inv₀]
      have hσζ : σ ((ζ.1 : Lˣ) : L) ≠ 0 := fun h0 => ζ.1.ne_zero (σ.injective (by rw [h0, map_zero]))
      have hα0 : (α : L) ≠ 0 := α.ne_zero
      have hζ0 : ((ζ.1 : Lˣ) : L) ≠ 0 := ζ.1.ne_zero
      have hmul : σ (α : L) * ((ζ.1 : Lˣ) : L) = σ ((ζ.1 : Lˣ) : L) * (α : L) := by
        have h1 := congrArg (fun t => t * ((α : L) * ((ζ.1 : Lˣ) : L))) hσ'
        field_simp [hα0, hζ0] at h1
        rw [mul_comm (σ (α : L)), ← h1]
      field_simp [hζ0, hσζ]
      exact hmul
    obtain ⟨y, hy⟩ := exists_algebraMap_of_gal_fixed K L hfix
    have hy0 : y ≠ 0 := by
      intro h0
      rw [h0, map_zero] at hy
      exact mul_ne_zero α.ne_zero (inv_ne_zero ζ.1.ne_zero) hy.symm
    let yu : Kˣ := Units.mk0 y hy0
    have hy_pow : yu ^ m = x := by
      apply Units.ext
      apply (algebraMap K L).injective
      have hζm : ((ζ.1 : Lˣ) : L) ^ m = 1 := by
        have h1 : (ζ.1 : Lˣ) ^ m = 1 := (mem_rootsOfUnity m ζ.1).mp ζ.2
        simpa [Units.val_pow_eq_pow_val] using congrArg (fun u : Lˣ => (u : L)) h1
      have hαm : (α : L) ^ m = algebraMap K L (x : K) := by
        simpa [Units.val_pow_eq_pow_val] using congrArg (fun u : Lˣ => (u : L)) hα
      calc algebraMap K L ((yu ^ m : Kˣ) : K)
          = (algebraMap K L y) ^ m := by rw [Units.val_pow_eq_pow_val, map_pow]; rfl
        _ = ((α : L) * ((ζ.1 : Lˣ) : L)⁻¹) ^ m := by rw [hy]
        _ = (α : L) ^ m * (((ζ.1 : Lˣ) : L) ^ m)⁻¹ := by rw [mul_pow, inv_pow]
        _ = algebraMap K L (x : K) := by rw [hαm, hζm, inv_one, mul_one]
    apply Additive.toMul.injective
    apply Subtype.ext
    change (QuotientGroup.mk x : Kˣ ⧸ (powMonoidHom (α := Kˣ) m).range) = 1
    rw [QuotientGroup.eq_one_iff]
    exact ⟨yu, hy_pow⟩

/-- **Surjectivity of the Galois Kummer Homomorphism** (via Hilbert's Theorem 90!):
for every finite Galois extension `L/K`, `δ : ((Lˣ)^m ∩ Kˣ) / (Kˣ)^m → H¹(Gal(L/K), μ_m(L))`
is SURJECTIVE! -/
theorem kummer_map_surjective [FiniteDimensional K L] [IsGalois K L] (m : ℕ) :
    Function.Surjective (kummerMap K L m) := by
  intro q
  induction q using Quotient.inductionOn' with
  | h c =>
    let cL : Cocycle1 (L ≃ₐ[K] L) (Additive Lˣ) :=
      { toFun := fun σ => Additive.ofMul (Additive.toMul (c σ)).1
        cocycle' := fun σ τ => by
          have h := congrArg (fun z : Additive (rootsOfUnity m L) => (Additive.toMul z).1)
            (c.map_mul σ τ)
          exact congrArg Additive.ofMul h }
    obtain ⟨αa, hαa⟩ := hilbert90_cocycle_eq_coboundary K L cL
    let α : Lˣ := Additive.toMul αa
    have hfix : ∀ σ : L ≃ₐ[K] L, σ ((α : L) ^ m) = (α : L) ^ m := by
      intro σ
      have hσ := congrArg (fun f : Cocycle1 (L ≃ₐ[K] L) (Additive Lˣ) =>
        (Additive.toMul (f σ) : Lˣ)) hαa
      change (Additive.toMul (c σ)).1 = Units.map σ.toMonoidHom α * α⁻¹ at hσ
      have h1 : (Units.map σ.toMonoidHom α * α⁻¹) ^ m = 1 := by
        rw [← hσ]
        exact (mem_rootsOfUnity m _).mp (Additive.toMul (c σ)).2
      rw [mul_pow, inv_pow, ← map_pow] at h1
      have h2 := congrArg (fun u : Lˣ => (u : L)) (eq_of_mul_inv_eq_one h1)
      simpa [Units.val_pow_eq_pow_val] using h2
    obtain ⟨x0, hx0⟩ := exists_algebraMap_of_gal_fixed K L hfix
    have hx0_ne : x0 ≠ 0 := by
      intro h0
      rw [h0, map_zero] at hx0
      exact pow_ne_zero m α.ne_zero hx0.symm
    let x : Kˣ := Units.mk0 x0 hx0_ne
    have hα_pow : α ^ m = Units.map (algebraMap K L : K →* L) x := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val]
      change (α : L) ^ m = algebraMap K L x0
      exact hx0.symm
    refine ⟨Additive.ofMul ⟨QuotientGroup.mk x, (mem_kummerDomain_iff K L m x).mpr ⟨α, hα_pow⟩⟩, ?_⟩
    rw [kummerMap_apply K L m α hα_pow]
    congr 1
    apply Cocycle1.ext
    intro σ
    apply Additive.toMul.injective
    apply Subtype.ext
    have hσ := congrArg (fun f : Cocycle1 (L ≃ₐ[K] L) (Additive Lˣ) =>
      (Additive.toMul (f σ) : Lˣ)) hαa
    exact hσ.symm

/-- **Exact Galois Kummer Isomorphism** for every finite Galois extension `L/K`:
`Additive (((Lˣ)^m ∩ Kˣ) / (Kˣ)^m) ≃+ H¹(Gal(L/K), μ_m(L))`! -/
def kummerEquivH1 [FiniteDimensional K L] [IsGalois K L] (m : ℕ) :
    Additive (KummerDomain K L m) ≃+ H1Group (L ≃ₐ[K] L) (Additive (rootsOfUnity m L)) :=
  AddEquiv.ofBijective (kummerMap K L m)
    ⟨kummer_map_injective K L m, kummer_map_surjective K L m⟩

/-- When `L` contains `m`-th roots of all elements of `Kˣ`, the Kummer map is defined on ALL of
`Additive (Kˣ ⧸ (Kˣ)^m)` and gives `Additive (Kˣ ⧸ (Kˣ)^m) ≃+ H¹(Gal(L/K), μ_m(L))`. -/
def kummerMapFull (m : ℕ) (hdiv : ∀ x : Kˣ, ∃ α : Lˣ, α ^ m = Units.map (algebraMap K L : K →* L) x) :
    Additive (Kˣ ⧸ (powMonoidHom (α := Kˣ) m).range) →+
      H1Group (L ≃ₐ[K] L) (Additive (rootsOfUnity m L)) :=
  (kummerMap K L m).comp
    { toFun := fun q => Additive.ofMul ⟨Additive.toMul q, by
        induction hq : Additive.toMul q using QuotientGroup.induction_on with
        | H x => exact (mem_kummerDomain_iff K L m x).mpr (hdiv x)⟩
      map_zero' := rfl
      map_add' := fun _ _ => rfl }

theorem kummerMapFull_injective [FiniteDimensional K L] [IsGalois K L] (m : ℕ)
    (hdiv : ∀ x : Kˣ, ∃ α : Lˣ, α ^ m = Units.map (algebraMap K L : K →* L) x) :
    Function.Injective (kummerMapFull K L m hdiv) := by
  intro a b hab
  have h1 := kummer_map_injective K L m hab
  exact Additive.toMul.injective (congrArg (fun z => (Additive.toMul z).1) h1)

end Hilbert90AndKummerCohomology

/-! ## Section 5: Bridge to `Stage2GaloisCohomology` & Global Unramified-Outside-`S` Finiteness -/

section Stage2Bridge

/-- Concrete unramified-outside-`S` Galois cohomology subgroup inside `H¹(Gal(L/K), μ_m(L))`,
defined as the image of `KummerSelmer K S m ⊓ KummerDomain K L m` under the concrete Kummer map `δ`. -/
def H1Unram (K L : Type*) [Field K] [NumberField K] [Field L] [Algebra K L]
    (S : Finset (Place K)) (m : ℕ) :
    AddSubgroup (H1Group (L ≃ₐ[K] L) (Additive (rootsOfUnity m L))) :=
  AddSubgroup.map (kummerMap K L m)
    ((KummerSelmer K S m).subgroupOf (KummerDomain K L m)).toAddSubgroup

/-- **Unconditional Finiteness & Explicit Order Bound for Concrete Unramified-Outside-`S`
Galois Cohomology `H¹_S(Gal(L/K), μ_m(L))`** on Mathlib's `NumberField`! -/
theorem finite_and_card_H1Unram (K L : Type*) [Field K] [NumberField K] [Field L] [Algebra K L]
    (S : Finset (Place K)) {m : ℕ} (hm : 0 < m) :
    Finite (H1Unram K L S m) ∧
      Nat.card (H1Unram K L S m) ≤ Nat.card (KummerSelmer K S m) := by
  have : Finite (KummerSelmer K S m) := kummerSelmer_finite K S hm
  let sub := ((KummerSelmer K S m).subgroupOf (KummerDomain K L m)).toAddSubgroup
  let toSel : sub → KummerSelmer K S m := fun x => ⟨(Additive.toMul x.1).1, x.2⟩
  have htoSel_inj : Function.Injective toSel := fun a b hab =>
    Subtype.ext (Additive.toMul.injective (Subtype.ext (congrArg (Subtype.val : KummerSelmer K S m → _) hab)))
  have : Finite sub := Finite.of_injective toSel htoSel_inj
  let mapSurj : sub → H1Unram K L S m := fun x => ⟨kummerMap K L m x.1, ⟨x.1, x.2, rfl⟩⟩
  have hmapSurj : Function.Surjective mapSurj := by
    rintro ⟨y, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  refine ⟨Finite.of_surjective mapSurj hmapSurj, ?_⟩
  exact (Nat.card_le_card_of_surjective mapSurj hmapSurj).trans
    (Nat.card_le_card_of_injective toSel htoSel_inj)

/-- Explicit Dirichlet–Class-Group upper bound on `H1Unram K L S m`:
`|H¹_S(Gal(L/K), μ_m(L))| ≤ gcd(w_K, m) * m ^ (rk((𝒪_K)ˣ) + |S|) * |Cl_S(K)[m]|`! -/
theorem card_H1Unram_le_exact (K L : Type*) [Field K] [NumberField K] [Field L] [Algebra K L]
    (S : Finset (Place K)) {m : ℕ} (hm : 0 < m) :
    Nat.card (H1Unram K L S m) ≤
      Nat.gcd (NumberField.Units.torsionOrder K) m * m ^ (NumberField.Units.rank K + S.card) *
        Nat.card (SClassGroupTorsion K S m) := by
  rw [← card_kummerSelmer_exact_formula K S hm]
  exact (finite_and_card_H1Unram K L S hm).2

/-- Concrete Kummer dual Galois group `Hom(KummerSelmer K S m, ZMod m)` — the maximal abelian
exponent-`m` Galois group of `K` unramified outside `S`! -/
abbrev KummerUnramGal (K : Type*) [Field K] [NumberField K]
    (S : Finset (Place K)) (m : ℕ) : Type _ :=
  KummerSelmer K S m →* Multiplicative (ZMod m)

/-- Unconditional finiteness of `KummerUnramGal K S m` for every number field `K`, finite `S`,
and `m ≥ 1`. -/
theorem kummerUnramGal_finite (K : Type*) [Field K] [NumberField K]
    (S : Finset (Place K)) {m : ℕ} (hm : 0 < m) :
    Finite (KummerUnramGal K S m) := by
  have : NeZero m := ⟨hm.ne'⟩
  have : Finite (KummerSelmer K S m) := kummerSelmer_finite K S hm
  exact Finite.of_injective
    (fun f : KummerUnramGal K S m => (f : KummerSelmer K S m → Multiplicative (ZMod m)))
    (fun _ _ h => MonoidHom.ext (congrFun h))

/-- **Direct Bridge into `Stage2GaloisCohomology.global_selmer_unramified_outside_S_finite`
via Concrete Number-Field `KummerSelmer L S_L m`**:
for ANY number field `L`, ANY finite set of places `S_L`, ANY `m ≥ 1`, and ANY global Galois
action of `G` on a finite module `M` trivialized on a finite-index normal subgroup `N ⊴ G` whose
homomorphisms `N →* Multiplicative M` factor through the concrete finite Kummer Selmer group
`KummerSelmer L S_L m`, EVERY Selmer subgroup `Sel ≤ H¹(G, M)` is FINITE with explicit bound
`|Sel| ≤ |M|^[G : N] * |M|^(gcd(w_L, m) * m^(rk((𝒪_L)ˣ) + |S_L|) * |Cl_{S_L}(L)[m]|)`! -/
theorem numberField_global_selmer_unramified_outside_S_finite
    (L : Type*) [Field L] [NumberField L] (S_L : Finset (Place L)) {m : ℕ} (hm : 0 < m)
    {G M : Type*} [Group G] [AddCommGroup M] [DistribMulAction G M]
    (N : Subgroup G) [N.Normal] [Finite (G ⧸ N)] [Finite M]
    (htriv : ∀ (n : N) (a : M), (n : G) • a = a)
    (qMap : N →* KummerSelmer L S_L m)
    (hfactor : ∀ φ : N →* Multiplicative M,
      ∃ ψ : KummerSelmer L S_L m →* Multiplicative M, φ = ψ.comp qMap)
    (Sel : AddSubgroup (H1Group G M)) :
    Finite Sel ∧
      Nat.card Sel ≤
        Nat.card M ^ Nat.card (G ⧸ N) *
          Nat.card M ^ (Nat.gcd (NumberField.Units.torsionOrder L) m *
            m ^ (NumberField.Units.rank L + S_L.card) *
            Nat.card (SClassGroupTorsion L S_L m)) := by
  have : Finite (KummerSelmer L S_L m) := kummerSelmer_finite L S_L hm
  have hmain := Stage2GaloisCohomology.global_selmer_unramified_outside_S_finite
    N htriv qMap hfactor Sel
  rw [card_kummerSelmer_exact_formula L S_L hm] at hmain
  exact hmain

/-- **Dual Kummer-Galois Bridge into `Stage2GaloisCohomology.global_selmer_unramified_outside_S_finite`**:
same unconditional global Selmer finiteness when `N →* Multiplicative M` factors through the
concrete Kummer dual Galois group `KummerUnramGal L S_L m = Hom(K(S_L, m), μ_m)`. -/
theorem numberField_global_selmer_via_kummerUnramGal_finite
    (L : Type*) [Field L] [NumberField L] (S_L : Finset (Place L)) {m : ℕ} (hm : 0 < m)
    {G M : Type*} [Group G] [AddCommGroup M] [DistribMulAction G M]
    (N : Subgroup G) [N.Normal] [Finite (G ⧸ N)] [Finite M]
    (htriv : ∀ (n : N) (a : M), (n : G) • a = a)
    (qMap : N →* KummerUnramGal L S_L m)
    (hfactor : ∀ φ : N →* Multiplicative M,
      ∃ ψ : KummerUnramGal L S_L m →* Multiplicative M, φ = ψ.comp qMap)
    (Sel : AddSubgroup (H1Group G M)) :
    Finite Sel ∧
      Nat.card Sel ≤
        Nat.card M ^ Nat.card (G ⧸ N) * Nat.card M ^ Nat.card (KummerUnramGal L S_L m) := by
  have : Finite (KummerUnramGal L S_L m) := kummerUnramGal_finite L S_L hm
  exact Stage2GaloisCohomology.global_selmer_unramified_outside_S_finite
    N htriv qMap hfactor Sel

end Stage2Bridge

end RHDirect.Stage5NumberFieldCohom
