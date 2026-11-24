import RHDirect.CFT_AbstractLocalReciprocity
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.IntUnitsPower
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.Data.ZMod.Units
import Mathlib.FieldTheory.AlgebraicClosure
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.GroupTheory.Torsion
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter
import Mathlib.NumberTheory.Cyclotomic.Gal
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.RingTheory.Frobenius
import Mathlib.RingTheory.Ideal.Over
import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients
import Mathlib.RingTheory.Invariant.Galois
import Mathlib.RingTheory.Invariant.Profinite
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity
import Mathlib.RingTheory.ZMod
import Mathlib.RingTheory.ZMod.UnitsCyclic
import Mathlib.Topology.Algebra.Group.Units

/-!
# RHDirect.CFT_CyclotomicCharacters

Global Cyclotomic Characters & Profinite / `p`-adic Decomposition:
- `Frobenius`: arithmetic Frobenius on cyclotomic extensions `ℚ(ζ_m)/ℚ`.
- `Character`: global cyclotomic character `Gal(ℚ̄/ℚ) →* ℤ̂ˣ`, surjectivity, continuity,
  and action on roots of unity.
- `ProfinitePadic`: Chinese remainder homeomorphism `ℤ̂ ≃ₜ ∏_p ℤ_p` and `ℤ̂ˣ ≃* ∏_p ℤ_pˣ`.
- `ClosedSubgroups`: closed subgroups of `ℤ_ℓ` and `ℤ̂`.
- `PadicUnitsLog`: `p`-adic logarithm `ℤ_ℓˣ →* Multiplicative ℤ_ℓ` and torsion splitting.
- `Degree`: degrees of cyclotomic extensions and Galois image characterization.
- `DegreeDecomposition`: Kronecker-Weber / cyclotomic degree decomposition over `ℚ̄`.
-/

open scoped RHDirect.CFT_AbstractLocalReciprocity
open RHDirect.CFT_AbstractLocalReciprocity

namespace RHDirect.CFT_CyclotomicCharacters

namespace Cyclotomic

section Sec_ContZModPowAux

private theorem continuous_toZModPow_aux :
    ∀ {ℓ : ℕ} [Fact (Nat.Prime ℓ)] (n : ℕ), Continuous (⇑(PadicInt.toZModPow n) : ℤ_[ℓ] → ZMod (ℓ ^ n)) := by
  intro ℓ hℓ n
  refine continuous_of_continuousAt_zero (PadicInt.toZModPow (p := ℓ) n) ?_
  have hpos : (0 : ℝ) < (ℓ : ℝ) ^ (-n : ℤ) :=
    zpow_pos (by exact_mod_cast hℓ.out.pos) _
  refine (continuousAt_const (y := (0 : ZMod (ℓ ^ n)))).congr ?_
  filter_upwards [Metric.closedBall_mem_nhds (0 : ℤ_[ℓ]) hpos] with x hx
  rw [mem_closedBall_zero_iff, PadicInt.norm_le_pow_iff_mem_span_pow,
    ← PadicInt.ker_toZModPow, RingHom.mem_ker] at hx
  exact hx.symm

end Sec_ContZModPowAux

section Sec_CC_Frobenius

open NumberField



section Frobenius

variable {m : ℕ} [NeZero m] (p : ℕ) [hp : Fact p.Prime] (K : Type*) [Field K] [NumberField K]
  [IsCyclotomicExtension {m} ℚ K]

variable (P : Ideal (𝓞 K)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})]

omit [P.IsPrime] in
include hp in

theorem ne_bot_of_liesOver : P ≠ ⊥ :=
  Ideal.ne_bot_of_liesOver_of_ne_bot (p := Ideal.span {(p : ℤ)})
    (by simpa using hp.out.ne_zero) P

omit [P.IsPrime] in
include hp in

theorem finite_quotient : Finite (𝓞 K ⧸ P) :=
  have : NeZero P := ⟨ne_bot_of_liesOver p K P⟩
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne P)

omit hp [NumberField K] [P.IsPrime] in

theorem card_quotient_under : Nat.card (ℤ ⧸ P.under ℤ) = p := by
  rw [← Ideal.LiesOver.over (P := P) (p := Ideal.span {(p : ℤ)}),
    Nat.card_congr (Int.quotientSpanNatEquivZMod p).toEquiv, Nat.card_zmod]

omit [NeZero m] hp [NumberField K] [IsCyclotomicExtension {m} ℚ K] [P.IsPrime] in

theorem natCast_notMem_of_not_dvd (hm : ¬ p ∣ m) : ((m : ℕ) : 𝓞 K) ∉ P := by
  intro h
  have : ((m : ℤ)) ∈ P.under ℤ := by
    rw [Ideal.under, Ideal.mem_comap]; simpa using h
  rw [← Ideal.LiesOver.over (P := P) (p := Ideal.span {(p : ℤ)}), Ideal.mem_span_singleton] at this
  exact hm (Int.natCast_dvd_natCast.mp this)

theorem eq_of_forall_pow_eq_one {σ τ : Gal(K/ℚ)}
    (h : ∀ x : K, x ^ m = 1 → σ x = τ x) : σ = τ := by
  have hζ := IsCyclotomicExtension.zeta_spec m ℚ K
  apply (IsCyclotomicExtension.Rat.galEquivZMod m K).injective
  have h₁ := IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq m K σ hζ.pow_eq_one
  have h₂ := IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq m K τ hζ.pow_eq_one
  rw [h _ hζ.pow_eq_one, h₂] at h₁
  rw [Units.ext_iff]
  exact ZMod.val_injective _ (hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) h₁.symm)

omit hp [IsCyclotomicExtension {m} ℚ K] [P.IsPrime] in

theorem IsArithFrobAt.apply_of_pow_eq_one (hm : ¬ p ∣ m) {σ : Gal(K/ℚ)}
    (hσ : IsArithFrobAt ℤ σ P) {x : K} (hx : x ^ m = 1) : σ x = x ^ p := by
  have hxi : IsIntegral ℤ x := by
    refine ⟨Polynomial.X ^ m - 1, Polynomial.monic_X_pow_sub_C 1 (NeZero.ne m), ?_⟩
    simp [hx]
  let y : 𝓞 K := ⟨x, hxi⟩
  have hy : y ^ m = 1 := by
    apply RingOfIntegers.ext
    exact hx
  have h := AlgHom.IsArithFrobAt.apply_of_pow_eq_one hσ hy
    (natCast_notMem_of_not_dvd p K P hm)
  rw [card_quotient_under p K P] at h
  exact congrArg (fun z : 𝓞 K => (z : K)) h

theorem isArithFrobAt_iff (hm : ¬ p ∣ m) (σ : Gal(K/ℚ)) :
    IsArithFrobAt ℤ σ P ↔ ∀ x : K, x ^ m = 1 → σ x = x ^ p := by
  refine ⟨fun hσ x hx => IsArithFrobAt.apply_of_pow_eq_one p K P hm hσ hx, fun h => ?_⟩
  have : IsGalois ℚ K := IsCyclotomicExtension.isGalois {m} ℚ K
  have : Finite (𝓞 K ⧸ P) := finite_quotient p K P
  obtain ⟨τ, hτ⟩ := IsArithFrobAt.exists_of_isInvariant ℤ Gal(K/ℚ) P
  have : σ = τ := eq_of_forall_pow_eq_one (m := m) K fun x hx => by
    rw [h x hx, IsArithFrobAt.apply_of_pow_eq_one p K P hm hτ hx]
  rwa [this]

theorem existsUnique_isArithFrobAt (hm : ¬ p ∣ m) : ∃! σ : Gal(K/ℚ), IsArithFrobAt ℤ σ P := by
  have : IsGalois ℚ K := IsCyclotomicExtension.isGalois {m} ℚ K
  have : Finite (𝓞 K ⧸ P) := finite_quotient p K P
  obtain ⟨τ, hτ⟩ := IsArithFrobAt.exists_of_isInvariant ℤ Gal(K/ℚ) P
  refine ⟨τ, hτ, fun σ hσ => eq_of_forall_pow_eq_one (m := m) K fun x hx => ?_⟩
  rw [IsArithFrobAt.apply_of_pow_eq_one p K P hm hσ hx,
    IsArithFrobAt.apply_of_pow_eq_one p K P hm hτ hx]

end Frobenius

end Sec_CC_Frobenius

section Sec_CC_Character

open NumberField IntermediateField
open scoped Pointwise




local notation "ℚ̄" => AlgebraicClosure ℚ

instance isAlgClosure_rat : IsAlgClosure ℚ ℚ̄ := by
  let i : Algebra ℚ ℚ̄ := AlgebraicClosure.instAlgebra ℚ (R := ℚ)
  have h : IsAlgClosure ℚ ℚ̄ := inferInstance
  convert h
  exact Subsingleton.elim _ _

section FixingSubgroup

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

theorem mem_fixingSubgroup_adjoin_iff (S : Set E) (σ : Gal(E/F)) :
    σ ∈ (adjoin F S).fixingSubgroup ↔ ∀ x ∈ S, σ x = x := by
  rw [IntermediateField.mem_fixingSubgroup_iff]
  refine ⟨fun h x hx => h x (subset_adjoin F S hx), fun h x hx => ?_⟩
  have := adjoin_algHom_ext F (φ₁ := (σ : E →ₐ[F] E).comp (adjoin F S).val)
    (φ₂ := (adjoin F S).val) (fun y hy => h y hy)
  exact congrArg (fun φ : adjoin F S →ₐ[F] E => φ ⟨x, hx⟩) this

end FixingSubgroup

section Fields

noncomputable def rootsOfUnityField (n : ℕ) : IntermediateField ℚ ℚ̄ :=
  adjoin ℚ {x : ℚ̄ | x ^ n = 1}

noncomputable def maxCyclotomic : IntermediateField ℚ ℚ̄ :=
  adjoin ℚ {x : ℚ̄ | ∃ n : ℕ, 0 < n ∧ x ^ n = 1}

theorem maxCyclotomic_eq_iSup : maxCyclotomic = ⨆ n : ℕ+, rootsOfUnityField n := by
  refine le_antisymm (adjoin_le_iff.mpr ?_) (iSup_le fun n => adjoin_le_iff.mpr ?_)
  · rintro x ⟨n, hn, hx⟩
    exact le_iSup (fun n : ℕ+ => rootsOfUnityField n) ⟨n, hn⟩ (subset_adjoin ℚ _ hx)
  · intro x hx
    exact subset_adjoin ℚ _ ⟨n, n.pos, hx⟩

theorem rootsOfUnityField_eq_adjoin {n : ℕ} [NeZero n] {ζ : ℚ̄} (hζ : IsPrimitiveRoot ζ n) :
    rootsOfUnityField n = ℚ⟮ζ⟯ := by
  refine le_antisymm (adjoin_le_iff.mpr fun x hx => ?_) (adjoin_le_iff.mpr ?_)
  · obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hx
    exact pow_mem (mem_adjoin_simple_self ℚ ζ) i
  · rw [Set.singleton_subset_iff]
    exact subset_adjoin ℚ _ hζ.pow_eq_one

instance (n : ℕ) [NeZero n] : IsCyclotomicExtension {n} ℚ (rootsOfUnityField n) := by
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot ℚ̄ n
  rw [rootsOfUnityField_eq_adjoin hζ]
  exact hζ.intermediateField_adjoin_isCyclotomicExtension ℚ

instance (n : ℕ) [NeZero n] : NumberField (rootsOfUnityField n) :=
  IsCyclotomicExtension.numberField {n} ℚ _

instance (n : ℕ) [NeZero n] : IsGalois ℚ (rootsOfUnityField n) :=
  IsCyclotomicExtension.isGalois {n} ℚ _

end Fields

section Modular

theorem pow_val_natCast {M : Type*} [Monoid M] {n : ℕ} {t : M} (ht : t ^ n = 1) (k : ℕ) :
    t ^ (k : ZMod n).val = t ^ k := by
  rw [ZMod.val_natCast]
  conv_rhs => rw [← Nat.mod_add_div k n, pow_add, pow_mul, ht, one_pow, mul_one]

theorem pow_val_one {M : Type*} [Monoid M] {n : ℕ} {t : M} (ht : t ^ n = 1) :
    t ^ (1 : ZMod n).val = t := by
  have := pow_val_natCast ht 1
  rwa [Nat.cast_one, pow_one] at this

theorem natCard_rootsOfUnity (n : ℕ) [NeZero n] : Nat.card (rootsOfUnity n ℚ̄) = n :=
  HasEnoughRootsOfUnity.natCard_rootsOfUnity ℚ̄ n

noncomputable def modCharacter (n : ℕ) [NeZero n] : Gal(ℚ̄/ℚ) →* (ZMod n)ˣ :=
  (modularCyclotomicCharacter ℚ̄ (natCard_rootsOfUnity n)).comp
    (MulSemiringAction.toRingAut Gal(ℚ̄/ℚ) ℚ̄)

variable {n : ℕ} [NeZero n]

theorem modCharacter_spec (σ : Gal(ℚ̄/ℚ)) {t : ℚ̄} (ht : t ^ n = 1) :
    σ t = t ^ (modCharacter n σ : ZMod n).val := by
  have ht0 : t ≠ 0 := by
    rintro rfl
    simp [NeZero.ne n] at ht
  have hmem : Units.mk0 t ht0 ∈ rootsOfUnity n ℚ̄ := by
    rw [mem_rootsOfUnity]; ext; simpa using ht
  exact modularCyclotomicCharacter.spec ℚ̄ (natCard_rootsOfUnity n)
    (MulSemiringAction.toRingAut Gal(ℚ̄/ℚ) ℚ̄ σ) hmem

theorem modCharacter_unique (σ : Gal(ℚ̄/ℚ)) {c : ZMod n}
    (hc : ∀ t : ℚ̄, t ^ n = 1 → σ t = t ^ c.val) : (modCharacter n σ : ZMod n) = c := by
  refine (modularCyclotomicCharacter.unique ℚ̄ (natCard_rootsOfUnity n)
    (MulSemiringAction.toRingAut Gal(ℚ̄/ℚ) ℚ̄ σ) fun t ht => ?_).symm
  have ht' : (t : ℚ̄) ^ n = 1 := by
    rw [mem_rootsOfUnity] at ht
    simpa using congrArg Units.val ht
  simpa using hc t ht'

theorem modCharacter_eq_of_apply {ζ : ℚ̄} (hζ : IsPrimitiveRoot ζ n) {σ : Gal(ℚ̄/ℚ)}
    {c : ZMod n} (h : σ ζ = ζ ^ c.val) : (modCharacter n σ : ZMod n) = c := by
  refine modCharacter_unique σ fun t ht => ?_
  obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one ht
  rw [map_pow, h, ← pow_mul, ← pow_mul, mul_comm]

theorem castHom_modCharacter {m : ℕ} [NeZero m] (h : m ∣ n) (σ : Gal(ℚ̄/ℚ)) :
    ZMod.castHom h (ZMod m) (modCharacter n σ : ZMod n) = modCharacter m σ := by
  refine (modCharacter_unique σ fun t ht => ?_).symm
  have ht' : t ^ n = 1 := by
    obtain ⟨k, rfl⟩ := h
    rw [pow_mul, ht, one_pow]
  rw [modCharacter_spec σ ht', ZMod.castHom_apply]
  conv_rhs => rw [← ZMod.natCast_zmod_val (modCharacter n σ : ZMod n), ZMod.cast_natCast h,
    pow_val_natCast ht]

theorem modCharacter_eq_one {ζ : ℚ̄} (hζ : IsPrimitiveRoot ζ n) {σ : Gal(ℚ̄/ℚ)} (h : σ ζ = ζ) :
    modCharacter n σ = 1 := by
  refine Units.ext (modCharacter_eq_of_apply hζ ?_)
  rw [Units.val_one, pow_val_one hζ.pow_eq_one, h]

theorem continuous_modCharacter (n : ℕ) [NeZero n] :
    Continuous fun σ : Gal(ℚ̄/ℚ) => (modCharacter n σ : ZMod n) := by
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot ℚ̄ n
  have : FiniteDimensional ℚ ℚ⟮ζ⟯ := adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral ζ)
  have hU := (ℚ⟮ζ⟯).fixingSubgroup_isOpen
  rw [continuous_discrete_rng]
  intro b
  rw [isOpen_iff_forall_mem_open]
  intro σ hσ
  refine ⟨σ • ((ℚ⟮ζ⟯).fixingSubgroup : Set Gal(ℚ̄/ℚ)), ?_, hU.smul σ,
    ⟨1, one_mem _, mul_one σ⟩⟩
  rintro _ ⟨τ, hτ, rfl⟩
  have hτζ : τ ζ = ζ := (mem_fixingSubgroup_iff _ τ).mp hτ ζ (mem_adjoin_simple_self ℚ ζ)
  simp only [Set.mem_preimage, Set.mem_singleton_iff, smul_eq_mul, map_mul,
    modCharacter_eq_one hζ hτζ, mul_one] at hσ ⊢
  exact hσ

theorem exists_modCharacter_eq (n : ℕ) [NeZero n] (a : (ZMod n)ˣ) :
    ∃ σ : Gal(ℚ̄/ℚ), modCharacter n σ = a := by
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot ℚ̄ n
  have : IsCyclotomicExtension {n} ℚ ℚ⟮ζ⟯ := hζ.intermediateField_adjoin_isCyclotomicExtension ℚ
  have : NumberField ℚ⟮ζ⟯ := IsCyclotomicExtension.numberField {n} ℚ _
  let τ := (IsCyclotomicExtension.Rat.galEquivZMod n ℚ⟮ζ⟯).symm a
  let ζ' : ℚ⟮ζ⟯ := ⟨ζ, mem_adjoin_simple_self ℚ ζ⟩
  have hζ' : ζ' ^ n = 1 := Subtype.ext hζ.pow_eq_one
  have hτ := IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq n ℚ⟮ζ⟯ τ hζ'
  rw [MulEquiv.apply_symm_apply] at hτ
  refine ⟨τ.liftNormal ℚ̄, Units.ext (modCharacter_eq_of_apply hζ ?_)⟩
  have := AlgEquiv.liftNormal_commutes τ ℚ̄ ζ'
  rw [hτ, map_pow] at this
  exact this

end Modular

section Character

noncomputable def characterToZHat : Gal(ℚ̄/ℚ) →* ℤ̂ where
  toFun σ := ⟨fun n => (modCharacter n σ : ZMod n), mem_profiniteIntegers.mpr
    fun m n h => castHom_modCharacter h σ⟩
  map_one' := by
    ext n
    simp [ProfiniteInteger.proj_apply]
  map_mul' σ τ := by
    ext n
    simp [ProfiniteInteger.proj_apply]

noncomputable def character : Gal(ℚ̄/ℚ) →* ℤ̂ˣ :=
  characterToZHat.toHomUnits

@[simp] theorem proj_character (n : ℕ+) (σ : Gal(ℚ̄/ℚ)) :
    ProfiniteInteger.proj n (character σ : ℤ̂) = (modCharacter n σ : ZMod n) :=
  rfl

theorem character_spec (σ : Gal(ℚ̄/ℚ)) (n : ℕ+) {t : ℚ̄} (ht : t ^ (n : ℕ) = 1) :
    σ t = t ^ (ProfiniteInteger.proj n (character σ : ℤ̂)).val := by
  rw [proj_character]
  exact modCharacter_spec σ ht

theorem eq_character (σ : Gal(ℚ̄/ℚ)) (u : ℤ̂)
    (hu : ∀ (n : ℕ+) (t : ℚ̄), t ^ (n : ℕ) = 1 → σ t = t ^ (ProfiniteInteger.proj n u).val) :
    u = character σ := by
  ext n
  rw [proj_character, modCharacter_unique σ (hu n)]

theorem continuous_character_val : Continuous fun σ : Gal(ℚ̄/ℚ) => (character σ : ℤ̂) := by
  refine continuous_induced_rng.2 (continuous_pi fun n => ?_)
  exact continuous_modCharacter n

theorem continuous_character : Continuous character := by
  rw [Units.continuous_iff]
  refine ⟨continuous_character_val, ?_⟩
  have : (fun σ : Gal(ℚ̄/ℚ) => (((character σ)⁻¹ : ℤ̂ˣ) : ℤ̂)) = fun σ => (character σ⁻¹ : ℤ̂) := by
    funext σ; rw [map_inv]
  rw [this]
  exact continuous_character_val.comp continuous_inv

theorem character_surjective : Function.Surjective character := by
  intro u
  have : IsGalois ℚ ℚ̄ := IsAlgClosure.isGalois ℚ ℚ̄
  let N : ℕ → ℕ+ := fun k => ⟨(k + 1).factorial, Nat.factorial_pos _⟩
  have hdvd : ∀ {k l : ℕ}, k ≤ l → (N k : ℕ) ∣ N l := fun h =>
    Nat.factorial_dvd_factorial (Nat.succ_le_succ h)
  have hcont : ∀ n : ℕ+, Continuous fun σ : Gal(ℚ̄/ℚ) => ProfiniteInteger.proj n (character σ : ℤ̂) :=
    fun n => (ProfiniteInteger.continuous_proj n).comp continuous_character_val
  let S : ℕ → Set Gal(ℚ̄/ℚ) := fun k =>
    {σ | ProfiniteInteger.proj (N k) (character σ : ℤ̂) = ProfiniteInteger.proj (N k) (u : ℤ̂)}
  have hmono : ∀ k, S (k + 1) ⊆ S k := fun k σ hσ => by
    simp only [S, Set.mem_ofPred_eq] at hσ ⊢
    rw [← ProfiniteInteger.castHom_proj (hdvd k.le_succ) (character σ : ℤ̂), hσ,
      ProfiniteInteger.castHom_proj]
  have hne : ∀ k, (S k).Nonempty := fun k => by
    obtain ⟨σ, hσ⟩ := exists_modCharacter_eq (N k)
      (Units.map (ProfiniteInteger.proj (N k)).toMonoidHom u)
    refine ⟨σ, ?_⟩
    simp only [S, Set.mem_ofPred_eq, proj_character, hσ]
    rfl
  have hclosed : ∀ k, IsClosed (S k) := fun k => isClosed_eq (hcont (N k)) continuous_const
  obtain ⟨σ, hσ⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed S hmono hne
    (hclosed 0).isCompact hclosed
  rw [Set.mem_iInter] at hσ
  refine ⟨σ, Units.ext (ProfiniteInteger.ext fun n => ?_)⟩
  have hn : (n : ℕ) ∣ N n := Nat.dvd_factorial n.pos (Nat.le_succ n)
  rw [← ProfiniteInteger.castHom_proj hn (character σ : ℤ̂), ← ProfiniteInteger.castHom_proj hn,
    show ProfiniteInteger.proj (N n) (character σ : ℤ̂) = _ from hσ n]

theorem character_eq_one_iff (σ : Gal(ℚ̄/ℚ)) :
    character σ = 1 ↔ ∀ x : ℚ̄, (∃ n : ℕ, 0 < n ∧ x ^ n = 1) → σ x = x := by
  constructor
  · rintro h x ⟨n, hn, hx⟩
    obtain ⟨N, rfl⟩ : ∃ N : ℕ+, (N : ℕ) = n := ⟨⟨n, hn⟩, rfl⟩
    have := character_spec σ N hx
    rw [h, Units.val_one, map_one, pow_val_one hx] at this
    exact this
  · intro h
    refine Units.ext (eq_character σ 1 fun n t ht => ?_).symm
    rw [map_one, pow_val_one ht]
    exact h t ⟨n, n.pos, ht⟩

theorem ker_character : character.ker = maxCyclotomic.fixingSubgroup := by
  ext σ
  rw [MonoidHom.mem_ker, character_eq_one_iff, maxCyclotomic, mem_fixingSubgroup_adjoin_iff]
  rfl

theorem fixedField_ker_character : fixedField character.ker = maxCyclotomic := by
  have : IsGalois ℚ ℚ̄ := IsAlgClosure.isGalois ℚ ℚ̄
  rw [ker_character, InfiniteGalois.fixedField_fixingSubgroup]

end Character

section Frobenius

variable (m : ℕ) [NeZero m] (p : ℕ) [Fact p.Prime] (P : Ideal (𝓞 (rootsOfUnityField m)))
  [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})]

theorem isArithFrobAt_restrictNormal_iff (hm : ¬ p ∣ m) (σ : Gal(ℚ̄/ℚ)) :
    IsArithFrobAt ℤ (σ.restrictNormal (rootsOfUnityField m)) P ↔
      (modCharacter m σ : ZMod m) = p := by
  rw [isArithFrobAt_iff p _ P hm]
  constructor
  · intro h
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot ℚ̄ m
    let ζ' : rootsOfUnityField m := ⟨ζ, subset_adjoin ℚ _ hζ.pow_eq_one⟩
    have hζ' : ζ' ^ m = 1 := Subtype.ext hζ.pow_eq_one
    have := congrArg (algebraMap (rootsOfUnityField m) ℚ̄) (h ζ' hζ')
    rw [AlgEquiv.restrictNormal_commutes, map_pow] at this
    refine modCharacter_eq_of_apply hζ ?_
    rw [pow_val_natCast hζ.pow_eq_one]
    exact this
  · intro h x hx
    have hx' : (algebraMap (rootsOfUnityField m) ℚ̄ x) ^ m = 1 := by
      rw [← map_pow, hx, map_one]
    apply (algebraMap (rootsOfUnityField m) ℚ̄).injective
    rw [AlgEquiv.restrictNormal_commutes, map_pow, modCharacter_spec σ hx', h,
      pow_val_natCast hx']

end Frobenius

section Padic

variable (ℓ : ℕ) [hℓ : Fact ℓ.Prime]

def primePowPNat (k : ℕ) : ℕ+ := ⟨ℓ ^ k, pow_pos hℓ.out.pos k⟩

@[simp] theorem coe_primePowPNat (k : ℕ) : (primePowPNat ℓ k : ℕ) = ℓ ^ k := rfl

noncomputable def toPadicInt : ℤ̂ →+* ℤ_[ℓ] :=
  PadicInt.lift (f := fun k => ProfiniteInteger.proj (primePowPNat ℓ k))
    fun k₁ k₂ hk => by
      ext x
      exact ProfiniteInteger.castHom_proj (m := primePowPNat ℓ k₁) (n := primePowPNat ℓ k₂)
        (pow_dvd_pow ℓ hk) x

theorem toZModPow_toPadicInt (k : ℕ) (x : ℤ̂) :
    PadicInt.toZModPow k (toPadicInt ℓ x) =
      ProfiniteInteger.proj (primePowPNat ℓ k) x :=
  RingHom.congr_fun (PadicInt.lift_spec _ k) x

theorem toPadicInt_character (σ : Gal(ℚ̄/ℚ)) :
    toPadicInt ℓ (character σ : ℤ̂) =
      (cyclotomicCharacter ℚ̄ ℓ (MulSemiringAction.toRingAut Gal(ℚ̄/ℚ) ℚ̄ σ) : ℤ_[ℓ]) := by
  refine PadicInt.ext_of_toZModPow.mp fun k => ?_
  rw [toZModPow_toPadicInt, cyclotomicCharacter.toZModPow, proj_character]
  rfl

end Padic

end Sec_CC_Character

section Sec_CC_ProfinitePadic

instance factPrime (q : Nat.Primes) : Fact (q : ℕ).Prime := ⟨q.2⟩

section Padic

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime]

theorem norm_sub_le_of_toZModPow_eq {x y : ℤ_[ℓ]} {n : ℕ}
    (h : PadicInt.toZModPow n x = PadicInt.toZModPow n y) :
    ‖x - y‖ ≤ (ℓ : ℝ) ^ (-(n : ℤ)) := by
  rw [PadicInt.norm_le_pow_iff_mem_span_pow, ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub,
    h, sub_self]

theorem exists_zpow_neg_lt {ε : ℝ} (hε : 0 < ε) : ∃ n : ℕ, (ℓ : ℝ) ^ (-(n : ℤ)) < ε := by
  have h1 : (1 : ℝ) < ℓ := by exact_mod_cast hℓ.out.one_lt
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε (inv_lt_one_of_one_lt₀ h1)
  exact ⟨n, by rwa [zpow_neg, zpow_natCast, ← inv_pow]⟩

theorem continuous_toZModPow (n : ℕ) : Continuous (PadicInt.toZModPow (p := ℓ) n) :=
  continuous_toZModPow_aux n

theorem continuous_of_continuous_toZModPow {X : Type*} [TopologicalSpace X] {f : X → ℤ_[ℓ]}
    (h : ∀ n, Continuous fun x => PadicInt.toZModPow n (f x)) : Continuous f := by
  refine continuous_iff_continuousAt.2 fun x => Metric.tendsto_nhds.2 fun ε hε => ?_
  obtain ⟨n, hn⟩ := exists_zpow_neg_lt (ℓ := ℓ) hε
  have hU : IsOpen {y | PadicInt.toZModPow n (f y) = PadicInt.toZModPow n (f x)} :=
    (isOpen_discrete {PadicInt.toZModPow n (f x)}).preimage (h n)
  filter_upwards [hU.mem_nhds rfl] with y hy
  rw [dist_eq_norm]
  exact (norm_sub_le_of_toZModPow_eq hy).trans_lt hn

variable (ℓ) in

theorem continuous_toPadicInt : Continuous (toPadicInt ℓ) :=
  continuous_of_continuous_toZModPow fun n =>
    (ProfiniteInteger.continuous_proj (primePowPNat ℓ n)).congr fun x =>
      (toZModPow_toPadicInt ℓ n x).symm

end Padic

section CRT

theorem equivPi_apply {n : ℕ} (hn : n ≠ 0) (z : ZMod n) (p : n.primeFactors) :
    ZMod.equivPi n hn z p = ZMod.castHom (Nat.ordProj_dvd n p) _ z :=
  RingHom.congr_fun (Subsingleton.elim
    ((Pi.evalRingHom (fun p : n.primeFactors => ZMod ((p : ℕ) ^ n.factorization p)) p).comp
      (ZMod.equivPi n hn).toRingHom) (ZMod.castHom (Nat.ordProj_dvd n p) _)) z

theorem eq_of_castHom_ordProj_eq {n : ℕ} (hn : n ≠ 0) {a b : ZMod n}
    (h : ∀ p ∈ n.primeFactors,
      ZMod.castHom (Nat.ordProj_dvd n p) (ZMod (p ^ n.factorization p)) a =
        ZMod.castHom (Nat.ordProj_dvd n p) _ b) : a = b :=
  (ZMod.equivPi n hn).injective (funext fun p => by rw [equivPi_apply, equivPi_apply, h p p.2])

theorem castHom_castHom {k m n : ℕ} (h₁ : k ∣ m) (h₂ : m ∣ n) (h₃ : k ∣ n) (z : ZMod n) :
    ZMod.castHom h₁ (ZMod k) (ZMod.castHom h₂ (ZMod m) z) = ZMod.castHom h₃ (ZMod k) z :=
  RingHom.congr_fun (Subsingleton.elim ((ZMod.castHom h₁ (ZMod k)).comp (ZMod.castHom h₂ (ZMod m)))
    (ZMod.castHom h₃ (ZMod k))) z

end CRT

section Product

noncomputable def padicReduceHom (n : ℕ) :
    (∀ q : Nat.Primes, ℤ_[q]) →+* ∀ p : n.primeFactors, ZMod ((p : ℕ) ^ n.factorization p) :=
  RingHom.pi fun p => (@PadicInt.toZModPow (p : ℕ) ⟨Nat.prime_of_mem_primeFactors p.2⟩
    (n.factorization p)).comp
      (Pi.evalRingHom (fun q : Nat.Primes => ℤ_[q]) ⟨p, Nat.prime_of_mem_primeFactors p.2⟩)

noncomputable def ofPadicsFamily (x : ∀ q : Nat.Primes, ℤ_[q]) (n : ℕ+) : ZMod n :=
  (ZMod.equivPi (n : ℕ) n.ne_zero).symm (padicReduceHom n x)

theorem castHom_ofPadicsFamily (x : ∀ q : Nat.Primes, ℤ_[q]) (n : ℕ+) {p : ℕ}
    (hp : p ∈ (n : ℕ).primeFactors) :
    ZMod.castHom (Nat.ordProj_dvd n p) _ (ofPadicsFamily x n) =
      @PadicInt.toZModPow p ⟨Nat.prime_of_mem_primeFactors hp⟩
        ((n : ℕ).factorization p) (x ⟨p, Nat.prime_of_mem_primeFactors hp⟩) := by
  have := equivPi_apply n.ne_zero (ofPadicsFamily x n) ⟨p, hp⟩
  rw [ofPadicsFamily, RingEquiv.apply_symm_apply] at this
  rw [ofPadicsFamily, ← this]
  rfl

theorem ofPadicsFamily_mem (x : ∀ q : Nat.Primes, ℤ_[q]) :
    ofPadicsFamily x ∈ profiniteIntegers := by
  rw [mem_profiniteIntegers]
  intro m n h
  refine eq_of_castHom_ordProj_eq m.ne_zero fun p hp => ?_
  have hpn : p ∈ (n : ℕ).primeFactors := Nat.primeFactors_mono h n.ne_zero hp
  have hle : (m : ℕ).factorization p ≤ (n : ℕ).factorization p :=
    (Nat.factorization_le_iff_dvd m.ne_zero n.ne_zero).2 h p
  rw [castHom_castHom _ h ((Nat.ordProj_dvd m p).trans h),
    ← castHom_castHom (pow_dvd_pow p hle) (Nat.ordProj_dvd n p) ((Nat.ordProj_dvd m p).trans h),
    castHom_ofPadicsFamily x n hpn, castHom_ofPadicsFamily x m hp]
  have : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hp⟩
  exact PadicInt.cast_toZModPow _ _ hle _

noncomputable def ofPadics : (∀ q : Nat.Primes, ℤ_[q]) →+* ℤ̂ :=
  RingHom.codRestrict
    (RingHom.pi fun n : ℕ+ => (ZMod.equivPi (n : ℕ) n.ne_zero).symm.toRingHom.comp
      (padicReduceHom n)) profiniteIntegers ofPadicsFamily_mem

theorem proj_ofPadics (x : ∀ q : Nat.Primes, ℤ_[q]) (n : ℕ+) :
    ProfiniteInteger.proj n (ofPadics x) = ofPadicsFamily x n :=
  rfl

noncomputable def toPadics : ℤ̂ →+* ∀ q : Nat.Primes, ℤ_[q] :=
  RingHom.pi fun q => toPadicInt q

@[simp] theorem toPadics_apply (x : ℤ̂) (q : Nat.Primes) : toPadics x q = toPadicInt q x :=
  rfl

theorem toPadics_ofPadics (x : ∀ q : Nat.Primes, ℤ_[q]) : toPadics (ofPadics x) = x := by
  funext q
  refine PadicInt.ext_of_toZModPow.mp fun k => ?_
  rw [toPadics_apply, toZModPow_toPadicInt, proj_ofPadics]
  refine eq_of_castHom_ordProj_eq (primePowPNat q k).ne_zero fun p hp => ?_
  have hpq : p = q := by
    have hk : k ≠ 0 := by
      rintro rfl
      simp at hp
    rw [coe_primePowPNat, Nat.primeFactors_prime_pow hk q.2, Finset.mem_singleton] at hp
    exact hp
  subst hpq
  have hle : (primePowPNat (q : ℕ) k : ℕ).factorization q ≤ k := by
    simp [coe_primePowPNat, Nat.factorization_pow, Nat.Prime.factorization_self q.2]
  rw [castHom_ofPadicsFamily x _ hp]
  exact (PadicInt.cast_toZModPow _ _ hle _).symm

theorem ofPadics_toPadics (x : ℤ̂) : ofPadics (toPadics x) = x := by
  ext n
  refine eq_of_castHom_ordProj_eq n.ne_zero fun p hp => ?_
  rw [proj_ofPadics, castHom_ofPadicsFamily _ n hp]
  have : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hp⟩
  change PadicInt.toZModPow _ (toPadicInt p x) = _
  rw [toZModPow_toPadicInt]
  exact (ProfiniteInteger.castHom_proj (m := primePowPNat p ((n : ℕ).factorization p))
    (Nat.ordProj_dvd n p) x).symm

noncomputable def padicEquiv : ℤ̂ ≃+* ∀ q : Nat.Primes, ℤ_[q] :=
  RingEquiv.ofRingHom toPadics ofPadics (RingHom.ext toPadics_ofPadics)
    (RingHom.ext ofPadics_toPadics)

@[simp] theorem padicEquiv_apply (x : ℤ̂) : padicEquiv x = toPadics x := rfl

@[simp] theorem padicEquiv_symm_apply (x : ∀ q : Nat.Primes, ℤ_[q]) :
    padicEquiv.symm x = ofPadics x := rfl

theorem continuous_toPadics : Continuous toPadics :=
  continuous_pi fun q => continuous_toPadicInt q

noncomputable def padicHomeomorph : ℤ̂ ≃ₜ ∀ q : Nat.Primes, ℤ_[q] :=
  Continuous.homeoOfEquivCompactToT2 (f := padicEquiv.toEquiv) continuous_toPadics

theorem continuous_ofPadics : Continuous ofPadics :=
  padicHomeomorph.symm.continuous

theorem toPadics_injective : Function.Injective toPadics :=
  padicEquiv.injective

theorem ext_toPadicInt {x y : ℤ̂} (h : ∀ q : Nat.Primes, toPadicInt q x = toPadicInt q y) :
    x = y :=
  toPadics_injective (funext h)

noncomputable def unitsPadicEquiv : ℤ̂ˣ ≃* ∀ q : Nat.Primes, ℤ_[q]ˣ :=
  (Units.mapEquiv padicEquiv.toMulEquiv).trans MulEquiv.piUnits

@[simp] theorem val_unitsPadicEquiv_apply (u : ℤ̂ˣ) (q : Nat.Primes) :
    (unitsPadicEquiv u q : ℤ_[q]) = toPadicInt q u :=
  rfl

theorem unitsPadicEquiv_apply (u : ℤ̂ˣ) (q : Nat.Primes) :
    unitsPadicEquiv u q = Units.map (toPadicInt q).toMonoidHom u :=
  Units.ext rfl

end Product

end Sec_CC_ProfinitePadic

section Sec_CC_ClosedSubgroups

open Filter Topology




section Padic

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime]

theorem mul_mem_of_isClosed (H : AddSubgroup ℤ_[ℓ]) (hH : IsClosed (H : Set ℤ_[ℓ])) {x : ℤ_[ℓ]}
    (hx : x ∈ H) (t : ℤ_[ℓ]) : x * t ∈ H :=
  PadicInt.denseRange_natCast.induction_on t (hH.preimage (continuous_const.mul continuous_id))
    fun k => by
      show x * (k : ℤ_[ℓ]) ∈ H
      rw [mul_comm, ← nsmul_eq_mul]
      exact H.nsmul_mem hx k

theorem isOpen_of_isClosed_of_ne_zero (H : AddSubgroup ℤ_[ℓ]) (hH : IsClosed (H : Set ℤ_[ℓ]))
    {x : ℤ_[ℓ]} (hx : x ∈ H) (hx0 : x ≠ 0) : IsOpen (H : Set ℤ_[ℓ]) := by
  obtain ⟨u, hu⟩ : ∃ u : ℤ_[ℓ]ˣ, x = u * (ℓ : ℤ_[ℓ]) ^ x.valuation :=
    ⟨_, PadicInt.unitCoeff_spec hx0⟩
  set v := x.valuation
  rw [Metric.isOpen_iff]
  intro y hy
  refine ⟨(ℓ : ℝ) ^ (-(v : ℤ)), zpow_pos (by exact_mod_cast hℓ.out.pos) _, fun w hw => ?_⟩
  have h1 : w - y ∈ Ideal.span {(ℓ : ℤ_[ℓ]) ^ v} :=
    (PadicInt.norm_le_pow_iff_mem_span_pow _ _).1 (by
      rw [← dist_eq_norm]; exact (Metric.mem_ball.1 hw).le)
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 h1
  have h2 : x * (↑u⁻¹ * t) = w - y := by
    rw [← ht, hu, show (u : ℤ_[ℓ]) * (ℓ : ℤ_[ℓ]) ^ v * (↑u⁻¹ * t) =
      ((u : ℤ_[ℓ]) * ↑u⁻¹) * t * (ℓ : ℤ_[ℓ]) ^ v by ring, Units.mul_inv, one_mul]
  have h3 : w - y ∈ H := h2 ▸ mul_mem_of_isClosed H hH hx _
  have := H.add_mem h3 hy
  rwa [sub_add_cancel] at this

theorem infinite_of_ne_zero (H : AddSubgroup ℤ_[ℓ]) {x : ℤ_[ℓ]} (hx : x ∈ H) (hx0 : x ≠ 0) :
    (H : Set ℤ_[ℓ]).Infinite :=
  Set.infinite_of_injective_forall_mem (f := fun k : ℕ => k • x)
    (fun a b hab => by
      simp only [nsmul_eq_mul] at hab
      exact Nat.cast_injective (mul_right_cancel₀ hx0 hab))
    fun k => H.nsmul_mem hx k

end Padic

section ProfiniteInteger

def factorialPNat (n : ℕ) : ℕ+ := ⟨(n + 1).factorial, Nat.factorial_pos _⟩

theorem tendsto_natCast (a : ℤ̂) :
    Tendsto (fun n : ℕ => (((ProfiniteInteger.proj (factorialPNat n) a).val : ℕ) : ℤ̂)) atTop
      (𝓝 a) := by
  rw [tendsto_subtype_rng, tendsto_pi_nhds]
  intro m
  refine tendsto_nhds_of_eventually_eq ?_
  filter_upwards [eventually_ge_atTop (m : ℕ)] with n hn
  have hdvd : (m : ℕ) ∣ (factorialPNat n : ℕ) := Nat.dvd_factorial m.pos (by omega)
  have h := ProfiniteInteger.castHom_proj hdvd a
  rw [ZMod.castHom_apply, ZMod.cast_eq_val] at h
  simp only [ProfiniteInteger.proj_apply] at h
  rw [← h]
  rfl

theorem denseRange_natCast : DenseRange (Nat.cast : ℕ → ℤ̂) := fun a =>
  mem_closure_of_tendsto (tendsto_natCast a) (Eventually.of_forall fun _ => Set.mem_range_self _)

theorem mul_mem_of_isClosed' (H : AddSubgroup ℤ̂) (hH : IsClosed (H : Set ℤ̂)) {x : ℤ̂}
    (hx : x ∈ H) (a : ℤ̂) : a * x ∈ H :=
  denseRange_natCast.induction_on a (hH.preimage (continuous_id.mul continuous_const))
    fun k => by
      show (k : ℤ̂) * x ∈ H
      rw [← nsmul_eq_mul]
      exact H.nsmul_mem hx k

def idealOfIsClosed (H : AddSubgroup ℤ̂) (hH : IsClosed (H : Set ℤ̂)) : Ideal ℤ̂ where
  carrier := H
  add_mem' := H.add_mem
  zero_mem' := H.zero_mem
  smul_mem' a _ hx := mul_mem_of_isClosed' H hH hx a

noncomputable def primeIdempotent (q : Nat.Primes) : ℤ̂ :=
  ofPadics (Pi.single q 1)

theorem toPadicInt_primeIdempotent (q q' : Nat.Primes) :
    toPadicInt q' (primeIdempotent q) = Pi.single (M := fun q : Nat.Primes => ℤ_[q]) q 1 q' :=
  congrFun (toPadics_ofPadics _) q'

theorem toPadicInt_surjective (q : Nat.Primes) : Function.Surjective (toPadicInt q) := fun z =>
  ⟨ofPadics (Pi.single q z), by
    rw [← toPadics_apply, toPadics_ofPadics, Pi.single_eq_same]⟩

theorem mem_of_forall_toPadicInt (H : AddSubgroup ℤ̂) (hH : IsClosed (H : Set ℤ̂)) {y : ℤ̂}
    (hy : ∀ q : Nat.Primes, ∃ h ∈ H, toPadicInt q h = toPadicInt q y) : y ∈ H := by
  choose h hh hhy using hy
  let s : Finset Nat.Primes → ℤ̂ := fun F => ∑ q ∈ F, primeIdempotent q * h q
  have hs : ∀ F, s F ∈ H := fun F =>
    H.sum_mem fun q _ => mul_mem_of_isClosed' H hH (hh q) _
  have hcomp : ∀ (F : Finset Nat.Primes) (q' : Nat.Primes), toPadicInt q' (s F) = if q' ∈ F then toPadicInt q' y else 0 := by
    intro F q'
    simp only [s, map_sum, map_mul, toPadicInt_primeIdempotent]
    split_ifs with hq'
    · rw [Finset.sum_eq_single q', Pi.single_eq_same, one_mul, hhy]
      · intro b _ hb
        rw [Pi.single_eq_of_ne hb.symm, zero_mul]
      · intro h'; exact absurd hq' h'
    · refine Finset.sum_eq_zero fun b hb => ?_
      rw [Pi.single_eq_of_ne (by rintro rfl; exact hq' hb), zero_mul]
  have ht : Tendsto (fun F => toPadics (s F)) atTop (𝓝 (toPadics y)) := by
    rw [tendsto_pi_nhds]
    intro q'
    refine tendsto_nhds_of_eventually_eq ?_
    filter_upwards [eventually_ge_atTop {q'}] with F hF
    rw [toPadics_apply, hcomp, if_pos (Finset.singleton_subset_iff.1 hF), toPadics_apply]
  have ht' := (continuous_ofPadics.tendsto _).comp ht
  simp only [Function.comp_def, ofPadics_toPadics] at ht'
  exact hH.mem_of_tendsto ht' (Eventually.of_forall hs)

theorem exists_eq_mul_of_isClosed (H : AddSubgroup ℤ̂) (hH : IsClosed (H : Set ℤ̂))
    (hne : ∀ q : Nat.Primes, ∃ h ∈ H, toPadicInt q h ≠ 0) :
    ∃ g : ℤ̂, (∀ q : Nat.Primes, toPadicInt q g ≠ 0) ∧ ∀ y, y ∈ H ↔ ∃ a, y = g * a := by
  let I : Ideal ℤ̂ := idealOfIsClosed H hH
  have hI : ∀ q : Nat.Primes, I.map (toPadicInt q) ≠ ⊥ := by
    intro q hbot
    obtain ⟨h, hh, hh0⟩ := hne q
    apply hh0
    have : toPadicInt q h ∈ I.map (toPadicInt q) := Ideal.mem_map_of_mem _ hh
    rwa [hbot, Ideal.mem_bot] at this
  choose v hv using fun q => PadicInt.ideal_eq_span_pow_p (hI q)
  have hmem : ∀ (q : Nat.Primes) (z : ℤ_[q]), (∃ h ∈ H, toPadicInt q h = z) ↔ (q : ℤ_[q]) ^ v q ∣ z := by
    intro q z
    rw [← Ideal.mem_span_singleton, ← hv q, Ideal.mem_map_iff_of_surjective _
      (toPadicInt_surjective q)]
    rfl
  let g : ℤ̂ := ofPadics fun q => (q : ℤ_[q]) ^ v q
  have hg : ∀ q : Nat.Primes, toPadicInt q g = (q : ℤ_[q]) ^ v q := fun q =>
    congrFun (toPadics_ofPadics _) q
  refine ⟨g, fun q => by rw [hg]; exact pow_ne_zero _ (Nat.cast_ne_zero.2 q.2.ne_zero), ?_⟩
  intro y
  constructor
  · intro hy
    choose t ht using fun q => (hmem q (toPadicInt q y)).1 ⟨y, hy, rfl⟩
    refine ⟨ofPadics t, ext_toPadicInt fun q => ?_⟩
    rw [map_mul, hg, ht q]
    congr 1
    exact (congrFun (toPadics_ofPadics t) q).symm
  · rintro ⟨a, rfl⟩
    have hgH : g ∈ H := mem_of_forall_toPadicInt H hH fun q =>
      (hmem q _).2 (by rw [hg])
    rw [mul_comm]
    exact mul_mem_of_isClosed' H hH hgH a

theorem nonempty_addEquiv_of_isClosed (H : AddSubgroup ℤ̂) (hH : IsClosed (H : Set ℤ̂))
    (hne : ∀ q : Nat.Primes, ∃ h ∈ H, toPadicInt q h ≠ 0) : Nonempty (H ≃+ ℤ̂) := by
  obtain ⟨g, hg0, hgH⟩ := exists_eq_mul_of_isClosed H hH hne
  let f : ℤ̂ →+ H :=
    { toFun := fun a => ⟨g * a, (hgH _).2 ⟨a, rfl⟩⟩
      map_zero' := by ext; simp
      map_add' := fun a b => by ext; simp [mul_add] }
  have hf : Function.Bijective f := by
    refine ⟨fun a b hab => ext_toPadicInt fun q => ?_, fun y => ?_⟩
    · have := congrArg (fun z : H => toPadicInt q (z : ℤ̂)) hab
      simp only [f, AddMonoidHom.coe_mk, ZeroHom.coe_mk, map_mul] at this
      exact mul_left_cancel₀ (hg0 q) this
    · obtain ⟨a, ha⟩ := (hgH y).1 y.2
      exact ⟨a, Subtype.ext ha.symm⟩
  exact ⟨(AddEquiv.ofBijective f hf).symm⟩

end ProfiniteInteger

end Sec_CC_ClosedSubgroups

section Sec_CC_PadicUnitsLog

section Discrete

variable (ℓ : ℕ) [hℓ : Fact ℓ.Prime]

def unitsLevel : ℕ := if ℓ = 2 then 3 else 1

def torsionExponent : ℕ := if ℓ = 2 then 2 else ℓ - 1

omit hℓ in
theorem unitsLevel_ne_zero : unitsLevel ℓ ≠ 0 := by
  unfold unitsLevel; split_ifs <;> norm_num

theorem unitsLevel_add_two_le : unitsLevel ℓ + 2 ≤ ℓ * unitsLevel ℓ := by
  unfold unitsLevel
  split_ifs with h
  · subst h; norm_num
  · have := hℓ.out.two_le
    omega

theorem torsionExponent_pos : 0 < torsionExponent ℓ := by
  unfold torsionExponent
  split_ifs
  · norm_num
  · have := hℓ.out.two_le
    omega

theorem pow_torsionExponent (x : (ZMod (ℓ ^ unitsLevel ℓ))ˣ) : x ^ torsionExponent ℓ = 1 := by
  by_cases h : ℓ = 2
  · subst h
    have key : ∀ y : ZMod 8, (∃ z : ZMod 8, y * z = 1) → y ^ 2 = 1 := by decide
    have h8 : (2 : ℕ) ^ unitsLevel 2 = 8 := by simp [unitsLevel]
    rw [torsionExponent, if_pos rfl]
    refine Units.ext ?_
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    revert x
    rw [h8]
    intro x
    exact key _ ⟨_, x.mul_inv⟩
  · have : NeZero ℓ := ⟨hℓ.out.ne_zero⟩
    have hc : Fintype.card (ZMod (ℓ ^ unitsLevel ℓ))ˣ = ℓ - 1 := by
      rw [ZMod.card_units_eq_totient, unitsLevel, if_neg h, pow_one, Nat.totient_prime hℓ.out]
    rw [torsionExponent, if_neg h, ← hc, pow_card_eq_one]

def unitsKer (n : ℕ) : Subgroup (ZMod (ℓ ^ (n + unitsLevel ℓ)))ˣ :=
  (ZMod.unitsMap (pow_dvd_pow ℓ (Nat.le_add_left (unitsLevel ℓ) n))).ker

theorem card_unitsKer (n : ℕ) : Nat.card (unitsKer ℓ n) = ℓ ^ n := by
  have : NeZero ℓ := ⟨hℓ.out.ne_zero⟩
  have h1 := Subgroup.card_mul_index (unitsKer ℓ n)
  rw [unitsKer, Subgroup.index_ker, MonoidHom.range_eq_top.2 (ZMod.unitsMap_surjective _),
    Subgroup.card_top, Nat.card_eq_fintype_card (α := (ZMod (ℓ ^ unitsLevel ℓ))ˣ),
    Nat.card_eq_fintype_card (α := (ZMod (ℓ ^ (n + unitsLevel ℓ)))ˣ), ZMod.card_units_eq_totient,
    ZMod.card_units_eq_totient, Nat.totient_prime_pow hℓ.out (Nat.pos_of_ne_zero
      (unitsLevel_ne_zero ℓ)), Nat.totient_prime_pow hℓ.out (by
        have := unitsLevel_ne_zero ℓ; omega)] at h1
  have hr : n + unitsLevel ℓ - 1 = n + (unitsLevel ℓ - 1) := by
    have := unitsLevel_ne_zero ℓ; omega
  have hpos : 0 < ℓ ^ (unitsLevel ℓ - 1) * (ℓ - 1) :=
    Nat.mul_pos (pow_pos hℓ.out.pos _) (by have := hℓ.out.two_le; omega)
  have h2 : Nat.card (unitsKer ℓ n) * (ℓ ^ (unitsLevel ℓ - 1) * (ℓ - 1)) =
      ℓ ^ n * (ℓ ^ (unitsLevel ℓ - 1) * (ℓ - 1)) := by
    rw [← mul_assoc (ℓ ^ n), ← pow_add, ← hr]
    exact h1
  exact Nat.eq_of_mul_eq_mul_right hpos h2

theorem coprime_one_add_pow (k : ℕ) : Nat.Coprime (1 + ℓ ^ unitsLevel ℓ) (ℓ ^ k) := by
  refine Nat.Coprime.pow_right _ ?_
  rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hℓ.out]
  intro h
  rw [add_comm] at h
  exact hℓ.out.not_dvd_one
    ((Nat.dvd_add_right (dvd_pow_self ℓ (unitsLevel_ne_zero ℓ))).1 h)

def genUnit (n : ℕ) : (ZMod (ℓ ^ (n + unitsLevel ℓ)))ˣ :=
  ZMod.unitOfCoprime (1 + ℓ ^ unitsLevel ℓ) (coprime_one_add_pow ℓ _)

@[simp] theorem coe_genUnit (n : ℕ) :
    (genUnit ℓ n : ZMod (ℓ ^ (n + unitsLevel ℓ))) = 1 + (ℓ : ZMod _) ^ unitsLevel ℓ := by
  simp [genUnit]

theorem orderOf_genUnit (n : ℕ) : orderOf (genUnit ℓ n) = ℓ ^ n := by
  rw [← orderOf_units, coe_genUnit]
  have := ZMod.orderOf_one_add_mul_prime_pow hℓ.out (unitsLevel ℓ) (unitsLevel_ne_zero ℓ)
    (unitsLevel_add_two_le ℓ) 1 (by norm_cast; exact hℓ.out.not_dvd_one) n
  simpa using this

theorem genUnit_pow_eq_one (n : ℕ) : genUnit ℓ n ^ (ℓ ^ n) = 1 := by
  have := pow_orderOf_eq_one (genUnit ℓ n)
  rwa [orderOf_genUnit] at this

theorem genUnit_mem_unitsKer (n : ℕ) : genUnit ℓ n ∈ unitsKer ℓ n := by
  rw [unitsKer, MonoidHom.mem_ker]
  refine Units.ext ?_
  simp only [ZMod.unitsMap_def, Units.coe_map, MonoidHom.coe_coe, coe_genUnit, map_add, map_one,
    map_pow, map_natCast, Units.val_one]
  rw [← Nat.cast_pow, ZMod.natCast_self, add_zero]

theorem zpowers_genUnit (n : ℕ) : Subgroup.zpowers (genUnit ℓ n) = unitsKer ℓ n :=
  Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 (genUnit_mem_unitsKer ℓ n))
    (by rw [card_unitsKer, Nat.card_zpowers, orderOf_genUnit])

theorem genUnit_pow_val_eq (n : ℕ) {a b : ℕ} (h : a ≡ b [MOD ℓ ^ n]) :
    genUnit ℓ n ^ a = genUnit ℓ n ^ b := by
  rw [pow_eq_pow_iff_modEq, orderOf_genUnit]
  exact h

def expHom (n : ℕ) : Multiplicative (ZMod (ℓ ^ n)) →* (ZMod (ℓ ^ (n + unitsLevel ℓ)))ˣ where
  toFun a := genUnit ℓ n ^ (Multiplicative.toAdd a).val
  map_one' := by simp
  map_mul' a b := by
    have : NeZero ℓ := ⟨hℓ.out.ne_zero⟩
    rw [← pow_add, toAdd_mul]
    exact genUnit_pow_val_eq ℓ n (by rw [ZMod.val_add]; exact Nat.mod_modEq _ _)

theorem expHom_apply (n : ℕ) (a : Multiplicative (ZMod (ℓ ^ n))) :
    expHom ℓ n a = genUnit ℓ n ^ (Multiplicative.toAdd a).val :=
  rfl

theorem expHom_injective (n : ℕ) : Function.Injective (expHom ℓ n) := by
  have : NeZero ℓ := ⟨hℓ.out.ne_zero⟩
  refine (injective_iff_map_eq_one _).2 fun a ha => ?_
  rw [expHom_apply] at ha
  have h1 : ℓ ^ n ∣ (Multiplicative.toAdd a).val := by
    have := orderOf_dvd_of_pow_eq_one ha
    rwa [orderOf_genUnit] at this
  have h2 := Nat.eq_zero_of_dvd_of_lt h1 (ZMod.val_lt _)
  rw [ZMod.val_eq_zero] at h2
  exact h2

theorem range_expHom (n : ℕ) : (expHom ℓ n).range = unitsKer ℓ n := by
  apply Subgroup.eq_of_le_of_card_ge
  · rintro _ ⟨a, rfl⟩
    rw [← zpowers_genUnit]
    exact Subgroup.npow_mem_zpowers _ _
  · rw [card_unitsKer, ← Nat.card_congr (MonoidHom.ofInjective (expHom_injective ℓ n)).toEquiv]
    exact (Nat.card_zmod _).ge

noncomputable def expEquiv (n : ℕ) : Multiplicative (ZMod (ℓ ^ n)) ≃* unitsKer ℓ n :=
  (MonoidHom.ofInjective (expHom_injective ℓ n)).trans (MulEquiv.subgroupCongr (range_expHom ℓ n))

theorem coe_expEquiv (n : ℕ) (a : Multiplicative (ZMod (ℓ ^ n))) :
    (expEquiv ℓ n a : (ZMod (ℓ ^ (n + unitsLevel ℓ)))ˣ) = expHom ℓ n a :=
  rfl

def powKer (n : ℕ) : (ZMod (ℓ ^ (n + unitsLevel ℓ)))ˣ →* unitsKer ℓ n :=
  (powMonoidHom (torsionExponent ℓ)).codRestrict (unitsKer ℓ n) fun x => by
    rw [unitsKer, MonoidHom.mem_ker, powMonoidHom_apply, map_pow, pow_torsionExponent]

noncomputable def logMod (n : ℕ) : (ZMod (ℓ ^ (n + unitsLevel ℓ)))ˣ →* Multiplicative (ZMod (ℓ ^ n)) :=
  (expEquiv ℓ n).symm.toMonoidHom.comp (powKer ℓ n)

theorem expHom_logMod (n : ℕ) (x : (ZMod (ℓ ^ (n + unitsLevel ℓ)))ˣ) :
    expHom ℓ n (logMod ℓ n x) = x ^ torsionExponent ℓ := by
  have := congrArg Subtype.val ((expEquiv ℓ n).apply_symm_apply (powKer ℓ n x))
  rw [coe_expEquiv] at this
  exact this

theorem logMod_eq_iff (n : ℕ) (x : (ZMod (ℓ ^ (n + unitsLevel ℓ)))ˣ)
    (a : Multiplicative (ZMod (ℓ ^ n))) :
    logMod ℓ n x = a ↔ expHom ℓ n a = x ^ torsionExponent ℓ :=
  ⟨fun h => h ▸ expHom_logMod ℓ n x,
    fun h => expHom_injective ℓ n (by rw [expHom_logMod, h])⟩

theorem unitsMap_genUnit {m n : ℕ} (h : m ≤ n) :
    ZMod.unitsMap (pow_dvd_pow ℓ (by omega : m + unitsLevel ℓ ≤ n + unitsLevel ℓ)) (genUnit ℓ n) =
      genUnit ℓ m := by
  refine Units.ext ?_
  simp only [ZMod.unitsMap_def, Units.coe_map, MonoidHom.coe_coe, coe_genUnit, map_add, map_one,
    map_pow, map_natCast]

theorem castHom_logMod {m n : ℕ} (h : m ≤ n) (x : (ZMod (ℓ ^ (n + unitsLevel ℓ)))ˣ) :
    ZMod.castHom (pow_dvd_pow ℓ h) (ZMod (ℓ ^ m)) (Multiplicative.toAdd (logMod ℓ n x)) =
      Multiplicative.toAdd (logMod ℓ m
        (ZMod.unitsMap (pow_dvd_pow ℓ (by omega : m + unitsLevel ℓ ≤ n + unitsLevel ℓ)) x)) := by
  have : NeZero ℓ := ⟨hℓ.out.ne_zero⟩
  set a := Multiplicative.toAdd (logMod ℓ n x) with ha
  have key : logMod ℓ m
      (ZMod.unitsMap (pow_dvd_pow ℓ (by omega : m + unitsLevel ℓ ≤ n + unitsLevel ℓ)) x) =
        Multiplicative.ofAdd (ZMod.castHom (pow_dvd_pow ℓ h) (ZMod (ℓ ^ m)) a) := by
    rw [logMod_eq_iff, expHom_apply, toAdd_ofAdd, ← map_pow, ← expHom_logMod ℓ n x, expHom_apply,
      map_pow, unitsMap_genUnit ℓ h, ← ha]
    refine genUnit_pow_val_eq ℓ m ?_
    rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.val_natCast]
    exact Nat.mod_modEq _ _
  rw [key, toAdd_ofAdd]

end Discrete

section Limit

variable (ℓ : ℕ) [hℓ : Fact ℓ.Prime]

def compatibleFamilies : Subring (∀ n : ℕ, ZMod (ℓ ^ n)) :=
  ⨅ (m : ℕ) (n : ℕ) (h : m ≤ n), RingHom.eqLocus
    ((ZMod.castHom (pow_dvd_pow ℓ h) (ZMod (ℓ ^ m))).comp
      (Pi.evalRingHom (fun k => ZMod (ℓ ^ k)) n)) (Pi.evalRingHom (fun k => ZMod (ℓ ^ k)) m)

omit hℓ in
theorem mem_compatibleFamilies {x : ∀ n : ℕ, ZMod (ℓ ^ n)} :
    x ∈ compatibleFamilies ℓ ↔
      ∀ (m n : ℕ) (h : m ≤ n), ZMod.castHom (pow_dvd_pow ℓ h) (ZMod (ℓ ^ m)) (x n) = x m := by
  simp [compatibleFamilies, Subring.mem_iInf, RingHom.mem_eqLocus]

noncomputable def limFamilies : compatibleFamilies ℓ →+* ℤ_[ℓ] :=
  PadicInt.lift (f := fun n => (Pi.evalRingHom (fun k => ZMod (ℓ ^ k)) n).comp
    (compatibleFamilies ℓ).subtype) fun m n h => by
      ext x
      exact (mem_compatibleFamilies ℓ).1 x.2 m n h

theorem toZModPow_limFamilies (x : compatibleFamilies ℓ) (n : ℕ) :
    PadicInt.toZModPow n (limFamilies ℓ x) = (x : ∀ n : ℕ, ZMod (ℓ ^ n)) n :=
  RingHom.congr_fun (PadicInt.lift_spec _ n) x

noncomputable def redUnits (k : ℕ) : ℤ_[ℓ]ˣ →* (ZMod (ℓ ^ k))ˣ :=
  Units.map (PadicInt.toZModPow k).toMonoidHom

@[simp] theorem coe_redUnits (k : ℕ) (u : ℤ_[ℓ]ˣ) :
    (redUnits ℓ k u : ZMod (ℓ ^ k)) = PadicInt.toZModPow k (u : ℤ_[ℓ]) :=
  rfl

theorem unitsMap_redUnits {k k' : ℕ} (h : k ≤ k') (u : ℤ_[ℓ]ˣ) :
    ZMod.unitsMap (pow_dvd_pow ℓ h) (redUnits ℓ k' u) = redUnits ℓ k u := by
  refine Units.ext ?_
  simp only [ZMod.unitsMap_def, Units.coe_map, MonoidHom.coe_coe, coe_redUnits,
    ZMod.castHom_apply]
  exact PadicInt.cast_toZModPow _ _ h _

theorem logFamily_mem (u : ℤ_[ℓ]ˣ) :
    (fun n => Multiplicative.toAdd (logMod ℓ n (redUnits ℓ (n + unitsLevel ℓ) u))) ∈
      compatibleFamilies ℓ := by
  rw [mem_compatibleFamilies]
  intro m n h
  rw [castHom_logMod ℓ h,
    unitsMap_redUnits ℓ (k := m + unitsLevel ℓ) (k' := n + unitsLevel ℓ) (by omega)]

noncomputable def padicUnitsLog : ℤ_[ℓ]ˣ →* Multiplicative ℤ_[ℓ] where
  toFun u := Multiplicative.ofAdd (limFamilies ℓ ⟨_, logFamily_mem ℓ u⟩)
  map_one' := by
    refine congrArg Multiplicative.ofAdd (PadicInt.ext_of_toZModPow.mp fun n => ?_)
    rw [toZModPow_limFamilies, map_zero]
    simp
  map_mul' u v := by
    rw [← ofAdd_add]
    refine congrArg Multiplicative.ofAdd (PadicInt.ext_of_toZModPow.mp fun n => ?_)
    rw [map_add, toZModPow_limFamilies, toZModPow_limFamilies, toZModPow_limFamilies]
    simp

theorem toZModPow_padicUnitsLog (u : ℤ_[ℓ]ˣ) (n : ℕ) :
    PadicInt.toZModPow n (Multiplicative.toAdd (padicUnitsLog ℓ u)) =
      Multiplicative.toAdd (logMod ℓ n (redUnits ℓ (n + unitsLevel ℓ) u)) :=
  toZModPow_limFamilies ℓ _ n

theorem continuous_redUnits (k : ℕ) : Continuous (redUnits ℓ k) := by
  rw [Units.continuous_iff]
  refine ⟨(continuous_toZModPow k).comp Units.continuous_val, ?_⟩
  have : (fun u : ℤ_[ℓ]ˣ => ((redUnits ℓ k u)⁻¹ : (ZMod (ℓ ^ k))ˣ).val) =
      fun u => PadicInt.toZModPow k ((u⁻¹ : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) := by
    funext u; rw [← map_inv]; rfl
  rw [this]
  exact (continuous_toZModPow k).comp (Units.continuous_val.comp continuous_inv)

theorem continuous_padicUnitsLog : Continuous (padicUnitsLog ℓ) := by
  have hc : Continuous fun u : ℤ_[ℓ]ˣ => Multiplicative.toAdd (padicUnitsLog ℓ u) :=
    continuous_of_continuous_toZModPow fun n =>
      ((continuous_of_discreteTopology (f := fun v : (ZMod (ℓ ^ (n + unitsLevel ℓ)))ˣ =>
        Multiplicative.toAdd (logMod ℓ n v))).comp (continuous_redUnits ℓ _)).congr fun u =>
          (toZModPow_padicUnitsLog ℓ u n).symm
  exact continuous_ofAdd.comp hc

def genNat : ℕ := if ℓ = 2 then 3 else ℓ + 1

def genLog : ℕ := if ℓ = 2 then 1 else ℓ - 1

theorem genNat_pow : genNat ℓ ^ torsionExponent ℓ = (1 + ℓ ^ unitsLevel ℓ) ^ genLog ℓ := by
  unfold genNat torsionExponent unitsLevel genLog
  split_ifs with h
  · subst h; norm_num
  · rw [pow_one, add_comm]

theorem coprime_genNat : Nat.Coprime ℓ (genNat ℓ) := by
  rw [Nat.Prime.coprime_iff_not_dvd hℓ.out]
  unfold genNat
  split_ifs with h
  · subst h; norm_num
  · intro hd
    exact hℓ.out.not_dvd_one ((Nat.dvd_add_right (dvd_refl ℓ)).1 hd)

theorem coprime_genLog : Nat.Coprime ℓ (genLog ℓ) := by
  rw [Nat.Prime.coprime_iff_not_dvd hℓ.out]
  unfold genLog
  split_ifs with h
  · subst h; norm_num
  · have := hℓ.out.two_le
    exact Nat.not_dvd_of_pos_of_lt (by omega) (by omega)

theorem isUnit_natCast_of_coprime {k : ℕ} (hk : Nat.Coprime ℓ k) : IsUnit (k : ℤ_[ℓ]) :=
  PadicInt.isUnit_iff.2 (PadicInt.norm_natCast_eq_one_iff.2 hk)

noncomputable def genPadicUnit : ℤ_[ℓ]ˣ := (isUnit_natCast_of_coprime ℓ (coprime_genNat ℓ)).unit

theorem padicUnitsLog_genPadicUnit :
    Multiplicative.toAdd (padicUnitsLog ℓ (genPadicUnit ℓ)) = (genLog ℓ : ℤ_[ℓ]) := by
  refine PadicInt.ext_of_toZModPow.mp fun n => ?_
  rw [toZModPow_padicUnitsLog, map_natCast]
  have : logMod ℓ n (redUnits ℓ (n + unitsLevel ℓ) (genPadicUnit ℓ)) =
      Multiplicative.ofAdd ((genLog ℓ : ℕ) : ZMod (ℓ ^ n)) := by
    rw [logMod_eq_iff, expHom_apply, toAdd_ofAdd, pow_val_natCast (genUnit_pow_eq_one ℓ n)]
    refine Units.ext ?_
    simp only [Units.val_pow_eq_pow_val, coe_genUnit, coe_redUnits, genPadicUnit,
      IsUnit.unit_spec, map_natCast]
    rw [← Nat.cast_pow (genNat ℓ), genNat_pow]
    push_cast
    ring
  rw [this, toAdd_ofAdd]

theorem padicUnitsLog_surjective : Function.Surjective (padicUnitsLog ℓ) := by
  have hc : Continuous fun u : ℤ_[ℓ]ˣ => Multiplicative.toAdd (padicUnitsLog ℓ u) :=
    continuous_toAdd.comp (continuous_padicUnitsLog ℓ)
  set s : ℤ_[ℓ] := (genLog ℓ : ℤ_[ℓ])
  have hs : IsUnit s := isUnit_natCast_of_coprime ℓ (coprime_genLog ℓ)
  set R : Set ℤ_[ℓ] := Set.range fun u : ℤ_[ℓ]ˣ => Multiplicative.toAdd (padicUnitsLog ℓ u)
  have hR : IsClosed R := (isCompact_range hc).isClosed
  have hmem : ∀ t : ℤ_[ℓ], s * t ∈ R := fun t =>
    PadicInt.denseRange_natCast.induction_on t
      (hR.preimage (continuous_const.mul continuous_id)) fun k =>
        ⟨genPadicUnit ℓ ^ k, by
          show Multiplicative.toAdd (padicUnitsLog ℓ (genPadicUnit ℓ ^ k)) = s * k
          rw [map_pow, toAdd_pow, padicUnitsLog_genPadicUnit, nsmul_eq_mul, mul_comm]⟩
  intro y
  obtain ⟨u, hu⟩ := hmem (↑hs.unit⁻¹ * Multiplicative.toAdd y)
  have hu : Multiplicative.toAdd (padicUnitsLog ℓ u) = s * (↑hs.unit⁻¹ * Multiplicative.toAdd y) :=
    hu
  refine ⟨u, ?_⟩
  apply Multiplicative.toAdd.injective
  rw [hu, ← mul_assoc, IsUnit.mul_val_inv, one_mul]

theorem padicUnitsLog_eq_one_of_pow_eq_one {u : ℤ_[ℓ]ˣ} {k : ℕ} (hk : 0 < k) (h : u ^ k = 1) :
    padicUnitsLog ℓ u = 1 := by
  have h1 := congrArg (fun v => Multiplicative.toAdd (padicUnitsLog ℓ v)) h
  simp only [map_pow, toAdd_pow, map_one, toAdd_one, nsmul_eq_mul] at h1
  rcases mul_eq_zero.1 h1 with h2 | h2
  · exact absurd h2 (Nat.cast_ne_zero.2 hk.ne')
  · exact congrArg Multiplicative.ofAdd h2

theorem padicUnitsLog_eq_one_iff (u : ℤ_[ℓ]ˣ) :
    padicUnitsLog ℓ u = 1 ↔ u ^ torsionExponent ℓ = 1 := by
  refine ⟨fun h => ?_, padicUnitsLog_eq_one_of_pow_eq_one ℓ (torsionExponent_pos ℓ)⟩
  have hk : ∀ k, PadicInt.toZModPow (k + unitsLevel ℓ) ((u ^ torsionExponent ℓ : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) =
      1 := fun k => by
    have h1 := toZModPow_padicUnitsLog ℓ u k
    rw [h, toAdd_one, map_zero] at h1
    have h2 : logMod ℓ k (redUnits ℓ (k + unitsLevel ℓ) u) = 1 :=
      congrArg Multiplicative.ofAdd h1.symm
    rw [logMod_eq_iff, map_one] at h2
    have h3 := congrArg Units.val h2
    rw [Units.val_one, Units.val_pow_eq_pow_val, coe_redUnits, ← map_pow] at h3
    rw [Units.val_pow_eq_pow_val]
    exact h3.symm
  refine Units.ext (PadicInt.ext_of_toZModPow.mp fun k => ?_)
  rw [← PadicInt.zmod_cast_comp_toZModPow k (k + unitsLevel ℓ) (Nat.le_add_right _ _),
    RingHom.comp_apply, RingHom.comp_apply, hk]
  simp

theorem ker_padicUnitsLog : (padicUnitsLog ℓ).ker = CommGroup.torsion ℤ_[ℓ]ˣ := by
  ext u
  rw [MonoidHom.mem_ker, CommGroup.mem_torsion, isOfFinOrder_iff_pow_eq_one]
  constructor
  · intro h
    exact ⟨_, torsionExponent_pos ℓ, (padicUnitsLog_eq_one_iff ℓ u).1 h⟩
  · rintro ⟨k, hk, h⟩
    exact padicUnitsLog_eq_one_of_pow_eq_one ℓ hk h

theorem mem_torsion_iff (u : ℤ_[ℓ]ˣ) :
    u ∈ CommGroup.torsion ℤ_[ℓ]ˣ ↔ u ^ torsionExponent ℓ = 1 := by
  rw [← ker_padicUnitsLog, MonoidHom.mem_ker, padicUnitsLog_eq_one_iff]

theorem mem_torsion_two_iff (u : ℤ_[2]ˣ) :
    u ∈ CommGroup.torsion ℤ_[2]ˣ ↔ u = 1 ∨ u = -1 := by
  rw [mem_torsion_iff, torsionExponent, if_pos rfl]
  constructor
  · intro h
    have h1 := congrArg Units.val h
    rw [Units.val_pow_eq_pow_val, Units.val_one, sq, mul_self_eq_one_iff] at h1
    rcases h1 with h1 | h1
    · exact Or.inl (Units.ext h1)
    · exact Or.inr (Units.ext (by rw [h1, Units.val_neg, Units.val_one]))
  · rintro (rfl | rfl) <;> simp

noncomputable def unitsModTorsionEquiv :
    ℤ_[ℓ]ˣ ⧸ CommGroup.torsion ℤ_[ℓ]ˣ ≃* Multiplicative ℤ_[ℓ] :=
  (QuotientGroup.quotientMulEquivOfEq (ker_padicUnitsLog ℓ).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (padicUnitsLog_surjective ℓ))

end Limit

end Sec_CC_PadicUnitsLog

section Sec_CC_Degree

open NumberField IntermediateField
open scoped ComplexConjugate




local notation "ℚ̄" => AlgebraicClosure ℚ

section UnitsDegree

theorem continuous_unitsPadicEquiv_apply (q : Nat.Primes) :
    Continuous fun u : ℤ̂ˣ => unitsPadicEquiv u q := by
  simp_rw [unitsPadicEquiv_apply]
  rw [Units.continuous_iff]
  exact ⟨(continuous_toPadicInt q).comp Units.continuous_val,
    (continuous_toPadicInt q).comp Units.continuous_coe_inv⟩

noncomputable def unitsDegree : ℤ̂ˣ →* Multiplicative ℤ̂ where
  toFun u := Multiplicative.ofAdd
    (ofPadics fun q => Multiplicative.toAdd (padicUnitsLog q (unitsPadicEquiv u q)))
  map_one' := by
    rw [show (fun q : Nat.Primes => Multiplicative.toAdd (padicUnitsLog q (unitsPadicEquiv 1 q))) =
      0 from funext fun q => by simp, map_zero, ofAdd_zero]
  map_mul' u v := by
    rw [← ofAdd_add, ← map_add]
    congr 2
    funext q
    simp

theorem toPadicInt_unitsDegree (u : ℤ̂ˣ) (q : Nat.Primes) :
    toPadicInt q (Multiplicative.toAdd (unitsDegree u)) =
      Multiplicative.toAdd (padicUnitsLog q (unitsPadicEquiv u q)) :=
  congrFun (toPadics_ofPadics _) q

theorem continuous_unitsDegree : Continuous unitsDegree :=
  continuous_ofAdd.comp (continuous_ofPadics.comp (continuous_pi fun q =>
    continuous_toAdd.comp ((continuous_padicUnitsLog q).comp
      (continuous_unitsPadicEquiv_apply q))))

theorem unitsDegree_surjective : Function.Surjective unitsDegree := by
  intro y
  choose g hg using fun q : Nat.Primes =>
    padicUnitsLog_surjective q (Multiplicative.ofAdd (toPadicInt q (Multiplicative.toAdd y)))
  refine ⟨unitsPadicEquiv.symm g, Multiplicative.toAdd.injective (ext_toPadicInt fun q => ?_)⟩
  rw [toPadicInt_unitsDegree, MulEquiv.apply_symm_apply, hg, toAdd_ofAdd]

theorem unitsDegree_eq_one_iff (u : ℤ̂ˣ) :
    unitsDegree u = 1 ↔ ∀ q : Nat.Primes, unitsPadicEquiv u q ∈ CommGroup.torsion ℤ_[q]ˣ := by
  simp_rw [← ker_padicUnitsLog, MonoidHom.mem_ker]
  constructor
  · intro h q
    have := toPadicInt_unitsDegree u q
    rw [h, toAdd_one, map_zero] at this
    exact congrArg Multiplicative.ofAdd this.symm
  · intro h
    refine Multiplicative.toAdd.injective (ext_toPadicInt fun q => ?_)
    rw [toPadicInt_unitsDegree, h q, toAdd_one, toAdd_one, map_zero]

theorem unitsDegree_eq_one_of_pow_eq_one {u : ℤ̂ˣ} {k : ℕ} (hk : 0 < k) (h : u ^ k = 1) :
    unitsDegree u = 1 := by
  rw [unitsDegree_eq_one_iff]
  intro q
  rw [CommGroup.mem_torsion, isOfFinOrder_iff_pow_eq_one]
  refine ⟨k, hk, ?_⟩
  rw [← Pi.pow_apply, ← map_pow, h, map_one, Pi.one_apply]

theorem unitsDegree_neg_one : unitsDegree (-1) = 1 :=
  unitsDegree_eq_one_of_pow_eq_one two_pos (by rw [neg_one_sq])

end UnitsDegree

section Degree

noncomputable def degree : Gal(ℚ̄/ℚ) →* Multiplicative ℤ̂ :=
  unitsDegree.comp character

theorem degree_apply (σ : Gal(ℚ̄/ℚ)) : degree σ = unitsDegree (character σ) :=
  rfl

theorem continuous_degree : Continuous degree :=
  continuous_unitsDegree.comp continuous_character

theorem degree_surjective : Function.Surjective degree :=
  unitsDegree_surjective.comp character_surjective

theorem ker_character_le_ker_degree : character.ker ≤ degree.ker := fun σ h => by
  rw [MonoidHom.mem_ker, degree_apply, MonoidHom.mem_ker.1 h, map_one]

noncomputable def degreeComponent (q : Nat.Primes) : Gal(ℚ̄/ℚ) →* Multiplicative ℤ_[q] :=
  (padicUnitsLog q).comp ((Units.map (toPadicInt q).toMonoidHom).comp character)

theorem degreeComponent_apply (q : Nat.Primes) (σ : Gal(ℚ̄/ℚ)) :
    degreeComponent q σ = padicUnitsLog q (Units.map (toPadicInt q).toMonoidHom (character σ)) :=
  rfl

theorem toPadicInt_degree (q : Nat.Primes) (σ : Gal(ℚ̄/ℚ)) :
    toPadicInt q (Multiplicative.toAdd (degree σ)) = Multiplicative.toAdd (degreeComponent q σ) := by
  rw [degree_apply, toPadicInt_unitsDegree, unitsPadicEquiv_apply]
  rfl

theorem continuous_degreeComponent (q : Nat.Primes) : Continuous (degreeComponent q) := by
  have h : Continuous fun σ : Gal(ℚ̄/ℚ) => Multiplicative.toAdd (degreeComponent q σ) :=
    ((continuous_toPadicInt q).comp (continuous_toAdd.comp continuous_degree)).congr
      (toPadicInt_degree q)
  exact continuous_ofAdd.comp h

end Degree

section ComplexConjugation

def IsComplexConjugation (σ : Gal(ℚ̄/ℚ)) : Prop :=
  ∃ ι : ℚ̄ →+* ℂ, ∀ x, ι (σ x) = conj (ι x)

theorem exists_algEquiv_conj (ι : ℚ̄ →+* ℂ) :
    ∃ σ : Gal(ℚ̄/ℚ), ∀ x, ι (σ x) = conj (ι x) := by
  let _ : Algebra ℚ̄ ℂ := ι.toAlgebra
  have : IsScalarTower ℚ ℚ̄ ℂ := IsScalarTower.of_algebraMap_eq fun x =>
    (eq_ratCast _ x).trans (eq_ratCast (ι.comp (algebraMap ℚ ℚ̄)) x).symm
  let c : ℂ →ₐ[ℚ] ℂ := (starRingEnd ℂ).toRatAlgHom
  exact ⟨c.restrictNormal' ℚ̄, fun x => c.restrictNormal_commutes ℚ̄ x⟩

theorem exists_isComplexConjugation : ∃ σ : Gal(ℚ̄/ℚ), IsComplexConjugation σ := by
  let ι : ℚ̄ →ₐ[ℚ] ℂ := IsAlgClosed.lift
  obtain ⟨σ, hσ⟩ := exists_algEquiv_conj ι.toRingHom
  exact ⟨σ, ι.toRingHom, hσ⟩

theorem character_of_isComplexConjugation {σ : Gal(ℚ̄/ℚ)} (h : IsComplexConjugation σ) :
    character σ = -1 := by
  obtain ⟨ι, hι⟩ := h
  refine Units.ext ?_
  rw [Units.val_neg, Units.val_one]
  refine (eq_character σ (-1) fun n t ht => ?_).symm
  have ht0 : t ≠ 0 := by
    rintro rfl
    rw [zero_pow n.ne_zero] at ht
    exact zero_ne_one ht
  have hσ : σ t = t⁻¹ := by
    apply ι.injective
    rw [hι, map_inv₀]
    have hn : ‖ι t‖ = 1 :=
      Complex.norm_eq_one_of_pow_eq_one (by rw [← map_pow, ht, map_one]) n.ne_zero
    rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hn]
    simp
  have hcast : (-1 : ZMod n) = (((n : ℕ) - 1 : ℕ) : ZMod n) := by
    rw [Nat.cast_sub (n.pos : 1 ≤ (n : ℕ)), ZMod.natCast_self, Nat.cast_one, zero_sub]
  rw [hσ, map_neg, map_one, hcast, pow_val_natCast ht]
  refine (eq_inv_of_mul_eq_one_left ?_).symm
  rw [← pow_succ, Nat.sub_add_cancel (n.pos : 1 ≤ (n : ℕ)), ht]

theorem degree_of_isComplexConjugation {σ : Gal(ℚ̄/ℚ)} (h : IsComplexConjugation σ) :
    degree σ = 1 := by
  rw [degree_apply, character_of_isComplexConjugation h, unitsDegree_neg_one]

end ComplexConjugation

section FixedField

noncomputable def zhatField : IntermediateField ℚ ℚ̄ :=
  fixedField degree.ker

theorem isClosed_ker_degree : IsClosed (degree.ker : Set Gal(ℚ̄/ℚ)) :=
  isClosed_singleton.preimage continuous_degree

theorem fixingSubgroup_zhatField : zhatField.fixingSubgroup = degree.ker :=
  InfiniteGalois.fixingSubgroup_fixedField ⟨degree.ker, isClosed_ker_degree⟩

theorem zhatField_le_maxCyclotomic : zhatField ≤ maxCyclotomic := by
  rw [← fixedField_ker_character]
  intro x hx
  rw [zhatField, mem_fixedField_iff] at hx
  rw [mem_fixedField_iff]
  exact fun f hf => hx f (ker_character_le_ker_degree hf)

theorem isReal_zhatField (φ : zhatField →+* ℂ) : ComplexEmbedding.IsReal φ := by
  let _ : Algebra zhatField ℂ := φ.toAlgebra
  have : Algebra.IsAlgebraic zhatField ℚ̄ := Algebra.IsAlgebraic.tower_top (K := ℚ) zhatField
  let ι : ℚ̄ →ₐ[zhatField] ℂ := IsAlgClosed.lift
  obtain ⟨σ, hσ⟩ := exists_algEquiv_conj ι.toRingHom
  have hdeg : σ ∈ degree.ker := degree_of_isComplexConjugation ⟨_, hσ⟩
  rw [ComplexEmbedding.isReal_iff]
  ext x
  rw [ComplexEmbedding.conjugate_coe_eq]
  have hx : σ (x : ℚ̄) = x := (mem_fixedField_iff _ _).1 x.2 σ hdeg
  have h1 : ι (x : ℚ̄) = φ x := ι.commutes x
  have h2 := hσ (x : ℚ̄)
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hx, h1] at h2
  exact h2.symm

instance isTotallyReal_zhatField : IsTotallyReal zhatField :=
  ⟨fun _ => InfinitePlace.isReal_iff.2 (isReal_zhatField _)⟩

end FixedField

end Sec_CC_Degree

section Sec_CC_DegreeDecomposition

open NumberField IntermediateField Filter Topology
open scoped Pointwise




local notation "ℚ̄" => AlgebraicClosure ℚ

section Lift

theorem isOpen_stabilizer_ringOfIntegers (b : 𝓞 ℚ̄) :
    IsOpen (MulAction.stabilizer Gal(ℚ̄/ℚ) b : Set Gal(ℚ̄/ℚ)) := by
  have : FiniteDimensional ℚ ℚ⟮(b : ℚ̄)⟯ :=
    adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral _)
  refine Subgroup.isOpen_mono (H₁ := (ℚ⟮(b : ℚ̄)⟯).fixingSubgroup) (fun σ hσ => ?_)
    (ℚ⟮(b : ℚ̄)⟯).fixingSubgroup_isOpen
  rw [MulAction.mem_stabilizer_iff]
  exact RingOfIntegers.ext ((mem_fixingSubgroup_iff _ σ).mp hσ (b : ℚ̄) (mem_adjoin_simple_self ℚ _))

noncomputable abbrev ringOfIntegersIncl (L : IntermediateField ℚ ℚ̄) : 𝓞 L →+* 𝓞 ℚ̄ :=
  RingOfIntegers.mapRingHom (algebraMap L ℚ̄)

theorem coe_ringOfIntegersIncl (L : IntermediateField ℚ ℚ̄) (a : 𝓞 L) :
    ((ringOfIntegersIncl L a : 𝓞 ℚ̄) : ℚ̄) = ((a : L) : ℚ̄) :=
  rfl

theorem exists_mem_stabilizer_of_comap_eq (L : IntermediateField ℚ ℚ̄) (P : Ideal (𝓞 ℚ̄))
    [P.IsPrime] (τ : Gal(ℚ̄/ℚ))
    (h : (τ⁻¹ • P).comap (ringOfIntegersIncl L) = P.comap (ringOfIntegersIncl L)) :
    ∃ σ ∈ MulAction.stabilizer Gal(ℚ̄/ℚ) P, ∀ x ∈ L, σ x = τ x := by
  let G := L.fixingSubgroup
  let _ : Algebra (𝓞 L) (𝓞 ℚ̄) := (ringOfIntegersIncl L).toAlgebra
  let _ : TopologicalSpace (𝓞 ℚ̄) := ⊥
  have : DiscreteTopology (𝓞 ℚ̄) := ⟨rfl⟩
  have : CompactSpace G :=
    isCompact_iff_compactSpace.mp (InfiniteGalois.fixingSubgroup_isClosed L).isCompact
  have hfix : ∀ (g : G) (a : 𝓞 L), g • ringOfIntegersIncl L a = ringOfIntegersIncl L a :=
    fun g a => RingOfIntegers.ext ((mem_fixingSubgroup_iff _ _).1 g.2 _ (a : L).2)
  have : SMulCommClass G (𝓞 L) (𝓞 ℚ̄) := ⟨fun g a b => by
    rw [Algebra.smul_def, Algebra.smul_def, smul_mul', RingHom.algebraMap_toAlgebra, hfix]⟩
  have : ContinuousSMul G (𝓞 ℚ̄) := continuousSMul_iff_stabilizer_isOpen.2 fun b =>
    (isOpen_stabilizer_ringOfIntegers b).preimage continuous_subtype_val
  have : Algebra.IsInvariant (𝓞 L) (𝓞 ℚ̄) G := ⟨fun b hb => by
    have hmem : (b : ℚ̄) ∈ fixedField L.fixingSubgroup := by
      rw [mem_fixedField_iff]
      intro f hf
      exact congrArg (fun c : 𝓞 ℚ̄ => (c : ℚ̄)) (hb ⟨f, hf⟩)
    rw [InfiniteGalois.fixedField_fixingSubgroup] at hmem
    have hint : IsIntegral ℤ (⟨b, hmem⟩ : L) :=
      (isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ L ℚ̄) (algebraMap L ℚ̄).injective).1
        b.isIntegral_coe
    exact ⟨⟨⟨b, hmem⟩, hint⟩, RingOfIntegers.ext rfl⟩⟩
  obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite
    (A := 𝓞 L) (G := G) P (τ⁻¹ • P) h.symm
  refine ⟨τ * g, ?_, fun x hx => ?_⟩
  · rw [MulAction.mem_stabilizer_iff, mul_smul]
    calc τ • ((g : Gal(ℚ̄/ℚ)) • P) = τ • (g • P) := rfl
      _ = τ • (τ⁻¹ • P) := by rw [hg]; rfl
      _ = P := smul_inv_smul τ P
  · change τ ((g : Gal(ℚ̄/ℚ)) x) = τ x
    rw [(mem_fixingSubgroup_iff _ _).1 g.2 x hx]

end Lift

section Cyclotomic

theorem modCharacter_eq_of_eqOn {M : ℕ} [NeZero M] {σ τ : Gal(ℚ̄/ℚ)}
    (h : ∀ x ∈ rootsOfUnityField M, σ x = τ x) : modCharacter M σ = modCharacter M τ :=
  Units.ext (modCharacter_unique σ fun t ht => by
    rw [h t (subset_adjoin ℚ _ ht), modCharacter_spec τ ht])

theorem redUnits_character (q : Nat.Primes) (k : ℕ) (σ : Gal(ℚ̄/ℚ)) :
    (redUnits q k (Units.map (toPadicInt q).toMonoidHom (character σ)) : ZMod ((q : ℕ) ^ k)) =
      (modCharacter ((q : ℕ) ^ k) σ : ZMod ((q : ℕ) ^ k)) := by
  rw [coe_redUnits, Units.coe_map]
  change PadicInt.toZModPow k (toPadicInt q (character σ : ℤ̂)) = _
  rw [toZModPow_toPadicInt]
  exact proj_character (primePowPNat q k) σ

theorem exists_mem_stabilizer_modCharacter_eq_prime {p : ℕ} [Fact p.Prime] (P : Ideal (𝓞 ℚ̄))
    [P.IsPrime] [hP : P.LiesOver (Ideal.span {(p : ℤ)})] {M : ℕ} [NeZero M] (hM : ¬ p ∣ M) :
    ∃ σ ∈ MulAction.stabilizer Gal(ℚ̄/ℚ) P, (modCharacter M σ : ZMod M) = p := by
  set L := rootsOfUnityField M
  let Q : Ideal (𝓞 L) := P.comap (ringOfIntegersIncl L)
  have : Q.LiesOver (Ideal.span {(p : ℤ)}) := ⟨by
    rw [Ideal.under, Ideal.comap_comap, show (ringOfIntegersIncl L).comp (algebraMap ℤ (𝓞 L)) =
      algebraMap ℤ (𝓞 ℚ̄) from RingHom.ext_int _ _]
    exact hP.over⟩
  obtain ⟨τ₀, hτ₀, -⟩ := existsUnique_isArithFrobAt p L Q hM
  let τ : Gal(ℚ̄/ℚ) := τ₀.liftNormal ℚ̄
  have hτ : ∀ x : L, τ (x : ℚ̄) = (τ₀ x : ℚ̄) := fun x => τ₀.liftNormal_commutes ℚ̄ x
  have hstab := hτ₀.mem_stabilizer
  have h : (τ⁻¹ • P).comap (ringOfIntegersIncl L) = P.comap (ringOfIntegersIncl L) := by
    ext x
    rw [Ideal.mem_comap, Ideal.mem_comap, Ideal.mem_pointwise_smul_iff_inv_smul_mem, inv_inv]
    have h1 : τ • ringOfIntegersIncl L x = ringOfIntegersIncl L (τ₀ • x) :=
      RingOfIntegers.ext (hτ x)
    rw [h1, ← Ideal.mem_comap]
    change τ₀ • x ∈ Q ↔ x ∈ Q
    conv_lhs => rw [← MulAction.mem_stabilizer_iff.1 hstab]
    exact Ideal.smul_mem_pointwise_smul_iff
  obtain ⟨σ, hσ, hστ⟩ := exists_mem_stabilizer_of_comap_eq L P τ h
  refine ⟨σ, hσ, ?_⟩
  have hres : σ.restrictNormal L = τ₀ := by
    ext x
    rw [← hτ x, ← hστ _ x.2]
    exact σ.restrictNormal_commutes L x
  rw [← isArithFrobAt_restrictNormal_iff M p Q hM σ, hres]
  exact hτ₀

theorem eq_of_natCast_mem_rootsOfUnityField {p : ℕ} [hp : Fact p.Prime] (k : ℕ)
    {Q₁ Q₂ : Ideal (𝓞 (rootsOfUnityField (p ^ (k + 1))))} [Q₁.IsPrime] [Q₂.IsPrime]
    (h₁ : (p : 𝓞 (rootsOfUnityField (p ^ (k + 1)))) ∈ Q₁)
    (h₂ : (p : 𝓞 (rootsOfUnityField (p ^ (k + 1)))) ∈ Q₂) : Q₁ = Q₂ := by
  let L := rootsOfUnityField (p ^ (k + 1))
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot ℚ̄ (p ^ (k + 1))
  let ζL : L := ⟨ζ, subset_adjoin ℚ _ hζ.pow_eq_one⟩
  have hζL : IsPrimitiveRoot ζL (p ^ (k + 1)) :=
    IsPrimitiveRoot.of_map_of_injective (f := algebraMap L ℚ̄) hζ (algebraMap L ℚ̄).injective
  have hprime : Prime (hζL.toInteger - 1) := hζL.zeta_sub_one_prime
  have hmax : (Ideal.span {hζL.toInteger - 1}).IsMaximal :=
    ((Ideal.span_singleton_prime hprime.ne_zero).2 hprime).isMaximal
      (by rw [Ne, Ideal.span_singleton_eq_bot]; exact hprime.ne_zero)
  have key : ∀ Q : Ideal (𝓞 L), Q.IsPrime → (p : 𝓞 L) ∈ Q →
      Q = Ideal.span {hζL.toInteger - 1} := by
    intro Q hQ hpQ
    refine (hmax.eq_of_le hQ.ne_top ?_).symm
    rw [Ideal.span_singleton_le_iff_mem, ← Ideal.Quotient.eq_zero_iff_mem]
    have : CharP (𝓞 L ⧸ Q) p := (CharP.charP_iff_prime_eq_zero hp.out).2 (by
      rw [← map_natCast (Ideal.Quotient.mk Q), Ideal.Quotient.eq_zero_iff_mem]
      exact hpQ)
    have h1 : (Ideal.Quotient.mk Q (hζL.toInteger - 1)) ^ (p ^ (k + 1)) = 0 := by
      rw [map_sub, map_one, sub_pow_char_pow, ← map_pow,
        (hζL.toInteger_isPrimitiveRoot).pow_eq_one, map_one, one_pow, sub_self]
    exact (pow_eq_zero_iff (pow_ne_zero _ hp.out.ne_zero)).1 h1
  rw [key Q₁ ‹_› h₁, key Q₂ ‹_› h₂]

theorem exists_mem_stabilizer_modCharacter_eq_of_prime_pow {p : ℕ} [hp : Fact p.Prime]
    (P : Ideal (𝓞 ℚ̄)) [P.IsPrime] [hP : P.LiesOver (Ideal.span {(p : ℤ)})] (k : ℕ)
    (a : (ZMod (p ^ (k + 1)))ˣ) :
    ∃ σ ∈ MulAction.stabilizer Gal(ℚ̄/ℚ) P, modCharacter (p ^ (k + 1)) σ = a := by
  obtain ⟨τ, hτ⟩ := exists_modCharacter_eq (p ^ (k + 1)) a
  set L := rootsOfUnityField (p ^ (k + 1))
  have hpP : ((p : ℕ) : 𝓞 ℚ̄) ∈ P := by
    have h : (p : ℤ) ∈ P.under ℤ := by
      rw [← hP.over]
      exact Ideal.mem_span_singleton_self _
    rw [Ideal.under, Ideal.mem_comap, map_natCast] at h
    exact h
  have hpP' : ((p : ℕ) : 𝓞 ℚ̄) ∈ τ⁻¹ • P := by
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, inv_inv]
    change MulSemiringAction.toRingHom _ _ τ (p : 𝓞 ℚ̄) ∈ P
    rw [map_natCast]
    exact hpP
  have h : (τ⁻¹ • P).comap (ringOfIntegersIncl L) = P.comap (ringOfIntegersIncl L) :=
    eq_of_natCast_mem_rootsOfUnityField k (by rw [Ideal.mem_comap, map_natCast]; exact hpP')
      (by rw [Ideal.mem_comap, map_natCast]; exact hpP)
  obtain ⟨σ, hσ, hστ⟩ := exists_mem_stabilizer_of_comap_eq L P τ h
  exact ⟨σ, hσ, (modCharacter_eq_of_eqOn hστ).trans hτ⟩


end Cyclotomic

section Component

theorem exists_degreeComponent_ne_one (q : Nat.Primes) (w : ℤ_[q]ˣ)
    (hw : padicUnitsLog q w ≠ 1) :
    ∃ N, 0 < N ∧ ∀ σ : Gal(ℚ̄/ℚ), (modCharacter ((q : ℕ) ^ N) σ : ZMod ((q : ℕ) ^ N)) =
      PadicInt.toZModPow N (w : ℤ_[q]) → degreeComponent q σ ≠ 1 := by
  obtain ⟨n, hn⟩ : ∃ n, PadicInt.toZModPow n (Multiplicative.toAdd (padicUnitsLog q w)) ≠ 0 := by
    by_contra! hcon
    apply hw
    have h0 : Multiplicative.toAdd (padicUnitsLog q w) = 0 :=
      PadicInt.ext_of_toZModPow.mp fun n => by rw [hcon n, map_zero]
    rw [← ofAdd_toAdd (padicUnitsLog q w), h0, ofAdd_zero]
  refine ⟨n + unitsLevel q, by have := unitsLevel_ne_zero q; omega, fun σ hσ h1 => hn ?_⟩
  have hred : redUnits q (n + unitsLevel q) (Units.map (toPadicInt q).toMonoidHom (character σ)) =
      redUnits q (n + unitsLevel q) w :=
    Units.ext (by rw [redUnits_character, hσ, coe_redUnits])
  rw [toZModPow_padicUnitsLog, ← hred, ← toZModPow_padicUnitsLog, ← degreeComponent_apply, h1,
    toAdd_one, map_zero]

theorem genLog_ne_zero (ℓ : ℕ) [hℓ : Fact ℓ.Prime] : genLog ℓ ≠ 0 := by
  intro h
  have := coprime_genLog ℓ
  rw [h, Nat.coprime_zero_right] at this
  exact hℓ.out.one_lt.ne' this

theorem exists_mem_stabilizer_degreeComponent_ne_one {p : ℕ} [hp : Fact p.Prime]
    (P : Ideal (𝓞 ℚ̄)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})] (q : Nat.Primes) :
    ∃ σ ∈ MulAction.stabilizer Gal(ℚ̄/ℚ) P, degreeComponent q σ ≠ 1 := by
  have : NeZero (q : ℕ) := ⟨q.2.ne_zero⟩
  by_cases hpq : p = q
  · have hw : padicUnitsLog q (genPadicUnit q) ≠ 1 := by
      intro h
      have := padicUnitsLog_genPadicUnit (q : ℕ)
      rw [h, toAdd_one] at this
      exact genLog_ne_zero q (Nat.cast_eq_zero.1 this.symm)
    obtain ⟨N, hN, hσ⟩ := exists_degreeComponent_ne_one q _ hw
    obtain ⟨k, rfl⟩ : ∃ k, N = k + 1 := ⟨N - 1, by omega⟩
    subst hpq
    obtain ⟨σ, hσP, hσa⟩ := exists_mem_stabilizer_modCharacter_eq_of_prime_pow P k
      (redUnits q (k + 1) (genPadicUnit q))
    exact ⟨σ, hσP, hσ σ (by rw [hσa, coe_redUnits])⟩
  · have hcop : Nat.Coprime q p := (Nat.coprime_primes q.2 hp.out).2 (Ne.symm hpq)
    have hw : padicUnitsLog q (isUnit_natCast_of_coprime (q : ℕ) hcop).unit ≠ 1 := by
      intro h
      rw [padicUnitsLog_eq_one_iff] at h
      have h2 := congrArg (fun u : ℤ_[q]ˣ => (u : ℤ_[q])) h
      simp only [Units.val_pow_eq_pow_val, IsUnit.unit_spec, Units.val_one] at h2
      rw [← Nat.cast_pow, ← Nat.cast_one, Nat.cast_inj, Nat.pow_eq_one] at h2
      rcases h2 with h2 | h2
      · exact hp.out.one_lt.ne' h2
      · exact (torsionExponent_pos q).ne' h2
    obtain ⟨N, -, hσ⟩ := exists_degreeComponent_ne_one q _ hw
    have hM : ¬ p ∣ (q : ℕ) ^ N := fun h =>
      hpq ((Nat.prime_dvd_prime_iff_eq hp.out q.2).1 (hp.out.dvd_of_dvd_pow h))
    obtain ⟨σ, hσP, hσp⟩ := exists_mem_stabilizer_modCharacter_eq_prime P hM
    exact ⟨σ, hσP, hσ σ (by rw [hσp, IsUnit.unit_spec, map_natCast])⟩

end Component

section Image

theorem isClosed_stabilizer (P : Ideal (𝓞 ℚ̄)) :
    IsClosed (MulAction.stabilizer Gal(ℚ̄/ℚ) P : Set Gal(ℚ̄/ℚ)) := by
  let _ : TopologicalSpace (𝓞 ℚ̄) := ⊥
  have : DiscreteTopology (𝓞 ℚ̄) := ⟨rfl⟩
  have : ContinuousSMul Gal(ℚ̄/ℚ) (𝓞 ℚ̄) :=
    continuousSMul_iff_stabilizer_isOpen.2 isOpen_stabilizer_ringOfIntegers
  have hset : (MulAction.stabilizer Gal(ℚ̄/ℚ) P : Set Gal(ℚ̄/ℚ)) =
      (⋂ x ∈ P, (fun σ : Gal(ℚ̄/ℚ) => σ • x) ⁻¹' (P : Set (𝓞 ℚ̄))) ∩
        ⋂ x ∈ P, (fun σ : Gal(ℚ̄/ℚ) => σ⁻¹ • x) ⁻¹' (P : Set (𝓞 ℚ̄)) := by
    ext σ
    simp only [SetLike.mem_coe, MulAction.mem_stabilizer_iff, Set.mem_inter_iff, Set.mem_iInter,
      Set.mem_preimage]
    constructor
    · intro h
      refine ⟨fun x hx => ?_, fun x hx => ?_⟩
      · rw [← h]
        exact Ideal.smul_mem_pointwise_smul_iff.2 hx
      · rw [← Ideal.mem_pointwise_smul_iff_inv_smul_mem, h]
        exact hx
    · rintro ⟨h1, h2⟩
      apply le_antisymm
      · intro y hy
        rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem] at hy
        have := h1 _ hy
        rwa [smul_inv_smul] at this
      · intro y hy
        rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem]
        exact h2 y hy
  rw [hset]
  refine (isClosed_biInter fun x _ => ?_).inter (isClosed_biInter fun x _ => ?_)
  · exact (isClosed_discrete (P : Set (𝓞 ℚ̄))).preimage (continuous_id.smul continuous_const)
  · exact (isClosed_discrete (P : Set (𝓞 ℚ̄))).preimage (continuous_inv.smul continuous_const)

variable (q : Nat.Primes) (P : Ideal (𝓞 ℚ̄))

def decompositionComponentImage : AddSubgroup ℤ_[q] where
  carrier := (fun σ => Multiplicative.toAdd (degreeComponent q σ)) ''
    (MulAction.stabilizer Gal(ℚ̄/ℚ) P)
  add_mem' := by
    rintro _ _ ⟨σ, hσ, rfl⟩ ⟨τ, hτ, rfl⟩
    exact ⟨σ * τ, mul_mem hσ hτ, by simp⟩
  zero_mem' := ⟨1, one_mem _, by simp⟩
  neg_mem' := by
    rintro _ ⟨σ, hσ, rfl⟩
    exact ⟨σ⁻¹, inv_mem hσ, by simp⟩

theorem coe_decompositionComponentImage :
    (decompositionComponentImage q P : Set ℤ_[q]) =
      (fun σ => Multiplicative.toAdd (degreeComponent q σ)) ''
        (MulAction.stabilizer Gal(ℚ̄/ℚ) P) :=
  rfl

theorem isClosed_decompositionComponentImage :
    IsClosed (decompositionComponentImage q P : Set ℤ_[q]) :=
  ((isClosed_stabilizer P).isCompact.image
    (continuous_toAdd.comp (continuous_degreeComponent q))).isClosed

def decompositionDegreeImage : AddSubgroup ℤ̂ where
  carrier := (fun σ => Multiplicative.toAdd (degree σ)) '' (MulAction.stabilizer Gal(ℚ̄/ℚ) P)
  add_mem' := by
    rintro _ _ ⟨σ, hσ, rfl⟩ ⟨τ, hτ, rfl⟩
    exact ⟨σ * τ, mul_mem hσ hτ, by simp⟩
  zero_mem' := ⟨1, one_mem _, by simp⟩
  neg_mem' := by
    rintro _ ⟨σ, hσ, rfl⟩
    exact ⟨σ⁻¹, inv_mem hσ, by simp⟩

theorem coe_decompositionDegreeImage :
    (decompositionDegreeImage P : Set ℤ̂) =
      (fun σ => Multiplicative.toAdd (degree σ)) '' (MulAction.stabilizer Gal(ℚ̄/ℚ) P) :=
  rfl

theorem isClosed_decompositionDegreeImage :
    IsClosed (decompositionDegreeImage P : Set ℤ̂) :=
  ((isClosed_stabilizer P).isCompact.image (continuous_toAdd.comp continuous_degree)).isClosed

theorem topologicalClosure_decompositionDegreeImage :
    (decompositionDegreeImage P).topologicalClosure = decompositionDegreeImage P :=
  SetLike.coe_injective (by
    rw [AddSubgroup.topologicalClosure_coe, (isClosed_decompositionDegreeImage P).closure_eq])

theorem exists_mem_decompositionComponentImage_ne_zero (p : ℕ) [Fact p.Prime] [P.IsPrime]
    [P.LiesOver (Ideal.span {(p : ℤ)})] :
    ∃ x ∈ decompositionComponentImage q P, x ≠ 0 := by
  obtain ⟨σ, hσ, hne⟩ := exists_mem_stabilizer_degreeComponent_ne_one (p := p) P q
  refine ⟨_, ⟨σ, hσ, rfl⟩, fun h => hne ?_⟩
  have h' : Multiplicative.toAdd (degreeComponent q σ) = 0 := h
  rw [← ofAdd_toAdd (degreeComponent q σ), h', ofAdd_zero]

theorem isOpen_decompositionComponentImage (p : ℕ) [Fact p.Prime] [P.IsPrime]
    [P.LiesOver (Ideal.span {(p : ℤ)})] :
    IsOpen (decompositionComponentImage q P : Set ℤ_[q]) := by
  obtain ⟨x, hx, hx0⟩ := exists_mem_decompositionComponentImage_ne_zero q P p
  exact isOpen_of_isClosed_of_ne_zero _ (isClosed_decompositionComponentImage q P) hx hx0

theorem infinite_decompositionComponentImage (p : ℕ) [Fact p.Prime] [P.IsPrime]
    [P.LiesOver (Ideal.span {(p : ℤ)})] :
    (decompositionComponentImage q P : Set ℤ_[q]).Infinite := by
  obtain ⟨x, hx, hx0⟩ := exists_mem_decompositionComponentImage_ne_zero q P p
  exact infinite_of_ne_zero _ hx hx0

theorem nonempty_addEquiv_decompositionDegreeImage (p : ℕ) [Fact p.Prime] [P.IsPrime]
    [P.LiesOver (Ideal.span {(p : ℤ)})] :
    Nonempty ((decompositionDegreeImage P).topologicalClosure ≃+ ℤ̂) := by
  rw [topologicalClosure_decompositionDegreeImage]
  refine nonempty_addEquiv_of_isClosed _ (isClosed_decompositionDegreeImage P) fun q => ?_
  obtain ⟨σ, hσ, hne⟩ := exists_mem_stabilizer_degreeComponent_ne_one (p := p) P q
  refine ⟨_, ⟨σ, hσ, rfl⟩, ?_⟩
  rw [toPadicInt_degree]
  exact fun h => hne (by rw [← ofAdd_toAdd (degreeComponent q σ), h, ofAdd_zero])

end Image

end Sec_CC_DegreeDecomposition

end Cyclotomic

end RHDirect.CFT_CyclotomicCharacters
