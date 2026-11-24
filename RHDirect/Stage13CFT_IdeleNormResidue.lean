import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Algebra.Group.Action.Basic
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Normal.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import Mathlib.RepresentationTheory.Basic
import Mathlib.RepresentationTheory.Invariants
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.NumberTheory.NumberField.Ideal.Basic
import Mathlib.NumberTheory.NumberField.ProductFormula
import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.ClassGroup.Basic
import Mathlib.RingTheory.FractionalIdeal.Operations
import Mathlib.RingTheory.FractionalIdeal.Inverse
import Mathlib.Topology.Algebra.RestrictedProduct.Basic
import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.DedekindDomain.SInteger
import Mathlib.RingTheory.DedekindDomain.SelmerGroup
import Mathlib.RingTheory.Ideal.Over
import Mathlib.RingTheory.Ideal.Pointwise
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.GroupTheory.Finiteness
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Normed.Field.ProperSpace
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.NumberTheory.NumberField.Units.Regulator
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.Algebra.Order.Positive.Field
import Mathlib.RingTheory.Norm.Basic
import Mathlib.RingTheory.Trace.Basic
import Mathlib.RingTheory.Valuation.Integral
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.Cyclotomic.Gal
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots

/-!
# RHDirect.Stage13CFT_IdeleNormResidue

Option-C Global Class Field Theory Wave 1 (`namespace RHDirect.Stage13CFT_IdeleNormResidue`):
Direct zero-wrapper formalization on concrete Mathlib `v4.33.1` types (`NumberField.AdeleRing`,
`IsDedekindDomain.HeightOneSpectrum`, `ClassGroup`, `NumberField.InfinitePlace`).
-/

noncomputable section

namespace RHDirect.Stage13CFT_IdeleNormResidue

namespace SemiLocal
open IsDedekindDomain NumberField WithZero
open scoped Pointwise
section ActionDefs
variable {K : Type*} [Field K] [NumberField K] (L : Type*) [Field L] [NumberField L] [Algebra K L]
abbrev PlacesOver (v : HeightOneSpectrum (𝓞 K)) : Type _ := {w : HeightOneSpectrum (𝓞 L) // w.asIdeal.LiesOver v.asIdeal}
instance (v : HeightOneSpectrum (𝓞 K)) (w : PlacesOver L v) : w.1.asIdeal.LiesOver v.asIdeal := w.2
def placesOverEquiv (v : HeightOneSpectrum (𝓞 K)) : PlacesOver L v ≃ v.asIdeal.primesOver (𝓞 L) where
  toFun w := ⟨w.1.asIdeal, w.1.isPrime, w.2⟩
  invFun P := ⟨⟨P.1, P.2.1, fun h => v.ne_bot (by rw [P.2.2.over, h, Ideal.under_bot])⟩, P.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
instance (v : HeightOneSpectrum (𝓞 K)) : Fintype (PlacesOver L v) :=
  Fintype.ofEquiv _ (placesOverEquiv L v).symm
end ActionDefs
variable {K L : Type*} [Field K] [Field L] [NumberField L] [Algebra K L]
section Action
instance : SMulCommClass (L ≃ₐ[K] L) (𝓞 K) (𝓞 L) where
  smul_comm σ a x := by
    apply RingOfIntegers.ext
    have h : ∀ y : 𝓞 L, ((a • y : 𝓞 L) : L) = algebraMap K L (a : K) * (y : L) := fun y ↦ by
      rw [Algebra.smul_def]
      change algebraMap (𝓞 L) L (algebraMap (𝓞 K) (𝓞 L) a * y) = _; rw [map_mul, ← IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 L) L, IsScalarTower.algebraMap_apply (𝓞 K) K L]
    change σ ((a • x : 𝓞 L) : L) = ((a • (σ • x) : 𝓞 L) : L); rw [h, h, map_mul, AlgEquiv.commutes]; rfl
instance : MulAction (L ≃ₐ[K] L) (HeightOneSpectrum (𝓞 L)) where
  smul σ w := ⟨σ • w.asIdeal, inferInstance, by
    intro h; apply w.ne_bot; rw [← inv_smul_smul σ w.asIdeal, h, Ideal.pointwise_smul_def, Ideal.map_bot]⟩
  one_smul w := HeightOneSpectrum.ext (one_smul _ w.asIdeal)
  mul_smul σ τ w := HeightOneSpectrum.ext (mul_smul σ τ w.asIdeal)
omit [NumberField L] in
theorem smul_asIdeal (σ : L ≃ₐ[K] L) (w : HeightOneSpectrum (𝓞 L)) : (σ • w).asIdeal = σ • w.asIdeal := rfl
theorem intValuation_smul (σ : L ≃ₐ[K] L) (w : HeightOneSpectrum (𝓞 L)) (x : 𝓞 L) : (σ • w).intValuation (σ • x) = w.intValuation x := by
  by_cases hx : x = 0
  · subst hx
    simp
  have hσx : σ • x ≠ 0 := fun h ↦ hx (by rw [← inv_smul_smul σ x, h, smul_zero])
  have key : ∀ n : ℕ, (σ • w).intValuation (σ • x) ≤ exp (-(n : ℤ)) ↔
      w.intValuation x ≤ exp (-(n : ℤ)) := by
    intro n; rw [HeightOneSpectrum.intValuation_le_pow_iff_mem, HeightOneSpectrum.intValuation_le_pow_iff_mem, smul_asIdeal, ← smul_pow', Ideal.smul_mem_pointwise_smul_iff]
  rw [HeightOneSpectrum.intValuation_eq_exp_neg_multiplicity _ hσx, HeightOneSpectrum.intValuation_eq_exp_neg_multiplicity _ hx] at key ⊢
  simp only [exp_le_exp, neg_le_neg_iff, Nat.cast_le] at key
  rw [le_antisymm ((key _).1 le_rfl) ((key _).2 le_rfl)]
theorem valuation_smul (σ : L ≃ₐ[K] L) (w : HeightOneSpectrum (𝓞 L)) (x : L) : (σ • w).valuation L (σ x) = w.valuation L x := by
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 L) x
  have h : ∀ c : 𝓞 L, σ (algebraMap (𝓞 L) L c) = algebraMap (𝓞 L) L (σ • c) := fun _ ↦ rfl
  rw [map_div₀, map_div₀, map_div₀, h, h, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.valuation_of_algebraMap, intValuation_smul, intValuation_smul]
theorem absNorm_smul (σ : L ≃ₐ[K] L) (w : HeightOneSpectrum (𝓞 L)) : Ideal.absNorm (σ • w).asIdeal = Ideal.absNorm w.asIdeal := by
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  exact Nat.card_congr (Ideal.quotientEquiv w.asIdeal (σ • w).asIdeal (MulSemiringAction.toRingEquiv _ (𝓞 L) σ) (by rw [smul_asIdeal, Ideal.pointwise_smul_def]; rfl)).toEquiv.symm
theorem norm_algebraMap_smul (σ : L ≃ₐ[K] L) (w : HeightOneSpectrum (𝓞 L)) (x : L) : ‖algebraMap L ((σ • w).adicCompletion L) (σ x)‖ = ‖algebraMap L (w.adicCompletion L) x‖ := by
  rw [HeightOneSpectrum.algebraMap_adicCompletion, HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply, Function.comp_apply, Algebra.algebraMap_self, RingHom.id_apply,
    RingHom.id_apply, ← FinitePlace.embedding_apply, ← FinitePlace.embedding_apply,
    FinitePlace.norm_embedding', FinitePlace.norm_embedding', valuation_smul]
  have : ∀ (e₁ e₂ : NNReal) (h₁ : e₁ ≠ 0) (h₂ : e₂ ≠ 0), e₁ = e₂ → ∀ c : ℤᵐ⁰,
      WithZeroMulInt.toNNReal h₁ c = WithZeroMulInt.toNNReal h₂ c := by
    rintro _ _ _ _ rfl _; rfl
  rw [this _ _ _ _ (by rw [absNorm_smul])]
variable [NumberField K] (v : HeightOneSpectrum (𝓞 K))
instance : MulAction (L ≃ₐ[K] L) (PlacesOver L v) where
  smul σ w := ⟨σ • w.1, show (σ • w.1.asIdeal).LiesOver v.asIdeal from inferInstance⟩
  one_smul w := Subtype.ext (one_smul _ w.1)
  mul_smul σ τ w := Subtype.ext (mul_smul σ τ w.1)
omit [NumberField K] [NumberField L] in
@[simp] theorem coe_smul_placesOver (σ : L ≃ₐ[K] L) (w : PlacesOver L v) :
    (σ • w).1 = σ • w.1 := rfl
instance [IsGalois K L] : MulAction.IsPretransitive (L ≃ₐ[K] L) (PlacesOver L v) where
  exists_smul_eq w₁ w₂ := by obtain ⟨σ, hσ⟩ := Ideal.exists_smul_eq_of_isGaloisGroup v.asIdeal w₁.1.asIdeal w₂.1.asIdeal (L ≃ₐ[K] L); exact ⟨σ, Subtype.ext (HeightOneSpectrum.ext hσ)⟩
end Action
end SemiLocal

/-! ### HerbrandAbstract -/
section Sec_HerbrandAbstract
section Card
theorem natCard_eq_ker_mul_range {X Y : Type*} [AddGroup X] [AddGroup Y] (φ : X →+ Y) :
    Nat.card X = Nat.card φ.ker * Nat.card φ.range := by
  rw [← AddSubgroup.index_ker φ, AddSubgroup.card_mul_index]
theorem finite_of_exact {X Y Z : Type*} [AddGroup X] [AddGroup Y] [AddGroup Z]
    (d : X →+ Y) (e : Y →+ Z) (h : e.ker = d.range) [Finite X] [Finite Z] : Finite Y := by
  have h1 : Finite d.range := Finite.of_surjective _ d.rangeRestrict_surjective
  have h2 : Finite e.ker := by rw [h]; exact h1
  apply Nat.finite_of_card_ne_zero
  rw [natCard_eq_ker_mul_range e]
  exact Nat.mul_ne_zero Nat.card_pos.ne' Nat.card_pos.ne'
theorem natCard_hexagon {X₁ X₂ X₃ X₄ X₅ X₆ : Type*} [AddGroup X₁] [AddGroup X₂] [AddGroup X₃] [AddGroup X₄] [AddGroup X₅] [AddGroup X₆] (d₁ : X₁ →+ X₂) (d₂ : X₂ →+ X₃) (d₃ : X₃ →+ X₄) (d₄ : X₄ →+ X₅) (d₅ : X₅ →+ X₆)
    (d₆ : X₆ →+ X₁) (e₁ : d₁.ker = d₆.range) (e₂ : d₂.ker = d₁.range) (e₃ : d₃.ker = d₂.range)
    (e₄ : d₄.ker = d₃.range) (e₅ : d₅.ker = d₄.range) (e₆ : d₆.ker = d₅.range) :
    Nat.card X₁ * Nat.card X₃ * Nat.card X₅ = Nat.card X₂ * Nat.card X₄ * Nat.card X₆ := by
  rw [natCard_eq_ker_mul_range d₁, natCard_eq_ker_mul_range d₂, natCard_eq_ker_mul_range d₃, natCard_eq_ker_mul_range d₄, natCard_eq_ker_mul_range d₅, natCard_eq_ker_mul_range d₆, e₁, e₂, e₃, e₄, e₅, e₆]
  ring
end Card
section Defs
variable {A : Type*} [AddCommGroup A]
abbrev KerModRange (f g : A →+ A) : Type _ :=
  f.ker ⧸ g.range.addSubgroupOf f.ker
def HasHerbrandQuotient (f g : A →+ A) : Prop :=
  Finite (KerModRange f g) ∧ Finite (KerModRange g f)
noncomputable def herbrandQuotient (f g : A →+ A) : ℚ :=
  (Nat.card (KerModRange f g) : ℚ) / Nat.card (KerModRange g f)
theorem range_le_ker {f g : A →+ A} (hfg : ∀ x, f (g x) = 0) : g.range ≤ f.ker := by
  intro y hy
  obtain ⟨x, rfl⟩ := AddMonoidHom.mem_range.1 hy; exact AddMonoidHom.mem_ker.2 (hfg x)
theorem KerModRange.mk_eq_zero_iff {f g : A →+ A} (x : f.ker) :
    (QuotientAddGroup.mk x : KerModRange f g) = 0 ↔ (x : A) ∈ g.range := by
  rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
theorem KerModRange.mk_eq_mk_iff {f g : A →+ A} (x y : f.ker) : (QuotientAddGroup.mk x : KerModRange f g) = QuotientAddGroup.mk y ↔
      (x : A) - y ∈ g.range := by
  rw [QuotientAddGroup.eq_iff_sub_mem, AddSubgroup.mem_addSubgroupOf, AddSubgroup.coe_sub]
theorem natCard_ker_eq {f g : A →+ A} (hfg : ∀ x, f (g x) = 0) :
    Nat.card f.ker = Nat.card (KerModRange f g) * Nat.card g.range := by
  have h1 := AddSubgroup.card_mul_index (g.range.addSubgroupOf f.ker)
  have h2 : Nat.card (g.range.addSubgroupOf f.ker) = Nat.card g.range :=
    Nat.card_congr (AddSubgroup.addSubgroupOfEquivOfLe (range_le_ker hfg)).toEquiv
  rw [← h1, h2, mul_comm]
  rfl
theorem hasHerbrandQuotient_of_finite [Finite A] (f g : A →+ A) : HasHerbrandQuotient f g :=
  ⟨inferInstance, inferInstance⟩
theorem natCard_kerModRange_eq_of_finite [Finite A] {f g : A →+ A} (hfg : ∀ x, f (g x) = 0)
    (hgf : ∀ x, g (f x) = 0) : Nat.card (KerModRange f g) = Nat.card (KerModRange g f) := by
  have h1 := natCard_ker_eq hfg
  have h2 := natCard_ker_eq hgf
  have h3 := natCard_eq_ker_mul_range f
  have h4 := natCard_eq_ker_mul_range g
  have hf : 0 < Nat.card f.range := Nat.card_pos
  have hg : 0 < Nat.card g.range := Nat.card_pos
  have key : Nat.card (KerModRange f g) * (Nat.card g.range * Nat.card f.range) =
      Nat.card (KerModRange g f) * (Nat.card g.range * Nat.card f.range) := by
    calc _ = Nat.card f.ker * Nat.card f.range := by rw [h1]; ring
      _ = Nat.card g.ker * Nat.card g.range := by rw [← h3, ← h4]
      _ = _ := by rw [h2]; ring
  exact Nat.eq_of_mul_eq_mul_right (Nat.mul_pos hg hf) key
theorem herbrandQuotient_eq_one_of_finite [Finite A] {f g : A →+ A} (hfg : ∀ x, f (g x) = 0)
    (hgf : ∀ x, g (f x) = 0) : herbrandQuotient f g = 1 := by
  have hq : 0 < Nat.card (KerModRange g f) := Nat.card_pos; rw [herbrandQuotient, natCard_kerModRange_eq_of_finite hfg hgf, div_self]; exact_mod_cast hq.ne'
end Defs
section Maps
variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]
def kerMap {fA : A →+ A} {fB : B →+ B} (i : A →+ B) (hf : ∀ a, i (fA a) = fB (i a)) :
    fA.ker →+ fB.ker :=
  (i.comp fA.ker.subtype).codRestrict fB.ker fun a => by
    rw [AddMonoidHom.mem_ker, AddMonoidHom.comp_apply, AddSubgroup.coe_subtype, ← hf, AddMonoidHom.mem_ker.1 a.2, map_zero]
@[simp]
theorem kerMap_apply {fA : A →+ A} {fB : B →+ B} (i : A →+ B) (hf : ∀ a, i (fA a) = fB (i a))
    (a : fA.ker) : (kerMap i hf a : B) = i a :=
  rfl
def KerModRange.map {fA gA : A →+ A} {fB gB : B →+ B} (i : A →+ B) (hf : ∀ a, i (fA a) = fB (i a)) (hg : ∀ a, i (gA a) = gB (i a)) :
    KerModRange fA gA →+ KerModRange fB gB :=
  QuotientAddGroup.map _ _ (kerMap i hf) fun a ha => by
    rw [AddSubgroup.mem_comap, AddSubgroup.mem_addSubgroupOf, kerMap_apply]
    rw [AddSubgroup.mem_addSubgroupOf] at ha
    obtain ⟨x, hx⟩ := AddMonoidHom.mem_range.1 ha; exact AddMonoidHom.mem_range.2 ⟨i x, by rw [← hg, hx]⟩
theorem KerModRange.map_mk {fA gA : A →+ A} {fB gB : B →+ B} (i : A →+ B) (hf : ∀ a, i (fA a) = fB (i a)) (hg : ∀ a, i (gA a) = gB (i a)) (a : fA.ker) : KerModRange.map i hf hg (QuotientAddGroup.mk a : KerModRange fA gA) =
      (QuotientAddGroup.mk (kerMap i hf a) : KerModRange fB gB) :=
  rfl
end Maps
section Hexagon
variable {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] {fA gA : A →+ A} {fB gB : B →+ B} {fC gC : C →+ C} {i : A →+ B} {p : B →+ C}
theorem KerModRange.ker_map_eq_range_map (hi : Function.Injective i) (hp : Function.Surjective p) (hex : Function.Exact i p) (hfi : ∀ a, i (fA a) = fB (i a)) (hgi : ∀ a, i (gA a) = gB (i a))
    (hfp : ∀ b, p (fB b) = fC (p b)) (hgp : ∀ b, p (gB b) = gC (p b))
    (hfgB : ∀ b, fB (gB b) = 0) :
    (KerModRange.map p hfp hgp).ker = (KerModRange.map i hfi hgi).range := by
  ext x
  induction x using QuotientAddGroup.induction_on with
  | H z =>
  obtain ⟨b, hb⟩ := z; rw [AddMonoidHom.mem_ker, KerModRange.map_mk, KerModRange.mk_eq_zero_iff, kerMap_apply, AddMonoidHom.mem_range]; constructor
  · intro h
    obtain ⟨c, hc⟩ := AddMonoidHom.mem_range.1 h
    obtain ⟨b', rfl⟩ := hp c
    obtain ⟨a, ha⟩ : b - gB b' ∈ Set.range i :=
      (hex _).1 (by rw [map_sub, hgp, hc, sub_self])
    have hfa : fA a = 0 := hi (by
      rw [hfi, ha, map_sub, hfgB, AddMonoidHom.mem_ker.1 hb, sub_zero, map_zero])
    refine ⟨QuotientAddGroup.mk ⟨a, hfa⟩, ?_⟩
    rw [KerModRange.map_mk, KerModRange.mk_eq_mk_iff, kerMap_apply]
    exact AddMonoidHom.mem_range.2 ⟨-b', by rw [ha, map_neg]; abel⟩
  · rintro ⟨y, hy⟩
    induction y using QuotientAddGroup.induction_on with
    | H w =>
    obtain ⟨a, ha⟩ := w; rw [KerModRange.map_mk, KerModRange.mk_eq_mk_iff, kerMap_apply] at hy
    obtain ⟨b'', hb''⟩ := AddMonoidHom.mem_range.1 hy
    have hpa : p (i a) = 0 := (hex _).2 ⟨a, rfl⟩; refine AddMonoidHom.mem_range.2 ⟨-p b'', ?_⟩
    have : b = i a - gB b'' := by rw [hb'']; abel
    show gC (-p b'') = p b
    rw [this, map_sub, hpa, hgp, map_neg, zero_sub]
def connDomain (fB : B →+ B) (i : A →+ B) : AddSubgroup B :=
  i.range.comap fB
theorem connDomain_mem_ker (hex : Function.Exact i p) (hfp : ∀ b, p (fB b) = fC (p b)) (s : connDomain fB i) : p s ∈ fC.ker := by
  have : p (fB s) = 0 := (hex _).2 (AddMonoidHom.mem_range.1 (AddSubgroup.mem_comap.1 s.2)); rw [AddMonoidHom.mem_ker, ← hfp, this]
def connLeft (hex : Function.Exact i p) (hfp : ∀ b, p (fB b) = fC (p b)) : connDomain fB i →+ KerModRange fC gC :=
  (QuotientAddGroup.mk' _).comp <| (p.comp (connDomain fB i).subtype).codRestrict fC.ker (connDomain_mem_ker hex hfp)
theorem connLeft_apply (hex : Function.Exact i p) (hfp : ∀ b, p (fB b) = fC (p b)) (s : connDomain fB i) : (connLeft hex hfp s : KerModRange fC gC) = QuotientAddGroup.mk (⟨p s, connDomain_mem_ker hex hfp s⟩ : fC.ker) :=
  rfl
noncomputable def connInv (hi : Function.Injective i) : connDomain fB i →+ A :=
  (AddMonoidHom.ofInjective hi).symm.toAddMonoidHom.comp <| (fB.comp (connDomain fB i).subtype).codRestrict i.range fun s => s.2
theorem apply_connInv (hi : Function.Injective i) (s : connDomain fB i) : i (connInv hi s) = fB s :=
  AddMonoidHom.apply_ofInjective_symm hi _
theorem connInv_mem_ker (hi : Function.Injective i) (hgi : ∀ a, i (gA a) = gB (i a)) (hgfB : ∀ b, gB (fB b) = 0) (s : connDomain fB i) : connInv hi s ∈ gA.ker := by
  rw [AddMonoidHom.mem_ker]
  apply hi
  rw [hgi, apply_connInv, hgfB, map_zero]
noncomputable def connRight (hi : Function.Injective i) (hgi : ∀ a, i (gA a) = gB (i a)) (hgfB : ∀ b, gB (fB b) = 0) : connDomain fB i →+ KerModRange gA fA :=
  (QuotientAddGroup.mk' _).comp <| (connInv hi).codRestrict gA.ker (connInv_mem_ker hi hgi hgfB)
theorem connRight_apply (hi : Function.Injective i) (hgi : ∀ a, i (gA a) = gB (i a)) (hgfB : ∀ b, gB (fB b) = 0) (s : connDomain fB i) : (connRight hi hgi hgfB s : KerModRange gA fA) =
      QuotientAddGroup.mk (⟨connInv hi s, connInv_mem_ker hi hgi hgfB s⟩ : gA.ker) :=
  rfl
theorem connLeft_surjective (hp : Function.Surjective p) (hex : Function.Exact i p) (hfp : ∀ b, p (fB b) = fC (p b)) : Function.Surjective (connLeft hex hfp : connDomain fB i →+ KerModRange fC gC) := by
  intro y
  induction y using QuotientAddGroup.induction_on with
  | H z =>
  obtain ⟨c, hc⟩ := z
  obtain ⟨b, rfl⟩ := hp c
  have hb : b ∈ connDomain fB i :=
    AddSubgroup.mem_comap.2 (AddMonoidHom.mem_range.2 ((hex _).1 (by rw [hfp]; exact AddMonoidHom.mem_ker.1 hc)))
  exact ⟨⟨b, hb⟩, rfl⟩
theorem ker_connLeft_le (hi : Function.Injective i) (hp : Function.Surjective p) (hex : Function.Exact i p) (hfi : ∀ a, i (fA a) = fB (i a)) (hgi : ∀ a, i (gA a) = gB (i a)) (hfp : ∀ b, p (fB b) = fC (p b))
    (hgp : ∀ b, p (gB b) = gC (p b)) (hfgB : ∀ b, fB (gB b) = 0) (hgfB : ∀ b, gB (fB b) = 0) :
    (connLeft hex hfp : connDomain fB i →+ KerModRange fC gC).ker ≤
      (connRight hi hgi hgfB : connDomain fB i →+ KerModRange gA fA).ker := by
  intro s hs; rw [AddMonoidHom.mem_ker, connLeft_apply, KerModRange.mk_eq_zero_iff] at hs; rw [AddMonoidHom.mem_ker, connRight_apply, KerModRange.mk_eq_zero_iff]
  obtain ⟨c, hc⟩ := AddMonoidHom.mem_range.1 hs
  obtain ⟨b', rfl⟩ := hp c
  obtain ⟨a, ha⟩ : (s : B) - gB b' ∈ Set.range i :=
    (hex _).1 (by rw [map_sub, hgp, hc]; exact sub_self _)
  refine AddMonoidHom.mem_range.2 ⟨a, hi ?_⟩
  rw [hfi, ha, apply_connInv, map_sub, hfgB, sub_zero]
noncomputable def connecting (hi : Function.Injective i) (hp : Function.Surjective p) (hex : Function.Exact i p) (hfi : ∀ a, i (fA a) = fB (i a)) (hgi : ∀ a, i (gA a) = gB (i a)) (hfp : ∀ b, p (fB b) = fC (p b))
    (hgp : ∀ b, p (gB b) = gC (p b)) (hfgB : ∀ b, fB (gB b) = 0) (hgfB : ∀ b, gB (fB b) = 0) :
    KerModRange fC gC →+ KerModRange gA fA :=
  (QuotientAddGroup.lift _ (connRight hi hgi hgfB : connDomain fB i →+ KerModRange gA fA) (ker_connLeft_le hi hp hex hfi hgi hfp hgp hfgB hgfB)).comp (QuotientAddGroup.quotientKerEquivOfSurjective _
      (connLeft_surjective hp hex hfp)).symm.toAddMonoidHom
theorem connecting_connLeft (hi : Function.Injective i) (hp : Function.Surjective p) (hex : Function.Exact i p) (hfi : ∀ a, i (fA a) = fB (i a)) (hgi : ∀ a, i (gA a) = gB (i a)) (hfp : ∀ b, p (fB b) = fC (p b))
    (hgp : ∀ b, p (gB b) = gC (p b)) (hfgB : ∀ b, fB (gB b) = 0) (hgfB : ∀ b, gB (fB b) = 0)
    (s : connDomain fB i) :
    connecting hi hp hex hfi hgi hfp hgp hfgB hgfB (connLeft hex hfp s) =
      (connRight hi hgi hgfB s : KerModRange gA fA) := by
  have : (QuotientAddGroup.quotientKerEquivOfSurjective _ (connLeft_surjective hp hex hfp)).symm (connLeft hex hfp s : KerModRange fC gC) = (QuotientAddGroup.mk s : connDomain fB i ⧸ (connLeft hex hfp :
        connDomain fB i →+ KerModRange fC gC).ker) :=
    (AddEquiv.symm_apply_eq _).2 rfl
  rw [connecting, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, this, QuotientAddGroup.lift_mk]
theorem ker_connecting (hi : Function.Injective i) (hp : Function.Surjective p) (hex : Function.Exact i p) (hfi : ∀ a, i (fA a) = fB (i a)) (hgi : ∀ a, i (gA a) = gB (i a)) (hfp : ∀ b, p (fB b) = fC (p b))
    (hgp : ∀ b, p (gB b) = gC (p b)) (hfgB : ∀ b, fB (gB b) = 0) (hgfB : ∀ b, gB (fB b) = 0) :
    (connecting hi hp hex hfi hgi hfp hgp hfgB hgfB).ker = (KerModRange.map p hfp hgp).range := by
  ext y
  constructor
  · intro hy
    obtain ⟨s, rfl⟩ := connLeft_surjective hp hex hfp y; rw [AddMonoidHom.mem_ker, connecting_connLeft, connRight_apply, KerModRange.mk_eq_zero_iff] at hy
    obtain ⟨a, ha⟩ := AddMonoidHom.mem_range.1 hy
    have hk : (s : B) - i a ∈ fB.ker := by rw [AddMonoidHom.mem_ker, map_sub, ← hfi, ha, apply_connInv, sub_self]
    refine ⟨QuotientAddGroup.mk ⟨_, hk⟩, ?_⟩
    rw [KerModRange.map_mk, connLeft_apply, KerModRange.mk_eq_mk_iff, kerMap_apply]
    have hpa : p (i a) = 0 := (hex _).2 ⟨a, rfl⟩; rw [map_sub, hpa, sub_zero, sub_self]; exact zero_mem _
  · rintro ⟨x, rfl⟩
    induction x using QuotientAddGroup.induction_on with
    | H z =>
    obtain ⟨b, hb⟩ := z
    have hb' : b ∈ connDomain fB i := by
      refine AddSubgroup.mem_comap.2 ?_
      rw [AddMonoidHom.mem_ker.1 hb]
      exact zero_mem _
    have h1 : KerModRange.map p hfp hgp (QuotientAddGroup.mk ⟨b, hb⟩ : KerModRange fB gB) =
        connLeft hex hfp ⟨b, hb'⟩ := rfl
    have h2 : connInv hi ⟨b, hb'⟩ = 0 :=
      hi (by rw [apply_connInv, map_zero]; exact AddMonoidHom.mem_ker.1 hb)
    rw [AddMonoidHom.mem_ker, h1, connecting_connLeft, connRight_apply, KerModRange.mk_eq_zero_iff]
    simp only [h2]
    exact zero_mem _
theorem range_connecting (hi : Function.Injective i) (hp : Function.Surjective p) (hex : Function.Exact i p) (hfi : ∀ a, i (fA a) = fB (i a)) (hgi : ∀ a, i (gA a) = gB (i a)) (hfp : ∀ b, p (fB b) = fC (p b))
    (hgp : ∀ b, p (gB b) = gC (p b)) (hfgB : ∀ b, fB (gB b) = 0) (hgfB : ∀ b, gB (fB b) = 0) :
    (connecting hi hp hex hfi hgi hfp hgp hfgB hgfB).range = (KerModRange.map i hgi hfi).ker := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨s, rfl⟩ := connLeft_surjective hp hex hfp y; rw [AddMonoidHom.mem_ker, connecting_connLeft, connRight_apply, KerModRange.map_mk, KerModRange.mk_eq_zero_iff, kerMap_apply, apply_connInv]
    exact AddMonoidHom.mem_range.2 ⟨s, rfl⟩
  · intro hx
    induction x using QuotientAddGroup.induction_on with
    | H z =>
    obtain ⟨a, ha⟩ := z; rw [AddMonoidHom.mem_ker, KerModRange.map_mk, KerModRange.mk_eq_zero_iff, kerMap_apply] at hx
    obtain ⟨b, hb⟩ := AddMonoidHom.mem_range.1 hx
    have hb' : b ∈ connDomain fB i := by
      refine AddSubgroup.mem_comap.2 ?_
      rw [hb]
      exact AddMonoidHom.mem_range.2 ⟨a, rfl⟩
    refine ⟨connLeft hex hfp ⟨b, hb'⟩, ?_⟩
    rw [connecting_connLeft, connRight_apply]
    have : connInv hi ⟨b, hb'⟩ = a := hi (by rw [apply_connInv]; exact hb); congr 1; exact Subtype.ext this
end Hexagon
section ShortExact
variable {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] {fA gA : A →+ A} {fB gB : B →+ B} {fC gC : C →+ C} {i : A →+ B} {p : B →+ C}
theorem natCard_kerModRange_hexagon (hi : Function.Injective i) (hp : Function.Surjective p) (hex : Function.Exact i p) (hfi : ∀ a, i (fA a) = fB (i a)) (hgi : ∀ a, i (gA a) = gB (i a)) (hfp : ∀ b, p (fB b) = fC (p b))
    (hgp : ∀ b, p (gB b) = gC (p b)) (hfgB : ∀ b, fB (gB b) = 0) (hgfB : ∀ b, gB (fB b) = 0) :
    Nat.card (KerModRange fA gA) * Nat.card (KerModRange fC gC) * Nat.card (KerModRange gB fB) = Nat.card (KerModRange fB gB) * Nat.card (KerModRange gA fA) *
        Nat.card (KerModRange gC fC) :=
  natCard_hexagon (KerModRange.map i hfi hgi) (KerModRange.map p hfp hgp) (connecting hi hp hex hfi hgi hfp hgp hfgB hgfB) (KerModRange.map i hgi hfi) (KerModRange.map p hgp hfp) (connecting hi hp hex hgi hfi hgp hfp hgfB hfgB)
    (range_connecting hi hp hex hgi hfi hgp hfp hgfB hfgB).symm
    (KerModRange.ker_map_eq_range_map hi hp hex hfi hgi hfp hgp hfgB)
    (ker_connecting hi hp hex hfi hgi hfp hgp hfgB hgfB)
    (range_connecting hi hp hex hfi hgi hfp hgp hfgB hgfB).symm
    (KerModRange.ker_map_eq_range_map hi hp hex hgi hfi hgp hfp hgfB)
    (ker_connecting hi hp hex hgi hfi hgp hfp hgfB hfgB)
theorem HasHerbrandQuotient.of_shortExact_left_right (hi : Function.Injective i) (hp : Function.Surjective p) (hex : Function.Exact i p) (hfi : ∀ a, i (fA a) = fB (i a)) (hgi : ∀ a, i (gA a) = gB (i a)) (hfp : ∀ b, p (fB b) = fC (p b))
    (hgp : ∀ b, p (gB b) = gC (p b)) (hfgB : ∀ b, fB (gB b) = 0) (hgfB : ∀ b, gB (fB b) = 0)
    (hA : HasHerbrandQuotient fA gA) (hC : HasHerbrandQuotient fC gC) :
    HasHerbrandQuotient fB gB := by
  have := hA.1; have := hA.2; have := hC.1; have := hC.2
  exact ⟨finite_of_exact (KerModRange.map i hfi hgi) (KerModRange.map p hfp hgp) (KerModRange.ker_map_eq_range_map hi hp hex hfi hgi hfp hgp hfgB), finite_of_exact (KerModRange.map i hgi hfi) (KerModRange.map p hgp hfp)
      (KerModRange.ker_map_eq_range_map hi hp hex hgi hfi hgp hfp hgfB)⟩
theorem HasHerbrandQuotient.of_shortExact_left_mid (hi : Function.Injective i) (hp : Function.Surjective p) (hex : Function.Exact i p) (hfi : ∀ a, i (fA a) = fB (i a)) (hgi : ∀ a, i (gA a) = gB (i a)) (hfp : ∀ b, p (fB b) = fC (p b))
    (hgp : ∀ b, p (gB b) = gC (p b)) (hfgB : ∀ b, fB (gB b) = 0) (hgfB : ∀ b, gB (fB b) = 0)
    (hA : HasHerbrandQuotient fA gA) (hB : HasHerbrandQuotient fB gB) :
    HasHerbrandQuotient fC gC := by
  have := hA.1; have := hA.2; have := hB.1; have := hB.2; exact ⟨finite_of_exact (KerModRange.map p hfp hgp) (connecting hi hp hex hfi hgi hfp hgp hfgB hgfB) (ker_connecting hi hp hex hfi hgi hfp hgp hfgB hgfB),
    finite_of_exact (KerModRange.map p hgp hfp) (connecting hi hp hex hgi hfi hgp hfp hgfB hfgB) (ker_connecting hi hp hex hgi hfi hgp hfp hgfB hfgB)⟩
theorem HasHerbrandQuotient.of_shortExact_mid_right (hi : Function.Injective i) (hp : Function.Surjective p) (hex : Function.Exact i p) (hfi : ∀ a, i (fA a) = fB (i a)) (hgi : ∀ a, i (gA a) = gB (i a)) (hfp : ∀ b, p (fB b) = fC (p b))
    (hgp : ∀ b, p (gB b) = gC (p b)) (hfgB : ∀ b, fB (gB b) = 0) (hgfB : ∀ b, gB (fB b) = 0)
    (hB : HasHerbrandQuotient fB gB) (hC : HasHerbrandQuotient fC gC) :
    HasHerbrandQuotient fA gA := by
  have := hB.1; have := hB.2; have := hC.1; have := hC.2; exact ⟨finite_of_exact (connecting hi hp hex hgi hfi hgp hfp hgfB hfgB) (KerModRange.map i hfi hgi) (range_connecting hi hp hex hgi hfi hgp hfp hgfB hfgB).symm,
    finite_of_exact (connecting hi hp hex hfi hgi hfp hgp hfgB hgfB) (KerModRange.map i hgi hfi) (range_connecting hi hp hex hfi hgi hfp hgp hfgB hgfB).symm⟩
theorem herbrandQuotient_eq_mul_of_shortExact (hi : Function.Injective i) (hp : Function.Surjective p) (hex : Function.Exact i p) (hfi : ∀ a, i (fA a) = fB (i a)) (hgi : ∀ a, i (gA a) = gB (i a)) (hfp : ∀ b, p (fB b) = fC (p b))
    (hgp : ∀ b, p (gB b) = gC (p b)) (hfgB : ∀ b, fB (gB b) = 0) (hgfB : ∀ b, gB (fB b) = 0)
    (hA : HasHerbrandQuotient fA gA) (hC : HasHerbrandQuotient fC gC) :
    herbrandQuotient fB gB = herbrandQuotient fA gA * herbrandQuotient fC gC := by
  have hB := HasHerbrandQuotient.of_shortExact_left_right hi hp hex hfi hgi hfp hgp hfgB hgfB hA hC
  have h := natCard_kerModRange_hexagon hi hp hex hfi hgi hfp hgp hfgB hgfB
  have := hA.2; have := hB.2; have := hC.2
  have h4 : (Nat.card (KerModRange gA fA) : ℚ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  have h5 : (Nat.card (KerModRange gB fB) : ℚ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  have h6 : (Nat.card (KerModRange gC fC) : ℚ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  have h' : (Nat.card (KerModRange fA gA) : ℚ) * Nat.card (KerModRange fC gC) * Nat.card (KerModRange gB fB) = (Nat.card (KerModRange fB gB) : ℚ) *
        Nat.card (KerModRange gA fA) * Nat.card (KerModRange gC fC) := by
    exact_mod_cast h
  rw [herbrandQuotient, herbrandQuotient, herbrandQuotient, div_mul_div_comm, div_eq_div_iff h5 (mul_ne_zero h4 h6)]
  linear_combination -h'
theorem hasHerbrandQuotient_iff_of_shortExact_of_finite [Finite C] (hi : Function.Injective i) (hp : Function.Surjective p) (hex : Function.Exact i p) (hfi : ∀ a, i (fA a) = fB (i a))
    (hgi : ∀ a, i (gA a) = gB (i a)) (hfp : ∀ b, p (fB b) = fC (p b))
    (hgp : ∀ b, p (gB b) = gC (p b)) (hfgB : ∀ b, fB (gB b) = 0) (hgfB : ∀ b, gB (fB b) = 0) :
    HasHerbrandQuotient fA gA ↔ HasHerbrandQuotient fB gB :=
  ⟨fun hA => HasHerbrandQuotient.of_shortExact_left_right hi hp hex hfi hgi hfp hgp hfgB hgfB hA (hasHerbrandQuotient_of_finite _ _), fun hB => HasHerbrandQuotient.of_shortExact_mid_right hi hp hex hfi hgi hfp hgp hfgB hgfB hB
      (hasHerbrandQuotient_of_finite _ _)⟩
theorem herbrandQuotient_eq_of_shortExact_of_finite [Finite C] (hi : Function.Injective i) (hp : Function.Surjective p) (hex : Function.Exact i p) (hfi : ∀ a, i (fA a) = fB (i a))
    (hgi : ∀ a, i (gA a) = gB (i a)) (hfp : ∀ b, p (fB b) = fC (p b))
    (hgp : ∀ b, p (gB b) = gC (p b)) (hfgB : ∀ b, fB (gB b) = 0) (hgfB : ∀ b, gB (fB b) = 0) :
    herbrandQuotient fA gA = herbrandQuotient fB gB := by
  have hfgC : ∀ c, fC (gC c) = 0 := by
    intro c
    obtain ⟨b, rfl⟩ := hp c; rw [← hgp, ← hfp, hfgB, map_zero]
  have hgfC : ∀ c, gC (fC c) = 0 := by
    intro c
    obtain ⟨b, rfl⟩ := hp c; rw [← hfp, ← hgp, hgfB, map_zero]
  have h := natCard_kerModRange_hexagon hi hp hex hfi hgi hfp hgp hfgB hgfB; rw [natCard_kerModRange_eq_of_finite hfgC hgfC] at h
  have h3 : 0 < Nat.card (KerModRange gC fC) := Nat.card_pos
  have h15 : Nat.card (KerModRange fA gA) * Nat.card (KerModRange gB fB) =
      Nat.card (KerModRange fB gB) * Nat.card (KerModRange gA fA) := by
    apply Nat.eq_of_mul_eq_mul_right h3
    calc _ = Nat.card (KerModRange fA gA) * Nat.card (KerModRange gC fC) *
          Nat.card (KerModRange gB fB) := by ring
      _ = _ := h
  by_cases h4 : Finite (KerModRange gA fA)
  · have h5 : Finite (KerModRange gB fB) :=
      finite_of_exact (KerModRange.map i hgi hfi) (KerModRange.map p hgp hfp) (KerModRange.ker_map_eq_range_map hi hp hex hgi hfi hgp hfp hgfB)
    have h4' : (Nat.card (KerModRange gA fA) : ℚ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
    have h5' : (Nat.card (KerModRange gB fB) : ℚ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
    rw [herbrandQuotient, herbrandQuotient, div_eq_div_iff h4' h5']
    exact_mod_cast h15
  · have h5 : ¬ Finite (KerModRange gB fB) := fun h5 =>
      h4 (finite_of_exact (connecting hi hp hex hfi hgi hfp hgp hfgB hgfB) (KerModRange.map i hgi hfi) (range_connecting hi hp hex hfi hgi hfp hgp hfgB hgfB).symm)
    rw [not_finite_iff_infinite] at h4 h5
    rw [herbrandQuotient, herbrandQuotient, Nat.card_eq_zero_of_infinite (α := KerModRange gA fA),
      Nat.card_eq_zero_of_infinite (α := KerModRange gB fB)]
    simp
end ShortExact
section FiniteIndex
variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]
theorem hasHerbrandQuotient_iff_of_injective_of_finite {fA gA : A →+ A} {fB gB : B →+ B} {i : A →+ B} (hi : Function.Injective i) [Finite (B ⧸ i.range)] (hfi : ∀ a, i (fA a) = fB (i a)) (hgi : ∀ a, i (gA a) = gB (i a))
    (hfgB : ∀ b, fB (gB b) = 0) (hgfB : ∀ b, gB (fB b) = 0) :
    HasHerbrandQuotient fA gA ↔ HasHerbrandQuotient fB gB := by
  have hf : i.range ≤ i.range.comap fB := by rintro _ ⟨a, rfl⟩; exact AddSubgroup.mem_comap.2 (AddMonoidHom.mem_range.2 ⟨fA a, hfi a⟩)
  have hg : i.range ≤ i.range.comap gB := by rintro _ ⟨a, rfl⟩; exact AddSubgroup.mem_comap.2 (AddMonoidHom.mem_range.2 ⟨gA a, hgi a⟩)
  refine hasHerbrandQuotient_iff_of_shortExact_of_finite (p := QuotientAddGroup.mk' i.range)
    (fC := QuotientAddGroup.map _ _ fB hf) (gC := QuotientAddGroup.map _ _ gB hg) hi
    (QuotientAddGroup.mk'_surjective _) ?_ hfi hgi (fun _ => rfl) (fun _ => rfl) hfgB hgfB
  intro b; rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff, AddMonoidHom.mem_range, Set.mem_range]
theorem herbrandQuotient_eq_of_injective_of_finite {fA gA : A →+ A} {fB gB : B →+ B} {i : A →+ B} (hi : Function.Injective i) [Finite (B ⧸ i.range)] (hfi : ∀ a, i (fA a) = fB (i a)) (hgi : ∀ a, i (gA a) = gB (i a))
    (hfgB : ∀ b, fB (gB b) = 0) (hgfB : ∀ b, gB (fB b) = 0) :
    herbrandQuotient fA gA = herbrandQuotient fB gB := by
  have hf : i.range ≤ i.range.comap fB := by rintro _ ⟨a, rfl⟩; exact AddSubgroup.mem_comap.2 (AddMonoidHom.mem_range.2 ⟨fA a, hfi a⟩)
  have hg : i.range ≤ i.range.comap gB := by rintro _ ⟨a, rfl⟩; exact AddSubgroup.mem_comap.2 (AddMonoidHom.mem_range.2 ⟨gA a, hgi a⟩)
  refine herbrandQuotient_eq_of_shortExact_of_finite (p := QuotientAddGroup.mk' i.range)
    (fC := QuotientAddGroup.map _ _ fB hf) (gC := QuotientAddGroup.map _ _ gB hg) hi
    (QuotientAddGroup.mk'_surjective _) ?_ hfi hgi (fun _ => rfl) (fun _ => rfl) hfgB hgfB
  intro b; rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff, AddMonoidHom.mem_range, Set.mem_range]
def restrictEnd (f : B →+ B) (S : AddSubgroup B) (hS : ∀ x ∈ S, f x ∈ S) : S →+ S :=
  (f.comp S.subtype).codRestrict S fun x => hS x x.2
@[simp]
theorem restrictEnd_apply (f : B →+ B) (S : AddSubgroup B) (hS : ∀ x ∈ S, f x ∈ S) (x : S) : (restrictEnd f S hS x : B) = f x :=
  rfl
theorem hasHerbrandQuotient_restrictEnd_iff {f g : B →+ B} (S : AddSubgroup B) [S.FiniteIndex] (hfS : ∀ x ∈ S, f x ∈ S) (hgS : ∀ x ∈ S, g x ∈ S) (hfg : ∀ b, f (g b) = 0) (hgf : ∀ b, g (f b) = 0) :
    HasHerbrandQuotient (restrictEnd f S hfS) (restrictEnd g S hgS) ↔ HasHerbrandQuotient f g := by
  have : Finite (B ⧸ S.subtype.range) := by rw [AddSubgroup.range_subtype]; infer_instance
  exact hasHerbrandQuotient_iff_of_injective_of_finite S.subtype_injective (fun _ => rfl) (fun _ => rfl) hfg hgf
theorem herbrandQuotient_restrictEnd {f g : B →+ B} (S : AddSubgroup B) [S.FiniteIndex] (hfS : ∀ x ∈ S, f x ∈ S) (hgS : ∀ x ∈ S, g x ∈ S) (hfg : ∀ b, f (g b) = 0) (hgf : ∀ b, g (f b) = 0) :
    herbrandQuotient (restrictEnd f S hfS) (restrictEnd g S hgS) = herbrandQuotient f g := by
  have : Finite (B ⧸ S.subtype.range) := by rw [AddSubgroup.range_subtype]; infer_instance
  exact herbrandQuotient_eq_of_injective_of_finite S.subtype_injective (fun _ => rfl) (fun _ => rfl) hfg hgf
end FiniteIndex
end Sec_HerbrandAbstract


/-! ### CycTate -/
section Sec_CycTate
open RHDirect.Stage13CFT_IdeleNormResidue
section KerModRange
variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]
noncomputable def kerModRangeEquivOfSurjective {f g : A →+ A} (φ : f.ker →+ B) (hs : Function.Surjective φ) (hk : ∀ a : f.ker, φ a = 0 ↔ (a : A) ∈ g.range) :
    KerModRange f g ≃+ B :=
  (QuotientAddGroup.quotientAddEquivOfEq (by
      ext a
      rw [AddMonoidHom.mem_ker, hk, AddSubgroup.mem_addSubgroupOf])).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective φ hs)
theorem kerModRangeEquivOfSurjective_mk {f g : A →+ A} (φ : f.ker →+ B) (hs : Function.Surjective φ) (hk : ∀ a : f.ker, φ a = 0 ↔ (a : A) ∈ g.range) (a : f.ker) :
    kerModRangeEquivOfSurjective φ hs hk (QuotientAddGroup.mk a : KerModRange f g) = φ a :=
  rfl
theorem addEquiv_symm_apply_comm {f : A →+ A} {f' : B →+ B} (e : A ≃+ B) (hf : ∀ a, e (f a) = f' (e a)) (b : B) :
    e.symm.toAddMonoidHom (f' b) = f (e.symm.toAddMonoidHom b) := by
  apply e.injective
  simp only [AddEquiv.coe_toAddMonoidHom, AddEquiv.apply_symm_apply, hf]
noncomputable def kerModRangeCongr {fA gA : A →+ A} {fB gB : B →+ B} (e : A ≃+ B) (hf : ∀ a, e (fA a) = fB (e a)) (hg : ∀ a, e (gA a) = gB (e a)) : KerModRange fA gA ≃+ KerModRange fB gB where
  toFun := KerModRange.map e.toAddMonoidHom hf hg
  invFun := KerModRange.map e.symm.toAddMonoidHom (addEquiv_symm_apply_comm e hf) (addEquiv_symm_apply_comm e hg)
  left_inv x := by
    induction x using QuotientAddGroup.induction_on with
    | H a => exact congrArg QuotientAddGroup.mk (Subtype.ext (e.symm_apply_apply (a : A)))
  right_inv x := by
    induction x using QuotientAddGroup.induction_on with
    | H a => exact congrArg QuotientAddGroup.mk (Subtype.ext (e.apply_symm_apply (a : B)))
  map_add' := map_add _
theorem kerModRangeCongr_mk {fA gA : A →+ A} {fB gB : B →+ B} (e : A ≃+ B) (hf : ∀ a, e (fA a) = fB (e a)) (hg : ∀ a, e (gA a) = gB (e a)) (a : fA.ker) : kerModRangeCongr e hf hg (QuotientAddGroup.mk a : KerModRange fA gA) =
      QuotientAddGroup.mk (kerMap e.toAddMonoidHom hf a) :=
  rfl
noncomputable def kerModRangePiEquiv {ι : Type*} {A : ι → Type*} [∀ i, AddCommGroup (A i)] (F G : (∀ i, A i) →+ (∀ i, A i)) (f g : ∀ i, A i →+ A i) (hF : ∀ x i, F x i = f i (x i)) (hG : ∀ x i, G x i = g i (x i)) :
    KerModRange F G ≃+ ∀ i, KerModRange (f i) (g i) :=
  kerModRangeEquivOfSurjective (AddMonoidHom.pi fun i => (QuotientAddGroup.mk' _).comp (((Pi.evalAddMonoidHom A i).comp F.ker.subtype).codRestrict (f i).ker fun x => by
        simp only [AddMonoidHom.comp_apply, AddSubgroup.coe_subtype, Pi.evalAddMonoidHom_apply, AddMonoidHom.mem_ker, ← hF, AddMonoidHom.mem_ker.1 x.2, Pi.zero_apply]))
    (by
      intro y
      choose z hz using fun i => QuotientAddGroup.mk_surjective (y i)
      refine ⟨⟨fun i => z i, AddMonoidHom.mem_ker.2 (funext fun i => ?_)⟩, funext fun i => ?_⟩
      · rw [hF, AddMonoidHom.mem_ker.1 (z i).2, Pi.zero_apply]
      · rw [← hz i]
        rfl)
    (by
      intro x; constructor
      · intro h
        have h' : ∀ i, (x : ∀ i, A i) i ∈ (g i).range := fun i => by
          have := congrFun h i; rw [Pi.zero_apply] at this; exact (KerModRange.mk_eq_zero_iff _).1 this
        choose y hy using fun i => AddMonoidHom.mem_range.1 (h' i)
        exact AddMonoidHom.mem_range.2 ⟨y, funext fun i => by rw [hG, hy]⟩
      · intro h
        obtain ⟨y, hy⟩ := AddMonoidHom.mem_range.1 h; funext i; rw [Pi.zero_apply]; refine (KerModRange.mk_eq_zero_iff _).2 (AddMonoidHom.mem_range.2 ⟨y i, ?_⟩); show g i (y i) = (x : ∀ i, A i) i; rw [← hG, hy])
theorem kerModRangePiEquiv_mk {ι : Type*} {A : ι → Type*} [∀ i, AddCommGroup (A i)] (F G : (∀ i, A i) →+ (∀ i, A i)) (f g : ∀ i, A i →+ A i) (hF : ∀ x i, F x i = f i (x i)) (hG : ∀ x i, G x i = g i (x i)) (x : F.ker) (i : ι) :
    kerModRangePiEquiv F G f g hF hG (QuotientAddGroup.mk x : KerModRange F G) i = QuotientAddGroup.mk (⟨(x : ∀ i, A i) i, by
        rw [AddMonoidHom.mem_ker, ← hF, AddMonoidHom.mem_ker.1 x.2, Pi.zero_apply]⟩ : (f i).ker) :=
  rfl
end KerModRange
section Defs
variable {k G V : Type*} [CommRing k] [Group G] [AddCommGroup V] [Module k V]
def cycSubOne (ρ : Representation k G V) (σ : G) : V →+ V :=
  (ρ σ - 1 : Module.End k V).toAddMonoidHom
theorem cycSubOne_apply (ρ : Representation k G V) (σ : G) (x : V) : cycSubOne ρ σ x = ρ σ x - x :=
  rfl
theorem apply_eq_self_of_generator (ρ : Representation k G V) {σ : G}
    (hσ : ∀ g, g ∈ Subgroup.zpowers σ) {x : V} (hx : ρ σ x = x) (g : G) : ρ g x = x := by
  have := hσ g; rw [Subgroup.zpowers_eq_closure] at this
  induction this using Subgroup.closure_induction with
  | mem y hy => rw [Set.mem_singleton_iff.1 hy, hx]
  | one => simp
  | mul a b _ _ ha hb => rw [map_mul, Module.End.mul_apply, hb, ha]
  | inv a _ ha =>
    conv_lhs => rw [← ha]
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
theorem mem_ker_cycSubOne_iff (ρ : Representation k G V) {σ : G} (hσ : ∀ g, g ∈ Subgroup.zpowers σ) (x : V) :
    x ∈ (cycSubOne ρ σ).ker ↔ ∀ g, ρ g x = x := by
  rw [AddMonoidHom.mem_ker, cycSubOne_apply, sub_eq_zero]
  exact ⟨fun h => apply_eq_self_of_generator ρ hσ h, fun h => h σ⟩
theorem apply_sub_self_mem_range_cycSubOne (ρ : Representation k G V) {σ : G} (hσ : ∀ g, g ∈ Subgroup.zpowers σ) (g : G) (x : V) :
    ρ g x - x ∈ (cycSubOne ρ σ).range := by
  have := hσ g; rw [Subgroup.zpowers_eq_closure] at this
  induction this using Subgroup.closure_induction generalizing x with
  | mem y hy =>
    rw [Set.mem_singleton_iff.1 hy]
    exact ⟨x, rfl⟩
  | one => simp
  | mul a b _ _ ha hb =>
    have : ρ (a * b) x - x = (ρ a (ρ b x) - ρ b x) + (ρ b x - x) := by rw [map_mul, Module.End.mul_apply]; abel
    rw [this]
    exact add_mem (ha _) (hb _)
  | inv a _ ha =>
    have : ρ a⁻¹ x - x = -(ρ a (ρ a⁻¹ x) - ρ a⁻¹ x) := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
      abel
    rw [this]
    exact neg_mem (ha _)
theorem range_cycSubOne_eq_closure (ρ : Representation k G V) {σ : G} (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    (cycSubOne ρ σ).range = AddSubgroup.closure {y | ∃ g x, ρ g x - x = y} := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    exact AddSubgroup.subset_closure ⟨σ, x, rfl⟩
  · rw [AddSubgroup.closure_le]
    rintro _ ⟨g, x, rfl⟩; exact apply_sub_self_mem_range_cycSubOne ρ hσ g x
variable [Fintype G]
def cycNorm (ρ : Representation k G V) : V →+ V :=
  ρ.norm.toAddMonoidHom
theorem cycNorm_apply (ρ : Representation k G V) (x : V) : cycNorm ρ x = ∑ g : G, ρ g x := by simp [cycNorm, Representation.norm, LinearMap.sum_apply]
theorem cycSubOne_cycNorm (ρ : Representation k G V) (σ : G) (x : V) : cycSubOne ρ σ (cycNorm ρ x) = 0 := by
  rw [cycSubOne_apply, sub_eq_zero]
  exact ρ.self_norm_apply σ x
theorem cycNorm_cycSubOne (ρ : Representation k G V) (σ : G) (x : V) : cycNorm ρ (cycSubOne ρ σ x) = 0 := by
  rw [cycSubOne_apply, map_sub, sub_eq_zero]
  exact ρ.norm_self_apply σ x
abbrev CycTateZero (ρ : Representation k G V) (σ : G) : Type _ :=
  KerModRange (cycSubOne ρ σ) (cycNorm ρ)
abbrev CycTateNegOne (ρ : Representation k G V) (σ : G) : Type _ :=
  KerModRange (cycNorm ρ) (cycSubOne ρ σ)
noncomputable def cycHerbrand (ρ : Representation k G V) (σ : G) : ℚ :=
  herbrandQuotient (cycSubOne ρ σ) (cycNorm ρ)
theorem cycHerbrand_eq (ρ : Representation k G V) (σ : G) : cycHerbrand ρ σ = (Nat.card (CycTateZero ρ σ) : ℚ) / Nat.card (CycTateNegOne ρ σ) :=
  rfl
end Defs
section Congr
variable {k G V W : Type*} [CommRing k] [Group G] [Fintype G] [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
noncomputable def cycTateZeroCongr {ρ : Representation k G V} {ρ' : Representation k G W} (e : V ≃+ W) (he : ∀ g v, e (ρ g v) = ρ' g (e v)) (σ : G) :
    CycTateZero ρ σ ≃+ CycTateZero ρ' σ :=
  kerModRangeCongr e (fun v => by simp [cycSubOne_apply, he]) (fun v => by simp [cycNorm_apply, map_sum, he])
noncomputable def cycTateNegOneCongr {ρ : Representation k G V} {ρ' : Representation k G W} (e : V ≃+ W) (he : ∀ g v, e (ρ g v) = ρ' g (e v)) (σ : G) :
    CycTateNegOne ρ σ ≃+ CycTateNegOne ρ' σ :=
  kerModRangeCongr e (fun v => by simp [cycNorm_apply, map_sum, he]) (fun v => by simp [cycSubOne_apply, he])
theorem cycHerbrand_congr {ρ : Representation k G V} {ρ' : Representation k G W} (e : V ≃+ W) (he : ∀ g v, e (ρ g v) = ρ' g (e v)) (σ : G) :
    cycHerbrand ρ σ = cycHerbrand ρ' σ := by
  rw [cycHerbrand_eq, cycHerbrand_eq, Nat.card_congr (cycTateZeroCongr e he σ).toEquiv, Nat.card_congr (cycTateNegOneCongr e he σ).toEquiv]
end Congr
section Pi
variable {k G ι : Type*} [CommRing k] [Group G] {V : ι → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
def piRep (ρ : ∀ i, Representation k G (V i)) : Representation k G (∀ i, V i) where
  toFun g := LinearMap.pi fun i => (ρ i g).comp (LinearMap.proj i)
  map_one' := by ext; simp
  map_mul' g h := by ext; simp
@[simp]
theorem piRep_apply (ρ : ∀ i, Representation k G (V i)) (g : G) (x : ∀ i, V i) (i : ι) : piRep ρ g x i = ρ i g (x i) :=
  rfl
theorem cycSubOne_piRep_apply (ρ : ∀ i, Representation k G (V i)) (σ : G) (x : ∀ i, V i) (i : ι) : cycSubOne (piRep ρ) σ x i = cycSubOne (ρ i) σ (x i) :=
  rfl
variable [Fintype G]
theorem cycNorm_piRep_apply (ρ : ∀ i, Representation k G (V i)) (x : ∀ i, V i) (i : ι) : cycNorm (piRep ρ) x i = cycNorm (ρ i) (x i) := by
  rw [cycNorm_apply, cycNorm_apply, Finset.sum_apply]
  rfl
noncomputable def cycTateZeroPiEquiv (ρ : ∀ i, Representation k G (V i)) (σ : G) : CycTateZero (piRep ρ) σ ≃+ ∀ i, CycTateZero (ρ i) σ :=
  kerModRangePiEquiv _ _ _ _ (cycSubOne_piRep_apply ρ σ) (cycNorm_piRep_apply ρ)
noncomputable def cycTateNegOnePiEquiv (ρ : ∀ i, Representation k G (V i)) (σ : G) : CycTateNegOne (piRep ρ) σ ≃+ ∀ i, CycTateNegOne (ρ i) σ :=
  kerModRangePiEquiv _ _ _ _ (cycNorm_piRep_apply ρ) (cycSubOne_piRep_apply ρ σ)
theorem cycHerbrand_pi [Fintype ι] (ρ : ∀ i, Representation k G (V i)) (σ : G) : cycHerbrand (piRep ρ) σ = ∏ i, cycHerbrand (ρ i) σ := by
  simp only [cycHerbrand_eq]
  rw [Nat.card_congr (cycTateZeroPiEquiv ρ σ).toEquiv, Nat.card_congr (cycTateNegOnePiEquiv ρ σ).toEquiv, Nat.card_pi, Nat.card_pi, Nat.cast_prod, Nat.cast_prod, Finset.prod_div_distrib]
end Pi
end Sec_CycTate


/-! ### CycTateNegOneOrbitEquivSymmMk -/
section Sec_CycTateNegOneOrbitEquivSymmMk
open RHDirect.Stage13CFT_IdeleNormResidue
section Orbit
variable {k G X : Type*} [CommRing k] [Group G] [MulAction G X] {M : X → Type*} [∀ x, AddCommGroup (M x)] [∀ x, Module k (M x)]
def PermutesFactors (ρ : Representation k G (∀ x, M x)) : Prop :=
  ∀ (g : G) (f : ∀ x, M x) (x : X), f x = 0 → ρ g f (g • x) = 0
theorem PermutesFactors.apply_eq {ρ : Representation k G (∀ x, M x)} (hρ : PermutesFactors ρ)
    (g : G) {f f' : ∀ x, M x} {x : X} (h : f x = f' x) : ρ g f (g • x) = ρ g f' (g • x) := by
  have := hρ g (f - f') x (by rw [Pi.sub_apply, h, sub_self]); rwa [map_sub, Pi.sub_apply, sub_eq_zero] at this
theorem PermutesFactors.apply_single_of_ne [DecidableEq X] {ρ : Representation k G (∀ x, M x)} (hρ : PermutesFactors ρ) (g : G) (x : X) (a : M x) {y : X} (hy : y ≠ g • x) :
    ρ g (Pi.single x a) y = 0 := by
  rw [← smul_inv_smul g y]
  refine hρ g _ _ (Pi.single_eq_of_ne ?_ a)
  intro h; exact hy (by rw [← h, smul_inv_smul])
theorem PermutesFactors.single_eq [DecidableEq X] {ρ : Representation k G (∀ x, M x)} (hρ : PermutesFactors ρ) (x₀ : X) (g : G) (f : ∀ x, M x) :
    Pi.single (g • x₀) (f (g • x₀)) = ρ g (Pi.single x₀ (ρ g⁻¹ f x₀)) := by
  funext z
  by_cases hz : z = g • x₀
  · subst hz
    rw [Pi.single_eq_same, hρ.apply_eq g (f' := ρ g⁻¹ f) (Pi.single_eq_same _ _), Representation.self_inv_apply]
  · rw [Pi.single_eq_of_ne hz, hρ.apply_single_of_ne _ _ _ hz]
theorem PermutesFactors.eq_zero_of_invariant [MulAction.IsPretransitive G X] {ρ : Representation k G (∀ x, M x)} (hρ : PermutesFactors ρ) {f : ∀ x, M x}
    (hf : ∀ g, ρ g f = f) (x₀ : X) (h0 : f x₀ = 0) : f = 0 := by
  funext y
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq G x₀ y; rw [← hf g, Pi.zero_apply]; exact hρ g f x₀ h0
variable [MulAction.IsPretransitive G X]
variable (G) in
noncomputable def orbitRep (x₀ y : X) : G :=
  (MulAction.exists_smul_eq G x₀ y).choose
theorem orbitRep_smul (x₀ y : X) : orbitRep G x₀ y • x₀ = y :=
  (MulAction.exists_smul_eq G x₀ y).choose_spec
variable (G) in
theorem finite_of_isPretransitive [Finite G] (x₀ : X) : Finite X :=
  Finite.of_surjective (fun g : G => g • x₀) fun y => MulAction.exists_smul_eq G x₀ y
noncomputable def stabProdEquiv (x₀ : X) (D : Subgroup G) (hD : ∀ g, g ∈ D ↔ g • x₀ = x₀) : D × X ≃ G where
  toFun p := (p.1 : G) * (orbitRep G x₀ p.2)⁻¹
  invFun g := (⟨g * orbitRep G x₀ (g⁻¹ • x₀), (hD _).2 (by
    rw [mul_smul, orbitRep_smul, smul_inv_smul])⟩, g⁻¹ • x₀)
  left_inv p := by
    obtain ⟨d, y⟩ := p
    have hd : (d : G)⁻¹ • x₀ = x₀ := (hD _).1 (inv_mem d.2)
    have hy : ((d : G) * (orbitRep G x₀ y)⁻¹)⁻¹ • x₀ = y := by rw [mul_inv_rev, inv_inv, mul_smul, hd, orbitRep_smul]
    refine Prod.ext (Subtype.ext ?_) hy
    show (d : G) * (orbitRep G x₀ y)⁻¹ * orbitRep G x₀ (((d : G) * (orbitRep G x₀ y)⁻¹)⁻¹ • x₀) = d
    rw [hy, inv_mul_cancel_right]
  right_inv g := mul_inv_cancel_right g _
noncomputable def orbitCores [Fintype X] (ρ : Representation k G (∀ x, M x)) (x₀ : X) : (∀ x, M x) →+ M x₀ where
  toFun f := ∑ y, ρ (orbitRep G x₀ y)⁻¹ f x₀
  map_zero' := by simp
  map_add' f f' := by simp [Finset.sum_add_distrib]
theorem orbitCores_apply [Fintype X] (ρ : Representation k G (∀ x, M x)) (x₀ : X) (f : ∀ x, M x) : orbitCores ρ x₀ f = ∑ y, ρ (orbitRep G x₀ y)⁻¹ f x₀ :=
  rfl
theorem cycNorm_apply_base [Fintype G] [Fintype X] (ρ : Representation k G (∀ x, M x)) (x₀ : X) (D : Subgroup G) [Fintype D] (hD : ∀ g, g ∈ D ↔ g • x₀ = x₀) (ρ₀ : Representation k D (M x₀))
    (hρ₀ : ∀ (d : D) (f : ∀ x, M x), ρ d f x₀ = ρ₀ d (f x₀)) (f : ∀ x, M x) :
    cycNorm ρ f x₀ = cycNorm ρ₀ (orbitCores ρ x₀ f) := by
  rw [cycNorm_apply, cycNorm_apply, Finset.sum_apply, orbitCores_apply]
  rw [show (∑ g : G, ρ g f x₀) = ∑ p : D × X, ρ ((p.1 : G) * (orbitRep G x₀ p.2)⁻¹) f x₀ from (Fintype.sum_equiv (stabProdEquiv x₀ D hD) (fun p => ρ ((p.1 : G) * (orbitRep G x₀ p.2)⁻¹) f x₀) (fun g => ρ g f x₀) fun p => rfl).symm]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [map_mul, Module.End.mul_apply, hρ₀]
omit [MulAction.IsPretransitive G X] in
theorem apply_single_base [DecidableEq X] {ρ : Representation k G (∀ x, M x)} (hρ : PermutesFactors ρ) {x₀ : X} {D : Subgroup G} (hD : ∀ g, g ∈ D ↔ g • x₀ = x₀)
    {ρ₀ : Representation k D (M x₀)} (hρ₀ : ∀ (d : D) (f : ∀ x, M x), ρ d f x₀ = ρ₀ d (f x₀))
    (d : D) (b : M x₀) : ρ d (Pi.single x₀ b) = Pi.single x₀ (ρ₀ d b) := by
  funext y
  by_cases hy : y = x₀
  · subst hy
    rw [hρ₀, Pi.single_eq_same, Pi.single_eq_same]
  · rw [Pi.single_eq_of_ne hy, hρ.apply_single_of_ne]
    rw [(hD d).1 d.2]
    exact hy
omit [MulAction.IsPretransitive G X] in
theorem apply_single_eq_of_smul_eq [DecidableEq X] {ρ : Representation k G (∀ x, M x)} (hρ : PermutesFactors ρ) {x₀ : X} {D : Subgroup G} (hD : ∀ g, g ∈ D ↔ g • x₀ = x₀)
    {ρ₀ : Representation k D (M x₀)} (hρ₀ : ∀ (d : D) (f : ∀ x, M x), ρ d f x₀ = ρ₀ d (f x₀))
    {b : M x₀} (hb : ∀ d : D, ρ₀ d b = b) {g g' : G} (h : g • x₀ = g' • x₀) :
    ρ g (Pi.single x₀ b) = ρ g' (Pi.single x₀ b) := by
  have hm : g'⁻¹ * g ∈ D := (hD _).2 (by rw [mul_smul, h, inv_smul_smul])
  have hg : g = g' * ((⟨g'⁻¹ * g, hm⟩ : D) : G) := by simp
  rw [hg, map_mul, Module.End.mul_apply, apply_single_base hρ hD hρ₀, hb]
theorem orbitCores_single [Fintype X] [DecidableEq X] {ρ : Representation k G (∀ x, M x)} (hρ : PermutesFactors ρ) {x₀ : X} {D : Subgroup G} (hD : ∀ g, g ∈ D ↔ g • x₀ = x₀)
    {ρ₀ : Representation k D (M x₀)} (hρ₀ : ∀ (d : D) (f : ∀ x, M x), ρ d f x₀ = ρ₀ d (f x₀))
    (b : M x₀) :
    orbitCores ρ x₀ (Pi.single x₀ b) =
      ρ₀ ⟨(orbitRep G x₀ x₀)⁻¹, (hD _).2 (by rw [inv_smul_eq_iff, orbitRep_smul])⟩ b := by
  rw [orbitCores_apply, Finset.sum_eq_single x₀]
  · exact (hρ₀ ⟨_, (hD _).2 (by rw [inv_smul_eq_iff, orbitRep_smul])⟩ _).trans (by rw [Pi.single_eq_same])
  · intro y _ hy
    apply hρ.apply_single_of_ne
    intro h; rw [eq_inv_smul_iff, orbitRep_smul] at h; exact hy h
  · intro h
    exact absurd (Finset.mem_univ _) h
theorem orbitCores_apply_sub_mem [Fintype X] {ρ : Representation k G (∀ x, M x)} {x₀ : X} {D : Subgroup G} [Fintype D] (hD : ∀ g, g ∈ D ↔ g • x₀ = x₀) {ρ₀ : Representation k D (M x₀)}
    (hρ₀ : ∀ (d : D) (f : ∀ x, M x), ρ d f x₀ = ρ₀ d (f x₀)) {τ : D}
    (hτ : ∀ d, d ∈ Subgroup.zpowers τ) (g : G) (h : ∀ x, M x) :
    orbitCores ρ x₀ (ρ g h) - orbitCores ρ x₀ h ∈ (cycSubOne ρ₀ τ).range := by
  have hmem : ∀ y, (orbitRep G x₀ y)⁻¹ * g * orbitRep G x₀ (g⁻¹ • y) ∈ D := fun y =>
    (hD _).2 (by rw [mul_smul, mul_smul, orbitRep_smul, smul_inv_smul, inv_smul_eq_iff, orbitRep_smul])
  have hterm : ∀ y, ρ (orbitRep G x₀ y)⁻¹ (ρ g h) x₀ =
      ρ₀ ⟨_, hmem y⟩ (ρ (orbitRep G x₀ (g⁻¹ • y))⁻¹ h x₀) := by
    intro y; rw [← hρ₀ ⟨_, hmem y⟩, ← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]; simp [mul_assoc]
  have e1 : orbitCores ρ x₀ (ρ g h) =
      ∑ y, ρ₀ ⟨_, hmem y⟩ (ρ (orbitRep G x₀ (g⁻¹ • y))⁻¹ h x₀) :=
    Finset.sum_congr rfl fun y _ => hterm y
  have e2 : orbitCores ρ x₀ h = ∑ y, ρ (orbitRep G x₀ (g⁻¹ • y))⁻¹ h x₀ :=
    (Fintype.sum_equiv (MulAction.toPerm g⁻¹) (fun y => ρ (orbitRep G x₀ (g⁻¹ • y))⁻¹ h x₀) (fun y => ρ (orbitRep G x₀ y)⁻¹ h x₀) fun y => rfl).symm
  rw [e1, e2, ← Finset.sum_sub_distrib]
  exact sum_mem fun y _ => apply_sub_self_mem_range_cycSubOne ρ₀ hτ _ _
omit [MulAction G X] [MulAction.IsPretransitive G X] in
theorem base_mem_ker_cycSubOne {ρ : Representation k G (∀ x, M x)} {x₀ : X} {D : Subgroup G} {ρ₀ : Representation k D (M x₀)} (hρ₀ : ∀ (d : D) (f : ∀ x, M x), ρ d f x₀ = ρ₀ d (f x₀))
    {σ : G} (hσ : ∀ g, g ∈ Subgroup.zpowers σ) (τ : D) (f : (cycSubOne ρ σ).ker) :
    (f : ∀ x, M x) x₀ ∈ (cycSubOne ρ₀ τ).ker := by
  rw [AddMonoidHom.mem_ker, cycSubOne_apply, ← hρ₀, (mem_ker_cycSubOne_iff ρ hσ _).1 f.2 τ, sub_self]
noncomputable def orbitZeroMap (ρ : Representation k G (∀ x, M x)) (x₀ : X) (D : Subgroup G) [Fintype D] (ρ₀ : Representation k D (M x₀)) (hρ₀ : ∀ (d : D) (f : ∀ x, M x), ρ d f x₀ = ρ₀ d (f x₀)) (σ : G)
    (hσ : ∀ g, g ∈ Subgroup.zpowers σ) (τ : D) :
    (cycSubOne ρ σ).ker →+ CycTateZero ρ₀ τ :=
  (QuotientAddGroup.mk' _).comp (((Pi.evalAddMonoidHom M x₀).comp (cycSubOne ρ σ).ker.subtype).codRestrict _ (base_mem_ker_cycSubOne hρ₀ hσ τ))
omit [MulAction G X] [MulAction.IsPretransitive G X] in
theorem orbitZeroMap_apply (ρ : Representation k G (∀ x, M x)) (x₀ : X) (D : Subgroup G) [Fintype D] (ρ₀ : Representation k D (M x₀)) (hρ₀ : ∀ (d : D) (f : ∀ x, M x), ρ d f x₀ = ρ₀ d (f x₀)) (σ : G)
    (hσ : ∀ g, g ∈ Subgroup.zpowers σ) (τ : D) (f : (cycSubOne ρ σ).ker) :
    orbitZeroMap ρ x₀ D ρ₀ hρ₀ σ hσ τ f =
      QuotientAddGroup.mk ⟨(f : ∀ x, M x) x₀, base_mem_ker_cycSubOne hρ₀ hσ τ f⟩ :=
  rfl
theorem orbitZeroMap_surjective [Fintype G] (ρ : Representation k G (∀ x, M x)) (hρ : PermutesFactors ρ) (x₀ : X) (D : Subgroup G) [Fintype D] (hD : ∀ g, g ∈ D ↔ g • x₀ = x₀) (ρ₀ : Representation k D (M x₀))
    (hρ₀ : ∀ (d : D) (f : ∀ x, M x), ρ d f x₀ = ρ₀ d (f x₀)) (σ : G)
    (hσ : ∀ g, g ∈ Subgroup.zpowers σ) (τ : D) (hτ : ∀ d, d ∈ Subgroup.zpowers τ) :
    Function.Surjective (orbitZeroMap ρ x₀ D ρ₀ hρ₀ σ hσ τ) := by
  classical
  have := finite_of_isPretransitive G x₀
  have := Fintype.ofFinite X; intro c
  induction c using QuotientAddGroup.induction_on with
  | H b =>
  obtain ⟨b, hb⟩ := b
  have hbD : ∀ d : D, ρ₀ d b = b := by
    rw [AddMonoidHom.mem_ker, cycSubOne_apply, sub_eq_zero] at hb
    exact apply_eq_self_of_generator ρ₀ hτ hb
  let F : ∀ x, M x := ∑ y, ρ (orbitRep G x₀ y) (Pi.single x₀ b)
  have hF : ∀ g, ρ g F = F := by
    intro g; rw [map_sum]
    refine (Finset.sum_congr rfl fun y _ => ?_).trans (Fintype.sum_equiv (MulAction.toPerm g) (fun y => ρ (orbitRep G x₀ (g • y)) (Pi.single x₀ b)) (fun y => ρ (orbitRep G x₀ y) (Pi.single x₀ b)) fun y => rfl)
    rw [← Module.End.mul_apply, ← map_mul]
    exact apply_single_eq_of_smul_eq hρ hD hρ₀ hbD (by rw [mul_smul, orbitRep_smul, orbitRep_smul])
  have hF0 : F x₀ = b := by
    simp only [F, Finset.sum_apply]
    rw [Finset.sum_eq_single x₀]
    · have hm : orbitRep G x₀ x₀ ∈ D := (hD _).2 (orbitRep_smul x₀ x₀)
      exact (hρ₀ ⟨_, hm⟩ _).trans (by rw [Pi.single_eq_same, hbD])
    · intro y _ hy
      apply hρ.apply_single_of_ne
      rw [orbitRep_smul]
      exact Ne.symm hy
    · intro h
      exact absurd (Finset.mem_univ _) h
  refine ⟨⟨F, ?_⟩, ?_⟩
  · rw [AddMonoidHom.mem_ker, cycSubOne_apply, hF, sub_self]
  · rw [orbitZeroMap_apply]
    exact congrArg QuotientAddGroup.mk (Subtype.ext hF0)
theorem orbitZeroMap_eq_zero_iff [Fintype G] (ρ : Representation k G (∀ x, M x)) (hρ : PermutesFactors ρ) (x₀ : X) (D : Subgroup G) [Fintype D] (hD : ∀ g, g ∈ D ↔ g • x₀ = x₀) (ρ₀ : Representation k D (M x₀))
    (hρ₀ : ∀ (d : D) (f : ∀ x, M x), ρ d f x₀ = ρ₀ d (f x₀)) (σ : G)
    (hσ : ∀ g, g ∈ Subgroup.zpowers σ) (τ : D) (f : (cycSubOne ρ σ).ker) :
    orbitZeroMap ρ x₀ D ρ₀ hρ₀ σ hσ τ f = 0 ↔ (f : ∀ x, M x) ∈ (cycNorm ρ).range := by
  classical
  have := finite_of_isPretransitive G x₀
  have := Fintype.ofFinite X
  have hf : ∀ g, ρ g f = f := (mem_ker_cycSubOne_iff ρ hσ _).1 f.2; rw [orbitZeroMap_apply, KerModRange.mk_eq_zero_iff]; constructor
  · rintro ⟨b, hb⟩
    refine ⟨Pi.single x₀ b, ?_⟩
    have h1 : ∀ g, ρ g (cycNorm ρ (Pi.single x₀ b)) = cycNorm ρ (Pi.single x₀ b) :=
      fun g => ρ.self_norm_apply g _
    have h2 : cycNorm ρ (Pi.single x₀ b) x₀ = (f : ∀ x, M x) x₀ := by
      rw [cycNorm_apply_base ρ x₀ D hD ρ₀ hρ₀, orbitCores_single hρ hD hρ₀]
      exact (ρ₀.norm_self_apply _ b).trans hb
    have := hρ.eq_zero_of_invariant (f := cycNorm ρ (Pi.single x₀ b) - f) (fun g => by rw [map_sub, h1, hf]) x₀ (by rw [Pi.sub_apply, h2, sub_self])
    exact sub_eq_zero.1 this
  · rintro ⟨h, hh⟩
    refine ⟨orbitCores ρ x₀ h, ?_⟩
    rw [← cycNorm_apply_base ρ x₀ D hD ρ₀ hρ₀, hh]
noncomputable def cycTateZeroOrbitEquiv [Fintype G] (ρ : Representation k G (∀ x, M x)) (hρ : PermutesFactors ρ) (x₀ : X) (D : Subgroup G) [Fintype D] (hD : ∀ g, g ∈ D ↔ g • x₀ = x₀) (ρ₀ : Representation k D (M x₀))
    (hρ₀ : ∀ (d : D) (f : ∀ x, M x), ρ d f x₀ = ρ₀ d (f x₀)) (σ : G)
    (hσ : ∀ g, g ∈ Subgroup.zpowers σ) (τ : D) (hτ : ∀ d, d ∈ Subgroup.zpowers τ) :
    CycTateZero ρ σ ≃+ CycTateZero ρ₀ τ :=
  kerModRangeEquivOfSurjective (orbitZeroMap ρ x₀ D ρ₀ hρ₀ σ hσ τ) (orbitZeroMap_surjective ρ hρ x₀ D hD ρ₀ hρ₀ σ hσ τ hτ) (orbitZeroMap_eq_zero_iff ρ hρ x₀ D hD ρ₀ hρ₀ σ hσ τ)
theorem cycTateZeroOrbitEquiv_mk [Fintype G] (ρ : Representation k G (∀ x, M x)) (hρ : PermutesFactors ρ) (x₀ : X) (D : Subgroup G) [Fintype D] (hD : ∀ g, g ∈ D ↔ g • x₀ = x₀) (ρ₀ : Representation k D (M x₀))
    (hρ₀ : ∀ (d : D) (f : ∀ x, M x), ρ d f x₀ = ρ₀ d (f x₀)) (σ : G)
    (hσ : ∀ g, g ∈ Subgroup.zpowers σ) (τ : D) (hτ : ∀ d, d ∈ Subgroup.zpowers τ)
    (f : (cycSubOne ρ σ).ker) :
    cycTateZeroOrbitEquiv ρ hρ x₀ D hD ρ₀ hρ₀ σ hσ τ hτ (QuotientAddGroup.mk f) =
      QuotientAddGroup.mk ⟨(f : ∀ x, M x) x₀, base_mem_ker_cycSubOne hρ₀ hσ τ f⟩ :=
  rfl
theorem orbitCores_mem_ker_cycNorm [Fintype G] [Fintype X] {ρ : Representation k G (∀ x, M x)} {x₀ : X} {D : Subgroup G} [Fintype D] (hD : ∀ g, g ∈ D ↔ g • x₀ = x₀)
    {ρ₀ : Representation k D (M x₀)} (hρ₀ : ∀ (d : D) (f : ∀ x, M x), ρ d f x₀ = ρ₀ d (f x₀))
    (f : (cycNorm ρ).ker) : orbitCores ρ x₀ f ∈ (cycNorm ρ₀).ker := by
  rw [AddMonoidHom.mem_ker, ← cycNorm_apply_base ρ x₀ D hD ρ₀ hρ₀, AddMonoidHom.mem_ker.1 f.2, Pi.zero_apply]
noncomputable def orbitNegOneMap [Fintype G] [Fintype X] (ρ : Representation k G (∀ x, M x)) (x₀ : X) (D : Subgroup G) [Fintype D] (hD : ∀ g, g ∈ D ↔ g • x₀ = x₀)
    (ρ₀ : Representation k D (M x₀)) (hρ₀ : ∀ (d : D) (f : ∀ x, M x), ρ d f x₀ = ρ₀ d (f x₀))
    (τ : D) : (cycNorm ρ).ker →+ CycTateNegOne ρ₀ τ :=
  (QuotientAddGroup.mk' _).comp (((orbitCores ρ x₀).comp (cycNorm ρ).ker.subtype).codRestrict _ (orbitCores_mem_ker_cycNorm hD hρ₀))
theorem orbitNegOneMap_apply [Fintype G] [Fintype X] (ρ : Representation k G (∀ x, M x)) (x₀ : X) (D : Subgroup G) [Fintype D] (hD : ∀ g, g ∈ D ↔ g • x₀ = x₀)
    (ρ₀ : Representation k D (M x₀)) (hρ₀ : ∀ (d : D) (f : ∀ x, M x), ρ d f x₀ = ρ₀ d (f x₀))
    (τ : D) (f : (cycNorm ρ).ker) :
    orbitNegOneMap ρ x₀ D hD ρ₀ hρ₀ τ f =
      QuotientAddGroup.mk ⟨orbitCores ρ x₀ f, orbitCores_mem_ker_cycNorm hD hρ₀ f⟩ :=
  rfl
theorem single_mem_ker_cycNorm [Fintype G] [DecidableEq X] {ρ : Representation k G (∀ x, M x)} (hρ : PermutesFactors ρ) {x₀ : X} {D : Subgroup G} [Fintype D] (hD : ∀ g, g ∈ D ↔ g • x₀ = x₀) {ρ₀ : Representation k D (M x₀)}
    (hρ₀ : ∀ (d : D) (f : ∀ x, M x), ρ d f x₀ = ρ₀ d (f x₀)) {b : M x₀}
    (hb : b ∈ (cycNorm ρ₀).ker) : Pi.single x₀ b ∈ (cycNorm ρ).ker := by
  have := finite_of_isPretransitive G x₀
  have := Fintype.ofFinite X; rw [AddMonoidHom.mem_ker]; refine hρ.eq_zero_of_invariant (fun g => ρ.self_norm_apply g _) x₀ ?_; rw [cycNorm_apply_base ρ x₀ D hD ρ₀ hρ₀, orbitCores_single hρ hD hρ₀]
  exact (ρ₀.norm_self_apply _ b).trans (AddMonoidHom.mem_ker.1 hb)
theorem orbitNegOneMap_surjective [Fintype G] [Fintype X] (ρ : Representation k G (∀ x, M x)) (hρ : PermutesFactors ρ) (x₀ : X) (D : Subgroup G) [Fintype D] (hD : ∀ g, g ∈ D ↔ g • x₀ = x₀) (ρ₀ : Representation k D (M x₀))
    (hρ₀ : ∀ (d : D) (f : ∀ x, M x), ρ d f x₀ = ρ₀ d (f x₀)) (τ : D)
    (hτ : ∀ d, d ∈ Subgroup.zpowers τ) :
    Function.Surjective (orbitNegOneMap ρ x₀ D hD ρ₀ hρ₀ τ) := by
  classical
  intro c
  induction c using QuotientAddGroup.induction_on with
  | H b =>
  obtain ⟨b, hb⟩ := b; refine ⟨⟨_, single_mem_ker_cycNorm hρ hD hρ₀ hb⟩, ?_⟩; rw [orbitNegOneMap_apply, KerModRange.mk_eq_mk_iff]; show orbitCores ρ x₀ (Pi.single x₀ b) - b ∈ _; rw [orbitCores_single hρ hD hρ₀]
  exact apply_sub_self_mem_range_cycSubOne ρ₀ hτ _ _
theorem orbitNegOneMap_eq_zero_iff [Fintype G] [Fintype X] (ρ : Representation k G (∀ x, M x)) (hρ : PermutesFactors ρ) (x₀ : X) (D : Subgroup G) [Fintype D] (hD : ∀ g, g ∈ D ↔ g • x₀ = x₀) (ρ₀ : Representation k D (M x₀))
    (hρ₀ : ∀ (d : D) (f : ∀ x, M x), ρ d f x₀ = ρ₀ d (f x₀)) (σ : G)
    (hσ : ∀ g, g ∈ Subgroup.zpowers σ) (τ : D) (hτ : ∀ d, d ∈ Subgroup.zpowers τ)
    (f : (cycNorm ρ).ker) :
    orbitNegOneMap ρ x₀ D hD ρ₀ hρ₀ τ f = 0 ↔ (f : ∀ x, M x) ∈ (cycSubOne ρ σ).range := by
  classical
  rw [orbitNegOneMap_apply, KerModRange.mk_eq_zero_iff]
  show orbitCores ρ x₀ f ∈ _ ↔ _
  constructor
  · rintro ⟨c, hc⟩
    have e1 : (f : ∀ x, M x) =
        ∑ y, ρ (orbitRep G x₀ y) (Pi.single x₀ (ρ (orbitRep G x₀ y)⁻¹ f x₀)) := by
      conv_lhs => rw [← Finset.univ_sum_single (f : ∀ x, M x)]
      refine Finset.sum_congr rfl fun y _ => ?_
      have := hρ.single_eq x₀ (orbitRep G x₀ y) f; rwa [orbitRep_smul] at this
    have e2 : Pi.single x₀ (orbitCores ρ x₀ f) =
        ∑ y, Pi.single x₀ (ρ (orbitRep G x₀ y)⁻¹ f x₀) :=
      map_sum (AddMonoidHom.single M x₀) _ _
    have step1 : (f : ∀ x, M x) - Pi.single x₀ (orbitCores ρ x₀ f) ∈ (cycSubOne ρ σ).range := by
      have : (f : ∀ x, M x) - Pi.single x₀ (orbitCores ρ x₀ f) = ∑ y, (ρ (orbitRep G x₀ y) (Pi.single x₀ (ρ (orbitRep G x₀ y)⁻¹ f x₀)) -
            Pi.single x₀ (ρ (orbitRep G x₀ y)⁻¹ f x₀)) := by
        rw [Finset.sum_sub_distrib, ← e1, ← e2]
      rw [this]
      exact sum_mem fun y _ => apply_sub_self_mem_range_cycSubOne ρ hσ _ _
    have step2 : Pi.single x₀ (orbitCores ρ x₀ f) ∈ (cycSubOne ρ σ).range := by
      rw [← hc, cycSubOne_apply, Pi.single_sub, ← apply_single_base hρ hD hρ₀ τ]
      exact apply_sub_self_mem_range_cycSubOne ρ hσ _ _
    have := add_mem step1 step2; rwa [sub_add_cancel] at this
  · rintro ⟨h, hh⟩
    rw [← hh, cycSubOne_apply, map_sub]
    exact orbitCores_apply_sub_mem hD hρ₀ hτ σ h
noncomputable def cycTateNegOneOrbitEquiv [Fintype G] (ρ : Representation k G (∀ x, M x)) (hρ : PermutesFactors ρ) (x₀ : X) (D : Subgroup G) [Fintype D] (hD : ∀ g, g ∈ D ↔ g • x₀ = x₀) (ρ₀ : Representation k D (M x₀))
    (hρ₀ : ∀ (d : D) (f : ∀ x, M x), ρ d f x₀ = ρ₀ d (f x₀)) (σ : G)
    (hσ : ∀ g, g ∈ Subgroup.zpowers σ) (τ : D) (hτ : ∀ d, d ∈ Subgroup.zpowers τ) :
    CycTateNegOne ρ σ ≃+ CycTateNegOne ρ₀ τ :=
  letI : Finite X := finite_of_isPretransitive G x₀
  letI : Fintype X := Fintype.ofFinite X
  kerModRangeEquivOfSurjective (orbitNegOneMap ρ x₀ D hD ρ₀ hρ₀ τ) (orbitNegOneMap_surjective ρ hρ x₀ D hD ρ₀ hρ₀ τ hτ) (orbitNegOneMap_eq_zero_iff ρ hρ x₀ D hD ρ₀ hρ₀ σ hσ τ hτ)
theorem cycTateNegOneOrbitEquiv_symm_mk [Fintype G] [DecidableEq X] (ρ : Representation k G (∀ x, M x)) (hρ : PermutesFactors ρ) (x₀ : X) (D : Subgroup G) [Fintype D] (hD : ∀ g, g ∈ D ↔ g • x₀ = x₀) (ρ₀ : Representation k D (M x₀))
    (hρ₀ : ∀ (d : D) (f : ∀ x, M x), ρ d f x₀ = ρ₀ d (f x₀)) (σ : G)
    (hσ : ∀ g, g ∈ Subgroup.zpowers σ) (τ : D) (hτ : ∀ d, d ∈ Subgroup.zpowers τ)
    (b : (cycNorm ρ₀).ker) :
    (cycTateNegOneOrbitEquiv ρ hρ x₀ D hD ρ₀ hρ₀ σ hσ τ hτ).symm (QuotientAddGroup.mk b) =
      QuotientAddGroup.mk ⟨Pi.single x₀ (b : M x₀), single_mem_ker_cycNorm hρ hD hρ₀ b.2⟩ := by
  rw [AddEquiv.symm_apply_eq, eq_comm]
  let _ : Finite X := finite_of_isPretransitive G x₀
  let _ : Fintype X := Fintype.ofFinite X; show orbitNegOneMap ρ x₀ D hD ρ₀ hρ₀ τ _ = _; rw [orbitNegOneMap_apply, KerModRange.mk_eq_mk_iff]
  show orbitCores ρ x₀ (Pi.single x₀ (b : M x₀)) - (b : M x₀) ∈ (cycSubOne ρ₀ τ).range
  rw [orbitCores_single hρ hD hρ₀]
  exact apply_sub_self_mem_range_cycSubOne ρ₀ hτ _ _
theorem cycHerbrand_orbit [Fintype G] (ρ : Representation k G (∀ x, M x)) (hρ : PermutesFactors ρ) (x₀ : X) (D : Subgroup G) [Fintype D] (hD : ∀ g, g ∈ D ↔ g • x₀ = x₀) (ρ₀ : Representation k D (M x₀))
    (hρ₀ : ∀ (d : D) (f : ∀ x, M x), ρ d f x₀ = ρ₀ d (f x₀)) (σ : G)
    (hσ : ∀ g, g ∈ Subgroup.zpowers σ) (τ : D) (hτ : ∀ d, d ∈ Subgroup.zpowers τ) :
    cycHerbrand ρ σ = cycHerbrand ρ₀ τ := by
  rw [cycHerbrand_eq, cycHerbrand_eq, Nat.card_congr (cycTateZeroOrbitEquiv ρ hρ x₀ D hD ρ₀ hρ₀ σ hσ τ hτ).toEquiv, Nat.card_congr (cycTateNegOneOrbitEquiv ρ hρ x₀ D hD ρ₀ hρ₀ σ hσ τ hτ).toEquiv]
end Orbit
end Sec_CycTateNegOneOrbitEquivSymmMk


/-! ### Cyclic -/
section Sec_Cyclic
open RHDirect.Stage13CFT_IdeleNormResidue
section Defs
variable {G M : Type*} [Group G] [AddCommGroup M]
def cycSub (ρ : Representation ℤ G M) (σ : G) : M →+ M :=
  (ρ σ - LinearMap.id).toAddMonoidHom
def normHom [Fintype G] (ρ : Representation ℤ G M) : M →+ M :=
  ρ.norm.toAddMonoidHom
noncomputable def cyclicHerbrand [Fintype G] (ρ : Representation ℤ G M) (σ : G) : ℚ :=
  herbrandQuotient (cycSub ρ σ) (normHom ρ)
def HasCyclicHerbrand [Fintype G] (ρ : Representation ℤ G M) (σ : G) : Prop :=
  HasHerbrandQuotient (cycSub ρ σ) (normHom ρ)
@[simp]
theorem cycSub_apply (ρ : Representation ℤ G M) (σ : G) (x : M) : cycSub ρ σ x = ρ σ x - x :=
  rfl
@[simp]
theorem normHom_apply [Fintype G] (ρ : Representation ℤ G M) (x : M) : normHom ρ x = ∑ g : G, ρ g x := by simp [normHom, Representation.norm, LinearMap.sum_apply]
theorem normHom_cycSub [Fintype G] (ρ : Representation ℤ G M) (σ : G) (x : M) : normHom ρ (cycSub ρ σ x) = 0 := by
  simp only [normHom, cycSub, LinearMap.toAddMonoidHom_coe, LinearMap.sub_apply, LinearMap.id_apply, map_sub, Representation.norm_self_apply, sub_self]
theorem cycSub_normHom [Fintype G] (ρ : Representation ℤ G M) (σ : G) (x : M) : cycSub ρ σ (normHom ρ x) = 0 := by
  simp only [normHom, cycSub, LinearMap.toAddMonoidHom_coe, LinearMap.sub_apply, LinearMap.id_apply, Representation.self_norm_apply, sub_self]
end Defs
section Generator
variable {G M : Type*} [Group G] [AddCommGroup M] (ρ : Representation ℤ G M) {σ : G}
theorem sub_mem_range_cycSub (hσ : ∀ g, g ∈ Subgroup.zpowers σ) (g : G) (x : M) : ρ g x - x ∈ (cycSub ρ σ).range := by
  let S : Subgroup G :=
    { carrier := {g | ∀ x, ρ g x - x ∈ (cycSub ρ σ).range}
      one_mem' := fun x => by simp
      mul_mem' := fun {a b} ha hb x => by
        have : ρ (a * b) x - x = (ρ a (ρ b x) - ρ b x) + (ρ b x - x) := by rw [map_mul, Module.End.mul_apply]; abel
        rw [this]
        exact add_mem (ha _) (hb _)
      inv_mem' := fun {a} ha x => by
        have : ρ a⁻¹ x - x = -(ρ a (ρ a⁻¹ x) - ρ a⁻¹ x) := by
          rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
          abel
        rw [this]
        exact neg_mem (ha _) }
  have hσS : σ ∈ S := fun x => ⟨x, rfl⟩
  have : Subgroup.zpowers σ ≤ S := (Subgroup.zpowers_le).2 hσS; exact this (hσ g) x
theorem apply_eq_of_cycSub_eq_zero (hσ : ∀ g, g ∈ Subgroup.zpowers σ) {x : M}
    (hx : cycSub ρ σ x = 0) (g : G) : ρ g x = x :=
  by
  have h1 : ρ σ x = x := sub_eq_zero.1 hx
  let H : Subgroup G := { carrier := {g | ρ g x = x}, one_mem' := by simp, mul_mem' := fun {a b} ha hb => by simp only [Set.mem_ofPred_eq, map_mul, Module.End.mul_apply] at ha hb ⊢; rw [hb, ha], inv_mem' := fun {a} ha => by have := congrArg (ρ a⁻¹) ha; simp [← Module.End.mul_apply, ← map_mul] at this; exact this.symm }
  exact (Subgroup.zpowers_le (H := H)).2 h1 (hσ g)
variable [Fintype G]
theorem normHom_eq_card_smul (hσ : ∀ g, g ∈ Subgroup.zpowers σ) {x : M}
    (hx : cycSub ρ σ x = 0) : normHom ρ x = (Fintype.card G : ℤ) • x := by
  rw [normHom_apply, Finset.sum_congr rfl fun g _ => apply_eq_of_cycSub_eq_zero ρ hσ hx g, Finset.sum_const, Finset.card_univ, natCast_zsmul]
theorem card_smul_sub_normHom_mem (hσ : ∀ g, g ∈ Subgroup.zpowers σ) (x : M) : (Fintype.card G : ℤ) • x - normHom ρ x ∈ (cycSub ρ σ).range := by
  have : (Fintype.card G : ℤ) • x - normHom ρ x = -∑ g : G, (ρ g x - x) := by
    rw [normHom_apply, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, natCast_zsmul]
    abel
  rw [this]
  exact neg_mem (AddSubgroup.sum_mem _ fun g _ => sub_mem_range_cycSub ρ hσ g x)
end Generator
section Finiteness
theorem finite_kerModRange_of_smul_mem {A : Type*} [AddCommGroup A] [Module.Finite ℤ A] (f g : A →+ A) {n : ℤ} (hn : n ≠ 0) (h : ∀ x ∈ f.ker, n • x ∈ g.range) :
    Finite (KerModRange f g) := by
  have hfin : Module.Finite ℤ f.ker := by have : Module.Finite ℤ (LinearMap.ker f.toIntLinearMap) := inferInstance; exact Module.Finite.equiv (R := ℤ) ((LinearEquiv.refl ℤ (LinearMap.ker f.toIntLinearMap)) : _ ≃ₗ[ℤ] f.ker)
  have hq : Module.Finite ℤ (KerModRange f g) :=
    Module.Finite.of_surjective (QuotientAddGroup.mk' (g.range.addSubgroupOf f.ker)).toIntLinearMap (QuotientAddGroup.mk'_surjective _)
  apply Module.finite_of_fg_torsion
  intro y
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective (g.range.addSubgroupOf f.ker) y; refine ⟨⟨n, mem_nonZeroDivisors_of_ne_zero hn⟩, ?_⟩; show n • (QuotientAddGroup.mk' _ x : KerModRange f g) = 0
  rw [← map_zsmul, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf, AddSubgroup.coe_zsmul]
  exact h x x.2
variable {G M : Type*} [Group G] [Fintype G] [AddCommGroup M] [Module.Finite ℤ M]
theorem hasCyclicHerbrand_of_finite (ρ : Representation ℤ G M) {σ : G}
    (hσ : ∀ g, g ∈ Subgroup.zpowers σ) : HasCyclicHerbrand ρ σ := by
  have hn : (Fintype.card G : ℤ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  refine ⟨finite_kerModRange_of_smul_mem _ _ hn fun x hx => ?_, finite_kerModRange_of_smul_mem _ _ hn fun x hx => ?_⟩
  · rw [← normHom_eq_card_smul ρ hσ hx]
    exact ⟨x, rfl⟩
  · have := card_smul_sub_normHom_mem ρ hσ x
    rwa [AddMonoidHom.mem_ker.1 hx, sub_zero] at this
end Finiteness
section Trivial
variable {G : Type*} [Group G] [Fintype G]
theorem cyclicHerbrand_trivial_int (σ : G) : cyclicHerbrand (Representation.trivial ℤ G ℤ) σ = Fintype.card G := by
  set ρ := Representation.trivial ℤ G ℤ
  have hf : cycSub ρ σ = 0 := by
    ext
    simp [ρ]
  have hg : normHom ρ = (Fintype.card G : ℤ) • AddMonoidHom.id ℤ := by
    ext
    simp [ρ, normHom_apply]
  have hn : (Fintype.card G : ℤ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have h1 : Nat.card (KerModRange (cycSub ρ σ) (normHom ρ)) = Fintype.card G := by
    show (normHom ρ).range.relIndex (cycSub ρ σ).ker = _
    have hr : (normHom ρ).range = AddSubgroup.zmultiples (Fintype.card G : ℤ) := by
      ext y
      simp only [hg, AddMonoidHom.mem_range, AddMonoidHom.smul_apply, AddMonoidHom.id_apply, AddSubgroup.mem_zmultiples_iff, smul_eq_mul]
      exact ⟨fun ⟨x, hx⟩ => ⟨x, by rw [← hx, mul_comm]⟩, fun ⟨x, hx⟩ => ⟨x, by rw [← hx, mul_comm]⟩⟩
    rw [hf, AddMonoidHom.ker_zero, AddSubgroup.relIndex_top_right, hr, Int.index_zmultiples, Int.natAbs_natCast]
  have h2 : Nat.card (KerModRange (normHom ρ) (cycSub ρ σ)) = 1 := by
    have : Subsingleton (normHom ρ).ker := by
      constructor
      rintro ⟨a, ha⟩ ⟨b, hb⟩; rw [AddMonoidHom.mem_ker, hg] at ha hb; simp only [AddMonoidHom.smul_apply, AddMonoidHom.id_apply, smul_eq_mul, mul_eq_zero, hn, false_or] at ha hb; subst ha hb; rfl
    have : Subsingleton (KerModRange (normHom ρ) (cycSub ρ σ)) := by
      constructor
      intro a b
      induction a using QuotientAddGroup.induction_on
      induction b using QuotientAddGroup.induction_on
      congr 1
      exact Subsingleton.elim _ _
    exact Nat.card_of_subsingleton 0
  rw [cyclicHerbrand, herbrandQuotient, h1, h2, Nat.cast_one, div_one]
end Trivial
end Sec_Cyclic


/-! ### RationalForm -/
section Sec_RationalForm
open Matrix
theorem exists_rat_intertwiner {ι J : Type*} [Fintype ι] [DecidableEq ι] (A A' : J → Matrix ι ι ℚ) (P : Matrix ι ι ℝ) (hP : P.det ≠ 0) (h : ∀ j, P * (A j).map (Rat.cast : ℚ → ℝ) = (A' j).map (Rat.cast : ℚ → ℝ) * P) :
    ∃ Q : Matrix ι ι ℚ, Q.det ≠ 0 ∧ ∀ j, Q * A j = A' j * Q := by
  obtain ⟨V, hV⟩ : ∃ V : Submodule ℚ ℝ,
      V = Submodule.span ℚ (Set.range fun p : ι × ι => P p.1 p.2) := ⟨_, rfl⟩
  have : Module.Finite ℚ V := hV ▸ Module.Finite.span_of_finite ℚ (Set.finite_range _)
  obtain ⟨κ, _, ⟨c⟩⟩ : ∃ (κ : Type) (_ : Fintype κ), Nonempty (Module.Basis κ ℚ V) :=
    ⟨_, inferInstance, ⟨Module.Free.chooseBasis ℚ V⟩⟩
  have hmem : ∀ a b, P a b ∈ V := fun a b => hV ▸ Submodule.subset_span ⟨(a, b), rfl⟩
  let Bm : κ → Matrix ι ι ℚ := fun k a b => c.repr ⟨P a b, hmem a b⟩ k
  have hcast : ∀ (q : ℚ) (r : ℝ), q • r = (q : ℝ) * r := fun q r => by
    rw [Algebra.smul_def, eq_ratCast]
  have hP_eq : P = ∑ k, (c k : ℝ) • (Bm k).map (Rat.cast : ℚ → ℝ) := by
    ext a b
    have h1 := congrArg (Subtype.val : V → ℝ) (c.sum_repr ⟨P a b, hmem a b⟩); rw [Submodule.coe_sum] at h1; simp only [Submodule.coe_smul, hcast] at h1; rw [Matrix.sum_apply]
    simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
    rw [← h1]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  have hli : LinearIndependent ℚ (fun k => (c k : ℝ)) :=
    c.linearIndependent.map' V.subtype (Submodule.ker_subtype V)
  have hB : ∀ k j, Bm k * A j = A' j * Bm k := by
    intro k j
    have hsum : ∑ k, (c k : ℝ) • (Bm k * A j - A' j * Bm k).map (Rat.cast : ℚ → ℝ) = 0 := by
      have hmap : ∀ X Y : Matrix ι ι ℚ, (X * Y).map (Rat.cast : ℚ → ℝ) =
          X.map (Rat.cast : ℚ → ℝ) * Y.map (Rat.cast : ℚ → ℝ) := fun X Y =>
        Matrix.map_mul (f := Rat.castHom ℝ)
      have hsub : ∀ X Y : Matrix ι ι ℚ, (X - Y).map (Rat.cast : ℚ → ℝ) =
          X.map (Rat.cast : ℚ → ℝ) - Y.map (Rat.cast : ℚ → ℝ) := fun X Y => by
        ext; simp
      have e1 : ∑ k, (c k : ℝ) • ((Bm k).map (Rat.cast : ℚ → ℝ) * (A j).map (Rat.cast : ℚ → ℝ)) =
          P * (A j).map (Rat.cast : ℚ → ℝ) := by
        rw [hP_eq, Finset.sum_mul]
        simp only [Matrix.smul_mul]
      have e2 : ∑ k, (c k : ℝ) • ((A' j).map (Rat.cast : ℚ → ℝ) * (Bm k).map (Rat.cast : ℚ → ℝ)) =
          (A' j).map (Rat.cast : ℚ → ℝ) * P := by
        rw [hP_eq, Finset.mul_sum]
        simp only [Matrix.mul_smul]
      simp only [hsub, hmap, smul_sub, Finset.sum_sub_distrib, e1, e2, h j, sub_self]
    ext a b
    have hab := congrFun (congrFun hsum a) b; simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, Matrix.zero_apply] at hab
    have := Fintype.linearIndependent_iff.1 hli (fun k => (Bm k * A j - A' j * Bm k) a b) (by simpa only [hcast, mul_comm] using hab) k; rwa [Matrix.sub_apply, sub_eq_zero] at this
  clear_value Bm
  obtain ⟨Mx, hMx⟩ : ∃ Mx : Matrix ι ι (MvPolynomial κ ℚ),
      Mx = Matrix.of fun a b => ∑ k, MvPolynomial.X k * MvPolynomial.C (Bm k a b) := ⟨_, rfl⟩
  have hev : ∀ (t : κ → ℝ), (MvPolynomial.aeval t : MvPolynomial κ ℚ →ₐ[ℚ] ℝ).mapMatrix Mx =
        Matrix.of fun a b => ∑ k, t k * algebraMap ℚ ℝ (Bm k a b) := by
    intro t; ext a b; rw [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply]; rw [hMx, Matrix.of_apply, map_sum]; refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, MvPolynomial.aeval_X, MvPolynomial.aeval_C]
  have hPof : P = Matrix.of fun a b => ∑ k, (c k : ℝ) * algebraMap ℚ ℝ (Bm k a b) := by
    refine hP_eq.trans ?_
    ext a b
    rw [Matrix.sum_apply, Matrix.of_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, eq_ratCast]
  have hF : Mx.det ≠ 0 := by intro h0; apply hP; rw [hPof, ← hev, ← AlgHom.map_det, h0]; exact map_zero _
  obtain ⟨q, hq⟩ : ∃ q : κ → ℚ, MvPolynomial.eval q Mx.det ≠ 0 := by
    by_contra! hall
    exact hF (MvPolynomial.funext fun x => by rw [hall x, map_zero])
  refine ⟨∑ k, q k • Bm k, ?_, fun j => ?_⟩
  · have hQ : ∑ k, q k • Bm k = Matrix.of fun a b => ∑ k, q k * algebraMap ℚ ℚ (Bm k a b) := by
      ext a b
      rw [Matrix.sum_apply, Matrix.of_apply]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Matrix.smul_apply, smul_eq_mul, Algebra.algebraMap_self, RingHom.id_apply]
    have hevq : (MvPolynomial.eval q).mapMatrix Mx =
        Matrix.of fun a b => ∑ k, q k * algebraMap ℚ ℚ (Bm k a b) := by
      ext a b
      rw [RingHom.mapMatrix_apply, Matrix.map_apply, hMx, Matrix.of_apply, Matrix.of_apply,
        map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_mul, MvPolynomial.eval_X, MvPolynomial.eval_C, Algebra.algebraMap_self, RingHom.id_apply]
    have := RingHom.map_det (MvPolynomial.eval q) Mx; rw [hevq] at this; rw [hQ, ← this]; exact hq
  · rw [Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [Matrix.smul_mul, Matrix.mul_smul, hB]
end Sec_RationalForm


/-! ### Lattice -/
section Sec_Lattice
open RHDirect.Stage13CFT_IdeleNormResidue
open scoped TensorProduct
theorem finite_quotient_of_smul_mem {B : Type*} [AddCommGroup B] [Module.Finite ℤ B]
    (S : AddSubgroup B) {n : ℤ} (hn : n ≠ 0) (h : ∀ y, n • y ∈ S) : Finite (B ⧸ S) := by
  have : Module.Finite ℤ (B ⧸ S) :=
    Module.Finite.of_surjective (QuotientAddGroup.mk' S).toIntLinearMap (QuotientAddGroup.mk'_surjective _)
  apply Module.finite_of_fg_torsion
  intro y
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective S y; refine ⟨⟨n, mem_nonZeroDivisors_of_ne_zero hn⟩, ?_⟩; show n • (QuotientAddGroup.mk' S x) = 0
  rw [← map_zsmul, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
  exact h x
variable {G M M' : Type*} [Group G] [AddCommGroup M] [AddCommGroup M']
theorem cyclicHerbrand_eq_of_injective [Fintype G] (ρ : Representation ℤ G M) (ρ' : Representation ℤ G M') (σ : G) (φ : M →+ M') (hφ : Function.Injective φ) [Finite (M' ⧸ φ.range)] (hcomm : ∀ g x, φ (ρ g x) = ρ' g (φ x)) :
    cyclicHerbrand ρ σ = cyclicHerbrand ρ' σ :=
  herbrandQuotient_eq_of_injective_of_finite (fA := cycSub ρ σ) (gA := normHom ρ)
    (fB := cycSub ρ' σ) (gB := normHom ρ') hφ
    (fun a => by rw [cycSub_apply, cycSub_apply, map_sub, hcomm])
    (fun a => by rw [normHom_apply, normHom_apply, map_sum]; simp only [hcomm])
    (cycSub_normHom ρ' σ) (normHom_cycSub ρ' σ)
theorem exists_injective_intertwiner_of_basis {ι : Type*} [Fintype ι] (ρ : Representation ℤ G M) (ρ' : Representation ℤ G M') (e : ℝ ⊗[ℤ] M ≃ₗ[ℝ] ℝ ⊗[ℤ] M') (he : ∀ g x, e ((ρ g).baseChange ℝ x) = (ρ' g).baseChange ℝ (e x))
    (b : Module.Basis ι ℤ M) (b' : Module.Basis ι ℤ M') :
    ∃ φ : M →ₗ[ℤ] M', Function.Injective φ ∧ (∃ n : ℤ, n ≠ 0 ∧ ∀ y, ∃ x, φ x = n • y) ∧
      ∀ g x, φ (ρ g x) = ρ' g (φ x) := by
  classical
  let bR := Algebra.TensorProduct.basis ℝ b
  let bR' := Algebra.TensorProduct.basis ℝ b'
  let A : G → Matrix ι ι ℤ := fun g => LinearMap.toMatrix b b (ρ g)
  let A' : G → Matrix ι ι ℤ := fun g => LinearMap.toMatrix b' b' (ρ' g)
  let P : Matrix ι ι ℝ := LinearMap.toMatrix bR bR' e.toLinearMap
  have hP : P.det ≠ 0 := by
    have hid : e.symm.toLinearMap ∘ₗ e.toLinearMap = LinearMap.id :=
      LinearMap.ext fun x => by simp
    have h1 := congrArg (LinearMap.toMatrix bR bR) hid; rw [LinearMap.toMatrix_comp bR bR' bR, LinearMap.toMatrix_id] at h1
    have h2 := congrArg Matrix.det h1; rw [Matrix.det_mul, Matrix.det_one] at h2; exact right_ne_zero_of_mul_eq_one h2
  have hPA : ∀ g, P * (A g).map (Int.cast : ℤ → ℝ) = (A' g).map (Int.cast : ℤ → ℝ) * P := by
    intro g
    have hc : e.toLinearMap ∘ₗ (ρ g).baseChange ℝ = (ρ' g).baseChange ℝ ∘ₗ e.toLinearMap :=
      LinearMap.ext (he g)
    have h1 := congrArg (LinearMap.toMatrix bR bR') hc; rw [LinearMap.toMatrix_comp bR bR bR', LinearMap.toMatrix_comp bR bR' bR', LinearMap.toMatrix_baseChange, LinearMap.toMatrix_baseChange, algebraMap_int_eq] at h1
    exact h1
  obtain ⟨Q, hQ, hQA⟩ := exists_rat_intertwiner (fun g => (A g).map (Int.cast : ℤ → ℚ)) (fun g => (A' g).map (Int.cast : ℤ → ℚ)) P hP (fun g => by
      rw [Matrix.map_map, Matrix.map_map]
      convert hPA g using 3 <;> ext x <;> simp)
  obtain ⟨⟨d, hd⟩, hdQ⟩ := IsLocalization.exist_integer_multiples (R := ℤ)
    (M := nonZeroDivisors ℤ) (S := ℚ) Finset.univ (fun p : ι × ι => Q p.1 p.2)
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  choose D hD using fun a b => RingHom.mem_rangeS.1 (hdQ (a, b) (Finset.mem_univ _))
  let Dm : Matrix ι ι ℤ := Matrix.of D
  have hDm : Dm.map (Int.cast : ℤ → ℚ) = (d : ℚ) • Q := by
    ext a b
    simp only [Matrix.map_apply, Matrix.smul_apply, Dm, Matrix.of_apply]
    rw [← eq_intCast (algebraMap ℤ ℚ), hD a b, zsmul_eq_mul, smul_eq_mul]
  have hdet : Dm.det ≠ 0 := by
    have h1 : (Dm.det : ℚ) = (d : ℚ) ^ Fintype.card ι * Q.det := by
      rw [Int.cast_det]
      change (Dm.map (Int.cast : ℤ → ℚ)).det = _; rw [hDm, Matrix.det_smul]
    intro h0; rw [h0, Int.cast_zero] at h1; exact mul_ne_zero (pow_ne_zero _ (by exact_mod_cast hd0)) hQ h1.symm
  have hmap : ∀ X Y : Matrix ι ι ℤ, (X * Y).map (Int.cast : ℤ → ℚ) =
      X.map (Int.cast : ℤ → ℚ) * Y.map (Int.cast : ℤ → ℚ) := fun X Y =>
    Matrix.map_mul (f := Int.castRingHom ℚ)
  have hDA : ∀ g, Dm * A g = A' g * Dm := by
    intro g; apply Matrix.map_injective (f := (Int.cast : ℤ → ℚ)) Int.cast_injective; show (Dm * A g).map (Int.cast : ℤ → ℚ) = (A' g * Dm).map (Int.cast : ℤ → ℚ)
    rw [hmap, hmap, hDm, Matrix.smul_mul, Matrix.mul_smul, hQA g]
  let φ : M →ₗ[ℤ] M' := Matrix.toLin b b' Dm; refine ⟨φ, ?_, ⟨Dm.det, hdet, fun y => ?_⟩, fun g x => ?_⟩
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have h1 := Matrix.repr_toLin (v₁ := b) (v₂ := b') Dm x; rw [show Matrix.toLin b b' Dm x = 0 from hx, map_zero] at h1
    have h2 := Matrix.eq_zero_of_mulVec_eq_zero hdet h1.symm; exact b.repr.map_eq_zero_iff.1 (Finsupp.ext fun i => congrFun h2 i)
  · refine ⟨Matrix.toLin b' b Dm.adjugate y, ?_⟩
    show (Matrix.toLin b b' Dm ∘ₗ Matrix.toLin b' b Dm.adjugate) y = _
    rw [← Matrix.toLin_mul, Matrix.mul_adjugate, map_smul, Matrix.toLin_one, LinearMap.smul_apply, LinearMap.id_apply]
  · have h1 : φ ∘ₗ ρ g = ρ' g ∘ₗ φ := by
      apply (LinearMap.toMatrix b b').injective
      rw [LinearMap.toMatrix_comp b b b', LinearMap.toMatrix_comp b b' b', LinearMap.toMatrix_toLin]
      exact hDA g
    exact LinearMap.congr_fun h1 x
variable [Module.Finite ℤ M] [Module.Free ℤ M] [Module.Finite ℤ M'] [Module.Free ℤ M']
theorem exists_injective_intertwiner_of_real_equiv (ρ : Representation ℤ G M) (ρ' : Representation ℤ G M') (e : ℝ ⊗[ℤ] M ≃ₗ[ℝ] ℝ ⊗[ℤ] M') (he : ∀ g x, e ((ρ g).baseChange ℝ x) = (ρ' g).baseChange ℝ (e x)) :
    ∃ φ : M →ₗ[ℤ] M', Function.Injective φ ∧ (∃ n : ℤ, n ≠ 0 ∧ ∀ y, ∃ x, φ x = n • y) ∧
      ∀ g x, φ (ρ g x) = ρ' g (φ x) := by
  let b := Module.Free.chooseBasis ℤ M
  let b₀ := Module.Free.chooseBasis ℤ M'
  have h1 := e.finrank_eq; rw [Module.finrank_eq_card_basis (Algebra.TensorProduct.basis ℝ b), Module.finrank_eq_card_basis (Algebra.TensorProduct.basis ℝ b₀)] at h1
  exact exists_injective_intertwiner_of_basis ρ ρ' e he b (b₀.reindex (Fintype.equivOfCardEq h1).symm)
theorem cyclicHerbrand_eq_of_real_equiv [Fintype G] (ρ : Representation ℤ G M) (ρ' : Representation ℤ G M') (σ : G) (e : ℝ ⊗[ℤ] M ≃ₗ[ℝ] ℝ ⊗[ℤ] M') (he : ∀ g x, e ((ρ g).baseChange ℝ x) = (ρ' g).baseChange ℝ (e x)) :
    cyclicHerbrand ρ σ = cyclicHerbrand ρ' σ := by
  obtain ⟨φ, hφ, ⟨n, hn, hrange⟩, hcomm⟩ := exists_injective_intertwiner_of_real_equiv ρ ρ' e he
  have : Finite (M' ⧸ φ.toAddMonoidHom.range) :=
    finite_quotient_of_smul_mem _ hn fun y => by
      obtain ⟨x, hx⟩ := hrange y; exact ⟨x, hx⟩
  exact cyclicHerbrand_eq_of_injective ρ ρ' σ φ.toAddMonoidHom hφ hcomm
end Sec_Lattice


/-! ### LatticeBridge -/
section Sec_LatticeBridge
open MulAction
open scoped TensorProduct
variable {G : Type*} [Group G] [Fintype G]
theorem cyclicHerbrand_eq_cycHerbrand {M : Type*} [AddCommGroup M] (ρ : Representation ℤ G M)
    (σ : G) : cyclicHerbrand ρ σ = cycHerbrand ρ σ :=
  rfl
theorem cycHerbrand_trivial_int (σ : G) : cycHerbrand (Representation.trivial ℤ G ℤ) σ = Fintype.card G :=
  cyclicHerbrand_trivial_int σ
theorem cycHerbrand_eq_of_real_equiv {M M' : Type*} [AddCommGroup M] [Module.Finite ℤ M] [Module.Free ℤ M] [AddCommGroup M'] [Module.Finite ℤ M'] [Module.Free ℤ M'] (ρ : Representation ℤ G M) (ρ' : Representation ℤ G M') (σ : G)
    (e : ℝ ⊗[ℤ] M ≃ₗ[ℝ] ℝ ⊗[ℤ] M')
    (he : ∀ g x, e ((ρ g).baseChange ℝ x) = (ρ' g).baseChange ℝ (e x)) :
    cycHerbrand ρ σ = cycHerbrand ρ' σ :=
  cyclicHerbrand_eq_of_real_equiv ρ ρ' σ e he
end Sec_LatticeBridge


/-! ### Permutation -/
section Sec_Permutation
open RHDirect.Stage13CFT_IdeleNormResidue MulAction
section Orbits
variable (G : Type*) {X : Type*} [Group G] [MulAction G X]
noncomputable def orbitPoint (x : X) : X :=
  Quotient.out (Quotient.mk (orbitRel G X) x)
variable {G}
theorem mk_orbitPoint (x : X) : Quotient.mk (orbitRel G X) (orbitPoint G x) = Quotient.mk (orbitRel G X) x :=
  Quotient.out_eq _
theorem orbitPoint_mem (x : X) : orbitPoint G x ∈ orbit G x :=
  orbitRel_apply.1 (Quotient.exact (mk_orbitPoint x))
theorem orbitPoint_eq_of_mem {x y : X} (h : y ∈ orbit G x) : orbitPoint G y = orbitPoint G x := by unfold orbitPoint; rw [Quotient.sound (orbitRel_apply.2 h)]
theorem orbitPoint_smul (g : G) (x : X) : orbitPoint G (g • x) = orbitPoint G x :=
  orbitPoint_eq_of_mem (mem_orbit x g)
theorem orbitPoint_orbitPoint (x : X) : orbitPoint G (orbitPoint G x) = orbitPoint G x :=
  orbitPoint_eq_of_mem (orbitPoint_mem x)
theorem card_stabilizer_eq_of_mem {x y : X} (h : y ∈ orbit G x) :
    Nat.card (stabilizer G y) = Nat.card (stabilizer G x) := by
  obtain ⟨g, rfl⟩ := h; exact (Nat.card_congr (stabilizerEquivStabilizer (rfl : g • x = g • x)).toEquiv).symm
variable [Fintype G]
theorem card_filter_smul_eq [DecidableEq X] (p : X) (g₀ : G) : (Finset.univ.filter fun g : G => g • p = g₀ • p).card = Nat.card (stabilizer G p) := by
  have h1 : Nat.card (stabilizer G p) = (Finset.univ.filter fun g : G => g • p = p).card := by
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun g => mem_stabilizer_iff)
  rw [h1]
  refine Finset.card_bij' (fun g _ => g₀⁻¹ * g) (fun h _ => g₀ * h) ?_ ?_ ?_ ?_
  · intro g hg
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢
    rw [mul_smul, hg, inv_smul_smul]
  · intro h hh
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hh ⊢
    rw [mul_smul, hh]
  · intro g _
    simp
  · intro h _
    simp
theorem card_stabilizer_dvd_card_filter [DecidableEq X] (p y : X) : Nat.card (stabilizer G p) ∣ (Finset.univ.filter fun g : G => g • p = y).card := by
  by_cases hy : y ∈ orbit G p
  · obtain ⟨g₀, rfl⟩ := hy
    rw [card_filter_smul_eq]
  · rw [Finset.card_eq_zero.2 (Finset.filter_eq_empty_iff.2 fun g _ hg => hy ⟨g, hg⟩)]
    exact dvd_zero _
theorem card_stabilizer_dvd_sum [Finite X] (F : X → ℤ) (p : X) : (Nat.card (stabilizer G p) : ℤ) ∣ ∑ g : G, F (g • p) := by
  classical
  have := Fintype.ofFinite X; rw [← Finset.sum_fiberwise Finset.univ (fun g : G => g • p) (fun g => F (g • p))]; refine Finset.dvd_sum fun y _ => ?_
  rw [Finset.sum_congr rfl fun g hg => by rw [(Finset.mem_filter.1 hg).2], Finset.sum_const, nsmul_eq_mul]
  exact Dvd.dvd.mul_right (Int.natCast_dvd_natCast.2 (card_stabilizer_dvd_card_filter p y)) _
theorem sum_smul_eq_of_support (F : X → ℤ) (hF : ∀ y, F y ≠ 0 → orbitPoint G y = y) (p : X) : ∑ g : G, F (g • p) = Nat.card (stabilizer G p) * F (orbitPoint G p) := by
  classical
  have h1 : ∀ g : G, F (g • p) = if g • p = orbitPoint G p then F (orbitPoint G p) else 0 := by
    intro g; split_ifs with hg
    · rw [hg]
    · by_contra hne
      apply hg
      rw [← hF _ hne, orbitPoint_smul]
  rw [Finset.sum_congr rfl fun g _ => h1 g, Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  obtain ⟨g₀, hg₀⟩ := orbitPoint_mem (G := G) p; rw [← show g₀ • p = orbitPoint G p from hg₀, ← card_filter_smul_eq p g₀]
end Orbits
section Permutation
variable {G X : Type*} [Group G] [Fintype G] [MulAction G X]
theorem coeff_normHom_ofMulAction (f : MonoidAlgebra ℤ X) (p : X) : (normHom (Representation.ofMulAction ℤ G X) f).coeff p = ∑ g : G, f.coeff (g • p) := by
  rw [normHom_apply, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  simp only [Representation.coeff_ofMulAction]
  exact Fintype.sum_equiv (Equiv.inv G) _ _ fun g => rfl
noncomputable def permOfFun [Finite X] (F : X → ℤ) : MonoidAlgebra ℤ X :=
  MonoidAlgebra.ofCoeff (Finsupp.equivFunOnFinite.symm F)
@[simp]
theorem coeff_permOfFun [Finite X] (F : X → ℤ) (x : X) : (permOfFun F).coeff x = F x := by simp [permOfFun, MonoidAlgebra.coeff_ofCoeff]
end Permutation
section Cohomology
variable {G X : Type*} [Group G] [Fintype G] [MulAction G X] [Finite X] {σ : G}
omit [Fintype G] [Finite X] in
theorem coeff_smul_of_mem_ker (hσ : ∀ g, g ∈ Subgroup.zpowers σ) {f : MonoidAlgebra ℤ X} (hf : f ∈ (cycSub (Representation.ofMulAction ℤ G X) σ).ker) (g : G) (x : X) :
    f.coeff (g • x) = f.coeff x := by
  have h1 := apply_eq_of_cycSub_eq_zero _ hσ (AddMonoidHom.mem_ker.1 hf) g⁻¹
  have h2 := congrArg (fun f : MonoidAlgebra ℤ X => f.coeff x) h1; simpa only [Representation.coeff_ofMulAction, inv_inv] using h2
omit [Fintype G] in
theorem permOfFun_mem_ker {F : X → ℤ} (hF : ∀ (g : G) x, F (g • x) = F x) :
    permOfFun F ∈ (cycSub (Representation.ofMulAction ℤ G X) σ).ker := by
  rw [AddMonoidHom.mem_ker, cycSub_apply]
  ext x
  simp [Representation.coeff_ofMulAction, hF]
theorem ker_normHom_le_range_cycSub_ofMulAction (hσ : ∀ g, g ∈ Subgroup.zpowers σ) : (normHom (Representation.ofMulAction ℤ G X)).ker ≤ (cycSub (Representation.ofMulAction ℤ G X) σ).range := by
  classical
  have := Fintype.ofFinite X; intro f hf
  let u : MonoidAlgebra ℤ X := ∑ x, f.coeff x • MonoidAlgebra.single (orbitPoint G x) 1
  have hcoeff_u : ∀ y, u.coeff y = ∑ x, if orbitPoint G x = y then f.coeff x else 0 := by intro y; simp [u, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, MonoidAlgebra.coeff_single, Finsupp.single_apply]
  have hfu : f - u ∈ (cycSub (Representation.ofMulAction ℤ G X) σ).range := by
    have hf' : f - u = ∑ x, f.coeff x • (MonoidAlgebra.single x (1 : ℤ) -
        MonoidAlgebra.single (orbitPoint G x) 1) := by
      ext y
      rw [MonoidAlgebra.coeff_sub, Finsupp.sub_apply, hcoeff_u]
      simp [MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, MonoidAlgebra.coeff_single, Finsupp.single_apply, mul_sub, Finset.sum_sub_distrib]
    rw [hf']
    refine AddSubgroup.sum_mem _ fun x _ => AddSubgroup.zsmul_mem _ ?_ _
    obtain ⟨g, hg⟩ := orbitPoint_mem (G := G) x
    have : MonoidAlgebra.single (orbitPoint G x) (1 : ℤ) = (Representation.ofMulAction ℤ G X) g (MonoidAlgebra.single x 1) := by rw [Representation.ofMulAction_single, ← show g • x = orbitPoint G x from hg]
    rw [this, ← neg_sub]
    exact neg_mem (sub_mem_range_cycSub (Representation.ofMulAction ℤ G X) hσ g _)
  have hNu : normHom (Representation.ofMulAction ℤ G X) u = 0 := by
    obtain ⟨v, hv⟩ := hfu
    have : u = f - cycSub (Representation.ofMulAction ℤ G X) σ v := by rw [hv]; abel
    rw [this, map_sub, AddMonoidHom.mem_ker.1 hf, normHom_cycSub, sub_zero]
  have hsupp : ∀ y, u.coeff y ≠ 0 → orbitPoint G y = y := by
    intro y hy; rw [hcoeff_u] at hy
    obtain ⟨x, _, hx⟩ := Finset.exists_ne_zero_of_sum_ne_zero hy
    have hxy : orbitPoint G x = y := by
      by_contra h
      exact hx (if_neg h)
    rw [← hxy, orbitPoint_orbitPoint]
  have hu : u = 0 := by
    ext p
    rw [MonoidAlgebra.coeff_zero, Finsupp.zero_apply]
    by_contra hp
    have hrep := hsupp p hp
    have h1 := congrArg (fun f : MonoidAlgebra ℤ X => f.coeff p) hNu; simp only [MonoidAlgebra.coeff_zero, Finsupp.zero_apply] at h1; rw [coeff_normHom_ofMulAction] at h1
    rw [sum_smul_eq_of_support (fun y => u.coeff y) hsupp p, hrep] at h1
    have hs : (Nat.card (stabilizer G p) : ℤ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
    exact hp ((mul_eq_zero.1 h1).resolve_left hs)
  rwa [hu, sub_zero] at hfu
theorem natCard_kerModRange_normHom_ofMulAction (hσ : ∀ g, g ∈ Subgroup.zpowers σ) : Nat.card (KerModRange (normHom (Representation.ofMulAction ℤ G X)) (cycSub (Representation.ofMulAction ℤ G X) σ)) = 1 := by
  have : Subsingleton (KerModRange (normHom (Representation.ofMulAction ℤ G X))
      (cycSub (Representation.ofMulAction ℤ G X) σ)) := by
    constructor
    intro a b
    induction a using QuotientAddGroup.induction_on with | H a => ?_
    induction b using QuotientAddGroup.induction_on with | H b => ?_
    rw [KerModRange.mk_eq_mk_iff]
    exact ker_normHom_le_range_cycSub_ofMulAction hσ (sub_mem a.2 b.2)
  exact Nat.card_of_subsingleton 0
theorem natCard_kerModRange_cycSub_ofMulAction [Fintype (orbitRel.Quotient G X)] (hσ : ∀ g, g ∈ Subgroup.zpowers σ) : Nat.card (KerModRange (cycSub (Representation.ofMulAction ℤ G X) σ) (normHom (Representation.ofMulAction ℤ G X))) =
      ∏ ω : orbitRel.Quotient G X, Nat.card (stabilizer G (Quotient.out ω)) := by
  classical
  set K := (cycSub (Representation.ofMulAction ℤ G X) σ).ker
  let s : orbitRel.Quotient G X → ℕ := fun ω => Nat.card (stabilizer G (Quotient.out ω))
  have hs : ∀ ω, NeZero (s ω) := fun ω => ⟨Nat.card_pos.ne'⟩
  let Φ : K →+ ((ω : orbitRel.Quotient G X) → ZMod (s ω)) :=
    { toFun := fun f ω => (((f : MonoidAlgebra ℤ X).coeff (Quotient.out ω) : ℤ) : ZMod (s ω))
      map_zero' := by
        ext ω
        simp
      map_add' := by intro f f'; ext ω; simp }
  have hΦ : ∀ (f : K) ω, Φ f ω = (((f : MonoidAlgebra ℤ X).coeff (Quotient.out ω) : ℤ) :
      ZMod (s ω)) := fun _ _ => rfl
  have hsurj : Function.Surjective Φ := by
    intro c
    let F : X → ℤ := fun x => ((c (Quotient.mk (orbitRel G X) x)).val : ℤ)
    have hF : ∀ (g : G) x, F (g • x) = F x := by intro g x; simp only [F]; rw [Quotient.sound (orbitRel_apply.2 (mem_orbit x g))]
    refine ⟨⟨permOfFun F, permOfFun_mem_ker hF⟩, ?_⟩
    ext ω
    rw [hΦ, coeff_permOfFun]
    have hω : Quotient.mk (orbitRel G X) (Quotient.out ω) = ω := Quotient.out_eq ω
    have key : ∀ ω', ω' = ω → ((((c ω').val : ℕ) : ℤ) : ZMod (s ω)) = c ω := by rintro _ rfl; rw [Int.cast_natCast]; exact @ZMod.natCast_zmod_val _ (hs _) _
    exact key _ hω
  have hker : Φ.ker = (normHom (Representation.ofMulAction ℤ G X)).range.addSubgroupOf K := by
    ext f
    rw [AddMonoidHom.mem_ker, AddSubgroup.mem_addSubgroupOf]
    constructor
    · intro hf
      have hinv := coeff_smul_of_mem_ker hσ f.2
      have hdiv : ∀ x, (Nat.card (stabilizer G x) : ℤ) ∣ (f : MonoidAlgebra ℤ X).coeff x := by
        intro x
        have h1 := congrFun hf (Quotient.mk (orbitRel G X) x); rw [hΦ, Pi.zero_apply, ZMod.intCast_zmod_eq_zero_iff_dvd] at h1
        obtain ⟨g, hg⟩ := orbitPoint_mem (G := G) x
        have h2 : Quotient.out (Quotient.mk (orbitRel G X) x) = g • x := hg.symm; rw [h2, hinv] at h1; simp only [s, h2] at h1; rwa [card_stabilizer_eq_of_mem (mem_orbit x g)] at h1
      let H : X → ℤ := fun y =>
        if orbitPoint G y = y then (f : MonoidAlgebra ℤ X).coeff y / Nat.card (stabilizer G y)
        else 0
      have hH : ∀ y, H y ≠ 0 → orbitPoint G y = y := by intro y hy; by_contra h; exact hy (if_neg h)
      refine ⟨permOfFun H, ?_⟩
      ext p
      rw [coeff_normHom_ofMulAction]
      simp only [coeff_permOfFun]
      rw [sum_smul_eq_of_support H hH p]
      simp only [H, orbitPoint_orbitPoint, if_true]
      obtain ⟨g, hg⟩ := orbitPoint_mem (G := G) p
      have hgp : g • p = orbitPoint G p := hg; rw [card_stabilizer_eq_of_mem (orbitPoint_mem p), ← hgp, hinv, Int.mul_ediv_cancel' (hdiv p)]
    · rintro ⟨h, hh⟩
      funext ω
      rw [hΦ, Pi.zero_apply, ZMod.intCast_zmod_eq_zero_iff_dvd, ← hh, coeff_normHom_ofMulAction]
      exact card_stabilizer_dvd_sum _ _
  calc Nat.card (KerModRange (cycSub (Representation.ofMulAction ℤ G X) σ) (normHom (Representation.ofMulAction ℤ G X)))
      = Nat.card (K ⧸ Φ.ker) :=
        Nat.card_congr (QuotientAddGroup.quotientAddEquivOfEq hker.symm).toEquiv
    _ = Nat.card ((ω : orbitRel.Quotient G X) → ZMod (s ω)) :=
        Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective Φ hsurj).toEquiv
    _ = ∏ ω : orbitRel.Quotient G X, Nat.card (stabilizer G (Quotient.out ω)) := by
        rw [Nat.card_pi]
        simp only [Nat.card_zmod, s]
theorem cyclicHerbrand_ofMulAction [Fintype (orbitRel.Quotient G X)] (hσ : ∀ g, g ∈ Subgroup.zpowers σ) : cyclicHerbrand (Representation.ofMulAction ℤ G X) σ =
      ∏ ω : orbitRel.Quotient G X, (Nat.card (stabilizer G (Quotient.out ω)) : ℚ) := by
  rw [cyclicHerbrand, herbrandQuotient, natCard_kerModRange_cycSub_ofMulAction hσ, natCard_kerModRange_normHom_ofMulAction hσ, Nat.cast_one, div_one, Nat.cast_prod]
end Cohomology
section Quotient
variable {G : Type*} [Group G] [Fintype G]
end Quotient
end Sec_Permutation


/-! ### SUnitsKernel -/
section Sec_SUnitsKernel
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Module
open scoped NumberField nonZeroDivisors
variable {K : Type*} [Field K] [NumberField K]
namespace SUnit
theorem forall_valuation_eq_one_iff (x : Kˣ) : (∀ v : HeightOneSpectrum (𝓞 K), v.valuation K (x : K) = 1) ↔ x ∈ (Units.map (algebraMap (𝓞 K) K : 𝓞 K →* K)).range := by
  constructor
  · intro h
    obtain ⟨a, ha⟩ := mem_integers_of_valuation_le_one (R := 𝓞 K) K (x : K) fun v => (h v).le
    obtain ⟨b, hb⟩ := mem_integers_of_valuation_le_one (R := 𝓞 K) K ((x⁻¹ : Kˣ) : K) fun v => by
      rw [Units.val_inv_eq_inv_val, map_inv₀, h v, inv_one]
    have hab : a * b = 1 := by
      apply IsFractionRing.injective (𝓞 K) K
      rw [map_mul, ha, hb, map_one, Units.mul_inv]
    have hba : b * a = 1 := by rw [mul_comm, hab]
    refine ⟨⟨a, b, hab, hba⟩, ?_⟩
    ext
    simp [ha]
  · rintro ⟨u, rfl⟩ v
    rw [← valuationOfNeZero_eq, valuation_of_unit_eq, WithZero.coe_one]
variable (S : Set (HeightOneSpectrum (𝓞 K)))
def ofUnits : (𝓞 K)ˣ →* S.unit K where
  toFun u := ⟨Units.map (algebraMap (𝓞 K) K : 𝓞 K →* K) u, fun v _ =>
    (forall_valuation_eq_one_iff _).mpr ⟨u, rfl⟩ v⟩
  map_one' := by ext; simp
  map_mul' _ _ := by ext; simp
@[simp]
theorem coe_ofUnits (u : (𝓞 K)ˣ) : ((ofUnits S u : Kˣ) : K) = algebraMap (𝓞 K) K u := rfl
theorem ofUnits_injective : Function.Injective (ofUnits S (K := K)) := by
  intro u u' h
  have : ((ofUnits S u : Kˣ) : K) = ((ofUnits S u' : Kˣ) : K) := by rw [h]
  simp only [coe_ofUnits] at this
  exact Units.ext (IsFractionRing.injective (𝓞 K) K this)
def valuationVector : Additive (S.unit K) →ₗ[ℤ] (S → ℤ) :=
  AddMonoidHom.toIntLinearMap
    { toFun := fun x v => Multiplicative.toAdd (v.1.valuationOfNeZero ((x.toMul : S.unit K) : Kˣ))
      map_zero' := by funext v; simp
      map_add' := fun x y => by funext v; simp }
theorem valuationVector_apply (x : S.unit K) (v : S) : valuationVector S (Additive.ofMul x) v = Multiplicative.toAdd (v.1.valuationOfNeZero (x : Kˣ)) :=
  rfl
theorem mem_ker_valuationVector_iff (x : S.unit K) : Additive.ofMul x ∈ LinearMap.ker (valuationVector S) ↔ ∀ v : HeightOneSpectrum (𝓞 K), v.valuation K ((x : Kˣ) : K) = 1 := by
  rw [LinearMap.mem_ker]
  constructor
  · intro h v
    by_cases hv : v ∈ S
    · have h1 := congrFun h ⟨v, hv⟩
      rw [valuationVector_apply, Pi.zero_apply, toAdd_eq_zero] at h1
      rw [← valuationOfNeZero_eq, h1, WithZero.coe_one]
    · exact x.2 v hv
  · intro h
    funext v
    rw [valuationVector_apply, Pi.zero_apply, toAdd_eq_zero, ← WithZero.coe_inj, valuationOfNeZero_eq, WithZero.coe_one]
    exact h v.1
theorem ker_valuationVector : LinearMap.ker (valuationVector S) = LinearMap.range (ofUnits S).toAdditive.toIntLinearMap := by
  ext x
  rw [← ofMul_toMul x, mem_ker_valuationVector_iff, LinearMap.mem_range]
  constructor
  · intro h
    obtain ⟨u, hu⟩ := (forall_valuation_eq_one_iff _).mp h; exact ⟨Additive.ofMul u, by
      change Additive.ofMul (ofUnits S u) = _; congr 1; exact Subtype.ext hu⟩
  · rintro ⟨u, hu⟩
    have hx : ofUnits S u.toMul = x.toMul := congrArg Additive.toMul hu; rw [← hx]; exact (forall_valuation_eq_one_iff _).mpr ⟨u.toMul, rfl⟩
def unitsEquivKer : Additive (𝓞 K)ˣ ≃ₗ[ℤ] LinearMap.ker (valuationVector S) :=
  (LinearEquiv.ofInjective (ofUnits S).toAdditive.toIntLinearMap (ofUnits_injective S)).trans (LinearEquiv.ofEq _ _ (ker_valuationVector S).symm)
end SUnit
end Sec_SUnitsKernel


/-! ### SUnits -/
section Sec_SUnits
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Module
open scoped NumberField nonZeroDivisors
variable {K : Type*} [Field K] [NumberField K]
namespace SUnit
theorem exists_pow_classNumber_eq_span (v : HeightOneSpectrum (𝓞 K)) : ∃ a : 𝓞 K, a ≠ 0 ∧ v.asIdeal ^ classNumber K = Ideal.span {a} := by
  let I : (Ideal (𝓞 K))⁰ := ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩
  have h1 : ClassGroup.mk0 (I ^ classNumber K) = 1 := by
    rw [map_pow, classNumber, Fintype.card_eq_nat_card]
    exact pow_card_eq_one'
  have h2 := (ClassGroup.mk0_eq_one_iff (I ^ classNumber K).2).mp h1
  obtain ⟨a, ha⟩ := h2.principal
  have ha' : v.asIdeal ^ classNumber K = Ideal.span {a} := by
    rw [SubmonoidClass.coe_pow] at ha
    exact ha
  refine ⟨a, ?_, ha'⟩
  rintro rfl; rw [Ideal.span_singleton_eq_bot.mpr rfl] at ha'; exact pow_ne_zero _ v.ne_bot ha'
open scoped Classical in
theorem intValuation_of_pow_eq_span {v w : HeightOneSpectrum (𝓞 K)} {a : 𝓞 K} (ha : a ≠ 0) {n : ℕ} (h : v.asIdeal ^ n = Ideal.span {a}) :
    w.intValuation a = if w = v then WithZero.exp (-(n : ℤ)) else 1 := by
  rw [intValuation_eq_exp_neg_multiplicity w ha, ← h]
  split_ifs with hw
  · subst hw
    rw [multiplicity_pow_self_of_prime w.prime n]
  · have h0 : multiplicity w.asIdeal (v.asIdeal ^ n) = 0 := by
      rw [multiplicity_eq_zero]
      intro hdvd; apply hw
      have hle : v.asIdeal ≤ w.asIdeal := Ideal.le_of_dvd (w.prime.dvd_of_dvd_pow hdvd); exact HeightOneSpectrum.ext (v.isMaximal.eq_of_le w.isPrime.ne_top hle).symm
    rw [h0]
    simp
def placeUnit (v : HeightOneSpectrum (𝓞 K)) : Kˣ :=
  Units.mk0 (algebraMap (𝓞 K) K (exists_pow_classNumber_eq_span v).choose) <| by
    rw [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 K) K)]
    exact (exists_pow_classNumber_eq_span v).choose_spec.1
open scoped Classical in
theorem valuationOfNeZero_placeUnit (v w : HeightOneSpectrum (𝓞 K)) : w.valuationOfNeZero (placeUnit v) = if w = v then Multiplicative.ofAdd (-(classNumber K : ℤ)) else 1 := by
  rw [← WithZero.coe_inj, valuationOfNeZero_eq, placeUnit, Units.val_mk0, valuation_of_algebraMap, intValuation_of_pow_eq_span (exists_pow_classNumber_eq_span v).choose_spec.1 (exists_pow_classNumber_eq_span v).choose_spec.2]
  split_ifs <;> rfl
variable (S : Set (HeightOneSpectrum (𝓞 K)))
theorem placeUnit_mem {v : HeightOneSpectrum (𝓞 K)} (hv : v ∈ S) : placeUnit v ∈ S.unit K := by
  intro w hw
  have hwv : w ≠ v := fun h => hw (h ▸ hv); rw [← valuationOfNeZero_eq, valuationOfNeZero_placeUnit, if_neg hwv, WithZero.coe_one]
open scoped Classical in
theorem valuationVector_placeUnit (v : S) : valuationVector S (Additive.ofMul ⟨placeUnit v.1, placeUnit_mem S v.2⟩) = Pi.single v (-(classNumber K : ℤ)) := by
  funext w
  rw [valuationVector_apply, valuationOfNeZero_placeUnit]
  by_cases h : w = v
  · subst h; simp
  · have h' : w.1 ≠ v.1 := fun e => h (Subtype.ext e)
    simp [h, h']
theorem valuation_eq_one_of_isOfFinOrder {x : Kˣ} (hx : IsOfFinOrder x)
    (v : HeightOneSpectrum (𝓞 K)) : v.valuation K (x : K) = 1 := by
  have h := v.valuationOfNeZero.isOfFinOrder hx; rw [isOfFinOrder_iff_eq_one] at h; rw [← valuationOfNeZero_eq, h, WithZero.coe_one]
def torsionEquiv : Units.torsion K ≃* CommGroup.torsion (S.unit K) :=
  MulEquiv.ofBijective
    ({ toFun := fun ζ => ⟨ofUnits S ζ, (ofUnits S).isOfFinOrder ζ.2⟩
       map_one' := Subtype.ext (map_one (ofUnits S))
       map_mul' := fun a b => Subtype.ext (map_mul (ofUnits S) (a : (𝓞 K)ˣ) b) } : Units.torsion K →* CommGroup.torsion (S.unit K)) <| by
    constructor
    · intro a b h
      exact Subtype.ext (ofUnits_injective S (congrArg Subtype.val h))
    · rintro ⟨x, hx⟩
      have hx' : IsOfFinOrder (x : Kˣ) := (S.unit K).subtype.isOfFinOrder hx
      obtain ⟨u, hu⟩ :=
        (forall_valuation_eq_one_iff (x : Kˣ)).mp (valuation_eq_one_of_isOfFinOrder hx')
      have hux : ofUnits S u = x := Subtype.ext hu; refine ⟨⟨u, ?_⟩, Subtype.ext hux⟩; change u ∈ CommGroup.torsion _
      rw [CommGroup.mem_torsion, ← orderOf_pos_iff, ← orderOf_injective (ofUnits S) (ofUnits_injective S), hux, orderOf_pos_iff]
      exact hx
instance : Finite (CommGroup.torsion (S.unit K)) :=
  Finite.of_equiv _ (torsionEquiv S).toEquiv
instance : IsCyclic (CommGroup.torsion (S.unit K)) :=
  isCyclic_of_surjective (torsionEquiv S).toMonoidHom (torsionEquiv S).surjective
variable [Finite S]
def placeUnitsMap : (S → ℤ) →ₗ[ℤ] Additive (S.unit K) :=
  (Pi.basisFun ℤ S).constr ℤ fun v => Additive.ofMul ⟨placeUnit v.1, placeUnit_mem S v.2⟩
theorem valuationVector_comp_placeUnitsMap : valuationVector S ∘ₗ placeUnitsMap S = (-(classNumber K : ℤ)) • LinearMap.id := by
  classical
  refine (Pi.basisFun ℤ S).ext fun v => ?_
  rw [LinearMap.comp_apply, placeUnitsMap, Basis.constr_basis, valuationVector_placeUnit, LinearMap.smul_apply, LinearMap.id_apply, Pi.basisFun_apply]
  rw [← Pi.single_smul, smul_eq_mul, mul_one]
theorem finrank_range_valuationVector : finrank ℤ (LinearMap.range (valuationVector S)) = Nat.card S := by
  have : Fintype S := Fintype.ofFinite S; apply le_antisymm
  · calc finrank ℤ (LinearMap.range (valuationVector S)) ≤ finrank ℤ (S → ℤ) :=
          Submodule.finrank_le _
      _ = Nat.card S := by rw [Module.finrank_fintype_fun_eq_card, Fintype.card_eq_nat_card]
  · have hinj : Function.Injective (valuationVector S ∘ₗ placeUnitsMap S) := by
      rw [valuationVector_comp_placeUnitsMap]
      intro c d hcd
      have hh : (-(classNumber K : ℤ)) ≠ 0 := by simpa using classNumber_ne_zero K
      exact smul_right_injective (S → ℤ) hh hcd
    calc Nat.card S = finrank ℤ (S → ℤ) := by
          rw [Module.finrank_fintype_fun_eq_card, Fintype.card_eq_nat_card]
      _ = finrank ℤ (LinearMap.range (valuationVector S ∘ₗ placeUnitsMap S)) :=
          (LinearMap.finrank_range_of_inj hinj).symm
      _ ≤ finrank ℤ (LinearMap.range (valuationVector S)) :=
          Submodule.finrank_mono (LinearMap.range_comp_le_range _ _)
instance : Module.Finite ℤ (Additive (S.unit K)) := by
  rw [Module.finite_def]
  refine Submodule.fg_of_fg_map_of_fg_inf_ker (valuationVector S) ?_ ?_
  · exact IsNoetherian.noetherian _
  · rw [inf_of_le_right le_top, ← Module.Finite.iff_fg]
    exact Module.Finite.equiv (unitsEquivKer S)
theorem fg : Group.FG (S.unit K) := by
  rw [Group.fg_iff_monoid_fg, Monoid.fg_iff_add_fg, ← AddGroup.fg_iff_addMonoid_fg, ← Module.Finite.iff_addGroup_fg]
  infer_instance
instance : Group.FG (S.unit K) := fg S
theorem finrank_eq : finrank ℤ (Additive (S.unit K)) = Units.rank K + Nat.card S := by
  rw [← Submodule.finrank_quotient_add_finrank (LinearMap.ker (valuationVector S)), LinearEquiv.finrank_eq (valuationVector S).quotKerEquivRange, finrank_range_valuationVector, ← LinearEquiv.finrank_eq (unitsEquivKer S),
    Units.finrank_eq, add_comm]
end SUnit
end Sec_SUnits


/-! ### SUnitsExact -/
section Sec_SUnitsExact
open RHDirect.Stage13CFT_IdeleNormResidue
variable {G A B C : Type*} [Group G] [Fintype G] [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
theorem hasHerbrandQuotient_cycSubOne_of_finite [Module.Finite ℤ A] (ρ : Representation ℤ G A) {σ : G} (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    HasHerbrandQuotient (cycSubOne ρ σ) (cycNorm ρ) :=
  hasCyclicHerbrand_of_finite ρ hσ
theorem cycHerbrand_eq_mul_of_exact (ρA : Representation ℤ G A) (ρB : Representation ℤ G B) (ρC : Representation ℤ G C) (σ : G) {i : A →+ B} {p : B →+ C} (hi : Function.Injective i) (hex : Function.Exact i p) [Finite (C ⧸ p.range)]
    (hiG : ∀ g a, i (ρA g a) = ρB g (i a)) (hpG : ∀ g b, p (ρB g b) = ρC g (p b))
    (hA : HasHerbrandQuotient (cycSubOne ρA σ) (cycNorm ρA))
    (hC : HasHerbrandQuotient (cycSubOne ρC σ) (cycNorm ρC)) :
    cycHerbrand ρB σ = cycHerbrand ρA σ * cycHerbrand ρC σ := by
  have hfS : ∀ x ∈ p.range, cycSubOne ρC σ x ∈ p.range := by rintro _ ⟨b, rfl⟩; exact ⟨cycSubOne ρB σ b, by rw [cycSubOne_apply, cycSubOne_apply, map_sub, hpG]⟩
  have hgS : ∀ x ∈ p.range, cycNorm ρC x ∈ p.range := by rintro _ ⟨b, rfl⟩; exact ⟨cycNorm ρB b, by rw [cycNorm_apply, cycNorm_apply, map_sum]; simp only [hpG]⟩
  have : p.range.FiniteIndex := AddSubgroup.finiteIndex_of_finite_quotient
  have hR := (hasHerbrandQuotient_restrictEnd_iff p.range hfS hgS (cycSubOne_cycNorm ρC σ) (cycNorm_cycSubOne ρC σ)).2 hC
  have hex' : Function.Exact i p.rangeRestrict := by
    intro b; rw [← hex b]; constructor
    · intro h
      simpa using congrArg Subtype.val h
    · intro h
      exact Subtype.ext (by simpa using h)
  rw [cycHerbrand, cycHerbrand, cycHerbrand, ← herbrandQuotient_restrictEnd p.range hfS hgS (cycSubOne_cycNorm ρC σ) (cycNorm_cycSubOne ρC σ)]
  exact herbrandQuotient_eq_mul_of_shortExact hi p.rangeRestrict_surjective hex' (fun a => by rw [cycSubOne_apply, cycSubOne_apply, map_sub, hiG]) (fun a => by rw [cycNorm_apply, cycNorm_apply, map_sum]; simp only [hiG])
    (fun b => Subtype.ext (by simp [cycSubOne_apply, hpG]))
    (fun b => Subtype.ext (by simp [cycNorm_apply, hpG, map_sum]))
    (cycSubOne_cycNorm ρB σ) (cycNorm_cycSubOne ρB σ) hA hR
theorem cycHerbrand_eq_of_surjective_of_finite_ker (ρB : Representation ℤ G B) (ρC : Representation ℤ G C) (σ : G) {p : B →+ C} (hp : Function.Surjective p) [Finite p.ker] (hpG : ∀ g b, p (ρB g b) = ρC g (p b))
    (hC : HasHerbrandQuotient (cycSubOne ρC σ) (cycNorm ρC)) :
    cycHerbrand ρB σ = cycHerbrand ρC σ := by
  have hfK : ∀ x ∈ p.ker, cycSubOne ρB σ x ∈ p.ker := by intro x hx; rw [AddMonoidHom.mem_ker] at hx ⊢; rw [cycSubOne_apply, map_sub, hpG, hx, map_zero, sub_zero]
  have hgK : ∀ x ∈ p.ker, cycNorm ρB x ∈ p.ker := by intro x hx; rw [AddMonoidHom.mem_ker] at hx ⊢; rw [cycNorm_apply, map_sum]; simp [hpG, hx]
  have hfgK : ∀ x, restrictEnd (cycSubOne ρB σ) p.ker hfK
      (restrictEnd (cycNorm ρB) p.ker hgK x) = 0 := fun x =>
    Subtype.ext (by simp [cycSubOne_cycNorm])
  have hgfK : ∀ x, restrictEnd (cycNorm ρB) p.ker hgK
      (restrictEnd (cycSubOne ρB σ) p.ker hfK x) = 0 := fun x =>
    Subtype.ext (by simp [cycNorm_cycSubOne])
  have hA : HasHerbrandQuotient (restrictEnd (cycSubOne ρB σ) p.ker hfK)
      (restrictEnd (cycNorm ρB) p.ker hgK) := hasHerbrandQuotient_of_finite _ _
  have hex : Function.Exact p.ker.subtype p := by intro b; simp
  rw [cycHerbrand, cycHerbrand, herbrandQuotient_eq_mul_of_shortExact p.ker.subtype_injective hp hex (fun _ => rfl) (fun _ => rfl) (fun b => by rw [cycSubOne_apply, cycSubOne_apply, map_sub, hpG])
      (fun b => by rw [cycNorm_apply, cycNorm_apply, map_sum]; simp only [hpG])
      (cycSubOne_cycNorm ρB σ) (cycNorm_cycSubOne ρB σ) hA hC,
    herbrandQuotient_eq_one_of_finite hfgK hgfK, one_mul]
theorem cycHerbrand_prod (ρA : Representation ℤ G A) (ρB : Representation ℤ G B) (σ : G) (hA : HasHerbrandQuotient (cycSubOne ρA σ) (cycNorm ρA)) (hB : HasHerbrandQuotient (cycSubOne ρB σ) (cycNorm ρB)) :
    cycHerbrand (ρA.prod ρB) σ = cycHerbrand ρA σ * cycHerbrand ρB σ := by
  have : Finite (B ⧸ (AddMonoidHom.snd A B).range) := by
    rw [AddMonoidHom.range_eq_top.2 (fun b => ⟨(0, b), rfl⟩)]
    infer_instance
  refine cycHerbrand_eq_mul_of_exact ρA (ρA.prod ρB) ρB σ (i := AddMonoidHom.inl A B)
    (p := AddMonoidHom.snd A B) (fun a a' h => congrArg Prod.fst h) ?_ (fun g a => ?_)
    (fun g b => rfl) hA hB
  · rintro ⟨a, b⟩
    simp only [AddMonoidHom.coe_snd, Set.mem_range, AddMonoidHom.inl_apply, Prod.ext_iff]
    constructor
    · rintro rfl
      exact ⟨a, rfl, rfl⟩
    · rintro ⟨a', -, rfl⟩
      rfl
  · exact Prod.ext rfl (map_zero (ρB g)).symm
end Sec_SUnitsExact


/-! ### SUnitsPerm -/
section Sec_SUnitsPerm
open MulAction NumberField IsDedekindDomain
open scoped Pointwise
section FunPerm
variable (k G X : Type*) [CommRing k] [Group G] [MulAction G X]
def funPermRep : Representation k G (X → k) where
  toFun g := LinearMap.funLeft k k (fun x => g⁻¹ • x)
  map_one' := by
    ext f x
    simp [LinearMap.funLeft_apply]
  map_mul' g h := by
    ext f x
    simp [LinearMap.funLeft_apply, mul_smul]
variable {k G X}
@[simp]
theorem funPermRep_apply (g : G) (f : X → k) (x : X) : funPermRep k G X g f x = f (g⁻¹ • x) :=
  rfl
def funEquivMonoidAlgebra [Finite X] : (X → ℤ) ≃+ MonoidAlgebra ℤ X where
  toFun := permOfFun
  invFun f x := f.coeff x
  left_inv F := funext fun x => coeff_permOfFun F x
  right_inv f := by
    ext x
    exact coeff_permOfFun _ x
  map_add' F F' := by
    ext x
    simp
theorem funEquivMonoidAlgebra_funPermRep [Finite X] (g : G) (F : X → ℤ) : funEquivMonoidAlgebra (funPermRep ℤ G X g F) = Representation.ofMulAction ℤ G X g (funEquivMonoidAlgebra F) := by
  ext x
  change (permOfFun _).coeff x = _; rw [coeff_permOfFun, Representation.coeff_ofMulAction]; change _ = (permOfFun F).coeff _; rw [coeff_permOfFun, funPermRep_apply]
theorem cycHerbrand_funPermRep [Fintype G] [Finite X] [Fintype (orbitRel.Quotient G X)] {σ : G} (hσ : ∀ g, g ∈ Subgroup.zpowers σ) : cycHerbrand (funPermRep ℤ G X) σ =
      ∏ ω : orbitRel.Quotient G X, (Nat.card (stabilizer G (Quotient.out ω)) : ℚ) := by
  rw [cycHerbrand_congr funEquivMonoidAlgebra funEquivMonoidAlgebra_funPermRep σ, ← cyclicHerbrand_eq_cycHerbrand, cyclicHerbrand_ofMulAction hσ]
end FunPerm
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
section Infinite
omit [NumberField L] in
open scoped Classical in
theorem prod_card_stabilizer_infinitePlace [Fintype (orbitRel.Quotient (L ≃ₐ[K] L) (InfinitePlace L))] : ∏ ω : orbitRel.Quotient (L ≃ₐ[K] L) (InfinitePlace L), (Nat.card (stabilizer (L ≃ₐ[K] L) (Quotient.out ω)) : ℚ) =
      ∏ v : InfinitePlace K, (if v.IsUnramifiedIn L then 1 else 2 : ℚ) := by
  classical
  refine Fintype.prod_equiv InfinitePlace.orbitRelEquiv _ _ fun ω => ?_
  have h1 : InfinitePlace.orbitRelEquiv ω = (Quotient.out ω).comap (algebraMap K L) := by
    conv_lhs => rw [← Quotient.out_eq ω]
    rfl
  rw [h1, InfinitePlace.card_stabilizer, InfinitePlace.isUnramifiedIn_comap]
  split_ifs <;> simp
end Infinite
section Finite
def placeBelow (w : HeightOneSpectrum (𝓞 L)) : HeightOneSpectrum (𝓞 K) :=
  ⟨w.asIdeal.under (𝓞 K), inferInstance, Ideal.under_ne_bot (𝓞 K) w.ne_bot⟩
instance (w : HeightOneSpectrum (𝓞 L)) : w.asIdeal.LiesOver (placeBelow (K := K) w).asIdeal :=
  ⟨rfl⟩
omit [NumberField K] [NumberField L] [IsGalois K L] in
theorem eq_placeBelow_of_liesOver {w : HeightOneSpectrum (𝓞 L)} {v : HeightOneSpectrum (𝓞 K)}
    (h : w.asIdeal.LiesOver v.asIdeal) : v = placeBelow w :=
  HeightOneSpectrum.ext h.over
omit [NumberField K] [NumberField L] [IsGalois K L] in
theorem placeBelow_smul (g : L ≃ₐ[K] L) (w : HeightOneSpectrum (𝓞 L)) : placeBelow (K := K) (g • w) = placeBelow w := by
  symm
  apply eq_placeBelow_of_liesOver
  change ((g • w.asIdeal : Ideal (𝓞 L))).LiesOver _; infer_instance
variable (S : Set (HeightOneSpectrum (𝓞 L)))
@[reducible] def stableMulAction (hS : ∀ (g : L ≃ₐ[K] L), ∀ w ∈ S, g • w ∈ S) : MulAction (L ≃ₐ[K] L) S where
  smul g w := ⟨g • w.1, hS g w.1 w.2⟩
  one_smul w := Subtype.ext (one_smul _ w.1)
  mul_smul g h w := Subtype.ext (mul_smul g h w.1)
theorem prod_card_stabilizer_finitePlace (hS : ∀ (g : L ≃ₐ[K] L), ∀ w ∈ S, g • w ∈ S) : letI := stableMulAction S hS
    ∀ [Fintype (orbitRel.Quotient (L ≃ₐ[K] L) S)],
    ∏ ω : orbitRel.Quotient (L ≃ₐ[K] L) S, (Nat.card (stabilizer (L ≃ₐ[K] L) (Quotient.out ω)) : ℚ) = ∏ᶠ (v : HeightOneSpectrum (𝓞 K)) (_ : ∃ w ∈ S, w.asIdeal.LiesOver v.asIdeal),
        ((v.asIdeal.ramificationIdxIn (𝓞 L) * v.asIdeal.inertiaDegIn (𝓞 L) : ℕ) : ℚ) := by
  let := stableMulAction S hS; intro _
  have hstab : ∀ x : S, Nat.card (stabilizer (L ≃ₐ[K] L) x) =
      (placeBelow (K := K) x.1).asIdeal.ramificationIdxIn (𝓞 L) *
        (placeBelow (K := K) x.1).asIdeal.inertiaDegIn (𝓞 L) := by
    intro x
    have h1 : stabilizer (L ≃ₐ[K] L) x = stabilizer (L ≃ₐ[K] L) x.1.asIdeal := by
      ext g
      rw [mem_stabilizer_iff, mem_stabilizer_iff, Subtype.ext_iff]
      exact ⟨fun h => congrArg HeightOneSpectrum.asIdeal h, fun h => HeightOneSpectrum.ext h⟩
    rw [h1]
    exact Ideal.card_stabilizer_eq (placeBelow (K := K) x.1).asIdeal x.1.asIdeal
  rw [← finprod_eq_prod_of_fintype, ← finprod_mem_univ]
  refine finprod_mem_eq_of_bijOn (fun ω => placeBelow (K := K) (Quotient.out ω).1) ⟨?_, ?_, ?_⟩ fun ω _ => by rw [hstab]
  · intro ω _
    exact ⟨(Quotient.out ω).1, (Quotient.out ω).2, inferInstance⟩
  · intro ω₁ _ ω₂ _ h
    simp only at h
    set x₁ := Quotient.out ω₁
    set x₂ := Quotient.out ω₂
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (L ≃ₐ[K] L)
      (⟨x₂.1, inferInstance⟩ : SemiLocal.PlacesOver L (placeBelow (K := K) x₂.1))
      ⟨x₁.1, by rw [← h]; infer_instance⟩
    rw [← Quotient.out_eq ω₁, ← Quotient.out_eq ω₂]
    have hg' : g • x₂.1 = x₁.1 := congrArg Subtype.val hg; exact Quotient.sound ⟨g, Subtype.ext hg'⟩
  · rintro v ⟨w, hw, hlies⟩
    refine ⟨Quotient.mk _ ⟨w, hw⟩, Set.mem_univ _, ?_⟩
    obtain ⟨g, hg⟩ : Quotient.out (Quotient.mk (orbitRel (L ≃ₐ[K] L) S) ⟨w, hw⟩) ∈
        orbit (L ≃ₐ[K] L) (⟨w, hw⟩ : S) :=
      Quotient.exact (Quotient.out_eq (Quotient.mk (orbitRel (L ≃ₐ[K] L) S) ⟨w, hw⟩))
    simp only
    rw [← hg]
    change placeBelow (g • w) = v; rw [placeBelow_smul, ← eq_placeBelow_of_liesOver hlies]
end Finite
end Sec_SUnitsPerm


/-! ### SUnitsRep -/
section Sec_SUnitsRep
open NumberField IsDedekindDomain NumberField.Units
open scoped Pointwise
variable {K L : Type*} [Field K] [Field L] [Algebra K L]
section Units
variable [NumberField L]
def unitsMap (g : L ≃ₐ[K] L) : (𝓞 L)ˣ →* (𝓞 L)ˣ :=
  Units.map (MulSemiringAction.toRingHom (L ≃ₐ[K] L) (𝓞 L) g : 𝓞 L →* 𝓞 L)
variable (K L) in
def unitsRep : Representation ℤ (L ≃ₐ[K] L) (Additive (𝓞 L)ˣ) where
  toFun g := (unitsMap g).toAdditive.toIntLinearMap
  map_one' := by
    refine LinearMap.ext fun u => ?_
    apply Additive.toMul.injective
    apply Units.ext
    apply RingOfIntegers.ext
    rfl
  map_mul' g h := by
    refine LinearMap.ext fun u => ?_
    apply Additive.toMul.injective
    apply Units.ext
    apply RingOfIntegers.ext
    rfl
omit [NumberField L] in
theorem unitsRep_apply (g : L ≃ₐ[K] L) (u : Additive (𝓞 L)ˣ) : unitsRep K L g u = Additive.ofMul (unitsMap g u.toMul) :=
  rfl
end Units
section SUnits
variable [NumberField L] (S : Set (HeightOneSpectrum (𝓞 L)))
theorem map_mem_unit (hS : ∀ (g : L ≃ₐ[K] L), ∀ w ∈ S, g • w ∈ S) (g : L ≃ₐ[K] L) {x : Lˣ}
    (hx : x ∈ S.unit L) : Units.map (g : L →+* L).toMonoidHom x ∈ S.unit L := by
  intro w hw
  have hw' : g⁻¹ • w ∉ S := fun h => hw (by simpa using hS g _ h)
  have h1 := SemiLocal.valuation_smul g (g⁻¹ • w) (x : L); rw [smul_inv_smul] at h1; change w.valuation L (g (x : L)) = 1; rw [h1]; exact hx _ hw'
def sUnitMap (hS : ∀ (g : L ≃ₐ[K] L), ∀ w ∈ S, g • w ∈ S) (g : L ≃ₐ[K] L) : S.unit L →* S.unit L :=
  ((Units.map (g : L →+* L).toMonoidHom).comp (S.unit L).subtype).codRestrict (S.unit L) fun x => map_mem_unit S hS g x.2
theorem coe_sUnitMap (hS : ∀ (g : L ≃ₐ[K] L), ∀ w ∈ S, g • w ∈ S) (g : L ≃ₐ[K] L) (x : S.unit L) : (((sUnitMap S hS g x : S.unit L) : Lˣ) : L) = g ((x : Lˣ) : L) :=
  rfl
def sUnitRep (hS : ∀ (g : L ≃ₐ[K] L), ∀ w ∈ S, g • w ∈ S) : Representation ℤ (L ≃ₐ[K] L) (Additive (S.unit L)) where
  toFun g := (sUnitMap S hS g).toAdditive.toIntLinearMap
  map_one' := by
    refine LinearMap.ext fun x => ?_
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Units.ext
    rfl
  map_mul' g h := by
    refine LinearMap.ext fun x => ?_
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Units.ext
    rfl
theorem sUnitRep_apply (hS : ∀ (g : L ≃ₐ[K] L), ∀ w ∈ S, g • w ∈ S) (g : L ≃ₐ[K] L) (x : Additive (S.unit L)) : sUnitRep S hS g x = Additive.ofMul (sUnitMap S hS g x.toMul) :=
  rfl
theorem ofUnits_unitsRep (hS : ∀ (g : L ≃ₐ[K] L), ∀ w ∈ S, g • w ∈ S) (g : L ≃ₐ[K] L) (u : Additive (𝓞 L)ˣ) : (SUnit.ofUnits S).toAdditive (unitsRep K L g u) = sUnitRep S hS g ((SUnit.ofUnits S).toAdditive u) := by
  apply Additive.toMul.injective
  apply Subtype.ext
  apply Units.ext
  rfl
theorem valuationVector_sUnitRep (hS : ∀ (g : L ≃ₐ[K] L), ∀ w ∈ S, g • w ∈ S) (g : L ≃ₐ[K] L) (x : Additive (S.unit L)) : letI := stableMulAction S hS
    SUnit.valuationVector S (sUnitRep S hS g x) =
      funPermRep ℤ (L ≃ₐ[K] L) S g (SUnit.valuationVector S x) := by
  let := stableMulAction S hS; funext w; rw [funPermRep_apply, ← ofMul_toMul x, sUnitRep_apply, toMul_ofMul, SUnit.valuationVector_apply, SUnit.valuationVector_apply]; congr 1
  rw [← WithZero.coe_inj, HeightOneSpectrum.valuationOfNeZero_eq, HeightOneSpectrum.valuationOfNeZero_eq, coe_sUnitMap]
  have h1 := SemiLocal.valuation_smul g (g⁻¹ • w.1) ((x.toMul : Lˣ) : L); rw [smul_inv_smul] at h1; exact h1
end SUnits
end Sec_SUnitsRep


/-! ### UnitsHerbrand -/
section Sec_UnitsHerbrand
open NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem NumberField.InfinitePlace
  MulAction Module
open scoped TensorProduct
section Log
open scoped Classical
variable (L : Type*) [Field L] [NumberField L]
def fullLog : Additive (𝓞 L)ˣ →+ (InfinitePlace L → ℝ) where
  toFun x w := (w.mult : ℝ) * Real.log (w (algebraMap (𝓞 L) L (x.toMul : 𝓞 L)))
  map_zero' := by
    funext w
    simp
  map_add' x y := by
    funext w
    simp only [toMul_add, Units.val_mul, map_mul, Pi.add_apply]
    rw [Real.log_mul (pos_at_place _ w).ne' (pos_at_place _ w).ne', mul_add]
omit [NumberField L] in
theorem fullLog_apply (x : Additive (𝓞 L)ˣ) (w : InfinitePlace L) : fullLog L x w = (w.mult : ℝ) * Real.log (w (algebraMap (𝓞 L) L (x.toMul : 𝓞 L))) :=
  rfl
theorem sum_fullLog (x : Additive (𝓞 L)ˣ) : ∑ w, fullLog L x w = 0 :=
  sum_mult_mul_log x.toMul
def logLattice : Submodule ℤ (InfinitePlace L → ℝ) :=
  LinearMap.range (fullLog L).toIntLinearMap
def logProj : (InfinitePlace L → ℝ) →ₗ[ℝ] logSpace L :=
  LinearMap.funLeft ℝ ℝ Subtype.val
theorem logProj_fullLog (x : Additive (𝓞 L)ˣ) : logProj L (fullLog L x) = logEmbedding L x :=
  rfl
theorem fullLog_eq_zero_iff (x : Additive (𝓞 L)ˣ) : fullLog L x = 0 ↔ x.toMul ∈ torsion L := by
  constructor
  · intro h
    rw [← logEmbedding_eq_zero_iff, ofMul_toMul, ← logProj_fullLog, h, map_zero]
  · intro h
    rw [mem_torsion] at h
    funext w
    rw [fullLog_apply, h w, Real.log_one, mul_zero, Pi.zero_apply]
theorem logProj_mem_unitLattice (m : logLattice L) : logProj L m ∈ unitLattice L := by obtain ⟨x, hx⟩ := m.2; rw [← hx]; exact ⟨x, trivial, rfl⟩
def logLatticeEquiv : logLattice L ≃ₗ[ℤ] unitLattice L :=
  LinearEquiv.ofBijective (LinearMap.codRestrict (unitLattice L) ((logProj L).restrictScalars ℤ ∘ₗ (logLattice L).subtype) (logProj_mem_unitLattice L)) <| by
    constructor
    · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro m hm
      obtain ⟨x, hx⟩ := m.2
      have h1 : logEmbedding L x = 0 := by
        rw [← logProj_fullLog]
        have := congrArg Subtype.val hm; simp only [ZeroMemClass.coe_zero] at this; change logProj L (fullLog L x) = 0; rw [show fullLog L x = (m : InfinitePlace L → ℝ) from hx]; exact this
      rw [← ofMul_toMul x, logEmbedding_eq_zero_iff, ← fullLog_eq_zero_iff] at h1
      apply Subtype.ext
      rw [← hx]
      exact h1
    · rintro ⟨y, x, -, rfl⟩
      exact ⟨⟨fullLog L x, x, rfl⟩, rfl⟩
instance : Module.Free ℤ (logLattice L) :=
  have := ZLattice.module_free ℝ (unitLattice L); Module.Free.of_equiv (logLatticeEquiv L).symm
instance : Module.Finite ℤ (logLattice L) :=
  have := ZLattice.module_finite ℝ (unitLattice L); Module.Finite.equiv (logLatticeEquiv L).symm
theorem finrank_logLattice : finrank ℤ (logLattice L) = rank L :=
  (logLatticeEquiv L).finrank_eq.trans (unitLattice_rank L)
theorem linearIndependent_logLattice_basis {ι : Type*} (b : Basis ι ℤ (logLattice L)) :
    LinearIndependent ℝ (fun i => (b i : InfinitePlace L → ℝ)) := by
  apply LinearIndependent.of_comp (logProj L)
  have := ((b.map (logLatticeEquiv L)).ofZLatticeBasis ℝ (unitLattice L)).linearIndependent; convert this using 1
  · funext i
    rw [Basis.ofZLatticeBasis_apply, Basis.map_apply]
    rfl
  all_goals rfl
end Log
section Galois
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
omit [NumberField K] [NumberField L] in
theorem mult_smul (g : L ≃ₐ[K] L) (w : InfinitePlace L) : (g • w).mult = w.mult := by
  have := isReal_smul_iff (σ := g) (w := w); unfold mult; split_ifs with h1 h2 h2
  · rfl
  · exact absurd (this.mp h1) h2
  · exact absurd (this.mpr h2) h1
  · rfl
omit [NumberField K] [NumberField L] in
theorem fullLog_unitsRep (g : L ≃ₐ[K] L) (x : Additive (𝓞 L)ˣ) : fullLog L (unitsRep K L g x) = funPermRep ℝ (L ≃ₐ[K] L) (InfinitePlace L) g (fullLog L x) := by
  funext w
  rw [funPermRep_apply, fullLog_apply, fullLog_apply, mult_smul, unitsRep_apply, toMul_ofMul, InfinitePlace.smul_apply, AlgEquiv.aut_inv, AlgEquiv.symm_symm]
  rfl
omit [NumberField K] [NumberField L] in
theorem funPermRep_mem_logLattice (g : L ≃ₐ[K] L) {m : InfinitePlace L → ℝ}
    (hm : m ∈ logLattice L) : funPermRep ℝ (L ≃ₐ[K] L) (InfinitePlace L) g m ∈ logLattice L := by
  obtain ⟨x, rfl⟩ := hm; exact ⟨unitsRep K L g x, fullLog_unitsRep g x⟩
variable (K L) in
def logLatticeRep : Representation ℤ (L ≃ₐ[K] L) (logLattice L) where
  toFun g := ((funPermRep ℝ (L ≃ₐ[K] L) (InfinitePlace L) g).restrictScalars ℤ).restrict fun _ hm => funPermRep_mem_logLattice g hm
  map_one' := by
    refine LinearMap.ext fun m => Subtype.ext ?_
    funext w
    change (m : InfinitePlace L → ℝ) ((1 : L ≃ₐ[K] L)⁻¹ • w) = (m : InfinitePlace L → ℝ) w; rw [inv_one, one_smul]
  map_mul' g h := by
    refine LinearMap.ext fun m => Subtype.ext ?_
    funext w
    change (m : InfinitePlace L → ℝ) ((g * h)⁻¹ • w) = (m : InfinitePlace L → ℝ) (h⁻¹ • g⁻¹ • w); rw [mul_inv_rev, mul_smul]
omit [NumberField K] [NumberField L] in
theorem coe_logLatticeRep (g : L ≃ₐ[K] L) (m : logLattice L) : (logLatticeRep K L g m : InfinitePlace L → ℝ) = funPermRep ℝ (L ≃ₐ[K] L) (InfinitePlace L) g m :=
  rfl
variable [FiniteDimensional K L]
omit [NumberField K] in
theorem cycHerbrand_unitsRep_eq_logLattice {σ : L ≃ₐ[K] L} (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    cycHerbrand (unitsRep K L) σ = cycHerbrand (logLatticeRep K L) σ := by
  let p : Additive (𝓞 L)ˣ →+ logLattice L := (fullLog L).toIntLinearMap.rangeRestrict.toAddMonoidHom
  have hp : Function.Surjective p := (fullLog L).toIntLinearMap.surjective_rangeRestrict
  have : Finite p.ker := by
    refine Finite.of_injective (β := torsion L) (fun x => ⟨(x : Additive (𝓞 L)ˣ).toMul, (fullLog_eq_zero_iff L x).1 ?_⟩) ?_
    · have := congrArg Subtype.val (AddMonoidHom.mem_ker.1 x.2)
      exact this
    · intro x y h
      simp only [Subtype.mk.injEq] at h
      exact Subtype.ext (Additive.toMul.injective h)
  exact cycHerbrand_eq_of_surjective_of_finite_ker (unitsRep K L) (logLatticeRep K L) σ hp (fun g x => Subtype.ext (fullLog_unitsRep g x)) (hasHerbrandQuotient_cycSubOne_of_finite _ hσ)
end Galois
end Sec_UnitsHerbrand


/-! ### UnitsHerbrandValue -/
section Sec_UnitsHerbrandValue
open NumberField NumberField.Units NumberField.InfinitePlace MulAction Module
open scoped TensorProduct
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
theorem piScalarRight_baseChange_funPermRep {G X : Type*} [Group G] [MulAction G X] [Fintype X] [DecidableEq X] (g : G) (y : ℝ ⊗[ℤ] (X → ℤ)) : TensorProduct.piScalarRight ℤ ℝ ℝ X ((funPermRep ℤ G X g).baseChange ℝ y) =
      funPermRep ℝ G X g (TensorProduct.piScalarRight ℤ ℝ ℝ X y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul r f =>
    funext x
    simp [LinearMap.baseChange_tmul, TensorProduct.piScalarRightHom_tmul, funPermRep_apply]
  | add y z hy hz => rw [map_add, map_add, hy, hz, map_add, map_add]
def logLatticeProdMap : logLattice L × ℤ →ₗ[ℤ] (InfinitePlace L → ℝ) :=
  (logLattice L).subtype.coprod (LinearMap.toSpanSingleton ℤ (InfinitePlace L → ℝ) 1)
omit [NumberField L] in
theorem logLatticeProdMap_apply (m : logLattice L) (n : ℤ) : logLatticeProdMap (m, n) = (m : InfinitePlace L → ℝ) + n • (1 : InfinitePlace L → ℝ) :=
  rfl
omit [NumberField K] [NumberField L] in
theorem logLatticeProdMap_comm (g : L ≃ₐ[K] L) (x : logLattice L × ℤ) : logLatticeProdMap (((logLatticeRep K L).prod (Representation.trivial ℤ (L ≃ₐ[K] L) ℤ)) g x) = funPermRep ℝ (L ≃ₐ[K] L) (InfinitePlace L) g (logLatticeProdMap x) := by
  obtain ⟨m, n⟩ := x; funext w; simp [logLatticeProdMap_apply, Representation.prod_apply_apply, coe_logLatticeRep, funPermRep_apply]
theorem linearIndependent_logLattice_one {ι : Type*} (b : Basis ι ℤ (logLattice L)) : LinearIndependent ℝ (Sum.elim (fun i => (b i : InfinitePlace L → ℝ))
      (fun _ : Unit => (1 : InfinitePlace L → ℝ))) := by
  classical
  refine LinearIndependent.sum_type (linearIndependent_logLattice_basis L b) ?_ ?_
  · rw [linearIndependent_unique_iff]
    exact one_ne_zero
  · let s : (InfinitePlace L → ℝ) →ₗ[ℝ] ℝ :=
      { toFun := fun y => ∑ w, y w
        map_add' := fun y z => by simp [Finset.sum_add_distrib]
        map_smul' := fun c y => by simp [Finset.mul_sum] }
    have hs : Submodule.span ℝ (Set.range fun i => (b i : InfinitePlace L → ℝ)) ≤
        LinearMap.ker s := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      obtain ⟨x, hx⟩ := (b i).2; change ∑ w, (b i : InfinitePlace L → ℝ) w = 0; rw [← hx]; exact sum_fullLog L x
    rw [Submodule.disjoint_def]
    intro y hy1 hy2; rw [Set.range_const, Submodule.mem_span_singleton] at hy2
    obtain ⟨c, rfl⟩ := hy2
    have h1 : s (c • 1) = 0 := hs hy1
    have h2 : s (c • 1) = c * Fintype.card (InfinitePlace L) := by simp [s, Finset.sum_const]
    rw [h2] at h1
    have h3 : (Fintype.card (InfinitePlace L) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    rw [mul_eq_zero, or_iff_left h3] at h1
    rw [h1, zero_smul]
theorem cycHerbrand_logLatticeRep_mul_card {σ : L ≃ₐ[K] L} (hσ : ∀ g, g ∈ Subgroup.zpowers σ) : cycHerbrand (logLatticeRep K L) σ * Fintype.card (L ≃ₐ[K] L) =
      cycHerbrand (funPermRep ℤ (L ≃ₐ[K] L) (InfinitePlace L)) σ := by
  classical
  let bM := Module.Free.chooseBasis ℤ (logLattice L)
  let b := bM.prod (Basis.singleton Unit ℤ)
  let B := Algebra.TensorProduct.basis ℝ b
  let E := (logLatticeProdMap (L := L)).liftBaseChange ℝ
  let v := Sum.elim (fun i => (bM i : InfinitePlace L → ℝ)) (fun _ : Unit => (1 : InfinitePlace L → ℝ))
  have hEB : ∀ j, E (B j) = v j := by
    intro j; rw [Algebra.TensorProduct.basis_apply, LinearMap.liftBaseChange_tmul, one_smul]
    rcases j with i | u
    · simp [b, v, Basis.prod_apply, logLatticeProdMap_apply]
    · simp [b, v, Basis.prod_apply, logLatticeProdMap_apply]
  have hli : LinearIndependent ℝ v := linearIndependent_logLattice_one bM
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ (logLattice L) ⊕ Unit) =
      finrank ℝ (InfinitePlace L → ℝ) := by
    rw [Fintype.card_sum, Fintype.card_unit, Module.finrank_fintype_fun_eq_card, ← Module.finrank_eq_card_chooseBasisIndex, finrank_logLattice, rank]
    have : 0 < Fintype.card (InfinitePlace L) := Fintype.card_pos; omega
  have hspan := hli.span_eq_top_of_card_eq_finrank hcard
  have hsurj : Function.Surjective E := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hspan, Submodule.span_le]
    rintro _ ⟨j, rfl⟩; exact ⟨B j, hEB j⟩
  have hdim : finrank ℝ (ℝ ⊗[ℤ] (logLattice L × ℤ)) = finrank ℝ (InfinitePlace L → ℝ) := by rw [Module.finrank_eq_card_basis B, hcard]
  have hinj : Function.Injective E :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).2 hsurj
  have hbij : Function.Bijective E := ⟨hinj, hsurj⟩
  let P := TensorProduct.piScalarRight ℤ ℝ ℝ (InfinitePlace L)
  let e : ℝ ⊗[ℤ] (logLattice L × ℤ) ≃ₗ[ℝ] ℝ ⊗[ℤ] (InfinitePlace L → ℤ) :=
    (LinearEquiv.ofBijective E hbij).trans P.symm
  have hE : ∀ (g : L ≃ₐ[K] L) y, E ((((logLatticeRep K L).prod (Representation.trivial ℤ (L ≃ₐ[K] L) ℤ)) g).baseChange ℝ y) =
      funPermRep ℝ (L ≃ₐ[K] L) (InfinitePlace L) g (E y) := by
    intro g y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul r x =>
      rw [LinearMap.baseChange_tmul, LinearMap.liftBaseChange_tmul, LinearMap.liftBaseChange_tmul,
        map_smul, logLatticeProdMap_comm]
    | add y z hy hz => rw [map_add, map_add, hy, hz, map_add, map_add]
  have he : ∀ (g : L ≃ₐ[K] L) y, e ((((logLatticeRep K L).prod (Representation.trivial ℤ (L ≃ₐ[K] L) ℤ)) g).baseChange ℝ y) =
      (funPermRep ℤ (L ≃ₐ[K] L) (InfinitePlace L) g).baseChange ℝ (e y) := by
    intro g y; apply P.injective; simp only [e, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
    rw [piScalarRight_baseChange_funPermRep, LinearEquiv.apply_symm_apply, LinearEquiv.ofBijective_apply, LinearEquiv.ofBijective_apply, hE]
  rw [← cycHerbrand_eq_of_real_equiv _ _ σ e he, cycHerbrand_prod _ _ σ (hasHerbrandQuotient_cycSubOne_of_finite _ hσ) (hasHerbrandQuotient_cycSubOne_of_finite _ hσ), cycHerbrand_trivial_int]
variable [IsGalois K L]
open scoped Classical in
theorem cycHerbrand_unitsRep {σ : L ≃ₐ[K] L} (hσ : ∀ g, g ∈ Subgroup.zpowers σ) : cycHerbrand (unitsRep K L) σ =
      (∏ v : InfinitePlace K, (if v.IsUnramifiedIn L then 1 else 2 : ℚ)) / finrank K L := by
  have h1 := cycHerbrand_logLatticeRep_mul_card hσ; rw [cycHerbrand_funPermRep hσ, prod_card_stabilizer_infinitePlace] at h1
  have h2 : (Fintype.card (L ≃ₐ[K] L) : ℚ) = finrank K L := by rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank]
  have h3 : (finrank K L : ℚ) ≠ 0 := by exact_mod_cast Module.finrank_pos.ne'
  rw [cycHerbrand_unitsRep_eq_logLattice hσ, eq_div_iff h3, ← h2, h1]
end Sec_UnitsHerbrandValue


/-! ### SUnits -/
section Sec_SUnits
open NumberField IsDedekindDomain MulAction Module
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
variable (S : Set (HeightOneSpectrum (𝓞 L))) [Finite S]
omit [IsGalois K L] in
theorem hasHerbrandQuotient_sUnitRep (hS : ∀ (g : L ≃ₐ[K] L), ∀ w ∈ S, g • w ∈ S) {σ : L ≃ₐ[K] L} (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    HasHerbrandQuotient (cycSubOne (sUnitRep S hS) σ) (cycNorm (sUnitRep S hS)) :=
  hasHerbrandQuotient_cycSubOne_of_finite _ hσ
omit [IsGalois K L] in
theorem finite_quotient_range_valuationVector : Finite ((S → ℤ) ⧸ (SUnit.valuationVector (K := L) S).toAddMonoidHom.range) := by
  have hn : (-(classNumber L : ℤ)) ≠ 0 := by simpa using classNumber_ne_zero L
  refine finite_quotient_of_smul_mem _ hn fun y => ⟨SUnit.placeUnitsMap S y, ?_⟩
  change (SUnit.valuationVector S ∘ₗ SUnit.placeUnitsMap S) y = _; rw [SUnit.valuationVector_comp_placeUnitsMap]; rfl
omit [IsGalois K L] [Finite S] in
theorem exact_ofUnits_valuationVector : Function.Exact (SUnit.ofUnits (K := L) S).toAdditive
      (SUnit.valuationVector (K := L) S).toAddMonoidHom := by
  intro y
  have h := SetLike.ext_iff.1 (SUnit.ker_valuationVector (K := L) S) y; rw [LinearMap.mem_ker, LinearMap.mem_range] at h; exact h
open scoped Classical in
theorem cycHerbrand_sUnitRep (hS : ∀ (g : L ≃ₐ[K] L), ∀ w ∈ S, g • w ∈ S) {σ : L ≃ₐ[K] L} (hσ : ∀ g, g ∈ Subgroup.zpowers σ) : cycHerbrand (sUnitRep S hS) σ = (∏ᶠ (v : HeightOneSpectrum (𝓞 K)) (_ : ∃ w ∈ S, w.asIdeal.LiesOver v.asIdeal),
          ((v.asIdeal.ramificationIdxIn (𝓞 L) * v.asIdeal.inertiaDegIn (𝓞 L) : ℕ) : ℚ)) *
        (∏ v : InfinitePlace K, (if v.IsUnramifiedIn L then 1 else 2 : ℚ)) / finrank K L := by
  let := stableMulAction S hS
  have : Fintype (orbitRel.Quotient (L ≃ₐ[K] L) S) := Fintype.ofFinite _
  have : Finite ((S → ℤ) ⧸ (SUnit.valuationVector (K := L) S).toAddMonoidHom.range) :=
    finite_quotient_range_valuationVector S
  have h1 := cycHerbrand_eq_mul_of_exact (unitsRep K L) (sUnitRep S hS) (funPermRep ℤ (L ≃ₐ[K] L) S) σ
    (i := (SUnit.ofUnits (K := L) S).toAdditive)
    (p := (SUnit.valuationVector (K := L) S).toAddMonoidHom)
    (fun a b h => SUnit.ofUnits_injective S (congrArg Additive.toMul h))
    (exact_ofUnits_valuationVector S) (fun g a => ofUnits_unitsRep S hS g a)
    (fun g b => valuationVector_sUnitRep S hS g b)
    (hasHerbrandQuotient_cycSubOne_of_finite _ hσ) (hasHerbrandQuotient_cycSubOne_of_finite _ hσ)
  rw [h1, cycHerbrand_unitsRep hσ, cycHerbrand_funPermRep hσ, prod_card_stabilizer_finitePlace S hS]
  ring
end Sec_SUnits


/-! ### LocalAtPlace -/
section Sec2_LocalAtPlace
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField
section Residue
variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K] (v : HeightOneSpectrum R)
theorem algebraMap_mem_maximalIdeal_adicCompletionIntegers_iff (r : R) : algebraMap R (v.adicCompletionIntegers K) r ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ↔ r ∈ v.asIdeal := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, adicCompletionIntegers.isUnit_iff_valued_eq_one, algebraMap_adicCompletionIntegers_apply, valuedAdicCompletion_eq_valuation', valuation_eq_one_iff_notMem, not_not]
theorem exists_algebraMap_sub_mem_maximalIdeal (x : v.adicCompletionIntegers K) : ∃ r : R, x - algebraMap R (v.adicCompletionIntegers K) r ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) := by
  have hnhds : {y : v.adicCompletion K | Valued.v (y - (x : v.adicCompletion K)) < 1} ∈
      nhds (x : v.adicCompletion K) :=
    Valued.mem_nhds.2 ⟨1, fun y hy ↦ by
      simpa [Valuation.restrict_lt_one_iff] using hy⟩
  obtain ⟨k, hk⟩ := (denseRange_algebraMap (K := K) v).mem_nhds hnhds
  have hk' : Valued.v ((x : v.adicCompletion K) - (k : v.adicCompletion K)) < 1 := by rw [Valuation.map_sub_swap]; exact hk
  have hk1 : v.valuation K k ≤ 1 := by
    rw [← valuedAdicCompletion_eq_valuation']
    have : (k : v.adicCompletion K) = (x : v.adicCompletion K) -
        ((x : v.adicCompletion K) - (k : v.adicCompletion K)) := by ring
    rw [this]
    exact (Valuation.map_sub _ _ _).trans (max_le x.2 hk'.le)
  obtain ⟨r, hr⟩ := exists_valuation_sub_lt_of_integer v hk1 1; refine ⟨r, ?_⟩; rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, adicCompletionIntegers.isUnit_iff_valued_eq_one]; refine ne_of_lt ?_
  have hr' : Valued.v (algebraMap K (v.adicCompletion K) (k - algebraMap R K r)) < 1 := by
    rw [Valuation.map_sub_swap] at hr
    have := valuedAdicCompletion_eq_valuation' (R := R) v (k - algebraMap R K r); exact this.trans_lt (by simpa using hr)
  have : ((x - algebraMap R (v.adicCompletionIntegers K) r : v.adicCompletionIntegers K) : v.adicCompletion K) = ((x : v.adicCompletion K) - (k : v.adicCompletion K)) +
        algebraMap K (v.adicCompletion K) (k - algebraMap R K r) := by
    rw [map_sub]
    simp [algebraMap_adicCompletion]
  rw [this]
  exact Valuation.map_add_lt _ hk' hr'
noncomputable def toResidueFieldAdicCompletionIntegers : R →+* IsLocalRing.ResidueField (v.adicCompletionIntegers K) :=
  (IsLocalRing.residue _).comp (algebraMap R (v.adicCompletionIntegers K))
theorem ker_toResidueFieldAdicCompletionIntegers : RingHom.ker (toResidueFieldAdicCompletionIntegers (K := K) v) = v.asIdeal := by
  ext r
  rw [RingHom.mem_ker, toResidueFieldAdicCompletionIntegers, RingHom.comp_apply, IsLocalRing.residue_eq_zero_iff, algebraMap_mem_maximalIdeal_adicCompletionIntegers_iff]
theorem toResidueFieldAdicCompletionIntegers_surjective : Function.Surjective (toResidueFieldAdicCompletionIntegers (K := K) v) := by
  intro y
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective y
  obtain ⟨r, hr⟩ := exists_algebraMap_sub_mem_maximalIdeal v x; exact ⟨r, (Ideal.Quotient.eq.2 hr).symm⟩
noncomputable def residueFieldEquiv : (R ⧸ v.asIdeal) ≃+* IsLocalRing.ResidueField (v.adicCompletionIntegers K) :=
  (Ideal.quotEquivOfEq (ker_toResidueFieldAdicCompletionIntegers v).symm).trans (RingHom.quotientKerEquivOfSurjective (toResidueFieldAdicCompletionIntegers_surjective v))
@[simp]
theorem residueFieldEquiv_mk (r : R) : residueFieldEquiv (K := K) v (Ideal.Quotient.mk v.asIdeal r) =
      IsLocalRing.residue _ (algebraMap R (v.adicCompletionIntegers K) r) :=
  rfl
end Residue
section NumberField
variable {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
instance : Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers K)) :=
  haveI := Ideal.finiteQuotientOfFreeOfNeBot v.asIdeal v.ne_bot
  Finite.of_equiv _ (residueFieldEquiv v).toEquiv
theorem natCard_residueField_adicCompletionIntegers : Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers K)) = Ideal.absNorm v.asIdeal := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  exact (Nat.card_congr (residueFieldEquiv v).toEquiv).symm
end NumberField
section Topology
variable {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
theorem isOpen_adicCompletionIntegers : IsOpen (v.adicCompletionIntegers K : Set (v.adicCompletion K)) :=
  Valued.isOpen_valuationSubring _
theorem isClosed_adicCompletionIntegers : IsClosed (v.adicCompletionIntegers K : Set (v.adicCompletion K)) :=
  (Valued.isClopen_integer (v.adicCompletion K)).isClosed
theorem isCompact_adicCompletionIntegers : IsCompact (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := by
  have : CompleteSpace (Valued.integer (v.adicCompletion K)) :=
    (isClosed_adicCompletionIntegers v).completeSpace_coe
  have : IsDiscreteValuationRing (Valued.integer (v.adicCompletion K)) :=
    inferInstanceAs (IsDiscreteValuationRing (v.adicCompletionIntegers K))
  have : Finite (Valued.ResidueField (v.adicCompletion K)) :=
    inferInstanceAs (Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers K)))
  have h : CompactSpace (Valued.integer (v.adicCompletion K)) :=
    Valued.integer.compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField.2 ⟨inferInstance, inferInstance, inferInstance⟩
  exact isCompact_iff_compactSpace.2 h
instance : CompactSpace (v.adicCompletionIntegers K) :=
  isCompact_iff_compactSpace.1 (isCompact_adicCompletionIntegers v)
instance : LocallyCompactSpace (v.adicCompletion K) :=
  (isCompact_adicCompletionIntegers v).locallyCompactSpace_of_mem_nhds_of_addGroup ((isOpen_adicCompletionIntegers v).mem_nhds (v.adicCompletionIntegers K).zero_mem)
instance : CompleteSpace (v.adicCompletionIntegers K) :=
  (isClosed_adicCompletionIntegers v).completeSpace_coe
end Topology
end Sec2_LocalAtPlace


/-! ### InfiniteProjInfiniteEmbeddingOfNe -/
section Sec2_InfiniteProjInfiniteEmbeddingOfNe
open NumberField IsDedekindDomain Topology
open scoped NumberField.AdeleRing RestrictedProduct
variable (K : Type*) [Field K] [NumberField K]
abbrev IdeleGroup : Type _ := (𝔸[K])ˣ
namespace IdeleGroup
theorem isEmbedding_val_inv : IsEmbedding (fun x : IdeleGroup K ↦ ((x : 𝔸[K]), ((x⁻¹ : IdeleGroup K) : 𝔸[K]))) :=
  ((Homeomorph.refl (𝔸[K])).prodCongr MulOpposite.opHomeomorph.symm).isEmbedding.comp
    (Units.isEmbedding_embedProduct (M := 𝔸[K]))
def prodEquiv : IdeleGroup K ≃ₜ* (InfiniteAdeleRing K)ˣ × (FiniteAdeleRing (𝓞 K) K)ˣ where
  toMulEquiv := MulEquiv.prodUnits
  continuous_toFun := (Homeomorph.prodUnits (α := InfiniteAdeleRing K)
    (β := FiniteAdeleRing (𝓞 K) K)).continuous_toFun
  continuous_invFun := (Homeomorph.prodUnits (α := InfiniteAdeleRing K)
    (β := FiniteAdeleRing (𝓞 K) K)).continuous_invFun
@[simp]
theorem prodEquiv_apply_fst (x : IdeleGroup K) : ((prodEquiv K x).1 : InfiniteAdeleRing K) = (x : 𝔸[K]).1 := rfl
@[simp]
theorem prodEquiv_apply_snd (x : IdeleGroup K) : ((prodEquiv K x).2 : FiniteAdeleRing (𝓞 K) K) = (x : 𝔸[K]).2 := rfl
def toInfinite : IdeleGroup K →* (InfiniteAdeleRing K)ˣ :=
  (MonoidHom.fst _ _).comp (prodEquiv K).toMulEquiv.toMonoidHom
def toFinite : IdeleGroup K →* (FiniteAdeleRing (𝓞 K) K)ˣ :=
  (MonoidHom.snd _ _).comp (prodEquiv K).toMulEquiv.toMonoidHom
theorem continuous_toInfinite : Continuous (toInfinite K) :=
  continuous_fst.comp (prodEquiv K).continuous
theorem continuous_toFinite : Continuous (toFinite K) :=
  continuous_snd.comp (prodEquiv K).continuous
def diagonal : Kˣ →* IdeleGroup K :=
  Units.map (algebraMap K 𝔸[K]).toMonoidHom
@[simp]
theorem coe_diagonal (x : Kˣ) : ((diagonal K x : IdeleGroup K) : 𝔸[K]) = algebraMap K 𝔸[K] x :=
  rfl
theorem diagonal_injective : Function.Injective (diagonal K) := by intro x y h; ext; exact AdeleRing.algebraMap_injective (𝓞 K) K (congrArg Units.val h)
end IdeleGroup
abbrev IdeleClassGroup : Type _ := IdeleGroup K ⧸ (IdeleGroup.diagonal K).range
namespace IdeleClassGroup
def mk : IdeleGroup K →* IdeleClassGroup K := QuotientGroup.mk' _
theorem continuous_mk : Continuous (mk K) := QuotientGroup.continuous_mk
theorem isOpenMap_mk : IsOpenMap (mk K) := QuotientGroup.isOpenMap_coe
theorem mk_surjective : Function.Surjective (mk K) := QuotientGroup.mk'_surjective _
theorem mk_diagonal (x : Kˣ) : mk K (IdeleGroup.diagonal K x) = 1 :=
  (QuotientGroup.eq_one_iff _).2 ⟨x, rfl⟩
theorem ker_mk : (mk K).ker = (IdeleGroup.diagonal K).range := QuotientGroup.ker_mk' _
end IdeleClassGroup
namespace IdeleGroup
section Finite
variable {K}
open Classical in
def finiteAdeleSingle (v : HeightOneSpectrum (𝓞 K)) : v.adicCompletion K →* FiniteAdeleRing (𝓞 K) K where
  toFun x := RestrictedProduct.mulSingle (fun w : HeightOneSpectrum (𝓞 K) ↦ w.adicCompletionIntegers K) v x
  map_one' := Subtype.ext (Pi.mulSingle_one (M := fun w : HeightOneSpectrum (𝓞 K) ↦
    w.adicCompletion K) v)
  map_mul' x y := Subtype.ext (Pi.mulSingle_mul v x y)
open Classical in
theorem finiteAdeleSingle_apply (v w : HeightOneSpectrum (𝓞 K)) (x : v.adicCompletion K) : finiteAdeleSingle v x w = Pi.mulSingle (M := fun u : HeightOneSpectrum (𝓞 K) ↦
      u.adicCompletion K) v x w := rfl
@[simp]
theorem finiteAdeleSingle_apply_self (v : HeightOneSpectrum (𝓞 K)) (x : v.adicCompletion K) : finiteAdeleSingle v x v = x := by
  classical
  rw [finiteAdeleSingle_apply]
  exact Pi.mulSingle_eq_same v x
theorem finiteAdeleSingle_apply_of_ne {v w : HeightOneSpectrum (𝓞 K)} (h : w ≠ v)
    (x : v.adicCompletion K) : finiteAdeleSingle v x w = 1 := by
  classical
  rw [finiteAdeleSingle_apply]
  exact Pi.mulSingle_eq_of_ne h x
theorem continuous_finiteAdeleSingle (v : HeightOneSpectrum (𝓞 K)) : Continuous (finiteAdeleSingle (K := K) v) := by
  classical
  have hS : Filter.cofinite ≤ Filter.principal ({v}ᶜ : Set (HeightOneSpectrum (𝓞 K))) := by simp
  let g : v.adicCompletion K → Πʳ w : HeightOneSpectrum (𝓞 K),
      [w.adicCompletion K, w.adicCompletionIntegers K]_[Filter.principal {v}ᶜ] :=
    fun x ↦ ⟨Pi.mulSingle v x, Filter.eventually_principal.2 fun w hw ↦ by
      rw [Pi.mulSingle_eq_of_ne hw x]
      exact one_mem _⟩
  have hg : Continuous g :=
    RestrictedProduct.continuous_rng_of_principal.mpr (continuous_mulSingle v)
  have hfg : (finiteAdeleSingle (K := K) v : v.adicCompletion K → FiniteAdeleRing (𝓞 K) K) =
      RestrictedProduct.inclusion _ _ hS ∘ g := by
    rfl
  rw [hfg]
  exact (RestrictedProduct.continuous_inclusion hS).comp hg
def finiteEmbedding (v : HeightOneSpectrum (𝓞 K)) : (v.adicCompletion K)ˣ →* IdeleGroup K :=
  Units.map ((MonoidHom.prod 1 (finiteAdeleSingle v) : v.adicCompletion K →* InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K))
def finiteProj (v : HeightOneSpectrum (𝓞 K)) : IdeleGroup K →* (v.adicCompletion K)ˣ :=
  Units.map (((RestrictedProduct.evalMonoidHom (fun w : HeightOneSpectrum (𝓞 K) ↦ w.adicCompletion K) v).comp (MonoidHom.snd (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K))) :
    InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K →* v.adicCompletion K)
@[simp]
theorem coe_finiteEmbedding (v : HeightOneSpectrum (𝓞 K)) (x : (v.adicCompletion K)ˣ) : ((finiteEmbedding v x : IdeleGroup K) : 𝔸[K]) = (1, finiteAdeleSingle v (x : v.adicCompletion K)) :=
  rfl
@[simp]
theorem coe_finiteProj (v : HeightOneSpectrum (𝓞 K)) (x : IdeleGroup K) : ((finiteProj v x : (v.adicCompletion K)ˣ) : v.adicCompletion K) = (x : 𝔸[K]).2 v :=
  rfl
theorem continuous_finiteEmbedding (v : HeightOneSpectrum (𝓞 K)) : Continuous (finiteEmbedding (K := K) v) :=
  Units.continuous_map (continuous_const.prodMk (continuous_finiteAdeleSingle v))
theorem continuous_finiteProj (v : HeightOneSpectrum (𝓞 K)) : Continuous (finiteProj (K := K) v) :=
  Units.continuous_map ((RestrictedProduct.continuous_eval v).comp continuous_snd)
@[simp]
theorem finiteProj_finiteEmbedding (v : HeightOneSpectrum (𝓞 K)) (x : (v.adicCompletion K)ˣ) : finiteProj v (finiteEmbedding v x) = x := by
  ext
  simp
theorem finiteProj_finiteEmbedding_of_ne {v w : HeightOneSpectrum (𝓞 K)} (h : w ≠ v)
    (x : (v.adicCompletion K)ˣ) : finiteProj w (finiteEmbedding v x) = 1 := by
  ext
  simp [finiteAdeleSingle_apply_of_ne h]
@[simp]
theorem coe_finiteProj_diagonal (v : HeightOneSpectrum (𝓞 K)) (x : Kˣ) : ((finiteProj v (diagonal K x) : (v.adicCompletion K)ˣ) : v.adicCompletion K) = ((x : K) : v.adicCompletion K) :=
  rfl
end Finite
section Infinite
variable {K}
open Classical in
def infiniteAdeleSingle (w : InfinitePlace K) : w.Completion →* InfiniteAdeleRing K :=
  MonoidHom.mulSingle (fun u : InfinitePlace K ↦ u.Completion) w
omit [NumberField K] in
open Classical in
theorem infiniteAdeleSingle_apply (w u : InfinitePlace K) (x : w.Completion) : infiniteAdeleSingle w x u = Pi.mulSingle (M := fun u : InfinitePlace K ↦ u.Completion) w x u :=
  rfl
omit [NumberField K] in
theorem continuous_infiniteAdeleSingle (w : InfinitePlace K) : Continuous (infiniteAdeleSingle w) := by
  classical
  exact continuous_mulSingle (A := fun u : InfinitePlace K ↦ u.Completion) w
def infiniteEmbedding (w : InfinitePlace K) : (w.Completion)ˣ →* IdeleGroup K :=
  Units.map ((MonoidHom.prod (infiniteAdeleSingle w) 1 : w.Completion →* InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K))
def infiniteProj (w : InfinitePlace K) : IdeleGroup K →* (w.Completion)ˣ :=
  Units.map (((Pi.evalMonoidHom (fun u : InfinitePlace K ↦ u.Completion) w).comp (MonoidHom.fst (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K))) : InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K →* w.Completion)
@[simp]
theorem coe_infiniteEmbedding (w : InfinitePlace K) (x : (w.Completion)ˣ) : ((infiniteEmbedding w x : IdeleGroup K) : 𝔸[K]) = (infiniteAdeleSingle w (x : w.Completion), 1) :=
  rfl
@[simp]
theorem coe_infiniteProj (w : InfinitePlace K) (x : IdeleGroup K) : ((infiniteProj w x : (w.Completion)ˣ) : w.Completion) = (x : 𝔸[K]).1 w :=
  rfl
theorem continuous_infiniteEmbedding (w : InfinitePlace K) : Continuous (infiniteEmbedding (K := K) w) :=
  Units.continuous_map ((continuous_infiniteAdeleSingle w).prodMk continuous_const)
theorem continuous_infiniteProj (w : InfinitePlace K) : Continuous (infiniteProj (K := K) w) :=
  Units.continuous_map ((continuous_apply w).comp continuous_fst)
@[simp]
theorem infiniteProj_infiniteEmbedding (w : InfinitePlace K) (x : (w.Completion)ˣ) : infiniteProj w (infiniteEmbedding w x) = x := by
  classical
  ext
  simp [infiniteAdeleSingle_apply]
theorem infiniteProj_infiniteEmbedding_of_ne {w u : InfinitePlace K} (h : u ≠ w)
    (x : (w.Completion)ˣ) : infiniteProj u (infiniteEmbedding w x) = 1 := by
  classical
  ext
  simp [infiniteAdeleSingle_apply, Pi.mulSingle_eq_of_ne h]
@[simp]
theorem coe_infiniteProj_diagonal (w : InfinitePlace K) (x : Kˣ) : ((infiniteProj w (diagonal K x) : (w.Completion)ˣ) : w.Completion) = ((x : K) : w.Completion) :=
  rfl
end Infinite
def integralAtFinite : Submonoid 𝔸[K] where
  carrier := {a | ∀ v : HeightOneSpectrum (𝓞 K), a.2 v ∈ v.adicCompletionIntegers K}
  one_mem' v := one_mem (v.adicCompletionIntegers K)
  mul_mem' ha hb v := mul_mem (ha v) (hb v)
theorem mem_integralAtFinite {a : 𝔸[K]} :
    a ∈ integralAtFinite K ↔ ∀ v : HeightOneSpectrum (𝓞 K), a.2 v ∈ v.adicCompletionIntegers K :=
  Iff.rfl
theorem isOpen_integralAtFinite : IsOpen (integralAtFinite K : Set 𝔸[K]) :=
  (RestrictedProduct.isOpen_forall_mem fun v : HeightOneSpectrum (𝓞 K) ↦
    Valued.isOpen_valuationSubring (v.adicCompletion K)).preimage continuous_snd
def standardOpenSubgroup : Subgroup (IdeleGroup K) := (integralAtFinite K).units
theorem mem_standardOpenSubgroup {x : IdeleGroup K} : x ∈ standardOpenSubgroup K ↔ ∀ v : HeightOneSpectrum (𝓞 K), (x : 𝔸[K]).2 v ∈ v.adicCompletionIntegers K ∧
        ((x⁻¹ : IdeleGroup K) : 𝔸[K]).2 v ∈ v.adicCompletionIntegers K := by
  rw [standardOpenSubgroup, Submonoid.mem_units_iff, mem_integralAtFinite, mem_integralAtFinite, ← forall_and]
theorem isOpen_standardOpenSubgroup : IsOpen (standardOpenSubgroup K : Set (IdeleGroup K)) :=
  Submonoid.isOpen_units (isOpen_integralAtFinite K)
end IdeleGroup
end Sec2_InfiniteProjInfiniteEmbeddingOfNe


/-! ### Restricted -/
section Sec2_Restricted
open Filter Topology NumberField IsDedekindDomain
open scoped RestrictedProduct NumberField.AdeleRing
namespace RestrictedProdAux
variable {ι : Type*} {R : ι → Type*} [∀ i, Monoid (R i)] [∀ i, TopologicalSpace (R i)] {S : ι → Type*} [∀ i, SetLike (S i) (R i)] [∀ i, SubmonoidClass (S i) (R i)] {B : Π i, S i}
theorem continuous_unitsEquiv_symm : Continuous (_root_.RestrictedProduct.unitsEquiv R (B := B) (𝓕 := cofinite)).symm := by
  rw [Units.continuous_iff]
  constructor
  · exact _root_.RestrictedProduct.mapAlong_continuous (fun i ↦ (R i)ˣ) R id tendsto_id
      (A₁ := fun i ↦ ((Submonoid.ofClass (B i)).units : Set (R i)ˣ))
      (A₂ := fun i ↦ (B i : Set (R i)))
      (fun i (u : (R i)ˣ) ↦ (u : R i)) (.of_forall fun _ _ hu ↦ hu.1)
      (fun _ ↦ Units.continuous_val)
  · exact _root_.RestrictedProduct.mapAlong_continuous (fun i ↦ (R i)ˣ) R id tendsto_id
      (A₁ := fun i ↦ ((Submonoid.ofClass (B i)).units : Set (R i)ˣ))
      (A₂ := fun i ↦ (B i : Set (R i)))
      (fun i (u : (R i)ˣ) ↦ ((u⁻¹ : (R i)ˣ) : R i)) (.of_forall fun _ _ hu ↦ hu.2)
      (fun _ ↦ Units.continuous_coe_inv)
theorem continuous_unitsEquiv (hBopen : ∀ i, IsOpen (B i : Set (R i))) : Continuous (_root_.RestrictedProduct.unitsEquiv R (B := B) (𝓕 := cofinite)) := by
  refine continuous_iff_continuousAt.2 fun x ↦ ?_
  set T : Set ι :=
    {i | _root_.RestrictedProduct.unitsEquiv R x i ∈ (Submonoid.ofClass (B i)).units} with hTdef
  have hT : cofinite ≤ 𝓟 T := le_principal_iff.2 (_root_.RestrictedProduct.unitsEquiv R x).2
  let U : Set (Πʳ i, [R i, B i])ˣ :=
    {y | ∀ i ∈ T, (y : Πʳ i, [R i, B i]) i ∈ B i ∧
      ((y⁻¹ : (Πʳ i, [R i, B i])ˣ) : Πʳ i, [R i, B i]) i ∈ B i}
  have hUo : IsOpen U := by
    have h1 := _root_.RestrictedProduct.isOpen_forall_imp_mem hBopen (p := (· ∈ T))
    have h2 := (h1.preimage Units.continuous_val).inter (h1.preimage Units.continuous_coe_inv); convert h2 using 1; ext y; simp only [U, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage, ← forall_and]
    exact forall_congr' fun i ↦ ⟨fun h hi ↦ h hi, fun h hi ↦ h hi⟩
  have hxU : x ∈ U := fun i hi ↦ hi
  let G : U → Πʳ i, [(R i)ˣ, (Submonoid.ofClass (B i)).units]_[𝓟 T] :=
    fun y ↦ ⟨fun i ↦ _root_.RestrictedProduct.unitsEquiv R y.1 i, eventually_principal.2 fun i hi ↦ y.2 i hi⟩
  have hG : Continuous G := by
    rw [_root_.RestrictedProduct.continuous_rng_of_principal]
    refine continuous_pi fun i ↦ ?_
    exact (Units.continuous_map (f := _root_.RestrictedProduct.evalMonoidHom R i) (_root_.RestrictedProduct.continuous_eval i)).comp continuous_subtype_val
  have hFU : ContinuousOn (_root_.RestrictedProduct.unitsEquiv R (B := B) (𝓕 := cofinite)) U := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact (_root_.RestrictedProduct.continuous_inclusion hT).comp hG
  exact hFU.continuousAt (hUo.mem_nhds hxU)
def continuousUnitsEquiv (hBopen : ∀ i, IsOpen (B i : Set (R i))) : (Πʳ i, [R i, B i])ˣ ≃ₜ* Πʳ i, [(R i)ˣ, (Submonoid.ofClass (B i)).units] where
  toMulEquiv := _root_.RestrictedProduct.unitsEquiv R
  continuous_toFun := continuous_unitsEquiv hBopen
  continuous_invFun := continuous_unitsEquiv_symm
@[simp]
theorem continuousUnitsEquiv_apply (hBopen : ∀ i, IsOpen (B i : Set (R i))) (x : (Πʳ i, [R i, B i])ˣ) (i : ι) : ((continuousUnitsEquiv hBopen x i : (R i)ˣ) : R i) = (x : Πʳ i, [R i, B i]) i :=
  rfl
end RestrictedProdAux
namespace IdeleGroup
variable (K : Type*) [Field K] [NumberField K]
theorem isOpen_units_adicCompletionIntegers (v : HeightOneSpectrum (𝓞 K)) : IsOpen ((Submonoid.ofClass (v.adicCompletionIntegers K)).units : Set (v.adicCompletion K)ˣ) :=
  Submonoid.isOpen_units (Valued.isOpen_valuationSubring (v.adicCompletion K))
def finiteUnitsEquiv : (FiniteAdeleRing (𝓞 K) K)ˣ ≃ₜ* Πʳ v : HeightOneSpectrum (𝓞 K),
      [(v.adicCompletion K)ˣ, (Submonoid.ofClass (v.adicCompletionIntegers K)).units] :=
  RestrictedProdAux.continuousUnitsEquiv (R := fun v : HeightOneSpectrum (𝓞 K) ↦ v.adicCompletion K)
    (B := fun v ↦ v.adicCompletionIntegers K)
    (fun v ↦ Valued.isOpen_valuationSubring (v.adicCompletion K))
@[simp]
theorem finiteUnitsEquiv_apply (x : (FiniteAdeleRing (𝓞 K) K)ˣ) (v : HeightOneSpectrum (𝓞 K)) : ((finiteUnitsEquiv K x v : (v.adicCompletion K)ˣ) : v.adicCompletion K) = (x : FiniteAdeleRing (𝓞 K) K) v :=
  rfl
def prodRestrictedEquiv : IdeleGroup K ≃ₜ* (InfiniteAdeleRing K)ˣ × Πʳ v : HeightOneSpectrum (𝓞 K),
      [(v.adicCompletion K)ˣ, (Submonoid.ofClass (v.adicCompletionIntegers K)).units] :=
  (prodEquiv K).trans
    { toMulEquiv := MulEquiv.prodCongr (MulEquiv.refl _) (finiteUnitsEquiv K).toMulEquiv
      continuous_toFun :=
        continuous_fst.prodMk ((finiteUnitsEquiv K).continuous.comp continuous_snd)
      continuous_invFun :=
        continuous_fst.prodMk ((finiteUnitsEquiv K).symm.continuous.comp continuous_snd) }
@[simp]
theorem prodRestrictedEquiv_apply_fst (x : IdeleGroup K) : ((prodRestrictedEquiv K x).1 : InfiniteAdeleRing K) = (x : 𝔸[K]).1 :=
  rfl
@[simp]
theorem prodRestrictedEquiv_apply_snd (x : IdeleGroup K) (v : HeightOneSpectrum (𝓞 K)) : (((prodRestrictedEquiv K x).2 v : (v.adicCompletion K)ˣ) : v.adicCompletion K) = (x : 𝔸[K]).2 v :=
  rfl
end IdeleGroup
end Sec2_Restricted


/-! ### ClassGroup -/
section Sec2_ClassGroup
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero FractionalIdeal
open scoped NumberField.AdeleRing nonZeroDivisors
variable {K : Type*} [Field K] [NumberField K]
def primeIdealUnit (v : HeightOneSpectrum (𝓞 K)) : (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
  Units.mk0 (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) (coeIdeal_ne_zero.mpr v.ne_bot)
@[simp]
theorem coe_primeIdealUnit (v : HeightOneSpectrum (𝓞 K)) : ((primeIdealUnit v : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) = (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) :=
  rfl
theorem fractionalIdealUnits_eq_iff {I J : (FractionalIdeal (𝓞 K)⁰ K)ˣ} : I = J ↔ ∀ v : HeightOneSpectrum (𝓞 K),
      count K v (I : FractionalIdeal (𝓞 K)⁰ K) = count K v (J : FractionalIdeal (𝓞 K)⁰ K) := by
  refine ⟨fun h v ↦ h ▸ rfl, fun h ↦ Units.ext ?_⟩
  rw [← finprod_heightOneSpectrum_factorization' (K := K) I.ne_zero,
    ← finprod_heightOneSpectrum_factorization' (K := K) J.ne_zero]
  exact finprod_congr fun v ↦ by rw [h v]
theorem coe_finprod_primeIdealUnit_zpow (n : HeightOneSpectrum (𝓞 K) → ℤ) (hn : ∀ᶠ v in Filter.cofinite, n v = 0) : ((∏ᶠ v, primeIdealUnit v ^ n v : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) =
      ∏ᶠ v : HeightOneSpectrum (𝓞 K), (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^ n v := by
  have hfin : (Function.mulSupport fun v ↦ primeIdealUnit (K := K) v ^ n v).Finite :=
    (Filter.eventually_cofinite.1 hn).subset fun v hv h ↦ hv (by simp only [h, zpow_zero])
  rw [← Units.coeHom_apply, map_finprod _ hfin]
  exact finprod_congr fun v ↦ by simp [Units.val_zpow_eq_zpow_val]
theorem count_finprod_primeIdealUnit_zpow (n : HeightOneSpectrum (𝓞 K) → ℤ) (hn : ∀ᶠ v in Filter.cofinite, n v = 0) (v : HeightOneSpectrum (𝓞 K)) : count K v ((∏ᶠ w, primeIdealUnit w ^ n w : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
      FractionalIdeal (𝓞 K)⁰ K) = n v := by
  rw [coe_finprod_primeIdealUnit_zpow n hn, count_finprod K v n hn]
theorem finprod_primeIdealUnit_zpow_count (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : ∏ᶠ v, primeIdealUnit v ^ count K v (I : FractionalIdeal (𝓞 K)⁰ K) = I := by
  rw [fractionalIdealUnits_eq_iff]
  intro v; exact count_finprod_primeIdealUnit_zpow _ (FractionalIdeal.finite_factors _) v
open Classical in
theorem count_primeIdealUnit (v w : HeightOneSpectrum (𝓞 K)) : count K w ((primeIdealUnit v : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) = if w = v then 1 else 0 := by
  rw [coe_primeIdealUnit]
  split_ifs with h
  · subst h
    exact count_self K w
  · exact count_maximal_coprime K w (Ne.symm h)
theorem count_spanSingleton (v : HeightOneSpectrum (𝓞 K)) {a : K} (ha : a ≠ 0) :
    count K v (spanSingleton (𝓞 K)⁰ a) = -log (v.valuation K a) := by
  obtain ⟨n, d, hd, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) a
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  have hn0 : n ≠ 0 := by rintro rfl; simp at ha
  have hI : spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K n / algebraMap (𝓞 K) K d) =
      spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K d)⁻¹ * ↑(Ideal.span {n} : Ideal (𝓞 K)) := by
    rw [coeIdeal_span_singleton, spanSingleton_mul_spanSingleton, div_eq_mul_inv, mul_comm]
  rw [count_well_defined K v ((spanSingleton_ne_zero_iff).2 ha) hI, map_div₀, valuation_of_algebraMap, valuation_of_algebraMap, intValuation_if_neg _ hn0, intValuation_if_neg _ hd0, ← exp_sub, log_exp]
  ring
namespace IdeleGroup
def ord (v : HeightOneSpectrum (𝓞 K)) (x : IdeleGroup K) : ℤ :=
  -log (Valued.v ((x : 𝔸[K]).2 v))
theorem valued_ne_zero (v : HeightOneSpectrum (𝓞 K)) (x : IdeleGroup K) : Valued.v ((x : 𝔸[K]).2 v) ≠ 0 :=
  (Valuation.ne_zero_iff _).2 (finiteProj v x).ne_zero
theorem ord_mul (v : HeightOneSpectrum (𝓞 K)) (x y : IdeleGroup K) : ord v (x * y) = ord v x + ord v y := by
  have h : ((x * y : IdeleGroup K) : 𝔸[K]).2 v = (x : 𝔸[K]).2 v * (y : 𝔸[K]).2 v := rfl; rw [ord, ord, ord, h, map_mul, log_mul (valued_ne_zero v x) (valued_ne_zero v y), neg_add]
@[simp]
theorem ord_one (v : HeightOneSpectrum (𝓞 K)) : ord v (1 : IdeleGroup K) = 0 := by have h : ((1 : IdeleGroup K) : 𝔸[K]).2 v = 1 := rfl; rw [ord, h, map_one, log_one, neg_zero]
theorem ord_inv (v : HeightOneSpectrum (𝓞 K)) (x : IdeleGroup K) : ord v x⁻¹ = -ord v x := by have h := ord_mul v x x⁻¹; rw [mul_inv_cancel, ord_one] at h; omega
theorem mem_adicCompletionIntegers_iff_ord_nonneg (v : HeightOneSpectrum (𝓞 K)) (x : IdeleGroup K) : (x : 𝔸[K]).2 v ∈ v.adicCompletionIntegers K ↔ 0 ≤ ord v x := by
  rw [mem_adicCompletionIntegers, ord, neg_nonneg, log_le_iff_le_exp (valued_ne_zero v x), exp_zero]
theorem ord_eq_zero_iff (v : HeightOneSpectrum (𝓞 K)) (x : IdeleGroup K) : ord v x = 0 ↔ (x : 𝔸[K]).2 v ∈ v.adicCompletionIntegers K ∧ ((x⁻¹ : IdeleGroup K) : 𝔸[K]).2 v ∈ v.adicCompletionIntegers K := by
  rw [mem_adicCompletionIntegers_iff_ord_nonneg, mem_adicCompletionIntegers_iff_ord_nonneg, ord_inv]
  omega
theorem eventually_ord_eq_zero (x : IdeleGroup K) : ∀ᶠ v in Filter.cofinite, ord v x = 0 :=
  ((x : 𝔸[K]).2.2.and ((x⁻¹ : IdeleGroup K) : 𝔸[K]).2.2).mono fun v hv ↦
    (ord_eq_zero_iff v x).2 hv
theorem mem_standardOpenSubgroup_iff_ord {x : IdeleGroup K} :
    x ∈ standardOpenSubgroup K ↔ ∀ v : HeightOneSpectrum (𝓞 K), ord v x = 0 := by
  simp only [mem_standardOpenSubgroup, ord_eq_zero_iff]
theorem ord_finiteEmbedding_self (v : HeightOneSpectrum (𝓞 K)) (a : (v.adicCompletion K)ˣ) : ord v (finiteEmbedding v a) = -log (Valued.v (a : v.adicCompletion K)) := by rw [ord, ← coe_finiteProj, finiteProj_finiteEmbedding]
theorem ord_finiteEmbedding_of_ne {v w : HeightOneSpectrum (𝓞 K)} (h : w ≠ v)
    (a : (v.adicCompletion K)ˣ) : ord w (finiteEmbedding v a) = 0 := by
  rw [ord, ← coe_finiteProj, finiteProj_finiteEmbedding_of_ne h, Units.val_one, map_one, log_one, neg_zero]
theorem ord_diagonal (v : HeightOneSpectrum (𝓞 K)) (a : Kˣ) : ord v (diagonal K a) = -log (v.valuation K a) := by rw [ord, ← coe_finiteProj, coe_finiteProj_diagonal, valuedAdicCompletion_eq_valuation']
open Classical in
theorem exists_ord_eq_ite (v : HeightOneSpectrum (𝓞 K)) : ∃ x : IdeleGroup K, ∀ w, ord w x = if w = v then 1 else 0 := by
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer K
  have hne : ((π : K) : v.adicCompletion K) ≠ 0 := by
    intro h
    have h' := congrArg Valued.v h; rw [valuedAdicCompletion_eq_valuation', hπ, map_zero] at h'; exact exp_ne_zero h'
  refine ⟨finiteEmbedding v (Units.mk0 _ hne), fun w ↦ ?_⟩
  split_ifs with h
  · subst h
    rw [ord_finiteEmbedding_self, Units.val_mk0, valuedAdicCompletion_eq_valuation', hπ, log_exp, neg_neg]
  · exact ord_finiteEmbedding_of_ne h _
theorem finite_mulSupport_primeIdealUnit_zpow_ord (x : IdeleGroup K) : (Function.mulSupport fun v ↦ primeIdealUnit (K := K) v ^ ord v x).Finite :=
  (Filter.eventually_cofinite.1 (eventually_ord_eq_zero x)).subset fun v hv h ↦
    hv (by simp only [h, zpow_zero])
def toFractionalIdeal : IdeleGroup K →* (FractionalIdeal (𝓞 K)⁰ K)ˣ where
  toFun x := ∏ᶠ v, primeIdealUnit v ^ ord v x
  map_one' := by simp only [ord_one, zpow_zero, finprod_one]
  map_mul' x y := by
    simp only [ord_mul, zpow_add]
    exact finprod_mul_distrib (finite_mulSupport_primeIdealUnit_zpow_ord x) (finite_mulSupport_primeIdealUnit_zpow_ord y)
@[simp]
theorem count_toFractionalIdeal (v : HeightOneSpectrum (𝓞 K)) (x : IdeleGroup K) : count K v ((toFractionalIdeal x : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) = ord v x :=
  count_finprod_primeIdealUnit_zpow _ (eventually_ord_eq_zero x) v
theorem toFractionalIdeal_eq_iff {x : IdeleGroup K} {I : (FractionalIdeal (𝓞 K)⁰ K)ˣ} : toFractionalIdeal x = I ↔
      ∀ v : HeightOneSpectrum (𝓞 K), ord v x = count K v (I : FractionalIdeal (𝓞 K)⁰ K) := by
  simp only [fractionalIdealUnits_eq_iff, count_toFractionalIdeal]
theorem ker_toFractionalIdeal : (toFractionalIdeal (K := K)).ker = standardOpenSubgroup K := by
  ext x
  rw [MonoidHom.mem_ker, toFractionalIdeal_eq_iff, mem_standardOpenSubgroup_iff_ord]
  simp only [Units.val_one, count_one]
open Classical in
theorem primeIdealUnit_mem_range (v : HeightOneSpectrum (𝓞 K)) : primeIdealUnit v ∈ (toFractionalIdeal (K := K)).range := by
  obtain ⟨x, hx⟩ := exists_ord_eq_ite v; refine ⟨x, toFractionalIdeal_eq_iff.2 fun w ↦ ?_⟩; rw [hx, count_primeIdealUnit]
theorem toFractionalIdeal_surjective : Function.Surjective (toFractionalIdeal (K := K)) := by
  intro I
  have h : I ∈ (toFractionalIdeal (K := K)).range := by
    rw [← finprod_primeIdealUnit_zpow_count I]
    exact finprod_induction (· ∈ (toFractionalIdeal (K := K)).range) (one_mem _) (fun _ _ ↦ mul_mem) fun v ↦ zpow_mem (primeIdealUnit_mem_range v) _
  exact h
theorem toFractionalIdeal_diagonal (a : Kˣ) : toFractionalIdeal (diagonal K a) = toPrincipalIdeal (𝓞 K) K a := by
  rw [toFractionalIdeal_eq_iff]
  intro v; rw [ord_diagonal, coe_toPrincipalIdeal, count_spanSingleton v a.ne_zero]
theorem classGroup_mk_eq_one_iff {I : (FractionalIdeal (𝓞 K)⁰ K)ˣ} :
    ClassGroup.mk K I = 1 ↔ I ∈ (toPrincipalIdeal (𝓞 K) K).range := by
  rw [ClassGroup.mk_eq_one_iff, mem_principal_ideals_iff]
  constructor
  · intro hI
    obtain ⟨x, hx⟩ := Submodule.IsPrincipal.principal (S := (I : Submodule (𝓞 K) K)); refine ⟨x, ?_⟩; symm; apply Subtype.coe_injective; simp only [FractionalIdeal.val_eq_coe, hx, coe_spanSingleton]
  · rintro ⟨x, hx⟩
    exact ⟨⟨x, by rw [← hx, coe_spanSingleton]⟩⟩
theorem classGroup_mk_surjective : Function.Surjective (ClassGroup.mk K : (FractionalIdeal (𝓞 K)⁰ K)ˣ →* ClassGroup (𝓞 K)) :=
  fun c ↦ ClassGroup.induction K (P := fun c ↦ ∃ I, ClassGroup.mk K I = c) (fun I ↦ ⟨I, rfl⟩) c
def toClassGroup : IdeleGroup K →* ClassGroup (𝓞 K) :=
  (ClassGroup.mk K).comp toFractionalIdeal
theorem toClassGroup_apply (x : IdeleGroup K) : toClassGroup x = ClassGroup.mk K (toFractionalIdeal x) :=
  rfl
theorem toClassGroup_surjective : Function.Surjective (toClassGroup (K := K)) :=
  classGroup_mk_surjective.comp toFractionalIdeal_surjective
theorem ker_toClassGroup : (toClassGroup (K := K)).ker = (diagonal K).range ⊔ standardOpenSubgroup K := by
  apply le_antisymm
  · intro x hx
    rw [MonoidHom.mem_ker, toClassGroup_apply, classGroup_mk_eq_one_iff] at hx
    obtain ⟨a, ha⟩ := hx
    have hu : (diagonal K a)⁻¹ * x ∈ standardOpenSubgroup K := by rw [← ker_toFractionalIdeal, MonoidHom.mem_ker, map_mul, map_inv, toFractionalIdeal_diagonal, ha, inv_mul_cancel]
    exact Subgroup.mem_sup.2 ⟨diagonal K a, ⟨a, rfl⟩, _, hu, mul_inv_cancel_left _ _⟩
  · refine sup_le ?_ ?_
    · rintro _ ⟨a, rfl⟩
      rw [MonoidHom.mem_ker, toClassGroup_apply, toFractionalIdeal_diagonal, classGroup_mk_eq_one_iff]
      exact ⟨a, rfl⟩
    · intro x hx
      rw [← ker_toFractionalIdeal, MonoidHom.mem_ker] at hx
      rw [MonoidHom.mem_ker, toClassGroup_apply, hx, map_one]
def quotientEquivClassGroup : IdeleGroup K ⧸ ((diagonal K).range ⊔ standardOpenSubgroup K) ≃* ClassGroup (𝓞 K) :=
  (QuotientGroup.quotientMulEquivOfEq ker_toClassGroup.symm).trans (QuotientGroup.quotientKerEquivOfSurjective _ toClassGroup_surjective)
@[simp]
theorem quotientEquivClassGroup_mk (x : IdeleGroup K) : quotientEquivClassGroup (QuotientGroup.mk x : IdeleGroup K ⧸ ((diagonal K).range ⊔ standardOpenSubgroup K)) = ClassGroup.mk K (toFractionalIdeal x) :=
  rfl
end IdeleGroup
namespace IdeleClassGroup
open IdeleGroup
def toClassGroup : IdeleClassGroup K →* ClassGroup (𝓞 K) :=
  QuotientGroup.lift _ IdeleGroup.toClassGroup
    (le_sup_left.trans_eq (ker_toClassGroup (K := K)).symm)
@[simp]
theorem toClassGroup_mk (x : IdeleGroup K) : toClassGroup (mk K x) = IdeleGroup.toClassGroup x :=
  rfl
theorem toClassGroup_surjective : Function.Surjective (toClassGroup (K := K)) := by
  intro c
  obtain ⟨x, rfl⟩ := IdeleGroup.toClassGroup_surjective c; exact ⟨mk K x, rfl⟩
theorem ker_toClassGroup : (toClassGroup (K := K)).ker = (standardOpenSubgroup K).map (mk K) := by
  ext c
  obtain ⟨x, rfl⟩ := mk_surjective K c; rw [MonoidHom.mem_ker, toClassGroup_mk, ← MonoidHom.mem_ker, IdeleGroup.ker_toClassGroup]; constructor
  · intro hx
    obtain ⟨_, ⟨a, rfl⟩, u, hu, rfl⟩ := Subgroup.mem_sup.1 hx; exact ⟨u, hu, by rw [map_mul, mk_diagonal]; exact (one_mul (mk K u)).symm⟩
  · rintro ⟨u, hu, h⟩
    have h1 : mk K (x * u⁻¹) = 1 := by rw [map_mul, map_inv, h, mul_inv_cancel]
    rw [← MonoidHom.mem_ker, ker_mk] at h1
    rw [← inv_mul_cancel_right x u]
    exact mul_mem (Subgroup.mem_sup_left h1) (Subgroup.mem_sup_right hu)
instance : ((standardOpenSubgroup K).map (mk K)).Normal :=
  ⟨fun n hn g ↦ by rwa [mul_comm g n, mul_inv_cancel_right]⟩
def quotientEquivClassGroup : IdeleClassGroup K ⧸ (standardOpenSubgroup K).map (mk K) ≃* ClassGroup (𝓞 K) :=
  (QuotientGroup.quotientMulEquivOfEq (ker_toClassGroup (K := K)).symm).trans (QuotientGroup.quotientKerEquivOfSurjective _ toClassGroup_surjective)
end IdeleClassGroup
end Sec2_ClassGroup


/-! ### StandardOpenEquiv -/
section Sec2_StandardOpenEquiv
open NumberField IsDedekindDomain Topology
open scoped NumberField.AdeleRing
theorem continuous_equiv_symm_of_eq {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ Y) (h : X ≃ₜ Y) (he : ∀ x, e x = h x) : Continuous e.symm :=
  h.symm.continuous.congr fun y ↦ e.injective (by rw [e.apply_symm_apply, he, h.apply_symm_apply])
def unitsContinuousMulEquiv {A B : Type*} [Monoid A] [Monoid B] [TopologicalSpace A] [TopologicalSpace B] (e : A ≃* B) (h₁ : Continuous e) (h₂ : Continuous e.symm) : Aˣ ≃ₜ* Bˣ where
  toMulEquiv := Units.mapEquiv e
  continuous_toFun := Units.continuous_map (f := e.toMonoidHom) h₁
  continuous_invFun := Units.continuous_map (f := e.symm.toMonoidHom) h₂
def continuousMulEquivProdCongr {A B C D : Type*} [Monoid A] [Monoid B] [Monoid C] [Monoid D] [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C] [TopologicalSpace D] (e₁ : A ≃ₜ* B) (e₂ : C ≃ₜ* D) : A × C ≃ₜ* B × D where
  toMulEquiv := MulEquiv.prodCongr e₁.toMulEquiv e₂.toMulEquiv
  continuous_toFun := by exact (e₁.continuous.comp continuous_fst).prodMk (e₂.continuous.comp continuous_snd)
  continuous_invFun := by exact (e₁.symm.continuous.comp continuous_fst).prodMk (e₂.symm.continuous.comp continuous_snd)
def openSubgroupEquivQuotient {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] (H N : Subgroup G) (hH : IsOpen (H : Set G)) (hinf : H ⊓ N = ⊥)
    (hsup : H ⊔ N = ⊤) : H ≃ₜ* G ⧸ N :=
  let f : H →* G ⧸ N := (QuotientGroup.mk' N).comp H.subtype
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro h hh
    have h2 : (h : G) ∈ H ⊓ N := ⟨h.2, (QuotientGroup.eq_one_iff _).1 hh⟩; rw [hinf, Subgroup.mem_bot] at h2; exact Subtype.ext h2
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N y
    have hg : g ∈ H ⊔ N := hsup ▸ Subgroup.mem_top g
    obtain ⟨h, hh, n, hn, rfl⟩ := Subgroup.mem_sup.1 hg; refine ⟨⟨h, hh⟩, ?_⟩; show ((h : G) : G ⧸ N) = ((h * n : G) : G ⧸ N); exact QuotientGroup.eq.2 (by rwa [inv_mul_cancel_left])
  let e : H ≃* G ⧸ N := MulEquiv.ofBijective f ⟨hinj, hsurj⟩
  have hc : Continuous e := QuotientGroup.continuous_mk.comp continuous_subtype_val
  have ho : IsOpenMap e := QuotientGroup.isOpenMap_coe.comp hH.isOpenMap_subtype_val
  { toMulEquiv := e
    continuous_toFun := hc
    continuous_invFun := (e.toEquiv.toHomeomorphOfContinuousOpen hc ho).symm.continuous }
@[simp]
theorem openSubgroupEquivQuotient_apply {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] (H N : Subgroup G) (hH : IsOpen (H : Set G)) (hinf : H ⊓ N = ⊥) (hsup : H ⊔ N = ⊤) (h : H) :
    openSubgroupEquivQuotient H N hH hinf hsup h = ((h : G) : G ⧸ N) :=
  rfl
namespace IdeleGroup
variable {K : Type*} [Field K] [NumberField K]
def localIntegerUnit (v : HeightOneSpectrum (𝓞 K)) (x : standardOpenSubgroup K) : (v.adicCompletionIntegers K)ˣ where
  val := ⟨((x : IdeleGroup K) : 𝔸[K]).2 v, ((mem_standardOpenSubgroup K).1 x.2 v).1⟩
  inv := ⟨(((x : IdeleGroup K)⁻¹ : IdeleGroup K) : 𝔸[K]).2 v, ((mem_standardOpenSubgroup K).1 x.2 v).2⟩
  val_inv := Subtype.ext (congrArg (fun y : 𝔸[K] ↦ y.2 v) (x : IdeleGroup K).mul_inv)
  inv_val := Subtype.ext (congrArg (fun y : 𝔸[K] ↦ y.2 v) (x : IdeleGroup K).inv_mul)
@[simp]
theorem coe_localIntegerUnit (v : HeightOneSpectrum (𝓞 K)) (x : standardOpenSubgroup K) : (((localIntegerUnit v x : (v.adicCompletionIntegers K)ˣ) : v.adicCompletionIntegers K) : v.adicCompletion K) = ((x : IdeleGroup K) : 𝔸[K]).2 v :=
  rfl
theorem continuous_localIntegerUnit (v : HeightOneSpectrum (𝓞 K)) : Continuous (localIntegerUnit (K := K) v) := by
  rw [Units.continuous_iff]
  constructor
  · exact ((Units.continuous_val.comp (continuous_finiteProj v)).comp
      continuous_subtype_val).subtype_mk _
  · exact ((Units.continuous_coe_inv.comp (continuous_finiteProj v)).comp
      continuous_subtype_val).subtype_mk _
def ofIntegerUnits (a : (InfiniteAdeleRing K)ˣ) (u : Π v : HeightOneSpectrum (𝓞 K), (v.adicCompletionIntegers K)ˣ) : IdeleGroup K where
  val := ((a : InfiniteAdeleRing K), _root_.RestrictedProduct.structureMap _ _ _ fun v ↦ (u v : v.adicCompletionIntegers K))
  inv := (((a⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K), _root_.RestrictedProduct.structureMap _ _ _ fun v ↦ ((u v)⁻¹ : (v.adicCompletionIntegers K)ˣ))
  val_inv := Prod.ext a.mul_inv (Subtype.ext (funext fun v ↦ congrArg Subtype.val (u v).mul_inv))
  inv_val := Prod.ext a.inv_mul (Subtype.ext (funext fun v ↦ congrArg Subtype.val (u v).inv_mul))
@[simp]
theorem coe_ofIntegerUnits_fst (a : (InfiniteAdeleRing K)ˣ) (u : Π v : HeightOneSpectrum (𝓞 K), (v.adicCompletionIntegers K)ˣ) : ((ofIntegerUnits a u : IdeleGroup K) : 𝔸[K]).1 = a :=
  rfl
@[simp]
theorem coe_ofIntegerUnits_snd (a : (InfiniteAdeleRing K)ˣ) (u : Π v : HeightOneSpectrum (𝓞 K), (v.adicCompletionIntegers K)ˣ) (v : HeightOneSpectrum (𝓞 K)) : ((ofIntegerUnits a u : IdeleGroup K) : 𝔸[K]).2 v =
      ((u v : v.adicCompletionIntegers K) : v.adicCompletion K) :=
  rfl
theorem ofIntegerUnits_mem (a : (InfiniteAdeleRing K)ˣ) (u : Π v : HeightOneSpectrum (𝓞 K), (v.adicCompletionIntegers K)ˣ) : ofIntegerUnits a u ∈ standardOpenSubgroup K :=
  (mem_standardOpenSubgroup K).2 fun v ↦
    ⟨(u v : v.adicCompletionIntegers K).2, (((u v)⁻¹ : (v.adicCompletionIntegers K)ˣ) : v.adicCompletionIntegers K).2⟩
theorem continuous_ofIntegerUnits : Continuous (fun p : (InfiniteAdeleRing K)ˣ × (Π v : HeightOneSpectrum (𝓞 K), (v.adicCompletionIntegers K)ˣ) ↦
      ofIntegerUnits p.1 p.2) := by
  rw [Units.continuous_iff]
  constructor
  · exact (Units.continuous_val.comp continuous_fst).prodMk (_root_.RestrictedProduct.isEmbedding_structureMap.continuous.comp (continuous_pi fun v ↦ Units.continuous_val.comp ((continuous_apply v).comp continuous_snd)))
  · exact (Units.continuous_coe_inv.comp continuous_fst).prodMk (_root_.RestrictedProduct.isEmbedding_structureMap.continuous.comp (continuous_pi fun v ↦
          Units.continuous_coe_inv.comp ((continuous_apply v).comp continuous_snd)))
variable (K) in
def standardOpenSubgroupEquiv : standardOpenSubgroup K ≃ₜ* (InfiniteAdeleRing K)ˣ × Π v : HeightOneSpectrum (𝓞 K), (v.adicCompletionIntegers K)ˣ where
  toFun x := (toInfinite K (x : IdeleGroup K), fun v ↦ localIntegerUnit v x)
  invFun p := ⟨ofIntegerUnits p.1 p.2, ofIntegerUnits_mem p.1 p.2⟩
  left_inv _ := Subtype.ext (Units.ext (Prod.ext rfl (Subtype.ext (funext fun _ ↦ rfl))))
  right_inv _ := Prod.ext (Units.ext rfl) (funext fun _ ↦ Units.ext (Subtype.ext rfl))
  map_mul' x y := Prod.ext (map_mul (toInfinite K) (x : IdeleGroup K) y) (funext fun _ ↦ Units.ext (Subtype.ext rfl))
  continuous_toFun := ((continuous_toInfinite K).comp continuous_subtype_val).prodMk (continuous_pi fun v ↦ continuous_localIntegerUnit v)
  continuous_invFun := continuous_ofIntegerUnits.subtype_mk _
@[simp]
theorem standardOpenSubgroupEquiv_apply_fst (x : standardOpenSubgroup K) : (standardOpenSubgroupEquiv K x).1 = toInfinite K (x : IdeleGroup K) :=
  rfl
@[simp]
theorem standardOpenSubgroupEquiv_apply_snd (x : standardOpenSubgroup K) (v : HeightOneSpectrum (𝓞 K)) : (standardOpenSubgroupEquiv K x).2 v = localIntegerUnit v x :=
  rfl
@[simp]
theorem coe_standardOpenSubgroupEquiv_symm_apply (p : (InfiniteAdeleRing K)ˣ × Π v : HeightOneSpectrum (𝓞 K), (v.adicCompletionIntegers K)ˣ) : (((standardOpenSubgroupEquiv K).symm p : standardOpenSubgroup K) : IdeleGroup K) =
      ofIntegerUnits p.1 p.2 :=
  rfl
end IdeleGroup
end Sec2_StandardOpenEquiv


/-! ### SIdeleGroups -/
section Sec2_SIdeleGroups
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero FractionalIdeal
open scoped NumberField.AdeleRing nonZeroDivisors
variable {K : Type*} [Field K] [NumberField K]
namespace IdeleGroup
def sIdeles (S : Set (HeightOneSpectrum (𝓞 K))) : Subgroup (IdeleGroup K) where
  carrier := {x | ∀ v ∉ S, ord v x = 0}
  one_mem' v _ := ord_one v
  mul_mem' {x y} hx hy v hv := by rw [ord_mul, hx v hv, hy v hv, add_zero]
  inv_mem' {x} hx v hv := by rw [ord_inv, hx v hv, neg_zero]
variable (S : Set (HeightOneSpectrum (𝓞 K)))
theorem mem_sIdeles {x : IdeleGroup K} : x ∈ sIdeles S ↔ ∀ v ∉ S, ord v x = 0 :=
  Iff.rfl
theorem mem_sIdeles_iff {x : IdeleGroup K} : x ∈ sIdeles S ↔ ∀ v ∉ S, (x : 𝔸[K]).2 v ∈ v.adicCompletionIntegers K ∧
      ((x⁻¹ : IdeleGroup K) : 𝔸[K]).2 v ∈ v.adicCompletionIntegers K := by
  simp only [mem_sIdeles, ord_eq_zero_iff]
theorem standardOpenSubgroup_le_sIdeles : standardOpenSubgroup K ≤ sIdeles S :=
  fun _ hx v _ ↦ mem_standardOpenSubgroup_iff_ord.1 hx v
theorem sIdeles_mono {S T : Set (HeightOneSpectrum (𝓞 K))} (h : S ⊆ T) :
    sIdeles S ≤ sIdeles T :=
  fun _ hx v hv ↦ hx v fun hvS ↦ hv (h hvS)
theorem neg_log_eq_zero_iff {y : ℤᵐ⁰} (hy : y ≠ 0) : -log y = 0 ↔ y = 1 := by
  rw [neg_eq_zero]
  constructor
  · intro h
    rw [← exp_log hy, h, exp_zero]
  · rintro rfl
    exact log_one
theorem diagonal_mem_sIdeles_iff (a : Kˣ) : diagonal K a ∈ sIdeles S ↔ a ∈ S.unit K := by
  have ha : ∀ v : HeightOneSpectrum (𝓞 K), v.valuation K (a : K) ≠ 0 := fun v ↦
    (Valuation.ne_zero_iff _).2 a.ne_zero
  simp only [mem_sIdeles, ord_diagonal, neg_log_eq_zero_iff (ha _)]
  rfl
theorem exists_diagonal_mul_of_sup_eq_top (h : (diagonal K).range ⊔ sIdeles S = ⊤) (x : IdeleGroup K) : ∃ a : Kˣ, ∃ s ∈ sIdeles S, diagonal K a * s = x := by
  have hx : x ∈ (diagonal K).range ⊔ sIdeles S := h ▸ Subgroup.mem_top x
  obtain ⟨_, ⟨a, rfl⟩, s, hs, hx⟩ := Subgroup.mem_sup.1 hx; exact ⟨a, s, hs, hx⟩
theorem sup_sIdeles_eq_top_of_subset {S T : Set (HeightOneSpectrum (𝓞 K))} (hST : S ⊆ T)
    (h : (diagonal K).range ⊔ sIdeles S = ⊤) : (diagonal K).range ⊔ sIdeles T = ⊤ :=
  eq_top_iff.2 (h.symm.le.trans (sup_le_sup_left (sIdeles_mono hST) _))
theorem exists_finset_sup_sIdeles_eq_top : ∃ S : Finset (HeightOneSpectrum (𝓞 K)),
      (diagonal K).range ⊔ sIdeles (S : Set (HeightOneSpectrum (𝓞 K))) = ⊤ := by
  classical
  choose x hx using toClassGroup_surjective (K := K)
  let S : Finset (HeightOneSpectrum (𝓞 K)) := Finset.univ.biUnion fun c ↦
    (Filter.eventually_cofinite.1 (eventually_ord_eq_zero (x c))).toFinset
  have hxS : ∀ c, x c ∈ sIdeles (S : Set (HeightOneSpectrum (𝓞 K))) := by intro c v hv; by_contra h; exact hv (Finset.mem_biUnion.2 ⟨c, Finset.mem_univ c, Set.Finite.mem_toFinset _ |>.2 h⟩)
  refine ⟨S, eq_top_iff.2 fun y _ ↦ ?_⟩
  have hker : y * (x (toClassGroup y))⁻¹ ∈ (toClassGroup (K := K)).ker := by rw [MonoidHom.mem_ker, map_mul, map_inv, hx, mul_inv_cancel]
  rw [ker_toClassGroup] at hker
  have h := mul_mem (sup_le_sup_left (standardOpenSubgroup_le_sIdeles _) _ hker) (Subgroup.mem_sup_right (hxS (toClassGroup y))); rwa [inv_mul_cancel_right] at h
def sUnitsToSIdeles : S.unit K →* sIdeles S :=
  ((diagonal K).comp (S.unit K).subtype).codRestrict (sIdeles S) fun a ↦
    (diagonal_mem_sIdeles_iff S a).2 a.2
@[simp]
theorem coe_sUnitsToSIdeles (a : S.unit K) : (sUnitsToSIdeles S a : IdeleGroup K) = diagonal K a :=
  rfl
def sIdelesToIdeleClassGroup : sIdeles S →* IdeleClassGroup K :=
  (IdeleClassGroup.mk K).comp (sIdeles S).subtype
@[simp]
theorem sIdelesToIdeleClassGroup_apply (s : sIdeles S) : sIdelesToIdeleClassGroup S s = IdeleClassGroup.mk K s :=
  rfl
theorem sUnitsToSIdeles_injective : Function.Injective (sUnitsToSIdeles S) := fun _ _ h ↦
  Subtype.ext (diagonal_injective K (congrArg Subtype.val h))
theorem range_sUnitsToSIdeles : (sUnitsToSIdeles S).range = (sIdelesToIdeleClassGroup S).ker := by
  ext y
  constructor
  · rintro ⟨a, rfl⟩
    rw [MonoidHom.mem_ker, sIdelesToIdeleClassGroup_apply, coe_sUnitsToSIdeles]
    exact IdeleClassGroup.mk_diagonal K a
  · intro hy
    rw [MonoidHom.mem_ker, sIdelesToIdeleClassGroup_apply, ← MonoidHom.mem_ker, IdeleClassGroup.ker_mk] at hy
    obtain ⟨a, ha⟩ := hy
    have haS : a ∈ S.unit K := (diagonal_mem_sIdeles_iff S a).1 (ha ▸ y.2); exact ⟨⟨a, haS⟩, Subtype.ext ha⟩
theorem sIdelesToIdeleClassGroup_surjective_iff : Function.Surjective (sIdelesToIdeleClassGroup S) ↔ (diagonal K).range ⊔ sIdeles S = ⊤ := by
  constructor
  · intro h
    refine eq_top_iff.2 fun y _ ↦ ?_
    obtain ⟨s, hs⟩ := h (IdeleClassGroup.mk K y); rw [sIdelesToIdeleClassGroup_apply] at hs
    have hr : (s : IdeleGroup K)⁻¹ * y ∈ (diagonal K).range := by rw [← IdeleClassGroup.ker_mk, MonoidHom.mem_ker, map_mul, map_inv, hs, inv_mul_cancel]
    have h' := mul_mem (Subgroup.mem_sup_right (S := (diagonal K).range) s.2)
      (Subgroup.mem_sup_left (T := sIdeles S) hr)
    rwa [mul_inv_cancel_left] at h'
  · intro h c
    obtain ⟨y, rfl⟩ := IdeleClassGroup.mk_surjective K c
    obtain ⟨a, s, hs, rfl⟩ := exists_diagonal_mul_of_sup_eq_top S h y; refine ⟨⟨s, hs⟩, ?_⟩; rw [sIdelesToIdeleClassGroup_apply, map_mul, IdeleClassGroup.mk_diagonal]; exact (one_mul (IdeleClassGroup.mk K s)).symm
theorem sUnits_sIdeles_exact (h : (diagonal K).range ⊔ sIdeles S = ⊤) : Function.Injective (sUnitsToSIdeles S) ∧ (sUnitsToSIdeles S).range = (sIdelesToIdeleClassGroup S).ker ∧ Function.Surjective (sIdelesToIdeleClassGroup S) :=
  ⟨sUnitsToSIdeles_injective S, range_sUnitsToSIdeles S, (sIdelesToIdeleClassGroup_surjective_iff S).2 h⟩
instance : (sUnitsToSIdeles S).range.Normal :=
  ⟨fun n hn g ↦ by rwa [mul_comm g n, mul_inv_cancel_right]⟩
def sIdelesQuotientEquiv (h : (diagonal K).range ⊔ sIdeles S = ⊤) : sIdeles S ⧸ (sUnitsToSIdeles S).range ≃* IdeleClassGroup K :=
  (QuotientGroup.quotientMulEquivOfEq (range_sUnitsToSIdeles S)).trans (QuotientGroup.quotientKerEquivOfSurjective _ ((sIdelesToIdeleClassGroup_surjective_iff S).2 h))
end IdeleGroup
end Sec2_SIdeleGroups


/-! ### IndexFormula -/
section Sec2_IndexFormula
open NumberField IsDedekindDomain
section GroupLemma
variable {G C : Type*} [Group G] [Group C]
theorem index_map_mul_relIndex_ker {f : G →* C} (hf : Function.Surjective f) (W : Subgroup G)
    [W.Normal] : (W.map f).index * W.relIndex f.ker = W.index := by
  rw [Subgroup.index_map, f.range_eq_top_of_surjective hf, Subgroup.index_top, mul_one, ← Subgroup.relIndex_sup_left, mul_comm, Subgroup.relIndex_mul_index le_sup_left]
end GroupLemma
variable {K : Type*} [Field K] [NumberField K]
namespace IdeleGroup
variable (S : Set (HeightOneSpectrum (𝓞 K)))
theorem index_comap_sUnitsToSIdeles (W : Subgroup (sIdeles S)) : (W.comap (sUnitsToSIdeles S)).index = W.relIndex (sIdelesToIdeleClassGroup S).ker := by rw [Subgroup.index_comap, range_sUnitsToSIdeles]
theorem index_map_mul_index_comap (h : (diagonal K).range ⊔ sIdeles S = ⊤) (W : Subgroup (sIdeles S)) : (W.map (sIdelesToIdeleClassGroup S)).index * (W.comap (sUnitsToSIdeles S)).index = W.index := by
  rw [index_comap_sUnitsToSIdeles]
  exact index_map_mul_relIndex_ker ((sIdelesToIdeleClassGroup_surjective_iff S).2 h) W
end IdeleGroup
end Sec2_IndexFormula


/-! ### IndexProductFormula -/
section Sec2_IndexProductFormula
open NumberField IsDedekindDomain
variable {K : Type*} [Field K] [NumberField K]
theorem norm_natCast_adicCompletion_eq_one {v : HeightOneSpectrum (𝓞 K)} {n : ℕ}
    (hv : (n : 𝓞 K) ∉ v.asIdeal) : ‖(n : v.adicCompletion K)‖ = 1 := by
  have h := (FinitePlace.norm_eq_one_iff_notMem (K := K) (v := v) (n : 𝓞 K)).2 hv; rwa [map_natCast, map_natCast] at h
theorem finprod_norm_natCast_adicCompletion_mul {n : ℕ} (hn : n ≠ 0) : (∏ᶠ v : HeightOneSpectrum (𝓞 K), ‖(n : v.adicCompletion K)‖) *
      (n : ℝ) ^ Module.finrank ℚ K = 1 := by
  have hn' : (n : K) ≠ 0 := Nat.cast_ne_zero.2 hn
  have h := FinitePlace.prod_eq_inv_abs_norm hn'; simp only [← finprod_comp_equiv FinitePlace.equivHeightOneSpectrum.symm, FinitePlace.equivHeightOneSpectrum_symm_apply, map_natCast] at h
  rw [h, ← map_natCast (algebraMap ℚ K) n, Algebra.norm_algebraMap]
  have hpos : (0 : ℝ) < (n : ℝ) ^ Module.finrank ℚ K := by positivity
  push_cast; rw [abs_of_pos hpos, inv_mul_cancel₀ hpos.ne']
theorem prod_norm_natCast_adicCompletion_mul {n : ℕ} (hn : n ≠ 0) (S : Finset (HeightOneSpectrum (𝓞 K))) (hS : ∀ v, (n : 𝓞 K) ∈ v.asIdeal → v ∈ S) :
    (∏ v ∈ S, ‖(n : v.adicCompletion K)‖) * (n : ℝ) ^ Module.finrank ℚ K = 1 := by
  rw [← finprod_eq_prod_of_mulSupport_subset]
  · exact finprod_norm_natCast_adicCompletion_mul hn
  · intro v hv
    by_contra h
    exact hv (norm_natCast_adicCompletion_eq_one fun h' ↦ h (hS v h'))
theorem prod_norm_natCast_infinitePlaceCompletion_pow_mult (n : ℕ) : ∏ w : InfinitePlace K, ‖(n : w.Completion)‖ ^ w.mult = (n : ℝ) ^ Module.finrank ℚ K := by
  have h := InfinitePlace.prod_eq_abs_norm (n : K)
  have hw : ∀ w : InfinitePlace K, ‖(n : w.Completion)‖ = w (n : K) := fun w ↦ by
    rw [← map_natCast (algebraMap K w.Completion) n]
    exact InfinitePlace.Completion.norm_coe (K := K) (v := w) _
  simp_rw [hw, h, ← map_natCast (algebraMap ℚ K) n, Algebra.norm_algebraMap]
  push_cast; exact abs_of_nonneg (by positivity)
theorem prod_norm_natCast_mul_prod_infinitePlace {n : ℕ} (hn : n ≠ 0) (S : Finset (HeightOneSpectrum (𝓞 K))) (hS : ∀ v, (n : 𝓞 K) ∈ v.asIdeal → v ∈ S) : (∏ v ∈ S, ‖(n : v.adicCompletion K)‖) *
      ∏ w : InfinitePlace K, ‖(n : w.Completion)‖ ^ w.mult = 1 := by
  rw [prod_norm_natCast_infinitePlaceCompletion_pow_mult]
  exact prod_norm_natCast_adicCompletion_mul hn S hS
end Sec2_IndexProductFormula


section Sec_ArchPowIndex
section Archimedean
theorem exists_pos_real_pow_eq {x : ℝ} (hx : 0 < x) {n : ℕ} (hn : n ≠ 0) :
    ∃ y : ℝ, 0 < y ∧ y ^ n = x :=
  ⟨x ^ (n⁻¹ : ℝ), Real.rpow_pos_of_pos hx _, Real.rpow_inv_natCast_pow hx.le hn⟩
theorem mem_range_powMonoidHom_real_iff_of_even {n : ℕ} (hn : n ≠ 0) (he : Even n) (x : ℝˣ) :
    x ∈ (powMonoidHom n : ℝˣ →* ℝˣ).range ↔ 0 < (x : ℝ) := by
  rw [MonoidHom.mem_range]
  constructor
  · rintro ⟨y, rfl⟩
    rw [powMonoidHom_apply, Units.val_pow_eq_pow_val]
    exact he.pow_pos y.ne_zero
  · intro hx
    obtain ⟨y, hy, hyx⟩ := exists_pos_real_pow_eq hx hn; refine ⟨Units.mk0 y hy.ne', ?_⟩; ext; rw [powMonoidHom_apply, Units.val_pow_eq_pow_val, Units.val_mk0, hyx]
theorem range_powMonoidHom_real_of_odd {n : ℕ} (ho : Odd n) :
    (powMonoidHom n : ℝˣ →* ℝˣ).range = ⊤ := by
  have hn : n ≠ 0 := by rintro rfl; simp at ho
  refine eq_top_iff.2 fun x _ ↦ ?_
  rw [MonoidHom.mem_range]
  rcases lt_or_gt_of_ne x.ne_zero with hx | hx
  · obtain ⟨y, hy, hyx⟩ := exists_pos_real_pow_eq (neg_pos.2 hx) hn
    refine ⟨Units.mk0 (-y) (neg_ne_zero.2 hy.ne'), ?_⟩
    ext
    rw [powMonoidHom_apply, Units.val_pow_eq_pow_val, Units.val_mk0, ho.neg_pow, hyx, neg_neg]
  · obtain ⟨y, hy, hyx⟩ := exists_pos_real_pow_eq hx hn
    refine ⟨Units.mk0 y hy.ne', ?_⟩
    ext
    rw [powMonoidHom_apply, Units.val_pow_eq_pow_val, Units.val_mk0, hyx]
theorem index_range_powMonoidHom_real_of_even {n : ℕ} (hn : n ≠ 0) (he : Even n) :
    (powMonoidHom n : ℝˣ →* ℝˣ).range.index = 2 := by
  rw [Subgroup.index_eq_two_iff]
  refine ⟨-1, fun b ↦ ?_⟩
  rw [mem_range_powMonoidHom_real_iff_of_even hn he, mem_range_powMonoidHom_real_iff_of_even hn he, Units.val_mul, Units.val_neg, Units.val_one, mul_neg_one]
  rcases lt_or_gt_of_ne b.ne_zero with hb | hb
  · exact Or.inl ⟨neg_pos.2 hb, hb.not_gt⟩
  · exact Or.inr ⟨hb, by linarith⟩
theorem index_range_powMonoidHom_real_of_odd {n : ℕ} (ho : Odd n) :
    (powMonoidHom n : ℝˣ →* ℝˣ).range.index = 1 := by
  rw [range_powMonoidHom_real_of_odd ho, Subgroup.index_top]
theorem index_range_powMonoidHom_real {n : ℕ} (hn : n ≠ 0) :
    (powMonoidHom n : ℝˣ →* ℝˣ).range.index = if Even n then 2 else 1 := by
  split_ifs with he
  · exact index_range_powMonoidHom_real_of_even hn he
  · exact index_range_powMonoidHom_real_of_odd (Nat.not_even_iff_odd.1 he)
theorem range_powMonoidHom_complex {n : ℕ} (hn : n ≠ 0) :
    (powMonoidHom n : ℂˣ →* ℂˣ).range = ⊤ := by
  refine eq_top_iff.2 fun x _ ↦ ?_
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (x : ℂ) (Nat.pos_of_ne_zero hn)
  have hz0 : z ≠ 0 := by rintro rfl; rw [zero_pow hn] at hz; exact x.ne_zero hz.symm
  refine ⟨Units.mk0 z hz0, ?_⟩
  ext
  rw [powMonoidHom_apply, Units.val_pow_eq_pow_val, Units.val_mk0, hz]
theorem index_range_powMonoidHom_complex {n : ℕ} (hn : n ≠ 0) :
    (powMonoidHom n : ℂˣ →* ℂˣ).range.index = 1 := by
  rw [range_powMonoidHom_complex hn, Subgroup.index_top]
end Archimedean
end Sec_ArchPowIndex


/-! ### LocalConditionIndex -/
section Sec2_LocalConditionIndex
open NumberField IsDedekindDomain
variable {K : Type*} [Field K] [NumberField K]
theorem map_range_powMonoidHom {G H : Type*} [CommGroup G] [CommGroup H] (e : G ≃* H) (n : ℕ) :
    (powMonoidHom n : G →* G).range.map (e : G →* H) = (powMonoidHom n : H →* H).range := by
  ext y
  simp only [Subgroup.mem_map, MonoidHom.mem_range, powMonoidHom_apply]
  constructor
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨e x, by simp [map_pow]⟩
  · rintro ⟨x, rfl⟩
    exact ⟨e.symm x ^ n, ⟨e.symm x, rfl⟩, by simp [map_pow]⟩
theorem index_range_powMonoidHom_of_mulEquiv {G H : Type*} [CommGroup G] [CommGroup H] (e : G ≃* H) (n : ℕ) :
    (powMonoidHom n : G →* G).range.index = (powMonoidHom n : H →* H).range.index := by
  rw [← map_range_powMonoidHom e n, Subgroup.index_map_equiv]
omit [NumberField K] in
open Classical in
theorem index_range_powMonoidHom_infinitePlaceCompletion (w : InfinitePlace K) {n : ℕ} (hn : n ≠ 0) : (powMonoidHom n : (w.Completion)ˣ →* (w.Completion)ˣ).range.index =
      if w.IsReal ∧ Even n then 2 else 1 := by
  rcases w.isReal_or_isComplex with hw | hw
  · rw [index_range_powMonoidHom_of_mulEquiv (Units.mapEquiv (InfinitePlace.Completion.ringEquivRealOfIsReal hw).toMulEquiv) n, index_range_powMonoidHom_real hn]
    by_cases he : Even n <;> simp [hw, he]
  · rw [index_range_powMonoidHom_of_mulEquiv (Units.mapEquiv (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw).toMulEquiv) n, index_range_powMonoidHom_complex hn]
    have hw' : ¬w.IsReal := InfinitePlace.not_isReal_iff_isComplex.2 hw; simp [hw']
namespace IdeleGroup
@[simp]
theorem finiteProj_infiniteEmbedding (v : HeightOneSpectrum (𝓞 K)) (w : InfinitePlace K) (x : (w.Completion)ˣ) : finiteProj v (infiniteEmbedding w x) = 1 :=
  Units.ext rfl
@[simp]
theorem infiniteProj_finiteEmbedding (w : InfinitePlace K) (v : HeightOneSpectrum (𝓞 K)) (x : (v.adicCompletion K)ˣ) : infiniteProj w (finiteEmbedding v x) = 1 :=
  Units.ext rfl
theorem infiniteEmbedding_mem_standardOpenSubgroup (w : InfinitePlace K) (x : (w.Completion)ˣ) : infiniteEmbedding w x ∈ standardOpenSubgroup K := by
  rw [mem_standardOpenSubgroup]
  intro v; rw [← map_inv]; simp only [coe_infiniteEmbedding]; exact ⟨one_mem _, one_mem _⟩
def localSubgroup (S T : Set (HeightOneSpectrum (𝓞 K))) (H : ∀ v : HeightOneSpectrum (𝓞 K), Subgroup (v.adicCompletion K)ˣ) (H' : ∀ w : InfinitePlace K, Subgroup (w.Completion)ˣ) : Subgroup (IdeleGroup K) where
  carrier := {x | (∀ v ∈ S, finiteProj v x ∈ H v) ∧ (∀ w, infiniteProj w x ∈ H' w) ∧
    ∀ v ∉ S ∪ T, ord v x = 0}
  one_mem' := ⟨fun v _ ↦ by rw [map_one]; exact one_mem _, fun w ↦ by rw [map_one]; exact one_mem _, fun v _ ↦ ord_one v⟩
  mul_mem' {x y} hx hy := ⟨fun v hv ↦ by rw [map_mul]; exact mul_mem (hx.1 v hv) (hy.1 v hv),
    fun w ↦ by rw [map_mul]; exact mul_mem (hx.2.1 w) (hy.2.1 w),
    fun v hv ↦ by rw [ord_mul, hx.2.2 v hv, hy.2.2 v hv, add_zero]⟩
  inv_mem' {x} hx := ⟨fun v hv ↦ by rw [map_inv]; exact inv_mem (hx.1 v hv),
    fun w ↦ by rw [map_inv]; exact inv_mem (hx.2.1 w),
    fun v hv ↦ by rw [ord_inv, hx.2.2 v hv, neg_zero]⟩
variable (S T : Set (HeightOneSpectrum (𝓞 K))) (H : ∀ v : HeightOneSpectrum (𝓞 K), Subgroup (v.adicCompletion K)ˣ) (H' : ∀ w : InfinitePlace K, Subgroup (w.Completion)ˣ)
theorem mem_localSubgroup {x : IdeleGroup K} : x ∈ localSubgroup S T H H' ↔ (∀ v ∈ S, finiteProj v x ∈ H v) ∧
      (∀ w, infiniteProj w x ∈ H' w) ∧ ∀ v ∉ S ∪ T, ord v x = 0 :=
  Iff.rfl
theorem localSubgroup_le_sIdeles : localSubgroup S T H H' ≤ sIdeles (S ∪ T) :=
  fun _ hx ↦ hx.2.2
def localQuotientMap (S : Finset (HeightOneSpectrum (𝓞 K))) : sIdeles ((S : Set (HeightOneSpectrum (𝓞 K))) ∪ T) →* (∀ v : S, (v.1.adicCompletion K)ˣ ⧸ H v.1) × (∀ w : InfinitePlace K, (w.Completion)ˣ ⧸ H' w) :=
  MonoidHom.prod (MonoidHom.pi fun v ↦ (QuotientGroup.mk' (H v.1)).comp ((finiteProj v.1).comp (sIdeles _).subtype)) (MonoidHom.pi fun w ↦ (QuotientGroup.mk' (H' w)).comp ((infiniteProj w).comp (sIdeles _).subtype))
theorem ker_localQuotientMap (S : Finset (HeightOneSpectrum (𝓞 K))) : (localQuotientMap T H H' S).ker = (localSubgroup S T H H').subgroupOf (sIdeles ((S : Set (HeightOneSpectrum (𝓞 K))) ∪ T)) := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_localSubgroup]
  simp only [localQuotientMap, MonoidHom.prod_apply, Prod.mk_eq_one, funext_iff, Pi.one_apply, MonoidHom.pi_apply, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    Subgroup.coe_subtype, Subtype.forall, Finset.mem_coe]
  exact ⟨fun h ↦ ⟨h.1, h.2, x.2⟩, fun h ↦ ⟨h.1, h.2.1⟩⟩
theorem localQuotientMap_surjective (S : Finset (HeightOneSpectrum (𝓞 K))) : Function.Surjective (localQuotientMap T H H' S) := by
  classical
  rintro ⟨a, b⟩
  choose α hα using fun v : S ↦ QuotientGroup.mk_surjective (a v)
  choose β hβ using fun w ↦ QuotientGroup.mk_surjective (b w)
  let x : IdeleGroup K := (∏ v : S, finiteEmbedding v.1 (α v)) * ∏ w, infiniteEmbedding w (β w)
  have hx : x ∈ sIdeles ((S : Set (HeightOneSpectrum (𝓞 K))) ∪ T) := by
    refine mul_mem (prod_mem fun v _ ↦ ?_) (prod_mem fun w _ ↦ ?_)
    · intro u hu
      exact ord_finiteEmbedding_of_ne (fun h ↦ hu (Or.inl (by rw [h]; exact Finset.mem_coe.2 v.2))) _
    · exact standardOpenSubgroup_le_sIdeles _ (infiniteEmbedding_mem_standardOpenSubgroup w _)
  have hfin : ∀ v : S, finiteProj v.1 x = α v := by
    intro v; simp only [x, map_mul, map_prod, finiteProj_infiniteEmbedding, Finset.prod_const_one, mul_one]; rw [Finset.prod_eq_single v (fun u _ hu ↦
      finiteProj_finiteEmbedding_of_ne (fun h ↦ hu (Subtype.ext h.symm)) _) (by simp),
      finiteProj_finiteEmbedding]
  have hinf : ∀ w : InfinitePlace K, infiniteProj w x = β w := by
    intro w; simp only [x, map_mul, map_prod, infiniteProj_finiteEmbedding, Finset.prod_const_one, one_mul]; rw [Finset.prod_eq_single w (fun u _ hu ↦
      infiniteProj_infiniteEmbedding_of_ne (fun h ↦ hu h.symm) _) (by simp),
      infiniteProj_infiniteEmbedding]
  refine ⟨⟨x, hx⟩, Prod.ext (funext fun v ↦ ?_) (funext fun w ↦ ?_)⟩
  · exact (congrArg (QuotientGroup.mk (s := H v.1)) (hfin v)).trans (hα v)
  · exact (congrArg (QuotientGroup.mk (s := H' w)) (hinf w)).trans (hβ w)
theorem relIndex_localSubgroup (S : Finset (HeightOneSpectrum (𝓞 K))) : (localSubgroup S T H H').relIndex (sIdeles ((S : Set (HeightOneSpectrum (𝓞 K))) ∪ T)) = (∏ v ∈ S, (H v).index) * ∏ w : InfinitePlace K, (H' w).index := by
  have hk := Subgroup.index_ker (G' := (∀ v : S, (v.1.adicCompletion K)ˣ ⧸ H v.1) × (∀ w : InfinitePlace K, (w.Completion)ˣ ⧸ H' w)) (localQuotientMap T H H' S)
  rw [Subgroup.relIndex, ← ker_localQuotientMap, hk, MonoidHom.range_eq_top_of_surjective _ (localQuotientMap_surjective T H H' S), Subgroup.card_top, Nat.card_prod, Nat.card_pi, Nat.card_pi, ← Finset.prod_coe_sort S]
  rfl
def powerSubgroup (n : ℕ) (S T : Set (HeightOneSpectrum (𝓞 K))) : Subgroup (IdeleGroup K) :=
  localSubgroup S T (fun v ↦ (powMonoidHom n : (v.adicCompletion K)ˣ →* _).range) (fun w ↦ (powMonoidHom n : (w.Completion)ˣ →* _).range)
theorem powerSubgroup_le_sIdeles (n : ℕ) : powerSubgroup n S T ≤ sIdeles (S ∪ T) :=
  localSubgroup_le_sIdeles S T _ _
theorem relIndex_powerSubgroup (n : ℕ) (S : Finset (HeightOneSpectrum (𝓞 K))) : (powerSubgroup n S T).relIndex (sIdeles ((S : Set (HeightOneSpectrum (𝓞 K))) ∪ T)) = (∏ v ∈ S, (powMonoidHom n : (v.adicCompletion K)ˣ →* _).range.index) *
        ∏ w : InfinitePlace K, (powMonoidHom n : (w.Completion)ˣ →* _).range.index :=
  relIndex_localSubgroup T _ _ S
theorem relIndex_powerSubgroup_empty (n : ℕ) (S : Finset (HeightOneSpectrum (𝓞 K))) : (powerSubgroup n S ∅).relIndex (sIdeles (S : Set (HeightOneSpectrum (𝓞 K)))) = (∏ v ∈ S, (powMonoidHom n : (v.adicCompletion K)ˣ →* _).range.index) *
        ∏ w : InfinitePlace K, (powMonoidHom n : (w.Completion)ˣ →* _).range.index := by
  have h := relIndex_powerSubgroup (K := K) ∅ n S; rwa [Set.union_empty] at h
end IdeleGroup
end Sec2_LocalConditionIndex


/-! ### IdeleNorms -/
section Sec2_IdeleNorms
open NumberField IsDedekindDomain Topology Filter
open scoped NumberField.AdeleRing RestrictedProduct
variable (K : Type*) [Field K] [NumberField K]
namespace IdeleGroup
variable {K}
@[simp] theorem adele_fst_mul_apply (a b : 𝔸[K]) (w : InfinitePlace K) :
    (a * b).1 w = a.1 w * b.1 w := rfl
@[simp] theorem adele_snd_mul_apply (a b : 𝔸[K]) (v : HeightOneSpectrum (𝓞 K)) :
    (a * b).2 v = a.2 v * b.2 v := rfl
@[simp] theorem adele_fst_one_apply (w : InfinitePlace K) : (1 : 𝔸[K]).1 w = 1 := rfl
@[simp] theorem adele_snd_one_apply (v : HeightOneSpectrum (𝓞 K)) : (1 : 𝔸[K]).2 v = 1 := rfl
theorem norm_eq_one_of_mul_eq_one {v : HeightOneSpectrum (𝓞 K)} {a b : v.adicCompletion K} (hab : a * b = 1) (ha : a ∈ v.adicCompletionIntegers K)
    (hb : b ∈ v.adicCompletionIntegers K) : ‖a‖ = 1 := by
  have ha' : ‖a‖ ≤ 1 := (Valued.toNormedField.norm_le_one_iff).2
    ((HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 K) K v).1 ha)
  have hb' : ‖b‖ ≤ 1 := (Valued.toNormedField.norm_le_one_iff).2
    ((HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 K) K v).1 hb)
  have h1 : ‖a‖ * ‖b‖ = 1 := by rw [← norm_mul, hab, norm_one]
  nlinarith [norm_nonneg a, norm_nonneg b]
theorem finite_mul_inv (x : IdeleGroup K) (v : HeightOneSpectrum (𝓞 K)) : (x : 𝔸[K]).2 v * ((x⁻¹ : IdeleGroup K) : 𝔸[K]).2 v = 1 := by
  have h : ((x : 𝔸[K]) * ((x⁻¹ : IdeleGroup K) : 𝔸[K])).2 v = 1 := by simp
  rwa [adele_snd_mul_apply] at h
theorem infinite_mul_inv (x : IdeleGroup K) (w : InfinitePlace K) : (x : 𝔸[K]).1 w * ((x⁻¹ : IdeleGroup K) : 𝔸[K]).1 w = 1 := by
  have h : ((x : 𝔸[K]) * ((x⁻¹ : IdeleGroup K) : 𝔸[K])).1 w = 1 := by simp
  rwa [adele_fst_mul_apply] at h
theorem finite_ne_zero (x : IdeleGroup K) (v : HeightOneSpectrum (𝓞 K)) : (x : 𝔸[K]).2 v ≠ 0 :=
  left_ne_zero_of_mul_eq_one (finite_mul_inv x v)
theorem infinite_ne_zero (x : IdeleGroup K) (w : InfinitePlace K) : (x : 𝔸[K]).1 w ≠ 0 :=
  left_ne_zero_of_mul_eq_one (infinite_mul_inv x w)
theorem eventually_norm_eq_one (x : IdeleGroup K) : ∀ᶠ v : HeightOneSpectrum (𝓞 K) in cofinite, ‖(x : 𝔸[K]).2 v‖ = 1 := by
  filter_upwards [(x : 𝔸[K]).2.2, ((x⁻¹ : IdeleGroup K) : 𝔸[K]).2.2] with v h1 h2
  exact norm_eq_one_of_mul_eq_one (finite_mul_inv x v) h1 h2
theorem finite_mulSupport_norm (x : IdeleGroup K) : (Function.mulSupport fun v : HeightOneSpectrum (𝓞 K) ↦ ‖(x : 𝔸[K]).2 v‖).Finite :=
  Filter.eventually_cofinite.1 (eventually_norm_eq_one x)
def infiniteModule (x : IdeleGroup K) : ℝ :=
  ∏ w : InfinitePlace K, ‖(x : 𝔸[K]).1 w‖ ^ w.mult
def finiteModule (x : IdeleGroup K) : ℝ :=
  ∏ᶠ v : HeightOneSpectrum (𝓞 K), ‖(x : 𝔸[K]).2 v‖
theorem infiniteModule_mul (x y : IdeleGroup K) : infiniteModule (x * y) = infiniteModule x * infiniteModule y := by simp only [infiniteModule, Units.val_mul, adele_fst_mul_apply, norm_mul, mul_pow, Finset.prod_mul_distrib]
theorem finiteModule_mul (x y : IdeleGroup K) : finiteModule (x * y) = finiteModule x * finiteModule y := by
  simp only [finiteModule, Units.val_mul, adele_snd_mul_apply, norm_mul]
  exact finprod_mul_distrib (finite_mulSupport_norm x) (finite_mulSupport_norm y)
theorem infiniteModule_pos (x : IdeleGroup K) : 0 < infiniteModule x :=
  Finset.prod_pos fun w _ ↦ pow_pos (norm_pos_iff.2 (infinite_ne_zero x w)) _
theorem finiteModule_pos (x : IdeleGroup K) : 0 < finiteModule x := by
  rw [finiteModule, finprod_eq_prod _ (finite_mulSupport_norm x)]
  exact Finset.prod_pos fun v _ ↦ norm_pos_iff.2 (finite_ne_zero x v)
variable (K) in
def ideleModule : IdeleGroup K →* {r : ℝ // 0 < r} where
  toFun x := ⟨infiniteModule x * finiteModule x, mul_pos (infiniteModule_pos x) (finiteModule_pos x)⟩
  map_one' := by
    ext
    simp [infiniteModule, finiteModule]
  map_mul' x y := by
    ext
    simp only [Positive.val_mul, infiniteModule_mul, finiteModule_mul]
    ring
theorem ideleModule_apply (x : IdeleGroup K) : (ideleModule K x : ℝ) = infiniteModule x * finiteModule x :=
  rfl
theorem ideleModule_eq (x : IdeleGroup K) : (ideleModule K x : ℝ) = (∏ w : InfinitePlace K, ‖(x : 𝔸[K]).1 w‖ ^ w.mult) * ∏ᶠ v : HeightOneSpectrum (𝓞 K), ‖(x : 𝔸[K]).2 v‖ :=
  rfl
theorem continuous_infiniteModule : Continuous (infiniteModule (K := K)) :=
  continuous_finsetProd _ fun w _ ↦
    (continuous_norm.comp (Units.continuous_val.comp (continuous_infiniteProj w))).pow _
theorem finiteModule_eq_one_of_mem {x : IdeleGroup K} (hx : x ∈ standardOpenSubgroup K) :
    finiteModule x = 1 :=
  finprod_eq_one_of_forall_eq_one fun v ↦
    norm_eq_one_of_mul_eq_one (finite_mul_inv x v) ((mem_standardOpenSubgroup K).1 hx v).1 ((mem_standardOpenSubgroup K).1 hx v).2
theorem continuous_finiteModule : Continuous (finiteModule (K := K)) := by
  refine continuous_iff_continuousAt.2 fun x ↦ ?_
  have hU : (fun y ↦ x⁻¹ * y) ⁻¹' (standardOpenSubgroup K : Set (IdeleGroup K)) ∈ 𝓝 x :=
    ((isOpen_standardOpenSubgroup K).preimage (continuous_const.mul continuous_id)).mem_nhds (by simp [(standardOpenSubgroup K).one_mem])
  refine (continuousAt_const (y := finiteModule x)).congr ?_
  filter_upwards [hU] with y hy
  rw [← mul_inv_cancel_left x y, finiteModule_mul, finiteModule_eq_one_of_mem hy, mul_one]
theorem continuous_ideleModule : Continuous (ideleModule K) :=
  (continuous_infiniteModule.mul continuous_finiteModule).subtype_mk _
theorem ideleModule_infiniteEmbedding (w : InfinitePlace K) (z : (w.Completion)ˣ) : (ideleModule K (infiniteEmbedding w z) : ℝ) = ‖(z : w.Completion)‖ ^ w.mult := by
  classical
  rw [ideleModule_eq, coe_infiniteEmbedding]
  have h1 : ∏ᶠ v : HeightOneSpectrum (𝓞 K), ‖((infiniteAdeleSingle w (z : w.Completion), (1 : FiniteAdeleRing (𝓞 K) K)) : 𝔸[K]).2 v‖
      = 1 :=
    finprod_eq_one_of_forall_eq_one fun v ↦ norm_one
  rw [h1, mul_one]
  refine (Fintype.prod_eq_single w fun u hu ↦ ?_).trans ?_
  · simp [infiniteAdeleSingle_apply, Pi.mulSingle_eq_of_ne hu]
  · simp [infiniteAdeleSingle_apply]
theorem ideleModule_finiteEmbedding (v : HeightOneSpectrum (𝓞 K)) (z : (v.adicCompletion K)ˣ) : (ideleModule K (finiteEmbedding v z) : ℝ) = ‖(z : v.adicCompletion K)‖ := by
  rw [ideleModule_eq, coe_finiteEmbedding]
  have h1 : ∏ w : InfinitePlace K, ‖((1 : InfiniteAdeleRing K), finiteAdeleSingle v (z : v.adicCompletion K)).1 w‖ ^ w.mult
      = 1 :=
    Finset.prod_eq_one fun w _ ↦ (by rw [norm_one, one_pow] : ‖(1 : w.Completion)‖ ^ w.mult = 1)
  rw [h1, one_mul]
  refine (finprod_eq_single _ v fun u hu ↦ ?_).trans ?_
  · simp [finiteAdeleSingle_apply_of_ne hu]
  · simp
theorem ideleModule_surjective : Function.Surjective (ideleModule K) := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace K) := inferInstance; rintro ⟨t, ht⟩
  obtain ⟨z, hz0, hz⟩ : ∃ z : w.Completion, z ≠ 0 ∧ ‖z‖ ^ w.mult = t := by
    rcases w.isReal_or_isComplex with hw | hw
    · let e := InfinitePlace.Completion.ringEquivRealOfIsReal hw
      refine ⟨e.symm t, (map_ne_zero_iff _ e.symm.injective).2 ht.ne', ?_⟩
      have hn : ‖e.symm t‖ = ‖e (e.symm t)‖ := by
        rw [InfinitePlace.Completion.ringEquivRealOfIsReal_apply]
        exact ((InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero (map_zero _) _).symm
      rw [hn, RingEquiv.apply_symm_apply, Real.norm_of_nonneg ht.le]
      simp [InfinitePlace.mult, hw]
    · let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex hw
      refine ⟨e.symm (Real.sqrt t : ℂ), (map_ne_zero_iff _ e.symm.injective).2 (Complex.ofReal_ne_zero.2 (Real.sqrt_ne_zero'.2 ht)), ?_⟩
      have hn : ‖e.symm (Real.sqrt t : ℂ)‖ = ‖e (e.symm (Real.sqrt t : ℂ))‖ := by
        rw [InfinitePlace.Completion.ringEquivComplexOfIsComplex_apply]
        exact ((InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) _).symm
      have hw' : ¬ w.IsReal := InfinitePlace.not_isReal_iff_isComplex.2 hw; rw [hn, RingEquiv.apply_symm_apply, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg t)]
      simp [InfinitePlace.mult, hw', Real.sq_sqrt ht.le]
  refine ⟨infiniteEmbedding w (Units.mk0 z hz0), Subtype.ext ?_⟩
  rw [ideleModule_infiniteEmbedding, Units.val_mk0, hz]
theorem infiniteModule_diagonal (k : Kˣ) : infiniteModule (diagonal K k) = ∏ w : InfinitePlace K, w (k : K) ^ w.mult := by
  refine Finset.prod_congr rfl fun w _ ↦ ?_
  congr 1
  exact InfinitePlace.Completion.norm_coe (K := K) (v := w) _
theorem finiteModule_diagonal (k : Kˣ) : finiteModule (diagonal K k) = ∏ᶠ w : FinitePlace K, w (k : K) := by
  rw [← finprod_comp_equiv FinitePlace.equivHeightOneSpectrum.symm]
  simp only [FinitePlace.equivHeightOneSpectrum_symm_apply]
  rfl
theorem ideleModule_diagonal (k : Kˣ) : ideleModule K (diagonal K k) = 1 := by
  refine Subtype.ext ?_
  rw [ideleModule_apply, infiniteModule_diagonal, finiteModule_diagonal, Positive.val_one]
  exact prod_abs_eq_one k.ne_zero
variable (K) in
def normOneSubgroup : Subgroup (IdeleGroup K) := (ideleModule K).ker
theorem mem_normOneSubgroup {x : IdeleGroup K} :
    x ∈ normOneSubgroup K ↔ (ideleModule K x : ℝ) = 1 := by
  rw [normOneSubgroup, MonoidHom.mem_ker]
  exact ⟨fun h ↦ by rw [h, Positive.val_one], fun h ↦ Subtype.ext (h.trans Positive.val_one.symm)⟩
variable (K) in
theorem isClosed_normOneSubgroup : IsClosed (normOneSubgroup K : Set (IdeleGroup K)) := by
  have h : (normOneSubgroup K : Set (IdeleGroup K)) =
      (fun x ↦ (ideleModule K x : ℝ)) ⁻¹' {1} := by
    ext x
    exact mem_normOneSubgroup
  rw [h]
  exact isClosed_singleton.preimage (continuous_subtype_val.comp continuous_ideleModule)
variable (K) in
theorem range_diagonal_le_normOneSubgroup : (diagonal K).range ≤ normOneSubgroup K := by rintro _ ⟨k, rfl⟩; exact ideleModule_diagonal k
end IdeleGroup
namespace IdeleClassGroup
def ideleModule : IdeleClassGroup K →* {r : ℝ // 0 < r} :=
  QuotientGroup.lift _ (IdeleGroup.ideleModule K) (IdeleGroup.range_diagonal_le_normOneSubgroup K)
@[simp]
theorem ideleModule_mk (x : IdeleGroup K) : ideleModule K (mk K x) = IdeleGroup.ideleModule K x :=
  rfl
theorem continuous_ideleModule : Continuous (ideleModule K) :=
  (QuotientGroup.isQuotientMap_mk _).continuous_iff.2 (IdeleGroup.continuous_ideleModule (K := K))
theorem ideleModule_surjective : Function.Surjective (ideleModule K) := fun t ↦
  let ⟨x, hx⟩ := IdeleGroup.ideleModule_surjective (K := K) t; ⟨mk K x, hx⟩
def normOneSubgroup : Subgroup (IdeleClassGroup K) := (ideleModule K).ker
theorem normOneSubgroup_eq_map : normOneSubgroup K = (IdeleGroup.normOneSubgroup K).map (mk K) := by
  ext c
  obtain ⟨x, rfl⟩ := mk_surjective K c; constructor
  · intro hx
    exact ⟨x, hx, rfl⟩
  · rintro ⟨y, hy, hyx⟩
    change ideleModule K (mk K x) = 1; rw [← hyx]; exact hy
end IdeleClassGroup
end Sec2_IdeleNorms

section CompactBridge
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Topology
open scoped NumberField.AdeleRing _root_.RestrictedProduct
def integralFiniteAdeles (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K] : Subring (FiniteAdeleRing R K) where
  carrier := {a | ∀ v : HeightOneSpectrum R, a v ∈ v.adicCompletionIntegers K}
  mul_mem' ha hb v := Subring.mul_mem _ (ha v) (hb v)
  one_mem' _ := Subring.one_mem _
  add_mem' ha hb v := Subring.add_mem _ (ha v) (hb v)
  zero_mem' _ := Subring.zero_mem _
  neg_mem' ha v := Subring.neg_mem _ (ha v)
theorem mem_integralFiniteAdeles {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K] {a : FiniteAdeleRing R K} :
    a ∈ integralFiniteAdeles R K ↔ ∀ v : HeightOneSpectrum R, a v ∈ v.adicCompletionIntegers K := Iff.rfl
theorem coe_mem_adicCompletionIntegers_iff {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K] (v : HeightOneSpectrum R) (k : K) :
    (k : v.adicCompletion K) ∈ v.adicCompletionIntegers K ↔ v.valuation K k ≤ 1 := by
  rw [mem_adicCompletionIntegers, valuedAdicCompletion_eq_valuation']
theorem isCompact_integralFiniteAdeles (K : Type*) [Field K] [NumberField K] : IsCompact (integralFiniteAdeles (𝓞 K) K : Set (FiniteAdeleRing (𝓞 K) K)) := by
  have : ∀ v : HeightOneSpectrum (𝓞 K), CompactSpace ((v.adicCompletionIntegers K : Set (v.adicCompletion K))) := fun v =>
    isCompact_iff_compactSpace.1 (isCompact_adicCompletionIntegers v)
  have hcont := (_root_.RestrictedProduct.isEmbedding_structureMap
    (R := fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K)
    (A := fun v => (v.adicCompletionIntegers K : Set (v.adicCompletion K))) (𝓕 := Filter.cofinite)).continuous
  have h := isCompact_range hcont; rw [_root_.RestrictedProduct.range_structureMap] at h; exact h
theorem isOpen_units_adicCompletionIntegers (K : Type*) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) : IsOpen ((Submonoid.ofClass (v.adicCompletionIntegers K)).units : Set (v.adicCompletion K)ˣ) := by
  have h1 : IsOpen {x : (v.adicCompletion K)ˣ | (x : v.adicCompletion K) ∈ v.adicCompletionIntegers K} :=
    (isOpen_adicCompletionIntegers v).preimage Units.continuous_val
  have h2 : IsOpen {x : (v.adicCompletion K)ˣ | ((x⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) ∈ v.adicCompletionIntegers K} :=
    (isOpen_adicCompletionIntegers v).preimage Units.continuous_coe_inv
  convert h1.inter h2 using 1
  ext x; exact Submonoid.mem_units_iff _ _
instance fact_isOpen_adicCompletionIntegers (K : Type*) [Field K] [NumberField K] : Fact (∀ v : HeightOneSpectrum (𝓞 K), IsOpen (v.adicCompletionIntegers K : Set (v.adicCompletion K))) :=
  ⟨fun v => isOpen_adicCompletionIntegers v⟩
instance t2Space_finiteAdeleRing (K : Type*) [Field K] [NumberField K] : T2Space (FiniteAdeleRing (𝓞 K) K) :=
  .of_injective_continuous DFunLike.coe_injective (continuous_pi fun v => _root_.RestrictedProduct.continuous_eval v)
instance locallyCompactSpace_finiteAdeleRing (K : Type*) [Field K] [NumberField K] : LocallyCompactSpace (FiniteAdeleRing (𝓞 K) K) :=
  _root_.RestrictedProduct.locallyCompactSpace_of_addGroup
    (R := fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K)
    (B := fun v => v.adicCompletionIntegers K)
    (.of_forall fun v => isCompact_adicCompletionIntegers v)
end CompactBridge

/-! ### UnitBound -/
section Sec2_UnitBound
open NumberField IsDedekindDomain Topology Filter NumberField.Units
  NumberField.Units.dirichletUnitTheorem
open scoped NumberField.AdeleRing RestrictedProduct
variable (K : Type*) [Field K] [NumberField K]
instance InfinitePlace.Completion.properSpace (w : InfinitePlace K) : ProperSpace w.Completion := by
  let _ : NontriviallyNormedField w.Completion :=
    { (inferInstance : NormedField w.Completion) with
      non_trivial := ⟨2, by
        have h := (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) 2; rw [map_ofNat] at h; rw [← h]; norm_num⟩ }
  exact ProperSpace.of_locallyCompactSpace w.Completion
namespace IdeleGroup
theorem abs_log_le_iff {r M : ℝ} (hr : 0 < r) :
    |Real.log r| ≤ M ↔ Real.exp (-M) ≤ r ∧ r ≤ Real.exp M := by
  rw [abs_le, neg_le, ← Real.log_inv, Real.log_le_iff_le_exp (inv_pos.2 hr), Real.log_le_iff_le_exp hr, inv_le_comm₀ hr (Real.exp_pos _), Real.exp_neg]
omit [NumberField K] in
theorem isCompact_units_abs_log_le (w : InfinitePlace K) (M : ℝ) : IsCompact {z : (w.Completion)ˣ | |Real.log ‖(z : w.Completion)‖| ≤ M} := by
  rw [Units.isEmbedding_val₀.isCompact_iff]
  have h : ((↑) : (w.Completion)ˣ → w.Completion) '' {z : (w.Completion)ˣ | |Real.log ‖(z : w.Completion)‖| ≤ M} =
      {c : w.Completion | Real.exp (-M) ≤ ‖c‖ ∧ ‖c‖ ≤ Real.exp M} := by
    ext c
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact (abs_log_le_iff (norm_pos_iff.2 z.ne_zero)).1 hz
    · rintro ⟨h1, h2⟩
      have hc : c ≠ 0 := norm_pos_iff.1 ((Real.exp_pos _).trans_le h1); exact ⟨Units.mk0 c hc, (abs_log_le_iff (norm_pos_iff.2 hc)).2 ⟨h1, h2⟩, rfl⟩
  rw [h]
  refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
  · exact (isClosed_le continuous_const continuous_norm).inter (isClosed_le continuous_norm continuous_const)
  · exact (Metric.isBounded_closedBall (x := (0 : w.Completion)) (r := Real.exp M)).subset fun c hc ↦ by simpa using hc.2
omit [NumberField K] in
theorem isCompact_infinite_abs_log_le (M : ℝ) : IsCompact {y : (InfiniteAdeleRing K)ˣ |
      ∀ w : InfinitePlace K, |Real.log ‖(y : InfiniteAdeleRing K) w‖| ≤ M} := by
  let p := (ContinuousMulEquiv.piUnits : (InfiniteAdeleRing K)ˣ ≃ₜ* ∀ w : InfinitePlace K, (w.Completion)ˣ)
  have hc : IsCompact ((p ⁻¹' Set.univ.pi fun w ↦
      {z : (w.Completion)ˣ | |Real.log ‖(z : w.Completion)‖| ≤ M}) : Set (InfiniteAdeleRing K)ˣ) :=
    p.toHomeomorph.isCompact_preimage.2 (isCompact_univ_pi fun w ↦ isCompact_units_abs_log_le K w M)
  convert hc using 1
  ext y
  exact ⟨fun hy w _ ↦ hy w, fun hy w ↦ hy w (Set.mem_univ w)⟩
theorem isCompact_finite_units_integral : IsCompact {f : (FiniteAdeleRing (𝓞 K) K)ˣ | ∀ v : HeightOneSpectrum (𝓞 K), (f : FiniteAdeleRing (𝓞 K) K) v ∈ v.adicCompletionIntegers K ∧
        ((f⁻¹ : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) v ∈
          v.adicCompletionIntegers K} := by
  have hI := isCompact_integralFiniteAdeles K
  have h : IsCompact ((integralFiniteAdeles (𝓞 K) K : Set (FiniteAdeleRing (𝓞 K) K)) ×ˢ
      (MulOpposite.unop ⁻¹' (integralFiniteAdeles (𝓞 K) K : Set (FiniteAdeleRing (𝓞 K) K)))) :=
    hI.prod (MulOpposite.opHomeomorph.symm.isCompact_preimage.2 hI)
  convert Units.isClosedEmbedding_embedProduct.isCompact_preimage h using 1
  ext f
  simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_prod, Units.embedProduct_apply, MulOpposite.unop_op, SetLike.mem_coe, mem_integralFiniteAdeles, ← forall_and]
theorem isCompact_abs_log_le_inter_standardOpenSubgroup (M : ℝ) : IsCompact {x : IdeleGroup K | (∀ w : InfinitePlace K, |Real.log ‖(x : 𝔸[K]).1 w‖| ≤ M) ∧
      x ∈ standardOpenSubgroup K} := by
  let e := prodEquiv K
  have hc : IsCompact (e ⁻¹' ({y : (InfiniteAdeleRing K)ˣ |
        ∀ w : InfinitePlace K, |Real.log ‖(y : InfiniteAdeleRing K) w‖| ≤ M} ×ˢ
      {f : (FiniteAdeleRing (𝓞 K) K)ˣ | ∀ v : HeightOneSpectrum (𝓞 K),
        (f : FiniteAdeleRing (𝓞 K) K) v ∈ v.adicCompletionIntegers K ∧ ((f⁻¹ : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) v ∈
            v.adicCompletionIntegers K})) :=
    e.toHomeomorph.isCompact_preimage.2 ((isCompact_infinite_abs_log_le K M).prod (isCompact_finite_units_integral K))
  convert hc using 1
  ext x
  exact ⟨fun ⟨h1, h2⟩ ↦ ⟨h1, (mem_standardOpenSubgroup K).1 h2⟩, fun ⟨h1, h2⟩ ↦ ⟨h1, (mem_standardOpenSubgroup K).2 h2⟩⟩
def unitsToUnits : (𝓞 K)ˣ →* Kˣ := Units.map (algebraMap (𝓞 K) K).toMonoidHom
omit [NumberField K] in
@[simp]
theorem coe_unitsToUnits (u : (𝓞 K)ˣ) : ((unitsToUnits K u : Kˣ) : K) = ((u : 𝓞 K) : K) :=
  rfl
theorem diagonal_unitsToUnits_mem (u : (𝓞 K)ˣ) : diagonal K (unitsToUnits K u) ∈ standardOpenSubgroup K := by
  rw [mem_standardOpenSubgroup K]
  intro v; refine ⟨(coe_mem_adicCompletionIntegers_iff v _).2 (HeightOneSpectrum.valuation_le_one v _), ?_⟩; rw [← map_inv]
  exact (coe_mem_adicCompletionIntegers_iff v _).2 (HeightOneSpectrum.valuation_le_one v ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K))
theorem infiniteModule_diagonal_unitsToUnits (u : (𝓞 K)ˣ) : infiniteModule (diagonal K (unitsToUnits K u)) = 1 := by
  have h := congrArg Subtype.val (ideleModule_diagonal (unitsToUnits K u)); rwa [ideleModule_apply, finiteModule_eq_one_of_mem (diagonal_unitsToUnits_mem K u), mul_one, Positive.val_one] at h
variable {K}
theorem norm_diagonal_mul (k : Kˣ) (y : IdeleGroup K) (w : InfinitePlace K) : ‖((diagonal K k * y : IdeleGroup K) : 𝔸[K]).1 w‖ = w (k : K) * ‖(y : 𝔸[K]).1 w‖ := by
  rw [Units.val_mul, adele_fst_mul_apply, norm_mul]
  congr 1
  exact InfinitePlace.Completion.norm_coe (K := K) (v := w) _
theorem log_infiniteModule (x : IdeleGroup K) : Real.log (infiniteModule x) = ∑ w : InfinitePlace K, (w.mult : ℝ) * Real.log ‖(x : 𝔸[K]).1 w‖ := by
  rw [infiniteModule, Real.log_prod fun w _ ↦ pow_ne_zero _ (norm_ne_zero_iff.2 (infinite_ne_zero x w))]
  simp only [Real.log_pow]
def logVector (x : IdeleGroup K) : logSpace K :=
  fun w ↦ (w.1.mult : ℝ) * Real.log ‖(x : 𝔸[K]).1 w.1‖
theorem logVector_diagonal_mul (u : (𝓞 K)ˣ) (y : IdeleGroup K) : logVector (diagonal K (unitsToUnits K u) * y) = logEmbedding K (Additive.ofMul u) + logVector y := by
  ext w
  have hu : w.1 (((u : 𝓞 K) : K)) ≠ 0 := by
    rw [Ne, map_eq_zero]
    exact (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 K) K)).2 u.ne_zero
  rw [logVector, norm_diagonal_mul, coe_unitsToUnits, Real.log_mul hu (norm_ne_zero_iff.2 (infinite_ne_zero y w.1)), Pi.add_apply, logEmbedding_component, logVector, mul_add]
theorem exists_unit_forall_abs_log_le (M₀ : ℝ) : ∃ M : ℝ, ∀ y : IdeleGroup K,
    |Real.log (infiniteModule y)| ≤ M₀ → ∃ u : (𝓞 K)ˣ, ∀ w : InfinitePlace K,
      |Real.log ‖((diagonal K (unitsToUnits K u) * y : IdeleGroup K) : 𝔸[K]).1 w‖| ≤ M := by
  classical
  let B := (basisUnitLattice K).ofZLatticeBasis ℝ (unitLattice K)
  obtain ⟨C, hC⟩ := (ZSpan.fundamentalDomain_isBounded B).exists_norm_le
  set C' := max C 0 with hC'; refine ⟨M₀ + Fintype.card {w : InfinitePlace K // w ≠ w₀} * C' + C', fun y hy ↦ ?_⟩
  have hM₀ : 0 ≤ M₀ := (abs_nonneg _).trans hy
  have hC'0 : 0 ≤ C' := le_max_right _ _
  obtain ⟨⟨e, he⟩, hmem, -⟩ := ZSpan.exist_unique_vadd_mem_fundamentalDomain B (logVector y); rw [Module.Basis.ofZLatticeBasis_span ℝ (unitLattice K)] at he
  obtain ⟨u, -, rfl⟩ := he; refine ⟨Additive.toMul u, ?_⟩
  set z := diagonal K (unitsToUnits K (Additive.toMul u)) * y with hz
  have hF : logVector z ∈ ZSpan.fundamentalDomain B := by
    rw [hz, logVector_diagonal_mul]
    exact hmem
  have hbound : ∀ w : {w : InfinitePlace K // w ≠ w₀},
      |(w.1.mult : ℝ) * Real.log ‖(z : 𝔸[K]).1 w.1‖| ≤ C' := fun w ↦ by
    have := (norm_le_pi_norm (logVector z) w).trans (hC _ hF); rw [Real.norm_eq_abs] at this; exact this.trans (le_max_left _ _)
  have hmult : ∀ (w : InfinitePlace K) (t : ℝ), |t| ≤ |(w.mult : ℝ) * t| := fun w t ↦ by
    rw [abs_mul]
    exact le_mul_of_one_le_left (abs_nonneg t) (by
      rw [abs_of_nonneg (Nat.cast_nonneg _)]
      exact_mod_cast w.mult_pos)
  have hmod : infiniteModule z = infiniteModule y := by rw [hz, infiniteModule_mul, infiniteModule_diagonal_unitsToUnits, one_mul]
  intro w; by_cases hw : w = w₀
  · subst hw
    have hsum := log_infiniteModule z; rw [Fintype.sum_eq_add_sum_subtype_ne _ (w₀ : InfinitePlace K), hmod] at hsum
    have h1 : |∑ w : {w : InfinitePlace K // w ≠ w₀},
        (w.1.mult : ℝ) * Real.log ‖(z : 𝔸[K]).1 w.1‖| ≤
        Fintype.card {w : InfinitePlace K // w ≠ w₀} * C' := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      refine (Finset.sum_le_sum fun w _ ↦ hbound w).trans ?_
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have h2 : ((w₀ : InfinitePlace K).mult : ℝ) * Real.log ‖(z : 𝔸[K]).1 w₀‖ = Real.log (infiniteModule y) - ∑ w : {w : InfinitePlace K // w ≠ w₀},
          (w.1.mult : ℝ) * Real.log ‖(z : 𝔸[K]).1 w.1‖ := by
      linarith
    refine (hmult (w₀ : InfinitePlace K) _).trans ?_
    rw [h2]
    refine (abs_sub _ _).trans ?_
    linarith
  · refine (hmult w _).trans ((hbound ⟨w, hw⟩).trans ?_)
    have : 0 ≤ (Fintype.card {w : InfinitePlace K // w ≠ w₀} : ℝ) * C' :=
      mul_nonneg (Nat.cast_nonneg _) hC'0
    linarith
end IdeleGroup
end Sec2_UnitBound


/-! ### NormOneCompact -/
section Sec2_NormOneCompact
open NumberField IsDedekindDomain Topology
open scoped NumberField.AdeleRing
variable (K : Type*) [Field K] [NumberField K]
namespace IdeleGroup
theorem exists_finset_mul_mem_standardOpenSubgroup : ∃ R : Finset (IdeleGroup K), ∀ x : IdeleGroup K, ∃ k : Kˣ, ∃ r ∈ R,
      diagonal K k * x * r⁻¹ ∈ standardOpenSubgroup K := by
  classical
  let s : ClassGroup (𝓞 K) → IdeleGroup K := Function.invFun toClassGroup; refine ⟨Finset.univ.image s, fun x ↦ ?_⟩
  have hs : toClassGroup (s (toClassGroup x)) = toClassGroup x :=
    Function.invFun_eq (toClassGroup_surjective _)
  have hmem : x * (s (toClassGroup x))⁻¹ ∈ (diagonal K).range ⊔ standardOpenSubgroup K := by rw [← ker_toClassGroup, MonoidHom.mem_ker, map_mul, map_inv, hs, mul_inv_cancel]
  obtain ⟨_, ⟨k, rfl⟩, u, hu, hku⟩ := Subgroup.mem_sup.1 hmem; refine ⟨k⁻¹, s (toClassGroup x), Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩; rw [map_inv, mul_assoc, ← hku, inv_mul_cancel_left]; exact hu
theorem exists_isCompact_of_finset (R : Finset (IdeleGroup K)) (hR : ∀ x : IdeleGroup K, ∃ k : Kˣ, ∃ r ∈ R, diagonal K k * x * r⁻¹ ∈ standardOpenSubgroup K) : ∃ D : Set (IdeleGroup K), IsCompact D ∧
      ∀ x ∈ normOneSubgroup K, ∃ k : Kˣ, diagonal K k * x ∈ D := by
  obtain ⟨M, hM⟩ := exists_unit_forall_abs_log_le (K := K) (∑ r ∈ R, |Real.log (ideleModule K r : ℝ)|)
  let S := {x : IdeleGroup K | (∀ w : InfinitePlace K, |Real.log ‖(x : 𝔸[K]).1 w‖| ≤ M) ∧
    x ∈ standardOpenSubgroup K}
  refine ⟨⋃ r ∈ R, (fun s ↦ s * r) '' S, R.isCompact_biUnion fun r _ ↦
    (isCompact_abs_log_le_inter_standardOpenSubgroup K M).image (continuous_id.mul continuous_const), fun x hx ↦ ?_⟩
  obtain ⟨k, r, hr, hy⟩ := hR x
  set y := diagonal K k * x * r⁻¹ with hydef
  have hmod : ideleModule K y = (ideleModule K r)⁻¹ := by rw [hydef, map_mul, map_mul, map_inv, ideleModule_diagonal, MonoidHom.mem_ker.1 hx, one_mul, one_mul]
  have hinf : |Real.log (infiniteModule y)| ≤ ∑ r ∈ R, |Real.log (ideleModule K r : ℝ)| := by
    have h1 : infiniteModule y = ((ideleModule K r : ℝ))⁻¹ := by have := congrArg Subtype.val hmod; rw [ideleModule_apply, finiteModule_eq_one_of_mem hy, mul_one] at this; exact this
    rw [h1, Real.log_inv, abs_neg]
    exact Finset.single_le_sum (f := fun r ↦ |Real.log (ideleModule K r : ℝ)|) (fun r _ ↦ abs_nonneg _) hr
  obtain ⟨u, hu⟩ := hM y hinf; refine ⟨unitsToUnits K u * k, Set.mem_biUnion hr ⟨diagonal K (unitsToUnits K u) * y, ⟨hu, mul_mem (diagonal_unitsToUnits_mem K u) hy⟩, ?_⟩⟩
  simp only [hydef, map_mul, mul_assoc, inv_mul_cancel, mul_one]
theorem exists_isCompact_normOneSubgroup : ∃ D : Set (IdeleGroup K), IsCompact D ∧ D ⊆ normOneSubgroup K ∧ ∀ x ∈ normOneSubgroup K, ∃ k : Kˣ, diagonal K k * x ∈ D := by
  obtain ⟨R, hR⟩ := exists_finset_mul_mem_standardOpenSubgroup K
  obtain ⟨D, hD, hxD⟩ := exists_isCompact_of_finset K R hR; refine ⟨D ∩ normOneSubgroup K, hD.inter_right (isClosed_normOneSubgroup K), Set.inter_subset_right, fun x hx ↦ ?_⟩
  obtain ⟨k, hk⟩ := hxD x hx; exact ⟨k, hk, mul_mem (range_diagonal_le_normOneSubgroup K ⟨k, rfl⟩) hx⟩
instance compactSpace_normOneSubgroup_quotient : CompactSpace (normOneSubgroup K ⧸ (diagonal K).range.subgroupOf (normOneSubgroup K)) := by
  obtain ⟨D, hD, -, hxD⟩ := exists_isCompact_normOneSubgroup K
  have hD' : IsCompact ((Subtype.val : normOneSubgroup K → IdeleGroup K) ⁻¹' D) :=
    (isClosed_normOneSubgroup K).isClosedEmbedding_subtypeVal.isCompact_preimage hD
  have h : (QuotientGroup.mk : normOneSubgroup K → normOneSubgroup K ⧸ (diagonal K).range.subgroupOf (normOneSubgroup K)) ''
      ((Subtype.val : normOneSubgroup K → IdeleGroup K) ⁻¹' D) = Set.univ := by
    refine Set.eq_univ_of_forall fun q ↦ ?_
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨k, hk⟩ := hxD x x.2; refine ⟨⟨diagonal K k * x, mul_mem (range_diagonal_le_normOneSubgroup K ⟨k, rfl⟩) x.2⟩, hk, (QuotientGroup.eq.2 ?_).symm⟩; rw [Subgroup.mem_subgroupOf]; refine ⟨k, ?_⟩
    change diagonal K k = ((x : IdeleGroup K))⁻¹ * (diagonal K k * x); rw [mul_comm (diagonal K k) x, inv_mul_cancel_left]
  exact isCompact_univ_iff.1 (h ▸ hD'.image QuotientGroup.continuous_mk)
end IdeleGroup
namespace IdeleClassGroup
theorem isCompact_normOneSubgroup : IsCompact (normOneSubgroup K : Set (IdeleClassGroup K)) := by
  obtain ⟨D, hD, hDJ, hxD⟩ := IdeleGroup.exists_isCompact_normOneSubgroup K
  have h : (normOneSubgroup K : Set (IdeleClassGroup K)) = mk K '' D := by
    rw [normOneSubgroup_eq_map, Subgroup.coe_map]
    ext c
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨k, hk⟩ := hxD x hx; refine ⟨IdeleGroup.diagonal K k * x, hk, ?_⟩; rw [map_mul, mk_diagonal]; exact one_mul (mk K x)
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hDJ hx, rfl⟩
  rw [h]
  exact hD.image (continuous_mk K)
instance compactSpace_normOneSubgroup : CompactSpace (normOneSubgroup K) :=
  isCompact_iff_compactSpace.1 (isCompact_normOneSubgroup K)
end IdeleClassGroup
end Sec2_NormOneCompact


/-! ### Rational -/
section Sec2_Rational
open NumberField IsDedekindDomain Topology
open scoped NumberField.AdeleRing
local instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩
namespace RationalIdeles
open IdeleGroup
theorem isReal_infinitePlace (w : InfinitePlace ℚ) : w.IsReal := by
  rw [Subsingleton.elim w Rat.infinitePlace]
  exact Rat.isReal_infinitePlace
def realEquiv : InfiniteAdeleRing ℚ ≃+* ℝ :=
  (RingEquiv.piUnique fun w : InfinitePlace ℚ ↦ w.Completion).trans (InfinitePlace.Completion.ringEquivRealOfIsReal (isReal_infinitePlace default))
theorem realEquiv_apply (x : InfiniteAdeleRing ℚ) : realEquiv x = InfinitePlace.Completion.extensionEmbeddingOfIsReal (isReal_infinitePlace default) (x default) :=
  rfl
theorem continuous_realEquiv : Continuous realEquiv :=
  (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal _).continuous.comp (continuous_apply _)
theorem continuous_realEquiv_symm : Continuous realEquiv.symm := by
  exact continuous_equiv_symm_of_eq realEquiv.toEquiv ((Homeomorph.piUnique fun w : InfinitePlace ℚ ↦ w.Completion).trans (InfinitePlace.Completion.isometryEquivRealOfIsReal (isReal_infinitePlace default)).toHomeomorph) fun _ ↦ rfl
def realUnitsEquiv : (InfiniteAdeleRing ℚ)ˣ ≃ₜ* ℝˣ :=
  unitsContinuousMulEquiv realEquiv.toMulEquiv continuous_realEquiv continuous_realEquiv_symm
def realPart : IdeleGroup ℚ →* ℝˣ :=
  realUnitsEquiv.toMulEquiv.toMonoidHom.comp (toInfinite ℚ)
theorem coe_realPart (x : IdeleGroup ℚ) : (realPart x : ℝ) = realEquiv (x : 𝔸[ℚ]).1 :=
  rfl
theorem continuous_realPart : Continuous realPart :=
  realUnitsEquiv.continuous.comp (continuous_toInfinite ℚ)
@[simp]
theorem realPart_diagonal (a : ℚˣ) : (realPart (diagonal ℚ a) : ℝ) = a := by
  rw [coe_realPart, coe_diagonal]
  exact eq_ratCast (realEquiv.toRingHom.comp (algebraMap ℚ (InfiniteAdeleRing ℚ))) a
theorem realPart_ofIntegerUnits (a : (InfiniteAdeleRing ℚ)ˣ) (u : Π v : HeightOneSpectrum (𝓞 ℚ), (v.adicCompletionIntegers ℚ)ˣ) : realPart (ofIntegerUnits a u) = realUnitsEquiv a :=
  rfl
def positiveSubgroup : Subgroup (IdeleGroup ℚ) :=
  standardOpenSubgroup ℚ ⊓ (Units.posSubgroup ℝ).comap realPart
theorem mem_positiveSubgroup {x : IdeleGroup ℚ} :
    x ∈ positiveSubgroup ↔ x ∈ standardOpenSubgroup ℚ ∧ 0 < (realPart x : ℝ) := by
  rw [positiveSubgroup, Subgroup.mem_inf, Subgroup.mem_comap, Units.mem_posSubgroup]
theorem isOpen_positiveSubgroup : IsOpen (positiveSubgroup : Set (IdeleGroup ℚ)) := by
  have h : (positiveSubgroup : Set (IdeleGroup ℚ)) =
      (standardOpenSubgroup ℚ : Set (IdeleGroup ℚ)) ∩ {x | 0 < (realPart x : ℝ)} := by
    ext x
    exact mem_positiveSubgroup
  rw [h]
  exact (isOpen_standardOpenSubgroup ℚ).inter (isOpen_lt continuous_const (Units.continuous_val.comp continuous_realPart))
theorem diagonal_mem_standardOpenSubgroup_iff (a : ℚˣ) : diagonal ℚ a ∈ standardOpenSubgroup ℚ ↔ (a : ℚ) = 1 ∨ (a : ℚ) = -1 := by
  rw [← ker_toFractionalIdeal, MonoidHom.mem_ker, toFractionalIdeal_diagonal, toPrincipalIdeal_eq_iff, Units.val_one, ← FractionalIdeal.spanSingleton_one, FractionalIdeal.spanSingleton_eq_spanSingleton]
  constructor
  · rintro ⟨z, hz⟩
    have hz' : ((z : 𝓞 ℚ) : ℚ) * a = 1 := by
      rw [Units.smul_def, Algebra.smul_def] at hz
      exact hz
    rcases Rat.RingOfIntegers.isUnit_iff.1 z.isUnit with h | h
    · left
      rwa [h, one_mul] at hz'
    · right
      rwa [h, neg_one_mul, neg_eq_iff_eq_neg] at hz'
  · rintro (h | h)
    · exact ⟨1, by rw [one_smul, h]⟩
    · exact ⟨-1, by rw [Units.neg_smul, one_smul, h, neg_neg]⟩
theorem positiveSubgroup_inf_diagonal_range : positiveSubgroup ⊓ (diagonal ℚ).range = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hx, a, rfl⟩
  obtain ⟨h1, h2⟩ := mem_positiveSubgroup.1 hx; rw [realPart_diagonal] at h2; rw [Subgroup.mem_bot]
  rcases (diagonal_mem_standardOpenSubgroup_iff a).1 h1 with h | h
  · rw [show a = 1 from Units.ext h, map_one]
  · rw [h] at h2
    norm_num at h2
theorem subsingleton_classGroup : Subsingleton (ClassGroup (𝓞 ℚ)) := by have h := Rat.classNumber_eq; rw [NumberField.classNumber] at h; exact Fintype.card_le_one_iff_subsingleton.1 h.le
theorem positiveSubgroup_sup_diagonal_range : positiveSubgroup ⊔ (diagonal ℚ).range = ⊤ := by
  have htop : (diagonal ℚ).range ⊔ standardOpenSubgroup ℚ = ⊤ := by
    rw [← IdeleGroup.ker_toClassGroup, eq_top_iff]
    intro x _
    have := subsingleton_classGroup; exact Subsingleton.elim _ _
  rw [eq_top_iff]
  intro x _
  have hx : x ∈ (diagonal ℚ).range ⊔ standardOpenSubgroup ℚ := htop ▸ Subgroup.mem_top x
  obtain ⟨_, ⟨a, rfl⟩, u, hu, rfl⟩ := Subgroup.mem_sup.1 hx
  rcases lt_or_gt_of_ne (realPart u).ne_zero with hneg | hpos
  · have hm : diagonal ℚ (-1) ∈ standardOpenSubgroup ℚ :=
      (diagonal_mem_standardOpenSubgroup_iff (-1)).2 (Or.inr (by simp))
    have hp : diagonal ℚ (-1) * u ∈ positiveSubgroup := by
      refine mem_positiveSubgroup.2 ⟨mul_mem hm hu, ?_⟩
      rw [map_mul, Units.val_mul, realPart_diagonal]
      push_cast; linarith
    refine Subgroup.mem_sup.2 ⟨_, hp, diagonal ℚ (-a), ⟨-a, rfl⟩, ?_⟩
    rw [mul_right_comm, ← map_mul, neg_one_mul, neg_neg]
  · exact Subgroup.mem_sup.2 ⟨u, mem_positiveSubgroup.2 ⟨hu, hpos⟩, diagonal ℚ a, ⟨a, rfl⟩, mul_comm _ _⟩
def positiveSubgroupEquivIdeleClassGroup : positiveSubgroup ≃ₜ* IdeleClassGroup ℚ :=
  openSubgroupEquivQuotient _ _ isOpen_positiveSubgroup positiveSubgroup_inf_diagonal_range positiveSubgroup_sup_diagonal_range
@[simp]
theorem positiveSubgroupEquivIdeleClassGroup_apply (x : positiveSubgroup) : positiveSubgroupEquivIdeleClassGroup x = IdeleClassGroup.mk ℚ x :=
  rfl
def positiveSubgroupEquiv : positiveSubgroup ≃ₜ* Units.posSubgroup ℝ × Π v : HeightOneSpectrum (𝓞 ℚ), (v.adicCompletionIntegers ℚ)ˣ where
  toFun x := (⟨realPart x, (Units.mem_posSubgroup _).2 (mem_positiveSubgroup.1 x.2).2⟩, (standardOpenSubgroupEquiv ℚ ⟨x, (mem_positiveSubgroup.1 x.2).1⟩).2)
  invFun p := ⟨ofIntegerUnits (realUnitsEquiv.symm p.1) p.2, mem_positiveSubgroup.2 ⟨ofIntegerUnits_mem _ _, by
      rw [realPart_ofIntegerUnits, ContinuousMulEquiv.apply_symm_apply]
      exact (Units.mem_posSubgroup _).1 p.1.2⟩⟩
  left_inv x := by
    have h : realUnitsEquiv.symm (realPart x) = toInfinite ℚ x :=
      realUnitsEquiv.symm_apply_apply _
    apply Subtype.ext
    change ofIntegerUnits (realUnitsEquiv.symm (realPart x)) _ = (x : IdeleGroup ℚ); rw [h]; exact Units.ext (Prod.ext rfl (Subtype.ext (funext fun _ ↦ rfl)))
  right_inv p := Prod.ext (Subtype.ext (realUnitsEquiv.apply_symm_apply _)) (funext fun _ ↦ Units.ext (Subtype.ext rfl))
  map_mul' x y := Prod.ext (Subtype.ext (map_mul realPart (x : IdeleGroup ℚ) y)) (funext fun _ ↦ Units.ext (Subtype.ext rfl))
  continuous_toFun := by exact ((continuous_realPart.comp continuous_subtype_val).subtype_mk _).prodMk (continuous_snd.comp ((standardOpenSubgroupEquiv ℚ).continuous.comp (continuous_subtype_val.subtype_mk _)))
  continuous_invFun := by
    exact (continuous_subtype_val.comp ((standardOpenSubgroupEquiv ℚ).symm.continuous.comp ((realUnitsEquiv.symm.continuous.comp (continuous_subtype_val.comp continuous_fst)).prodMk
        continuous_snd))).subtype_mk _
@[simp]
theorem coe_positiveSubgroupEquiv_apply_fst (x : positiveSubgroup) : ((positiveSubgroupEquiv x).1 : ℝˣ) = realPart x :=
  rfl
@[simp]
theorem coe_positiveSubgroupEquiv_apply_snd (x : positiveSubgroup) (v : HeightOneSpectrum (𝓞 ℚ)) : (((positiveSubgroupEquiv x).2 v : v.adicCompletionIntegers ℚ) : v.adicCompletion ℚ) = ((x : IdeleGroup ℚ) : 𝔸[ℚ]).2 v :=
  rfl
@[simp]
theorem realPart_positiveSubgroupEquiv_symm_apply (p : Units.posSubgroup ℝ × Π v : HeightOneSpectrum (𝓞 ℚ), (v.adicCompletionIntegers ℚ)ˣ) : realPart (positiveSubgroupEquiv.symm p : IdeleGroup ℚ) = p.1 :=
  congrArg (fun q ↦ (q.1 : ℝˣ)) (positiveSubgroupEquiv.apply_symm_apply p)
@[simp]
theorem coe_positiveSubgroupEquiv_symm_apply_snd (p : Units.posSubgroup ℝ × Π v : HeightOneSpectrum (𝓞 ℚ), (v.adicCompletionIntegers ℚ)ˣ) (v : HeightOneSpectrum (𝓞 ℚ)) : ((positiveSubgroupEquiv.symm p : IdeleGroup ℚ) : 𝔸[ℚ]).2 v =
      ((p.2 v : v.adicCompletionIntegers ℚ) : v.adicCompletion ℚ) :=
  rfl
def integersRingEquiv : (Π v : HeightOneSpectrum (𝓞 ℚ), v.adicCompletionIntegers ℚ) ≃+* Π p : Nat.Primes, ℤ_[p] :=
  (RingEquiv.piCongrRight fun v ↦
      (Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v).toAlgEquiv.toRingEquiv).trans
    (RingEquiv.piCongrLeft (fun p : Nat.Primes ↦ ℤ_[p]) Rat.HeightOneSpectrum.primesEquiv)
def integersHomeomorph : (Π v : HeightOneSpectrum (𝓞 ℚ), v.adicCompletionIntegers ℚ) ≃ₜ Π p : Nat.Primes, ℤ_[p] :=
  (Homeomorph.piCongrRight fun v ↦
      (Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v).toHomeomorph).trans
    (Homeomorph.piCongrLeft (Y := fun p : Nat.Primes ↦ ℤ_[p]) Rat.HeightOneSpectrum.primesEquiv)
theorem integersRingEquiv_eq_integersHomeomorph (x : Π v : HeightOneSpectrum (𝓞 ℚ),
    v.adicCompletionIntegers ℚ) : integersRingEquiv x = integersHomeomorph x :=
  rfl
theorem continuous_integersRingEquiv : Continuous integersRingEquiv :=
  integersHomeomorph.continuous.congr fun x ↦ (integersRingEquiv_eq_integersHomeomorph x).symm
theorem continuous_integersRingEquiv_symm : Continuous integersRingEquiv.symm := by exact continuous_equiv_symm_of_eq integersRingEquiv.toEquiv integersHomeomorph integersRingEquiv_eq_integersHomeomorph
def integerUnitsEquiv : (Π v : HeightOneSpectrum (𝓞 ℚ), (v.adicCompletionIntegers ℚ)ˣ) ≃ₜ* (Π p : Nat.Primes, ℤ_[p])ˣ :=
  ContinuousMulEquiv.piUnits.symm.trans (unitsContinuousMulEquiv integersRingEquiv.toMulEquiv continuous_integersRingEquiv
      continuous_integersRingEquiv_symm)
def integerUnitsEquivPi : (Π v : HeightOneSpectrum (𝓞 ℚ), (v.adicCompletionIntegers ℚ)ˣ) ≃ₜ* Π p : Nat.Primes, ℤ_[p]ˣ :=
  integerUnitsEquiv.trans ContinuousMulEquiv.piUnits
def mulMap : ℚˣ × positiveSubgroup →* IdeleGroup ℚ :=
  (diagonal ℚ).coprod positiveSubgroup.subtype
theorem mulMap_apply (p : ℚˣ × positiveSubgroup) : mulMap p = diagonal ℚ p.1 * (p.2 : IdeleGroup ℚ) :=
  rfl
theorem mulMap_bijective : Function.Bijective mulMap := by
  constructor
  · rw [injective_iff_map_eq_one]
    rintro ⟨a, u⟩ h
    have h' : diagonal ℚ a * (u : IdeleGroup ℚ) = 1 := h
    have hu : (u : IdeleGroup ℚ)⁻¹ ∈ positiveSubgroup ⊓ (diagonal ℚ).range :=
      ⟨positiveSubgroup.inv_mem u.2, a, eq_inv_of_mul_eq_one_left h'⟩
    rw [positiveSubgroup_inf_diagonal_range, Subgroup.mem_bot, inv_eq_one] at hu
    have ha : diagonal ℚ a = 1 := by rwa [hu, mul_one] at h'
    exact Prod.ext (diagonal_injective ℚ (ha.trans (map_one _).symm)) (Subtype.ext hu)
  · intro x
    have hx : x ∈ positiveSubgroup ⊔ (diagonal ℚ).range :=
      positiveSubgroup_sup_diagonal_range ▸ Subgroup.mem_top x
    obtain ⟨u, hu, _, ⟨a, rfl⟩, rfl⟩ := Subgroup.mem_sup.1 hx; exact ⟨(a, ⟨u, hu⟩), mul_comm _ _⟩
def ideleEquiv : IdeleGroup ℚ ≃* ℚˣ × Units.posSubgroup ℝ × Π p : Nat.Primes, ℤ_[p]ˣ :=
  (MulEquiv.ofBijective mulMap mulMap_bijective).symm.trans (MulEquiv.prodCongr (MulEquiv.refl _) (positiveSubgroupEquiv.toMulEquiv.trans (MulEquiv.prodCongr (MulEquiv.refl _) integerUnitsEquivPi.toMulEquiv)))
def ideleClassGroupEquiv : IdeleClassGroup ℚ ≃ₜ* Units.posSubgroup ℝ × (Π p : Nat.Primes, ℤ_[p])ˣ :=
  positiveSubgroupEquivIdeleClassGroup.symm.trans (positiveSubgroupEquiv.trans (continuousMulEquivProdCongr (ContinuousMulEquiv.refl _) integerUnitsEquiv))
def ideleClassGroupEquivPi : IdeleClassGroup ℚ ≃ₜ* Units.posSubgroup ℝ × Π p : Nat.Primes, ℤ_[p]ˣ :=
  positiveSubgroupEquivIdeleClassGroup.symm.trans (positiveSubgroupEquiv.trans (continuousMulEquivProdCongr (ContinuousMulEquiv.refl _) integerUnitsEquivPi))
theorem ideleClassGroupEquiv_mk (x : positiveSubgroup) : ideleClassGroupEquiv (IdeleClassGroup.mk ℚ x) = (⟨realPart x, (Units.mem_posSubgroup _).2 (mem_positiveSubgroup.1 x.2).2⟩,
        integerUnitsEquiv (positiveSubgroupEquiv x).2) := by
  simp only [ideleClassGroupEquiv, ContinuousMulEquiv.trans_apply]
  rw [← positiveSubgroupEquivIdeleClassGroup_apply, ContinuousMulEquiv.symm_apply_apply]
  rfl
end RationalIdeles
end Sec2_Rational


/-! ### IdeleBasis -/
section Sec2_IdeleBasis
open Filter Topology TopologicalSpace NumberField IsDedekindDomain
open scoped RestrictedProduct NumberField.AdeleRing
namespace RestrictedProdAux
variable {ι : Type*} {R : ι → Type*} [∀ i, TopologicalSpace (R i)] {A : (i : ι) → Set (R i)}
theorem isOpen_setOf_forall_mem (hAopen : ∀ i, IsOpen (A i)) {V : ∀ i, Set (R i)} (hV : ∀ i, IsOpen (V i)) (hVA : ∀ᶠ i in cofinite, V i = A i) :
    IsOpen {x : Πʳ i, [R i, A i] | ∀ i, x i ∈ V i} := by
  set S : Set ι := {i | V i = A i}
  have hSf : Sᶜ.Finite := hVA
  have hEq : {x : Πʳ i, [R i, A i] | ∀ i, x i ∈ V i} =
      {x : Πʳ i, [R i, A i] | ∀ i, i ∈ S → x.1 i ∈ A i} ∩
        ⋂ i ∈ Sᶜ, (fun x : Πʳ i, [R i, A i] ↦ x i) ⁻¹' V i := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage]
    constructor
    · intro h
      exact ⟨fun i hi ↦ (show V i = A i from hi) ▸ h i, fun i _ ↦ h i⟩
    · rintro ⟨h1, h2⟩ i
      by_cases hi : i ∈ S
      · rw [show V i = A i from hi]
        exact h1 i hi
      · exact h2 i hi
  rw [hEq]
  exact (_root_.RestrictedProduct.isOpen_forall_imp_mem hAopen).inter (hSf.isOpen_biInter fun i _ ↦ (hV i).preimage (_root_.RestrictedProduct.continuous_eval i))
theorem isTopologicalBasis (hAopen : ∀ i, IsOpen (A i)) : IsTopologicalBasis {s : Set (Πʳ i, [R i, A i]) | ∃ V : ∀ i, Set (R i),
      (∀ i, IsOpen (V i)) ∧ (∀ᶠ i in cofinite, V i = A i) ∧ s = {x | ∀ i, x i ∈ V i}} := by
  classical
  refine isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
  · rintro _ ⟨V, hV, hVA, rfl⟩
    exact isOpen_setOf_forall_mem hAopen hV hVA
  · intro x u hxu hu
    set T : Set ι := {i | x i ∈ A i}
    have hT : cofinite ≤ 𝓟 T := le_principal_iff.mpr x.2
    obtain ⟨x', hxx'⟩ :=
      _root_.RestrictedProduct.exists_inclusion_eq_of_eventually R A hT (fun i hi ↦ hi)
    have hu' : IsOpen (_root_.RestrictedProduct.inclusion R A hT ⁻¹' u) :=
      hu.preimage (_root_.RestrictedProduct.continuous_inclusion hT)
    rw [_root_.RestrictedProduct.isEmbedding_coe_of_principal.isInducing.isOpen_iff] at hu'
    obtain ⟨t, ht, htu⟩ := hu'
    have hx't : (x' : ∀ i, R i) ∈ t := by
      have : x' ∈ _root_.RestrictedProduct.inclusion R A hT ⁻¹' u := by
        rw [Set.mem_preimage, hxx']
        exact hxu
      rw [← htu] at this
      exact this
    obtain ⟨I, W, hW, hIW⟩ := isOpen_pi_iff.1 ht _ hx't
    let V : ∀ i, Set (R i) := fun i ↦
      (if i ∈ I then W i else Set.univ) ∩ (if i ∈ T then A i else Set.univ)
    refine ⟨{y | ∀ i, y i ∈ V i}, ⟨V, fun i ↦ ?_, ?_, rfl⟩, ?_, ?_⟩
    · refine IsOpen.inter ?_ ?_
      · split_ifs with h
        exacts [(hW i h).1, isOpen_univ]
      · split_ifs
        exacts [hAopen i, isOpen_univ]
    · filter_upwards [x.2, I.finite_toSet.compl_mem_cofinite] with i hi hiI
      have hiI' : i ∉ I := hiI
      have hiT : i ∈ T := hi; simp only [V, if_neg hiI', if_pos hiT, Set.univ_inter]
    · intro i
      rw [← hxx']
      refine ⟨?_, ?_⟩
      · split_ifs with h
        exacts [(hW i h).2, Set.mem_univ _]
      · split_ifs with h
        exacts [eventually_principal.1 x'.2 i h, Set.mem_univ _]
    · intro y hy
      let y' : Πʳ i, [R i, A i]_[𝓟 T] := ⟨y.1, eventually_principal.2 fun i hi ↦ by
        have := (hy i).2; simp only [if_pos hi] at this; exact this⟩
      have hy' : y' ∈ _root_.RestrictedProduct.inclusion R A hT ⁻¹' u := by
        rw [← htu]
        refine hIW fun i hi ↦ ?_
        have := (hy i).1; simp only [if_pos (Finset.mem_coe.1 hi)] at this; exact this
      exact hy'
end RestrictedProdAux
namespace IdeleGroup
variable (K : Type*) [Field K] [NumberField K]
theorem finiteProj_eq (v : HeightOneSpectrum (𝓞 K)) (x : IdeleGroup K) : finiteProj v x = (prodRestrictedEquiv K x).2 v :=
  Units.ext rfl
theorem infiniteProj_eq (w : InfinitePlace K) (x : IdeleGroup K) : infiniteProj w x = ContinuousMulEquiv.piUnits (prodRestrictedEquiv K x).1 w :=
  Units.ext rfl
theorem isTopologicalBasis : IsTopologicalBasis {s : Set (IdeleGroup K) | ∃ (U : ∀ w : InfinitePlace K, Set (w.Completion)ˣ) (V : ∀ v : HeightOneSpectrum (𝓞 K), Set (v.adicCompletion K)ˣ), (∀ w, IsOpen (U w)) ∧ (∀ v, IsOpen (V v)) ∧
        (∀ᶠ v in cofinite, V v = ((Submonoid.ofClass (v.adicCompletionIntegers K)).units : Set (v.adicCompletion K)ˣ)) ∧
        s = {x | (∀ w, infiniteProj w x ∈ U w) ∧ ∀ v, finiteProj v x ∈ V v}} := by
  set e := prodRestrictedEquiv K
  set p := (ContinuousMulEquiv.piUnits : (InfiniteAdeleRing K)ˣ ≃ₜ* ∀ w : InfinitePlace K, (w.Completion)ˣ); refine isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
  · rintro _ ⟨U, V, hU, hV, hVO, rfl⟩
    have h1 : IsOpen {x : IdeleGroup K | ∀ w, infiniteProj w x ∈ U w} := by
      simp only [Set.ofPred_forall]
      exact isOpen_iInter_of_finite fun w ↦ (hU w).preimage (continuous_infiniteProj w)
    have h2 : IsOpen {x : IdeleGroup K | ∀ v, finiteProj v x ∈ V v} := by
      simp only [finiteProj_eq]
      exact (RestrictedProdAux.isOpen_setOf_forall_mem (fun v ↦ isOpen_units_adicCompletionIntegers K v) hV hVO).preimage (continuous_snd.comp e.continuous)
    exact h1.inter h2
  · intro x u hxu hu
    have hu' : IsOpen (e.symm ⁻¹' u) := hu.preimage e.symm.continuous
    have hxu' : e x ∈ e.symm ⁻¹' u := by simpa using hxu
    obtain ⟨a, b, ha, hb, hxa, hxb, hab⟩ := isOpen_prod_iff.1 hu' (e x).1 (e x).2 hxu'
    obtain ⟨_, ⟨V, hV, hVO, rfl⟩, hxV, hVb⟩ :=
      (RestrictedProdAux.isTopologicalBasis (fun v ↦ isOpen_units_adicCompletionIntegers K v)).exists_subset_of_mem_open hxb hb
    have ha' : IsOpen (p.symm ⁻¹' a) := ha.preimage p.symm.continuous
    have hxa' : p (e x).1 ∈ p.symm ⁻¹' a := by change p.symm (p (e x).1) ∈ a; exact (congrArg (fun z : (InfiniteAdeleRing K)ˣ ↦ z ∈ a) (p.symm_apply_apply (e x).1)).mpr hxa
    obtain ⟨U, hU, hUa⟩ := isOpen_pi_iff'.1 ha' _ hxa'; refine ⟨{y | (∀ w, infiniteProj w y ∈ U w) ∧ ∀ v, finiteProj v y ∈ V v},
      ⟨U, V, fun w ↦ (hU w).1, hV, hVO, rfl⟩, ⟨fun w ↦ ?_, fun v ↦ ?_⟩, ?_⟩
    · rw [infiniteProj_eq]
      exact (hU w).2
    · rw [finiteProj_eq]
      exact hxV v
    · rintro y ⟨hyU, hyV⟩
      have hya : (e y).1 ∈ a := by
        have : p (e y).1 ∈ p.symm ⁻¹' a := hUa fun w _ ↦ by
          rw [← infiniteProj_eq]
          exact hyU w
        change p.symm (p (e y).1) ∈ a at this; exact (congrArg (fun z : (InfiniteAdeleRing K)ˣ ↦ z ∈ a) (p.symm_apply_apply (e y).1)).mp this
      have hyb : (e y).2 ∈ b := hVb fun v ↦ by
        rw [← finiteProj_eq]
        exact hyV v
      have := hab (Set.mk_mem_prod hya hyb); simpa using this
end IdeleGroup
end Sec2_IdeleBasis


/-! ### NormResidueAbstract -/
section Sec3_Abstract
open Filter Topology NumberField IsDedekindDomain
open scoped NumberField.AdeleRing
namespace IdeleGroup
variable {K : Type*} [Field K] [NumberField K]
theorem eventually_finiteProj_mem_units (x : IdeleGroup K) : ∀ᶠ v in cofinite, finiteProj v x ∈ (Submonoid.ofClass (v.adicCompletionIntegers K)).units := by
  filter_upwards [(prodRestrictedEquiv K x).2.2] with v hv
  rw [finiteProj_eq]
  exact hv
end IdeleGroup
namespace IdeleMap
open IdeleGroup
variable {K : Type*} [Field K] [NumberField K] {G : Type*} [CommGroup G] (φ : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* G) (φinf : ∀ w : InfinitePlace K, (w.Completion)ˣ →* G)
theorem hasFiniteMulSupport (hφ : ∀ᶠ v in cofinite, (Submonoid.ofClass (v.adicCompletionIntegers K)).units ≤ (φ v).ker) (x : IdeleGroup K) : Function.HasFiniteMulSupport fun v ↦ φ v (finiteProj v x) := by
  have h : ∀ᶠ v in cofinite, φ v (finiteProj v x) = 1 := by
    filter_upwards [hφ, eventually_finiteProj_mem_units x] with v hv hx
    exact hv hx
  exact eventually_cofinite.1 h
def ideleMap (hφ : ∀ᶠ v in cofinite, (Submonoid.ofClass (v.adicCompletionIntegers K)).units ≤ (φ v).ker) : IdeleGroup K →* G where
  toFun x := (∏ᶠ v, φ v (finiteProj v x)) * ∏ w, φinf w (infiniteProj w x)
  map_one' := by simp
  map_mul' x y := by
    simp only [map_mul]
    rw [finprod_mul_distrib (hasFiniteMulSupport φ hφ x) (hasFiniteMulSupport φ hφ y), Finset.prod_mul_distrib]
    exact mul_mul_mul_comm _ _ _ _
variable (hφ : ∀ᶠ v in cofinite, (Submonoid.ofClass (v.adicCompletionIntegers K)).units ≤ (φ v).ker)
theorem ideleMap_apply (x : IdeleGroup K) : ideleMap φ φinf hφ x = (∏ᶠ v, φ v (finiteProj v x)) * ∏ w, φinf w (infiniteProj w x) :=
  rfl
@[simp]
theorem ideleMap_finiteEmbedding (v : HeightOneSpectrum (𝓞 K)) (a : (v.adicCompletion K)ˣ) : ideleMap φ φinf hφ (finiteEmbedding v a) = φ v a := by
  rw [ideleMap_apply, finprod_eq_single _ v fun u hu ↦ by
    rw [finiteProj_finiteEmbedding_of_ne hu, map_one]]
  have h : ∀ w, infiniteProj w (finiteEmbedding v a) = 1 := fun w ↦ Units.ext rfl; simp [h]
@[simp]
theorem ideleMap_infiniteEmbedding (w : InfinitePlace K) (a : (w.Completion)ˣ) : ideleMap φ φinf hφ (infiniteEmbedding w a) = φinf w a := by
  rw [ideleMap_apply, Finset.prod_eq_single w (fun u _ hu ↦ by
    rw [infiniteProj_infiniteEmbedding_of_ne hu, map_one]) (fun h ↦ (h (Finset.mem_univ w)).elim)]
  have h : ∀ v, finiteProj v (infiniteEmbedding w a) = 1 := fun v ↦ Units.ext rfl; simp [h]
theorem ideleMap_comp_finiteEmbedding (v : HeightOneSpectrum (𝓞 K)) : (ideleMap φ φinf hφ).comp (finiteEmbedding v) = φ v :=
  MonoidHom.ext (ideleMap_finiteEmbedding φ φinf hφ v)
theorem ideleMap_comp_infiniteEmbedding (w : InfinitePlace K) : (ideleMap φ φinf hφ).comp (infiniteEmbedding w) = φinf w :=
  MonoidHom.ext (ideleMap_infiniteEmbedding φ φinf hφ w)
theorem ideleMap_eq_one_of_forall_mem (N : ∀ v : HeightOneSpectrum (𝓞 K), Subgroup (v.adicCompletion K)ˣ) (Ninf : ∀ w : InfinitePlace K, Subgroup (w.Completion)ˣ)
    (hN : ∀ v, N v ≤ (φ v).ker) (hNinf : ∀ w, Ninf w ≤ (φinf w).ker) {x : IdeleGroup K}
    (hx : ∀ v, finiteProj v x ∈ N v) (hxinf : ∀ w, infiniteProj w x ∈ Ninf w) :
    ideleMap φ φinf hφ x = 1 := by
  rw [ideleMap_apply, finprod_eq_one_of_forall_eq_one fun v ↦ hN v (hx v), Finset.prod_eq_one fun w _ ↦ hNinf w (hxinf w), mul_one]
variable [TopologicalSpace G] [DiscreteTopology G]
theorem continuous_ideleMap (hφc : ∀ v, Continuous (φ v)) (hφinfc : ∀ w, Continuous (φinf w)) : Continuous (ideleMap φ φinf hφ) := by
  have hker : ∀ {X : Type _} [TopologicalSpace X] [Group X] (f : X →* G), Continuous f →
      IsOpen (f.ker : Set X) := fun f hf ↦ by
    rw [MonoidHom.coe_ker]
    exact (isOpen_discrete ({1} : Set G)).preimage hf
  set V : ∀ v : HeightOneSpectrum (𝓞 K), Set (v.adicCompletion K)ˣ := fun v ↦
    ((Submonoid.ofClass (v.adicCompletionIntegers K)).units : Set (v.adicCompletion K)ˣ) ∩ ((φ v).ker : Set (v.adicCompletion K)ˣ) with hVdef
  set W : Set (IdeleGroup K) :=
    {x | (∀ w, infiniteProj w x ∈ ((φinf w).ker : Set (w.Completion)ˣ)) ∧
      ∀ v, finiteProj v x ∈ V v} with hWdef
  have hWo : IsOpen W := (isTopologicalBasis K).isOpen ⟨fun w ↦ ((φinf w).ker : Set (w.Completion)ˣ), V, fun w ↦ hker _ (hφinfc w), fun v ↦ (isOpen_units_adicCompletionIntegers K v).inter (hker _ (hφc v)),
      hφ.mono fun v hv ↦ Set.inter_eq_left.2 (SetLike.coe_subset_coe.2 hv), rfl⟩
  have h1W : (1 : IdeleGroup K) ∈ W :=
    ⟨fun w ↦ by simp, fun v ↦ by simp [V]⟩
  have hψW : ∀ x ∈ W, ideleMap φ φinf hφ x = 1 := fun x hx ↦
    ideleMap_eq_one_of_forall_mem φ φinf hφ (fun v ↦ (φ v).ker) (fun w ↦ (φinf w).ker) (fun _ ↦ le_rfl) (fun _ ↦ le_rfl) (fun v ↦ (hx.2 v).2) hx.1
  refine continuous_of_continuousAt_one _ ?_
  rw [ContinuousAt, map_one, nhds_discrete G, tendsto_pure]
  exact eventually_of_mem (hWo.mem_nhds h1W) hψW
def continuousIdeleMap (hφc : ∀ v, Continuous (φ v)) (hφinfc : ∀ w, Continuous (φinf w)) : IdeleGroup K →ₜ* G where
  toMonoidHom := ideleMap φ φinf hφ
  continuous_toFun := continuous_ideleMap φ φinf hφ hφc hφinfc
@[simp]
theorem continuousIdeleMap_apply (hφc : ∀ v, Continuous (φ v)) (hφinfc : ∀ w, Continuous (φinf w)) (x : IdeleGroup K) : continuousIdeleMap φ φinf hφ hφc hφinfc x = ideleMap φ φinf hφ x :=
  rfl
end IdeleMap
end Sec3_Abstract


/-! ### NormResidueAbstractUnique -/
section Sec3_AbstractUnique
open Filter Topology NumberField IsDedekindDomain
open scoped NumberField.AdeleRing
namespace IdeleGroup
variable (K : Type*) [Field K] [NumberField K]
def localEmbeddingSubgroup : Subgroup (IdeleGroup K) :=
  (⨆ v : HeightOneSpectrum (𝓞 K), (finiteEmbedding v).range) ⊔ ⨆ w : InfinitePlace K, (infiniteEmbedding w).range
variable {K}
theorem finiteEmbedding_mem_localEmbeddingSubgroup (v : HeightOneSpectrum (𝓞 K)) (a : (v.adicCompletion K)ˣ) : finiteEmbedding v a ∈ localEmbeddingSubgroup K :=
  Subgroup.mem_sup_left (Subgroup.mem_iSup_of_mem v ⟨a, rfl⟩)
theorem infiniteEmbedding_mem_localEmbeddingSubgroup (w : InfinitePlace K) (a : (w.Completion)ˣ) : infiniteEmbedding w a ∈ localEmbeddingSubgroup K :=
  Subgroup.mem_sup_right (Subgroup.mem_iSup_of_mem w ⟨a, rfl⟩)
theorem exists_mem_localEmbeddingSubgroup_inv_mul_mem {N : Set (IdeleGroup K)} (hN : N ∈ 𝓝 1)
    (x : IdeleGroup K) : ∃ h ∈ localEmbeddingSubgroup K, h⁻¹ * x ∈ N := by
  classical
  obtain ⟨_, ⟨U, V, -, -, hVO, rfl⟩, h1, htN⟩ := (isTopologicalBasis K).mem_nhds_iff.1 hN
  have hU1 : ∀ w, (1 : (w.Completion)ˣ) ∈ U w := fun w ↦ by simpa using h1.1 w
  have hV1 : ∀ v, (1 : (v.adicCompletion K)ˣ) ∈ V v := fun v ↦ by simpa using h1.2 v
  have hS : {v : HeightOneSpectrum (𝓞 K) | ¬ (V v =
      ((Submonoid.ofClass (v.adicCompletionIntegers K)).units : Set (v.adicCompletion K)ˣ) ∧
        finiteProj v x ∈ (Submonoid.ofClass (v.adicCompletionIntegers K)).units)}.Finite :=
    eventually_cofinite.1 (hVO.and (eventually_finiteProj_mem_units x))
  set S := hS.toFinset with hSdef
  set h : IdeleGroup K := (∏ w, infiniteEmbedding w (infiniteProj w x)) * ∏ v ∈ S, finiteEmbedding v (finiteProj v x) with hhdef; refine ⟨h, ?_, htN ⟨fun w ↦ ?_, fun v ↦ ?_⟩⟩
  · exact Subgroup.mul_mem _ (Subgroup.prod_mem _ fun w _ ↦ infiniteEmbedding_mem_localEmbeddingSubgroup _ _) (Subgroup.prod_mem _ fun v _ ↦ finiteEmbedding_mem_localEmbeddingSubgroup _ _)
  · have hfi : ∀ (u : HeightOneSpectrum (𝓞 K)) (a : (u.adicCompletion K)ˣ),
        infiniteProj w (finiteEmbedding u a) = 1 := fun _ _ ↦ Units.ext rfl
    have hw : infiniteProj w h = infiniteProj w x := by
      simp only [h, map_mul, map_prod, hfi, Finset.prod_const_one, mul_one]
      rw [Finset.prod_eq_single w (fun u _ hu ↦ infiniteProj_infiniteEmbedding_of_ne (Ne.symm hu) _) (fun hw ↦ (hw (Finset.mem_univ w)).elim)]
      simp
    rw [map_mul, map_inv, hw, inv_mul_cancel]
    exact hU1 w
  · have hif : ∀ (u : InfinitePlace K) (a : (u.Completion)ˣ),
        finiteProj v (infiniteEmbedding u a) = 1 := fun _ _ ↦ Units.ext rfl
    by_cases hv : v ∈ S
    · have hv' : finiteProj v h = finiteProj v x := by
        simp only [h, map_mul, map_prod, hif, Finset.prod_const_one, one_mul]
        rw [Finset.prod_eq_single_of_mem v hv (fun u _ hu ↦ finiteProj_finiteEmbedding_of_ne (Ne.symm hu) _)]
        simp
      rw [map_mul, map_inv, hv', inv_mul_cancel]
      exact hV1 v
    · have hv' : finiteProj v h = 1 := by
        simp only [h, map_mul, map_prod, hif, Finset.prod_const_one, one_mul]
        rw [Finset.prod_eq_one (fun u hu ↦ finiteProj_finiteEmbedding_of_ne (by rintro rfl; exact hv hu) _)]
      have hvS := hv; rw [hSdef, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_not] at hvS; rw [map_mul, map_inv, hv', inv_one, one_mul, hvS.1]; exact hvS.2
theorem dense_localEmbeddingSubgroup : Dense (localEmbeddingSubgroup K : Set (IdeleGroup K)) := by
  refine fun x ↦ mem_closure_iff_nhds.2 fun t ht ↦ ?_
  have hN : {y : IdeleGroup K | x * y⁻¹ ∈ t} ∈ 𝓝 (1 : IdeleGroup K) := by have hc : Continuous fun y : IdeleGroup K ↦ x * y⁻¹ := continuous_const.mul continuous_inv; exact hc.continuousAt.preimage_mem_nhds (by simpa using ht)
  obtain ⟨h, hh, hhN⟩ := exists_mem_localEmbeddingSubgroup_inv_mul_mem hN x; exact ⟨h, by simpa using hhN, hh⟩
theorem continuous_monoidHom_ext {M : Type*} [Monoid M] [TopologicalSpace M] [T2Space M] {ψ ψ' : IdeleGroup K →* M} (hψ : Continuous ψ) (hψ' : Continuous ψ') (hfin : ∀ v a, ψ (finiteEmbedding v a) = ψ' (finiteEmbedding v a))
    (hinf : ∀ w a, ψ (infiniteEmbedding w a) = ψ' (infiniteEmbedding w a)) : ψ = ψ' := by
  have hle : localEmbeddingSubgroup K ≤ ψ.eqLocus ψ' :=
    sup_le (iSup_le fun v ↦ by rintro _ ⟨a, rfl⟩; exact hfin v a) (iSup_le fun w ↦ by rintro _ ⟨a, rfl⟩; exact hinf w a)
  exact MonoidHom.ext (congrFun (Continuous.ext_on dense_localEmbeddingSubgroup hψ hψ' fun x hx ↦ hle hx))
end IdeleGroup
namespace IdeleMap
open IdeleGroup
variable {K : Type*} [Field K] [NumberField K] {G : Type*} [CommGroup G] [TopologicalSpace G] [DiscreteTopology G] (φ : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* G) (φinf : ∀ w : InfinitePlace K, (w.Completion)ˣ →* G)
  (hφ : ∀ᶠ v in cofinite, (Submonoid.ofClass (v.adicCompletionIntegers K)).units ≤ (φ v).ker)
theorem eq_ideleMap (hφc : ∀ v, Continuous (φ v)) (hφinfc : ∀ w, Continuous (φinf w)) {ψ : IdeleGroup K →* G} (hψ : Continuous ψ) (hfin : ∀ v, ψ.comp (finiteEmbedding v) = φ v) (hinf : ∀ w, ψ.comp (infiniteEmbedding w) = φinf w) :
    ψ = ideleMap φ φinf hφ :=
  continuous_monoidHom_ext hψ (continuous_ideleMap φ φinf hφ hφc hφinfc) (fun v a ↦ by rw [ideleMap_finiteEmbedding, ← hfin v, MonoidHom.comp_apply]) (fun w a ↦ by rw [ideleMap_infiniteEmbedding, ← hinf w, MonoidHom.comp_apply])
include hφ in
theorem existsUnique_ideleMap (hφc : ∀ v, Continuous (φ v)) (hφinfc : ∀ w, Continuous (φinf w)) : ∃! ψ : IdeleGroup K →* G, Continuous ψ ∧ (∀ v, ψ.comp (finiteEmbedding v) = φ v) ∧ ∀ w, ψ.comp (infiniteEmbedding w) = φinf w :=
  ⟨ideleMap φ φinf hφ, ⟨continuous_ideleMap φ φinf hφ hφc hφinfc, ideleMap_comp_finiteEmbedding φ φinf hφ, ideleMap_comp_infiniteEmbedding φ φinf hφ⟩, fun _ hψ ↦ eq_ideleMap φ φinf hφ hφc hφinfc hψ.1 hψ.2.1 hψ.2.2⟩
end IdeleMap
end Sec3_AbstractUnique


end RHDirect.Stage13CFT_IdeleNormResidue
