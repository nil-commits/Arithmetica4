import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.PNat.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.FieldTheory.AlgebraicClosure
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.GroupTheory.Abelianization.Finite
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.GroupTheory.Finiteness
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.IndexNormal
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.QuotientGroup.Finite
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.Transfer
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.Tactic.Group
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.Group.Compact
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Algebra.Group.ClosedSubgroup
import Mathlib.Topology.Algebra.Group.TopologicalAbelianization
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Limits
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Instances.ZMod

/-!
# RHDirect.CFT_AbstractLocalReciprocity

Abstract Local Class Field Theory (Neukirch / Hazewinkel) + CFT Power Subgroups:
- `PowerSubgroups`: `relIndex_sup_of_le_normalizer`, `mulZPowers`, `le_powerSubgroup₂`,
  `mem_mulZPowers_self`, `exists_eq_unit_mul_pow_adicCompletion`,
  `exists_pow_apply_eq_self_of_aeval_eq_zero`.
- `ProfiniteInteger` (`ℤ̂`) and its topology, multiples, and density of `ℤ`.
- `ClassFieldData`, `ClassFieldAxiom`, `ClassFieldTheory`, norms, Henselian valuations,
  Frobenius lifts, unramified extensions, Neukirch reciprocity map, multiplicativity,
  functoriality (restriction, norm, Verlagerung/transfer), reciprocity isomorphism
  (cyclic -> p-group -> general finite Galois), norm group correspondence, and profinite
  reciprocity limit.
-/

namespace RHDirect.CFT_AbstractLocalReciprocity

namespace PowerSubgroups

section Sec_PS_RelIndexSup

open Subgroup

theorem relIndex_sup_of_le_normalizer {G : Type*} [Group G] {H N : Subgroup G}
    (hLE : H ≤ Subgroup.normalizer (N : Set G)) : H.relIndex (H ⊔ N) = H.relIndex N := by
  symm
  let f : N →* (H ⊔ N : Subgroup G) := Subgroup.inclusion le_sup_right
  let g : N ⧸ H.subgroupOf N → (H ⊔ N : Subgroup G) ⧸ H.subgroupOf (H ⊔ N) :=
    fun q => Quotient.liftOn' q (fun n => ((f n : (H ⊔ N : Subgroup G)) :
        (H ⊔ N : Subgroup G) ⧸ H.subgroupOf (H ⊔ N))) (by
      intro a b hab
      rw [QuotientGroup.leftRel_apply, mem_subgroupOf] at hab
      rw [QuotientGroup.eq, mem_subgroupOf]
      simpa [f] using hab)
  have hinj : Function.Injective g := by
    intro x y hxy
    induction x using QuotientGroup.induction_on with
    | H a =>
    induction y using QuotientGroup.induction_on with
    | H b =>
    have h1 : ((f a : (H ⊔ N : Subgroup G)) : (H ⊔ N : Subgroup G) ⧸ H.subgroupOf (H ⊔ N)) =
        ((f b : (H ⊔ N : Subgroup G)) : (H ⊔ N : Subgroup G) ⧸ H.subgroupOf (H ⊔ N)) := hxy
    rw [QuotientGroup.eq, mem_subgroupOf] at h1
    rw [QuotientGroup.eq, mem_subgroupOf]
    simpa [f] using h1
  have hsurj : Function.Surjective g := by
    intro x
    induction x using QuotientGroup.induction_on with
    | H k =>
    obtain ⟨y, hy⟩ := k
    have hy' : y ∈ ((N ⊔ H : Subgroup G) : Set G) := by
      rw [sup_comm]; exact hy
    rw [coe_mul_of_right_le_normalizer_left N H hLE] at hy'
    obtain ⟨n, hn, h, hh, rfl⟩ := hy'
    refine ⟨((⟨n, hn⟩ : N) : N ⧸ H.subgroupOf N), ?_⟩
    change ((f ⟨n, hn⟩ : (H ⊔ N : Subgroup G)) :
        (H ⊔ N : Subgroup G) ⧸ H.subgroupOf (H ⊔ N)) = _
    rw [QuotientGroup.eq, mem_subgroupOf]
    simpa [f] using hh
  rw [Subgroup.relIndex, Subgroup.relIndex, Subgroup.index, Subgroup.index]
  exact Nat.card_congr (Equiv.ofBijective g ⟨hinj, hsurj⟩)

end Sec_PS_RelIndexSup

section Sec_PS_PowInvariant

def mulZPowers (U : Subgroup Gal(AlgebraicClosure ℚ/ℚ)) (s : Gal(AlgebraicClosure ℚ/ℚ))
    (hU : ∀ (k : ℤ), ∀ x ∈ U, s ^ k * x * (s ^ k)⁻¹ ∈ U) :
    Subgroup Gal(AlgebraicClosure ℚ/ℚ) where
  carrier := {x | ∃ k : ℤ, ∃ u ∈ U, x = s ^ k * u}
  one_mem' := ⟨0, 1, U.one_mem, by simp⟩
  mul_mem' := by
    rintro _ _ ⟨a, u, hu, rfl⟩ ⟨b, v, hv, rfl⟩
    refine ⟨a + b, s ^ (-b) * u * (s ^ (-b))⁻¹ * v, U.mul_mem (hU (-b) u hu) hv, ?_⟩
    rw [zpow_add, zpow_neg, inv_inv]
    group
  inv_mem' := by
    rintro _ ⟨k, u, hu, rfl⟩
    refine ⟨-k, s ^ k * u⁻¹ * (s ^ k)⁻¹, hU k _ (U.inv_mem hu), ?_⟩
    rw [zpow_neg]
    group

theorem le_powerSubgroup₂ (U : Subgroup Gal(AlgebraicClosure ℚ/ℚ))
    (s : Gal(AlgebraicClosure ℚ/ℚ)) (hU : ∀ (k : ℤ), ∀ x ∈ U, s ^ k * x * (s ^ k)⁻¹ ∈ U) :
    U ≤ mulZPowers U s hU := fun u hu => ⟨0, u, hu, by simp⟩

theorem mem_mulZPowers_self (U : Subgroup Gal(AlgebraicClosure ℚ/ℚ))
    (s : Gal(AlgebraicClosure ℚ/ℚ)) (hU : ∀ (k : ℤ), ∀ x ∈ U, s ^ k * x * (s ^ k)⁻¹ ∈ U) :
    s ∈ mulZPowers U s hU := ⟨1, 1, U.one_mem, by simp⟩

end Sec_PS_PowInvariant

section Sec_PS_UnitMulPowAdic

open IsLocalRing

theorem exists_eq_unit_mul_pow_adicCompletion {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {ϖ : R} (hϖ : Irreducible ϖ)
    {x : AdicCompletion (maximalIdeal R) R} (hx : x ≠ 0) :
    ∃ (n : ℕ) (u : (AdicCompletion (maximalIdeal R) R)ˣ),
      x = ↑u * (algebraMap R (AdicCompletion (maximalIdeal R) R)) ϖ ^ n := by

  have hM : maximalIdeal (AdicCompletion (maximalIdeal R) R) =
      Ideal.span {algebraMap R (AdicCompletion (maximalIdeal R) R) ϖ} := by
    have e := congrArg (Ideal.map (algebraMap R (AdicCompletion (maximalIdeal R) R)))
      hϖ.maximalIdeal_eq
    rw [AdicCompletion.maximalIdeal_eq_map, e, Ideal.map_span, Set.image_singleton]
  have hMpow : ∀ k : ℕ, maximalIdeal (AdicCompletion (maximalIdeal R) R) ^ k =
      Ideal.span {algebraMap R (AdicCompletion (maximalIdeal R) R) ϖ ^ k} := fun k => by
    rw [hM, Ideal.span_singleton_pow]

  have hex : ∃ k : ℕ, x ∉ maximalIdeal (AdicCompletion (maximalIdeal R) R) ^ k := by
    by_contra h
    push Not at h
    apply hx
    apply IsHausdorff.haus (IsAdicComplete.toIsHausdorff
      (I := maximalIdeal (AdicCompletion (maximalIdeal R) R))
      (M := AdicCompletion (maximalIdeal R) R)) x
    intro k
    simpa only [← Ideal.one_eq_top, smul_eq_mul, mul_one, SModEq.zero] using h k
  classical
  have hk : x ∉ maximalIdeal (AdicCompletion (maximalIdeal R) R) ^ Nat.find hex :=
    Nat.find_spec hex
  have hk0 : Nat.find hex ≠ 0 := by
    intro h0
    apply hk
    rw [h0, pow_zero, Ideal.one_eq_top]
    exact Submodule.mem_top
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hk0
  have hxn : x ∈ maximalIdeal (AdicCompletion (maximalIdeal R) R) ^ n := by
    have := Nat.find_min hex (show n < Nat.find hex by omega)
    simpa using this
  rw [hMpow, Ideal.mem_span_singleton'] at hxn
  obtain ⟨y, hy⟩ := hxn
  have hyu : IsUnit y := by
    rw [← notMem_maximalIdeal]
    intro hyM
    apply hk
    rw [hn, hMpow, Ideal.mem_span_singleton']
    rw [hM, Ideal.mem_span_singleton'] at hyM
    obtain ⟨z, hz⟩ := hyM
    exact ⟨z, by rw [← hy, ← hz, pow_succ]; ring⟩
  exact ⟨n, hyu.unit, by rw [IsUnit.unit_spec, hy]⟩

end Sec_PS_UnitMulPowAdic

section Sec_PS_DescentPowerSubgroups

theorem exists_pow_apply_eq_self_of_aeval_eq_zero {K : Type*} [Field K] {Ω : Type*} [Field Ω]
    [Algebra K Ω] (σ : Gal(Ω/K)) {p : Polynomial K} (hp : p ≠ 0) {x : Ω}
    (hx : Polynomial.aeval x p = 0) : ∃ N : ℕ, 0 < N ∧ (σ ^ N) x = x := by
  have hmem : ∀ n : ℕ, (σ ^ n) x ∈ p.rootSet Ω := fun n => by
    rw [Polynomial.mem_rootSet_of_ne hp, Polynomial.aeval_algHom_apply, hx, map_zero]
  have : Finite (p.rootSet Ω) := (Polynomial.rootSet_finite p Ω).to_subtype
  let f : ℕ → p.rootSet Ω := fun n => ⟨(σ ^ n) x, hmem n⟩
  obtain ⟨i, j, hne, hij⟩ := Finite.exists_ne_map_eq_of_infinite f
  have key : (σ ^ i) x = (σ ^ j) x := congrArg Subtype.val hij
  rcases lt_or_gt_of_ne hne with h | h
  · refine ⟨j - i, Nat.sub_pos_of_lt h, ?_⟩
    apply (σ ^ i).injective
    rw [← AlgEquiv.mul_apply, ← pow_add, Nat.add_sub_cancel' h.le, key]
  · refine ⟨i - j, Nat.sub_pos_of_lt h, ?_⟩
    apply (σ ^ j).injective
    rw [← AlgEquiv.mul_apply, ← pow_add, Nat.add_sub_cancel' h.le, key]

end Sec_PS_DescentPowerSubgroups

end PowerSubgroups

section Sec_TransferAux

private theorem transfer_of_comp_subtype_aux.{u_1} :
    ∀ {Γ : Type u_1} [Group Γ] (H : Subgroup Γ)
    [H.FiniteIndex] (g : Γ),
    ((Abelianization.of.comp H.subtype).transfer : Γ → Abelianization Γ) g =
      (Abelianization.of : Γ → Abelianization Γ) g ^ H.index := by
  intro Γ _ H _ g
  classical
  let _ := H.fintypeQuotientOfFiniteIndex
  rw [MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot,
    Subgroup.index_eq_sum_minimalPeriod H g, ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_congr rfl fun q _ => ?_
  rw [MonoidHom.comp_apply, Subgroup.subtype_apply, map_mul, map_mul, map_inv, map_pow,
    inv_mul_cancel_comm]

end Sec_TransferAux

section Sec_ALR_ProfiniteInteger

def profiniteIntegers : Subring (∀ n : ℕ+, ZMod n) :=
  ⨅ (m : ℕ+) (n : ℕ+) (h : (m : ℕ) ∣ n),
    RingHom.eqLocus ((ZMod.castHom h (ZMod m)).comp (Pi.evalRingHom (fun k : ℕ+ => ZMod k) n))
      (Pi.evalRingHom (fun k : ℕ+ => ZMod k) m)

/-- The ring of profinite integers `ℤ̂ = lim← ZMod n`. -/
abbrev ProfiniteInteger : Type := profiniteIntegers

@[inherit_doc] scoped notation "ℤ̂" => ProfiniteInteger

theorem mem_profiniteIntegers {x : ∀ n : ℕ+, ZMod n} :
    x ∈ profiniteIntegers ↔
      ∀ (m n : ℕ+) (h : (m : ℕ) ∣ n), ZMod.castHom h (ZMod m) (x n) = x m := by
  simp [profiniteIntegers, Subring.mem_iInf, RingHom.mem_eqLocus]

namespace ProfiniteInteger

def proj (n : ℕ+) : ℤ̂ →+* ZMod n :=
  (Pi.evalRingHom (fun k : ℕ+ => ZMod k) n).comp profiniteIntegers.subtype

@[simp] theorem proj_apply (n : ℕ+) (x : ℤ̂) : proj n x = (x : ∀ k : ℕ+, ZMod k) n := rfl

theorem castHom_proj {m n : ℕ+} (h : (m : ℕ) ∣ n) (x : ℤ̂) :
    ZMod.castHom h (ZMod m) (proj n x) = proj m x :=
  mem_profiniteIntegers.1 x.2 m n h

@[ext] theorem ext {x y : ℤ̂} (h : ∀ n, proj n x = proj n y) : x = y :=
  Subtype.ext (funext h)

@[simp] theorem proj_intCast (n : ℕ+) (m : ℤ) : proj n (m : ℤ̂) = m := map_intCast _ m

theorem isClosed_profiniteIntegers :
    IsClosed (profiniteIntegers : Set (∀ n : ℕ+, ZMod n)) := by
  have : (profiniteIntegers : Set (∀ n : ℕ+, ZMod n)) =
      ⋂ (m : ℕ+) (n : ℕ+) (h : (m : ℕ) ∣ n), {x | ZMod.castHom h (ZMod m) (x n) = x m} := by
    ext x
    simp only [SetLike.mem_coe, mem_profiniteIntegers, Set.mem_iInter, Set.mem_ofPred_eq]
  rw [this]
  refine isClosed_iInter fun m => isClosed_iInter fun n => isClosed_iInter fun h => ?_
  exact isClosed_eq (continuous_of_discreteTopology.comp (continuous_apply n)) (continuous_apply m)

instance : CompactSpace ℤ̂ :=
  isCompact_iff_compactSpace.mp isClosed_profiniteIntegers.isCompact

theorem continuous_proj (n : ℕ+) : Continuous (proj n) :=
  (continuous_apply n).comp continuous_subtype_val

instance : CharZero ℤ̂ := by
  refine charZero_of_inj_zero fun n hn => ?_
  have h := congrArg (proj n.succPNat) hn
  rw [map_natCast, map_zero, ZMod.natCast_eq_zero_iff, Nat.succPNat_coe] at h
  exact Nat.eq_zero_of_dvd_of_lt h (Nat.lt_succ_self n)

theorem dvd_of_intCast_eq_nsmul {n : ℕ} (hn : 0 < n) {m : ℤ} {w : ℤ̂} (h : (m : ℤ̂) = n • w) :
    (n : ℤ) ∣ m := by
  obtain ⟨N, rfl⟩ : ∃ N : ℕ+, (N : ℕ) = n := ⟨⟨n, hn⟩, rfl⟩
  have h' := congrArg (proj N) h
  rw [map_intCast, map_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul] at h'
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd m N).1 h'

end ProfiniteInteger

end Sec_ALR_ProfiniteInteger

section Sec_ALR_ExistsOpenSubgroupMemFixedModule

section FixedModule

variable {G : Type*} [Group G] (A : Type*) [CommGroup A] [MulDistribMulAction G A]

def fixedModule (H : Subgroup G) : Subgroup A where
  carrier := {a | ∀ g ∈ H, g • a = a}
  mul_mem' {a b} ha hb g hg := by rw [smul_mul', ha g hg, hb g hg]
  one_mem' g _ := smul_one g
  inv_mem' {a} ha g hg := by rw [smul_inv', ha g hg]

variable {A}

theorem mem_fixedModule {H : Subgroup G} {a : A} :
    a ∈ fixedModule A H ↔ ∀ g ∈ H, g • a = a :=
  Iff.rfl

theorem fixedModule_anti {H H' : Subgroup G} (h : H ≤ H') : fixedModule A H' ≤ fixedModule A H :=
  fun _ ha g hg => ha g (h hg)

theorem coe_fixedModule (H : Subgroup G) :
    (fixedModule A H : Set A) = MulAction.fixedPoints H A := by
  ext a
  simp only [SetLike.mem_coe, mem_fixedModule, MulAction.mem_fixedPoints, Subtype.forall,
    Subgroup.mk_smul]

theorem smul_mem_fixedModule {H : Subgroup G} {a : A} (ha : a ∈ fixedModule A H) (g : G) :
    g • a ∈ fixedModule A (H.map (MulAut.conj g).toMonoidHom) := by
  rintro _ ⟨h, hh, rfl⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ← mul_smul]
  rw [show g * h * g⁻¹ * g = g * h by group, mul_smul, ha h hh]

end FixedModule

section Discrete

class IsDiscreteModule (G : Type*) [Group G] [TopologicalSpace G] (A : Type*) [CommGroup A]
    [MulDistribMulAction G A] : Prop where
  isOpen_stabilizer : ∀ a : A, IsOpen (MulAction.stabilizer G a : Set G)

variable {G : Type*} [Group G] [TopologicalSpace G] {A : Type*} [CommGroup A]
  [MulDistribMulAction G A]

theorem isDiscreteModule_iff [ContinuousMul G] :
    IsDiscreteModule G A ↔ ∀ a : A, ∃ U : OpenSubgroup G, a ∈ fixedModule A (U : Subgroup G) := by
  constructor
  · intro h a
    exact ⟨⟨MulAction.stabilizer G a, h.isOpen_stabilizer a⟩, fun g hg => hg⟩
  · intro h
    refine ⟨fun a => ?_⟩
    obtain ⟨U, hU⟩ := h a
    exact Subgroup.isOpen_mono (H₁ := (U : Subgroup G)) (fun g hg => hU g hg) U.isOpen

theorem exists_openSubgroup_mem_fixedModule [IsDiscreteModule G A] (a : A) :
    ∃ U : OpenSubgroup G, a ∈ fixedModule A (U : Subgroup G) :=
  ⟨⟨MulAction.stabilizer G a, IsDiscreteModule.isOpen_stabilizer a⟩, fun _ hg => hg⟩

end Discrete

section Norm

variable {G : Type*} [Group G] (A : Type*) [CommGroup A] [MulDistribMulAction G A]
variable (K L : Subgroup G)

def cosetSMul (a : fixedModule A L) : K ⧸ L.subgroupOf K → A :=
  Quotient.lift (fun σ : K => (σ : G) • (a : A)) fun σ τ hστ => by
    have h : σ⁻¹ * τ ∈ L.subgroupOf K := QuotientGroup.leftRel_apply.mp hστ
    rw [Subgroup.mem_subgroupOf] at h
    have ha := a.2 _ h
    calc (σ : G) • (a : A) = (σ : G) • ((((σ⁻¹ * τ : K)) : G) • (a : A)) := by rw [ha]
      _ = (τ : G) • (a : A) := by rw [smul_smul]; simp

variable {A K L}

@[simp] theorem cosetSMul_mk (a : fixedModule A L) (σ : K) :
    cosetSMul A K L a (σ : K ⧸ L.subgroupOf K) = (σ : G) • (a : A) :=
  rfl

theorem cosetSMul_one (q : K ⧸ L.subgroupOf K) : cosetSMul A K L 1 q = 1 := by
  induction q using QuotientGroup.induction_on with
  | H σ => simp

theorem cosetSMul_mul (a b : fixedModule A L) (q : K ⧸ L.subgroupOf K) :
    cosetSMul A K L (a * b) q = cosetSMul A K L a q * cosetSMul A K L b q := by
  induction q using QuotientGroup.induction_on with
  | H σ => simp [smul_mul']

theorem smul_cosetSMul (a : fixedModule A L) (g : K) (q : K ⧸ L.subgroupOf K) :
    (g : G) • cosetSMul A K L a q = cosetSMul A K L a (g • q) := by
  induction q using QuotientGroup.induction_on with
  | H σ =>
    rw [cosetSMul_mk, smul_smul]
    rfl

theorem smul_mem_fixedModule_of_normal (hLK : L ≤ K) [hN : (L.subgroupOf K).Normal] {g : G}
    (hg : g ∈ K) {a : A} (ha : a ∈ fixedModule A L) : g • a ∈ fixedModule A L := by
  intro h hh
  have hc : g⁻¹ * h * g ∈ L := by
    have := hN.conj_mem ⟨h, hLK hh⟩ (by simpa [Subgroup.mem_subgroupOf] using hh) ⟨g, hg⟩⁻¹
    simpa [Subgroup.mem_subgroupOf, mul_assoc] using this
  calc h • g • a = g • (g⁻¹ * h * g) • a := by simp [smul_smul, mul_assoc]
    _ = g • a := by rw [ha _ hc]

variable (A K L)

noncomputable def normFun (a : fixedModule A L) : A :=
  ∏ᶠ q, cosetSMul A K L a q

variable [(L.subgroupOf K).FiniteIndex]

theorem normFun_mem_fixedModule (a : fixedModule A L) : normFun A K L a ∈ fixedModule A K := by
  intro g hg
  unfold normFun
  rw [smul_finprod']
  simp_rw [smul_cosetSMul a ⟨g, hg⟩]
  exact finprod_comp_equiv (MulAction.toPerm (⟨g, hg⟩ : K))

noncomputable def norm : fixedModule A L →* fixedModule A K where
  toFun a := ⟨normFun A K L a, normFun_mem_fixedModule A K L a⟩
  map_one' := by
    ext
    simp [normFun, cosetSMul_one]
  map_mul' a b := by
    classical
    let _ := Fintype.ofFinite (K ⧸ L.subgroupOf K)
    ext
    simp only [normFun, Subgroup.coe_mul, finprod_eq_prod_of_fintype, cosetSMul_mul,
      Finset.prod_mul_distrib]

variable {A K L}

theorem coe_norm (a : fixedModule A L) :
    (norm A K L a : A) = ∏ᶠ q, cosetSMul A K L a q :=
  rfl

theorem norm_smul [(L.subgroupOf K).Normal] (g : K) (a : fixedModule A L)
    (hga : (g : G) • (a : A) ∈ fixedModule A L) :
    norm A K L ⟨(g : G) • (a : A), hga⟩ = norm A K L a := by
  ext
  rw [coe_norm, coe_norm]
  have h : ∀ q : K ⧸ L.subgroupOf K,
      cosetSMul A K L ⟨(g : G) • (a : A), hga⟩ q = cosetSMul A K L a (q * (g : K ⧸ L.subgroupOf K)) := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H σ =>
      rw [← QuotientGroup.mk_mul, cosetSMul_mk, cosetSMul_mk]
      simp [smul_smul]
  simp_rw [h]
  exact finprod_comp_equiv (Equiv.mulRight _)

variable (A K L)

def augmentation : Subgroup A :=
  Subgroup.closure {x | ∃ g ∈ K, ∃ a ∈ fixedModule A L, x = g • a / a}

abbrev tateZero : Type _ :=
  fixedModule A K ⧸ (norm A K L).range

abbrev tateNegOne : Type _ :=
  (norm A K L).ker ⧸
    (augmentation A K L).comap ((fixedModule A L).subtype.comp (norm A K L).ker.subtype)

variable {A K L}

theorem augmentation_le_map_ker (hLK : L ≤ K) [(L.subgroupOf K).Normal] :
    augmentation A K L ≤ (norm A K L).ker.map (fixedModule A L).subtype := by
  rw [augmentation, Subgroup.closure_le]
  rintro _ ⟨g, hg, a, ha, rfl⟩
  have hga := smul_mem_fixedModule_of_normal hLK hg ha
  refine ⟨⟨g • a, hga⟩ / ⟨a, ha⟩, ?_, rfl⟩
  rw [SetLike.mem_coe, MonoidHom.mem_ker, map_div, div_eq_one]
  exact norm_smul ⟨g, hg⟩ ⟨a, ha⟩ hga

end Norm

section Data

instance finiteIndex_openSubgroup {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] (U : OpenSubgroup G) : (U : Subgroup G).FiniteIndex :=
  Subgroup.finiteIndex_of_finite_quotient

variable {G : Type*} [Group G]

noncomputable def inertiaDegree (d : G →* Multiplicative ℤ̂) (K : Subgroup G) : ℕ :=
  (K.map d).index

noncomputable def ramificationIndex (d : G →* Multiplicative ℤ̂) (K : Subgroup G) : ℕ :=
  K.relIndex d.ker

variable (G) [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
variable (A : Type*) [CommGroup A] [MulDistribMulAction G A]

structure ClassFieldData where

  deg : G →* Multiplicative ℤ̂
  continuous_deg : Continuous deg
  surjective_deg : Function.Surjective deg

  val : fixedModule A (⊤ : Subgroup G) →* Multiplicative ℤ̂

  intCast_mem_range_val : ∀ n : ℤ, Multiplicative.ofAdd (n : ℤ̂) ∈ val.range

  exists_eq_intCast_add_nsmul : ∀ n : ℕ, 0 < n → ∀ a : fixedModule A (⊤ : Subgroup G),
    ∃ (m : ℤ) (b : fixedModule A (⊤ : Subgroup G)),
      Multiplicative.toAdd (val a) = (m : ℤ̂) + n • Multiplicative.toAdd (val b)

  range_val_comp_norm : ∀ K : OpenSubgroup G,
    (val.comp (norm A (⊤ : Subgroup G) (K : Subgroup G))).range =
      val.range.map (powMonoidHom (inertiaDegree deg (K : Subgroup G)))

def ClassFieldAxiom : Prop :=
  ∀ K L : OpenSubgroup G, L ≤ K → ∀ [((L : Subgroup G).subgroupOf K).Normal],
    IsCyclic (K ⧸ (L : Subgroup G).subgroupOf K) →
      Nat.card (tateZero A (K : Subgroup G) (L : Subgroup G)) = (L : Subgroup G).relIndex K ∧
        Nat.card (tateNegOne A (K : Subgroup G) (L : Subgroup G)) = 1

structure ClassFieldTheory extends ClassFieldData G A where
  isDiscreteModule : IsDiscreteModule G A
  classFieldAxiom : ClassFieldAxiom G A

end Data

end Sec_ALR_ExistsOpenSubgroupMemFixedModule

section Sec_ALR_UniqueQuotientSubgroupOfSelf

variable {G : Type*} [Group G] {A : Type*} [CommGroup A] [MulDistribMulAction G A]

section Self

variable (K : Subgroup G)

instance uniqueQuotientSubgroupOfSelf : Unique (K ⧸ K.subgroupOf K) where
  default := ((1 : K) : K ⧸ K.subgroupOf K)
  uniq q := by
    induction q using QuotientGroup.induction_on with
    | H σ =>
      rw [QuotientGroup.eq]
      simp

instance finiteIndex_subgroupOf_self : (K.subgroupOf K).FiniteIndex :=
  ⟨by simp [Subgroup.subgroupOf_self]⟩

theorem norm_self : norm A K K = MonoidHom.id (fixedModule A K) := by
  refine MonoidHom.ext fun a => Subtype.ext ?_
  rw [coe_norm, finprod_unique]
  show ((1 : K) : G) • (a : A) = a
  simp

end Self

section Pow

variable {K L : Subgroup G} [(L.subgroupOf K).FiniteIndex]

theorem coe_norm_of_mem (hLK : L ≤ K) {a : A} (ha : a ∈ fixedModule A K) :
    (norm A K L ⟨a, fixedModule_anti hLK ha⟩ : A) = a ^ L.relIndex K := by
  classical
  let _ := Fintype.ofFinite (K ⧸ L.subgroupOf K)
  rw [coe_norm, finprod_eq_prod_of_fintype]
  have h : ∀ q : K ⧸ L.subgroupOf K, cosetSMul A K L ⟨a, fixedModule_anti hLK ha⟩ q = a := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H σ => exact ha σ σ.2
  simp_rw [h]
  rw [Finset.prod_const, Finset.card_univ, ← Nat.card_eq_fintype_card, Subgroup.relIndex,
    Subgroup.index_eq_card]

end Pow

section Transitivity

variable {K L M : Subgroup G}

def cosetShift (hLK : L ≤ K) (σ : K) : L ⧸ M.subgroupOf L → K ⧸ M.subgroupOf K :=
  Quotient.map' (fun τ : L => σ * (⟨τ, hLK τ.2⟩ : K)) fun τ τ' h => by
    rw [QuotientGroup.leftRel_apply] at h ⊢
    simpa [Subgroup.mem_subgroupOf, mul_assoc] using h

@[simp] theorem cosetShift_mk (hLK : L ≤ K) (σ : K) (τ : L) :
    cosetShift (M := M) hLK σ (τ : L ⧸ M.subgroupOf L) =
      ((σ * (⟨τ, hLK τ.2⟩ : K) : K) : K ⧸ M.subgroupOf K) :=
  rfl

theorem norm_norm (hML : M ≤ L) (hLK : L ≤ K) [(L.subgroupOf K).FiniteIndex]
    [(M.subgroupOf L).FiniteIndex] [(M.subgroupOf K).FiniteIndex] (a : fixedModule A M) :
    norm A K L (norm A L M a) = norm A K M a := by
  classical
  let _ := Fintype.ofFinite (K ⧸ M.subgroupOf K)
  let _ := Fintype.ofFinite (K ⧸ L.subgroupOf K)
  let _ := Fintype.ofFinite (L ⧸ M.subgroupOf L)
  have hle : M.subgroupOf K ≤ L.subgroupOf K := fun x hx => hML hx
  ext
  simp only [coe_norm, finprod_eq_prod_of_fintype]
  rw [← Finset.prod_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ)
    (g := Subgroup.quotientMapOfLE hle) (fun _ _ => Finset.mem_univ _)]
  refine Finset.prod_congr rfl fun p _ => ?_
  induction p using QuotientGroup.induction_on with
  | H σ =>
    rw [cosetSMul_mk, coe_norm, finprod_eq_prod_of_fintype, Finset.smul_prod']
    refine Finset.prod_bij (fun t _ => cosetShift hLK σ t) ?_ ?_ ?_ ?_
    · intro t _
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      induction t using QuotientGroup.induction_on with
      | H τ =>
        rw [cosetShift_mk, Subgroup.quotientMapOfLE_apply_mk, QuotientGroup.eq]
        simp [Subgroup.mem_subgroupOf, mul_assoc]
    · intro t _ t' _ h
      induction t using QuotientGroup.induction_on with
      | H τ =>
      induction t' using QuotientGroup.induction_on with
      | H τ' =>
        rw [cosetShift_mk, cosetShift_mk, QuotientGroup.eq] at h
        rw [QuotientGroup.eq]
        simpa [Subgroup.mem_subgroupOf, mul_assoc] using h
    · intro q hq
      rw [Finset.mem_filter] at hq
      induction q using QuotientGroup.induction_on with
      | H ρ =>
        have h := hq.2
        rw [Subgroup.quotientMapOfLE_apply_mk, QuotientGroup.eq] at h
        have hmem : (σ : G)⁻¹ * ρ ∈ L := by
          have := L.inv_mem h
          simpa [Subgroup.mem_subgroupOf, mul_inv_rev] using this
        refine ⟨((⟨(σ : G)⁻¹ * ρ, hmem⟩ : L) : L ⧸ M.subgroupOf L), Finset.mem_univ _, ?_⟩
        rw [cosetShift_mk]
        congr 1
        ext
        simp
    · intro t _
      induction t using QuotientGroup.induction_on with
      | H τ =>
        rw [cosetShift_mk, cosetSMul_mk, cosetSMul_mk, smul_smul]
        rfl

theorem range_norm_le_range_norm (hML : M ≤ L) (hLK : L ≤ K) [(L.subgroupOf K).FiniteIndex]
    [(M.subgroupOf L).FiniteIndex] [(M.subgroupOf K).FiniteIndex] :
    (norm A K M).range ≤ (norm A K L).range := by
  rintro _ ⟨a, rfl⟩
  exact ⟨norm A L M a, norm_norm hML hLK a⟩

end Transitivity

section Conjugation

variable {K L : Subgroup G}

def cosetConj (σ : G) :
    K ⧸ L.subgroupOf K →
      K.map (MulAut.conj σ).toMonoidHom ⧸
        (L.map (MulAut.conj σ).toMonoidHom).subgroupOf (K.map (MulAut.conj σ).toMonoidHom) :=
  Quotient.map' (fun τ : K => (⟨σ * τ * σ⁻¹, τ, τ.2, rfl⟩ : K.map (MulAut.conj σ).toMonoidHom))
    fun τ τ' h => by
      rw [QuotientGroup.leftRel_apply] at h ⊢
      rw [Subgroup.mem_subgroupOf] at h ⊢
      refine ⟨(τ : G)⁻¹ * τ', by simpa using h, ?_⟩
      simp only [Subgroup.coe_mul, InvMemClass.coe_inv, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group

@[simp] theorem cosetConj_mk (σ : G) (τ : K) :
    cosetConj (L := L) σ (τ : K ⧸ L.subgroupOf K) =
      ((⟨σ * τ * σ⁻¹, τ, τ.2, rfl⟩ : K.map (MulAut.conj σ).toMonoidHom) : _ ⧸ _) :=
  rfl

theorem smul_norm (σ : G) [(L.subgroupOf K).FiniteIndex]
    [((L.map (MulAut.conj σ).toMonoidHom).subgroupOf (K.map (MulAut.conj σ).toMonoidHom)).FiniteIndex]
    (a : fixedModule A L) :
    σ • (norm A K L a : A) =
      norm A (K.map (MulAut.conj σ).toMonoidHom) (L.map (MulAut.conj σ).toMonoidHom)
        ⟨σ • (a : A), smul_mem_fixedModule a.2 σ⟩ := by
  classical
  let _ := Fintype.ofFinite (K ⧸ L.subgroupOf K)
  let _ := Fintype.ofFinite (K.map (MulAut.conj σ).toMonoidHom ⧸
    (L.map (MulAut.conj σ).toMonoidHom).subgroupOf (K.map (MulAut.conj σ).toMonoidHom))
  rw [coe_norm, coe_norm, finprod_eq_prod_of_fintype, finprod_eq_prod_of_fintype, Finset.smul_prod']
  refine Finset.prod_bij (fun t _ => cosetConj σ t) (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
  · intro t _ t' _ h
    induction t using QuotientGroup.induction_on with
    | H τ =>
    induction t' using QuotientGroup.induction_on with
    | H τ' =>
      rw [cosetConj_mk, cosetConj_mk, QuotientGroup.eq, Subgroup.mem_subgroupOf] at h
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      obtain ⟨x, hx, hx'⟩ := h
      have : x = (τ : G)⁻¹ * τ' := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subgroup.coe_mul,
          InvMemClass.coe_inv, mul_inv_rev, inv_inv] at hx'
        have := congrArg (fun y => σ⁻¹ * y * σ) hx'
        simpa [mul_assoc] using this
      simpa [this] using hx
  · intro q _
    induction q using QuotientGroup.induction_on with
    | H ρ =>
      obtain ⟨κ, hκ, hκρ⟩ := Subgroup.mem_map.1 ρ.2
      refine ⟨((⟨κ, hκ⟩ : K) : K ⧸ L.subgroupOf K), Finset.mem_univ _, ?_⟩
      rw [cosetConj_mk]
      congr 1
      ext
      simpa using hκρ
  · intro t _
    induction t using QuotientGroup.induction_on with
    | H τ =>
      rw [cosetConj_mk, cosetSMul_mk, cosetSMul_mk, smul_smul, smul_smul]
      simp

end Conjugation

end Sec_ALR_UniqueQuotientSubgroupOfSelf

section Sec_ALR_NormFormula

variable {G : Type*} [Group G] {A : Type*} [CommGroup A] [MulDistribMulAction G A]

theorem coe_norm_of_le {K L : Subgroup G} (hKL : K ≤ L) [(L.subgroupOf K).FiniteIndex]
    (a : fixedModule A L) : (norm A K L a : A) = a := by
  have : Unique (K ⧸ L.subgroupOf K) :=
    { default := ((1 : K) : K ⧸ L.subgroupOf K)
      uniq := fun q => by
        induction q using QuotientGroup.induction_on with
        | H σ =>
          rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
          exact hKL (by simp) }
  rw [coe_norm, finprod_eq_single _ ((1 : K) : K ⧸ L.subgroupOf K)
    (fun q hq => absurd (Subsingleton.elim q _) hq), cosetSMul_mk]
  simp

theorem coe_norm_congr {K K' L L' : Subgroup G} (hK : K = K') (hL : L = L')
    [(L.subgroupOf K).FiniteIndex] [(L'.subgroupOf K').FiniteIndex] (a : fixedModule A L) :
    (norm A K L a : A) = norm A K' L' ⟨a, hL ▸ a.2⟩ := by
  subst hK
  subst hL
  rfl

theorem smul_norm_of_map_eq {K L : Subgroup G} (g : G) (hK : K.map (MulAut.conj g).toMonoidHom = K)
    (hL : L.map (MulAut.conj g).toMonoidHom = L) [(L.subgroupOf K).FiniteIndex]
    (a : fixedModule A L) :
    g • (norm A K L a : A) = norm A K L ⟨g • (a : A), by
      have := smul_mem_fixedModule a.2 g
      rwa [hL] at this⟩ := by
  have : ((L.map (MulAut.conj g).toMonoidHom).subgroupOf
      (K.map (MulAut.conj g).toMonoidHom)).FiniteIndex := by
    rw [hK, hL]
    infer_instance
  rw [smul_norm g a, coe_norm_congr hK hL]

theorem coe_norm_eq_of_mul_eq {K S Q J : Subgroup G} (hQK : Q ≤ K)
    (hmul : ∀ k ∈ K, ∃ q ∈ Q, q⁻¹ * k ∈ S) (hJ : ∀ q ∈ Q, q ∈ S ↔ q ∈ J)
    [(S.subgroupOf K).FiniteIndex] [(J.subgroupOf Q).FiniteIndex] (a : fixedModule A S)
    (ha : (a : A) ∈ fixedModule A J) :
    (norm A K S a : A) = norm A Q J ⟨a, ha⟩ := by
  let f : Q ⧸ J.subgroupOf Q → K ⧸ S.subgroupOf K :=
    Quotient.map' (fun q : Q => (⟨q, hQK q.2⟩ : K)) fun q q' h => by
      rw [QuotientGroup.leftRel_apply, Subgroup.mem_subgroupOf] at h ⊢
      have hq : ((q⁻¹ * q' : Q) : G) ∈ Q := (q⁻¹ * q').2
      simpa using (hJ _ hq).2 h
  have hf : Function.Bijective f := by
    constructor
    · intro x y hxy
      induction x using QuotientGroup.induction_on with
      | H q =>
      induction y using QuotientGroup.induction_on with
      | H q' =>
        have h' : ((⟨q, hQK q.2⟩ : K) : K ⧸ S.subgroupOf K) = ((⟨q', hQK q'.2⟩ : K) : K ⧸ _) := hxy
        rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at h'
        rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
        have hq : ((q⁻¹ * q' : Q) : G) ∈ Q := (q⁻¹ * q').2
        exact (hJ _ hq).1 (by simpa using h')
    · intro y
      induction y using QuotientGroup.induction_on with
      | H k =>
        obtain ⟨q, hq, hqk⟩ := hmul k k.2
        refine ⟨((⟨q, hq⟩ : Q) : Q ⧸ J.subgroupOf Q), ?_⟩
        show ((⟨q, hQK hq⟩ : K) : K ⧸ S.subgroupOf K) = _
        rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
        simpa using hqk
  rw [coe_norm, coe_norm, ← finprod_comp_equiv (Equiv.ofBijective f hf)]
  congr 1
  funext x
  induction x using QuotientGroup.induction_on with
  | H q => rfl

end Sec_ALR_NormFormula

section Sec_ALR_ExistsEqNsmulOfProjEqZero

namespace ProfiniteInteger

def multiples (n : ℕ) : AddSubgroup ℤ̂ :=
  (AddMonoidHom.mulLeft (n : ℤ̂)).range

theorem mem_multiples {n : ℕ} {x : ℤ̂} : x ∈ multiples n ↔ ∃ y : ℤ̂, x = n • y := by
  simp only [multiples, AddMonoidHom.mem_range, AddMonoidHom.coe_mulLeft, nsmul_eq_mul]
  exact ⟨fun ⟨y, hy⟩ => ⟨y, hy.symm⟩, fun ⟨y, hy⟩ => ⟨y, hy.symm⟩⟩

theorem proj_eq_val_cast {n k : ℕ+} (h : (n : ℕ) ∣ k) (x : ℤ̂) :
    proj n x = ((proj k x).val : ZMod n) := by
  rw [← castHom_proj h x, ZMod.castHom_apply, ZMod.cast_eq_val]

theorem proj_surjective (n : ℕ+) : Function.Surjective (proj n) := fun z =>
  ⟨((z.val : ℕ) : ℤ̂), by rw [map_natCast, ZMod.natCast_zmod_val]⟩

theorem exists_eq_nsmul_of_proj_eq_zero {n : ℕ+} {x : ℤ̂} (hx : proj n x = 0) :
    ∃ y : ℤ̂, x = (n : ℕ) • y := by

  let v : ℕ+ → ℕ := fun m => (proj (n * m) x).val
  have hdvd : ∀ m : ℕ+, (n : ℕ) ∣ v m := by
    intro m
    have h := proj_eq_val_cast (n := n) (k := n * m) (by simp) x
    rw [hx, eq_comm, ZMod.natCast_eq_zero_iff] at h
    exact h
  have hmod : ∀ m k : ℕ+, (m : ℕ) ∣ (k : ℕ) → v k ≡ v m [MOD (n : ℕ) * m] := by
    intro m k hmk
    have h := proj_eq_val_cast (n := n * m) (k := n * k) (by simpa using Nat.mul_dvd_mul_left _ hmk) x
    have h2 : ((v m : ℕ) : ZMod ((n * m : ℕ+) : ℕ)) = proj (n * m) x := ZMod.natCast_zmod_val _
    rw [← h2, ZMod.natCast_eq_natCast_iff, PNat.mul_coe] at h
    exact h.symm
  let yf : ∀ m : ℕ+, ZMod m := fun m => ((v m / n : ℕ) : ZMod m)
  have hy : yf ∈ profiniteIntegers := by
    rw [mem_profiniteIntegers]
    intro m k hmk
    simp only [yf, map_natCast]
    rw [ZMod.natCast_eq_natCast_iff]
    have h := hmod m k hmk
    obtain ⟨a, ha⟩ := hdvd k
    obtain ⟨b, hb⟩ := hdvd m
    rw [ha, hb] at h ⊢
    rw [Nat.mul_div_cancel_left _ n.pos, Nat.mul_div_cancel_left _ n.pos]
    exact Nat.ModEq.mul_left_cancel' n.ne_zero h
  refine ⟨⟨yf, hy⟩, ?_⟩
  ext m
  rw [map_nsmul, nsmul_eq_mul]
  change proj m x = (n : ZMod m) * ((v m / n : ℕ) : ZMod m)
  rw [← Nat.cast_mul, Nat.mul_div_cancel' (hdvd m)]
  exact proj_eq_val_cast (n := m) (k := n * m) (by simp) x

theorem proj_eq_zero_iff {n : ℕ+} {x : ℤ̂} : proj n x = 0 ↔ x ∈ multiples n := by
  rw [mem_multiples]
  refine ⟨exists_eq_nsmul_of_proj_eq_zero, ?_⟩
  rintro ⟨y, rfl⟩
  rw [map_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul]

theorem ker_proj (n : ℕ+) : (proj n).toAddMonoidHom.ker = multiples n := by
  ext x
  exact proj_eq_zero_iff

theorem eq_zero_of_nsmul_eq_zero {n : ℕ} (hn : n ≠ 0) {x : ℤ̂} (h : n • x = 0) : x = 0 := by
  obtain ⟨N, rfl⟩ : ∃ N : ℕ+, (N : ℕ) = n := ⟨⟨n, Nat.pos_of_ne_zero hn⟩, rfl⟩
  ext m
  rw [map_zero, proj_eq_val_cast (n := m) (k := N * m) (by simp) x, ZMod.natCast_eq_zero_iff]
  have h' := congrArg (proj (N * m)) h
  rw [map_nsmul, map_zero, nsmul_eq_mul] at h'
  have h'' : (((N : ℕ) * (proj (N * m) x).val : ℕ) : ZMod ((N * m : ℕ+) : ℕ)) = 0 := by
    rw [Nat.cast_mul, ZMod.natCast_zmod_val]
    exact h'
  rw [ZMod.natCast_eq_zero_iff] at h''
  have h3 : (N : ℕ) * m ∣ (N : ℕ) * (proj (N * m) x).val := by
    rw [← PNat.mul_coe]
    exact h''
  exact Nat.dvd_of_mul_dvd_mul_left N.pos h3

instance : IsAddTorsionFree ℤ̂ where
  nsmul_right_injective n hn x y h := by
    rw [← sub_eq_zero]
    apply eq_zero_of_nsmul_eq_zero hn
    simp only at h
    rw [nsmul_sub, h, sub_self]

theorem index_multiples (n : ℕ+) : (multiples n).index = n := by
  rw [← ker_proj, AddSubgroup.index_ker, AddMonoidHom.range_eq_top.2 (proj_surjective n)]
  simp

theorem eq_multiples_index {H : AddSubgroup ℤ̂} (hH : H.index ≠ 0) : H = multiples H.index := by
  have hle : multiples H.index ≤ H := by
    intro x hx
    obtain ⟨y, rfl⟩ := mem_multiples.1 hx
    exact H.nsmul_index_mem y
  have hidx := AddSubgroup.relIndex_mul_index hle
  have hm := index_multiples ⟨H.index, Nat.pos_of_ne_zero hH⟩
  simp only [PNat.mk_coe] at hm
  rw [hm] at hidx
  have h1 : (multiples H.index).relIndex H = 1 := (Nat.mul_eq_right hH).1 hidx
  exact le_antisymm (AddSubgroup.relIndex_eq_one.1 h1) hle

theorem intCast_mem_multiples_iff {n : ℕ} (hn : 0 < n) {k : ℤ} :
    (k : ℤ̂) ∈ multiples n ↔ (n : ℤ) ∣ k := by
  rw [mem_multiples]
  refine ⟨fun ⟨w, hw⟩ => dvd_of_intCast_eq_nsmul hn hw, ?_⟩
  rintro ⟨c, rfl⟩
  exact ⟨(c : ℤ̂), by push_cast; rw [nsmul_eq_mul]⟩

end ProfiniteInteger

end Sec_ALR_ExistsEqNsmulOfProjEqZero

section Sec_ALR_Valuation

section Degrees

variable {G : Type*} [Group G]

theorem relIndex_sup_of_le_normalizer {H N : Subgroup G} (hLE : H ≤ Subgroup.normalizer (N : Set G)) :
    H.relIndex (H ⊔ N) = H.relIndex N :=
  PowerSubgroups.relIndex_sup_of_le_normalizer hLE

variable (d : G →* Multiplicative ℤ̂)

noncomputable def relInertiaDegree (K L : Subgroup G) : ℕ :=
  (L.map d).relIndex (K.map d)

noncomputable def relRamificationIndex (K L : Subgroup G) : ℕ :=
  L.relIndex (d.ker ⊓ K)

variable {d}

theorem relRamificationIndex_top (K : Subgroup G) :
    relRamificationIndex d ⊤ K = ramificationIndex d K := by
  rw [relRamificationIndex, ramificationIndex, inf_top_eq]

theorem relInertiaDegree_top (hd : Function.Surjective d) (K : Subgroup G) :
    relInertiaDegree d ⊤ K = inertiaDegree d K := by
  rw [relInertiaDegree, inertiaDegree, ← MonoidHom.range_eq_map,
    MonoidHom.range_eq_top_of_surjective d hd, Subgroup.relIndex_top_right]

theorem relInertiaDegree_mul {K L M : Subgroup G} (hML : M ≤ L) (hLK : L ≤ K) :
    relInertiaDegree d L M * relInertiaDegree d K L = relInertiaDegree d K M :=
  Subgroup.relIndex_mul_relIndex _ _ _ (Subgroup.map_mono hML) (Subgroup.map_mono hLK)

theorem relRamificationIndex_mul {K L M : Subgroup G} (hML : M ≤ L) (hLK : L ≤ K) :
    relRamificationIndex d L M * relRamificationIndex d K L = relRamificationIndex d K M := by
  unfold relRamificationIndex
  have h := Subgroup.relIndex_inf_mul_relIndex M L (d.ker ⊓ K)
  have h1 : L ⊓ (d.ker ⊓ K) = d.ker ⊓ L := by
    rw [inf_comm d.ker K, ← inf_assoc, inf_eq_left.2 hLK, inf_comm]
  rw [h1, inf_eq_left.2 hML] at h
  exact h

theorem inertiaDegree_eq_mul (hd : Function.Surjective d) {K L : Subgroup G} (hLK : L ≤ K) :
    inertiaDegree d L = relInertiaDegree d K L * inertiaDegree d K := by
  rw [← relInertiaDegree_top hd, ← relInertiaDegree_top hd, relInertiaDegree_mul hLK le_top]

theorem ramificationIndex_eq_mul {K L : Subgroup G} (hLK : L ≤ K) :
    ramificationIndex d L = relRamificationIndex d K L * ramificationIndex d K := by
  rw [← relRamificationIndex_top, ← relRamificationIndex_top, relRamificationIndex_mul hLK le_top]

theorem relIndex_eq_mul {K L : Subgroup G} (hLK : L ≤ K) :
    L.relIndex K = relRamificationIndex d K L * relInertiaDegree d K L := by
  have hP : L ⊔ (d.ker ⊓ K) ≤ K := sup_le hLK inf_le_right
  rw [← Subgroup.relIndex_mul_relIndex L (L ⊔ (d.ker ⊓ K)) K le_sup_left hP]
  congr 1
  · rw [relRamificationIndex]
    refine relIndex_sup_of_le_normalizer ?_
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have hgK : g ∈ K := hLK hg
    simp only [Subgroup.mem_inf, MonoidHom.mem_ker, map_mul, map_inv]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨?_, K.mul_mem (K.mul_mem hgK h2) (K.inv_mem hgK)⟩
      rw [h1, mul_one, mul_inv_cancel]
    · rintro ⟨h1, h2⟩
      refine ⟨?_, ?_⟩
      · have : d x = (d g)⁻¹ * (d g * d x * (d g)⁻¹) * d g := by group
        rw [this, h1]; group
      · have : x = g⁻¹ * (g * x * g⁻¹) * g := by group
        rw [this]
        exact K.mul_mem (K.mul_mem (K.inv_mem hgK) h2) hgK
  · rw [relInertiaDegree, ← Subgroup.relIndex_comap, Subgroup.comap_map_eq,
      ← Subgroup.inf_relIndex_right (L ⊔ d.ker) K]
    congr 1
    refine le_antisymm (le_inf (sup_le_sup_left inf_le_left L) hP) ?_
    intro x hx
    obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.1 hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 hx1
    have hzK : z ∈ K := by
      have := K.mul_mem (K.inv_mem (hLK hy)) hx2
      simpa using this
    exact Subgroup.mul_mem_sup hy (Subgroup.mem_inf.2 ⟨hz, hzK⟩)

theorem index_eq_mul (hd : Function.Surjective d) (K : Subgroup G) :
    K.index = ramificationIndex d K * inertiaDegree d K := by
  rw [← relRamificationIndex_top, ← relInertiaDegree_top hd, ← relIndex_eq_mul le_top,
    Subgroup.relIndex_top_right]

end Degrees

section PowProfinite

namespace ProfiniteInteger

theorem pow_left_injective {n : ℕ} (hn : n ≠ 0) :
    Function.Injective (fun x : Multiplicative ℤ̂ => x ^ n) := by
  intro x y h
  apply Multiplicative.toAdd.injective
  have h' : n • Multiplicative.toAdd x = n • Multiplicative.toAdd y := by
    rw [← toAdd_pow, ← toAdd_pow]
    exact congrArg Multiplicative.toAdd h
  exact nsmul_right_injective hn h'

theorem pow_left_inj {n : ℕ} (hn : n ≠ 0) {x y : Multiplicative ℤ̂} : x ^ n = y ^ n ↔ x = y :=
  (pow_left_injective hn).eq_iff

theorem mem_of_index_ne_zero {H : Subgroup (Multiplicative ℤ̂)} (hH : H.index ≠ 0)
    {x : Multiplicative ℤ̂} : x ∈ H ↔ ∃ y, y ^ H.index = x := by
  have hi : (Subgroup.toAddSubgroup' H).index = H.index := rfl
  have h := eq_multiples_index (H := Subgroup.toAddSubgroup' H) (by rwa [hi])
  rw [hi] at h
  have hx : x ∈ H ↔ Multiplicative.toAdd x ∈ Subgroup.toAddSubgroup' H := Iff.rfl
  rw [hx, h, mem_multiples]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨Multiplicative.ofAdd y, Multiplicative.toAdd.injective ?_⟩
    rw [toAdd_pow, toAdd_ofAdd, hy]
  · rintro ⟨y, rfl⟩
    exact ⟨Multiplicative.toAdd y, by rw [toAdd_pow]⟩

theorem index_range_powMonoidHom {n : ℕ} (hn : n ≠ 0) :
    (powMonoidHom n : Multiplicative ℤ̂ →* Multiplicative ℤ̂).range.index = n := by
  have h : Subgroup.toAddSubgroup' (powMonoidHom n : Multiplicative ℤ̂ →* Multiplicative ℤ̂).range =
      multiples n := by
    ext x
    rw [mem_multiples]
    change Multiplicative.ofAdd x ∈ (powMonoidHom n).range ↔ _
    constructor
    · rintro ⟨y, hy⟩
      refine ⟨Multiplicative.toAdd y, ?_⟩
      rw [← toAdd_pow, ← powMonoidHom_apply, hy, toAdd_ofAdd]
    · rintro ⟨y, rfl⟩
      exact ⟨Multiplicative.ofAdd y, by rw [powMonoidHom_apply, ← ofAdd_nsmul]⟩
  have hi := index_multiples ⟨n, Nat.pos_of_ne_zero hn⟩
  simp only [PNat.mk_coe] at hi
  rw [← h] at hi
  exact hi

end ProfiniteInteger

end PowProfinite

namespace ClassFieldData

open ProfiniteInteger

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  {A : Type*} [CommGroup A] [MulDistribMulAction G A] (D : ClassFieldData G A)

theorem inertiaDegree_ne_zero (K : OpenSubgroup G) : inertiaDegree D.deg K ≠ 0 :=
  fun h => Subgroup.FiniteIndex.index_ne_zero (H := (K : Subgroup G))
    (Nat.eq_zero_of_zero_dvd (h ▸ Subgroup.index_map_dvd _ D.surjective_deg))

theorem mem_map_deg_iff (K : OpenSubgroup G) {x : Multiplicative ℤ̂} :
    x ∈ (K : Subgroup G).map D.deg ↔ ∃ y, y ^ inertiaDegree D.deg K = x :=
  mem_of_index_ne_zero (D.inertiaDegree_ne_zero K)

theorem exists_pow_eq_deg (K : OpenSubgroup G) (σ : (K : Subgroup G)) :
    ∃ x, x ^ inertiaDegree D.deg K = D.deg σ :=
  (D.mem_map_deg_iff K).1 ⟨σ, σ.2, rfl⟩

noncomputable def relDeg (K : OpenSubgroup G) : (K : Subgroup G) →* Multiplicative ℤ̂ where
  toFun σ := (D.exists_pow_eq_deg K σ).choose
  map_one' := by
    refine (ProfiniteInteger.pow_left_inj (D.inertiaDegree_ne_zero K)).1 ?_
    rw [(D.exists_pow_eq_deg K 1).choose_spec, one_pow, OneMemClass.coe_one, map_one]
  map_mul' σ τ := by
    refine (ProfiniteInteger.pow_left_inj (D.inertiaDegree_ne_zero K)).1 ?_
    rw [(D.exists_pow_eq_deg K (σ * τ)).choose_spec, mul_pow, (D.exists_pow_eq_deg K σ).choose_spec,
      (D.exists_pow_eq_deg K τ).choose_spec, Subgroup.coe_mul, map_mul]

theorem relDeg_pow (K : OpenSubgroup G) (σ : (K : Subgroup G)) :
    D.relDeg K σ ^ inertiaDegree D.deg K = D.deg σ :=
  (D.exists_pow_eq_deg K σ).choose_spec

theorem relDeg_eq_iff (K : OpenSubgroup G) (σ : (K : Subgroup G)) (x : Multiplicative ℤ̂) :
    D.relDeg K σ = x ↔ D.deg σ = x ^ inertiaDegree D.deg K := by
  rw [← ProfiniteInteger.pow_left_inj (D.inertiaDegree_ne_zero K), relDeg_pow]

theorem relDeg_surjective (K : OpenSubgroup G) : Function.Surjective (D.relDeg K) := by
  intro x
  obtain ⟨σ, hσ, hσx⟩ := (D.mem_map_deg_iff K).2 ⟨x, rfl⟩
  exact ⟨⟨σ, hσ⟩, (D.relDeg_eq_iff K _ x).2 hσx⟩

theorem continuous_relDeg (K : OpenSubgroup G) : Continuous (D.relDeg K) := by
  have hp : Topology.IsClosedEmbedding (fun x : Multiplicative ℤ̂ => x ^ inertiaDegree D.deg K) :=
    (continuous_pow _).isClosedEmbedding (ProfiniteInteger.pow_left_injective (D.inertiaDegree_ne_zero K))
  rw [hp.isEmbedding.continuous_iff]
  have h : ((fun x : Multiplicative ℤ̂ => x ^ inertiaDegree D.deg K) ∘ D.relDeg K) =
      D.deg ∘ Subtype.val := funext (D.relDeg_pow K)
  rw [h]
  exact D.continuous_deg.comp continuous_subtype_val

theorem mem_map_relDeg_iff {K L : OpenSubgroup G} (hLK : L ≤ K) {x : Multiplicative ℤ̂} :
    x ∈ ((L : Subgroup G).subgroupOf K).map (D.relDeg K) ↔
      ∃ y, y ^ relInertiaDegree D.deg K L = x := by
  have hf := inertiaDegree_eq_mul D.surjective_deg (K := (K : Subgroup G)) (L := (L : Subgroup G)) hLK
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    obtain ⟨y, hy⟩ := D.exists_pow_eq_deg L ⟨σ, hσ⟩
    refine ⟨y, ?_⟩
    rw [eq_comm, relDeg_eq_iff, ← pow_mul, ← hf]
    exact hy.symm
  · rintro ⟨y, rfl⟩
    obtain ⟨σ, hσ, hσy⟩ := (D.mem_map_deg_iff L).2 ⟨y, rfl⟩
    refine ⟨⟨σ, hLK hσ⟩, hσ, ?_⟩
    rw [relDeg_eq_iff, ← pow_mul, ← hf]
    exact hσy

theorem inertiaDegree_relDeg {K L : OpenSubgroup G} (hLK : L ≤ K) :
    inertiaDegree (D.relDeg K) ((L : Subgroup G).subgroupOf K) = relInertiaDegree D.deg K L := by
  have hf := inertiaDegree_eq_mul D.surjective_deg (K := (K : Subgroup G)) (L := (L : Subgroup G)) hLK
  have hne : relInertiaDegree D.deg K L ≠ 0 := fun h => D.inertiaDegree_ne_zero L (by rw [hf, h, zero_mul])
  have h : ((L : Subgroup G).subgroupOf K).map (D.relDeg K) =
      (powMonoidHom (relInertiaDegree D.deg K L) : Multiplicative ℤ̂ →* Multiplicative ℤ̂).range := by
    ext x
    rw [D.mem_map_relDeg_iff hLK]
    rfl
  rw [inertiaDegree, h, index_range_powMonoidHom hne]

theorem relInertiaDegree_ne_zero {K L : OpenSubgroup G} (hLK : L ≤ K) :
    relInertiaDegree D.deg K L ≠ 0 := fun h =>
  D.inertiaDegree_ne_zero L (by
    rw [inertiaDegree_eq_mul D.surjective_deg (K := (K : Subgroup G)) (L := (L : Subgroup G)) hLK, h,
      zero_mul])

theorem exists_valuation (K : OpenSubgroup G) (a : fixedModule A (K : Subgroup G)) :
    ∃ z ∈ D.val.range, z ^ inertiaDegree D.deg K = D.val (norm A ⊤ (K : Subgroup G) a) := by
  have h : D.val (norm A ⊤ (K : Subgroup G) a) ∈ (D.val.comp (norm A (⊤ : Subgroup G) (K : Subgroup G))).range :=
    ⟨a, rfl⟩
  rw [D.range_val_comp_norm K] at h
  obtain ⟨z, hz, hza⟩ := h
  exact ⟨z, hz, hza⟩

noncomputable def valuation (K : OpenSubgroup G) : fixedModule A (K : Subgroup G) →* Multiplicative ℤ̂ where
  toFun a := (D.exists_valuation K a).choose
  map_one' := by
    refine (ProfiniteInteger.pow_left_inj (D.inertiaDegree_ne_zero K)).1 ?_
    rw [(D.exists_valuation K 1).choose_spec.2, one_pow, map_one, map_one]
  map_mul' a b := by
    refine (ProfiniteInteger.pow_left_inj (D.inertiaDegree_ne_zero K)).1 ?_
    rw [(D.exists_valuation K (a * b)).choose_spec.2, mul_pow, (D.exists_valuation K a).choose_spec.2,
      (D.exists_valuation K b).choose_spec.2, map_mul, map_mul]

theorem valuation_pow (K : OpenSubgroup G) (a : fixedModule A (K : Subgroup G)) :
    D.valuation K a ^ inertiaDegree D.deg K = D.val (norm A ⊤ (K : Subgroup G) a) :=
  (D.exists_valuation K a).choose_spec.2

theorem valuation_eq_iff (K : OpenSubgroup G) (a : fixedModule A (K : Subgroup G)) (z : Multiplicative ℤ̂) :
    D.valuation K a = z ↔ D.val (norm A ⊤ (K : Subgroup G) a) = z ^ inertiaDegree D.deg K := by
  rw [← ProfiniteInteger.pow_left_inj (D.inertiaDegree_ne_zero K), valuation_pow]

theorem range_valuation (K : OpenSubgroup G) : (D.valuation K).range = D.val.range := by
  ext z
  constructor
  · rintro ⟨a, rfl⟩
    exact (D.exists_valuation K a).choose_spec.1
  · intro hz
    have h : z ^ inertiaDegree D.deg K ∈
        (D.val.comp (norm A (⊤ : Subgroup G) (K : Subgroup G))).range := by
      rw [D.range_val_comp_norm K]
      exact ⟨z, hz, rfl⟩
    obtain ⟨a, ha⟩ := h
    exact ⟨a, (D.valuation_eq_iff K a z).2 ha⟩

noncomputable def units (K : OpenSubgroup G) : Subgroup (fixedModule A (K : Subgroup G)) :=
  (D.valuation K).ker

theorem mem_units {K : OpenSubgroup G} {a : fixedModule A (K : Subgroup G)} : a ∈ D.units K ↔ D.valuation K a = 1 :=
  Iff.rfl

theorem valuation_norm {K L : OpenSubgroup G} (hLK : L ≤ K) (a : fixedModule A (L : Subgroup G)) :
    D.valuation K (norm A (K : Subgroup G) (L : Subgroup G) a) = D.valuation L a ^ relInertiaDegree D.deg K L := by
  rw [valuation_eq_iff, norm_norm (M := (L : Subgroup G)) (L := (K : Subgroup G)) hLK le_top, ← valuation_pow,
    ← pow_mul, inertiaDegree_eq_mul D.surjective_deg (K := (K : Subgroup G)) (L := (L : Subgroup G)) hLK]

theorem range_valuation_comp_norm {K L : OpenSubgroup G} (hLK : L ≤ K) :
    ((D.valuation K).comp (norm A (K : Subgroup G) (L : Subgroup G))).range =
      (D.valuation K).range.map (powMonoidHom (relInertiaDegree D.deg K L)) := by
  ext z
  constructor
  · rintro ⟨a, rfl⟩
    refine ⟨D.valuation L a, ?_, (D.valuation_norm hLK a).symm⟩
    rw [range_valuation, ← D.range_valuation L]
    exact ⟨a, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    rw [range_valuation, ← D.range_valuation L] at hy
    obtain ⟨a, rfl⟩ := hy
    exact ⟨a, D.valuation_norm hLK a⟩

theorem valuation_of_mem {K L : OpenSubgroup G} (hLK : L ≤ K) {a : A} (ha : a ∈ fixedModule A (K : Subgroup G)) :
    D.valuation L ⟨a, fixedModule_anti hLK ha⟩ =
      D.valuation K ⟨a, ha⟩ ^ relRamificationIndex D.deg K L := by
  refine (ProfiniteInteger.pow_left_inj (D.relInertiaDegree_ne_zero hLK)).1 ?_
  rw [← valuation_norm D hLK, ← pow_mul, ← relIndex_eq_mul hLK]
  have hn : norm A (K : Subgroup G) (L : Subgroup G) ⟨a, fixedModule_anti hLK ha⟩ =
      ⟨a, ha⟩ ^ (L : Subgroup G).relIndex K :=
    Subtype.ext (by rw [coe_norm_of_mem hLK ha]; rfl)
  rw [hn, map_pow]

end ClassFieldData

end Sec_ALR_Valuation

section Sec_ALR_Frobenius

open ProfiniteInteger

section Density

theorem isClosed_multiples (N : ℕ) : IsClosed (multiples N : Set ℤ̂) := by
  have : (multiples N : Set ℤ̂) = Set.range (fun y : ℤ̂ => (N : ℤ̂) * y) := by
    ext x
    simp [multiples]
  rw [this]
  exact (isCompact_range (continuous_const.mul continuous_id)).isClosed

instance finiteIndex_multiples (N : ℕ+) : (multiples N).FiniteIndex :=
  ⟨by rw [index_multiples]; exact N.ne_zero⟩

theorem isOpen_multiples (N : ℕ+) : IsOpen (multiples N : Set ℤ̂) :=
  AddSubgroup.isOpen_of_isClosed_of_finiteIndex _ (isClosed_multiples N)

theorem denseRange_intCast : DenseRange (Int.cast : ℤ → ℤ̂) := by
  intro x
  rw [mem_closure_iff]
  intro U hU hxU
  obtain ⟨W, hW⟩ := ProfiniteGrp.exist_openNormalAddSubgroup_sub_open_nhds_of_zero
    (hU.preimage (continuous_const_add x)) (by simpa using hxU)
  have : Finite (ℤ̂ ⧸ W.toAddSubgroup) :=
    AddSubgroup.quotient_finite_of_isOpen W.toAddSubgroup W.isOpen'
  have hfi : W.toAddSubgroup.FiniteIndex := AddSubgroup.finiteIndex_of_finite_quotient
  have hm : W.toAddSubgroup.index ≠ 0 := hfi.index_ne_zero
  have hWm := eq_multiples_index hm
  set m : ℕ+ := ⟨W.toAddSubgroup.index, Nat.pos_of_ne_zero hm⟩ with hmdef
  refine ⟨((((proj m x).val : ℕ) : ℤ) : ℤ̂), ?_, Set.mem_range_self _⟩
  have hk : ((((proj m x).val : ℕ) : ℤ) : ℤ̂) - x ∈ W.toAddSubgroup := by
    rw [hWm]
    have := (proj_eq_zero_iff (n := m) (x := ((((proj m x).val : ℕ) : ℤ) : ℤ̂) - x)).1 (by
      rw [map_sub, map_intCast, Int.cast_natCast, ZMod.natCast_zmod_val, sub_self])
    simpa [hmdef] using this
  have := hW hk
  simpa using this

end Density

section FixedField

variable {G : Type*} [Group G] {d : G →* Multiplicative ℤ̂} {L : Subgroup G} {σ : G}

theorem mem_zpowers_sup_iff (hσ : σ ∈ Subgroup.normalizer ((L ⊓ d.ker : Subgroup G) : Set G))
    {h : G} : h ∈ Subgroup.zpowers σ ⊔ (L ⊓ d.ker) ↔ ∃ k : ℤ, ∃ j ∈ L ⊓ d.ker, h = σ ^ k * j := by
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _
    (Subgroup.zpowers_le.2 hσ), Set.mem_mul]
  constructor
  · rintro ⟨a, ha, j, hj, rfl⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    exact ⟨k, j, hj, rfl⟩
  · rintro ⟨k, j, hj, rfl⟩
    exact ⟨σ ^ k, Subgroup.zpow_mem_zpowers σ k, j, hj, rfl⟩

theorem deg_zpow_mul {N : ℕ} (hdσ : d σ = Multiplicative.ofAdd (N : ℤ̂)) (k : ℤ) {j : G}
    (hj : j ∈ L ⊓ d.ker) :
    Multiplicative.toAdd (d (σ ^ k * j)) = ((k * N : ℤ) : ℤ̂) := by
  rw [map_mul, map_zpow, hdσ, (MonoidHom.mem_ker).1 hj.2, mul_one, ← ofAdd_zsmul, toAdd_ofAdd,
    zsmul_eq_mul]
  push_cast
  ring

variable [TopologicalSpace G] [IsTopologicalGroup G]

variable (d L σ) in

def frobeniusClosure : Subgroup G :=
  (Subgroup.zpowers σ ⊔ (L ⊓ d.ker)).topologicalClosure

theorem le_frobeniusClosure : L ⊓ d.ker ≤ frobeniusClosure d L σ :=
  le_sup_right.trans (Subgroup.le_topologicalClosure _)

theorem mem_frobeniusClosure_self : σ ∈ frobeniusClosure d L σ :=
  Subgroup.le_topologicalClosure _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers σ))

theorem isClosed_frobeniusClosure : IsClosed (frobeniusClosure d L σ : Set G) :=
  Subgroup.isClosed_topologicalClosure _

theorem frobeniusClosure_le {K : Subgroup G} (hK : IsClosed (K : Set G)) (hσK : σ ∈ K)
    (hLK : L ⊓ d.ker ≤ K) : frobeniusClosure d L σ ≤ K :=
  Subgroup.topologicalClosure_minimal _ (sup_le (Subgroup.zpowers_le.2 hσK) hLK) hK

theorem mem_fixedModule_frobeniusClosure {A : Type*} [CommGroup A] [MulDistribMulAction G A]
    [IsDiscreteModule G A] {a : A} :
    a ∈ fixedModule A (frobeniusClosure d L σ) ↔ a ∈ fixedModule A (L ⊓ d.ker) ∧ σ • a = a := by
  constructor
  · intro ha
    exact ⟨fixedModule_anti le_frobeniusClosure ha, ha σ mem_frobeniusClosure_self⟩
  · rintro ⟨ha, hσa⟩
    have hS : IsClosed (MulAction.stabilizer G a : Set G) :=
      Subgroup.isClosed_of_isOpen _ (IsDiscreteModule.isOpen_stabilizer a)
    have hle : frobeniusClosure d L σ ≤ MulAction.stabilizer G a :=
      frobeniusClosure_le hS (MulAction.mem_stabilizer_iff.2 hσa) fun g hg => ha g hg
    exact fun g hg => MulAction.mem_stabilizer_iff.1 (hle hg)

variable [CompactSpace G] [TotallyDisconnectedSpace G]

theorem frobeniusClosure_inf_ker (hd : Continuous d) (hL : IsOpen (L : Set G))
    (hσ : σ ∈ Subgroup.normalizer ((L ⊓ d.ker : Subgroup G) : Set G)) {N : ℕ} (hN : N ≠ 0)
    (hdσ : d σ = Multiplicative.ofAdd (N : ℤ̂)) :
    frobeniusClosure d L σ ⊓ d.ker = L ⊓ d.ker := by
  refine le_antisymm ?_ (le_inf le_frobeniusClosure inf_le_right)
  intro x hx0
  obtain ⟨hx, hxk⟩ := Subgroup.mem_inf.1 hx0
  rw [MonoidHom.mem_ker] at hxk
  obtain ⟨U0, hU0⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hL L.one_mem
  have : Finite (G ⧸ U0.toSubgroup) := Subgroup.quotient_finite_of_isOpen _ U0.isOpen'
  set t := orderOf (σ : G ⧸ U0.toSubgroup) with htdef
  have ht : 0 < t := orderOf_pos _
  set M : ℕ+ := ⟨t * N, Nat.mul_pos ht (Nat.pos_of_ne_zero hN)⟩ with hMdef
  set V : Set G := (U0 : Set G) ∩ d ⁻¹' (Multiplicative.toAdd ⁻¹' (multiples M : Set ℤ̂)) with hVdef
  have hV : IsOpen V :=
    U0.isOpen'.inter ((isOpen_multiples M).preimage (continuous_toAdd.comp hd))
  have hO : IsOpen ((fun y => x⁻¹ * y) ⁻¹' V) := hV.preimage (continuous_const.mul continuous_id)
  have hxO : x ∈ (fun y => x⁻¹ * y) ⁻¹' V := by
    simp only [Set.mem_preimage, inv_mul_cancel, hVdef, Set.mem_inter_iff, map_one, toAdd_one]
    exact ⟨U0.one_mem', (multiples M).zero_mem⟩
  have hx' : x ∈ closure ((Subgroup.zpowers σ ⊔ (L ⊓ d.ker) : Subgroup G) : Set G) := by
    rw [← Subgroup.topologicalClosure_coe]
    exact hx
  obtain ⟨h, hhO, hhH⟩ := mem_closure_iff.1 hx' _ hO hxO
  obtain ⟨k, j, hj, rfl⟩ := (mem_zpowers_sup_iff hσ).1 hhH
  obtain ⟨hU, hWm⟩ := hhO
  have hdk : Multiplicative.toAdd (d (x⁻¹ * (σ ^ k * j))) = ((k * N : ℤ) : ℤ̂) := by
    rw [map_mul, map_inv, hxk, inv_one, one_mul]
    exact deg_zpow_mul hdσ k hj
  have hdiv : ((M : ℕ) : ℤ) ∣ k * N := by
    have hmem : ((k * N : ℤ) : ℤ̂) ∈ multiples M := by
      rw [← hdk]
      exact hWm
    exact (intCast_mem_multiples_iff M.pos).1 hmem
  have htk : (t : ℤ) ∣ k := by
    have h2 : (t : ℤ) * N ∣ k * N := by simpa [hMdef] using hdiv
    exact (mul_dvd_mul_iff_right (by exact_mod_cast hN)).1 h2
  have hσk : σ ^ k ∈ U0.toSubgroup := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_zpow, ← orderOf_dvd_iff_zpow_eq_one]
    exact htk
  refine ⟨?_, (MonoidHom.mem_ker).2 hxk⟩
  have hx_eq : x = σ ^ k * j * (x⁻¹ * (σ ^ k * j))⁻¹ := by group
  rw [hx_eq]
  exact L.mul_mem (L.mul_mem (hU0 hσk) hj.1) (L.inv_mem (hU0 hU))

omit [TotallyDisconnectedSpace G] in

theorem map_frobeniusClosure (hd : Continuous d)
    (hσ : σ ∈ Subgroup.normalizer ((L ⊓ d.ker : Subgroup G) : Set G)) {N : ℕ}
    (hdσ : d σ = Multiplicative.ofAdd (N : ℤ̂)) :
    (frobeniusClosure d L σ).map d = AddSubgroup.toSubgroup (multiples N) := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    have hcl : IsClosed (d ⁻¹' (Multiplicative.toAdd ⁻¹' (multiples N : Set ℤ̂))) :=
      (isClosed_multiples N).preimage (continuous_toAdd.comp hd)
    have hsub : ((Subgroup.zpowers σ ⊔ (L ⊓ d.ker) : Subgroup G) : Set G) ⊆
        d ⁻¹' (Multiplicative.toAdd ⁻¹' (multiples N : Set ℤ̂)) := by
      intro h hh
      obtain ⟨k, j, hj, rfl⟩ := (mem_zpowers_sup_iff hσ).1 hh
      simp only [Set.mem_preimage, SetLike.mem_coe]
      rw [deg_zpow_mul hdσ k hj, mem_multiples]
      exact ⟨(k : ℤ̂), by push_cast; rw [nsmul_eq_mul]; ring⟩
    have hx' : x ∈ closure ((Subgroup.zpowers σ ⊔ (L ⊓ d.ker) : Subgroup G) : Set G) := by
      rw [← Subgroup.topologicalClosure_coe]
      exact hx
    exact closure_minimal hsub hcl hx'
  · intro y hy
    have hy' : Multiplicative.toAdd y ∈ multiples N := hy
    obtain ⟨w, hw⟩ := mem_multiples.1 hy'
    set S : Set (Multiplicative ℤ̂) := d '' (frobeniusClosure d L σ : Set G) with hSdef
    have hS : IsClosed S := (isClosed_frobeniusClosure.isCompact.image hd).isClosed
    have key : ∀ w : ℤ̂, Multiplicative.ofAdd ((N : ℤ̂) * w) ∈ S := by
      intro w
      refine denseRange_intCast.induction_on w
        (hS.preimage (continuous_ofAdd.comp (continuous_const.mul continuous_id))) fun k => ?_
      refine ⟨σ ^ k, Subgroup.zpow_mem _ mem_frobeniusClosure_self k, ?_⟩
      rw [map_zpow, hdσ, ← ofAdd_zsmul, zsmul_eq_mul, mul_comm]
    obtain ⟨x, hx, hxy⟩ := key w
    refine ⟨x, hx, ?_⟩
    rw [hxy, ← nsmul_eq_mul, ← hw]
    rfl

theorem isOpen_frobeniusClosure (hd : Continuous d) (hL : IsOpen (L : Set G))
    (hσ : σ ∈ Subgroup.normalizer ((L ⊓ d.ker : Subgroup G) : Set G)) {N : ℕ} (hN : N ≠ 0)
    (hdσ : d σ = Multiplicative.ofAdd (N : ℤ̂)) :
    IsOpen (frobeniusClosure d L σ : Set G) := by
  set S := frobeniusClosure d L σ with hSdef
  have hsup : S ⊔ d.ker = (AddSubgroup.toSubgroup (multiples N)).comap d := by
    rw [← map_frobeniusClosure hd hσ hdσ, Subgroup.comap_map_eq]
  have hsupOpen : IsOpen ((S ⊔ d.ker : Subgroup G) : Set G) := by
    rw [hsup]
    exact (isOpen_multiples ⟨N, Nat.pos_of_ne_zero hN⟩).preimage (continuous_toAdd.comp hd)
  have : Finite (G ⧸ (S ⊔ d.ker)) := Subgroup.quotient_finite_of_isOpen _ hsupOpen
  have h1 : (S ⊔ d.ker).FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have : Finite (G ⧸ L) := Subgroup.quotient_finite_of_isOpen _ hL
  have : L.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have h2 : S.relIndex (S ⊔ d.ker) ≠ 0 := by
    rw [relIndex_sup_of_le_normalizer (Subgroup.le_normalizer_of_normal),
      ← Subgroup.inf_relIndex_right, frobeniusClosure_inf_ker hd hL hσ hN hdσ,
      Subgroup.inf_relIndex_right]
    exact Subgroup.FiniteIndex.index_ne_zero
  have : S.FiniteIndex :=
    ⟨by rw [← Subgroup.relIndex_mul_index le_sup_left]; exact mul_ne_zero h2 h1.index_ne_zero⟩
  exact Subgroup.isOpen_of_isClosed_of_finiteIndex _ isClosed_frobeniusClosure

omit [TotallyDisconnectedSpace G] in

theorem inertiaDegree_frobeniusClosure (hd : Continuous d)
    (hσ : σ ∈ Subgroup.normalizer ((L ⊓ d.ker : Subgroup G) : Set G)) {N : ℕ} (hN : N ≠ 0)
    (hdσ : d σ = Multiplicative.ofAdd (N : ℤ̂)) :
    inertiaDegree d (frobeniusClosure d L σ) = N := by
  rw [inertiaDegree, map_frobeniusClosure hd hσ hdσ, AddSubgroup.index_toSubgroup]
  exact index_multiples ⟨N, Nat.pos_of_ne_zero hN⟩

end FixedField

end Sec_ALR_Frobenius

section Sec_ALR_Unramified

section Unramified

variable {G : Type*} [Group G] (d : G →* Multiplicative ℤ̂)

def IsUnramified (K L : Subgroup G) : Prop :=
  relRamificationIndex d K L = 1

variable {d}

theorem isUnramified_iff {K L : Subgroup G} : IsUnramified d K L ↔ K ⊓ d.ker ≤ L := by
  rw [IsUnramified, relRamificationIndex, Subgroup.relIndex_eq_one, inf_comm]

theorem relIndex_eq_relInertiaDegree {K L : Subgroup G} (hLK : L ≤ K) (hu : K ⊓ d.ker ≤ L) :
    L.relIndex K = relInertiaDegree d K L := by
  rw [relIndex_eq_mul (d := d) hLK, (isUnramified_iff.2 hu : relRamificationIndex d K L = 1), one_mul]

theorem mem_iff_map_mem_of_unramified {K L : Subgroup G} (hLK : L ≤ K) (hu : K ⊓ d.ker ≤ L)
    {σ : G} (hσ : σ ∈ K) : σ ∈ L ↔ d σ ∈ L.map d := by
  refine ⟨fun h => ⟨σ, h, rfl⟩, ?_⟩
  rintro ⟨τ, hτ, hτσ⟩
  have h : τ⁻¹ * σ ∈ L := hu (Subgroup.mem_inf.2 ⟨K.mul_mem (K.inv_mem (hLK hτ)) hσ,
    MonoidHom.mem_ker.2 (by rw [map_mul, map_inv, hτσ, inv_mul_cancel])⟩)
  simpa using L.mul_mem hτ h

theorem normal_of_unramified {K L : Subgroup G} (hLK : L ≤ K) (hu : K ⊓ d.ker ≤ L) :
    (L.subgroupOf K).Normal := by
  have h : L.subgroupOf K = (L.map d).comap (d.comp K.subtype) := by
    ext σ
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap, MonoidHom.comp_apply, Subgroup.coe_subtype]
    exact mem_iff_map_mem_of_unramified hLK hu σ.2
  rw [h]
  exact Subgroup.Normal.comap inferInstance _

end Unramified

namespace ClassFieldData

open ProfiniteInteger

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  {A : Type*} [CommGroup A] [MulDistribMulAction G A] (D : ClassFieldData G A)

section Frobenius

variable {K L : OpenSubgroup G}

theorem exists_pow_mul_mem_of_unramified (hLK : L ≤ K) (hu : (K : Subgroup G) ⊓ D.deg.ker ≤ L)
    {φ : (K : Subgroup G)} (hφ : D.relDeg K φ = Multiplicative.ofAdd 1) (τ : (K : Subgroup G)) :
    ∃ m : ℕ, ((φ ^ m)⁻¹ * τ : G) ∈ (L : Subgroup G) := by
  set n : ℕ+ := ⟨relInertiaDegree D.deg K L, Nat.pos_of_ne_zero (D.relInertiaDegree_ne_zero hLK)⟩
  set x : ℤ̂ := Multiplicative.toAdd (D.relDeg K τ)
  set m : ℕ := (proj n x).val
  have hx : x - (m : ℤ̂) ∈ multiples n := by
    rw [← proj_eq_zero_iff, map_sub, map_natCast, ZMod.natCast_zmod_val, sub_self]
  obtain ⟨w, hw⟩ := mem_multiples.1 hx
  obtain ⟨ρ, hρ, hρw⟩ := (D.mem_map_relDeg_iff hLK).2 ⟨Multiplicative.ofAdd w, rfl⟩
  refine ⟨m, ?_⟩
  have hdeg : D.relDeg K (ρ⁻¹ * ((φ ^ m)⁻¹ * τ)) = 1 := by
    rw [map_mul, map_mul, map_inv, map_inv, map_pow, hφ, hρw]
    apply Multiplicative.toAdd.injective
    simp only [toAdd_mul, toAdd_inv, toAdd_pow, toAdd_ofAdd, toAdd_one]
    have hw' : relInertiaDegree D.deg K L • w = x - m := hw.symm
    rw [hw', nsmul_one]
    abel
  have hker : ((ρ⁻¹ * ((φ ^ m)⁻¹ * τ) : (K : Subgroup G)) : G) ∈ (K : Subgroup G) ⊓ D.deg.ker := by
    refine Subgroup.mem_inf.2 ⟨Subtype.coe_prop _, MonoidHom.mem_ker.2 ?_⟩
    rw [← relDeg_pow, hdeg, one_pow]
  have h := (L : Subgroup G).mul_mem (Subgroup.mem_subgroupOf.1 hρ) (hu hker)
  simpa using h

theorem zpowers_eq_top_of_unramified (hLK : L ≤ K) (hu : (K : Subgroup G) ⊓ D.deg.ker ≤ L)
    [((L : Subgroup G).subgroupOf K).Normal]
    {φ : (K : Subgroup G)} (hφ : D.relDeg K φ = Multiplicative.ofAdd 1) :
    Subgroup.zpowers ((φ : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K)) = ⊤ := by
  refine eq_top_iff.2 fun q _ => ?_
  induction q using QuotientGroup.induction_on with
  | H τ =>
    obtain ⟨m, hm⟩ := D.exists_pow_mul_mem_of_unramified hLK hu hφ τ
    refine ⟨m, ?_⟩
    change ((φ : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K)) ^ (m : ℤ) = τ
    rw [zpow_natCast, ← QuotientGroup.mk_pow, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simpa using hm

theorem isCyclic_of_unramified (hLK : L ≤ K) (hu : (K : Subgroup G) ⊓ D.deg.ker ≤ L)
    [((L : Subgroup G).subgroupOf K).Normal] :
    IsCyclic ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) := by
  obtain ⟨φ, hφ⟩ := D.relDeg_surjective K (Multiplicative.ofAdd 1)
  exact isCyclic_iff_exists_zpowers_eq_top.2 ⟨_, D.zpowers_eq_top_of_unramified hLK hu hφ⟩

end Frobenius

section TateZero

variable {K L : OpenSubgroup G}

noncomputable def valuationMod (K : OpenSubgroup G) (n : ℕ+) :
    fixedModule A (K : Subgroup G) →* Multiplicative (ZMod n) :=
  (AddMonoidHom.toMultiplicative (proj n).toAddMonoidHom).comp (D.valuation K)

theorem valuationMod_apply (K : OpenSubgroup G) (n : ℕ+) (a : fixedModule A (K : Subgroup G)) :
    D.valuationMod K n a = Multiplicative.ofAdd (proj n (Multiplicative.toAdd (D.valuation K a))) :=
  rfl

theorem valuationMod_surjective (K : OpenSubgroup G) (n : ℕ+) :
    Function.Surjective (D.valuationMod K n) := by
  intro z
  have h : Multiplicative.ofAdd ((Multiplicative.toAdd z).val : ℤ̂) ∈ (D.valuation K).range := by
    rw [range_valuation]
    exact_mod_cast D.intCast_mem_range_val ((Multiplicative.toAdd z).val : ℤ)
  obtain ⟨a, ha⟩ := h
  refine ⟨a, ?_⟩
  rw [valuationMod_apply, ha, toAdd_ofAdd, map_natCast, ZMod.natCast_zmod_val, ofAdd_toAdd]

noncomputable def relInertiaDegreePNat (hLK : L ≤ K) : ℕ+ :=
  ⟨relInertiaDegree D.deg K L, Nat.pos_of_ne_zero (D.relInertiaDegree_ne_zero hLK)⟩

@[simp] theorem coe_relInertiaDegreePNat (hLK : L ≤ K) :
    (D.relInertiaDegreePNat hLK : ℕ) = relInertiaDegree D.deg K L :=
  rfl

theorem range_norm_le_ker_valuationMod (hLK : L ≤ K) :
    (norm A (K : Subgroup G) (L : Subgroup G)).range ≤
      (D.valuationMod K (D.relInertiaDegreePNat hLK)).ker := by
  rintro _ ⟨a, rfl⟩
  rw [MonoidHom.mem_ker, valuationMod_apply, D.valuation_norm hLK, toAdd_pow, map_nsmul,
    nsmul_eq_mul]
  change Multiplicative.ofAdd (((D.relInertiaDegreePNat hLK : ℕ) : ZMod (D.relInertiaDegreePNat hLK)) *
    _) = 1
  rw [ZMod.natCast_self, zero_mul, ofAdd_zero]

noncomputable def tateZeroVal (hLK : L ≤ K) :
    tateZero A (K : Subgroup G) (L : Subgroup G) →*
      Multiplicative (ZMod (D.relInertiaDegreePNat hLK)) :=
  QuotientGroup.lift _ (D.valuationMod K (D.relInertiaDegreePNat hLK))
    (D.range_norm_le_ker_valuationMod hLK)

theorem tateZeroVal_mk (hLK : L ≤ K) (a : fixedModule A (K : Subgroup G)) :
    D.tateZeroVal hLK (a : tateZero A (K : Subgroup G) (L : Subgroup G)) =
      D.valuationMod K (D.relInertiaDegreePNat hLK) a :=
  rfl

theorem tateZeroVal_surjective (hLK : L ≤ K) : Function.Surjective (D.tateZeroVal hLK) := by
  intro z
  obtain ⟨a, ha⟩ := D.valuationMod_surjective K (D.relInertiaDegreePNat hLK) z
  exact ⟨a, ha⟩

theorem tateZeroVal_bijective (hax : ClassFieldAxiom G A) (hLK : L ≤ K)
    (hu : (K : Subgroup G) ⊓ D.deg.ker ≤ L) : Function.Bijective (D.tateZeroVal hLK) := by
  have := normal_of_unramified (d := D.deg) hLK hu
  have hcyc := D.isCyclic_of_unramified hLK hu
  have hcard := (hax K L hLK hcyc).1
  rw [relIndex_eq_relInertiaDegree hLK hu] at hcard
  have : Finite (tateZero A (K : Subgroup G) (L : Subgroup G)) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact D.relInertiaDegree_ne_zero hLK)
  refine (D.tateZeroVal_surjective hLK).bijective_of_nat_card_le ?_
  rw [hcard, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod, coe_relInertiaDegreePNat]

noncomputable def tateZeroEquiv (hax : ClassFieldAxiom G A) (hLK : L ≤ K)
    (hu : (K : Subgroup G) ⊓ D.deg.ker ≤ L) :
    tateZero A (K : Subgroup G) (L : Subgroup G) ≃*
      Multiplicative (ZMod ((L : Subgroup G).relIndex K)) :=
  (MulEquiv.ofBijective _ (D.tateZeroVal_bijective hax hLK hu)).trans
    (AddEquiv.toMultiplicative
      (ZMod.ringEquivCongr (m := (D.relInertiaDegreePNat hLK : ℕ))
        (relIndex_eq_relInertiaDegree (d := D.deg) hLK hu).symm).toAddEquiv)

end TateZero

section Units

variable {K L : OpenSubgroup G}

theorem norm_mem_units (hLK : L ≤ K) {a : fixedModule A (L : Subgroup G)} (ha : a ∈ D.units L) :
    norm A (K : Subgroup G) (L : Subgroup G) a ∈ D.units K := by
  rw [D.mem_units, D.valuation_norm hLK, D.mem_units.1 ha, one_pow]

theorem units_eq_map_norm (hax : ClassFieldAxiom G A) (hLK : L ≤ K)
    (hu : (K : Subgroup G) ⊓ D.deg.ker ≤ L) :
    D.units K = (D.units L).map (norm A (K : Subgroup G) (L : Subgroup G)) := by
  refine le_antisymm ?_ ?_
  · intro u hU
    have h1 : D.tateZeroVal hLK (u : tateZero A (K : Subgroup G) (L : Subgroup G)) = 1 := by
      rw [tateZeroVal_mk, valuationMod_apply, D.mem_units.1 hU, toAdd_one, map_zero, ofAdd_zero]
    have h2 : (u : tateZero A (K : Subgroup G) (L : Subgroup G)) = 1 :=
      (D.tateZeroVal_bijective hax hLK hu).1 (by rw [h1, map_one])
    obtain ⟨x, hx⟩ := (QuotientGroup.eq_one_iff u).1 h2
    refine ⟨x, ?_, hx⟩
    show x ∈ D.units L
    rw [D.mem_units]
    have h3 := D.valuation_norm hLK x
    rw [hx, D.mem_units.1 hU] at h3
    exact (ProfiniteInteger.pow_left_inj (D.relInertiaDegree_ne_zero hLK)).1
      (by rw [one_pow]; exact h3.symm)
  · rintro _ ⟨x, hx, rfl⟩
    exact D.norm_mem_units hLK hx

theorem exists_eq_smul_div_of_mem_augmentation (hLK : L ≤ K) (hu : (K : Subgroup G) ⊓ D.deg.ker ≤ L)
    {φ : (K : Subgroup G)} (hφ : D.relDeg K φ = Multiplicative.ofAdd 1) {x : A}
    (hx : x ∈ augmentation A (K : Subgroup G) (L : Subgroup G)) :
    ∃ b ∈ fixedModule A (L : Subgroup G), x = (φ : G) • b / b := by
  have := normal_of_unramified (d := D.deg) hLK hu

  let S : Subgroup A :=
    { carrier := {y | ∃ b ∈ fixedModule A (L : Subgroup G), y = (φ : G) • b / b}
      one_mem' := ⟨1, Subgroup.one_mem _, by rw [smul_one, div_one]⟩
      mul_mem' := by
        rintro _ _ ⟨b, hb, rfl⟩ ⟨c, hc, rfl⟩
        exact ⟨b * c, Subgroup.mul_mem _ hb hc, by rw [smul_mul', mul_div_mul_comm]⟩
      inv_mem' := by
        rintro _ ⟨b, hb, rfl⟩
        exact ⟨b⁻¹, Subgroup.inv_mem _ hb, by rw [smul_inv', inv_div_inv, inv_div]⟩ }

  let T : Subgroup (K : Subgroup G) :=
    { carrier := {g | ∀ a ∈ fixedModule A (L : Subgroup G), (g : G) • a / a ∈ S}
      one_mem' := fun a _ => by
        rw [OneMemClass.coe_one, one_smul, div_self']
        exact S.one_mem
      mul_mem' := by
        intro g h hg hh a ha
        have hha : (h : G) • a ∈ fixedModule A (L : Subgroup G) :=
          smul_mem_fixedModule_of_normal (L := (L : Subgroup G)) hLK h.2 ha
        have e : ((g * h : (K : Subgroup G)) : G) • a / a =
            ((g : G) • ((h : G) • a) / ((h : G) • a)) * ((h : G) • a / a) := by
          rw [Subgroup.coe_mul, mul_smul]
          simp only [div_eq_mul_inv, mul_assoc, inv_mul_cancel_left]
        rw [e]
        exact S.mul_mem (hg _ hha) (hh a ha)
      inv_mem' := by
        intro g hg a ha
        have hga : ((g⁻¹ : (K : Subgroup G)) : G) • a ∈ fixedModule A (L : Subgroup G) :=
          smul_mem_fixedModule_of_normal (L := (L : Subgroup G)) hLK (g⁻¹).2 ha
        have e : ((g⁻¹ : (K : Subgroup G)) : G) • a / a =
            ((g : G) • (((g⁻¹ : (K : Subgroup G)) : G) • a) / (((g⁻¹ : (K : Subgroup G)) : G) • a))⁻¹ := by
          rw [smul_smul, InvMemClass.coe_inv, mul_inv_cancel, one_smul, inv_div]
        rw [e]
        exact S.inv_mem (hg _ hga) }
  have hφT : φ ∈ T := fun a ha => ⟨a, ha, rfl⟩
  have hLT : ∀ ρ : (K : Subgroup G), (ρ : G) ∈ (L : Subgroup G) → ρ ∈ T := fun ρ hρ a ha => by
    rw [ha ρ hρ, div_self']
    exact S.one_mem
  have hTop : ∀ g : (K : Subgroup G), g ∈ T := by
    intro g
    obtain ⟨m, hm⟩ := D.exists_pow_mul_mem_of_unramified hLK hu hφ g
    have hg : g = φ ^ m * ((φ ^ m)⁻¹ * g) := by group
    rw [hg]
    exact T.mul_mem (T.pow_mem hφT m) (hLT _ (by simpa using hm))
  have hle : augmentation A (K : Subgroup G) (L : Subgroup G) ≤ S := by
    rw [augmentation, Subgroup.closure_le]
    rintro _ ⟨g, hg, a, ha, rfl⟩
    exact hTop ⟨g, hg⟩ a ha
  exact hle hx

theorem exists_units_eq_smul_div (hax : ClassFieldAxiom G A) (hLK : L ≤ K)
    (hu : (K : Subgroup G) ⊓ D.deg.ker ≤ L) {φ : (K : Subgroup G)}
    (hφ : D.relDeg K φ = Multiplicative.ofAdd 1) {u : fixedModule A (L : Subgroup G)}
    (hN : norm A (K : Subgroup G) (L : Subgroup G) u = 1) :
    ∃ ε ∈ D.units L, (u : A) = (φ : G) • (ε : A) / ε := by
  have := normal_of_unramified (d := D.deg) hLK hu
  have hcard := (hax K L hLK (D.isCyclic_of_unramified hLK hu)).2
  have hsub := (Nat.card_eq_one_iff_unique.1 hcard).1

  have haug : (u : A) ∈ augmentation A (K : Subgroup G) (L : Subgroup G) := by
    have h := (QuotientGroup.eq_one_iff
      (N := (augmentation A (K : Subgroup G) (L : Subgroup G)).comap
        ((fixedModule A (L : Subgroup G)).subtype.comp
          (norm A (K : Subgroup G) (L : Subgroup G)).ker.subtype))
      (⟨u, hN⟩ : (norm A (K : Subgroup G) (L : Subgroup G)).ker)).1 (Subsingleton.elim _ _)
    exact h
  obtain ⟨b, hb, hub⟩ := D.exists_eq_smul_div_of_mem_augmentation hLK hu hφ haug

  have hval : D.valuation L ⟨b, hb⟩ ∈ (D.valuation K).range := by
    rw [range_valuation, ← D.range_valuation L]
    exact ⟨_, rfl⟩
  obtain ⟨c, hc⟩ := hval
  have he : relRamificationIndex D.deg K L = 1 := isUnramified_iff.2 hu
  refine ⟨⟨b, hb⟩ / ⟨c, fixedModule_anti hLK c.2⟩, ?_, ?_⟩
  · rw [D.mem_units, map_div, D.valuation_of_mem hLK c.2, he, pow_one]
    change D.valuation L ⟨b, hb⟩ / D.valuation K c = 1
    rw [hc, div_self']
  · have hφc : (φ : G) • (c : A) = c := c.2 φ φ.2
    change (u : A) = (φ : G) • ((b : A) / c) / (b / c)
    rw [smul_div', hφc, div_div_div_cancel_right, hub]

end Units

end ClassFieldData

end Sec_ALR_Unramified

section Sec_ALR_Reciprocity

open ProfiniteInteger

namespace ClassFieldData

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] {A : Type*} [CommGroup A] [MulDistribMulAction G A]
  (D : ClassFieldData G A)

structure FrobeniusLift (K : OpenSubgroup G) where

  elt : G
  mem : elt ∈ (K : Subgroup G)

  deg : ℕ
  deg_pos : 0 < deg
  deg_eq : D.deg elt = Multiplicative.ofAdd ((deg * inertiaDegree D.deg K : ℕ) : ℤ̂)

variable {D} {K L : OpenSubgroup G}

namespace FrobeniusLift

omit [TotallyDisconnectedSpace G] in
theorem degree_ne_zero (s : D.FrobeniusLift K) : s.deg * inertiaDegree D.deg K ≠ 0 :=
  mul_ne_zero s.deg_pos.ne' (D.inertiaDegree_ne_zero K)

omit [TotallyDisconnectedSpace G] in

theorem mem_normalizer (hLK : L ≤ K) [hN : ((L : Subgroup G).subgroupOf K).Normal] {σ : G}
    (hσ : σ ∈ (K : Subgroup G)) :
    σ ∈ Subgroup.normalizer (((L : Subgroup G) ⊓ D.deg.ker : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  have hconj : ∀ g ∈ (K : Subgroup G), ∀ x ∈ (L : Subgroup G), g * x * g⁻¹ ∈ (L : Subgroup G) := by
    intro g hg x hx
    have := hN.conj_mem ⟨x, hLK hx⟩ (by simpa [Subgroup.mem_subgroupOf] using hx) ⟨g, hg⟩
    simpa [Subgroup.mem_subgroupOf] using this
  simp only [Subgroup.mem_inf, MonoidHom.mem_ker, map_mul, map_inv]
  constructor
  · rintro ⟨hL, hk⟩
    refine ⟨hconj σ hσ h hL, ?_⟩
    rw [hk, mul_one, mul_inv_cancel]
  · rintro ⟨hL, hk⟩
    refine ⟨?_, ?_⟩
    · have := hconj σ⁻¹ (K.inv_mem hσ) _ hL
      simpa [mul_assoc] using this
    · have := hk
      rwa [mul_comm (D.deg σ), mul_assoc, mul_inv_cancel, mul_one] at this

variable (L) in

noncomputable def field (hLK : L ≤ K) [((L : Subgroup G).subgroupOf K).Normal]
    (s : D.FrobeniusLift K) : OpenSubgroup G where
  toSubgroup := frobeniusClosure D.deg L s.elt
  isOpen' := isOpen_frobeniusClosure D.continuous_deg L.isOpen (mem_normalizer hLK s.mem)
    s.degree_ne_zero s.deg_eq

variable (hLK : L ≤ K) [((L : Subgroup G).subgroupOf K).Normal] (s : D.FrobeniusLift K)

theorem coe_field : ((s.field L hLK : OpenSubgroup G) : Subgroup G) =
    frobeniusClosure D.deg L s.elt :=
  rfl

theorem field_le : s.field L hLK ≤ K := by
  intro x hx
  exact frobeniusClosure_le K.isClosed s.mem (inf_le_left.trans hLK) hx

theorem elt_mem_field : s.elt ∈ ((s.field L hLK : OpenSubgroup G) : Subgroup G) :=
  mem_frobeniusClosure_self

theorem field_inf_ker :
    ((s.field L hLK : OpenSubgroup G) : Subgroup G) ⊓ D.deg.ker = (L : Subgroup G) ⊓ D.deg.ker :=
  frobeniusClosure_inf_ker D.continuous_deg L.isOpen (mem_normalizer hLK s.mem) s.degree_ne_zero
    s.deg_eq

theorem inertiaDegree_field :
    inertiaDegree D.deg ((s.field L hLK : OpenSubgroup G) : Subgroup G) =
      s.deg * inertiaDegree D.deg K :=
  inertiaDegree_frobeniusClosure D.continuous_deg (mem_normalizer hLK s.mem) s.degree_ne_zero
    s.deg_eq

theorem relDeg_field :
    D.relDeg (s.field L hLK) ⟨s.elt, s.elt_mem_field hLK⟩ = Multiplicative.ofAdd 1 := by
  refine (ProfiniteInteger.pow_left_inj (D.inertiaDegree_ne_zero (s.field L hLK))).1 ?_
  rw [D.relDeg_pow, inertiaDegree_field, ← ofAdd_nsmul, nsmul_one]
  exact s.deg_eq

theorem inf_ker_le_inf :
    ((s.field L hLK : OpenSubgroup G) : Subgroup G) ⊓ D.deg.ker ≤
      ((L ⊓ s.field L hLK : OpenSubgroup G) : Subgroup G) := by
  intro x hx
  have hx' := hx
  rw [field_inf_ker] at hx'
  exact ⟨hx'.1, hx.1⟩

end FrobeniusLift

omit [TotallyDisconnectedSpace G] in

theorem exists_prime (K : OpenSubgroup G) :
    ∃ π : fixedModule A (K : Subgroup G), D.valuation K π = Multiplicative.ofAdd 1 := by
  have h := D.intCast_mem_range_val 1
  rw [← D.range_valuation K, Int.cast_one] at h
  exact h

section PrimeNorm

variable (K L) in

noncomputable def primeNorm (S : OpenSubgroup G) : tateZero A (K : Subgroup G) (L : Subgroup G) :=
  QuotientGroup.mk (norm A (K : Subgroup G) (S : Subgroup G) (D.exists_prime S).choose)

omit [TotallyDisconnectedSpace G] in

theorem norm_mem_range_of_mem_units (hax : ClassFieldAxiom G A) {S : OpenSubgroup G} (hSK : S ≤ K)
    (hLK : L ≤ K) (hu : (S : Subgroup G) ⊓ D.deg.ker ≤ L) {u : fixedModule A (S : Subgroup G)}
    (hu' : u ∈ D.units S) :
    norm A (K : Subgroup G) (S : Subgroup G) u ∈ (norm A (K : Subgroup G) (L : Subgroup G)).range := by
  set M : OpenSubgroup G := L ⊓ S with hMdef
  have hMS : M ≤ S := inf_le_right
  have hML : M ≤ L := inf_le_left
  have hMu : (S : Subgroup G) ⊓ D.deg.ker ≤ M := fun x hx => ⟨hu hx, hx.1⟩
  rw [D.units_eq_map_norm hax hMS hMu] at hu'
  obtain ⟨w, -, rfl⟩ := hu'
  rw [norm_norm (fun x hx => hMS hx) (fun x hx => hSK hx) w]
  exact ⟨norm A (L : Subgroup G) (M : Subgroup G) w,
    norm_norm (fun x hx => hML hx) (fun x hx => hLK hx) w⟩

omit [TotallyDisconnectedSpace G] in

theorem mk_norm_eq_primeNorm (hax : ClassFieldAxiom G A) {S : OpenSubgroup G} (hSK : S ≤ K)
    (hLK : L ≤ K) (hu : (S : Subgroup G) ⊓ D.deg.ker ≤ L) {π : fixedModule A (S : Subgroup G)}
    (hπ : D.valuation S π = Multiplicative.ofAdd 1) :
    (QuotientGroup.mk (norm A (K : Subgroup G) (S : Subgroup G) π) :
      tateZero A (K : Subgroup G) (L : Subgroup G)) = D.primeNorm K L S := by
  set π0 := (D.exists_prime S).choose with hπ0
  have h0 : D.valuation S π0 = Multiplicative.ofAdd 1 := (D.exists_prime S).choose_spec
  have hu' : π * π0⁻¹ ∈ D.units S := by
    rw [D.mem_units, map_mul, map_inv, hπ, h0, mul_inv_cancel]
  obtain ⟨b, hb⟩ := D.norm_mem_range_of_mem_units hax hSK hLK hu hu'
  rw [primeNorm, ← hπ0, QuotientGroup.eq]
  have : (norm A (K : Subgroup G) (S : Subgroup G) π)⁻¹ * norm A (K : Subgroup G) (S : Subgroup G) π0 =
      (norm A (K : Subgroup G) (S : Subgroup G) (π * π0⁻¹))⁻¹ := by
    rw [map_mul, map_inv, mul_inv_rev, inv_inv, mul_comm]
  rw [this]
  exact Subgroup.inv_mem _ ⟨b, hb⟩

end PrimeNorm

section RecFrob

variable (hLK : L ≤ K) [((L : Subgroup G).subgroupOf K).Normal]

variable (L) in

noncomputable def recFrob (s : D.FrobeniusLift K) : tateZero A (K : Subgroup G) (L : Subgroup G) :=
  D.primeNorm K L (s.field L hLK)

theorem mk_norm_eq_recFrob (hax : ClassFieldAxiom G A) (s : D.FrobeniusLift K)
    {π : fixedModule A ((s.field L hLK : OpenSubgroup G) : Subgroup G)}
    (hπ : D.valuation (s.field L hLK) π = Multiplicative.ofAdd 1) :
    (QuotientGroup.mk (norm A (K : Subgroup G) ((s.field L hLK : OpenSubgroup G) : Subgroup G) π) :
      tateZero A (K : Subgroup G) (L : Subgroup G)) = D.recFrob L hLK s :=
  D.mk_norm_eq_primeNorm hax (s.field_le hLK) hLK (fun x hx => by
    have := (s.field_inf_ker hLK).le hx
    exact this.1) hπ

end RecFrob

end ClassFieldData

end Sec_ALR_Reciprocity

section Sec_ALR_CoeNormEqProdSmulNorm

open ProfiniteInteger

variable {G : Type*} [Group G] {A : Type*} [CommGroup A] [MulDistribMulAction G A]

theorem coe_norm_eq_prod_smul_norm (d : G →* Multiplicative ℤ̂) {K S J : Subgroup G} {f n : ℕ}
    (hn : 0 < n) (hf : 0 < f) (hSK : S ≤ K)
    (hdS : ∀ s ∈ S, Multiplicative.toAdd (d s) ∈ multiples (n * f))
    (hsurj : ∀ k ∈ K, Multiplicative.toAdd (d k) ∈ multiples (n * f) → ∃ s ∈ S, d s = d k)
    (hdK : ∀ k ∈ K, Multiplicative.toAdd (d k) ∈ multiples f)
    (hJ : ∀ q ∈ K ⊓ d.ker, q ∈ S ↔ q ∈ J)
    {φ : G} (hφK : φ ∈ K) (hdφ : d φ = Multiplicative.ofAdd (f : ℤ̂))
    [(S.subgroupOf K).FiniteIndex] [(J.subgroupOf (K ⊓ d.ker)).FiniteIndex]
    (a : fixedModule A S) (ha : (a : A) ∈ fixedModule A J) :
    (norm A K S a : A) =
      ∏ ν : Fin n, φ ^ (ν : ℕ) • (norm A (K ⊓ d.ker) J ⟨a, ha⟩ : A) := by
  classical
  set Q := K ⊓ d.ker with hQ
  have hQK : Q ≤ K := inf_le_left

  let incl : Q ⧸ J.subgroupOf Q → K ⧸ S.subgroupOf K :=
    Quotient.map' (fun q : Q => (⟨q, hQK q.2⟩ : K)) fun q q' h => by
      rw [QuotientGroup.leftRel_apply, Subgroup.mem_subgroupOf] at h ⊢
      have hq : ((q⁻¹ * q' : Q) : G) ∈ Q := (q⁻¹ * q').2
      simpa using (hJ _ hq).2 h
  let φK : K := ⟨φ, hφK⟩
  let F : Fin n × (Q ⧸ J.subgroupOf Q) → K ⧸ S.subgroupOf K := fun p => (φK ^ (p.1 : ℕ)) • incl p.2
  have hFmk : ∀ (ν : Fin n) (q : Q), F (ν, (q : Q ⧸ J.subgroupOf Q)) =
      ((φK ^ (ν : ℕ) * ⟨q, hQK q.2⟩ : K) : K ⧸ S.subgroupOf K) := fun _ _ => rfl

  have hdeg : ∀ (m : ℤ) (q : G), q ∈ Q →
      Multiplicative.toAdd (d (φ ^ m * q)) = ((m * f : ℤ) : ℤ̂) := by
    intro m q hq
    rw [map_mul, map_zpow, hdφ, (MonoidHom.mem_ker).1 hq.2, mul_one, ← ofAdd_zsmul, toAdd_ofAdd,
      zsmul_eq_mul]
    push_cast
    ring
  have hF : Function.Bijective F := by
    constructor
    · rintro ⟨ν, x⟩ ⟨μ, y⟩ hxy
      induction x using QuotientGroup.induction_on with
      | H q =>
      induction y using QuotientGroup.induction_on with
      | H q' =>
        rw [hFmk, hFmk, QuotientGroup.eq, Subgroup.mem_subgroupOf] at hxy
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, SubmonoidClass.coe_pow] at hxy

        have hx : ((φ ^ (ν : ℕ) * (q : G))⁻¹ * (φ ^ (μ : ℕ) * q') : G) =
            (q : G)⁻¹ * (φ ^ ((μ : ℤ) - ν) * q') := by
          rw [zpow_sub, zpow_natCast, zpow_natCast]
          group
        have hdq : Multiplicative.toAdd (d ((q : G)⁻¹ * (φ ^ ((μ : ℤ) - ν) * q'))) =
            ((((μ : ℤ) - ν) * f : ℤ) : ℤ̂) := by
          rw [map_mul, map_inv, (MonoidHom.mem_ker).1 q.2.2, inv_one, one_mul]
          exact hdeg _ _ q'.2
        have hmem := hdS _ hxy
        rw [hx, hdq] at hmem
        have hdvd := (intCast_mem_multiples_iff (Nat.mul_pos hn hf)).1 hmem
        push_cast at hdvd
        have hdvd' : (n : ℤ) ∣ (μ : ℤ) - ν :=
          (mul_dvd_mul_iff_right (by exact_mod_cast hf.ne')).1 hdvd
        have hνμ : ν = μ := by
          have hμ := μ.2
          have hν := ν.2
          have h0 : ((μ : ℤ) - ν) = 0 :=
            Int.eq_zero_of_abs_lt_dvd hdvd' (abs_sub_lt_iff.2 ⟨by omega, by omega⟩)
          exact Fin.ext (by omega)
        subst hνμ
        have hqq : (q : G)⁻¹ * q' ∈ S := by simpa [mul_assoc] using hxy
        have hqQ : (q : G)⁻¹ * q' ∈ Q := Q.mul_mem (Q.inv_mem q.2) q'.2
        refine Prod.ext rfl ?_
        rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
        simpa using (hJ _ hqQ).1 hqq
    · intro y
      induction y using QuotientGroup.induction_on with
      | H k =>
        obtain ⟨w, hw⟩ := mem_multiples.1 (hdK k k.2)
        set N : ℕ+ := ⟨n, hn⟩ with hNdef
        set ν : ℕ := (proj N w).val with hνdef
        have hνn : ν < n := ZMod.val_lt _
        have hw' : w - (ν : ℤ̂) ∈ multiples n := by
          have := (proj_eq_zero_iff (n := N) (x := w - (ν : ℤ̂))).1 (by
            rw [map_sub, map_natCast, hνdef, ZMod.natCast_zmod_val, sub_self])
          simpa [hNdef] using this
        obtain ⟨z, hz⟩ := mem_multiples.1 hw'
        have hdk : Multiplicative.toAdd (d (φ ^ (-(ν : ℤ)) * k)) ∈ multiples (n * f) := by
          rw [map_mul, map_zpow, hdφ, ← ofAdd_zsmul, toAdd_mul, toAdd_ofAdd, hw]
          refine mem_multiples.2 ⟨z, ?_⟩
          have : w = (ν : ℤ̂) + n • z := by rw [← hz]; ring
          rw [this]
          simp only [nsmul_eq_mul, zsmul_eq_mul]
          push_cast
          ring
        obtain ⟨s, hs, hds⟩ := hsurj _ (K.mul_mem (K.zpow_mem hφK _) k.2) hdk
        set q : G := φ ^ (-(ν : ℤ)) * k * s⁻¹ with hqdef
        have hqQ : q ∈ Q := by
          refine ⟨K.mul_mem (K.mul_mem (K.zpow_mem hφK _) k.2) (K.inv_mem (hSK hs)), ?_⟩
          show d q = 1
          rw [hqdef, map_mul, map_inv, ← hds, mul_inv_cancel]
        refine ⟨(⟨ν, hνn⟩, ((⟨q, hqQ⟩ : Q) : Q ⧸ J.subgroupOf Q)), ?_⟩
        rw [hFmk, QuotientGroup.eq, Subgroup.mem_subgroupOf]
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, SubmonoidClass.coe_pow, hqdef]
        have : ((φ ^ ν * (φ ^ (-(ν : ℤ)) * (k : G) * s⁻¹))⁻¹ * k : G) = s := by
          rw [zpow_neg, zpow_natCast]
          group
        rw [this]
        exact hs
  rw [coe_norm, ← finprod_comp_equiv (Equiv.ofBijective F hF)]
  let _ := Fintype.ofFinite (Q ⧸ J.subgroupOf Q)
  rw [finprod_eq_prod_of_fintype, Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun ν _ => ?_
  rw [coe_norm, finprod_eq_prod_of_fintype, Finset.smul_prod']
  refine Finset.prod_congr rfl fun x _ => ?_
  induction x using QuotientGroup.induction_on with
  | H q =>
    rw [Equiv.ofBijective_apply, hFmk, cosetSMul_mk, cosetSMul_mk, smul_smul]
    rfl

namespace ClassFieldData

variable [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]
  {D : ClassFieldData G A} {K L : OpenSubgroup G}

omit [TotallyDisconnectedSpace G] in

instance finiteIndex_inf_ker (d : G →* Multiplicative ℤ̂) (K L : OpenSubgroup G) :
    (((L : Subgroup G) ⊓ d.ker).subgroupOf ((K : Subgroup G) ⊓ d.ker)).FiniteIndex := by
  have h : ((L : Subgroup G) ⊓ d.ker).subgroupOf ((K : Subgroup G) ⊓ d.ker) =
      (L : Subgroup G).subgroupOf ((K : Subgroup G) ⊓ d.ker) := by
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, and_iff_left_iff_imp]
    exact fun _ => x.2.2
  rw [h]
  infer_instance

omit [TotallyDisconnectedSpace G] in

theorem toAdd_deg_mem_multiples (K : OpenSubgroup G) {k : G} (hk : k ∈ (K : Subgroup G)) :
    Multiplicative.toAdd (D.deg k) ∈ multiples (inertiaDegree D.deg K) := by
  obtain ⟨y, hy⟩ := (D.mem_map_deg_iff K).1 ⟨k, hk, rfl⟩
  refine mem_multiples.2 ⟨Multiplicative.toAdd y, ?_⟩
  rw [← hy, toAdd_pow]

variable (hLK : L ≤ K) [((L : Subgroup G).subgroupOf K).Normal] (s : D.FrobeniusLift K)

theorem coe_norm_field_eq {φ : G} (hφK : φ ∈ (K : Subgroup G))
    (hdφ : D.deg φ = Multiplicative.ofAdd (inertiaDegree D.deg K : ℤ̂))
    (a : fixedModule A ((s.field L hLK : OpenSubgroup G) : Subgroup G)) :
    (norm A (K : Subgroup G) (s.field L hLK : Subgroup G) a : A) =
      ∏ ν : Fin s.deg, φ ^ (ν : ℕ) •
        (norm A ((K : Subgroup G) ⊓ D.deg.ker) ((L : Subgroup G) ⊓ D.deg.ker)
          ⟨a, fixedModule_anti le_frobeniusClosure a.2⟩ : A) := by
  have hmap := map_frobeniusClosure D.continuous_deg (FrobeniusLift.mem_normalizer hLK s.mem)
    s.deg_eq (L := (L : Subgroup G))
  refine coe_norm_eq_prod_smul_norm D.deg s.deg_pos (Nat.pos_of_ne_zero (D.inertiaDegree_ne_zero K))
    (fun x hx => s.field_le hLK hx) ?_ ?_ (fun k hk => toAdd_deg_mem_multiples K hk) ?_ hφK hdφ a _
  · intro x hx
    have : D.deg x ∈ (frobeniusClosure D.deg L s.elt).map D.deg := ⟨x, hx, rfl⟩
    rw [hmap] at this
    exact this
  · intro k _ hk
    have : D.deg k ∈ AddSubgroup.toSubgroup (multiples (s.deg * inertiaDegree D.deg K)) := hk
    rw [← hmap] at this
    obtain ⟨x, hx, hxk⟩ := this
    exact ⟨x, hx, hxk⟩
  · intro q hq
    constructor
    · intro hqS
      have : q ∈ ((s.field L hLK : OpenSubgroup G) : Subgroup G) ⊓ D.deg.ker := ⟨hqS, hq.2⟩
      rw [s.field_inf_ker hLK] at this
      exact this
    · intro hqJ
      exact le_frobeniusClosure hqJ

end ClassFieldData

end Sec_ALR_CoeNormEqProdSmulNorm

section Sec_ALR_KeyLemma

open ProfiniteInteger

namespace ClassFieldData

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] {A : Type*} [CommGroup A] [MulDistribMulAction G A]
  {D : ClassFieldData G A} {K L : OpenSubgroup G}

section SlopeTestRemainingChoices

omit [TotallyDisconnectedSpace G] in

def powLift {φ : G} (hφK : φ ∈ (K : Subgroup G))
    (hdφ : D.deg φ = Multiplicative.ofAdd (inertiaDegree D.deg K : ℤ̂)) (m : ℕ) (hm : 0 < m) :
    D.FrobeniusLift K where
  elt := φ ^ m
  mem := K.pow_mem hφK m
  deg := m
  deg_pos := hm
  deg_eq := by
    rw [map_pow, hdφ, ← ofAdd_nsmul]
    congr 1
    push_cast
    rw [nsmul_eq_mul]

omit [TotallyDisconnectedSpace G] in

theorem mem_fixedModule_of_smul_eq [IsDiscreteModule G A] (K : OpenSubgroup G) {φ : G}
    (hφK : φ ∈ (K : Subgroup G)) (hdφ : D.deg φ = Multiplicative.ofAdd (inertiaDegree D.deg K : ℤ̂))
    {w : A} (hw : w ∈ fixedModule A ((K : Subgroup G) ⊓ D.deg.ker)) (hφw : φ • w = w) :
    w ∈ fixedModule A (K : Subgroup G) := by
  let S : OpenSubgroup G := ⟨MulAction.stabilizer G w, IsDiscreteModule.isOpen_stabilizer w⟩
  let M : OpenSubgroup G := S ⊓ K
  have hMK : M ≤ K := inf_le_right
  have hu : (K : Subgroup G) ⊓ D.deg.ker ≤ M := fun g hg => ⟨hw g hg, hg.1⟩
  have hrel : D.relDeg K ⟨φ, hφK⟩ = Multiplicative.ofAdd 1 := by
    refine (ProfiniteInteger.pow_left_inj (D.inertiaDegree_ne_zero K)).1 ?_
    rw [D.relDeg_pow, ← ofAdd_nsmul, nsmul_one]
    exact hdφ
  intro τ hτ
  obtain ⟨m, hm⟩ := D.exists_pow_mul_mem_of_unramified hMK hu hrel ⟨τ, hτ⟩
  have h1 : ∀ j : ℕ, (φ ^ j) • w = w := by
    intro j
    induction j with
    | zero => simp
    | succ k ih => rw [pow_succ, mul_smul, hφw, ih]
  have h2 : ((φ ^ m)⁻¹ * τ) • w = w := by
    have h3 : (φ ^ m)⁻¹ * τ ∈ S := by simpa using hm.1
    exact MulAction.mem_stabilizer_iff.1 h3
  calc τ • w = (φ ^ m * ((φ ^ m)⁻¹ * τ)) • w := by group
    _ = w := by rw [mul_smul, h2, h1]

omit [TotallyDisconnectedSpace G] in

theorem map_conj_inf_ker (hLK : L ≤ K) [((L : Subgroup G).subgroupOf K).Normal] {g : G}
    (hg : g ∈ (K : Subgroup G)) :
    ((L : Subgroup G) ⊓ D.deg.ker).map (MulAut.conj g).toMonoidHom = (L : Subgroup G) ⊓ D.deg.ker :=
  Subgroup.mem_normalizer_iff_map_conj_eq.1 (FrobeniusLift.mem_normalizer hLK hg)

omit [TotallyDisconnectedSpace G] in

theorem map_conj_inf_ker_self {g : G} (hg : g ∈ (K : Subgroup G)) :
    ((K : Subgroup G) ⊓ D.deg.ker).map (MulAut.conj g).toMonoidHom =
      (K : Subgroup G) ⊓ D.deg.ker := by
  have : ((K : Subgroup G).subgroupOf K).Normal := by
    rw [Subgroup.subgroupOf_self]
    infer_instance
  exact map_conj_inf_ker le_rfl hg

omit [TotallyDisconnectedSpace G] in

theorem smul_mem_fixedModule_inf_ker (hLK : L ≤ K) [((L : Subgroup G).subgroupOf K).Normal] {g : G}
    (hg : g ∈ (K : Subgroup G)) {y : A} (hy : y ∈ fixedModule A ((L : Subgroup G) ⊓ D.deg.ker)) :
    g • y ∈ fixedModule A ((L : Subgroup G) ⊓ D.deg.ker) := by
  have := smul_mem_fixedModule hy g
  rwa [map_conj_inf_ker hLK hg] at this

omit [TotallyDisconnectedSpace G] in

theorem smul_norm_inf_ker (hLK : L ≤ K) [((L : Subgroup G).subgroupOf K).Normal] {g : G}
    (hg : g ∈ (K : Subgroup G)) (y : fixedModule A ((L : Subgroup G) ⊓ D.deg.ker)) :
    g • (norm A ((K : Subgroup G) ⊓ D.deg.ker) ((L : Subgroup G) ⊓ D.deg.ker) y : A) =
      norm A ((K : Subgroup G) ⊓ D.deg.ker) ((L : Subgroup G) ⊓ D.deg.ker)
        ⟨g • (y : A), smul_mem_fixedModule_inf_ker hLK hg y.2⟩ :=
  smul_norm_of_map_eq g (map_conj_inf_ker_self hg) (map_conj_inf_ker hLK hg) y

omit [TotallyDisconnectedSpace G] in

theorem smul_smul_comm (hLK : L ≤ K) [hN : ((L : Subgroup G).subgroupOf K).Normal] {δ ψ : G}
    (hδ : δ ∈ (K : Subgroup G) ⊓ D.deg.ker) (hψ : ψ ∈ (L : Subgroup G)) {y : A}
    (hy : y ∈ fixedModule A ((L : Subgroup G) ⊓ D.deg.ker)) : δ • ψ • y = ψ • δ • y := by
  have hconj : ∀ g ∈ (K : Subgroup G), ∀ x ∈ (L : Subgroup G), g * x * g⁻¹ ∈ (L : Subgroup G) := by
    intro g hg x hx
    have := hN.conj_mem ⟨x, hLK hx⟩ (by simpa [Subgroup.mem_subgroupOf] using hx) ⟨g, hg⟩
    simpa [Subgroup.mem_subgroupOf] using this
  have hc : δ⁻¹ * ψ⁻¹ * δ * ψ ∈ (L : Subgroup G) ⊓ D.deg.ker := by
    refine ⟨?_, ?_⟩
    · have h1 : δ⁻¹ * ψ⁻¹ * δ⁻¹⁻¹ ∈ (L : Subgroup G) :=
        hconj δ⁻¹ (K.inv_mem hδ.1) _ (L.inv_mem hψ)
      rw [inv_inv] at h1
      exact L.mul_mem h1 hψ
    · have hdδ : D.deg δ = 1 := hδ.2
      show D.deg (δ⁻¹ * ψ⁻¹ * δ * ψ) = 1
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hdδ]
      simp
  calc δ • ψ • y = (ψ * δ * (δ⁻¹ * ψ⁻¹ * δ * ψ)) • y := by rw [← mul_smul]; group
    _ = ψ • δ • y := by rw [mul_smul, hy _ hc, mul_smul]

theorem smul_mem_field [IsDiscreteModule G A] (hLK : L ≤ K) [((L : Subgroup G).subgroupOf K).Normal]
    (s : D.FrobeniusLift K) {g : G}
    (hgJ : ∀ y ∈ fixedModule A ((L : Subgroup G) ⊓ D.deg.ker),
      g • y ∈ fixedModule A ((L : Subgroup G) ⊓ D.deg.ker))
    (hcomm : ∀ y ∈ fixedModule A ((L : Subgroup G) ⊓ D.deg.ker), s.elt • g • y = g • s.elt • y)
    {y : A} (hy : y ∈ fixedModule A ((s.field L hLK : OpenSubgroup G) : Subgroup G)) :
    g • y ∈ fixedModule A ((s.field L hLK : OpenSubgroup G) : Subgroup G) := by
  rw [FrobeniusLift.coe_field, mem_fixedModule_frobeniusClosure] at hy ⊢
  exact ⟨hgJ y hy.1, by rw [hcomm y hy.1, hy.2]⟩

end SlopeTestRemainingChoices

section Helpers

omit [TotallyDisconnectedSpace G] in

theorem normal_inf_ker (hLK : L ≤ K) [hN : ((L : Subgroup G).subgroupOf K).Normal] :
    (((L : Subgroup G) ⊓ D.deg.ker).subgroupOf ((K : Subgroup G) ⊓ D.deg.ker)).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  have h := (Subgroup.mem_normalizer_iff.1 (FrobeniusLift.mem_normalizer (D := D) hLK g.2.1) n).1 hn
  simpa using h

omit [TotallyDisconnectedSpace G] in

theorem prod_range_prod_range_eq {M : Type*} [CommMonoid M] (f : ℕ → M) (g D0 : ℕ) :
    ∏ i ∈ Finset.range g, ∏ j ∈ Finset.range D0, f (D0 * i + j) =
      ∏ m ∈ Finset.range (g * D0), f m := by
  induction g with
  | zero => simp
  | succ k ih =>
    rw [Finset.prod_range_succ, ih, Nat.succ_mul, Finset.prod_range_add, mul_comm D0 k]

variable (hLK : L ≤ K) [((L : Subgroup G).subgroupOf K).Normal]

theorem field_le_field_of_pow (s1 s2 : D.FrobeniusLift K) (k : ℕ) (h2 : s2.elt = s1.elt ^ k) :
    s2.field L hLK ≤ s1.field L hLK := by
  intro x hx
  refine frobeniusClosure_le (s1.field L hLK).isClosed ?_ le_frobeniusClosure hx
  rw [h2]
  exact Subgroup.pow_mem _ (s1.elt_mem_field hLK) k

theorem coe_norm_field_field (s1 s2 : D.FrobeniusLift K) (k : ℕ) (hk : 0 < k)
    (h2 : s2.elt = s1.elt ^ k) (hdeg : s2.deg = k * s1.deg)
    (z : fixedModule A ((s2.field L hLK : OpenSubgroup G) : Subgroup G)) :
    (norm A ((s1.field L hLK : OpenSubgroup G) : Subgroup G)
      ((s2.field L hLK : OpenSubgroup G) : Subgroup G) z : A) =
      ∏ i : Fin k, s1.elt ^ (i : ℕ) • (z : A) := by
  have hmap1 := map_frobeniusClosure D.continuous_deg (FrobeniusLift.mem_normalizer hLK s1.mem)
    s1.deg_eq (L := (L : Subgroup G))
  have hmap2 := map_frobeniusClosure D.continuous_deg (FrobeniusLift.mem_normalizer hLK s2.mem)
    s2.deg_eq (L := (L : Subgroup G))
  rw [hdeg, mul_assoc] at hmap2
  have hf : 0 < s1.deg * inertiaDegree D.deg K :=
    Nat.mul_pos s1.deg_pos (Nat.pos_of_ne_zero (D.inertiaDegree_ne_zero K))
  have key := coe_norm_eq_prod_smul_norm D.deg (K := ((s1.field L hLK : OpenSubgroup G) : Subgroup G))
    (S := ((s2.field L hLK : OpenSubgroup G) : Subgroup G)) (J := (L : Subgroup G) ⊓ D.deg.ker)
    (f := s1.deg * inertiaDegree D.deg K) (n := k) hk hf
    (fun x hx => field_le_field_of_pow hLK s1 s2 k h2 hx) ?_ ?_ ?_ ?_
    (s1.elt_mem_field hLK) s1.deg_eq z (fixedModule_anti le_frobeniusClosure z.2)
  · rw [key]
    refine Finset.prod_congr rfl fun i _ => ?_
    congr 1
    exact coe_norm_of_le (fun x hx => (s1.field_inf_ker hLK).le hx) _
  · intro x hx
    have : D.deg x ∈ (frobeniusClosure D.deg L s2.elt).map D.deg := ⟨x, hx, rfl⟩
    rw [hmap2] at this
    exact this
  · intro x _ hx
    have : D.deg x ∈ AddSubgroup.toSubgroup (multiples (k * (s1.deg * inertiaDegree D.deg K))) := hx
    rw [← hmap2] at this
    obtain ⟨y, hy, hyx⟩ := this
    exact ⟨y, hy, hyx⟩
  · intro x hx
    have : D.deg x ∈ (frobeniusClosure D.deg L s1.elt).map D.deg := ⟨x, hx, rfl⟩
    rw [hmap1] at this
    exact this
  · intro q hq
    have hqJ : q ∈ (L : Subgroup G) ⊓ D.deg.ker := (s1.field_inf_ker hLK).le hq
    exact ⟨fun _ => hqJ, fun h => le_frobeniusClosure h⟩

omit [TotallyDisconnectedSpace G] [((L : Subgroup G).subgroupOf K).Normal] in

theorem coe_norm_inf_ker_prod {ι : Type*} (s : Finset ι) (f : ι → A)
    (hf : ∀ i, f i ∈ fixedModule A ((L : Subgroup G) ⊓ D.deg.ker)) :
    (norm A ((K : Subgroup G) ⊓ D.deg.ker) ((L : Subgroup G) ⊓ D.deg.ker)
      ⟨∏ i ∈ s, f i, Subgroup.prod_mem _ fun i _ => hf i⟩ : A) =
      ∏ i ∈ s, (norm A ((K : Subgroup G) ⊓ D.deg.ker) ((L : Subgroup G) ⊓ D.deg.ker)
        ⟨f i, hf i⟩ : A) := by
  have h : (⟨∏ i ∈ s, f i, Subgroup.prod_mem _ fun i _ => hf i⟩ :
      fixedModule A ((L : Subgroup G) ⊓ D.deg.ker)) = ∏ i ∈ s, ⟨f i, hf i⟩ := by
    ext
    simp
  rw [h, map_prod]
  simp

omit [TotallyDisconnectedSpace G] [((L : Subgroup G).subgroupOf K).Normal] in

theorem coe_norm_inf_ker_mul {y z : A} (hy : y ∈ fixedModule A ((L : Subgroup G) ⊓ D.deg.ker))
    (hz : z ∈ fixedModule A ((L : Subgroup G) ⊓ D.deg.ker)) :
    (norm A ((K : Subgroup G) ⊓ D.deg.ker) ((L : Subgroup G) ⊓ D.deg.ker)
      ⟨y * z, Subgroup.mul_mem _ hy hz⟩ : A) =
      (norm A ((K : Subgroup G) ⊓ D.deg.ker) ((L : Subgroup G) ⊓ D.deg.ker) ⟨y, hy⟩ : A) *
        norm A ((K : Subgroup G) ⊓ D.deg.ker) ((L : Subgroup G) ⊓ D.deg.ker) ⟨z, hz⟩ := by
  have h : (⟨y * z, Subgroup.mul_mem _ hy hz⟩ : fixedModule A ((L : Subgroup G) ⊓ D.deg.ker)) =
      ⟨y, hy⟩ * ⟨z, hz⟩ := rfl
  rw [h, map_mul]
  rfl

end Helpers

section Key

variable (hLK : L ≤ K) [((L : Subgroup G).subgroupOf K).Normal]

theorem exists_norm_eq_norm_inf_ker (hax : ClassFieldAxiom G A) [IsDiscreteModule G A]
    {φ : G} (hφK : φ ∈ (K : Subgroup G))
    (hdφ : D.deg φ = Multiplicative.ofAdd (inertiaDegree D.deg K : ℤ̂))
    (s1 s2 : D.FrobeniusLift K) (h1 : s1.elt = φ ^ s1.deg) (hψL : s1.elt ∈ (L : Subgroup G))
    (h2 : s2.elt = s1.elt ^ ((L : Subgroup G).relIndex K))
    (hdeg : s2.deg = (L : Subgroup G).relIndex K * s1.deg)
    {x a : A} (hx : x ∈ fixedModule A ((s1.field L hLK : OpenSubgroup G) : Subgroup G))
    (ha : a ∈ fixedModule A ((s1.field L hLK : OpenSubgroup G) : Subgroup G))
    (hxu : D.valuation (s1.field L hLK) ⟨x, hx⟩ = 1)
    (hau : D.valuation (s1.field L hLK) ⟨a, ha⟩ = 1)
    {δ : G} (hδ : δ ∈ (K : Subgroup G) ⊓ D.deg.ker) (hrel : φ • x / x = δ • a / a) :
    ∃ b : fixedModule A (L : Subgroup G),
      (norm A (K : Subgroup G) (L : Subgroup G) b : A) =
        norm A ((K : Subgroup G) ⊓ D.deg.ker) ((L : Subgroup G) ⊓ D.deg.ker)
          ⟨x, fixedModule_anti le_frobeniusClosure hx⟩ := by
  classical
  set g := (L : Subgroup G).relIndex K with hgdef
  have hg : 0 < g := Nat.pos_of_ne_zero (Subgroup.FiniteIndex.index_ne_zero
    (H := (L : Subgroup G).subgroupOf K))
  have hP'P : s2.field L hLK ≤ s1.field L hLK := field_le_field_of_pow hLK s1 s2 g h2
  have hP'L : s2.field L hLK ≤ L := fun y hy =>
    frobeniusClosure_le L.isClosed (by rw [h2]; exact L.pow_mem hψL g) inf_le_left hy
  have hu : ((s1.field L hLK : OpenSubgroup G) : Subgroup G) ⊓ D.deg.ker ≤ s2.field L hLK :=
    fun y hy => le_frobeniusClosure ((s1.field_inf_ker hLK).le hy)
  have hT := coe_norm_field_field hLK s1 s2 g hg h2 hdeg
  have hrelψ := s1.relDeg_field hLK

  have hφJ : ∀ y ∈ fixedModule A ((L : Subgroup G) ⊓ D.deg.ker),
      φ • y ∈ fixedModule A ((L : Subgroup G) ⊓ D.deg.ker) :=
    fun y hy => smul_mem_fixedModule_inf_ker hLK hφK hy
  have hφjJ : ∀ (j : ℕ), ∀ y ∈ fixedModule A ((L : Subgroup G) ⊓ D.deg.ker),
      φ ^ j • y ∈ fixedModule A ((L : Subgroup G) ⊓ D.deg.ker) :=
    fun j y hy => smul_mem_fixedModule_inf_ker hLK (K.pow_mem hφK j) hy
  have hδJ : ∀ y ∈ fixedModule A ((L : Subgroup G) ⊓ D.deg.ker),
      δ • y ∈ fixedModule A ((L : Subgroup G) ⊓ D.deg.ker) :=
    fun y hy => smul_mem_fixedModule_inf_ker hLK hδ.1 hy
  have hcommφ : ∀ (i j : ℕ) (y : A), s1.elt ^ i • φ ^ j • y = φ ^ j • s1.elt ^ i • y := by
    intro i j y
    have hc : Commute (s1.elt ^ i) (φ ^ j) := by
      rw [h1]
      exact (((Commute.refl φ).pow_left _).pow_left _).pow_right _
    rw [smul_smul, smul_smul, hc.eq]
  have hcommδ : ∀ (i : ℕ), ∀ y ∈ fixedModule A ((L : Subgroup G) ⊓ D.deg.ker),
      s1.elt ^ i • δ • y = δ • s1.elt ^ i • y :=
    fun i y hy => (smul_smul_comm hLK hδ (L.pow_mem hψL i) hy).symm
  have hφP' : ∀ (j : ℕ), ∀ y ∈ fixedModule A ((s2.field L hLK : OpenSubgroup G) : Subgroup G),
      φ ^ j • y ∈ fixedModule A ((s2.field L hLK : OpenSubgroup G) : Subgroup G) := by
    intro j y hy
    refine smul_mem_field hLK s2 (hφjJ j) (fun z _ => ?_) hy
    rw [h2]
    exact hcommφ g j z
  have hδP' : ∀ y ∈ fixedModule A ((s2.field L hLK : OpenSubgroup G) : Subgroup G),
      δ • y ∈ fixedModule A ((s2.field L hLK : OpenSubgroup G) : Subgroup G) := by
    intro y hy
    refine smul_mem_field hLK s2 hδJ (fun z hz => ?_) hy
    rw [h2]
    exact hcommδ g z hz
  have hP'J : ∀ y ∈ fixedModule A ((s2.field L hLK : OpenSubgroup G) : Subgroup G),
      y ∈ fixedModule A ((L : Subgroup G) ⊓ D.deg.ker) :=
    fun y hy => fixedModule_anti le_frobeniusClosure hy

  have hxU : (⟨x, hx⟩ : fixedModule A ((s1.field L hLK : OpenSubgroup G) : Subgroup G)) ∈
      D.units (s1.field L hLK) := hxu
  rw [D.units_eq_map_norm hax hP'P hu] at hxU
  obtain ⟨x'', -, hx''⟩ := hxU
  have haU : (⟨a, ha⟩ : fixedModule A ((s1.field L hLK : OpenSubgroup G) : Subgroup G)) ∈
      D.units (s1.field L hLK) := hau
  rw [D.units_eq_map_norm hax hP'P hu] at haU
  obtain ⟨c, -, hc⟩ := haU
  have hxN : x = ∏ i : Fin g, s1.elt ^ (i : ℕ) • (x'' : A) := by
    rw [← hT, hx'']
  have haN : a = ∏ i : Fin g, s1.elt ^ (i : ℕ) • (c : A) := by
    rw [← hT, hc]

  have hφx'' : φ • (x'' : A) ∈ fixedModule A ((s2.field L hLK : OpenSubgroup G) : Subgroup G) := by
    simpa using hφP' 1 _ x''.2
  have hδc : δ • (c : A) ∈ fixedModule A ((s2.field L hLK : OpenSubgroup G) : Subgroup G) :=
    hδP' _ c.2
  set y' : fixedModule A ((s2.field L hLK : OpenSubgroup G) : Subgroup G) :=
    ⟨φ • (x'' : A), hφx''⟩ / x'' / (⟨δ • (c : A), hδc⟩ / c) with hy'def
  have hNy' : norm A ((s1.field L hLK : OpenSubgroup G) : Subgroup G)
      ((s2.field L hLK : OpenSubgroup G) : Subgroup G) y' = 1 := by
    apply Subtype.ext
    rw [hT]
    simp only [hy'def, Subgroup.coe_div, OneMemClass.coe_one, smul_div', Finset.prod_div_distrib]
    have e1 : ∏ i : Fin g, s1.elt ^ (i : ℕ) • φ • (x'' : A) = φ • x := by
      rw [hxN, Finset.smul_prod']
      refine Finset.prod_congr rfl fun i _ => ?_
      simpa using hcommφ i 1 (x'' : A)
    have e2 : ∏ i : Fin g, s1.elt ^ (i : ℕ) • δ • (c : A) = δ • a := by
      rw [haN, Finset.smul_prod']
      exact Finset.prod_congr rfl fun i _ => hcommδ i _ (hP'J _ c.2)
    rw [e1, e2, ← hxN, ← haN, hrel, div_self']
  obtain ⟨b, -, hb⟩ := D.exists_units_eq_smul_div hax hP'P hu hrelψ hNy'

  set Tb : A := ∏ j : Fin s1.deg, φ ^ (j : ℕ) • (b : A) with hTbdef
  have hTbP' : Tb ∈ fixedModule A ((s2.field L hLK : OpenSubgroup G) : Subgroup G) :=
    Subgroup.prod_mem _ fun j _ => hφP' j _ b.2
  have htele : φ • Tb / Tb = s1.elt • (b : A) / b := by
    rw [hTbdef, Finset.smul_prod', h1]
    simp only [Fin.prod_univ_eq_prod_range (fun j => φ • φ ^ j • (b : A)),
      Fin.prod_univ_eq_prod_range (fun j => φ ^ j • (b : A))]
    have hs := Finset.prod_range_succ (fun j => φ ^ j • (b : A)) s1.deg
    have hs' := Finset.prod_range_succ' (fun j => φ ^ j • (b : A)) s1.deg
    simp only [pow_zero, one_smul] at hs'
    have : ∏ j ∈ Finset.range s1.deg, φ • φ ^ j • (b : A) =
        ∏ j ∈ Finset.range s1.deg, φ ^ (j + 1) • (b : A) := by
      refine Finset.prod_congr rfl fun j _ => ?_
      rw [smul_smul, ← pow_succ']
    rw [this, div_eq_div_iff_mul_eq_mul, ← hs', hs, mul_comm]
  set x' : A := (x'' : A) / Tb with hx'def
  have hx'P' : x' ∈ fixedModule A ((s2.field L hLK : OpenSubgroup G) : Subgroup G) :=
    Subgroup.div_mem _ x''.2 hTbP'
  have hx'J := hP'J _ hx'P'
  have hrel' : φ • x' = x' * (δ • (c : A) / c) := by
    have hy'v : (y' : A) = φ • (x'' : A) / x'' / (δ • (c : A) / c) := by
      simp [hy'def]
    have e : φ • (x'' : A) / x'' = (s1.elt • (b : A) / b) * (δ • (c : A) / c) := by
      rw [← hb, hy'v, div_mul_cancel]
    have e2 : φ • Tb = Tb * (s1.elt • (b : A) / b) := by
      rw [← htele, mul_div_cancel]
    rw [hx'def, smul_div', e2]
    have e3 : φ • (x'' : A) = x'' * ((s1.elt • (b : A) / b) * (δ • (c : A) / c)) := by
      rw [← e, mul_div_cancel]
    rw [e3, mul_div_mul_comm, mul_div_cancel_left]

  set w : A := (norm A ((K : Subgroup G) ⊓ D.deg.ker) ((L : Subgroup G) ⊓ D.deg.ker) ⟨x', hx'J⟩ : A)
    with hwdef
  have := normal_inf_ker (D := D) hLK
  have hcJ := hP'J _ c.2
  have hwφ : φ • w = w := by
    rw [hwdef, smul_norm_inf_ker hLK hφK]
    have e : (⟨φ • x', smul_mem_fixedModule_inf_ker hLK hφK hx'J⟩ :
        fixedModule A ((L : Subgroup G) ⊓ D.deg.ker)) =
        ⟨x', hx'J⟩ * (⟨δ • (c : A), hδJ _ hcJ⟩ / ⟨c, hcJ⟩) := by
      ext
      simp [hrel']
    rw [e, map_mul, map_div, norm_smul (K := (K : Subgroup G) ⊓ D.deg.ker)
      (L := (L : Subgroup G) ⊓ D.deg.ker) ⟨δ, hδ⟩ ⟨(c : A), hcJ⟩ (hδJ _ hcJ), div_self', mul_one]
  have hwK : w ∈ fixedModule A (K : Subgroup G) :=
    mem_fixedModule_of_smul_eq K hφK hdφ (norm _ _ _ _).2 hwφ

  have hbJ := hP'J _ b.2
  have hNb := coe_norm_field_eq hLK s2 hφK hdφ b
  refine ⟨⟨w, fixedModule_anti hLK hwK⟩ * norm A (L : Subgroup G)
    ((s2.field L hLK : OpenSubgroup G) : Subgroup G) b, ?_⟩
  have hψK : ∀ i : ℕ, s1.elt ^ i ∈ (K : Subgroup G) := fun i => K.pow_mem s1.mem i
  have hx''eq : (x'' : A) = x' * Tb := by rw [hx'def, div_mul_cancel]
  have hTbJ := hP'J _ hTbP'
  have hNTb : (norm A ((K : Subgroup G) ⊓ D.deg.ker) ((L : Subgroup G) ⊓ D.deg.ker) ⟨Tb, hTbJ⟩ : A) =
      ∏ j : Fin s1.deg, φ ^ (j : ℕ) •
        (norm A ((K : Subgroup G) ⊓ D.deg.ker) ((L : Subgroup G) ⊓ D.deg.ker) ⟨b, hbJ⟩ : A) := by
    have hmemj : ∀ j : Fin s1.deg, φ ^ (j : ℕ) • (b : A) ∈ fixedModule A ((L : Subgroup G) ⊓ D.deg.ker) :=
      fun j => hφjJ j _ hbJ
    rw [show (⟨Tb, hTbJ⟩ : fixedModule A ((L : Subgroup G) ⊓ D.deg.ker)) =
        ⟨∏ j : Fin s1.deg, φ ^ (j : ℕ) • (b : A), Subgroup.prod_mem _ fun j _ => hmemj j⟩ from rfl,
      coe_norm_inf_ker_prod Finset.univ _ hmemj]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [smul_norm_inf_ker hLK (K.pow_mem hφK j)]
  have hNx : (norm A ((K : Subgroup G) ⊓ D.deg.ker) ((L : Subgroup G) ⊓ D.deg.ker)
      ⟨x, fixedModule_anti le_frobeniusClosure hx⟩ : A) =
      w ^ g * ∏ i : Fin g, s1.elt ^ (i : ℕ) •
        (norm A ((K : Subgroup G) ⊓ D.deg.ker) ((L : Subgroup G) ⊓ D.deg.ker) ⟨Tb, hTbJ⟩ : A) := by
    have hmemi : ∀ i : Fin g, s1.elt ^ (i : ℕ) • (x'' : A) ∈
        fixedModule A ((L : Subgroup G) ⊓ D.deg.ker) :=
      fun i => smul_mem_fixedModule_inf_ker hLK (hψK i) (hP'J _ x''.2)
    have e1 : (⟨x, fixedModule_anti le_frobeniusClosure hx⟩ :
        fixedModule A ((L : Subgroup G) ⊓ D.deg.ker)) =
        ⟨∏ i : Fin g, s1.elt ^ (i : ℕ) • (x'' : A), Subgroup.prod_mem _ fun i _ => hmemi i⟩ :=
      Subtype.ext hxN
    rw [e1, coe_norm_inf_ker_prod Finset.univ _ hmemi]
    have e2 : ∀ i : Fin g, (norm A ((K : Subgroup G) ⊓ D.deg.ker) ((L : Subgroup G) ⊓ D.deg.ker)
        ⟨s1.elt ^ (i : ℕ) • (x'' : A), hmemi i⟩ : A) =
        w * s1.elt ^ (i : ℕ) •
          (norm A ((K : Subgroup G) ⊓ D.deg.ker) ((L : Subgroup G) ⊓ D.deg.ker) ⟨Tb, hTbJ⟩ : A) := by
      intro i
      have h3 := smul_norm_inf_ker hLK (hψK i) ⟨(x'' : A), hP'J _ x''.2⟩
      rw [← h3]
      have e4 : (⟨(x'' : A), hP'J _ x''.2⟩ : fixedModule A ((L : Subgroup G) ⊓ D.deg.ker)) =
          ⟨x' * Tb, Subgroup.mul_mem _ hx'J hTbJ⟩ := Subtype.ext hx''eq
      rw [e4, coe_norm_inf_ker_mul hx'J hTbJ, smul_mul', ← hwdef, hwK _ (hψK i)]
    rw [Finset.prod_congr rfl fun i _ => e2 i, Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin]
  rw [map_mul, Subgroup.coe_mul, coe_norm_of_mem hLK hwK,
    norm_norm (fun y hy => hP'L hy) (fun y hy => hLK hy) b, hNb, hNx, hNTb]
  congr 1
  simp_rw [Finset.smul_prod', smul_smul, h1, ← pow_mul, ← pow_add]
  rw [Fin.prod_univ_eq_prod_range (fun m => φ ^ m • _) s2.deg, hdeg,
    ← prod_range_prod_range_eq _ g s1.deg]
  simp only [Finset.prod_range]

end Key

end ClassFieldData

end Sec_ALR_KeyLemma

section Sec_ALR_Multiplicative

open ProfiniteInteger

namespace ClassFieldData

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] {A : Type*} [CommGroup A] [MulDistribMulAction G A]
  {D : ClassFieldData G A} {K L : OpenSubgroup G}

namespace FrobeniusLift

omit [TotallyDisconnectedSpace G] in

def mul (s t : D.FrobeniusLift K) : D.FrobeniusLift K where
  elt := s.elt * t.elt
  mem := K.mul_mem s.mem t.mem
  deg := s.deg + t.deg
  deg_pos := Nat.add_pos_left s.deg_pos _
  deg_eq := by
    rw [map_mul, s.deg_eq, t.deg_eq, ← ofAdd_add]
    push_cast
    ring_nf

omit [TotallyDisconnectedSpace G] in

def ofDegOne {φ : G} (hφK : φ ∈ (K : Subgroup G))
    (hdφ : D.deg φ = Multiplicative.ofAdd (inertiaDegree D.deg K : ℤ̂)) : D.FrobeniusLift K where
  elt := φ
  mem := hφK
  deg := 1
  deg_pos := Nat.one_pos
  deg_eq := by rw [hdφ, one_mul]

variable (hLK : L ≤ K) [((L : Subgroup G).subgroupOf K).Normal]

theorem field_congr {s t : D.FrobeniusLift K} (h : s.elt = t.elt) :
    s.field L hLK = t.field L hLK := by
  apply OpenSubgroup.toSubgroup_injective
  show frobeniusClosure D.deg L s.elt = frobeniusClosure D.deg L t.elt
  rw [h]

theorem relInertiaDegree_field (s : D.FrobeniusLift K) :
    relInertiaDegree D.deg K (s.field L hLK) = s.deg := by
  have h := inertiaDegree_eq_mul D.surjective_deg (K := (K : Subgroup G))
    (L := ((s.field L hLK : OpenSubgroup G) : Subgroup G)) (fun x hx => s.field_le hLK hx)
  rw [s.inertiaDegree_field hLK] at h
  exact (Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero (D.inertiaDegree_ne_zero K)) h).symm

end FrobeniusLift

variable (hLK : L ≤ K) [((L : Subgroup G).subgroupOf K).Normal]

theorem recFrob_congr {s t : D.FrobeniusLift K} (h : s.elt = t.elt) :
    D.recFrob L hLK s = D.recFrob L hLK t := by
  unfold recFrob
  rw [FrobeniusLift.field_congr hLK h]

theorem valuation_norm_prime (s : D.FrobeniusLift K)
    {π : fixedModule A ((s.field L hLK : OpenSubgroup G) : Subgroup G)}
    (hπ : D.valuation (s.field L hLK) π = Multiplicative.ofAdd 1) :
    D.valuation K (norm A (K : Subgroup G) ((s.field L hLK : OpenSubgroup G) : Subgroup G) π) =
      Multiplicative.ofAdd (s.deg : ℤ̂) := by
  rw [D.valuation_norm (s.field_le hLK), hπ, FrobeniusLift.relInertiaDegree_field, ← ofAdd_nsmul,
    nsmul_one]

section DegOne

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]
  [((L : Subgroup G).subgroupOf K).Normal] in

theorem smul_prod_pow_div (φ : G) (y : A) (n : ℕ) :
    φ • (∏ ν : Fin n, φ ^ (ν : ℕ) • y) / ∏ ν : Fin n, φ ^ (ν : ℕ) • y = φ ^ n • y / y := by
  rw [Finset.smul_prod']
  simp only [Fin.prod_univ_eq_prod_range (fun j => φ • φ ^ j • y),
    Fin.prod_univ_eq_prod_range (fun j => φ ^ j • y)]
  have hs := Finset.prod_range_succ (fun j => φ ^ j • y) n
  have hs' := Finset.prod_range_succ' (fun j => φ ^ j • y) n
  simp only [pow_zero, one_smul] at hs'
  have : ∏ j ∈ Finset.range n, φ • φ ^ j • y = ∏ j ∈ Finset.range n, φ ^ (j + 1) • y := by
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [smul_smul, ← pow_succ']
  rw [this, div_eq_div_iff_mul_eq_mul, ← hs', hs, mul_comm]

omit [TotallyDisconnectedSpace G] in

theorem valuation_eq_of_inf_ker_eq {S P : OpenSubgroup G}
    (h : (S : Subgroup G) ⊓ D.deg.ker = (P : Subgroup G) ⊓ D.deg.ker) {y : A}
    (hyS : y ∈ fixedModule A (S : Subgroup G)) (hyP : y ∈ fixedModule A (P : Subgroup G)) :
    D.valuation P ⟨y, hyP⟩ = D.valuation S ⟨y, hyS⟩ := by
  set M : OpenSubgroup G := S ⊓ P
  have hMS : M ≤ S := inf_le_left
  have hMP : M ≤ P := inf_le_right
  have heS : relRamificationIndex D.deg S M = 1 :=
    isUnramified_iff.2 fun x hx => ⟨hx.1, (h.le hx).1⟩
  have heP : relRamificationIndex D.deg P M = 1 :=
    isUnramified_iff.2 fun x hx => ⟨(h.ge hx).1, hx.1⟩
  have h1 := D.valuation_of_mem hMS hyS
  have h2 := D.valuation_of_mem hMP hyP
  rw [heS, pow_one] at h1
  rw [heP, pow_one] at h2
  rw [← h1, ← h2]

theorem recFrob_mul_ofDegOne (hax : ClassFieldAxiom G A) [IsDiscreteModule G A]
    (s : D.FrobeniusLift K) {φ : G} (hφK : φ ∈ (K : Subgroup G))
    (hdφ : D.deg φ = Multiplicative.ofAdd (inertiaDegree D.deg K : ℤ̂)) :
    D.recFrob L hLK (s.mul (FrobeniusLift.ofDegOne hφK hdφ)) =
      D.recFrob L hLK s * D.recFrob L hLK (FrobeniusLift.ofDegOne hφK hdφ) := by
  classical
  set t := FrobeniusLift.ofDegOne (D := D) hφK hdφ with htdef
  set u := s.mul t with hudef
  set n := s.deg with hndef
  obtain ⟨π1, hπ1⟩ := D.exists_prime (s.field L hLK)
  obtain ⟨π2, hπ2⟩ := D.exists_prime (t.field L hLK)
  obtain ⟨π3, hπ3⟩ := D.exists_prime (u.field L hLK)
  rw [← D.mk_norm_eq_recFrob hLK hax s hπ1, ← D.mk_norm_eq_recFrob hLK hax t hπ2,
    ← D.mk_norm_eq_recFrob hLK hax u hπ3, ← QuotientGroup.mk_mul, QuotientGroup.eq]

  have hJ : ∀ (v : D.FrobeniusLift K) (y : A),
      y ∈ fixedModule A ((v.field L hLK : OpenSubgroup G) : Subgroup G) →
        y ∈ fixedModule A ((L : Subgroup G) ⊓ D.deg.ker) :=
    fun v y hy => fixedModule_anti le_frobeniusClosure hy
  have hφνJ : ∀ (ν : ℕ) (y : A), y ∈ fixedModule A ((L : Subgroup G) ⊓ D.deg.ker) →
      φ ^ ν • y ∈ fixedModule A ((L : Subgroup G) ⊓ D.deg.ker) :=
    fun ν y hy => smul_mem_fixedModule_inf_ker hLK (K.pow_mem hφK ν) hy
  have hσπ1 : s.elt • (π1 : A) = π1 := π1.2 _ (s.elt_mem_field hLK)
  have hφπ2 : φ • (π2 : A) = π2 := π2.2 _ (t.elt_mem_field hLK)
  have hσφπ3 : (s.elt * φ) • (π3 : A) = π3 := π3.2 _ (u.elt_mem_field hLK)
  set T1 : A := ∏ ν : Fin n, φ ^ (ν : ℕ) • (π1 : A) with hT1
  set T3 : A := ∏ ν : Fin (n + 1), φ ^ (ν : ℕ) • (π3 : A) with hT3
  set x : A := T1 * φ ^ n • (π2 : A) / T3 with hxdef
  set a : A := (π1 : A) / π3 with hadef
  have hT1J : T1 ∈ fixedModule A ((L : Subgroup G) ⊓ D.deg.ker) :=
    Subgroup.prod_mem _ fun ν _ => hφνJ ν _ (hJ s _ π1.2)
  have hT3J : T3 ∈ fixedModule A ((L : Subgroup G) ⊓ D.deg.ker) :=
    Subgroup.prod_mem _ fun ν _ => hφνJ ν _ (hJ u _ π3.2)
  have hπ2J : φ ^ n • (π2 : A) ∈ fixedModule A ((L : Subgroup G) ⊓ D.deg.ker) :=
    hφνJ n _ (hJ t _ π2.2)
  have hxJ : x ∈ fixedModule A ((L : Subgroup G) ⊓ D.deg.ker) :=
    Subgroup.div_mem _ (Subgroup.mul_mem _ hT1J hπ2J) hT3J

  have hNprod : ∀ (m : ℕ) (y : A) (hy : y ∈ fixedModule A ((L : Subgroup G) ⊓ D.deg.ker)),
      (norm A ((K : Subgroup G) ⊓ D.deg.ker) ((L : Subgroup G) ⊓ D.deg.ker)
        ⟨∏ ν : Fin m, φ ^ (ν : ℕ) • y, Subgroup.prod_mem _ fun ν _ => hφνJ ν y hy⟩ : A) =
        ∏ ν : Fin m, φ ^ (ν : ℕ) •
          (norm A ((K : Subgroup G) ⊓ D.deg.ker) ((L : Subgroup G) ⊓ D.deg.ker) ⟨y, hy⟩ : A) := by
    intro m y hy
    rw [coe_norm_inf_ker_prod Finset.univ _ (fun ν : Fin m => hφνJ (ν : ℕ) y hy)]
    refine Finset.prod_congr rfl fun ν _ => ?_
    rw [smul_norm_inf_ker hLK (K.pow_mem hφK ν)]
  have hN1 : (norm A (K : Subgroup G) ((s.field L hLK : OpenSubgroup G) : Subgroup G) π1 : A) =
      (norm A ((K : Subgroup G) ⊓ D.deg.ker) ((L : Subgroup G) ⊓ D.deg.ker) ⟨T1, hT1J⟩ : A) := by
    exact (coe_norm_field_eq hLK s hφK hdφ π1).trans (hNprod _ _ _).symm
  have hN3 : (norm A (K : Subgroup G) ((u.field L hLK : OpenSubgroup G) : Subgroup G) π3 : A) =
      (norm A ((K : Subgroup G) ⊓ D.deg.ker) ((L : Subgroup G) ⊓ D.deg.ker) ⟨T3, hT3J⟩ : A) := by
    exact (coe_norm_field_eq hLK u hφK hdφ π3).trans (hNprod _ _ _).symm
  have hN2K := (norm A (K : Subgroup G) ((t.field L hLK : OpenSubgroup G) : Subgroup G) π2).2
  have hN2 : (norm A (K : Subgroup G) ((t.field L hLK : OpenSubgroup G) : Subgroup G) π2 : A) =
      (norm A ((K : Subgroup G) ⊓ D.deg.ker) ((L : Subgroup G) ⊓ D.deg.ker)
        ⟨φ ^ n • (π2 : A), hπ2J⟩ : A) := by
    have h0 : (norm A (K : Subgroup G) ((t.field L hLK : OpenSubgroup G) : Subgroup G) π2 : A) =
        (norm A ((K : Subgroup G) ⊓ D.deg.ker) ((L : Subgroup G) ⊓ D.deg.ker)
          ⟨(π2 : A), hJ t _ π2.2⟩ : A) := by
      have h0' : (norm A (K : Subgroup G) ((t.field L hLK : OpenSubgroup G) : Subgroup G) π2 : A) =
          ∏ ν : Fin 1, φ ^ (ν : ℕ) • (norm A ((K : Subgroup G) ⊓ D.deg.ker)
            ((L : Subgroup G) ⊓ D.deg.ker) ⟨(π2 : A), hJ t _ π2.2⟩ : A) :=
        coe_norm_field_eq hLK t hφK hdφ π2
      rw [Fin.prod_univ_one] at h0'
      simpa using h0'
    calc (norm A (K : Subgroup G) ((t.field L hLK : OpenSubgroup G) : Subgroup G) π2 : A)
        = φ ^ n • (norm A (K : Subgroup G) ((t.field L hLK : OpenSubgroup G) : Subgroup G) π2 : A) :=
          (hN2K _ (K.pow_mem hφK n)).symm
      _ = φ ^ n • (norm A ((K : Subgroup G) ⊓ D.deg.ker) ((L : Subgroup G) ⊓ D.deg.ker)
            ⟨(π2 : A), hJ t _ π2.2⟩ : A) := by rw [h0]
      _ = _ := smul_norm_inf_ker hLK (K.pow_mem hφK n) _
  have hNx : (norm A ((K : Subgroup G) ⊓ D.deg.ker) ((L : Subgroup G) ⊓ D.deg.ker) ⟨x, hxJ⟩ : A) =
      (norm A (K : Subgroup G) ((s.field L hLK : OpenSubgroup G) : Subgroup G) π1 : A) *
        norm A (K : Subgroup G) ((t.field L hLK : OpenSubgroup G) : Subgroup G) π2 /
          norm A (K : Subgroup G) ((u.field L hLK : OpenSubgroup G) : Subgroup G) π3 := by
    rw [hN1, hN2, hN3]
    have e : (⟨x, hxJ⟩ : fixedModule A ((L : Subgroup G) ⊓ D.deg.ker)) =
        ⟨T1, hT1J⟩ * ⟨φ ^ n • (π2 : A), hπ2J⟩ / ⟨T3, hT3J⟩ := rfl
    rw [e, map_div, map_mul]
    rfl

  have hst : ∀ y : A, IsOpen (MulAction.stabilizer G y : Set G) :=
    fun y => IsDiscreteModule.isOpen_stabilizer y
  have hopen : IsOpen ((L : Set G) ∩ (MulAction.stabilizer G (π1 : A) : Set G) ∩
      (MulAction.stabilizer G (π2 : A) : Set G) ∩ (MulAction.stabilizer G (π3 : A) : Set G)) :=
    ((L.isOpen.inter (hst _)).inter (hst _)).inter (hst _)
  have hone : (1 : G) ∈ (L : Set G) ∩ (MulAction.stabilizer G (π1 : A) : Set G) ∩
      (MulAction.stabilizer G (π2 : A) : Set G) ∩ (MulAction.stabilizer G (π3 : A) : Set G) :=
    ⟨⟨⟨L.one_mem, Subgroup.one_mem _⟩, Subgroup.one_mem _⟩, Subgroup.one_mem _⟩
  obtain ⟨U, hU⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hopen hone
  have : Finite (G ⧸ U.toSubgroup) := Subgroup.quotient_finite_of_isOpen _ U.isOpen'
  set D0 := orderOf (φ : G ⧸ U.toSubgroup) with hD0def
  have hD0 : 0 < D0 := orderOf_pos _
  have hφD0U : φ ^ D0 ∈ U.toSubgroup := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, hD0def, pow_orderOf_eq_one]
  obtain ⟨⟨⟨hψL, hψ1⟩, hψ2⟩, hψ3⟩ := hU hφD0U
  have hψπ1 : φ ^ D0 • (π1 : A) = π1 := MulAction.mem_stabilizer_iff.1 hψ1
  have hψπ2 : φ ^ D0 • (π2 : A) = π2 := MulAction.mem_stabilizer_iff.1 hψ2
  have hψπ3 : φ ^ D0 • (π3 : A) = π3 := MulAction.mem_stabilizer_iff.1 hψ3
  set g := (L : Subgroup G).relIndex K with hgdef
  have hg : 0 < g := Nat.pos_of_ne_zero (Subgroup.FiniteIndex.index_ne_zero
    (H := (L : Subgroup G).subgroupOf K))
  set s1 := powLift hφK hdφ D0 hD0 with hs1
  set s2 := powLift hφK hdφ (g * D0) (Nat.mul_pos hg hD0) with hs2
  have hfix : ∀ (ν : ℕ) (y : A), φ ^ D0 • y = y → φ ^ D0 • φ ^ ν • y = φ ^ ν • y := by
    intro ν y hy
    rw [smul_smul, ← pow_add, add_comm, pow_add, mul_smul, hy]
  have hT1ψ : φ ^ D0 • T1 = T1 := by
    rw [hT1, Finset.smul_prod']
    exact Finset.prod_congr rfl fun ν _ => hfix ν _ hψπ1
  have hT3ψ : φ ^ D0 • T3 = T3 := by
    rw [hT3, Finset.smul_prod']
    exact Finset.prod_congr rfl fun ν _ => hfix ν _ hψπ3
  have hxP : x ∈ fixedModule A ((s1.field L hLK : OpenSubgroup G) : Subgroup G) := by
    rw [FrobeniusLift.coe_field, mem_fixedModule_frobeniusClosure]
    refine ⟨hxJ, ?_⟩
    show φ ^ D0 • x = x
    rw [hxdef, smul_div', smul_mul', hT1ψ, hfix n _ hψπ2, hT3ψ]
  have hπ1P : (π1 : A) ∈ fixedModule A ((s1.field L hLK : OpenSubgroup G) : Subgroup G) := by
    rw [FrobeniusLift.coe_field, mem_fixedModule_frobeniusClosure]
    exact ⟨hJ s _ π1.2, hψπ1⟩
  have hπ3P : (π3 : A) ∈ fixedModule A ((s1.field L hLK : OpenSubgroup G) : Subgroup G) := by
    rw [FrobeniusLift.coe_field, mem_fixedModule_frobeniusClosure]
    exact ⟨hJ u _ π3.2, hψπ3⟩
  have haP : a ∈ fixedModule A ((s1.field L hLK : OpenSubgroup G) : Subgroup G) :=
    Subgroup.div_mem _ hπ1P hπ3P

  have hπP : ∀ (v : D.FrobeniusLift K) (y : A)
      (hy : y ∈ fixedModule A ((v.field L hLK : OpenSubgroup G) : Subgroup G))
      (hyP : y ∈ fixedModule A ((s1.field L hLK : OpenSubgroup G) : Subgroup G)),
      D.valuation (s1.field L hLK) ⟨y, hyP⟩ = D.valuation (v.field L hLK) ⟨y, hy⟩ :=
    fun v y hy hyP => valuation_eq_of_inf_ker_eq
      ((v.field_inf_ker hLK).trans (s1.field_inf_ker hLK).symm) hy hyP
  have hau : D.valuation (s1.field L hLK) ⟨a, haP⟩ = 1 := by
    have e : (⟨a, haP⟩ : fixedModule A ((s1.field L hLK : OpenSubgroup G) : Subgroup G)) =
        ⟨(π1 : A), hπ1P⟩ / ⟨(π3 : A), hπ3P⟩ := rfl
    rw [e, map_div, hπP s _ π1.2 hπ1P, hπP u _ π3.2 hπ3P]
    simp [hπ1, hπ3]
  set N : fixedModule A (K : Subgroup G) :=
    norm A (K : Subgroup G) ((s.field L hLK : OpenSubgroup G) : Subgroup G) π1 *
      norm A (K : Subgroup G) ((t.field L hLK : OpenSubgroup G) : Subgroup G) π2 /
        norm A (K : Subgroup G) ((u.field L hLK : OpenSubgroup G) : Subgroup G) π3 with hNdef
  have hNcoe : (norm A ((K : Subgroup G) ⊓ D.deg.ker) ((L : Subgroup G) ⊓ D.deg.ker) ⟨x, hxJ⟩ : A) =
      (N : A) := by
    rw [hNx]
    rfl
  have hvN : D.valuation K N = 1 := by
    rw [hNdef, map_div, map_mul, valuation_norm_prime hLK s hπ1, valuation_norm_prime hLK t hπ2,
      valuation_norm_prime hLK u hπ3, ← ofAdd_add, ← ofAdd_sub]
    show Multiplicative.ofAdd ((s.deg : ℤ̂) + ((1 : ℕ) : ℤ̂) - ((s.deg + 1 : ℕ) : ℤ̂)) = 1
    push_cast
    simp
  have hxu : D.valuation (s1.field L hLK) ⟨x, hxP⟩ = 1 := by
    have hNP : norm A (K : Subgroup G) ((s1.field L hLK : OpenSubgroup G) : Subgroup G) ⟨x, hxP⟩ =
        N ^ D0 := by
      apply Subtype.ext
      rw [coe_norm_field_eq hLK s1 hφK hdφ ⟨x, hxP⟩, SubmonoidClass.coe_pow]
      have h' : ∀ m : Fin s1.deg, φ ^ (m : ℕ) •
          (norm A ((K : Subgroup G) ⊓ D.deg.ker) ((L : Subgroup G) ⊓ D.deg.ker)
            ⟨x, fixedModule_anti le_frobeniusClosure hxP⟩ : A) = (N : A) := by
        intro m
        rw [show (⟨x, fixedModule_anti le_frobeniusClosure hxP⟩ :
            fixedModule A ((L : Subgroup G) ⊓ D.deg.ker)) = ⟨x, hxJ⟩ from rfl, hNcoe]
        exact N.2 _ (K.pow_mem hφK _)
      rw [Finset.prod_congr rfl fun m _ => h' m, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin]
      rfl
    have hv := D.valuation_norm (s1.field_le hLK) ⟨x, hxP⟩
    rw [hNP, map_pow, hvN, one_pow, FrobeniusLift.relInertiaDegree_field] at hv
    exact (ProfiniteInteger.pow_left_inj (n := s1.deg) hD0.ne').1 (by rw [one_pow]; exact hv.symm)

  set δ : G := φ ^ n * s.elt⁻¹ with hδdef
  have hδ : δ ∈ (K : Subgroup G) ⊓ D.deg.ker := by
    refine ⟨K.mul_mem (K.pow_mem hφK n) (K.inv_mem s.mem), ?_⟩
    show D.deg (φ ^ n * s.elt⁻¹) = 1
    rw [map_mul, map_inv, map_pow, hdφ, s.deg_eq, ← ofAdd_nsmul, ← ofAdd_neg, ← ofAdd_add]
    rw [hndef]
    push_cast
    rw [nsmul_eq_mul, add_neg_cancel, ofAdd_zero]
  have hδπ1 : δ • (π1 : A) = φ ^ n • (π1 : A) := by
    rw [hδdef, mul_smul, inv_smul_eq_iff.2 hσπ1.symm]
  have hφπ3 : φ • (π3 : A) = s.elt⁻¹ • (π3 : A) := by
    rw [eq_inv_smul_iff, ← mul_smul]
    exact hσφπ3
  have hδπ3 : δ • (π3 : A) = φ ^ (n + 1) • (π3 : A) := by
    rw [hδdef, mul_smul, ← hφπ3, ← mul_smul, ← pow_succ]
  have e2 : φ • φ ^ n • (π2 : A) = φ ^ n • (π2 : A) := by
    rw [smul_smul, ← pow_succ', pow_succ, mul_smul, hφπ2]
  have L1 : φ • x / x = (φ • T1 / T1) / (φ • T3 / T3) := by
    rw [hxdef, smul_div', smul_mul', e2, div_div_div_comm, mul_div_mul_comm, div_self', mul_one]
  have R1 : δ • a / a = (φ ^ n • (π1 : A) / π1) / (φ ^ (n + 1) • (π3 : A) / π3) := by
    rw [hadef, smul_div', hδπ1, hδπ3, div_div_div_comm]
  have hrel : φ • x / x = δ • a / a := by
    rw [L1, R1, hT1, hT3, smul_prod_pow_div, smul_prod_pow_div]

  obtain ⟨b, hb⟩ := exists_norm_eq_norm_inf_ker hLK hax hφK hdφ s1 s2 rfl hψL
    (by show φ ^ (g * D0) = (φ ^ D0) ^ g; rw [mul_comm, pow_mul]) rfl hxP haP hxu hau hδ hrel
  refine ⟨b, Subtype.ext ?_⟩
  rw [hb, show (⟨x, fixedModule_anti le_frobeniusClosure hxP⟩ :
      fixedModule A ((L : Subgroup G) ⊓ D.deg.ker)) = ⟨x, hxJ⟩ from rfl, hNcoe, hNdef]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_div]
  rw [div_eq_inv_mul]

end DegOne

section General

omit [TotallyDisconnectedSpace G] in

theorem exists_deg_eq (K : OpenSubgroup G) :
    ∃ φ ∈ (K : Subgroup G), D.deg φ = Multiplicative.ofAdd (inertiaDegree D.deg K : ℤ̂) := by
  obtain ⟨φ, hφ⟩ := D.relDeg_surjective K (Multiplicative.ofAdd 1)
  refine ⟨φ, φ.2, ?_⟩
  rw [← D.relDeg_pow, hφ, ← ofAdd_nsmul, nsmul_one]

theorem recFrob_mul (hax : ClassFieldAxiom G A) [IsDiscreteModule G A] (s t : D.FrobeniusLift K) :
    D.recFrob L hLK (s.mul t) = D.recFrob L hLK s * D.recFrob L hLK t := by
  obtain ⟨φ, hφK, hdφ⟩ := exists_deg_eq (D := D) K
  suffices h : ∀ (m : ℕ) (s t : D.FrobeniusLift K), t.deg = m + 1 →
      D.recFrob L hLK (s.mul t) = D.recFrob L hLK s * D.recFrob L hLK t by
    obtain ⟨m, hm⟩ : ∃ m, t.deg = m + 1 := ⟨t.deg - 1, by have := t.deg_pos; omega⟩
    exact h m s t hm
  intro m
  induction m with
  | zero =>
    intro s t ht
    have hdt : D.deg t.elt = Multiplicative.ofAdd (inertiaDegree D.deg K : ℤ̂) := by
      rw [t.deg_eq, ht, zero_add, one_mul]
    rw [recFrob_congr hLK (s := s.mul t) (t := s.mul (FrobeniusLift.ofDegOne t.mem hdt)) rfl,
      recFrob_congr hLK (s := t) (t := FrobeniusLift.ofDegOne t.mem hdt) rfl]
    exact recFrob_mul_ofDegOne hLK hax s t.mem hdt
  | succ k ih =>
    intro s t ht
    set φ1 := FrobeniusLift.ofDegOne (D := D) hφK hdφ with hφ1
    let t' : D.FrobeniusLift K :=
      { elt := t.elt * φ⁻¹
        mem := K.mul_mem t.mem (K.inv_mem hφK)
        deg := k + 1
        deg_pos := Nat.succ_pos k
        deg_eq := by
          rw [map_mul, map_inv, t.deg_eq, hdφ, ht, ← ofAdd_neg, ← ofAdd_add]
          push_cast
          ring_nf }
    have h1 : D.recFrob L hLK (s.mul t) = D.recFrob L hLK ((s.mul t').mul φ1) :=
      recFrob_congr hLK (by simp [FrobeniusLift.mul, t', φ1, FrobeniusLift.ofDegOne, mul_assoc])
    have h2 : D.recFrob L hLK t = D.recFrob L hLK (t'.mul φ1) :=
      recFrob_congr hLK (by simp [FrobeniusLift.mul, t', φ1, FrobeniusLift.ofDegOne])
    rw [h1, h2, recFrob_mul_ofDegOne hLK hax _ hφK hdφ, recFrob_mul_ofDegOne hLK hax _ hφK hdφ,
      ih s t' rfl, mul_assoc]

end General

end ClassFieldData

end Sec_ALR_Multiplicative

section Sec_ALR_ReciprocityMap

open ProfiniteInteger

namespace ClassFieldData

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] {A : Type*} [CommGroup A] [MulDistribMulAction G A]
  {D : ClassFieldData G A} {K L : OpenSubgroup G}

variable (hLK : L ≤ K) [((L : Subgroup G).subgroupOf K).Normal]

include hLK in
omit [TotallyDisconnectedSpace G] [((L : Subgroup G).subgroupOf K).Normal] in

theorem exists_frobeniusLift {τ : G} (hτ : τ ∈ (K : Subgroup G)) :
    ∃ s : D.FrobeniusLift K, τ⁻¹ * s.elt ∈ (L : Subgroup G) := by
  obtain ⟨w, hw⟩ := mem_multiples.1 (toAdd_deg_mem_multiples (D := D) K hτ)
  set f' := relInertiaDegree D.deg K L with hf'def
  have hf' : 0 < f' := Nat.pos_of_ne_zero (D.relInertiaDegree_ne_zero hLK)
  set F : ℕ+ := ⟨f', hf'⟩ with hFdef
  set m : ℕ := (proj F w).val + f' with hmdef
  have hm : 0 < m := by omega
  have hmw : (m : ℤ̂) - w ∈ multiples f' := by
    have := (proj_eq_zero_iff (n := F) (x := (m : ℤ̂) - w)).1 (by
      rw [map_sub, map_natCast, hmdef, Nat.cast_add, ZMod.natCast_zmod_val]
      have : ((f' : ℕ) : ZMod F) = 0 := by
        rw [hFdef]
        exact ZMod.natCast_self f'
      rw [this, add_zero, sub_self])
    simpa [hFdef] using this
  obtain ⟨z, hz⟩ := mem_multiples.1 hmw
  have hfL := inertiaDegree_eq_mul D.surjective_deg (K := (K : Subgroup G)) (L := (L : Subgroup G)) hLK
  obtain ⟨ρ, hρL, hρ⟩ := (D.mem_map_deg_iff L).2 ⟨Multiplicative.ofAdd z, rfl⟩
  refine ⟨⟨τ * ρ, K.mul_mem hτ (hLK hρL), m, hm, ?_⟩, by simpa using hρL⟩
  apply Multiplicative.toAdd.injective
  rw [map_mul, toAdd_mul, hρ, toAdd_pow, toAdd_ofAdd, toAdd_ofAdd, hw, hfL]
  have hz' : (f' : ℤ̂) * z = m - w := by rw [← nsmul_eq_mul, ← hz]
  simp only [nsmul_eq_mul]
  push_cast
  linear_combination (inertiaDegree D.deg K : ℤ̂) * hz'

theorem recFrob_eq_one_of_mem (s : D.FrobeniusLift K) (hs : s.elt ∈ (L : Subgroup G)) :
    D.recFrob L hLK s = 1 := by
  have hle : s.field L hLK ≤ L := fun x hx => frobeniusClosure_le L.isClosed hs inf_le_left hx
  unfold recFrob primeNorm
  rw [QuotientGroup.eq_one_iff]
  exact ⟨norm A (L : Subgroup G) ((s.field L hLK : OpenSubgroup G) : Subgroup G) _,
    norm_norm (fun x hx => hle hx) (fun x hx => hLK hx) _⟩

theorem field_eq_of_mem (s t : D.FrobeniusLift K)
    (h : s.elt⁻¹ * t.elt ∈ (L : Subgroup G) ⊓ D.deg.ker) : s.field L hLK = t.field L hLK := by
  apply OpenSubgroup.toSubgroup_injective
  show frobeniusClosure D.deg L s.elt = frobeniusClosure D.deg L t.elt
  unfold frobeniusClosure
  congr 1
  apply le_antisymm
  · refine sup_le (Subgroup.zpowers_le.2 ?_) le_sup_right
    have : s.elt = t.elt * (s.elt⁻¹ * t.elt)⁻¹ := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))
      (Subgroup.mem_sup_right (Subgroup.inv_mem _ h))
  · refine sup_le (Subgroup.zpowers_le.2 ?_) le_sup_right
    have : t.elt = s.elt * (s.elt⁻¹ * t.elt) := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))
      (Subgroup.mem_sup_right h)

theorem recFrob_eq_of_mem_of_le (hax : ClassFieldAxiom G A) [IsDiscreteModule G A]
    (s t : D.FrobeniusLift K) (h : s.elt⁻¹ * t.elt ∈ (L : Subgroup G)) (hle : s.deg ≤ t.deg) :
    D.recFrob L hLK s = D.recFrob L hLK t := by
  rcases Nat.eq_or_lt_of_le hle with heq | hlt
  · have hker : s.elt⁻¹ * t.elt ∈ D.deg.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, s.deg_eq, t.deg_eq, heq, inv_mul_cancel]
    unfold recFrob
    rw [field_eq_of_mem hLK s t ⟨h, hker⟩]
  · let ρ : D.FrobeniusLift K :=
      { elt := s.elt⁻¹ * t.elt
        mem := K.mul_mem (K.inv_mem s.mem) t.mem
        deg := t.deg - s.deg
        deg_pos := by omega
        deg_eq := by
          apply Multiplicative.toAdd.injective
          rw [map_mul, map_inv, toAdd_mul, toAdd_inv, s.deg_eq, t.deg_eq, toAdd_ofAdd, toAdd_ofAdd,
            toAdd_ofAdd]
          push_cast [Nat.cast_sub hlt.le]
          ring }
    have hρ : D.recFrob L hLK ρ = 1 := recFrob_eq_one_of_mem hLK ρ h
    rw [recFrob_congr hLK (s := t) (t := s.mul ρ) (by simp [FrobeniusLift.mul, ρ]),
      recFrob_mul hLK hax, hρ, mul_one]

theorem recFrob_eq_of_mem (hax : ClassFieldAxiom G A) [IsDiscreteModule G A]
    (s t : D.FrobeniusLift K) (h : s.elt⁻¹ * t.elt ∈ (L : Subgroup G)) :
    D.recFrob L hLK s = D.recFrob L hLK t := by
  rcases le_total s.deg t.deg with hle | hle
  · exact recFrob_eq_of_mem_of_le hLK hax s t h hle
  · refine (recFrob_eq_of_mem_of_le hLK hax t s ?_ hle).symm
    have := L.inv_mem h
    simpa using this

section Map

noncomputable def liftOf (τ : (K : Subgroup G)) : D.FrobeniusLift K :=
  (exists_frobeniusLift hLK τ.2).choose

omit [TotallyDisconnectedSpace G] [((L : Subgroup G).subgroupOf K).Normal] in
theorem liftOf_spec (τ : (K : Subgroup G)) : (τ : G)⁻¹ * (liftOf (D := D) hLK τ).elt ∈ (L : Subgroup G) :=
  (exists_frobeniusLift hLK τ.2).choose_spec

omit [TotallyDisconnectedSpace G] [((L : Subgroup G).subgroupOf K).Normal] in

theorem mk_liftOf (τ : (K : Subgroup G)) :
    ((⟨(liftOf (D := D) hLK τ).elt, (liftOf (D := D) hLK τ).mem⟩ : (K : Subgroup G)) :
      (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) = (τ : (K : Subgroup G) ⧸ _) := by
  rw [eq_comm, QuotientGroup.eq, Subgroup.mem_subgroupOf]
  simpa using liftOf_spec hLK τ

variable (hax : ClassFieldAxiom G A) [IsDiscreteModule G A]

noncomputable def recHom : (K : Subgroup G) →* tateZero A (K : Subgroup G) (L : Subgroup G) where
  toFun τ := D.recFrob L hLK (liftOf hLK τ)
  map_one' := recFrob_eq_one_of_mem hLK _ (by simpa using liftOf_spec (D := D) hLK 1)
  map_mul' τ1 τ2 := by
    rw [← recFrob_mul hLK hax]
    apply recFrob_eq_of_mem hLK hax
    have h12 := mk_liftOf (D := D) hLK (τ1 * τ2)
    have h1 := mk_liftOf (D := D) hLK τ1
    have h2 := mk_liftOf (D := D) hLK τ2
    have key : ((⟨(liftOf (D := D) hLK (τ1 * τ2)).elt, (liftOf (D := D) hLK (τ1 * τ2)).mem⟩ :
        (K : Subgroup G)) : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) =
        ((⟨(liftOf (D := D) hLK τ1).elt * (liftOf (D := D) hLK τ2).elt,
          K.mul_mem (liftOf (D := D) hLK τ1).mem (liftOf (D := D) hLK τ2).mem⟩ : (K : Subgroup G)) :
            (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) := by
      rw [h12, QuotientGroup.mk_mul, ← h1, ← h2, ← QuotientGroup.mk_mul]
      rfl
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at key
    simpa [FrobeniusLift.mul] using key

theorem recHom_apply (τ : (K : Subgroup G)) :
    D.recHom hLK hax τ = D.recFrob L hLK (liftOf hLK τ) :=
  rfl

noncomputable def reciprocity :
    (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K →* tateZero A (K : Subgroup G) (L : Subgroup G) :=
  QuotientGroup.lift _ (D.recHom hLK hax) fun τ hτ => by
    rw [MonoidHom.mem_ker, recHom_apply]
    apply recFrob_eq_one_of_mem hLK
    have := L.mul_mem (Subgroup.mem_subgroupOf.1 hτ) (liftOf_spec (D := D) hLK τ)
    simpa using this

theorem reciprocity_mk (s : D.FrobeniusLift K) :
    D.reciprocity hLK hax ((⟨s.elt, s.mem⟩ : (K : Subgroup G)) :
      (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) = D.recFrob L hLK s := by
  show D.recHom hLK hax ⟨s.elt, s.mem⟩ = _
  rw [recHom_apply]
  apply recFrob_eq_of_mem hLK hax
  have := L.inv_mem (liftOf_spec (D := D) hLK ⟨s.elt, s.mem⟩)
  simpa using this

theorem reciprocity_mk_eq_norm (s : D.FrobeniusLift K)
    {π : fixedModule A ((s.field L hLK : OpenSubgroup G) : Subgroup G)}
    (hπ : D.valuation (s.field L hLK) π = Multiplicative.ofAdd 1) :
    D.reciprocity hLK hax ((⟨s.elt, s.mem⟩ : (K : Subgroup G)) :
      (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) =
      (QuotientGroup.mk (norm A (K : Subgroup G)
        ((s.field L hLK : OpenSubgroup G) : Subgroup G) π) :
          tateZero A (K : Subgroup G) (L : Subgroup G)) := by
  rw [reciprocity_mk, D.mk_norm_eq_recFrob hLK hax s hπ]

include hLK in
omit [IsDiscreteModule G A] [TotallyDisconnectedSpace G] [((L : Subgroup G).subgroupOf K).Normal] in

theorem exists_frobeniusLift_mk (q : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) :
    ∃ s : D.FrobeniusLift K,
      ((⟨s.elt, s.mem⟩ : (K : Subgroup G)) : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) = q := by
  induction q using QuotientGroup.induction_on with
  | H τ => exact ⟨liftOf hLK τ, mk_liftOf hLK τ⟩

end Map

end ClassFieldData

end Sec_ALR_ReciprocityMap

section Sec_ALR_Functoriality

open ProfiniteInteger

section Conj

variable {G : Type*} [Group G]

theorem map_conj_apply {M : Type*} [CommGroup M] (f : G →* M) (σ x : G) :
    f (σ * x * σ⁻¹) = f x := by
  rw [map_mul, map_mul, map_inv, mul_right_comm, mul_inv_cancel, one_mul]

theorem mem_map_conj {H : Subgroup G} {σ x : G} :
    x ∈ H.map (MulAut.conj σ).toMonoidHom ↔ σ⁻¹ * x * σ ∈ H := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [mul_assoc] using hy
  · intro h
    exact ⟨σ⁻¹ * x * σ, h, by simp [mul_assoc]⟩

theorem coe_map_conj (H : Subgroup G) (σ : G) :
    (H.map (MulAut.conj σ).toMonoidHom : Set G) = (fun x => σ⁻¹ * x * σ) ⁻¹' (H : Set G) := by
  ext x
  exact mem_map_conj

theorem inertiaDegree_map_conj (d : G →* Multiplicative ℤ̂) (K : Subgroup G) (σ : G) :
    inertiaDegree d (K.map (MulAut.conj σ).toMonoidHom) = inertiaDegree d K := by
  have h : d.comp (MulAut.conj σ).toMonoidHom = d := MonoidHom.ext fun x => map_conj_apply d σ x
  rw [inertiaDegree, inertiaDegree, Subgroup.map_map, h]

variable [TopologicalSpace G] [IsTopologicalGroup G]

theorem isClosed_map_conj {H : Subgroup G} (hH : IsClosed (H : Set G)) (σ : G) :
    IsClosed (H.map (MulAut.conj σ).toMonoidHom : Set G) := by
  rw [coe_map_conj]
  exact hH.preimage ((continuous_const.mul continuous_id).mul continuous_const)

theorem map_conj_frobeniusClosure (d : G →* Multiplicative ℤ̂) (L : Subgroup G) (x ρ : G) :
    (frobeniusClosure d L x).map (MulAut.conj ρ).toMonoidHom =
      frobeniusClosure d (L.map (MulAut.conj ρ).toMonoidHom) (ρ * x * ρ⁻¹) := by
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    refine frobeniusClosure_le ?_ ?_ ?_
    · exact isClosed_frobeniusClosure.preimage
        ((continuous_const.mul continuous_id).mul continuous_const)
    · exact mem_frobeniusClosure_self
    · intro y hy
      obtain ⟨hyL, hyk⟩ := Subgroup.mem_inf.1 hy
      rw [Subgroup.mem_comap]
      refine le_frobeniusClosure (Subgroup.mem_inf.2 ⟨⟨y, hyL, rfl⟩, ?_⟩)
      rw [MonoidHom.mem_ker] at hyk ⊢
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [map_conj_apply, hyk]
  · refine frobeniusClosure_le (isClosed_map_conj isClosed_frobeniusClosure ρ)
      ⟨x, mem_frobeniusClosure_self, rfl⟩ ?_
    intro y hy
    obtain ⟨hyL, hyk⟩ := Subgroup.mem_inf.1 hy
    rw [mem_map_conj] at hyL ⊢
    refine le_frobeniusClosure (Subgroup.mem_inf.2 ⟨hyL, ?_⟩)
    rw [MonoidHom.mem_ker] at hyk ⊢
    have h : ρ⁻¹ * y * ρ = ρ⁻¹ * y * ρ⁻¹⁻¹ := by rw [inv_inv]
    rw [h, map_conj_apply, hyk]

theorem frobeniusClosure_mono {d : G →* Multiplicative ℤ̂} {L L' : Subgroup G} (h : L' ≤ L) (x : G) :
    frobeniusClosure d L' x ≤ frobeniusClosure d L x :=
  frobeniusClosure_le isClosed_frobeniusClosure mem_frobeniusClosure_self
    ((inf_le_inf_right _ h).trans le_frobeniusClosure)

def conjOpen (σ : G) (K : OpenSubgroup G) : OpenSubgroup G where
  toSubgroup := (K : Subgroup G).map (MulAut.conj σ).toMonoidHom
  isOpen' := by
    show IsOpen (((K : Subgroup G).map (MulAut.conj σ).toMonoidHom : Subgroup G) : Set G)
    rw [coe_map_conj]
    exact K.isOpen.preimage ((continuous_const.mul continuous_id).mul continuous_const)

theorem coe_conjOpen (σ : G) (K : OpenSubgroup G) :
    ((conjOpen σ K : OpenSubgroup G) : Subgroup G) = (K : Subgroup G).map (MulAut.conj σ).toMonoidHom :=
  rfl

theorem mem_conjOpen {σ x : G} {K : OpenSubgroup G} :
    x ∈ ((conjOpen σ K : OpenSubgroup G) : Subgroup G) ↔ σ⁻¹ * x * σ ∈ (K : Subgroup G) :=
  mem_map_conj

theorem conjOpen_mono (σ : G) {K L : OpenSubgroup G} (h : L ≤ K) : conjOpen σ L ≤ conjOpen σ K :=
  fun _ hx => Subgroup.map_mono (f := (MulAut.conj σ).toMonoidHom) h hx

instance normal_conjOpen (σ : G) (K L : OpenSubgroup G) [hN : ((L : Subgroup G).subgroupOf K).Normal] :
    (((conjOpen σ L : OpenSubgroup G) : Subgroup G).subgroupOf (conjOpen σ K)).Normal := by
  constructor
  intro n hn g
  rw [Subgroup.mem_subgroupOf, mem_conjOpen] at hn ⊢
  have hnK : σ⁻¹ * (n : G) * σ ∈ (K : Subgroup G) := mem_conjOpen.1 n.2
  have hgK : σ⁻¹ * (g : G) * σ ∈ (K : Subgroup G) := mem_conjOpen.1 g.2
  have := hN.conj_mem ⟨_, hnK⟩ (Subgroup.mem_subgroupOf.2 hn) ⟨_, hgK⟩
  rw [Subgroup.mem_subgroupOf] at this
  convert this using 1
  simp only [Subgroup.coe_mul, InvMemClass.coe_inv]
  group

end Conj

section Maps

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  {A : Type*} [CommGroup A] [MulDistribMulAction G A]

def galRestrict {K L K' L' : OpenSubgroup G} [((L : Subgroup G).subgroupOf K).Normal]
    [((L' : Subgroup G).subgroupOf K').Normal] (hK : K' ≤ K) (hL : L' ≤ L) :
    (K' : Subgroup G) ⧸ (L' : Subgroup G).subgroupOf K' →* (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K :=
  QuotientGroup.map _ _ (Subgroup.inclusion hK) fun x hx => by
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
    exact hL (Subgroup.mem_subgroupOf.1 hx)

omit [IsTopologicalGroup G] [CompactSpace G] in
theorem galRestrict_mk {K L K' L' : OpenSubgroup G} [((L : Subgroup G).subgroupOf K).Normal]
    [((L' : Subgroup G).subgroupOf K').Normal] (hK : K' ≤ K) (hL : L' ≤ L) (τ : (K' : Subgroup G)) :
    galRestrict hK hL (τ : (K' : Subgroup G) ⧸ (L' : Subgroup G).subgroupOf K') =
      ((⟨τ, hK τ.2⟩ : (K : Subgroup G)) : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) :=
  rfl

noncomputable def normTateZero {K L K' L' : OpenSubgroup G} (hK : K' ≤ K) (hL : L' ≤ L)
    (hL'K' : L' ≤ K') (hLK : L ≤ K) :
    tateZero A (K' : Subgroup G) (L' : Subgroup G) →* tateZero A (K : Subgroup G) (L : Subgroup G) :=
  QuotientGroup.map _ _ (norm A (K : Subgroup G) (K' : Subgroup G)) (by
    rintro _ ⟨b, rfl⟩
    rw [Subgroup.mem_comap, norm_norm (M := (L' : Subgroup G)) hL'K' hK,
      ← norm_norm (M := (L' : Subgroup G)) hL hLK]
    exact ⟨_, rfl⟩)

theorem normTateZero_mk {K L K' L' : OpenSubgroup G} (hK : K' ≤ K) (hL : L' ≤ L)
    (hL'K' : L' ≤ K') (hLK : L ≤ K) (a : fixedModule A (K' : Subgroup G)) :
    normTateZero hK hL hL'K' hLK (QuotientGroup.mk a : tateZero A (K' : Subgroup G) (L' : Subgroup G)) =
      (QuotientGroup.mk (norm A (K : Subgroup G) (K' : Subgroup G) a) :
        tateZero A (K : Subgroup G) (L : Subgroup G)) :=
  rfl

noncomputable def galConj (σ : G) (K L : OpenSubgroup G) [((L : Subgroup G).subgroupOf K).Normal] :
    (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K →*
      ((conjOpen σ K : OpenSubgroup G) : Subgroup G) ⧸
        ((conjOpen σ L : OpenSubgroup G) : Subgroup G).subgroupOf (conjOpen σ K) :=
  QuotientGroup.map _ _
    ((K : Subgroup G).equivMapOfInjective _ (MulAut.conj σ).injective).toMonoidHom fun x hx => by
      rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
      exact ⟨x, Subgroup.mem_subgroupOf.1 hx, rfl⟩

omit [CompactSpace G] in
theorem galConj_mk (σ : G) (K L : OpenSubgroup G) [((L : Subgroup G).subgroupOf K).Normal]
    (τ : (K : Subgroup G)) :
    galConj σ K L (τ : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) =
      ((⟨σ * τ * σ⁻¹, τ, τ.2, rfl⟩ : ((conjOpen σ K : OpenSubgroup G) : Subgroup G)) : _ ⧸ _) :=
  rfl

def conjFixed (σ : G) (K : OpenSubgroup G) :
    fixedModule A (K : Subgroup G) →* fixedModule A ((conjOpen σ K : OpenSubgroup G) : Subgroup G) where
  toFun a := ⟨σ • (a : A), smul_mem_fixedModule a.2 σ⟩
  map_one' := Subtype.ext (smul_one σ)
  map_mul' a b := Subtype.ext (smul_mul' σ (a : A) b)

theorem smul_norm_conjOpen (σ : G) (K L : OpenSubgroup G) (a : fixedModule A (L : Subgroup G)) :
    σ • (norm A (K : Subgroup G) (L : Subgroup G) a : A) =
      norm A ((conjOpen σ K : OpenSubgroup G) : Subgroup G) ((conjOpen σ L : OpenSubgroup G) : Subgroup G)
        (conjFixed σ L a) := by
  have : (((L : Subgroup G).map (MulAut.conj σ).toMonoidHom).subgroupOf
      ((K : Subgroup G).map (MulAut.conj σ).toMonoidHom)).FiniteIndex :=
    (inferInstance : (((conjOpen σ L : OpenSubgroup G) : Subgroup G).subgroupOf
      (conjOpen σ K)).FiniteIndex)
  exact smul_norm σ a

noncomputable def tateZeroConj (σ : G) (K L : OpenSubgroup G) :
    tateZero A (K : Subgroup G) (L : Subgroup G) →*
      tateZero A ((conjOpen σ K : OpenSubgroup G) : Subgroup G) ((conjOpen σ L : OpenSubgroup G) : Subgroup G) :=
  QuotientGroup.map _ _ (conjFixed σ K) (by
    rintro _ ⟨b, rfl⟩
    exact ⟨conjFixed σ L b, Subtype.ext (smul_norm_conjOpen σ K L b).symm⟩)

theorem tateZeroConj_mk (σ : G) (K L : OpenSubgroup G) (a : fixedModule A (K : Subgroup G)) :
    tateZeroConj σ K L (QuotientGroup.mk a : tateZero A (K : Subgroup G) (L : Subgroup G)) =
      (QuotientGroup.mk (conjFixed σ K a) : tateZero A _ _) :=
  rfl

end Maps

namespace ClassFieldData

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  {A : Type*} [CommGroup A] [MulDistribMulAction G A] {D : ClassFieldData G A}

theorem valuation_conj (σ : G) {K K' : OpenSubgroup G}
    (hK' : (K' : Subgroup G) = (K : Subgroup G).map (MulAut.conj σ).toMonoidHom)
    (a : fixedModule A (K : Subgroup G)) (b : fixedModule A (K' : Subgroup G))
    (hb : (b : A) = σ • (a : A)) : D.valuation K' b = D.valuation K a := by
  have hf : inertiaDegree D.deg (K' : Subgroup G) = inertiaDegree D.deg (K : Subgroup G) := by
    rw [hK', inertiaDegree_map_conj]
  rw [valuation_eq_iff, hf, valuation_pow D K a]
  congr 1
  apply Subtype.ext
  have htop : (⊤ : Subgroup G).map (MulAut.conj σ).toMonoidHom = ⊤ :=
    Subgroup.map_top_of_surjective _ (MulAut.conj σ).surjective
  have : (((K : Subgroup G).map (MulAut.conj σ).toMonoidHom).subgroupOf
      ((⊤ : Subgroup G).map (MulAut.conj σ).toMonoidHom)).FiniteIndex := by
    rw [← hK', htop]
    infer_instance
  have h1 := smul_norm σ (K := ⊤) a
  rw [(norm A ⊤ (K : Subgroup G) a).2 σ (Subgroup.mem_top σ), coe_norm_congr htop hK'.symm] at h1
  rw [h1]
  exact congrArg (fun x => (norm A ⊤ (K' : Subgroup G) x : A)) (Subtype.ext hb)

variable [TotallyDisconnectedSpace G]

section Restriction

noncomputable def FrobeniusLift.toBase {K K' : OpenSubgroup G} (hK : K' ≤ K) (s : D.FrobeniusLift K') :
    D.FrobeniusLift K where
  elt := s.elt
  mem := hK s.mem
  deg := s.deg * relInertiaDegree D.deg K K'
  deg_pos := Nat.mul_pos s.deg_pos (Nat.pos_of_ne_zero (D.relInertiaDegree_ne_zero hK))
  deg_eq := by
    rw [s.deg_eq, inertiaDegree_eq_mul D.surjective_deg (K := (K : Subgroup G))
      (L := (K' : Subgroup G)) hK, Nat.mul_assoc]

theorem reciprocity_galRestrict (hax : ClassFieldAxiom G A) [IsDiscreteModule G A]
    {K L K' L' : OpenSubgroup G} (hLK : L ≤ K) [((L : Subgroup G).subgroupOf K).Normal]
    (hL'K' : L' ≤ K') [((L' : Subgroup G).subgroupOf K').Normal] (hK : K' ≤ K) (hL : L' ≤ L)
    (q : (K' : Subgroup G) ⧸ (L' : Subgroup G).subgroupOf K') :
    D.reciprocity hLK hax (galRestrict hK hL q) =
      normTateZero hK hL hL'K' hLK (D.reciprocity hL'K' hax q) := by
  obtain ⟨s, rfl⟩ := exists_frobeniusLift_mk (D := D) hL'K' q
  set t := s.toBase hK with htdef
  have ht : t.deg = s.deg * relInertiaDegree D.deg K K' := rfl
  have hle : s.field L' hL'K' ≤ t.field L hLK := fun x hx => frobeniusClosure_mono hL s.elt hx
  obtain ⟨π, hπ⟩ := D.exists_prime (s.field L' hL'K')
  have hrel : relInertiaDegree D.deg (t.field L hLK) (s.field L' hL'K') = 1 := by
    have h1 := inertiaDegree_eq_mul D.surjective_deg
      (K := ((t.field L hLK : OpenSubgroup G) : Subgroup G))
      (L := ((s.field L' hL'K' : OpenSubgroup G) : Subgroup G)) hle
    rw [s.inertiaDegree_field hL'K', t.inertiaDegree_field hLK, ht,
      inertiaDegree_eq_mul D.surjective_deg (K := (K : Subgroup G)) (L := (K' : Subgroup G)) hK] at h1
    have hpos : 0 < s.deg * relInertiaDegree D.deg K K' * inertiaDegree D.deg K :=
      Nat.mul_pos (Nat.mul_pos s.deg_pos (Nat.pos_of_ne_zero (D.relInertiaDegree_ne_zero hK)))
        (Nat.pos_of_ne_zero (D.inertiaDegree_ne_zero K))
    refine Nat.eq_of_mul_eq_mul_right hpos ?_
    rw [one_mul]
    exact h1.symm.trans (Nat.mul_assoc _ _ _).symm
  set π0 := norm A ((t.field L hLK : OpenSubgroup G) : Subgroup G)
    ((s.field L' hL'K' : OpenSubgroup G) : Subgroup G) π with hπ0def
  have hπ0 : D.valuation (t.field L hLK) π0 = Multiplicative.ofAdd 1 := by
    rw [hπ0def, D.valuation_norm hle, hrel, pow_one, hπ]
  have e1 : galRestrict hK hL ((⟨s.elt, s.mem⟩ : (K' : Subgroup G)) :
      (K' : Subgroup G) ⧸ (L' : Subgroup G).subgroupOf K') =
      ((⟨t.elt, t.mem⟩ : (K : Subgroup G)) : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) := rfl
  rw [e1, D.reciprocity_mk_eq_norm hLK hax t hπ0, D.reciprocity_mk_eq_norm hL'K' hax s hπ,
    normTateZero_mk, hπ0def,
    norm_norm (M := ((s.field L' hL'K' : OpenSubgroup G) : Subgroup G)) (s.field_le hL'K') hK,
    norm_norm (M := ((s.field L' hL'K' : OpenSubgroup G) : Subgroup G)) hle (t.field_le hLK)]

end Restriction

section Conjugation

def FrobeniusLift.conj (ρ : G) {K : OpenSubgroup G} (s : D.FrobeniusLift K) :
    D.FrobeniusLift (conjOpen ρ K) where
  elt := ρ * s.elt * ρ⁻¹
  mem := ⟨s.elt, s.mem, rfl⟩
  deg := s.deg
  deg_pos := s.deg_pos
  deg_eq := by
    rw [map_conj_apply, s.deg_eq, coe_conjOpen, inertiaDegree_map_conj]

theorem FrobeniusLift.coe_field_conj (ρ : G) {K L : OpenSubgroup G} (hLK : L ≤ K)
    [((L : Subgroup G).subgroupOf K).Normal] (s : D.FrobeniusLift K) :
    (((s.conj ρ).field (conjOpen ρ L) (conjOpen_mono ρ hLK) : OpenSubgroup G) : Subgroup G) =
      ((s.field L hLK : OpenSubgroup G) : Subgroup G).map (MulAut.conj ρ).toMonoidHom :=
  (map_conj_frobeniusClosure D.deg (L : Subgroup G) s.elt ρ).symm

theorem reciprocity_galConj (hax : ClassFieldAxiom G A) [IsDiscreteModule G A] (σ : G)
    {K L : OpenSubgroup G} (hLK : L ≤ K) [((L : Subgroup G).subgroupOf K).Normal]
    (q : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) :
    D.reciprocity (conjOpen_mono σ hLK) hax (galConj σ K L q) =
      tateZeroConj σ K L (D.reciprocity hLK hax q) := by
  obtain ⟨s, rfl⟩ := exists_frobeniusLift_mk (D := D) hLK q
  set t := s.conj σ with htdef
  have hfield := s.coe_field_conj σ hLK
  obtain ⟨π, hπ⟩ := D.exists_prime (s.field L hLK)
  let π' : fixedModule A (((t.field (conjOpen σ L) (conjOpen_mono σ hLK)) : OpenSubgroup G) :
      Subgroup G) := ⟨σ • (π : A), hfield ▸ smul_mem_fixedModule π.2 σ⟩
  have hπ' : D.valuation (t.field (conjOpen σ L) (conjOpen_mono σ hLK)) π' = Multiplicative.ofAdd 1 := by
    rw [valuation_conj σ hfield π π' rfl, hπ]
  have e1 : galConj σ K L ((⟨s.elt, s.mem⟩ : (K : Subgroup G)) :
      (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) =
      ((⟨t.elt, t.mem⟩ : ((conjOpen σ K : OpenSubgroup G) : Subgroup G)) : _ ⧸ _) := rfl
  rw [e1, D.reciprocity_mk_eq_norm (conjOpen_mono σ hLK) hax t hπ',
    D.reciprocity_mk_eq_norm hLK hax s hπ, tateZeroConj_mk]
  congr 1
  apply Subtype.ext
  show _ = σ • (norm A (K : Subgroup G) ((s.field L hLK : OpenSubgroup G) : Subgroup G) π : A)
  rw [smul_norm_conjOpen σ K (s.field L hLK) π]
  have : ((((s.field L hLK : OpenSubgroup G) : Subgroup G).map (MulAut.conj σ).toMonoidHom).subgroupOf
      ((conjOpen σ K : OpenSubgroup G) : Subgroup G)).FiniteIndex := by
    rw [← hfield]
    infer_instance
  exact coe_norm_congr rfl hfield _

end Conjugation

end ClassFieldData

end Sec_ALR_Functoriality

section Sec_ALR_FunctorialityNorm

section DoubleCoset

variable {G : Type*} [Group G] {A : Type*} [CommGroup A] [MulDistribMulAction G A]

def doubleCosetMap {K K' S M : Subgroup G} (hK'K : K' ≤ K) {τ : G} (hτ : τ ∈ K)
    (hM : ∀ k ∈ K', k ∈ M → τ * k * τ⁻¹ ∈ S) : K' ⧸ M.subgroupOf K' → K ⧸ S.subgroupOf K :=
  Quotient.map' (fun k : K' => (⟨k * τ⁻¹, K.mul_mem (hK'K k.2) (K.inv_mem hτ)⟩ : K)) fun k k' h => by
    rw [QuotientGroup.leftRel_apply, Subgroup.mem_subgroupOf] at h ⊢
    have := hM _ (K'.mul_mem (K'.inv_mem k.2) k'.2) (by simpa using h)
    simpa [mul_assoc] using this

theorem coe_norm_eq_prod_norm_inf {K K' S : Subgroup G} (hK'K : K' ≤ K)
    [(S.subgroupOf K).FiniteIndex] {ι : Type*} [Fintype ι] (τ : ι → G) (hτ : ∀ i, τ i ∈ K)
    (M : ι → Subgroup G) [∀ i, ((M i).subgroupOf K').FiniteIndex]
    (hM : ∀ i, ∀ k ∈ K', k ∈ M i ↔ τ i * k * (τ i)⁻¹ ∈ S)
    (hcover : ∀ c ∈ K, ∃ i, ∃ k ∈ K', τ i * k⁻¹ * c ∈ S)
    (hdisj : ∀ i j, ∀ k ∈ K', ∀ k' ∈ K', τ i * k⁻¹ * k' * (τ j)⁻¹ ∈ S → i = j)
    (a : fixedModule A S) (ha : ∀ i, (τ i)⁻¹ • (a : A) ∈ fixedModule A (M i)) :
    (norm A K S a : A) = ∏ i, (norm A K' (M i) ⟨(τ i)⁻¹ • (a : A), ha i⟩ : A) := by
  classical
  let f : ∀ i, K' ⧸ (M i).subgroupOf K' → K ⧸ S.subgroupOf K := fun i =>
    doubleCosetMap hK'K (hτ i) (fun k hk hkM => (hM i k hk).1 hkM)
  let F : (Σ i, K' ⧸ (M i).subgroupOf K') → K ⧸ S.subgroupOf K := fun p => f p.1 p.2
  have hFmk : ∀ i (k : K'), F ⟨i, (k : K' ⧸ (M i).subgroupOf K')⟩ =
      ((⟨k * (τ i)⁻¹, K.mul_mem (hK'K k.2) (K.inv_mem (hτ i))⟩ : K) : K ⧸ S.subgroupOf K) :=
    fun _ _ => rfl
  have hF : Function.Bijective F := by
    constructor
    · rintro ⟨i, x⟩ ⟨j, y⟩ hxy
      induction x using QuotientGroup.induction_on with
      | H k =>
      induction y using QuotientGroup.induction_on with
      | H k' =>
        rw [hFmk, hFmk, QuotientGroup.eq, Subgroup.mem_subgroupOf] at hxy
        have hxy' : τ i * (k : G)⁻¹ * k' * (τ j)⁻¹ ∈ S := by simpa [mul_assoc] using hxy
        obtain rfl := hdisj i j k k.2 k' k'.2 hxy'
        have hkk : (k : G)⁻¹ * k' ∈ M i :=
          (hM i _ (K'.mul_mem (K'.inv_mem k.2) k'.2)).2 (by simpa [mul_assoc] using hxy')
        have : ((k : K' ⧸ (M i).subgroupOf K')) = (k' : K' ⧸ (M i).subgroupOf K') := by
          rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
          simpa using hkk
        rw [this]
    · intro y
      induction y using QuotientGroup.induction_on with
      | H c =>
        obtain ⟨i, k, hk, hc⟩ := hcover c c.2
        refine ⟨⟨i, ((⟨k, hk⟩ : K') : K' ⧸ (M i).subgroupOf K')⟩, ?_⟩
        rw [hFmk, QuotientGroup.eq, Subgroup.mem_subgroupOf]
        simpa [mul_assoc] using hc
  have : ∀ i, Fintype (K' ⧸ (M i).subgroupOf K') := fun i => Fintype.ofFinite _
  let _ := Fintype.ofFinite (K ⧸ S.subgroupOf K)
  rw [coe_norm, ← finprod_comp_equiv (Equiv.ofBijective F hF), finprod_eq_prod_of_fintype,
    Fintype.prod_sigma]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [coe_norm, finprod_eq_prod_of_fintype]
  refine Finset.prod_congr rfl fun x _ => ?_
  induction x using QuotientGroup.induction_on with
  | H k =>
    rw [Equiv.ofBijective_apply, hFmk, cosetSMul_mk, cosetSMul_mk]
    exact mul_smul _ _ _

theorem conj_mem_of_normal {K L : Subgroup G} [hN : (L.subgroupOf K).Normal] {τ k : G} (hτ : τ ∈ K)
    (hk : k ∈ K) (hkL : k ∈ L) : τ * k * τ⁻¹ ∈ L := by
  have := hN.conj_mem ⟨k, hk⟩ (Subgroup.mem_subgroupOf.2 hkL) ⟨τ, hτ⟩
  simpa [Subgroup.mem_subgroupOf] using this

theorem conj_mem_iff_of_normal {K L : Subgroup G} [(L.subgroupOf K).Normal] {τ k : G} (hτ : τ ∈ K)
    (hk : k ∈ K) : τ * k * τ⁻¹ ∈ L ↔ k ∈ L := by
  refine ⟨fun h => ?_, conj_mem_of_normal hτ hk⟩
  have := conj_mem_of_normal (K.inv_mem hτ) (K.mul_mem (K.mul_mem hτ hk) (K.inv_mem hτ)) h
  simpa [mul_assoc] using this

end DoubleCoset

section Inclusion

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  {A : Type*} [CommGroup A] [MulDistribMulAction G A]

theorem norm_mem_range_norm_of_le {K K' L : OpenSubgroup G} (hLK' : L ≤ K') (hK'K : K' ≤ K)
    [((L : Subgroup G).subgroupOf K).Normal] (b : fixedModule A (L : Subgroup G)) :
    (⟨norm A (K : Subgroup G) (L : Subgroup G) b,
        fixedModule_anti hK'K (norm A (K : Subgroup G) (L : Subgroup G) b).2⟩ :
        fixedModule A (K' : Subgroup G)) ∈ (norm A (K' : Subgroup G) (L : Subgroup G)).range := by
  classical
  have hLK : L ≤ K := hLK'.trans hK'K
  let _ := Fintype.ofFinite ((K : Subgroup G) ⧸ (K' : Subgroup G).subgroupOf K)
  let τ : (K : Subgroup G) ⧸ (K' : Subgroup G).subgroupOf K → G := fun i => ((Quotient.out i : K) : G)
  have hτ : ∀ i, τ i ∈ (K : Subgroup G) := fun i => (Quotient.out i : K).2
  have ha : ∀ i, (τ i)⁻¹ • (b : A) ∈ fixedModule A (L : Subgroup G) := fun i =>
    smul_mem_fixedModule_of_normal hLK ((K : Subgroup G).inv_mem (hτ i)) b.2
  have key := coe_norm_eq_prod_norm_inf (A := A) (S := (L : Subgroup G)) hK'K τ hτ
    (fun _ => (L : Subgroup G)) (fun i k hk => (conj_mem_iff_of_normal (hτ i) (hK'K hk)).symm)
    (fun c hc => by
      obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul ((K' : Subgroup G).subgroupOf K)
        (⟨c⁻¹, (K : Subgroup G).inv_mem hc⟩ : (K : Subgroup G))
      refine ⟨((⟨c⁻¹, (K : Subgroup G).inv_mem hc⟩ : (K : Subgroup G)) : _ ⧸ _), (h : G),
        Subgroup.mem_subgroupOf.1 h.2, ?_⟩
      have : τ ((⟨c⁻¹, (K : Subgroup G).inv_mem hc⟩ : (K : Subgroup G)) : _ ⧸ _) = c⁻¹ * (h : G) := by
        simp only [τ, hh, Subgroup.coe_mul]
      rw [this]
      simp)
    (fun i j k hk k' hk' hy => by
      rw [← QuotientGroup.out_eq' i, ← QuotientGroup.out_eq' j, QuotientGroup.eq,
        Subgroup.mem_subgroupOf]
      have hyK : τ i * k⁻¹ * k' * (τ j)⁻¹ ∈ (K : Subgroup G) := hLK hy
      have hc := conj_mem_of_normal ((K : Subgroup G).inv_mem (hτ j)) ((K : Subgroup G).inv_mem hyK)
        ((L : Subgroup G).inv_mem hy)
      have hmem : k⁻¹ * k' * ((τ j)⁻¹ * (τ i * k⁻¹ * k' * (τ j)⁻¹)⁻¹ * (τ j)⁻¹⁻¹) ∈
          (K' : Subgroup G) :=
        (K' : Subgroup G).mul_mem ((K' : Subgroup G).mul_mem ((K' : Subgroup G).inv_mem hk) hk')
          (hLK' hc)
      convert hmem using 1
      simp only [Subgroup.coe_mul, InvMemClass.coe_inv, τ]
      group)
    b ha
  refine ⟨∏ i, ⟨(τ i)⁻¹ • (b : A), ha i⟩, Subtype.ext ?_⟩
  rw [map_prod]
  simp only [SubmonoidClass.coe_finsetProd]
  exact key.symm

noncomputable def tateZeroIncl {K K' L : OpenSubgroup G} (hLK' : L ≤ K') (hK'K : K' ≤ K)
    [((L : Subgroup G).subgroupOf K).Normal] :
    tateZero A (K : Subgroup G) (L : Subgroup G) →* tateZero A (K' : Subgroup G) (L : Subgroup G) :=
  QuotientGroup.map _ _ (Subgroup.inclusion (fixedModule_anti (A := A) hK'K)) (by
    rintro _ ⟨b, rfl⟩
    exact norm_mem_range_norm_of_le hLK' hK'K b)

theorem tateZeroIncl_mk {K K' L : OpenSubgroup G} (hLK' : L ≤ K') (hK'K : K' ≤ K)
    [((L : Subgroup G).subgroupOf K).Normal] (a : fixedModule A (K : Subgroup G)) :
    tateZeroIncl hLK' hK'K (QuotientGroup.mk a : tateZero A (K : Subgroup G) (L : Subgroup G)) =
      (QuotientGroup.mk ⟨(a : A), fixedModule_anti hK'K a.2⟩ : tateZero A (K' : Subgroup G) (L : Subgroup G)) :=
  rfl

end Inclusion

end Sec_ALR_FunctorialityNorm

section Sec_ALR_FunctorialityTransfer

open ProfiniteInteger MulAction

section Transfer

theorem map_transfer {Γ : Type*} [Group Γ] {H : Subgroup Γ} [H.FiniteIndex] {B C : Type*} [CommGroup B]
    [CommGroup C] (φ : H →* B) (f : B →* C) (g : Γ) : f (φ.transfer g) = (f.comp φ).transfer g := by
  classical
  let _ : Fintype (Quotient (orbitRel (Subgroup.zpowers g) (Γ ⧸ H))) := Fintype.ofFinite _
  rw [MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot,
    MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot, map_prod]
  rfl

end Transfer

section FixedField

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {d : G →* Multiplicative ℤ̂} {L : Subgroup G} {σ : G}

theorem exists_eq_zpow_mul_of_mem_frobeniusClosure (hL : IsOpen (L : Set G))
    (hσ : σ ∈ Subgroup.normalizer ((L ⊓ d.ker : Subgroup G) : Set G)) {y : G}
    (hy : y ∈ frobeniusClosure d L σ) : ∃ m : ℤ, ∃ l ∈ L, y = σ ^ m * l := by
  have hy' : y ∈ closure ((Subgroup.zpowers σ ⊔ (L ⊓ d.ker) : Subgroup G) : Set G) := by
    rw [← Subgroup.topologicalClosure_coe]
    exact hy
  have hO : IsOpen ((fun z => y⁻¹ * z) ⁻¹' (L : Set G)) :=
    hL.preimage (continuous_const.mul continuous_id)
  have hyO : y ∈ (fun z => y⁻¹ * z) ⁻¹' (L : Set G) := by
    show y⁻¹ * y ∈ L
    rw [inv_mul_cancel]
    exact L.one_mem
  obtain ⟨h, hhO, hhS⟩ := mem_closure_iff.1 hy' _ hO hyO
  obtain ⟨m, j, hj, rfl⟩ := (mem_zpowers_sup_iff hσ).1 hhS
  refine ⟨m, j * (y⁻¹ * (σ ^ m * j))⁻¹, L.mul_mem hj.1 (L.inv_mem hhO), by group⟩

variable [CompactSpace G] [TotallyDisconnectedSpace G]

theorem frobeniusClosure_pow_eq_inf (hd : Continuous d) (hL : IsOpen (L : Set G)) {K' : Subgroup G}
    (hK' : IsOpen (K' : Set G)) (hLK' : L ≤ K') {ρ : G}
    (hρ : ρ ∈ Subgroup.normalizer ((L ⊓ d.ker : Subgroup G) : Set G)) {N : ℕ} (hN : N ≠ 0)
    (hdρ : d ρ = Multiplicative.ofAdd (N : ℤ̂)) {f : ℕ} (hf : 0 < f) (hρf : ρ ^ f ∈ K')
    (hdiv : ∀ k : ℤ, ρ ^ k ∈ K' → (f : ℤ) ∣ k) :
    frobeniusClosure d L (ρ ^ f) = K' ⊓ frobeniusClosure d L ρ := by
  have hρf' : ρ ^ f ∈ Subgroup.normalizer ((L ⊓ d.ker : Subgroup G) : Set G) := Subgroup.pow_mem _ hρ f
  have hdρf : d (ρ ^ f) = Multiplicative.ofAdd ((f * N : ℕ) : ℤ̂) := by
    rw [map_pow, hdρ, ← ofAdd_nsmul, nsmul_eq_mul, Nat.cast_mul]
  have hle : frobeniusClosure d L (ρ ^ f) ≤ frobeniusClosure d L ρ :=
    frobeniusClosure_le isClosed_frobeniusClosure (Subgroup.pow_mem _ mem_frobeniusClosure_self f)
      le_frobeniusClosure
  apply le_antisymm
  · refine frobeniusClosure_le ((OpenSubgroup.isClosed ⟨K', hK'⟩).inter isClosed_frobeniusClosure)
      ⟨hρf, Subgroup.pow_mem _ mem_frobeniusClosure_self f⟩ ?_
    exact le_inf (inf_le_left.trans hLK') le_frobeniusClosure
  · intro y hy
    obtain ⟨hyK', hyS⟩ := Subgroup.mem_inf.1 hy
    set M : ℕ+ := ⟨f * N, Nat.mul_pos hf (Nat.pos_of_ne_zero hN)⟩ with hMdef
    set V : Set G := (L : Set G) ∩ d ⁻¹' (Multiplicative.toAdd ⁻¹' (multiples M : Set ℤ̂)) with hVdef
    have hV : IsOpen V := hL.inter ((isOpen_multiples M).preimage (continuous_toAdd.comp hd))
    have hO : IsOpen ((fun z => y⁻¹ * z) ⁻¹' V) := hV.preimage (continuous_const.mul continuous_id)
    have hyO : y ∈ (fun z => y⁻¹ * z) ⁻¹' V := by
      simp only [Set.mem_preimage, inv_mul_cancel, hVdef, Set.mem_inter_iff, map_one, toAdd_one]
      exact ⟨L.one_mem, (multiples M).zero_mem⟩
    have hy' : y ∈ closure ((Subgroup.zpowers ρ ⊔ (L ⊓ d.ker) : Subgroup G) : Set G) := by
      rw [← Subgroup.topologicalClosure_coe]
      exact hyS
    obtain ⟨h, hhO, hhS⟩ := mem_closure_iff.1 hy' _ hO hyO
    have hhS' : h ∈ frobeniusClosure d L ρ := Subgroup.le_topologicalClosure _ hhS
    obtain ⟨k, j, hj, rfl⟩ := (mem_zpowers_sup_iff hρ).1 hhS
    obtain ⟨huL, huM⟩ := hhO
    set u := y⁻¹ * (ρ ^ k * j) with hudef

    have hρk : ρ ^ k ∈ K' := by
      have : ρ ^ k = y * u * j⁻¹ := by rw [hudef]; group
      rw [this]
      exact K'.mul_mem (K'.mul_mem hyK' (hLK' huL)) (K'.inv_mem (hLK' hj.1))
    obtain ⟨k', rfl⟩ := hdiv k hρk
    have hhf : ρ ^ ((f : ℤ) * k') * j ∈ frobeniusClosure d L (ρ ^ f) := by
      refine Subgroup.mul_mem _ ?_ (le_frobeniusClosure hj)
      rw [zpow_mul, zpow_natCast]
      exact Subgroup.zpow_mem _ mem_frobeniusClosure_self k'

    have huS : u ∈ frobeniusClosure d L ρ :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ hyS) hhS'
    have hmap := map_frobeniusClosure hd hρf' hdρf
    have hdu : d u ∈ (frobeniusClosure d L (ρ ^ f)).map d := by
      rw [hmap]
      exact huM
    obtain ⟨z, hz, hzu⟩ := hdu
    have hzu' : z⁻¹ * u ∈ frobeniusClosure d L ρ ⊓ d.ker := by
      refine ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ (hle hz)) huS, ?_⟩
      exact (MonoidHom.mem_ker).2 (by rw [map_mul, map_inv, hzu, inv_mul_cancel])
    rw [frobeniusClosure_inf_ker hd hL hρ hN hdρ] at hzu'
    have hu : u ∈ frobeniusClosure d L (ρ ^ f) := by
      have : u = z * (z⁻¹ * u) := by group
      rw [this]
      exact Subgroup.mul_mem _ hz (le_frobeniusClosure hzu')
    have : y = ρ ^ ((f : ℤ) * k') * j * u⁻¹ := by rw [hudef]; group
    rw [this]
    exact Subgroup.mul_mem _ hhf (Subgroup.inv_mem _ hu)

end FixedField

section Ver

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] in

theorem map_conj_eq_of_normal {K L : Subgroup G} [(L.subgroupOf K).Normal] (hLK : L ≤ K) {τ : G}
    (hτ : τ ∈ K) : L.map (MulAut.conj τ).toMonoidHom = L := by
  ext y
  rw [mem_map_conj]
  constructor
  · intro h
    have := conj_mem_of_normal hτ (hLK h) h
    simpa [mul_assoc] using this
  · intro h
    have := conj_mem_of_normal (K.inv_mem hτ) (hLK h) h
    simpa using this

variable {K K' L : OpenSubgroup G} [((L : Subgroup G).subgroupOf K).Normal]
  [((L : Subgroup G).subgroupOf K').Normal]

omit [IsTopologicalGroup G] [CompactSpace G] in

theorem galRestrict_injective (hK'K : K' ≤ K) :
    Function.Injective (galRestrict (K := K) (L := L) (K' := K') (L' := L) hK'K le_rfl) := by
  rw [injective_iff_map_eq_one]
  intro q hq
  induction q using QuotientGroup.induction_on with
  | H k =>
    rw [galRestrict_mk, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hq
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact hq

omit [IsTopologicalGroup G] [CompactSpace G] in

theorem mk_mem_range_galRestrict_iff (hLK' : L ≤ K') (hK'K : K' ≤ K) (k : (K : Subgroup G)) :
    (k : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) ∈
      (galRestrict (K := K) (L := L) (K' := K') (L' := L) hK'K le_rfl).range ↔
      (k : G) ∈ (K' : Subgroup G) := by
  constructor
  · rintro ⟨q, hq⟩
    induction q using QuotientGroup.induction_on with
    | H k' =>
      rw [galRestrict_mk, QuotientGroup.eq, Subgroup.mem_subgroupOf] at hq
      have h := (K' : Subgroup G).mul_mem k'.2 (hLK' hq)
      simpa using h
  · intro hk
    exact ⟨((⟨k, hk⟩ : (K' : Subgroup G)) : _ ⧸ _), rfl⟩

omit [IsTopologicalGroup G] [CompactSpace G] in
theorem mk_mk_eq_iff (hLK' : L ≤ K') (hK'K : K' ≤ K) (a b : (K : Subgroup G)) :
    ((a : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) :
        _ ⧸ (galRestrict (K := K) (L := L) (K' := K') (L' := L) hK'K le_rfl).range) =
      ((b : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) : _ ⧸ _) ↔
      (a : G)⁻¹ * b ∈ (K' : Subgroup G) := by
  rw [QuotientGroup.eq, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
    mk_mem_range_galRestrict_iff hLK' hK'K]
  simp

omit [IsTopologicalGroup G] [CompactSpace G] in
theorem zpow_smul_mk_mk_eq_iff (hLK' : L ≤ K') (hK'K : K' ≤ K) (σ x : (K : Subgroup G)) (k : ℤ) :
    ((σ : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) ^ k) •
        ((x : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) :
          _ ⧸ (galRestrict (K := K) (L := L) (K' := K') (L' := L) hK'K le_rfl).range) =
      ((x : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) : _ ⧸ _) ↔
      (x : G)⁻¹ * (σ : G) ^ k * x ∈ (K' : Subgroup G) := by
  rw [MulAction.Quotient.smul_mk, smul_eq_mul, ← QuotientGroup.mk_zpow, ← QuotientGroup.mk_mul,
    mk_mk_eq_iff hLK' hK'K]
  have e : (((σ ^ k * x : (K : Subgroup G)) : G))⁻¹ * x = ((x : G)⁻¹ * (σ : G) ^ k * x)⁻¹ := by
    simp only [Subgroup.coe_mul, SubgroupClass.coe_zpow]
    group
  rw [e, Subgroup.inv_mem_iff]

noncomputable def verlagerung (hK'K : K' ≤ K) :
    (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K →*
      Abelianization ((K' : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K') :=
  ((Abelianization.of).comp
    (MonoidHom.ofInjective (galRestrict_injective (L := L) hK'K)).symm.toMonoidHom).transfer

end Ver

namespace ClassFieldData

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] {A : Type*} [CommGroup A] [MulDistribMulAction G A]
  {D : ClassFieldData G A}

omit [TotallyDisconnectedSpace G] in

theorem exists_frobeniusLift_of_deg {K : OpenSubgroup G} {x : G} (hx : x ∈ (K : Subgroup G)) {N : ℕ}
    (hN : 0 < N) (hd : D.deg x = Multiplicative.ofAdd (N : ℤ̂)) :
    ∃ s : D.FrobeniusLift K, s.elt = x := by
  have hm := toAdd_deg_mem_multiples (D := D) K hx
  rw [hd, toAdd_ofAdd, ← Int.cast_natCast,
    intCast_mem_multiples_iff (Nat.pos_of_ne_zero (D.inertiaDegree_ne_zero K))] at hm
  obtain ⟨m, rfl⟩ := Int.natCast_dvd_natCast.1 hm
  have hm0 : 0 < m := Nat.pos_of_mul_pos_left hN
  exact ⟨⟨x, hx, m, hm0, by rw [hd, Nat.mul_comm]⟩, rfl⟩

section Ver

variable {K K' L : OpenSubgroup G} [((L : Subgroup G).subgroupOf K).Normal]
  [((L : Subgroup G).subgroupOf K').Normal]

theorem reciprocity_mk_conj_pow (hax : ClassFieldAxiom G A) [IsDiscreteModule G A]
    (hLK' : L ≤ K') (hK'K : K' ≤ K) (s : D.FrobeniusLift K) (x : (K : Subgroup G)) {f : ℕ}
    (hf0 : 0 < f) (hf : ∀ k : ℤ, (x : G)⁻¹ * s.elt ^ k * x ∈ (K' : Subgroup G) ↔ (f : ℤ) ∣ k)
    (hmem : (x : G)⁻¹ * s.elt ^ f * x ∈ (K' : Subgroup G))
    {π : fixedModule A ((s.field L (hLK'.trans hK'K) : OpenSubgroup G) : Subgroup G)}
    (hπ : D.valuation (s.field L (hLK'.trans hK'K)) π = Multiplicative.ofAdd 1) :
    D.reciprocity hLK' hax ((⟨_, hmem⟩ : (K' : Subgroup G)) :
      (K' : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K') =
      (QuotientGroup.mk (norm A (K' : Subgroup G)
        ((K' ⊓ conjOpen (x : G)⁻¹ (s.field L (hLK'.trans hK'K)) : OpenSubgroup G) : Subgroup G)
        ⟨(x : G)⁻¹ • (π : A), fixedModule_anti (inf_le_right (a := K'))
          (smul_mem_fixedModule π.2 _)⟩) : tateZero A (K' : Subgroup G) (L : Subgroup G)) := by
  have hLK : L ≤ K := hLK'.trans hK'K
  obtain ⟨ρ, hρdef⟩ : ∃ ρ : G, ρ = (x : G)⁻¹ * s.elt * x := ⟨_, rfl⟩
  have hρK : ρ ∈ (K : Subgroup G) := by
    rw [hρdef]
    exact (K : Subgroup G).mul_mem ((K : Subgroup G).mul_mem ((K : Subgroup G).inv_mem x.2) s.mem) x.2
  have hρn := FrobeniusLift.mem_normalizer (D := D) hLK hρK
  have hdρ : D.deg ρ = Multiplicative.ofAdd ((s.deg * inertiaDegree D.deg K : ℕ) : ℤ̂) := by
    rw [hρdef, map_mul, map_mul, map_inv, mul_comm _ (D.deg s.elt), mul_assoc, inv_mul_cancel,
      mul_one, s.deg_eq]
  have hN : s.deg * inertiaDegree D.deg K ≠ 0 := s.degree_ne_zero
  have hρz : ∀ k : ℤ, ρ ^ k = (x : G)⁻¹ * s.elt ^ k * x := fun k => by
    have := conj_zpow (i := k) (a := (x : G)⁻¹) (b := s.elt)
    simpa [hρdef] using this
  have hρn' : ∀ k : ℕ, ρ ^ k = (x : G)⁻¹ * s.elt ^ k * x := fun k => by
    have := conj_pow (i := k) (a := (x : G)⁻¹) (b := s.elt)
    simpa [hρdef] using this
  have hmemρ : ρ ^ f ∈ (K' : Subgroup G) := by
    rw [hρn']
    exact hmem
  have hdivρ : ∀ k : ℤ, ρ ^ k ∈ (K' : Subgroup G) → (f : ℤ) ∣ k := fun k hk =>
    (hf k).1 (by rwa [hρz] at hk)
  obtain ⟨t, ht⟩ := exists_frobeniusLift_of_deg (D := D) (K := K') hmemρ
    (N := f * (s.deg * inertiaDegree D.deg K)) (Nat.mul_pos hf0 (Nat.pos_of_ne_zero hN))
    (by rw [map_pow, hdρ, ← ofAdd_nsmul, nsmul_eq_mul]; norm_cast)
  have hconjS : ((conjOpen (x : G)⁻¹ (s.field L hLK) : OpenSubgroup G) : Subgroup G) =
      frobeniusClosure D.deg L ρ := by
    rw [coe_conjOpen, s.coe_field hLK, map_conj_frobeniusClosure,
      map_conj_eq_of_normal hLK ((K : Subgroup G).inv_mem x.2), inv_inv, hρdef]
  have hkey := frobeniusClosure_pow_eq_inf D.continuous_deg L.isOpen K'.isOpen hLK' hρn hN hdρ hf0
    hmemρ hdivρ
  have htfield : ((t.field L hLK' : OpenSubgroup G) : Subgroup G) =
      ((K' ⊓ conjOpen (x : G)⁻¹ (s.field L hLK) : OpenSubgroup G) : Subgroup G) := by
    rw [t.coe_field hLK', ht, hkey, ← hconjS]
    rfl
  have hle : t.field L hLK' ≤ conjOpen (x : G)⁻¹ (s.field L hLK) := by
    intro y hy
    have : y ∈ ((t.field L hLK' : OpenSubgroup G) : Subgroup G) := hy
    rw [htfield] at this
    exact (Subgroup.mem_inf.1 this).2
  have ha : (x : G)⁻¹ • (π : A) ∈
      fixedModule A ((conjOpen (x : G)⁻¹ (s.field L hLK) : OpenSubgroup G) : Subgroup G) :=
    smul_mem_fixedModule π.2 _
  have hv1 : D.valuation (conjOpen (x : G)⁻¹ (s.field L hLK)) ⟨_, ha⟩ = Multiplicative.ofAdd 1 := by
    rw [valuation_conj (x : G)⁻¹ rfl π ⟨_, ha⟩ rfl, hπ]
  have hram : relRamificationIndex D.deg (conjOpen (x : G)⁻¹ (s.field L hLK)) (t.field L hLK') = 1 := by
    rw [relRamificationIndex, Subgroup.relIndex_eq_one]
    intro y hy
    obtain ⟨hyk, hyS⟩ := Subgroup.mem_inf.1 hy
    have hy' : y ∈ frobeniusClosure D.deg L ρ ⊓ D.deg.ker := by
      refine ⟨?_, hyk⟩
      rw [← hconjS]
      exact hyS
    rw [frobeniusClosure_inf_ker D.continuous_deg L.isOpen hρn hN hdρ] at hy'
    show y ∈ frobeniusClosure D.deg L t.elt
    rw [ht]
    exact le_frobeniusClosure hy'
  have hπ' : D.valuation (t.field L hLK') ⟨(x : G)⁻¹ • (π : A), fixedModule_anti hle ha⟩ =
      Multiplicative.ofAdd 1 := by
    rw [D.valuation_of_mem hle ha, hv1, hram, pow_one]
  have he : ((⟨_, hmem⟩ : (K' : Subgroup G)) : (K' : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K') =
      ((⟨t.elt, t.mem⟩ : (K' : Subgroup G)) : _ ⧸ _) := by
    congr 1
    apply Subtype.ext
    show _ = t.elt
    rw [ht, hρn']
  rw [he, D.reciprocity_mk_eq_norm hLK' hax t hπ']
  congr 1
  apply Subtype.ext
  exact coe_norm_congr rfl htfield _

theorem reciprocity_verlagerung (hax : ClassFieldAxiom G A) [IsDiscreteModule G A] (hLK' : L ≤ K')
    (hK'K : K' ≤ K) (g : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) :
    Abelianization.lift (D.reciprocity hLK' hax) (verlagerung hK'K g) =
      tateZeroIncl hLK' hK'K (D.reciprocity (hLK'.trans hK'K) hax g) := by
  classical
  have hLK : L ≤ K := hLK'.trans hK'K
  obtain ⟨s, rfl⟩ := exists_frobeniusLift_mk (D := D) hLK g
  obtain ⟨π, hπ⟩ := D.exists_prime (s.field L hLK)
  rw [D.reciprocity_mk_eq_norm hLK hax s hπ, tateZeroIncl_mk, verlagerung, map_transfer]
  set H := (galRestrict (K := K) (L := L) (K' := K') (L' := L) hK'K le_rfl).range with hH
  set γ : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K :=
    ((⟨s.elt, s.mem⟩ : (K : Subgroup G)) : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) with hγ
  let _ : Fintype (Quotient (orbitRel (Subgroup.zpowers γ)
    (((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) ⧸ H))) := Fintype.ofFinite _
  rw [MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot]
  let τ : Quotient (orbitRel (Subgroup.zpowers γ)
      (((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) ⧸ H)) → (K : Subgroup G) :=
    fun q => q.out.out.out
  have hqτ : ∀ q, q.out = (((τ q : (K : Subgroup G)) : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) :
      _ ⧸ H) := fun q => by
    simp only [τ, QuotientGroup.out_eq']
  have hper : ∀ q (k : ℤ), ((τ q : G))⁻¹ * s.elt ^ k * τ q ∈ (K' : Subgroup G) ↔
      (Function.minimalPeriod (γ • ·) q.out : ℤ) ∣ k := fun q k => by
    rw [← zpow_smul_eq_iff_minimalPeriod_dvd, hqτ q, hγ, zpow_smul_mk_mk_eq_iff hLK' hK'K]
  have hpos : ∀ q : Quotient (orbitRel (Subgroup.zpowers γ) (((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) ⧸ H)), 0 < Function.minimalPeriod (γ • ·) q.out := fun q =>
    Nat.pos_of_dvd_of_pos (pow_smul_eq_iff_minimalPeriod_dvd.1 (by rw [pow_orderOf_eq_one, one_smul]))
      (orderOf_pos γ)
  have hmemf : ∀ q : Quotient (orbitRel (Subgroup.zpowers γ) (((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) ⧸ H)), ((τ q : G))⁻¹ * s.elt ^ Function.minimalPeriod (γ • ·) q.out * τ q ∈
      (K' : Subgroup G) := fun q => by
    have := (hper q (Function.minimalPeriod (γ • ·) q.out)).2 dvd_rfl
    rwa [zpow_natCast] at this
  have hfac : ∀ q : Quotient (orbitRel (Subgroup.zpowers γ) (((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) ⧸ H)), ((Abelianization.lift (D.reciprocity hLK' hax)).comp
      ((Abelianization.of).comp
        (MonoidHom.ofInjective (galRestrict_injective (L := L) hK'K)).symm.toMonoidHom))
        ⟨(q.out.out)⁻¹ * γ ^ Function.minimalPeriod (γ • ·) q.out * q.out.out,
          QuotientGroup.out_conj_pow_minimalPeriod_mem H γ q.out⟩ =
      (QuotientGroup.mk (norm A (K' : Subgroup G)
        ((K' ⊓ conjOpen ((τ q : G))⁻¹ (s.field L hLK) : OpenSubgroup G) : Subgroup G)
        ⟨((τ q : G))⁻¹ • (π : A), fixedModule_anti (inf_le_right (a := K'))
          (smul_mem_fixedModule π.2 _)⟩) : tateZero A (K' : Subgroup G) (L : Subgroup G)) := by
    intro q
    refine Eq.trans ?_ (reciprocity_mk_conj_pow hax hLK' hK'K s (τ q) (hpos q) (hper q) (hmemf q) hπ)
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, Abelianization.lift_apply_of]
    congr 1
    rw [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_eq]
    apply Subtype.ext
    rw [MonoidHom.ofInjective_apply, galRestrict_mk]
    show (Quotient.out q.out)⁻¹ * γ ^ Function.minimalPeriod (γ • ·) q.out * Quotient.out q.out = _
    have hL : (Quotient.out q.out)⁻¹ * γ ^ Function.minimalPeriod (γ • ·) q.out * Quotient.out q.out =
        ((((τ q)⁻¹ * ⟨s.elt, s.mem⟩ ^ Function.minimalPeriod (γ • ·) q.out * τ q : (K : Subgroup G))) :
          (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_pow]
      simp only [τ, QuotientGroup.out_eq']
      rfl
    rw [hL]
    congr 1
  rw [Finset.prod_congr rfl fun q _ => hfac q, ← QuotientGroup.mk_prod]
  congr 1
  apply Subtype.ext
  rw [SubmonoidClass.coe_finsetProd]
  refine (coe_norm_eq_prod_norm_inf hK'K (fun q => (τ q : G)) (fun q => (τ q).2)
    (fun q => ((K' ⊓ conjOpen ((τ q : G))⁻¹ (s.field L hLK) : OpenSubgroup G) : Subgroup G))
    ?_ ?_ ?_ π (fun q => fixedModule_anti (inf_le_right (a := K'))
      (smul_mem_fixedModule π.2 _))).symm
  · intro q k hk
    show k ∈ (K' : Subgroup G) ⊓ ((conjOpen ((τ q : G))⁻¹ (s.field L hLK) : OpenSubgroup G) :
      Subgroup G) ↔ _
    rw [Subgroup.mem_inf, mem_conjOpen, inv_inv]
    exact ⟨fun h => h.2, fun h => ⟨hk, h⟩⟩
  · intro c hc
    let p : ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) ⧸ H :=
      (((⟨c⁻¹, (K : Subgroup G).inv_mem hc⟩ : (K : Subgroup G)) :
        (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) : _ ⧸ H)
    let q : Quotient (orbitRel (Subgroup.zpowers γ) (((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) ⧸ H)) := Quotient.mk'' p
    obtain ⟨⟨z, hz⟩, hzp⟩ := orbitRel_apply.1 (Quotient.mk_out' p : orbitRel _ _ q.out p)
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    have hzp' : γ ^ m • p = q.out := hzp
    rw [hqτ q, hγ, ← QuotientGroup.mk_zpow, MulAction.Quotient.smul_mk, smul_eq_mul,
      ← QuotientGroup.mk_mul, mk_mk_eq_iff hLK' hK'K] at hzp'
    refine ⟨q, _, hzp', ?_⟩
    have e : (τ q : G) * ((((⟨s.elt, s.mem⟩ : (K : Subgroup G)) ^ m *
        ⟨c⁻¹, (K : Subgroup G).inv_mem hc⟩ : (K : Subgroup G)) : G)⁻¹ * τ q)⁻¹ * c = s.elt ^ m := by
      simp only [Subgroup.coe_mul, SubgroupClass.coe_zpow]
      group
    rw [e]
    exact Subgroup.zpow_mem _ (s.elt_mem_field hLK) m
  · intro q q' k hk k' hk' hy
    obtain ⟨m, l, hl, hyeq⟩ := exists_eq_zpow_mul_of_mem_frobeniusClosure L.isOpen
      (FrobeniusLift.mem_normalizer (D := D) hLK s.mem) hy
    rw [← Quotient.out_eq q, ← Quotient.out_eq q']
    apply Quotient.sound
    refine (orbitRel_apply (G := Subgroup.zpowers γ)).2 ⟨⟨γ ^ m, Subgroup.zpow_mem_zpowers γ m⟩, ?_⟩
    show γ ^ m • q'.out = q.out
    rw [hqτ q, hqτ q', hγ, ← QuotientGroup.mk_zpow, MulAction.Quotient.smul_mk, smul_eq_mul,
      ← QuotientGroup.mk_mul, mk_mk_eq_iff hLK' hK'K]
    have hl1 : s.elt ^ m * l * (s.elt ^ m)⁻¹ ∈ (L : Subgroup G) :=
      conj_mem_of_normal ((K : Subgroup G).zpow_mem s.mem m) (hLK hl) hl
    have hl2 := conj_mem_of_normal ((K : Subgroup G).inv_mem (τ q).2) (hLK hl1) hl1
    have hτ' : (τ q' : G) = (s.elt ^ m * l)⁻¹ * ((τ q : G) * k⁻¹ * k') := by
      rw [← hyeq]
      group
    have e : ((((⟨s.elt, s.mem⟩ : (K : Subgroup G)) ^ m * τ q' : (K : Subgroup G)) : G))⁻¹ * τ q =
        k'⁻¹ * k * (((τ q : G))⁻¹ * (s.elt ^ m * l * (s.elt ^ m)⁻¹) * ((τ q : G))⁻¹⁻¹) := by
      simp only [Subgroup.coe_mul, SubgroupClass.coe_zpow]
      rw [hτ']
      group
    rw [e]
    exact (K' : Subgroup G).mul_mem
      ((K' : Subgroup G).mul_mem ((K' : Subgroup G).inv_mem hk') hk) (hLK' hl2)

end Ver

end ClassFieldData

end Sec_ALR_FunctorialityTransfer

section Sec_ALR_IsoCyclic

open ProfiniteInteger

section Augmentation

variable {G : Type*} [Group G] {A : Type*} [CommGroup A] [MulDistribMulAction G A]

theorem exists_eq_smul_div_of_mem_augmentation_of_generator {K L : Subgroup G} (hLK : L ≤ K)
    [(L.subgroupOf K).Normal] {τ : G} (hτ : τ ∈ K) (hgen : ∀ g ∈ K, ∃ m : ℕ, (τ ^ m)⁻¹ * g ∈ L)
    {x : A} (hx : x ∈ augmentation A K L) : ∃ b ∈ fixedModule A L, x = τ • b / b := by

  let S : Subgroup A :=
    { carrier := {y | ∃ b ∈ fixedModule A L, y = τ • b / b}
      one_mem' := ⟨1, Subgroup.one_mem _, by rw [smul_one, div_one]⟩
      mul_mem' := by
        rintro _ _ ⟨b, hb, rfl⟩ ⟨c, hc, rfl⟩
        exact ⟨b * c, Subgroup.mul_mem _ hb hc, by rw [smul_mul', mul_div_mul_comm]⟩
      inv_mem' := by
        rintro _ ⟨b, hb, rfl⟩
        exact ⟨b⁻¹, Subgroup.inv_mem _ hb, by rw [smul_inv', inv_div_inv, inv_div]⟩ }

  let T : Subgroup K :=
    { carrier := {g | ∀ a ∈ fixedModule A L, (g : G) • a / a ∈ S}
      one_mem' := fun a _ => by
        rw [OneMemClass.coe_one, one_smul, div_self']
        exact S.one_mem
      mul_mem' := by
        intro g h hg hh a ha
        have hha : (h : G) • a ∈ fixedModule A L := smul_mem_fixedModule_of_normal hLK h.2 ha
        have e : ((g * h : K) : G) • a / a = ((g : G) • ((h : G) • a) / ((h : G) • a)) * ((h : G) • a / a) := by
          rw [Subgroup.coe_mul, mul_smul]
          simp only [div_eq_mul_inv, mul_assoc, inv_mul_cancel_left]
        rw [e]
        exact S.mul_mem (hg _ hha) (hh a ha)
      inv_mem' := by
        intro g hg a ha
        have hga : ((g⁻¹ : K) : G) • a ∈ fixedModule A L :=
          smul_mem_fixedModule_of_normal hLK (g⁻¹).2 ha
        have e : ((g⁻¹ : K) : G) • a / a =
            ((g : G) • (((g⁻¹ : K) : G) • a) / (((g⁻¹ : K) : G) • a))⁻¹ := by
          rw [smul_smul, InvMemClass.coe_inv, mul_inv_cancel, one_smul, inv_div]
        rw [e]
        exact S.inv_mem (hg _ hga) }
  have hτT : (⟨τ, hτ⟩ : K) ∈ T := fun a ha => ⟨a, ha, rfl⟩
  have hLT : ∀ ρ : K, (ρ : G) ∈ L → ρ ∈ T := fun ρ hρ a ha => by
    rw [ha ρ hρ, div_self']
    exact S.one_mem
  have hTop : ∀ g : K, g ∈ T := by
    intro g
    obtain ⟨m, hm⟩ := hgen g g.2
    have hg : g = (⟨τ, hτ⟩ : K) ^ m * (((⟨τ, hτ⟩ : K) ^ m)⁻¹ * g) := by group
    rw [hg]
    exact T.mul_mem (T.pow_mem hτT m) (hLT _ (by simpa using hm))
  have hle : augmentation A K L ≤ S := by
    rw [augmentation, Subgroup.closure_le]
    rintro _ ⟨g, hg, a, ha, rfl⟩
    exact hTop ⟨g, hg⟩ a ha
  exact hle hx

end Augmentation

theorem exists_pow_eq_of_exists_zpow_eq {α : Type*} [Group α] [Finite α] {g x : α}
    (h : ∃ n : ℤ, g ^ n = x) : ∃ k : ℕ, g ^ k = x := by
  have hx : x ∈ Subgroup.zpowers g := Subgroup.mem_zpowers_iff.2 h
  rw [← mem_powers_iff_mem_zpowers] at hx
  exact (Submonoid.mem_powers_iff _ _).1 hx

namespace ClassFieldData

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] {A : Type*} [CommGroup A] [MulDistribMulAction G A]
  {D : ClassFieldData G A}

section Galois

omit [TotallyDisconnectedSpace G] in

theorem valuation_smul_of_map_eq (S : OpenSubgroup G) {g : G}
    (hg : (S : Subgroup G).map (MulAut.conj g).toMonoidHom = S) (a : fixedModule A (S : Subgroup G))
    (hga : g • (a : A) ∈ fixedModule A (S : Subgroup G)) :
    D.valuation S ⟨g • (a : A), hga⟩ = D.valuation S a := by
  rw [valuation_eq_iff, valuation_pow]
  congr 1
  ext
  have htop : (⊤ : Subgroup G).map (MulAut.conj g).toMonoidHom = ⊤ :=
    Subgroup.map_top_of_surjective _ (MulAut.conj g).surjective
  have h := smul_norm_of_map_eq (A := A) g htop hg a
  refine h.symm.trans ?_
  exact (norm A ⊤ (S : Subgroup G) a).2 g trivial

variable {K L : OpenSubgroup G}

omit [TotallyDisconnectedSpace G] in

theorem commutator_mem_of_isCyclic [((L : Subgroup G).subgroupOf K).Normal]
    (hcyc : IsCyclic ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K)) {a b : G}
    (ha : a ∈ (K : Subgroup G)) (hb : b ∈ (K : Subgroup G)) :
    a⁻¹ * b⁻¹ * a * b ∈ (L : Subgroup G) ⊓ D.deg.ker := by
  refine Subgroup.mem_inf.2 ⟨?_, MonoidHom.mem_ker.2 ?_⟩
  · have := hcyc
    have hc : ((⟨b, hb⟩ : (K : Subgroup G)) : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) *
        ((⟨a, ha⟩ : (K : Subgroup G)) : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) =
        ((⟨a, ha⟩ : (K : Subgroup G)) : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) *
        ((⟨b, hb⟩ : (K : Subgroup G)) : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) :=
      IsCyclic.commGroup.mul_comm _ _
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf] at hc
    simpa [mul_assoc] using hc
  · rw [map_mul, map_mul, map_mul, map_inv, map_inv,
      mul_right_comm (D.deg a)⁻¹, inv_mul_cancel, one_mul, inv_mul_cancel]

omit [TotallyDisconnectedSpace G] in

theorem conj_mem_of_isCyclic [((L : Subgroup G).subgroupOf K).Normal]
    (hcyc : IsCyclic ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K)) {H : Subgroup G}
    (hH : (L : Subgroup G) ⊓ D.deg.ker ≤ H) {g h : G} (hg : g ∈ (K : Subgroup G))
    (hh : h ∈ (K : Subgroup G)) (hhH : h ∈ H) : g * h * g⁻¹ ∈ H := by
  have hc := commutator_mem_of_isCyclic (D := D) hcyc hh (K.inv_mem hg)
  have e : g * h * g⁻¹ = h * (h⁻¹ * g⁻¹⁻¹ * h * g⁻¹) := by group
  rw [e]
  exact H.mul_mem hhH (hH hc)

end Galois

section Hull

variable (D) in

def maxUnramified (K L : OpenSubgroup G) : OpenSubgroup G where
  toSubgroup := (K : Subgroup G) ⊓ ((L : Subgroup G).map D.deg).comap D.deg
  isOpen' := Subgroup.isOpen_mono (H₁ := ((K ⊓ L : OpenSubgroup G) : Subgroup G))
    (fun x hx => ⟨hx.1, x, hx.2, rfl⟩) (K ⊓ L).isOpen

variable {K L : OpenSubgroup G}

omit [TotallyDisconnectedSpace G] in
theorem mem_maxUnramified {g : G} :
    g ∈ (D.maxUnramified K L : Subgroup G) ↔
      g ∈ (K : Subgroup G) ∧ ∃ l ∈ (L : Subgroup G), D.deg l = D.deg g :=
  Iff.rfl

omit [TotallyDisconnectedSpace G] in
theorem maxUnramified_le : D.maxUnramified K L ≤ K := fun _ hx => hx.1

omit [TotallyDisconnectedSpace G] in
theorem le_maxUnramified (hLK : L ≤ K) : L ≤ D.maxUnramified K L :=
  fun x hx => ⟨hLK hx, x, hx, rfl⟩

omit [TotallyDisconnectedSpace G] in

theorem inf_ker_le_maxUnramified :
    (K : Subgroup G) ⊓ D.deg.ker ≤ (D.maxUnramified K L : Subgroup G) :=
  fun x hx => ⟨hx.1, 1, (L : Subgroup G).one_mem, by rw [map_one, (MonoidHom.mem_ker.1 hx.2)]⟩

omit [TotallyDisconnectedSpace G] in

theorem relInertiaDegree_maxUnramified :
    relInertiaDegree D.deg (D.maxUnramified K L) L = 1 := by
  rw [relInertiaDegree, Subgroup.relIndex_eq_one]
  rintro _ ⟨g, hg, rfl⟩
  obtain ⟨l, hl, e⟩ := hg.2
  exact ⟨l, hl, e⟩

end Hull

section Unramified

variable {K L : OpenSubgroup G} (hLK : L ≤ K) [((L : Subgroup G).subgroupOf K).Normal]
  (hax : ClassFieldAxiom G A) [IsDiscreteModule G A]

theorem reciprocity_frobenius_of_unramified (hu : (K : Subgroup G) ⊓ D.deg.ker ≤ L)
    {φ : (K : Subgroup G)} (hφ : D.relDeg K φ = Multiplicative.ofAdd 1)
    {π : fixedModule A (K : Subgroup G)} (hπ : D.valuation K π = Multiplicative.ofAdd 1) :
    D.reciprocity hLK hax (φ : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) =
      (π : tateZero A (K : Subgroup G) (L : Subgroup G)) := by
  have hdφ : D.deg φ = Multiplicative.ofAdd (inertiaDegree D.deg K : ℤ̂) := by
    rw [← D.relDeg_pow, hφ, ← ofAdd_nsmul, nsmul_one]
  set s : D.FrobeniusLift K := FrobeniusLift.ofDegOne φ.2 hdφ with hs
  have hSK := s.field_le hLK

  have he : relRamificationIndex D.deg K (s.field L hLK) = 1 := by
    rw [relRamificationIndex, Subgroup.relIndex_eq_one]
    intro x hx
    exact le_frobeniusClosure ⟨hu ⟨hx.2, hx.1⟩, hx.1⟩
  have hrel : ((s.field L hLK : OpenSubgroup G) : Subgroup G).relIndex K = 1 := by
    rw [relIndex_eq_mul (d := D.deg) hSK, he, FrobeniusLift.relInertiaDegree_field hLK s]
    rfl
  have hπ' : D.valuation (s.field L hLK) ⟨π, fixedModule_anti hSK π.2⟩ = Multiplicative.ofAdd 1 := by
    rw [D.valuation_of_mem hSK π.2, he, pow_one]
    exact hπ
  have h := reciprocity_mk_eq_norm hLK hax s hπ'
  refine h.trans ?_
  congr 1
  ext
  rw [coe_norm_of_mem hSK π.2, hrel, pow_one]

end Unramified

section TotallyRamified

variable {K L : OpenSubgroup G} (hLK : L ≤ K) [((L : Subgroup G).subgroupOf K).Normal]
  (hax : ClassFieldAxiom G A) [IsDiscreteModule G A]

theorem reciprocity_injective_of_totallyRamified
    (hcyc : IsCyclic ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K))
    (htot : relInertiaDegree D.deg K L = 1) : Function.Injective (D.reciprocity hLK hax) := by

  have hdeg : ∀ k ∈ (K : Subgroup G), ∃ l ∈ (L : Subgroup G), D.deg l = D.deg k := by
    intro k hk
    obtain ⟨l, hl, e⟩ := (Subgroup.relIndex_eq_one.1 htot) ⟨k, hk, rfl⟩
    exact ⟨l, hl, e⟩

  obtain ⟨φ0, hφ0K, hdφ0⟩ := D.exists_deg_eq K
  obtain ⟨φ, hφL, hdφ⟩ := hdeg φ0 hφ0K

  have := hcyc
  obtain ⟨γ, hγ⟩ := exists_zpow_surjective ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K)
  obtain ⟨g0, rfl⟩ := QuotientGroup.mk_surjective γ
  obtain ⟨l0, hl0L, hl0⟩ := hdeg g0 g0.2
  obtain ⟨τ, hτdef⟩ : ∃ τ : G, τ = (g0 : G) * l0⁻¹ := ⟨_, rfl⟩
  have hτK : τ ∈ (K : Subgroup G) := hτdef ▸ K.mul_mem g0.2 (K.inv_mem (hLK hl0L))
  have hτker : D.deg τ = 1 := by rw [hτdef, map_mul, map_inv, hl0, mul_inv_cancel]
  have hτγ : (((⟨τ, hτK⟩ : (K : Subgroup G))) : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) =
      (g0 : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) := by
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simpa [hτdef, mul_assoc] using hl0L
  have hpow : ∀ q : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K, ∃ m : ℕ,
      (((⟨τ, hτK⟩ : (K : Subgroup G))) : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) ^ m = q := by
    intro q
    rw [hτγ]
    exact exists_pow_eq_of_exists_zpow_eq (hγ q)
  have hgen : ∀ k ∈ (K : Subgroup G), ∃ m : ℕ, (τ ^ m)⁻¹ * k ∈ (L : Subgroup G) := by
    intro k hk
    obtain ⟨m, hm⟩ := hpow (⟨k, hk⟩ : (K : Subgroup G))
    refine ⟨m, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq, Subgroup.mem_subgroupOf] at hm
    simpa using hm
  rw [injective_iff_map_eq_one]
  intro σ hσ
  obtain ⟨k, rfl⟩ := hpow σ
  rw [← QuotientGroup.mk_pow] at hσ ⊢

  obtain ⟨s, hs_elt, hs_deg⟩ : ∃ s : D.FrobeniusLift K, s.elt = τ ^ k * φ ∧ s.deg = 1 :=
    ⟨{ elt := τ ^ k * φ
       mem := K.mul_mem (K.pow_mem hτK k) (hLK hφL)
       deg := 1
       deg_pos := one_pos
       deg_eq := by rw [map_mul, map_pow, hτker, one_pow, one_mul, hdφ, hdφ0, one_mul] }, rfl, rfl⟩
  have hs : ((((⟨τ, hτK⟩ : (K : Subgroup G)) ^ k : (K : Subgroup G))) :
      (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) = ((⟨s.elt, s.mem⟩ : (K : Subgroup G)) :
      (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) := by
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simpa [hs_elt] using hφL
  rw [hs] at hσ
  obtain ⟨π0, hπ0⟩ := D.exists_prime (s.field L hLK)
  rw [reciprocity_mk_eq_norm hLK hax s hπ0, QuotientGroup.eq_one_iff] at hσ
  obtain ⟨b, hb⟩ := hσ

  have hvb : D.valuation L b = Multiplicative.ofAdd 1 := by
    have h1 := D.valuation_norm hLK b
    rw [htot, pow_one, hb, valuation_norm_prime hLK s hπ0, hs_deg, Nat.cast_one] at h1
    exact h1.symm

  obtain ⟨L1, hL1L, hL1S, hIL⟩ : ∃ L1 : OpenSubgroup G, L1 ≤ L ∧ L1 ≤ s.field L hLK ∧
      (L : Subgroup G) ⊓ D.deg.ker ≤ L1 :=
    ⟨L ⊓ s.field L hLK, inf_le_left, inf_le_right, fun x hx => ⟨hx.1, le_frobeniusClosure hx⟩⟩
  have hL1K : L1 ≤ K := hL1L.trans hLK
  obtain ⟨K1, hL1K1, hK1K, hIK1, hK1deg⟩ : ∃ K1 : OpenSubgroup G, L1 ≤ K1 ∧ K1 ≤ K ∧
      (K : Subgroup G) ⊓ D.deg.ker ≤ K1 ∧
      ∀ g ∈ (K1 : Subgroup G), ∃ l ∈ (L1 : Subgroup G), D.deg l = D.deg g :=
    ⟨D.maxUnramified K L1, le_maxUnramified hL1K, maxUnramified_le, inf_ker_le_maxUnramified,
      fun g hg => (mem_maxUnramified.1 hg).2⟩

  have hconj : ∀ g ∈ (K : Subgroup G), ∀ h ∈ (L1 : Subgroup G), g * h * g⁻¹ ∈ (L1 : Subgroup G) :=
    fun g hg h hh => conj_mem_of_isCyclic (D := D) hcyc hIL hg (hL1K hh) hh
  have hmapL1 : ∀ g ∈ (K : Subgroup G),
      (L1 : Subgroup G).map (MulAut.conj g).toMonoidHom = L1 := by
    intro g hg
    refine le_antisymm ?_ fun h hh => ⟨g⁻¹ * h * g, ?_, ?_⟩
    · rintro _ ⟨h, hh, rfl⟩
      exact hconj g hg h hh
    · simpa using hconj g⁻¹ (K.inv_mem hg) h hh
    · simp [MulAut.conj_apply, mul_assoc]
  have hsmulL1 : ∀ g ∈ (K : Subgroup G), ∀ a ∈ fixedModule A (L1 : Subgroup G),
      g • a ∈ fixedModule A (L1 : Subgroup G) := by
    intro g hg a ha h hh
    have hc : g⁻¹ * h * g ∈ (L1 : Subgroup G) := by simpa using hconj g⁻¹ (K.inv_mem hg) h hh
    calc h • g • a = g • (g⁻¹ * h * g) • a := by
          rw [smul_smul, smul_smul]
          congr 1
          group
      _ = g • a := by rw [ha _ hc]
  have hN1 : ((L1 : Subgroup G).subgroupOf K1).Normal :=
    ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      simpa using hconj g (hK1K g.2) n hn⟩

  have hτK1 : τ ∈ (K1 : Subgroup G) := hIK1 (Subgroup.mem_inf.2 ⟨hτK, MonoidHom.mem_ker.2 hτker⟩)
  have hgen1 : ∀ g ∈ (K1 : Subgroup G), ∃ m : ℕ, (τ ^ m)⁻¹ * g ∈ (L1 : Subgroup G) := by
    intro g hg
    obtain ⟨l, hl, hdl⟩ := hK1deg g hg
    obtain ⟨m, hm⟩ := hgen (g * l⁻¹) (K.mul_mem (hK1K hg) (K.inv_mem (hL1K hl)))
    refine ⟨m, ?_⟩
    have hker : (τ ^ m)⁻¹ * (g * l⁻¹) ∈ D.deg.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, map_pow, hτker, one_pow, inv_one, one_mul, map_mul,
        map_inv, hdl, mul_inv_cancel]
    have h := (L1 : Subgroup G).mul_mem (hIL (Subgroup.mem_inf.2 ⟨hm, hker⟩)) hl
    simpa [mul_assoc] using h
  have hcyc1 : IsCyclic ((K1 : Subgroup G) ⧸ (L1 : Subgroup G).subgroupOf K1) := by
    refine ⟨⟨((⟨τ, hτK1⟩ : (K1 : Subgroup G)) : (K1 : Subgroup G) ⧸ (L1 : Subgroup G).subgroupOf K1),
      fun q => ?_⟩⟩
    induction q using QuotientGroup.induction_on with
    | H g =>
      obtain ⟨m, hm⟩ := hgen1 g g.2
      refine ⟨m, ?_⟩
      show _ ^ ((m : ℕ) : ℤ) = _
      rw [zpow_natCast, ← QuotientGroup.mk_pow, QuotientGroup.eq, Subgroup.mem_subgroupOf]
      simpa using hm

  have hNS : (norm A (K : Subgroup G) (s.field L hLK : Subgroup G) π0 : A) =
      (norm A ((K : Subgroup G) ⊓ D.deg.ker) ((L : Subgroup G) ⊓ D.deg.ker)
        ⟨π0, fixedModule_anti le_frobeniusClosure π0.2⟩ : A) := by
    rw [coe_norm_field_eq hLK s hφ0K hdφ0 π0, Fintype.prod_eq_single
      (⟨0, by rw [hs_deg]; exact one_pos⟩ : Fin s.deg) (fun ν hν => absurd (Fin.ext (by
        have := ν.2
        omega)) hν), Fin.val_mk, pow_zero, one_smul]
  have hNL : (norm A (K : Subgroup G) (L : Subgroup G) b : A) =
      (norm A ((K : Subgroup G) ⊓ D.deg.ker) ((L : Subgroup G) ⊓ D.deg.ker)
        ⟨b, fixedModule_anti inf_le_left b.2⟩ : A) := by
    have h := coe_norm_eq_prod_smul_norm (A := A) D.deg (n := 1) one_pos
      (Nat.pos_of_ne_zero (D.inertiaDegree_ne_zero K)) (fun x hx => hLK hx)
      (fun x hx => by rw [one_mul]; exact toAdd_deg_mem_multiples (D := D) K (hLK hx))
      (fun k hk _ => hdeg k hk)
      (fun k hk => toAdd_deg_mem_multiples (D := D) K hk)
      (fun q hq => ⟨fun h => Subgroup.mem_inf.2 ⟨h, (Subgroup.mem_inf.1 hq).2⟩,
        fun h => (Subgroup.mem_inf.1 h).1⟩) hφ0K hdφ0 b (fixedModule_anti inf_le_left b.2)
    rw [h]
    simp
  have hNK1 : ∀ a : fixedModule A (L1 : Subgroup G),
      (norm A (K1 : Subgroup G) (L1 : Subgroup G) a : A) =
        (norm A ((K : Subgroup G) ⊓ D.deg.ker) ((L : Subgroup G) ⊓ D.deg.ker)
          ⟨a, fixedModule_anti hIL a.2⟩ : A) := fun a =>
    coe_norm_eq_of_mul_eq (fun x hx => hIK1 hx)
      (fun k hk => by
        obtain ⟨l, hl, hdl⟩ := hK1deg k hk
        refine ⟨k * l⁻¹, Subgroup.mem_inf.2 ⟨K.mul_mem (hK1K hk) (K.inv_mem (hL1K hl)), ?_⟩, ?_⟩
        · rw [MonoidHom.mem_ker, map_mul, map_inv, hdl, mul_inv_cancel]
        · simpa using hl)
      (fun q hq => ⟨fun h => Subgroup.mem_inf.2 ⟨hL1L h, (Subgroup.mem_inf.1 hq).2⟩,
        fun h => hIL h⟩) a _

  have hπ0L1 : (π0 : A) ∈ fixedModule A (L1 : Subgroup G) := fixedModule_anti hL1S π0.2
  have hbL1 : (b : A) ∈ fixedModule A (L1 : Subgroup G) := fixedModule_anti hL1L b.2
  have hy : norm A (K1 : Subgroup G) (L1 : Subgroup G)
      ((⟨π0, hπ0L1⟩ : fixedModule A (L1 : Subgroup G)) / ⟨b, hbL1⟩) = 1 := by
    rw [map_div, div_eq_one]
    ext
    rw [hNK1, hNK1]
    exact (hNS.symm.trans (congrArg Subtype.val hb).symm).trans hNL
  obtain ⟨-, hH1⟩ := hax K1 L1 hL1K1 hcyc1
  have hsub := (Nat.card_eq_one_iff_unique.1 hH1).1
  have haug : (((⟨π0, hπ0L1⟩ : fixedModule A (L1 : Subgroup G)) / ⟨b, hbL1⟩ :
      fixedModule A (L1 : Subgroup G)) : A) ∈ augmentation A (K1 : Subgroup G) (L1 : Subgroup G) :=
    (QuotientGroup.eq_one_iff (N := (augmentation A (K1 : Subgroup G) (L1 : Subgroup G)).comap
        ((fixedModule A (L1 : Subgroup G)).subtype.comp
          (norm A (K1 : Subgroup G) (L1 : Subgroup G)).ker.subtype))
      (⟨_, hy⟩ : (norm A (K1 : Subgroup G) (L1 : Subgroup G)).ker)).1 (Subsingleton.elim _ _)
  obtain ⟨x, hxL1, hxy⟩ := exists_eq_smul_div_of_mem_augmentation_of_generator
    (fun z hz => hL1K1 hz) hτK1 hgen1 haug
  have hπ0x : (π0 : A) = τ • x / x * b := by
    rw [← hxy, Subgroup.coe_div, div_mul_cancel]

  have hσπ : s.elt • (π0 : A) = π0 := π0.2 s.elt (s.elt_mem_field hLK)
  have hσb : s.elt • (b : A) = τ ^ k • (b : A) := by rw [hs_elt, mul_smul, b.2 φ hφL]
  have hcomm : s.elt • τ • x = τ • s.elt • x := by
    have hc : s.elt⁻¹ * τ⁻¹ * s.elt * τ ∈ (L1 : Subgroup G) :=
      hIL (commutator_mem_of_isCyclic (D := D) hcyc s.mem hτK)
    calc s.elt • τ • x = (τ * s.elt) • (s.elt⁻¹ * τ⁻¹ * s.elt * τ) • x := by
          rw [smul_smul, smul_smul]
          congr 1
          group
      _ = τ • s.elt • x := by rw [hxL1 _ hc, mul_smul]
  have e1 : τ • (s.elt • x) / s.elt • x * τ ^ k • (b : A) = τ • x / x * b := by
    have h := hσπ
    rw [hπ0x, smul_mul', smul_div', hcomm, hσb] at h
    exact h

  obtain ⟨c, hcdef⟩ : ∃ c : A, c = ∏ ν : Fin k, τ ^ (ν : ℕ) • (b : A) := ⟨_, rfl⟩
  obtain ⟨z, hzdef⟩ : ∃ z : A, z = x / s.elt • x := ⟨_, rfl⟩
  have hτc : τ • c / c = τ ^ k • (b : A) / b := by rw [hcdef]; exact smul_prod_pow_div τ (b : A) k
  have hkb : τ ^ k • (b : A) / b = τ • x / x / (τ • (s.elt • x) / s.elt • x) := by
    rw [div_eq_div_iff_mul_eq_mul, mul_comm (τ ^ k • (b : A))]
    exact e1
  have hτz : τ • z / z = τ • x / x / (τ • (s.elt • x) / s.elt • x) := by
    rw [hzdef, smul_div', div_div_div_comm]
  have hτw : τ • (c / z) = c / z := by
    have h : τ • (c / z) / (c / z) = 1 := by
      rw [smul_div', div_div_div_comm, hτc, hτz, hkb, div_self']
    exact div_eq_one.1 h
  have hcL1 : c ∈ fixedModule A (L1 : Subgroup G) := by
    rw [hcdef]
    exact Subgroup.prod_mem _ fun ν _ => hsmulL1 _ (K.pow_mem hτK _) _ hbL1
  have hσxL1 : s.elt • x ∈ fixedModule A (L1 : Subgroup G) := hsmulL1 _ s.mem x hxL1
  have hzL1 : z ∈ fixedModule A (L1 : Subgroup G) := by
    rw [hzdef]
    exact Subgroup.div_mem _ hxL1 hσxL1
  have hwL1 : c / z ∈ fixedModule A (L1 : Subgroup G) := Subgroup.div_mem _ hcL1 hzL1
  have hpw : ∀ m : ℕ, τ ^ m • (c / z) = c / z := by
    intro m
    induction m with
    | zero => rw [pow_zero, one_smul]
    | succ m ih => rw [pow_succ, mul_smul, hτw, ih]
  have hwK1 : c / z ∈ fixedModule A (K1 : Subgroup G) := by
    intro g hg
    obtain ⟨m, hm⟩ := hgen1 g hg
    have e : g = τ ^ m * ((τ ^ m)⁻¹ * g) := by group
    rw [e, mul_smul, hwL1 _ hm, hpw]

  have he1L : relRamificationIndex D.deg L L1 = 1 := by
    rw [relRamificationIndex, Subgroup.relIndex_eq_one]
    intro y hy
    exact hIL (Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hy).2, (Subgroup.mem_inf.1 hy).1⟩)
  have hvb1 : D.valuation L1 ⟨(b : A), hbL1⟩ = Multiplicative.ofAdd 1 := by
    rw [D.valuation_of_mem hL1L b.2, he1L, pow_one]
    exact hvb
  have hvτb : ∀ ν : ℕ, D.valuation L1 ⟨τ ^ ν • (b : A), hsmulL1 _ (K.pow_mem hτK ν) _ hbL1⟩ =
      Multiplicative.ofAdd 1 :=
    fun ν => (valuation_smul_of_map_eq L1 (hmapL1 _ (K.pow_mem hτK ν)) ⟨(b : A), hbL1⟩ _).trans hvb1
  have hvσx : D.valuation L1 ⟨s.elt • x, hσxL1⟩ = D.valuation L1 ⟨x, hxL1⟩ :=
    valuation_smul_of_map_eq L1 (hmapL1 _ s.mem) ⟨x, hxL1⟩ _
  have hweq : (⟨c / z, hwL1⟩ : fixedModule A (L1 : Subgroup G)) =
      (∏ ν : Fin k, (⟨τ ^ (ν : ℕ) • (b : A), hsmulL1 _ (K.pow_mem hτK _) _ hbL1⟩ :
        fixedModule A (L1 : Subgroup G))) /
        ((⟨x, hxL1⟩ : fixedModule A (L1 : Subgroup G)) / ⟨s.elt • x, hσxL1⟩) := by
    ext
    simp [hcdef, hzdef]
  have hvw : D.valuation L1 ⟨c / z, hwL1⟩ = Multiplicative.ofAdd (k : ℤ̂) := by
    rw [hweq, map_div, map_div, map_prod, hvσx, div_self', div_one]
    simp only [hvτb, Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← ofAdd_nsmul, nsmul_one]

  have hval := D.valuation_of_mem hL1K1 hwK1
  rw [hvw] at hval
  have he1 : 0 < relRamificationIndex D.deg K1 L1 :=
    Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero
  have hk : ((k : ℤ) : ℤ̂) =
      relRamificationIndex D.deg K1 L1 • Multiplicative.toAdd (D.valuation K1 ⟨c / z, hwK1⟩) := by
    have h := congrArg Multiplicative.toAdd hval
    rw [toAdd_ofAdd, toAdd_pow] at h
    rw [Int.cast_natCast]
    exact h
  have hdvd : relRamificationIndex D.deg K1 L1 ∣ k :=
    Int.natCast_dvd_natCast.1 (dvd_of_intCast_eq_nsmul he1 hk)

  have hNker : ((L1 : Subgroup G).subgroupOf (D.deg.ker ⊓ (K1 : Subgroup G))).Normal :=
    ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      simpa using hconj g (hK1K (Subgroup.mem_inf.1 g.2).2) n hn⟩
  have hτe : τ ^ relRamificationIndex D.deg K1 L1 ∈ (L1 : Subgroup G) := by
    have h := Subgroup.pow_index_mem ((L1 : Subgroup G).subgroupOf (D.deg.ker ⊓ (K1 : Subgroup G)))
      (⟨τ, Subgroup.mem_inf.2 ⟨MonoidHom.mem_ker.2 hτker, hτK1⟩⟩ :
        (D.deg.ker ⊓ (K1 : Subgroup G) : Subgroup G))
    rw [Subgroup.mem_subgroupOf, SubgroupClass.coe_pow] at h
    exact h
  obtain ⟨j, hj⟩ := hdvd
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, SubgroupClass.coe_pow, hj, pow_mul]
  exact hL1L (Subgroup.pow_mem _ hτe j)

theorem reciprocity_bijective_of_totallyRamified
    (hcyc : IsCyclic ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K))
    (htot : relInertiaDegree D.deg K L = 1) : Function.Bijective (D.reciprocity hLK hax) := by
  have hcard := (hax K L hLK hcyc).1
  have : Finite (tateZero A (K : Subgroup G) (L : Subgroup G)) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact Subgroup.FiniteIndex.index_ne_zero)
  refine (reciprocity_injective_of_totallyRamified hLK hax hcyc htot).bijective_of_nat_card_le ?_
  rw [hcard]
  exact le_rfl

end TotallyRamified

section Cyclic

variable {K L : OpenSubgroup G} (hLK : L ≤ K) [((L : Subgroup G).subgroupOf K).Normal]
  (hax : ClassFieldAxiom G A) [IsDiscreteModule G A]

theorem reciprocity_surjective_of_isCyclic
    (hcyc : IsCyclic ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K)) :
    Function.Surjective (D.reciprocity hLK hax) := by

  obtain ⟨M, hLM, hMK, huM, htotM⟩ : ∃ M : OpenSubgroup G, L ≤ M ∧ M ≤ K ∧
      (K : Subgroup G) ⊓ D.deg.ker ≤ M ∧ relInertiaDegree D.deg M L = 1 :=
    ⟨D.maxUnramified K L, le_maxUnramified hLK, maxUnramified_le, inf_ker_le_maxUnramified,
      relInertiaDegree_maxUnramified⟩
  have hNM : ((L : Subgroup G).subgroupOf M).Normal :=
    ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      have h := (inferInstance : ((L : Subgroup G).subgroupOf K).Normal).conj_mem ⟨n, hMK n.2⟩
        (by rw [Subgroup.mem_subgroupOf]; exact hn) ⟨g, hMK g.2⟩
      rw [Subgroup.mem_subgroupOf] at h
      simpa using h⟩

  have hcycM : IsCyclic ((M : Subgroup G) ⧸ (L : Subgroup G).subgroupOf M) := by
    have := hcyc
    refine isCyclic_of_injective
      (QuotientGroup.map ((L : Subgroup G).subgroupOf M) ((L : Subgroup G).subgroupOf K)
        (Subgroup.inclusion (fun x hx => hMK hx)) ?_) ?_
    · intro x hx
      rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
      rw [Subgroup.mem_subgroupOf] at hx
      exact hx
    · rw [injective_iff_map_eq_one]
      intro q hq
      induction q using QuotientGroup.induction_on with
      | H g =>
        rw [QuotientGroup.map_mk, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hq
        rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
        exact hq
  have hbijLM := reciprocity_bijective_of_totallyRamified hLM hax hcycM htotM

  obtain ⟨φ0, hφ0K, hdφ0⟩ := D.exists_deg_eq K
  obtain ⟨s1, hs1⟩ : ∃ s1 : D.FrobeniusLift K, s1.deg = 1 :=
    ⟨FrobeniusLift.ofDegOne hφ0K hdφ0, rfl⟩
  obtain ⟨π1, hπ1⟩ := D.exists_prime (s1.field L hLK)
  have hr1 := reciprocity_mk_eq_norm hLK hax s1 hπ1
  have hvc : D.valuation K (norm A (K : Subgroup G) (s1.field L hLK : Subgroup G) π1) =
      Multiplicative.ofAdd 1 := by
    rw [valuation_norm_prime hLK s1 hπ1, hs1, Nat.cast_one]
  intro x
  induction x using QuotientGroup.induction_on with
  | H a =>

    obtain ⟨j, hj⟩ : ∃ j : ℕ, (j : ZMod (D.relInertiaDegreePNat hMK)) =
        proj (D.relInertiaDegreePNat hMK) (Multiplicative.toAdd (D.valuation K a)) :=
      ⟨_, ZMod.natCast_zmod_val _⟩
    have hker : D.tateZeroVal hMK ((a / norm A (K : Subgroup G) (s1.field L hLK : Subgroup G) π1 ^ j :
        fixedModule A (K : Subgroup G)) : tateZero A (K : Subgroup G) (M : Subgroup G)) = 1 := by
      rw [tateZeroVal_mk, valuationMod_apply, map_div, map_pow, hvc, toAdd_div, toAdd_pow,
        toAdd_ofAdd, nsmul_one, map_sub, map_natCast, hj, sub_self, ofAdd_zero]
    have h0 : ((a / norm A (K : Subgroup G) (s1.field L hLK : Subgroup G) π1 ^ j :
        fixedModule A (K : Subgroup G)) : tateZero A (K : Subgroup G) (M : Subgroup G)) = 1 :=
      (D.tateZeroVal_bijective hax hMK huM).1 (by rw [hker, map_one])
    obtain ⟨a0, ha0⟩ := (QuotientGroup.eq_one_iff _).1 h0

    obtain ⟨q, hq⟩ := hbijLM.2 (a0 : tateZero A (M : Subgroup G) (L : Subgroup G))
    obtain ⟨s, rfl⟩ := exists_frobeniusLift_mk (D := D) hLM q
    obtain ⟨π2, hπ2⟩ := D.exists_prime (s.field L hLM)
    rw [reciprocity_mk_eq_norm hLM hax s hπ2, QuotientGroup.eq] at hq
    obtain ⟨b, hb⟩ := hq

    let s' : D.FrobeniusLift K :=
      { elt := s.elt
        mem := hMK s.mem
        deg := s.deg * relInertiaDegree D.deg K M
        deg_pos := Nat.mul_pos s.deg_pos (Nat.pos_of_ne_zero (D.relInertiaDegree_ne_zero hMK))
        deg_eq := by
          rw [s.deg_eq, inertiaDegree_eq_mul D.surjective_deg (K := (K : Subgroup G))
            (L := (M : Subgroup G)) (fun x hx => hMK hx), mul_assoc] }
    have hr' := reciprocity_mk_eq_norm hLK hax s' (π := π2) hπ2
    have hnn : norm A (K : Subgroup G) (M : Subgroup G)
        (norm A (M : Subgroup G) (s.field L hLM : Subgroup G) π2) =
          norm A (K : Subgroup G) (s.field L hLM : Subgroup G) π2 :=
      norm_norm (fun x hx => s.field_le hLM hx) (fun x hx => hMK hx) π2
    refine ⟨((⟨s'.elt, s'.mem⟩ : (K : Subgroup G)) : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) *
      ((⟨s1.elt, s1.mem⟩ : (K : Subgroup G)) : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) ^ j, ?_⟩
    rw [map_mul, map_pow, hr', hr1, ← QuotientGroup.mk_pow, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    refine ⟨b, ?_⟩
    have h1 := congrArg (norm A (K : Subgroup G) (M : Subgroup G)) hb
    rw [norm_norm (fun x hx => hLM hx) (fun x hx => hMK hx), map_mul, map_inv, hnn, ha0] at h1
    rw [h1, div_eq_mul_inv, mul_inv_rev]
    ac_rfl

theorem reciprocity_bijective_of_isCyclic
    (hcyc : IsCyclic ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K)) :
    Function.Bijective (D.reciprocity hLK hax) := by
  have hcard := (hax K L hLK hcyc).1
  refine (reciprocity_surjective_of_isCyclic hLK hax hcyc).bijective_of_nat_card_le ?_
  rw [hcard]
  exact le_rfl

variable (D) in

noncomputable def reciprocityEquiv
    (hcyc : IsCyclic ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K)) :
    (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K ≃* tateZero A (K : Subgroup G) (L : Subgroup G) :=
  MulEquiv.ofBijective _ (reciprocity_bijective_of_isCyclic (D := D) hLK hax hcyc)

end Cyclic

end ClassFieldData

end Sec_ALR_IsoCyclic

section Sec_ALR_IsoPGroup

open ProfiniteInteger

section Normal

variable {G : Type*} [Group G]

theorem normal_subgroupOf_of_le {K L M : Subgroup G} (hMK : M ≤ K) [hN : (L.subgroupOf K).Normal] :
    (L.subgroupOf M).Normal :=
  ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have h := hN.conj_mem ⟨n, hMK n.2⟩ (by rw [Subgroup.mem_subgroupOf]; exact hn) ⟨g, hMK g.2⟩
    rw [Subgroup.mem_subgroupOf] at h
    simpa using h⟩

theorem card_quotient_eq_relIndex (K L : Subgroup G) :
    Nat.card (K ⧸ L.subgroupOf K) = L.relIndex K :=
  (Subgroup.index_eq_card _).symm

end Normal

section FixedField

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

variable {K L : OpenSubgroup G} (hLK : L ≤ K) [((L : Subgroup G).subgroupOf K).Normal]

def fixedOpen (H : Subgroup ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K)) : OpenSubgroup G where
  toSubgroup := (H.comap (QuotientGroup.mk' _)).map (K : Subgroup G).subtype
  isOpen' := Subgroup.isOpen_mono (H₁ := (L : Subgroup G)) (fun x hx => ⟨⟨x, hLK hx⟩, by
      show ((⟨x, hLK hx⟩ : (K : Subgroup G)) : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) ∈ H
      rw [(QuotientGroup.eq_one_iff (⟨x, hLK hx⟩ : (K : Subgroup G))).2 (Subgroup.mem_subgroupOf.2 hx)]
      exact H.one_mem, rfl⟩) L.isOpen

theorem mem_fixedOpen {H : Subgroup ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K)} {g : G} :
    g ∈ ((fixedOpen hLK H : OpenSubgroup G) : Subgroup G) ↔
      ∃ h : g ∈ (K : Subgroup G), ((⟨g, h⟩ : (K : Subgroup G)) :
        (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) ∈ H := by
  show g ∈ (H.comap (QuotientGroup.mk' _)).map (K : Subgroup G).subtype ↔ _
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k.2, hk⟩
  · rintro ⟨h, hH⟩
    exact ⟨⟨g, h⟩, hH, rfl⟩

variable (H : Subgroup ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K))

theorem le_fixedOpen : L ≤ fixedOpen hLK H := fun x hx =>
  (mem_fixedOpen hLK).2 ⟨hLK hx, by
    rw [(QuotientGroup.eq_one_iff (⟨x, hLK hx⟩ : (K : Subgroup G))).2 (Subgroup.mem_subgroupOf.2 hx)]
    exact H.one_mem⟩

theorem fixedOpen_le : fixedOpen hLK H ≤ K := fun _ hx => ((mem_fixedOpen hLK).1 hx).1

instance normal_fixedOpen_self :
    ((L : Subgroup G).subgroupOf ((fixedOpen hLK H : OpenSubgroup G) : Subgroup G)).Normal :=
  normal_subgroupOf_of_le (K := (K : Subgroup G)) (fun _ hx => ((mem_fixedOpen hLK).1 hx).1)

instance normal_fixedOpen [hH : H.Normal] :
    (((fixedOpen hLK H : OpenSubgroup G) : Subgroup G).subgroupOf K).Normal :=
  ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨_, hnH⟩ := (mem_fixedOpen hLK).1 hn
    refine (mem_fixedOpen hLK).2 ⟨(g * n * g⁻¹).2, ?_⟩
    exact hH.conj_mem _ hnH (g : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K)⟩

theorem range_galRestrict_fixedOpen [CompactSpace G] :
    (galRestrict (K := K) (L := L) (K' := fixedOpen hLK H) (L' := L) (fixedOpen_le hLK H)
      le_rfl).range = H := by
  ext q
  induction q using QuotientGroup.induction_on with
  | H k =>
    rw [mk_mem_range_galRestrict_iff (le_fixedOpen hLK H) (fixedOpen_le hLK H), mem_fixedOpen]
    exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨k.2, h⟩⟩

noncomputable def galFixedEquiv [CompactSpace G] :
    ((fixedOpen hLK H : OpenSubgroup G) : Subgroup G) ⧸
      (L : Subgroup G).subgroupOf ((fixedOpen hLK H : OpenSubgroup G) : Subgroup G) ≃* H :=
  (MonoidHom.ofInjective (galRestrict_injective (K := K) (L := L) (fixedOpen_le hLK H))).trans
    (MulEquiv.subgroupCongr (range_galRestrict_fixedOpen hLK H))

theorem relIndex_fixedOpen [CompactSpace G] :
    (L : Subgroup G).relIndex (fixedOpen hLK H) = Nat.card H := by
  rw [← card_quotient_eq_relIndex]
  exact Nat.card_congr (galFixedEquiv hLK H).toEquiv

theorem relIndex_fixedOpen_eq_index [CompactSpace G] :
    ((fixedOpen hLK H : OpenSubgroup G) : Subgroup G).relIndex K = H.index := by
  have h1 := Subgroup.relIndex_mul_relIndex (H := (L : Subgroup G))
    (K := ((fixedOpen hLK H : OpenSubgroup G) : Subgroup G)) (L := (K : Subgroup G))
    (fun x hx => le_fixedOpen hLK H hx) (fun x hx => fixedOpen_le hLK H hx)
  rw [relIndex_fixedOpen, ← card_quotient_eq_relIndex (K : Subgroup G) (L : Subgroup G),
    ← H.card_mul_index] at h1
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h1

end FixedField

section Restrict

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]

omit [IsTopologicalGroup G] [CompactSpace G] in

theorem galRestrict_surjective {K L M : OpenSubgroup G} [((L : Subgroup G).subgroupOf K).Normal]
    [((M : Subgroup G).subgroupOf K).Normal] (hLM : L ≤ M) :
    Function.Surjective (galRestrict (K := K) (L := M) (K' := K) (L' := L) le_rfl hLM) := by
  intro q
  induction q using QuotientGroup.induction_on with
  | H τ => exact ⟨(τ : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K), rfl⟩

omit [CompactSpace G] in

theorem conjOpen_eq_of_normal {K M : OpenSubgroup G} (hMK : M ≤ K)
    [((M : Subgroup G).subgroupOf K).Normal] {g : G} (hg : g ∈ (K : Subgroup G)) :
    conjOpen g M = M := by
  have h := map_conj_eq_of_normal (L := (M : Subgroup G)) (fun _ hy => hMK hy) hg
  apply OpenSubgroup.ext
  intro x
  show x ∈ ((conjOpen g M : OpenSubgroup G) : Subgroup G) ↔ x ∈ (M : Subgroup G)
  rw [coe_conjOpen, h]

theorem Abelianization.lift_injective_of_ker_le {Γ T : Type*} [Group Γ] [CommGroup T] (f : Γ →* T)
    (h : f.ker ≤ commutator Γ) : Function.Injective (Abelianization.lift f) := by
  rw [injective_iff_map_eq_one]
  intro z hz
  induction z using QuotientGroup.induction_on with
  | H q =>
    have hq : Abelianization.lift f (Abelianization.of q) = 1 := hz
    rw [Abelianization.lift_apply_of] at hq
    have := h hq
    rw [← Abelianization.ker_of, MonoidHom.mem_ker] at this
    exact this

end Restrict

namespace ClassFieldData

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] {A : Type*} [CommGroup A] [MulDistribMulAction G A]
  {D : ClassFieldData G A} (hax : ClassFieldAxiom G A) [IsDiscreteModule G A]

theorem reciprocity_congr {K₁ K₂ L₁ L₂ : OpenSubgroup G} (hK : K₁ = K₂) (hL : L₁ = L₂)
    (h1 : L₁ ≤ K₁) (h2 : L₂ ≤ K₂) [((L₁ : Subgroup G).subgroupOf K₁).Normal]
    [((L₂ : Subgroup G).subgroupOf K₂).Normal] {τ : G} (hτ1 : τ ∈ (K₁ : Subgroup G))
    (hτ2 : τ ∈ (K₂ : Subgroup G)) {a : A} (ha1 : a ∈ fixedModule A (K₁ : Subgroup G))
    (ha2 : a ∈ fixedModule A (K₂ : Subgroup G))
    (h : D.reciprocity h1 hax ((⟨τ, hτ1⟩ : (K₁ : Subgroup G)) :
        (K₁ : Subgroup G) ⧸ (L₁ : Subgroup G).subgroupOf K₁) =
      ((⟨a, ha1⟩ : fixedModule A (K₁ : Subgroup G)) : tateZero A (K₁ : Subgroup G) (L₁ : Subgroup G))) :
    D.reciprocity h2 hax ((⟨τ, hτ2⟩ : (K₂ : Subgroup G)) :
        (K₂ : Subgroup G) ⧸ (L₂ : Subgroup G).subgroupOf K₂) =
      ((⟨a, ha2⟩ : fixedModule A (K₂ : Subgroup G)) : tateZero A (K₂ : Subgroup G) (L₂ : Subgroup G)) := by
  subst hK hL
  exact h

section Tower

variable {K M L : OpenSubgroup G} (hLM : L ≤ M) (hMK : M ≤ K)
  [((L : Subgroup G).subgroupOf K).Normal] [((L : Subgroup G).subgroupOf M).Normal]
  [((M : Subgroup G).subgroupOf K).Normal]

theorem reciprocity_surjective_of_tower (h1 : Function.Surjective (D.reciprocity hLM hax))
    (h2 : Function.Surjective (D.reciprocity hMK hax)) :
    Function.Surjective (D.reciprocity (hLM.trans hMK) hax) := by
  have hLK : L ≤ K := hLM.trans hMK
  intro x
  induction x using QuotientGroup.induction_on with
  | H a =>
    obtain ⟨q', hq'⟩ := h2 (a : tateZero A (K : Subgroup G) (M : Subgroup G))
    obtain ⟨q, rfl⟩ := galRestrict_surjective (K := K) hLM q'
    have e1 := D.reciprocity_galRestrict hax hMK hLK le_rfl hLM q
    obtain ⟨c, hc⟩ := QuotientGroup.mk_surjective (D.reciprocity hLK hax q)
    rw [hq', ← hc, normTateZero_mk, norm_self, MonoidHom.id_apply, QuotientGroup.eq] at e1
    obtain ⟨b, hb⟩ := e1
    obtain ⟨p, hp⟩ := h1 ((b⁻¹ : fixedModule A (M : Subgroup G)) :
      tateZero A (M : Subgroup G) (L : Subgroup G))
    have e2 := D.reciprocity_galRestrict hax hLK hLM hMK le_rfl p
    refine ⟨q * galRestrict hMK le_rfl p, ?_⟩
    rw [map_mul, e2, hp, ← hc, normTateZero_mk, map_inv, hb, ← QuotientGroup.mk_mul]
    congr 1
    group

theorem ker_reciprocity_le_of_tower
    (hcyc : IsCyclic ((K : Subgroup G) ⧸ (M : Subgroup G).subgroupOf K))
    (hs : Function.Surjective (D.reciprocity hLM hax))
    (hk : (D.reciprocity hLM hax).ker ≤ commutator ((M : Subgroup G) ⧸ (L : Subgroup G).subgroupOf M)) :
    (D.reciprocity (hLM.trans hMK) hax).ker ≤
      commutator ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) := by
  have hLK : L ≤ K := hLM.trans hMK
  have hMK' : (M : Subgroup G) ≤ K := fun _ hx => hMK hx
  have hLM' : (L : Subgroup G) ≤ M := fun _ hx => hLM hx
  have hLK' : (L : Subgroup G) ≤ K := fun _ hx => hLK hx
  set ι := galRestrict (K := K) (L := L) (K' := M) (L' := L) hMK le_rfl with hι
  set S := (commutator ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K)).comap ι with hS

  have hconj : ∀ (g : G) (hg : g ∈ (K : Subgroup G)) (τ : G) (hτ : τ ∈ (M : Subgroup G)) (x : A)
      (hx : x ∈ fixedModule A (M : Subgroup G)),
      D.reciprocity hLM hax ((⟨τ, hτ⟩ : (M : Subgroup G)) :
          (M : Subgroup G) ⧸ (L : Subgroup G).subgroupOf M) =
        ((⟨x, hx⟩ : fixedModule A (M : Subgroup G)) :
          tateZero A (M : Subgroup G) (L : Subgroup G)) →
      D.reciprocity hLM hax ((⟨g * τ * g⁻¹, conj_mem_of_normal hg (hMK' hτ) hτ⟩ :
          (M : Subgroup G)) : (M : Subgroup G) ⧸ (L : Subgroup G).subgroupOf M) =
        ((⟨g • x, smul_mem_fixedModule_of_normal hMK' hg hx⟩ : fixedModule A (M : Subgroup G)) :
          tateZero A (M : Subgroup G) (L : Subgroup G)) := by
    intro g hg τ hτ x hx h
    have e := D.reciprocity_galConj hax g hLM
      ((⟨τ, hτ⟩ : (M : Subgroup G)) : (M : Subgroup G) ⧸ (L : Subgroup G).subgroupOf M)
    rw [galConj_mk, h, tateZeroConj_mk] at e
    exact D.reciprocity_congr hax (conjOpen_eq_of_normal hMK hg) (conjOpen_eq_of_normal hLK hg)
      (conjOpen_mono g hLM) hLM _ _ (a := g • x) _ _ e
  intro q hq
  rw [MonoidHom.mem_ker] at hq

  have hq1 : galRestrict (K := K) (L := M) (K' := K) (L' := L) le_rfl hLM q = 1 := by
    apply (reciprocity_bijective_of_isCyclic (D := D) hMK hax hcyc).1
    rw [map_one, D.reciprocity_galRestrict hax hMK hLK le_rfl hLM q, hq, map_one]
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
  rw [galRestrict_mk, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hq1
  set t : (M : Subgroup G) ⧸ (L : Subgroup G).subgroupOf M :=
    ((⟨k, hq1⟩ : (M : Subgroup G)) : (M : Subgroup G) ⧸ (L : Subgroup G).subgroupOf M) with ht
  have hιt : ι t = QuotientGroup.mk k := rfl
  rw [← hιt] at hq ⊢

  have h2 := D.reciprocity_galRestrict hax hLK hLM hMK le_rfl t
  rw [hq] at h2
  obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective (D.reciprocity hLM hax t)
  rw [← ha, normTateZero_mk] at h2
  obtain ⟨b, hb⟩ := (QuotientGroup.eq_one_iff _).1 h2.symm
  set a' : fixedModule A (M : Subgroup G) := a * (norm A (M : Subgroup G) (L : Subgroup G) b)⁻¹
    with ha'def
  have ha' : norm A (K : Subgroup G) (M : Subgroup G) a' = 1 := by
    rw [ha'def, map_mul, map_inv, norm_norm hLM' hMK' b, hb, mul_inv_cancel]
  have hmk : (QuotientGroup.mk a' : tateZero A (M : Subgroup G) (L : Subgroup G)) =
      D.reciprocity hLM hax t := by
    rw [← ha, QuotientGroup.eq]
    exact ⟨b, by rw [ha'def]; group⟩

  have hsub : Subsingleton (tateNegOne A (K : Subgroup G) (M : Subgroup G)) :=
    (Nat.card_eq_one_iff_unique.1 (hax K M hMK hcyc).2).1
  have haug : (a' : A) ∈ augmentation A (K : Subgroup G) (M : Subgroup G) := by
    have h0 : ((⟨a', ha'⟩ : (norm A (K : Subgroup G) (M : Subgroup G)).ker) :
        tateNegOne A (K : Subgroup G) (M : Subgroup G)) = 1 := Subsingleton.elim _ _
    exact (QuotientGroup.eq_one_iff
      (⟨a', ha'⟩ : (norm A (K : Subgroup G) (M : Subgroup G)).ker)).1 h0

  set P : Subgroup A := ((S.map (D.reciprocity hLM hax)).comap
    (QuotientGroup.mk' (norm A (M : Subgroup G) (L : Subgroup G)).range)).map
      (fixedModule A (M : Subgroup G)).subtype with hP
  have hAP : augmentation A (K : Subgroup G) (M : Subgroup G) ≤ P := by
    rw [augmentation, Subgroup.closure_le]
    rintro _ ⟨g, hg, x, hx, rfl⟩
    obtain ⟨ρ, hρ⟩ := hs ((⟨x, hx⟩ : fixedModule A (M : Subgroup G)) :
      tateZero A (M : Subgroup G) (L : Subgroup G))
    obtain ⟨τ, rfl⟩ := QuotientGroup.mk_surjective ρ
    have e := hconj g hg τ τ.2 x hx hρ
    refine ⟨⟨g • x / x, (fixedModule A (M : Subgroup G)).div_mem
      (smul_mem_fixedModule_of_normal hMK' hg hx) hx⟩, ?_, rfl⟩
    refine ⟨((⟨g * τ * g⁻¹, conj_mem_of_normal hg (hMK' τ.2) τ.2⟩ : (M : Subgroup G)) :
      (M : Subgroup G) ⧸ (L : Subgroup G).subgroupOf M) * (τ : (M : Subgroup G) ⧸ _)⁻¹, ?_, ?_⟩
    · show ι (_ * _) ∈ commutator _
      rw [map_mul, map_inv]
      have hc := Subgroup.commutator_mem_commutator
        (Subgroup.mem_top ((⟨g, hg⟩ : (K : Subgroup G)) : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K))
        (Subgroup.mem_top ((⟨τ, hMK' τ.2⟩ : (K : Subgroup G)) :
          (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K))
      rw [commutatorElement_def] at hc
      exact hc
    · rw [map_mul, map_inv, e, hρ, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
        QuotientGroup.mk'_apply]
      congr 1
      exact Subtype.ext (div_eq_mul_inv _ _).symm
  obtain ⟨y, hy, hya⟩ := hAP haug
  obtain rfl : y = a' := Subtype.ext hya
  obtain ⟨s, hsS, hrs⟩ := hy
  rw [QuotientGroup.mk'_apply, hmk] at hrs
  have hts : t * s⁻¹ ∈ (D.reciprocity hLM hax).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hrs, mul_inv_cancel]
  have hcomm : ι (t * s⁻¹) ∈ commutator ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) := by
    have h := hk hts
    rw [← Abelianization.ker_of, MonoidHom.mem_ker] at h ⊢
    rw [← Abelianization.map_of, h, map_one]
  have e3 : ι t = ι (t * s⁻¹) * ι s := by rw [map_mul, map_inv, inv_mul_cancel_right]
  rw [e3]
  exact Subgroup.mul_mem _ hcomm hsS

end Tower

section PGroup

theorem reciprocity_of_isPGroup {p : ℕ} [hp : Fact p.Prime] (n : ℕ) :
    ∀ {K L : OpenSubgroup G} (hLK : L ≤ K) [((L : Subgroup G).subgroupOf K).Normal],
      (L : Subgroup G).relIndex K = n →
      IsPGroup p ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) →
      Function.Surjective (D.reciprocity hLK hax) ∧
        (D.reciprocity hLK hax).ker ≤ commutator ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro K L hLK _ hn hP
  by_cases hcyc : IsCyclic ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K)
  · have hb := reciprocity_bijective_of_isCyclic (D := D) hLK hax hcyc
    refine ⟨hb.2, fun q hq => ?_⟩
    rw [(injective_iff_map_eq_one _).1 hb.1 q hq]
    exact Subgroup.one_mem _
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hk
    exact hcyc (@isCyclic_of_subsingleton _ _ (Nat.card_eq_one_iff_unique.1 hk).1)

  obtain ⟨H, hH⟩ := Sylow.exists_subgroup_card_pow_prime p
    (pow_dvd_pow p (Nat.sub_le k 1) |>.trans hk.symm.dvd)
  have hpk : p ^ (k - 1) * p = p ^ k := by rw [← pow_succ, Nat.sub_add_cancel (Nat.pos_of_ne_zero hk0)]
  have hHi : H.index = p := by
    have h := H.card_mul_index
    rw [hH, hk, ← hpk] at h
    exact Nat.eq_of_mul_eq_mul_left (pow_pos hp.out.pos _) h
  have hmin : (p ^ k).minFac = p := by
    have h2 : (p ^ k).minFac.Prime := Nat.minFac_prime (Nat.one_lt_pow hk0 hp.out.one_lt).ne'
    exact (Nat.prime_dvd_prime_iff_eq h2 hp.out).1 (h2.dvd_of_dvd_pow (Nat.minFac_dvd _))
  have hHn : H.Normal := Subgroup.normal_of_index_eq_minFac_card (by rw [hHi, hk, hmin])
  set M := fixedOpen hLK H with hM
  have hLM : L ≤ M := le_fixedOpen hLK H
  have hMK : M ≤ K := fixedOpen_le hLK H

  have hcycM : IsCyclic ((K : Subgroup G) ⧸ (M : Subgroup G).subgroupOf K) :=
    isCyclic_of_prime_card (p := p) (by
      rw [card_quotient_eq_relIndex, hM, relIndex_fixedOpen_eq_index, hHi])

  have hPM : IsPGroup p ((M : Subgroup G) ⧸ (L : Subgroup G).subgroupOf M) :=
    (hP.to_subgroup H).of_equiv (galFixedEquiv hLK H).symm
  have hLMn : (L : Subgroup G).relIndex M = p ^ (k - 1) := by
    rw [hM, relIndex_fixedOpen, hH]
  have hlt : p ^ (k - 1) < n := by
    rw [← hn, ← card_quotient_eq_relIndex, hk]
    exact Nat.pow_lt_pow_right hp.out.one_lt (Nat.sub_lt (Nat.pos_of_ne_zero hk0) one_pos)
  obtain ⟨hs, hker⟩ := ih _ hlt hLM hLMn hPM
  exact ⟨D.reciprocity_surjective_of_tower hax hLM hMK hs
      (reciprocity_bijective_of_isCyclic (D := D) hMK hax hcycM).2,
    D.ker_reciprocity_le_of_tower hax hLM hMK hcycM hs hker⟩

end PGroup

end ClassFieldData

end Sec_ALR_IsoPGroup

section Sec_ALR_Isomorphism

open ProfiniteInteger MulAction

section Transfer

theorem transfer_of_comp_subtype {Γ : Type*} [Group Γ] (H : Subgroup Γ) [H.FiniteIndex] (g : Γ) :
    ((Abelianization.of : Γ →* Abelianization Γ).comp H.subtype).transfer g =
      Abelianization.of g ^ H.index :=
  transfer_of_comp_subtype_aux H g

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]

theorem map_verlagerung {K K' L : OpenSubgroup G} [((L : Subgroup G).subgroupOf K).Normal]
    [((L : Subgroup G).subgroupOf K').Normal] (hK'K : K' ≤ K)
    (g : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) :
    Abelianization.map (galRestrict (K := K) (L := L) (K' := K') (L' := L) hK'K le_rfl)
        (verlagerung hK'K g) =
      Abelianization.of g ^ (galRestrict (K := K) (L := L) (K' := K') (L' := L) hK'K le_rfl).range.index := by
  rw [verlagerung, map_transfer, ← transfer_of_comp_subtype]
  have e : (Abelianization.map (galRestrict (K := K) (L := L) (K' := K') (L' := L) hK'K le_rfl)).comp
      ((Abelianization.of).comp
        (MonoidHom.ofInjective (galRestrict_injective (L := L) hK'K)).symm.toMonoidHom) =
      (Abelianization.of).comp
        (galRestrict (K := K) (L := L) (K' := K') (L' := L) hK'K le_rfl).range.subtype := by
    refine MonoidHom.ext fun h => ?_
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, Abelianization.map_of,
      MonoidHom.comp_apply, Subgroup.coe_subtype]
    congr 1
    have := congrArg Subtype.val
      ((MonoidHom.ofInjective (galRestrict_injective (L := L) hK'K)).apply_symm_apply h)
    rw [MonoidHom.ofInjective_apply] at this
    exact this
  rw [e]

end Transfer

namespace ClassFieldData

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] {A : Type*} [CommGroup A] [MulDistribMulAction G A]
  {D : ClassFieldData G A}

section General

variable {K L : OpenSubgroup G} (hLK : L ≤ K) [((L : Subgroup G).subgroupOf K).Normal]
  (hax : ClassFieldAxiom G A) [IsDiscreteModule G A]

theorem reciprocity_fixedOpen_sylow {p : ℕ} [Fact p.Prime]
    (P : Sylow p ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K)) :
    Function.Surjective (D.reciprocity (le_fixedOpen hLK (P : Subgroup ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K))) hax) ∧
      (D.reciprocity (le_fixedOpen hLK (P : Subgroup ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K))) hax).ker ≤
        commutator (((fixedOpen hLK (P : Subgroup ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K)) : OpenSubgroup G) : Subgroup G) ⧸
          (L : Subgroup G).subgroupOf ((fixedOpen hLK (P : Subgroup ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K)) : OpenSubgroup G) : Subgroup G)) :=
  reciprocity_of_isPGroup hax _ (le_fixedOpen hLK _) rfl
    (P.isPGroup'.of_equiv (galFixedEquiv hLK (P : Subgroup ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K))).symm)

theorem reciprocity_surjective : Function.Surjective (D.reciprocity hLK hax) := by
  classical
  intro x
  by_contra hx
  set R := (D.reciprocity hLK hax).range with hR
  have hxR : x ∉ R := fun h => hx (MonoidHom.mem_range.1 h)
  set y : tateZero A (K : Subgroup G) (L : Subgroup G) ⧸ R := (x : _ ⧸ R) with hy
  have hy1 : y ≠ 1 := fun h => hxR ((QuotientGroup.eq_one_iff x).1 h)
  obtain ⟨p, hp, hpy⟩ := Nat.exists_prime_and_dvd (mt orderOf_eq_one_iff.1 hy1)
  have := Fact.mk hp
  let P : Sylow p ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) := Classical.arbitrary _
  have hMK : ((fixedOpen hLK (P : Subgroup ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K)) : OpenSubgroup G) : Subgroup G) ≤ K :=
    fun _ h => fixedOpen_le hLK _ h
  obtain ⟨hs, -⟩ := reciprocity_fixedOpen_sylow (D := D) hLK hax P

  have hyP : y ^ (P : Subgroup ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K)).index = 1 := by
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨t, ht⟩ := hs ((⟨a, fixedModule_anti hMK a.2⟩ :
      fixedModule A ((fixedOpen hLK (P : Subgroup ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K)) : OpenSubgroup G) : Subgroup G)) :
        tateZero A _ (L : Subgroup G))
    have e := D.reciprocity_galRestrict hax hLK (le_fixedOpen hLK _) (fixedOpen_le hLK _) le_rfl t
    rw [ht, normTateZero_mk] at e
    have hn : norm A (K : Subgroup G) ((fixedOpen hLK (P : Subgroup ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K)) : OpenSubgroup G) : Subgroup G)
        ⟨a, fixedModule_anti hMK a.2⟩ = a ^ (P : Subgroup ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K)).index := by
      apply Subtype.ext
      rw [coe_norm_of_mem hMK a.2, relIndex_fixedOpen_eq_index, SubgroupClass.coe_pow]
    rw [hn, QuotientGroup.mk_pow] at e
    rw [hy, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact ⟨_, e⟩
  exact Sylow.not_dvd_index P (hpy.trans (orderOf_dvd_of_pow_eq_one hyP))

theorem ker_reciprocity_le_commutator :
    (D.reciprocity hLK hax).ker ≤ commutator ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) := by
  classical
  intro σ hσ
  rw [MonoidHom.mem_ker] at hσ
  rw [← Abelianization.ker_of, MonoidHom.mem_ker]
  by_contra h1
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (mt orderOf_eq_one_iff.1 h1)
  have := Fact.mk hp
  let P : Sylow p ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) := Classical.arbitrary _
  obtain ⟨-, hk⟩ := reciprocity_fixedOpen_sylow (D := D) hLK hax P
  have hinj := Abelianization.lift_injective_of_ker_le _ hk
  have hv := D.reciprocity_verlagerung hax (le_fixedOpen hLK (P : Subgroup ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K)))
    (fixedOpen_le hLK (P : Subgroup ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K))) σ
  rw [hσ, map_one] at hv
  have hv1 : verlagerung (L := L) (fixedOpen_le hLK (P : Subgroup ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K))) σ = 1 :=
    hinj (by rw [hv, map_one])
  have hmap := map_verlagerung (fixedOpen_le hLK (P : Subgroup ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K))) σ
  rw [hv1, map_one, range_galRestrict_fixedOpen] at hmap
  exact Sylow.not_dvd_index P (hpd.trans (orderOf_dvd_of_pow_eq_one hmap.symm))

theorem ker_reciprocity_eq_commutator :
    (D.reciprocity hLK hax).ker = commutator ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) := by
  refine le_antisymm (ker_reciprocity_le_commutator hLK hax) ?_
  rw [← Abelianization.ker_of]
  intro σ hσ
  rw [MonoidHom.mem_ker] at hσ ⊢
  rw [← Abelianization.lift_apply_of (D.reciprocity hLK hax), hσ, map_one]

variable (D) in

noncomputable def reciprocityAb :
    Abelianization ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) →*
      tateZero A (K : Subgroup G) (L : Subgroup G) :=
  Abelianization.lift (D.reciprocity hLK hax)

theorem reciprocityAb_of (q : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) :
    D.reciprocityAb hLK hax (Abelianization.of q) = D.reciprocity hLK hax q :=
  Abelianization.lift_apply_of _ q

theorem reciprocityAb_bijective : Function.Bijective (D.reciprocityAb hLK hax) := by
  refine ⟨Abelianization.lift_injective_of_ker_le _ (ker_reciprocity_le_commutator hLK hax),
    fun x => ?_⟩
  obtain ⟨q, hq⟩ := reciprocity_surjective (D := D) hLK hax x
  exact ⟨Abelianization.of q, hq⟩

variable (D) in

noncomputable def reciprocityAbEquiv :
    Abelianization ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) ≃*
      tateZero A (K : Subgroup G) (L : Subgroup G) :=
  MulEquiv.ofBijective _ (reciprocityAb_bijective (D := D) hLK hax)

theorem reciprocityAbEquiv_apply (z : Abelianization ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K)) :
    D.reciprocityAbEquiv hLK hax z = D.reciprocityAb hLK hax z :=
  rfl

theorem reciprocityAbEquiv_of (q : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) :
    D.reciprocityAbEquiv hLK hax (Abelianization.of q) = D.reciprocity hLK hax q :=
  reciprocityAb_of hLK hax q

include hLK hax in

theorem card_tateZero (D : ClassFieldData G A) :
    Nat.card (tateZero A (K : Subgroup G) (L : Subgroup G)) =
      Nat.card (Abelianization ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K)) :=
  (Nat.card_congr (D.reciprocityAbEquiv hLK hax).toEquiv).symm

theorem reciprocity_bijective_of_isMulCommutative
    [IsMulCommutative ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K)] :
    Function.Bijective (D.reciprocity hLK hax) := by
  refine ⟨?_, reciprocity_surjective hLK hax⟩
  rw [injective_iff_map_eq_one]
  intro q hq
  have h := ker_reciprocity_le_commutator (D := D) hLK hax hq
  rw [commutator, Subgroup.commutator_eq_bot_iff_le_centralizer.2 (fun x _ y _ => mul_comm' y x)] at h
  exact h

end General

section Squares

variable (hax : ClassFieldAxiom G A) [IsDiscreteModule G A]

theorem reciprocityAb_map_galRestrict {K L K' L' : OpenSubgroup G} (hLK : L ≤ K)
    [((L : Subgroup G).subgroupOf K).Normal] (hL'K' : L' ≤ K')
    [((L' : Subgroup G).subgroupOf K').Normal] (hK : K' ≤ K) (hL : L' ≤ L)
    (z : Abelianization ((K' : Subgroup G) ⧸ (L' : Subgroup G).subgroupOf K')) :
    D.reciprocityAb hLK hax (Abelianization.map (galRestrict hK hL) z) =
      normTateZero hK hL hL'K' hLK (D.reciprocityAb hL'K' hax z) := by
  induction z using QuotientGroup.induction_on with
  | H q =>
    show D.reciprocityAb hLK hax (Abelianization.map (galRestrict hK hL) (Abelianization.of q)) =
      normTateZero hK hL hL'K' hLK (D.reciprocityAb hL'K' hax (Abelianization.of q))
    rw [Abelianization.map_of, reciprocityAb_of, reciprocityAb_of,
      D.reciprocity_galRestrict hax hLK hL'K' hK hL q]

theorem reciprocityAbEquiv_symm_normTateZero {K L K' L' : OpenSubgroup G} (hLK : L ≤ K)
    [((L : Subgroup G).subgroupOf K).Normal] (hL'K' : L' ≤ K')
    [((L' : Subgroup G).subgroupOf K').Normal] (hK : K' ≤ K) (hL : L' ≤ L)
    (x : tateZero A (K' : Subgroup G) (L' : Subgroup G)) :
    (D.reciprocityAbEquiv hLK hax).symm (normTateZero hK hL hL'K' hLK x) =
      Abelianization.map (galRestrict hK hL) ((D.reciprocityAbEquiv hL'K' hax).symm x) := by
  rw [MulEquiv.symm_apply_eq]
  obtain ⟨z, rfl⟩ := (D.reciprocityAbEquiv hL'K' hax).surjective x
  rw [MulEquiv.symm_apply_apply, reciprocityAbEquiv_apply, reciprocityAbEquiv_apply,
    reciprocityAb_map_galRestrict]

theorem reciprocityAbEquiv_symm_tateZeroConj (σ : G) {K L : OpenSubgroup G} (hLK : L ≤ K)
    [((L : Subgroup G).subgroupOf K).Normal] (x : tateZero A (K : Subgroup G) (L : Subgroup G)) :
    (D.reciprocityAbEquiv (conjOpen_mono σ hLK) hax).symm (tateZeroConj σ K L x) =
      Abelianization.map (galConj σ K L) ((D.reciprocityAbEquiv hLK hax).symm x) := by
  rw [MulEquiv.symm_apply_eq]
  obtain ⟨z, rfl⟩ := (D.reciprocityAbEquiv hLK hax).surjective x
  rw [MulEquiv.symm_apply_apply]
  induction z using QuotientGroup.induction_on with
  | H q =>
    show tateZeroConj σ K L (D.reciprocityAbEquiv hLK hax (Abelianization.of q)) =
      D.reciprocityAbEquiv (conjOpen_mono σ hLK) hax
        (Abelianization.map (galConj σ K L) (Abelianization.of q))
    rw [Abelianization.map_of, reciprocityAbEquiv_of, reciprocityAbEquiv_of,
      D.reciprocity_galConj hax σ hLK q]

theorem reciprocityAbEquiv_symm_tateZeroIncl {K K' L : OpenSubgroup G}
    [((L : Subgroup G).subgroupOf K).Normal] [((L : Subgroup G).subgroupOf K').Normal]
    (hLK' : L ≤ K') (hK'K : K' ≤ K) (x : tateZero A (K : Subgroup G) (L : Subgroup G)) :
    (D.reciprocityAbEquiv hLK' hax).symm (tateZeroIncl hLK' hK'K x) =
      Abelianization.lift (verlagerung hK'K) ((D.reciprocityAbEquiv (hLK'.trans hK'K) hax).symm x) := by
  rw [MulEquiv.symm_apply_eq]
  obtain ⟨z, rfl⟩ := (D.reciprocityAbEquiv (hLK'.trans hK'K) hax).surjective x
  rw [MulEquiv.symm_apply_apply]
  induction z using QuotientGroup.induction_on with
  | H q =>
    show tateZeroIncl hLK' hK'K (D.reciprocityAbEquiv (hLK'.trans hK'K) hax (Abelianization.of q)) =
      D.reciprocityAbEquiv hLK' hax (Abelianization.lift (verlagerung hK'K) (Abelianization.of q))
    rw [Abelianization.lift_apply_of, reciprocityAbEquiv_of, reciprocityAbEquiv_apply, reciprocityAb,
      D.reciprocity_verlagerung hax hLK' hK'K q]

end Squares

section Unramified

variable {K L : OpenSubgroup G} (hLK : L ≤ K) [((L : Subgroup G).subgroupOf K).Normal]
  (hax : ClassFieldAxiom G A) [IsDiscreteModule G A]

theorem reciprocityAbEquiv_symm_of_unramified (hu : (K : Subgroup G) ⊓ D.deg.ker ≤ L)
    {φ : (K : Subgroup G)} (hφ : D.relDeg K φ = Multiplicative.ofAdd 1)
    (a : fixedModule A (K : Subgroup G)) :
    (D.reciprocityAbEquiv hLK hax).symm (a : tateZero A (K : Subgroup G) (L : Subgroup G)) =
      Abelianization.of (φ : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) ^
        (proj (D.relInertiaDegreePNat hLK) (Multiplicative.toAdd (D.valuation K a))).val := by
  obtain ⟨π, hπ⟩ := D.exists_prime K
  rw [MulEquiv.symm_apply_eq, map_pow, reciprocityAbEquiv_of,
    reciprocity_frobenius_of_unramified hLK hax hu hφ hπ]
  apply (D.tateZeroVal_bijective hax hLK hu).1
  rw [map_pow, tateZeroVal_mk, tateZeroVal_mk, valuationMod_apply, valuationMod_apply, hπ, toAdd_ofAdd,
    map_one, ← ofAdd_nsmul, nsmul_one, ZMod.natCast_zmod_val]

theorem reciprocityAbEquiv_symm_of_unramified_of_valuation (hu : (K : Subgroup G) ⊓ D.deg.ker ≤ L)
    {φ : (K : Subgroup G)} (hφ : D.relDeg K φ = Multiplicative.ofAdd 1)
    (a : fixedModule A (K : Subgroup G)) (m : ℤ)
    (ha : D.valuation K a = Multiplicative.ofAdd (m : ℤ̂)) :
    (D.reciprocityAbEquiv hLK hax).symm (a : tateZero A (K : Subgroup G) (L : Subgroup G)) =
      Abelianization.of (φ : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) ^ m := by
  obtain ⟨π, hπ⟩ := D.exists_prime K
  rw [MulEquiv.symm_apply_eq, map_zpow, reciprocityAbEquiv_of,
    reciprocity_frobenius_of_unramified hLK hax hu hφ hπ]
  apply (D.tateZeroVal_bijective hax hLK hu).1
  rw [map_zpow, tateZeroVal_mk, tateZeroVal_mk, valuationMod_apply, valuationMod_apply, hπ, ha,
    toAdd_ofAdd, toAdd_ofAdd, map_one, map_intCast, ← ofAdd_zsmul, zsmul_one]

end Unramified

end ClassFieldData

end Sec_ALR_Isomorphism

section Sec_ALR_NormGroups

section Abelian

variable {G : Type*} [Group G] [TopologicalSpace G]

def IsAbelianExtension (K L : OpenSubgroup G) : Prop :=
  L ≤ K ∧ commutator (K : Subgroup G) ≤ (L : Subgroup G).subgroupOf K

variable {K L : OpenSubgroup G}

theorem IsAbelianExtension.le (h : IsAbelianExtension K L) : L ≤ K :=
  h.1

theorem IsAbelianExtension.commutator_le (h : IsAbelianExtension K L) :
    commutator (K : Subgroup G) ≤ (L : Subgroup G).subgroupOf K :=
  h.2

theorem IsAbelianExtension.normal (h : IsAbelianExtension K L) :
    ((L : Subgroup G).subgroupOf K).Normal :=
  Subgroup.Normal.of_commutator_le _ h.2

theorem IsAbelianExtension.isMulCommutative (h : IsAbelianExtension K L)
    [((L : Subgroup G).subgroupOf K).Normal] :
    IsMulCommutative ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) :=
  Subgroup.Normal.quotient_commutative_iff_commutator_le.2 h.2

theorem isAbelianExtension_of_isMulCommutative (hLK : L ≤ K) [((L : Subgroup G).subgroupOf K).Normal]
    [IsMulCommutative ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K)] : IsAbelianExtension K L :=
  ⟨hLK, Subgroup.Normal.quotient_commutative_iff_commutator_le.1 inferInstance⟩

theorem IsAbelianExtension.mono {H : OpenSubgroup G} (h : IsAbelianExtension K L) (hLH : L ≤ H)
    (hHK : H ≤ K) : IsAbelianExtension K H :=
  ⟨hHK, fun _ hx => hLH (h.2 hx)⟩

theorem IsAbelianExtension.inf {L' : OpenSubgroup G} (h : IsAbelianExtension K L)
    (h' : IsAbelianExtension K L') : IsAbelianExtension K (L ⊓ L') :=
  ⟨inf_le_left.trans h.le, fun _ hx => ⟨h.2 hx, h'.2 hx⟩⟩

theorem isAbelianExtension_self (K : OpenSubgroup G) : IsAbelianExtension K K :=
  ⟨le_rfl, fun x _ => x.2⟩

variable [IsTopologicalGroup G]

def maxAbelian (hLK : L ≤ K) : OpenSubgroup G where
  toSubgroup :=
    ((L : Subgroup G).subgroupOf K ⊔ commutator (K : Subgroup G)).map (K : Subgroup G).subtype
  isOpen' := Subgroup.isOpen_mono (H₁ := (L : Subgroup G))
    (fun x hx => ⟨⟨x, hLK hx⟩, Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.2 hx), rfl⟩) L.isOpen

theorem mem_maxAbelian (hLK : L ≤ K) (x : (K : Subgroup G)) :
    (x : G) ∈ (maxAbelian hLK : Subgroup G) ↔
      x ∈ (L : Subgroup G).subgroupOf K ⊔ commutator (K : Subgroup G) :=
  Subgroup.mem_map_iff_mem Subtype.val_injective

theorem maxAbelian_le (hLK : L ≤ K) : maxAbelian hLK ≤ K :=
  fun _ ⟨x, _, hx⟩ => hx ▸ x.2

theorem le_maxAbelian (hLK : L ≤ K) : L ≤ maxAbelian hLK :=
  fun x hx => ⟨⟨x, hLK hx⟩, Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.2 hx), rfl⟩

theorem isAbelianExtension_maxAbelian (hLK : L ≤ K) : IsAbelianExtension K (maxAbelian hLK) :=
  ⟨maxAbelian_le hLK, fun x hx => (mem_maxAbelian hLK x).2 (Subgroup.mem_sup_right hx)⟩

end Abelian

section NormGroup

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  (A : Type*) [CommGroup A] [MulDistribMulAction G A]

noncomputable def normGroup (K L : OpenSubgroup G) : Subgroup (fixedModule A (K : Subgroup G)) :=
  (norm A (K : Subgroup G) (L : Subgroup G)).range

variable {A}

theorem normGroup_mono {K L H : OpenSubgroup G} (hLH : L ≤ H) (hHK : H ≤ K) :
    normGroup A K L ≤ normGroup A K H :=
  range_norm_le_range_norm hLH hHK

end NormGroup

theorem exists_openSubgroup_normal_le {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] (L : OpenSubgroup G) :
    ∃ N : OpenSubgroup G, N ≤ L ∧ (N : Subgroup G).Normal := by
  obtain ⟨U, hU⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one L.isOpen L.one_mem
  exact ⟨U.toOpenSubgroup, fun x hx => hU hx, U.isNormal'⟩

namespace ClassFieldData

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] {A : Type*} [CommGroup A] [MulDistribMulAction G A]
  (D : ClassFieldData G A) (hax : ClassFieldAxiom G A) [IsDiscreteModule G A]

section Reciprocity

variable {K L : OpenSubgroup G}

omit [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] in
theorem mk_eq_one_iff [((L : Subgroup G).subgroupOf K).Normal] (x : (K : Subgroup G)) :
    (x : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) = 1 ↔ (x : G) ∈ (L : Subgroup G) :=
  (QuotientGroup.eq_one_iff x).trans Subgroup.mem_subgroupOf

theorem exists_reciprocity_mk_eq (hLK : L ≤ K) [((L : Subgroup G).subgroupOf K).Normal]
    (a : fixedModule A (K : Subgroup G)) :
    ∃ x : (K : Subgroup G),
      D.reciprocity hLK hax (x : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) =
        (a : tateZero A (K : Subgroup G) (L : Subgroup G)) := by
  obtain ⟨q, hq⟩ := reciprocity_surjective (D := D) hLK hax
    (a : tateZero A (K : Subgroup G) (L : Subgroup G))
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  exact ⟨x, hq⟩

theorem reciprocity_mk_of_le {L' : OpenSubgroup G} (hLK : L ≤ K)
    [((L : Subgroup G).subgroupOf K).Normal] (hL'K : L' ≤ K) [((L' : Subgroup G).subgroupOf K).Normal]
    (hLL' : L ≤ L') (x : (K : Subgroup G)) (a : fixedModule A (K : Subgroup G))
    (h : D.reciprocity hLK hax (x : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) =
      (a : tateZero A (K : Subgroup G) (L : Subgroup G))) :
    D.reciprocity hL'K hax (x : (K : Subgroup G) ⧸ (L' : Subgroup G).subgroupOf K) =
      (a : tateZero A (K : Subgroup G) (L' : Subgroup G)) := by
  have e := D.reciprocity_galRestrict hax hL'K hLK le_rfl hLL'
    (x : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K)
  rw [galRestrict_mk, h, normTateZero_mk, norm_self] at e
  exact e

theorem reciprocity_injective (hL : IsAbelianExtension K L)
    [((L : Subgroup G).subgroupOf K).Normal] : Function.Injective (D.reciprocity hL.le hax) :=
  haveI := hL.isMulCommutative
  (reciprocity_bijective_of_isMulCommutative (D := D) hL.le hax).1

theorem reciprocity_mk_eq_one_iff (hL : IsAbelianExtension K L)
    [((L : Subgroup G).subgroupOf K).Normal] (x : (K : Subgroup G)) :
    D.reciprocity hL.le hax (x : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) = 1 ↔
      (x : G) ∈ (L : Subgroup G) := by
  rw [← mk_eq_one_iff, ← (D.reciprocity_injective hax hL).eq_iff, map_one]

theorem mem_normGroup_iff_of_reciprocity (hL : IsAbelianExtension K L)
    [((L : Subgroup G).subgroupOf K).Normal] {x : (K : Subgroup G)}
    {a : fixedModule A (K : Subgroup G)}
    (h : D.reciprocity hL.le hax (x : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) =
      (a : tateZero A (K : Subgroup G) (L : Subgroup G))) :
    a ∈ normGroup A K L ↔ (x : G) ∈ (L : Subgroup G) := by
  rw [← D.reciprocity_mk_eq_one_iff hax hL, h, QuotientGroup.eq_one_iff]
  rfl

end Reciprocity

section Limitation

variable {K L : OpenSubgroup G}

include D hax

theorem normGroup_maxAbelian (hLK : L ≤ K) :
    normGroup A K (maxAbelian hLK) = normGroup A K L := by
  refine le_antisymm ?_ (normGroup_mono (le_maxAbelian hLK) (maxAbelian_le hLK))
  obtain ⟨N, hNL, hN⟩ := exists_openSubgroup_normal_le L
  have hNK : N ≤ K := hNL.trans hLK
  have hM := isAbelianExtension_maxAbelian hLK
  have := hM.normal
  have := hN
  rintro a ⟨m, rfl⟩
  obtain ⟨x, hx⟩ := D.exists_reciprocity_mk_eq hax hNK
    (norm A (K : Subgroup G) (maxAbelian hLK : Subgroup G) m)
  have hxM : (x : G) ∈ (maxAbelian hLK : Subgroup G) :=
    (D.mem_normGroup_iff_of_reciprocity hax hM
      (D.reciprocity_mk_of_le hax hNK hM.le (hNL.trans (le_maxAbelian hLK)) x _ hx)).1 ⟨m, rfl⟩
  obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 ((mem_maxAbelian hLK x).1 hxM)

  have hz1 : D.reciprocity hNK hax (z : (K : Subgroup G) ⧸ (N : Subgroup G).subgroupOf K) = 1 :=
    MonoidHom.mem_ker.1
      (Abelianization.commutator_subset_ker ((D.reciprocity hNK hax).comp (QuotientGroup.mk' _)) hz)

  obtain ⟨b, hb⟩ := QuotientGroup.mk_surjective (D.reciprocity hNL hax
    ((⟨y, hy⟩ : (L : Subgroup G)) : (L : Subgroup G) ⧸ (N : Subgroup G).subgroupOf L))
  have e := D.reciprocity_galRestrict hax hNK hNL hLK le_rfl
    ((⟨y, hy⟩ : (L : Subgroup G)) : (L : Subgroup G) ⧸ (N : Subgroup G).subgroupOf L)
  rw [galRestrict_mk, ← hb, normTateZero_mk] at e
  have e' : D.reciprocity hNK hax (y : (K : Subgroup G) ⧸ (N : Subgroup G).subgroupOf K) =
      (norm A (K : Subgroup G) (L : Subgroup G) b : tateZero A (K : Subgroup G) (N : Subgroup G)) := e
  rw [QuotientGroup.mk_mul, map_mul, hz1, mul_one, e'] at hx
  obtain ⟨c, hc⟩ := QuotientGroup.eq.1 hx
  refine ⟨b * norm A (L : Subgroup G) (N : Subgroup G) c, ?_⟩
  rw [map_mul, norm_norm hNL hLK, hc, mul_inv_cancel_left]

end Limitation

section Correspondence

variable {K L L' : OpenSubgroup G}

include D hax

theorem normGroup_le_normGroup_iff (hL : IsAbelianExtension K L) (hL' : IsAbelianExtension K L') :
    normGroup A K L ≤ normGroup A K L' ↔ L ≤ L' := by
  refine ⟨fun h => ?_, fun h => normGroup_mono h hL'.le⟩
  have hI := hL.inf hL'
  have := hI.normal
  have := hL.normal
  have := hL'.normal
  intro g hg
  have hgK : g ∈ (K : Subgroup G) := hL.le hg
  obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective (D.reciprocity hI.le hax
    ((⟨g, hgK⟩ : (K : Subgroup G)) : (K : Subgroup G) ⧸ ((L ⊓ L' : OpenSubgroup G) : Subgroup G).subgroupOf K))
  have h1 := D.reciprocity_mk_of_le hax hI.le hL.le inf_le_left ⟨g, hgK⟩ a ha.symm
  have h2 := D.reciprocity_mk_of_le hax hI.le hL'.le inf_le_right ⟨g, hgK⟩ a ha.symm
  exact (D.mem_normGroup_iff_of_reciprocity hax hL' h2).1
    (h ((D.mem_normGroup_iff_of_reciprocity hax hL h1).2 hg))

theorem normGroup_eq_normGroup_iff (hL : IsAbelianExtension K L) (hL' : IsAbelianExtension K L') :
    normGroup A K L = normGroup A K L' ↔ L = L' := by
  rw [le_antisymm_iff, le_antisymm_iff, D.normGroup_le_normGroup_iff hax hL hL',
    D.normGroup_le_normGroup_iff hax hL' hL]

theorem normGroup_injective (K : OpenSubgroup G) :
    Function.Injective fun L : {L : OpenSubgroup G // IsAbelianExtension K L} => normGroup A K L :=
  fun L L' h => Subtype.ext ((D.normGroup_eq_normGroup_iff hax L.2 L'.2).1 h)

theorem exists_normGroup_eq_of_le_of_isAbelianExtension (hL : IsAbelianExtension K L)
    {B : Subgroup (fixedModule A (K : Subgroup G))} (hB : normGroup A K L ≤ B) :
    ∃ H : OpenSubgroup G, IsAbelianExtension K H ∧ L ≤ H ∧ normGroup A K H = B := by
  have := hL.normal
  set Q : Subgroup ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) :=
    (B.map (QuotientGroup.mk' (norm A (K : Subgroup G) (L : Subgroup G)).range)).comap
      (D.reciprocity hL.le hax) with hQ
  have hH : IsAbelianExtension K (fixedOpen hL.le Q) :=
    hL.mono (le_fixedOpen hL.le Q) (fixedOpen_le hL.le Q)
  have := hH.normal
  refine ⟨fixedOpen hL.le Q, hH, le_fixedOpen hL.le Q, ?_⟩
  ext a
  obtain ⟨x, hx⟩ := D.exists_reciprocity_mk_eq hax hL.le a
  rw [D.mem_normGroup_iff_of_reciprocity hax hH
    (D.reciprocity_mk_of_le hax hL.le hH.le (le_fixedOpen hL.le Q) x a hx), mem_fixedOpen]
  constructor
  · rintro ⟨_, hq⟩
    have hq' : D.reciprocity hL.le hax (x : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) ∈
        B.map (QuotientGroup.mk' (norm A (K : Subgroup G) (L : Subgroup G)).range) := hq
    rw [hx] at hq'
    obtain ⟨b, hbB, hba⟩ := Subgroup.mem_map.1 hq'
    obtain ⟨n, hn⟩ := QuotientGroup.eq.1 hba
    have ha : a = b * (b⁻¹ * a) := (mul_inv_cancel_left b a).symm
    rw [ha, ← hn]
    exact B.mul_mem hbB (hB ⟨n, rfl⟩)
  · intro ha
    refine ⟨x.2, ?_⟩
    show D.reciprocity hL.le hax (x : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) ∈
      B.map (QuotientGroup.mk' (norm A (K : Subgroup G) (L : Subgroup G)).range)
    rw [hx]
    exact ⟨a, ha, rfl⟩

theorem exists_normGroup_eq_of_le (hLK : L ≤ K) {B : Subgroup (fixedModule A (K : Subgroup G))}
    (hB : normGroup A K L ≤ B) :
    ∃ H : OpenSubgroup G, IsAbelianExtension K H ∧ L ≤ H ∧ normGroup A K H = B := by
  rw [← D.normGroup_maxAbelian hax hLK] at hB
  obtain ⟨H, hH, hMH, e⟩ :=
    D.exists_normGroup_eq_of_le_of_isAbelianExtension hax (isAbelianExtension_maxAbelian hLK) hB
  exact ⟨H, hH, (le_maxAbelian hLK).trans hMH, e⟩

theorem index_normGroup (hL : IsAbelianExtension K L) :
    (normGroup A K L).index = (L : Subgroup G).relIndex K := by
  have := hL.normal
  have := hL.isMulCommutative
  rw [Subgroup.index_eq_card, ← card_quotient_eq_relIndex]
  exact (Nat.card_congr
    (Equiv.ofBijective _ (reciprocity_bijective_of_isMulCommutative (D := D) hL.le hax))).symm

end Correspondence

end ClassFieldData

end Sec_ALR_NormGroups

section Sec_ALR_ReciprocityAbelianizationRestrictReciprocityLimi

section Abelianization

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

instance compactSpace_openSubgroup [CompactSpace G] (K : OpenSubgroup G) :
    CompactSpace (K : Subgroup G) :=
  isCompact_iff_compactSpace.mp K.isClosed.isCompact

variable {K L : OpenSubgroup G}

omit [IsTopologicalGroup G] in

theorem isOpen_subgroupOf (K L : OpenSubgroup G) :
    IsOpen (((L : Subgroup G).subgroupOf K : Subgroup (K : Subgroup G)) : Set (K : Subgroup G)) :=
  L.isOpen.preimage continuous_subtype_val

theorem IsAbelianExtension.topologicalClosure_commutator_le (hL : IsAbelianExtension K L) :
    (commutator (K : Subgroup G)).topologicalClosure ≤ (L : Subgroup G).subgroupOf K :=
  Subgroup.topologicalClosure_minimal _ hL.commutator_le
    (Subgroup.isClosed_of_isOpen _ (isOpen_subgroupOf K L))

noncomputable def abelianizationRestrict (hL : IsAbelianExtension K L)
    [((L : Subgroup G).subgroupOf K).Normal] :
    TopologicalAbelianization (K : Subgroup G) →* (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K :=
  QuotientGroup.map _ _ (MonoidHom.id _) hL.topologicalClosure_commutator_le

@[simp]
theorem abelianizationRestrict_mk (hL : IsAbelianExtension K L)
    [((L : Subgroup G).subgroupOf K).Normal] (g : (K : Subgroup G)) :
    abelianizationRestrict hL (g : TopologicalAbelianization (K : Subgroup G)) =
      (g : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) :=
  rfl

variable [CompactSpace G] [TotallyDisconnectedSpace G]

theorem mem_topologicalClosure_commutator_iff (x : (K : Subgroup G)) :
    x ∈ (commutator (K : Subgroup G)).topologicalClosure ↔
      ∀ L : OpenSubgroup G, IsAbelianExtension K L → (x : G) ∈ (L : Subgroup G) := by
  refine ⟨fun hx L hL => hL.topologicalClosure_commutator_le hx, fun h => ?_⟩
  have key := ProfiniteGrp.closedSubgroup_eq_sInf_open (G := (K : Subgroup G))
    ⟨(commutator (K : Subgroup G)).topologicalClosure, Subgroup.isClosed_topologicalClosure _⟩
  have hx : x ∈ sInf {N : Subgroup (K : Subgroup G) | IsOpen (N : Set (K : Subgroup G)) ∧
      (commutator (K : Subgroup G)).topologicalClosure ≤ N} := by
    rw [Subgroup.mem_sInf]
    rintro N ⟨hNo, hCN⟩
    let M : OpenSubgroup G :=
      { toSubgroup := N.map (K : Subgroup G).subtype
        isOpen' := by
          have h := K.isOpen.isOpenMap_subtype_val _ hNo
          rw [← Subgroup.coe_subtype, ← Subgroup.coe_map] at h
          exact h }
    have hM : IsAbelianExtension K M :=
      ⟨fun _ ⟨y, _, hy⟩ => hy ▸ y.2, fun y hy =>
        ⟨y, hCN (Subgroup.le_topologicalClosure _ hy), rfl⟩⟩
    exact (Subgroup.mem_map_iff_mem Subtype.val_injective).1 (h M hM)
  rw [← key] at hx
  exact hx

end Abelianization

namespace ClassFieldData

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] {A : Type*} [CommGroup A] [MulDistribMulAction G A]
  (D : ClassFieldData G A) (hax : ClassFieldAxiom G A) [IsDiscreteModule G A]

section Equiv

variable {K L : OpenSubgroup G}

noncomputable def reciprocityAbelianEquiv (hL : IsAbelianExtension K L)
    [((L : Subgroup G).subgroupOf K).Normal] :
    (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K ≃* tateZero A (K : Subgroup G) (L : Subgroup G) :=
  haveI := hL.isMulCommutative
  MulEquiv.ofBijective _ (reciprocity_bijective_of_isMulCommutative (D := D) hL.le hax)

theorem reciprocityAbelianEquiv_apply (hL : IsAbelianExtension K L) [((L : Subgroup G).subgroupOf K).Normal]
    (q : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) :
    D.reciprocityAbelianEquiv hax hL q = D.reciprocity hL.le hax q :=
  rfl

end Equiv

section Limit

variable (K : OpenSubgroup G)

theorem exists_forall_reciprocity_mk_eq (a : fixedModule A (K : Subgroup G)) :
    ∃ g : (K : Subgroup G), ∀ (L : OpenSubgroup G) (hL : IsAbelianExtension K L)
      [((L : Subgroup G).subgroupOf K).Normal],
      D.reciprocity hL.le hax (g : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) =
        (a : tateZero A (K : Subgroup G) (L : Subgroup G)) := by
  let ι := {L : OpenSubgroup G // IsAbelianExtension K L}
  have : Nonempty ι := ⟨⟨K, isAbelianExtension_self K⟩⟩
  let t : ι → Set (K : Subgroup G) := fun L =>
    haveI := L.2.normal
    {g | D.reciprocity L.2.le hax (g : (K : Subgroup G) ⧸ (L.1 : Subgroup G).subgroupOf K) =
      (a : tateZero A (K : Subgroup G) (L.1 : Subgroup G))}
  have htn : ∀ L, (t L).Nonempty := fun L => by
    have := L.2.normal
    obtain ⟨x, hx⟩ := D.exists_reciprocity_mk_eq hax L.2.le a
    exact ⟨x, hx⟩
  have htcl : ∀ L, IsClosed (t L) := fun L => by
    have := L.2.normal
    obtain ⟨x, hx⟩ := htn L
    have ht : t L = (fun g => x⁻¹ * g) ⁻¹'
        (((L.1 : Subgroup G).subgroupOf K : Subgroup (K : Subgroup G)) : Set (K : Subgroup G)) := by
      ext g
      change D.reciprocity L.2.le hax _ = _ ↔ _
      rw [← show D.reciprocity L.2.le hax _ = _ from hx, (D.reciprocity_injective hax L.2).eq_iff,
        eq_comm, QuotientGroup.eq]
      rfl
    rw [ht]
    exact (Subgroup.isClosed_of_isOpen _ (isOpen_subgroupOf K L.1)).preimage
      (continuous_const.mul continuous_id)
  have htd : Directed (· ⊇ ·) t := by
    intro L L'
    refine ⟨⟨L.1 ⊓ L'.1, L.2.inf L'.2⟩, fun g hg => ?_, fun g hg => ?_⟩
    · have := L.2.normal
      have := (L.2.inf L'.2).normal
      exact D.reciprocity_mk_of_le hax (L.2.inf L'.2).le L.2.le inf_le_left g a hg
    · have := L'.2.normal
      have := (L.2.inf L'.2).normal
      exact D.reciprocity_mk_of_le hax (L.2.inf L'.2).le L'.2.le inf_le_right g a hg
  obtain ⟨g, hg⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed t htd htn
    (fun L => (htcl L).isCompact) htcl
  refine ⟨g, fun L hL _ => ?_⟩
  exact Set.mem_iInter.1 hg ⟨L, hL⟩

theorem mk_eq_mk_of_forall_reciprocity_mk_eq {a : fixedModule A (K : Subgroup G)}
    {g g' : (K : Subgroup G)}
    (hg : ∀ (L : OpenSubgroup G) (hL : IsAbelianExtension K L) [((L : Subgroup G).subgroupOf K).Normal],
      D.reciprocity hL.le hax (g : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) =
        (a : tateZero A (K : Subgroup G) (L : Subgroup G)))
    (hg' : ∀ (L : OpenSubgroup G) (hL : IsAbelianExtension K L) [((L : Subgroup G).subgroupOf K).Normal],
      D.reciprocity hL.le hax (g' : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) =
        (a : tateZero A (K : Subgroup G) (L : Subgroup G))) :
    (g : TopologicalAbelianization (K : Subgroup G)) = g' := by
  rw [QuotientGroup.eq, mem_topologicalClosure_commutator_iff]
  intro L hL
  have := hL.normal
  have h := (hg L hL).trans (hg' L hL).symm
  rw [(D.reciprocity_injective hax hL).eq_iff, QuotientGroup.eq] at h
  exact h

noncomputable def reciprocityLimit :
    fixedModule A (K : Subgroup G) →* TopologicalAbelianization (K : Subgroup G) where
  toFun a := ((D.exists_forall_reciprocity_mk_eq hax K a).choose :
    TopologicalAbelianization (K : Subgroup G))
  map_one' := by
    rw [← QuotientGroup.mk_one]
    refine D.mk_eq_mk_of_forall_reciprocity_mk_eq hax K
      (D.exists_forall_reciprocity_mk_eq hax K 1).choose_spec ?_
    intro L hL _
    rw [QuotientGroup.mk_one, map_one, QuotientGroup.mk_one]
  map_mul' a b := by
    rw [← QuotientGroup.mk_mul]
    refine D.mk_eq_mk_of_forall_reciprocity_mk_eq hax K
      (D.exists_forall_reciprocity_mk_eq hax K (a * b)).choose_spec ?_
    intro L hL _
    rw [QuotientGroup.mk_mul, map_mul, (D.exists_forall_reciprocity_mk_eq hax K a).choose_spec L hL,
      (D.exists_forall_reciprocity_mk_eq hax K b).choose_spec L hL, QuotientGroup.mk_mul]

variable {K}

theorem reciprocity_abelianizationRestrict_reciprocityLimit {L : OpenSubgroup G}
    (hL : IsAbelianExtension K L) [((L : Subgroup G).subgroupOf K).Normal]
    (a : fixedModule A (K : Subgroup G)) :
    D.reciprocity hL.le hax (abelianizationRestrict hL (D.reciprocityLimit hax K a)) =
      (a : tateZero A (K : Subgroup G) (L : Subgroup G)) :=
  (D.exists_forall_reciprocity_mk_eq hax K a).choose_spec L hL

theorem abelianizationRestrict_reciprocityLimit {L : OpenSubgroup G} (hL : IsAbelianExtension K L)
    [((L : Subgroup G).subgroupOf K).Normal] (a : fixedModule A (K : Subgroup G)) :
    abelianizationRestrict hL (D.reciprocityLimit hax K a) =
      (D.reciprocityAbelianEquiv hax hL).symm (a : tateZero A (K : Subgroup G) (L : Subgroup G)) := by
  rw [MulEquiv.eq_symm_apply, reciprocityAbelianEquiv_apply,
    D.reciprocity_abelianizationRestrict_reciprocityLimit hax hL]

theorem eq_one_iff_forall_abelianizationRestrict (σ : TopologicalAbelianization (K : Subgroup G)) :
    σ = 1 ↔ ∀ (L : OpenSubgroup G) (hL : IsAbelianExtension K L)
      [((L : Subgroup G).subgroupOf K).Normal], abelianizationRestrict hL σ = 1 := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective σ
  rw [QuotientGroup.eq_one_iff, mem_topologicalClosure_commutator_iff]
  refine ⟨fun h L hL _ => ?_, fun h L hL => ?_⟩
  · rw [abelianizationRestrict_mk, mk_eq_one_iff]
    exact h L hL
  · have := hL.normal
    have h' := h L hL
    rwa [abelianizationRestrict_mk, mk_eq_one_iff] at h'

theorem ext_abelianizationRestrict {σ τ : TopologicalAbelianization (K : Subgroup G)}
    (h : ∀ (L : OpenSubgroup G) (hL : IsAbelianExtension K L)
      [((L : Subgroup G).subgroupOf K).Normal], abelianizationRestrict hL σ = abelianizationRestrict hL τ) :
    σ = τ := by
  rw [← div_eq_one, eq_one_iff_forall_abelianizationRestrict]
  intro L hL _
  rw [map_div, h L hL, div_self']

theorem eq_reciprocityLimit {a : fixedModule A (K : Subgroup G)}
    {σ : TopologicalAbelianization (K : Subgroup G)}
    (h : ∀ (L : OpenSubgroup G) (hL : IsAbelianExtension K L)
      [((L : Subgroup G).subgroupOf K).Normal],
      D.reciprocity hL.le hax (abelianizationRestrict hL σ) =
        (a : tateZero A (K : Subgroup G) (L : Subgroup G))) :
    σ = D.reciprocityLimit hax K a := by
  refine ext_abelianizationRestrict fun L hL _ => D.reciprocity_injective hax hL ?_
  rw [h L hL, D.reciprocity_abelianizationRestrict_reciprocityLimit hax hL]

theorem ker_reciprocityLimit :
    (D.reciprocityLimit hax K).ker =
      ⨅ L : {L : OpenSubgroup G // IsAbelianExtension K L}, normGroup A K L.1 := by
  ext a
  rw [MonoidHom.mem_ker, eq_one_iff_forall_abelianizationRestrict, Subgroup.mem_iInf]
  refine ⟨fun h L => ?_, fun h L hL _ => ?_⟩
  · have := L.2.normal
    have h' := congrArg (D.reciprocity L.2.le hax) (h L.1 L.2)
    rw [D.reciprocity_abelianizationRestrict_reciprocityLimit hax L.2, map_one,
      QuotientGroup.eq_one_iff] at h'
    exact h'
  · apply D.reciprocity_injective hax hL
    rw [D.reciprocity_abelianizationRestrict_reciprocityLimit hax hL, map_one,
      QuotientGroup.eq_one_iff]
    exact h ⟨L, hL⟩

theorem ker_reciprocityLimit_eq_iInf :
    (D.reciprocityLimit hax K).ker = ⨅ L : {L : OpenSubgroup G // L ≤ K}, normGroup A K L.1 := by
  rw [ker_reciprocityLimit]
  refine le_antisymm (le_iInf fun L => ?_) (le_iInf fun L => iInf_le_of_le ⟨L.1, L.2.le⟩ le_rfl)
  rw [← D.normGroup_maxAbelian hax L.2]
  exact iInf_le_of_le ⟨maxAbelian L.2, isAbelianExtension_maxAbelian L.2⟩ le_rfl

theorem denseRange_reciprocityLimit : DenseRange (D.reciprocityLimit hax K) := by
  rw [DenseRange, dense_iff_inter_open]
  rintro U hU ⟨σ, hσ⟩
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective σ
  set C := (commutator (K : Subgroup G)).topologicalClosure
  set V : Set (K : Subgroup G) := (fun y => ((g * y : (K : Subgroup G)) :
    TopologicalAbelianization (K : Subgroup G))) ⁻¹' U with hV
  have hVo : IsOpen V :=
    hU.preimage (QuotientGroup.continuous_mk.comp (continuous_const.mul continuous_id))
  have hV1 : (1 : (K : Subgroup G)) ∈ V := by
    simp only [hV, Set.mem_preimage, mul_one]
    exact hσ
  obtain ⟨N, hN⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hVo hV1

  let M : OpenSubgroup G :=
    { toSubgroup := ((N : Subgroup (K : Subgroup G)) ⊔ C).map (K : Subgroup G).subtype
      isOpen' := by
        have ho : IsOpen (((N : Subgroup (K : Subgroup G)) ⊔ C : Subgroup (K : Subgroup G)) :
            Set (K : Subgroup G)) :=
          Subgroup.isOpen_mono (H₁ := (N : Subgroup (K : Subgroup G)))
            (H₂ := (N : Subgroup (K : Subgroup G)) ⊔ C) le_sup_left N.isOpen'
        have h := K.isOpen.isOpenMap_subtype_val _ ho
        rw [← Subgroup.coe_subtype, ← Subgroup.coe_map] at h
        exact h }
  have hMmem : ∀ x : (K : Subgroup G), (x : G) ∈ (M : Subgroup G) ↔ x ∈ (N : Subgroup (K : Subgroup G)) ⊔ C :=
    fun x => Subgroup.mem_map_iff_mem Subtype.val_injective
  have hM : IsAbelianExtension K M :=
    ⟨fun _ ⟨y, _, hy⟩ => hy ▸ y.2, fun y hy =>
      (hMmem y).2 (Subgroup.mem_sup_right (Subgroup.le_topologicalClosure _ hy))⟩
  have := hM.normal
  obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective
    (D.reciprocity hM.le hax (g : (K : Subgroup G) ⧸ (M : Subgroup G).subgroupOf K))
  refine ⟨D.reciprocityLimit hax K a, ?_, a, rfl⟩
  obtain ⟨h, hh⟩ := QuotientGroup.mk_surjective (D.reciprocityLimit hax K a)
  have e := D.reciprocity_abelianizationRestrict_reciprocityLimit hax hM a
  rw [← hh, abelianizationRestrict_mk, ha, (D.reciprocity_injective hax hM).eq_iff, eq_comm,
    QuotientGroup.eq] at e

  have e' : g⁻¹ * h ∈ (N : Subgroup (K : Subgroup G)) ⊔ C := (hMmem _).1 e
  obtain ⟨n, hn, c, hc, hnc⟩ := Subgroup.mem_sup_of_normal_left.1 e'
  have hnV : n ∈ V := hN hn
  rw [← hh]
  have hgh : h = g * n * c := by
    rw [mul_assoc, hnc, mul_inv_cancel_left]
  have hmk : ((h : (K : Subgroup G)) : TopologicalAbelianization (K : Subgroup G)) =
      ((g * n : (K : Subgroup G)) : TopologicalAbelianization (K : Subgroup G)) := by
    have hc' : (g * n * c)⁻¹ * (g * n) = c⁻¹ := by group
    rw [QuotientGroup.eq, hgh, hc']
    exact C.inv_mem hc
  rw [hmk]
  exact hnV

end Limit

end ClassFieldData

end Sec_ALR_ReciprocityAbelianizationRestrictReciprocityLimi

end RHDirect.CFT_AbstractLocalReciprocity
