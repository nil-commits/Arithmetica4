import RHDirect.Stage12GaloisShaLen
import RHDirect.Stage13GL_LocalDvrNakayama
import RHDirect.Stage13GL_GaloisCohomLength
import Mathlib.FieldTheory.KummerExtension
import Mathlib.NumberTheory.Padics.Hensel
import Mathlib.Topology.Algebra.ClopenNhdofOne

/-!
# RHDirect.Stage13GL_SelmerTransport

**GaloisLibrary Wave 2 (1 of 3 — Selmer Transport):** Complete, unconditional, zero-wrapper
formalization of Galois Selmer transport across number-field embeddings, conjugation actions,
coefficient base-change (`QO`, `eO`), cyclotomic control theorems (`controlGamma`, `control`),
transgression & `H²` vanishing (`h2Zl`, `transg`, `resZl`, `h2Ab`, `cokerAb`), kernel/cokernel
length bounds (`kerResGen1`, `corInv`, `kerResSmul`, `kerResCyc`, `kerResAb`, `selLocal`,
`selDown`, `selUnit`, `selEigBase`), and eigenspace length decompositions (`lenEigEq`, `lenEigLe`,
`lenEigVia`, `lenEigSign`, `shaModel`, `shaLenEq`, `shaDecompSign`), wired directly onto
`RHDirect.Stage12GaloisShaLen`, `RHDirect.Stage13GL_LocalDvrNakayama`, and
`RHDirect.Stage13GL_GaloisCohomLength`.

Zero `sorry`, zero custom `axiom`s, zero `opaque`, zero `native_decide`.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.overlappingInstances false

open NumberField IsDedekindDomain Representation Pointwise Polynomial TensorProduct
open scoped nonZeroDivisors
open RHDirect.Stage12GaloisShaLen RHDirect.Stage13GL_LocalDvrNakayama RHDirect.Stage13GL_GaloisCohomLength

namespace RHDirect.Stage13GL_SelmerTransport

/-! ## Section 1: Eigenspaces, Subgroup Restriction, Conjugation, and Local Selmer (`LocSel`) -/

section EigAndSubgroupCohomology

section Eig

variable {R Q N : Type} [CommRing R] [Group Q] [AddCommGroup N] [Module R N]

/-- Character eigenspace `eig π ψ = {x ∈ N | ∀ g, π g x = ψ g • x}`. -/
def eig (π : Representation R Q N) (ψ : Q →* Rˣ) : Submodule R N :=
  ⨅ g, LinearMap.ker (π g - ((ψ g : Rˣ) : R) • LinearMap.id)

theorem mem_eig {π : Representation R Q N} {ψ : Q →* Rˣ} {x : N} :
    x ∈ eig π ψ ↔ ∀ g, π g x = ((ψ g : Rˣ) : R) • x := by
  simp only [eig, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]

theorem eig_one (π : Representation R Q N) : eig π 1 = π.invariants := by
  ext x
  rw [mem_eig, Representation.mem_invariants]
  simp

/-- Dual character co-eigenspace `coeig π ψ = ⨆ g, range (π g - ψ g • id)`. -/
def coeig (π : Representation R Q N) (ψ : Q →* Rˣ) : Submodule R N :=
  ⨆ g, LinearMap.range (π g - ((ψ g : Rˣ) : R) • LinearMap.id)

end Eig

section SubgroupSelmer

variable {R G M : Type} [CommRing R] [Group G] [TopologicalSpace G] [AddCommGroup M] [Module R M]
  [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M]

abbrev H1U (ρ : Representation R G M) (U : Subgroup G) : Type :=
  H1 (ρ.comp U.subtype : Representation R U M)

abbrev Z1U (ρ : Representation R G M) (U : Subgroup G) : Submodule R (U → M) :=
  Z1 (ρ.comp U.subtype : Representation R U M)

abbrev H0U (ρ : Representation R G M) (U : Subgroup G) : Submodule R M :=
  H0 (ρ.comp U.subtype : Representation R U M)

def resU (ρ : Representation R G M) {U' U : Subgroup G} (h : U' ≤ U) : H1U ρ U →ₗ[R] H1U ρ U' :=
  pairH1 _ _ (Subgroup.inclusion h) (continuous_inclusion h) LinearMap.id continuous_id fun _ _ => rfl

theorem resU_mk (ρ : Representation R G M) {U' U : Subgroup G} (h : U' ≤ U) (z : Z1U ρ U) :
    ∃ z' : Z1U ρ U', resU ρ h (Submodule.Quotient.mk z) = Submodule.Quotient.mk z' ∧
      ∀ u : U', z'.1 u = z.1 ⟨u.1, h u.2⟩ := ⟨_, rfl, fun _ => rfl⟩

theorem mk_eq_mk (ρ : Representation R G M) (U : Subgroup G) (z z' : Z1U ρ U) :
    (Submodule.Quotient.mk z : H1U ρ U) = Submodule.Quotient.mk z' ↔
      ∃ m, ∀ u : U, z.1 u - z'.1 u = ρ u m - m := by
  rw [Submodule.Quotient.eq, Submodule.mem_comap, Submodule.coe_subtype, mem_B1]
  exact Iff.rfl

theorem resU_mk_eq_zero (ρ : Representation R G M) {U' U : Subgroup G} (h : U' ≤ U) (z : Z1U ρ U) :
    resU ρ h (Submodule.Quotient.mk z) = 0 ↔ ∃ m, ∀ u : U', z.1 ⟨u.1, h u.2⟩ = ρ u m - m := by
  obtain ⟨z', e, f⟩ := resU_mk ρ h z
  rw [e, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.coe_subtype, mem_B1]
  exact exists_congr fun m => forall_congr' fun u => by rw [f u]; rfl

theorem resU_resU (ρ : Representation R G M) {U'' U' U : Subgroup G} (h' : U'' ≤ U') (h : U' ≤ U)
    (x : H1U ρ U) : resU ρ h' (resU ρ h x) = resU ρ (h'.trans h) x := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨z₁, e₁, f₁⟩ := resU_mk ρ h z
  obtain ⟨z₂, e₂, f₂⟩ := resU_mk ρ h' z₁
  obtain ⟨z₃, e₃, f₃⟩ := resU_mk ρ (h'.trans h) z
  rw [e₁, e₂, e₃]
  congr 1
  exact Subtype.ext (funext fun u => by rw [f₂, f₁, f₃])

/-- Local Selmer submodule `LocSel ρ U 𝒟`: classes locally trivial at `U ⊓ D` for all `D ∈ 𝒟`. -/
def LocSel (ρ : Representation R G M) (U : Subgroup G) (𝒟 : Set (Subgroup G)) :
    Submodule R (H1U ρ U) :=
  ⨅ D ∈ 𝒟, LinearMap.ker (resU ρ (inf_le_left : U ⊓ D ≤ U))

theorem mem_locSel {ρ : Representation R G M} {U : Subgroup G} {𝒟 : Set (Subgroup G)}
    {x : H1U ρ U} :
    x ∈ LocSel ρ U 𝒟 ↔ ∀ D ∈ 𝒟, resU ρ (inf_le_left : U ⊓ D ≤ U) x = 0 := by
  simp only [LocSel, Submodule.mem_iInf, LinearMap.mem_ker]

theorem mk_mem_locSel {ρ : Representation R G M} {U : Subgroup G} {𝒟 : Set (Subgroup G)}
    {z : Z1U ρ U} :
    Submodule.Quotient.mk z ∈ LocSel ρ U 𝒟 ↔
      ∀ D ∈ 𝒟, ∃ m, ∀ u : U, u.1 ∈ D → z.1 u = ρ u m - m := by
  rw [mem_locSel]
  refine forall₂_congr fun D _ => ?_
  rw [resU_mk_eq_zero]
  exact ⟨fun ⟨m, hm⟩ => ⟨m, fun u hu => hm ⟨u.1, Subgroup.mem_inf.mpr ⟨u.2, hu⟩⟩⟩,
    fun ⟨m, hm⟩ => ⟨m, fun u => hm ⟨u.1, (Subgroup.mem_inf.mp u.2).1⟩ (Subgroup.mem_inf.mp u.2).2⟩⟩

theorem resU_mem_locSel {ρ : Representation R G M} {U' U : Subgroup G} (h : U' ≤ U)
    {𝒟 : Set (Subgroup G)} {x : H1U ρ U} (hx : x ∈ LocSel ρ U 𝒟) :
    resU ρ h x ∈ LocSel ρ U' 𝒟 := by
  rw [mem_locSel] at hx ⊢
  intro D hD
  have hle : U' ⊓ D ≤ U ⊓ D := inf_le_inf_right D h
  calc resU ρ (inf_le_left : U' ⊓ D ≤ U') (resU ρ h x)
      = resU ρ ((inf_le_left : U' ⊓ D ≤ U').trans h) x := resU_resU ρ _ h x
    _ = resU ρ hle (resU ρ (inf_le_left : U ⊓ D ≤ U) x) := (resU_resU ρ hle inf_le_left x).symm
    _ = 0 := by rw [hx D hD, map_zero]

def selRes (ρ : Representation R G M) {U' U : Subgroup G} (h : U' ≤ U) (𝒟 : Set (Subgroup G)) :
    LocSel ρ U 𝒟 →ₗ[R] LocSel ρ U' 𝒟 :=
  (resU ρ h).restrict fun _ hx => resU_mem_locSel h hx

def ConjStable (𝒟 : Set (Subgroup G)) : Prop :=
  ∀ D ∈ 𝒟, ∀ g : G, ∃ D' ∈ 𝒟, ∀ x, x ∈ D ↔ g⁻¹ * x * g ∈ D'

abbrev quotRep (ρ : Representation R G M) (U U' : Subgroup G) [(U'.subgroupOf U).Normal] :=
  Representation.quotientToInvariants (ρ.comp U.subtype : Representation R U M) (U'.subgroupOf U)

section Conj

variable [IsTopologicalGroup G] [DiscreteTopology M]

def conjHom (U : Subgroup G) [hU : U.Normal] (g : G) : U →* U where
  toFun u := ⟨g⁻¹ * u * g, by simpa using hU.conj_mem u u.2 g⁻¹⟩
  map_one' := Subtype.ext (by simp)
  map_mul' _ _ := Subtype.ext (by simp [mul_assoc])

theorem continuous_conjHom (U : Subgroup G) [U.Normal] (g : G) : Continuous (conjHom U g) :=
  continuous_induced_rng.2 ((continuous_const.mul continuous_subtype_val).mul continuous_const)

def conjU (ρ : Representation R G M) (U : Subgroup G) [U.Normal] (g : G) :
    H1U ρ U →ₗ[R] H1U ρ U :=
  pairH1 _ _ (conjHom U g) (continuous_conjHom U g) (ρ g) continuous_of_discreteTopology fun u m => by
    show ρ g (ρ (g⁻¹ * u * g) m) = ρ u (ρ g m)
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
    simp [mul_assoc]

theorem conjU_mk (ρ : Representation R G M) (U : Subgroup G) [U.Normal] (g : G) (z : Z1U ρ U) :
    ∃ z' : Z1U ρ U, conjU ρ U g (Submodule.Quotient.mk z) = Submodule.Quotient.mk z' ∧
      ∀ u : U, z'.1 u = ρ g (z.1 (conjHom U g u)) := ⟨_, rfl, fun _ => rfl⟩

def conjRep (ρ : Representation R G M) (U : Subgroup G) [U.Normal] :
    Representation R G (H1U ρ U) where
  toFun := conjU ρ U
  map_one' := LinearMap.ext fun x => by
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨z', e, f⟩ := conjU_mk ρ U 1 z
    rw [e, Module.End.one_apply]
    congr 1
    refine Subtype.ext (funext fun u => ?_)
    rw [f, map_one, Module.End.one_apply]
    exact congrArg z.1 (Subtype.ext (by simp [conjHom]))
  map_mul' g h := LinearMap.ext fun x => by
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨z₁, e₁, f₁⟩ := conjU_mk ρ U h z
    obtain ⟨z₂, e₂, f₂⟩ := conjU_mk ρ U g z₁
    obtain ⟨z₃, e₃, f₃⟩ := conjU_mk ρ U (g * h) z
    rw [Module.End.mul_apply, e₁, e₂, e₃]
    congr 1
    refine Subtype.ext (funext fun u => ?_)
    rw [f₃, f₂, f₁, map_mul, Module.End.mul_apply]
    exact congrArg (fun t => ρ g (ρ h (z.1 t))) (Subtype.ext (by simp [conjHom, mul_assoc]))

theorem conjRep_apply (ρ : Representation R G M) (U : Subgroup G) [U.Normal] (g : G) :
    conjRep ρ U g = conjU ρ U g := rfl

private theorem cocycle_conj_identity (ρ : Representation R G M) (U : Subgroup G) (z : Z1U ρ U)
    (γ v : U) : ρ γ (z.1 (γ⁻¹ * (v * γ))) - z.1 v = ρ v (z.1 γ) - z.1 γ := by
  have hz : ∀ a b : U, z.1 (a * b) = z.1 a + ρ a (z.1 b) := ((mem_Z1 _ _).mp z.2).2
  have h1 : z.1 1 = 0 := by simpa using hz 1 1
  have hinv : ρ γ (z.1 γ⁻¹) = -z.1 γ := by
    have := hz γ γ⁻¹
    rw [mul_inv_cancel, h1] at this
    exact eq_neg_of_add_eq_zero_right this.symm
  have hmul : ∀ w : M, ρ γ (ρ (γ⁻¹ : U) w) = w := fun w => by
    rw [← Module.End.mul_apply, ← map_mul]; simp
  rw [hz, hz, map_add, hmul, hinv]
  abel

theorem conjRep_of_mem (ρ : Representation R G M) (U : Subgroup G) [U.Normal] {g : G} (hg : g ∈ U)
    (x : H1U ρ U) : conjRep ρ U g x = x := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨z', e, f⟩ := conjU_mk ρ U g z
  rw [conjRep_apply, e, mk_eq_mk]
  refine ⟨z.1 ⟨g, hg⟩, fun u => ?_⟩
  have hc : conjHom U g u = (⟨g, hg⟩ : U)⁻¹ * (u * ⟨g, hg⟩) :=
    Subtype.ext (by simp [conjHom, mul_assoc])
  rw [f u, hc]
  exact cocycle_conj_identity ρ U z ⟨g, hg⟩ u

theorem resU_conjRep (ρ : Representation R G M) {U' U : Subgroup G} [U.Normal] [U'.Normal]
    (h : U' ≤ U) (g : G) (x : H1U ρ U) :
    resU ρ h (conjRep ρ U g x) = conjRep ρ U' g (resU ρ h x) := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨z₁, e₁, f₁⟩ := conjU_mk ρ U g z
  obtain ⟨z₂, e₂, f₂⟩ := resU_mk ρ h z₁
  obtain ⟨z₃, e₃, f₃⟩ := resU_mk ρ h z
  obtain ⟨z₄, e₄, f₄⟩ := conjU_mk ρ U' g z₃
  rw [conjRep_apply, conjRep_apply, e₁, e₂, e₃, e₄]
  congr 1
  exact Subtype.ext (funext fun u => by
    rw [f₂, f₁, f₄, f₃]
    exact congrArg (fun t => ρ g (z.1 t)) (Subtype.ext (by simp [conjHom])))

theorem conjRep_mem_locSel (ρ : Representation R G M) (U : Subgroup G) [U.Normal]
    {𝒟 : Set (Subgroup G)} (h𝒟 : ConjStable 𝒟) (g : G) {x : H1U ρ U} (hx : x ∈ LocSel ρ U 𝒟) :
    conjRep ρ U g x ∈ LocSel ρ U 𝒟 := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨z', e, f⟩ := conjU_mk ρ U g z
  rw [conjRep_apply, e, mk_mem_locSel]
  rw [mk_mem_locSel] at hx
  intro D hD
  obtain ⟨D', hD', hiff⟩ := h𝒟 D hD g
  obtain ⟨m, hm⟩ := hx D' hD'
  refine ⟨ρ g m, fun u hu => ?_⟩
  rw [f u, hm (conjHom U g u) ((hiff u).mp hu), map_sub]
  congr 1
  rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
  congr 2
  simp [conjHom, mul_assoc]

def selRep (ρ : Representation R G M) (U : Subgroup G) [U.Normal] {𝒟 : Set (Subgroup G)}
    (h𝒟 : ConjStable 𝒟) : Representation R G (LocSel ρ U 𝒟) :=
  (conjRep ρ U).subrepresentation (LocSel ρ U 𝒟) fun g _ hx => conjRep_mem_locSel ρ U h𝒟 g hx

theorem coe_selRep (ρ : Representation R G M) (U : Subgroup G) [U.Normal] {𝒟 : Set (Subgroup G)}
    (h𝒟 : ConjStable 𝒟) (g : G) (x : LocSel ρ U 𝒟) :
    (selRep ρ U h𝒟 g x : H1U ρ U) = conjRep ρ U g x := rfl

theorem selRep_of_mem (ρ : Representation R G M) (U : Subgroup G) [U.Normal] {𝒟 : Set (Subgroup G)}
    (h𝒟 : ConjStable 𝒟) {g : G} (hg : g ∈ U) (x : LocSel ρ U 𝒟) :
    selRep ρ U h𝒟 g x = x :=
  Subtype.ext ((coe_selRep ρ U h𝒟 g x).trans (conjRep_of_mem ρ U hg x))

theorem selRes_selRep (ρ : Representation R G M) {U' U : Subgroup G} [U.Normal] [U'.Normal]
    (h : U' ≤ U) {𝒟 : Set (Subgroup G)} (h𝒟 : ConjStable 𝒟) (g : G) (x : LocSel ρ U 𝒟) :
    selRes ρ h 𝒟 (selRep ρ U h𝒟 g x) = selRep ρ U' h𝒟 g (selRes ρ h 𝒟 x) :=
  Subtype.ext (resU_conjRep ρ h g x)

abbrev invariantsUnderSubgroupH1 (ρ : Representation R G M) (U U' : Subgroup G) [U'.Normal] :
    Submodule R (H1U ρ U') :=
  Representation.invariants ((conjRep ρ U').comp U.subtype : Representation R U (H1U ρ U'))

abbrev selEig (ρ : Representation R G M) (U : Subgroup G) [U.Normal] {𝒟 : Set (Subgroup G)}
    (h𝒟 : ConjStable 𝒟) (W : Subgroup G) (ψ : W →* Rˣ) : Submodule R (LocSel ρ U 𝒟) :=
  eig ((selRep ρ U h𝒟).comp W.subtype : Representation R W (LocSel ρ U 𝒟)) ψ

abbrev resCoker (ρ : Representation R G M) {U' U : Subgroup G} [U'.Normal] (h : U' ≤ U) : Type :=
  invariantsUnderSubgroupH1 ρ U U' ⧸
    (LinearMap.range (resU ρ h)).comap (invariantsUnderSubgroupH1 ρ U U').subtype

theorem restriction_mem_invariant_H1 (ρ : Representation R G M) {U' U : Subgroup G} [U'.Normal]
    (h : U' ≤ U) (x : H1U ρ U) : resU ρ h x ∈ invariantsUnderSubgroupH1 ρ U U' := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨z₁, e₁, f₁⟩ := resU_mk ρ h z
  rw [e₁, Representation.mem_invariants]
  intro u
  show conjRep ρ U' (u : G) (Submodule.Quotient.mk z₁) = Submodule.Quotient.mk z₁
  obtain ⟨z₂, e₂, f₂⟩ := conjU_mk ρ U' (u : G) z₁
  rw [conjRep_apply, e₂, mk_eq_mk]
  refine ⟨z.1 u, fun v => ?_⟩
  have hc : (⟨(conjHom U' (u : G) v).1, h (conjHom U' (u : G) v).2⟩ : U) =
      u⁻¹ * (⟨v.1, h v.2⟩ * u) := Subtype.ext (by simp [conjHom, mul_assoc])
  have key := cocycle_conj_identity ρ U z u ⟨v.1, h v.2⟩
  rw [← hc] at key
  rw [f₂ v, f₁, f₁ v]
  exact key

end Conj

end SubgroupSelmer

end EigAndSubgroupCohomology

/-! ## Section 2: `QO`, `galOf`/`galEmb`, `shaFam`, Tower Subgroups, `Places`, and `RamFinite` -/

section CoeffFieldsShaAndPlaces

section Coeff

variable (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O]

/-- Base-changed `p`-divisible module `O ⊗_{ℤ_l} (ℚ_l / ℤ_l)` with discrete topology. -/
def QO : Type := O ⊗[ℤ_[l]] QZ l

instance : AddCommGroup (QO l O) := inferInstanceAs (AddCommGroup (O ⊗[ℤ_[l]] QZ l))
instance : Module O (QO l O) := inferInstanceAs (Module O (O ⊗[ℤ_[l]] QZ l))
instance : Module ℤ_[l] (QO l O) := inferInstanceAs (Module ℤ_[l] (O ⊗[ℤ_[l]] QZ l))
instance : IsScalarTower ℤ_[l] O (QO l O) := inferInstanceAs (IsScalarTower ℤ_[l] O (O ⊗[ℤ_[l]] QZ l))
instance : TopologicalSpace (QO l O) := ⊥
instance : DiscreteTopology (QO l O) := ⟨rfl⟩
instance : IsTopologicalAddGroup (QO l O) where
  continuous_add := continuous_of_discreteTopology
  continuous_neg := continuous_of_discreteTopology

def QO.incl : QZ l →ₗ[ℤ_[l]] QO l O := TensorProduct.mk ℤ_[l] O (QZ l) 1

theorem QO.isBaseChange : IsBaseChange O (QO.incl l O) := TensorProduct.isBaseChange ℤ_[l] (QZ l) O

/-- Ramification/length index `e_O = length_O(O / lO)`. -/
def eO : ℕ∞ := Module.length O (O ⧸ Ideal.span {(l : O)})

/-- Twisted representation `Oˣ`-character on `QO l O`. -/
abbrev twist₂ {Γ : Type} [Group Γ] {O : Type} [CommRing O] [Algebra ℤ_[l] O] (θ : Γ →* Oˣ) :
    Representation O Γ (QO l O) := scalRep (QO l O) θ

end Coeff

section Fields

variable (k E Ω : Type) [Field k] [Field E] [Field Ω] [Algebra k Ω] [Algebra E Ω]

def galOf : Subgroup (G k Ω) where
  carrier := {σ | ∀ x : E, σ (algebraMap E Ω x) = algebraMap E Ω x}
  one_mem' _ := rfl
  mul_mem' {a b} ha hb x := by rw [AlgEquiv.mul_apply, hb, ha]
  inv_mem' {a} ha x := a.symm_apply_eq.2 (ha x).symm

theorem mem_galOf {σ : G k Ω} :
    σ ∈ galOf k E Ω ↔ ∀ x : E, σ (algebraMap E Ω x) = algebraMap E Ω x := Iff.rfl

theorem galOf_self : galOf k k Ω = ⊤ := by
  ext σ
  exact ⟨fun _ => Subgroup.mem_top σ, fun _ => (mem_galOf k k Ω).2 fun x => σ.commutes x⟩

theorem galOf_le (E' : Type) [Field E'] [Algebra E E'] [Algebra E' Ω] [IsScalarTower E E' Ω] :
    galOf k E' Ω ≤ galOf k E Ω := by
  intro σ hσ
  rw [mem_galOf] at hσ ⊢
  intro x
  rw [IsScalarTower.algebraMap_apply E E' Ω]
  exact hσ _

variable [Algebra k E] [IsScalarTower k E Ω]

def galEmb : G E Ω →* G k Ω := AlgEquiv.restrictScalarsHom k

theorem galEmb_apply (σ : G E Ω) (x : Ω) : galEmb k E Ω σ x = σ x := rfl

theorem galEmb_mem (σ : G E Ω) : galEmb k E Ω σ ∈ galOf k E Ω := fun x => σ.commutes x

theorem range_galEmb : (galEmb k E Ω).range = galOf k E Ω := by
  ext σ
  constructor
  · rintro ⟨τ, rfl⟩
    exact galEmb_mem k E Ω τ
  · intro h
    exact ⟨{ σ.toRingEquiv with commutes' := fun x => (mem_galOf k E Ω).1 h x }, AlgEquiv.ext fun _ => rfl⟩

instance galOf_normal [Normal k E] : (galOf k E Ω).Normal where
  conj_mem σ h g x := by
    have e : (g⁻¹ : G k Ω) (algebraMap E Ω x) = algebraMap E Ω ((g⁻¹ : G k Ω).restrictNormal E x) :=
      (AlgEquiv.restrictNormal_commutes _ E x).symm
    rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, e, h, ← e]
    exact g.apply_symm_apply _

private def galBack : galOf k E Ω →* (Ω ≃ₐ[E] Ω) where
  toFun σ := AlgEquiv.ofRingEquiv (f := σ.1.toRingEquiv) σ.2
  map_one' := AlgEquiv.ext fun _ => rfl
  map_mul' _ _ := AlgEquiv.ext fun _ => rfl

end Fields

section ShaAndTower

variable (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] (l : ℕ)

/-- Conjugation-stable local Selmer family `shaFam`: `Dec A` for `A(l) < 1` and `Ine A` for all `A`. -/
def shaFam : Set (Subgroup (G k Ω)) :=
  {D | (∃ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 ∧ D = Dec (F := k) A) ∨
    ∃ A : ValuationSubring Ω, D = Ine (F := k) A}

private theorem valuation_lt_one_iff_mem_and_inv_not_mem {Ω : Type} [Field Ω] (A : ValuationSubring Ω)
    (z : Ω) : A.valuation z < 1 ↔ z ∈ A ∧ (z = 0 ∨ z⁻¹ ∉ A) := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp
  · have h0 : 0 < A.valuation z := by rw [zero_lt_iff]; simpa using hz
    rw [← A.valuation_le_one_iff, ← A.valuation_le_one_iff, map_inv₀, inv_le_one₀ h0]
    simp only [hz, false_or, not_le]
    exact ⟨fun h => ⟨h.le, h⟩, fun h => h.2⟩

private theorem comap_valuation_lt_one_iff_st {Ω : Type} [Field Ω] (A : ValuationSubring Ω)
    (f : Ω →+* Ω) (z : Ω) : (A.comap f).valuation z < 1 ↔ A.valuation (f z) < 1 := by
  rw [valuation_lt_one_iff_mem_and_inv_not_mem, valuation_lt_one_iff_mem_and_inv_not_mem,
    ValuationSubring.mem_comap, ValuationSubring.mem_comap, map_inv₀, map_eq_zero]

private theorem mem_decompositionSubgroup_iff_st {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
    (A : ValuationSubring Ω) (x : G k Ω) :
    x ∈ ValuationSubring.decompositionSubgroup k A ↔ ∀ y : Ω, x y ∈ A ↔ y ∈ A := by
  simp only [ValuationSubring.decompositionSubgroup, MulAction.mem_stabilizer_iff]
  constructor
  · intro h y
    have e := SetLike.ext_iff.1 h (x y)
    rw [ValuationSubring.mem_smul_pointwise_iff_exists] at e
    rw [← e]
    exact ⟨fun ⟨s, hs, hs'⟩ => by rw [AlgEquiv.smul_def] at hs'; rwa [← x.injective hs'],
      fun hy => ⟨y, hy, rfl⟩⟩
  · intro h
    ext y
    rw [ValuationSubring.mem_smul_pointwise_iff_exists]
    exact ⟨fun ⟨s, hs, hs'⟩ => hs' ▸ (h s).2 hs,
      fun hy => ⟨x.symm y, (h _).1 (by simpa using hy), by simp [AlgEquiv.smul_def]⟩⟩

theorem conjStable_shaFam : ConjStable (shaFam k Ω l) := by
  intro D hD g
  have key : ∀ x : G k Ω, ∀ y, g ((g⁻¹ * x * g) y) = x (g y) := fun x y => by
    rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, ← AlgEquiv.mul_apply g g⁻¹, mul_inv_cancel,
      AlgEquiv.one_apply]
  rcases hD with ⟨A, hl, rfl⟩ | ⟨A, rfl⟩
  · refine ⟨Dec (F := k) (A.comap (g : Ω →+* Ω)), Or.inl ⟨_, ?_, rfl⟩, fun x => ?_⟩
    · rw [comap_valuation_lt_one_iff_st]; simpa using hl
    · simp only [Dec, mem_decompositionSubgroup_iff_st, ValuationSubring.mem_comap,
        RingHom.coe_coe, key]
      exact ⟨fun h y => h (g y), fun h y => by simpa using h (g.symm y)⟩
  · refine ⟨Ine (F := k) (A.comap (g : Ω →+* Ω)), Or.inr ⟨_, rfl⟩, fun x => ?_⟩
    change x ∈ Inertia (F := k) A ↔ g⁻¹ * x * g ∈ Inertia (F := k) (A.comap (g : Ω →+* Ω))
    simp only [Inertia, Set.mem_ofPred_eq, mem_decompositionSubgroup_iff_st,
      ValuationSubring.valuation_le_one_iff, ValuationSubring.mem_comap, RingHom.coe_coe,
      comap_valuation_lt_one_iff_st, map_sub, key]
    exact ⟨fun ⟨h1, h2⟩ => ⟨fun y => h1 (g y), fun y hy => h2 (g y) hy⟩,
      fun ⟨h1, h2⟩ => ⟨fun y => by simpa using h1 (g.symm y),
        fun y hy => by simpa using h2 (g.symm y) (by simpa using hy)⟩⟩

variable {k Ω} {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] [TopologicalSpace M]
  [IsTopologicalAddGroup M] [ContinuousConstSMul R M]

abbrev ShaU (ρ : Representation R (G k Ω) M) (l : ℕ) (U : Subgroup (G k Ω)) :
    Submodule R (H1U ρ U) :=
  LocSel ρ U (shaFam k Ω l)

abbrev shaRep [DiscreteTopology M] (ρ : Representation R (G k Ω) M) (l : ℕ) (U : Subgroup (G k Ω))
    [U.Normal] : Representation R (G k Ω) (ShaU ρ l U) :=
  selRep ρ U (conjStable_shaFam k Ω l)

abbrev shaEig [DiscreteTopology M] (ρ : Representation R (G k Ω) M) (l : ℕ) (U : Subgroup (G k Ω))
    [U.Normal] (W : Subgroup (G k Ω)) (ψ : W →* Rˣ) : Submodule R (ShaU ρ l U) :=
  selEig ρ U (conjStable_shaFam k Ω l) W ψ

end ShaAndTower

section Tower

variable {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] (l : ℕ) [Fact l.Prime]

variable (k Ω) in
def chiO (O : Type) [CommRing O] [Algebra ℤ_[l] O] : G k Ω →* Oˣ :=
  (Units.map (algebraMap ℤ_[l] O).toMonoidHom).comp (cycZ k Ω l)

def levU (U : Subgroup (G k Ω)) (n : ℕ) : Subgroup (G k Ω) :=
  U ⊓ (princ l n).comap (cycZ k Ω l)

def cycU (U : Subgroup (G k Ω)) : Subgroup (G k Ω) := U ⊓ (cycZ k Ω l).ker

def delU (U : Subgroup (G k Ω)) : Subgroup (G k Ω) :=
  U ⊓ (CommGroup.torsion ℤ_[l]ˣ).comap (cycZ k Ω l)

def qExp (l : ℕ) : ℕ := if l = 2 then 2 else 1

abbrev gamU (U : Subgroup (G k Ω)) : Subgroup (G k Ω) := levU l U (qExp l)

instance (U : Subgroup (G k Ω)) [U.Normal] (n : ℕ) : (levU l U n).Normal := by
  unfold levU; infer_instance
instance (U : Subgroup (G k Ω)) [U.Normal] : (cycU l U).Normal := by
  unfold cycU; infer_instance
instance (U : Subgroup (G k Ω)) [U.Normal] : (delU l U).Normal := by
  unfold delU; infer_instance

theorem levU_le (U : Subgroup (G k Ω)) (n : ℕ) : levU l U n ≤ U := inf_le_left
theorem cycU_le (U : Subgroup (G k Ω)) : cycU l U ≤ U := inf_le_left

theorem cycU_le_levU (U : Subgroup (G k Ω)) (n : ℕ) : cycU l U ≤ levU l U n := by
  intro σ hσ
  simp only [cycU, levU, Subgroup.mem_inf, Subgroup.mem_comap, MonoidHom.mem_ker] at hσ ⊢
  exact ⟨hσ.1, by rw [hσ.2]; exact Subgroup.one_mem _⟩

theorem cycU_levU (U : Subgroup (G k Ω)) (n : ℕ) : cycU l (levU l U n) = cycU l U :=
  le_antisymm (inf_le_inf_right _ (levU_le l U n)) (le_inf (cycU_le_levU l U n) inf_le_right)

end Tower

section InflDef

variable (k : Type) {E Ω : Type} [Field k] [NumberField k] [Field E] [NumberField E] [Field Ω]
  [Algebra k E] [Algebra k Ω] [Algebra E Ω] [IsScalarTower k E Ω] [IsAlgClosure E Ω]
  {l : ℕ} [Fact l.Prime]

def Infl (D : LData E Ω l) (e : ℤ) (x : H1 (qzTw D e))
    (y : H1U (qzG k Ω l e) (galOf k E Ω)) : Prop :=
  ∃ (z : Z1 (qzTw D e)) (z' : Z1U (qzG k Ω l e) (galOf k E Ω)),
    x = Submodule.Quotient.mk z ∧ y = Submodule.Quotient.mk z' ∧
      ∀ σ : G E Ω, z'.1 ⟨galEmb k E Ω σ, galEmb_mem k E Ω σ⟩ = z.1 (toGS Ω _ σ)

end InflDef

theorem places :
    ∀ (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
      (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω),
      (A ≠ ⊤ → ∃ v : HeightOneSpectrum (𝓞 k), IsPlaceOver A v) ∧
      (A = ⊤ → Ine (F := k) A = ⊥ ∧ ¬ A.valuation (l : Ω) < 1) ∧
      (∀ v : HeightOneSpectrum (𝓞 k), IsPlaceOver A v → (A.valuation (l : Ω) < 1 ↔ v ∈ Above k l)) ∧
      (¬ A.valuation (l : Ω) < 1 → Ine (F := k) A ≤ (cycZ k Ω l).ker) := by
  intro k Ω _ _ _ _ _ l _ A
  have hint : ∀ z : Ω, IsIntegral ℤ z → A.valuation z ≤ 1 := fun z hz => by
    obtain ⟨y, rfl⟩ := (IsIntegrallyClosed.isIntegral_iff (R := A) (K := Ω)).mp (hz.tower_top (A := A))
    exact A.valuation_le_one y
  have hOk : ∀ x : 𝓞 k, A.valuation (algebraMap k Ω (x : k)) ≤ 1 := fun x =>
    hint _ x.isIntegral_coe.algebraMap
  have hl1 : A.valuation (l : Ω) ≤ 1 := (A.valuation_le_one_iff _).mpr (natCast_mem A l)
  have htop : A = ⊤ → ∀ y : Ω, A.valuation y < 1 → y = 0 := fun hA y hy => by
    by_contra h0
    have h2 : A.valuation y⁻¹ ≤ 1 :=
      (A.valuation_le_one_iff _).mpr (by rw [hA]; exact ValuationSubring.mem_top _)
    have h3 : A.valuation y * A.valuation y⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel₀ h0, map_one]
    exact absurd h3 (ne_of_lt (lt_of_le_of_lt (mul_le_of_le_one_right' h2) hy))
  have hlne : (l : Ω) ≠ 0 := by
    rw [← map_natCast (algebraMap k Ω)]
    exact (_root_.map_ne_zero _).mpr (Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hA
    let p : Ideal (𝓞 k) :=
      { carrier := {x | A.valuation (algebraMap k Ω (x : k)) < 1}
        add_mem' := fun {a b} ha hb => by
          simp only [Set.mem_ofPred_eq, map_add] at *
          exact lt_of_le_of_lt (A.valuation.map_add _ _) (max_lt ha hb)
        zero_mem' := by simp
        smul_mem' := fun c x hx => by
          simp only [Set.mem_ofPred_eq, smul_eq_mul, map_mul] at *
          exact lt_of_le_of_lt (mul_le_of_le_one_left' (hOk c)) hx }
    have hprime : p.IsPrime := by
      refine ⟨?_, fun {x y} hxy => ?_⟩
      · rw [Ne, Ideal.eq_top_iff_one]
        show ¬ A.valuation (algebraMap k Ω ((1 : 𝓞 k) : k)) < 1
        simp
      · change A.valuation (algebraMap k Ω ((x * y : 𝓞 k) : k)) < 1 at hxy
        change A.valuation (algebraMap k Ω (x : k)) < 1 ∨ A.valuation (algebraMap k Ω (y : k)) < 1
        simp only [map_mul] at hxy
        by_contra h
        push Not at h
        rw [le_antisymm (hOk x) h.1, le_antisymm (hOk y) h.2, one_mul] at hxy
        exact lt_irrefl _ hxy
    have hne : p ≠ ⊥ := by
      intro hbot
      apply hA
      have hk : ∀ y : k, A.valuation (algebraMap k Ω y) ≤ 1 := fun y => by
        obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 k) y
        have hb0 : (b : 𝓞 k) ≠ 0 := nonZeroDivisors.ne_zero hb
        have hbv : A.valuation (algebraMap k Ω (algebraMap (𝓞 k) k b)) = 1 :=
          le_antisymm (hOk b) (not_lt.mp fun h => hb0 (by have hbp : b ∈ p := h; rw [hbot] at hbp; exact (Submodule.mem_bot _).mp hbp))
        rw [map_div₀, map_div₀, hbv, div_one]
        exact hOk a
      let f : k →+* A := (algebraMap k Ω).codRestrict A fun y => (A.valuation_le_one_iff _).mp (hk y)
      have hcomp : (algebraMap A Ω).comp f = algebraMap k Ω := by ext y; rfl
      rw [eq_top_iff]
      intro z _
      obtain ⟨q, hqm, hq⟩ := Algebra.IsIntegral.isIntegral (R := k) z
      have hz : IsIntegral A z := ⟨q.map f, hqm.map f, by rw [Polynomial.eval₂_map, hcomp]; exact hq⟩
      obtain ⟨y, rfl⟩ := (IsIntegrallyClosed.isIntegral_iff (R := A) (K := Ω)).mp hz
      exact y.2
    exact ⟨⟨p, hprime, hne⟩, fun _ => Iff.rfl⟩
  · intro hA
    refine ⟨?_, fun h => hlne (htop hA _ h)⟩
    rw [Subgroup.eq_bot_iff_forall]
    intro σ hσ
    ext z
    have h1 := hσ.2 z ((A.valuation_le_one_iff _).mpr (by rw [hA]; exact ValuationSubring.mem_top _))
    have h2 := sub_eq_zero.mp (htop hA _ h1)
    simpa using h2
  · intro v hv
    have h := hv (l : 𝓞 k)
    simp only [map_natCast] at h
    exact h
  · intro hl σ hσ
    have hl1' : A.valuation (l : Ω) = 1 := le_antisymm hl1 (not_lt.mp hl)
    have hfix : ∀ (n : ℕ) (t : Ω), t ^ (l ^ n) = 1 → σ t = t := fun n t ht => by
      have hN : 0 < l ^ n := pow_pos (Fact.out : l.Prime).pos n
      set N := l ^ n with hNdef
      have htI : IsIntegral ℤ t := IsIntegral.of_pow hN (by rw [ht]; exact isIntegral_one)
      have huN : (σ t) ^ N = 1 := by rw [← map_pow, ht, map_one]
      have huI : IsIntegral ℤ (σ t) := IsIntegral.of_pow hN (by rw [huN]; exact isIntegral_one)
      by_contra hne
      set u := σ t
      set s := t ^ (N - 1)
      have hst : s * t = 1 := by rw [← pow_succ, Nat.sub_add_cancel hN, ht]
      set w := u * s with hw
      have hwN : w ^ N = 1 := by
        rw [mul_pow, huN, one_mul, ← pow_mul, mul_comm (N - 1) N, pow_mul, ht, one_pow]
      have hw1 : w ≠ 1 := fun h => hne (by
        have h' : w * t = t := by rw [h, one_mul]
        rw [hw, mul_assoc, hst, mul_one] at h'
        exact h')
      have hsI : IsIntegral ℤ s := htI.pow _
      have hwI : IsIntegral ℤ w := huI.mul hsI
      have hval : A.valuation (w - 1) < 1 := by
        have hws : w - 1 = (u - t) * s := by rw [sub_mul, mul_comm t s, hst]
        rw [hws, map_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_right' (hint s hsI)) (hσ.2 t (hint t htI))
      set c := ∑ j ∈ Finset.range N, ∑ i ∈ Finset.range j, w ^ i
      have hcI : IsIntegral ℤ c :=
        IsIntegral.sum _ fun j _ => IsIntegral.sum _ fun i _ => hwI.pow i
      have hid : (N : Ω) = (1 - w) * c := by
        rw [Finset.mul_sum]
        simp_rw [mul_neg_geom_sum]
        rw [Finset.sum_sub_distrib, geom_sum_eq hw1, hwN, sub_self, zero_div, sub_zero]
        simp
      have hNv : A.valuation (N : Ω) = 1 := by rw [hNdef, Nat.cast_pow, map_pow, hl1', one_pow]
      have hlt : A.valuation (N : Ω) < 1 := by
        rw [hid, map_mul, Valuation.map_sub_swap]
        exact lt_of_le_of_lt (mul_le_of_le_one_right' (hint c hcI)) hval
      rw [hNv] at hlt
      exact lt_irrefl _ hlt
    haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed k
    haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap k Ω).injective
    rw [MonoidHom.mem_ker]
    change cyclotomicCharacter Ω l (MulSemiringAction.toRingAut (G k Ω) Ω σ) = 1
    apply Units.ext
    rw [Units.val_one]
    refine PadicInt.ext_of_toZModPow.mp fun n => ?_
    rw [cyclotomicCharacter.toZModPow, map_one]
    refine (modularCyclotomicCharacter.unique _ _ _ fun t ht => ?_).symm
    have ht' : (t : Ω) ^ (l ^ n) = 1 := by
      rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity _ _).mp ht, Units.val_one]
    change σ (t : Ω) = _
    rw [hfix n _ ht']
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp at ht'; simp [ht']
    · haveI : Fact (1 < l ^ n) := ⟨Nat.one_lt_pow hn.ne' (Fact.out : l.Prime).one_lt⟩
      rw [ZMod.val_one, pow_one]

private theorem mem_nhds_one_gal_iff_exists_finset_fixing (K L : Type) [Field K] [Field L]
    [Algebra K L] [Algebra.IsIntegral K L] (s : Set Gal(L/K)) :
    s ∈ nhds (1 : Gal(L/K)) ↔ ∃ S : Finset L, {σ : Gal(L/K) | ∀ x ∈ S, σ x = x} ⊆ s := by
  classical
  constructor
  · intro hs
    obtain ⟨F, _, hFs⟩ := (krullTopology_mem_nhds_one_iff K L s).mp hs
    let b := Module.finBasis K F
    refine ⟨Finset.univ.image (fun i => (b i : L)), fun σ hσ => hFs ?_⟩
    rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]
    intro y hy
    have hb : ∀ i, σ (b i : L) = b i := fun i => hσ _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
    have hy' : y = ∑ i, (b.repr ⟨y, hy⟩ i) • (b i : L) := by
      have h := congrArg (fun z : F => (z : L)) (b.sum_repr ⟨y, hy⟩)
      simp only [IntermediateField.coe_sum, IntermediateField.coe_smul] at h
      exact h.symm
    rw [hy', map_sum]
    simp [map_smul, hb]
  · rintro ⟨S, hS⟩
    refine Filter.mem_of_superset ?_ hS
    have : {σ : Gal(L/K) | ∀ x ∈ S, σ x = x} =
        ⋂ x ∈ S, (MulAction.stabilizer Gal(L/K) x : Set Gal(L/K)) := by
      ext σ; simp [MulAction.mem_stabilizer_iff, AlgEquiv.smul_def]
    rw [this]
    exact (isOpen_biInter_finset fun x _ => stabilizer_isOpen_of_isIntegral x).mem_nhds (by simp)

theorem galEmbTop :
    ∀ (k E Ω : Type) [Field k] [NumberField k] [Field E] [NumberField E] [Field Ω] [Algebra k E]
      [Algebra k Ω] [Algebra E Ω] [IsScalarTower k E Ω] [IsAlgClosure k Ω] [IsAlgClosure E Ω],
      Topology.IsEmbedding (galEmb k E Ω) ∧ IsOpen (galOf k E Ω : Set (G k Ω)) ∧
        (galOf k E Ω).index = Module.finrank k E := by
  intro k E Ω _ _ _ _ _ _ _ _ _ _ _
  have hE : FiniteDimensional k E := Module.Finite.of_restrictScalars_finite ℚ k E
  let L : IntermediateField k Ω := (IsScalarTower.toAlgHom k E Ω).fieldRange
  have hL : FiniteDimensional k L :=
    LinearEquiv.finiteDimensional (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom k E Ω)).toLinearEquiv
  have hset : galOf k E Ω = L.fixingSubgroup := by
    ext σ
    rw [IntermediateField.mem_fixingSubgroup_iff]
    exact ⟨fun h y ⟨x, hx⟩ => hx ▸ by simpa using h x, fun h x => by simpa using h _ ⟨x, rfl⟩⟩
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rw [IsTopologicalGroup.isInducing_iff_nhds_one]
    ext s
    rw [Filter.mem_comap]
    constructor
    · intro hs
      obtain ⟨S, hS⟩ := (mem_nhds_one_gal_iff_exists_finset_fixing E Ω s).mp hs
      exact ⟨{σ : G k Ω | ∀ x ∈ S, σ x = x},
        (mem_nhds_one_gal_iff_exists_finset_fixing k Ω _).mpr ⟨S, subset_rfl⟩, fun _ hσ => hS hσ⟩
    · rintro ⟨t, ht, hts⟩
      obtain ⟨S, hS⟩ := (mem_nhds_one_gal_iff_exists_finset_fixing k Ω t).mp ht
      exact (mem_nhds_one_gal_iff_exists_finset_fixing E Ω s).mpr ⟨S, fun _ hσ => hts (hS hσ)⟩
  · exact fun _ _ h => AlgEquiv.ext fun x => DFunLike.congr_fun h x
  · rw [hset]; exact L.fixingSubgroup_isOpen
  · rw [hset, ← IntermediateField.finrank_eq_fixingSubgroup_index]
    exact (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom k E Ω)).toLinearEquiv.finrank_eq.symm

theorem galEmbFam :
    ∀ (k E Ω : Type) [Field k] [NumberField k] [Field E] [NumberField E] [Field Ω] [Algebra k E]
      [Algebra k Ω] [Algebra E Ω] [IsScalarTower k E Ω] [IsAlgClosure k Ω] [IsAlgClosure E Ω]
      (l : ℕ) [Fact l.Prime],
      (∀ A : ValuationSubring Ω,
        (Dec (F := k) A).comap (galEmb k E Ω) = Dec (F := E) A ∧
        (Ine (F := k) A).comap (galEmb k E Ω) = Ine (F := E) A) ∧
      Subgroup.comap (galEmb k E Ω) '' shaFam k Ω l = shaFam E Ω l ∧
      (cycZ k Ω l).comp (galEmb k E Ω) = cycZ E Ω l ∧
      ∀ e : ℤ, (qzG k Ω l e).comp (galEmb k E Ω) = qzG E Ω l e := by
  intro k E Ω _ _ _ _ _ _ _ _ _ _ _ l _
  have hD : ∀ A : ValuationSubring Ω, (Dec (F := k) A).comap (galEmb k E Ω) = Dec (F := E) A := fun A => by
    ext σ; rw [Subgroup.mem_comap, mem_Dec, mem_Dec]; exact Iff.rfl
  have hI : ∀ A : ValuationSubring Ω, (Ine (F := k) A).comap (galEmb k E Ω) = Ine (F := E) A := fun A => by
    ext σ; rw [Subgroup.mem_comap]; exact and_congr (SetLike.ext_iff.1 (hD A) σ) Iff.rfl
  refine ⟨fun A => ⟨hD A, hI A⟩, ?_, MonoidHom.ext fun _ => rfl, fun _ => MonoidHom.ext fun _ => rfl⟩
  ext D
  exact ⟨by rintro ⟨_, ⟨A, hl, rfl⟩ | ⟨A, rfl⟩, rfl⟩; exact Or.inl ⟨A, hl, hD A⟩; exact Or.inr ⟨A, hI A⟩,
    by rintro (⟨A, hl, rfl⟩ | ⟨A, rfl⟩); exact ⟨_, Or.inl ⟨A, hl, rfl⟩, hD A⟩; exact ⟨_, Or.inr ⟨A, rfl⟩, hI A⟩⟩

theorem galQuot :
    ∀ (k E Ω : Type) [Field k] [NumberField k] [Field E] [NumberField E] [Field Ω] [Algebra k E]
      [Algebra k Ω] [Algebra E Ω] [IsScalarTower k E Ω] [IsAlgClosure k Ω] [IsAlgClosure E Ω]
      [Normal k E],
      Function.Surjective (AlgEquiv.restrictNormalHom E : G k Ω →* (E ≃ₐ[k] E)) ∧
      (AlgEquiv.restrictNormalHom E : G k Ω →* (E ≃ₐ[k] E)).ker = galOf k E Ω ∧
      ∀ σ : G k Ω, IsLift (AlgEquiv.restrictNormalHom E σ : E ≃ₐ[k] E).toRingEquiv σ.toRingEquiv := by
  intro k E Ω _ _ _ _ _ _ _ _ _ _ _ _
  have hN : Normal k Ω := IsAlgClosure.normal k Ω
  have hc : ∀ (σ : G k Ω) (x : E),
      σ (algebraMap E Ω x) = algebraMap E Ω (AlgEquiv.restrictNormalHom E σ x) :=
    fun σ x => (AlgEquiv.restrictNormal_commutes σ E x).symm
  refine ⟨AlgEquiv.restrictNormalHom_surjective Ω, ?_, hc⟩
  ext σ
  rw [MonoidHom.mem_ker]
  exact ⟨fun h x => by rw [hc, h]; rfl,
    fun h => AlgEquiv.ext fun x => (algebraMap E Ω).injective (by rw [← hc, h]; rfl)⟩

open Polynomial in
private theorem ram_key {Ω : Type} [Field Ω] (A : ValuationSubring Ω) (f : ℤ[X]) {a b : Ω}
    (ha : a ∈ A) (hb : b ∈ A) (fa : aeval a f = 0) (fb : aeval b f = 0)
    (hab : A.valuation (b - a) < 1) (hd : ¬ A.valuation (aeval a (derivative f)) < 1) : b = a := by
  by_contra hne
  apply hd
  obtain ⟨c, hc⟩ := (f.map (algebraMap ℤ A)).binomExpansion ⟨a, ha⟩ (⟨b, hb⟩ - ⟨a, ha⟩)
  have e : ∀ (g : ℤ[X]) (x : A), ((eval x (g.map (algebraMap ℤ A)) : A) : Ω) = aeval (x : Ω) g :=
    fun g x => by rw [eval_map_algebraMap]; exact (aeval_algHom_apply (A.subtype.toIntAlgHom) x g).symm
  rw [add_sub_cancel, derivative_map] at hc
  have h2 := congrArg (fun x : A => (x : Ω)) hc
  push_cast at h2
  simp only [e, fa, fb] at h2
  have h3 : aeval a (derivative f) = -(c : Ω) * (b - a) :=
    mul_right_cancel₀ (sub_ne_zero.2 hne) (by linear_combination -h2)
  rw [h3, map_mul, Valuation.map_neg]
  exact lt_of_le_of_lt (mul_le_of_le_one_left' (A.valuation_le_one c)) hab

open Polynomial in
private theorem ram_fix_int {k E' Ω : Type} [Field k] [NumberField k] [Field E'] [NumberField E']
    [Field Ω] [Algebra k Ω] [Algebra E' Ω] (α : 𝓞 E') :
    ∃ d : ℤ, d ≠ 0 ∧ ∀ A : ValuationSubring Ω, ¬ A.valuation (d : Ω) < 1 →
      ∀ σ ∈ Ine (F := k) A, σ (algebraMap E' Ω α) = algebraMap E' Ω α := by
  have hi : IsIntegral ℤ α := Algebra.IsIntegral.isIntegral α
  have hne : aeval α (derivative (minpoly ℤ α)) ≠ 0 := fun h => by
    have h1 := minpoly.isIntegrallyClosed_dvd hi h
    have h2 := minpoly.natDegree_pos hi
    have h3 : derivative (minpoly ℤ α) ≠ 0 := fun h0 => by
      have := derivative_eq_zero.mp h0; omega
    have h4 := natDegree_le_of_dvd h1 h3
    have h5 := natDegree_derivative_lt (p := minpoly ℤ α) (by omega)
    omega
  set δ := aeval α (derivative (minpoly ℤ α)) with hδ
  have hm : (Algebra.norm ℤ δ : 𝓞 E') ∈ Ideal.span {δ} := by
    have := Ideal.absNorm_mem (Ideal.span {δ})
    rw [Ideal.absNorm_span_singleton] at this
    rcases Int.natAbs_eq (Algebra.norm ℤ δ) with h | h <;> [rw [h]; rw [h]] <;> simpa using this
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 hm
  refine ⟨Algebra.norm ℤ δ, Algebra.norm_ne_zero_iff.2 hne, fun A hA σ hσ => ?_⟩
  let φ : 𝓞 E' →ₐ[ℤ] Ω := ((algebraMap E' Ω).comp (algebraMap (𝓞 E') E')).toIntAlgHom
  have hφ : ∀ x, φ x ∈ A := fun x => mem_of_isIntegral_int A ((Algebra.IsIntegral.isIntegral x).map φ)
  let ψ : Ω →ₐ[ℤ] Ω := σ.toRingEquiv.toRingHom.toIntAlgHom
  have fa : aeval (φ α) (minpoly ℤ α) = 0 := by rw [aeval_algHom_apply, minpoly.aeval, map_zero]
  change ψ (φ α) = φ α
  refine ram_key A (minpoly ℤ α) (hφ α) (mem_of_isIntegral_int A ((hi.map φ).map ψ)) fa
    (by rw [aeval_algHom_apply, fa, map_zero]) (hσ.2 _ ((A.valuation_le_one_iff _).2 (hφ α))) fun h => hA ?_
  rw [aeval_algHom_apply, ← hδ] at h
  have e : ((Algebra.norm ℤ δ : ℤ) : Ω) = φ t * φ δ := by rw [← map_mul, ht, map_intCast]
  rw [e, map_mul]
  exact lt_of_le_of_lt (mul_le_of_le_one_left' ((A.valuation_le_one_iff _).2 (hφ t))) h

open Polynomial in
private theorem ram_fix_root {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    {N : ℕ} (hN : N ≠ 0) (A : ValuationSubring Ω) (hA : ¬ A.valuation (N : Ω) < 1) {σ : G k Ω}
    (hσ : σ ∈ Ine (F := k) A) {z : Ω} (hz : z ^ N = 1) : σ z = z := by
  have hm : ∀ {y : Ω}, y ^ N = 1 → y ∈ A := fun {y} hy =>
    mem_of_isIntegral_int A (IsIntegral.of_pow (Nat.pos_of_ne_zero hN) (hy ▸ isIntegral_one))
  have hz' : (σ z) ^ N = 1 := by rw [← map_pow, hz, map_one]
  refine ram_key A (X ^ N - 1) (hm hz) (hm hz') (by simp [hz]) (by simp [hz'])
    (hσ.2 _ ((A.valuation_le_one_iff _).2 (hm hz))) fun h => hA ?_
  have e : (N : Ω) = z * aeval z (derivative (X ^ N - 1 : ℤ[X])) := by
    simp only [derivative_sub, derivative_X_pow, derivative_one, sub_zero, map_mul, map_natCast,
      map_pow, aeval_X]
    rw [mul_left_comm, ← pow_succ', Nat.sub_add_cancel (Nat.pos_of_ne_zero hN), hz, mul_one]
  rw [e, map_mul]
  exact lt_of_le_of_lt (mul_le_of_le_one_left' ((A.valuation_le_one_iff _).2 (hm hz))) h

theorem ramFinite :
    ∀ (k E E' Ω : Type) [Field k] [NumberField k] [Field E] [NumberField E] [Field E']
      [NumberField E'] [Field Ω] [Algebra k Ω] [Algebra E E'] [Algebra E Ω] [Algebra E' Ω]
      [Algebra k E] [IsScalarTower k E Ω] [IsScalarTower E E' Ω] [IsAlgClosure k Ω]
      [IsAlgClosure E Ω] [IsAlgClosure E' Ω],
      (∃ T : Finset (HeightOneSpectrum (𝓞 E)), ∀ v, v ∉ T → ∀ A : ValuationSubring Ω,
        IsPlaceOver A v → galOf k E Ω ⊓ Ine (F := k) A ≤ galOf k E' Ω) ∧
      ∀ (N : ℕ) [NeZero N] [IsCyclotomicExtension {N} E E'] (A : ValuationSubring Ω),
        ¬ A.valuation (N : Ω) < 1 → galOf k E Ω ⊓ Ine (F := k) A ≤ galOf k E' Ω := by
  intro k E E' Ω _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap k Ω).injective
  refine ⟨?_, fun N _ hc A hA σ hσ x => ?_⟩
  · choose d hd0 hd using fun α : 𝓞 E' => ram_fix_int (k := k) (Ω := Ω) α
    have hfin : ∀ i, {v : HeightOneSpectrum (𝓞 E) |
        v.asIdeal ∣ Ideal.span {((d (RingOfIntegers.basis E' i) : ℤ) : 𝓞 E)}}.Finite := fun i =>
      Ideal.finite_factors (by simpa using hd0 _)
    refine ⟨(Set.finite_iUnion hfin).toFinset, fun v hv A hA σ hσ x => ?_⟩
    simp only [Set.Finite.mem_toFinset, Set.mem_iUnion, Set.mem_ofPred_eq, not_exists,
      Ideal.dvd_span_singleton] at hv
    have h : (σ.toRingEquiv.toRingHom.comp (algebraMap E' Ω)).toRatAlgHom.toLinearMap =
        (algebraMap E' Ω).toRatAlgHom.toLinearMap := (integralBasis E').ext fun i => by
      rw [integralBasis_apply]
      exact hd _ A (fun h => hv i ((hA _).1 (by simpa using h))) σ hσ.2
    exact LinearMap.congr_fun h x
  · have hx := hc.adjoin_roots x
    induction hx using Algebra.adjoin_induction with
    | mem y hy =>
      obtain ⟨n, hn, h0, hy⟩ := hy
      obtain rfl : n = N := hn
      exact ram_fix_root h0 A hA hσ.2 (by rw [← map_pow, hy, map_one])
    | algebraMap r => rw [← IsScalarTower.algebraMap_apply]; exact hσ.1 r
    | add a b _ _ ha hb => rw [map_add, map_add, ha, hb]
    | mul a b _ _ ha hb => rw [map_mul, map_mul, ha, hb]

end CoeffFieldsShaAndPlaces

/-! ## Section 3: `dvrFacts`, `existsO`, `normO`, `contTw`, `decInf`, `padicUnitsLog`, `princZl`, `gammaGen` -/

section DvrAndCyclotomicUnits

section DvrAndO

private theorem dvr_algebraMap_inj {l : ℕ} [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] :
    Function.Injective (algebraMap ℤ_[l] O) := by
  rw [RingHom.injective_iff_ker_eq_bot]
  by_contra hne
  have hp : (RingHom.ker (algebraMap ℤ_[l] O)).IsPrime := RingHom.ker_isPrime _
  have hmax : (RingHom.ker (algebraMap ℤ_[l] O)).IsMaximal := hp.isMaximal hne
  have hbot : (⊥ : Ideal O).IsMaximal := by
    apply Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := ℤ_[l])
    rwa [← RingHom.ker_eq_comap_bot]
  exact IsDiscreteValuationRing.not_a_field O (IsLocalRing.eq_maximalIdeal hbot).symm

private theorem dvr_length_quot {l : ℕ} [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [Module.Free ℤ_[l] O] :
    Module.length ℤ_[l] (O ⧸ Ideal.span {(l : O)}) = Module.finrank ℤ_[l] O := by
  have hspan : Ideal.span {(l : O)} = (IsLocalRing.maximalIdeal ℤ_[l]).map (algebraMap ℤ_[l] O) := by
    rw [PadicInt.maximalIdeal_eq_span_p, Ideal.map_span, Set.image_singleton, map_natCast]
  rw [hspan, ← IsLocalRing.finrank_quotient_map (R := ℤ_[l]) (S := O)]
  letI : Field (ℤ_[l] ⧸ IsLocalRing.maximalIdeal ℤ_[l]) := Ideal.Quotient.field _
  haveI : Module.Finite (ℤ_[l] ⧸ IsLocalRing.maximalIdeal ℤ_[l])
      (O ⧸ (IsLocalRing.maximalIdeal ℤ_[l]).map (algebraMap ℤ_[l] O)) :=
    Module.Finite.of_restrictScalars_finite ℤ_[l] _ _
  rw [← Module.length_eq_finrank]
  exact Module.length_eq_of_surjective Ideal.Quotient.mk_surjective

theorem dvrFacts :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
      [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O],
      Function.Injective (algebraMap ℤ_[l] O) ∧ Module.Free ℤ_[l] O ∧
      IsLocalHom (algebraMap ℤ_[l] O) ∧ IsAdicComplete (IsLocalRing.maximalIdeal O) O ∧
      eO l O = Module.length O (O ⧸ (IsLocalRing.maximalIdeal ℤ_[l]).map (algebraMap ℤ_[l] O)) ∧
      eO l O ≠ 0 ∧ eO l O ≤ (Module.finrank ℤ_[l] O : ℕ∞) ∧
      eO l O = IsDiscreteValuationRing.addVal O (l : O) ∧
      ∀ n : ℕ, ¬ l ∣ n → IsUnit (n : O) := by
  intro l _ O _ _ _ _ _
  have hinj := dvr_algebraMap_inj (l := l) O
  haveI : CharZero O := charZero_of_injective_algebraMap hinj
  obtain ⟨hcomp, -, hlm, -, hfree, hloc⟩ := dvr_finite l O
  haveI := hfree; haveI := hloc
  have hspan : Ideal.span {(l : O)} = (IsLocalRing.maximalIdeal ℤ_[l]).map (algebraMap ℤ_[l] O) := by
    rw [PadicInt.maximalIdeal_eq_span_p, Ideal.map_span, Set.image_singleton, map_natCast]
  have hl0 : (l : O) ≠ 0 := fun h => by
    have h'' : ((l : ℕ) : ℤ_[l]) = 0 := hinj (by rw [map_natCast, h, map_zero])
    exact (Fact.out : l.Prime).ne_zero (by exact_mod_cast h'')
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hl0 hϖ
  have hval : IsDiscreteValuationRing.addVal O (l : O) = n :=
    IsDiscreteValuationRing.addVal_def _ u hϖ n hu
  have he : eO l O = n := by
    show Module.length O (O ⧸ Ideal.span {(l : O)}) = n
    rw [hu, Ideal.span_singleton_mul_left_unit u.isUnit, ← Ideal.span_singleton_pow,
      ← hϖ.maximalIdeal_eq]
    exact IsDiscreteValuationRing.length_quotient_pow_maximalIdeal (R := O) n
  have hn0 : n ≠ 0 := by
    rintro rfl; rw [pow_zero, mul_one] at hu
    exact (IsLocalRing.mem_maximalIdeal _).1 hlm (hu ▸ u.isUnit)
  refine ⟨hinj, hfree, hloc, hcomp, ?_, ?_, ?_, ?_, ?_⟩
  · show Module.length O (O ⧸ Ideal.span {(l : O)}) = _; rw [hspan]
  · rw [he]; exact_mod_cast hn0
  · rw [← dvr_length_quot (l := l) O]
    show Module.length O (O ⧸ Ideal.span {(l : O)}) ≤ _
    rw [IsLocalRing.length_restrictScalars ℤ_[l] O (O ⧸ Ideal.span {(l : O)})]
    exact le_mul_of_one_le_right' (Order.one_le_iff_pos.2 Module.length_pos)
  · rw [he, hval]
  · intro m hm
    obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hm)
    by_contra hmu
    have hmm : (m : O) ∈ IsLocalRing.maximalIdeal O := (IsLocalRing.mem_maximalIdeal _).2 hmu
    have h1 : (1 : O) ∈ IsLocalRing.maximalIdeal O := by
      have hab' : (a : O) * (l : O) + (b : O) * (m : O) = 1 := by
        exact_mod_cast congrArg (Int.cast : ℤ → O) hab
      rw [← hab']
      exact add_mem (Ideal.mul_mem_left _ _ hlm) (Ideal.mul_mem_left _ _ hmm)
    exact (IsLocalRing.maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).2 h1)

theorem existsO :
    ∀ (l : ℕ) [Fact l.Prime] (n : ℕ) [NeZero n], ∃ O : Subalgebra ℤ_[l] (PadicAlgCl l),
      IsDiscreteValuationRing O ∧ Module.Finite ℤ_[l] O ∧ HasEnoughRootsOfUnity O n := by
  intro l _ n _
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (PadicAlgCl l) n
  have hζi : IsIntegral ℤ_[l] ζ := (hζ.isIntegral (NeZero.pos n)).tower_top
  let K : IntermediateField ℚ_[l] (PadicAlgCl l) := IntermediateField.adjoin ℚ_[l] {ζ}
  haveI : FiniteDimensional ℚ_[l] K :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral ζ)
  obtain ⟨_, _, _⟩ := dvr_intClosure l K
  let f : K →ₐ[ℤ_[l]] PadicAlgCl l := K.val.restrictScalars ℤ_[l]
  have hf : Function.Injective f := Subtype.val_injective
  let e := (integralClosure ℤ_[l] K).equivMapOfInjective f hf
  refine ⟨(integralClosure ℤ_[l] K).map f,
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e,
    Module.Finite.equiv e.toLinearEquiv, ?_⟩
  have hmem : ζ ∈ (integralClosure ℤ_[l] K).map f :=
    ⟨⟨ζ, IntermediateField.mem_adjoin_simple_self _ _⟩, (isIntegral_algHom_iff f hf).1 hζi, rfl⟩
  exact ⟨⟨⟨ζ, hmem⟩, IsPrimitiveRoot.of_map_of_injective
    (f := ((integralClosure ℤ_[l] K).map f).val) hζ Subtype.val_injective⟩, rootsOfUnity.isCyclic _ _⟩

private theorem norm_le_one_of_isIntegral (l : ℕ) [Fact l.Prime] (x : PadicAlgCl l)
    (hx : IsIntegral ℤ_[l] x) : ‖x‖ ≤ 1 := by
  have hle : ∀ y : PadicAlgCl l, y ∈ (PadicAlgCl.valued l).v.integer ↔ ‖y‖ ≤ 1 := fun y => by
    rw [Valuation.mem_integer_iff, ← NNReal.coe_le_coe, PadicAlgCl.valuation_coe, NNReal.coe_one]
  have hmem : ∀ a : ℤ_[l], algebraMap ℤ_[l] (PadicAlgCl l) a ∈ (PadicAlgCl.valued l).v.integer :=
    fun a => (hle _).2 (by
      rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l)]
      exact (PadicAlgCl.norm_extends l _).trans_le a.2)
  exact (hle x).1 ((Valuation.integer.integers (PadicAlgCl.valued l).v).mem_of_integral
    (hx.map_of_comp_eq ((algebraMap ℤ_[l] (PadicAlgCl l)).codRestrict _ hmem) (RingHom.id _) rfl))

theorem normO :
    ∀ (l : ℕ) [Fact l.Prime] (O : Subalgebra ℤ_[l] (PadicAlgCl l)) [IsDiscreteValuationRing O]
      [Module.Finite ℤ_[l] O] (a : O), a ≠ 0 →
      ‖(a : PadicAlgCl l)‖ ^ (eO l O).toNat = ((l : ℝ)⁻¹) ^ (IsDiscreteValuationRing.addVal O a).toNat := by
  intro l _ O _ _ a ha
  have hle : ∀ x : O, ‖(x : PadicAlgCl l)‖ ≤ 1 := fun x =>
    norm_le_one_of_isIntegral l _ ((Algebra.IsIntegral.isIntegral (R := ℤ_[l]) x).map O.val)
  have hu : ∀ u : Oˣ, ‖((u : O) : PadicAlgCl l)‖ = 1 := fun u => by
    have h1 : ‖((u : O) : PadicAlgCl l)‖ * ‖((u⁻¹ : Oˣ) : O).1‖ = 1 := by
      rw [← norm_mul, ← Subalgebra.coe_mul, Units.mul_inv]; simp
    have := hle u; have := hle (u⁻¹ : Oˣ); have := norm_nonneg ((u : O) : PadicAlgCl l)
    nlinarith
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have key : ∀ x : O, x ≠ 0 →
      ‖(x : PadicAlgCl l)‖ = ‖(ϖ : PadicAlgCl l)‖ ^ (IsDiscreteValuationRing.addVal O x).toNat :=
    fun x hx => by
      obtain ⟨n, u, h⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hϖ
      rw [IsDiscreteValuationRing.addVal_def x u hϖ n h, h]
      simp [hu]
  have hl0 : (l : O) ≠ 0 := fun h => by
    have h' : ((l : O) : PadicAlgCl l) = 0 := by rw [h]; rfl
    exact (Fact.out : l.Prime).ne_zero (by simpa using h')
  have hl : ‖((l : O) : PadicAlgCl l)‖ = (l : ℝ)⁻¹ := by
    have : ((l : O) : PadicAlgCl l) = algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l]) := by simp
    rw [this, norm_algebraMap', Padic.norm_p]
  have he : eO l O = IsDiscreteValuationRing.addVal O (l : O) := (dvrFacts l O).2.2.2.2.2.2.2.1
  rw [he, ← hl, key a ha, key _ hl0, ← pow_mul, ← pow_mul, mul_comm]

end DvrAndO

section ContTwAndDecInf

private theorem cont_smul (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O]
    (Γ : Type) [Group Γ] [TopologicalSpace Γ] (χ : Γ →* ℤ_[l]ˣ)
    (hχ : Continuous fun g => ((χ g : ℤ_[l]ˣ) : ℤ_[l])) (m : QO l O) :
    Continuous fun g => ((χ g : ℤ_[l]ˣ) : ℤ_[l]) • m := by
  refine (QO.isBaseChange l O).inductionOn m
    (motive := fun m => Continuous fun g => ((χ g : ℤ_[l]ˣ) : ℤ_[l]) • m)
    (by simpa using continuous_const)
    (fun x => ((continuous_of_discreteTopology (f := QO.incl l O)).comp
      ((contScal l Γ χ hχ).comp (Continuous.prodMk_left x))).congr fun g =>
        map_smul (QO.incl l O) _ x)
    (fun s _ hx => (continuous_of_discreteTopology.comp hx).congr fun g => smul_comm _ _ _)
    (fun _ _ hx hy => (hx.add hy).congr fun g => (smul_add _ _ _).symm)

private theorem locConst_of_isOpen_ker {Γ A : Type} [Group Γ] [TopologicalSpace Γ]
    [IsTopologicalGroup Γ] [Group A] (ψ : Γ →* A) (h : IsOpen (ψ.ker : Set Γ)) :
    IsLocallyConstant ψ := by
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  refine ⟨(fun y => x⁻¹ * y) ⁻¹' (ψ.ker : Set Γ), h.preimage (continuous_const.mul continuous_id),
    by simp, fun y hy => ?_⟩
  have hk : ψ (x⁻¹ * y) = 1 := MonoidHom.mem_ker.mp hy
  rw [map_mul, map_inv, inv_mul_eq_one] at hk
  exact hk.symm

theorem contTw :
    ∀ (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
      (l : ℕ) [Fact l.Prime],
      Continuous (cycZ k Ω l) ∧ (∀ e : ℤ, ContAction (qzG k Ω l e)) ∧
      ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] (ψ : G k Ω →* Oˣ) (n : ℤ),
        IsOpen (ψ.ker : Set (G k Ω)) → ContAction (twist₂ l (ψ * chiO k Ω l O ^ n)) := by
  intro k Ω _ _ _ _ _ l _
  have hc := continuous_cycZ k Ω l
  refine ⟨hc, fun e => contScal l _ _ (Units.continuous_val.comp (hc.zpow (-e))),
    fun O _ _ ψ n hψ => continuous_prod_of_discrete_right.2 fun m => ?_⟩
  have h1 := cont_smul l O _ (cycZ k Ω l ^ n) (Units.continuous_val.comp (hc.zpow n)) m
  have h2 := ((locConst_of_isOpen_ker ψ hψ).prodMk ((IsLocallyConstant.iff_continuous _).2 h1)).comp
    fun p : Oˣ × QO l O => (p.1 : O) • p.2
  refine h2.continuous.congr fun g => ?_
  show (ψ g : O) • (((cycZ k Ω l g ^ n : ℤ_[l]ˣ) : ℤ_[l]) • m) =
    ((ψ g * chiO k Ω l O g ^ n : Oˣ) : O) • m
  have e : chiO k Ω l O g ^ n = Units.map (algebraMap ℤ_[l] O).toMonoidHom (cycZ k Ω l g ^ n) :=
    (map_zpow (Units.map (algebraMap ℤ_[l] O).toMonoidHom) (cycZ k Ω l g) n).symm
  rw [Units.val_mul, mul_smul, e]
  exact congrArg _ (algebraMap_smul O _ m).symm

private theorem exists_unit_not_finOrder (l : ℕ) [hl : Fact l.Prime] :
    ∃ u : ℤ_[l]ˣ, ¬ IsOfFinOrder u := by
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.out.one_lt
  have hl2 := hl.out.two_le
  have hnorm : ‖((1 + l : ℕ) : ℤ_[l])‖ = 1 := by
    push_cast
    rw [PadicInt.norm_add_eq_max_of_ne, norm_one, PadicInt.norm_p]
    · exact max_eq_left (inv_le_one_of_one_le₀ hl1.le)
    · rw [norm_one, PadicInt.norm_p]; exact (inv_lt_one_of_one_lt₀ hl1).ne'
  obtain ⟨u, hu⟩ := PadicInt.isUnit_iff.2 hnorm
  refine ⟨u, fun h => ?_⟩
  rw [← Units.isOfFinOrder_val, hu, isOfFinOrder_iff_pow_eq_one] at h
  obtain ⟨n, hn, h⟩ := h
  rw [← Nat.cast_pow, Nat.cast_eq_one, Nat.pow_eq_one] at h
  omega

theorem decInf :
    ∀ (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
      (l : ℕ) [Fact l.Prime] (U : Subgroup (G k Ω)), IsOpen (U : Set (G k Ω)) →
      ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 →
      ∃ g ∈ U ⊓ Dec (F := k) A, ¬ IsOfFinOrder (cycZ k Ω l g) := by
  intro k Ω _ _ _ _ _ l _ U hU A hlt
  obtain ⟨hP1, hP2, hP3, -⟩ := places k Ω l A
  have hA : A ≠ ⊤ := fun h => (hP2 h).2 hlt
  obtain ⟨v, hv⟩ := hP1 hA
  have hvl : v ∈ Above k l := (hP3 v hv).1 hlt
  obtain ⟨-, hidx, -⟩ := ineOpen k Ω l v A hvl hv
  obtain ⟨u, hu⟩ := exists_unit_not_finOrder l
  have hmem : u ^ (ineImage k l A).index ∈ ineImage k l A := Subgroup.pow_index_mem _ u
  obtain ⟨g, hg, hgu⟩ := Subgroup.mem_map.1 hmem
  haveI : Finite (G k Ω ⧸ U) := Subgroup.quotient_finite_of_isOpen U hU
  haveI : U.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  haveI := Subgroup.finiteIndex_normalCore U
  haveI := Subgroup.normalCore_normal U
  have hN : U.normalCore.index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
  have hgU : g ^ U.normalCore.index ∈ U := U.normalCore_le (Subgroup.pow_index_mem _ g)
  refine ⟨g ^ U.normalCore.index, ⟨hgU, Subgroup.pow_mem (Dec (F := k) A) hg.1 _⟩, ?_⟩
  rw [map_pow, hgu, ← pow_mul, isOfFinOrder_pow]
  rintro (h | h)
  · exact hu h
  · exact mul_ne_zero hidx hN h

end ContTwAndDecInf

section PadicUnitsLogAndPrincZl

section PadicUnitsLog

variable (ℓ : ℕ) [hℓ : Fact ℓ.Prime]

private def unitsLevel : ℕ := if ℓ = 2 then 3 else 1
private def torsionExponent : ℕ := if ℓ = 2 then 2 else ℓ - 1

private theorem unitsLevel_ne_zero : unitsLevel ℓ ≠ 0 := by unfold unitsLevel; split_ifs <;> norm_num

private theorem unitsLevel_add_two_le : unitsLevel ℓ + 2 ≤ ℓ * unitsLevel ℓ := by
  unfold unitsLevel; split_ifs with h
  · subst h; norm_num
  · have := hℓ.out.two_le; omega

private theorem torsionExponent_pos : 0 < torsionExponent ℓ := by
  unfold torsionExponent; split_ifs
  · norm_num
  · have := hℓ.out.two_le; omega

private theorem pow_torsionExponent (x : (ZMod (ℓ ^ unitsLevel ℓ))ˣ) :
    x ^ torsionExponent ℓ = 1 := by
  by_cases h : ℓ = 2
  · subst h
    have key : ∀ y : ZMod 8, (∃ z : ZMod 8, y * z = 1) → y ^ 2 = 1 := by decide
    have h8 : (2 : ℕ) ^ unitsLevel 2 = 8 := by simp [unitsLevel]
    rw [torsionExponent, if_pos rfl]
    refine Units.ext ?_
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    revert x; rw [h8]; intro x; exact key _ ⟨_, x.mul_inv⟩
  · have : NeZero ℓ := ⟨hℓ.out.ne_zero⟩
    have hc : Fintype.card (ZMod (ℓ ^ unitsLevel ℓ))ˣ = ℓ - 1 := by
      rw [ZMod.card_units_eq_totient, unitsLevel, if_neg h, pow_one, Nat.totient_prime hℓ.out]
    rw [torsionExponent, if_neg h, ← hc, pow_card_eq_one]

private def unitsKer (n : ℕ) : Subgroup (ZMod (ℓ ^ (n + unitsLevel ℓ)))ˣ :=
  (ZMod.unitsMap (pow_dvd_pow ℓ (Nat.le_add_left (unitsLevel ℓ) n))).ker

private theorem card_unitsKer (n : ℕ) : Nat.card (unitsKer ℓ n) = ℓ ^ n := by
  have : NeZero ℓ := ⟨hℓ.out.ne_zero⟩
  have h1 := Subgroup.card_mul_index (unitsKer ℓ n)
  rw [unitsKer, Subgroup.index_ker, MonoidHom.range_eq_top.2 (ZMod.unitsMap_surjective _),
    Subgroup.card_top, Nat.card_eq_fintype_card (α := (ZMod (ℓ ^ unitsLevel ℓ))ˣ),
    Nat.card_eq_fintype_card (α := (ZMod (ℓ ^ (n + unitsLevel ℓ)))ˣ), ZMod.card_units_eq_totient,
    ZMod.card_units_eq_totient, Nat.totient_prime_pow hℓ.out (Nat.pos_of_ne_zero (unitsLevel_ne_zero ℓ)),
    Nat.totient_prime_pow hℓ.out (by have := unitsLevel_ne_zero ℓ; omega)] at h1
  have hr : n + unitsLevel ℓ - 1 = n + (unitsLevel ℓ - 1) := by have := unitsLevel_ne_zero ℓ; omega
  have hpos : 0 < ℓ ^ (unitsLevel ℓ - 1) * (ℓ - 1) :=
    Nat.mul_pos (pow_pos hℓ.out.pos _) (by have := hℓ.out.two_le; omega)
  have h2 : Nat.card (unitsKer ℓ n) * (ℓ ^ (unitsLevel ℓ - 1) * (ℓ - 1)) =
      ℓ ^ n * (ℓ ^ (unitsLevel ℓ - 1) * (ℓ - 1)) := by
    rw [← mul_assoc (ℓ ^ n), ← pow_add, ← hr]; exact h1
  exact Nat.eq_of_mul_eq_mul_right hpos h2

private theorem coprime_one_add_pow (k : ℕ) : Nat.Coprime (1 + ℓ ^ unitsLevel ℓ) (ℓ ^ k) := by
  refine Nat.Coprime.pow_right _ ?_
  rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hℓ.out]
  intro h; rw [add_comm] at h
  exact hℓ.out.not_dvd_one ((Nat.dvd_add_right (dvd_pow_self ℓ (unitsLevel_ne_zero ℓ))).1 h)

private def genUnit (n : ℕ) : (ZMod (ℓ ^ (n + unitsLevel ℓ)))ˣ :=
  ZMod.unitOfCoprime (1 + ℓ ^ unitsLevel ℓ) (coprime_one_add_pow ℓ _)

private theorem coe_genUnit (n : ℕ) :
    (genUnit ℓ n : ZMod (ℓ ^ (n + unitsLevel ℓ))) = 1 + (ℓ : ZMod _) ^ unitsLevel ℓ := by
  simp [genUnit]

private theorem orderOf_genUnit (n : ℕ) : orderOf (genUnit ℓ n) = ℓ ^ n := by
  rw [← orderOf_units, coe_genUnit]
  simpa using ZMod.orderOf_one_add_mul_prime_pow hℓ.out (unitsLevel ℓ) (unitsLevel_ne_zero ℓ)
    (unitsLevel_add_two_le ℓ) 1 (by norm_cast; exact hℓ.out.not_dvd_one) n

private theorem genUnit_pow_eq_one (n : ℕ) : genUnit ℓ n ^ (ℓ ^ n) = 1 := by
  have := pow_orderOf_eq_one (genUnit ℓ n); rwa [orderOf_genUnit] at this

private theorem zpowers_genUnit (n : ℕ) : Subgroup.zpowers (genUnit ℓ n) = unitsKer ℓ n := by
  refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 ?_)
    (by rw [card_unitsKer, Nat.card_zpowers, orderOf_genUnit])
  rw [unitsKer, MonoidHom.mem_ker]
  refine Units.ext ?_
  simp only [ZMod.unitsMap_def, Units.coe_map, MonoidHom.coe_coe, coe_genUnit, map_add, map_one,
    map_pow, map_natCast, Units.val_one]
  rw [← Nat.cast_pow, ZMod.natCast_self, add_zero]

private theorem genUnit_pow_val_eq (n : ℕ) {a b : ℕ} (h : a ≡ b [MOD ℓ ^ n]) :
    genUnit ℓ n ^ a = genUnit ℓ n ^ b := by
  rw [pow_eq_pow_iff_modEq, orderOf_genUnit]; exact h

private def expHom (n : ℕ) : Multiplicative (ZMod (ℓ ^ n)) →* (ZMod (ℓ ^ (n + unitsLevel ℓ)))ˣ where
  toFun a := genUnit ℓ n ^ (Multiplicative.toAdd a).val
  map_one' := by simp
  map_mul' a b := by
    have : NeZero ℓ := ⟨hℓ.out.ne_zero⟩
    rw [← pow_add, toAdd_mul]
    exact genUnit_pow_val_eq ℓ n (by rw [ZMod.val_add]; exact Nat.mod_modEq _ _)

private theorem expHom_injective (n : ℕ) : Function.Injective (expHom ℓ n) := by
  have : NeZero ℓ := ⟨hℓ.out.ne_zero⟩
  refine (injective_iff_map_eq_one _).2 fun a ha => ?_
  have h1 : ℓ ^ n ∣ (Multiplicative.toAdd a).val := by
    have := orderOf_dvd_of_pow_eq_one ha; rwa [orderOf_genUnit] at this
  have h2 := Nat.eq_zero_of_dvd_of_lt h1 (ZMod.val_lt _)
  rwa [ZMod.val_eq_zero] at h2

private def expEquiv (n : ℕ) : Multiplicative (ZMod (ℓ ^ n)) ≃* unitsKer ℓ n :=
  (MonoidHom.ofInjective (expHom_injective ℓ n)).trans (MulEquiv.subgroupCongr (by
    apply Subgroup.eq_of_le_of_card_ge
    · rintro _ ⟨a, rfl⟩; rw [← zpowers_genUnit]; exact Subgroup.npow_mem_zpowers _ _
    · rw [card_unitsKer, ← Nat.card_congr (MonoidHom.ofInjective (expHom_injective ℓ n)).toEquiv]
      exact (Nat.card_zmod _).ge))

private def powKer (n : ℕ) : (ZMod (ℓ ^ (n + unitsLevel ℓ)))ˣ →* unitsKer ℓ n :=
  (powMonoidHom (torsionExponent ℓ)).codRestrict (unitsKer ℓ n) fun x => by
    rw [unitsKer, MonoidHom.mem_ker, powMonoidHom_apply, map_pow, pow_torsionExponent]

private def logMod (n : ℕ) : (ZMod (ℓ ^ (n + unitsLevel ℓ)))ˣ →* Multiplicative (ZMod (ℓ ^ n)) :=
  (expEquiv ℓ n).symm.toMonoidHom.comp (powKer ℓ n)

private theorem expHom_logMod (n : ℕ) (x : (ZMod (ℓ ^ (n + unitsLevel ℓ)))ˣ) :
    expHom ℓ n (logMod ℓ n x) = x ^ torsionExponent ℓ :=
  congrArg Subtype.val ((expEquiv ℓ n).apply_symm_apply (powKer ℓ n x))

private theorem logMod_eq_iff (n : ℕ) (x : (ZMod (ℓ ^ (n + unitsLevel ℓ)))ˣ)
    (a : Multiplicative (ZMod (ℓ ^ n))) :
    logMod ℓ n x = a ↔ expHom ℓ n a = x ^ torsionExponent ℓ :=
  ⟨fun h => h ▸ expHom_logMod ℓ n x, fun h => expHom_injective ℓ n (by rw [expHom_logMod, h])⟩

private theorem castHom_logMod {m n : ℕ} (h : m ≤ n) (x : (ZMod (ℓ ^ (n + unitsLevel ℓ)))ˣ) :
    ZMod.castHom (pow_dvd_pow ℓ h) (ZMod (ℓ ^ m)) (Multiplicative.toAdd (logMod ℓ n x)) =
      Multiplicative.toAdd (logMod ℓ m
        (ZMod.unitsMap (pow_dvd_pow ℓ (by omega : m + unitsLevel ℓ ≤ n + unitsLevel ℓ)) x)) := by
  have : NeZero ℓ := ⟨hℓ.out.ne_zero⟩
  set a := Multiplicative.toAdd (logMod ℓ n x)
  have key : logMod ℓ m
      (ZMod.unitsMap (pow_dvd_pow ℓ (by omega : m + unitsLevel ℓ ≤ n + unitsLevel ℓ)) x) =
        Multiplicative.ofAdd (ZMod.castHom (pow_dvd_pow ℓ h) (ZMod (ℓ ^ m)) a) := by
    rw [logMod_eq_iff, ← map_pow, ← expHom_logMod ℓ n x]
    change genUnit ℓ m ^ _ = _
    rw [show ∀ b, expHom ℓ n b = genUnit ℓ n ^ (Multiplicative.toAdd b).val from fun _ => rfl, map_pow]
    have hum : ZMod.unitsMap (pow_dvd_pow ℓ (by omega : m + unitsLevel ℓ ≤ n + unitsLevel ℓ))
        (genUnit ℓ n) = genUnit ℓ m := Units.ext (by
      simp only [ZMod.unitsMap_def, Units.coe_map, MonoidHom.coe_coe, coe_genUnit, map_add,
        map_one, map_pow, map_natCast])
    rw [hum]
    refine genUnit_pow_val_eq ℓ m ?_
    rw [toAdd_ofAdd, ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.val_natCast]
    exact Nat.mod_modEq _ _
  rw [key, toAdd_ofAdd]

private def compatibleFamilies : Subring (∀ n : ℕ, ZMod (ℓ ^ n)) :=
  ⨅ (m : ℕ) (n : ℕ) (h : m ≤ n), RingHom.eqLocus
    ((ZMod.castHom (pow_dvd_pow ℓ h) (ZMod (ℓ ^ m))).comp
      (Pi.evalRingHom (fun k => ZMod (ℓ ^ k)) n)) (Pi.evalRingHom (fun k => ZMod (ℓ ^ k)) m)

private theorem mem_compatibleFamilies {x : ∀ n : ℕ, ZMod (ℓ ^ n)} :
    x ∈ compatibleFamilies ℓ ↔
      ∀ (m n : ℕ) (h : m ≤ n), ZMod.castHom (pow_dvd_pow ℓ h) (ZMod (ℓ ^ m)) (x n) = x m := by
  simp [compatibleFamilies, Subring.mem_iInf, RingHom.mem_eqLocus]

private def limFamilies : compatibleFamilies ℓ →+* ℤ_[ℓ] :=
  PadicInt.lift (f := fun n => (Pi.evalRingHom (fun k => ZMod (ℓ ^ k)) n).comp
    (compatibleFamilies ℓ).subtype) fun m n h => by
      ext x
      exact (mem_compatibleFamilies ℓ).1 x.2 m n h

private theorem toZModPow_limFamilies (x : compatibleFamilies ℓ) (n : ℕ) :
    PadicInt.toZModPow n (limFamilies ℓ x) = (x : ∀ n : ℕ, ZMod (ℓ ^ n)) n :=
  RingHom.congr_fun (PadicInt.lift_spec _ n) x

private theorem logFamily_mem (u : ℤ_[ℓ]ˣ) :
    (fun n => Multiplicative.toAdd (logMod ℓ n (redPow ℓ (n + unitsLevel ℓ) u))) ∈
      compatibleFamilies ℓ := by
  rw [mem_compatibleFamilies]
  intro m n h
  rw [castHom_logMod ℓ h]
  have hmap : ZMod.unitsMap (pow_dvd_pow ℓ (by omega : m + unitsLevel ℓ ≤ n + unitsLevel ℓ))
      (redPow ℓ (n + unitsLevel ℓ) u) = redPow ℓ (m + unitsLevel ℓ) u := Units.ext (by
    simp only [ZMod.unitsMap_def, Units.coe_map, MonoidHom.coe_coe, redPow, ZMod.castHom_apply]
    exact PadicInt.cast_toZModPow _ _ (by omega) _)
  rw [hmap]

private def padicUnitsLog : ℤ_[ℓ]ˣ →* Multiplicative ℤ_[ℓ] where
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

private theorem toZModPow_padicUnitsLog (u : ℤ_[ℓ]ˣ) (n : ℕ) :
    PadicInt.toZModPow n (Multiplicative.toAdd (padicUnitsLog ℓ u)) =
      Multiplicative.toAdd (logMod ℓ n (redPow ℓ (n + unitsLevel ℓ) u)) :=
  toZModPow_limFamilies ℓ _ n

private theorem continuous_padicUnitsLog : Continuous (padicUnitsLog ℓ) := by
  refine continuous_ofAdd.comp (continuous_iff_continuousAt.2 fun u => Metric.tendsto_nhds.2 fun ε hε => ?_)
  have h1 : (1 : ℝ) < ℓ := by exact_mod_cast hℓ.out.one_lt
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε (inv_lt_one_of_one_lt₀ h1)
  have hpos : (0 : ℝ) < (ℓ : ℝ) ^ (-(n + unitsLevel ℓ : ℕ) : ℤ) :=
    zpow_pos (by exact_mod_cast hℓ.out.pos) _
  let U : Set ℤ_[ℓ]ˣ := Units.val ⁻¹' Metric.closedBall (u : ℤ_[ℓ]) ((ℓ : ℝ) ^ (-(n + unitsLevel ℓ : ℕ) : ℤ))
  have hUo : IsOpen U := (IsUltrametricDist.isOpen_closedBall _ hpos.ne').preimage Units.continuous_val
  filter_upwards [hUo.mem_nhds (Metric.mem_closedBall_self hpos.le)] with v hv
  have hsub : PadicInt.toZModPow (n + unitsLevel ℓ) (v : ℤ_[ℓ]) =
      PadicInt.toZModPow (n + unitsLevel ℓ) (u : ℤ_[ℓ]) := by
    rw [← sub_eq_zero, ← map_sub, ← RingHom.mem_ker, PadicInt.ker_toZModPow,
      ← PadicInt.norm_le_pow_iff_mem_span_pow, ← dist_eq_norm]
    exact hv
  have hred : redPow ℓ (n + unitsLevel ℓ) v = redPow ℓ (n + unitsLevel ℓ) u := Units.ext hsub
  have hvlog : PadicInt.toZModPow n (Multiplicative.toAdd (padicUnitsLog ℓ v)) =
      PadicInt.toZModPow n (Multiplicative.toAdd (padicUnitsLog ℓ u)) := by
    rw [toZModPow_padicUnitsLog, toZModPow_padicUnitsLog, hred]
  have hnorm : ‖Multiplicative.toAdd (padicUnitsLog ℓ v) - Multiplicative.toAdd (padicUnitsLog ℓ u)‖ ≤
      (ℓ : ℝ) ^ (-n : ℤ) := by
    rw [PadicInt.norm_le_pow_iff_mem_span_pow, ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, hvlog, sub_self]
  rw [dist_eq_norm]
  refine lt_of_le_of_lt hnorm ?_
  rw [zpow_neg, zpow_natCast, ← inv_pow]; exact hn

private theorem padicUnitsLog_eq_one_of_pow_eq_one {u : ℤ_[ℓ]ˣ} {k : ℕ} (hk : 0 < k)
    (h : u ^ k = 1) : padicUnitsLog ℓ u = 1 := by
  have h1 := congrArg (fun v => Multiplicative.toAdd (padicUnitsLog ℓ v)) h
  simp only [map_pow, toAdd_pow, map_one, toAdd_one, nsmul_eq_mul] at h1
  rcases mul_eq_zero.1 h1 with h2 | h2
  · exact absurd h2 (Nat.cast_ne_zero.2 hk.ne')
  · exact congrArg Multiplicative.ofAdd h2

private theorem ker_padicUnitsLog : (padicUnitsLog ℓ).ker = CommGroup.torsion ℤ_[ℓ]ˣ := by
  ext u
  rw [MonoidHom.mem_ker, CommGroup.mem_torsion, isOfFinOrder_iff_pow_eq_one]
  refine ⟨fun h => ⟨_, torsionExponent_pos ℓ, ?_⟩, fun ⟨_, hk, h⟩ => padicUnitsLog_eq_one_of_pow_eq_one ℓ hk h⟩
  have hk : ∀ k, PadicInt.toZModPow (k + unitsLevel ℓ) ((u ^ torsionExponent ℓ : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) = 1 :=
    fun k => by
      have h1 := toZModPow_padicUnitsLog ℓ u k
      rw [h, toAdd_one, map_zero] at h1
      have h2 : logMod ℓ k (redPow ℓ (k + unitsLevel ℓ) u) = 1 := congrArg Multiplicative.ofAdd h1.symm
      rw [logMod_eq_iff, map_one] at h2
      have h3 := congrArg Units.val h2
      rw [Units.val_one, Units.val_pow_eq_pow_val] at h3
      simpa [redPow, Units.val_pow_eq_pow_val, ← map_pow] using h3.symm
  refine Units.ext (PadicInt.ext_of_toZModPow.mp fun k => ?_)
  rw [← PadicInt.zmod_cast_comp_toZModPow k (k + unitsLevel ℓ) (Nat.le_add_right _ _),
    RingHom.comp_apply, RingHom.comp_apply, hk]
  simp

private theorem padicUnitsLog_eq_one_iff (u : ℤ_[ℓ]ˣ) :
    padicUnitsLog ℓ u = 1 ↔ u ^ torsionExponent ℓ = 1 := by
  refine ⟨fun h => ?_, padicUnitsLog_eq_one_of_pow_eq_one ℓ (torsionExponent_pos ℓ)⟩
  have hk : ∀ k, PadicInt.toZModPow (k + unitsLevel ℓ) ((u ^ torsionExponent ℓ : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) = 1 :=
    fun k => by
      have h1 := toZModPow_padicUnitsLog ℓ u k
      rw [h, toAdd_one, map_zero] at h1
      have h2 : logMod ℓ k (redPow ℓ (k + unitsLevel ℓ) u) = 1 := congrArg Multiplicative.ofAdd h1.symm
      rw [logMod_eq_iff, map_one] at h2
      have h3 := congrArg Units.val h2
      rw [Units.val_one, Units.val_pow_eq_pow_val] at h3
      simpa [redPow, Units.val_pow_eq_pow_val, ← map_pow] using h3.symm
  refine Units.ext (PadicInt.ext_of_toZModPow.mp fun k => ?_)
  rw [← PadicInt.zmod_cast_comp_toZModPow k (k + unitsLevel ℓ) (Nat.le_add_right _ _),
    RingHom.comp_apply, RingHom.comp_apply, hk]
  simp

private theorem mem_torsion_iff (u : ℤ_[ℓ]ˣ) :
    u ∈ CommGroup.torsion ℤ_[ℓ]ˣ ↔ u ^ torsionExponent ℓ = 1 := by
  rw [← ker_padicUnitsLog, MonoidHom.mem_ker, padicUnitsLog_eq_one_iff]

private theorem eq_one_of_mem_princ_one {o : ℕ} (ho : ¬ ℓ ∣ o) {ζ : ℤ_[ℓ]ˣ}
    (hζ : ζ ∈ rootsOfUnity o ℤ_[ℓ]) (h1 : ζ ∈ princ ℓ 1) : ζ = 1 := by
  have ht1 : PadicInt.toZMod (ζ : ℤ_[ℓ]) = 1 := by
    have hd := mem_princ.mp h1
    rw [pow_one] at hd
    rw [← sub_eq_zero, ← map_one (PadicInt.toZMod (p := ℓ)), ← map_sub, ← RingHom.mem_ker,
      PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p]
    exact Ideal.mem_span_singleton.mpr hd
  rw [mem_rootsOfUnity'] at hζ
  have h := mul_geom_sum (ζ : ℤ_[ℓ]) o
  rw [hζ, sub_self, mul_eq_zero] at h
  rcases h with h | h
  · exact Units.ext (by simpa [sub_eq_zero] using h)
  · exfalso
    have := congrArg PadicInt.toZMod h
    rw [map_sum, map_zero] at this
    simp only [map_pow, ht1, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at this
    exact ho ((ZMod.natCast_eq_zero_iff o ℓ).1 this)

end PadicUnitsLog

theorem princZl :
    ∀ (l : ℕ) [Fact l.Prime] (H : Subgroup ℤ_[l]ˣ), IsClosed (H : Set ℤ_[l]ˣ) →
      H ≤ princ l (qExp l) → H ≠ ⊥ →
      Nonempty (H ≃ₜ* Multiplicative ℤ_[l]) ∧ ∀ u ∈ H, IsOfFinOrder u → u = 1 := by
  intro l _ H hHc hHp hH1
  have tors : ∀ u ∈ H, IsOfFinOrder u → u = 1 := fun u hu hfin => by
    have hpr := hHp hu
    have hmem : u ∈ CommGroup.torsion ℤ_[l]ˣ := (CommGroup.mem_torsion u).2 hfin
    by_cases h2 : l = 2
    · subst h2
      have ht := (mem_torsion_iff 2 u).1 hmem
      have hsq : (u : ℤ_[2]) * (u : ℤ_[2]) = 1 := by
        have := congrArg Units.val ht
        simpa [torsionExponent, sq] using this
      rcases mul_self_eq_one_iff.1 hsq with h | h
      · exact Units.ext h
      · exfalso
        rw [mem_princ, qExp, if_pos rfl] at hpr
        obtain ⟨c, hc⟩ := hpr
        rw [h] at hc
        have hc2 : (2 : ℤ_[2]) * (1 + 2 * c) = 0 := by push_cast at hc; linear_combination -hc
        have h1 : (1 : ℤ_[2]) + 2 * c = 0 := (mul_eq_zero.1 hc2).resolve_left two_ne_zero
        have hn : ‖(2 : ℤ_[2]) * c‖ = 1 := by
          rw [show (2 : ℤ_[2]) * c = -1 by linear_combination h1, norm_neg, norm_one]
        have hn2 : ‖(2 : ℤ_[2])‖ = 1 / 2 := by
          have := PadicInt.norm_p (p := 2); norm_num at this ⊢; exact this
        rw [norm_mul, hn2] at hn
        have := PadicInt.norm_le_one c
        linarith
    · have ht : u ^ torsionExponent l = 1 := (mem_torsion_iff l u).1 hmem
      rw [show qExp l = 1 by simp [qExp, h2]] at hpr
      rw [show torsionExponent l = l - 1 by simp [torsionExponent, h2]] at ht
      have hl := (Fact.out : l.Prime).two_le
      refine eq_one_of_mem_princ_one l (o := l - 1) (fun hd => by
        have := Nat.le_of_dvd (by omega) hd; omega) ((mem_rootsOfUnity _ _).2 ht) hpr
  refine ⟨?_, tors⟩
  classical
  let L : ℤ_[l]ˣ →* Multiplicative ℤ_[l] := padicUnitsLog l
  have hker : L.ker = CommGroup.torsion ℤ_[l]ˣ := ker_padicUnitsLog l
  let f : H → ℤ_[l] := fun h => Multiplicative.toAdd (L h)
  have hfc : Continuous f := (continuous_padicUnitsLog l).comp continuous_subtype_val
  have hmul : ∀ a b : H, f (a * b) = f a + f b := fun a b => by simp [f, L]
  have hpow : ∀ (a : H) (n : ℤ), f (a ^ n) = n * f a := fun a n => by simp [f, L, zsmul_eq_mul]
  have hf1 : f 1 = 0 := by simp [f, L]
  have hinj : Function.Injective f := fun a b hab => by
    have hk : (a : ℤ_[l]ˣ) * (b : ℤ_[l]ˣ)⁻¹ ∈ L.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, show L a = L b from hab, mul_inv_cancel]
    rw [hker, CommGroup.mem_torsion] at hk
    exact Subtype.ext (mul_inv_eq_one.1 (tors _ (H.mul_mem a.2 (H.inv_mem b.2)) hk))
  haveI : CompactSpace H := isCompact_iff_compactSpace.1 hHc.isCompact
  have hcl : IsClosed (Set.range f) := (isCompact_range hfc).isClosed
  let I : Ideal ℤ_[l] :=
    { carrier := Set.range f
      add_mem' := fun {_ _} ⟨a, ha⟩ ⟨b, hb⟩ => ⟨a * b, by rw [hmul, ha, hb]⟩
      zero_mem' := ⟨1, hf1⟩
      smul_mem' := fun c {_} ⟨a, ha⟩ => by
        rw [← ha]
        have hm : Continuous (fun t : ℤ_[l] => t * f a) := continuous_mul_const (f a)
        have hsub := hm.range_subset_closure_image_dense (PadicInt.denseRange_intCast (p := l))
        exact closure_minimal (by rintro _ ⟨_, ⟨n, rfl⟩, rfl⟩; exact ⟨a ^ n, hpow a n⟩) hcl (hsub ⟨c, rfl⟩) }
  have hI : ∀ y, y ∈ Set.range f ↔ ∃ c, c * Submodule.IsPrincipal.generator I = y := fun y => by
    have h : y ∈ I ↔ y ∈ Ideal.span {Submodule.IsPrincipal.generator I} := by
      rw [Ideal.span_singleton_generator]
    rwa [Ideal.mem_span_singleton'] at h
  set g := Submodule.IsPrincipal.generator I
  obtain ⟨a0, ha0⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hH1
  have hg0 : g ≠ 0 := fun hg => by
    obtain ⟨c, hc⟩ := (hI (f a0)).1 ⟨a0, rfl⟩
    rw [hg, mul_zero, ← hf1] at hc
    exact ha0 (hinj hc).symm
  let e : H → ℤ_[l] := fun h => Classical.choose ((hI (f h)).1 ⟨h, rfl⟩)
  have he : ∀ h, e h * g = f h := fun h => Classical.choose_spec ((hI (f h)).1 ⟨h, rfl⟩)
  have hminj : Function.Injective (fun t : ℤ_[l] => t * g) := mul_left_injective₀ hg0
  have hec : Continuous e := by
    rw [((continuous_mul_const g).isClosedEmbedding hminj).isEmbedding.continuous_iff]
    rw [show ((fun t : ℤ_[l] => t * g) ∘ e) = f from funext he]
    exact hfc
  have hemul : ∀ a b : H, e (a * b) = e a + e b := fun a b =>
    hminj (by dsimp only; rw [he, add_mul, he, he, hmul])
  let φ : H →* Multiplicative ℤ_[l] := MonoidHom.mk' (fun h => Multiplicative.ofAdd (e h)) fun a b => by
    rw [hemul]; rfl
  let E : H ≃* Multiplicative ℤ_[l] := MulEquiv.ofBijective φ
    ⟨fun a b hab => hinj (by rw [← he a, ← he b]; exact congrArg (· * g) (Multiplicative.ofAdd.injective hab)),
     fun c => by
       obtain ⟨h, hh⟩ := (hI (Multiplicative.toAdd c * g)).2 ⟨Multiplicative.toAdd c, rfl⟩
       exact ⟨h, Multiplicative.toAdd.injective (hminj (by show Multiplicative.toAdd (φ h) * g = Multiplicative.toAdd c * g; rw [show Multiplicative.toAdd (φ h) = e h from rfl, he h, hh]))⟩⟩
  let E0 : H ≃ ℤ_[l] := E.toEquiv.trans Multiplicative.toAdd
  let Φ := Continuous.homeoOfEquivCompactToT2 (f := E0) hec
  exact ⟨{ toMulEquiv := E, continuous_toFun := hec, continuous_invFun := Φ.symm.continuous }⟩

theorem gammaGen :
    ∀ (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
      (l : ℕ) [Fact l.Prime] (U : Subgroup (G k Ω)), IsClosed (U : Set (G k Ω)) →
      U ≤ gamU l ⊤ → ¬ U ≤ (cycZ k Ω l).ker →
      ∃ (κ : U →* Multiplicative ℤ_[l]) (γ : U), Continuous κ ∧ Function.Surjective κ ∧
        κ.ker = (cycU l U).subgroupOf U ∧ κ γ = Multiplicative.ofAdd 1 ∧
        U ≤ (Subgroup.zpowers γ.1 ⊔ cycU l U).topologicalClosure ∧
        ¬ IsOfFinOrder (cycZ k Ω l γ.1) := by
  intro k Ω _ _ _ _ _ l _ U hUc hUg hUk
  have hχc : Continuous (cycZ k Ω l) := continuous_cycZ k Ω l
  have hHc : IsClosed ((U.map (cycZ k Ω l) : Subgroup ℤ_[l]ˣ) : Set ℤ_[l]ˣ) := by
    rw [Subgroup.coe_map]
    exact (hUc.isCompact.image hχc).isClosed
  have hHp : U.map (cycZ k Ω l) ≤ princ l (qExp l) := by
    rintro _ ⟨u, hu, rfl⟩
    exact (hUg hu).2
  have hHb : U.map (cycZ k Ω l) ≠ ⊥ := fun h => hUk fun u hu => by
    have hm : cycZ k Ω l u ∈ U.map (cycZ k Ω l) := ⟨u, hu, rfl⟩
    rw [h] at hm
    exact MonoidHom.mem_ker.mpr (Subgroup.mem_bot.mp hm)
  obtain ⟨⟨e⟩, htor⟩ := princZl l _ hHc hHp hHb
  let ψ : U →* U.map (cycZ k Ω l) := (cycZ k Ω l).subgroupMap U
  have hψc : Continuous ψ := Continuous.subtype_mk (hχc.comp continuous_subtype_val) _
  let κ : U →* Multiplicative ℤ_[l] := e.toMulEquiv.toMonoidHom.comp ψ
  have hκc : Continuous κ := e.continuous.comp hψc
  have hκs : Function.Surjective κ := e.surjective.comp (MonoidHom.subgroupMap_surjective _ U)
  have hkκ : ∀ x : U, κ x = 1 ↔ cycZ k Ω l x = 1 := fun x => by
    change e (ψ x) = 1 ↔ _
    rw [map_eq_one_iff e e.injective, Subtype.ext_iff]
    exact Iff.rfl
  obtain ⟨γ, hγ⟩ := hκs (Multiplicative.ofAdd 1)
  refine ⟨κ, γ, hκc, hκs, ?_, hγ, ?_, fun hfin => ?_⟩
  · ext x
    rw [MonoidHom.mem_ker, hkκ, Subgroup.mem_subgroupOf]
    simp only [cycU, Subgroup.mem_inf, MonoidHom.mem_ker]
    exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩
  · set V := (Subgroup.zpowers γ.1 ⊔ cycU l U).topologicalClosure
    have hVc : IsClosed (V : Set (G k Ω)) := Subgroup.isClosed_topologicalClosure _
    have hsub : Subgroup.zpowers γ.1 ⊔ cycU l U ≤ V := Subgroup.le_topologicalClosure _
    have hcU : CompactSpace U := isCompact_iff_compactSpace.mp hUc.isCompact
    let S : Set U := Subtype.val ⁻¹' (V : Set (G k Ω))
    have hIc : IsClosed (κ '' S) := ((hVc.preimage continuous_subtype_val).isCompact.image hκc).isClosed
    let T : Set ℤ_[l] := fun a => Multiplicative.ofAdd a ∈ κ '' S
    have hT : T = Set.univ := Set.eq_univ_of_univ_subset <| by
      rw [← PadicInt.denseRange_intCast.closure_range]
      refine closure_minimal ?_ (hIc.preimage continuous_ofAdd)
      rintro _ ⟨n, rfl⟩
      refine ⟨γ ^ n, ?_, ?_⟩
      · show ((γ ^ n : U) : G k Ω) ∈ V
        rw [Subgroup.coe_zpow]
        exact hsub (Subgroup.mem_sup_left (Subgroup.zpow_mem_zpowers _ n))
      · rw [map_zpow, hγ, ← ofAdd_zsmul, zsmul_one]
    intro u hu
    have ha : Multiplicative.toAdd (κ ⟨u, hu⟩) ∈ T := by rw [hT]; trivial
    obtain ⟨s, hs, hks⟩ := ha
    have hq' := (hkκ _).mp (show κ (⟨u, hu⟩ * s⁻¹) = 1 by
      rw [map_mul, map_inv, hks, ofAdd_toAdd, mul_inv_cancel])
    have hmem : ((⟨u, hu⟩ * s⁻¹ : U) : G k Ω) ∈ V :=
      hsub (Subgroup.mem_sup_right ⟨(⟨u, hu⟩ * s⁻¹ : U).2, hq'⟩)
    rw [show u = ((⟨u, hu⟩ * s⁻¹ : U) : G k Ω) * (s : G k Ω) by simp]
    exact V.mul_mem hmem hs
  · have h1 := (hkκ γ).mpr (htor _ ⟨γ.1, γ.2, rfl⟩ hfin)
    rw [hγ] at h1
    exact one_ne_zero (ofAdd_eq_one.mp h1)

end PadicUnitsLogAndPrincZl

end DvrAndCyclotomicUnits

/-! ## Section 4: Equivariant Transport, `shaModel`, `shaLenEq`, and `shaDecompSign` -/

section TransportShaModelAndSign

private theorem exists_continuous_mulEquiv_of_map_embedding {G G' : Type} [Group G] [Group G']
    [TopologicalSpace G] [TopologicalSpace G'] (φ : G' →* G) (hφ : Topology.IsEmbedding φ)
    (U' : Subgroup G') (U : Subgroup G) (h : U'.map φ = U) :
    ∃ e : U' ≃* U, (∀ u' : U', ((e u' : U) : G) = φ u') ∧ Continuous e ∧ Continuous e.symm := by
  have hmem : ∀ u' : U', φ u' ∈ U := fun u' => h ▸ Subgroup.mem_map_of_mem φ u'.2
  let f : U' →* U :=
    { toFun := fun u' => ⟨φ u', hmem u'⟩
      map_one' := by ext; simp
      map_mul' := fun _ _ => by ext; simp }
  let e : U' ≃* U := MulEquiv.ofBijective f
    ⟨fun _ _ hab => Subtype.ext (hφ.injective (congrArg Subtype.val hab)),
     fun ⟨_, hg⟩ => by
       obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp (h.symm ▸ hg)
       exact ⟨⟨x, hx⟩, rfl⟩⟩
  refine ⟨e, fun _ => rfl, (hφ.continuous.comp continuous_subtype_val).subtype_mk _, ?_⟩
  rw [Topology.IsEmbedding.subtypeVal.isInducing.continuous_iff, hφ.isInducing.continuous_iff]
  have hc : (⇑φ ∘ Subtype.val ∘ ⇑e.symm) = (Subtype.val : U → G) := funext fun u =>
    congrArg Subtype.val (e.apply_symm_apply u)
  rw [hc]
  exact continuous_subtype_val

theorem selTransport :
    ∀ (R G M : Type) [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
      [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M]
      [ContinuousConstSMul R M] [DiscreteTopology M] (ρ : Representation R G M) (G' : Type)
      [Group G'] [TopologicalSpace G'] (φ : G' →* G), Topology.IsEmbedding φ →
      ∀ (U' : Subgroup G') (U : Subgroup G), U'.map φ = U → ∀ 𝒟 : Set (Subgroup G),
      ∃ Φ : LocSel (ρ.comp φ : Representation R G' M) U' (Subgroup.comap φ '' 𝒟) ≃ₗ[R]
        LocSel ρ U 𝒟,
        ∀ (z' : Z1U (ρ.comp φ : Representation R G' M) U') (z : Z1U ρ U) hz',
          (∀ (u' : U') (u : U), φ u' = u → z.1 u = z'.1 u') →
          (Φ ⟨Submodule.Quotient.mk z', hz'⟩ : H1U ρ U) = Submodule.Quotient.mk z := by
  intro R G M _ _ _ _ _ _ _ _ _ _ ρ G' _ _ φ hφ U' U hU 𝒟
  obtain ⟨e, he, hec, hesc⟩ := exists_continuous_mulEquiv_of_map_embedding φ hφ U' U hU
  have key : ∀ g : U, φ ((e.symm g : U') : G') = g := fun g => by rw [← he, e.apply_symm_apply]
  let A : Representation R U' M := (ρ.comp φ).comp U'.subtype
  let B : Representation R U M := ρ.comp U.subtype
  let F : H1 B →ₗ[R] H1 A := pairH1 B A e.toMonoidHom hec LinearMap.id continuous_id fun g m => by
    simp only [A, B, LinearMap.id_apply, MonoidHom.comp_apply, Subgroup.coe_subtype,
      MulEquiv.coe_toMonoidHom, he]
  let E : H1 A →ₗ[R] H1 B := pairH1 A B e.symm.toMonoidHom hesc LinearMap.id continuous_id fun g m => by
    simp only [A, B, LinearMap.id_apply, MonoidHom.comp_apply, Subgroup.coe_subtype,
      MulEquiv.coe_toMonoidHom, key]
  have hEF : E ∘ₗ F = LinearMap.id := LinearMap.ext fun x => by
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    simp only [E, F, LinearMap.comp_apply, pairH1, Submodule.mapQ_apply, LinearMap.id_apply]
    congr 1; exact Subtype.ext (funext fun g => by simp [compatiblePairCocycles1])
  have hFE : F ∘ₗ E = LinearMap.id := LinearMap.ext fun x => by
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    simp only [E, F, LinearMap.comp_apply, pairH1, Submodule.mapQ_apply, LinearMap.id_apply]
    congr 1; exact Subtype.ext (funext fun g => by simp [compatiblePairCocycles1])
  let L : H1 A ≃ₗ[R] H1 B := LinearEquiv.ofLinearMap E F hEF hFE
  have hmap : (LocSel (ρ.comp φ : Representation R G' M) U' (Subgroup.comap φ '' 𝒟)).map
      (L : H1 A →ₗ[R] H1 B) = LocSel ρ U 𝒟 := by
    ext x
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [Submodule.mem_map_equiv]
    change Submodule.Quotient.mk (compatiblePairCocycles1 B A e.toMonoidHom hec LinearMap.id continuous_id _ z) ∈
      LocSel (ρ.comp φ : Representation R G' M) U' (Subgroup.comap φ '' 𝒟) ↔ _
    rw [mk_mem_locSel, mk_mem_locSel]
    constructor
    · intro hyp D hD
      obtain ⟨m, hm⟩ := hyp _ ⟨D, hD, rfl⟩
      refine ⟨m, fun u hu => ?_⟩
      have h1 := hm (e.symm u) (by rw [Subgroup.mem_comap, key]; exact hu)
      simpa [compatiblePairCocycles1, key] using h1
    · rintro hyp D' ⟨D, hD, rfl⟩
      obtain ⟨m, hm⟩ := hyp D hD
      refine ⟨m, fun u' hu' => ?_⟩
      have h1 := hm (e u') (by rw [he]; exact hu')
      rw [he] at h1
      simpa [compatiblePairCocycles1, he] using h1
  refine ⟨L.ofSubmodules _ _ hmap, fun z' z hz' hzz => ?_⟩
  rw [LinearEquiv.ofSubmodules_apply]
  simp only [L, LinearEquiv.coe_ofLinearMap, E, pairH1, Submodule.mapQ_apply]
  congr 1; exact Subtype.ext (funext fun u => (hzz (e.symm u) u (key u)).symm)

section SelTwistHelpers

variable {R G M : Type} [CommRing R] [Group G] [TopologicalSpace G] [AddCommGroup M] [Module R M]
  [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M]

private def h1MapOfAgreeOnSubgroup (ρ ρ' : Representation R G M) (U : Subgroup G)
    (h : ∀ (u : U) m, ρ u m = ρ' u m) : H1U ρ U →ₗ[R] H1U ρ' U :=
  pairH1 _ _ (MonoidHom.id U) continuous_id LinearMap.id continuous_id fun u m => h u m

private theorem sameH1_mem_localSelmer (ρ ρ' : Representation R G M) (U : Subgroup G)
    (h : ∀ (u : U) m, ρ u m = ρ' u m) (𝒟 : Set (Subgroup G)) (x : H1U ρ U)
    (hx : x ∈ LocSel ρ U 𝒟) : h1MapOfAgreeOnSubgroup ρ ρ' U h x ∈ LocSel ρ' U 𝒟 := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  change Submodule.Quotient.mk _ ∈ LocSel ρ' U 𝒟
  rw [mk_mem_locSel] at hx ⊢
  intro D hD
  obtain ⟨m, hm⟩ := hx D hD
  exact ⟨m, fun u hu => by show z.1 u = _; rw [hm u hu, h]⟩

private def sameSel (ρ ρ' : Representation R G M) (U : Subgroup G)
    (h : ∀ (u : U) m, ρ u m = ρ' u m) (𝒟 : Set (Subgroup G)) : LocSel ρ U 𝒟 ≃ₗ[R] LocSel ρ' U 𝒟 :=
  LinearEquiv.ofLinearMap
    ((h1MapOfAgreeOnSubgroup ρ ρ' U h).restrict (sameH1_mem_localSelmer ρ ρ' U h 𝒟))
    ((h1MapOfAgreeOnSubgroup ρ' ρ U fun u m => (h u m).symm).restrict
      (sameH1_mem_localSelmer ρ' ρ U _ 𝒟))
    (LinearMap.ext fun x => Subtype.ext (by
      obtain ⟨z, hz⟩ := Submodule.Quotient.mk_surjective _ x.1
      change h1MapOfAgreeOnSubgroup ρ ρ' U h (h1MapOfAgreeOnSubgroup ρ' ρ U _ x.1) = x.1
      rw [← hz]; rfl))
    (LinearMap.ext fun x => Subtype.ext (by
      obtain ⟨z, hz⟩ := Submodule.Quotient.mk_surjective _ x.1
      change h1MapOfAgreeOnSubgroup ρ' ρ U _ (h1MapOfAgreeOnSubgroup ρ ρ' U h x.1) = x.1
      rw [← hz]; rfl))

private theorem sameH1_conjugation_scalar [IsTopologicalGroup G] [DiscreteTopology M]
    (ρ ρ' : Representation R G M) (U : Subgroup G) [U.Normal]
    (h : ∀ (u : U) m, ρ u m = ρ' u m) (g : G) (c : R) (hg : ∀ m, ρ g m = c • ρ' g m)
    (x : H1U ρ U) :
    h1MapOfAgreeOnSubgroup ρ ρ' U h (conjRep ρ U g x) =
      c • conjRep ρ' U g (h1MapOfAgreeOnSubgroup ρ ρ' U h x) := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [conjRep_apply, conjRep_apply]
  change Submodule.Quotient.mk _ = c • Submodule.Quotient.mk _
  rw [← Submodule.Quotient.mk_smul]
  congr 1; exact Subtype.ext (funext fun u => (hg _))

end SelTwistHelpers

theorem selTwist :
    ∀ (R G M : Type) [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
      [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M]
      [ContinuousConstSMul R M] [DiscreteTopology M] (ρ ρ' : Representation R G M)
      (θ : G →* Rˣ), (∀ g m, ρ g m = ((θ g : Rˣ) : R) • ρ' g m) →
      ∀ (U : Subgroup G) [U.Normal], (∀ u ∈ U, θ u = 1) →
      ∀ (𝒟 : Set (Subgroup G)) (h𝒟 : ConjStable 𝒟),
      (∃ Φ : LocSel ρ U 𝒟 ≃ₗ[R] LocSel ρ' U 𝒟,
        ∀ g x, Φ (selRep ρ U h𝒟 g x) = ((θ g : Rˣ) : R) • selRep ρ' U h𝒟 g (Φ x)) ∧
      ∀ (W : Subgroup G) (φ : W →* Rˣ),
        Module.length R (selEig ρ U h𝒟 W (θ.comp W.subtype * φ)) =
          Module.length R (selEig ρ' U h𝒟 W φ) := by
  intro R G M _ _ _ _ _ _ _ _ _ _ ρ ρ' θ hθ U _ hU 𝒟 h𝒟
  have h : ∀ (u : U) m, ρ u m = ρ' u m := fun u m => by
    rw [hθ, hU u u.2, Units.val_one, one_smul]
  have hΦ : ∀ g x, sameSel ρ ρ' U h 𝒟 (selRep ρ U h𝒟 g x) =
      ((θ g : Rˣ) : R) • selRep ρ' U h𝒟 g (sameSel ρ ρ' U h 𝒟 x) := fun g x =>
    Subtype.ext (sameH1_conjugation_scalar ρ ρ' U h g _ (hθ g) x.1)
  refine ⟨⟨_, hΦ⟩, fun W φ => ?_⟩
  generalize sameSel ρ ρ' U h 𝒟 = Φ at hΦ
  have key : ∀ x, x ∈ selEig ρ U h𝒟 W (θ.comp W.subtype * φ) ↔ Φ x ∈ selEig ρ' U h𝒟 W φ :=
    fun x => by
      rw [mem_eig, mem_eig]
      refine forall_congr' fun w => ?_
      show selRep ρ U h𝒟 w x = ((θ w * φ w : Rˣ) : R) • x ↔
        selRep ρ' U h𝒟 w (Φ x) = ((φ w : Rˣ) : R) • Φ x
      rw [← Φ.injective.eq_iff, hΦ, map_smul, Units.val_mul, mul_smul]
      exact (Units.isUnit (θ w)).smul_left_cancel
  have hmap : (selEig ρ U h𝒟 W (θ.comp W.subtype * φ)).map (Φ : _ →ₗ[R] _) =
      selEig ρ' U h𝒟 W φ := by
    ext y
    obtain ⟨x, rfl⟩ := Φ.surjective y
    rw [← key]
    exact ⟨fun ⟨x', hx', e⟩ => Φ.injective e ▸ hx', fun hx => ⟨x, hx, rfl⟩⟩
  exact (Φ.ofSubmodules _ _ hmap).length_eq

theorem inflAct :
    ∀ (k E Ω : Type) [Field k] [NumberField k] [Field E] [NumberField E] [Field Ω] [Algebra k E]
      [Algebra k Ω] [Algebra E Ω] [IsScalarTower k E Ω] [IsAlgClosure k Ω] [IsAlgClosure E Ω]
      [Normal k E] (l : ℕ) [Fact l.Prime] (D : LData E Ω l) (e : ℤ) (τ : E ≃+* E) (σ : G k Ω),
      IsLift τ σ.toRingEquiv → ∀ x y, Infl k D e x y →
      Infl k D e (galoisActionOnCohomology D e τ x)
        (conjRep (qzG k Ω l e) (galOf k E Ω) σ y) := by
  intro k E Ω _ _ _ _ _ _ _ _ _ _ _ _ l _ D e τ σ h x y hxy
  obtain ⟨z, z', rfl, rfl, hz⟩ := hxy
  obtain ⟨z₁, e₁, f₁⟩ := exists_cocycle_h1TwistConjByLift_mk_eq_mk D e h z
  obtain ⟨z₂, e₂, f₂⟩ := conjU_mk (qzG k Ω l e) (galOf k E Ω) σ z'
  refine ⟨z₁, z₂, by rw [galois_action_cohomology_eq_conj D e h, e₁],
    by rw [conjRep_apply, e₂], fun g => ?_⟩
  have hc : conjHom (galOf k E Ω) σ ⟨galEmb k E Ω g, galEmb_mem k E Ω g⟩ =
      ⟨galEmb k E Ω (conjGal h g), galEmb_mem k E Ω _⟩ := Subtype.ext (AlgEquiv.ext fun _ => rfl)
  rw [f₂, f₁, conjGS_toGS, hc, hz]
  rfl

theorem inflUnique :
    ∀ (k E Ω : Type) [Field k] [NumberField k] [Field E] [NumberField E] [Field Ω] [Algebra k E]
      [Algebra k Ω] [Algebra E Ω] [IsScalarTower k E Ω] [IsAlgClosure k Ω] [IsAlgClosure E Ω]
      (l : ℕ) [Fact l.Prime] (D : LData E Ω l) (e : ℤ),
      (∀ x, ∃ y, Infl k D e x y) ∧
      ∀ x x' y y', Infl k D e x y → Infl k D e x' y' → (x = x' ↔ y = y') := by
  intro k E Ω _ _ _ _ _ _ _ _ _ _ _ l _ D e
  obtain ⟨hemb, -, -⟩ := galEmbTop k E Ω
  let ψ : G E Ω →* galOf k E Ω := (galEmb k E Ω).codRestrict _ (galEmb_mem k E Ω)
  have hsurj : Function.Surjective ψ := fun ⟨τ, hτ⟩ =>
    ⟨AlgEquiv.ofRingEquiv (f := τ.toRingEquiv) (fun x => hτ x), Subtype.ext (AlgEquiv.ext fun _ => rfl)⟩
  let Ψ : G E Ω ≃* galOf k E Ω :=
    MulEquiv.ofBijective ψ ⟨fun _ _ h => hemb.injective (congrArg Subtype.val h), hsurj⟩
  have hΨ : ∀ σ, Ψ σ = ⟨galEmb k E Ω σ, galEmb_mem k E Ω σ⟩ := fun _ => rfl
  have hcont : Continuous (fun u : galOf k E Ω => Ψ.symm u) := by
    rw [hemb.continuous_iff]
    have hc : (galEmb k E Ω) ∘ (fun u : galOf k E Ω => Ψ.symm u) = Subtype.val := funext fun u => by
      show ((Ψ (Ψ.symm u) : galOf k E Ω) : G k Ω) = u
      rw [Ψ.apply_symm_apply]
    rw [hc]; exact continuous_subtype_val
  have hEk : ∀ σ : G E Ω, qzG k Ω l e (galEmb k E Ω σ) = qzG E Ω l e σ := fun σ => by
    have hχ : (cycZ k Ω l ^ (-e)).comp (galEmb k E Ω) = cycZ E Ω l ^ (-e) :=
      MonoidHom.ext fun _ => by rw [MonoidHom.comp_apply]; simp only [MonoidHom.zpow_apply]; rfl
    show scalRep (QZ l) (cycZ k Ω l ^ (-e)) (galEmb k E Ω σ) = scalRep (QZ l) (cycZ E Ω l ^ (-e)) σ
    rw [← hχ]; rfl
  have hrep : ∀ σ : G E Ω, qzG k Ω l e (galEmb k E Ω σ) = qzTw D e (toGS Ω _ σ) := fun σ => by
    have h := DFunLike.congr_fun (qzTw_comp_toGS E Ω l D e) σ
    rw [MonoidHom.comp_apply] at h; rw [hEk]; exact h.symm
  have hu : ∀ u : galOf k E Ω, (u : G k Ω) = galEmb k E Ω (Ψ.symm u) := fun u => by
    conv_lhs => rw [← Ψ.apply_symm_apply u]
    rw [hΨ]
  have hTs : Function.Surjective (toGS Ω (D.S : Set (HeightOneSpectrum (𝓞 E)))) :=
    QuotientGroup.mk'_surjective _
  constructor
  · intro x
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    let f : galOf k E Ω → QZ l := fun u => z.1 (toGS Ω _ (Ψ.symm u))
    have hf : f ∈ Z1U (qzG k Ω l e) (galOf k E Ω) :=
      ⟨z.2.1.comp ((continuous_toGS Ω _).comp hcont), fun u v => by
        show z.1 (toGS Ω _ (Ψ.symm (u * v))) =
          z.1 (toGS Ω _ (Ψ.symm u)) + ((qzG k Ω l e).comp (galOf k E Ω).subtype u)
            (z.1 (toGS Ω _ (Ψ.symm v)))
        rw [map_mul, map_mul, z.2.2, MonoidHom.comp_apply, Subgroup.coe_subtype, hu u, hrep]⟩
    refine ⟨Submodule.Quotient.mk ⟨f, hf⟩, z, ⟨f, hf⟩, rfl, rfl, fun σ => ?_⟩
    show z.1 (toGS Ω _ (Ψ.symm ⟨galEmb k E Ω σ, _⟩)) = _
    rw [← hΨ, Ψ.symm_apply_apply]
  · rintro x x' y y' ⟨z1, w1, rfl, rfl, h1⟩ ⟨z2, w2, rfl, rfl, h2⟩
    rw [mk_eq_mk, Submodule.Quotient.eq, Submodule.mem_comap, Submodule.coe_subtype, mem_B1]
    refine exists_congr fun m => ⟨fun h u => ?_, fun h g => ?_⟩
    · obtain ⟨σ, rfl⟩ := Ψ.surjective u
      have h3 := h (toGS Ω _ σ)
      rw [Submodule.coe_sub, Pi.sub_apply] at h3
      rw [hΨ, h1, h2, h3]
      exact congrArg (fun T => T m - m) (hrep σ).symm
    · obtain ⟨σ, rfl⟩ := hTs g
      have h3 := h (Ψ σ)
      rw [hΨ, h1, h2] at h3
      rw [Submodule.coe_sub, Pi.sub_apply, h3]
      exact congrArg (fun T => T m - m) (hrep σ)

section ShaModelSection

private theorem resH1_injective_of_surjective {R G H M : Type} [CommRing R] [Group G]
    [TopologicalSpace G] [Group H] [TopologicalSpace H] [AddCommGroup M] [Module R M]
    [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M]
    (ρ : Representation R G M) (π : H →* G) (hπ : Continuous π)
    (hs : Function.Surjective π) : Function.Injective (resH1 ρ π hπ) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro x hx
  induction x using Submodule.Quotient.induction_on with
  | H z =>
    rw [LinearMap.mem_ker, resH1, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hx
    rw [Submodule.Quotient.mk_eq_zero]
    obtain ⟨m, hm⟩ := hx
    refine ⟨m, funext fun g => ?_⟩
    obtain ⟨h, rfl⟩ := hs g
    simpa [d0, restrictCocycles1] using congrFun hm h

private theorem resH1_bot_eq_zero {R G M : Type} [CommRing R] [Group G] [TopologicalSpace G]
    [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [ContinuousConstSMul R M] (ρ : Representation R G M) (x : H1 ρ) :
    resH1 ρ (⊥ : Subgroup G).subtype continuous_subtype_val x = 0 := by
  induction x using Submodule.Quotient.induction_on with
  | H z =>
    simp only [resH1, Submodule.mapQ_apply]
    rw [Submodule.Quotient.mk_eq_zero]
    refine ⟨0, funext fun ⟨u, hu⟩ => ?_⟩
    rw [Subgroup.mem_bot] at hu; subst hu
    have h1 := z.2.2 1 1
    simp at h1; simp [d0, restrictCocycles1, h1]

private theorem resH1_eq_zero_of_le {R G M : Type} [CommRing R] [Group G] [TopologicalSpace G]
    [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [ContinuousConstSMul R M] (ρ : Representation R G M) {K L : Subgroup G} (h : K ≤ L)
    (x : H1 ρ) (hx : resH1 ρ L.subtype continuous_subtype_val x = 0) :
    resH1 ρ K.subtype continuous_subtype_val x = 0 := by
  induction x using Submodule.Quotient.induction_on with
  | H z =>
    simp only [resH1, Submodule.mapQ_apply] at hx ⊢
    rw [Submodule.Quotient.mk_eq_zero] at hx ⊢
    obtain ⟨m, hm⟩ := hx
    refine ⟨m, funext fun u => by simpa [d0, restrictCocycles1] using congrFun hm ⟨u.1, h u.2⟩⟩

private theorem resU_resH1_subtype_eq {R G M : Type} [CommRing R] [Group G] [TopologicalSpace G]
    [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [ContinuousConstSMul R M] (ρ : Representation R G M) {U' U : Subgroup G} (h : U' ≤ U)
    (x : H1 ρ) :
    resU ρ h (resH1 ρ U.subtype continuous_subtype_val x) =
      resH1 ρ U'.subtype continuous_subtype_val x := by
  induction x using Submodule.Quotient.induction_on with
  | H z =>
    obtain ⟨z', hz', hz'u⟩ := resU_mk ρ h (restrictCocycles1 ρ U.subtype continuous_subtype_val z)
    simp only [resH1, Submodule.mapQ_apply] at hz' ⊢
    rw [hz']
    congr 1; ext u; simp [hz'u, restrictCocycles1]

private theorem resH1_subtype_whole_bijective_sha {R G M : Type} [CommRing R] [Group G]
    [TopologicalSpace G] [AddCommGroup M] [Module R M] [TopologicalSpace M]
    [IsTopologicalAddGroup M] [ContinuousConstSMul R M] (ρ : Representation R G M) :
    Function.Bijective (resH1 ρ (⊤ : Subgroup G).subtype continuous_subtype_val) := by
  refine ⟨resH1_injective_of_surjective ρ _ _ (fun g => ⟨⟨g, Subgroup.mem_top g⟩, rfl⟩), fun y => ?_⟩
  induction y using Submodule.Quotient.induction_on with
  | H z' =>
    have hz : (fun g : G => (z' : (⊤ : Subgroup G) → M) ⟨g, Subgroup.mem_top g⟩) ∈ Z1 ρ :=
      ⟨z'.2.1.comp (continuous_id.subtype_mk _), fun g h => z'.2.2 ⟨g, trivial⟩ ⟨h, trivial⟩⟩
    refine ⟨Submodule.Quotient.mk ⟨_, hz⟩, ?_⟩
    simp only [resH1, Submodule.mapQ_apply]; congr 1

private theorem mem_shaAbs_iff_resH1_whole_mem_locSel {E Ω : Type} [Field E] [NumberField E]
    [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] {M : Type}
    [AddCommGroup M] [Module ℤ_[l] M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [ContinuousConstSMul ℤ_[l] M] (ρ : Representation ℤ_[l] (G E Ω) M)
    (S : Set (HeightOneSpectrum (𝓞 E))) (hS : S = Above E l) (x : H1 ρ) :
    x ∈ ShaAbs ρ S ↔
      resH1 ρ (⊤ : Subgroup (G E Ω)).subtype continuous_subtype_val x ∈
        LocSel ρ ⊤ (shaFam E Ω l) := by
  subst hS
  have key : ∀ D : Subgroup (G E Ω),
      resU ρ (inf_le_left : ⊤ ⊓ D ≤ ⊤) (resH1 ρ (⊤ : Subgroup (G E Ω)).subtype continuous_subtype_val x) = 0 ↔
        resH1 ρ D.subtype continuous_subtype_val x = 0 := fun D => by
    rw [resU_resH1_subtype_eq]
    exact ⟨resH1_eq_zero_of_le ρ (le_inf le_top le_rfl) x, resH1_eq_zero_of_le ρ inf_le_right x⟩
  simp only [ShaAbs, LocSel, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, key]
  constructor
  · rintro ⟨h1, h2⟩ D hD
    rcases hD with ⟨A, hA, rfl⟩ | ⟨A, rfl⟩
    · have hA' : A ≠ ⊤ := fun h => ((places E Ω l A).2.1 h).2 hA
      obtain ⟨v, hv⟩ := (places E Ω l A).1 hA'
      exact h1 v (((places E Ω l A).2.2.1 v hv).1 hA) A hv
    · by_cases hT : A = ⊤
      · rw [((places E Ω l A).2.1 hT).1]; exact resH1_bot_eq_zero ρ x
      · obtain ⟨v, hv⟩ := (places E Ω l A).1 hT
        by_cases hvS : v ∈ Above E l
        · exact resH1_eq_zero_of_le ρ (Ine_le_Dec A) x (h1 v hvS A hv)
        · exact h2 v hvS A hv
  · intro h
    exact ⟨fun v hv A hA => h _ (Or.inl ⟨A, ((places E Ω l A).2.2.1 v hA).2 hv, rfl⟩),
      fun v _ A _ => h _ (Or.inr ⟨A, rfl⟩)⟩

private theorem sha_exists_cocycle_lift_whole {E Ω : Type} [Field E] [NumberField E] [Field Ω]
    [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime] (D : LData E Ω l) (e : ℤ)
    (ρ' : Representation ℤ_[l] (G E Ω) (QZ l))
    (hρ' : MonoidHom.comp (qzTw D e) (toGS Ω (D.S : Set (HeightOneSpectrum (𝓞 E)))) = ρ')
    (𝒟 : Set (Subgroup (G E Ω))) (h𝒟 : shaFam E Ω l = 𝒟) :
    ∃ Ψ : Sha D e ≃ₗ[ℤ_[l]] LocSel ρ' ⊤ 𝒟, ∀ (x : Sha D e) (z : Z1 (qzTw D e)),
      x.1 = Submodule.Quotient.mk z → ∃ w : Z1U ρ' ⊤, (Ψ x).1 = Submodule.Quotient.mk w ∧
        ∀ σ : G E Ω, (w : (⊤ : Subgroup (G E Ω)) → QZ l) ⟨σ, Subgroup.mem_top σ⟩ =
          (z : GS Ω (D.S : Set (HeightOneSpectrum (𝓞 E))) → QZ l) (toGS Ω _ σ) := by
  subst hρ' h𝒟
  have hinj := resH1_injective_of_surjective (qzTw D e) _ (continuous_toGS Ω _)
    (QuotientGroup.mk'_surjective _)
  have hmapS := shaInfl E Ω D.S D.A D.hA ℤ_[l] (QZ l) (qzTw D e)
  have hbij := resH1_subtype_whole_bijective_sha (MonoidHom.comp (qzTw D e) (toGS Ω (D.S : Set (HeightOneSpectrum (𝓞 E)))))
  have hEq : Submodule.map (resH1 _ (⊤ : Subgroup (G E Ω)).subtype continuous_subtype_val)
      (ShaAbs (MonoidHom.comp (qzTw D e) (toGS Ω (D.S : Set (HeightOneSpectrum (𝓞 E))))) (D.S : Set _)) =
      LocSel (MonoidHom.comp (qzTw D e) (toGS Ω (D.S : Set (HeightOneSpectrum (𝓞 E))))) ⊤ (shaFam E Ω l) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩; exact (mem_shaAbs_iff_resH1_whole_mem_locSel l _ _ D.hS x).1 hx
    · intro hy; obtain ⟨x, rfl⟩ := hbij.2 y
      exact ⟨x, (mem_shaAbs_iff_resH1_whole_mem_locSel l _ _ D.hS x).2 hy, rfl⟩
  refine ⟨((Submodule.equivMapOfInjective _ hinj (Sha D e)).trans (LinearEquiv.ofEq _ _ hmapS)).trans
    (((LinearEquiv.ofBijective _ hbij).submoduleMap _).trans (LinearEquiv.ofEq _ _ hEq)), ?_⟩
  intro x z hz
  refine ⟨restrictCocycles1 _ _ continuous_subtype_val (restrictCocycles1 _ _ (continuous_toGS Ω _) z),
    ?_, fun σ => rfl⟩
  have h1 : (((((Submodule.equivMapOfInjective _ hinj (Sha D e)).trans (LinearEquiv.ofEq _ _ hmapS)).trans
      (((LinearEquiv.ofBijective _ hbij).submoduleMap _).trans (LinearEquiv.ofEq _ _ hEq))) x) :
        H1U (MonoidHom.comp (qzTw D e) (toGS Ω (D.S : Set (HeightOneSpectrum (𝓞 E))))) ⊤) =
      resH1 (MonoidHom.comp (qzTw D e) (toGS Ω (D.S : Set (HeightOneSpectrum (𝓞 E)))))
        (⊤ : Subgroup (G E Ω)).subtype continuous_subtype_val
        (resH1 (qzTw D e) (toGS Ω (D.S : Set (HeightOneSpectrum (𝓞 E)))) (continuous_toGS Ω _) x.1) := rfl
  rw [h1, hz]
  simp only [resH1, Submodule.mapQ_apply]

theorem shaModel :
    ∀ (k E Ω : Type) [Field k] [NumberField k] [Field E] [NumberField E] [Field Ω] [Algebra k E]
      [Algebra k Ω] [Algebra E Ω] [IsScalarTower k E Ω] [IsAlgClosure k Ω] [IsAlgClosure E Ω]
      (l : ℕ) [Fact l.Prime] (D : LData E Ω l) (e : ℤ),
      ∃ Φ : Sha D e ≃ₗ[ℤ_[l]] ShaU (qzG k Ω l e) l (galOf k E Ω), ∀ x, Infl k D e x.1 (Φ x).1 := by
  intro k E Ω _ _ _ _ _ _ _ _ _ _ _ l _ D e
  obtain ⟨_, hfam, _, hrep⟩ := galEmbFam k E Ω l
  obtain ⟨hemb, _, _⟩ := galEmbTop k E Ω
  have hmap : Subgroup.map (galEmb k E Ω) ⊤ = galOf k E Ω := by
    rw [← MonoidHom.range_eq_map, range_galEmb]
  obtain ⟨Φ, hΦ⟩ := selTransport ℤ_[l] (G k Ω) (QZ l) (qzG k Ω l e) (G E Ω) (galEmb k E Ω)
    hemb ⊤ (galOf k E Ω) hmap (shaFam k Ω l)
  obtain ⟨Ψ, hΨ⟩ := sha_exists_cocycle_lift_whole D e (MonoidHom.comp (qzG k Ω l e) (galEmb k E Ω))
    ((qzTw_comp_toGS E Ω l D e).trans (hrep e).symm) _ hfam.symm
  have hr : ∀ u : galOf k E Ω, (u : G k Ω) ∈ Set.range (galEmb k E Ω) := fun u => by
    have : (u : G k Ω) ∈ (galEmb k E Ω).range := by rw [range_galEmb]; exact u.2
    exact this
  let ψ : galOf k E Ω → G E Ω := fun u => hemb.toHomeomorph.symm ⟨u.1, hr u⟩
  have hψc : Continuous ψ := hemb.toHomeomorph.symm.continuous.comp (continuous_subtype_val.subtype_mk _)
  have hψ : ∀ u, galEmb k E Ω (ψ u) = u := fun u =>
    congrArg Subtype.val (hemb.toHomeomorph.apply_symm_apply ⟨u.1, hr u⟩)
  have hψm : ∀ u v, ψ (u * v) = ψ u * ψ v := fun u v =>
    hemb.injective (by rw [map_mul, hψ, hψ, hψ]; rfl)
  refine ⟨Ψ.trans Φ, fun x => ?_⟩
  obtain ⟨z, hz⟩ := Submodule.Quotient.mk_surjective _ x.1
  obtain ⟨w, hw1, hw2⟩ := hΨ x z hz.symm
  have hz'' : (fun u : galOf k E Ω => (w : (⊤ : Subgroup (G E Ω)) → QZ l) ⟨ψ u, Subgroup.mem_top _⟩) ∈
      Z1U (qzG k Ω l e) (galOf k E Ω) := by
    refine ⟨w.2.1.comp (hψc.subtype_mk _), fun u v => ?_⟩
    have hw := w.2.2 ⟨ψ u, trivial⟩ ⟨ψ v, trivial⟩
    have e1 : (⟨ψ (u * v), Subgroup.mem_top _⟩ : (⊤ : Subgroup (G E Ω))) =
        ⟨ψ u, trivial⟩ * ⟨ψ v, trivial⟩ := Subtype.ext (hψm u v)
    simp only [MonoidHom.comp_apply, Subgroup.coe_subtype] at hw ⊢
    rw [e1, hw, hψ]
  have hmem : Submodule.Quotient.mk w ∈ LocSel (MonoidHom.comp (qzG k Ω l e) (galEmb k E Ω)) ⊤
      (Subgroup.comap (galEmb k E Ω) '' shaFam k Ω l) := hw1 ▸ (Ψ x).2
  have hx : Ψ x = ⟨Submodule.Quotient.mk w, hmem⟩ := Subtype.ext hw1
  have hcomp := hΦ w ⟨_, hz''⟩ hmem (fun u' u hu => by
    obtain ⟨u', hu'⟩ := u'; obtain ⟨u, hu2⟩ := u
    change (w : (⊤ : Subgroup (G E Ω)) → QZ l) ⟨ψ ⟨u, hu2⟩, trivial⟩ =
      (w : (⊤ : Subgroup (G E Ω)) → QZ l) ⟨u', hu'⟩
    have h5 : ψ ⟨u, hu2⟩ = u' := hemb.injective ((hψ _).trans hu.symm)
    exact congrArg (fun s => (w : (⊤ : Subgroup (G E Ω)) → QZ l) ⟨s, trivial⟩) h5)
  refine ⟨z, ⟨_, hz''⟩, hz.symm, ?_, fun σ => ?_⟩
  · rw [LinearEquiv.trans_apply, hx, hcomp]
  · change (w : (⊤ : Subgroup (G E Ω)) → QZ l) ⟨ψ ⟨galEmb k E Ω σ, _⟩, trivial⟩ = _
    rw [← hw2 σ]
    have h5 : ψ ⟨galEmb k E Ω σ, galEmb_mem k E Ω σ⟩ = σ := hemb.injective (hψ _)
    exact congrArg (fun s => (w : (⊤ : Subgroup (G E Ω)) → QZ l) ⟨s, trivial⟩) h5

set_option maxHeartbeats 800000 in
theorem shaLenEq :
    ∀ (k E Ω : Type) [Field k] [NumberField k] [Field E] [NumberField E] [Field Ω] [Algebra k E]
      [Algebra k Ω] [Algebra E Ω] [IsScalarTower k E Ω] [IsAlgClosure k Ω] [IsAlgClosure E Ω]
      (l : ℕ) [Fact l.Prime] (D : LData E Ω l) (e : ℤ),
      shaLen D e = Module.length ℤ_[l] (ShaU (qzG k Ω l e) l (galOf k E Ω)) ∧
      ∀ [Normal k E] (τ : E ≃+* E) (σ : G k Ω), IsLift τ σ.toRingEquiv → ∀ s : ℤ_[l],
        Module.length ℤ_[l] ↥(Sha D e ⊓ Module.End.eigenspace (galoisActionOnCohomology D e τ) s) =
          Module.length ℤ_[l] (Module.End.eigenspace (shaRep (qzG k Ω l e) l (galOf k E Ω) σ) s) := by
  intro k E Ω _ _ _ _ _ _ _ _ _ _ _ l _ D e
  obtain ⟨Φ, hΦ⟩ := shaModel k E Ω l D e
  refine ⟨Φ.length_eq, ?_⟩
  intro _ τ σ hτσ s
  have key : ∀ x : ↥(Sha D e), ∃ h : galoisActionOnCohomology D e τ (x : H1 (qzTw D e)) ∈ Sha D e,
      Φ ⟨_, h⟩ = shaRep (qzG k Ω l e) l (galOf k E Ω) σ (Φ x) := fun x => by
    set y := shaRep (qzG k Ω l e) l (galOf k E Ω) σ (Φ x)
    have h1 := inflAct k E Ω l D e τ σ hτσ _ _ (hΦ x)
    have h2 := hΦ (Φ.symm y)
    rw [LinearEquiv.apply_symm_apply] at h2
    have heq : galoisActionOnCohomology D e τ (x : H1 (qzTw D e)) = ((Φ.symm y : ↥(Sha D e)) : H1 (qzTw D e)) :=
      ((inflUnique k E Ω l D e).2 _ _ _ _ h1 h2).2 rfl
    have hmem : galoisActionOnCohomology D e τ (x : H1 (qzTw D e)) ∈ Sha D e := by
      rw [heq]; exact (Φ.symm y).2
    refine ⟨hmem, ?_⟩
    have hsub : (⟨_, hmem⟩ : ↥(Sha D e)) = Φ.symm y := Subtype.ext heq
    rw [hsub, LinearEquiv.apply_symm_apply]
  have hle : Sha D e ⊓ Module.End.eigenspace (galoisActionOnCohomology D e τ) s ≤ Sha D e := inf_le_left
  have hmap : Submodule.map (Φ : ↥(Sha D e) →ₗ[ℤ_[l]] ↥(ShaU (qzG k Ω l e) l (galOf k E Ω)))
      (Submodule.comap (Sha D e).subtype (Sha D e ⊓ Module.End.eigenspace (galoisActionOnCohomology D e τ) s)) =
      Module.End.eigenspace (shaRep (qzG k Ω l e) l (galOf k E Ω) σ) s := by
    rw [Submodule.map_equiv_eq_comap_symm]
    ext y
    obtain ⟨h, hk⟩ := key (Φ.symm y)
    rw [LinearEquiv.apply_symm_apply] at hk
    rw [Module.End.mem_eigenspace_iff, Submodule.mem_comap, Submodule.mem_comap, Submodule.subtype_apply,
      Submodule.mem_inf, Module.End.mem_eigenspace_iff]
    refine ⟨fun hx => ?_, fun hx => ?_⟩
    · have hs : (⟨_, h⟩ : ↥(Sha D e)) = s • Φ.symm y := Subtype.ext hx.2
      calc shaRep (qzG k Ω l e) l (galOf k E Ω) σ y = Φ ⟨_, h⟩ := hk.symm
        _ = Φ (s • Φ.symm y) := congrArg Φ hs
        _ = s • y := by rw [map_smul, LinearEquiv.apply_symm_apply]
    · refine ⟨(Φ.symm y).2, ?_⟩
      have hs : (⟨_, h⟩ : ↥(Sha D e)) = s • Φ.symm y :=
        Φ.injective (calc Φ ⟨_, h⟩ = shaRep (qzG k Ω l e) l (galOf k E Ω) σ y := hk
          _ = s • y := hx
          _ = Φ (s • Φ.symm y) := by rw [map_smul, LinearEquiv.apply_symm_apply])
      exact congrArg Subtype.val hs
  rw [← hmap]
  exact ((Submodule.comapSubtypeEquivOfLe hle).symm.trans (Φ.submoduleMap _)).length_eq

end ShaModelSection

section EigenLengthBounds

theorem lenComp :
    ∀ (R N : Type) [CommRing R] [AddCommGroup N] [Module R N] (a b : Module.End R N),
      Module.length R (LinearMap.ker (a * b)) ≤ Module.length R (LinearMap.ker a) + Module.length R (LinearMap.ker b) ∧
      Module.length R (N ⧸ LinearMap.range (a * b)) ≤
        Module.length R (N ⧸ LinearMap.range a) + Module.length R (N ⧸ LinearMap.range b) := by
  have len_ex : ∀ {R A B C : Type} [CommRing R] [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
      [AddCommGroup C] [Module R C] (f : A →ₗ[R] B) (g : B →ₗ[R] C),
      LinearMap.ker g ≤ LinearMap.range f → Module.length R B ≤ Module.length R C + Module.length R A :=
    fun f g h => by
      have e := Module.length_eq_add_of_exact (LinearMap.ker g).subtype g.rangeRestrict
        (Submodule.subtype_injective _) g.surjective_rangeRestrict
        (by rw [LinearMap.exact_iff, LinearMap.ker_rangeRestrict, Submodule.range_subtype])
      rw [e, add_comm]
      exact add_le_add (Module.length_le_of_injective _ (Submodule.subtype_injective _))
        ((Module.length_le_of_injective _ (Submodule.inclusion_injective h)).trans
          (Module.length_le_of_surjective _ f.surjective_rangeRestrict))
  intro R N _ _ _ a b
  constructor
  · have h1 : LinearMap.ker b ≤ LinearMap.ker (a * b) := fun x hx => by
      rw [LinearMap.mem_ker] at hx ⊢; rw [Module.End.mul_apply, hx, map_zero]
    exact len_ex (Submodule.inclusion h1) (LinearMap.restrict b fun _ hx => hx)
      fun x hx => ⟨⟨x.1, congrArg Subtype.val hx⟩, rfl⟩
  · have h1 : LinearMap.range b ≤ (LinearMap.range (a * b)).comap a := fun _ ⟨y, hy⟩ => ⟨y, by rw [← hy]; rfl⟩
    have h2 : LinearMap.range (a * b) ≤ (LinearMap.range a).comap LinearMap.id :=
      fun _ ⟨y, hy⟩ => ⟨b y, hy⟩
    refine len_ex (Submodule.mapQ _ _ a h1) (Submodule.mapQ _ _ LinearMap.id h2) fun x hx => ?_
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [LinearMap.mem_ker, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hx
    obtain ⟨y, hy⟩ := hx
    exact ⟨Submodule.Quotient.mk y, by rw [Submodule.mapQ_apply, hy]; rfl⟩

private theorem length_product_polynomial_le (O N : Type) [CommRing O] [AddCommGroup N] [Module O N]
    (f : Module.End O N) (p : ℕ → Polynomial O) (s : Finset ℕ) :
    Module.length O (LinearMap.ker (Polynomial.aeval f (∏ i ∈ s, p i))) ≤
        ∑ i ∈ s, Module.length O (LinearMap.ker (Polynomial.aeval f (p i))) ∧
    Module.length O (N ⧸ LinearMap.range (Polynomial.aeval f (∏ i ∈ s, p i))) ≤
        ∑ i ∈ s, Module.length O (N ⧸ LinearMap.range (Polynomial.aeval f (p i))) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have hg : Polynomial.aeval f (∏ i ∈ (∅ : Finset ℕ), p i) = 1 := by rw [Finset.prod_empty, map_one]
    rw [Finset.sum_empty, hg, Module.End.one_eq_id, LinearMap.ker_id, LinearMap.range_id]
    exact ⟨(Module.length_eq_zero_iff.2 inferInstance).le, (Module.length_eq_zero_iff.2 inferInstance).le⟩
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Finset.sum_insert ha, map_mul]
    obtain ⟨h1, h2⟩ := lenComp O N (Polynomial.aeval f (p a)) (Polynomial.aeval f (∏ i ∈ s, p i))
    exact ⟨h1.trans (add_le_add le_rfl ih.1), h2.trans (add_le_add le_rfl ih.2)⟩

theorem lenRoots :
    ∀ (O N : Type) [CommRing O] [IsDomain O] [AddCommGroup N] [Module O N] (n : ℕ) (ζ : O),
      0 < n → IsPrimitiveRoot ζ n → ∀ f : Module.End O N, f ^ n = 1 →
      Module.length O N ≤ ∑ i ∈ Finset.range n, Module.length O (LinearMap.ker (f - ζ ^ i • (1 : Module.End O N))) ∧
      Module.length O N ≤ ∑ i ∈ Finset.range n, Module.length O (N ⧸ LinearMap.range (f - ζ ^ i • (1 : Module.End O N))) := by
  intro O N _ _ _ _ n ζ hn hζ f hf
  have hprod := X_pow_sub_C_eq_prod hζ hn (one_pow n)
  have hterm : ∀ i, Polynomial.aeval f (Polynomial.X - Polynomial.C (ζ ^ i * 1)) =
      f - ζ ^ i • (1 : Module.End O N) := fun i => by simp [Algebra.algebraMap_eq_smul_one, _root_.smul_pow]
  have e : Polynomial.aeval f (∏ i ∈ Finset.range n, (Polynomial.X - Polynomial.C (ζ ^ i * 1))) = 0 := by
    rw [← hprod]; simp [hf]
  obtain ⟨h1, h2⟩ := length_product_polynomial_le O N f (fun i => Polynomial.X - Polynomial.C (ζ ^ i * 1))
    (Finset.range n)
  rw [e] at h1 h2
  rw [LinearMap.ker_zero, Module.length_top] at h1
  rw [LinearMap.range_zero, (Submodule.quotEquivOfEqBot (⊥ : Submodule O N) rfl).length_eq] at h2
  exact ⟨h1.trans (le_of_eq (Finset.sum_congr rfl fun i _ => by rw [hterm i])),
    h2.trans (le_of_eq (Finset.sum_congr rfl fun i _ => by rw [hterm i]))⟩

section LenEigEqSection

variable {O Q N : Type} [CommRing O] [CommGroup Q] [Fintype Q] [AddCommGroup N] [Module O N]

private def prj (π : Representation O Q N) (c : O) (ψ : Q →* Oˣ) : N →ₗ[O] N :=
  c • ∑ g : Q, ((ψ g⁻¹ : Oˣ) : O) • π g

private theorem prj_apply (π : Representation O Q N) (c : O) (ψ : Q →* Oˣ) (x : N) :
    prj π c ψ x = c • ∑ g : Q, ((ψ g⁻¹ : Oˣ) : O) • π g x := by
  simp only [prj, LinearMap.smul_apply, LinearMap.sum_apply]

private theorem prj_mem (π : Representation O Q N) (c : O) (ψ : Q →* Oˣ) (x : N) :
    prj π c ψ x ∈ eig π ψ := by
  rw [mem_eig]; intro h
  rw [prj_apply, map_smul, smul_comm, map_sum, Finset.smul_sum (r := ((ψ h : Oˣ) : O))]
  congr 1
  refine Fintype.sum_equiv (Equiv.mulLeft h) _ _ fun g => ?_
  rw [map_smul, smul_smul, Equiv.coe_mulLeft, ← Units.val_mul, ← map_mul, map_mul π, Module.End.mul_apply]
  congr 3; rw [mul_inv, mul_inv_cancel_left]

private theorem prj_act (π : Representation O Q N) (c : O) (ψ : Q →* Oˣ) (h : Q) (x : N) :
    prj π c ψ (π h x) = ((ψ h : Oˣ) : O) • prj π c ψ x := by
  rw [← mem_eig.1 (prj_mem π c ψ x) h, prj_apply, prj_apply, map_smul, map_sum]
  congr 1; refine Finset.sum_congr rfl fun g _ => ?_
  rw [map_smul, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, mul_comm]

private theorem prj_self (π : Representation O Q N) {c : O} (hc : c * (Fintype.card Q : O) = 1)
    (ψ : Q →* Oˣ) {x : N} (hx : x ∈ eig π ψ) : prj π c ψ x = x := by
  rw [prj_apply]
  have : ∀ g : Q, ((ψ g⁻¹ : Oˣ) : O) • π g x = x := fun g => by
    rw [mem_eig.1 hx, smul_smul, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, one_smul]
  simp only [this, Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul O, smul_smul, hc, one_smul]

private theorem prj_ne [IsDomain O] (π : Representation O Q N) (c : O) {ψ χ : Q →* Oˣ} (hne : ψ ≠ χ)
    {x : N} (hx : x ∈ eig π χ) : prj π c ψ x = 0 := by
  rw [prj_apply]
  have : ∀ g : Q, ((ψ g⁻¹ : Oˣ) : O) • π g x = ((Units.coeHom O).comp (ψ⁻¹ * χ) g) • x := fun g => by
    rw [mem_eig.1 hx, smul_smul]; simp
  simp only [this]
  rw [← Finset.sum_smul, sum_hom_units_eq_zero _ fun h => hne (MonoidHom.ext fun g => by
    have h1 := DFunLike.congr_fun h g
    have h2 : (ψ g)⁻¹ * χ g = 1 := Units.ext (by simpa [Units.coeHom_apply, MonoidHom.comp_apply, MonoidHom.mul_apply, MonoidHom.inv_apply] using h1)
    exact inv_mul_eq_one.1 h2), zero_smul, smul_zero]

private theorem sub_prj_mem (π : Representation O Q N) {c : O} (hc : c * (Fintype.card Q : O) = 1)
    (ψ : Q →* Oˣ) (x : N) : prj π c ψ x - x ∈ coeig π ψ := by
  have hx : x = c • ∑ g : Q, ((ψ g⁻¹ : Oˣ) : O) • ((ψ g : Oˣ) : O) • x := by
    have : ∀ g : Q, ((ψ g⁻¹ : Oˣ) : O) • ((ψ g : Oˣ) : O) • x = x := fun g => by
      rw [smul_smul, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, one_smul]
    simp only [this, Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul O, smul_smul, hc, one_smul]
  have : prj π c ψ x - x = c • ∑ g : Q, ((ψ g⁻¹ : Oˣ) : O) • (π g x - ((ψ g : Oˣ) : O) • x) := by
    simp only [smul_sub, Finset.sum_sub_distrib]; rw [← hx, prj_apply]
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun g _ =>
    Submodule.smul_mem _ _ (Submodule.mem_iSup_of_mem g ⟨x, rfl⟩))

private theorem sum_prj [IsDomain O] [HasEnoughRootsOfUnity O (Monoid.exponent Q)]
    [Fintype (Q →* Oˣ)] (π : Representation O Q N) {c : O} (hc : c * (Fintype.card Q : O) = 1)
    (x : N) : ∑ ψ : Q →* Oˣ, prj π c ψ x = x := by
  simp only [prj_apply]
  rw [← Finset.smul_sum, Finset.sum_comm, Finset.sum_eq_single (1 : Q)]
  · simp only [inv_one, map_one, Units.val_one, one_smul, Module.End.one_apply]
    rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card,
      CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity, Nat.card_eq_fintype_card,
      ← Nat.cast_smul_eq_nsmul O, smul_smul, hc, one_smul]
  · intro g _ hg
    rw [← Finset.sum_smul]
    obtain ⟨φ, hφ⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity Q O (inv_ne_one.2 hg)
    have h2 : ∑ ψ : Q →* Oˣ, ((ψ g⁻¹ : Oˣ) : O) = 0 :=
      sum_hom_units_eq_zero ((Units.coeHom O).comp (MonoidHom.eval g⁻¹ : (Q →* Oˣ) →* Oˣ))
        fun h => hφ (Units.ext (DFunLike.congr_fun h φ))
    rw [h2, zero_smul]
  · simp

end LenEigEqSection

theorem lenEigEq :
    ∀ (O Q N : Type) [CommRing O] [IsDomain O] [CommGroup Q] [Finite Q]
      [HasEnoughRootsOfUnity O (Monoid.exponent Q)] [Fintype (Q →* Oˣ)]
      [AddCommGroup N] [Module O N] (π : Representation O Q N), IsUnit (Nat.card Q : O) →
      Module.length O N = ∑ ψ : Q →* Oˣ, Module.length O (eig π ψ) ∧
      ∀ ψ : Q →* Oˣ, IsCompl (eig π ψ) (coeig π ψ) := by
  intro O Q N _ _ _ _ _ _ _ _ π hu
  classical
  letI := Fintype.ofFinite Q
  rw [Nat.card_eq_fintype_card] at hu
  obtain ⟨c, hc⟩ := hu.exists_left_inv
  refine ⟨?_, fun ψ => ⟨?_, ?_⟩⟩
  · rw [← Module.length_pi_of_fintype]
    let f : N →ₗ[O] (∀ ψ : Q →* Oˣ, eig π ψ) :=
      LinearMap.pi fun ψ => (prj π c ψ).codRestrict (eig π ψ) (prj_mem π c ψ)
    have hf : ∀ x ψ, ((f x ψ : eig π ψ) : N) = prj π c ψ x := fun _ _ => rfl
    refine (LinearEquiv.ofBijective f ⟨fun x y hxy => ?_, fun y => ?_⟩).length_eq
    · rw [← sum_prj π hc x, ← sum_prj π hc y]
      exact Finset.sum_congr rfl fun ψ _ => by rw [← hf, ← hf, hxy]
    · refine ⟨∑ χ, (y χ : N), funext fun ψ => Subtype.ext ?_⟩
      rw [hf, map_sum, Finset.sum_eq_single ψ, prj_self π hc ψ (y ψ).2]
      · intro χ _ hχ; exact prj_ne π c hχ.symm (y χ).2
      · simp
  · rw [Submodule.disjoint_def]
    intro x hx hy
    have hle : coeig π ψ ≤ LinearMap.ker (prj π c ψ) :=
      iSup_le fun g _ ⟨z, hz⟩ => by simp [← hz, prj_act]
    rw [← prj_self π hc ψ hx]; exact hle hy
  · rw [codisjoint_iff, eq_top_iff]
    intro x _
    rw [show x = prj π c ψ x - (prj π c ψ x - x) by abel]
    exact Submodule.sub_mem _ (Submodule.mem_sup_left (prj_mem π c ψ x))
      (Submodule.mem_sup_right (sub_prj_mem π hc ψ x))

private theorem lenEigLe_one {O N : Type} [CommRing O] [IsDomain O] [AddCommGroup N] [Module O N]
    (n : ℕ) (ζ : O) (hn : 0 < n) (hζ : IsPrimitiveRoot ζ n) (f : Module.End O N) (hf : f ^ n = 1)
    (P : Submodule O N) (hP : ∀ x ∈ P, f x ∈ P) :
    Module.length O P ≤ ∑ j : Fin n,
      Module.length O (P ⊓ LinearMap.ker (f - ζ ^ (j : ℕ) • (1 : Module.End O N)) : Submodule O N) := by
  have h1 : (f.restrict hP) ^ n = 1 := by ext x; rw [Module.End.pow_restrict]; simp [hf]
  refine (lenRoots O P n ζ hn hζ (f.restrict hP) h1).1.trans ?_
  rw [Finset.sum_range]
  refine Finset.sum_le_sum fun j _ => Module.length_le_of_injective
    (LinearMap.codRestrict _ (P.subtype ∘ₗ Submodule.subtype _)
      fun x => ⟨x.1.2, congrArg Subtype.val (LinearMap.mem_ker.1 x.2)⟩)
    fun _ _ h => Subtype.ext (Subtype.ext (congrArg (fun z : ↥(P ⊓ LinearMap.ker (f - ζ ^ (j : ℕ) • (1 : Module.End O N))) => (z.1 : N)) h))

private theorem lenEigLe_many {O N : Type} [CommRing O] [IsDomain O] [AddCommGroup N] [Module O N]
    (k : ℕ) :
    ∀ (n : Fin k → ℕ) (ζ : Fin k → O), (∀ i, 0 < n i) → (∀ i, IsPrimitiveRoot (ζ i) (n i)) →
      ∀ f : Fin k → Module.End O N, (∀ i, f i ^ n i = 1) → (∀ i j, f i * f j = f j * f i) →
      ∀ P : Submodule O N, (∀ i, ∀ x ∈ P, f i x ∈ P) →
      Module.length O P ≤ ∑ a : (∀ i, Fin (n i)),
        Module.length O (P ⊓ ⨅ i, LinearMap.ker (f i - ζ i ^ (a i : ℕ) • (1 : Module.End O N)) : Submodule O N) := by
  induction k with
  | zero =>
    intro n ζ _ _ f _ _ P _
    rw [Fintype.sum_unique, iInf_of_empty, inf_top_eq]
  | succ k ih =>
    intro n ζ hn hζ f hf hc P hP
    refine (lenEigLe_one (n 0) (ζ 0) (hn 0) (hζ 0) (f 0) (hf 0) P (hP 0)).trans ?_
    rw [← (Fin.consEquiv fun i => Fin (n i)).sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_le_sum fun j _ => ?_
    refine (ih (fun i => n i.succ) (fun i => ζ i.succ) (fun i => hn _) (fun i => hζ _)
      (fun i => f i.succ) (fun i => hf _) (fun i j => hc _ _) _ ?_).trans (le_of_eq ?_)
    · intro i x hx
      refine ⟨hP _ x hx.1, ?_⟩
      have h2 : f 0 x = ζ 0 ^ (j : ℕ) • x := by simpa [sub_eq_zero] using hx.2
      have h3 : f 0 (f i.succ x) = ζ 0 ^ (j : ℕ) • f i.succ x := by
        rw [← Module.End.mul_apply, hc, Module.End.mul_apply, h2, map_smul]
      simpa [sub_eq_zero] using h3
    · refine Finset.sum_congr rfl fun a _ => ?_
      have : (P ⊓ LinearMap.ker (f 0 - ζ 0 ^ (j : ℕ) • (1 : Module.End O N))) ⊓
          ⨅ i : Fin k, LinearMap.ker (f i.succ - ζ i.succ ^ (a i : ℕ) • (1 : Module.End O N)) =
          P ⊓ ⨅ i, LinearMap.ker (f i - ζ i ^
            (((Fin.consEquiv fun i => Fin (n i)) (j, a) i : Fin (n i)) : ℕ) • (1 : Module.End O N)) := by
        ext x; simp only [Submodule.mem_inf, Submodule.mem_iInf, Fin.forall_fin_succ, and_assoc]; rfl
      rw [this]

private theorem lenEigLe_gen (Q : Type) [CommGroup Q] [Finite Q] :
    ∃ (k : ℕ) (n : Fin k → ℕ) (g : Fin k → Q), (∀ i, 0 < n i) ∧ (∀ i, orderOf (g i) = n i) ∧
      Submonoid.closure (Set.range g) = ⊤ ∧
      ∀ (C : Type) [CommGroup C] (u : Fin k → C), (∀ i, u i ^ n i = 1) →
        ∃ ψ : Q →* C, ∀ i, ψ (g i) = u i := by
  classical
  obtain ⟨ι, _, n, hn, ⟨e⟩⟩ := CommGroup.equiv_prod_multiplicative_zmod_of_finite Q
  let σ := (Fintype.equivFin ι).symm
  haveI : ∀ i, NeZero (n i) := fun i => ⟨by have := hn i; omega⟩
  refine ⟨_, fun i => n (σ i), fun i => e.symm (Pi.mulSingle (σ i) (Multiplicative.ofAdd 1)),
    fun i => zero_lt_one.trans (hn (σ i)), fun i => ?_, ?_, ?_⟩
  · rw [MulEquiv.orderOf_eq]
    have := orderOf_injective (MonoidHom.mulSingle (fun i => Multiplicative (ZMod (n i))) (σ i))
      (Pi.mulSingle_injective (M := fun i => Multiplicative (ZMod (n i))) (σ i)) (Multiplicative.ofAdd 1)
    rw [MonoidHom.mulSingle_apply] at this
    rw [this, orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_one]
  · rw [eq_top_iff]; intro q _
    obtain ⟨y, rfl⟩ := e.symm.surjective q
    rw [← Finset.univ_prod_mulSingle y, map_prod]
    refine Submonoid.prod_mem _ fun i _ => ?_
    obtain ⟨i, rfl⟩ := σ.surjective i
    have : y (σ i) = Multiplicative.ofAdd (1 : ZMod (n (σ i))) ^ (y (σ i)).toAdd.val := by
      rw [← ofAdd_nsmul]; simp
    rw [this, Pi.mulSingle_pow, map_pow]
    exact Submonoid.pow_mem _ (Submonoid.subset_closure (Set.mem_range_self i)) _
  · intro C _ u hu
    have hu' : ∀ i, u (σ.symm i) ^ n i = 1 := fun i => by simpa using hu (σ.symm i)
    refine ⟨(∏ i, (AddChar.zmodChar (n i) (hu' i)).toMonoidHom.comp
      (Pi.evalMonoidHom (fun i => Multiplicative (ZMod (n i))) i)).comp e.toMonoidHom, fun i => ?_⟩
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply,
      MonoidHom.finsetProd_apply, Pi.evalMonoidHom_apply]
    rw [Finset.prod_eq_single (σ i)]
    · haveI : Fact (1 < n (σ i)) := ⟨hn _⟩
      simp [AddChar.zmodChar_apply, ZMod.val_one]
    · intro j _ hj; rw [Pi.mulSingle_eq_of_ne hj, map_one]
    · simp

theorem lenEigLe :
    ∀ (O Q N : Type) [CommRing O] [IsDomain O] [CommGroup Q] [Finite Q]
      [HasEnoughRootsOfUnity O (Monoid.exponent Q)] [Fintype (Q →* Oˣ)]
      [AddCommGroup N] [Module O N] (π : Representation O Q N),
      Module.length O N ≤ ∑ ψ : Q →* Oˣ, Module.length O (eig π ψ) := by
  intro O Q N _ _ _ _ _ _ _ _ π
  classical
  obtain ⟨k, n, g, hn, hg, hcl, hψ⟩ := lenEigLe_gen Q
  have hζ : ∀ i, ∃ ζ : Oˣ, IsPrimitiveRoot ζ (n i) := fun i => by
    obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot O (Monoid.exponent Q)
    have he : 0 < Monoid.exponent Q := Nat.pos_of_ne_zero Monoid.exponent_ne_zero_of_finite
    obtain ⟨m, hm⟩ : n i ∣ Monoid.exponent Q := hg i ▸ Monoid.order_dvd_exponent (g i)
    exact ⟨_, (hz.pow he (hm.trans (mul_comm _ _))).isUnit_unit (hn i).ne'⟩
  choose ζ hζ using hζ
  have h1 := lenEigLe_many k n (fun i => (ζ i : O)) hn (fun i => IsPrimitiveRoot.coe_units_iff.2 (hζ i))
    (fun i => π (g i)) (fun i => by rw [← map_pow, ← hg i, pow_orderOf_eq_one, map_one])
    (fun i j => by rw [← map_mul, mul_comm, map_mul]) ⊤ (fun _ _ _ => trivial)
  have h2 : ∀ a : (∀ i, Fin (n i)), ∃ ψ : Q →* Oˣ, ∀ i, ψ (g i) = ζ i ^ (a i : ℕ) := fun a =>
    hψ Oˣ _ fun i => by rw [← pow_mul, mul_comm, pow_mul, (hζ i).pow_eq_one, one_pow]
  choose ψ hψ' using h2
  have hinj : Function.Injective ψ := fun a b h => funext fun i => Fin.ext <|
    (hζ i).pow_inj (a i).2 (b i).2 (by rw [← hψ', ← hψ', h])
  rw [Module.length_top] at h1
  refine h1.trans (Finset.sum_le_sum (fun a _ => ?_) |>.trans
    ((Finset.sum_image (f := fun χ => Module.length O (eig π χ)) fun _ _ _ _ h => hinj h).symm.le.trans
      (Finset.sum_le_sum_of_subset (Finset.subset_univ _))))
  refine Module.length_le_of_injective (Submodule.inclusion ?_) (Submodule.inclusion_injective _)
  intro x hx
  rw [mem_eig]; intro q
  have hq : q ∈ Submonoid.closure (Set.range g) := hcl ▸ Submonoid.mem_top q
  induction hq using Submonoid.closure_induction with
  | mem q hq =>
    obtain ⟨i, rfl⟩ := hq
    have := (Submodule.mem_iInf _).1 hx.2 i
    rw [hψ']; simpa [sub_eq_zero] using this
  | one => simp
  | mul p q _ _ hp hq =>
    rw [map_mul, Module.End.mul_apply, hq, map_smul, hp, map_mul, Units.val_mul, smul_smul, mul_comm]

theorem lenEigVia :
    ∀ (O W Q N : Type) [CommRing O] [IsDomain O] [Group W] [CommGroup Q] [Finite Q]
      [HasEnoughRootsOfUnity O (Monoid.exponent Q)] [Fintype (Q →* Oˣ)]
      [AddCommGroup N] [Module O N] (π : Representation O W N) (p : W →* Q),
      Function.Surjective p → (∀ g, p g = 1 → ∀ x, π g x = x) →
      Module.length O N ≤ ∑ ψ : Q →* Oˣ, Module.length O (eig π (ψ.comp p)) ∧
      (IsUnit (Nat.card Q : O) → Module.length O N = ∑ ψ : Q →* Oˣ, Module.length O (eig π (ψ.comp p))) := by
  intro O W Q N _ _ _ _ _ _ _ _ _ π p hp hfix
  have hker : p.ker ≤ MonoidHom.ker π := fun g hg =>
    MonoidHom.mem_ker.mpr (LinearMap.ext (hfix g (MonoidHom.mem_ker.mp hg)))
  let e := QuotientGroup.quotientKerEquivOfSurjective p hp
  let π' : Representation O Q N := (QuotientGroup.lift p.ker π hker).comp e.symm.toMonoidHom
  have hπ' : ∀ g, π' (p g) = π g := fun g => by
    have he : e.symm (p g) = (g : W ⧸ p.ker) := by rw [MulEquiv.symm_apply_eq]; rfl
    show QuotientGroup.lift p.ker π hker (e.symm (p g)) = π g
    rw [he, QuotientGroup.lift_mk]
  have heig : ∀ ψ : Q →* Oˣ, eig π (ψ.comp p) = eig π' ψ := fun ψ => by
    ext x; simp only [mem_eig]
    exact ⟨fun h q => by obtain ⟨g, rfl⟩ := hp q; rw [hπ']; exact h g,
      fun h g => by rw [← hπ']; exact h (p g)⟩
  have hsum : ∑ ψ : Q →* Oˣ, Module.length O (eig π (ψ.comp p)) =
      ∑ ψ : Q →* Oˣ, Module.length O (eig π' ψ) :=
    Finset.sum_congr rfl fun ψ _ => congrArg (fun S : Submodule O N => Module.length O S) (heig ψ)
  rw [hsum]
  exact ⟨lenEigLe O Q N π', fun hu => (lenEigEq O Q N π' hu).1⟩

theorem lenEigSign :
    ∀ (O W Q N : Type) [CommRing O] [IsDomain O] [Group W] [CommGroup Q] [Finite Q]
      [HasEnoughRootsOfUnity O (Monoid.exponent Q)] [Fintype (Q →* Oˣ)]
      [AddCommGroup N] [Module O N] (π : Representation O W N) (p : W →* Q),
      Function.Surjective p → (∀ g, p g = 1 → ∀ x, π g x = x) → IsUnit (2 : O) →
      ∀ (c : W) (s : Oˣ), p c * p c = 1 → s * s = 1 → ∀ T : Finset (Q →* Oˣ),
      (∀ ψ, ψ (p c) = s → ψ ∈ T) →
      Module.length O (Module.End.eigenspace (π c) (s : O)) ≤
        ∑ ψ ∈ T, Module.length O (eig π (ψ.comp p)) := by
  intro O W Q N _ _ _ _ _ _ _ _ _ π p hp hker h2 c s hc hs T hT
  have hcomm : ∀ (g : W) (x : N), π g (π c x) = π c (π g x) := fun g x => by
    have hk : p ((c * g)⁻¹ * (g * c)) = 1 := by
      rw [map_mul, map_inv, map_mul, map_mul, mul_comm (p g) (p c), inv_mul_cancel]
    have e1 : g * c = (c * g) * ((c * g)⁻¹ * (g * c)) := by group
    rw [show π g (π c x) = π (g * c) x from by rw [map_mul]; rfl,
      show π c (π g x) = π (c * g) x from by rw [map_mul]; rfl, e1, map_mul, Module.End.mul_apply,
      hker _ hk]
  have hE : ∀ g, Module.End.eigenspace (π c) (s : O) ≤
      (Module.End.eigenspace (π c) (s : O)).comap (π g) := fun g x hx => by
    rw [Submodule.mem_comap, Module.End.mem_eigenspace_iff] at *
    rw [← hcomm, hx, map_smul]
  let πE := π.subrepresentation _ hE
  obtain ⟨hlen, -⟩ := lenEigVia O W Q _ πE p hp fun g hg x => Subtype.ext (hker g hg x)
  refine hlen.trans ?_
  have hzero : ∀ ψ : Q →* Oˣ, ψ ∉ T → Module.length O (eig πE (ψ.comp p)) = 0 := fun ψ hψ => by
    have hne : ψ (p c) ≠ s := fun h => hψ (hT ψ h)
    have hu : IsUnit ((s : O) - (ψ (p c) : O)) := by
      have a : (s : O) * s = 1 := by rw [← Units.val_mul, hs, Units.val_one]
      have b : (ψ (p c) : O) * ψ (p c) = 1 := by
        rw [← Units.val_mul, ← map_mul, hc, map_one, Units.val_one]
      rcases mul_eq_zero.mp (show ((s : O) - ψ (p c)) * ((s : O) + ψ (p c)) = 0 by
          linear_combination a - b) with h | h
      · exact absurd (Units.ext (sub_eq_zero.mp h)).symm hne
      · rw [show (s : O) - ψ (p c) = 2 * s by linear_combination (-1 : O) * h]; exact h2.mul s.isUnit
    have key : ∀ y : eig πE (ψ.comp p), y = 0 := fun y => by
      have h1 : π c y.1.1 = (ψ (p c) : O) • y.1.1 := congrArg Subtype.val ((mem_eig.mp y.2) c)
      have h2' : π c y.1.1 = (s : O) • y.1.1 := Module.End.mem_eigenspace_iff.mp y.1.2
      exact Subtype.ext (Subtype.ext (hu.smul_eq_zero.mp (by rw [sub_smul, ← h1, ← h2', sub_self])))
    rw [Module.length_eq_zero_iff]
    exact ⟨fun a b => (key a).trans (key b).symm⟩
  have hmono : ∀ ψ : Q →* Oˣ,
      Module.length O (eig πE (ψ.comp p)) ≤ Module.length O (eig π (ψ.comp p)) := fun ψ =>
    Module.length_le_of_injective
      (LinearMap.codRestrict (eig π (ψ.comp p))
        ((Module.End.eigenspace (π c) (s : O)).subtype ∘ₗ (eig πE (ψ.comp p)).subtype)
        fun y => mem_eig.mpr fun g => congrArg Subtype.val ((mem_eig.mp y.2) g))
      fun _ _ hab => Subtype.ext (Subtype.ext (congrArg (fun z : eig π (ψ.comp p) => (z : N)) hab))
  rw [← Finset.sum_subset (Finset.subset_univ T) (fun ψ _ hψ => hzero ψ hψ)]
  exact Finset.sum_le_sum fun ψ _ => hmono ψ

end EigenLengthBounds

end TransportShaModelAndSign

/-! ## Section 5: Base-Change Coordinates, `selBase`, `selBaseEig`, `qoFacts`, `qoBase`, `qoExt`, `shaDecompSign` -/

section BaseChangeAndQO

section AlgBaseChange

variable {R O ι N N' : Type} [CommRing R] [CommRing O] [Algebra R O] [Fintype ι] [AddCommGroup N]
  [Module R N] [AddCommGroup N'] [Module O N'] [Module R N'] [IsScalarTower R O N']

def coordSum (b : Module.Basis ι R O) (j : N →ₗ[R] N') : (ι → N) →ₗ[R] N' where
  toFun x := ∑ i, b i • j (x i)
  map_add' _ _ := by simp [Finset.sum_add_distrib]
  map_smul' r x := by simp only [Finset.smul_sum, Pi.smul_apply, map_smul]; refine Finset.sum_congr rfl fun i _ => smul_comm _ _ _

theorem coordSum_apply (b : Module.Basis ι R O) (j : N →ₗ[R] N') (x : ι → N) :
    coordSum b j x = ∑ i, b i • j (x i) := rfl

theorem isBaseChange_iff_coordSum (b : Module.Basis ι R O) (j : N →ₗ[R] N') :
    IsBaseChange O j ↔ Function.Bijective (coordSum b j) := by
  classical
  let e : (ι → N) ≃ₗ[R] O ⊗[R] N :=
    (Finsupp.linearEquivFunOnFinite R N ι).symm ≪≫ₗ (TensorProduct.equivFinsuppOfBasisLeft b).symm
  have he : ∀ x, e x = ∑ i, b i ⊗ₜ x i := fun x => by
    simp [e, TensorProduct.equivFinsuppOfBasisLeft_symm_apply, Finsupp.sum_fintype]
  unfold IsBaseChange IsTensorProduct
  rw [← Function.Bijective.of_comp_iff _ e.bijective]
  refine iff_of_eq (congrArg _ (funext fun x => ?_))
  simp [he, coordSum_apply]

theorem isBaseChange_restrict (b : Module.Basis ι R O) {j : N →ₗ[R] N'} (hj : IsBaseChange O j)
    (P : Submodule R N) (P' : Submodule O N') (h : ∀ x, coordSum b j x ∈ P' ↔ ∀ i, x i ∈ P)
    (j' : P →ₗ[R] P') (hj' : ∀ x, (j' x : N') = j x) : IsBaseChange O j' := by
  rw [isBaseChange_iff_coordSum b] at hj ⊢
  have e : ∀ x : ι → P, (coordSum b j' x : N') = coordSum b j fun i => x i := fun x => by
    simp [coordSum_apply, hj']
  refine ⟨fun x y hxy => funext fun i => Subtype.ext
    (congrFun (hj.1 ((e x).symm.trans ((congrArg Subtype.val hxy).trans (e y)))) i),
    fun y => ?_⟩
  obtain ⟨x, hx⟩ := hj.2 y
  exact ⟨fun i => ⟨x i, (h x).1 (hx ▸ y.2) i⟩, Subtype.ext ((e _).trans hx)⟩

theorem length_of_isBaseChange [IsLocalRing R] [IsLocalRing O] [IsLocalHom (algebraMap R O)]
    [Module.Flat R O] {j : N →ₗ[R] N'} (hj : IsBaseChange O j) :
    Module.length O N' =
      Module.length R N * Module.length O (O ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R O)) := by
  rw [← hj.equiv.length_eq, IsLocalRing.length_baseChange]

theorem map_coordSum (b : Module.Basis ι R O) (j : N →ₗ[R] N') (f : N → N) (f' : N' →ₗ[O] N')
    (h : ∀ x, j (f x) = f' (j x)) (x : ι → N) :
    f' (coordSum b j x) = coordSum b j fun i => f (x i) := by
  simp [coordSum_apply, h]

end AlgBaseChange

section CohBaseChange

variable {R G M : Type} [CommRing R] [Group G] [TopologicalSpace G] [AddCommGroup M] [Module R M]
  [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M] [DiscreteTopology M]
  {O M' : Type} [CommRing O] [Algebra R O] [AddCommGroup M'] [Module O M'] [Module R M']
  [IsScalarTower R O M'] [TopologicalSpace M'] [IsTopologicalAddGroup M'] [ContinuousConstSMul O M']
  (ρ : Representation R G M) (ρ' : Representation O G M') (j : M →ₗ[R] M')
  (hj : ∀ g m, j (ρ g m) = ρ' g (j m)) (U : Subgroup G)

def continuousCocycleMap : Z1U ρ U →ₗ[R] Z1U ρ' U where
  toFun z := ⟨fun u => j (z.1 u), (continuous_of_discreteTopology (f := j)).comp z.2.1, fun g h => by
    show j _ = j _ + ρ' g (j _); rw [z.2.2, map_add, ← hj]; rfl⟩
  map_add' _ _ := Subtype.ext (funext fun _ => map_add j _ _)
  map_smul' _ _ := Subtype.ext (funext fun _ => map_smul j _ _)

theorem continuousCocycleMap_apply (z : Z1U ρ U) (u : U) :
    (continuousCocycleMap ρ ρ' j hj U z).1 u = j (z.1 u) := rfl

def h1Map : H1U ρ U →ₗ[R] H1U ρ' U :=
  Submodule.liftQ _ (((Submodule.mkQ _).restrictScalars R).comp (continuousCocycleMap ρ ρ' j hj U))
    fun z hz => by
      obtain ⟨m, hm⟩ := (mem_B1 _ _).1 hz
      refine (Submodule.Quotient.mk_eq_zero _).2 ((mem_B1 _ _).2 ⟨j m, fun u => ?_⟩)
      have e := hm u; simp only [Submodule.coe_subtype, MonoidHom.comp_apply, Subgroup.coe_subtype] at e
      show j (z.1 u) = ρ' u (j m) - j m
      rw [e, map_sub, hj]

theorem h1Map_mk (z : Z1U ρ U) :
    h1Map ρ ρ' j hj U (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk (continuousCocycleMap ρ ρ' j hj U z) := rfl

theorem h1Map_mem_locSel (𝒟 : Set (Subgroup G)) {x : H1U ρ U} (hx : x ∈ LocSel ρ U 𝒟) :
    h1Map ρ ρ' j hj U x ∈ LocSel ρ' U 𝒟 := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [h1Map_mk, mk_mem_locSel]
  intro D hD
  obtain ⟨m, hm⟩ := mk_mem_locSel.1 hx D hD
  exact ⟨j m, fun u hu => by rw [continuousCocycleMap_apply, hm u hu, map_sub, hj]⟩

def selMap (𝒟 : Set (Subgroup G)) : LocSel ρ U 𝒟 →ₗ[R] LocSel ρ' U 𝒟 where
  toFun x := ⟨h1Map ρ ρ' j hj U x, h1Map_mem_locSel ρ ρ' j hj U 𝒟 x.2⟩
  map_add' _ _ := Subtype.ext (by simp)
  map_smul' _ _ := Subtype.ext (by simp)

variable {ι : Type} [Fintype ι] (b : Module.Basis ι R O)

theorem coordSum_z1Map (z : ι → Z1U ρ U) (u : U) :
    (coordSum b (continuousCocycleMap ρ ρ' j hj U) z).1 u = coordSum b j fun i => (z i).1 u := by
  simp [coordSum_apply, continuousCocycleMap_apply]

theorem coordSum_h1Map (z : ι → Z1U ρ U) :
    coordSum b (h1Map ρ ρ' j hj U) (fun i => Submodule.Quotient.mk (z i)) =
      Submodule.Quotient.mk (coordSum b (continuousCocycleMap ρ ρ' j hj U) z) := by
  simp only [coordSum_apply, ← Submodule.mkQ_apply, map_sum, map_smul]; rfl

include hj in
theorem exists_cob_iff (hb : IsBaseChange O j) (p : U → Prop) (z : ι → U → M) :
    (∃ m', ∀ u : U, p u → coordSum b j (fun i => z i u) = ρ' u m' - m') ↔
      ∀ i, ∃ m, ∀ u : U, p u → z i u = ρ u m - m := by
  rw [isBaseChange_iff_coordSum b] at hb
  have e : ∀ (u : U) (m : ι → M),
      ρ' u (coordSum b j m) - coordSum b j m = coordSum b j fun i => ρ u (m i) - m i := fun u m => by
    rw [map_coordSum b j (ρ u) (ρ' u) (hj u), ← map_sub]; rfl
  constructor
  · rintro ⟨m', hm⟩ i
    obtain ⟨m, rfl⟩ := hb.2 m'
    exact ⟨m i, fun u hu => congrFun (hb.1 ((hm u hu).trans (e u m))) i⟩
  · intro h
    choose m hm using h
    exact ⟨coordSum b j m, fun u hu => by rw [e]; exact congrArg _ (funext fun i => hm i u hu)⟩

theorem coordSum_z1Map_surjective [DiscreteTopology M'] (hb : IsBaseChange O j) :
    Function.Surjective (coordSum b (continuousCocycleMap ρ ρ' j hj U)) := by
  rw [isBaseChange_iff_coordSum b] at hb
  intro y
  let e := LinearEquiv.ofBijective _ hb
  have he : ∀ m, coordSum b j (e.symm m) = m := e.apply_symm_apply
  refine ⟨fun i => ⟨fun u => e.symm (y.1 u) i,
    (continuous_of_discreteTopology (f := fun m => e.symm m i)).comp y.2.1, fun g h => ?_⟩, ?_⟩
  · have : e.symm (y.1 (g * h)) = e.symm (y.1 g) + fun i => ρ g (e.symm (y.1 h) i) := by
      apply hb.1
      rw [map_add, ← map_coordSum b j (ρ g) (ρ' g) (hj g), he, he, he]
      exact y.2.2 g h
    exact congrFun this i
  · exact Subtype.ext (funext fun u => (coordSum_z1Map ρ ρ' j hj U b _ u).trans (he _))

include b in
private theorem isBaseChange_h1Map' [DiscreteTopology M'] (hb : IsBaseChange O j) :
    IsBaseChange O (h1Map ρ ρ' j hj U) := by
  rw [isBaseChange_iff_coordSum b]
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    choose z hz using fun i => Submodule.Quotient.mk_surjective _ (x i)
    obtain rfl : x = fun i => Submodule.Quotient.mk (z i) := funext fun i => (hz i).symm
    rw [coordSum_h1Map] at hx
    obtain ⟨m', hm'⟩ := (mem_B1 _ _).1 ((Submodule.Quotient.mk_eq_zero _).1 hx)
    funext i
    obtain ⟨m, hm⟩ := (exists_cob_iff ρ ρ' j hj U b hb (fun _ => True) fun i => (z i).1).1
      ⟨m', fun u _ => (coordSum_z1Map ρ ρ' j hj U b z u).symm.trans (hm' u)⟩ i
    exact (Submodule.Quotient.mk_eq_zero _).2 ((mem_B1 _ _).2 ⟨m, fun u => hm u trivial⟩)
  · intro y
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    obtain ⟨z, rfl⟩ := coordSum_z1Map_surjective ρ ρ' j hj U b hb y
    exact ⟨_, coordSum_h1Map ρ ρ' j hj U b z⟩

theorem coordSum_mem_locSel (hb : IsBaseChange O j) (𝒟 : Set (Subgroup G)) (x : ι → H1U ρ U) :
    coordSum b (h1Map ρ ρ' j hj U) x ∈ LocSel ρ' U 𝒟 ↔ ∀ i, x i ∈ LocSel ρ U 𝒟 := by
  choose z hz using fun i => Submodule.Quotient.mk_surjective _ (x i)
  obtain rfl : x = fun i => Submodule.Quotient.mk (z i) := funext fun i => (hz i).symm
  rw [coordSum_h1Map]
  simp only [mk_mem_locSel, coordSum_z1Map]
  rw [forall_comm]
  refine forall_congr' fun D => ?_
  rw [forall_comm]
  exact imp_congr_right fun _ => exists_cob_iff ρ ρ' j hj U b hb (fun u => u.1 ∈ D) fun i => (z i).1

omit [Fintype ι] in
theorem isBaseChange_h1Map [Module.Free R O] [Module.Finite R O] [DiscreteTopology M']
    (hb : IsBaseChange O j) : IsBaseChange O (h1Map ρ ρ' j hj U) :=
  isBaseChange_h1Map' ρ ρ' j hj U (Module.Free.chooseBasis R O) hb

omit [Fintype ι] in
theorem isBaseChange_selMap [Module.Free R O] [Module.Finite R O] [DiscreteTopology M']
    (hb : IsBaseChange O j) (𝒟 : Set (Subgroup G)) : IsBaseChange O (selMap ρ ρ' j hj U 𝒟) :=
  isBaseChange_restrict (Module.Free.chooseBasis R O) (isBaseChange_h1Map ρ ρ' j hj U hb) _ _
    (coordSum_mem_locSel ρ ρ' j hj U _ hb 𝒟) _ fun _ => rfl

end CohBaseChange

theorem selBase :
    ∀ (R G M : Type) [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
      [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M]
      [ContinuousConstSMul R M] [DiscreteTopology M] (ρ : Representation R G M) (O M' : Type)
      [CommRing O] [Algebra R O] [IsLocalRing R] [IsLocalRing O] [IsLocalHom (algebraMap R O)]
      [Module.Free R O] [Module.Finite R O] [AddCommGroup M'] [Module O M'] [Module R M']
      [IsScalarTower R O M'] [TopologicalSpace M'] [IsTopologicalAddGroup M']
      [ContinuousConstSMul O M'] [DiscreteTopology M'] (ρ' : Representation O G M')
      (j : M →ₗ[R] M'), IsBaseChange O j → (∀ g m, j (ρ g m) = ρ' g (j m)) →
      ∀ (U : Subgroup G) (𝒟 : Set (Subgroup G)),
      Module.length O (LocSel ρ' U 𝒟) =
        Module.length R (LocSel ρ U 𝒟) *
          Module.length O (O ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R O)) := by
  intro R G M _ _ _ _ _ _ _ _ _ _ ρ O M' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ρ' j hb hj U 𝒟
  exact length_of_isBaseChange (isBaseChange_selMap ρ ρ' j hj U hb 𝒟)

section SelBaseEigSection

section AbstractCoords

variable {R O ι : Type} [CommRing R] [CommRing O] [Algebra R O] [Fintype ι] (b : Module.Basis ι R O)
  {N N' : Type} [AddCommGroup N] [Module R N] [AddCommGroup N'] [Module O N']

private structure Coords (J : N →+ N') (C : ι → N' →+ N) : Prop where
  smul : ∀ (r : R) x, J (r • x) = algebraMap R O r • J x
  sum : ∀ y, ∑ i, b i • J (C i y) = y
  coord : ∀ i (o : O) x, C i (o • J x) = b.repr o i • x

variable {b} {J : N →+ N'} {C : ι → N' →+ N}

private theorem Coords.comm (h : Coords b J C) (f : N → N) (f' : N' →ₗ[O] N')
    (hf : ∀ x, J (f x) = f' (J x)) (i : ι) (y : N') : C i (f' y) = f (C i y) := by
  conv_lhs => rw [← h.sum y]
  simp only [map_sum, LinearMap.map_smul, ← hf, h.coord, Module.Basis.repr_self]
  rw [Finset.sum_eq_single i]
  · simp
  · intro k _ hk; rw [Finsupp.single_eq_of_ne hk.symm, zero_smul]
  · intro hi; exact absurd (Finset.mem_univ i) hi

private theorem Coords.length [IsLocalRing R] [IsLocalRing O] [IsLocalHom (algebraMap R O)]
    (h : Coords b J C) :
    Module.length O N' =
      Module.length R N * Module.length O (O ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R O)) := by
  classical
  haveI : Module.Free R O := Module.Free.of_basis b
  let F : O →+ N →+ N' :=
    { toFun := fun o => { toFun := fun x => o • J x, map_zero' := by simp, map_add' := fun _ _ => by simp [smul_add] }
      map_zero' := by ext; simp
      map_add' := fun _ _ => by ext; simp [add_smul] }
  let φ : O ⊗[R] N →+ N' := TensorProduct.liftAddHom F fun r o x => by
    show (r • o) • J x = o • J (r • x); rw [h.smul, smul_smul, Algebra.smul_def, mul_comm]
  have hφ : ∀ (o : O) (x : N), φ (o ⊗ₜ[R] x) = o • J x := fun o x => by
    simp [φ, F, TensorProduct.liftAddHom_tmul]
  let ψ : N' → O ⊗[R] N := fun y => ∑ i, b i ⊗ₜ[R] C i y
  have hψφ : ∀ t, ψ (φ t) = t := fun t => by
    induction t using TensorProduct.induction_on with
    | zero => simp [ψ]
    | tmul o x => simp only [ψ, hφ, h.coord, ← TensorProduct.smul_tmul, ← TensorProduct.sum_tmul, b.sum_repr]
    | add _ _ hs ht => simp only [ψ, map_add, TensorProduct.tmul_add, Finset.sum_add_distrib] at hs ht ⊢; rw [hs, ht]
  have hφψ : ∀ y, φ (ψ y) = y := fun y => by simp only [ψ, map_sum, hφ, h.sum]
  have hφs : ∀ (o : O) t, φ (o • t) = o • φ t := fun o t => by
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul o' x => rw [TensorProduct.smul_tmul', hφ, hφ, smul_eq_mul, mul_smul]
    | add _ _ hs ht => rw [smul_add, map_add, map_add, hs, ht, smul_add]
  let e : N' ≃ₗ[O] O ⊗[R] N :=
    { toFun := ψ, invFun := φ, left_inv := hφψ, right_inv := hψφ
      map_add' := fun _ _ => by simp [ψ, map_add, TensorProduct.tmul_add, Finset.sum_add_distrib]
      map_smul' := fun o y => by show ψ (o • y) = o • ψ y; conv_lhs => rw [← hφψ y, ← hφs, hψφ] }
  rw [e.length_eq, IsLocalRing.length_baseChange]

end AbstractCoords

section CohAddCoords

variable {G : Type} [Group G] [TopologicalSpace G]
  {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
  [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M] [DiscreteTopology M]
  {O M' : Type} [CommRing O] [AddCommGroup M'] [Module O M']
  [TopologicalSpace M'] [IsTopologicalAddGroup M'] [ContinuousConstSMul O M'] [DiscreteTopology M']
  (ρ : Representation R G M) (ρ' : Representation O G M') (u : M →+ M')
  (hu : ∀ g m, u (ρ g m) = ρ' g (u m)) (U : Subgroup G)

private def zAddMap : Z1U ρ U →+ Z1U ρ' U where
  toFun f := ⟨u ∘ f.1, continuous_of_discreteTopology.comp f.2.1, fun g h => by
    simp only [Function.comp_apply, f.2.2 g h, map_add]; exact congrArg _ (hu _ _)⟩
  map_zero' := Subtype.ext (funext fun _ => map_zero u)
  map_add' _ _ := Subtype.ext (funext fun _ => map_add u _ _)

private def hAddMap : H1U ρ U →+ H1U ρ' U :=
  QuotientAddGroup.map (Submodule.toAddSubgroup _) (Submodule.toAddSubgroup _) (zAddMap ρ ρ' u hu U)
    fun f hf => by
      obtain ⟨m, hm⟩ := (mem_B1 _ _).1 hf
      refine (mem_B1 _ _).2 ⟨u m, fun g => ?_⟩
      have e := hm g; simp only [Submodule.coe_subtype, MonoidHom.comp_apply, Subgroup.coe_subtype] at e
      change u (f.1 g) = ρ' g (u m) - u m
      rw [e, map_sub, hu]

private theorem hAddMap_mk (z : Z1U ρ U) :
    hAddMap ρ ρ' u hu U (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk (zAddMap ρ ρ' u hu U z) := rfl

end CohAddCoords

private theorem exists_coords_of_isBaseChange {R O ι M M' : Type} [CommRing R] [CommRing O]
    [Algebra R O] [Fintype ι] (b : Module.Basis ι R O) [AddCommGroup M] [Module R M]
    [AddCommGroup M'] [Module O M'] [Module R M'] [IsScalarTower R O M'] (j : M →ₗ[R] M')
    (hj : IsBaseChange O j) :
    ∃ C : ι → M' →+ M, Coords b j.toAddMonoidHom C := by
  classical
  let F : ι → O →+ M →+ M := fun i =>
    { toFun := fun o => { toFun := fun x => b.repr o i • x, map_zero' := by simp, map_add' := fun _ _ => by simp [smul_add] }
      map_zero' := by ext; simp
      map_add' := fun _ _ => by ext; simp [add_smul] }
  have hF : ∀ i (r : R) (o : O) (x : M), F i (r • o) x = F i o (r • x) := fun i r o x => by
    show b.repr (r • o) i • x = b.repr o i • r • x
    rw [map_smul, Finsupp.smul_apply, smul_eq_mul, mul_comm, mul_smul]
  have hFt : ∀ i (o : O) (x : M), TensorProduct.liftAddHom (F i) (hF i) (o ⊗ₜ[R] x) = b.repr o i • x :=
    fun i o x => by simp [F, TensorProduct.liftAddHom_tmul]
  refine ⟨fun i => (TensorProduct.liftAddHom (F i) (hF i)).comp hj.equiv.symm.toLinearMap.toAddMonoidHom,
    fun r x => by simp [algebraMap_smul], fun y => ?_, fun i o x => ?_⟩
  · obtain ⟨t, rfl⟩ := hj.equiv.surjective y
    simp only [AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply]
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul o x =>
      simp only [hFt, IsBaseChange.equiv_tmul, map_smul, smul_comm (b _) (b.repr o _),
        ← smul_assoc, ← Finset.sum_smul, b.sum_repr]
    | add _ _ hs ht => simp only [map_add, smul_add, Finset.sum_add_distrib, hs, ht]
  · simp only [AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe, LinearEquiv.coe_coe]
    rw [← IsBaseChange.equiv_tmul hj, LinearEquiv.symm_apply_apply, hFt]

private theorem coords_restrict_to_submodules {R O ι : Type} [CommRing R] [CommRing O] [Algebra R O]
    [Fintype ι] {b : Module.Basis ι R O} {N N' : Type} [AddCommGroup N] [Module R N]
    [AddCommGroup N'] [Module O N'] {J : N →+ N'} {C : ι → N' →+ N} (h : Coords b J C)
    (P : Submodule R N) (P' : Submodule O N') (hJ : ∀ x ∈ P, J x ∈ P') (hC : ∀ i, ∀ y ∈ P', C i y ∈ P) :
    ∃ (J0 : P →+ P') (C0 : ι → P' →+ P), Coords b J0 C0 ∧
      (∀ x, (J0 x : N') = J x) ∧ (∀ i y, (C0 i y : N) = C i y) :=
  ⟨{ toFun := fun x => ⟨J x, hJ x x.2⟩, map_zero' := by ext; simp, map_add' := fun _ _ => by ext; simp },
   fun i => { toFun := fun y => ⟨C i y, hC i y y.2⟩, map_zero' := by ext; simp, map_add' := fun _ _ => by ext; simp },
   ⟨fun r x => Subtype.ext (by simp [h.smul]), fun y => Subtype.ext (by simp [h.sum]),
    fun i o x => Subtype.ext (by simp [h.coord])⟩, fun _ => rfl, fun _ _ => rfl⟩

private theorem selBaseEig_coords_H1 {G : Type} [Group G] [TopologicalSpace G]
    {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M] [DiscreteTopology M]
    {O M' : Type} [CommRing O] [Algebra R O] [AddCommGroup M'] [Module O M']
    [TopologicalSpace M'] [IsTopologicalAddGroup M'] [ContinuousConstSMul O M'] [DiscreteTopology M']
    {ι : Type} [Fintype ι] {b : Module.Basis ι R O} (ρ : Representation R G M)
    (ρ' : Representation O G M') (u : M →+ M') (hu : ∀ g m, u (ρ g m) = ρ' g (u m))
    {C : ι → M' →+ M} (h : Coords b u C) (hcomm : ∀ i g y, C i (ρ' g y) = ρ g (C i y)) :
    ∃ CH : (V : Subgroup G) → ι → H1U ρ' V →+ H1U ρ V,
      (∀ V, Coords b (hAddMap ρ ρ' u hu V) (CH V)) ∧
      (∀ (V' V : Subgroup G) (hV : V' ≤ V) i y, CH V' i (resU ρ' hV y) = resU ρ hV (CH V i y)) := by
  classical
  let CZ : (V : Subgroup G) → ι → Z1U ρ' V →+ Z1U ρ V := fun V i =>
    { toFun := fun f => ⟨fun g => C i (f.1 g), continuous_of_discreteTopology.comp f.2.1, fun g k => by
        dsimp only; rw [f.2.2 g k, map_add]; simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, hcomm]⟩
      map_zero' := Subtype.ext (funext fun _ => map_zero _)
      map_add' := fun _ _ => Subtype.ext (funext fun _ => map_add _ _ _) }
  let CH : (V : Subgroup G) → ι → H1U ρ' V →+ H1U ρ V := fun V i =>
    QuotientAddGroup.map (Submodule.toAddSubgroup _) (Submodule.toAddSubgroup _) (CZ V i) fun f hf => by
      obtain ⟨m, hm⟩ := (mem_B1 _ _).1 hf
      refine (mem_B1 _ _).2 ⟨C i m, fun g => ?_⟩
      have e := hm g; simp only [Submodule.coe_subtype, MonoidHom.comp_apply, Subgroup.coe_subtype] at e
      change C i (f.1 g) = ρ g (C i m) - C i m
      rw [e, map_sub, hcomm]
  refine ⟨CH, fun V => ⟨fun r x => ?_, fun x => ?_, fun i o x => ?_⟩, fun V' V hV i y => ?_⟩
  · obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [← Submodule.Quotient.mk_smul, hAddMap_mk, hAddMap_mk, ← Submodule.Quotient.mk_smul]
    exact congrArg _ (Subtype.ext (funext fun g => h.smul r (z.1 g)))
  · obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have key : (∑ i, b i • zAddMap ρ ρ' u hu V (CZ V i z)) = z := Subtype.ext (funext fun g => by
      simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply]
      exact h.sum (z.1 g))
    conv_rhs => rw [← key]
    show (∑ i, b i • Submodule.Quotient.mk (zAddMap ρ ρ' u hu V (CZ V i z))) = _
    simp only [← Submodule.Quotient.mk_smul]
    exact (map_sum (Submodule.mkQ _) _ _).symm
  · obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [hAddMap_mk, ← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul]
    exact congrArg _ (Subtype.ext (funext fun g => h.coord i o (z.1 g)))
  · obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y; rfl

private theorem resU_hAddMap_comm {G : Type} [Group G] [TopologicalSpace G]
    {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M] [DiscreteTopology M]
    {O M' : Type} [CommRing O] [AddCommGroup M'] [Module O M']
    [TopologicalSpace M'] [IsTopologicalAddGroup M'] [ContinuousConstSMul O M'] [DiscreteTopology M']
    (ρ : Representation R G M) (ρ' : Representation O G M') (u : M →+ M')
    (hu : ∀ g m, u (ρ g m) = ρ' g (u m)) (V' V : Subgroup G) (hV : V' ≤ V) (x : H1U ρ V) :
    resU ρ' hV (hAddMap ρ ρ' u hu V x) = hAddMap ρ ρ' u hu V' (resU ρ hV x) := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x; rfl

private theorem conjU_hAddMap_comm {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M] [DiscreteTopology M]
    {O M' : Type} [CommRing O] [AddCommGroup M'] [Module O M']
    [TopologicalSpace M'] [IsTopologicalAddGroup M'] [ContinuousConstSMul O M'] [DiscreteTopology M']
    (ρ : Representation R G M) (ρ' : Representation O G M') (u : M →+ M')
    (hu : ∀ g m, u (ρ g m) = ρ' g (u m)) (U : Subgroup G) [U.Normal] (g : G) (x : H1U ρ U) :
    conjU ρ' U g (hAddMap ρ ρ' u hu U x) = hAddMap ρ ρ' u hu U (conjU ρ U g x) := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  exact congrArg Submodule.Quotient.mk (Subtype.ext (funext fun w => (hu _ _).symm))

set_option maxHeartbeats 600000 in
theorem selBaseEig :
    ∀ (R G M : Type) [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
      [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M]
      [ContinuousConstSMul R M] [DiscreteTopology M] (ρ : Representation R G M) (O M' : Type)
      [CommRing O] [Algebra R O] [IsLocalRing R] [IsLocalRing O] [IsLocalHom (algebraMap R O)]
      [Module.Free R O] [Module.Finite R O] [AddCommGroup M'] [Module O M'] [Module R M']
      [IsScalarTower R O M'] [TopologicalSpace M'] [IsTopologicalAddGroup M']
      [ContinuousConstSMul O M'] [DiscreteTopology M'] (ρ' : Representation O G M')
      (j : M →ₗ[R] M'), IsBaseChange O j → (∀ g m, j (ρ g m) = ρ' g (j m)) →
      ∀ (U : Subgroup G) [U.Normal] (𝒟 : Set (Subgroup G)) (h𝒟 : ConjStable 𝒟),
      (∀ (W : Subgroup G) (ψ : W →* Rˣ),
        Module.length O (selEig ρ' U h𝒟 W ((Units.map (algebraMap R O).toMonoidHom).comp ψ)) =
          Module.length R (selEig ρ U h𝒟 W ψ) *
            Module.length O (O ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R O))) ∧
      ∀ (g : G) (s : R),
        Module.length O (Module.End.eigenspace (selRep ρ' U h𝒟 g) (algebraMap R O s)) =
          Module.length R (Module.End.eigenspace (selRep ρ U h𝒟 g) s) *
            Module.length O (O ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R O)) := by
  intro R G M _ _ _ _ _ _ _ _ _ _ ρ O M' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ρ' j hj hu U _ 𝒟 h𝒟
  classical
  let b := Module.Free.chooseBasis R O
  obtain ⟨C, hC⟩ := exists_coords_of_isBaseChange b j hj
  have hu' : ∀ g m, j.toAddMonoidHom (ρ g m) = ρ' g (j.toAddMonoidHom m) := hu
  have hcomm : ∀ i g y, C i (ρ' g y) = ρ g (C i y) := fun i g y =>
    Coords.comm hC (fun m => ρ g m) (ρ' g) (fun x => hu g x) i y
  obtain ⟨CH, hCH, hres⟩ := selBaseEig_coords_H1 ρ ρ' j.toAddMonoidHom hu' hC hcomm
  have hLJ : ∀ x ∈ LocSel ρ U 𝒟, hAddMap ρ ρ' j.toAddMonoidHom hu' U x ∈ LocSel ρ' U 𝒟 := fun x hx => by
    simp only [LocSel, Submodule.mem_iInf, LinearMap.mem_ker] at hx ⊢
    intro D hD; rw [resU_hAddMap_comm, hx D hD, map_zero]
  have hLC : ∀ i, ∀ y ∈ LocSel ρ' U 𝒟, CH U i y ∈ LocSel ρ U 𝒟 := fun i y hy => by
    simp only [LocSel, Submodule.mem_iInf, LinearMap.mem_ker] at hy ⊢
    intro D hD; rw [← hres, hy D hD, map_zero]
  obtain ⟨JL, CL, hL, hJL, -⟩ := coords_restrict_to_submodules (hCH U) _ _ hLJ hLC
  have hJconj : ∀ g x, JL (selRep ρ U h𝒟 g x) = selRep ρ' U h𝒟 g (JL x) := fun g x =>
    Subtype.ext (by rw [hJL]; exact (conjU_hAddMap_comm ρ ρ' _ hu' U g x.1).symm.trans (congrArg _ (hJL x).symm))
  have hCconj : ∀ i g y, CL i (selRep ρ' U h𝒟 g y) = selRep ρ U h𝒟 g (CL i y) := fun i g y =>
    Coords.comm hL (fun x => selRep ρ U h𝒟 g x) (selRep ρ' U h𝒟 g) (hJconj g) i y
  have hCs : ∀ i (s : R) y, CL i (algebraMap R O s • y) = s • CL i y := fun i s y =>
    Coords.comm hL (fun x => s • x) (algebraMap R O s • LinearMap.id) (fun x => by simp [hL.smul]) i y
  constructor
  · intro W ψ
    have hEJ : ∀ x ∈ selEig ρ U h𝒟 W ψ,
        JL x ∈ selEig ρ' U h𝒟 W ((Units.map (algebraMap R O).toMonoidHom).comp ψ) := fun x hx => by
      simp only [selEig, eig, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
        LinearMap.id_apply, MonoidHom.comp_apply, Subgroup.coe_subtype, sub_eq_zero, Units.coe_map,
        RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe] at hx ⊢
      intro w; rw [← hJconj, hx w, hL.smul]
    have hEC : ∀ i, ∀ y ∈ selEig ρ' U h𝒟 W ((Units.map (algebraMap R O).toMonoidHom).comp ψ),
        CL i y ∈ selEig ρ U h𝒟 W ψ := fun i y hy => by
      simp only [selEig, eig, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
        LinearMap.id_apply, MonoidHom.comp_apply, Subgroup.coe_subtype, sub_eq_zero, Units.coe_map,
        RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe] at hy ⊢
      intro w; rw [← hCconj, hy w, hCs]
    obtain ⟨_, _, hE, -, -⟩ := coords_restrict_to_submodules hL _ _ hEJ hEC
    exact Coords.length hE
  · intro g s
    have hEJ : ∀ x ∈ Module.End.eigenspace (selRep ρ U h𝒟 g) s,
        JL x ∈ Module.End.eigenspace (selRep ρ' U h𝒟 g) (algebraMap R O s) := fun x hx => by
      rw [Module.End.mem_eigenspace_iff] at hx ⊢; rw [← hJconj, hx, hL.smul]
    have hEC : ∀ i, ∀ y ∈ Module.End.eigenspace (selRep ρ' U h𝒟 g) (algebraMap R O s),
        CL i y ∈ Module.End.eigenspace (selRep ρ U h𝒟 g) s := fun i y hy => by
      rw [Module.End.mem_eigenspace_iff] at hy ⊢
      calc selRep ρ U h𝒟 g (CL i y) = CL i (selRep ρ' U h𝒟 g y) := (hCconj i g y).symm
        _ = CL i (algebraMap R O s • y) := congrArg _ hy
        _ = s • CL i y := hCs i s y
    obtain ⟨_, _, hE, -, -⟩ := coords_restrict_to_submodules hL
      (Module.End.eigenspace (selRep ρ U h𝒟 g) s)
      (Module.End.eigenspace (selRep ρ' U h𝒟 g) (algebraMap R O s)) hEJ hEC
    exact Coords.length hE

end SelBaseEigSection

section QoFactsSection

private theorem qo_inj (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] :
    Function.Injective (algebraMap ℤ_[l] O) :=
  dvr_algebraMap_inj (l := l) O

private theorem exists_padicInt_multiple_of_ne_zero (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O]
    [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] (b : O)
    (hb : b ≠ 0) : ∃ c : ℤ_[l], c ≠ 0 ∧ ∃ d : O, algebraMap ℤ_[l] O c = b * d := by
  have hint : Algebra.IsIntegral ℤ_[l] O := Algebra.IsIntegral.of_finite ℤ_[l] O
  have h := Ideal.IsIntegral.comap_ne_bot ℤ_[l] (show Ideal.span {b} ≠ ⊥ by rwa [Ne, Ideal.span_singleton_eq_bot])
  obtain ⟨c, hc, hc0⟩ := (Submodule.ne_bot_iff _).mp h
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.mp (Ideal.mem_comap.mp hc)
  exact ⟨c, hc0, d, by rw [← hd, mul_comm]⟩

private theorem fractionRing_exists_padicInt_clear_denom (l : ℕ) [Fact l.Prime] (O : Type)
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O]
    [Module.Finite ℤ_[l] O] (x : FractionRing O) :
    ∃ o : O, ∃ c : ℤ_[l], c ≠ 0 ∧
      x * algebraMap ℤ_[l] (FractionRing O) c = algebraMap O (FractionRing O) o := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := O) x
  obtain ⟨c, hc, d, hd⟩ := exists_padicInt_multiple_of_ne_zero l O b (nonZeroDivisors.ne_zero hb)
  have hb' : algebraMap O (FractionRing O) b ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  refine ⟨a * d, c, hc, ?_⟩
  rw [IsScalarTower.algebraMap_apply ℤ_[l] O (FractionRing O), hd, map_mul, map_mul]
  field_simp

private theorem tmul_qz_inv_mul_eq (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O]
    (o : O) (c d : ℤ_[l]) (hd : d ≠ 0) :
    (o ⊗ₜ[ℤ_[l]] (Submodule.Quotient.mk (algebraMap ℤ_[l] ℚ_[l] c)⁻¹ : QZ l)) =
      (o * algebraMap ℤ_[l] O d) ⊗ₜ[ℤ_[l]]
        (Submodule.Quotient.mk (algebraMap ℤ_[l] ℚ_[l] (c * d))⁻¹ : QZ l) := by
  have hd' : algebraMap ℤ_[l] ℚ_[l] d ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective ℤ_[l] ℚ_[l])).mpr hd
  rw [mul_comm o, ← Algebra.smul_def, TensorProduct.smul_tmul, ← Submodule.Quotient.mk_smul,
    Algebra.smul_def, map_mul]
  congr 2
  rw [mul_inv, mul_comm (algebraMap ℤ_[l] ℚ_[l] c)⁻¹, ← mul_assoc, mul_inv_cancel₀ hd', one_mul]

private theorem qo_equiv (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] :
    Nonempty (QO l O ≃ₗ[O] (FractionRing O ⧸ (1 : Submodule O (FractionRing O)))) := by
  classical
  have hinjK : Function.Injective (algebraMap ℤ_[l] (FractionRing O)) := by
    rw [IsScalarTower.algebraMap_eq ℤ_[l] O (FractionRing O), RingHom.coe_comp]
    exact (IsFractionRing.injective O (FractionRing O)).comp (qo_inj l O)
  let ι : ℚ_[l] →+* FractionRing O := IsFractionRing.lift hinjK
  have hι : ∀ z : ℤ_[l], ι (algebraMap ℤ_[l] ℚ_[l] z) = algebraMap ℤ_[l] (FractionRing O) z :=
    fun z => IsFractionRing.lift_algebraMap hinjK z
  let g₁ : ℚ_[l] →ₗ[ℤ_[l]] FractionRing O :=
    { toFun := ι, map_add' := map_add ι
      map_smul' := fun z q => by simp only [RingHom.id_apply, Algebra.smul_def, map_mul, hι] }
  let g₂ : ℚ_[l] →ₗ[ℤ_[l]] (FractionRing O ⧸ (1 : Submodule O (FractionRing O))) :=
    ((1 : Submodule O (FractionRing O)).mkQ.restrictScalars ℤ_[l]).comp g₁
  have hg₂ : ZlSub l ≤ LinearMap.ker g₂ := by
    rintro _ ⟨z, rfl⟩
    rw [LinearMap.mem_ker]
    show (Submodule.Quotient.mk (ι (algebraMap ℤ_[l] ℚ_[l] z)) :
      FractionRing O ⧸ (1 : Submodule O (FractionRing O))) = 0
    rw [Submodule.Quotient.mk_eq_zero, hι, Submodule.mem_one]
    exact ⟨algebraMap ℤ_[l] O z, (IsScalarTower.algebraMap_apply ℤ_[l] O _ z).symm⟩
  let g₃ : QZ l →ₗ[ℤ_[l]] (FractionRing O ⧸ (1 : Submodule O (FractionRing O))) :=
    (ZlSub l).liftQ g₂ hg₂
  let φ : QO l O →ₗ[O] (FractionRing O ⧸ (1 : Submodule O (FractionRing O))) :=
    LinearMap.liftBaseChange O g₃
  have hφ : ∀ (a : O) (r : ℚ_[l]), φ (a ⊗ₜ[ℤ_[l]] (Submodule.Quotient.mk r : QZ l)) =
      a • (Submodule.Quotient.mk (ι r) : FractionRing O ⧸ (1 : Submodule O (FractionRing O))) :=
    fun a r => LinearMap.liftBaseChange_tmul O g₃ a _
  choose o c hc hx using fractionRing_exists_padicInt_clear_denom l O
  let ψ₀ : FractionRing O → QO l O := fun x =>
    (o x ⊗ₜ[ℤ_[l]] (Submodule.Quotient.mk (algebraMap ℤ_[l] ℚ_[l] (c x))⁻¹ : QZ l))
  have spec : ∀ (x : FractionRing O) (p : O) (e : ℤ_[l]), e ≠ 0 →
      x * algebraMap ℤ_[l] (FractionRing O) e = algebraMap O (FractionRing O) p →
      ψ₀ x = (p ⊗ₜ[ℤ_[l]] (Submodule.Quotient.mk (algebraMap ℤ_[l] ℚ_[l] e)⁻¹ : QZ l)) := by
    intro x p e he hxe
    show (o x ⊗ₜ[ℤ_[l]] (Submodule.Quotient.mk (algebraMap ℤ_[l] ℚ_[l] (c x))⁻¹ : QZ l)) = _
    rw [tmul_qz_inv_mul_eq l O (o x) (c x) e he, tmul_qz_inv_mul_eq l O p e (c x) (hc x), mul_comm e (c x)]
    refine congrArg (· ⊗ₜ[ℤ_[l]] _) (IsFractionRing.injective O (FractionRing O) ?_)
    simp only [map_mul, ← IsScalarTower.algebraMap_apply, ← hx x, ← hxe]; ring
  let ψL : FractionRing O →ₗ[O] QO l O :=
    { toFun := ψ₀
      map_add' := fun x y => by
        rw [spec (x + y) (o x * algebraMap ℤ_[l] O (c y) + o y * algebraMap ℤ_[l] O (c x))
          (c x * c y) (mul_ne_zero (hc x) (hc y)) (by
            simp only [map_add, map_mul, ← IsScalarTower.algebraMap_apply, ← hx x, ← hx y]; ring),
          TensorProduct.add_tmul]
        show _ = (o x ⊗ₜ[ℤ_[l]] (Submodule.Quotient.mk (algebraMap ℤ_[l] ℚ_[l] (c x))⁻¹ : QZ l)) +
          (o y ⊗ₜ[ℤ_[l]] (Submodule.Quotient.mk (algebraMap ℤ_[l] ℚ_[l] (c y))⁻¹ : QZ l))
        rw [tmul_qz_inv_mul_eq l O (o x) (c x) (c y) (hc y),
          tmul_qz_inv_mul_eq l O (o y) (c y) (c x) (hc x), mul_comm (c y) (c x)]
      map_smul' := fun a x => by
        rw [spec (a • x) (a * o x) (c x) (hc x) (by rw [Algebra.smul_def, mul_assoc, hx x, map_mul])]
        show _ = a • (o x ⊗ₜ[ℤ_[l]] (Submodule.Quotient.mk (algebraMap ℤ_[l] ℚ_[l] (c x))⁻¹ : QZ l))
        rw [TensorProduct.smul_tmul', smul_eq_mul] }
  have hker : (1 : Submodule O (FractionRing O)) ≤ LinearMap.ker ψL := by
    intro x hx'
    obtain ⟨p, rfl⟩ := Submodule.mem_one.mp hx'
    change ψ₀ (algebraMap O (FractionRing O) p) = 0
    rw [spec _ p 1 one_ne_zero (by rw [map_one, mul_one]), map_one, inv_one]
    have h1 : (Submodule.Quotient.mk (1 : ℚ_[l]) : QZ l) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr ⟨1, by simp⟩
    rw [h1, TensorProduct.tmul_zero]; rfl
  let ψ : (FractionRing O ⧸ (1 : Submodule O (FractionRing O))) →ₗ[O] QO l O :=
    (1 : Submodule O (FractionRing O)).liftQ ψL hker
  refine ⟨LinearEquiv.ofLinearMap φ ψ ?_ ?_⟩
  · apply Submodule.linearMap_qext; ext x
    show φ (o x ⊗ₜ[ℤ_[l]] (Submodule.Quotient.mk (algebraMap ℤ_[l] ℚ_[l] (c x))⁻¹ : QZ l)) =
      Submodule.Quotient.mk x
    have hne : algebraMap ℤ_[l] (FractionRing O) (c x) ≠ 0 := (map_ne_zero_iff _ hinjK).mpr (hc x)
    rw [hφ, map_inv₀, hι, ← Submodule.Quotient.mk_smul]
    congr 1; rw [Algebra.smul_def, ← hx x, mul_inv_cancel_right₀ hne]
  · refine LinearMap.ext fun t => ?_
    induction t using TensorProduct.induction_on with
    | zero => exact ((ψ ∘ₗ φ).map_zero).trans (LinearMap.id (R := O) (M := QO l O)).map_zero.symm
    | tmul a q =>
      obtain ⟨r, rfl⟩ := Submodule.Quotient.mk_surjective (ZlSub l) q
      show ψ (φ (a ⊗ₜ[ℤ_[l]] (Submodule.Quotient.mk r : QZ l))) =
        a ⊗ₜ[ℤ_[l]] (Submodule.Quotient.mk r : QZ l)
      rw [hφ, map_smul]; show a • ψ₀ (ι r) = _
      obtain ⟨z, e, he, rfl⟩ := IsFractionRing.div_surjective (A := ℤ_[l]) r
      have he0 : e ≠ 0 := nonZeroDivisors.ne_zero he
      rw [spec _ (algebraMap ℤ_[l] O z) e he0 (by
        rw [map_div₀, hι, hι, div_mul_cancel₀ _ ((map_ne_zero_iff _ hinjK).mpr he0),
          IsScalarTower.algebraMap_apply ℤ_[l] O (FractionRing O)]),
        Algebra.algebraMap_eq_smul_one (A := O) z, TensorProduct.smul_tmul, ← Submodule.Quotient.mk_smul]
      show a • ((1 : O) ⊗ₜ[ℤ_[l]] (Submodule.Quotient.mk (z • (algebraMap ℤ_[l] ℚ_[l] e)⁻¹) : QZ l)) = _
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one, Algebra.smul_def, div_eq_mul_inv]
    | add t₁ t₂ h₁ h₂ => have hadd := (ψ ∘ₗ φ).map_add t₁ t₂; rw [h₁, h₂] at hadd; exact hadd

private theorem length_quotient_span_eq_addVal (R : Type) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] (x : R) (hx : x ≠ 0) :
    Module.length R (R ⧸ Ideal.span {x}) = IsDiscreteValuationRing.addVal R x := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨m, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hϖ
  rw [IsDiscreteValuationRing.addVal_def _ u hϖ m rfl, Ideal.span_singleton_mul_left_unit u.isUnit,
    ← Ideal.span_singleton_pow, ← hϖ.maximalIdeal_eq,
    IsDiscreteValuationRing.length_quotient_pow_maximalIdeal]

private theorem length_ker_fracMod_smul (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (a : O) :
    Module.length O (LinearMap.ker (a • (LinearMap.id :
      (FractionRing O ⧸ (1 : Submodule O (FractionRing O))) →ₗ[O]
        (FractionRing O ⧸ (1 : Submodule O (FractionRing O)))))) =
      IsDiscreteValuationRing.addVal O a := by
  let K := FractionRing O
  let FM := K ⧸ (1 : Submodule O K)
  have hne : ∀ b : O, b ≠ 0 →
      Module.length O (LinearMap.ker (b • (LinearMap.id : FM →ₗ[O] FM))) =
        IsDiscreteValuationRing.addVal O b := fun b hb => by
    have hbK : algebraMap O K b ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective O K)).mpr hb
    let φ : O →ₗ[O] LinearMap.ker (b • (LinearMap.id : FM →ₗ[O] FM)) :=
      { toFun := fun o => ⟨Submodule.Quotient.mk (algebraMap O K o / algebraMap O K b), by
          rw [LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply, ← Submodule.Quotient.mk_smul,
            Submodule.Quotient.mk_eq_zero, Submodule.mem_one]
          exact ⟨o, by rw [Algebra.smul_def, mul_div_cancel₀ _ hbK]⟩⟩
        map_add' := fun x y => Subtype.ext (show Submodule.Quotient.mk (algebraMap O K (x + y) / algebraMap O K b) =
          Submodule.Quotient.mk (algebraMap O K x / algebraMap O K b) +
          Submodule.Quotient.mk (algebraMap O K y / algebraMap O K b) by
          rw [map_add, add_div, Submodule.Quotient.mk_add])
        map_smul' := fun r o => Subtype.ext (show Submodule.Quotient.mk (algebraMap O K (r • o) / algebraMap O K b) =
          r • Submodule.Quotient.mk (algebraMap O K o / algebraMap O K b) by
          rw [smul_eq_mul, map_mul, mul_div_assoc, ← Algebra.smul_def, Submodule.Quotient.mk_smul]) }
    have hsurj : Function.Surjective φ := fun ⟨y, hy⟩ => by
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      rw [LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply, ← Submodule.Quotient.mk_smul,
        Submodule.Quotient.mk_eq_zero, Submodule.mem_one] at hy
      obtain ⟨o, ho⟩ := hy
      refine ⟨o, Subtype.ext (congrArg Submodule.Quotient.mk ?_)⟩
      rw [Algebra.smul_def] at ho
      exact (div_eq_iff hbK).mpr (by rw [mul_comm, ho])
    have hker : LinearMap.ker φ = Ideal.span {b} := by
      ext o
      rw [LinearMap.mem_ker, Subtype.ext_iff, ZeroMemClass.coe_zero]
      change Submodule.Quotient.mk (algebraMap O K o / algebraMap O K b) = (0 : FM) ↔ _
      rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_one,
        Ideal.mem_span_singleton]
      refine ⟨fun ⟨y, hy⟩ => ⟨y, IsFractionRing.injective O K ?_⟩, fun ⟨y, hy⟩ => ⟨y, ?_⟩⟩
      · rw [map_mul]; exact ((div_eq_iff hbK).mp hy.symm).trans (mul_comm _ _)
      · rw [hy, map_mul, mul_div_cancel_left₀ _ hbK]
    rw [← (φ.quotKerEquivOfSurjective hsurj).length_eq,
      (Submodule.quotEquivOfEq _ _ hker).length_eq]
    exact length_quotient_span_eq_addVal O b hb
  rcases eq_or_ne a 0 with rfl | ha
  · rw [IsDiscreteValuationRing.addVal_zero, ENat.eq_top_iff_forall_ge]
    intro m
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
    have hm0 : ϖ ^ m ≠ 0 := pow_ne_zero _ hϖ.ne_zero
    have hle : LinearMap.ker ((ϖ ^ m) • (LinearMap.id : FM →ₗ[O] FM)) ≤
        LinearMap.ker ((0 : O) • (LinearMap.id : FM →ₗ[O] FM)) := by
      intro x _; simp
    have hlen := Module.length_le_of_injective (Submodule.inclusion hle) (Submodule.inclusion_injective hle)
    rw [hne _ hm0, IsDiscreteValuationRing.addVal_def (ϖ ^ m) 1 hϖ m (by simp)] at hlen
    exact hlen
  · exact hne a ha

private theorem qo_len (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] (a : O) :
    Module.length O (LinearMap.ker (a • (LinearMap.id : QO l O →ₗ[O] QO l O))) =
      IsDiscreteValuationRing.addVal O a := by
  obtain ⟨e⟩ := qo_equiv l O
  rw [← length_ker_fracMod_smul O a]
  refine LinearEquiv.length_eq (e.ofSubmodules _ _ ?_)
  ext y
  simp only [Submodule.mem_map, LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply,
    LinearEquiv.coe_coe]
  exact ⟨fun ⟨m, hm, e'⟩ => e' ▸ by rw [← map_smul, hm, map_zero],
    fun hy => ⟨e.symm y, by rw [← map_smul, hy, map_zero], e.apply_symm_apply y⟩⟩

private theorem qo_tor (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O]
    (m : QO l O) : ∃ n : ℕ, l ^ n • m = 0 := by
  refine TensorProduct.induction_on (motive := fun m : O ⊗[ℤ_[l]] QZ l => ∃ n : ℕ, l ^ n • m = 0)
    m ⟨0, smul_zero _⟩ (fun o q => ?_) (fun x y ⟨n, hn⟩ ⟨k, hk⟩ => ⟨n + k, by
      have h1 : l ^ (n + k) • x = 0 := by rw [pow_add, mul_comm, mul_smul, hn, smul_zero]
      have h2 : l ^ (n + k) • y = 0 := by rw [pow_add, mul_smul, hk, smul_zero]
      rw [smul_add, h1, h2, add_zero]⟩)
  obtain ⟨r, rfl⟩ := Submodule.Quotient.mk_surjective (ZlSub l) q
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt ‖r‖ hl
  have hpowpos : (0 : ℝ) < (l : ℝ) ^ n := pow_pos (by exact_mod_cast (Fact.out : l.Prime).pos) n
  have hle : ‖((l ^ n : ℕ) : ℚ_[l]) * r‖ ≤ 1 := by
    rw [norm_mul, Nat.cast_pow, norm_pow, Padic.norm_p, inv_pow, inv_mul_le_iff₀ hpowpos, mul_one]
    exact hn.le
  let q0 : QZ l := Submodule.Quotient.mk r
  have hq : ((l ^ n : ℕ) : ℤ_[l]) • q0 = 0 := by
    rw [Nat.cast_smul_eq_nsmul ℤ_[l]]
    show (Submodule.Quotient.mk (l ^ n • r) : QZ l) = 0
    rw [nsmul_eq_mul, Submodule.Quotient.mk_eq_zero]
    exact LinearMap.mem_range.mpr ⟨⟨_, hle⟩, rfl⟩
  exact ⟨n, by show l ^ n • (o ⊗ₜ[ℤ_[l]] q0) = 0; rw [← Nat.cast_smul_eq_nsmul ℤ_[l], TensorProduct.smul_tmul', TensorProduct.smul_tmul, hq, TensorProduct.tmul_zero]⟩

theorem qoFacts :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
      [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O],
      (∀ m : QO l O, Module.length O (Submodule.span O {m}) ≠ ⊤) ∧
      (∀ m : QO l O, ∃ n : ℕ, l ^ n • m = 0) ∧
      (∀ a : O, a ≠ 0 → ∀ m : QO l O, ∃ m' : QO l O, a • m' = m) ∧
      ∀ a : O, Module.length O (LinearMap.ker (a • (LinearMap.id : QO l O →ₗ[O] QO l O))) =
        IsDiscreteValuationRing.addVal O a := by
  intro l _ O _ _ _ _ _
  obtain ⟨e⟩ := qo_equiv l O
  refine ⟨fun m => ?_, qo_tor l O, fun a ha m => ?_, qo_len l O⟩
  · obtain ⟨n, hn⟩ := qo_tor l O m
    have hb : ((l ^ n : ℕ) : O) ≠ 0 := by
      rw [← map_natCast (algebraMap ℤ_[l] O), map_ne_zero_iff _ (qo_inj l O), Nat.cast_ne_zero]
      exact pow_ne_zero _ (Fact.out : l.Prime).ne_zero
    have hle : Submodule.span O {m} ≤
        LinearMap.ker (((l ^ n : ℕ) : O) • (LinearMap.id : QO l O →ₗ[O] QO l O)) := by
      rw [Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe, LinearMap.mem_ker,
        LinearMap.smul_apply, LinearMap.id_apply, Nat.cast_smul_eq_nsmul O, hn]
    intro htop
    have hlen := Module.length_le_of_injective (Submodule.inclusion hle) (Submodule.inclusion_injective hle)
    rw [htop, qo_len l O, top_le_iff, IsDiscreteValuationRing.addVal_eq_top_iff] at hlen
    exact hb hlen
  · obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective (1 : Submodule O (FractionRing O)) (e m)
    have ha' : algebraMap O (FractionRing O) a ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective O (FractionRing O))).mpr ha
    refine ⟨e.symm (Submodule.Quotient.mk (x / algebraMap O (FractionRing O) a)), ?_⟩
    have hdiv : a • (x / algebraMap O (FractionRing O) a) = x := by rw [Algebra.smul_def]; field_simp
    rw [← map_smul, ← Submodule.Quotient.mk_smul, hdiv, hx, e.symm_apply_apply]

end QoFactsSection

theorem qoBase :
    ∀ (l : ℕ) [Fact l.Prime] (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
      (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O]
      [Module.Finite ℤ_[l] O] (χ : G →* ℤ_[l]ˣ) (U : Subgroup G) (𝒟 : Set (Subgroup G)),
      Module.length O (LocSel (twist₂ l ((Units.map (algebraMap ℤ_[l] O).toMonoidHom).comp χ)) U 𝒟) =
        Module.length ℤ_[l] (LocSel (scalRep (QZ l) χ) U 𝒟) * eO l O ∧
      ∀ [U.Normal] (h𝒟 : ConjStable 𝒟) (g : G) (s : ℤ_[l]),
        Module.length O (Module.End.eigenspace
          (selRep (twist₂ l ((Units.map (algebraMap ℤ_[l] O).toMonoidHom).comp χ)) U h𝒟 g)
          (algebraMap ℤ_[l] O s)) =
          Module.length ℤ_[l] (Module.End.eigenspace (selRep (scalRep (QZ l) χ) U h𝒟 g) s) * eO l O := by
  intro l _ G _ _ _ O _ _ _ _ _ χ U 𝒟
  obtain ⟨-, hfree, hloc, -, he, -⟩ := dvrFacts l O
  have hj : ∀ g m, QO.incl l O (scalRep (QZ l) χ g m) =
      twist₂ l ((Units.map (algebraMap ℤ_[l] O).toMonoidHom).comp χ) g (QO.incl l O m) := fun g m => by
    show QO.incl l O (((χ g : ℤ_[l]ˣ) : ℤ_[l]) • m) = algebraMap ℤ_[l] O (χ g : ℤ_[l]ˣ) • QO.incl l O m
    rw [map_smul, algebraMap_smul]
  rw [he]
  exact ⟨selBase ℤ_[l] G (QZ l) (scalRep (QZ l) χ) O (QO l O) _ (QO.incl l O) (QO.isBaseChange l O) hj U 𝒟,
    fun h𝒟 g s => (selBaseEig ℤ_[l] G (QZ l) (scalRep (QZ l) χ) O (QO l O) _ (QO.incl l O)
      (QO.isBaseChange l O) hj U 𝒟 h𝒟).2 g s⟩

theorem qoExt :
    ∀ (l : ℕ) [Fact l.Prime] (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
      (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O]
      [Module.Finite ℤ_[l] O] (O' : Type) [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O']
      [Algebra ℤ_[l] O'] [Module.Finite ℤ_[l] O'] [Algebra O O'] [IsScalarTower ℤ_[l] O O']
      (θ : G →* Oˣ) (U : Subgroup G) (𝒟 : Set (Subgroup G)),
      Module.length O' (LocSel (twist₂ l ((Units.map (algebraMap O O').toMonoidHom).comp θ)) U 𝒟) * eO l O =
        Module.length O (LocSel (twist₂ l θ) U 𝒟) * eO l O' ∧
      ∀ [U.Normal] (h𝒟 : ConjStable 𝒟) (W : Subgroup G) (ψ : W →* Oˣ),
        Module.length O' (selEig (twist₂ l ((Units.map (algebraMap O O').toMonoidHom).comp θ)) U h𝒟 W
          ((Units.map (algebraMap O O').toMonoidHom).comp ψ)) * eO l O =
          Module.length O (selEig (twist₂ l θ) U h𝒟 W ψ) * eO l O' := by
  intro l _ G _ _ _ O _ _ _ _ _ O' _ _ _ _ _ _ _ θ U 𝒟
  obtain ⟨hiO, -, hlocO, -, -, -, -, hvO, -⟩ := dvrFacts l O
  obtain ⟨hiO', -, -, -, -, -, -, hvO', -⟩ := dvrFacts l O'
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hl0 : (l : ℤ_[l]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero
  have hlO : (l : O) ≠ 0 := fun h => hl0 (hiO (by rw [map_natCast, h, map_zero]))
  have hlmax : (l : O) ∈ IsLocalRing.maximalIdeal O := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, ← map_natCast (algebraMap ℤ_[l] O), isUnit_map_iff]
    exact PadicInt.p_nonunit
  have hdvd : ϖ ∣ (l : O) := by rwa [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at hlmax
  have hϖ' : algebraMap O O' ϖ ≠ 0 := fun h => by
    obtain ⟨c, hc⟩ := hdvd
    exact hl0 (hiO' (by rw [map_zero, IsScalarTower.algebraMap_apply ℤ_[l] O O', map_natCast, hc, map_mul, h, zero_mul]))
  have hinj : Function.Injective (algebraMap O O') := by
    rw [injective_iff_map_eq_zero]
    intro x hx; by_contra hx0
    obtain ⟨m, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx0 hϖ
    rw [map_mul, map_pow] at hx
    rcases mul_eq_zero.mp hx with h | h
    · exact (u.isUnit.map (algebraMap O O')).ne_zero h
    · exact hϖ' (pow_eq_zero_iff'.mp h).1
  haveI : FaithfulSMul O O' := (faithfulSMul_iff_algebraMap_injective O O').mpr hinj
  haveI : Module.Finite O O' := Module.Finite.of_restrictScalars_finite ℤ_[l] O O'
  haveI : Module.Free O O' := Module.free_of_finite_type_torsion_free'
  haveI : IsLocalHom (algebraMap O O') := inferInstance
  have hf : Module.length O' (O' ⧸ Ideal.map (algebraMap O O') (IsLocalRing.maximalIdeal O)) * eO l O =
      eO l O' := by
    obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hlO hϖ
    have hlO' : (l : O') = algebraMap O O' u * (algebraMap O O' ϖ) ^ n := by
      rw [← map_natCast (algebraMap O O'), hu, map_mul, map_pow]
    rw [hvO, hvO', hϖ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton,
      length_quotient_span_eq_addVal O' _ hϖ', IsDiscreteValuationRing.addVal_def _ u hϖ n hu,
      hlO', IsDiscreteValuationRing.addVal_mul, IsDiscreteValuationRing.addVal_pow,
      (IsDiscreteValuationRing.addVal_eq_zero_iff).mpr (u.isUnit.map _), zero_add, nsmul_eq_mul, mul_comm]
  letI : Module O (QO l O') := TensorProduct.leftModule
  haveI : IsScalarTower O O' (QO l O') :=
    (inferInstance : IsScalarTower O O' (TensorProduct ℤ_[l] O' (QZ l)))
  haveI : IsScalarTower ℤ_[l] O (QO l O') :=
    (inferInstance : IsScalarTower ℤ_[l] O (TensorProduct ℤ_[l] O' (QZ l)))
  let j : QO l O →ₗ[O] QO l O' :=
    TensorProduct.AlgebraTensorModule.map (Algebra.linearMap O O') LinearMap.id
  have hj : IsBaseChange O' j := by
    refine (QO.isBaseChange l O).of_comp ?_
    convert QO.isBaseChange l O' using 1
    apply LinearMap.ext; intro m
    change TensorProduct.AlgebraTensorModule.map (Algebra.linearMap O O') LinearMap.id
      ((1 : O) ⊗ₜ[ℤ_[l]] m) = (1 : O') ⊗ₜ[ℤ_[l]] m
    rw [TensorProduct.AlgebraTensorModule.map_tmul, Algebra.linearMap_apply, map_one, LinearMap.id_apply]
  have hcomp : ∀ (g : G) (m : QO l O), j ((twist₂ l θ) g m) =
      (twist₂ l ((Units.map (algebraMap O O').toMonoidHom).comp θ)) g (j m) := fun g m => by
    simp only [twist₂, scalRep, MonoidHom.coe_mk, OneHom.coe_mk, LinearMap.smul_apply, LinearMap.id_coe,
      id_eq, map_smul, MonoidHom.coe_comp, Function.comp_apply, Units.coe_map,
      RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]
    rw [algebraMap_smul]
  refine ⟨?_, ?_⟩
  · rw [selBase O G (QO l O) (twist₂ l θ) O' (QO l O') _ j hj hcomp U 𝒟, mul_assoc, hf]
  · intro _ h𝒟 W ψ
    rw [(selBaseEig O G (QO l O) (twist₂ l θ) O' (QO l O') _ j hj hcomp U 𝒟 h𝒟).1 W ψ, mul_assoc, hf]

private theorem signTop {O W Q N : Type} [CommRing O] [IsDomain O] [Group W] [Group Q]
    [IsMulCommutative Q] [Finite Q] [HasEnoughRootsOfUnity O (Monoid.exponent Q)]
    [Fintype (Q →* Oˣ)] [AddCommGroup N] [Module O N] (π : Representation O W N) (p : W →* Q)
    (hp : Function.Surjective p) (hker : ∀ g, p g = 1 → ∀ x, π g x = x) (h2 : IsUnit (2 : O))
    (c : W) (s : ℤˣ) (a : O) (ha : a = ((s : ℤ) : O)) (hc : p c * p c = 1)
    (T : Finset (Q →* Oˣ)) (hT : ∀ ψ, ((ψ (p c) : Oˣ) : O) = ((s : ℤ) : O) → ψ ∈ T) :
    Module.length O (Module.End.eigenspace (π c) a) ≤
      ∑ ψ ∈ T, Module.length O (eig (π.comp (⊤ : Subgroup W).subtype : Representation O (⊤ : Subgroup W) N)
        ((ψ.comp p).comp (⊤ : Subgroup W).subtype)) := by
  subst ha
  let s' : Oˣ := Units.map (Int.castRingHom O).toMonoidHom s
  letI : CommGroup Q := { (inferInstance : Group Q) with mul_comm := fun a b => IsMulCommutative.is_comm.comm a b }
  exact lenEigSign O (⊤ : Subgroup W) Q N (π.comp (⊤ : Subgroup W).subtype)
    (p.comp (⊤ : Subgroup W).subtype) (fun q => by obtain ⟨g, hg⟩ := hp q; exact ⟨⟨g, trivial⟩, hg⟩)
    (fun g hg x => hker g hg x) h2 ⟨c, trivial⟩ s' hc (by rw [← map_mul, Int.units_mul_self, map_one]) T
    (fun ψ hψ => hT ψ (by simpa [s'] using congrArg Units.val hψ))

theorem shaDecompSign :
    ∀ (k E Ω : Type) [Field k] [NumberField k] [Field E] [NumberField E] [Field Ω] [Algebra k E]
      [Algebra k Ω] [Algebra E Ω] [IsScalarTower k E Ω] [IsAlgClosure k Ω] [IsAlgClosure E Ω]
      [IsAbelianGalois k E] (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O]
      [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O]
      [HasEnoughRootsOfUnity O (Monoid.exponent (E ≃ₐ[k] E))] [Fintype ((E ≃ₐ[k] E) →* Oˣ)]
      (D : LData E Ω l) (e : ℤ), l ≠ 2 → ∀ (c : E ≃ₐ[k] E) (s : ℤˣ), c * c = 1 →
      ∀ T : Finset ((E ≃ₐ[k] E) →* Oˣ), (∀ ψ, ((ψ c : Oˣ) : O) = ((s : ℤ) : O) → ψ ∈ T) →
      Module.length ℤ_[l] ↥(Sha D e ⊓ Module.End.eigenspace (galoisActionOnCohomology D e c.toRingEquiv) ((s : ℤ) : ℤ_[l])) * eO l O ≤
        ∑ ψ ∈ T, Module.length O (shaEig (twist₂ l (chiO k Ω l O ^ (-e))) l (galOf k E Ω) ⊤
          ((ψ.comp (AlgEquiv.restrictNormalHom E)).comp (⊤ : Subgroup (G k Ω)).subtype)) := by
  intro k E Ω _ _ _ _ _ _ _ _ _ _ _ _ l hl O _ _ _ _ _ _ _ D e hl2 c s hc T hT
  obtain ⟨hsurj, hker, hlift⟩ := galQuot k E Ω
  obtain ⟨σ, rfl⟩ := hsurj c
  have h2 : IsUnit (2 : O) := by
    simpa using (dvrFacts l O).2.2.2.2.2.2.2.2 2 fun h => hl2 ((Nat.prime_dvd_prime_iff_eq hl.out Nat.prime_two).1 h)
  have hχ : chiO k Ω l O ^ (-e) = (Units.map (algebraMap ℤ_[l] O).toMonoidHom).comp (cycZ k Ω l ^ (-e)) := by
    ext g; simp [chiO]
  have h1 := (shaLenEq k E Ω l D e).2 _ σ (hlift σ) ((s : ℤ) : ℤ_[l])
  have h3 := (qoBase l (G k Ω) O (cycZ k Ω l ^ (-e)) (galOf k E Ω) (shaFam k Ω l)).2
    (conjStable_shaFam k Ω l) σ ((s : ℤ) : ℤ_[l])
  rw [h1, hχ]
  refine (le_of_eq h3.symm).trans ?_
  exact signTop (shaRep (twist₂ l ((Units.map (algebraMap ℤ_[l] O).toMonoidHom).comp (cycZ k Ω l ^ (-e)))) l (galOf k E Ω))
    (AlgEquiv.restrictNormalHom E) hsurj
    (fun g hg x => selRep_of_mem _ _ (conjStable_shaFam k Ω l) (hker ▸ MonoidHom.mem_ker.2 hg) x)
    h2 σ s _ (map_intCast (algebraMap ℤ_[l] O) _) hc T hT

end BaseChangeAndQO

/-! ## Section 6: Kernel/Cokernel Bounds, Corestriction, Transgression, `H²` Vanishing & Abelian Bounds -/

section KernelCokerAndH2

section KerResAndCorestriction

private theorem exists_inj_of_ker_eq {R A B C : Type} [CommRing R] [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C] (p : A →ₗ[R] B) (q : A →ₗ[R] C)
    (hp : Function.Surjective p) (hk : ∀ a, p a = 0 ↔ q a = 0) :
    ∃ φ : B →ₗ[R] C, Function.Injective φ := by
  have hle : LinearMap.ker p ≤ LinearMap.ker q := fun a ha => (hk a).1 ha
  have hle' : LinearMap.ker q ≤ LinearMap.ker p := fun a ha => (hk a).2 ha
  refine ⟨(LinearMap.ker p).liftQ q hle ∘ₗ (p.quotKerEquivOfSurjective hp).symm.toLinearMap, ?_⟩
  rw [LinearMap.coe_comp]
  exact (LinearMap.ker_eq_bot.mp (Submodule.ker_liftQ_eq_bot _ q hle hle')).comp
    (p.quotKerEquivOfSurjective hp).symm.injective

section CocycleZeroHelpers

variable {R G M : Type} [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [ContinuousConstSMul R M] [DiscreteTopology M]

private theorem cocycle_eq_zero (ρ : Representation R G M) {U' U : Subgroup G} (h : U' ≤ U)
    {γ : G} (hγ : γ ∈ U) (hU : U ≤ (Subgroup.zpowers γ ⊔ U').topologicalClosure) (z : Z1U ρ U)
    (h1 : ∀ u : U, u.1 ∈ U' → z.1 u = 0) (h2 : z.1 ⟨γ, hγ⟩ = 0) (u : U) : z.1 u = 0 := by
  obtain ⟨hcont, hcoc⟩ := (mem_Z1 _ _).1 z.2
  have hone : z.1 1 = 0 := by have e := hcoc 1 1; simp only [mul_one, map_one, Module.End.one_apply] at e; simpa using e
  let K : Subgroup U :=
    { carrier := {x | z.1 x = 0}
      mul_mem' := fun {a b} ha hb => by show z.1 (a * b) = 0; rw [hcoc, ha, hb, map_zero, add_zero]
      one_mem' := hone
      inv_mem' := fun {a} ha => by
        show z.1 a⁻¹ = 0
        have e := hcoc a⁻¹ a; rw [inv_mul_cancel, hone, ha, map_zero, add_zero] at e; exact e.symm }
  have hS : Subgroup.zpowers γ ⊔ U' ≤ K.map U.subtype := sup_le
    (Subgroup.zpowers_le.2 ⟨⟨γ, hγ⟩, h2, rfl⟩)
    (fun x hx => ⟨⟨x, h hx⟩, h1 ⟨x, h hx⟩ hx, rfl⟩)
  have hu := hU u.2
  rw [← SetLike.mem_coe, Subgroup.topologicalClosure_coe] at hu
  obtain ⟨O, hO, hOV⟩ := isOpen_induced_iff.1 (hcont.isOpen_preimage _ (isOpen_discrete {z.1 u}))
  obtain ⟨s, hsO, hsS⟩ := mem_closure_iff.1 hu O hO (by show u ∈ Subtype.val ⁻¹' O; rw [hOV]; rfl)
  obtain ⟨⟨s', hs'U⟩, hzs, rfl⟩ := hS hsS
  have hmem : (⟨s', hs'U⟩ : U) ∈ Subtype.val ⁻¹' O := hsO
  rw [hOV] at hmem
  exact hmem ▸ hzs

private def cob (ρ : Representation R G M) (hρ : ContAction ρ) (U : Subgroup G) (m : M) : Z1U ρ U := by
  have hρU : ContAction (ρ.comp U.subtype) := hρ.comp (continuous_subtype_val.prodMap continuous_id)
  exact ⟨d0 (ρ.comp U.subtype : Representation R U M) m, coboundaries_le_cocycles _ hρU ⟨m, rfl⟩⟩

private def Z0Sub (ρ : Representation R G M) (U' U : Subgroup G) : Submodule R (Z1U ρ U) where
  carrier := {z | ∀ u : U, u.1 ∈ U' → z.1 u = 0}
  zero_mem' := fun _ _ => rfl
  add_mem' := fun ha hb u hu => by simp only [Submodule.coe_add, Pi.add_apply]; rw [ha u hu, hb u hu, add_zero]
  smul_mem' := fun _ _ ha u hu => by simp only [Submodule.coe_smul, Pi.smul_apply]; rw [ha u hu, smul_zero]

private theorem cocycle_zero_mem_invariants (ρ : Representation R G M) {U' U : Subgroup G}
    (h : U' ≤ U) [hN : (U'.subgroupOf U).Normal] (g : U) (z : Z0Sub ρ U' U) :
    z.1.1 g ∈ H0U ρ U' := by
  obtain ⟨_, hcoc⟩ := (mem_Z1 _ _).1 z.1.2
  rw [H0U, H0, Representation.mem_invariants]
  intro v
  let v' : U := ⟨v.1, h v.2⟩
  have hw : g⁻¹ * v' * g ∈ U'.subgroupOf U := by
    simpa using hN.conj_mem v' (Subgroup.mem_subgroupOf.mpr v.2) g⁻¹
  have e1 := hcoc v' g
  have e2 := hcoc g (g⁻¹ * v' * g)
  rw [show g * (g⁻¹ * v' * g) = v' * g by group, z.2 _ (Subgroup.mem_subgroupOf.mp hw),
    map_zero, add_zero] at e2
  rw [z.2 v' v.2, zero_add, e2] at e1
  exact e1.symm

end CocycleZeroHelpers

theorem kerResGen1 :
    ∀ (R G M : Type) [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
      [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M]
      [ContinuousConstSMul R M] [DiscreteTopology M] (ρ : Representation R G M),
      ContAction ρ → ∀ (U' U : Subgroup G) (h : U' ≤ U) [(U'.subgroupOf U).Normal] (γ : G),
      γ ∈ U → U ≤ (Subgroup.zpowers γ ⊔ U').topologicalClosure →
      ∀ T : H0U ρ U' →ₗ[R] H0U ρ U', (∀ m, (T m : M) = ρ γ m - m) →
      ∃ φ : LinearMap.ker (resU ρ h) →ₗ[R] (H0U ρ U' ⧸ LinearMap.range T), Function.Injective φ := by
  intro R G M _ _ _ _ _ _ _ _ _ _ ρ hρ U' U h _ γ hγ hU T hT
  have hcobv : ∀ (m : M) (u : U), (cob ρ hρ U m).1 u = ρ u m - m := fun _ _ => rfl
  let ev : Z0Sub ρ U' U →ₗ[R] H0U ρ U' :=
    { toFun := fun a => ⟨a.1.1 ⟨γ, hγ⟩, cocycle_zero_mem_invariants ρ h ⟨γ, hγ⟩ a⟩
      map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  let q : Z0Sub ρ U' U →ₗ[R] (H0U ρ U' ⧸ LinearMap.range T) := (LinearMap.range T).mkQ ∘ₗ ev
  let p : Z0Sub ρ U' U →ₗ[R] LinearMap.ker (resU ρ h) :=
    LinearMap.codRestrict _
      ((Submodule.comap (Z1U ρ U).subtype (B1 (MonoidHom.comp ρ U.subtype))).mkQ ∘ₗ
        (Z0Sub ρ U' U).subtype)
      fun a => (resU_mk_eq_zero ρ h a.1).2 ⟨0, fun u => by rw [map_zero, sub_zero]; exact a.2 _ u.2⟩
  have hp : Function.Surjective p := by
    rintro ⟨x, hx⟩
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨m, hm⟩ := (resU_mk_eq_zero ρ h z).1 (LinearMap.mem_ker.1 hx)
    refine ⟨⟨z - cob ρ hρ U m, fun u hu => by show z.1 u - (cob ρ hρ U m).1 u = 0; rw [hcobv]; exact sub_eq_zero.2 (hm ⟨u.1, hu⟩)⟩,
      Subtype.ext ((mk_eq_mk ρ U (z - cob ρ hρ U m) z).2 ⟨-m, fun u => by
        show z.1 u - (cob ρ hρ U m).1 u - z.1 u = ρ u (-m) - -m; rw [hcobv, map_neg]; abel⟩)⟩
  have hk : ∀ a, p a = 0 ↔ q a = 0 := fun a => by
    have hpa : p a = 0 ↔ ∃ m : M, ∀ u : U, a.1.1 u - (0 : Z1U ρ U).1 u = ρ u m - m := by
      rw [Subtype.ext_iff]; show Submodule.Quotient.mk a.1 = (0 : H1U ρ U) ↔ _
      rw [← Submodule.Quotient.mk_zero, mk_eq_mk]
    have hqa : q a = 0 ↔ ∃ n : H0U ρ U', (T n : M) = a.1.1 ⟨γ, hγ⟩ := by
      show Submodule.Quotient.mk (ev a) = 0 ↔ _
      rw [Submodule.Quotient.mk_eq_zero, LinearMap.mem_range]
      exact ⟨fun ⟨n, hn⟩ => ⟨n, congrArg Subtype.val hn⟩, fun ⟨n, hn⟩ => ⟨n, Subtype.ext hn⟩⟩
    rw [hpa, hqa]
    constructor
    · rintro ⟨m, hm⟩
      have hmH : m ∈ H0U ρ U' := by
        rw [H0U, H0, Representation.mem_invariants]
        intro v; have e := hm ⟨v.1, h v.2⟩; rw [a.2 ⟨v.1, h v.2⟩ v.2] at e
        exact sub_eq_zero.1 (by simpa using e.symm)
      exact ⟨⟨m, hmH⟩, by rw [hT]; simpa using (hm ⟨γ, hγ⟩).symm⟩
    · rintro ⟨n, hn⟩
      rw [hT] at hn
      have hnH := (Representation.mem_invariants _ _).1 n.2
      have hv1 : ∀ u : U, u.1 ∈ U' → (a.1 - cob ρ hρ U n.1).1 u = 0 := fun u hu => by
        show a.1.1 u - (cob ρ hρ U n.1).1 u = 0
        rw [hcobv, a.2 u hu]
        have e := hnH ⟨u.1, hu⟩
        simp only [MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype] at e
        simp [e]
      have hv2 : (a.1 - cob ρ hρ U n.1).1 ⟨γ, hγ⟩ = 0 := by
        show a.1.1 ⟨γ, hγ⟩ - (cob ρ hρ U n.1).1 ⟨γ, hγ⟩ = 0; rw [hcobv, ← hn]; simp
      refine ⟨n.1, fun u => ?_⟩
      have e : a.1.1 u - (cob ρ hρ U n.1).1 u = 0 :=
        cocycle_eq_zero ρ h hγ hU (a.1 - cob ρ hρ U n.1) hv1 hv2 u
      rw [hcobv] at e; simpa using sub_eq_zero.1 e
  exact exists_inj_of_ker_eq p q hp hk

private theorem corCoc_mem {G : Type} [Group G] (H : Subgroup G) (g : G) (q : G ⧸ H) :
    (g • q).out⁻¹ * g * q.out ∈ H := by
  have h : (QuotientGroup.mk (g • q).out : G ⧸ H) = QuotientGroup.mk (g * q.out) := by
    rw [QuotientGroup.out_eq']
    conv_lhs => rw [← QuotientGroup.out_eq' q]
    rfl
  simpa [mul_assoc] using QuotientGroup.eq.mp h

private theorem exists_corestriction_cocycle :
    ∀ (R G X : Type) [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
      [AddCommGroup X] [Module R X] [TopologicalSpace X] [IsTopologicalAddGroup X]
      (ρ : Representation R G X) (H : Subgroup G) [H.Normal] [H.FiniteIndex],
      IsOpen (H : Set G) → (∀ g, Continuous (ρ g)) → (∀ x, Continuous fun g => ρ g x) →
      ∀ f : G → X, ContinuousOn f H → (∀ g ∈ H, ∀ h ∈ H, f (g * h) = f g + ρ g (f h)) →
      ∃ F : G → X, Continuous F ∧ (∀ g h, F (g * h) = F g + ρ g (F h)) ∧
        (∃ x, ∀ h ∈ H, F h = (∑ᶠ q : G ⧸ H, ρ q.out (f (q.out⁻¹ * h * q.out))) + (ρ h x - x)) := by
  intro R G X _ _ _ _ _ _ _ _ ρ H _ _ hH hρ _ f hf hc
  classical
  haveI : Fintype (G ⧸ H) := Fintype.ofFinite _
  have hmul : ∀ (a b : G) (x : X), ρ a (ρ b x) = ρ (a * b) x := fun a b x => by rw [map_mul]; rfl
  refine ⟨fun g => ∑ q : G ⧸ H, ρ (g • q).out (f ((g • q).out⁻¹ * g * q.out)),
    continuous_finsetSum _ fun q _ => continuous_iff_continuousAt.2 fun g₀ => ?_,
    fun g h => ?_, ⟨0, fun h hh => ?_⟩⟩
  · have hk : Continuous fun g : G => (g₀ • q).out⁻¹ * g * q.out := by fun_prop
    have hn : ∀ᶠ g in nhds g₀, (g₀ • q).out⁻¹ * g * q.out ∈ H :=
      hk.continuousAt.preimage_mem_nhds (hH.mem_nhds (corCoc_mem H g₀ q))
    refine ((hρ (g₀ • q).out).continuousAt.comp
      (ContinuousAt.comp (f := fun g : G => (g₀ • q).out⁻¹ * g * q.out)
        (hf.continuousAt (hH.mem_nhds (corCoc_mem H g₀ q))) (hk.continuousAt (x := g₀)))).congr ?_
    filter_upwards [hn] with g hg
    have : g • q = g₀ • q := by
      conv_rhs => rw [← QuotientGroup.out_eq' (g₀ • q)]
      conv_lhs => rw [← QuotientGroup.out_eq' q]
      symm; change (QuotientGroup.mk (g₀ • q).out : G ⧸ H) = QuotientGroup.mk (g * q.out)
      exact QuotientGroup.eq.mpr (by simpa [mul_assoc] using hg)
    rw [this]; rfl
  · simp only [map_sum]
    rw [← Equiv.sum_comp (MulAction.toPerm h)
      (fun q : G ⧸ H => ρ (g • q).out (f ((g • q).out⁻¹ * g * q.out))), ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun q _ => ?_
    simp only [MulAction.toPerm_apply, mul_smul]
    have e : (g • h • q).out⁻¹ * (g * h) * q.out =
        ((g • h • q).out⁻¹ * g * (h • q).out) * ((h • q).out⁻¹ * h * q.out) := by group
    rw [e, hc _ (corCoc_mem H g (h • q)) _ (corCoc_mem H h q), map_add, hmul, hmul]
    congr 3; group
  · rw [finsum_eq_sum_of_fintype]
    simp only [map_zero, sub_zero, add_zero]
    refine Finset.sum_congr rfl fun q _ => ?_
    have : h • q = q := by
      conv_rhs => rw [← QuotientGroup.out_eq' q]
      conv_lhs => rw [← QuotientGroup.out_eq' q]
      symm
      change (QuotientGroup.mk q.out : G ⧸ H) = QuotientGroup.mk (h * q.out)
      exact QuotientGroup.eq.mpr (by simpa [mul_assoc] using Subgroup.Normal.conj_mem' ‹H.Normal› h hh q.out)
    rw [this]

theorem corInv :
    ∀ (R G M : Type) [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
      [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M]
      [ContinuousConstSMul R M] [DiscreteTopology M] (ρ : Representation R G M),
      ContAction ρ → ∀ (U' U : Subgroup G) [U'.Normal] (h : U' ≤ U),
      IsOpen (U'.subgroupOf U : Set U) → ∀ x ∈ invariantsUnderSubgroupH1 ρ U U',
      U'.relIndex U • x ∈ LinearMap.range (resU ρ h) := by
  classical
  intro R G M _ _ _ _ _ _ _ _ _ _ ρ hρ U' U _ h hopen x hx
  by_cases hfin : U'.relIndex U = 0
  · rw [hfin, zero_smul]; exact zero_mem _
  haveI : (U'.subgroupOf U).FiniteIndex := ⟨hfin⟩
  haveI : Fintype (U ⧸ U'.subgroupOf U) := Fintype.ofFinite _
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have hinv : ∀ g : U, conjU ρ U' g (Submodule.Quotient.mk z) = Submodule.Quotient.mk z :=
    fun g => (Representation.mem_invariants _ _).mp hx g
  have hq : ∀ q : U ⧸ U'.subgroupOf U, ∃ m : M, ∀ u : U',
      ρ (q.out : G) (z.1 (conjHom U' (q.out : G) u)) - z.1 u = ρ u m - m := fun q => by
    obtain ⟨z', hz1, hz2⟩ := conjU_mk ρ U' (q.out : G) z
    rw [hinv, mk_eq_mk] at hz1
    obtain ⟨m, hm⟩ := hz1
    refine ⟨-m, fun u => ?_⟩
    have e := hm u; rw [hz2] at e; rw [map_neg, neg_sub_neg, ← neg_sub ((ρ u) m) m, ← e]; abel
  choose mq hmq using hq
  let f : U → M := fun g => if hg : (g : G) ∈ U' then z.1 ⟨g, hg⟩ else 0
  have hfc : ContinuousOn f (U'.subgroupOf U : Set U) := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact (z.2.1.comp (Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val)
      (fun g : (U'.subgroupOf U : Set U) => Subgroup.mem_subgroupOf.mp g.2))).congr
      fun g => by simp [f, dif_pos (Subgroup.mem_subgroupOf.mp g.2)]
  have hfcoc : ∀ g ∈ U'.subgroupOf U, ∀ k ∈ U'.subgroupOf U,
      f (g * k) = f g + (ρ.comp U.subtype) g (f k) := fun g hg k hk => by
    rw [Subgroup.mem_subgroupOf] at hg hk
    have hgk : ((g * k : U) : G) ∈ U' := by rw [Subgroup.coe_mul]; exact U'.mul_mem hg hk
    simp only [f, dif_pos hg, dif_pos hk, dif_pos hgk]
    exact z.2.2 ⟨g, hg⟩ ⟨k, hk⟩
  obtain ⟨F, hFc, hFcoc, ⟨x0, hx0⟩⟩ := exists_corestriction_cocycle R U M
    (ρ.comp U.subtype) (U'.subgroupOf U) hopen (fun _ => continuous_of_discreteTopology)
    (fun m => hρ.comp (Continuous.prodMk continuous_subtype_val continuous_const)) f hfc hfcoc
  let Fz : Z1U ρ U := ⟨F, hFc, hFcoc⟩
  refine ⟨Submodule.Quotient.mk Fz, ?_⟩
  obtain ⟨w, hw1, hw2⟩ := resU_mk ρ h Fz
  rw [hw1, ← Submodule.Quotient.mk_smul, mk_eq_mk]
  refine ⟨x0 + ∑ q, mq q, fun u => ?_⟩
  have hterm : ∀ q : U ⧸ U'.subgroupOf U,
      (ρ.comp U.subtype) q.out (f ((q.out)⁻¹ * ⟨(u : G), h u.2⟩ * q.out)) =
        z.1 u + (ρ u (mq q) - mq q) := fun q => by
    rw [← hmq q u, add_sub_cancel]
    have hmem : (((q.out)⁻¹ * ⟨(u : G), h u.2⟩ * q.out : U) : G) ∈ U' := by
      simpa [mul_assoc] using ‹U'.Normal›.conj_mem u u.2 ((q.out : G)⁻¹)
    simp only [f, dif_pos hmem]; rfl
  have hcard : Fintype.card (U ⧸ U'.subgroupOf U) = U'.relIndex U := by
    rw [Subgroup.relIndex, Subgroup.index, Nat.card_eq_fintype_card]
  rw [hw2 u]
  show F ⟨(u : G), h u.2⟩ - _ = _
  rw [hx0 ⟨u, h u.2⟩ (Subgroup.mem_subgroupOf.mpr u.2), finsum_eq_sum_of_fintype,
    Finset.sum_congr rfl (fun q _ => hterm q), Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_univ, hcard]
  simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, map_add, map_sum]
  rw [show ((U'.relIndex U • z : Z1U ρ U') : U' → M) u = U'.relIndex U • z.1 u from rfl]
  abel

theorem kerResSmul :
    ∀ (R G M : Type) [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
      [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M]
      [ContinuousConstSMul R M] [DiscreteTopology M] (ρ : Representation R G M) (U' U : Subgroup G)
      (h : U' ≤ U) (x : H1U ρ U), resU ρ h x = 0 → U'.relIndex U • x = 0 := by
  intro R G M _ _ _ _ _ _ _ _ _ _ ρ U' U h x hx
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨m, hm⟩ := (resU_mk_eq_zero ρ h z).1 hx
  have aux : ∃ s, ∀ g : U, U'.relIndex U • (z.1 g - (ρ g m - m)) = ρ g s - s := by
    let f : U → M := fun u => z.1 u - (ρ u m - m)
    have hf : ∀ g k : U, f (g * k) = f g + ρ g (f k) := fun g k => by
      show z.1 (g * k) - (ρ ((g : G) * k) m - m) = z.1 g - (ρ g m - m) + ρ g (z.1 k - (ρ k m - m))
      rw [z.2.2 g k, map_mul, Module.End.mul_apply, map_sub, map_sub]
      simp only [MonoidHom.comp_apply, Subgroup.coe_subtype]
      abel
    have h0 : ∀ u ∈ U'.subgroupOf U, f u = 0 := fun u hu => sub_eq_zero.2 (hm ⟨u.1, hu⟩)
    by_cases h0idx : (U'.subgroupOf U).index = 0
    · exact ⟨0, fun g => by unfold Subgroup.relIndex; simp [h0idx]⟩
    haveI : Finite (U ⧸ U'.subgroupOf U) := Nat.finite_of_card_ne_zero h0idx
    letI : Fintype (U ⧸ U'.subgroupOf U) := Fintype.ofFinite _
    have key : ∀ a b : U, (a : U ⧸ U'.subgroupOf U) = (b : U ⧸ U'.subgroupOf U) → f a = f b := fun a b hab => by
      have h1 := hf a (a⁻¹ * b)
      rw [h0 _ (QuotientGroup.eq.mp hab), map_zero, add_zero, mul_inv_cancel_left] at h1
      exact h1.symm
    have step : ∀ (g : U) (x : U ⧸ U'.subgroupOf U), f (g • x).out = f g + ρ g (f x.out) := fun g x => by
      rw [← hf]; apply key
      rw [QuotientGroup.out_eq', ← smul_eq_mul, ← MulAction.Quotient.smul_coe, QuotientGroup.out_eq']
    refine ⟨-∑ x : U ⧸ U'.subgroupOf U, f x.out, fun g => ?_⟩
    have hs : ∑ x : U ⧸ U'.subgroupOf U, f (g • x).out = ∑ x : U ⧸ U'.subgroupOf U, f x.out :=
      Equiv.sum_comp (MulAction.toPerm g) (fun x : U ⧸ U'.subgroupOf U => f x.out)
    simp only [step, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ] at hs
    rw [← map_sum] at hs
    rw [Subgroup.relIndex, Subgroup.index, Nat.card_eq_fintype_card, map_neg, sub_neg_eq_add,
      eq_sub_of_add_eq hs]
    abel
  obtain ⟨s, hs⟩ := aux
  have e0 : U'.relIndex U • (Submodule.Quotient.mk z : H1U ρ U) = Submodule.Quotient.mk (U'.relIndex U • z) :=
    (map_nsmul (Submodule.mkQ _) _ z).symm
  rw [e0, Submodule.Quotient.mk_eq_zero]
  refine (mem_B1 _ _).2 ⟨s + U'.relIndex U • m, fun g => ?_⟩
  have e : U'.relIndex U • (z.1 g - (ρ g m - m)) = ρ g s - s := hs g
  show U'.relIndex U • z.1 g = ρ g (s + U'.relIndex U • m) - (s + U'.relIndex U • m)
  rw [smul_sub, smul_sub, sub_eq_iff_eq_add] at e
  rw [e, map_add, map_nsmul]; abel

private theorem len_ker_eq_coker {R A : Type} [CommRing R] [AddCommGroup A] [Module R A]
    (f : A →ₗ[R] A) (hfin : Module.length R A ≠ ⊤) :
    Module.length R (A ⧸ LinearMap.range f) = Module.length R (LinearMap.ker f) := by
  have h1 := Module.length_eq_add_of_exact (LinearMap.range f).subtype (LinearMap.range f).mkQ
    (Submodule.subtype_injective _) (Submodule.mkQ_surjective _) (LinearMap.exact_subtype_mkQ _)
  have h2 := Module.length_eq_add_of_exact (LinearMap.ker f).subtype (LinearMap.ker f).mkQ
    (Submodule.subtype_injective _) (Submodule.mkQ_surjective _) (LinearMap.exact_subtype_mkQ _)
  rw [(f.quotKerEquivRange).length_eq] at h2
  have h3 : Module.length R (LinearMap.range f) ≠ ⊤ := fun h => hfin (by rw [h, top_add] at h1; exact h1)
  rw [h1, add_comm] at h2
  exact (WithTop.add_right_inj h3).1 h2

private theorem len_sup_ne_top {R A : Type} [CommRing R] [AddCommGroup A] [Module R A]
    (S T : Submodule R A) (hS : Module.length R S ≠ ⊤) (hT : Module.length R T ≠ ⊤) :
    Module.length R (S ⊔ T : Submodule R A) ≠ ⊤ := by
  have h := Module.length_le_of_surjective (S.subtype.coprod T.subtype).rangeRestrict
    (LinearMap.surjective_rangeRestrict _)
  rw [LinearMap.range_coprod, Submodule.range_subtype, Submodule.range_subtype, Module.length_prod] at h
  exact ne_top_of_le_ne_top (WithTop.add_ne_top.2 ⟨hS, hT⟩) h

private theorem len_map_le {R N : Type} [CommRing R] [AddCommGroup N] [Module R N] (a : R)
    (F : Submodule R N) (hF : Module.length R F ≠ ⊤) :
    Module.length R (F.map (LinearMap.range (a • (LinearMap.id : N →ₗ[R] N))).mkQ) ≤
      Module.length R (LinearMap.ker (a • (LinearMap.id : N →ₗ[R] N))) := by
  set P := LinearMap.range (a • (LinearMap.id : N →ₗ[R] N))
  let g := P.mkQ.submoduleMap F
  have hle : LinearMap.range (a • (LinearMap.id : F →ₗ[R] F)) ≤ LinearMap.ker g := by
    rintro _ ⟨x, rfl⟩; refine Subtype.ext ?_
    show P.mkQ (a • (x : N)) = 0; exact (Submodule.Quotient.mk_eq_zero _).2 ⟨x, rfl⟩
  refine (Module.length_le_of_surjective (Submodule.liftQ _ g hle) fun y => by
    obtain ⟨x, rfl⟩ := LinearMap.submoduleMap_surjective P.mkQ F y
    exact ⟨Submodule.Quotient.mk x, rfl⟩).trans ?_
  rw [len_ker_eq_coker _ hF]
  exact Module.length_le_of_injective
    (F.subtype.restrict (p := LinearMap.ker (a • (LinearMap.id : F →ₗ[R] F)))
      (q := LinearMap.ker (a • (LinearMap.id : N →ₗ[R] N))) fun _ hx => congrArg Subtype.val hx)
    fun _ _ h => Subtype.ext (Subtype.ext (congrArg (fun z : LinearMap.ker (a • (LinearMap.id : N →ₗ[R] N)) => (z : N)) h))

theorem lenCokerLe :
    ∀ (R N : Type) [CommRing R] [AddCommGroup N] [Module R N],
      (∀ m : N, Module.length R (Submodule.span R {m}) ≠ ⊤) → ∀ a : R,
      Module.length R (N ⧸ LinearMap.range (a • (LinearMap.id : N →ₗ[R] N))) ≤
        Module.length R (LinearMap.ker (a • (LinearMap.id : N →ₗ[R] N))) := by
  intro R N _ _ _ hN a
  by_contra hlt
  rw [not_le] at hlt
  set P := LinearMap.range (a • (LinearMap.id : N →ₗ[R] N))
  set K := LinearMap.ker (a • (LinearMap.id : N →ₗ[R] N))
  have key : ∀ k : ℕ, ∃ F : Submodule R N, Module.length R F ≠ ⊤ ∧
      (k : ℕ∞) ≤ Module.length R (F.map P.mkQ) := fun k => by
    induction k with
    | zero => exact ⟨⊥, by simp, by simp⟩
    | succ k ih =>
      obtain ⟨F, hF, hk⟩ := ih
      have h1 : Module.length R (F.map P.mkQ) ≤ Module.length R K := len_map_le a F hF
      have h2 : F.map P.mkQ ≠ ⊤ := fun h => by rw [h, Module.length_top] at h1; exact absurd hlt (not_lt.2 h1)
      obtain ⟨y, hy⟩ : ∃ y, y ∉ F.map P.mkQ := by
        by_contra hh; exact h2 (eq_top_iff.2 fun y _ => by_contra fun h => hh ⟨y, h⟩)
      obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective P y
      refine ⟨F ⊔ Submodule.span R {x}, len_sup_ne_top _ _ hF (hN x), ?_⟩
      have h3 : F.map P.mkQ < (F ⊔ Submodule.span R {x}).map P.mkQ :=
        lt_of_le_of_ne (Submodule.map_mono le_sup_left) fun h =>
          hy (h ▸ Submodule.mem_map_of_mem (Submodule.mem_sup_right (Submodule.mem_span_singleton_self x)))
      have h4 : Order.height (F.map P.mkQ) < ⊤ := by
        rw [← Module.length_submodule]; exact lt_of_le_of_lt h1 (lt_of_lt_of_le hlt le_top)
      have h5 := Order.height_strictMono h3 h4
      rw [← Module.length_submodule, ← Module.length_submodule] at h5
      rw [Nat.cast_succ]
      exact Order.add_one_le_of_lt (lt_of_le_of_lt hk h5)
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 (lt_of_lt_of_le hlt le_top).ne
  obtain ⟨F, hF, hk⟩ := key (n + 1)
  have h := hk.trans (len_map_le a F hF)
  rw [← hn] at h
  exact absurd (Nat.cast_le.1 h) (by omega)

theorem kerResCyc :
    ∀ (R G M : Type) [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
      [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M]
      [ContinuousConstSMul R M] [DiscreteTopology M] (ρ : Representation R G M),
      ContAction ρ → ∀ (U' U : Subgroup G) (h : U' ≤ U) [(U'.subgroupOf U).Normal] (γ : G),
      γ ∈ U → U ≤ (Subgroup.zpowers γ ⊔ U').topologicalClosure →
      (Module.length R (H0U ρ U') ≠ ⊤ → Module.length R (LinearMap.ker (resU ρ h)) ≤ Module.length R (H0U ρ U)) ∧
      ((∀ m ∈ H0U ρ U', ∃ m' ∈ H0U ρ U', ρ γ m' - m' = m) → Function.Injective (resU ρ h)) := by
  intro R G M _ _ _ _ _ _ _ _ _ _ ρ hρ U' U h _ γ hγ hcl
  have memU : ∀ (V : Subgroup G) (m : M), m ∈ H0U ρ V ↔ ∀ g ∈ V, ρ g m = m := fun V m => by
    simp [H0U, H0, Representation.mem_invariants]
  have hinv : ∀ m ∈ H0U ρ U', ρ γ m ∈ H0U ρ U' := fun m hm => by
    rw [memU] at hm ⊢; intro u hu
    have hc := Subgroup.Normal.conj_mem ‹(U'.subgroupOf U).Normal› ⟨u, h hu⟩
      (Subgroup.mem_subgroupOf.mpr hu) (⟨γ, hγ⟩⁻¹)
    rw [Subgroup.mem_subgroupOf] at hc
    simp only [inv_inv, Subgroup.coe_mul, InvMemClass.coe_inv] at hc
    have e : ρ u (ρ γ m) = ρ γ (ρ (γ⁻¹ * u * γ) m) := by
      rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]; congr 2; group
    rw [e, hm _ hc]
  let T : H0U ρ U' →ₗ[R] H0U ρ U' := LinearMap.codRestrict (H0U ρ U')
    ((ρ γ - LinearMap.id) ∘ₗ (H0U ρ U').subtype) (fun m => Submodule.sub_mem _ (hinv m m.2) m.2)
  have hT : ∀ m : H0U ρ U', ((T m : H0U ρ U') : M) = ρ γ m - m := fun _ => rfl
  obtain ⟨φ, hφ⟩ := kerResGen1 R G M ρ hρ U' U h γ hγ hcl T hT
  refine ⟨fun hfin => ?_, fun hsurj => ?_⟩
  · have hfix : ∀ m : H0U ρ U', T m = 0 → (m : M) ∈ H0U ρ U := fun m hm0 => by
      have hγm : ρ γ m = m := sub_eq_zero.mp (by rw [← hT m]; exact congrArg Subtype.val hm0)
      let S : Subgroup G :=
        { carrier := {g | ρ g m = m}
          mul_mem' := fun ha hb => by simp only [Set.mem_ofPred_eq, map_mul, Module.End.mul_apply] at *; rw [hb, ha]
          one_mem' := by simp
          inv_mem' := fun {a} ha => by
            simp only [Set.mem_ofPred_eq] at *
            calc ρ a⁻¹ m = ρ a⁻¹ (ρ a m) := by rw [ha]
              _ = m := by rw [← Module.End.mul_apply, ← map_mul]; simp }
      have hScl : IsClosed (S : Set G) :=
        IsClosed.preimage (hρ.comp (Continuous.prodMk continuous_id continuous_const)) (isClosed_singleton (x := (m : M)))
      have hUS := hcl.trans (Subgroup.topologicalClosure_minimal _
        (sup_le (Subgroup.zpowers_le.mpr hγm) fun u hu => (memU U' m).mp m.2 u hu) hScl)
      exact (memU U m).mpr fun g hg => hUS hg
    let ι : LinearMap.ker T →ₗ[R] H0U ρ U :=
      LinearMap.codRestrict (H0U ρ U) ((H0U ρ U').subtype ∘ₗ (LinearMap.ker T).subtype) (fun m => hfix m m.2)
    have hι : Function.Injective ι := fun _ _ hab => Subtype.ext (Subtype.ext (congrArg (fun z : H0U ρ U => (z : M)) hab))
    have hker_coker : Module.length R (H0U ρ U' ⧸ LinearMap.range T) = Module.length R (LinearMap.ker T) := by
      have h1 := Module.length_eq_add_of_exact (LinearMap.range T).subtype (LinearMap.range T).mkQ
        (Submodule.subtype_injective _) (Submodule.mkQ_surjective _) (LinearMap.exact_subtype_mkQ _)
      have h2 := Module.length_eq_add_of_exact (LinearMap.ker T).subtype (LinearMap.ker T).mkQ
        (Submodule.subtype_injective _) (Submodule.mkQ_surjective _) (LinearMap.exact_subtype_mkQ _)
      rw [(T.quotKerEquivRange).length_eq] at h2
      have h3 : Module.length R (LinearMap.range T) ≠ ⊤ := fun h => hfin (by rw [h, top_add] at h1; exact h1)
      rw [h1, add_comm] at h2
      exact (WithTop.add_right_inj h3).1 h2
    calc Module.length R (LinearMap.ker (resU ρ h))
        ≤ Module.length R (H0U ρ U' ⧸ LinearMap.range T) := Module.length_le_of_injective φ hφ
      _ = Module.length R (LinearMap.ker T) := hker_coker
      _ ≤ Module.length R (H0U ρ U) := Module.length_le_of_injective ι hι
  · have hq : ∀ x : H0U ρ U' ⧸ LinearMap.range T, x = 0 := fun x => by
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      rw [Submodule.Quotient.mk_eq_zero]
      obtain ⟨m', hm', he⟩ := hsurj y y.2
      exact ⟨⟨m', hm'⟩, Subtype.ext (by rw [hT]; exact he)⟩
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro x hx
    have e : (x : H1U ρ U) = 0 := congrArg Subtype.val (@hφ ⟨x, hx⟩ 0 (by rw [hq (φ _), hq (φ 0)]))
    rw [Submodule.mem_bot]; exact e

private theorem len_le_pi {R Z M ι : Type} [CommRing R] [AddCommGroup Z] [Module R Z]
    [AddCommGroup M] [Module R M] [Fintype ι] (ev : Z →ₗ[R] (ι → M)) (hev : Function.Injective ev)
    (W : Submodule R Z) (H : ι → Submodule R M) (hW : ∀ z ∈ W, ∀ i, ev z i ∈ H i) :
    Module.length R W ≤ ∑ i, Module.length R (H i) := by
  rw [← Module.length_pi_of_fintype]
  let φ : W →ₗ[R] (∀ i, H i) := LinearMap.pi fun i =>
    LinearMap.codRestrict (H i) ((LinearMap.proj i).comp (ev.comp W.subtype)) fun z => hW z.1 z.2 i
  exact Module.length_le_of_injective φ fun _ _ hxy =>
    Subtype.ext (hev (funext fun i => congrArg Subtype.val (congrFun hxy i)))

theorem kerResAb :
    ∀ (R G M : Type) [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
      [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M]
      [ContinuousConstSMul R M] [DiscreteTopology M] (ρ : Representation R G M)
      [IsPrincipalIdealRing R], ContAction ρ →
      (∀ m : M, Module.length R (Submodule.span R {m}) ≠ ⊤) →
      (∀ g, ∃ c : R, ∀ m, ρ g m = c • m) → ∀ (U' U : Subgroup G) (h : U' ≤ U),
      (∀ a ∈ U, ∀ b ∈ U, a * b * a⁻¹ * b⁻¹ ∈ U') → ∀ T : Finset G, (T : Set G) ⊆ U →
      U ≤ (Subgroup.closure (T : Set G) ⊔ U').topologicalClosure →
      Module.length R (LinearMap.ker (resU ρ h)) ≤ T.card * Module.length R (H0U ρ U) := by
  intro R G M _ _ _ _ _ _ _ _ _ _ ρ _ hρ hM hc U' U h hab T hT hU
  choose c hc using hc
  have hρU : ContAction (ρ.comp U.subtype : Representation R U M) :=
    hρ.comp ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  let Z0 : Submodule R (Z1U ρ U) := Z0Sub ρ U' U
  have hcoc : ∀ (z : Z1U ρ U) (u v : U), z.1 (u * v) = z.1 u + ρ u (z.1 v) := fun z u v => z.2.2 u v
  let ev : Z0 →ₗ[R] (T → M) := LinearMap.pi fun t =>
    (LinearMap.proj (⟨t.1, hT t.2⟩ : U)).comp ((Z1U ρ U).subtype.comp Z0.subtype)
  have hev : Function.Injective ev := by
    rw [injective_iff_map_eq_zero]; intro z hz
    have h1 : z.1.1 1 = 0 := z.2 1 U'.one_mem
    let K : Subgroup U :=
      { carrier := {u | z.1.1 u = 0}, one_mem' := h1
        mul_mem' := fun {u v} hu hv => by show z.1.1 (u * v) = 0; rw [hcoc, hu, hv, map_zero, add_zero]
        inv_mem' := fun {u} hu => by
          have e := hcoc z.1 u⁻¹ u; rw [inv_mul_cancel, h1, hu, map_zero, add_zero] at e; exact e.symm }
    have hK : IsClosed (K : Set U) := isClosed_eq z.1.2.1 continuous_const
    have hle : Subgroup.closure (T : Set G) ⊔ U' ≤ K.map U.subtype := sup_le
      ((Subgroup.closure_le _).2 fun t ht => ⟨⟨t, hT ht⟩, congrFun hz ⟨t, ht⟩, rfl⟩)
      (fun u hu => ⟨⟨u, h hu⟩, z.2 _ hu, rfl⟩)
    refine Subtype.ext (Subtype.ext (funext fun u => ?_))
    have : u ∈ closure (K : Set U) := by
      rw [Topology.IsInducing.subtypeVal.closure_eq_preimage_closure_image]
      exact closure_mono hle (hU u.2)
    rwa [hK.closure_eq] at this
  let π : Z0 →ₗ[R] LinearMap.ker (resU ρ h) :=
    LinearMap.codRestrict _ ((Submodule.mkQ _).comp Z0.subtype) fun z =>
      (resU_mk_eq_zero ρ h z.1).2 ⟨0, fun u => by rw [z.2 _ u.2]; simp⟩
  have hπ : Function.Surjective π := fun ⟨x, hx⟩ => by
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨m, hm⟩ := (resU_mk_eq_zero ρ h z).1 hx
    let b : Z1U ρ U := ⟨d0 _ m, coboundaries_le_cocycles _ hρU ⟨m, rfl⟩⟩
    exact ⟨⟨z - b, fun u hu => sub_eq_zero.2 (hm ⟨u.1, hu⟩)⟩, Subtype.ext
      ((mk_eq_mk ρ U (z - b) z).2 ⟨-m, fun u => by show z.1 u - (ρ u m - m) - z.1 u = _; rw [map_neg]; abel⟩)⟩
  obtain ⟨a, ha⟩ := (IsPrincipalIdealRing.principal (Ideal.span (Set.range fun u : U => c u - 1))).principal
  have hkill : ∀ (u : U) (z : Z0), π ((c u - 1) • z) = 0 := fun u z =>
    Subtype.ext ((Submodule.Quotient.mk_eq_zero _).2 ((mem_B1 _ _).2 ⟨z.1.1 u, fun g => by
      show (c u - 1) • z.1.1 g = ρ g (z.1.1 u) - z.1.1 u
      have e0 : u * g = (u * g * u⁻¹ * g⁻¹) * (g * u) := by group
      have e1 : ρ ((u * g * u⁻¹ * g⁻¹ : U) : G) = 1 := by
        have : ρ u * ρ g = ρ g * ρ u := by ext m; simp only [Module.End.mul_apply, hc, smul_smul, mul_comm]
        rw [show ((u * g * u⁻¹ * g⁻¹ : U) : G) = u * g * ((u : G)⁻¹ * (g : G)⁻¹) by simp [mul_assoc],
          map_mul, map_mul, this, ← map_mul, ← map_mul]; simp
      have e2 : z.1.1 (u * g) = z.1.1 (g * u) := by
        rw [e0, hcoc, e1, z.2 _ (hab u u.2 g g.2)]; simp
      rw [hcoc, hcoc, hc u] at e2; rw [sub_smul, one_smul, eq_sub_of_add_eq' e2]; abel⟩))
  have hamem : a ∈ Ideal.span (Set.range fun u : U => c u - 1) := ha ▸ Submodule.mem_span_singleton_self a
  have hZ : ∀ z : Z0, Module.length R (Submodule.span R {z}) ≠ ⊤ := fun z =>
    ne_top_of_le_ne_top (WithTop.sum_ne_top.2 fun _ _ => hM _)
      (len_le_pi ev hev _ (fun i => Submodule.span R {ev z i}) fun w hw i => by
        obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.1 hw
        rw [map_smul]; exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))
  have h1 := lenCokerLe R Z0 hZ a
  have h2 := len_le_pi ev hev (LinearMap.ker (a • (LinearMap.id : Z0 →ₗ[R] Z0))) (fun _ => H0U ρ U) fun z hz i => by
    have hza : a • ev z i = 0 := congrFun (congrArg ev hz) i
    rw [H0U, H0, Representation.mem_invariants]; intro u
    have hcu : c u - 1 ∈ Ideal.span (Set.range fun u : U => c u - 1) := Ideal.subset_span ⟨u, rfl⟩
    rw [ha] at hcu
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1 hcu
    have e : (c u - 1) • ev z i = 0 := by rw [← hr, smul_assoc, hza, smul_zero]
    show ((ρ.comp U.subtype) u) (ev z i) = ev z i
    simp only [MonoidHom.comp_apply, Subgroup.coe_subtype]
    rw [hc, ← sub_eq_zero, ← e, sub_smul, one_smul]
  have h3 : Module.length R (LinearMap.ker (resU ρ h)) ≤
      Module.length R (Z0 ⧸ LinearMap.range (a • (LinearMap.id : Z0 →ₗ[R] Z0))) :=
    Module.length_le_of_surjective (Submodule.liftQ _ π (by
      rintro _ ⟨z, rfl⟩
      exact Submodule.span_induction (p := fun r _ => π (r • z) = 0)
        (fun _ h => by obtain ⟨u, rfl⟩ := h; exact hkill u z) (by simp) (fun _ _ _ _ hx hy => by rw [add_smul, map_add, hx, hy, add_zero])
        (fun _ _ _ hx => by rw [smul_assoc, map_smul, hx, smul_zero]) hamem))
      fun k => by obtain ⟨z, rfl⟩ := hπ k; exact ⟨Submodule.Quotient.mk z, rfl⟩
  refine h3.trans (h1.trans (h2.trans ?_))
  simp

end KerResAndCorestriction

section SelUpLocalDownUnitEigBase

private theorem len_le_add_of_inj {R A B C D : Type} [CommRing R] [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C] [AddCommGroup D] [Module R D]
    (g : A →ₗ[R] B) (j : A →ₗ[R] C) (k : C →ₗ[R] D) (hj : Function.Injective j)
    (hk : ∀ x, g x = 0 → k (j x) = 0) :
    Module.length R A ≤ Module.length R B + Module.length R (LinearMap.ker k) := by
  have h1 : Module.length R A = Module.length R (LinearMap.ker g) + Module.length R (LinearMap.range g) :=
    Module.length_eq_add_of_exact (LinearMap.ker g).subtype g.rangeRestrict (Submodule.injective_subtype _)
      g.surjective_rangeRestrict (by rw [LinearMap.exact_iff, LinearMap.ker_rangeRestrict, Submodule.range_subtype])
  rw [h1, add_comm]
  exact add_le_add (Module.length_le_of_injective _ (Submodule.injective_subtype _))
    (Module.length_le_of_injective (j.restrict (p := LinearMap.ker g) (q := LinearMap.ker k) hk)
      fun _ _ e => Subtype.ext (hj (congrArg Subtype.val e)))

theorem selUp :
    ∀ (R G M : Type) [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
      [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M]
      [ContinuousConstSMul R M] [DiscreteTopology M] (ρ : Representation R G M)
      (U' U : Subgroup G) (h : U' ≤ U) (𝒟 : Set (Subgroup G)) (h𝒟 : ConjStable 𝒟),
      Module.length R (LocSel ρ U 𝒟) ≤ Module.length R (LocSel ρ U' 𝒟) + Module.length R (LinearMap.ker (resU ρ h)) ∧
      (∀ [U'.Normal], Module.length R (LocSel ρ U 𝒟) ≤
        Module.length R (selEig ρ U' h𝒟 U 1) + Module.length R (LinearMap.ker (resU ρ h))) ∧
      (∀ [U'.Normal] [U.Normal] (W : Subgroup G) (ψ : W →* Rˣ),
        Module.length R (selEig ρ U h𝒟 W ψ) ≤
          Module.length R (selEig ρ U' h𝒟 W ψ) + Module.length R (LinearMap.ker (resU ρ h))) ∧
      ∀ [U'.Normal] [U.Normal] (g : G) (s : R),
        Module.length R (Module.End.eigenspace (selRep ρ U h𝒟 g) s) ≤
          Module.length R (Module.End.eigenspace (selRep ρ U' h𝒟 g) s) + Module.length R (LinearMap.ker (resU ρ h)) := by
  intro R G M _ _ _ _ _ _ _ _ _ _ ρ U' U h 𝒟 h𝒟
  have hj := Submodule.injective_subtype (LocSel ρ U 𝒟)
  have hk : ∀ x, selRes ρ h 𝒟 x = 0 → resU ρ h ((LocSel ρ U 𝒟).subtype x) = 0 :=
    fun x hx => congrArg Subtype.val hx
  refine ⟨len_le_add_of_inj (selRes ρ h 𝒟) _ _ hj hk, ?_, ?_, ?_⟩
  · intro _
    have hm : ∀ x, selRes ρ h 𝒟 x ∈ selEig ρ U' h𝒟 U 1 := fun x => by
      rw [selEig, eig_one]; intro g; exact Subtype.ext (restriction_mem_invariant_H1 ρ h x.1 g)
    exact len_le_add_of_inj ((selRes ρ h 𝒟).codRestrict _ hm) _ _ hj fun x hx => hk x (congrArg Subtype.val hx)
  · intro _ _ W ψ
    refine len_le_add_of_inj ((selRes ρ h 𝒟).restrict fun x hx => ?_)
      ((LocSel ρ U 𝒟).subtype.comp (selEig ρ U h𝒟 W ψ).subtype) _
      (hj.comp (Submodule.injective_subtype _)) fun x hx => hk x.1 (congrArg Subtype.val hx)
    rw [mem_eig] at hx ⊢; intro g
    have hxg := hx g; simp only [MonoidHom.comp_apply, Subgroup.coe_subtype] at hxg
    show selRep ρ U' h𝒟 g.1 _ = _; rw [← selRes_selRep, hxg, map_smul]
  · intro _ _ g s
    refine len_le_add_of_inj ((selRes ρ h 𝒟).restrict fun x hx => ?_)
      ((LocSel ρ U 𝒟).subtype.comp (Module.End.eigenspace (selRep ρ U h𝒟 g) s).subtype) _
      (hj.comp (Submodule.injective_subtype _)) fun x hx => hk x.1 (congrArg Subtype.val hx)
    rw [Module.End.mem_eigenspace_iff] at hx ⊢; rw [← selRes_selRep, hx, map_smul]

theorem selLocal :
    ∀ (R G M : Type) [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
      [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M]
      [ContinuousConstSMul R M] [DiscreteTopology M] (ρ : Representation R G M)
      (U' U : Subgroup G) (h : U' ≤ U) (𝒟 : Set (Subgroup G)) (ι : Type) [Fintype ι]
      (D : ι → Subgroup G), (∀ i, D i ∈ 𝒟) →
      (∀ D' ∈ 𝒟, U ⊓ D' ≤ U' ∨ ∃ i, ∃ u ∈ U, ∀ x ∈ U ⊓ D', u⁻¹ * x * u ∈ D i) →
      Module.length R ((LocSel ρ U' 𝒟).comap (resU ρ h)) ≤
        Module.length R (LocSel ρ U 𝒟) + ∑ i, Module.length R (LinearMap.ker (resU ρ (inf_le_inf_right (D i) h))) := by
  intro R G M _ _ _ _ _ _ _ _ _ _ ρ U' U h 𝒟 ι _ D hD hcov
  set X := (LocSel ρ U' 𝒟).comap (resU ρ h)
  have key0 : ∀ x ∈ X, ∀ D' ∈ 𝒟, resU ρ (le_trans inf_le_left h : U' ⊓ D' ≤ U) x = 0 :=
    fun x hx D' hD' => by have e := (mem_locSel.mp (Submodule.mem_comap.mp hx)) D' hD'; rwa [resU_resU] at e
  let f : X →ₗ[R] (∀ i, LinearMap.ker (resU ρ (inf_le_inf_right (D i) h))) :=
    LinearMap.pi fun i => LinearMap.codRestrict _ ((resU ρ (inf_le_left : U ⊓ D i ≤ U)).comp X.subtype)
      (fun x => LinearMap.mem_ker.mpr (by
        change resU ρ (inf_le_inf_right (D i) h) (resU ρ (inf_le_left : U ⊓ D i ≤ U) x.1) = 0
        rw [resU_resU]; exact key0 x.1 x.2 (D i) (hD i)))
  have hmem : ∀ y ∈ LinearMap.ker f, (y : H1U ρ U) ∈ LocSel ρ U 𝒟 := fun y hy => by
    have hy' : ∀ i, resU ρ (inf_le_left : U ⊓ D i ≤ U) (y : H1U ρ U) = 0 := fun i => by
      simpa [f] using congrArg Subtype.val (congrFun (LinearMap.mem_ker.mp hy) i)
    rw [mem_locSel]; intro D' hD'
    rcases hcov D' hD' with hle | ⟨i, u, hu, hconj⟩
    · have e := resU_resU ρ (le_inf hle inf_le_right : U ⊓ D' ≤ U' ⊓ D') (le_trans inf_le_left h) (y : H1U ρ U)
      rw [key0 _ y.2 D' hD', map_zero] at e; exact e.symm
    · obtain ⟨z, hz⟩ := Submodule.Quotient.mk_surjective _ (y : H1U ρ U)
      have h0 := hy' i; rw [← hz] at h0 ⊢; rw [resU_mk_eq_zero] at h0 ⊢
      obtain ⟨m, hm⟩ := h0
      refine ⟨ρ u m - z.1 ⟨u, hu⟩, fun v => ?_⟩
      have hvU : (v : G) ∈ U := (Subgroup.mem_inf.mp v.2).1
      have hwU : u⁻¹ * (v : G) * u ∈ U := U.mul_mem (U.mul_mem (U.inv_mem hu) hvU) hu
      have e1 : z.1 ⟨u⁻¹ * (v : G) * u, hwU⟩ = ρ (u⁻¹ * (v : G) * u) m - m :=
        hm ⟨u⁻¹ * (v : G) * u, Subgroup.mem_inf.mpr ⟨hwU, hconj v v.2⟩⟩
      have c1 := z.2.2 ⟨v, hvU⟩ ⟨u, hu⟩
      have c2 := z.2.2 ⟨u, hu⟩ ⟨u⁻¹ * (v : G) * u, hwU⟩
      have eq : (⟨v, hvU⟩ * ⟨u, hu⟩ : U) = ⟨u, hu⟩ * ⟨u⁻¹ * (v : G) * u, hwU⟩ := Subtype.ext (by simp [mul_assoc])
      rw [eq, c2, e1] at c1
      simp only [MonoidHom.comp_apply, Subgroup.coe_subtype] at c1
      have hr : ρ u (ρ (u⁻¹ * (v : G) * u) m) = ρ v (ρ u m) := by
        rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]; congr 2; group
      rw [map_sub, hr] at c1
      show z.1 ⟨v, hvU⟩ = _; rw [eq_sub_of_add_eq c1.symm]; simp only [map_sub]; abel
  let g : LinearMap.ker f →ₗ[R] LocSel ρ U 𝒟 :=
    LinearMap.codRestrict _ (X.subtype.comp (LinearMap.ker f).subtype) (fun y => hmem y.1 y.2)
  have hex : Module.length R X = Module.length R (LinearMap.ker f) + Module.length R (LinearMap.range f) :=
    Module.length_eq_add_of_exact (LinearMap.ker f).subtype f.rangeRestrict (Submodule.injective_subtype _)
      f.surjective_rangeRestrict (by rw [LinearMap.exact_iff, LinearMap.ker_rangeRestrict, Submodule.range_subtype])
  rw [hex, ← Module.length_pi_of_fintype]
  exact add_le_add
    (Module.length_le_of_injective g fun _ _ hab => Subtype.ext (Subtype.ext (congrArg (fun z : LocSel ρ U 𝒟 => (z : H1U ρ U)) hab)))
    (Module.length_le_of_injective (LinearMap.range f).subtype (Submodule.subtype_injective _))

theorem selDown :
    ∀ (R G M : Type) [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
      [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M]
      [ContinuousConstSMul R M] [DiscreteTopology M] (ρ : Representation R G M)
      (U' U : Subgroup G) [U'.Normal] (h : U' ≤ U) (𝒟 : Set (Subgroup G)) (h𝒟 : ConjStable 𝒟)
      (ι : Type) [Fintype ι] (D : ι → Subgroup G), (∀ i, D i ∈ 𝒟) →
      (∀ D' ∈ 𝒟, U ⊓ D' ≤ U' ∨ ∃ i, ∃ u ∈ U, ∀ x ∈ U ⊓ D', u⁻¹ * x * u ∈ D i) →
      Module.length R (selEig ρ U' h𝒟 U 1) ≤
        Module.length R (LocSel ρ U 𝒟) +
          ∑ i, Module.length R (LinearMap.ker (resU ρ (inf_le_inf_right (D i) h))) +
          Module.length R (resCoker ρ h) := by
  intro R G M _ _ _ _ _ _ _ _ _ _ ρ U' U _ h 𝒟 h𝒟 ι _ D hD hcov
  have hinv : ∀ x : selEig ρ U' h𝒟 U 1, ((x : LocSel ρ U' 𝒟) : H1U ρ U') ∈ invariantsUnderSubgroupH1 ρ U U' :=
    fun x => (Representation.mem_invariants _ _).2 fun u => by
      have := (mem_eig.mp x.2) u
      simpa [selRep, Representation.subrepresentation] using congrArg Subtype.val this
  let j : selEig ρ U' h𝒟 U 1 →ₗ[R] H1U ρ U' :=
    (LocSel ρ U' 𝒟).subtype.comp (selEig ρ U' h𝒟 U 1).subtype
  let g : selEig ρ U' h𝒟 U 1 →ₗ[R] resCoker ρ h :=
    (Submodule.mkQ _).comp (LinearMap.codRestrict (invariantsUnderSubgroupH1 ρ U U') j hinv)
  let A := Submodule.comap (resU ρ h) (LocSel ρ U' 𝒟)
  have hj : Function.Injective j := fun _ _ hab => Subtype.ext (Subtype.ext hab)
  have hker : ∀ x, g x = 0 → j x ∈ LinearMap.range ((resU ρ h).comp A.subtype) := fun x hx => by
    obtain ⟨y, hy⟩ := (Submodule.Quotient.mk_eq_zero _).mp hx
    exact ⟨⟨y, by show resU ρ h y ∈ LocSel ρ U' 𝒟; rw [hy]; exact (x : LocSel ρ U' 𝒟).2⟩, hy⟩
  have hex : Function.Exact (LinearMap.ker g).subtype g.rangeRestrict := fun x =>
    ⟨fun hx => ⟨⟨x, by simpa [LinearMap.mem_ker] using congrArg Subtype.val hx⟩, rfl⟩,
     fun ⟨y, hy⟩ => hy ▸ Subtype.ext (by simp)⟩
  rw [Module.length_eq_add_of_exact (LinearMap.ker g).subtype g.rangeRestrict
    (Submodule.subtype_injective _) g.surjective_rangeRestrict hex]
  have hleft : Module.length R (LinearMap.ker g) ≤
      Module.length R (LocSel ρ U 𝒟) + ∑ i, Module.length R (LinearMap.ker (resU ρ (inf_le_inf_right (D i) h))) :=
    ((Module.length_le_of_injective
      ((j.comp (LinearMap.ker g).subtype).codRestrict _ (fun x => hker x x.2))
      fun _ _ hab => Subtype.ext (hj (congrArg (fun z : LinearMap.range ((resU ρ h).comp A.subtype) => (z : H1U ρ U')) hab))).trans
      (Module.length_le_of_surjective _ ((resU ρ h).comp A.subtype).surjective_rangeRestrict)).trans
      (selLocal R G M ρ U' U h 𝒟 ι D hD hcov)
  exact add_le_add hleft (Module.length_le_of_injective (LinearMap.range g).subtype (Submodule.subtype_injective _))

private theorem relIndex_inf_dvd {G : Type} [Group G] (U' U D : Subgroup G) [U'.Normal] :
    (U' ⊓ D).relIndex (U ⊓ D) ∣ U'.relIndex U := by
  have e : (U' ⊓ D).relIndex (U ⊓ D) = U'.relIndex (U ⊓ D) := by
    unfold Subgroup.relIndex; congr 1; ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun h => h.1, fun h => ⟨h, x.2.2⟩⟩
  rw [e]
  have k : ∀ K : Subgroup G, U'.relIndex K = Nat.card (K.map (QuotientGroup.mk' U')) := fun K => by
    rw [← Subgroup.relIndex_ker, QuotientGroup.ker_mk']
  rw [k, k]; exact Subgroup.card_dvd_of_le (Subgroup.map_mono inf_le_left)

private theorem eq_zero_of_nsmul_unit {R N : Type} [CommRing R] [AddCommGroup N] [Module R N] {n : ℕ}
    (hn : IsUnit (n : R)) {x : N} (hx : n • x = 0) : x = 0 := by
  rw [← Nat.cast_smul_eq_nsmul R] at hx; exact (hn.smul_eq_zero).1 hx

theorem selUnit :
    ∀ (R G M : Type) [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
      [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M]
      [ContinuousConstSMul R M] [DiscreteTopology M] (ρ : Representation R G M),
      ContAction ρ → ∀ (U' U : Subgroup G) [U'.Normal] (h : U' ≤ U),
      IsOpen (U'.subgroupOf U : Set U) → IsUnit (U'.relIndex U : R) →
      ∀ (𝒟 : Set (Subgroup G)) (h𝒟 : ConjStable 𝒟),
      Function.Injective (selRes ρ h 𝒟) ∧ LinearMap.range (selRes ρ h 𝒟) = selEig ρ U' h𝒟 U 1 := by
  intro R G M _ _ _ _ _ _ _ _ _ _ ρ hρ U' U _ h hop hu 𝒟 h𝒟
  refine ⟨?_, ?_⟩
  · rw [injective_iff_map_eq_zero]; intro x hx
    exact Subtype.ext (eq_zero_of_nsmul_unit hu (kerResSmul R G M ρ U' U h x.1 (congrArg Subtype.val hx)))
  · ext y; rw [selEig, eig_one]
    constructor
    · rintro ⟨x, rfl⟩ g; exact Subtype.ext (restriction_mem_invariant_H1 ρ h x.1 g)
    · intro hy
      have h1 := corInv R G M ρ hρ U' U h hop y.1 (fun g => congrArg Subtype.val (hy g))
      rw [← Nat.cast_smul_eq_nsmul R] at h1
      obtain ⟨v, hv⟩ := hu.exists_left_inv
      have h2 := Submodule.smul_mem _ v h1
      rw [smul_smul, hv, one_smul] at h2
      obtain ⟨x, hx⟩ := h2
      have hxs : x ∈ LocSel ρ U 𝒟 := by
        rw [mem_locSel]; intro D hD
        refine eq_zero_of_nsmul_unit (isUnit_of_dvd_unit (Nat.cast_dvd_cast (relIndex_inf_dvd U' U D)) hu)
          (kerResSmul R G M ρ _ _ (inf_le_inf_right D h) _ ?_)
        rw [resU_resU, ← resU_resU ρ inf_le_left h, hx]; exact mem_locSel.1 y.2 D hD
      exact ⟨⟨x, hxs⟩, Subtype.ext hx⟩

theorem selEigBase :
    ∀ (R G M : Type) [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
      [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M]
      [ContinuousConstSMul R M] [DiscreteTopology M] (ρ ρ' : Representation R G M)
      (θ : G →* Rˣ), (∀ g m, ρ g m = ((θ g : Rˣ) : R) • ρ' g m) → ContAction ρ' →
      ∀ (U W : Subgroup G) [U.Normal], U ≤ W → (∀ u ∈ U, θ u = 1) →
      IsOpen (U.subgroupOf W : Set W) → IsUnit (U.relIndex W : R) →
      ∀ (𝒟 : Set (Subgroup G)) (h𝒟 : ConjStable 𝒟),
      Module.length R (selEig ρ U h𝒟 W (θ.comp W.subtype)) = Module.length R (LocSel ρ' W 𝒟) := by
  intro R G M _ _ _ _ _ _ _ _ _ _ ρ ρ' θ hρ hc U W _ hUW hθ ho hu 𝒟 h𝒟
  have h1 := (selTwist R G M ρ ρ' θ hρ U hθ 𝒟 h𝒟).2 W 1
  obtain ⟨hi, hr⟩ := selUnit R G M ρ' hc U W hUW ho hu 𝒟 h𝒟
  rw [mul_one] at h1
  rw [h1, ← hr]
  exact (LinearEquiv.ofInjective _ hi).length_eq.symm

end SelUpLocalDownUnitEigBase

section H2VanishingAndTransgression

section DenseGenH2Zl

private theorem contMod (l : ℕ) [Fact l.Prime] (k : ℕ) {N : Type} [TopologicalSpace N]
    (c : ZMod (l ^ k) → N) : Continuous fun x : ℤ_[l] => c (PadicInt.toZModPow k x) := by
  apply IsLocallyConstant.continuous
  rw [IsLocallyConstant.iff_eventually_eq]; intro x
  filter_upwards [Metric.ball_mem_nhds x (zpow_pos (by exact_mod_cast (Fact.out : l.Prime).pos : (0 : ℝ) < l) (-(k : ℤ)))] with y hy
  have h1 : y - x ∈ Ideal.span {(l : ℤ_[l]) ^ k} := by
    rw [← PadicInt.norm_le_pow_iff_mem_span_pow]; rw [Metric.mem_ball, dist_eq_norm] at hy; exact hy.le
  rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, sub_eq_zero] at h1
  rw [h1]

private theorem clopenEq {X N : Type} [TopologicalSpace X] [TopologicalSpace N] [DiscreteTopology N]
    {f g : X → N} (hf : Continuous f) (hg : Continuous g) : IsClopen {x | f x = g x} :=
  (isClopen_discrete {p : N × N | p.1 = p.2}).preimage (hf.prodMk hg)

private theorem denseGen (l : ℕ) [Fact l.Prime] :
    DenseRange fun n : ℕ => (Multiplicative.ofAdd (1 : ℤ_[l])) ^ n := by
  have h : (fun n : ℕ => (Multiplicative.ofAdd (1 : ℤ_[l])) ^ n) =
      fun n : ℕ => Multiplicative.ofAdd (n : ℤ_[l]) := funext fun n => by rw [← ofAdd_nsmul, nsmul_one]
  rw [h]; exact PadicInt.denseRange_natCast

private theorem tendGen (l : ℕ) [Fact l.Prime] :
    Filter.Tendsto (fun a : ℕ => (Multiplicative.ofAdd (1 : ℤ_[l])) ^ (l ^ a)) Filter.atTop (nhds 1) := by
  have h : (fun a : ℕ => (Multiplicative.ofAdd (1 : ℤ_[l])) ^ (l ^ a)) =
      fun a : ℕ => Multiplicative.ofAdd ((l : ℤ_[l]) ^ a) := funext fun a => by
    rw [← ofAdd_nsmul, nsmul_one]; push_cast; rfl
  rw [h]
  exact tendsto_pow_atTop_nhds_zero_of_norm_lt_one (by
    rw [PadicInt.norm_p (p := l)]; exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt))

private theorem solveGen (l : ℕ) [Fact l.Prime] (R N : Type) [CommRing R] [AddCommGroup N] [Module R N]
    [TopologicalSpace N] [DiscreteTopology N] (σ : Representation R (Multiplicative ℤ_[l]) N)
    (hσ : ContAction σ) (ht : ∀ m : N, ∃ n : ℕ, l ^ n • m = 0)
    (φ : Multiplicative ℤ_[l] → N) (hφ : Continuous φ) (m₀ : N) :
    ∃ C : Multiplicative ℤ_[l] → N, Continuous C ∧ C 1 = m₀ ∧
      ∀ x, C (Multiplicative.ofAdd 1 * x) = σ (Multiplicative.ofAdd 1) (C x) - φ x := by
  let γ : Multiplicative ℤ_[l] := Multiplicative.ofAdd 1
  let a : ℕ → N := fun n => Nat.rec (motive := fun _ => N) m₀ (fun k ak => σ γ ak - φ (γ ^ k)) n
  have hσ' : Continuous fun p : Multiplicative ℤ_[l] × N => σ p.1 p.2 := hσ
  have hper : ∀ m : N, ∀ᶠ k in Filter.atTop, σ (γ ^ (l ^ k)) m = m := fun m => by
    have ht2 := ((hσ'.comp (continuous_id.prodMk (continuous_const (y := m)))).tendsto 1).comp (tendGen l)
    rw [nhds_discrete, Filter.tendsto_pure] at ht2
    simpa only [Function.comp_apply, id_eq, map_one, Module.End.one_apply] using ht2
  have hφper : ∀ᶠ k in Filter.atTop, ∀ x, φ (γ ^ (l ^ k) * x) = φ x := by
    have hev : ∀ᶠ y in nhds (1 : Multiplicative ℤ_[l]),
        ∀ x ∈ (Set.univ : Set (Multiplicative ℤ_[l])), φ (y * x) = φ x :=
      isCompact_univ.eventually_forall_of_forall_eventually fun x _ =>
        (clopenEq (hφ.comp continuous_mul) (hφ.comp continuous_snd)).isOpen.mem_nhds (by simp)
    filter_upwards [(tendGen l).eventually hev] with k hk x; exact hk x (Set.mem_univ x)
  have L1 : ∀ q : ℕ, (∀ x, φ (γ ^ q * x) = φ x) → ∀ n, a (n + q) - a n = σ (γ ^ n) (a q - a 0) := by
    intro q hq n; induction n with
    | zero => simp
    | succ n ih =>
      rw [show n + 1 + q = n + q + 1 by omega]
      dsimp only [a]; rw [pow_succ', map_mul, Module.End.mul_apply, ← ih, map_sub]
      rw [show φ (γ ^ (n + q)) = φ (γ ^ n) by rw [pow_add, mul_comm (γ ^ n), hq]]; abel
  have L2 : ∀ q : ℕ, (∀ x, φ (γ ^ q * x) = φ x) →
      ∀ s, a (s * q) - a 0 = ∑ t ∈ Finset.range s, σ (γ ^ (t * q)) (a q - a 0) := by
    intro q hq s; induction s with
    | zero => simp
    | succ s ih => rw [Finset.sum_range_succ, ← ih, ← L1 q hq (s * q), add_one_mul]; abel
  have Lmul : ∀ q : ℕ, (∀ x, φ (γ ^ q * x) = φ x) → ∀ s, ∀ x, φ (γ ^ (q * s) * x) = φ x := by
    intro q hq s; induction s with
    | zero => intro x; simp
    | succ s ih => intro x; rw [Nat.mul_succ, pow_add, mul_assoc, ih, hq]
  obtain ⟨k, hk⟩ := hφper.exists
  obtain ⟨A, hA⟩ := Filter.eventually_atTop.mp (hper (a (l ^ k) - a 0))
  have hK1 : l ^ (max A k) = l ^ k * l ^ (max A k - k) := by rw [← pow_add, Nat.add_sub_cancel' (le_max_right A k)]
  have hφQ : ∀ x, φ (γ ^ (l ^ (max A k)) * x) = φ x := by rw [hK1]; exact Lmul _ hk _
  have hdQ : a (l ^ (max A k)) - a 0 =
      ∑ t ∈ Finset.range (l ^ (max A k - k)), σ (γ ^ (t * l ^ k)) (a (l ^ k) - a 0) := by
    rw [← L2 _ hk, hK1, mul_comm (l ^ k)]
  have hfixQ : σ (γ ^ (l ^ (max A k))) (a (l ^ (max A k)) - a 0) = a (l ^ (max A k)) - a 0 := by
    rw [hdQ, map_sum]; refine Finset.sum_congr rfl fun t _ => ?_
    rw [← Module.End.mul_apply, ← map_mul, mul_comm (γ ^ (l ^ (max A k))), map_mul,
      Module.End.mul_apply, hA (max A k) (le_max_left A k)]
  obtain ⟨j, hj⟩ := ht (a (l ^ (max A k)) - a 0)
  have hφK : ∀ x, φ (γ ^ (l ^ (max A k + j)) * x) = φ x := by rw [pow_add]; exact Lmul _ hφQ _
  have haK : a (l ^ (max A k + j)) = a 0 := by
    have h2 := L2 _ hφQ (l ^ j)
    have h3 : ∀ t ∈ Finset.range (l ^ j),
        σ (γ ^ (t * l ^ (max A k))) (a (l ^ (max A k)) - a 0) = a (l ^ (max A k)) - a 0 := fun t _ => by
      rw [mul_comm t, pow_mul, map_pow, Module.End.pow_apply, Function.iterate_fixed hfixQ]
    rw [Finset.sum_congr rfl h3, Finset.sum_const, Finset.card_range, hj] at h2
    rw [pow_add, mul_comm]; exact sub_eq_zero.mp h2
  have hperiod : ∀ n, a (n + l ^ (max A k + j)) = a n := fun n => by
    have h4 := L1 _ hφK n; rw [haK, sub_self, map_zero, sub_eq_zero] at h4; exact h4
  have hperiod' : ∀ s n, a (n + l ^ (max A k + j) * s) = a n := fun s => by
    induction s with
    | zero => intro n; simp
    | succ s ih => intro n; rw [Nat.mul_succ, ← add_assoc, hperiod, ih]
  have hmod : ∀ n, a (n % l ^ (max A k + j)) = a n := fun n => by
    conv_rhs => rw [← Nat.mod_add_div n (l ^ (max A k + j))]; rw [hperiod']
  let C : Multiplicative ℤ_[l] → N :=
    fun x => a (PadicInt.toZModPow (max A k + j) (Multiplicative.toAdd x)).val
  have hCc : Continuous C := (contMod l (max A k + j) fun i : ZMod (l ^ (max A k + j)) => a i.val).comp continuous_toAdd
  have hCn : ∀ n : ℕ, C (γ ^ n) = a n := fun n => by
    simp only [C, γ, ← ofAdd_nsmul, nsmul_one, toAdd_ofAdd, map_natCast, ZMod.val_natCast]; exact hmod n
  refine ⟨C, hCc, by simp [C, a], fun x => (denseGen l).induction_on
    (p := fun x => C (Multiplicative.ofAdd 1 * x) = σ (Multiplicative.ofAdd 1) (C x) - φ x) x
    (clopenEq (hCc.comp (continuous_const_mul _))
      ((continuous_of_discreteTopology (f := fun pr : N × N => σ (Multiplicative.ofAdd 1) pr.1 - pr.2)).comp
        (hCc.prodMk hφ))).isClosed
    (fun n => by show C (γ * γ ^ n) = σ γ (C (γ ^ n)) - φ (γ ^ n); rw [← pow_succ', hCn, hCn])⟩

theorem h2Zl :
    ∀ (l : ℕ) [Fact l.Prime] (R N : Type) [CommRing R] [AddCommGroup N] [Module R N]
      [TopologicalSpace N] [IsTopologicalAddGroup N] [ContinuousConstSMul R N] [DiscreteTopology N]
      (σ : Representation R (Multiplicative ℤ_[l]) N), ContAction σ →
      (∀ m : N, ∃ n : ℕ, l ^ n • m = 0) → Subsingleton (H2 σ) := by
  intro l _ R N _ _ _ _ _ _ _ σ hσ ht
  refine subsingleton_of_forall_eq 0 fun x => ?_
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
  show f.1 ∈ B2 σ
  rw [mem_B2]
  have hf : Continuous f.1 := f.2.1
  have hcoc := f.2.2
  obtain ⟨C, hC, hC1, hCeq⟩ := solveGen l R N σ hσ ht (fun x => f.1 (Multiplicative.ofAdd 1, x)) (hf.comp ((continuous_const (y := Multiplicative.ofAdd (1 : ℤ_[l]))).prodMk continuous_id)) (f.1 (1, 1))
  refine ⟨C, hC, funext fun ⟨g, h⟩ => ?_⟩
  show σ g (C h) - C (g * h) + C g = f.1 (g, h)
  have hf1 : ∀ k, f.1 (1, k) = f.1 (1, 1) := fun k => by
    have h0 := hcoc 1 1 k; simp only [map_one, one_mul, Module.End.one_apply, sub_self, zero_add] at h0
    exact sub_eq_zero.mp h0
  have hσ' : Continuous fun p : Multiplicative ℤ_[l] × N => σ p.1 p.2 := hσ
  refine (denseGen l).induction_on (p := fun g => σ g (C h) - C (g * h) + C g = f.1 (g, h)) g
    (clopenEq (((hσ'.comp (continuous_id.prodMk continuous_const)).sub (hC.comp (continuous_mul_const h))).add hC)
      (hf.comp (continuous_id.prodMk continuous_const))).isClosed
    fun n => ?_
  induction n with
  | zero => simp only [pow_zero, map_one, Module.End.one_apply, one_mul, sub_self, zero_add]; rw [hC1, hf1 h]
  | succ n ih =>
    rw [pow_succ', mul_assoc, hCeq, hCeq, map_mul, Module.End.mul_apply]
    have hc := hcoc (Multiplicative.ofAdd 1) (Multiplicative.ofAdd 1 ^ n) h
    rw [← ih, map_add, map_sub] at hc
    rw [← sub_eq_zero, ← hc]; abel

end DenseGenH2Zl

section ContinuousSectionsAndTransgression

section ContinuousSections

private def csRel {G : Type} [Group G] (K N : Subgroup G) [hN : N.Normal] : Setoid G where
  r x y := ∃ k ∈ K, ∃ n ∈ N, y = k * n * x
  iseqv :=
    { refl := fun x => ⟨1, K.one_mem, 1, N.one_mem, by simp⟩
      symm := fun ⟨k, hk, n, hn, e⟩ =>
        ⟨k⁻¹, K.inv_mem hk, k * n⁻¹ * k⁻¹, hN.conj_mem _ (N.inv_mem hn) k, by rw [e]; group⟩
      trans := fun ⟨k, hk, n, hn, e1⟩ ⟨k', hk', n', hn', e2⟩ =>
        ⟨k' * k, K.mul_mem hk' hk, k⁻¹ * n' * k * n,
          N.mul_mem (by simpa using hN.conj_mem n' hn' k⁻¹) hn, by rw [e2, e1]; group⟩ }

private def csRep {G : Type} [Group G] (K N : Subgroup G) [N.Normal] (x : G) : G :=
  (Quotient.mk (csRel K N) x).out

private lemma csRep_eq {G : Type} [Group G] (K N : Subgroup G) [N.Normal] {x y : G}
    (h : csRel K N x y) : csRep K N x = csRep K N y := by
  unfold csRep; rw [Quotient.sound (s := csRel K N) h]

private def csTr {G : Type} [Group G] (K N : Subgroup G) [N.Normal] : Set G :=
  {y | y * (csRep K N y)⁻¹ ∈ N}

private lemma csTr_coset {G : Type} [Group G] (K N : Subgroup G) [N.Normal] {y z : G}
    (h : z * y⁻¹ ∈ N) : z ∈ csTr K N ↔ y ∈ csTr K N := by
  have hr : csRep K N z = csRep K N y := (csRep_eq K N ⟨1, K.one_mem, z * y⁻¹, h, by group⟩).symm
  show z * (csRep K N z)⁻¹ ∈ N ↔ y * (csRep K N y)⁻¹ ∈ N
  rw [hr, show z * (csRep K N y)⁻¹ = z * y⁻¹ * (y * (csRep K N y)⁻¹) by group]
  exact N.mul_mem_cancel_left h

private def csAdmitted {G : Type} [Group G] [TopologicalSpace G] (U : Subgroup G)
    (p : Subgroup G × Set G) : Prop :=
  p.1 ≤ U ∧ IsClosed p.2 ∧ (∀ k ∈ p.1, ∀ s ∈ p.2, k * s ∈ p.2) ∧
    (∀ a ∈ p.2, ∀ b ∈ p.2, a * b⁻¹ ∈ U → a * b⁻¹ ∈ p.1) ∧ ∀ g, ∃ a ∈ p.2, a * g⁻¹ ∈ U

private lemma cs_adm_step {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (U K : Subgroup G) (S : Set G) (h : csAdmitted U (K, S)) (N : Subgroup G) [N.Normal]
    (hN : IsOpen (N : Set G)) : csAdmitted U (K ⊓ N, S ∩ csTr K N) := by
  obtain ⟨hKU, hSc, hKS, hSK, hSU⟩ := h
  refine ⟨inf_le_left.trans hKU, hSc.inter ?_, fun k ⟨hkK, hkN⟩ s ⟨hsS, hsT⟩ =>
      ⟨hKS k hkK s hsS, (csTr_coset K N (by simpa using hkN)).2 hsT⟩,
    fun a ⟨haS, haT⟩ b ⟨hbS, hbT⟩ hab => ?_, fun g => ?_⟩
  · rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
    intro y hy
    exact ⟨(fun z => z * y⁻¹) ⁻¹' (N : Set G), fun z hz hzt => hy ((csTr_coset K N hz).1 hzt),
      hN.preimage (continuous_id.mul continuous_const), by simp⟩
  · have habK := hSK a haS b hbS hab
    refine ⟨habK, ?_⟩
    have hr : csRep K N b = csRep K N a := csRep_eq K N ⟨a * b⁻¹, habK, 1, N.one_mem, by group⟩
    have ha : a * (csRep K N a)⁻¹ ∈ N := haT
    have hb : b * (csRep K N b)⁻¹ ∈ N := hbT
    rw [hr] at hb
    simpa [mul_assoc] using N.mul_mem ha (N.inv_mem hb)
  · obtain ⟨a, haS, hag⟩ := hSU g
    obtain ⟨k, hk, n, hn, ha⟩ := Quotient.mk_out (s := csRel K N) a
    have hrel : csRep K N (k⁻¹ * a) = csRep K N a :=
      (csRep_eq K N ⟨k⁻¹, K.inv_mem hk, 1, N.one_mem, by group⟩).symm
    refine ⟨k⁻¹ * a, ⟨hKS _ (K.inv_mem hk) a haS, ?_⟩, ?_⟩
    · show k⁻¹ * a * (csRep K N (k⁻¹ * a))⁻¹ ∈ N
      have ha' : a = k * n * csRep K N a := ha
      rw [hrel, show k⁻¹ * a * (csRep K N a)⁻¹ = n by nth_rw 1 [ha']; group]; exact hn
    · rw [mul_assoc]; exact U.mul_mem (U.inv_mem (hKU hk)) hag

private lemma cs_chain_inf {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] (U : Subgroup G) (hU : IsClosed (U : Set G))
    (c : Set (Subgroup G × Set G)) (hc : ∀ p ∈ c, csAdmitted U p)
    (htot : ∀ p ∈ c, ∀ q ∈ c, p ≤ q ∨ q ≤ p) (y : Subgroup G × Set G) (hy : y ∈ c) :
    csAdmitted U (⨅ p ∈ c, p.1, ⋂ p ∈ c, p.2) := by
  refine ⟨(iInf₂_le y hy).trans (hc y hy).1, isClosed_biInter fun p hp => (hc p hp).2.1,
    fun k hk s hs => Set.mem_iInter₂.2 fun p hp => (hc p hp).2.2.1 k (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hk p) hp) s (Set.mem_iInter₂.1 hs p hp),
    fun a ha b hb hab => Subgroup.mem_iInf.2 fun p => Subgroup.mem_iInf.2 fun hp => (hc p hp).2.2.2.1 a (Set.mem_iInter₂.1 ha p hp) b (Set.mem_iInter₂.1 hb p hp) hab,
    fun g => ?_⟩
  have : Nonempty c := ⟨⟨y, hy⟩⟩
  obtain ⟨a, ha⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
    (fun p : c => p.1.2 ∩ ((fun x => x * g⁻¹) ⁻¹' (U : Set G)))
    (fun p q => by
      rcases htot p.1 p.2 q.1 q.2 with hpq | hqp
      · exact ⟨p, le_rfl, Set.inter_subset_inter_left _ (Prod.le_def.1 hpq).2⟩
      · exact ⟨q, Set.inter_subset_inter_left _ (Prod.le_def.1 hqp).2, le_rfl⟩)
    (fun p => (hc p.1 p.2).2.2.2.2 g)
    (fun p => ((hc p.1 p.2).2.1.inter (hU.preimage (continuous_id.mul (continuous_const (y := g⁻¹))))).isCompact)
    (fun p => (hc p.1 p.2).2.1.inter (hU.preimage (continuous_id.mul (continuous_const (y := g⁻¹)))))
  simp only [Set.mem_iInter] at ha
  exact ⟨a, Set.mem_iInter₂.2 fun p hp => (ha ⟨p, hp⟩).1, (ha ⟨y, hy⟩).2⟩

private theorem continuous_groupSection {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (U : Subgroup G) (hU : IsClosed (U : Set G)) :
    ∃ r : G → U, Continuous r ∧ r 1 = 1 ∧ ∀ (x : U) (g : G), r (x * g) = x * r g := by
  classical
  have hchain : ∀ c ⊆ {p : (Subgroup G × Set G)ᵒᵈ | csAdmitted U (OrderDual.ofDual p)},
      IsChain (· ≤ ·) c → ∀ y ∈ c, ∃ ub ∈ {p : (Subgroup G × Set G)ᵒᵈ | csAdmitted U (OrderDual.ofDual p)},
        ∀ z ∈ c, z ≤ ub := fun c hcs hc y hy =>
    ⟨OrderDual.toDual (⨅ p ∈ OrderDual.toDual ⁻¹' c, p.1, ⋂ p ∈ OrderDual.toDual ⁻¹' c, p.2),
     cs_chain_inf U hU _ (fun p hp => hcs hp) (fun p hp q hq => by
       by_cases hpq : p = q
       · exact Or.inl (le_of_eq hpq)
       · rcases hc hp hq (fun h => hpq (OrderDual.toDual.injective h)) with h | h
         · exact Or.inr h
         · exact Or.inl h) (OrderDual.ofDual y) hy,
     fun z hz => Prod.le_def.2 ⟨iInf₂_le (OrderDual.ofDual z) hz, Set.iInter₂_subset (OrderDual.ofDual z) hz⟩⟩
  have hstart : OrderDual.toDual ((U, Set.univ) : Subgroup G × Set G) ∈
      {p : (Subgroup G × Set G)ᵒᵈ | csAdmitted U (OrderDual.ofDual p)} :=
    ⟨le_rfl, isClosed_univ, fun _ _ _ _ => Set.mem_univ _, fun _ _ _ _ h => h, fun g => ⟨g, Set.mem_univ _, by simp⟩⟩
  obtain ⟨m, -, hm⟩ := zorn_le_nonempty₀ _ hchain _ hstart
  have hA := hm.1
  set K := (OrderDual.ofDual m).1
  set S := (OrderDual.ofDual m).2
  have hK1 : ∀ k ∈ K, k = 1 := fun k hk => by
    by_contra hne
    obtain ⟨N, hN⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
      (isOpen_compl_singleton : IsOpen ({k}ᶜ : Set G)) (Set.mem_compl_singleton_iff.2 (Ne.symm hne))
    have hle := hm.2 (y := OrderDual.toDual (K ⊓ N.toSubgroup, S ∩ csTr K N.toSubgroup))
      (cs_adm_step U K S hA N.toSubgroup N.isOpen') (Prod.le_def.2 ⟨inf_le_left, Set.inter_subset_left⟩)
    exact hN ((Prod.le_def.1 hle).1 hk).2 rfl
  have huniq : ∀ g a a', a ∈ S → a' ∈ S → a * g⁻¹ ∈ U → a' * g⁻¹ ∈ U → a = a' :=
    fun g a a' ha ha' hag ha'g => mul_inv_eq_one.1 (hK1 _ (hA.2.2.2.1 a ha a' ha'
      (by simpa [mul_assoc] using U.mul_mem hag (U.inv_mem ha'g))))
  choose t htS htU using hA.2.2.2.2
  have htc : Continuous t := by
    rw [continuous_iff_isClosed]; intro C hC
    have hset : t ⁻¹' C = (U : Set G) * (S ∩ C) := by
      ext g; constructor
      · intro hg; exact Set.mem_mul.2 ⟨g * (t g)⁻¹, by simpa using U.inv_mem (htU g), t g, ⟨htS g, hg⟩, by group⟩
      · rintro ⟨u, hu, a, ⟨haS, haC⟩, rfl⟩
        show t (u * a) ∈ C
        rw [huniq (u * a) (t (u * a)) a (htS _) haS (htU _) (by simpa using U.inv_mem hu)]
        exact haC
    rw [hset]; exact (hU.isCompact.mul (hA.2.1.inter hC).isCompact).isClosed
  have hconst : ∀ g h, g * h⁻¹ ∈ U → t g = t h := fun g h hgh =>
    huniq g (t g) (t h) (htS g) (htS h) (htU g)
      (by rw [show t h * g⁻¹ = (t h * h⁻¹) * (g * h⁻¹)⁻¹ by group]; exact U.mul_mem (htU h) (U.inv_mem hgh))
  let r0 : G → U := fun g => ⟨g * (t g)⁻¹, by simpa using U.inv_mem (htU g)⟩
  have hr0 : Continuous r0 := (continuous_id.mul htc.inv).subtype_mk _
  refine ⟨fun g => r0 g * (r0 1)⁻¹, hr0.mul continuous_const, mul_inv_cancel _, fun x g => ?_⟩
  have h : t (x * g) = t g := hconst _ _ (by rw [mul_inv_cancel_right]; exact x.2)
  apply Subtype.ext; simp only [r0, Subgroup.coe_mul, Subgroup.coe_inv, h, mul_assoc]

end ContinuousSections

section TransgressionSection

variable {R G M : Type} [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [ContinuousConstSMul R M] [DiscreteTopology M]

private theorem exists_cont_select_profinite {X Y : Type} [TopologicalSpace X] [CompactSpace X]
    [T2Space X] [TotallyDisconnectedSpace X] [TopologicalSpace Y] [DiscreteTopology Y] [Nonempty Y]
    (P : X → Y → Prop) (hP : ∀ y, IsOpen {x | P x y}) (hex : ∀ x, ∃ y, P x y) :
    ∃ ψ : X → Y, Continuous ψ ∧ ∀ x, P x (ψ x) := by
  classical
  have hb : TopologicalSpace.IsTopologicalBasis {s : Set X | IsClopen s} :=
    isTopologicalBasis_isClopen
  choose yx hyx using hex
  choose C hCc hxC hCs using fun x => hb.exists_subset_of_mem_open (hyx x) (hP (yx x))
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover C (fun x => (hCc x).isOpen)
    (fun x _ => Set.mem_iUnion.2 ⟨x, hxC x⟩)
  have key : ∀ s : Finset X, ∃ ψ : X → Y, Continuous ψ ∧ ∀ x ∈ s, ∀ z ∈ C x, P z (ψ z) := fun s => by
    induction s using Finset.induction_on with
    | empty => exact ⟨fun _ => Classical.arbitrary Y, continuous_const, by simp⟩
    | @insert a s _ ih =>
      obtain ⟨ψ, hψc, hψ⟩ := ih
      refine ⟨fun z => if z ∈ C a then yx a else ψ z, ?_, fun x hx z hz => ?_⟩
      · exact continuous_if (fun x hx => by
            have hx' : x ∈ frontier (C a) := hx
            rw [(hCc a).frontier_eq] at hx'
            exact hx'.elim)
          continuous_const.continuousOn hψc.continuousOn
      · by_cases hza : z ∈ C a
        · dsimp only; rw [if_pos hza]; exact hCs a hza
        · dsimp only; rw [if_neg hza]
          rcases Finset.mem_insert.1 hx with rfl | hx'
          · exact absurd hz hza
          · exact hψ x hx' z hz
  obtain ⟨ψ, hψc, hψ⟩ := key t
  exact ⟨ψ, hψc, fun z => by
    obtain ⟨x, hx, hz⟩ : ∃ x ∈ t, z ∈ C x := by simpa using ht (Set.mem_univ z)
    exact hψ x hx z hz⟩

private theorem isOpen_setOf_conj_eq (ρ : Representation R G M) (hρ : ContAction ρ)
    {U' U : Subgroup G} [U'.Normal] [CompactSpace U] (h : U' ≤ U)
    (hU'c : IsClosed (U'.subgroupOf U : Set U)) (z : Z1U ρ U') (m : M) :
    IsOpen {s : U | ∀ u : U', ρ s (z.1 (conjHom U' s u)) - z.1 u = ρ u m - m} := by
  -- directly on U'.subgroupOf U
  haveI : CompactSpace (U'.subgroupOf U) := isCompact_iff_compactSpace.mp hU'c.isCompact
  let toU' : U'.subgroupOf U → U' := fun u => ⟨u.1.1, u.2⟩
  have htoU' : Continuous toU' := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  have hcj : Continuous (fun p : U × U'.subgroupOf U => conjHom U' p.1 (toU' p.2)) :=
    (((continuous_subtype_val.comp continuous_fst).inv.mul (continuous_subtype_val.comp (htoU'.comp continuous_snd))).mul
      (continuous_subtype_val.comp continuous_fst)).subtype_mk _
  have hΦ : Continuous (fun p : U × U'.subgroupOf U =>
      ρ p.1 (z.1 (conjHom U' p.1 (toU' p.2))) - z.1 (toU' p.2) - (ρ (p.2 : G) m - m)) :=
    ((hρ.comp ((continuous_subtype_val.comp continuous_fst).prodMk (z.2.1.comp hcj))).sub
      (z.2.1.comp (htoU'.comp continuous_snd))).sub
      ((hρ.comp ((continuous_subtype_val.comp (htoU'.comp continuous_snd)).prodMk continuous_const)).sub
        continuous_const)
  have hO := hΦ.isOpen_preimage {0} (isOpen_discrete _)
  rw [isOpen_iff_mem_nhds]; intro s0 hs0
  have hev : ∀ᶠ (s : U) in nhds s0, ∀ u ∈ (Set.univ : Set (U'.subgroupOf U)),
      ρ s (z.1 (conjHom U' s (toU' u))) - z.1 (toU' u) - (ρ (u : G) m - m) = 0 :=
    isCompact_univ.eventually_forall_of_forall_eventually fun u _ => hO.mem_nhds (sub_eq_zero.mpr (hs0 (toU' u)))
  filter_upwards [hev] with s hs u
  exact sub_eq_zero.mp (hs ⟨⟨u.1, h u.2⟩, u.2⟩ (Set.mem_univ _))

private theorem exists_ext_closed [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (ρ : Representation R G M) (hρ : ContAction ρ) {U' U : Subgroup G} [U'.Normal] (h : U' ≤ U)
    (hU : IsClosed (U : Set G)) (hU' : IsClosed (U'.subgroupOf U : Set U))
    (z : Z1U ρ U') (hz : Submodule.Quotient.mk z ∈ invariantsUnderSubgroupH1 ρ U U') :
    ∃ y : U → M, Continuous y ∧ y 1 = 0 ∧
      (∀ (u : U') (g : U), y (Subgroup.inclusion h u * g) = z.1 u + ρ u (y g)) ∧
      ∀ (u : U') (g : U), y (g * Subgroup.inclusion h u) = y g + ρ g (z.1 u) := by
  haveI : CompactSpace U := isCompact_iff_compactSpace.mp hU.isCompact
  haveI : Nonempty M := ⟨0⟩
  have hinv : ∀ s : U, ∃ m : M, ∀ u : U', ρ s (z.1 (conjHom U' s u)) - z.1 u = ρ u m - m := fun s => by
    obtain ⟨z', hz'e, hz'⟩ := conjU_mk ρ U' (s : G) z
    have hc : conjU ρ U' (s : G) (Submodule.Quotient.mk z) = Submodule.Quotient.mk z := hz s
    rw [hz'e, mk_eq_mk] at hc
    obtain ⟨m, hm⟩ := hc
    exact ⟨m, fun u => by rw [← hz' u]; exact hm u⟩
  obtain ⟨ψ, hψc, hψ⟩ := exists_cont_select_profinite (X := U)
    (fun (s : U) m => ∀ u : U', ρ s (z.1 (conjHom U' s u)) - z.1 u = ρ u m - m)
    (isOpen_setOf_conj_eq ρ hρ h hU' z) hinv
  obtain ⟨r, hrc, hr1, hr⟩ := continuous_groupSection (U'.subgroupOf U) hU'
  let toU' : U'.subgroupOf U → U' := fun u => ⟨u.1.1, u.2⟩
  have htoU' : Continuous toU' := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  let r' : U → U' := toU' ∘ r
  have hr'c : Continuous r' := htoU'.comp hrc
  have hr'1 : r' 1 = 1 := by simp [r', hr1, toU']
  have hr'mul : ∀ (u : U') (g : U), r' (Subgroup.inclusion h u * g) = u * r' g := fun u g =>
    Subtype.ext (congrArg (fun x : U'.subgroupOf U => (x : G)) (hr ⟨⟨u.1, h u.2⟩, u.2⟩ g))
  have hf1 : z.1 1 = 0 := by have e := z.2.2 1 1; simp only [mul_one, map_one, Module.End.one_apply] at e; exact left_eq_add.1 e
  have hψ1 : ∀ u : U', ρ u (ψ 1) = ψ 1 := fun u => by
    have e := hψ 1 u
    have hc1 : conjHom U' (1 : U) u = u := Subtype.ext (by simp [conjHom])
    rw [hc1, Subgroup.coe_one, map_one, Module.End.one_apply, sub_self] at e
    exact sub_eq_zero.1 e.symm
  have hrσ : ∀ g : U, r' ((Subgroup.inclusion h (r' g))⁻¹ * g) = 1 := fun g => by
    rw [← map_inv, hr'mul, inv_mul_cancel]
  let σ : U → U := fun g => (Subgroup.inclusion h (r' g))⁻¹ * g
  let y : U → M := fun g => z.1 (r' g) + ρ (r' g) (ψ (σ g)) - ψ 1
  have hσn : ∀ (u : U') (g : U), σ (Subgroup.inclusion h u * g) = σ g := fun u g => by
    simp only [σ, hr'mul u g, map_mul, mul_inv_rev, mul_assoc]; group
  have h3 : ∀ (u : U') (g : U), y (Subgroup.inclusion h u * g) = z.1 u + ρ u (y g) := fun u g => by
    simp only [y, hσn, hr'mul u g, z.2.2, Subgroup.coe_mul, map_mul, Module.End.mul_apply, map_add,
      map_sub, hψ1, MonoidHom.comp_apply, Subgroup.coe_subtype]
    abel
  have h2 : ∀ (u : U') (g : U), y (g * Subgroup.inclusion h u) = y g + ρ g (z.1 u) := fun u g => by
    set t := σ g
    let u'' : U' := ⟨t * u * t⁻¹, ‹U'.Normal›.conj_mem u u.2 t⟩
    have hg : Subgroup.inclusion h (r' g) * t = g := by simp [t, σ]
    have e1 : g * Subgroup.inclusion h u = Subgroup.inclusion h (r' g * u'') * t := by
      apply Subtype.ext; simp only [Subgroup.coe_mul, Subgroup.coe_inclusion, u'']
      calc (g : G) * u = (r' g : G) * t * u := by rw [← congrArg Subtype.val hg]; simp
        _ = _ := by push_cast; group
    have hrgn : r' (g * Subgroup.inclusion h u) = r' g * u'' := by rw [e1, hr'mul, hrσ g, mul_one]
    have hσgn : σ (g * Subgroup.inclusion h u) = t := by
      show (Subgroup.inclusion h (r' (g * Subgroup.inclusion h u)))⁻¹ * (g * Subgroup.inclusion h u) = t
      rw [hrgn, e1]; group
    have hc : conjHom U' t u'' = u := Subtype.ext (by simp [conjHom, u'']; group)
    have e2 := hψ t u''
    rw [hc] at e2
    have e3 : z.1 u'' + ρ u'' (ψ t) = ρ t (z.1 u) + ψ t := by
      rw [sub_eq_sub_iff_add_eq_add] at e2; rw [add_comm (z.1 u''), ← e2]
    have hrg : ρ g = ρ (r' g) * ρ t := by rw [← map_mul, ← congrArg Subtype.val hg]; rfl
    show z.1 (r' (g * Subgroup.inclusion h u)) + ρ (r' (g * Subgroup.inclusion h u)) (ψ (σ (g * Subgroup.inclusion h u))) - ψ 1 =
      y g + ρ g (z.1 u)
    rw [hrgn, hσgn, z.2.2]
    calc _ = z.1 (r' g) + ρ (r' g) (z.1 u'' + ρ u'' (ψ t)) - ψ 1 := by
          simp only [Subgroup.coe_mul, map_mul, Module.End.mul_apply, map_add, MonoidHom.comp_apply,
            Subgroup.coe_subtype]
          abel
      _ = z.1 (r' g) + ρ (r' g) (ρ t (z.1 u) + ψ t) - ψ 1 := by rw [e3]
      _ = (z.1 (r' g) + ρ (r' g) (ψ t) - ψ 1) + ρ (r' g) (ρ t (z.1 u)) := by
          rw [map_add]; abel
      _ = _ := by rw [hrg, Module.End.mul_apply]
  have hr'G : Continuous fun g : U => (r' g : G) := continuous_subtype_val.comp hr'c
  have hσc : Continuous σ := continuous_induced_rng.2 ((hr'G.inv).mul continuous_subtype_val)
  refine ⟨y, ((z.2.1.comp hr'c).add (hρ.comp (hr'G.prodMk (hψc.comp hσc)))).sub continuous_const,
    by simp [y, hr'1, hf1, σ], h3, h2⟩

private theorem exists_infl_general (ρ : Representation R G M) (hρ : ContAction ρ) {U' U : Subgroup G} [U'.Normal]
    (h : U' ≤ U) (z : U' → M) (y : U → M) (hy : Continuous y)
    (hL : ∀ (u : U') (g : U), y (Subgroup.inclusion h u * g) = z u + ρ u (y g))
    (hR : ∀ (u : U') (g : U), y (g * Subgroup.inclusion h u) = y g + ρ g (z u)) :
    ∃ w : Z2 (quotRep ρ U U'), ∀ a b : U,
      (w.1 (QuotientGroup.mk a, QuotientGroup.mk b) : M) = ρ a (y b) - y (a * b) + y a := by
  set F : U → U → M := fun a b => ρ a (y b) - y (a * b) + y a
  have hFr : ∀ (a b : U) (u : U'), F a (b * Subgroup.inclusion h u) = F a b := fun a b u => by
    simp only [F]; rw [← mul_assoc, hR, hR]; simp only [map_add, Subgroup.coe_mul, map_mul, Module.End.mul_apply]; abel
  have hFl : ∀ (a b : U) (u : U'), F (a * Subgroup.inclusion h u) b = F a b := fun a b u => by
    obtain ⟨v, hv⟩ : ∃ v : U', Subgroup.inclusion h u * b = b * Subgroup.inclusion h v :=
      ⟨⟨(b : G)⁻¹ * u * b, ‹U'.Normal›.conj_mem' _ u.2 _⟩, Subtype.ext (by simp [mul_assoc])⟩
    have key : ρ u (y b) = y b + ρ b (z v) - z u := by
      have e1 := hL u b; rw [hv, hR] at e1; rw [e1]; abel
    simp only [F]; rw [mul_assoc a, hv, ← mul_assoc, hR, hR]
    simp only [Subgroup.coe_mul, Subgroup.coe_inclusion, map_mul, Module.End.mul_apply, key, map_add, map_sub]; abel
  have hinv : ∀ (a b : U) (u : U'), ρ u (F a b) = F a b := fun a b u => by
    obtain ⟨v, hv⟩ : ∃ v : U', Subgroup.inclusion h u * a = a * Subgroup.inclusion h v :=
      ⟨⟨(a : G)⁻¹ * u * a, ‹U'.Normal›.conj_mem' _ u.2 _⟩, Subtype.ext (by simp [mul_assoc])⟩
    have e1 : ∀ g : U, ρ u (y g) = y (Subgroup.inclusion h u * g) - z u := fun g => by rw [hL]; abel
    calc ρ u (F a b) = F (Subgroup.inclusion h u * a) b := by
          simp only [F, map_add, map_sub, e1, mul_assoc, Subgroup.coe_mul, Subgroup.coe_inclusion,
            map_mul, Module.End.mul_apply]; abel
      _ = F (a * Subgroup.inclusion h v) b := by rw [hv]
      _ = F a b := hFl a b v
  have hN : ∀ a b : U, F a b ∈ Representation.invariants ((ρ.comp U.subtype).comp (U'.subgroupOf U).subtype) :=
    fun a b v => hinv a b ⟨(v : U), Subgroup.mem_subgroupOf.mp v.2⟩
  have hWF : ∀ a b : U,
      F (QuotientGroup.mk a : U ⧸ U'.subgroupOf U).out (QuotientGroup.mk b : U ⧸ U'.subgroupOf U).out = F a b := fun a b => by
    obtain ⟨h1, e1⟩ := QuotientGroup.mk_out_eq_mul (U'.subgroupOf U) a
    obtain ⟨h2, e2⟩ := QuotientGroup.mk_out_eq_mul (U'.subgroupOf U) b
    have e1' : (QuotientGroup.mk a : U ⧸ U'.subgroupOf U).out = a * Subgroup.inclusion h ⟨h1.1, h1.2⟩ :=
      Subtype.ext (by simpa using congrArg Subtype.val e1)
    have e2' : (QuotientGroup.mk b : U ⧸ U'.subgroupOf U).out = b * Subgroup.inclusion h ⟨h2.1, h2.2⟩ :=
      Subtype.ext (by simpa using congrArg Subtype.val e2)
    rw [e1', e2', hFl, hFr]
  let W : (U ⧸ U'.subgroupOf U) × (U ⧸ U'.subgroupOf U) →
      Representation.invariants ((ρ.comp U.subtype).comp (U'.subgroupOf U).subtype) :=
    fun p => ⟨F p.1.out p.2.out, hN _ _⟩
  have hW : ∀ a b : U, (W (QuotientGroup.mk a, QuotientGroup.mk b) : M) = F a b := hWF
  have hWc : Continuous W := by
    have hq := (QuotientGroup.isOpenQuotientMap_mk (N := U'.subgroupOf U)).prodMap
      (QuotientGroup.isOpenQuotientMap_mk (N := U'.subgroupOf U))
    rw [← hq.continuous_comp_iff]
    refine continuous_induced_rng.2 ?_
    change Continuous fun p : U × U => (W (QuotientGroup.mk p.1, QuotientGroup.mk p.2) : M)
    have e : (fun p : U × U => (W (QuotientGroup.mk p.1, QuotientGroup.mk p.2) : M)) =
        fun p => F p.1 p.2 := funext fun p => hW p.1 p.2
    rw [e]
    exact ((hρ.comp ((continuous_subtype_val.comp continuous_fst).prodMk (hy.comp continuous_snd))).sub
      (hy.comp continuous_mul)).add (hy.comp continuous_fst)
  refine ⟨⟨W, hWc, fun p q r => ?_⟩, hW⟩
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective p
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective r
  apply Subtype.ext
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  show ρ a (W (QuotientGroup.mk b, QuotientGroup.mk c) : M) -
    (W (QuotientGroup.mk (a * b), QuotientGroup.mk c) : M) +
    (W (QuotientGroup.mk a, QuotientGroup.mk (b * c)) : M) -
    (W (QuotientGroup.mk a, QuotientGroup.mk b) : M) = 0
  rw [hW, hW, hW, hW]
  simp only [F, map_add, map_sub, Subgroup.coe_mul, map_mul, Module.End.mul_apply, mul_assoc]; abel

private theorem exists_of_mk_eq_zero_general (ρ : Representation R G M) {U' U : Subgroup G}
    [U'.Normal] (h : U' ≤ U) (w : Z2 (quotRep ρ U U'))
    (hw : (Submodule.Quotient.mk w : H2 (quotRep ρ U U')) = 0) :
    ∃ c : U → M, Continuous c ∧ (∀ u : U', c (Subgroup.inclusion h u) = c 1) ∧ ∀ a b : U,
      (w.1 (QuotientGroup.mk a, QuotientGroup.mk b) : M) = ρ a (c b) - c (a * b) + c a := by
  have hw' : w.1 ∈ B2 (quotRep ρ U U') := Submodule.mem_comap.mp ((Submodule.Quotient.mk_eq_zero _).mp hw)
  obtain ⟨cb, hcb, hd⟩ := (mem_B2 _ _).mp hw'
  refine ⟨fun a => (cb (QuotientGroup.mk a) : M),
    continuous_subtype_val.comp (hcb.comp continuous_coinduced_rng), fun u => ?_, fun a b => ?_⟩
  · have h1 : (QuotientGroup.mk (Subgroup.inclusion h u) : U ⧸ U'.subgroupOf U) = QuotientGroup.mk 1 := by
      rw [QuotientGroup.mk_one, QuotientGroup.eq_one_iff]; exact Subgroup.mem_subgroupOf.mpr u.2
    show ((cb _ : _) : M) = cb _; rw [h1]
  · rw [← hd]; rfl

private theorem mem_range_resU_general (ρ : Representation R G M) {U' U : Subgroup G} (h : U' ≤ U)
    (z : Z1U ρ U') (y c : U → M) (hy : Continuous y) (hc : Continuous c)
    (hz : ∀ u : U', y (Subgroup.inclusion h u) = z.1 u) (hc1 : ∀ u : U', c (Subgroup.inclusion h u) = c 1)
    (e : ∀ a b : U, ρ a (c b) - c (a * b) + c a = ρ a (y b) - y (a * b) + y a) :
    Submodule.Quotient.mk z ∈ LinearMap.range (resU ρ h) := by
  have hz1 : (z : U' → M) 1 = 0 := by simpa using z.2.2 1 1
  have hy1 : y 1 = 0 := by have h0 := hz 1; rw [map_one] at h0; rw [h0, hz1]
  have hc0 : c 1 = 0 := by have h0 := e 1 1; simp at h0; rw [h0, hy1]
  have hx : (fun g => y g - c g) ∈ Z1U ρ U := ⟨hy.sub hc, fun a b => by
    show y (a * b) - c (a * b) = (y a - c a) + ρ a (y b - c b)
    rw [map_sub]; have h0 := e a b; rw [← sub_eq_zero] at h0 ⊢; rw [← h0]; abel⟩
  obtain ⟨x', hx'e, hx'⟩ := resU_mk ρ h ⟨_, hx⟩
  refine ⟨Submodule.Quotient.mk ⟨_, hx⟩, ?_⟩
  rw [hx'e]; congr 1; refine Subtype.ext (funext fun u => ?_)
  rw [hx' u]; show y (Subgroup.inclusion h u) - c (Subgroup.inclusion h u) = z.1 u
  rw [hz u, hc1 u, hc0, sub_zero]

private theorem transg_unique (ρ : Representation R G M) (hρ : ContAction ρ) {U' U : Subgroup G} [U'.Normal]
    (h : U' ≤ U) (y y' : U → M) (hy : Continuous y) (hy' : Continuous y')
    (w w' : Z2 (quotRep ρ U U'))
    (hw : ∀ a b : U, (w.1 (QuotientGroup.mk a, QuotientGroup.mk b) : M) = ρ a (y b) - y (a * b) + y a)
    (hw' : ∀ a b : U, (w'.1 (QuotientGroup.mk a, QuotientGroup.mk b) : M) = ρ a (y' b) - y' (a * b) + y' a)
    (hz : ∃ m : M, ∀ u : U', y (Subgroup.inclusion h u) - y' (Subgroup.inclusion h u) = ρ u m - m) :
    (Submodule.Quotient.mk w : H2 (quotRep ρ U U')) = Submodule.Quotient.mk w' := by
  obtain ⟨m, hm⟩ := hz
  let v : U → M := fun g => y g - y' g - (ρ g m - m)
  have hvU' : ∀ u : U', v (Subgroup.inclusion h u) = 0 := fun u => sub_eq_zero.2 (hm u)
  have hv1 : v 1 = 0 := by simpa using hvU' 1
  have hdv : ∀ a b : U, ρ a (v b) - v (a * b) + v a =
      ((w.1 - w'.1) (QuotientGroup.mk a, QuotientGroup.mk b) : M) := fun a b => by
    simp only [v, hw a b, hw' a b, Submodule.coe_sub, Pi.sub_apply, Subgroup.coe_mul, map_sub, map_mul, Module.End.mul_apply]
    abel
  have hd0l : ∀ (a : U) (u : U'), (w.1 - w'.1) (QuotientGroup.mk a, QuotientGroup.mk (Subgroup.inclusion h u)) = 0 :=
    fun a u => by
      have hmk : (QuotientGroup.mk (Subgroup.inclusion h u) : U ⧸ U'.subgroupOf U) = QuotientGroup.mk 1 := by
        rw [QuotientGroup.mk_one, QuotientGroup.eq_one_iff]; exact Subgroup.mem_subgroupOf.mpr u.2
      apply Subtype.ext
      change ((w.1 - w'.1) (QuotientGroup.mk a, QuotientGroup.mk (Subgroup.inclusion h u)) : M) = 0
      rw [hmk]
      have e : (w.1 (QuotientGroup.mk a, QuotientGroup.mk 1) : M) -
          (w'.1 (QuotientGroup.mk a, QuotientGroup.mk 1) : M) = ρ a (v 1) - v (a * 1) + v a := by
        simpa using (hdv a 1).symm
      rw [hv1, map_zero, mul_one, zero_sub, neg_add_cancel] at e
      exact e
  have hvr : ∀ (a : U) (u : U'), v (a * Subgroup.inclusion h u) = v a := fun a u => by
    have e := hdv a (Subgroup.inclusion h u)
    have e0 := congrArg Subtype.val (hd0l a u)
    simp only [ZeroMemClass.coe_zero] at e0
    rw [e0, hvU' u, map_zero, zero_sub] at e
    rw [neg_add_eq_zero] at e; exact e
  have hvinv : ∀ (a : U) (u : U'), ρ u (v a) = v a := fun a u => by
    obtain ⟨u', hu'⟩ : ∃ u' : U', Subgroup.inclusion h u * a = a * Subgroup.inclusion h u' :=
      ⟨⟨(a : G)⁻¹ * u * a, ‹U'.Normal›.conj_mem' _ u.2 _⟩, Subtype.ext (by simp [mul_assoc])⟩
    have e := hdv (Subgroup.inclusion h u) a
    have hmk : (QuotientGroup.mk (Subgroup.inclusion h u) : U ⧸ U'.subgroupOf U) = QuotientGroup.mk 1 := by
      rw [QuotientGroup.mk_one, QuotientGroup.eq_one_iff]; exact Subgroup.mem_subgroupOf.mpr u.2
    have h1 : ((w.1 - w'.1) (QuotientGroup.mk (Subgroup.inclusion h u), QuotientGroup.mk a) : M) = 0 := by
      rw [hmk]
      have e1 : ((w.1 - w'.1) (QuotientGroup.mk 1, QuotientGroup.mk a) : M) = ρ 1 (v a) - v (1 * a) + v 1 :=
        (hdv 1 a).symm
      simpa [hv1] using e1
    rw [h1, hvU' u, add_zero, hu', hvr a u'] at e
    exact sub_eq_zero.1 e
  let cb0 : (U ⧸ U'.subgroupOf U) → Representation.invariants ((ρ.comp U.subtype).comp (U'.subgroupOf U).subtype) :=
    fun q => ⟨v q.out, fun u => hvinv q.out ⟨(u : U), Subgroup.mem_subgroupOf.mp u.2⟩⟩
  have hcb0 : ∀ a : U, (cb0 (QuotientGroup.mk a) : M) = v a := fun a => by
    obtain ⟨h1, e1⟩ := QuotientGroup.mk_out_eq_mul (U'.subgroupOf U) a
    have e1' : (QuotientGroup.mk a : U ⧸ U'.subgroupOf U).out = a * Subgroup.inclusion h ⟨h1.1, h1.2⟩ :=
      Subtype.ext (by simpa using congrArg Subtype.val e1)
    change v (QuotientGroup.mk a : U ⧸ U'.subgroupOf U).out = v a
    rw [e1', hvr]
  have hcb0c : Continuous cb0 := by
    rw [← (QuotientGroup.isOpenQuotientMap_mk (N := U'.subgroupOf U)).continuous_comp_iff]
    refine continuous_induced_rng.2 ?_
    change Continuous fun a : U => (cb0 (QuotientGroup.mk a) : M)
    rw [show (fun a : U => (cb0 (QuotientGroup.mk a) : M)) = v from _root_.funext hcb0]
    exact (hy.sub hy').sub ((hρ.comp (continuous_subtype_val.prodMk continuous_const)).sub continuous_const)
  rw [Submodule.Quotient.eq, Submodule.mem_comap, Submodule.coe_subtype, mem_B2]
  refine ⟨cb0, hcb0c, _root_.funext fun p => ?_⟩
  obtain ⟨p1, p2⟩ := p
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective p1
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective p2
  apply Subtype.ext
  rw [d1_apply]
  change ρ a (cb0 (QuotientGroup.mk b) : M) - (cb0 (QuotientGroup.mk (a * b)) : M) +
    (cb0 (QuotientGroup.mk a) : M) = _
  rw [hcb0 b, hcb0 (a * b), hcb0 a, hdv a b, Submodule.coe_sub]

theorem transg [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (ρ : Representation R G M) (hρ : ContAction ρ) (U' U : Subgroup G) [U'.Normal]
    (h : U' ≤ U) (hU : IsClosed (U : Set G)) (hU' : IsClosed (U' : Set G)) :
    ∃ tg : resCoker ρ h →ₗ[R] H2 (quotRep ρ U U'), Function.Injective tg := by
  classical
  have hU'sub : IsClosed (U'.subgroupOf U : Set U) := hU'.preimage continuous_subtype_val
  have hE : ∀ x : invariantsUnderSubgroupH1 ρ U U',
      ∃ (z : Z1U ρ U') (y : U → M) (w : Z2 (quotRep ρ U U')),
        Submodule.Quotient.mk z = x.1 ∧ Continuous y ∧ y 1 = 0 ∧
        (∀ (u : U') (g : U), y (Subgroup.inclusion h u * g) = z.1 u + ρ u (y g)) ∧
        (∀ (u : U') (g : U), y (g * Subgroup.inclusion h u) = y g + ρ g (z.1 u)) ∧
        ∀ a b : U, (w.1 (QuotientGroup.mk a, QuotientGroup.mk b) : M) = ρ a (y b) - y (a * b) + y a := by
    intro x
    obtain ⟨z, hz⟩ := Submodule.Quotient.mk_surjective _ x.1
    obtain ⟨y, hy, hy1, hL, hR⟩ := exists_ext_closed ρ hρ h hU hU'sub z (hz ▸ x.2)
    obtain ⟨w, hw⟩ := exists_infl_general ρ hρ h z.1 y hy hL hR
    exact ⟨z, y, w, hz, hy, hy1, hL, hR, hw⟩
  choose zf yf wf hzf hyf hy1f hLf hRf hwf using hE
  let T : invariantsUnderSubgroupH1 ρ U U' →ₗ[R] H2 (quotRep ρ U U') :=
    { toFun := fun x => Submodule.Quotient.mk (wf x)
      map_add' := fun x₁ x₂ => transg_unique ρ hρ h (yf (x₁ + x₂)) (yf x₁ + yf x₂)
        (hyf _) ((hyf x₁).add (hyf x₂)) (wf (x₁ + x₂)) (wf x₁ + wf x₂) (hwf _)
        (fun a b => by simp only [Submodule.coe_add, Pi.add_apply, hwf x₁, hwf x₂, map_add]; abel)
        (by
          have h12 : (Submodule.Quotient.mk (zf (x₁ + x₂)) : H1U ρ U') =
              Submodule.Quotient.mk (zf x₁ + zf x₂) := by
            rw [Submodule.Quotient.mk_add, hzf, hzf, hzf]; rfl
          obtain ⟨m, hm⟩ := (mk_eq_mk ρ U' _ _).1 h12
          refine ⟨m, fun u => ?_⟩
          have e0 := hRf (x₁ + x₂) u 1
          have e1 := hRf x₁ u 1
          have e2 := hRf x₂ u 1
          simp only [one_mul, OneMemClass.coe_one, map_one, Module.End.one_apply, hy1f, zero_add] at e0 e1 e2
          simpa [e0, e1, e2] using hm u)
      map_smul' := fun r x => transg_unique ρ hρ h (yf (r • x)) (r • yf x)
        (hyf _) ((hyf x).const_smul r) (wf (r • x)) (r • wf x) (hwf _)
        (fun a b => by simp only [Submodule.coe_smul, Pi.smul_apply, hwf x, map_smul, smul_sub, smul_add])
        (by
          have h1 : (Submodule.Quotient.mk (zf (r • x)) : H1U ρ U') = Submodule.Quotient.mk (r • zf x) := by
            rw [Submodule.Quotient.mk_smul, hzf, hzf]; rfl
          obtain ⟨m, hm⟩ := (mk_eq_mk ρ U' _ _).1 h1
          refine ⟨m, fun u => ?_⟩
          have e0 := hRf (r • x) u 1
          have e1 := hRf x u 1
          simp only [one_mul, OneMemClass.coe_one, map_one, Module.End.one_apply, hy1f, zero_add] at e0 e1
          simpa [e0, e1] using hm u) }
  have hk : ∀ x, T x = 0 ↔ x.1 ∈ LinearMap.range (resU ρ h) := fun x => by
    constructor
    · intro h0
      obtain ⟨c, hc, hc1, hcw⟩ := exists_of_mk_eq_zero_general ρ h (wf x) h0
      rw [← hzf x]
      exact mem_range_resU_general ρ h (zf x) (yf x) c (hyf x) hc
        (fun u => by have e := hRf x u 1; simpa [hy1f x] using e) hc1
        (fun a b => (hcw a b).symm.trans (hwf x a b))
    · rintro ⟨y, hy⟩
      have h1 : (Submodule.Quotient.mk (zf x) : H1U ρ U') = resU ρ h y := (hzf x).trans hy.symm
      obtain ⟨z0, hz0⟩ := Submodule.Quotient.mk_surjective _ y
      obtain ⟨z', hz'e, hz'f⟩ := resU_mk ρ h z0
      rw [← hz0, hz'e, mk_eq_mk] at h1
      obtain ⟨m, hm⟩ := h1
      refine transg_unique ρ hρ h (yf x) (fun g => z0.1 g) (hyf x) z0.2.1 (wf x) 0 (hwf x)
        (fun a b => by simp only [ZeroMemClass.coe_zero, Pi.zero_apply]; rw [z0.2.2 a b]; simp only [MonoidHom.comp_apply, Subgroup.coe_subtype]; abel)
        ⟨m, fun u => ?_⟩
      have e := hRf x u 1
      simp only [one_mul, OneMemClass.coe_one, map_one, Module.End.one_apply, hy1f x, zero_add] at e
      have hm' := hm u
      rw [hz'f u] at hm'
      rw [e]; exact hm'
  refine ⟨Submodule.liftQ _ T fun x hx => (hk x).2 hx, ?_⟩
  rw [← LinearMap.ker_eq_bot]
  exact Submodule.ker_liftQ_eq_bot _ _ _ fun x hx => (hk x).1 hx

theorem length_restriction_coker_le_H2 [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (ρ : Representation R G M) (hρ : ContAction ρ) {U' U : Subgroup G} [U'.Normal] (h : U' ≤ U)
    (hU : IsClosed (U : Set G)) (hU' : IsClosed (U' : Set G)) :
    Module.length R (resCoker ρ h) ≤ Module.length R (H2 (quotRep ρ U U')) := by
  obtain ⟨tg, htg⟩ := transg ρ hρ U' U h hU hU'
  exact Module.length_le_of_injective tg htg

theorem length_H0_quotient_rep_le (ρ : Representation R G M) (U' U : Subgroup G)
    [(U'.subgroupOf U).Normal] :
    Module.length R (H0 (quotRep ρ U U')) ≤ Module.length R (H0U ρ U) :=
  Module.length_le_of_injective
    (LinearMap.codRestrict (H0U ρ U)
      ((Representation.invariants ((ρ.comp U.subtype).comp (U'.subgroupOf U).subtype)).subtype ∘ₗ
        (H0 (quotRep ρ U U')).subtype) fun x g => congrArg Subtype.val (x.2 (QuotientGroup.mk g)))
    fun _ _ hxx => Subtype.ext (Subtype.ext (congrArg (fun z : H0U ρ U => (z : M)) hxx))

end TransgressionSection

section H2SubsingletonAndAbelianBounds

private theorem H2_subsingleton_of_mulEquiv {R Q Q' N : Type} [CommRing R] [Group Q]
    [TopologicalSpace Q] [Group Q'] [TopologicalSpace Q'] [AddCommGroup N] [Module R N]
    [TopologicalSpace N] [IsTopologicalAddGroup N] [ContinuousConstSMul R N]
    (σ : Representation R Q N) (e : Q ≃* Q') (he : Continuous e) (he' : Continuous e.symm)
    (hs : Subsingleton (H2 (σ.comp e.symm.toMonoidHom : Representation R Q' N))) :
    Subsingleton (H2 σ) := by
  have hc : ∀ g m, (LinearMap.id : N →ₗ[R] N)
      ((σ.comp e.symm.toMonoidHom : Representation R Q' N) (e.toMonoidHom g) m) =
      σ g ((LinearMap.id : N →ₗ[R] N) m) := fun _ _ => by simp
  refine Function.Surjective.subsingleton (f := pairH2 _ σ e.toMonoidHom he LinearMap.id continuous_id hc)
    fun x => ?_
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  refine ⟨Submodule.Quotient.mk (restrictCocycles2 σ e.symm.toMonoidHom he' z), ?_⟩
  show Submodule.Quotient.mk (compatiblePairCocycles2 _ σ e.toMonoidHom he LinearMap.id continuous_id hc _) = _
  congr 1; exact Subtype.ext (funext fun ⟨g, h⟩ => by show z.1 (e.symm (e g), e.symm (e h)) = _; simp)

private theorem cont_quot {R G M : Type} [CommRing R] [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [AddCommGroup M] [Module R M] [TopologicalSpace M]
    (ρ : Representation R G M) (hρ : ContAction ρ) (S : Subgroup G) [S.Normal] :
    ContAction (ρ.quotientToInvariants S) := by
  unfold ContAction
  have hq := (QuotientGroup.isOpenQuotientMap_mk (N := S)).prodMap
    (IsOpenQuotientMap.id (X := Representation.invariants (ρ.comp S.subtype)))
  rw [← hq.continuous_comp_iff]
  exact (hρ.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk _

theorem resZl :
    ∀ (l : ℕ) [Fact l.Prime], ∀ (R G M : Type) [CommRing R] [Group G] [TopologicalSpace G]
      [IsTopologicalGroup G] [AddCommGroup M] [Module R M] [TopologicalSpace M]
      [IsTopologicalAddGroup M] [ContinuousConstSMul R M] [DiscreteTopology M]
      (ρ : Representation R G M) [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G],
      ContAction ρ → (∀ m : M, ∃ n : ℕ, l ^ n • m = 0) →
      ∀ (U' U : Subgroup G) [U'.Normal] (h : U' ≤ U), IsClosed (U : Set G) →
      ∀ κ : U →* Multiplicative ℤ_[l], Continuous κ → Function.Surjective κ →
      κ.ker = U'.subgroupOf U → invariantsUnderSubgroupH1 ρ U U' ≤ LinearMap.range (resU ρ h) := by
  intro l _ R G M _ _ _ _ _ _ _ _ _ _ ρ _ _ _ hρ hl U' U _ h hU κ hκ hs hk
  haveI : CompactSpace U := isCompact_iff_compactSpace.1 hU.isCompact
  have hρU : ContAction (ρ.comp U.subtype : Representation R U M) :=
    hρ.comp ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  let e : U ⧸ U'.subgroupOf U ≃* Multiplicative ℤ_[l] :=
    (QuotientGroup.quotientMulEquivOfEq hk.symm).trans (QuotientGroup.quotientKerEquivOfSurjective κ hs)
  have he : Continuous e := by
    rw [← (QuotientGroup.isOpenQuotientMap_mk (N := U'.subgroupOf U)).continuous_comp_iff]; exact hκ
  have he' : Continuous e.symm := (Continuous.homeoOfEquivCompactToT2 (f := e.toEquiv) he).symm.continuous
  haveI : Subsingleton (H2 (quotRep ρ U U')) := H2_subsingleton_of_mulEquiv _ e he he'
    (h2Zl l R _ _ ((cont_quot _ hρU _).comp ((he'.comp continuous_fst).prodMk continuous_snd))
      fun m => by obtain ⟨n, hn⟩ := hl m.1; exact ⟨n, Subtype.ext (by simpa using hn)⟩)
  have hc : IsClosed (U'.subgroupOf U : Set U) := hk ▸ isClosed_singleton.preimage hκ
  have hc' : IsClosed (U' : Set G) := by
    convert hU.isClosedEmbedding_subtypeVal.isClosedMap _ hc using 1
    ext x; exact ⟨fun hx => ⟨⟨x, h hx⟩, hx, rfl⟩, fun ⟨_, hy, e⟩ => e ▸ hy⟩
  obtain ⟨tg, htg⟩ := transg ρ hρ U' U h hU hc'
  intro x hx
  have h0 : (Submodule.Quotient.mk ⟨x, hx⟩ : resCoker ρ h) = 0 := htg (Subsingleton.elim _ _)
  exact Submodule.mem_comap.1 ((Submodule.Quotient.mk_eq_zero _).1 h0)

private theorem length_span_cocycle_finite {R N I : Type} [CommRing R] [AddCommGroup N] [Module R N]
    [Finite I] (hN : ∀ m : N, Module.length R (Submodule.span R {m}) ≠ ⊤)
    (Z : Submodule R (I → N)) (f : Z) : Module.length R (Submodule.span R {f}) ≠ ⊤ := by
  classical
  have := Fintype.ofFinite I
  let φ : Submodule.span R {f} →ₗ[R] (Π i : I, Submodule.span R {(f : I → N) i}) :=
    { toFun := fun g i => ⟨((g : Z) : I → N) i, by
        obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp g.2
        rw [← hr]; exact Submodule.mem_span_singleton.mpr ⟨r, by simp⟩⟩
      map_add' := fun _ _ => by ext; simp, map_smul' := fun _ _ => by ext; simp }
  refine ne_top_of_le_ne_top ?_ (Module.length_le_of_injective φ fun _ _ e =>
    Subtype.ext (Subtype.ext (funext fun i => congrArg Subtype.val (congrFun e i))))
  rw [Module.length_pi_of_fintype]
  exact (WithTop.sum_lt_top.mpr fun i _ => (hN _).lt_top).ne

theorem h2Ab :
    ∀ (R Q N : Type) [CommRing R] [TopologicalSpace Q] [DiscreteTopology Q] [Finite Q]
      [AddCommGroup N] [Module R N] [TopologicalSpace N] [IsTopologicalAddGroup N]
      [ContinuousConstSMul R N] [DiscreteTopology N] [IsPrincipalIdealRing R] [Group Q]
      (σ : Representation R Q N), (∀ a b : Q, a * b = b * a) →
      (∀ m : N, Module.length R (Submodule.span R {m}) ≠ ⊤) → (∀ g, ∃ c : R, ∀ m, σ g m = c • m) →
      Module.length R (H2 σ) ≤ (Nat.card Q : ℕ∞) ^ 2 * Module.length R (H0 σ) := by
  intro R Q N _ _ _ _ _ _ _ _ _ _ _ _ σ hcomm hN hsc
  classical
  choose c hc using hsc
  set J : Ideal R := Ideal.span (Set.range fun g => c g - 1)
  set a : R := Submodule.IsPrincipal.generator J
  have haJ : a ∈ J := Submodule.IsPrincipal.generator_mem J
  have hJa : ∀ g, ∃ r : R, c g - 1 = r * a := fun g => by
    have hmem : c g - 1 ∈ J := Ideal.subset_span ⟨g, rfl⟩
    rw [← Ideal.span_singleton_generator J] at hmem
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hmem; exact ⟨r, hr.symm⟩
  have hH0 : ∀ m : N, a • m = 0 → m ∈ H0 σ := fun m hm => by
    rw [H0, Representation.mem_invariants]; intro g
    obtain ⟨r, hr⟩ := hJa g
    have hz : (c g - 1) • m = 0 := by rw [hr, mul_smul, hm, smul_zero]
    rw [hc, ← sub_eq_zero, ← hz, sub_smul, one_smul]
  have hB : ∀ f : Z2 σ, a • (f : Q × Q → N) ∈ B2 σ := fun f => by
    set F : Q × Q → N := (f : Q × Q → N)
    obtain ⟨-, hcoc⟩ := f.2
    refine Submodule.span_induction (p := fun x _ => x • F ∈ B2 σ) ?_ (by rw [zero_smul]; exact zero_mem _)
      (fun _ _ _ _ hx hy => by rw [add_smul]; exact add_mem hx hy)
      (fun _ _ _ hx => by rw [smul_eq_mul, mul_smul]; exact Submodule.smul_mem _ _ hx) haJ
    rintro _ ⟨g, rfl⟩
    rw [mem_B2]
    refine ⟨fun x => F (g, x) - F (x, g), continuous_of_discreteTopology, funext fun ⟨x, y⟩ => ?_⟩
    have e1 := hcoc g x y; have e2 := hcoc x g y; have e3 := hcoc x y g
    rw [hc] at e1 e2 e3; rw [hcomm x g] at e2; rw [hcomm y g] at e3
    simp only [d1_apply, hc, Pi.smul_apply]
    have key : c x • (F (g, y) - F (y, g)) - (F (g, x * y) - F (x * y, g)) + (F (g, x) - F (x, g)) -
        (c g - 1) • F (x, y) = -((c g • F (x, y) - F (g * x, y) + F (g, x * y) - F (g, x)) -
        (c x • F (g, y) - F (g * x, y) + F (x, g * y) - F (x, g)) +
        (c x • F (y, g) - F (x * y, g) + F (x, g * y) - F (x, y))) := by
      simp only [smul_sub, sub_smul, one_smul]; abel
    rw [e1, e2, e3] at key; simpa [sub_eq_zero] using key
  let Zs := Z2 σ
  let mul : Zs →ₗ[R] Zs := a • LinearMap.id
  have h1 : Module.length R (H2 σ) ≤ Module.length R (Zs ⧸ LinearMap.range mul) :=
    Module.length_le_of_surjective (Submodule.liftQ (LinearMap.range mul)
      (Submodule.mkQ (Submodule.comap Zs.subtype (B2 σ))) fun _ ⟨z, hz⟩ => by
        rw [← hz, LinearMap.mem_ker, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
        exact hB z)
      fun y => by obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective _ y; exact ⟨Submodule.mkQ _ z, rfl⟩
  have h2 := lenCokerLe R Zs (length_span_cocycle_finite hN Zs) a
  have h3 : Module.length R (LinearMap.ker mul) ≤ Module.length R (Q × Q → H0 σ) :=
    Module.length_le_of_injective
      { toFun := fun z p => ⟨((z : Zs) : Q × Q → N) p, hH0 _ (congrFun (congrArg Subtype.val (LinearMap.mem_ker.mp z.2)) p)⟩
        map_add' := fun _ _ => by ext; simp, map_smul' := fun _ _ => by ext; simp }
      fun _ _ e => Subtype.ext (Subtype.ext (funext fun p => congrArg Subtype.val (congrFun e p)))
  calc Module.length R (H2 σ) ≤ _ := h1
    _ ≤ _ := h2
    _ ≤ _ := h3
    _ = (Nat.card Q : ℕ∞) ^ 2 * Module.length R (H0 σ) := by
      rw [Module.length_pi]; congr 1; rw [ENat.card_eq_coe_natCard, Nat.card_prod, pow_two]; push_cast; rfl

theorem cokerAb :
    ∀ (R G M : Type) [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
      [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M]
      [ContinuousConstSMul R M] [DiscreteTopology M] (ρ : Representation R G M) [CompactSpace G]
      [T2Space G] [TotallyDisconnectedSpace G] [IsPrincipalIdealRing R], ContAction ρ →
      (∀ m : M, Module.length R (Submodule.span R {m}) ≠ ⊤) → (∀ g, ∃ c : R, ∀ m, ρ g m = c • m) →
      ∀ (U' U : Subgroup G) [U'.Normal] (h : U' ≤ U), IsClosed (U : Set G) →
      IsOpen (U'.subgroupOf U : Set U) → (∀ a ∈ U, ∀ b ∈ U, a * b * a⁻¹ * b⁻¹ ∈ U') →
      Module.length R (resCoker ρ h) ≤ (U'.relIndex U : ℕ∞) ^ 2 * Module.length R (H0U ρ U) := by
  intro R G M _ _ _ _ _ _ _ _ _ _ ρ _ _ _ _ hρ hfin hsc U' U _ h hcl ho hab
  haveI : CompactSpace U := isCompact_iff_compactSpace.1 hcl.isCompact
  haveI : Finite (U ⧸ U'.subgroupOf U) := Subgroup.quotient_finite_of_isOpen _ ho
  haveI : DiscreteTopology (U ⧸ U'.subgroupOf U) := QuotientGroup.discreteTopology ho
  have hc' : IsClosed (U' : Set G) := by
    convert hcl.isClosedEmbedding_subtypeVal.isClosedMap _ (Subgroup.isClosed_of_isOpen (U'.subgroupOf U) ho) using 1
    ext x; exact ⟨fun hx => ⟨⟨x, h hx⟩, hx, rfl⟩, fun ⟨_, hy, e⟩ => e ▸ hy⟩
  refine (length_restriction_coker_le_H2 ρ hρ h hcl hc').trans
    ((h2Ab R _ _ (quotRep ρ U U') (fun a b => ?_) (fun m => ?_) fun g => ?_).trans
      (mul_le_mul_right (length_H0_quotient_rep_le ρ U' U) _))
  · obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    rw [← mul_inv_eq_one, mul_inv_rev, ← mul_assoc, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_inv,
      ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff]
    exact hab a a.2 b b.2
  · have e := (Submodule.equivMapOfInjective _ (Submodule.injective_subtype _) (Submodule.span R {m})).length_eq
    rw [Submodule.map_span, Set.image_singleton] at e; rw [e]; exact hfin _
  · obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g; obtain ⟨c, hc⟩ := hsc g
    exact ⟨c, fun m => Subtype.ext (hc m)⟩

end H2SubsingletonAndAbelianBounds

end ContinuousSectionsAndTransgression

end H2VanishingAndTransgression

end KernelCokerAndH2

/-! ## Section 7: Cyclotomic Control Theorems (`controlGamma`, `control`) and `Stage12`/`Stage13GL` Bridges -/

section ControlTheorems

private theorem exists_val_lt_one (Ω : Type) [Field Ω] [CharZero Ω] (p : ℕ) (hp : p.Prime) :
    ∃ W : ValuationSubring Ω, W.valuation (p : Ω) < 1 := by
  have hne : (Ideal.span {(p : (⊥ : Subring Ω))}) ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]; intro hu
    obtain ⟨v, hv⟩ := hu.exists_right_inv; obtain ⟨n, hn⟩ := Subring.mem_bot.1 v.2
    have h1 : ((p : ℤ) * n : ℤ) = 1 := by
      have := congrArg Subtype.val hv; simp only [Subring.coe_mul, Subring.coe_natCast, Subring.coe_one] at this
      rw [← hn] at this; exact_mod_cast this
    have := Int.isUnit_iff_natAbs_eq.1 (IsUnit.of_mul_eq_one _ h1); simp at this; exact hp.one_lt.ne' this
  obtain ⟨W, -, hW⟩ := Ideal.image_subset_nonunits_valuationSubring _ hne
  exact ⟨W, (ValuationSubring.mem_nonunits_iff W).1 (hW ⟨p, Ideal.mem_span_singleton_self _, by simp⟩)⟩

private theorem inj_cyc (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O]
    (ψ : G k Ω →* Oˣ) (n : ℤ) (hn : n ≠ 0) (hψo : IsOpen (ψ.ker : Set (G k Ω)))
    (V : Subgroup (G k Ω)) (hV : IsClosed (V : Set (G k Ω))) (hg : V ≤ gamU l ⊤)
    (hψ : V ≤ ψ.ker) (hχ : ¬ V ≤ (cycZ k Ω l).ker) :
    Function.Injective (resU (twist₂ l (ψ * chiO k Ω l O ^ n)) (cycU_le l V)) := by
  obtain ⟨κ, γ, -, -, hk, -, hcl, hfin⟩ := gammaGen k Ω l V hV hg hχ
  haveI : ((cycU l V).subgroupOf V).Normal := hk ▸ inferInstance
  refine (kerResCyc O (G k Ω) (QO l O) _ ((contTw k Ω l).2.2 O ψ n hψo) (cycU l V) V (cycU_le l V) γ.1 γ.2 hcl).2 ?_
  intro m _
  have hall : ∀ m' : QO l O, m' ∈ H0U (twist₂ l (ψ * chiO k Ω l O ^ n)) (cycU l V) := fun m' u => by
    have h3 : (ψ * chiO k Ω l O ^ n) u.1 = 1 := by
      rw [MonoidHom.mul_apply, MonoidHom.mem_ker.1 (hψ u.2.1), one_mul, MonoidHom.zpow_apply, chiO, MonoidHom.comp_apply, MonoidHom.mem_ker.1 u.2.2, map_one, one_zpow]
    show (((ψ * chiO k Ω l O ^ n) u.1 : Oˣ) : O) • m' = m'; rw [h3, Units.val_one, one_smul]
  have ha : (((ψ * chiO k Ω l O ^ n) γ.1 : Oˣ) : O) - 1 ≠ 0 := fun h0 => by
    have h2 : (ψ * chiO k Ω l O ^ n) γ.1 = 1 := Units.ext (sub_eq_zero.1 h0)
    have h3 : Units.map (algebraMap ℤ_[l] O).toMonoidHom (cycZ k Ω l γ.1 ^ n) = 1 := by
      rw [map_zpow]; simpa [chiO, MonoidHom.mem_ker.1 (hψ γ.2)] using h2
    exact hfin (isOfFinOrder_iff_zpow_eq_one.2 ⟨n, hn,
      Units.map_injective (f := (algebraMap ℤ_[l] O).toMonoidHom) (dvrFacts l O).1 (h3.trans (map_one _).symm)⟩)
  obtain ⟨m', hm'⟩ := (qoFacts l O).2.2.1 _ ha m
  exact ⟨m', hall m', by show (((ψ * chiO k Ω l O ^ n) γ.1 : Oˣ) : O) • m' - m' = m; rw [← hm', sub_smul, one_smul]⟩

private theorem mem_selEig_one {R G M : Type} [CommRing R] [Group G] [TopologicalSpace G]
    [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [ContinuousConstSMul R M] [IsTopologicalGroup G] [DiscreteTopology M]
    (ρ : Representation R G M) (U' : Subgroup G) [U'.Normal] {𝒟 : Set (Subgroup G)}
    (h𝒟 : ConjStable 𝒟) (U : Subgroup G) (x : LocSel ρ U' 𝒟) :
    x ∈ selEig ρ U' h𝒟 U 1 ↔ x.1 ∈ invariantsUnderSubgroupH1 ρ U U' := by
  unfold selEig; rw [eig_one]
  exact ⟨fun h g => congrArg Subtype.val (h g), fun h g => Subtype.ext (h g)⟩

theorem controlGamma :
    ∀ (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
      (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
      [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] (U : Subgroup (G k Ω)) [U.Normal],
      IsOpen (U : Set (G k Ω)) → U ≤ gamU l ⊤ → ∀ (ψ : G k Ω →* Oˣ) (n : ℤ), U ≤ ψ.ker →
      n ≠ 0 →
      Function.Injective (selRes (twist₂ l (ψ * chiO k Ω l O ^ n)) (cycU_le l U) (shaFam k Ω l)) ∧
      LinearMap.range (selRes (twist₂ l (ψ * chiO k Ω l O ^ n)) (cycU_le l U) (shaFam k Ω l)) =
        shaEig (twist₂ l (ψ * chiO k Ω l O ^ n)) l (cycU l U) U 1 := by
  intro k Ω _ _ _ _ _ l hl O _ _ _ _ _ U _ hU hg ψ n hψ hn
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap k Ω).injective
  have hψo : IsOpen (ψ.ker : Set (G k Ω)) := Subgroup.isOpen_mono hψ hU
  have hUc : IsClosed (U : Set (G k Ω)) := U.isClosed_of_isOpen hU
  have hnt : ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → ¬ U ⊓ Dec (F := k) A ≤ (cycZ k Ω l).ker :=
    fun A hA h => by
      obtain ⟨g, hgm, hf⟩ := decInf k Ω l U hU A hA
      exact hf (by rw [MonoidHom.mem_ker.1 (h hgm)]; exact IsOfFinOrder.one)
  have hχ : ¬ U ≤ (cycZ k Ω l).ker := by
    obtain ⟨A, hA⟩ := exists_val_lt_one Ω l hl.out
    exact fun h => hnt A hA (inf_le_left.trans h)
  refine ⟨fun _ _ hab => Subtype.ext (inj_cyc k Ω l O ψ n hn hψo U hUc hg hψ hχ (congrArg Subtype.val hab)),
    le_antisymm (by rintro _ ⟨y, rfl⟩; exact (mem_selEig_one _ _ _ _ _).2 (restriction_mem_invariant_H1 _ (cycU_le l U) y.1))
      fun x hx => ?_⟩
  obtain ⟨κ, _, hκ, hs, hk, -⟩ := gammaGen k Ω l U hUc hg hχ
  obtain ⟨y, hy⟩ := resZl l O (G k Ω) (QO l O) _ ((contTw k Ω l).2.2 O ψ n hψo) (qoFacts l O).2.1
    (cycU l U) U (cycU_le l U) hUc κ hκ hs hk ((mem_selEig_one _ _ _ _ _).1 hx)
  have hz : ∀ D ∈ shaFam k Ω l, ∀ (W : Subgroup (G k Ω)) (h : W ≤ cycU l U ⊓ D) (h' : W ≤ U),
      resU (twist₂ l (ψ * chiO k Ω l O ^ n)) h' y = 0 := fun D hD W h h' => by
    have h0 := mem_locSel.1 x.2 D hD; rw [← hy, resU_resU] at h0
    have := congrArg (fun t => resU (twist₂ l (ψ * chiO k Ω l O ^ n)) h t) h0
    rwa [resU_resU, map_zero] at this
  have hdec : ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 →
      resU (twist₂ l (ψ * chiO k Ω l O ^ n)) (inf_le_left : U ⊓ Dec (F := k) A ≤ U) y = 0 := fun A hA => by
    apply inj_cyc k Ω l O ψ n hn hψo (U ⊓ Dec (F := k) A) (hUc.inter (isClosed_Dec A)) (inf_le_left.trans hg)
      (inf_le_left.trans hψ) (hnt A hA)
    rw [resU_resU, map_zero]
    exact hz _ (Or.inl ⟨A, hA, rfl⟩) (cycU l (U ⊓ Dec (F := k) A)) (fun _ hg => ⟨⟨hg.1.1, hg.2⟩, hg.1.2⟩) _
  refine ⟨⟨y, mem_locSel.2 ?_⟩, Subtype.ext hy⟩
  rintro D (⟨A, hA, rfl⟩ | ⟨A, rfl⟩)
  · exact hdec A hA
  · by_cases hA : A.valuation (l : Ω) < 1
    · have := congrArg (fun t => resU (twist₂ l (ψ * chiO k Ω l O ^ n)) (inf_le_inf_left U (Ine_le_Dec (F := k) A)) t)
        (hdec A hA)
      rwa [resU_resU, map_zero] at this
    · exact hz _ (Or.inr ⟨A, rfl⟩) (U ⊓ Ine (F := k) A)
        (fun _ hg => ⟨⟨hg.1, (places k Ω l A).2.2.2 hA hg.2⟩, hg.2⟩) _

private theorem control_lemma {R Γ M : Type} [CommRing R] [Group Γ] [TopologicalSpace Γ]
    [IsTopologicalGroup Γ] [AddCommGroup M] [Module R M] [TopologicalSpace M]
    [IsTopologicalAddGroup M] [ContinuousConstSMul R M] [DiscreteTopology M]
    (ρ : Representation R Γ M) {C V U : Subgroup Γ} [C.Normal] [V.Normal] [U.Normal]
    (hCV : C ≤ V) (hVU : V ≤ U) (hCU : C ≤ U) {𝒟 : Set (Subgroup Γ)} (h𝒟 : ConjStable 𝒟)
    (H1 : Function.Injective (selRes ρ hCV 𝒟) ∧ LinearMap.range (selRes ρ hCV 𝒟) = selEig ρ C h𝒟 V 1)
    (H2 : Function.Injective (selRes ρ hVU 𝒟) ∧ LinearMap.range (selRes ρ hVU 𝒟) = selEig ρ V h𝒟 U 1) :
    Function.Injective (selRes ρ hCU 𝒟) ∧ LinearMap.range (selRes ρ hCU 𝒟) = selEig ρ C h𝒟 U 1 := by
  have hcomp : ∀ x, selRes ρ hCU 𝒟 x = selRes ρ hCV 𝒟 (selRes ρ hVU 𝒟 x) := fun x =>
    Subtype.ext (resU_resU ρ hCV hVU x.1).symm
  have memE : ∀ (W : Subgroup Γ) [W.Normal] (X : Subgroup Γ) (y : LocSel ρ W 𝒟),
      y ∈ selEig ρ W h𝒟 X 1 ↔ ∀ g : X, selRep ρ W h𝒟 g y = y := fun W _ X y => by
    simp only [selEig, mem_eig, MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype,
      MonoidHom.one_apply, Units.val_one, one_smul]
  refine ⟨fun x y hxy => H2.1 (H1.1 (by rwa [← hcomp, ← hcomp])), ?_⟩
  ext y; constructor
  · rintro ⟨x, rfl⟩; rw [memE]; intro g
    have hx : selRes ρ hVU 𝒟 x ∈ selEig ρ V h𝒟 U 1 := H2.2 ▸ ⟨x, rfl⟩
    rw [memE] at hx; rw [hcomp, ← selRes_selRep, hx g]
  · intro hy; rw [memE] at hy
    obtain ⟨z, rfl⟩ := H1.2 ▸ (memE C V y).2 fun g => hy ⟨g, hVU g.2⟩
    obtain ⟨x, rfl⟩ := H2.2 ▸ (memE V U z).2 fun g => H1.1 (by rw [selRes_selRep]; exact hy g)
    exact ⟨x, hcomp x⟩

private theorem selRes_injective_range_eq_of_le {R Γ M : Type} [CommRing R] [Group Γ]
    [TopologicalSpace Γ] [IsTopologicalGroup Γ] [AddCommGroup M] [Module R M] [TopologicalSpace M]
    [IsTopologicalAddGroup M] [ContinuousConstSMul R M] [DiscreteTopology M]
    (ρ : Representation R Γ M) {C C' V : Subgroup Γ} [C.Normal] [C'.Normal] [V.Normal]
    (e : C' = C) (h : C ≤ V) (h' : C' ≤ V) {𝒟 : Set (Subgroup Γ)} (h𝒟 : ConjStable 𝒟)
    (H : Function.Injective (selRes ρ h' 𝒟) ∧ LinearMap.range (selRes ρ h' 𝒟) = selEig ρ C' h𝒟 V 1) :
    Function.Injective (selRes ρ h 𝒟) ∧ LinearMap.range (selRes ρ h 𝒟) = selEig ρ C h𝒟 V 1 := by
  subst e; exact H

private theorem zmod_eq_intCast_of_primitiveRoot_pow_eq_selmer {Ω : Type} [Field Ω] {N : ℕ}
    [NeZero N] {ζ : Ω} (hζ : IsPrimitiveRoot ζ N) (a : ZMod N) (k : ℤ) (h : ζ ^ a.val = ζ ^ k) :
    a = (k : ZMod N) := by
  have h0 : ζ ≠ 0 := hζ.ne_zero (NeZero.ne N)
  have h1 : ζ ^ ((a.val : ℤ) - k) = 1 := by rw [zpow_sub₀ h0, zpow_natCast, h, div_self (zpow_ne_zero _ h0)]
  have h3 : (((a.val : ℤ) - k : ℤ) : ZMod N) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr ((hζ.zpow_eq_one_iff_dvd _).mp h1)
  push_cast at h3; rw [ZMod.natCast_zmod_val] at h3; exact sub_eq_zero.mp h3

theorem control :
    ∀ (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
      (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
      [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] (U : Subgroup (G k Ω)) [U.Normal],
      IsOpen (U : Set (G k Ω)) → (l ≠ 2 ∨ U ≤ gamU l ⊤) → ∀ (ψ : G k Ω →* Oˣ) (n : ℤ),
      U ≤ ψ.ker → n ≠ 0 →
      Function.Injective (selRes (twist₂ l (ψ * chiO k Ω l O ^ n)) (cycU_le l U) (shaFam k Ω l)) ∧
      LinearMap.range (selRes (twist₂ l (ψ * chiO k Ω l O ^ n)) (cycU_le l U) (shaFam k Ω l)) =
        shaEig (twist₂ l (ψ * chiO k Ω l O ^ n)) l (cycU l U) U 1 := by
  intro k Ω _ _ _ _ _ l _ O _ _ _ _ _ U _ hU hl ψ n hψ hn
  by_cases hγ : U ≤ gamU l ⊤
  · exact controlGamma k Ω l O U hU hγ ψ n hψ hn
  have hl2 : l ≠ 2 := hl.resolve_right hγ
  have hp : l.Prime := Fact.out
  haveI : NeZero (l ^ 1) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hρ := (contTw k Ω l).2.2 O ψ n (Subgroup.isOpen_mono hψ hU)
  have hq : qExp l = 1 := by simp [qExp, hl2]
  have hV : gamU l U = U ⊓ ((redPow l 1).comp (cycZ k Ω l)).ker := by
    show levU l U (qExp l) = _; rw [hq]; simp only [levU, princ, MonoidHom.comap_ker]
  have hVγ : gamU l U ≤ gamU l ⊤ := by show levU l U (qExp l) ≤ levU l ⊤ (qExp l); simp only [levU]; exact inf_le_inf_right _ le_top
  have hVU : gamU l U ≤ U := levU_le l U (qExp l)
  haveI hVn : (gamU l U).Normal := by rw [hV]; infer_instance
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed k
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap k Ω).injective
  have hVopen : IsOpen ((gamU l U : Subgroup (G k Ω)) : Set (G k Ω)) := by
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ 1)
    haveI : FiniteDimensional k (IntermediateField.adjoin k {ζ}) :=
      IntermediateField.adjoin.finiteDimensional (Algebra.IsAlgebraic.isAlgebraic ζ).isIntegral
    refine Subgroup.isOpen_mono (H₁ := U ⊓ (IntermediateField.adjoin k {ζ}).fixingSubgroup) (fun g hg => ?_)
      (by rw [Subgroup.coe_inf]; exact hU.inter (IntermediateField.fixingSubgroup_isOpen _))
    rw [Subgroup.mem_inf] at hg; rw [hV, Subgroup.mem_inf, MonoidHom.mem_ker]
    refine ⟨hg.1, ?_⟩
    have hgz : g ζ = ζ := by
      simpa [AlgEquiv.smul_def] using (IntermediateField.mem_fixingSubgroup_iff _ _).mp hg.2 ζ
        (IntermediateField.mem_adjoin_simple_self k ζ)
    have hs := cyclotomicCharacter.spec l (n := 1) (MulSemiringAction.toRingAut (G k Ω) Ω g) ζ hζ.pow_eq_one
    simp only [MulSemiringAction.toRingAut_apply, MulSemiringAction.toRingEquiv_apply_apply,
      AlgEquiv.smul_def, hgz] at hs
    exact Units.ext (by
      simpa [redPow, cycZ] using zmod_eq_intCast_of_primitiveRoot_pow_eq_selmer hζ
        (PadicInt.toZModPow 1 (cycZ k Ω l g : ℤ_[l])) 1 (by rw [zpow_one]; exact hs.symm))
  have hrel : IsOpen ((gamU l U).subgroupOf U : Set U) := by
    rw [Subgroup.coe_subgroupOf]; exact hVopen.preimage continuous_subtype_val
  have hd : (gamU l U).relIndex U ∣ l - 1 := by
    rw [hV]; unfold Subgroup.relIndex
    rw [Subgroup.inf_subgroupOf_left, Subgroup.subgroupOf, MonoidHom.comap_ker, Subgroup.index_ker]
    refine (Subgroup.card_subgroup_dvd_card _).trans ?_
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, pow_one, Nat.totient_prime hp]
  have hunit : IsUnit (((gamU l U).relIndex U : ℕ) : O) := by
    have h2 := hp.two_le
    have hpos : 0 < (gamU l U).relIndex U := Nat.pos_of_dvd_of_pos hd (by omega)
    have hle : (gamU l U).relIndex U ≤ l - 1 := Nat.le_of_dvd (by omega) hd
    have hnd : ¬ l ∣ (gamU l U).relIndex U := fun h => by have := Nat.le_of_dvd hpos h; omega
    simpa using (PadicInt.isUnit_iff.mpr (PadicInt.norm_natCast_eq_one_iff.mpr
      ((Nat.Prime.coprime_iff_not_dvd hp).mpr hnd))).map (algebraMap ℤ_[l] O)
  have H2 := selUnit O (G k Ω) (QO l O) (twist₂ l (ψ * chiO k Ω l O ^ n)) hρ (gamU l U) U hVU
    hrel hunit (shaFam k Ω l) (conjStable_shaFam k Ω l)
  have HV := controlGamma k Ω l O (gamU l U) hVopen hVγ ψ n (le_trans hVU hψ) hn
  have hCV : cycU l U ≤ gamU l U := by
    have := cycU_le l (gamU l U)
    rwa [show cycU l (gamU l U) = cycU l U from cycU_levU l U (qExp l)] at this
  have H1 := selRes_injective_range_eq_of_le (twist₂ l (ψ * chiO k Ω l O ^ n))
    (cycU_levU l U (qExp l)) hCV (cycU_le l (gamU l U)) (conjStable_shaFam k Ω l) HV
  exact control_lemma _ hCV hVU (cycU_le l U) (conjStable_shaFam k Ω l) H1 H2

/-! ### Direct Bridges to `galoisShaLen` and `realGaloisSelmerSystem` -/

theorem galoisShaLen_eq_shaU_length (k E : Type) [Field k] [NumberField k] [Field E] [NumberField E]
    [Algebra k E] (p : Nat.Primes) (e : ℤ) :
    galoisShaLen E p e =
      Module.length ℤ_[p.1] (ShaU (qzG k (AlgebraicClosure E) p.1 e) p.1 (galOf k E (AlgebraicClosure E))) := by
  haveI : IsScalarTower k E (AlgebraicClosure E) := IsScalarTower.of_algebraMap_eq' rfl
  change shaLen (canonicalLData E p) e = _
  exact (shaLenEq k E (AlgebraicClosure E) p.1 (canonicalLData E p) e).1

theorem realGaloisSelmerSystem_shaLen_eq_shaU_length (k E : Type) [Field k] [NumberField k]
    [Field E] [NumberField E] [Algebra k E] (p : Nat.Primes) (e : ℕ) :
    realGaloisSelmerSystem.shaLen E p e =
      Module.length ℤ_[p.1] (ShaU (qzG k (AlgebraicClosure E) p.1 e) p.1 (galOf k E (AlgebraicClosure E))) :=
  (realGaloisSelmerSystem_shaLen E p e).symm ▸ galoisShaLen_eq_shaU_length k E p e

end ControlTheorems

end RHDirect.Stage13GL_SelmerTransport
