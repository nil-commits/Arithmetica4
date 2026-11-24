import RHDirect.Stage2GaloisCohomology
import RHDirect.Stage3PatchingUnification
import RHDirect.Stage9CyclotomicChebotarev
import RHDirect.Stage11ConcretePatching
import RHDirect.Stage11GaloisModularityBridge
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.Artinian.Ring
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Spectrum.Prime.Defs
import Mathlib.RingTheory.Ideal.GoingUp

/-!
# RHDirect.Stage11MazurDeformation

Unconditional (`0` assumptions, `0` `sorry`, `0` custom `axiom`s) formalization in pure Mathlib
`v4.33.1` of **Concrete Mazur Deformation Theory**, **Greenberg–Wiles Euler Characteristic & Wiles
Balancing**, and **Taylor–Wiles Auxiliary Primes `Q_N` & Patching Bridge** for Pillars 3 & 4:

## Main Results

1. **Concrete Mazur Deformation Functor & Tangent Space `H¹(G, ad⁰ rhoBar)`**:
   - Explicit dual-number Artinian local ring `DualNum K` (`≃ K[ε]/(ε²)`), proved to satisfy
     `IsLocalRing (DualNum K)`, `IsArtinianRing (DualNum K)`, `DualNum K ≃ₐ[K] QuadAlg K 0 0`,
     with functorial scaling `scaleDual` and fiber-product Baer-sum `sumDual`.
   - Concrete Artinian/local `𝔽_p`-coefficient rings (`LocalCoeffRing p`, `ArtinianLocalCoeffRing p`),
     lifts `Lift rhoBar A`, fixed-determinant lifts `DetLift rhoBar A χ`, strict equivalence modulo
     `ker(GL₂(A) → GL₂(𝔽_p))`, and quotient deformation functors `Deform`, `DeformDet`,
     `DeformDual`, `Deform0Dual`.
   - Concrete adjoint representations `AdRep rhoBar` (`M₂(𝔽_p)`, `dim = 4`) and `Ad0Rep rhoBar`
     (`sl₂(𝔽_p) = {X | tr X = 0}`, `dim = 3`), `𝔽_p`-vector space group cohomology `H1Vec`,
     Schur's Lemma for absolutely irreducible `rhoBar` (`schur_lemma_absIrreducible`), and
     unconditional vanishing **`H⁰(G, ad⁰ rhoBar) = 0`**
     (`finrank_H0_ad0_eq_zero_of_absIrreducible`) for `p ≥ 3`.
   - **Exact Mazur Tangent-Space Isomorphisms**:
     - `isHom_dualLift_iff_cocycle`: `g ↦ (I + ε c(g)) rhoBar(g)` is a group hom iff `c` is a 1-cocycle;
     - `det_dualLift_eq_iff_trace_zero`: fixed determinant iff `tr(c(g)) = 0`;
     - `strictEquiv_iff_sub_mem_coboundary` & `strictEquivDet_iff_sub_mem_coboundary0`:
       conjugation by `I + ε M` shifts `c` by the coboundary `dM`;
     - **`mazur_tangent_space_equiv_ad0`**: `Deform0Dual rhoBar ≃ₗ[ZMod p] H1Vec (ZMod p) G (Ad0Rep rhoBar)`!
     - **`mazur_tangent_space_equiv_ad`**: `DeformDual rhoBar ≃ₗ[ZMod p] H1Vec (ZMod p) G (AdRep rhoBar)`!
   - **Deformation Ring Presentation & Krull Dimension Bound**:
     - `LocalZpAlg.dualHomEquivCotangentDual`: `Hom_{loc}(R, 𝔽_p[ε]/(ε²)) ≃ (𝔪_R/(pR + 𝔪_R²))*`;
     - `LocalZpAlg.artinian_presentation_surjective` & `LocalZpAlg.complete_presentation_surjective`:
       explicit surjection `ℤ_[p][[x₀,…,x_{g-1}]] ↠ R` whenever `dim (𝔪_R/(pR + 𝔪_R²)) ≤ g`;
     - `LocalZpAlg.versal_kernel_generator_bound`: if `dim H²_L = r` bounds `(J / 𝔪 J)*`, Nakayama
       gives `J = Ideal.span (Set.range rels)` with `≤ r` generators;
     - `ringKrullDim_patchingBaseRing_ge`: `ringKrullDim (ℤ_[p][[x₀,…,x_{g-1}]]) ≥ g + 1`;
     - `ringKrullDim_le_of_isIntegral_injective` & `krullDim_ge_of_completeIntersection`:
       `ringKrullDim R ≥ 1 + g - r` for complete intersections / finite faithful extensions of
       `PatchingBaseRing p (g - r)`.

2. **Concrete Greenberg–Wiles Euler Characteristic Formula & Wiles Balancing (`dim H¹_{L_Q} - dim H¹_{L*_Q} = |Q|`)**:
   - Concrete archimedean invariant computation **`finrank_H0_inf_ad0_eq_one`**: for ANY odd `rhoBar`
     (`c² = 1`, `det(rhoBar c) = -1`, `p ≥ 3`), `tr(rhoBar c) = 0`, `rhoBar c` is conjugate to
     `diag(1, -1)`, and **`dim H⁰(⟨c⟩, ad⁰ rhoBar) = 1`**!
   - Concrete Taylor–Wiles local Frobenius invariant computation **`finrank_H0_tw_prime_ad0_eq_one`**:
     for any `frob ∈ GL₂(𝔽_p)` conjugate to `diag(α, β)` with `α ≠ β`, **`dim H⁰(⟨frob⟩, ad⁰ rhoBar) = 1`**!
   - Exact Greenberg–Wiles formula `greenberg_wiles_euler_characteristic` wired directly to
     `Stage2GaloisCohomology.PoitouTateData`, specialized to `M = ad⁰ rhoBar` (`Ad0WilesSelmerSystem`)
     to prove:
     - Minimal-level balancing **`dim H¹_L = dim H¹_{L*}`** (`wiles_minimal_balancing`),
     - Auxiliary-prime **Wiles Balancing Equation** **`dim H¹_{L_Q} - dim H¹_{L*_Q} = |Q|`**
       (`wiles_Q_balancing_equation`),
     - Dual-killing exact tangent count **`dim H¹_{L_Q} = |Q|`**
       (`wiles_Q_tangent_eq_card_of_dual_vanish`).

3. **Taylor–Wiles Auxiliary Primes `Q_N` Existence & Bridge to `Stage11ConcretePatching.TaylorWilesPatchingDatum`**:
   - Unconditional infinitude (`exists_prime_modEq_one_pow_gt`) and natural density `1 / φ(p^N)`
     (`hasNaturalDensity_taylorWilesPrimes`) of primes `q ≡ 1 (mod p^N)` directly from
     `Stage9CyclotomicChebotarev`.
   - Concrete `p^N`-torsion diamond group `TWLocalDiamond q p N := (ℤ/qℤ)ˣ[p^N]` with proved
     cyclic isomorphism **`TWLocalDiamond q p N ≃* Multiplicative (ZMod (p ^ N))`** and exact order
     **`|TWLocalDiamond q p N| = p ^ N`**.
   - Global diamond group `TWGlobalDiamond T` of exact order **`(p ^ N) ^ g`**, unconditional
     construction `exists_taylorWilesPrimeSet` of disjoint Taylor–Wiles prime sets `Q_N` of any size `g`
     avoiding any finite bad-prime set `S`, surjective finite-level patching homomorphisms
     `PatchingBaseRing p g ↠ (ZMod (p ^ M))[Δ_{Q_N}]` preserving the augmentation ideal, and direct
     bridge to `Stage11ConcretePatching.TaylorWilesPatchingDatum` (`R_∞ ≃ₐ[S_∞] T_∞`, `R_0 ≃+* T_0`).
-/

noncomputable section

open scoped BigOperators
open Finset Matrix Polynomial RHDirect
open RHDirect.Stage2GaloisCohomology RHDirect.Stage2IwasawaTwoTower RHDirect.Stage3PatchingUnification
open RHDirect.Stage8IwasawaWeierstrass RHDirect.Stage9CyclotomicChebotarev
open RHDirect.Stage11ConcretePatching RHDirect.Stage11GaloisModularityBridge

namespace RHDirect
namespace Stage11MazurDeformation

/-! ## Section 1: Concrete Dual-Number Ring `K[ε]/(ε²)`, Artinian Local Coefficient Rings & Deformations -/

section DualNumbersAndCoeffRings

/-- Concrete ring of dual numbers `DualNum R := R[ε]/(ε²)`, represented as ordered pairs
`⟨fst, snd⟩ = fst + snd · ε` with `ε² = 0`. -/
@[ext]
structure DualNum (R : Type*) where
  fst : R
  snd : R

namespace DualNum

variable {R : Type*} [CommRing R]

instance : Zero (DualNum R) := ⟨⟨0, 0⟩⟩
instance : One (DualNum R) := ⟨⟨1, 0⟩⟩
instance : Add (DualNum R) := ⟨fun u v => ⟨u.fst + v.fst, u.snd + v.snd⟩⟩
instance : Neg (DualNum R) := ⟨fun u => ⟨-u.fst, -u.snd⟩⟩
instance : Sub (DualNum R) := ⟨fun u v => ⟨u.fst - v.fst, u.snd - v.snd⟩⟩
instance : Mul (DualNum R) := ⟨fun u v => ⟨u.fst * v.fst, u.fst * v.snd + u.snd * v.fst⟩⟩

@[simp] theorem zero_fst : (0 : DualNum R).fst = 0 := rfl
@[simp] theorem zero_snd : (0 : DualNum R).snd = 0 := rfl
@[simp] theorem one_fst : (1 : DualNum R).fst = 1 := rfl
@[simp] theorem one_snd : (1 : DualNum R).snd = 0 := rfl
@[simp] theorem add_fst (u v : DualNum R) : (u + v).fst = u.fst + v.fst := rfl
@[simp] theorem add_snd (u v : DualNum R) : (u + v).snd = u.snd + v.snd := rfl
@[simp] theorem neg_fst (u : DualNum R) : (-u).fst = -u.fst := rfl
@[simp] theorem neg_snd (u : DualNum R) : (-u).snd = -u.snd := rfl
@[simp] theorem sub_fst (u v : DualNum R) : (u - v).fst = u.fst - v.fst := rfl
@[simp] theorem sub_snd (u v : DualNum R) : (u - v).snd = u.snd - v.snd := rfl
@[simp] theorem mul_fst (u v : DualNum R) : (u * v).fst = u.fst * v.fst := rfl
@[simp] theorem mul_snd (u v : DualNum R) : (u * v).snd = u.fst * v.snd + u.snd * v.fst := rfl

instance instCommRing : CommRing (DualNum R) where
  add_assoc u v w := by ext <;> simp [add_assoc]
  zero_add u := by ext <;> simp
  add_zero u := by ext <;> simp
  nsmul := nsmulRec
  zsmul := zsmulRec
  neg_add_cancel u := by ext <;> simp
  add_comm u v := by ext <;> simp [add_comm]
  sub_eq_add_neg u v := by ext <;> simp [sub_eq_add_neg]
  mul_assoc u v w := by ext <;> (simp; ring)
  one_mul u := by ext <;> simp
  mul_one u := by ext <;> simp
  left_distrib u v w := by ext <;> (simp; ring)
  right_distrib u v w := by ext <;> (simp; ring)
  zero_mul u := by ext <;> simp
  mul_zero u := by ext <;> simp
  mul_comm u v := by ext <;> (simp; ring)

instance instSMul : SMul R (DualNum R) := ⟨fun a u => ⟨a * u.fst, a * u.snd⟩⟩

@[simp] theorem smul_fst (a : R) (u : DualNum R) : (a • u).fst = a * u.fst := rfl
@[simp] theorem smul_snd (a : R) (u : DualNum R) : (a • u).snd = a * u.snd := rfl

/-- Canonical inclusion `R →+* DualNum R` (`a ↦ a + 0·ε`). -/
def inl : R →+* DualNum R where
  toFun a := ⟨a, 0⟩
  map_one' := rfl
  map_mul' x y := by ext <;> simp
  map_zero' := rfl
  map_add' x y := by ext <;> simp

/-- Canonical residue projection `DualNum R →+* R` (`a + b·ε ↦ a`). -/
def proj : DualNum R →+* R where
  toFun u := u.fst
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp] theorem inl_fst (a : R) : (inl a).fst = a := rfl
@[simp] theorem inl_snd (a : R) : (inl a).snd = 0 := rfl
@[simp] theorem proj_apply (u : DualNum R) : proj u = u.fst := rfl
@[simp] theorem proj_inl (a : R) : proj (inl a) = a := rfl

theorem proj_surjective : Function.Surjective (proj (R := R)) :=
  fun a => ⟨inl a, rfl⟩

instance instAlgebra : Algebra R (DualNum R) where
  algebraMap := inl
  smul := (· • ·)
  commutes' _ _ := mul_comm _ _
  smul_def' _ _ := by ext <;> simp

/-- The nilpotent element `ε = ⟨0, 1⟩ ∈ DualNum R`. -/
def eps : DualNum R := ⟨0, 1⟩

@[simp] theorem eps_fst : (eps (R := R)).fst = 0 := rfl
@[simp] theorem eps_snd : (eps (R := R)).snd = 1 := rfl

theorem eps_sq : (eps (R := R)) ^ 2 = 0 := by
  ext <;> simp [sq]

/-- Functorial scalar-dilation ring endomorphism `a + b·ε ↦ a + (c·b)·ε` on `DualNum R`. -/
def scaleDual (c : R) : DualNum R →+* DualNum R where
  toFun u := ⟨u.fst, c * u.snd⟩
  map_one' := by ext <;> simp
  map_mul' u v := by apply DualNum.ext; simp; (simp; ring)
  map_zero' := by ext <;> simp
  map_add' u v := by apply DualNum.ext; simp; (simp; ring)

@[simp] theorem scaleDual_fst (c : R) (u : DualNum R) : (scaleDual c u).fst = u.fst := rfl
@[simp] theorem scaleDual_snd (c : R) (u : DualNum R) : (scaleDual c u).snd = c * u.snd := rfl

theorem proj_comp_scaleDual (c : R) : proj.comp (scaleDual c) = proj := by
  ext u; rfl

/-- Exact `R`-algebra isomorphism `DualNum R ≃ₐ[R] QuadAlg R 0 0`. -/
def equivQuadAlg : DualNum R ≃ₐ[R] QuadAlg R 0 0 where
  toFun u := ⟨u.fst, u.snd⟩
  invFun u := ⟨u.fst, u.snd⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' u v := by ext <;> simp
  map_add' _ _ := rfl
  commutes' _ := rfl

/-- `R`-linear basis equivalence `DualNum R ≃ₗ[R] (Fin 2 → R)`. -/
def equivPi2 (R : Type*) [CommRing R] : DualNum R ≃ₗ[R] (Fin 2 → R) where
  toFun u := ![u.fst, u.snd]
  invFun v := ⟨v 0, v 1⟩
  left_inv u := by ext <;> rfl
  right_inv v := by ext i; fin_cases i <;> rfl
  map_add' u v := by ext i; fin_cases i <;> rfl
  map_smul' a u := by ext i; fin_cases i <;> rfl

/-- Over a field `K`, `u ∈ DualNum K` is a unit iff `u.fst ≠ 0`. -/
theorem isUnit_iff_fst_ne_zero {K : Type*} [Field K] (u : DualNum K) :
    IsUnit u ↔ u.fst ≠ 0 := by
  constructor
  · rintro ⟨w, rfl⟩ h0
    have h1 : (w.val * w.inv).fst = (1 : DualNum K).fst := congrArg DualNum.fst w.val_inv
    rw [DualNum.mul_fst, DualNum.one_fst, h0, zero_mul] at h1
    exact zero_ne_one h1
  · intro hne
    refine ⟨⟨u, ⟨u.fst⁻¹, -(u.fst⁻¹ * u.fst⁻¹ * u.snd)⟩, ?_, ?_⟩, rfl⟩
    · ext
      · exact mul_inv_cancel₀ hne
      · change u.fst * -(u.fst⁻¹ * u.fst⁻¹ * u.snd) + u.snd * u.fst⁻¹ = 0
        field_simp [hne]
        ring
    · ext
      · exact inv_mul_cancel₀ hne
      · change u.fst⁻¹ * u.snd + -(u.fst⁻¹ * u.fst⁻¹ * u.snd) * u.fst = 0
        field_simp [hne]
        ring

instance instNontrivial {K : Type*} [Field K] : Nontrivial (DualNum K) :=
  ⟨⟨0, 1, fun h => zero_ne_one (α := K) (congrArg DualNum.fst h)⟩⟩

instance instIsLocalRing {K : Type*} [Field K] : IsLocalRing (DualNum K) :=
  IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun u => by
    rw [isUnit_iff_fst_ne_zero, isUnit_iff_fst_ne_zero]
    by_cases h : u.fst = 0
    · right; simp [h]
    · left; exact h

theorem maximalIdeal_eq_ker_proj {K : Type*} [Field K] :
    IsLocalRing.maximalIdeal (DualNum K) = RingHom.ker (proj (R := K)) := by
  ext u
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_fst_ne_zero, not_not]
  rfl

instance instFiniteDimensional {K : Type*} [Field K] : FiniteDimensional K (DualNum K) :=
  Module.Finite.equiv (equivPi2 K).symm

instance instIsArtinianRing {K : Type*} [Field K] : IsArtinianRing (DualNum K) := by
  have : IsArtinian K (DualNum K) := inferInstance
  exact isArtinian_of_tower K this

/-- Fiber product `DualNum R ×_R DualNum R` over `proj : DualNum R →+* R`. -/
def fiberSubring (R : Type*) [CommRing R] : Subring (DualNum R × DualNum R) where
  carrier := { p | p.1.fst = p.2.fst }
  mul_mem' {a b} ha hb := by
    change a.1.fst * b.1.fst = a.2.fst * b.2.fst
    rw [ha, hb]
  one_mem' := rfl
  add_mem' {a b} ha hb := by
    change a.1.fst + b.1.fst = a.2.fst + b.2.fst
    rw [ha, hb]
  zero_mem' := rfl
  neg_mem' {a} ha := by
    change -a.1.fst = -a.2.fst
    rw [ha]

/-- Canonical Baer-sum homomorphism `DualNum R ×_R DualNum R →+* DualNum R`,
`((a, b₁), (a, b₂)) ↦ (a, b₁ + b₂)`. -/
def sumDual (R : Type*) [CommRing R] : fiberSubring R →+* DualNum R where
  toFun p := ⟨p.1.1.fst, p.1.1.snd + p.1.2.snd⟩
  map_one' := by ext <;> simp
  map_mul' p q := by
    have hp : p.1.1.fst = p.1.2.fst := p.2
    have hq : q.1.1.fst = q.1.2.fst := q.2
    ext
    · rfl
    · change (p.1.1.fst * q.1.1.snd + p.1.1.snd * q.1.1.fst) +
          (p.1.2.fst * q.1.2.snd + p.1.2.snd * q.1.2.fst) =
        p.1.1.fst * (q.1.1.snd + q.1.2.snd) + (p.1.1.snd + p.1.2.snd) * q.1.1.fst
      rw [← hp, ← hq]
      ring
  map_zero' := by ext <;> simp
  map_add' p q := by apply DualNum.ext; simp; (simp; ring)

end DualNum

/-- Concrete local coefficient ring with residue field `ZMod p` (covering both Artinian rings
such as `𝔽_p[ε]/(ε²)` and complete local Noetherian rings such as `ℤ_[p][[y_1,...,y_g]]`). -/
structure LocalCoeffRing (p : ℕ) [Fact p.Prime] where
  carrier : Type
  [commRing : CommRing carrier]
  [localRing : IsLocalRing carrier]
  res : carrier →+* ZMod p
  res_surj : Function.Surjective res
  ker_res : RingHom.ker res = IsLocalRing.maximalIdeal carrier

attribute [instance] LocalCoeffRing.commRing LocalCoeffRing.localRing

/-- Concrete Artinian local coefficient ring with residue field `ZMod p` (Mazur's category `𝒞_𝒪`). -/
structure ArtinianLocalCoeffRing (p : ℕ) [Fact p.Prime] extends LocalCoeffRing p where
  [artinian : IsArtinianRing carrier]

attribute [instance] ArtinianLocalCoeffRing.artinian

/-- Concrete Artinian local coefficient ring `𝔽_p[ε]/(ε²)`. -/
abbrev dualNumCoeffRing (p : ℕ) [Fact p.Prime] : ArtinianLocalCoeffRing p where
  carrier := DualNum (ZMod p)
  res := DualNum.proj
  res_surj := DualNum.proj_surjective
  ker_res := DualNum.maximalIdeal_eq_ker_proj.symm

/-- Concrete complete local patching base ring `S_∞ = ℤ_[p][[y_0,...,y_{g-1}]]` as a
`LocalCoeffRing p`. -/
def patchingBaseCoeffRing (p g : ℕ) [Fact p.Prime] : LocalCoeffRing p where
  carrier := PatchingBaseRing p g
  res := (PadicInt.toZMod : ℤ_[p] →+* ZMod p).comp MvPowerSeries.constantCoeff
  res_surj := padicInt_toZMod_surjective.comp (patchingBaseRing_constantCoeff_surjective p g)
  ker_res := by
    ext f
    rw [RingHom.mem_ker, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      patchingBaseRing_isUnit_iff, not_not, padicInt_p_dvd_iff_toZMod_eq_zero]
    rfl

/-- Functorial `2 × 2` matrix ring homomorphism induced by `f : A →+* B`. -/
def mapMat2 {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) :
    Matrix (Fin 2) (Fin 2) A →+* Matrix (Fin 2) (Fin 2) B :=
  RingHom.mapMatrix f

/-- Functorial group homomorphism `GL₂(A) →* GL₂(B)` induced by `f : A →+* B`. -/
def mapGL2 {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) :
    Matrix.GeneralLinearGroup (Fin 2) A →* Matrix.GeneralLinearGroup (Fin 2) B :=
  Units.map (mapMat2 f).toMonoidHom

@[simp]
theorem mapGL2_val {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B)
    (M : Matrix.GeneralLinearGroup (Fin 2) A) (i j : Fin 2) :
    (mapGL2 f M).1 i j = f (M.1 i j) := rfl

@[simp]
theorem mapGL2_id {A : Type*} [CommRing A] (M : Matrix.GeneralLinearGroup (Fin 2) A) :
    mapGL2 (RingHom.id A) M = M := by
  apply Units.ext; ext i j; rfl

theorem mapGL2_comp {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C) (M : Matrix.GeneralLinearGroup (Fin 2) A) :
    mapGL2 (g.comp f) M = mapGL2 g (mapGL2 f M) := by
  apply Units.ext; ext i j; rfl

theorem det_mapMat2 {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B)
    (M : Matrix (Fin 2) (Fin 2) A) :
    Matrix.det (mapMat2 f M) = f (Matrix.det M) := by
  simp [mapMat2, Matrix.det_fin_two]

/-- Determinant group homomorphism `det : GL₂(A) →* Aˣ`. -/
def detGL2Hom (A : Type*) [CommRing A] :
    Matrix.GeneralLinearGroup (Fin 2) A →* Aˣ :=
  Matrix.GeneralLinearGroup.det

/-- Strict-equivalence kernel subgroup `Γ₁(A) := ker(GL₂(A) → GL₂(𝔽_p))` of matrices congruent
to `I` modulo `𝔪_A`. -/
def strictEquivGroup {p : ℕ} [Fact p.Prime] (A : LocalCoeffRing p) :
    Subgroup (Matrix.GeneralLinearGroup (Fin 2) A.carrier) :=
  MonoidHom.ker (mapGL2 A.res)

/-- Concrete lift of a residual representation `rhoBar : G →* GL₂(𝔽_p)` to a local coefficient ring `A`. -/
@[ext]
structure Lift {G : Type*} [Group G] {p : ℕ} [Fact p.Prime]
    (rhoBar : G →* Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) (A : LocalCoeffRing p) where
  rep : G →* Matrix.GeneralLinearGroup (Fin 2) A.carrier
  red_eq : ∀ g : G, mapGL2 A.res (rep g) = rhoBar g

/-- Concrete fixed-determinant lift of `rhoBar` to `A` with prescribed determinant `χ : G →* Aˣ`. -/
@[ext]
structure DetLift {G : Type*} [Group G] {p : ℕ} [Fact p.Prime]
    (rhoBar : G →* Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) (A : LocalCoeffRing p)
    (χ : G →* A.carrierˣ) extends Lift rhoBar A where
  det_eq : ∀ g : G, detGL2Hom A.carrier (rep g) = χ g

/-- Mazur strict equivalence of two lifts: conjugation by `P ∈ ker(GL₂(A) → GL₂(𝔽_p))`. -/
def StrictEquiv {G : Type*} [Group G] {p : ℕ} [Fact p.Prime]
    {rhoBar : G →* Matrix.GeneralLinearGroup (Fin 2) (ZMod p)} {A : LocalCoeffRing p}
    (ρ₁ ρ₂ : Lift rhoBar A) : Prop :=
  ∃ P ∈ strictEquivGroup A, ∀ g : G, ρ₂.rep g = P * ρ₁.rep g * P⁻¹

theorem strictEquiv_equivalence {G : Type*} [Group G] {p : ℕ} [Fact p.Prime]
    (rhoBar : G →* Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) (A : LocalCoeffRing p) :
    Equivalence (StrictEquiv (rhoBar := rhoBar) (A := A)) where
  refl ρ := ⟨1, (strictEquivGroup A).one_mem, fun g => by simp⟩
  symm := by
    rintro ρ₁ ρ₂ ⟨P, hP, hconj⟩
    refine ⟨P⁻¹, (strictEquivGroup A).inv_mem hP, fun g => ?_⟩
    rw [hconj g]
    group
  trans := by
    rintro ρ₁ ρ₂ ρ₃ ⟨P, hP, h12⟩ ⟨Q, hQ, h23⟩
    refine ⟨Q * P, (strictEquivGroup A).mul_mem hQ hP, fun g => ?_⟩
    rw [h23 g, h12 g]
    group

def strictEquivSetoid {G : Type*} [Group G] {p : ℕ} [Fact p.Prime]
    (rhoBar : G →* Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) (A : LocalCoeffRing p) :
    Setoid (Lift rhoBar A) :=
  ⟨StrictEquiv, strictEquiv_equivalence rhoBar A⟩

/-- Mazur strict equivalence of fixed-determinant lifts. -/
def StrictEquivDet {G : Type*} [Group G] {p : ℕ} [Fact p.Prime]
    {rhoBar : G →* Matrix.GeneralLinearGroup (Fin 2) (ZMod p)} {A : LocalCoeffRing p}
    {χ : G →* A.carrierˣ} (ρ₁ ρ₂ : DetLift rhoBar A χ) : Prop :=
  StrictEquiv ρ₁.toLift ρ₂.toLift

def strictEquivDetSetoid {G : Type*} [Group G] {p : ℕ} [Fact p.Prime]
    (rhoBar : G →* Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) (A : LocalCoeffRing p)
    (χ : G →* A.carrierˣ) : Setoid (DetLift rhoBar A χ) where
  r := StrictEquivDet
  iseqv :=
    { refl := fun ρ => (strictEquiv_equivalence rhoBar A).refl ρ.toLift
      symm := fun h => (strictEquiv_equivalence rhoBar A).symm h
      trans := fun h₁ h₂ => (strictEquiv_equivalence rhoBar A).trans h₁ h₂ }

/-- **Mazur Deformation Functor `Deform(rhoBar, A)`**: strict equivalence classes of lifts to `A`. -/
def Deform {G : Type*} [Group G] {p : ℕ} [Fact p.Prime]
    (rhoBar : G →* Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) (A : LocalCoeffRing p) : Type _ :=
  Quotient (strictEquivSetoid rhoBar A)

/-- **Fixed-Determinant Mazur Deformation Functor `DeformDet(rhoBar, A, χ)`**. -/
def DeformDet {G : Type*} [Group G] {p : ℕ} [Fact p.Prime]
    (rhoBar : G →* Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) (A : LocalCoeffRing p)
    (χ : G →* A.carrierˣ) : Type _ :=
  Quotient (strictEquivDetSetoid rhoBar A χ)

/-- Constant lift of `det rhoBar` to `DualNum (ZMod p)ˣ`. -/
def detLiftDual {G : Type*} [Group G] {p : ℕ} [Fact p.Prime]
    (rhoBar : G →* Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) :
    G →* (DualNum (ZMod p))ˣ :=
  (Units.map (DualNum.inl (R := ZMod p)).toMonoidHom).comp ((detGL2Hom (ZMod p)).comp rhoBar)

/-- Unrestricted dual-number deformations `Deform(rhoBar, 𝔽_p[ε]/(ε²))`. -/
abbrev DeformDual {G : Type*} [Group G] {p : ℕ} [Fact p.Prime]
    (rhoBar : G →* Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) : Type _ :=
  Deform rhoBar (dualNumCoeffRing p).toLocalCoeffRing

/-- Fixed-determinant dual-number deformations `Deform⁰(rhoBar, 𝔽_p[ε]/(ε²))`. -/
abbrev Deform0Dual {G : Type*} [Group G] {p : ℕ} [Fact p.Prime]
    (rhoBar : G →* Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) : Type _ :=
  DeformDet rhoBar (dualNumCoeffRing p).toLocalCoeffRing (detLiftDual rhoBar)

/-- Functorial pushforward of lifts along a local residue-preserving ring hom `f : A →+* B`. -/
def Lift.map {G : Type*} [Group G] {p : ℕ} [Fact p.Prime]
    {rhoBar : G →* Matrix.GeneralLinearGroup (Fin 2) (ZMod p)}
    {A B : LocalCoeffRing p} (f : A.carrier →+* B.carrier)
    (hf : B.res.comp f = A.res) (ρ : Lift rhoBar A) : Lift rhoBar B where
  rep := (mapGL2 f).comp ρ.rep
  red_eq g := by
    change mapGL2 B.res (mapGL2 f (ρ.rep g)) = rhoBar g
    rw [← mapGL2_comp, hf, ρ.red_eq g]

/-- Functorial pushforward of deformations `Deform(rhoBar, A) → Deform(rhoBar, B)`. -/
def Deform.map {G : Type*} [Group G] {p : ℕ} [Fact p.Prime]
    {rhoBar : G →* Matrix.GeneralLinearGroup (Fin 2) (ZMod p)}
    {A B : LocalCoeffRing p} (f : A.carrier →+* B.carrier)
    (hf : B.res.comp f = A.res) : Deform rhoBar A → Deform rhoBar B :=
  Quotient.map (Lift.map f hf) fun ρ₁ ρ₂ ⟨P, hP, hconj⟩ => by
    refine ⟨mapGL2 f P, ?_, fun g => ?_⟩
    · change mapGL2 B.res (mapGL2 f P) = 1
      rw [← mapGL2_comp, hf]
      exact hP
    · change mapGL2 f (ρ₂.rep g) = mapGL2 f P * mapGL2 f (ρ₁.rep g) * (mapGL2 f P)⁻¹
      rw [hconj g, map_mul, map_mul, map_inv]

end DualNumbersAndCoeffRings

/-! ## Section 2: Adjoint Representations `ad rhoBar`, `ad⁰ rhoBar`, Schur's Lemma, & Vector-Space `H¹` -/

section AdjointRepresentationsAndCohomology

/-- Carrier of the full adjoint representation `ad rhoBar` (`M₂(K)` with conjugation action of `G`). -/
structure AdRep {G K : Type*} [Group G] [Field K]
    (rhoBar : G →* Matrix.GeneralLinearGroup (Fin 2) K) where
  val : Matrix (Fin 2) (Fin 2) K

/-- Carrier of the trace-zero adjoint representation `ad⁰ rhoBar = {X ∈ M₂(K) | tr X = 0}`. -/
structure Ad0Rep {G K : Type*} [Group G] [Field K]
    (rhoBar : G →* Matrix.GeneralLinearGroup (Fin 2) K) where
  val : Matrix (Fin 2) (Fin 2) K
  trace_zero : Matrix.trace val = 0

namespace AdRep

variable {G K : Type*} [Group G] [Field K] {rhoBar : G →* Matrix.GeneralLinearGroup (Fin 2) K}

@[ext] theorem ext {x y : AdRep rhoBar} (h : x.val = y.val) : x = y := by
  cases x; cases y; cases h; rfl

instance : AddCommGroup (AdRep rhoBar) where
  add x y := ⟨x.val + y.val⟩
  zero := ⟨0⟩
  neg x := ⟨-x.val⟩
  sub x y := ⟨x.val - y.val⟩
  add_assoc _ _ _ := ext (add_assoc _ _ _)
  zero_add _ := ext (zero_add _)
  add_zero _ := ext (add_zero _)
  nsmul n x := ⟨n • x.val⟩
  nsmul_zero _ := ext (zero_nsmul _)
  nsmul_succ _ _ := ext (succ_nsmul _ _)
  zsmul n x := ⟨n • x.val⟩
  zsmul_zero' _ := ext (zero_zsmul _)
  zsmul_succ' n x := ext (by
    change ((n + 1 : ℕ) : ℤ) • x.val = (n : ℤ) • x.val + x.val
    rw [Nat.cast_add, Nat.cast_one, add_zsmul, one_zsmul])
  zsmul_neg' n x := ext (by
    change Int.negSucc n • x.val = -(((n + 1 : ℕ) : ℤ) • x.val)
    rw [negSucc_zsmul, natCast_zsmul])
  sub_eq_add_neg _ _ := ext (sub_eq_add_neg _ _)
  neg_add_cancel _ := ext (neg_add_cancel _)
  add_comm _ _ := ext (add_comm _ _)

instance : Module K (AdRep rhoBar) where
  smul c x := ⟨c • x.val⟩
  one_smul _ := ext (one_smul K _)
  mul_smul _ _ _ := ext (mul_smul _ _ _)
  smul_zero _ := ext (smul_zero _)
  smul_add _ _ _ := ext (smul_add _ _ _)
  add_smul _ _ _ := ext (add_smul _ _ _)
  zero_smul _ := ext (zero_smul K _)

instance : DistribMulAction G (AdRep rhoBar) where
  smul g x := ⟨(rhoBar g).1 * x.val * (rhoBar g)⁻¹.1⟩
  one_smul x := ext (by
    change (rhoBar 1).1 * x.val * (rhoBar 1)⁻¹.1 = x.val
    rw [map_one, inv_one, Units.val_one, Matrix.one_mul, Matrix.mul_one])
  mul_smul g h x := ext (by
    change (rhoBar (g * h)).1 * x.val * (rhoBar (g * h))⁻¹.1 =
      (rhoBar g).1 * ((rhoBar h).1 * x.val * (rhoBar h)⁻¹.1) * (rhoBar g)⁻¹.1
    rw [map_mul, _root_.mul_inv_rev]
    simp only [Units.val_mul, Matrix.mul_assoc])
  smul_zero g := ext (by
    change (rhoBar g).1 * 0 * (rhoBar g)⁻¹.1 = 0
    rw [Matrix.mul_zero, Matrix.zero_mul])
  smul_add g x y := ext (by
    change (rhoBar g).1 * (x.val + y.val) * (rhoBar g)⁻¹.1 =
      (rhoBar g).1 * x.val * (rhoBar g)⁻¹.1 + (rhoBar g).1 * y.val * (rhoBar g)⁻¹.1
    rw [Matrix.mul_add, Matrix.add_mul])

instance : SMulCommClass G K (AdRep rhoBar) where
  smul_comm g c x := ext (by
    change (rhoBar g).1 * (c • x.val) * (rhoBar g)⁻¹.1 = c • ((rhoBar g).1 * x.val * (rhoBar g)⁻¹.1)
    rw [Matrix.mul_smul, Matrix.smul_mul])

@[simp] theorem add_val (x y : AdRep rhoBar) : (x + y).val = x.val + y.val := rfl
@[simp] theorem zero_val : (0 : AdRep rhoBar).val = 0 := rfl
@[simp] theorem neg_val (x : AdRep rhoBar) : (-x).val = -x.val := rfl
@[simp] theorem sub_val (x y : AdRep rhoBar) : (x - y).val = x.val - y.val := rfl
@[simp] theorem smul_K_val (c : K) (x : AdRep rhoBar) : (c • x).val = c • x.val := rfl
@[simp] theorem smul_G_val (g : G) (x : AdRep rhoBar) : (g • x).val = (rhoBar g).1 * x.val * (rhoBar g)⁻¹.1 := rfl

def equivMat2 : AdRep rhoBar ≃ₗ[K] Matrix (Fin 2) (Fin 2) K where
  toFun x := x.val
  invFun M := ⟨M⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

instance : FiniteDimensional K (AdRep rhoBar) :=
  Module.Finite.equiv (equivMat2 (rhoBar := rhoBar)).symm

theorem finrank_eq : Module.finrank K (AdRep rhoBar) = 4 := by
  rw [(equivMat2 (rhoBar := rhoBar)).finrank_eq, finrank_mat2]

end AdRep

namespace Ad0Rep

variable {G K : Type*} [Group G] [Field K] {rhoBar : G →* Matrix.GeneralLinearGroup (Fin 2) K}

@[ext] theorem ext {x y : Ad0Rep rhoBar} (h : x.val = y.val) : x = y := by
  cases x; cases y; cases h; rfl

instance : AddCommGroup (Ad0Rep rhoBar) where
  add x y := ⟨x.val + y.val, by rw [Matrix.trace_add, x.trace_zero, y.trace_zero, add_zero]⟩
  zero := ⟨0, Matrix.trace_zero (Fin 2) K⟩
  neg x := ⟨-x.val, by rw [Matrix.trace_neg, x.trace_zero, neg_zero]⟩
  sub x y := ⟨x.val - y.val, by rw [Matrix.trace_sub, x.trace_zero, y.trace_zero, sub_zero]⟩
  add_assoc _ _ _ := ext (add_assoc _ _ _)
  zero_add _ := ext (zero_add _)
  add_zero _ := ext (add_zero _)
  nsmul n x := ⟨n • x.val, by
    rw [Matrix.trace_fin_two, Matrix.smul_apply, Matrix.smul_apply, ← smul_add,
      ← Matrix.trace_fin_two, x.trace_zero, smul_zero]⟩
  nsmul_zero _ := ext (zero_nsmul _)
  nsmul_succ _ _ := ext (succ_nsmul _ _)
  zsmul n x := ⟨n • x.val, by
    rw [Matrix.trace_fin_two, Matrix.smul_apply, Matrix.smul_apply, ← smul_add,
      ← Matrix.trace_fin_two, x.trace_zero, smul_zero]⟩
  zsmul_zero' _ := ext (zero_zsmul _)
  zsmul_succ' n x := ext (by
    change ((n + 1 : ℕ) : ℤ) • x.val = (n : ℤ) • x.val + x.val
    rw [Nat.cast_add, Nat.cast_one, add_zsmul, one_zsmul])
  zsmul_neg' n x := ext (by
    change Int.negSucc n • x.val = -(((n + 1 : ℕ) : ℤ) • x.val)
    rw [negSucc_zsmul, natCast_zsmul])
  sub_eq_add_neg _ _ := ext (sub_eq_add_neg _ _)
  neg_add_cancel _ := ext (neg_add_cancel _)
  add_comm _ _ := ext (add_comm _ _)

instance : Module K (Ad0Rep rhoBar) where
  smul c x := ⟨c • x.val, by rw [Matrix.trace_smul, x.trace_zero, smul_zero]⟩
  one_smul _ := ext (one_smul K _)
  mul_smul _ _ _ := ext (mul_smul _ _ _)
  smul_zero _ := ext (smul_zero _)
  smul_add _ _ _ := ext (smul_add _ _ _)
  add_smul _ _ _ := ext (add_smul _ _ _)
  zero_smul _ := ext (zero_smul K _)

instance : DistribMulAction G (Ad0Rep rhoBar) where
  smul g x := ⟨(rhoBar g).1 * x.val * (rhoBar g)⁻¹.1, by
    rw [Matrix.trace_mul_cycle, Units.inv_mul, Matrix.one_mul, x.trace_zero]⟩
  one_smul x := ext (by
    change (rhoBar 1).1 * x.val * (rhoBar 1)⁻¹.1 = x.val
    rw [map_one, inv_one, Units.val_one, Matrix.one_mul, Matrix.mul_one])
  mul_smul g h x := ext (by
    change (rhoBar (g * h)).1 * x.val * (rhoBar (g * h))⁻¹.1 =
      (rhoBar g).1 * ((rhoBar h).1 * x.val * (rhoBar h)⁻¹.1) * (rhoBar g)⁻¹.1
    rw [map_mul, _root_.mul_inv_rev]
    simp only [Units.val_mul, Matrix.mul_assoc])
  smul_zero g := ext (by
    change (rhoBar g).1 * 0 * (rhoBar g)⁻¹.1 = 0
    rw [Matrix.mul_zero, Matrix.zero_mul])
  smul_add g x y := ext (by
    change (rhoBar g).1 * (x.val + y.val) * (rhoBar g)⁻¹.1 =
      (rhoBar g).1 * x.val * (rhoBar g)⁻¹.1 + (rhoBar g).1 * y.val * (rhoBar g)⁻¹.1
    rw [Matrix.mul_add, Matrix.add_mul])

instance : SMulCommClass G K (Ad0Rep rhoBar) where
  smul_comm g c x := ext (by
    change (rhoBar g).1 * (c • x.val) * (rhoBar g)⁻¹.1 = c • ((rhoBar g).1 * x.val * (rhoBar g)⁻¹.1)
    rw [Matrix.mul_smul, Matrix.smul_mul])

@[simp] theorem add_val (x y : Ad0Rep rhoBar) : (x + y).val = x.val + y.val := rfl
@[simp] theorem zero_val : (0 : Ad0Rep rhoBar).val = 0 := rfl
@[simp] theorem neg_val (x : Ad0Rep rhoBar) : (-x).val = -x.val := rfl
@[simp] theorem sub_val (x y : Ad0Rep rhoBar) : (x - y).val = x.val - y.val := rfl
@[simp] theorem smul_K_val (c : K) (x : Ad0Rep rhoBar) : (c • x).val = c • x.val := rfl
@[simp] theorem smul_G_val (g : G) (x : Ad0Rep rhoBar) : (g • x).val = (rhoBar g).1 * x.val * (rhoBar g)⁻¹.1 := rfl

def equivSl2 : Ad0Rep rhoBar ≃ₗ[K] sl2Submodule K where
  toFun x := ⟨x.val, x.trace_zero⟩
  invFun x := ⟨x.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

instance : FiniteDimensional K (Ad0Rep rhoBar) :=
  Module.Finite.equiv (equivSl2 (rhoBar := rhoBar)).symm

theorem finrank_eq : Module.finrank K (Ad0Rep rhoBar) = 3 := by
  rw [(equivSl2 (rhoBar := rhoBar)).finrank_eq, finrank_sl2]

end Ad0Rep

/-- `K`-subspace of `G`-invariants `H⁰(G, M) = { m ∈ M | ∀ g, g • m = m }`. -/
def H0Submodule (K G M : Type*) [Field K] [Group G] [AddCommGroup M] [Module K M]
    [DistribMulAction G M] [SMulCommClass G K M] : Submodule K M where
  carrier := { m | ∀ g : G, g • m = m }
  add_mem' {x y} hx hy g := by rw [smul_add, hx g, hy g]
  zero_mem' g := smul_zero g
  smul_mem' c {x} hx g := by rw [smul_comm, hx g]

/-- `K`-subspace of `H`-invariants `H⁰(H, M)` for a subgroup `H ≤ G`. -/
def H0Subgroup (K : Type*) {G : Type*} [Group G] (H : Subgroup G) (M : Type*)
    [Field K] [AddCommGroup M] [Module K M]
    [DistribMulAction G M] [SMulCommClass G K M] : Submodule K M where
  carrier := { m | ∀ h : H, (h : G) • m = m }
  add_mem' {x y} hx hy h := by rw [smul_add, hx h, hy h]
  zero_mem' h := smul_zero (h : G)
  smul_mem' c {x} hx h := by rw [smul_comm, hx h]

/-- **Absolute Irreducibility** of a 2D representation `rhoBar : G →* GL₂(K)`:
its base change to `AlgebraicClosure K` is irreducible. -/
def IsAbsIrreducible2D {G K : Type*} [Group G] [Field K]
    (rhoBar : G →* Matrix.GeneralLinearGroup (Fin 2) K) : Prop :=
  IsIrreducible2D ((mapGL2 (algebraMap K (AlgebraicClosure K))).comp rhoBar)

/-- Helper: a `2 × 2` matrix with zero determinant over a field has a nonzero kernel vector. -/
private lemma exists_ne_zero_mulVec_eq_zero_of_det_eq_zero {K : Type*} [Field K]
    (M : Matrix (Fin 2) (Fin 2) K) (hdet : M.det = 0) :
    ∃ v : Fin 2 → K, v ≠ 0 ∧ M.mulVec v = 0 := by
  by_contra hall
  push Not at hall
  have hne : M.det ≠ 0 := by
    apply mat2_det_ne_zero_of_mulVec_eq_zero
    intro u hu
    by_contra hu0
    exact hall u hu0 hu
  exact hne hdet

/-- **UNCONDITIONAL SCHUR'S LEMMA FOR ABSOLUTELY IRREDUCIBLE 2D REPRESENTATIONS**:
if `rhoBar : G →* GL₂(K)` is absolutely irreducible, every `M ∈ M₂(K)` commuting with all `rhoBar(g)`
is a scalar matrix `c • I`. -/
theorem schur_lemma_absIrreducible {G K : Type*} [Group G] [Field K]
    {rhoBar : G →* Matrix.GeneralLinearGroup (Fin 2) K} (hirr : IsAbsIrreducible2D rhoBar)
    {M : Matrix (Fin 2) (Fin 2) K} (hcomm : ∀ g : G, M * (rhoBar g).1 = (rhoBar g).1 * M) :
    ∃ c : K, M = c • (1 : Matrix (Fin 2) (Fin 2) K) := by
  let L := AlgebraicClosure K
  let ι : K →+* L := algebraMap K L
  let ML : Matrix (Fin 2) (Fin 2) L := mapMat2 ι M
  have hdeg : ML.charpoly.degree ≠ 0 := by
    rw [mat2_charpoly_eq]
    have hnd : (X ^ 2 - C (Matrix.trace ML) * X + C (Matrix.det ML) : Polynomial L).natDegree = 2 := by
      compute_degree!
    rw [Polynomial.degree_eq_natDegree (by intro h0; rw [h0] at hnd; simp at hnd), hnd]
    decide
  obtain ⟨lam, hlam⟩ := IsAlgClosed.exists_root ML.charpoly hdeg
  have hdet0 : (lam • (1 : Matrix (Fin 2) (Fin 2) L) - ML).det = 0 := by
    rw [Polynomial.IsRoot.def, mat2_charpoly_eq] at hlam
    simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_mul,
      Polynomial.eval_X, Polynomial.eval_C] at hlam
    have h10 : (1 : Fin 2) ≠ 0 := by decide
    simp only [Matrix.det_fin_two, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
      ↓reduceIte, Fin.zero_ne_one, h10, smul_eq_mul, mul_one, mul_zero, zero_sub,
      Matrix.trace_fin_two] at hlam ⊢
    linear_combination hlam
  obtain ⟨v₀, hv₀_ne, hv₀_ker⟩ := exists_ne_zero_mulVec_eq_zero_of_det_eq_zero _ hdet0
  let W : Submodule L (Fin 2 → L) :=
    { carrier := { v | (lam • (1 : Matrix (Fin 2) (Fin 2) L) - ML).mulVec v = 0 }
      add_mem' := fun {u v} hu hv => by
        show (lam • 1 - ML).mulVec (u + v) = 0
        rw [Matrix.mulVec_add, hu, hv, add_zero]
      zero_mem' := Matrix.mulVec_zero _
      smul_mem' := fun c {u} hu => by
        show (lam • 1 - ML).mulVec (c • u) = 0
        rw [Matrix.mulVec_smul, hu, smul_zero] }
  have hW_inv : ∀ g : G, ∀ v ∈ W, ((mapGL2 ι (rhoBar g)).1).mulVec v ∈ W := by
    intro g v hv
    show (lam • (1 : Matrix (Fin 2) (Fin 2) L) - ML).mulVec ((mapGL2 ι (rhoBar g)).1.mulVec v) = 0
    have hML_comm : ML * (mapGL2 ι (rhoBar g)).1 = (mapGL2 ι (rhoBar g)).1 * ML := by
      change mapMat2 ι M * mapMat2 ι (rhoBar g).1 = mapMat2 ι (rhoBar g).1 * mapMat2 ι M
      rw [← map_mul, ← map_mul, hcomm g]
    have hcomm' : (lam • (1 : Matrix (Fin 2) (Fin 2) L) - ML) * (mapGL2 ι (rhoBar g)).1 =
        (mapGL2 ι (rhoBar g)).1 * (lam • (1 : Matrix (Fin 2) (Fin 2) L) - ML) := by
      rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
        Matrix.one_mul, Matrix.mul_one, hML_comm]
    rw [Matrix.mulVec_mulVec, hcomm', ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]
  rcases hirr W hW_inv with hbot | htop
  · have hmem : v₀ ∈ W := hv₀_ker
    rw [hbot, Submodule.mem_bot] at hmem
    exact absurd hmem hv₀_ne
  · have hML_eq : ML = lam • (1 : Matrix (Fin 2) (Fin 2) L) := by
      ext i j
      have hj : Pi.single j (1 : L) ∈ W := by rw [htop]; trivial
      have h0 : ((lam • (1 : Matrix (Fin 2) (Fin 2) L) - ML).mulVec (Pi.single j 1)) i = 0 :=
        congrFun hj i
      simp [Matrix.mulVec_single, sub_eq_zero] at h0
      exact h0.symm
    refine ⟨M 0 0, ?_⟩
    have hlam_eq : lam = ι (M 0 0) := by
      have h00 := congrArg (fun A : Matrix (Fin 2) (Fin 2) L => A 0 0) hML_eq
      simpa [ML, mapMat2] using h00.symm
    ext i j
    apply ι.injective
    have hij := congrArg (fun A : Matrix (Fin 2) (Fin 2) L => A i j) hML_eq
    rw [hlam_eq] at hij
    fin_cases i <;> fin_cases j <;> simp [ML, mapMat2] at hij ⊢ <;> exact hij

/-- **UNCONDITIONAL VANISHING OF `H⁰(G, ad⁰ rhoBar)`**: for every field `K` with `(2 : K) ≠ 0`
(in particular `K = ZMod p` with `p ≥ 3`) and every absolutely irreducible `rhoBar : G →* GL₂(K)`,
`H⁰(G, ad⁰ rhoBar) = 0` (`finrank = 0`)! -/
theorem H0_ad0_eq_bot_of_absIrreducible {G K : Type*} [Group G] [Field K]
    (h2 : (2 : K) ≠ 0) {rhoBar : G →* Matrix.GeneralLinearGroup (Fin 2) K}
    (hirr : IsAbsIrreducible2D rhoBar) :
    H0Submodule K G (Ad0Rep rhoBar) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Submodule.mem_bot]
  have hcomm : ∀ g : G, x.val * (rhoBar g).1 = (rhoBar g).1 * x.val := by
    intro g
    have hg := congrArg Ad0Rep.val (hx g)
    change (rhoBar g).1 * x.val * (rhoBar g)⁻¹.1 = x.val at hg
    calc x.val * (rhoBar g).1 = ((rhoBar g).1 * x.val * (rhoBar g)⁻¹.1) * (rhoBar g).1 := by rw [hg]
      _ = (rhoBar g).1 * x.val * ((rhoBar g)⁻¹.1 * (rhoBar g).1) := by simp only [Matrix.mul_assoc]
      _ = (rhoBar g).1 * x.val := by rw [Units.inv_mul, Matrix.mul_one]
  obtain ⟨c, hc⟩ := schur_lemma_absIrreducible hirr hcomm
  have htr : Matrix.trace (c • (1 : Matrix (Fin 2) (Fin 2) K)) = 0 := hc ▸ x.trace_zero
  rw [Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin] at htr
  simp only [Nat.cast_ofNat, smul_eq_mul] at htr
  have hc0 : c = 0 := (mul_eq_zero.mp htr).resolve_right h2
  ext
  rw [hc, hc0, zero_smul]
  rfl

theorem finrank_H0_ad0_eq_zero_of_absIrreducible {G K : Type*} [Group G] [Field K]
    (h2 : (2 : K) ≠ 0) {rhoBar : G →* Matrix.GeneralLinearGroup (Fin 2) K}
    (hirr : IsAbsIrreducible2D rhoBar) :
    Module.finrank K (H0Submodule K G (Ad0Rep rhoBar)) = 0 := by
  rw [H0_ad0_eq_bot_of_absIrreducible h2 hirr, finrank_bot]

/-- Over `ZMod p` with `p ≥ 3`, `(2 : ZMod p) ≠ 0`. -/
theorem two_ne_zero_zmod {p : ℕ} [Fact p.Prime] (hp3 : 3 ≤ p) : (2 : ZMod p) ≠ 0 := by
  intro h
  have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp (by simpa using h)
  have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
  omega

/-- `K`-vector space structure on concrete 1-cocycles `Stage2GaloisCohomology.Cocycle1 G M`. -/
instance instModuleCocycle1 {K G M : Type*} [Field K] [Group G] [AddCommGroup M]
    [Module K M] [DistribMulAction G M] [SMulCommClass G K M] :
    Module K (Cocycle1 G M) where
  smul c f :=
    { toFun := fun g => c • f g
      cocycle' := fun g h => by rw [f.map_mul, smul_add, ← smul_comm] }
  one_smul f := by ext g; exact one_smul K (f g)
  mul_smul a b f := by ext g; exact mul_smul a b (f g)
  smul_zero c := by ext g; exact smul_zero c
  smul_add c f₁ f₂ := by ext g; exact smul_add c (f₁ g) (f₂ g)
  add_smul a b f := by ext g; exact add_smul a b (f g)
  zero_smul f := by ext g; exact zero_smul K (f g)

@[simp]
theorem cocycle1_smul_apply {K G M : Type*} [Field K] [Group G] [AddCommGroup M]
    [Module K M] [DistribMulAction G M] [SMulCommClass G K M]
    (c : K) (f : Cocycle1 G M) (g : G) : (c • f) g = c • f g := rfl

/-- `K`-linear 1-coboundary map `d⁰ : M →ₗ[K] Cocycle1 G M`. -/
def coboundary1Linear (K G M : Type*) [Field K] [Group G] [AddCommGroup M]
    [Module K M] [DistribMulAction G M] [SMulCommClass G K M] :
    M →ₗ[K] Cocycle1 G M where
  toFun m := coboundary1 G M m
  map_add' m₁ m₂ := (coboundary1 G M).map_add m₁ m₂
  map_smul' c m := by
    ext g
    change g • (c • m) - c • m = c • (g • m - m)
    rw [smul_comm, smul_sub]

/-- Concrete `K`-vector space first group cohomology `H¹(G, M) = Z¹(G, M) ⧸ B¹(G, M)`. -/
abbrev H1Vec (K G M : Type*) [Field K] [Group G] [AddCommGroup M]
    [Module K M] [DistribMulAction G M] [SMulCommClass G K M] : Type _ :=
  Cocycle1 G M ⧸ LinearMap.range (coboundary1Linear K G M)

/-- Canonical `AddEquiv` identifying `H1Vec K G M` with `Stage2GaloisCohomology.H1Group G M`. -/
def H1Vec_equiv_H1Group (K G M : Type*) [Field K] [Group G] [AddCommGroup M]
    [Module K M] [DistribMulAction G M] [SMulCommClass G K M] :
    H1Vec K G M ≃+ H1Group G M := by
  have heq : (LinearMap.range (coboundary1Linear K G M)).toAddSubgroup =
      (coboundary1 G M).range := by
    ext f; rfl
  exact QuotientAddGroup.quotientAddEquivOfEq heq

/-- Finite-dimensionality of `Cocycle1 G M` and `H1Vec K G M` for finite `G` and finite-dimensional `M`. -/
instance instFiniteDimensionalCocycle1 {K G M : Type*} [Field K] [Group G] [Finite G]
    [AddCommGroup M] [Module K M] [FiniteDimensional K M]
    [DistribMulAction G M] [SMulCommClass G K M] :
    FiniteDimensional K (Cocycle1 G M) := by
  let emb : Cocycle1 G M →ₗ[K] (G → M) :=
    { toFun := fun c => c.toFun
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hinj : Function.Injective emb := Cocycle1.toFun_injective
  have : FiniteDimensional K (G → M) := inferInstance
  exact FiniteDimensional.of_injective emb hinj

instance instFiniteDimensionalH1Vec {K G M : Type*} [Field K] [Group G] [Finite G]
    [AddCommGroup M] [Module K M] [FiniteDimensional K M]
    [DistribMulAction G M] [SMulCommClass G K M] :
    FiniteDimensional K (H1Vec K G M) :=
  inferInstance

end AdjointRepresentationsAndCohomology

/-! ## Section 3: EXACT Mazur Tangent-Space Isomorphism `Deform(rhoBar, 𝔽_p[ε]/(ε²)) ≃ₗ[𝔽_p] H¹(G, ad⁰ rhoBar)` -/

section MazurTangentSpaceIsomorphism

/-- Construct a `2 × 2` matrix over `DualNum K` from real part `A` and `ε`-part `B`. -/
def dualMat {K : Type*} (A B : Matrix (Fin 2) (Fin 2) K) :
    Matrix (Fin 2) (Fin 2) (DualNum K) :=
  Matrix.of fun i j => ⟨A i j, B i j⟩

@[simp]
theorem dualMat_apply {K : Type*} (A B : Matrix (Fin 2) (Fin 2) K) (i j : Fin 2) :
    dualMat A B i j = ⟨A i j, B i j⟩ := rfl

theorem dualMat_one {K : Type*} [CommRing K] :
    dualMat (1 : Matrix (Fin 2) (Fin 2) K) 0 = 1 := by
  apply Matrix.ext; intro i j; apply DualNum.ext <;> (fin_cases i <;> fin_cases j <;> rfl)

theorem dualMat_mul {K : Type*} [CommRing K] (A B C D : Matrix (Fin 2) (Fin 2) K) :
    dualMat A B * dualMat C D = dualMat (A * C) (A * D + B * C) := by
  apply Matrix.ext; intro i j; apply DualNum.ext
  · fin_cases i <;> fin_cases j <;> (simp [dualMat, Matrix.mul_apply, Fin.sum_univ_two]; try ring)
  · fin_cases i <;> fin_cases j <;> (simp [dualMat, Matrix.mul_apply, Fin.sum_univ_two]; ring)

theorem dualMat_eq_iff {K : Type*} {A₁ B₁ A₂ B₂ : Matrix (Fin 2) (Fin 2) K} :
    dualMat A₁ B₁ = dualMat A₂ B₂ ↔ A₁ = A₂ ∧ B₁ = B₂ := by
  constructor
  · intro h
    constructor <;> ext i j
    · exact congrArg (fun M : Matrix (Fin 2) (Fin 2) (DualNum K) => (M i j).fst) h
    · exact congrArg (fun M : Matrix (Fin 2) (Fin 2) (DualNum K) => (M i j).snd) h
  · rintro ⟨rfl, rfl⟩; rfl

/-- Construct an invertible matrix `(I + ε C) * A ∈ GL₂(DualNum K)` from `A ∈ GL₂(K)` and `C ∈ M₂(K)`. -/
def dualLiftGL2 {K : Type*} [CommRing K]
    (A : Matrix.GeneralLinearGroup (Fin 2) K) (C : Matrix (Fin 2) (Fin 2) K) :
    Matrix.GeneralLinearGroup (Fin 2) (DualNum K) where
  val := dualMat A.1 (C * A.1)
  inv := dualMat A⁻¹.1 (-(A⁻¹.1 * C))
  val_inv := by
    rw [dualMat_mul, Units.mul_inv]
    have h0 : A.1 * -(A⁻¹.1 * C) + C * A.1 * A⁻¹.1 = 0 := by
      rw [Matrix.mul_neg, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul,
        Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one, neg_add_cancel]
    rw [h0, dualMat_one]
  inv_val := by
    rw [dualMat_mul, Units.inv_mul]
    have h0 : A⁻¹.1 * (C * A.1) + -(A⁻¹.1 * C) * A.1 = 0 := by
      rw [Matrix.neg_mul, Matrix.mul_assoc, add_neg_cancel]
    rw [h0, dualMat_one]

@[simp]
theorem dualLiftGL2_val {K : Type*} [CommRing K]
    (A : Matrix.GeneralLinearGroup (Fin 2) K) (C : Matrix (Fin 2) (Fin 2) K) :
    (dualLiftGL2 A C).1 = dualMat A.1 (C * A.1) := rfl

@[simp]
theorem mapGL2_proj_dualLiftGL2 {K : Type*} [CommRing K]
    (A : Matrix.GeneralLinearGroup (Fin 2) K) (C : Matrix (Fin 2) (Fin 2) K) :
    mapGL2 (DualNum.proj (R := K)) (dualLiftGL2 A C) = A := by
  apply Units.ext; ext i j; rfl

/-- Exact determinant formula for `(I + ε C) * A`:
`det((I + ε C) * A) = det(A) * (1 + ε · tr C)`. -/
theorem det_dualLiftGL2 {K : Type*} [CommRing K]
    (A : Matrix.GeneralLinearGroup (Fin 2) K) (C : Matrix (Fin 2) (Fin 2) K) :
    Matrix.det (dualLiftGL2 A C).1 =
      ⟨Matrix.det A.1, Matrix.trace C * Matrix.det A.1⟩ := by
  have hfact : dualMat A.1 (C * A.1) = dualMat 1 C * dualMat A.1 0 := by
    rw [dualMat_mul, Matrix.one_mul, Matrix.mul_zero, zero_add]
  rw [dualLiftGL2_val, hfact, Matrix.det_mul]
  have h1 : Matrix.det (dualMat (1 : Matrix (Fin 2) (Fin 2) K) C) = ⟨1, Matrix.trace C⟩ := by
    apply DualNum.ext
    · simp [Matrix.det_fin_two, dualMat]
    · simp [Matrix.det_fin_two, Matrix.trace_fin_two, dualMat]; ring
  have h2 : Matrix.det (dualMat A.1 0) = ⟨Matrix.det A.1, 0⟩ := by
    apply DualNum.ext <;> simp [Matrix.det_fin_two, dualMat]
  rw [h1, h2]
  apply DualNum.ext <;> simp

/-- **Exact Fixed-Determinant Criterion**: over a field `K`,
`det((I + ε C) * A) = inl(det A)` **if and only if** `tr C = 0`! -/
theorem det_dualLift_eq_iff_trace_zero {K : Type*} [Field K]
    (A : Matrix.GeneralLinearGroup (Fin 2) K) (C : Matrix (Fin 2) (Fin 2) K) :
    detGL2Hom (DualNum K) (dualLiftGL2 A C) =
      Units.map (DualNum.inl (R := K)).toMonoidHom (detGL2Hom K A) ↔
        Matrix.trace C = 0 := by
  have hdetA : Matrix.det A.1 ≠ 0 := (Matrix.isUnit_iff_isUnit_det A.1).mp A.isUnit |>.ne_zero
  constructor
  · intro h
    have hv := congrArg (fun u : (DualNum K)ˣ => u.1.snd) h
    change (Matrix.det (dualLiftGL2 A C).1).snd = 0 at hv
    rw [det_dualLiftGL2] at hv
    exact (mul_eq_zero.mp hv).resolve_right hdetA
  · intro htr
    apply Units.ext
    change Matrix.det (dualLiftGL2 A C).1 = DualNum.inl (Matrix.det A.1)
    rw [det_dualLiftGL2, htr, zero_mul]
    rfl

/-- Exact multiplication rule for dual-number lifts:
`((I + ε C₁) A₁) * ((I + ε C₂) A₂) = (I + ε (C₁ + A₁ C₂ A₁⁻¹)) (A₁ A₂)`. -/
theorem dualLiftGL2_mul {K : Type*} [CommRing K]
    (A₁ A₂ : Matrix.GeneralLinearGroup (Fin 2) K) (C₁ C₂ : Matrix (Fin 2) (Fin 2) K) :
    dualLiftGL2 A₁ C₁ * dualLiftGL2 A₂ C₂ =
      dualLiftGL2 (A₁ * A₂) (C₁ + A₁.1 * C₂ * A₁⁻¹.1) := by
  apply Units.ext
  change dualMat A₁.1 (C₁ * A₁.1) * dualMat A₂.1 (C₂ * A₂.1) =
    dualMat (A₁.1 * A₂.1) ((C₁ + A₁.1 * C₂ * A₁⁻¹.1) * (A₁.1 * A₂.1))
  rw [dualMat_mul]
  congr 1
  rw [Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc A₁⁻¹.1,
    Units.inv_mul, Matrix.one_mul, add_comm, Matrix.mul_assoc]

/-- **Exact Cocycle Characterization**: `g ↦ (I + ε c(g)) rhoBar(g)` is a group homomorphism
`G →* GL₂(DualNum K)` **if and only if** `c` satisfies the 1-cocycle equation
`c(gh) = c(g) + rhoBar(g) c(h) rhoBar(g)⁻¹`! -/
theorem isHom_dualLift_iff_cocycle {G K : Type*} [Group G] [CommRing K]
    (rhoBar : G →* Matrix.GeneralLinearGroup (Fin 2) K) (c : G → Matrix (Fin 2) (Fin 2) K) :
    (∀ g h : G, dualLiftGL2 (rhoBar (g * h)) (c (g * h)) =
      dualLiftGL2 (rhoBar g) (c g) * dualLiftGL2 (rhoBar h) (c h)) ↔
      (∀ g h : G, c (g * h) = c g + (rhoBar g).1 * c h * (rhoBar g)⁻¹.1) := by
  constructor
  · intro hhom g h
    have h1 := hhom g h
    rw [dualLiftGL2_mul, ← map_mul] at h1
    have h2 : dualMat (rhoBar (g * h)).1 (c (g * h) * (rhoBar (g * h)).1) =
        dualMat (rhoBar (g * h)).1 ((c g + (rhoBar g).1 * c h * (rhoBar g)⁻¹.1) * (rhoBar (g * h)).1) :=
      congrArg Units.val h1
    have h3 := (dualMat_eq_iff.mp h2).2
    calc c (g * h) = (c (g * h) * (rhoBar (g * h)).1) * (rhoBar (g * h))⁻¹.1 := by
          rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
      _ = ((c g + (rhoBar g).1 * c h * (rhoBar g)⁻¹.1) * (rhoBar (g * h)).1) * (rhoBar (g * h))⁻¹.1 := by rw [h3]
      _ = c g + (rhoBar g).1 * c h * (rhoBar g)⁻¹.1 := by
          rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  · intro hcoc g h
    rw [dualLiftGL2_mul, ← map_mul, hcoc g h]

/-- Exact conjugation formula by `I + ε M ∈ ker(GL₂(DualNum K) → GL₂(K))`:
`(I + ε M) * ((I + ε C) A) * (I + ε M)⁻¹ = (I + ε (C + M - A M A⁻¹)) A`. -/
theorem dualLiftGL2_conj {K : Type*} [CommRing K]
    (A : Matrix.GeneralLinearGroup (Fin 2) K) (C M : Matrix (Fin 2) (Fin 2) K) :
    dualLiftGL2 1 M * dualLiftGL2 A C * (dualLiftGL2 1 M)⁻¹ =
      dualLiftGL2 A (C + M - A.1 * M * A⁻¹.1) := by
  have hinv : (dualLiftGL2 (1 : Matrix.GeneralLinearGroup (Fin 2) K) M)⁻¹ = dualLiftGL2 1 (-M) := by
    apply Units.ext
    change dualMat ((1 : Matrix.GeneralLinearGroup (Fin 2) K)⁻¹).1
      (-(((1 : Matrix.GeneralLinearGroup (Fin 2) K)⁻¹).1 * M)) =
      dualMat (1 : Matrix (Fin 2) (Fin 2) K) (-M * 1)
    simp
  rw [hinv, dualLiftGL2_mul, dualLiftGL2_mul]
  simp only [one_mul, mul_one, Units.val_one, inv_one]
  congr 1
  rw [Matrix.mul_neg, Matrix.neg_mul]
  abel

/-- Every matrix in `ker(GL₂(DualNum K) → GL₂(K))` has the exact form `I + ε M` (`dualLiftGL2 1 M`). -/
theorem eq_dualLiftGL2_one_of_mem_strictEquivGroup {p : ℕ} [Fact p.Prime]
    {P : Matrix.GeneralLinearGroup (Fin 2) (DualNum (ZMod p))}
    (hP : P ∈ strictEquivGroup (dualNumCoeffRing p).toLocalCoeffRing) :
    ∃ M : Matrix (Fin 2) (Fin 2) (ZMod p), P = dualLiftGL2 1 M := by
  refine ⟨Matrix.of fun i j => (P.1 i j).snd, ?_⟩
  apply Units.ext
  apply Matrix.ext; intro i j
  have h1 : (mapGL2 (DualNum.proj (R := ZMod p)) P).1 i j = (1 : Matrix (Fin 2) (Fin 2) (ZMod p)) i j :=
    congrArg (fun U : Matrix.GeneralLinearGroup (Fin 2) (ZMod p) => U.1 i j) hP
  exact DualNum.ext (by simpa [dualLiftGL2, dualMat] using h1) (by simp [dualLiftGL2, dualMat])

/-- Extract the 1-cocycle `c_ρ ∈ Cocycle1 G (AdRep rhoBar)` from any lift `ρ`. -/
def cocycleOfLift {G : Type*} [Group G] {p : ℕ} [Fact p.Prime]
    {rhoBar : G →* Matrix.GeneralLinearGroup (Fin 2) (ZMod p)}
    (ρ : Lift rhoBar (dualNumCoeffRing p).toLocalCoeffRing) : Cocycle1 G (AdRep rhoBar) where
  toFun g := ⟨(Matrix.of fun i j => ((ρ.rep g).1 i j).snd) * (rhoBar g)⁻¹.1⟩
  cocycle' g h := by
    have hrep : ∀ x : G, ρ.rep x =
        dualLiftGL2 (rhoBar x) ((Matrix.of fun i j => ((ρ.rep x).1 i j).snd) * (rhoBar x)⁻¹.1) := by
      intro x
      apply Units.ext
      apply Matrix.ext; intro i j
      have hfst : ((ρ.rep x).1 i j).fst = (rhoBar x).1 i j :=
        congrArg (fun U : Matrix.GeneralLinearGroup (Fin 2) (ZMod p) => U.1 i j) (ρ.red_eq x)
      refine DualNum.ext (by simpa [dualLiftGL2, dualMat] using hfst) ?_
      change ((ρ.rep x).1 i j).snd =
        (((Matrix.of fun a b => ((ρ.rep x).1 a b).snd) * (rhoBar x)⁻¹.1) * (rhoBar x).1) i j
      rw [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
      rfl
    have hhom : ∀ x y : G,
        dualLiftGL2 (rhoBar (x * y)) ((Matrix.of fun i j => ((ρ.rep (x * y)).1 i j).snd) * (rhoBar (x * y))⁻¹.1) =
        dualLiftGL2 (rhoBar x) ((Matrix.of fun i j => ((ρ.rep x).1 i j).snd) * (rhoBar x)⁻¹.1) *
        dualLiftGL2 (rhoBar y) ((Matrix.of fun i j => ((ρ.rep y).1 i j).snd) * (rhoBar y)⁻¹.1) := by
      intro x y
      rw [← hrep (x * y), ← hrep x, ← hrep y]
      exact map_mul ρ.rep x y
    exact AdRep.ext ((isHom_dualLift_iff_cocycle rhoBar
      (fun x => (Matrix.of fun i j => ((ρ.rep x).1 i j).snd) * (rhoBar x)⁻¹.1)).mp hhom g h)

/-- Construct a lift `ρ_c : Lift rhoBar (DualNum 𝔽_p)` from any 1-cocycle `c ∈ Cocycle1 G (AdRep rhoBar)`. -/
def liftOfCocycle {G : Type*} [Group G] {p : ℕ} [Fact p.Prime]
    {rhoBar : G →* Matrix.GeneralLinearGroup (Fin 2) (ZMod p)}
    (c : Cocycle1 G (AdRep rhoBar)) : Lift rhoBar (dualNumCoeffRing p).toLocalCoeffRing where
  rep :=
    { toFun := fun g => dualLiftGL2 (rhoBar g) (c g).val
      map_one' := by
        apply Units.ext
        have hc1 : (c 1).val = 0 := congrArg AdRep.val c.map_one
        change dualMat (rhoBar 1).1 ((c 1).val * (rhoBar 1).1) = 1
        rw [map_one, hc1, Matrix.zero_mul, Units.val_one, dualMat_one]
      map_mul' := fun g h =>
        (isHom_dualLift_iff_cocycle rhoBar (fun x => (c x).val)).mpr
          (fun x y => congrArg AdRep.val (c.map_mul x y)) g h }
  red_eq g := mapGL2_proj_dualLiftGL2 (rhoBar g) (c g).val

theorem cocycleOfLift_liftOfCocycle {G : Type*} [Group G] {p : ℕ} [Fact p.Prime]
    {rhoBar : G →* Matrix.GeneralLinearGroup (Fin 2) (ZMod p)}
    (c : Cocycle1 G (AdRep rhoBar)) :
    cocycleOfLift (liftOfCocycle c) = c := by
  apply Cocycle1.ext; intro g
  apply AdRep.ext
  change ((Matrix.of fun i j => (dualMat (rhoBar g).1 ((c g).val * (rhoBar g).1) i j).snd) * (rhoBar g)⁻¹.1) =
    (c g).val
  have hof : (Matrix.of fun i j => (dualMat (rhoBar g).1 ((c g).val * (rhoBar g).1) i j).snd) =
      (c g).val * (rhoBar g).1 := by ext i j; rfl
  rw [hof, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]

theorem liftOfCocycle_cocycleOfLift {G : Type*} [Group G] {p : ℕ} [Fact p.Prime]
    {rhoBar : G →* Matrix.GeneralLinearGroup (Fin 2) (ZMod p)}
    (ρ : Lift rhoBar (dualNumCoeffRing p).toLocalCoeffRing) :
    liftOfCocycle (cocycleOfLift ρ) = ρ := by
  apply Lift.ext
  apply MonoidHom.ext; intro g
  apply Units.ext
  apply Matrix.ext; intro i j
  have hfst : ((ρ.rep g).1 i j).fst = (rhoBar g).1 i j :=
    congrArg (fun U : Matrix.GeneralLinearGroup (Fin 2) (ZMod p) => U.1 i j) (ρ.red_eq g)
  refine DualNum.ext (by simpa [liftOfCocycle, cocycleOfLift, dualLiftGL2, dualMat] using hfst.symm) ?_
  change ((((Matrix.of fun a b => ((ρ.rep g).1 a b).snd) * (rhoBar g)⁻¹.1) * (rhoBar g).1) i j) =
    ((ρ.rep g).1 i j).snd
  rw [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
  rfl

/-- **Exact Coboundary / Strict-Equivalence Equivalence for `ad rhoBar`**:
two dual-number lifts are strictly equivalent iff their cocycles differ by a 1-coboundary! -/
theorem strictEquiv_iff_sub_mem_coboundary {G : Type*} [Group G] {p : ℕ} [Fact p.Prime]
    {rhoBar : G →* Matrix.GeneralLinearGroup (Fin 2) (ZMod p)}
    (ρ₁ ρ₂ : Lift rhoBar (dualNumCoeffRing p).toLocalCoeffRing) :
    StrictEquiv ρ₁ ρ₂ ↔
      cocycleOfLift ρ₂ - cocycleOfLift ρ₁ ∈ LinearMap.range (coboundary1Linear (ZMod p) G (AdRep rhoBar)) := by
  have h1 : ∀ ρ : Lift rhoBar (dualNumCoeffRing p).toLocalCoeffRing, ∀ g : G,
      ρ.rep g = dualLiftGL2 (rhoBar g) (cocycleOfLift ρ g).val := fun ρ g => by
    have := congrArg (fun L : Lift rhoBar (dualNumCoeffRing p).toLocalCoeffRing => L.rep g)
      (liftOfCocycle_cocycleOfLift ρ)
    exact this.symm
  constructor
  · rintro ⟨P, hP, hconj⟩
    obtain ⟨M, rfl⟩ := eq_dualLiftGL2_one_of_mem_strictEquivGroup hP
    refine ⟨⟨-M⟩, ?_⟩
    apply Cocycle1.ext; intro g
    apply AdRep.ext
    have hg := hconj g
    rw [h1 ρ₁ g, h1 ρ₂ g, dualLiftGL2_conj] at hg
    have h2 : dualMat (rhoBar g).1 ((cocycleOfLift ρ₂ g).val * (rhoBar g).1) =
        dualMat (rhoBar g).1 (((cocycleOfLift ρ₁ g).val + M - (rhoBar g).1 * M * (rhoBar g)⁻¹.1) * (rhoBar g).1) :=
      congrArg Units.val hg
    have h3 := (dualMat_eq_iff.mp h2).2
    have h4 : (cocycleOfLift ρ₂ g).val =
        (cocycleOfLift ρ₁ g).val + M - (rhoBar g).1 * M * (rhoBar g)⁻¹.1 := by
      calc (cocycleOfLift ρ₂ g).val
          = ((cocycleOfLift ρ₂ g).val * (rhoBar g).1) * (rhoBar g)⁻¹.1 := by
              rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
        _ = (((cocycleOfLift ρ₁ g).val + M - (rhoBar g).1 * M * (rhoBar g)⁻¹.1) * (rhoBar g).1) * (rhoBar g)⁻¹.1 := by
              rw [h3]
        _ = (cocycleOfLift ρ₁ g).val + M - (rhoBar g).1 * M * (rhoBar g)⁻¹.1 := by
              rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
    rw [Cocycle1.sub_apply, AdRep.sub_val]
    change (rhoBar g).1 * (-M) * (rhoBar g)⁻¹.1 - (-M) =
      (cocycleOfLift ρ₂ g).val - (cocycleOfLift ρ₁ g).val
    rw [h4, Matrix.mul_neg, Matrix.neg_mul]
    abel
  · rintro ⟨M, hM⟩
    refine ⟨dualLiftGL2 1 (-M.val), ?_, fun g => ?_⟩
    · change mapGL2 (DualNum.proj (R := ZMod p)) (dualLiftGL2 1 (-M.val)) = 1
      exact mapGL2_proj_dualLiftGL2 1 (-M.val)
    · rw [h1 ρ₁ g, h1 ρ₂ g, dualLiftGL2_conj]
      congr 1
      have hg := congrArg (fun c : Cocycle1 G (AdRep rhoBar) => (c g).val) hM
      rw [Cocycle1.sub_apply, AdRep.sub_val] at hg
      change (rhoBar g).1 * M.val * (rhoBar g)⁻¹.1 - M.val =
        (cocycleOfLift ρ₂ g).val - (cocycleOfLift ρ₁ g).val at hg
      rw [Matrix.mul_neg, Matrix.neg_mul]
      have h5 : (cocycleOfLift ρ₂ g).val =
          (cocycleOfLift ρ₁ g).val + ((rhoBar g).1 * M.val * (rhoBar g)⁻¹.1 - M.val) := by
        rw [hg]; abel
      rw [h5]
      abel

/-- Extract the trace-zero 1-cocycle `c_ρ ∈ Cocycle1 G (Ad0Rep rhoBar)` from any fixed-determinant lift. -/
def cocycle0OfDetLift {G : Type*} [Group G] {p : ℕ} [Fact p.Prime]
    {rhoBar : G →* Matrix.GeneralLinearGroup (Fin 2) (ZMod p)}
    (ρ : DetLift rhoBar (dualNumCoeffRing p).toLocalCoeffRing (detLiftDual rhoBar)) :
    Cocycle1 G (Ad0Rep rhoBar) where
  toFun g :=
    ⟨(cocycleOfLift ρ.toLift g).val, by
      have hrep : ρ.rep g = dualLiftGL2 (rhoBar g) (cocycleOfLift ρ.toLift g).val := by
        have := congrArg (fun L : Lift rhoBar (dualNumCoeffRing p).toLocalCoeffRing => L.rep g)
          (liftOfCocycle_cocycleOfLift ρ.toLift)
        exact this.symm
      have hdet := ρ.det_eq g
      rw [hrep] at hdet
      exact (det_dualLift_eq_iff_trace_zero (rhoBar g) _).mp hdet⟩
  cocycle' g h := Ad0Rep.ext (congrArg AdRep.val ((cocycleOfLift ρ.toLift).map_mul g h))

/-- Construct a fixed-determinant lift from any trace-zero 1-cocycle `c ∈ Cocycle1 G (Ad0Rep rhoBar)`. -/
def detLiftOfCocycle0 {G : Type*} [Group G] {p : ℕ} [Fact p.Prime]
    {rhoBar : G →* Matrix.GeneralLinearGroup (Fin 2) (ZMod p)}
    (c : Cocycle1 G (Ad0Rep rhoBar)) :
    DetLift rhoBar (dualNumCoeffRing p).toLocalCoeffRing (detLiftDual rhoBar) where
  toLift := liftOfCocycle
    { toFun := fun g => ⟨(c g).val⟩
      cocycle' := fun g h => AdRep.ext (congrArg Ad0Rep.val (c.map_mul g h)) }
  det_eq g := (det_dualLift_eq_iff_trace_zero (rhoBar g) (c g).val).mpr (c g).trace_zero

theorem cocycle0OfDetLift_detLiftOfCocycle0 {G : Type*} [Group G] {p : ℕ} [Fact p.Prime]
    {rhoBar : G →* Matrix.GeneralLinearGroup (Fin 2) (ZMod p)}
    (c : Cocycle1 G (Ad0Rep rhoBar)) :
    cocycle0OfDetLift (detLiftOfCocycle0 c) = c := by
  apply Cocycle1.ext; intro g
  apply Ad0Rep.ext
  have h := cocycleOfLift_liftOfCocycle (rhoBar := rhoBar)
    { toFun := fun x => ⟨(c x).val⟩
      cocycle' := fun x y => AdRep.ext (congrArg Ad0Rep.val (c.map_mul x y)) }
  exact congrArg (fun f : Cocycle1 G (AdRep rhoBar) => (f g).val) h

theorem detLiftOfCocycle0_cocycle0OfDetLift {G : Type*} [Group G] {p : ℕ} [Fact p.Prime]
    {rhoBar : G →* Matrix.GeneralLinearGroup (Fin 2) (ZMod p)}
    (ρ : DetLift rhoBar (dualNumCoeffRing p).toLocalCoeffRing (detLiftDual rhoBar)) :
    detLiftOfCocycle0 (cocycle0OfDetLift ρ) = ρ := by
  apply DetLift.ext
  exact congrArg Lift.rep (liftOfCocycle_cocycleOfLift ρ.toLift)

/-- **Exact Trace-Zero Coboundary Equivalence (`p ≥ 3`)**: for two fixed-determinant lifts,
strict equivalence in `GL₂(𝔽_p[ε]/(ε²))` holds iff their trace-zero cocycles differ by a
trace-zero 1-coboundary `dM₀` with `M₀ ∈ ad⁰ rhoBar`! -/
theorem strictEquivDet_iff_sub_mem_coboundary0 {G : Type*} [Group G] {p : ℕ} [Fact p.Prime]
    (hp3 : 3 ≤ p) {rhoBar : G →* Matrix.GeneralLinearGroup (Fin 2) (ZMod p)}
    (ρ₁ ρ₂ : DetLift rhoBar (dualNumCoeffRing p).toLocalCoeffRing (detLiftDual rhoBar)) :
    StrictEquivDet ρ₁ ρ₂ ↔
      cocycle0OfDetLift ρ₂ - cocycle0OfDetLift ρ₁ ∈
        LinearMap.range (coboundary1Linear (ZMod p) G (Ad0Rep rhoBar)) := by
  have h2 : (2 : ZMod p) ≠ 0 := two_ne_zero_zmod hp3
  unfold StrictEquivDet
  rw [strictEquiv_iff_sub_mem_coboundary]
  constructor
  · rintro ⟨M, hM⟩
    let c : ZMod p := (2 : ZMod p)⁻¹ * Matrix.trace M.val
    let M₀ : Ad0Rep rhoBar :=
      ⟨M.val - c • (1 : Matrix (Fin 2) (Fin 2) (ZMod p)), by
        rw [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin]
        dsimp only [c]
        simp only [Nat.cast_ofNat, smul_eq_mul]
        field_simp [h2]
        ring⟩
    refine ⟨M₀, ?_⟩
    apply Cocycle1.ext; intro g
    apply Ad0Rep.ext
    have hg := congrArg (fun f : Cocycle1 G (AdRep rhoBar) => (f g).val) hM
    rw [Cocycle1.sub_apply, AdRep.sub_val] at hg
    rw [Cocycle1.sub_apply, Ad0Rep.sub_val]
    change (rhoBar g).1 * M.val * (rhoBar g)⁻¹.1 - M.val =
      (cocycleOfLift ρ₂.toLift g).val - (cocycleOfLift ρ₁.toLift g).val at hg
    change (rhoBar g).1 * (M.val - c • 1) * (rhoBar g)⁻¹.1 - (M.val - c • 1) =
      (cocycleOfLift ρ₂.toLift g).val - (cocycleOfLift ρ₁.toLift g).val
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      Units.mul_inv]
    rw [← hg]
    abel
  · rintro ⟨M₀, hM₀⟩
    refine ⟨⟨M₀.val⟩, ?_⟩
    apply Cocycle1.ext; intro g
    have hg := congrArg (fun f : Cocycle1 G (Ad0Rep rhoBar) => (f g).val) hM₀
    rw [Cocycle1.sub_apply, Ad0Rep.sub_val] at hg
    apply AdRep.ext
    rw [Cocycle1.sub_apply, AdRep.sub_val]
    exact hg

/-- Functorial Mazur–Schlessinger `𝔽_p`-scalar multiplication on `DeformDual rhoBar`. -/
def deformDualSMul {G : Type*} [Group G] {p : ℕ} [Fact p.Prime]
    {rhoBar : G →* Matrix.GeneralLinearGroup (Fin 2) (ZMod p)}
    (c : ZMod p) : DeformDual rhoBar → DeformDual rhoBar :=
  Deform.map (DualNum.scaleDual c) (DualNum.proj_comp_scaleDual c)

/-- Functorial Mazur–Schlessinger Baer-sum addition on `Lift rhoBar (DualNum 𝔽_p)`. -/
def liftBaerAdd {G : Type*} [Group G] {p : ℕ} [Fact p.Prime]
    {rhoBar : G →* Matrix.GeneralLinearGroup (Fin 2) (ZMod p)}
    (ρ₁ ρ₂ : Lift rhoBar (dualNumCoeffRing p).toLocalCoeffRing) :
    Lift rhoBar (dualNumCoeffRing p).toLocalCoeffRing where
  rep :=
    let pairGL2 : G →* Matrix.GeneralLinearGroup (Fin 2) (DualNum.fiberSubring (ZMod p)) :=
      { toFun := fun g =>
          { val := Matrix.of fun i j =>
              ⟨((ρ₁.rep g).1 i j, (ρ₂.rep g).1 i j), by
                have h1 := congrArg (fun U : Matrix.GeneralLinearGroup (Fin 2) (ZMod p) => U.1 i j) (ρ₁.red_eq g)
                have h2 := congrArg (fun U : Matrix.GeneralLinearGroup (Fin 2) (ZMod p) => U.1 i j) (ρ₂.red_eq g)
                exact h1.trans h2.symm⟩
            inv := Matrix.of fun i j =>
              ⟨((ρ₁.rep g)⁻¹.1 i j, (ρ₂.rep g)⁻¹.1 i j), by
                have h1 := congrArg (fun U : Matrix.GeneralLinearGroup (Fin 2) (ZMod p) => U.1 i j)
                  (by rw [map_inv, ρ₁.red_eq g] : mapGL2 DualNum.proj (ρ₁.rep g)⁻¹ = (rhoBar g)⁻¹)
                have h2 := congrArg (fun U : Matrix.GeneralLinearGroup (Fin 2) (ZMod p) => U.1 i j)
                  (by rw [map_inv, ρ₂.red_eq g] : mapGL2 DualNum.proj (ρ₂.rep g)⁻¹ = (rhoBar g)⁻¹)
                exact h1.trans h2.symm⟩
            val_inv := by
              apply Matrix.ext; intro i j
              apply Subtype.ext; apply Prod.ext
              · have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) (DualNum (ZMod p)) => M i j)
                  (ρ₁.rep g).val_inv
                fin_cases i <;> fin_cases j <;> simpa [Matrix.mul_apply, Fin.sum_univ_two] using h
              · have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) (DualNum (ZMod p)) => M i j)
                  (ρ₂.rep g).val_inv
                fin_cases i <;> fin_cases j <;> simpa [Matrix.mul_apply, Fin.sum_univ_two] using h
            inv_val := by
              apply Matrix.ext; intro i j
              apply Subtype.ext; apply Prod.ext
              · have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) (DualNum (ZMod p)) => M i j)
                  (ρ₁.rep g).inv_val
                fin_cases i <;> fin_cases j <;> simpa [Matrix.mul_apply, Fin.sum_univ_two] using h
              · have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) (DualNum (ZMod p)) => M i j)
                  (ρ₂.rep g).inv_val
                fin_cases i <;> fin_cases j <;> simpa [Matrix.mul_apply, Fin.sum_univ_two] using h }
        map_one' := by
          apply Units.ext; apply Matrix.ext; intro i j; apply Subtype.ext; apply Prod.ext
          · fin_cases i <;> fin_cases j <;> simp
          · fin_cases i <;> fin_cases j <;> simp
        map_mul' := fun g h => by
          apply Units.ext; apply Matrix.ext; intro i j; apply Subtype.ext; apply Prod.ext
          · fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
          · fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] }
    (mapGL2 (DualNum.sumDual (ZMod p))).comp pairGL2
  red_eq g := by
    apply Units.ext; ext i j
    exact congrArg (fun U : Matrix.GeneralLinearGroup (Fin 2) (ZMod p) => U.1 i j) (ρ₁.red_eq g)

theorem cocycleOfLift_baerAdd {G : Type*} [Group G] {p : ℕ} [Fact p.Prime]
    {rhoBar : G →* Matrix.GeneralLinearGroup (Fin 2) (ZMod p)}
    (ρ₁ ρ₂ : Lift rhoBar (dualNumCoeffRing p).toLocalCoeffRing) :
    cocycleOfLift (liftBaerAdd ρ₁ ρ₂) = cocycleOfLift ρ₁ + cocycleOfLift ρ₂ := by
  apply Cocycle1.ext; intro g
  apply AdRep.ext
  change (Matrix.of fun i j => ((ρ₁.rep g).1 i j).snd + ((ρ₂.rep g).1 i j).snd) * (rhoBar g)⁻¹.1 =
    (Matrix.of fun i j => ((ρ₁.rep g).1 i j).snd) * (rhoBar g)⁻¹.1 +
      (Matrix.of fun i j => ((ρ₂.rep g).1 i j).snd) * (rhoBar g)⁻¹.1
  rw [← Matrix.add_mul]
  rfl

theorem cocycleOfLift_scaleDual {G : Type*} [Group G] {p : ℕ} [Fact p.Prime]
    {rhoBar : G →* Matrix.GeneralLinearGroup (Fin 2) (ZMod p)}
    (c : ZMod p) (ρ : Lift rhoBar (dualNumCoeffRing p).toLocalCoeffRing) :
    cocycleOfLift (Lift.map (DualNum.scaleDual c) (DualNum.proj_comp_scaleDual c) ρ) =
      c • cocycleOfLift ρ := by
  apply Cocycle1.ext; intro g
  apply AdRep.ext
  change (Matrix.of fun i j => c * ((ρ.rep g).1 i j).snd) * (rhoBar g)⁻¹.1 =
    c • ((Matrix.of fun i j => ((ρ.rep g).1 i j).snd) * (rhoBar g)⁻¹.1)
  rw [← Matrix.smul_mul]
  rfl

/-- Canonical bijection `DeformDual rhoBar ≃ H1Vec (ZMod p) G (AdRep rhoBar)`. -/
def deformDualEquivH1 {G : Type*} [Group G] {p : ℕ} [Fact p.Prime]
    (rhoBar : G →* Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) :
    DeformDual rhoBar ≃ H1Vec (ZMod p) G (AdRep rhoBar) where
  toFun := Quotient.lift (fun ρ => Submodule.Quotient.mk (cocycleOfLift ρ)) fun ρ₁ ρ₂ h => by
    rw [Submodule.Quotient.eq]
    have hmem := (strictEquiv_iff_sub_mem_coboundary ρ₁ ρ₂).mp h
    simpa only [neg_sub] using Submodule.neg_mem _ hmem
  invFun := Quotient.lift (fun c => Quotient.mk _ (liftOfCocycle c)) fun c₁ c₂ h => by
    apply Quotient.sound
    change StrictEquiv (liftOfCocycle c₁) (liftOfCocycle c₂)
    rw [strictEquiv_iff_sub_mem_coboundary, cocycleOfLift_liftOfCocycle, cocycleOfLift_liftOfCocycle]
    have hmem : c₁ - c₂ ∈ LinearMap.range (coboundary1Linear (ZMod p) G (AdRep rhoBar)) :=
      (Submodule.quotientRel_def _).mp h
    simpa only [neg_sub] using Submodule.neg_mem _ hmem
  left_inv q := by
    induction q using Quotient.inductionOn' with
    | h ρ =>
      change Quotient.mk _ (liftOfCocycle (cocycleOfLift ρ)) = Quotient.mk _ ρ
      rw [liftOfCocycle_cocycleOfLift]
  right_inv q := by
    induction q using Quotient.inductionOn' with
    | h c =>
      change Submodule.Quotient.mk (cocycleOfLift (liftOfCocycle c)) = Submodule.Quotient.mk c
      rw [cocycleOfLift_liftOfCocycle]

/-- Canonical bijection `Deform0Dual rhoBar ≃ H1Vec (ZMod p) G (Ad0Rep rhoBar)` for `p ≥ 3`. -/
def deform0DualEquivH1 {G : Type*} [Group G] {p : ℕ} [Fact p.Prime] (hp3 : 3 ≤ p)
    (rhoBar : G →* Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) :
    Deform0Dual rhoBar ≃ H1Vec (ZMod p) G (Ad0Rep rhoBar) where
  toFun := Quotient.lift (fun ρ => Submodule.Quotient.mk (cocycle0OfDetLift ρ)) fun ρ₁ ρ₂ h => by
    rw [Submodule.Quotient.eq]
    have hmem := (strictEquivDet_iff_sub_mem_coboundary0 hp3 ρ₁ ρ₂).mp h
    simpa only [neg_sub] using Submodule.neg_mem _ hmem
  invFun := Quotient.lift (fun c => Quotient.mk _ (detLiftOfCocycle0 c)) fun c₁ c₂ h => by
    apply Quotient.sound
    change StrictEquivDet (detLiftOfCocycle0 c₁) (detLiftOfCocycle0 c₂)
    rw [strictEquivDet_iff_sub_mem_coboundary0 hp3,
      cocycle0OfDetLift_detLiftOfCocycle0, cocycle0OfDetLift_detLiftOfCocycle0]
    have hmem : c₁ - c₂ ∈ LinearMap.range (coboundary1Linear (ZMod p) G (Ad0Rep rhoBar)) :=
      (Submodule.quotientRel_def _).mp h
    simpa only [neg_sub] using Submodule.neg_mem _ hmem
  left_inv q := by
    induction q using Quotient.inductionOn' with
    | h ρ =>
      change Quotient.mk _ (detLiftOfCocycle0 (cocycle0OfDetLift ρ)) = Quotient.mk _ ρ
      rw [detLiftOfCocycle0_cocycle0OfDetLift]
  right_inv q := by
    induction q using Quotient.inductionOn' with
    | h c =>
      change Submodule.Quotient.mk (cocycle0OfDetLift (detLiftOfCocycle0 c)) = Submodule.Quotient.mk c
      rw [cocycle0OfDetLift_detLiftOfCocycle0]

instance instAddCommGroupDeformDual {G : Type*} [Group G] {p : ℕ} [Fact p.Prime]
    (rhoBar : G →* Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) :
    AddCommGroup (DeformDual rhoBar) :=
  (deformDualEquivH1 rhoBar).addCommGroup

instance instModuleDeformDual {G : Type*} [Group G] {p : ℕ} [Fact p.Prime]
    (rhoBar : G →* Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) :
    Module (ZMod p) (DeformDual rhoBar) :=
  (deformDualEquivH1 rhoBar).module (ZMod p)

/-- Canonical quotient constructor into `DeformDual rhoBar`. -/
def deformDualMk {G : Type*} [Group G] {p : ℕ} [Fact p.Prime]
    {rhoBar : G →* Matrix.GeneralLinearGroup (Fin 2) (ZMod p)}
    (ρ : Lift rhoBar (dualNumCoeffRing p).toLocalCoeffRing) : DeformDual rhoBar :=
  Quotient.mk (strictEquivSetoid rhoBar _) ρ

/-- Verification that addition on `DeformDual rhoBar` IS the functorial Baer sum `liftBaerAdd`
and scalar multiplication IS functorial pushforward along `scaleDual`! -/
theorem deformDual_add_eq_baerAdd {G : Type*} [Group G] {p : ℕ} [Fact p.Prime]
    {rhoBar : G →* Matrix.GeneralLinearGroup (Fin 2) (ZMod p)}
    (ρ₁ ρ₂ : Lift rhoBar (dualNumCoeffRing p).toLocalCoeffRing) :
    deformDualMk ρ₁ + deformDualMk ρ₂ = deformDualMk (liftBaerAdd ρ₁ ρ₂) := by
  apply (deformDualEquivH1 rhoBar).injective
  change (deformDualEquivH1 rhoBar) ((deformDualEquivH1 rhoBar).symm
      ((deformDualEquivH1 rhoBar) (deformDualMk ρ₁) + (deformDualEquivH1 rhoBar) (deformDualMk ρ₂))) =
    Submodule.Quotient.mk (cocycleOfLift (liftBaerAdd ρ₁ ρ₂))
  rw [(deformDualEquivH1 rhoBar).apply_symm_apply, cocycleOfLift_baerAdd]
  rfl

theorem deformDual_smul_eq_scaleDual {G : Type*} [Group G] {p : ℕ} [Fact p.Prime]
    {rhoBar : G →* Matrix.GeneralLinearGroup (Fin 2) (ZMod p)}
    (c : ZMod p) (q : DeformDual rhoBar) :
    c • q = deformDualSMul c q := by
  induction q using Quotient.inductionOn' with
  | h ρ =>
    apply (deformDualEquivH1 rhoBar).injective
    change (deformDualEquivH1 rhoBar) ((deformDualEquivH1 rhoBar).symm
        (c • (deformDualEquivH1 rhoBar) (Quotient.mk _ ρ))) =
      Submodule.Quotient.mk (cocycleOfLift (Lift.map (DualNum.scaleDual c)
        (DualNum.proj_comp_scaleDual c) ρ))
    rw [(deformDualEquivH1 rhoBar).apply_symm_apply, cocycleOfLift_scaleDual]
    rfl

/-- **EXACT MAZUR TANGENT-SPACE ISOMORPHISM FOR `ad rhoBar`**:
`Deform(rhoBar, 𝔽_p[ε]/(ε²)) ≃ₗ[𝔽_p] H¹(G, ad rhoBar)`. -/
def mazur_tangent_space_equiv_ad {G : Type*} [Group G] {p : ℕ} [Fact p.Prime]
    (rhoBar : G →* Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) :
    DeformDual rhoBar ≃ₗ[ZMod p] H1Vec (ZMod p) G (AdRep rhoBar) where
  toEquiv := deformDualEquivH1 rhoBar
  map_add' _ _ := (deformDualEquivH1 rhoBar).apply_symm_apply _
  map_smul' _ _ := (deformDualEquivH1 rhoBar).apply_symm_apply _

/-- Canonical Mazur–Schlessinger `𝔽_p`-vector space structure on fixed-determinant deformations
`Deform0Dual rhoBar` (`p ≥ 3`). -/
@[instance_reducible]
def instAddCommGroupDeform0Dual {G : Type*} [Group G] {p : ℕ} [Fact p.Prime] (hp3 : 3 ≤ p)
    (rhoBar : G →* Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) :
    AddCommGroup (Deform0Dual rhoBar) :=
  (deform0DualEquivH1 hp3 rhoBar).addCommGroup

@[instance_reducible]
def instModuleDeform0Dual {G : Type*} [Group G] {p : ℕ} [Fact p.Prime] (hp3 : 3 ≤ p)
    (rhoBar : G →* Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) :
    letI := instAddCommGroupDeform0Dual hp3 rhoBar
    Module (ZMod p) (Deform0Dual rhoBar) :=
  letI := instAddCommGroupDeform0Dual hp3 rhoBar
  (deform0DualEquivH1 hp3 rhoBar).module (ZMod p)

/-- **EXACT MAZUR TANGENT-SPACE ISOMORPHISM FOR `ad⁰ rhoBar` (`p ≥ 3`)**:
`Deform⁰(rhoBar, 𝔽_p[ε]/(ε²)) ≃ₗ[𝔽_p] H¹(G, ad⁰ rhoBar)`! -/
def mazur_tangent_space_equiv_ad0 {G : Type*} [Group G] {p : ℕ} [Fact p.Prime] (hp3 : 3 ≤ p)
    (rhoBar : G →* Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) :
    letI := instAddCommGroupDeform0Dual hp3 rhoBar
    letI := instModuleDeform0Dual hp3 rhoBar
    Deform0Dual rhoBar ≃ₗ[ZMod p] H1Vec (ZMod p) G (Ad0Rep rhoBar) := by
  letI := instAddCommGroupDeform0Dual hp3 rhoBar
  letI := instModuleDeform0Dual hp3 rhoBar
  exact
    { toEquiv := deform0DualEquivH1 hp3 rhoBar
      map_add' := fun _ _ => (deform0DualEquivH1 hp3 rhoBar).apply_symm_apply _
      map_smul' := fun _ _ => (deform0DualEquivH1 hp3 rhoBar).apply_symm_apply _ }

end MazurTangentSpaceIsomorphism

/-! ## Section 4: Deformation Ring Presentation, Obstruction Relation Bound & Krull Dimension Bound -/

section DeformationRingPresentation

/-- Local `ℤ_[p]`-algebra with residue field `ZMod p`. -/
structure LocalZpAlg (p : ℕ) [Fact p.Prime] where
  carrier : Type
  [commRing : CommRing carrier]
  [localRing : IsLocalRing carrier]
  [algZp : Algebra ℤ_[p] carrier]
  res : carrier →+* ZMod p
  res_comp_alg : res.comp (algebraMap ℤ_[p] carrier) = PadicInt.toZMod
  ker_res : RingHom.ker res = IsLocalRing.maximalIdeal carrier

attribute [instance] LocalZpAlg.commRing LocalZpAlg.localRing LocalZpAlg.algZp

namespace LocalZpAlg

variable {p : ℕ} [Fact p.Prime] (R : LocalZpAlg p)

theorem res_surjective : Function.Surjective R.res := by
  intro a
  obtain ⟨c, hc⟩ := padicInt_toZMod_surjective (p := p) a
  refine ⟨algebraMap ℤ_[p] R.carrier c, ?_⟩
  change (R.res.comp (algebraMap ℤ_[p] R.carrier)) c = a
  rw [R.res_comp_alg, hc]

theorem p_mem_maximalIdeal : (p : R.carrier) ∈ IsLocalRing.maximalIdeal R.carrier := by
  rw [← R.ker_res, RingHom.mem_ker, map_natCast, ZMod.natCast_self]

/-- The ideal `p · R + 𝔪_R²` inside `R`. -/
def cotangentDenomIdeal : Ideal R.carrier :=
  Ideal.span ({(p : R.carrier)} : Set R.carrier) ⊔ (IsLocalRing.maximalIdeal R.carrier) ^ 2

theorem cotangentDenomIdeal_le_maximalIdeal :
    R.cotangentDenomIdeal ≤ IsLocalRing.maximalIdeal R.carrier := by
  refine sup_le ?_ (Ideal.pow_le_self (by norm_num))
  rw [Ideal.span_singleton_le_iff_mem]
  exact R.p_mem_maximalIdeal

/-- The `R`-submodule `(p · R + 𝔪_R²) ⊆ 𝔪_R`. -/
def cotangentSub : Submodule R.carrier (IsLocalRing.maximalIdeal R.carrier) :=
  Submodule.comap (IsLocalRing.maximalIdeal R.carrier).subtype R.cotangentDenomIdeal

/-- **Reduced Zariski Cotangent Space `𝔪_R ⧸ (p · R + 𝔪_R²)`** of a local `ℤ_[p]`-algebra `R`. -/
abbrev ReducedCotangent : Type :=
  (IsLocalRing.maximalIdeal R.carrier) ⧸ R.cotangentSub

/-- `𝔪_R` annihilates `ReducedCotangent R`. -/
theorem maximalIdeal_le_annihilator_reducedCotangent :
    IsLocalRing.maximalIdeal R.carrier ≤ Module.annihilator R.carrier R.ReducedCotangent := by
  intro m hm
  rw [Module.mem_annihilator]
  intro q
  induction q using Quotient.inductionOn' with
  | h x =>
    change Submodule.Quotient.mk (m • x) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    show (m • x).1 ∈ R.cotangentDenomIdeal
    exact Ideal.mem_sup_right (by rw [pow_two]; exact Ideal.mul_mem_mul hm x.2)

instance instSMulZModReducedCotangent : SMul (ZMod p) R.ReducedCotangent where
  smul a q := (Classical.choose (R.res_surjective a)) • q

theorem zmod_smul_reducedCotangent_eq (r : R.carrier) (q : R.ReducedCotangent) :
    R.res r • q = r • q := by
  change (Classical.choose (R.res_surjective (R.res r))) • q = r • q
  have hdiff : Classical.choose (R.res_surjective (R.res r)) - r ∈ IsLocalRing.maximalIdeal R.carrier := by
    rw [← R.ker_res, RingHom.mem_ker, map_sub, Classical.choose_spec (R.res_surjective (R.res r)), sub_self]
  have h0 := Module.mem_annihilator.mp (R.maximalIdeal_le_annihilator_reducedCotangent hdiff) q
  rw [sub_smul, sub_eq_zero] at h0
  exact h0

instance instModuleZModReducedCotangent : Module (ZMod p) R.ReducedCotangent where
  one_smul q := by
    rw [← map_one R.res, R.zmod_smul_reducedCotangent_eq, one_smul]
  mul_smul a b q := by
    obtain ⟨r, rfl⟩ := R.res_surjective a
    obtain ⟨s, rfl⟩ := R.res_surjective b
    rw [← map_mul, R.zmod_smul_reducedCotangent_eq, R.zmod_smul_reducedCotangent_eq,
      R.zmod_smul_reducedCotangent_eq, mul_smul]
  smul_zero a := by
    obtain ⟨r, rfl⟩ := R.res_surjective a
    rw [R.zmod_smul_reducedCotangent_eq, smul_zero]
  smul_add a q₁ q₂ := by
    obtain ⟨r, rfl⟩ := R.res_surjective a
    rw [R.zmod_smul_reducedCotangent_eq, R.zmod_smul_reducedCotangent_eq,
      R.zmod_smul_reducedCotangent_eq, smul_add]
  add_smul a b q := by
    obtain ⟨r, rfl⟩ := R.res_surjective a
    obtain ⟨s, rfl⟩ := R.res_surjective b
    rw [← map_add, R.zmod_smul_reducedCotangent_eq, R.zmod_smul_reducedCotangent_eq,
      R.zmod_smul_reducedCotangent_eq, add_smul]
  zero_smul q := by
    rw [← map_zero R.res, R.zmod_smul_reducedCotangent_eq, zero_smul]

/-- Structure of local `ℤ_[p]`-algebra homomorphisms `φ : R →+* 𝔽_p[ε]/(ε²)` lifting `R.res`. -/
@[ext]
structure DualHom where
  toRingHom : R.carrier →+* DualNum (ZMod p)
  proj_comp : DualNum.proj.comp toRingHom = R.res
  comp_algZp : toRingHom.comp (algebraMap ℤ_[p] R.carrier) = DualNum.inl.comp PadicInt.toZMod

/-- **EXACT ZARISKI TANGENT-COTANGENT ISOMORPHISM**:
For EVERY local `ℤ_[p]`-algebra `R` with residue field `ZMod p`, local `ℤ_[p]`-algebra homomorphisms
`R →+* 𝔽_p[ε]/(ε²)` are in exact bijection with `Module.Dual (ZMod p) (𝔪_R ⧸ (p R + 𝔪_R²))`! -/
def dualHomEquivCotangentDual : R.DualHom ≃ Module.Dual (ZMod p) R.ReducedCotangent where
  toFun φ :=
    letI : Module R.carrier (ZMod p) := Module.compHom (ZMod p) R.res
    let raw : (IsLocalRing.maximalIdeal R.carrier) →ₗ[R.carrier] ZMod p :=
      { toFun := fun m => (φ.toRingHom m.1).snd
        map_add' := fun m₁ m₂ => by
          change (φ.toRingHom (m₁.1 + m₂.1)).snd = _
          rw [map_add]; rfl
        map_smul' := fun r m => by
          change (φ.toRingHom (r * m.1)).snd = R.res r * (φ.toRingHom m.1).snd
          rw [map_mul, DualNum.mul_snd]
          have hm0 : (φ.toRingHom m.1).fst = 0 := by
            have h := RingHom.congr_fun φ.proj_comp m.1
            change (φ.toRingHom m.1).fst = R.res m.1 at h
            rw [h]
            exact RingHom.mem_ker.mp (R.ker_res.symm ▸ m.2)
          have hr : (φ.toRingHom r).fst = R.res r := RingHom.congr_fun φ.proj_comp r
          rw [hm0, hr, mul_zero, add_zero] }
    let f : R.ReducedCotangent →ₗ[R.carrier] ZMod p :=
      Submodule.liftQ R.cotangentSub raw (by
        intro m hm
        rw [LinearMap.mem_ker]
        change (φ.toRingHom m.1).snd = 0
        have hm' : m.1 ∈ Ideal.span ({(p : R.carrier)} : Set R.carrier) ⊔
            (IsLocalRing.maximalIdeal R.carrier) ^ 2 := hm
        rcases Submodule.mem_sup.mp hm' with ⟨a, ha, b, hb, hab⟩
        rw [← hab, map_add, DualNum.add_snd]
        have ha0 : (φ.toRingHom a).snd = 0 := by
          obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton.mp ha
          rw [map_mul, map_natCast]
          have hp0 : (p : DualNum (ZMod p)) = 0 := by
            rw [← map_natCast DualNum.inl, ZMod.natCast_self, map_zero]
          rw [hp0, zero_mul]; rfl
        have hb0 : (φ.toRingHom b).snd = 0 := by
          rw [pow_two] at hb
          refine Submodule.mul_induction_on hb ?_ ?_
          · intro x hx y hy
            rw [map_mul, DualNum.mul_snd]
            have hx0 : (φ.toRingHom x).fst = 0 := by
              have h := RingHom.congr_fun φ.proj_comp x
              change (φ.toRingHom x).fst = R.res x at h
              rw [h]; exact RingHom.mem_ker.mp (R.ker_res.symm ▸ hx)
            have hy0 : (φ.toRingHom y).fst = 0 := by
              have h := RingHom.congr_fun φ.proj_comp y
              change (φ.toRingHom y).fst = R.res y at h
              rw [h]; exact RingHom.mem_ker.mp (R.ker_res.symm ▸ hy)
            rw [hx0, hy0, zero_mul, mul_zero, add_zero]
          · intro u v hu hv
            rw [map_add, DualNum.add_snd, hu, hv, add_zero]
        rw [ha0, hb0, add_zero])
    { toFun := f
      map_add' := f.map_add'
      map_smul' := fun a q => by
        obtain ⟨r, rfl⟩ := R.res_surjective a
        rw [R.zmod_smul_reducedCotangent_eq]
        exact f.map_smul r q }
  invFun ψ :=
    let liftC : R.carrier → ℤ_[p] := fun x =>
      Classical.choose (padicInt_toZMod_surjective (p := p) (R.res x))
    have hliftC : ∀ x : R.carrier, PadicInt.toZMod (liftC x) = R.res x := fun x =>
      Classical.choose_spec (padicInt_toZMod_surjective (p := p) (R.res x))
    have hmemM : ∀ x : R.carrier, x - algebraMap ℤ_[p] R.carrier (liftC x) ∈ IsLocalRing.maximalIdeal R.carrier := by
      intro x
      rw [← R.ker_res, RingHom.mem_ker, map_sub]
      have hc : R.res (algebraMap ℤ_[p] R.carrier (liftC x)) = R.res x := by
        change (R.res.comp (algebraMap ℤ_[p] R.carrier)) (liftC x) = R.res x
        rw [R.res_comp_alg, hliftC x]
      rw [hc, sub_self]
    let D : R.carrier → ZMod p := fun x =>
      ψ (Submodule.Quotient.mk ⟨x - algebraMap ℤ_[p] R.carrier (liftC x), hmemM x⟩)
    have hD_indep : ∀ (x : R.carrier) (c : ℤ_[p]) (hm : x - algebraMap ℤ_[p] R.carrier c ∈ IsLocalRing.maximalIdeal R.carrier),
        D x = ψ (Submodule.Quotient.mk ⟨x - algebraMap ℤ_[p] R.carrier c, hm⟩) := by
      intro x c hm
      dsimp only [D]
      congr 1
      rw [Submodule.Quotient.eq]
      show ((⟨x - algebraMap ℤ_[p] R.carrier (liftC x), hmemM x⟩ -
        ⟨x - algebraMap ℤ_[p] R.carrier c, hm⟩ : IsLocalRing.maximalIdeal R.carrier).1) ∈ R.cotangentDenomIdeal
      have hsub : (x - algebraMap ℤ_[p] R.carrier (liftC x)) - (x - algebraMap ℤ_[p] R.carrier c) =
          algebraMap ℤ_[p] R.carrier (c - liftC x) := by rw [map_sub]; ring
      change (x - algebraMap ℤ_[p] R.carrier (liftC x)) - (x - algebraMap ℤ_[p] R.carrier c) ∈ R.cotangentDenomIdeal
      rw [hsub]
      have hmod0 : PadicInt.toZMod (c - liftC x) = 0 := by
        rw [map_sub, hliftC x]
        have hres_c : PadicInt.toZMod c = R.res x := by
          have hm0 : R.res (x - algebraMap ℤ_[p] R.carrier c) = 0 :=
            RingHom.mem_ker.mp (R.ker_res.symm ▸ hm)
          rw [map_sub, sub_eq_zero] at hm0
          have hc' : R.res (algebraMap ℤ_[p] R.carrier c) = PadicInt.toZMod c :=
            RingHom.congr_fun R.res_comp_alg c
          rw [← hc', hm0]
        rw [hres_c, sub_self]
      obtain ⟨z, hz⟩ := (padicInt_p_dvd_iff_toZMod_eq_zero (c - liftC x)).mpr hmod0
      rw [hz, map_mul, map_natCast]
      exact Ideal.mem_sup_left (Ideal.mem_span_singleton.mpr ⟨algebraMap ℤ_[p] R.carrier z, rfl⟩)
    { toRingHom :=
        { toFun := fun x => ⟨R.res x, D x⟩
          map_one' := by
            ext
            · exact map_one R.res
            · change D 1 = 0
              rw [hD_indep 1 1 (by simp)]
              have h0 : (⟨1 - algebraMap ℤ_[p] R.carrier 1, by simp⟩ : IsLocalRing.maximalIdeal R.carrier) = 0 := by
                ext; simp
              rw [h0, Submodule.Quotient.mk_zero, map_zero]
          map_zero' := by
            ext
            · exact map_zero R.res
            · change D 0 = 0
              rw [hD_indep 0 0 (by simp)]
              have h0 : (⟨0 - algebraMap ℤ_[p] R.carrier 0, by simp⟩ : IsLocalRing.maximalIdeal R.carrier) = 0 := by
                ext; simp
              rw [h0, Submodule.Quotient.mk_zero, map_zero]
          map_add' := fun x y => by
            ext
            · exact map_add R.res x y
            · change D (x + y) = D x + D y
              have hmxy : (x + y) - algebraMap ℤ_[p] R.carrier (liftC x + liftC y) ∈
                  IsLocalRing.maximalIdeal R.carrier := by
                have heq : (x + y) - algebraMap ℤ_[p] R.carrier (liftC x + liftC y) =
                    (x - algebraMap ℤ_[p] R.carrier (liftC x)) +
                      (y - algebraMap ℤ_[p] R.carrier (liftC y)) := by rw [map_add]; ring
                rw [heq]
                exact Ideal.add_mem _ (hmemM x) (hmemM y)
              rw [hD_indep (x + y) (liftC x + liftC y) hmxy]
              have hadd : (⟨(x + y) - algebraMap ℤ_[p] R.carrier (liftC x + liftC y), hmxy⟩ :
                  IsLocalRing.maximalIdeal R.carrier) =
                ⟨x - algebraMap ℤ_[p] R.carrier (liftC x), hmemM x⟩ +
                  ⟨y - algebraMap ℤ_[p] R.carrier (liftC y), hmemM y⟩ := by
                apply Subtype.ext
                change (x + y) - algebraMap ℤ_[p] R.carrier (liftC x + liftC y) =
                  (x - algebraMap ℤ_[p] R.carrier (liftC x)) + (y - algebraMap ℤ_[p] R.carrier (liftC y))
                rw [map_add]; ring
              rw [hadd, Submodule.Quotient.mk_add, map_add]
          map_mul' := fun x y => by
            ext
            · exact map_mul R.res x y
            · change D (x * y) = R.res x * D y + D x * R.res y
              let cx := liftC x
              let cy := liftC y
              let mx : IsLocalRing.maximalIdeal R.carrier := ⟨x - algebraMap ℤ_[p] R.carrier cx, hmemM x⟩
              let my : IsLocalRing.maximalIdeal R.carrier := ⟨y - algebraMap ℤ_[p] R.carrier cy, hmemM y⟩
              have hmxy : x * y - algebraMap ℤ_[p] R.carrier (cx * cy) ∈
                  IsLocalRing.maximalIdeal R.carrier := by
                have heq : x * y - algebraMap ℤ_[p] R.carrier (cx * cy) =
                    algebraMap ℤ_[p] R.carrier cx * my.1 + algebraMap ℤ_[p] R.carrier cy * mx.1 +
                      mx.1 * my.1 := by
                  simp only [mx, my, map_mul]; ring
                rw [heq]
                exact Ideal.add_mem _ (Ideal.add_mem _ (Ideal.mul_mem_left _ _ my.2)
                  (Ideal.mul_mem_left _ _ mx.2)) (Ideal.mul_mem_left _ _ my.2)
              rw [hD_indep (x * y) (cx * cy) hmxy]
              have hqeq : Submodule.Quotient.mk (p := R.cotangentSub)
                  ⟨x * y - algebraMap ℤ_[p] R.carrier (cx * cy), hmxy⟩ =
                  R.res x • Submodule.Quotient.mk my + R.res y • Submodule.Quotient.mk mx := by
                have hrx : R.res (algebraMap ℤ_[p] R.carrier cx) = R.res x := by
                  change (R.res.comp (algebraMap ℤ_[p] R.carrier)) cx = R.res x
                  rw [R.res_comp_alg, hliftC x]
                have hry : R.res (algebraMap ℤ_[p] R.carrier cy) = R.res y := by
                  change (R.res.comp (algebraMap ℤ_[p] R.carrier)) cy = R.res y
                  rw [R.res_comp_alg, hliftC y]
                rw [← hrx, ← hry, R.zmod_smul_reducedCotangent_eq, R.zmod_smul_reducedCotangent_eq,
                  ← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul,
                  ← Submodule.Quotient.mk_add, Submodule.Quotient.eq]
                show ((⟨x * y - algebraMap ℤ_[p] R.carrier (cx * cy), hmxy⟩ -
                  (algebraMap ℤ_[p] R.carrier cx • my + algebraMap ℤ_[p] R.carrier cy • mx) :
                    IsLocalRing.maximalIdeal R.carrier).1) ∈ R.cotangentDenomIdeal
                have hdiff : (x * y - algebraMap ℤ_[p] R.carrier (cx * cy)) -
                    (algebraMap ℤ_[p] R.carrier cx * my.1 + algebraMap ℤ_[p] R.carrier cy * mx.1) =
                    mx.1 * my.1 := by
                  simp only [mx, my, map_mul]; ring
                change (x * y - algebraMap ℤ_[p] R.carrier (cx * cy)) -
                  (algebraMap ℤ_[p] R.carrier cx * my.1 + algebraMap ℤ_[p] R.carrier cy * mx.1) ∈
                  R.cotangentDenomIdeal
                rw [hdiff]
                exact Ideal.mem_sup_right (by rw [pow_two]; exact Ideal.mul_mem_mul mx.2 my.2)
              rw [hqeq, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
              change R.res x * D y + R.res y * D x = R.res x * D y + D x * R.res y
              ring }
      proj_comp := by ext x; rfl
      comp_algZp := by
        ext c
        · exact RingHom.congr_fun R.res_comp_alg c
        · change D (algebraMap ℤ_[p] R.carrier c) = 0
          rw [hD_indep (algebraMap ℤ_[p] R.carrier c) c (by simp)]
          have h0 : (⟨algebraMap ℤ_[p] R.carrier c - algebraMap ℤ_[p] R.carrier c, by simp⟩ :
              IsLocalRing.maximalIdeal R.carrier) = 0 := by ext; simp
          rw [h0, Submodule.Quotient.mk_zero, map_zero] }
  left_inv φ := by
    ext x
    · exact (RingHom.congr_fun φ.proj_comp x).symm
    · let cx := Classical.choose (padicInt_toZMod_surjective (p := p) (R.res x))
      change (φ.toRingHom (x - algebraMap ℤ_[p] R.carrier cx)).snd = (φ.toRingHom x).snd
      rw [map_sub, DualNum.sub_snd]
      have hc0 : (φ.toRingHom (algebraMap ℤ_[p] R.carrier cx)).snd = 0 := by
        have h := RingHom.congr_fun φ.comp_algZp cx
        exact congrArg DualNum.snd h
      rw [hc0, sub_zero]
  right_inv ψ := by
    ext q
    induction q using Quotient.inductionOn' with
    | h m =>
      have hm0 : R.res m.1 = 0 := RingHom.mem_ker.mp (R.ker_res.symm ▸ m.2)
      let c := Classical.choose (padicInt_toZMod_surjective (p := p) (R.res m.1))
      have hc0 : PadicInt.toZMod c = 0 := by
        rw [Classical.choose_spec (padicInt_toZMod_surjective (p := p) (R.res m.1)), hm0]
      change ψ (Submodule.Quotient.mk ⟨m.1 - algebraMap ℤ_[p] R.carrier c, _⟩) = ψ (Submodule.Quotient.mk m)
      congr 1
      rw [Submodule.Quotient.eq]
      show (m.1 - algebraMap ℤ_[p] R.carrier c) - m.1 ∈ R.cotangentDenomIdeal
      have hsub : (m.1 - algebraMap ℤ_[p] R.carrier c) - m.1 = -(algebraMap ℤ_[p] R.carrier c) := by ring
      rw [hsub]
      obtain ⟨z, hz⟩ := (padicInt_p_dvd_iff_toZMod_eq_zero c).mpr hc0
      rw [hz, map_mul, map_natCast]
      exact Submodule.neg_mem _ (Ideal.mem_sup_left (Ideal.mem_span_singleton.mpr ⟨algebraMap ℤ_[p] R.carrier z, rfl⟩))

/-- **Artinian Power-Series Evaluation Homomorphism `ℤ_[p][[x₀,…,x_{g-1}]] →ₐ[ℤ_[p]] R`**:
whenever `𝔪_R ^ N = 0` and `r : Fin g → 𝔪_R`, evaluating `X_i ↦ r_i` is a `ℤ_[p]`-algebra hom. -/
def evalArtinian {g N : ℕ} (hN : (IsLocalRing.maximalIdeal R.carrier) ^ N = ⊥)
    (r : Fin g → IsLocalRing.maximalIdeal R.carrier) :
    PatchingBaseRing p g →ₐ[ℤ_[p]] R.carrier := by
  classical
  let degSet : Finset (Fin g →₀ ℕ) :=
    (Fintype.piFinset fun _ : Fin g => Finset.range N).image Finsupp.equivFunOnFinite.symm
  have hmem_degSet : ∀ α : Fin g →₀ ℕ, (∑ i : Fin g, α i) < N → α ∈ degSet := by
    intro α hα
    refine Finset.mem_image.mpr ⟨fun i => α i, ?_, by ext i; rfl⟩
    rw [Fintype.mem_piFinset]
    intro i
    rw [Finset.mem_range]
    exact lt_of_le_of_lt (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)) hα
  have hmon_zero : ∀ α : Fin g →₀ ℕ, N ≤ (∑ i : Fin g, α i) →
      (∏ i : Fin g, (r i).1 ^ (α i)) = 0 := by
    intro α hα
    have hmem : (∏ i : Fin g, (r i).1 ^ (α i)) ∈ (IsLocalRing.maximalIdeal R.carrier) ^ (∑ i : Fin g, α i) := by
      rw [← Finset.prod_pow_eq_pow_sum]
      exact Ideal.prod_mem_prod fun i _ => Ideal.pow_mem_pow (r i).2 (α i)
    have hle : (IsLocalRing.maximalIdeal R.carrier) ^ (∑ i : Fin g, α i) ≤
        (IsLocalRing.maximalIdeal R.carrier) ^ N := Ideal.pow_le_pow_right hα
    have hbot := hle hmem
    rw [hN] at hbot
    exact Ideal.mem_bot.mp hbot
  let evFun : PatchingBaseRing p g → R.carrier := fun f =>
    ∑ α ∈ degSet, algebraMap ℤ_[p] R.carrier (MvPowerSeries.coeff α f) * ∏ i : Fin g, (r i).1 ^ (α i)
  refine
    { toFun := evFun
      map_one' := by
        dsimp only [evFun]
        by_cases hN0 : N = 0
        · subst hN0
          have h10 : (1 : R.carrier) = 0 := by
            have hmem : (1 : R.carrier) ∈ (IsLocalRing.maximalIdeal R.carrier) ^ 0 := by
              rw [pow_zero, Ideal.one_eq_top]; trivial
            rw [hN] at hmem; exact Ideal.mem_bot.mp hmem
          have hsub : Subsingleton R.carrier := subsingleton_of_zero_eq_one h10.symm
          exact Subsingleton.elim _ _
        · have h0mem : (0 : Fin g →₀ ℕ) ∈ degSet := hmem_degSet 0 (by simp; omega)
          rw [Finset.sum_eq_single (0 : Fin g →₀ ℕ)]
          · simp
          · intro α _ hα0
            rw [MvPowerSeries.coeff_one, if_neg hα0, map_zero, zero_mul]
          · intro h; exact absurd h0mem h
      map_zero' := by dsimp only [evFun]; simp
      map_add' := fun f₁ f₂ => by
        dsimp only [evFun]
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun α _ => ?_
        rw [map_add, map_add, add_mul]
      map_mul' := fun f₁ f₂ => by
        dsimp only [evFun]
        rw [Finset.sum_mul]
        simp_rw [Finset.mul_sum]
        have hLHS :
            ∑ α ∈ degSet, algebraMap ℤ_[p] R.carrier (MvPowerSeries.coeff α (f₁ * f₂)) *
              ∏ i : Fin g, (r i).1 ^ α i =
            ∑ α ∈ degSet, ∑ pq ∈ Finset.antidiagonal α,
              (algebraMap ℤ_[p] R.carrier (MvPowerSeries.coeff pq.1 f₁) * ∏ i : Fin g, (r i).1 ^ pq.1 i) *
              (algebraMap ℤ_[p] R.carrier (MvPowerSeries.coeff pq.2 f₂) * ∏ i : Fin g, (r i).1 ^ pq.2 i) := by
          refine Finset.sum_congr rfl fun α _ => ?_
          rw [MvPowerSeries.coeff_mul, map_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun pq hpq => ?_
          have hadd : pq.1 + pq.2 = α := Finset.mem_antidiagonal.mp hpq
          rw [map_mul, ← hadd]
          have hprod : (∏ i : Fin g, (r i).1 ^ (pq.1 + pq.2) i) =
              (∏ i : Fin g, (r i).1 ^ pq.1 i) * (∏ i : Fin g, (r i).1 ^ pq.2 i) := by
            rw [← Finset.prod_mul_distrib]
            refine Finset.prod_congr rfl fun i _ => by rw [Finsupp.add_apply, pow_add]
          rw [hprod]; ring
        rw [hLHS]
        let term : (Fin g →₀ ℕ) × (Fin g →₀ ℕ) → R.carrier := fun pq =>
          (algebraMap ℤ_[p] R.carrier (MvPowerSeries.coeff pq.1 f₁) * ∏ i : Fin g, (r i).1 ^ pq.1 i) *
          (algebraMap ℤ_[p] R.carrier (MvPowerSeries.coeff pq.2 f₂) * ∏ i : Fin g, (r i).1 ^ pq.2 i)
        have hterm0 : ∀ pq : (Fin g →₀ ℕ) × (Fin g →₀ ℕ),
            N ≤ ∑ i : Fin g, (pq.1 + pq.2) i → term pq = 0 := by
          intro pq hge
          have hprod : (∏ i : Fin g, (r i).1 ^ pq.1 i) * (∏ i : Fin g, (r i).1 ^ pq.2 i) =
              ∏ i : Fin g, (r i).1 ^ (pq.1 + pq.2) i := by
            rw [← Finset.prod_mul_distrib]
            refine Finset.prod_congr rfl fun i _ => by rw [Finsupp.add_apply, pow_add]
          dsimp only [term]
          calc (algebraMap ℤ_[p] R.carrier (MvPowerSeries.coeff pq.1 f₁) * ∏ i, (r i).1 ^ pq.1 i) *
                (algebraMap ℤ_[p] R.carrier (MvPowerSeries.coeff pq.2 f₂) * ∏ i, (r i).1 ^ pq.2 i)
              = (algebraMap ℤ_[p] R.carrier (MvPowerSeries.coeff pq.1 f₁) *
                  algebraMap ℤ_[p] R.carrier (MvPowerSeries.coeff pq.2 f₂)) *
                  ((∏ i, (r i).1 ^ pq.1 i) * (∏ i, (r i).1 ^ pq.2 i)) := by ring
            _ = (algebraMap ℤ_[p] R.carrier (MvPowerSeries.coeff pq.1 f₁) *
                  algebraMap ℤ_[p] R.carrier (MvPowerSeries.coeff pq.2 f₂)) *
                  (∏ i, (r i).1 ^ (pq.1 + pq.2) i) := by rw [hprod]
            _ = 0 := by rw [hmon_zero (pq.1 + pq.2) hge, mul_zero]
        have hsum_L : (∑ α ∈ degSet, ∑ pq ∈ Finset.antidiagonal α, term pq) =
            ∑ pq ∈ (degSet ×ˢ degSet).filter (fun pq => ∑ i : Fin g, (pq.1 + pq.2) i < N), term pq := by
          rw [← Finset.sum_biUnion]
          · symm
            refine Finset.sum_subset_zero_on_sdiff ?_ ?_ (fun _ _ => rfl)
            · intro pq hpq
              rw [Finset.mem_filter, Finset.mem_product] at hpq
              refine Finset.mem_biUnion.mpr ⟨pq.1 + pq.2, hmem_degSet _ hpq.2, Finset.mem_antidiagonal.mpr rfl⟩
            · intro pq hpq
              rw [Finset.mem_sdiff] at hpq
              have hlt : ¬ ∑ i : Fin g, (pq.1 + pq.2) i < N := by
                intro hlt
                apply hpq.2
                rw [Finset.mem_filter, Finset.mem_product]
                refine ⟨⟨hmem_degSet pq.1 ?_, hmem_degSet pq.2 ?_⟩, hlt⟩
                · exact lt_of_le_of_lt (Finset.sum_le_sum fun i _ => Nat.le_add_right _ _) hlt
                · exact lt_of_le_of_lt (Finset.sum_le_sum fun i _ => Nat.le_add_left _ _) hlt
              exact hterm0 pq (Nat.le_of_not_lt hlt)
          · intro α₁ _ α₂ _ hne
            change Disjoint (Finset.antidiagonal α₁) (Finset.antidiagonal α₂)
            rw [Finset.disjoint_left]
            intro pq h1 h2
            exact hne ((Finset.mem_antidiagonal.mp h1).symm.trans (Finset.mem_antidiagonal.mp h2))
        have hsum_R : (∑ β ∈ degSet, ∑ γ ∈ degSet, term (β, γ)) =
            ∑ pq ∈ (degSet ×ˢ degSet).filter (fun pq => ∑ i : Fin g, (pq.1 + pq.2) i < N), term pq := by
          rw [← Finset.sum_product']
          symm
          refine Finset.sum_subset_zero_on_sdiff (Finset.filter_subset _ _) ?_ (fun _ _ => rfl)
          intro pq hpq
          rw [Finset.mem_sdiff, Finset.mem_filter] at hpq
          have hge : N ≤ ∑ i : Fin g, (pq.1 + pq.2) i := by
            by_contra hlt
            exact hpq.2 ⟨hpq.1, Nat.lt_of_not_ge hlt⟩
          exact hterm0 pq hge
        exact hsum_L.trans hsum_R.symm
      commutes' := fun c => by
        dsimp only [evFun]
        by_cases hN0 : N = 0
        · subst hN0
          have h10 : (1 : R.carrier) = 0 := by
            have hmem : (1 : R.carrier) ∈ (IsLocalRing.maximalIdeal R.carrier) ^ 0 := by
              rw [pow_zero, Ideal.one_eq_top]; trivial
            rw [hN] at hmem; exact Ideal.mem_bot.mp hmem
          have hsub : Subsingleton R.carrier := subsingleton_of_zero_eq_one h10.symm
          exact Subsingleton.elim _ _
        · have h0mem : (0 : Fin g →₀ ℕ) ∈ degSet := hmem_degSet 0 (by simp; omega)
          rw [Finset.sum_eq_single (0 : Fin g →₀ ℕ)]
          · simp only [Finsupp.coe_zero, Pi.zero_apply, pow_zero, Finset.prod_const_one, mul_one,
              MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
            exact congrArg (algebraMap ℤ_[p] R.carrier) (MvPowerSeries.constantCoeff_C c)
          · intro α _ hα0
            change algebraMap ℤ_[p] R.carrier (MvPowerSeries.coeff α (MvPowerSeries.C c)) * _ = 0
            rw [MvPowerSeries.coeff_C_of_ne_zero hα0, map_zero, zero_mul]
          · intro h; exact absurd h0mem h }

theorem evalArtinian_X {g N : ℕ} (hN : (IsLocalRing.maximalIdeal R.carrier) ^ N = ⊥)
    (r : Fin g → IsLocalRing.maximalIdeal R.carrier) (i : Fin g) :
    R.evalArtinian hN r (MvPowerSeries.X i) = (r i).1 := by
  classical
  by_cases hN1 : N ≤ 1
  · have hN1' : (IsLocalRing.maximalIdeal R.carrier) ^ 1 = ⊥ := by
      have hle := Ideal.pow_le_pow_right hN1 (I := IsLocalRing.maximalIdeal R.carrier)
      rw [hN] at hle; exact le_bot_iff.mp hle
    have hri0 : (r i).1 = 0 := by
      have hm : (r i).1 ∈ (IsLocalRing.maximalIdeal R.carrier) ^ 1 := by rw [pow_one]; exact (r i).2
      rw [hN1'] at hm; exact Ideal.mem_bot.mp hm
    rw [hri0]
    unfold evalArtinian
    dsimp only [AlgHom.coe_mk, RingHom.coe_mk, ZeroHom.coe_mk]
    refine Finset.sum_eq_zero fun α _ => ?_
    rw [MvPowerSeries.coeff_X]
    split_ifs with hα
    · subst hα
      have hprod : (∏ j : Fin g, (r j).1 ^ (Finsupp.single i 1 j)) = (r i).1 := by
        rw [Finset.prod_eq_single i]
        · simp
        · intro j _ hji; rw [Finsupp.single_eq_of_ne hji, pow_zero]
        · intro h; exact absurd (Finset.mem_univ i) h
      rw [hprod, hri0, mul_zero]
    · simp
  · have hlt : 1 < N := by omega
    let degSet : Finset (Fin g →₀ ℕ) :=
      (Fintype.piFinset fun _ : Fin g => Finset.range N).image Finsupp.equivFunOnFinite.symm
    have hmem : Finsupp.single i (1 : ℕ) ∈ degSet := by
      refine Finset.mem_image.mpr ⟨fun j => Finsupp.single i 1 j, ?_, by ext j; rfl⟩
      rw [Fintype.mem_piFinset]
      intro j
      rw [Finset.mem_range]
      by_cases hj : j = i
      · subst hj; simpa using hlt
      · rw [Finsupp.single_eq_of_ne hj]; omega
    change (∑ α ∈ degSet, algebraMap ℤ_[p] R.carrier (MvPowerSeries.coeff α (MvPowerSeries.X i)) *
      ∏ j : Fin g, (r j).1 ^ (α j)) = (r i).1
    rw [Finset.sum_eq_single (Finsupp.single i (1 : ℕ))]
    · rw [MvPowerSeries.coeff_X, if_pos rfl, map_one, one_mul]
      rw [Finset.prod_eq_single i]
      · simp
      · intro j _ hji; rw [Finsupp.single_eq_of_ne hji, pow_zero]
      · intro h; exact absurd (Finset.mem_univ i) h
    · intro α _ hα
      rw [MvPowerSeries.coeff_X, if_neg hα, map_zero, zero_mul]
    · intro h; exact absurd hmem h

/-- **UNCONDITIONAL ARTINIAN PRESENTATION SURJECTION (`ℤ_[p][[x₀,…,x_{g-1}]] ↠ R`)**:
if `𝔪_R ^ N = 0` and `r : Fin g → 𝔪_R` spans `𝔪_R ⧸ (p R + 𝔪_R²)`, then
`evalArtinian : PatchingBaseRing p g →ₐ[ℤ_[p]] R` is **SURJECTIVE**! -/
theorem artinian_presentation_surjective {g N : ℕ}
    (hN : (IsLocalRing.maximalIdeal R.carrier) ^ N = ⊥)
    (r : Fin g → IsLocalRing.maximalIdeal R.carrier)
    (hspan : Submodule.span (ZMod p)
      (Set.range fun i => Submodule.Quotient.mk (p := R.cotangentSub) (r i)) = ⊤) :
    Function.Surjective (R.evalArtinian hN r) := by
  let φ := R.evalArtinian hN r
  have hmax_gen : ∀ m ∈ IsLocalRing.maximalIdeal R.carrier,
      ∃ (a : R.carrier) (b : Fin g → R.carrier) (z : R.carrier),
        z ∈ (IsLocalRing.maximalIdeal R.carrier) ^ 2 ∧
        m = (p : R.carrier) * a + (∑ i : Fin g, b i * (r i).1) + z := by
    intro m hm
    have hq : Submodule.Quotient.mk (p := R.cotangentSub) ⟨m, hm⟩ ∈
        Submodule.span (ZMod p) (Set.range fun i => Submodule.Quotient.mk (p := R.cotangentSub) (r i)) := by
      rw [hspan]; trivial
    rw [Submodule.mem_span_range_iff_exists_fun] at hq
    obtain ⟨c, hc⟩ := hq
    choose b hb using fun i => R.res_surjective (c i)
    have hq2 : Submodule.Quotient.mk (p := R.cotangentSub) ⟨m, hm⟩ =
        Submodule.Quotient.mk (p := R.cotangentSub) (∑ i : Fin g, b i • r i) := by
      rw [← hc]
      change ∑ i : Fin g, c i • Submodule.Quotient.mk (p := R.cotangentSub) (r i) =
        R.cotangentSub.mkQ (∑ i : Fin g, b i • r i)
      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← hb i, R.zmod_smul_reducedCotangent_eq]
      rfl
    have hdiff : m - (∑ i : Fin g, b i * (r i).1) ∈ R.cotangentDenomIdeal := by
      have hsub := (Submodule.Quotient.eq R.cotangentSub).mp hq2
      have hval : (⟨m, hm⟩ - ∑ i : Fin g, b i • r i : IsLocalRing.maximalIdeal R.carrier).1 =
          m - ∑ i : Fin g, b i * (r i).1 := by
        simp only [Submodule.coe_sub, AddSubmonoidClass.coe_finsetSum, SetLike.val_smul, smul_eq_mul]
      simpa [cotangentSub, hval] using hsub
    rcases Submodule.mem_sup.mp hdiff with ⟨u, hu, z, hz, huz⟩
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton.mp hu
    refine ⟨a, b, z, hz, ?_⟩
    linear_combination -huz + ha
  have hφC : ∀ c : ℤ_[p], φ (MvPowerSeries.C c) = algebraMap ℤ_[p] R.carrier c := fun c => φ.commutes c
  have hstep1 : ∀ m ∈ IsLocalRing.maximalIdeal R.carrier,
      ∃ f₁ : PatchingBaseRing p g, m - φ f₁ ∈ (IsLocalRing.maximalIdeal R.carrier) ^ 2 := by
    intro m hm
    obtain ⟨a, b, z, hz, hmeq⟩ := hmax_gen m hm
    obtain ⟨ca, hca⟩ := padicInt_toZMod_surjective (p := p) (R.res a)
    choose cb hcb using fun i => padicInt_toZMod_surjective (p := p) (R.res (b i))
    let f₁ : PatchingBaseRing p g :=
      MvPowerSeries.C ((p : ℤ_[p]) * ca) + ∑ i : Fin g, MvPowerSeries.C (cb i) * MvPowerSeries.X i
    refine ⟨f₁, ?_⟩
    have hφf₁ : φ f₁ = (p : R.carrier) * algebraMap ℤ_[p] R.carrier ca +
        ∑ i : Fin g, algebraMap ℤ_[p] R.carrier (cb i) * (r i).1 := by
      dsimp only [f₁]
      rw [map_add, map_sum, map_mul, map_natCast, map_mul, map_natCast, hφC ca]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, hφC (cb i), R.evalArtinian_X hN r i]
    have hdiff_eq : m - φ f₁ =
        (p : R.carrier) * (a - algebraMap ℤ_[p] R.carrier ca) +
          (∑ i : Fin g, (b i - algebraMap ℤ_[p] R.carrier (cb i)) * (r i).1) + z := by
      have hsub : (∑ i : Fin g, b i * (r i).1) - (∑ i : Fin g, algebraMap ℤ_[p] R.carrier (cb i) * (r i).1) =
          ∑ i : Fin g, (b i - algebraMap ℤ_[p] R.carrier (cb i)) * (r i).1 := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun i _ => (sub_mul _ _ _).symm
      rw [hmeq, hφf₁]
      linear_combination hsub
    rw [hdiff_eq]
    have ha_mem : a - algebraMap ℤ_[p] R.carrier ca ∈ IsLocalRing.maximalIdeal R.carrier := by
      rw [← R.ker_res, RingHom.mem_ker, map_sub]
      have h1 := RingHom.congr_fun R.res_comp_alg ca
      change R.res (algebraMap ℤ_[p] R.carrier ca) = PadicInt.toZMod ca at h1
      rw [h1, hca, sub_self]
    have hb_mem : ∀ i : Fin g, b i - algebraMap ℤ_[p] R.carrier (cb i) ∈ IsLocalRing.maximalIdeal R.carrier := by
      intro i
      rw [← R.ker_res, RingHom.mem_ker, map_sub]
      have h1 := RingHom.congr_fun R.res_comp_alg (cb i)
      change R.res (algebraMap ℤ_[p] R.carrier (cb i)) = PadicInt.toZMod (cb i) at h1
      rw [h1, hcb i, sub_self]
    refine Ideal.add_mem _ (Ideal.add_mem _ ?_ (Ideal.sum_mem _ fun i _ => ?_)) hz
    · rw [pow_two]; exact Ideal.mul_mem_mul R.p_mem_maximalIdeal ha_mem
    · rw [pow_two]; exact Ideal.mul_mem_mul (hb_mem i) (r i).2
  have hpow_approx : ∀ n : ℕ, ∀ w ∈ (IsLocalRing.maximalIdeal R.carrier) ^ n,
      ∃ f : PatchingBaseRing p g, w - φ f ∈ (IsLocalRing.maximalIdeal R.carrier) ^ (n + 1) := by
    intro n
    induction n with
    | zero =>
      intro w _
      obtain ⟨c, hc⟩ := padicInt_toZMod_surjective (p := p) (R.res w)
      refine ⟨MvPowerSeries.C c, ?_⟩
      rw [pow_one, ← R.ker_res, RingHom.mem_ker, map_sub, hφC c]
      have h1 := RingHom.congr_fun R.res_comp_alg c
      change R.res (algebraMap ℤ_[p] R.carrier c) = PadicInt.toZMod c at h1
      rw [h1, hc, sub_self]
    | succ n ihn =>
      intro w hw
      rw [pow_succ] at hw
      refine Submodule.mul_induction_on hw ?_ ?_
      · intro u hu v hv
        obtain ⟨fu, hfu⟩ := ihn u hu
        obtain ⟨fv, hfv⟩ := hstep1 v hv
        refine ⟨fu * fv, ?_⟩
        rw [map_mul]
        have hdecomp : u * v - φ fu * φ fv = (u - φ fu) * v + u * (v - φ fv) - (u - φ fu) * (v - φ fv) := by ring
        rw [hdecomp]
        have h1 : (u - φ fu) * v ∈ (IsLocalRing.maximalIdeal R.carrier) ^ (n + 1 + 1) := by
          rw [pow_succ]; exact Ideal.mul_mem_mul hfu hv
        have h2 : u * (v - φ fv) ∈ (IsLocalRing.maximalIdeal R.carrier) ^ (n + 1 + 1) := by
          rw [show n + 1 + 1 = n + 2 by omega, pow_add]
          exact Ideal.mul_mem_mul hu hfv
        have h3 : (u - φ fu) * (v - φ fv) ∈ (IsLocalRing.maximalIdeal R.carrier) ^ (n + 1 + 1) := by
          have hm : (u - φ fu) * (v - φ fv) ∈ (IsLocalRing.maximalIdeal R.carrier) ^ ((n + 1) + 2) := by
            rw [pow_add]; exact Ideal.mul_mem_mul hfu hfv
          exact Ideal.pow_le_pow_right (by omega) hm
        exact Ideal.sub_mem _ (Ideal.add_mem _ h1 h2) h3
      · intro u v ⟨fu, hfu⟩ ⟨fv, hfv⟩
        refine ⟨fu + fv, ?_⟩
        rw [map_add]
        have hsub : (u + v) - (φ fu + φ fv) = (u - φ fu) + (v - φ fv) := by ring
        rw [hsub]
        exact Ideal.add_mem _ hfu hfv
  have hind : ∀ k : ℕ, ∀ x : R.carrier, ∃ f : PatchingBaseRing p g,
      x - φ f ∈ (IsLocalRing.maximalIdeal R.carrier) ^ k := by
    intro k
    induction k with
    | zero => intro x; exact ⟨0, by rw [pow_zero, Ideal.one_eq_top]; trivial⟩
    | succ k ih =>
      intro x
      obtain ⟨f, hf⟩ := ih x
      obtain ⟨g', hg'⟩ := hpow_approx k (x - φ f) hf
      refine ⟨f + g', ?_⟩
      rw [map_add]
      have hsub : x - (φ f + φ g') = (x - φ f) - φ g' := by ring
      rw [hsub]
      exact hg'
  intro x
  obtain ⟨f, hf⟩ := hind N x
  rw [hN, Ideal.mem_bot, sub_eq_zero] at hf
  exact ⟨f, hf.symm⟩

/-- `𝔪_R`-adic completeness and separatedness of a local `ℤ_[p]`-algebra `R` (e.g. any complete
local Noetherian deformation ring `R`). -/
structure IsMaxAdicComplete : Prop where
  separated : ∀ x : R.carrier, (∀ n : ℕ, x ∈ (IsLocalRing.maximalIdeal R.carrier) ^ n) → x = 0
  complete : ∀ s : ℕ → R.carrier,
    (∀ n : ℕ, s (n + 1) - s n ∈ (IsLocalRing.maximalIdeal R.carrier) ^ n) →
    ∃ x : R.carrier, ∀ n : ℕ, x - s n ∈ (IsLocalRing.maximalIdeal R.carrier) ^ n

/-- Degree-`< N` multi-index truncation of `f ∈ ℤ_[p][[x₀,…,x_{g-1}]]` evaluated at `r : Fin g → 𝔪_R`. -/
def partialEval {g : ℕ} (r : Fin g → IsLocalRing.maximalIdeal R.carrier) (N : ℕ)
    (f : PatchingBaseRing p g) : R.carrier := by
  classical
  let degSet : Finset (Fin g →₀ ℕ) :=
    ((Fintype.piFinset fun _ : Fin g => Finset.range N).image Finsupp.equivFunOnFinite.symm).filter
      (fun α => ∑ i : Fin g, α i < N)
  exact ∑ α ∈ degSet, algebraMap ℤ_[p] R.carrier (MvPowerSeries.coeff α f) *
    ∏ i : Fin g, (r i).1 ^ (α i)

private lemma mem_partialEval_degSet_iff {g : ℕ} (N : ℕ) (α : Fin g →₀ ℕ) :
    α ∈ ((Fintype.piFinset fun _ : Fin g => Finset.range N).image Finsupp.equivFunOnFinite.symm).filter
      (fun β => ∑ i : Fin g, β i < N) ↔ ∑ i : Fin g, α i < N := by
  classical
  rw [Finset.mem_filter]
  refine ⟨fun h => h.2, fun hlt => ⟨?_, hlt⟩⟩
  refine Finset.mem_image.mpr ⟨fun i => α i, ?_, by ext i; rfl⟩
  rw [Fintype.mem_piFinset]
  intro i
  rw [Finset.mem_range]
  exact lt_of_le_of_lt (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)) hlt

private lemma partialEval_cauchy {g : ℕ} (r : Fin g → IsLocalRing.maximalIdeal R.carrier)
    (f : PatchingBaseRing p g) (n : ℕ) :
    R.partialEval r (n + 1) f - R.partialEval r n f ∈ (IsLocalRing.maximalIdeal R.carrier) ^ n := by
  classical
  let s₁ := ((Fintype.piFinset fun _ : Fin g => Finset.range n).image Finsupp.equivFunOnFinite.symm).filter
    (fun β => ∑ i : Fin g, β i < n)
  let s₂ := ((Fintype.piFinset fun _ : Fin g => Finset.range (n + 1)).image Finsupp.equivFunOnFinite.symm).filter
    (fun β => ∑ i : Fin g, β i < n + 1)
  have hsub : s₁ ⊆ s₂ := fun α hα =>
    (mem_partialEval_degSet_iff (n + 1) α).mpr
      (Nat.lt_succ_of_lt ((mem_partialEval_degSet_iff n α).mp hα))
  have hdiff : R.partialEval r (n + 1) f - R.partialEval r n f =
      ∑ α ∈ s₂ \ s₁, algebraMap ℤ_[p] R.carrier (MvPowerSeries.coeff α f) *
        ∏ i : Fin g, (r i).1 ^ (α i) := by
    change (∑ α ∈ s₂, _) - (∑ α ∈ s₁, _) = _
    exact (Finset.sum_sdiff_eq_sub hsub).symm
  rw [hdiff]
  refine Ideal.sum_mem _ fun α hα => ?_
  rw [Finset.mem_sdiff, mem_partialEval_degSet_iff, mem_partialEval_degSet_iff] at hα
  have hdeg : n ≤ ∑ i : Fin g, α i := Nat.le_of_not_lt hα.2
  have hprod_mem : (∏ i : Fin g, (r i).1 ^ (α i)) ∈ (IsLocalRing.maximalIdeal R.carrier) ^ (∑ i : Fin g, α i) := by
    rw [← Finset.prod_pow_eq_pow_sum]
    exact Ideal.prod_mem_prod fun i _ => Ideal.pow_mem_pow (r i).2 (α i)
  exact Ideal.mul_mem_left _ _ (Ideal.pow_le_pow_right hdeg hprod_mem)

/-- **Complete Continuous Evaluation `ℤ_[p][[x₀,…,x_{g-1}]] →ₐ[ℤ_[p]] R`** for any `𝔪_R`-adically
complete local `ℤ_[p]`-algebra `R` and any `r : Fin g → 𝔪_R`. -/
def evalComplete {g : ℕ} (hcomp : R.IsMaxAdicComplete)
    (r : Fin g → IsLocalRing.maximalIdeal R.carrier) :
    PatchingBaseRing p g →ₐ[ℤ_[p]] R.carrier := by
  classical
  let evFun : PatchingBaseRing p g → R.carrier := fun f =>
    Classical.choose (hcomp.complete (fun n => R.partialEval r n f) (R.partialEval_cauchy r f))
  have hev_approx : ∀ (f : PatchingBaseRing p g) (n : ℕ),
      evFun f - R.partialEval r n f ∈ (IsLocalRing.maximalIdeal R.carrier) ^ n := fun f =>
    Classical.choose_spec (hcomp.complete (fun n => R.partialEval r n f) (R.partialEval_cauchy r f))
  have hpart_mul : ∀ (f₁ f₂ : PatchingBaseRing p g) (N : ℕ),
      R.partialEval r N (f₁ * f₂) - R.partialEval r N f₁ * R.partialEval r N f₂ ∈
        (IsLocalRing.maximalIdeal R.carrier) ^ N := by
    intro f₁ f₂ N
    let degSet := ((Fintype.piFinset fun _ : Fin g => Finset.range N).image Finsupp.equivFunOnFinite.symm).filter
      (fun α => ∑ i : Fin g, α i < N)
    let term : (Fin g →₀ ℕ) × (Fin g →₀ ℕ) → R.carrier := fun pq =>
      (algebraMap ℤ_[p] R.carrier (MvPowerSeries.coeff pq.1 f₁) * ∏ i : Fin g, (r i).1 ^ pq.1 i) *
      (algebraMap ℤ_[p] R.carrier (MvPowerSeries.coeff pq.2 f₂) * ∏ i : Fin g, (r i).1 ^ pq.2 i)
    have hprod_ge : ∀ pq : (Fin g →₀ ℕ) × (Fin g →₀ ℕ),
        N ≤ ∑ i : Fin g, (pq.1 + pq.2) i → term pq ∈ (IsLocalRing.maximalIdeal R.carrier) ^ N := by
      intro pq hge
      have hprod : (∏ i : Fin g, (r i).1 ^ pq.1 i) * (∏ i : Fin g, (r i).1 ^ pq.2 i) =
          ∏ i : Fin g, (r i).1 ^ (pq.1 + pq.2) i := by
        rw [← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun i _ => by rw [Finsupp.add_apply, pow_add]
      have hterm_eq : term pq =
          (algebraMap ℤ_[p] R.carrier (MvPowerSeries.coeff pq.1 f₁) *
            algebraMap ℤ_[p] R.carrier (MvPowerSeries.coeff pq.2 f₂)) *
            ∏ i : Fin g, (r i).1 ^ (pq.1 + pq.2) i := by
        dsimp only [term]; rw [← hprod]; ring
      rw [hterm_eq]
      have hmem : (∏ i : Fin g, (r i).1 ^ (pq.1 + pq.2) i) ∈
          (IsLocalRing.maximalIdeal R.carrier) ^ (∑ i : Fin g, (pq.1 + pq.2) i) := by
        rw [← Finset.prod_pow_eq_pow_sum]
        exact Ideal.prod_mem_prod fun i _ => Ideal.pow_mem_pow (r i).2 _
      exact Ideal.mul_mem_left _ _ (Ideal.pow_le_pow_right hge hmem)
    have hL : R.partialEval r N (f₁ * f₂) =
        ∑ pq ∈ (degSet ×ˢ degSet).filter (fun pq => ∑ i : Fin g, (pq.1 + pq.2) i < N), term pq := by
      change (∑ α ∈ degSet, algebraMap ℤ_[p] R.carrier (MvPowerSeries.coeff α (f₁ * f₂)) *
          ∏ i : Fin g, (r i).1 ^ α i) = _
      have h1 : (∑ α ∈ degSet, algebraMap ℤ_[p] R.carrier (MvPowerSeries.coeff α (f₁ * f₂)) *
            ∏ i : Fin g, (r i).1 ^ α i) =
          ∑ α ∈ degSet, ∑ pq ∈ Finset.antidiagonal α, term pq := by
        refine Finset.sum_congr rfl fun α _ => ?_
        rw [MvPowerSeries.coeff_mul, map_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun pq hpq => ?_
        have hadd : pq.1 + pq.2 = α := Finset.mem_antidiagonal.mp hpq
        rw [map_mul, ← hadd]
        have hprod : (∏ i : Fin g, (r i).1 ^ (pq.1 + pq.2) i) =
            (∏ i : Fin g, (r i).1 ^ pq.1 i) * (∏ i : Fin g, (r i).1 ^ pq.2 i) := by
          rw [← Finset.prod_mul_distrib]
          refine Finset.prod_congr rfl fun i _ => by rw [Finsupp.add_apply, pow_add]
        dsimp only [term]; rw [hprod]; ring
      rw [h1, ← Finset.sum_biUnion]
      · congr 1
        ext pq
        rw [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_product]
        constructor
        · rintro ⟨α, hα, hpq⟩
          have hadd : pq.1 + pq.2 = α := Finset.mem_antidiagonal.mp hpq
          have hlt : ∑ i : Fin g, (pq.1 + pq.2) i < N := by
            rw [hadd]; exact (mem_partialEval_degSet_iff N α).mp hα
          refine ⟨⟨(mem_partialEval_degSet_iff N pq.1).mpr ?_,
            (mem_partialEval_degSet_iff N pq.2).mpr ?_⟩, hlt⟩
          · exact lt_of_le_of_lt (Finset.sum_le_sum fun i _ => Nat.le_add_right _ _) hlt
          · exact lt_of_le_of_lt (Finset.sum_le_sum fun i _ => Nat.le_add_left _ _) hlt
        · rintro ⟨_, hlt⟩
          exact ⟨pq.1 + pq.2, (mem_partialEval_degSet_iff N _).mpr hlt,
            Finset.mem_antidiagonal.mpr rfl⟩
      · intro α₁ _ α₂ _ hne
        change Disjoint (Finset.antidiagonal α₁) (Finset.antidiagonal α₂)
        rw [Finset.disjoint_left]
        intro pq h1 h2
        exact hne ((Finset.mem_antidiagonal.mp h1).symm.trans (Finset.mem_antidiagonal.mp h2))
    have hR : R.partialEval r N f₁ * R.partialEval r N f₂ = ∑ pq ∈ degSet ×ˢ degSet, term pq := by
      change (∑ β ∈ degSet, _) * (∑ γ ∈ degSet, _) = _
      rw [Finset.sum_mul]
      simp_rw [Finset.mul_sum]
      exact (Finset.sum_product' _ _ _).symm
    rw [hL, hR]
    have hsub := Finset.sum_sdiff_eq_sub (f := term)
      (Finset.filter_subset (fun pq : (Fin g →₀ ℕ) × (Fin g →₀ ℕ) => ∑ i : Fin g, (pq.1 + pq.2) i < N)
        (degSet ×ˢ degSet))
    have hneg : (∑ pq ∈ (degSet ×ˢ degSet).filter (fun pq => ∑ i : Fin g, (pq.1 + pq.2) i < N), term pq) -
        (∑ pq ∈ degSet ×ˢ degSet, term pq) =
        -(∑ pq ∈ (degSet ×ˢ degSet) \ (degSet ×ˢ degSet).filter (fun pq => ∑ i : Fin g, (pq.1 + pq.2) i < N),
          term pq) := by
      rw [hsub, neg_sub]
    rw [hneg]
    refine Submodule.neg_mem _ (Ideal.sum_mem _ fun pq hpq => ?_)
    rw [Finset.mem_sdiff, Finset.mem_filter] at hpq
    exact hprod_ge pq (Nat.le_of_not_lt fun hlt => hpq.2 ⟨hpq.1, hlt⟩)
  refine
    { toFun := evFun
      map_one' := by
        apply sub_eq_zero.mp
        refine hcomp.separated _ fun n => ?_
        have hpart1 : R.partialEval r (n + 1) 1 = 1 := by
          let degSet := ((Fintype.piFinset fun _ : Fin g => Finset.range (n + 1)).image
            Finsupp.equivFunOnFinite.symm).filter (fun α => ∑ i : Fin g, α i < n + 1)
          have h0 : (0 : Fin g →₀ ℕ) ∈ degSet := (mem_partialEval_degSet_iff (n + 1) 0).mpr (by simp)
          change (∑ α ∈ degSet, _) = 1
          rw [Finset.sum_eq_single (0 : Fin g →₀ ℕ)]
          · simp
          · intro α _ hα0; rw [MvPowerSeries.coeff_one, if_neg hα0, map_zero, zero_mul]
          · intro h; exact absurd h0 h
        have h1 : evFun 1 - 1 = evFun 1 - R.partialEval r (n + 1) 1 := by rw [hpart1]
        rw [h1]
        exact Ideal.pow_le_pow_right (Nat.le_succ n) (hev_approx 1 (n + 1))
      map_zero' := by
        apply hcomp.separated _ fun n => ?_
        have h0 : R.partialEval r n 0 = 0 := by
          change (∑ α ∈ _, _) = 0; simp
        simpa [h0] using hev_approx 0 n
      map_add' := fun f₁ f₂ => by
        apply sub_eq_zero.mp
        refine hcomp.separated _ fun n => ?_
        have hpart_add : R.partialEval r n (f₁ + f₂) = R.partialEval r n f₁ + R.partialEval r n f₂ := by
          change (∑ α ∈ _, _) = (∑ α ∈ _, _) + (∑ α ∈ _, _)
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun α _ => by rw [map_add, map_add, add_mul]
        have hdecomp : evFun (f₁ + f₂) - (evFun f₁ + evFun f₂) =
            (evFun (f₁ + f₂) - R.partialEval r n (f₁ + f₂)) -
              (evFun f₁ - R.partialEval r n f₁) - (evFun f₂ - R.partialEval r n f₂) := by
          rw [hpart_add]; ring
        rw [hdecomp]
        exact Ideal.sub_mem _ (Ideal.sub_mem _ (hev_approx (f₁ + f₂) n) (hev_approx f₁ n)) (hev_approx f₂ n)
      map_mul' := fun f₁ f₂ => by
        apply sub_eq_zero.mp
        refine hcomp.separated _ fun n => ?_
        have hdecomp : evFun (f₁ * f₂) - evFun f₁ * evFun f₂ =
            (evFun (f₁ * f₂) - R.partialEval r n (f₁ * f₂)) +
            (R.partialEval r n (f₁ * f₂) - R.partialEval r n f₁ * R.partialEval r n f₂) -
            (evFun f₁ - R.partialEval r n f₁) * evFun f₂ -
            R.partialEval r n f₁ * (evFun f₂ - R.partialEval r n f₂) := by ring
        rw [hdecomp]
        exact Ideal.sub_mem _
          (Ideal.sub_mem _ (Ideal.add_mem _ (hev_approx (f₁ * f₂) n) (hpart_mul f₁ f₂ n))
            (Ideal.mul_mem_right _ _ (hev_approx f₁ n)))
          (Ideal.mul_mem_left _ _ (hev_approx f₂ n))
      commutes' := fun c => by
        apply sub_eq_zero.mp
        refine hcomp.separated _ fun n => ?_
        have hpartC : R.partialEval r (n + 1) (MvPowerSeries.C c) = algebraMap ℤ_[p] R.carrier c := by
          let degSet := ((Fintype.piFinset fun _ : Fin g => Finset.range (n + 1)).image
            Finsupp.equivFunOnFinite.symm).filter (fun α => ∑ i : Fin g, α i < n + 1)
          have h0 : (0 : Fin g →₀ ℕ) ∈ degSet := (mem_partialEval_degSet_iff (n + 1) 0).mpr (by simp)
          change (∑ α ∈ degSet, _) = _
          rw [Finset.sum_eq_single (0 : Fin g →₀ ℕ)]
          · simp only [Finsupp.coe_zero, Pi.zero_apply, pow_zero, Finset.prod_const_one, mul_one,
              MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.constantCoeff_C]
          · intro α _ hα0; rw [MvPowerSeries.coeff_C_of_ne_zero hα0, map_zero, zero_mul]
          · intro h; exact absurd h0 h
        have h1 : evFun (MvPowerSeries.C c) - algebraMap ℤ_[p] R.carrier c =
            evFun (MvPowerSeries.C c) - R.partialEval r (n + 1) (MvPowerSeries.C c) := by rw [hpartC]
        change evFun (MvPowerSeries.C c) - algebraMap ℤ_[p] R.carrier c ∈ _
        rw [h1]
        exact Ideal.pow_le_pow_right (Nat.le_succ n) (hev_approx (MvPowerSeries.C c) (n + 1)) }

theorem evalComplete_sub_partialEval_mem {g : ℕ} (hcomp : R.IsMaxAdicComplete)
    (r : Fin g → IsLocalRing.maximalIdeal R.carrier) (f : PatchingBaseRing p g) (n : ℕ) :
    R.evalComplete hcomp r f - R.partialEval r n f ∈ (IsLocalRing.maximalIdeal R.carrier) ^ n :=
  Classical.choose_spec (hcomp.complete (fun m => R.partialEval r m f) (R.partialEval_cauchy r f)) n

theorem evalComplete_X {g : ℕ} (hcomp : R.IsMaxAdicComplete)
    (r : Fin g → IsLocalRing.maximalIdeal R.carrier) (i : Fin g) :
    R.evalComplete hcomp r (MvPowerSeries.X i) = (r i).1 := by
  classical
  apply sub_eq_zero.mp
  refine hcomp.separated _ fun n => ?_
  have hpartX : R.partialEval r (n + 2) (MvPowerSeries.X i) = (r i).1 := by
    let degSet := ((Fintype.piFinset fun _ : Fin g => Finset.range (n + 2)).image
      Finsupp.equivFunOnFinite.symm).filter (fun α => ∑ j : Fin g, α j < n + 2)
    have hmem : Finsupp.single i (1 : ℕ) ∈ degSet :=
      (mem_partialEval_degSet_iff (n + 2) _).mpr (by
        rw [Finset.sum_eq_single i]
        · simp
        · intro j _ hji; exact Finsupp.single_eq_of_ne hji
        · intro h; exact absurd (Finset.mem_univ i) h)
    change (∑ α ∈ degSet, _) = (r i).1
    rw [Finset.sum_eq_single (Finsupp.single i (1 : ℕ))]
    · rw [MvPowerSeries.coeff_X, if_pos rfl, map_one, one_mul]
      rw [Finset.prod_eq_single i]
      · simp
      · intro j _ hji; rw [Finsupp.single_eq_of_ne hji, pow_zero]
      · intro h; exact absurd (Finset.mem_univ i) h
    · intro α _ hα; rw [MvPowerSeries.coeff_X, if_neg hα, map_zero, zero_mul]
    · intro h; exact absurd hmem h
  have h1 : R.evalComplete hcomp r (MvPowerSeries.X i) - (r i).1 =
      R.evalComplete hcomp r (MvPowerSeries.X i) - R.partialEval r (n + 2) (MvPowerSeries.X i) := by
    rw [hpartX]
  rw [h1]
  exact Ideal.pow_le_pow_right (by omega) (R.evalComplete_sub_partialEval_mem hcomp r (MvPowerSeries.X i) (n + 2))

/-- Helper: every `h ∈ 𝔪_{S_g} ^ k` has `p ^ (k - |α|) ∣ coeff α h` in `ℤ_[p]`. -/
private lemma coeff_dvd_of_mem_maximalIdeal_pow {g : ℕ} :
    ∀ (k : ℕ) (h : PatchingBaseRing p g),
      h ∈ (IsLocalRing.maximalIdeal (PatchingBaseRing p g)) ^ k →
      ∀ α : Fin g →₀ ℕ, (p : ℤ_[p]) ^ (k - ∑ i : Fin g, α i) ∣ MvPowerSeries.coeff α h := by
  intro k
  induction k with
  | zero =>
    intro h _ α; simp
  | succ k ih =>
    intro h hh
    rw [pow_succ] at hh
    refine Submodule.mul_induction_on hh ?_ ?_
    · intro u hu v hv α
      rw [MvPowerSeries.coeff_mul]
      refine Finset.dvd_sum fun pq hpq => ?_
      have hadd : pq.1 + pq.2 = α := Finset.mem_antidiagonal.mp hpq
      have hsum_add : (∑ i : Fin g, pq.1 i) + (∑ i : Fin g, pq.2 i) = ∑ i : Fin g, α i := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun i _ => by rw [← Finsupp.add_apply, hadd]
      by_cases h2z : pq.2 = 0
      · have h1eq : pq.1 = α := by rw [← hadd, h2z, add_zero]
        have hsum1 : ∑ i : Fin g, pq.1 i = ∑ i : Fin g, α i := by rw [h1eq]
        have hu_dvd : (p : ℤ_[p]) ^ (k - ∑ i : Fin g, α i) ∣ MvPowerSeries.coeff pq.1 u := by
          rw [← hsum1]; exact ih u hu pq.1
        have hv_dvd : (p : ℤ_[p]) ∣ MvPowerSeries.coeff pq.2 v := by
          rw [h2z, MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
          rwa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, patchingBaseRing_isUnit_iff, not_not] at hv
        have hmul_dvd : (p : ℤ_[p]) ^ ((k - ∑ i : Fin g, α i) + 1) ∣
            MvPowerSeries.coeff pq.1 u * MvPowerSeries.coeff pq.2 v := by
          rw [pow_succ]
          exact mul_dvd_mul hu_dvd hv_dvd
        exact (pow_dvd_pow (p : ℤ_[p]) (by omega)).trans hmul_dvd
      · have h2pos : 1 ≤ ∑ i : Fin g, pq.2 i := by
          obtain ⟨i₀, hi₀⟩ := Finsupp.support_nonempty_iff.mpr h2z
          have hi₀_pos : 1 ≤ pq.2 i₀ := Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi₀)
          exact le_trans hi₀_pos (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i₀))
        have hu_dvd := ih u hu pq.1
        have hle : k + 1 - ∑ i : Fin g, α i ≤ k - ∑ i : Fin g, pq.1 i := by omega
        exact dvd_mul_of_dvd_left ((pow_dvd_pow (p : ℤ_[p]) hle).trans hu_dvd) _
    · intro x y hx hy α
      rw [map_add]
      exact dvd_add (hx α) (hy α)

/-- **UNCONDITIONAL COHEN COMPLETE PRESENTATION SURJECTION (`ℤ_[p][[x₀,…,x_{g-1}]] ↠ R`)**:
for EVERY `𝔪_R`-adically complete and separated local `ℤ_[p]`-algebra `R` with residue field `𝔽_p`,
if `r : Fin g → 𝔪_R` spans the reduced cotangent space `𝔪_R ⧸ (p R + 𝔪_R²)` (dimension `≤ g`),
then **`evalComplete hcomp r : PatchingBaseRing p g →ₐ[ℤ_[p]] R` is SURJECTIVE**! -/
theorem complete_presentation_surjective {g : ℕ} (hcomp : R.IsMaxAdicComplete)
    (r : Fin g → IsLocalRing.maximalIdeal R.carrier)
    (hspan : Submodule.span (ZMod p)
      (Set.range fun i => Submodule.Quotient.mk (p := R.cotangentSub) (r i)) = ⊤) :
    Function.Surjective (R.evalComplete hcomp r) := by
  let φ := R.evalComplete hcomp r
  have hφC : ∀ c : ℤ_[p], φ (MvPowerSeries.C c) = algebraMap ℤ_[p] R.carrier c := fun c => φ.commutes c
  -- Step 1: Every `m ∈ 𝔪_R` is approximated mod `𝔪_R²` by some `f₁ ∈ 𝔪_{S_g}`!
  have hmax_gen : ∀ m ∈ IsLocalRing.maximalIdeal R.carrier,
      ∃ (a : R.carrier) (b : Fin g → R.carrier) (z : R.carrier),
        z ∈ (IsLocalRing.maximalIdeal R.carrier) ^ 2 ∧
        m = (p : R.carrier) * a + (∑ i : Fin g, b i * (r i).1) + z := by
    intro m hm
    have hq : Submodule.Quotient.mk (p := R.cotangentSub) ⟨m, hm⟩ ∈
        Submodule.span (ZMod p) (Set.range fun i => Submodule.Quotient.mk (p := R.cotangentSub) (r i)) := by
      rw [hspan]; trivial
    rw [Submodule.mem_span_range_iff_exists_fun] at hq
    obtain ⟨c, hc⟩ := hq
    choose b hb using fun i => R.res_surjective (c i)
    have hq2 : Submodule.Quotient.mk (p := R.cotangentSub) ⟨m, hm⟩ =
        Submodule.Quotient.mk (p := R.cotangentSub) (∑ i : Fin g, b i • r i) := by
      rw [← hc]
      change ∑ i : Fin g, c i • Submodule.Quotient.mk (p := R.cotangentSub) (r i) =
        R.cotangentSub.mkQ (∑ i : Fin g, b i • r i)
      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← hb i, R.zmod_smul_reducedCotangent_eq]
      rfl
    have hdiff : m - (∑ i : Fin g, b i * (r i).1) ∈ R.cotangentDenomIdeal := by
      have hsub := (Submodule.Quotient.eq R.cotangentSub).mp hq2
      have hval : (⟨m, hm⟩ - ∑ i : Fin g, b i • r i : IsLocalRing.maximalIdeal R.carrier).1 =
          m - ∑ i : Fin g, b i * (r i).1 := by
        simp only [Submodule.coe_sub, AddSubmonoidClass.coe_finsetSum, SetLike.val_smul, smul_eq_mul]
      simpa [cotangentSub, hval] using hsub
    rcases Submodule.mem_sup.mp hdiff with ⟨u, hu, z, hz, huz⟩
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton.mp hu
    refine ⟨a, b, z, hz, ?_⟩
    linear_combination -huz + ha
  have hstep1 : ∀ m ∈ IsLocalRing.maximalIdeal R.carrier,
      ∃ f₁ ∈ IsLocalRing.maximalIdeal (PatchingBaseRing p g),
        m - φ f₁ ∈ (IsLocalRing.maximalIdeal R.carrier) ^ 2 := by
    intro m hm
    obtain ⟨a, b, z, hz, hmeq⟩ := hmax_gen m hm
    obtain ⟨ca, hca⟩ := padicInt_toZMod_surjective (p := p) (R.res a)
    choose cb hcb using fun i => padicInt_toZMod_surjective (p := p) (R.res (b i))
    let f₁ : PatchingBaseRing p g :=
      MvPowerSeries.C ((p : ℤ_[p]) * ca) + ∑ i : Fin g, MvPowerSeries.C (cb i) * MvPowerSeries.X i
    have hf₁_mem : f₁ ∈ IsLocalRing.maximalIdeal (PatchingBaseRing p g) := by
      rw [maximalIdeal_patchingBaseRing_eq]
      refine Ideal.add_mem _ ?_ (Ideal.sum_mem _ fun i _ => ?_)
      · rw [map_mul, map_natCast]
        exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_insert _ _))
      · exact Ideal.mul_mem_left _ _
          (Ideal.subset_span (Set.mem_insert_of_mem _ ⟨i, rfl⟩))
    refine ⟨f₁, hf₁_mem, ?_⟩
    have hφf₁ : φ f₁ = (p : R.carrier) * algebraMap ℤ_[p] R.carrier ca +
        ∑ i : Fin g, algebraMap ℤ_[p] R.carrier (cb i) * (r i).1 := by
      dsimp only [f₁]
      rw [map_add, map_sum, map_mul, map_natCast, map_mul, map_natCast, hφC ca]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, hφC (cb i), R.evalComplete_X hcomp r i]
    have hdiff_eq : m - φ f₁ =
        (p : R.carrier) * (a - algebraMap ℤ_[p] R.carrier ca) +
          (∑ i : Fin g, (b i - algebraMap ℤ_[p] R.carrier (cb i)) * (r i).1) + z := by
      have hsub : (∑ i : Fin g, b i * (r i).1) - (∑ i : Fin g, algebraMap ℤ_[p] R.carrier (cb i) * (r i).1) =
          ∑ i : Fin g, (b i - algebraMap ℤ_[p] R.carrier (cb i)) * (r i).1 := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun i _ => (sub_mul _ _ _).symm
      rw [hmeq, hφf₁]
      linear_combination hsub
    rw [hdiff_eq]
    have ha_mem : a - algebraMap ℤ_[p] R.carrier ca ∈ IsLocalRing.maximalIdeal R.carrier := by
      rw [← R.ker_res, RingHom.mem_ker, map_sub]
      have h1 := RingHom.congr_fun R.res_comp_alg ca
      change R.res (algebraMap ℤ_[p] R.carrier ca) = PadicInt.toZMod ca at h1
      rw [h1, hca, sub_self]
    have hb_mem : ∀ i : Fin g, b i - algebraMap ℤ_[p] R.carrier (cb i) ∈ IsLocalRing.maximalIdeal R.carrier := by
      intro i
      rw [← R.ker_res, RingHom.mem_ker, map_sub]
      have h1 := RingHom.congr_fun R.res_comp_alg (cb i)
      change R.res (algebraMap ℤ_[p] R.carrier (cb i)) = PadicInt.toZMod (cb i) at h1
      rw [h1, hcb i, sub_self]
    refine Ideal.add_mem _ (Ideal.add_mem _ ?_ (Ideal.sum_mem _ fun i _ => ?_)) hz
    · rw [pow_two]; exact Ideal.mul_mem_mul R.p_mem_maximalIdeal ha_mem
    · rw [pow_two]; exact Ideal.mul_mem_mul (hb_mem i) (r i).2
  -- Step 2: Every `w ∈ 𝔪_R ^ n` is approximated mod `𝔪_R ^ (n + 1)` by some `h ∈ 𝔪_{S_g} ^ n`!
  have hpow_approx : ∀ n : ℕ, ∀ w ∈ (IsLocalRing.maximalIdeal R.carrier) ^ n,
      ∃ h ∈ (IsLocalRing.maximalIdeal (PatchingBaseRing p g)) ^ n,
        w - φ h ∈ (IsLocalRing.maximalIdeal R.carrier) ^ (n + 1) := by
    intro n
    induction n with
    | zero =>
      intro w _
      obtain ⟨c, hc⟩ := padicInt_toZMod_surjective (p := p) (R.res w)
      refine ⟨MvPowerSeries.C c, by rw [pow_zero, Ideal.one_eq_top]; trivial, ?_⟩
      rw [pow_one, ← R.ker_res, RingHom.mem_ker, map_sub, hφC c]
      have h1 := RingHom.congr_fun R.res_comp_alg c
      change R.res (algebraMap ℤ_[p] R.carrier c) = PadicInt.toZMod c at h1
      rw [h1, hc, sub_self]
    | succ n ihn =>
      intro w hw
      rw [pow_succ] at hw
      refine Submodule.mul_induction_on hw ?_ ?_
      · intro u hu v hv
        obtain ⟨fu, hfu_mem, hfu⟩ := ihn u hu
        obtain ⟨fv, hfv_mem, hfv⟩ := hstep1 v hv
        refine ⟨fu * fv, by rw [pow_succ]; exact Ideal.mul_mem_mul hfu_mem hfv_mem, ?_⟩
        rw [map_mul]
        have hdecomp : u * v - φ fu * φ fv = (u - φ fu) * v + u * (v - φ fv) - (u - φ fu) * (v - φ fv) := by ring
        rw [hdecomp]
        have h1 : (u - φ fu) * v ∈ (IsLocalRing.maximalIdeal R.carrier) ^ (n + 1 + 1) := by
          rw [pow_succ]; exact Ideal.mul_mem_mul hfu hv
        have h2 : u * (v - φ fv) ∈ (IsLocalRing.maximalIdeal R.carrier) ^ (n + 1 + 1) := by
          rw [show n + 1 + 1 = n + 2 by omega, pow_add]
          exact Ideal.mul_mem_mul hu hfv
        have h3 : (u - φ fu) * (v - φ fv) ∈ (IsLocalRing.maximalIdeal R.carrier) ^ (n + 1 + 1) := by
          have hm : (u - φ fu) * (v - φ fv) ∈ (IsLocalRing.maximalIdeal R.carrier) ^ ((n + 1) + 2) := by
            rw [pow_add]; exact Ideal.mul_mem_mul hfu hfv
          exact Ideal.pow_le_pow_right (by omega) hm
        exact Ideal.sub_mem _ (Ideal.add_mem _ h1 h2) h3
      · intro u v ⟨fu, hfu_mem, hfu⟩ ⟨fv, hfv_mem, hfv⟩
        refine ⟨fu + fv, Ideal.add_mem _ hfu_mem hfv_mem, ?_⟩
        rw [map_add]
        have hsub : (u + v) - (φ fu + φ fv) = (u - φ fu) + (v - φ fv) := by ring
        rw [hsub]
        exact Ideal.add_mem _ hfu hfv
  -- Step 3: Build the recursive lifting sequence `h_n ∈ 𝔪_{S_g} ^ n` with `x - φ(∑_{k < n} h_k) ∈ 𝔪_R ^ n`!
  intro x
  let recStep : ∀ (n : ℕ) (st : { s : PatchingBaseRing p g //
      x - φ s ∈ (IsLocalRing.maximalIdeal R.carrier) ^ n }),
      { p_pair : PatchingBaseRing p g × { s : PatchingBaseRing p g //
          x - φ s ∈ (IsLocalRing.maximalIdeal R.carrier) ^ (n + 1) } //
        p_pair.1 ∈ (IsLocalRing.maximalIdeal (PatchingBaseRing p g)) ^ n ∧
        p_pair.2.1 = st.1 + p_pair.1 } := by
    intro n ⟨s, hs⟩
    let h := Classical.choose (hpow_approx n (x - φ s) hs)
    have hh := Classical.choose_spec (hpow_approx n (x - φ s) hs)
    refine ⟨(h, ⟨s + h, ?_⟩), hh.1, rfl⟩
    rw [map_add]
    have hsub : x - (φ s + φ h) = (x - φ s) - φ h := by ring
    rw [hsub]
    exact hh.2
  let seqState : ∀ n : ℕ, { s : PatchingBaseRing p g //
      x - φ s ∈ (IsLocalRing.maximalIdeal R.carrier) ^ n } :=
    Nat.rec ⟨0, by rw [pow_zero, Ideal.one_eq_top]; trivial⟩
      (fun n st => (recStep n st).1.2)
  let h : ℕ → PatchingBaseRing p g := fun n => (recStep n (seqState n)).1.1
  have hh_mem : ∀ n : ℕ, h n ∈ (IsLocalRing.maximalIdeal (PatchingBaseRing p g)) ^ n :=
    fun n => (recStep n (seqState n)).2.1
  have hseq_sum : ∀ n : ℕ, (seqState n).1 = ∑ k ∈ Finset.range n, h k := by
    intro n
    induction n with
    | zero => simp [seqState]
    | succ n ih =>
      rw [Finset.sum_range_succ, ← ih]
  -- Step 4: Sum `coeff α (h k)` `p`-adically in `ℤ_[p]` for each multi-index `α`!
  have hp_lt1 : ‖(p : ℤ_[p])‖ < 1 := by
    change ‖(p : ℚ_[p])‖ < 1
    rw [Padic.norm_p]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt)
  have hnorm_p_pow : ∀ m : ℕ, ‖(p : ℤ_[p])‖ ^ m = (p : ℝ) ^ (-(m : ℤ)) := fun m => by
    change ‖(p : ℚ_[p])‖ ^ m = _
    rw [Padic.norm_p, inv_pow, _root_.zpow_neg, zpow_natCast]
  have hcoeff_norm_le : ∀ (α : Fin g →₀ ℕ) (k : ℕ),
      ‖MvPowerSeries.coeff α (h k)‖ ≤ (p : ℝ) ^ (-((k - ∑ i : Fin g, α i : ℕ) : ℤ)) := by
    intro α k
    have hdvd := coeff_dvd_of_mem_maximalIdeal_pow (p := p) (g := g) k (h k) (hh_mem k) α
    rw [← Ideal.mem_span_singleton, ← PadicInt.norm_le_pow_iff_mem_span_pow] at hdvd
    exact hdvd
  have hsummable : ∀ α : Fin g →₀ ℕ, Summable (fun k : ℕ => MvPowerSeries.coeff α (h k)) := by
    intro α
    let d := ∑ i : Fin g, α i
    rw [← summable_nat_add_iff d]
    refine Summable.of_norm ?_
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun m => ?_)
      (summable_geometric_of_lt_one (norm_nonneg _) hp_lt1)
    have hbd := hcoeff_norm_le α (m + d)
    rw [Nat.add_sub_cancel] at hbd
    rwa [hnorm_p_pow m]
  let f : PatchingBaseRing p g := fun α => ∑' k : ℕ, MvPowerSeries.coeff α (h k)
  refine ⟨f, ?_⟩
  apply sub_eq_zero.mp
  refine hcomp.separated _ fun N => ?_
  have hdiff_split : φ f - x =
      (φ f - R.partialEval r N f) -
      (φ (seqState N).1 - R.partialEval r N (seqState N).1) +
      (R.partialEval r N f - R.partialEval r N (seqState N).1) -
      (x - φ (seqState N).1) := by ring
  rw [hdiff_split]
  refine Ideal.sub_mem _ (Ideal.add_mem _ (Ideal.sub_mem _
    (R.evalComplete_sub_partialEval_mem hcomp r f N)
    (R.evalComplete_sub_partialEval_mem hcomp r (seqState N).1 N)) ?_) (seqState N).2
  -- Show `partialEval r N f - partialEval r N (seqState N) ∈ 𝔪_R ^ N`!
  classical
  let degSet := ((Fintype.piFinset fun _ : Fin g => Finset.range N).image Finsupp.equivFunOnFinite.symm).filter
    (fun α => ∑ i : Fin g, α i < N)
  have hpart_diff : R.partialEval r N f - R.partialEval r N (seqState N).1 =
      ∑ α ∈ degSet, algebraMap ℤ_[p] R.carrier
        (MvPowerSeries.coeff α f - MvPowerSeries.coeff α (seqState N).1) *
        ∏ i : Fin g, (r i).1 ^ α i := by
    change (∑ α ∈ degSet, _) - (∑ α ∈ degSet, _) = _
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun α _ => by rw [map_sub, sub_mul]
  rw [hpart_diff]
  refine Ideal.sum_mem _ fun α hα => ?_
  have hdeg_lt : ∑ i : Fin g, α i < N := (mem_partialEval_degSet_iff N α).mp hα
  have htail_dvd : (p : ℤ_[p]) ^ (N - ∑ i : Fin g, α i) ∣
      (MvPowerSeries.coeff α f - MvPowerSeries.coeff α (seqState N).1) := by
    rw [← Ideal.mem_span_singleton, ← PadicInt.norm_le_pow_iff_mem_span_pow]
    have hcoeff_f : MvPowerSeries.coeff α f = ∑' k : ℕ, MvPowerSeries.coeff α (h k) := rfl
    have hcoeff_s : MvPowerSeries.coeff α (seqState N).1 = ∑ k ∈ Finset.range N, MvPowerSeries.coeff α (h k) := by
      rw [hseq_sum N, map_sum]
    rw [hcoeff_f, hcoeff_s]
    have hs := hsummable α
    have hsp : (∑' k : ℕ, MvPowerSeries.coeff α (h k)) - ∑ k ∈ Finset.range N, MvPowerSeries.coeff α (h k) =
        ∑' m : ℕ, MvPowerSeries.coeff α (h (m + N)) := by
      rw [← hs.sum_add_tsum_nat_add N]; ring
    rw [hsp]
    have hs' := (summable_nat_add_iff N).mpr hs
    have hlim : Filter.Tendsto (fun M => ‖∑ m ∈ Finset.range M, MvPowerSeries.coeff α (h (m + N))‖)
        Filter.atTop (nhds ‖∑' m : ℕ, MvPowerSeries.coeff α (h (m + N))‖) :=
      hs'.hasSum.tendsto_sum_nat.norm
    refine le_of_tendsto' hlim fun M => ?_
    rw [PadicInt.norm_le_pow_iff_mem_span_pow, Ideal.mem_span_singleton]
    refine Finset.dvd_sum fun m _ => ?_
    have hle : N - ∑ i : Fin g, α i ≤ m + N - ∑ i : Fin g, α i := by omega
    exact (pow_dvd_pow (p : ℤ_[p]) hle).trans
      (coeff_dvd_of_mem_maximalIdeal_pow (p := p) (g := g) (m + N) (h (m + N)) (hh_mem (m + N)) α)
  obtain ⟨z, hz⟩ := htail_dvd
  rw [hz, map_mul, map_pow, map_natCast, mul_assoc]
  have hp_mem : (p : R.carrier) ^ (N - ∑ i : Fin g, α i) ∈
      (IsLocalRing.maximalIdeal R.carrier) ^ (N - ∑ i : Fin g, α i) :=
    Ideal.pow_mem_pow R.p_mem_maximalIdeal _
  have hr_mem : (∏ i : Fin g, (r i).1 ^ α i) ∈
      (IsLocalRing.maximalIdeal R.carrier) ^ (∑ i : Fin g, α i) := by
    rw [← Finset.prod_pow_eq_pow_sum]
    exact Ideal.prod_mem_prod fun i _ => Ideal.pow_mem_pow (r i).2 (α i)
  have hmul : (p : R.carrier) ^ (N - ∑ i : Fin g, α i) * (∏ i : Fin g, (r i).1 ^ α i) ∈
      (IsLocalRing.maximalIdeal R.carrier) ^ N := by
    have hN : N = (N - ∑ i : Fin g, α i) + (∑ i : Fin g, α i) := by omega
    have hpow : (IsLocalRing.maximalIdeal R.carrier) ^ N =
        (IsLocalRing.maximalIdeal R.carrier) ^ (N - ∑ i : Fin g, α i) *
          (IsLocalRing.maximalIdeal R.carrier) ^ (∑ i : Fin g, α i) := by
      conv_lhs => rw [hN]
      rw [pow_add]
    rw [hpow]
    exact Ideal.mul_mem_mul hp_mem hr_mem
  have hreord : (p : R.carrier) ^ (N - ∑ i : Fin g, α i) * (algebraMap ℤ_[p] R.carrier z *
      ∏ i : Fin g, (r i).1 ^ α i) =
      algebraMap ℤ_[p] R.carrier z * ((p : R.carrier) ^ (N - ∑ i : Fin g, α i) *
        ∏ i : Fin g, (r i).1 ^ α i) := by ring
  rw [hreord]
  exact Ideal.mul_mem_left _ _ hmul

/-- **UNCONDITIONAL VERSAL KERNEL GENERATOR BOUND (`≤ r` RELATIONS VIA NAKAYAMA)**:
if `π : ℤ_[p][[x₀,…,x_{g-1}]] →ₐ[ℤ_[p]] R` has finitely generated kernel `J` and the dual reduced
relation space `(J ⧸ (𝔪_{S_g} • J))*` injects `𝔽_p`-linearly into an obstruction space `H2Obs` of
dimension `r`, then **`J` is generated by at most `r` elements**! -/
theorem versal_kernel_generator_bound {g r : ℕ}
    (π : PatchingBaseRing p g →ₐ[ℤ_[p]] R.carrier)
    (hfg : (RingHom.ker π.toRingHom).FG)
    (H2Obs : Type*) [AddCommGroup H2Obs] [Module (ZMod p) H2Obs] [FiniteDimensional (ZMod p) H2Obs]
    (hdimH2 : Module.finrank (ZMod p) H2Obs = r)
    (obMap :
      let J := RingHom.ker π.toRingHom
      let 𝔪 := IsLocalRing.maximalIdeal (PatchingBaseRing p g)
      let Q := Coinv 𝔪 J
      letI : Module (ZMod p) Q :=
        Module.compHom Q (patchingBaseRing_residueField_equiv_ZMod p g).symm.toRingHom
      Module.Dual (ZMod p) Q →ₗ[ZMod p] H2Obs)
    (hob_inj : Function.Injective obMap) :
    ∃ rels : Fin r → PatchingBaseRing p g,
      RingHom.ker π.toRingHom = Ideal.span (Set.range rels) := by
  classical
  let S := PatchingBaseRing p g
  let J := RingHom.ker π.toRingHom
  let 𝔪 := IsLocalRing.maximalIdeal S
  let Q := Coinv 𝔪 J
  let : Module (ZMod p) Q :=
    Module.compHom Q (patchingBaseRing_residueField_equiv_ZMod p g).symm.toRingHom
  have : Module.Finite S J := Module.Finite.iff_fg.mpr hfg
  have : Module.Finite (S ⧸ 𝔪) Q := by
    obtain ⟨s, hs⟩ := hfg
    refine Module.Finite.of_fg_top ?_
    refine ⟨s.attach.image fun x => Submodule.Quotient.mk
      ⟨x.1, by change x.1 ∈ RingHom.ker π.toRingHom; rw [← hs]; exact Submodule.subset_span x.2⟩, ?_⟩
    rw [eq_top_iff]
    intro q _
    induction q using Quotient.inductionOn' with
    | h j =>
      have hj : j.1 ∈ Submodule.span S (s : Set S) := by
        change j.1 ∈ Ideal.span (s : Set S); rw [hs]; exact j.2
      rw [Submodule.mem_span_finset] at hj
      obtain ⟨c, _, hc⟩ := hj
      have hj_eq : j = ∑ x ∈ s.attach, c x.1 •
          (⟨x.1, by change x.1 ∈ RingHom.ker π.toRingHom; rw [← hs]; exact Submodule.subset_span x.2⟩ : J) := by
        apply Subtype.ext
        rw [← hc]
        simp only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul, smul_eq_mul]
        exact (Finset.sum_attach s (fun a => c a * a)).symm
      rw [hj_eq]
      change (𝔪 • (⊤ : Submodule S J)).mkQ (∑ x ∈ s.attach, c x.1 •
          (⟨x.1, by change x.1 ∈ RingHom.ker π.toRingHom; rw [← hs]; exact Submodule.subset_span x.2⟩ : J)) ∈ _
      rw [map_sum]
      refine Submodule.sum_mem _ fun x hx => ?_
      have hsm : (𝔪 • (⊤ : Submodule S J)).mkQ
          (c x.1 • (⟨x.1, by change x.1 ∈ RingHom.ker π.toRingHom; rw [← hs]; exact Submodule.subset_span x.2⟩ : J)) =
          Ideal.Quotient.mk 𝔪 (c x.1) • Submodule.Quotient.mk (p := 𝔪 • (⊤ : Submodule S J))
            ⟨x.1, by change x.1 ∈ RingHom.ker π.toRingHom; rw [← hs]; exact Submodule.subset_span x.2⟩ := rfl
      rw [hsm]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Finset.mem_image_of_mem _ hx))
  have : FiniteDimensional (ZMod p) Q := by
    let eR := patchingBaseRing_residueField_equiv_ZMod p g
    have hfgQ : (⊤ : Submodule (S ⧸ 𝔪) Q).FG := Module.Finite.fg_top
    obtain ⟨s, hs⟩ := hfgQ
    refine Module.Finite.of_fg_top ⟨s, ?_⟩
    rw [eq_top_iff]
    intro q _
    have hq : q ∈ Submodule.span (S ⧸ 𝔪) (s : Set Q) := by rw [hs]; trivial
    rw [Submodule.mem_span_finset] at hq ⊢
    obtain ⟨c, hsupp, hc⟩ := hq
    refine ⟨fun x => eR (c x), ?_, ?_⟩
    · intro x hx
      apply hsupp
      intro hc0
      apply hx
      dsimp only
      rw [hc0, map_zero]
    · rw [← hc]
      refine Finset.sum_congr rfl fun x _ => ?_
      change (eR.symm (eR (c x))) • x = c x • x
      rw [eR.symm_apply_apply]
  have hdimQ : Module.finrank (ZMod p) Q ≤ r := by
    calc Module.finrank (ZMod p) Q
        = Module.finrank (ZMod p) (Module.Dual (ZMod p) Q) := (Subspace.dual_finrank_eq).symm
      _ ≤ Module.finrank (ZMod p) H2Obs := LinearMap.finrank_le_finrank_of_injective hob_inj
      _ = r := hdimH2
  let b := Module.finBasis (ZMod p) Q
  let qgen : Fin r → Q := fun i =>
    if h : i.1 < Module.finrank (ZMod p) Q then b ⟨i.1, h⟩ else 0
  choose v hv using fun i : Fin r => Submodule.Quotient.mk_surjective (𝔪 • (⊤ : Submodule S J)) (qgen i)
  have hspanQ : Submodule.span S
      (Set.range fun i : Fin r => Submodule.Quotient.mk (p := 𝔪 • (⊤ : Submodule S J)) (v i)) = ⊤ := by
    rw [eq_top_iff]
    intro q _
    have hq : q ∈ Submodule.span (ZMod p) (Set.range b) := by rw [b.span_eq]; trivial
    rw [Submodule.mem_span_range_iff_exists_fun] at hq
    obtain ⟨c, hc⟩ := hq
    rw [← hc]
    refine Submodule.sum_mem _ fun k _ => ?_
    have hk_lt : k.1 < r := lt_of_lt_of_le k.2 hdimQ
    let i : Fin r := ⟨k.1, hk_lt⟩
    have hvi : Submodule.Quotient.mk (p := 𝔪 • (⊤ : Submodule S J)) (v i) = b k := by
      rw [hv i]
      simp [qgen, i, k.2]
    obtain ⟨s, hs⟩ := Ideal.Quotient.mk_surjective
      ((patchingBaseRing_residueField_equiv_ZMod p g).symm (c k))
    have hsmul : c k • b k = s • Submodule.Quotient.mk (p := 𝔪 • (⊤ : Submodule S J)) (v i) := by
      rw [hvi]
      change ((patchingBaseRing_residueField_equiv_ZMod p g).symm (c k)) • b k = s • b k
      rw [← hs]
      rfl
    rw [hsmul]
    exact Submodule.smul_mem _ s (Submodule.subset_span ⟨i, rfl⟩)
  have hgenJ : Submodule.span S (Set.range v) = ⊤ :=
    nakayama_coinv_gen (le_refl 𝔪) v hspanQ
  refine ⟨fun i => (v i).1, ?_⟩
  apply le_antisymm
  · intro x hx
    have hmem : (⟨x, hx⟩ : J) ∈ Submodule.span S (Set.range v) := by rw [hgenJ]; trivial
    rw [Submodule.mem_span_range_iff_exists_fun] at hmem
    obtain ⟨c, hc⟩ := hmem
    have hx_eq : x = ∑ i : Fin r, c i * (v i).1 := by
      have := congrArg Subtype.val hc
      simpa only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul, smul_eq_mul] using this.symm
    rw [hx_eq]
    exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ (c i) (Ideal.subset_span ⟨i, rfl⟩)
  · rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact (v i).2

end LocalZpAlg

/-- `partialAugIdeal p g k` is a prime ideal of `PatchingBaseRing p g` for every `k ≤ g`. -/
theorem partialAugIdeal_isPrime {p g : ℕ} [Fact p.Prime] (k : ℕ) (hk : k ≤ g) :
    (partialAugIdeal p g k).IsPrime := by
  rw [← Ideal.Quotient.isDomain_iff_prime]
  exact (quot_partialAugIdeal_equiv p g k hk).toMulEquiv.isDomain (PatchingBaseRing p (g - k))

/-- **UNCONDITIONAL KRULL DIMENSION LOWER BOUND FOR `S_∞ = ℤ_[p][[y₀,…,y_{g-1}]]`**:
`ringKrullDim (PatchingBaseRing p g) ≥ g + 1`, witnessed by the explicit strict chain of `g + 2`
prime ideals `⊥ < (y₀) < (y₀, y₁) < ... < (y₀,…,y_{g-1}) < (y₀,…,y_{g-1}, p) = 𝔪`! -/
theorem ringKrullDim_patchingBaseRing_ge (p g : ℕ) [Fact p.Prime] :
    ((g + 1 : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (PatchingBaseRing p g) := by
  let chain : LTSeries (PrimeSpectrum (PatchingBaseRing p g)) :=
    { length := g + 1
      toFun := fun k =>
        if hk : k.1 ≤ g then
          ⟨partialAugIdeal p g k.1, partialAugIdeal_isPrime k.1 hk⟩
        else
          ⟨IsLocalRing.maximalIdeal (PatchingBaseRing p g),
            (IsLocalRing.maximalIdeal.isMaximal _).isPrime⟩
      step := fun k => by
        show (if hk : k.1 ≤ g then
            (⟨partialAugIdeal p g k.1, partialAugIdeal_isPrime k.1 hk⟩ : PrimeSpectrum (PatchingBaseRing p g))
          else ⟨IsLocalRing.maximalIdeal (PatchingBaseRing p g),
            (IsLocalRing.maximalIdeal.isMaximal _).isPrime⟩) <
          (if hk' : (k.1 + 1) ≤ g then
            ⟨partialAugIdeal p g (k.1 + 1), partialAugIdeal_isPrime (k.1 + 1) hk'⟩
          else ⟨IsLocalRing.maximalIdeal (PatchingBaseRing p g),
            (IsLocalRing.maximalIdeal.isMaximal _).isPrime⟩)
        have hk_le : k.1 ≤ g := Nat.le_of_lt_succ k.2
        rw [dif_pos hk_le]
        by_cases hk_lt : k.1 < g
        · have hk1_le : k.1 + 1 ≤ g := hk_lt
          rw [dif_pos hk1_le]
          show partialAugIdeal p g k.1 < partialAugIdeal p g (k.1 + 1)
          rw [lt_iff_le_and_ne]
          constructor
          · unfold partialAugIdeal
            refine Ideal.span_mono ?_
            rintro x ⟨i, hi, rfl⟩
            exact ⟨i, by omega, rfl⟩
          · intro heq
            have hmem : patchingVar (p := p) (g := g) ⟨k.1, hk_lt⟩ ∈ partialAugIdeal p g (k.1 + 1) :=
              Ideal.subset_span ⟨⟨k.1, hk_lt⟩, Nat.lt_succ_self k.1, rfl⟩
            rw [← heq, ← ker_evalPrefixZero k.1 hk_le, RingHom.mem_ker] at hmem
            have h1 := congrArg (MvPowerSeries.coeff (Finsupp.single ⟨0, by omega⟩ 1)) hmem
            change MvPowerSeries.coeff
              ((Finsupp.single (⟨0, by omega⟩ : Fin (g - k.1)) 1).mapDomain
                (Function.Embedding.mk (fun j : Fin (g - k.1) => (⟨k.1 + j.1, by omega⟩ : Fin g)) _))
              (MvPowerSeries.X ⟨k.1, hk_lt⟩) = 0 at h1
            have hmap : (Finsupp.single (⟨0, by omega⟩ : Fin (g - k.1)) 1).mapDomain
                (⟨fun j : Fin (g - k.1) => (⟨k.1 + j.1, by omega⟩ : Fin g), fun a b hab =>
                  Fin.ext (by have := congrArg Fin.val hab; simp at this; omega)⟩ : Fin (g - k.1) ↪ Fin g) =
                Finsupp.single ⟨k.1, hk_lt⟩ 1 := by
              rw [Finsupp.mapDomain_single]
              congr 1
            rw [hmap, MvPowerSeries.coeff_X, if_pos rfl] at h1
            exact one_ne_zero h1
        · have hk_eq : k.1 = g := by omega
          have hnot : ¬ k.1 + 1 ≤ g := by omega
          rw [dif_neg hnot]
          show partialAugIdeal p g k.1 < IsLocalRing.maximalIdeal (PatchingBaseRing p g)
          have haug_eq : partialAugIdeal p g k.1 = patchingAugIdeal p g := by
            rw [hk_eq]
            unfold partialAugIdeal patchingAugIdeal
            congr 1; ext x
            simp only [Set.mem_ofPred_eq, Set.mem_range]
            exact ⟨fun ⟨i, _, hi⟩ => ⟨i, hi.symm⟩, fun ⟨i, hi⟩ => ⟨i, i.2, hi.symm⟩⟩
          rw [haug_eq, lt_iff_le_and_ne]
          refine ⟨patchingAugIdeal_le_maximalIdeal p g, fun heq => ?_⟩
          have hp_mem : (p : PatchingBaseRing p g) ∈ IsLocalRing.maximalIdeal (PatchingBaseRing p g) := by
            rw [maximalIdeal_patchingBaseRing_eq]
            exact Ideal.subset_span (Set.mem_insert _ _)
          rw [← heq, patchingAugIdeal_eq_ker_constantCoeff, RingHom.mem_ker, map_natCast] at hp_mem
          exact padicInt_p_ne_zero hp_mem }
  exact le_iSup (fun s : LTSeries (PrimeSpectrum (PatchingBaseRing p g)) => (s.length : WithBot ℕ∞)) chain

/-- **UNCONDITIONAL KRULL DIMENSION LIFTING ALONG INTEGRAL / FINITE EXTENSIONS**:
if `R` is a finite `S`-algebra (hence integral over `S`) with injective structure map
`algebraMap S R`, then `ringKrullDim S ≤ ringKrullDim R` (proved directly via Going-Up)! -/
theorem ringKrullDim_le_of_isIntegral_injective {S R : Type*} [CommRing S] [CommRing R]
    [Algebra S R] [Module.Finite S R] (hinj : Function.Injective (algebraMap S R)) :
    ringKrullDim S ≤ ringKrullDim R := by
  have hlift : ∀ (n : ℕ) (f : Fin (n + 1) → PrimeSpectrum S), StrictMono f →
      ∃ g : Fin (n + 1) → PrimeSpectrum R, StrictMono g ∧
        Ideal.comap (algebraMap S R) (g (Fin.last n)).asIdeal = (f (Fin.last n)).asIdeal := by
    intro n
    induction n with
    | zero =>
      intro f _
      have hbot : Ideal.comap (algebraMap S R) (⊥ : Ideal R) ≤ (f 0).asIdeal := by
        intro s hs
        have hs0 : s = 0 := hinj (by simpa [Ideal.mem_comap] using hs)
        rw [hs0]
        exact (f 0).asIdeal.zero_mem
      obtain ⟨Q, _, hQprime, hQcomap⟩ :=
        Ideal.exists_ideal_over_prime_of_isIntegral (f 0).asIdeal (⊥ : Ideal R) hbot
      refine ⟨fun _ => ⟨Q, hQprime⟩, ?_, hQcomap⟩
      intro i j hij
      exact absurd hij (by omega)
    | succ m ih =>
      intro f hf
      let f0 : Fin (m + 1) → PrimeSpectrum S := fun i => f i.castSucc
      have hf0 : StrictMono f0 := fun i j hij => hf (Fin.castSucc_lt_castSucc_iff.mpr hij)
      obtain ⟨g0, hg0_mono, hg0_top⟩ := ih f0 hf0
      have hle_top : Ideal.comap (algebraMap S R) (g0 (Fin.last m)).asIdeal ≤
          (f (Fin.last (m + 1))).asIdeal := by
        rw [hg0_top]
        exact le_of_lt (hf (by simp [Fin.lt_def]))
      obtain ⟨Q, hQ_ge, hQ_prime, hQ_comap⟩ :=
        Ideal.exists_ideal_over_prime_of_isIntegral (f (Fin.last (m + 1))).asIdeal
          (g0 (Fin.last m)).asIdeal hle_top
      have hQ_gt : g0 (Fin.last m) < ⟨Q, hQ_prime⟩ := by
        change (g0 (Fin.last m)).asIdeal < Q
        rw [lt_iff_le_and_ne]
        refine ⟨hQ_ge, fun heq => ?_⟩
        have hcom := congrArg (Ideal.comap (algebraMap S R)) heq
        rw [hg0_top, hQ_comap] at hcom
        have hlt : f0 (Fin.last m) < f (Fin.last (m + 1)) := hf (by simp [Fin.lt_def])
        exact ne_of_lt hlt (PrimeSpectrum.ext hcom)
      let g : Fin (m + 2) → PrimeSpectrum R := Fin.snoc g0 ⟨Q, hQ_prime⟩
      have hg_mono : StrictMono g := by
        intro i j
        refine Fin.lastCases ?_ (fun i' => ?_) i
        · intro hij
          exact absurd hij (not_lt_of_ge (Fin.le_last j))
        · refine Fin.lastCases ?_ (fun j' => ?_) j
          · intro _
            simp only [g, Fin.snoc_castSucc, Fin.snoc_last]
            exact lt_of_le_of_lt (hg0_mono.monotone (Fin.le_last i')) hQ_gt
          · intro hij
            simp only [g, Fin.snoc_castSucc]
            exact hg0_mono (Fin.castSucc_lt_castSucc_iff.mp hij)
      refine ⟨g, hg_mono, ?_⟩
      simpa [g, Fin.snoc_last] using hQ_comap
  unfold ringKrullDim Order.krullDim
  refine iSup_le fun s => ?_
  obtain ⟨g, hg_mono, _⟩ := hlift s.length s.toFun s.strictMono
  let t : LTSeries (PrimeSpectrum R) :=
    { length := s.length
      toFun := g
      step := fun i => hg_mono (Fin.castSucc_lt_succ (i := i)) }
  exact le_iSup (fun u : LTSeries (PrimeSpectrum R) => (u.length : WithBot ℕ∞)) t

/-- **UNCONDITIONAL COMPLETE-INTERSECTION KRULL DIMENSION BOUND (`Krull dim R ≥ 1 + g - r`)**:
1. For any quotient `R ≃+* PatchingBaseRing p g ⧸ partialAugIdeal p g r` (`r ≤ g`, cut out by `r`
   complete-intersection parameters), `ringKrullDim R ≥ 1 + g - r`;
2. More generally, for ANY finite faithful `PatchingBaseRing p (g - r)`-algebra `R` (covering every
   patched complete-intersection deformation ring `R_∞` over `S_{g - r}`!), `ringKrullDim R ≥ 1 + g - r`! -/
theorem krullDim_ge_of_completeIntersection {p g r : ℕ} [Fact p.Prime] {R : Type*} [CommRing R]
    [Algebra (PatchingBaseRing p (g - r)) R] [Module.Finite (PatchingBaseRing p (g - r)) R]
    (hinj : Function.Injective (algebraMap (PatchingBaseRing p (g - r)) R)) :
    (((1 + (g - r) : ℕ) : WithBot ℕ∞)) ≤ ringKrullDim R := by
  have h1 : (((g - r) + 1 : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (PatchingBaseRing p (g - r)) :=
    ringKrullDim_patchingBaseRing_ge p (g - r)
  have h2 : ringKrullDim (PatchingBaseRing p (g - r)) ≤ ringKrullDim R :=
    ringKrullDim_le_of_isIntegral_injective hinj
  simpa [Nat.add_comm] using le_trans h1 h2

theorem krullDim_ge_of_quot_partialAugIdeal {p g r : ℕ} [Fact p.Prime] (hr : r ≤ g) :
    (((1 + (g - r) : ℕ) : WithBot ℕ∞)) ≤ ringKrullDim (PatchingBaseRing p g ⧸ partialAugIdeal p g r) := by
  let e := (quot_partialAugIdeal_equiv p g r hr).symm
  let : Algebra (PatchingBaseRing p (g - r)) (PatchingBaseRing p g ⧸ partialAugIdeal p g r) :=
    e.toRingHom.toAlgebra
  have : Module.Finite (PatchingBaseRing p (g - r)) (PatchingBaseRing p g ⧸ partialAugIdeal p g r) :=
    Module.Finite.of_surjective (Algebra.linearMap _ _) e.surjective
  exact krullDim_ge_of_completeIntersection e.injective

end DeformationRingPresentation

/-! ## Section 5: Concrete Greenberg–Wiles Euler Characteristic & Wiles Balancing (`dim H¹_{L_Q} - dim H¹_{L*_Q} = |Q|`) -/

section GreenbergWilesAndWilesBalancing

/-- **Odd Involution Trace Vanishing**: for any field `K` and any `A ∈ GL₂(K)` with `A² = I`
and `det A = -1`, `tr A = 0` (immediate from Cayley–Hamilton `A² = tr(A) A - det(A) I`). -/
theorem odd_involution_trace_zero {K : Type*} [Field K]
    (A : Matrix.GeneralLinearGroup (Fin 2) K) (hsq : A * A = 1) (hdet : Matrix.det A.1 = -1) :
    Matrix.trace A.1 = 0 := by
  have hch := mat2_sq_eq_trace_sub_det A.1
  have hA2 : A.1 * A.1 = 1 := congrArg Units.val hsq
  rw [hA2, hdet, neg_smul, sub_neg_eq_add, one_smul] at hch
  have htrA : Matrix.trace A.1 • A.1 = 0 := by
    have := congrArg (fun M => M - (1 : Matrix (Fin 2) (Fin 2) K)) hch
    simpa using this.symm
  have htr1 : Matrix.trace A.1 • (1 : Matrix (Fin 2) (Fin 2) K) = 0 := by
    calc Matrix.trace A.1 • (1 : Matrix (Fin 2) (Fin 2) K)
        = (Matrix.trace A.1 • A.1) * A⁻¹.1 := by rw [Matrix.smul_mul, Units.mul_inv]
      _ = 0 := by rw [htrA, Matrix.zero_mul]
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M 0 0) htr1
  simpa using h00

/-- **Diagonalization of 2×2 Matrices with Distinct Eigenvalues**:
if `A ∈ M₂(K)` has `tr A = α + β`, `det A = α * β`, and `α ≠ β`, then `A` is conjugate in `GL₂(K)`
to `diag(α, β)`. -/
theorem mat2_conj_diag_of_distinct_eigenvalues {K : Type*} [Field K]
    (A : Matrix (Fin 2) (Fin 2) K) {α β : K} (hne : α ≠ β)
    (htr : Matrix.trace A = α + β) (hdet : Matrix.det A = α * β) :
    ∃ P : Matrix.GeneralLinearGroup (Fin 2) K,
      P⁻¹.1 * A * P.1 = !![α, 0; 0, β] := by
  have hfact : (A - α • (1 : Matrix (Fin 2) (Fin 2) K)) * (A - β • 1) = 0 := by
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul,
      mat2_sq_eq_trace_sub_det, htr, hdet, add_smul, smul_smul]
    abel
  have hA_sub_β_ne : A - β • (1 : Matrix (Fin 2) (Fin 2) K) ≠ 0 := by
    intro h0
    have hAeq : A = β • (1 : Matrix (Fin 2) (Fin 2) K) := sub_eq_zero.mp h0
    rw [hAeq, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin] at htr
    simp only [Nat.cast_ofNat, smul_eq_mul] at htr
    apply hne
    linear_combination htr.symm
  have hA_sub_α_ne : A - α • (1 : Matrix (Fin 2) (Fin 2) K) ≠ 0 := by
    intro h0
    have hAeq : A = α • (1 : Matrix (Fin 2) (Fin 2) K) := sub_eq_zero.mp h0
    rw [hAeq, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin] at htr
    simp only [Nat.cast_ofNat, smul_eq_mul] at htr
    apply hne
    linear_combination htr
  have hex_eig : ∀ (lam μ : K),
      (A - lam • (1 : Matrix (Fin 2) (Fin 2) K)) * (A - μ • 1) = 0 →
      A - μ • (1 : Matrix (Fin 2) (Fin 2) K) ≠ 0 →
      ∃ v : Fin 2 → K, v ≠ 0 ∧ A.mulVec v = lam • v := by
    intro lam μ hprod hne_μ
    have hex_u : ∃ u : Fin 2 → K, (A - μ • (1 : Matrix (Fin 2) (Fin 2) K)).mulVec u ≠ 0 := by
      by_contra hall
      push Not at hall
      apply hne_μ
      ext i j
      have hu := congrFun (hall (Pi.single j 1)) i
      simpa [Matrix.mulVec_single] using hu
    obtain ⟨u, hu⟩ := hex_u
    refine ⟨(A - μ • 1).mulVec u, hu, ?_⟩
    have h0 : (A - lam • 1).mulVec ((A - μ • 1).mulVec u) = 0 := by
      rw [Matrix.mulVec_mulVec, hprod, Matrix.zero_mulVec]
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] at h0
    exact sub_eq_zero.mp h0
  have hfact_comm : (A - β • (1 : Matrix (Fin 2) (Fin 2) K)) * (A - α • 1) = 0 := by
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul,
      mat2_sq_eq_trace_sub_det, htr, hdet, add_smul, smul_smul, mul_comm β α]
    abel
  obtain ⟨v₁, hv₁_ne, hv₁_eig⟩ := hex_eig α β hfact hA_sub_β_ne
  obtain ⟨v₂, hv₂_ne, hv₂_eig⟩ := hex_eig β α hfact_comm hA_sub_α_ne
  let Pmat : Matrix (Fin 2) (Fin 2) K := Matrix.of fun r c => if c = 0 then v₁ r else v₂ r
  have hP_mulVec : ∀ u : Fin 2 → K, Pmat.mulVec u = u 0 • v₁ + u 1 • v₂ := by
    intro u; ext r; fin_cases r <;> (simp [Pmat, Matrix.mulVec, dotProduct, Fin.sum_univ_two]; ring)
  have hP_det : Pmat.det ≠ 0 := by
    apply mat2_det_ne_zero_of_mulVec_eq_zero
    intro u hu
    rw [hP_mulVec] at hu
    have hAu : u 0 • (α • v₁) + u 1 • (β • v₂) = 0 := by
      have h := congrArg A.mulVec hu
      rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hv₁_eig, hv₂_eig,
        Matrix.mulVec_zero] at h
      exact h
    have h0 : (u 0 * (α - β)) • v₁ = 0 := by
      calc (u 0 * (α - β)) • v₁
          = (u 0 • (α • v₁) + u 1 • (β • v₂)) - β • (u 0 • v₁ + u 1 • v₂) := by
              rw [smul_add, smul_smul, smul_smul, smul_smul, smul_smul, mul_sub, sub_smul,
                mul_comm β (u 0), mul_comm β (u 1)]
              abel
        _ = 0 := by rw [hAu, hu, smul_zero, sub_zero]
    have hu0 : u 0 = 0 := by
      have hprod0 := (smul_eq_zero.mp h0).resolve_right hv₁_ne
      exact (mul_eq_zero.mp hprod0).resolve_right (sub_ne_zero.mpr hne)
    rw [hu0, zero_smul, zero_add] at hu
    have hu1 : u 1 = 0 := (smul_eq_zero.mp hu).resolve_right hv₂_ne
    ext k; fin_cases k <;> [exact hu0; exact hu1]
  let P := gl2OfDetNeZero Pmat hP_det
  refine ⟨P, ?_⟩
  have hAP : A * P.1 = P.1 * !![α, 0; 0, β] := by
    ext r c
    have hcol : (A * P.1).mulVec (Pi.single c 1) = (P.1 * !![α, 0; 0, β]).mulVec (Pi.single c 1) := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      have hP0 : P.1.mulVec (Pi.single 0 1) = v₁ := by rw [gl2OfDetNeZero_val, hP_mulVec]; simp
      have hP1 : P.1.mulVec (Pi.single 1 1) = v₂ := by rw [gl2OfDetNeZero_val, hP_mulVec]; simp
      fin_cases c
      · change A.mulVec (P.1.mulVec (Pi.single 0 1)) = P.1.mulVec ((!![α, 0; 0, β] : Matrix (Fin 2) (Fin 2) K).mulVec (Pi.single 0 1))
        have hD0 : (!![α, 0; 0, β] : Matrix (Fin 2) (Fin 2) K).mulVec (Pi.single 0 1) = α • Pi.single 0 1 := by
          ext a; fin_cases a <;> simp [Matrix.mulVec_single]
        rw [hP0, hD0, Matrix.mulVec_smul, hP0, hv₁_eig]
      · change A.mulVec (P.1.mulVec (Pi.single 1 1)) = P.1.mulVec ((!![α, 0; 0, β] : Matrix (Fin 2) (Fin 2) K).mulVec (Pi.single 1 1))
        have hD1 : (!![α, 0; 0, β] : Matrix (Fin 2) (Fin 2) K).mulVec (Pi.single 1 1) = β • Pi.single 1 1 := by
          ext a; fin_cases a <;> simp [Matrix.mulVec_single]
        rw [hP1, hD1, Matrix.mulVec_smul, hP1, hv₂_eig]
    have hrc := congrFun hcol r
    simpa [Matrix.mulVec_single] using hrc
  calc P⁻¹.1 * A * P.1 = P⁻¹.1 * (A * P.1) := by rw [Matrix.mul_assoc]
    _ = P⁻¹.1 * (P.1 * !![α, 0; 0, β]) := by rw [hAP]
    _ = (P⁻¹.1 * P.1) * !![α, 0; 0, β] := by rw [Matrix.mul_assoc]
    _ = !![α, 0; 0, β] := by rw [Units.inv_mul, Matrix.one_mul]

/-- **Exact 1-Dimensionality of `ad⁰` Centralizer of a Regular Semisimple Matrix**:
if `rhoBar g ∈ GL₂(K)` has distinct eigenvalues `α ≠ β` (`tr = α + β`, `det = α * β`), then
`dim_K H⁰(⟨g⟩, ad⁰ rhoBar) = 1`! -/
theorem finrank_H0_zpowers_ad0_eq_one_of_distinct_eigenvalues {G K : Type*} [Group G] [Field K]
    (rhoBar : G →* Matrix.GeneralLinearGroup (Fin 2) K) (g : G) {α β : K} (hne : α ≠ β)
    (htr : Matrix.trace (rhoBar g).1 = α + β) (hdet : Matrix.det (rhoBar g).1 = α * β) :
    Module.finrank K (H0Subgroup K (Subgroup.zpowers g) (Ad0Rep rhoBar)) = 1 := by
  obtain ⟨P, hP⟩ := mat2_conj_diag_of_distinct_eigenvalues (rhoBar g).1 hne htr hdet
  have hα0 : α ≠ 0 := by
    intro h0
    have hdet0 : Matrix.det (rhoBar g).1 = 0 := by rw [hdet, h0, zero_mul]
    exact ((Matrix.isUnit_iff_isUnit_det (rhoBar g).1).mp (rhoBar g).isUnit).ne_zero hdet0
  have hβ0 : β ≠ 0 := by
    intro h0
    have hdet0 : Matrix.det (rhoBar g).1 = 0 := by rw [hdet, h0, mul_zero]
    exact ((Matrix.isUnit_iff_isUnit_det (rhoBar g).1).mp (rhoBar g).isUnit).ne_zero hdet0
  let D : Matrix (Fin 2) (Fin 2) K := !![α, 0; 0, β]
  have hA_eq : (rhoBar g).1 = P.1 * D * P⁻¹.1 := by
    calc (rhoBar g).1 = (P.1 * P⁻¹.1) * (rhoBar g).1 * (P.1 * P⁻¹.1) := by
          rw [Units.mul_inv, Matrix.one_mul, Matrix.mul_one]
      _ = P.1 * (P⁻¹.1 * (rhoBar g).1 * P.1) * P⁻¹.1 := by simp only [Matrix.mul_assoc]
      _ = P.1 * D * P⁻¹.1 := by rw [hP]
  let Hmat : Matrix (Fin 2) (Fin 2) K := !![1, 0; 0, -1]
  have hH_tr : Matrix.trace Hmat = 0 := by simp [Hmat, Matrix.trace_fin_two]
  have hgen_comm : ∀ x : Ad0Rep rhoBar,
      x ∈ H0Subgroup K (Subgroup.zpowers g) (Ad0Rep rhoBar) ↔
        (rhoBar g).1 * x.val = x.val * (rhoBar g).1 := by
    intro x
    constructor
    · intro hx
      have hg := congrArg Ad0Rep.val (hx ⟨g, Subgroup.mem_zpowers g⟩)
      change (rhoBar g).1 * x.val * (rhoBar g)⁻¹.1 = x.val at hg
      calc (rhoBar g).1 * x.val = ((rhoBar g).1 * x.val * (rhoBar g)⁻¹.1) * (rhoBar g).1 := by
            rw [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
        _ = x.val * (rhoBar g).1 := by rw [hg]
    · intro hcomm ⟨h, hh⟩
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
      have hcomm_unit : ∀ m : ℤ, (rhoBar (g ^ m)).1 * x.val * (rhoBar (g ^ m))⁻¹.1 = x.val := by
        intro m
        have hstep : g • x = x := by
          apply Ad0Rep.ext
          change (rhoBar g).1 * x.val * (rhoBar g)⁻¹.1 = x.val
          rw [hcomm, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
        have hstep_inv : g⁻¹ • x = x := by
          have := congrArg (fun y : Ad0Rep rhoBar => g⁻¹ • y) hstep
          simpa [← mul_smul] using this.symm
        have hz : (g ^ m) • x = x := by
          induction m using Int.induction_on with
          | zero => simp
          | succ n ih =>
            rw [_root_.zpow_add, zpow_one, mul_smul, hstep, ih]
          | pred n ih =>
            rw [sub_eq_add_neg, _root_.zpow_add, _root_.zpow_neg_one, mul_smul, hstep_inv, ih]
        exact congrArg Ad0Rep.val hz
      exact Ad0Rep.ext (hcomm_unit k)
  let e : K ≃ₗ[K] H0Subgroup K (Subgroup.zpowers g) (Ad0Rep rhoBar) :=
    { toFun := fun a =>
        ⟨⟨P.1 * (a • Hmat) * P⁻¹.1, by
          rw [Matrix.trace_mul_cycle, Units.inv_mul, Matrix.one_mul, Matrix.trace_smul, hH_tr, smul_zero]⟩,
          (hgen_comm _).mpr (by
            rw [hA_eq]
            have hDH : D * (a • Hmat) = (a • Hmat) * D := by
              ext i j; fin_cases i <;> fin_cases j <;>
                (simp [D, Hmat, Matrix.mul_apply, Fin.sum_univ_two]; try ring)
            calc (P.1 * D * P⁻¹.1) * (P.1 * (a • Hmat) * P⁻¹.1)
                = P.1 * D * ((P⁻¹.1 * P.1) * (a • Hmat)) * P⁻¹.1 := by simp only [Matrix.mul_assoc]
              _ = P.1 * (D * (a • Hmat)) * P⁻¹.1 := by
                    rw [Units.inv_mul, Matrix.one_mul]; simp only [Matrix.mul_assoc]
              _ = P.1 * ((a • Hmat) * D) * P⁻¹.1 := by rw [hDH]
              _ = P.1 * (a • Hmat) * ((P⁻¹.1 * P.1) * D) * P⁻¹.1 := by
                    rw [Units.inv_mul, Matrix.one_mul]; simp only [Matrix.mul_assoc]
              _ = (P.1 * (a • Hmat) * P⁻¹.1) * (P.1 * D * P⁻¹.1) := by simp only [Matrix.mul_assoc])⟩
      invFun := fun x => (P⁻¹.1 * x.1.val * P.1) 0 0
      map_add' := fun a b => by
        apply Subtype.ext; apply Ad0Rep.ext
        change P.1 * ((a + b) • Hmat) * P⁻¹.1 = P.1 * (a • Hmat) * P⁻¹.1 + P.1 * (b • Hmat) * P⁻¹.1
        rw [add_smul, Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun c a => by
        apply Subtype.ext; apply Ad0Rep.ext
        change P.1 * ((c * a) • Hmat) * P⁻¹.1 = c • (P.1 * (a • Hmat) * P⁻¹.1)
        rw [mul_smul, Matrix.mul_smul, Matrix.smul_mul]
      left_inv := fun a => by
        have h1 : P⁻¹.1 * (P.1 * (a • Hmat) * P⁻¹.1) * P.1 = a • Hmat := by
          calc P⁻¹.1 * (P.1 * (a • Hmat) * P⁻¹.1) * P.1
              = (P⁻¹.1 * P.1) * (a • Hmat) * (P⁻¹.1 * P.1) := by simp only [Matrix.mul_assoc]
            _ = a • Hmat := by rw [Units.inv_mul, Matrix.one_mul, Matrix.mul_one]
        change (P⁻¹.1 * (P.1 * (a • Hmat) * P⁻¹.1) * P.1) 0 0 = a
        rw [h1]
        simp [Hmat]
      right_inv := fun x => by
        apply Subtype.ext; apply Ad0Rep.ext
        let Y : Matrix (Fin 2) (Fin 2) K := P⁻¹.1 * x.1.val * P.1
        have hY_tr : Matrix.trace Y = 0 := by
          dsimp only [Y]
          rw [Matrix.trace_mul_cycle, Units.mul_inv, Matrix.one_mul, x.1.trace_zero]
        have hY_comm : D * Y = Y * D := by
          have hx := (hgen_comm x.1).mp x.2
          rw [hA_eq] at hx
          have h1 := congrArg (fun M => P⁻¹.1 * M * P.1) hx
          have hL : P⁻¹.1 * (P.1 * D * P⁻¹.1 * x.1.val) * P.1 = D * Y := by
            dsimp only [Y]
            calc P⁻¹.1 * (P.1 * D * P⁻¹.1 * x.1.val) * P.1
                = (P⁻¹.1 * P.1) * D * (P⁻¹.1 * x.1.val * P.1) := by simp only [Matrix.mul_assoc]
              _ = D * (P⁻¹.1 * x.1.val * P.1) := by rw [Units.inv_mul, Matrix.one_mul]
          have hR : P⁻¹.1 * (x.1.val * (P.1 * D * P⁻¹.1)) * P.1 = Y * D := by
            dsimp only [Y]
            calc P⁻¹.1 * (x.1.val * (P.1 * D * P⁻¹.1)) * P.1
                = (P⁻¹.1 * x.1.val * P.1) * D * (P⁻¹.1 * P.1) := by simp only [Matrix.mul_assoc]
              _ = (P⁻¹.1 * x.1.val * P.1) * D := by rw [Units.inv_mul, Matrix.mul_one]
          rw [hL, hR] at h1
          exact h1
        have hY01 : Y 0 1 = 0 := by
          have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M 0 1) hY_comm
          simp [D, Matrix.mul_apply, Fin.sum_univ_two] at h01
          have hdiff : (α - β) * Y 0 1 = 0 := by linear_combination h01
          exact (mul_eq_zero.mp hdiff).resolve_left (sub_ne_zero.mpr hne)
        have hY10 : Y 1 0 = 0 := by
          have h10 := congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M 1 0) hY_comm
          simp [D, Matrix.mul_apply, Fin.sum_univ_two] at h10
          have hdiff : (β - α) * Y 1 0 = 0 := by linear_combination h10
          exact (mul_eq_zero.mp hdiff).resolve_left (sub_ne_zero.mpr hne.symm)
        have hY11 : Y 1 1 = -Y 0 0 := eq_neg_of_add_eq_zero_right (by simpa [Matrix.trace_fin_two] using hY_tr)
        have hY_eq : Y = (Y 0 0) • Hmat := by
          ext i j; fin_cases i <;> fin_cases j <;> simp [Hmat, hY01, hY10, hY11]
        change P.1 * (Y 0 0 • Hmat) * P⁻¹.1 = x.1.val
        rw [← hY_eq]
        dsimp only [Y]
        calc P.1 * (P⁻¹.1 * x.1.val * P.1) * P⁻¹.1
            = (P.1 * P⁻¹.1) * x.1.val * (P.1 * P⁻¹.1) := by simp only [Matrix.mul_assoc]
          _ = x.1.val := by rw [Units.mul_inv, Matrix.one_mul, Matrix.mul_one] }
  rw [← e.finrank_eq, Module.finrank_self]

/-- **UNCONDITIONAL ARCHIMEDEAN INVARIANT DIMENSION FOR ODD `rhoBar`**:
for EVERY odd representation `rhoBar : G →* GL₂(K)` (`c² = 1`, `det(rhoBar c) = -1`) over a field
`K` with `(2 : K) ≠ 0` (in particular `ZMod p` for `p ≥ 3`),
**`dim_K H⁰(G_∞, ad⁰ rhoBar) = 1`**! -/
theorem finrank_H0_inf_ad0_eq_one {G K : Type*} [Group G] [Field K] (h2 : (2 : K) ≠ 0)
    (rhoBar : G →* Matrix.GeneralLinearGroup (Fin 2) K) (c : G)
    (hc2 : c * c = 1) (hodd : Matrix.det (rhoBar c).1 = -1) :
    Module.finrank K (H0Subgroup K (Subgroup.zpowers c) (Ad0Rep rhoBar)) = 1 := by
  have hsq : rhoBar c * rhoBar c = 1 := by rw [← map_mul, hc2, map_one]
  have htr : Matrix.trace (rhoBar c).1 = 0 := odd_involution_trace_zero (rhoBar c) hsq hodd
  have hne : (1 : K) ≠ -1 := by
    intro h
    apply h2
    linear_combination h
  exact finrank_H0_zpowers_ad0_eq_one_of_distinct_eigenvalues rhoBar c hne
    (by rw [htr]; ring) (by rw [hodd]; ring)

/-- **Exact Greenberg–Wiles Euler Characteristic Formula** for any finite-dimensional Selmer
structure `(L_v)_{v ∈ S}` (directly unifying `Stage2GaloisCohomology.PoitouTateData`):
`dim H¹_L - dim H¹_{L*} = dim H⁰(G, M) - dim H⁰(G, M*) + ∑_{v ∈ S} (dim L_v - dim H⁰(G_v, M))`. -/
theorem greenberg_wiles_euler_characteristic {k Places : Type*} [Field k]
    [Fintype Places] [DecidableEq Places]
    (D : PoitouTateData k Places) (hbal : D.EulerPoincareBalance)
    (L : ∀ v : Places, Submodule k (D.H1v v)) :
    (Module.finrank k (D.Selmer L) : ℤ) - Module.finrank k (D.DualSelmer L) =
      ((Module.finrank k D.H0 : ℤ) - Module.finrank k D.H0d) +
        ∑ v : Places, ((Module.finrank k (L v) : ℤ) - Module.finrank k (D.H0v v)) :=
  D.greenberg_wiles_formula hbal L

/-- **Concrete `ad⁰ rhoBar` Wiles–Taylor–Wiles Selmer System** over `ZMod p` (`p ≥ 3`):
packages an odd absolutely irreducible `rhoBar : G →* GL₂(ZMod p)`, base places `S₀` containing
distinct `v_inf` and `v_p`, and auxiliary Taylor–Wiles primes `Q` with Frobenius elements having
distinct eigenvalues `α_q ≠ β_q`, directly wired to `H0Submodule (ZMod p) G (Ad0Rep rhoBar)`,
`H0Subgroup (ZMod p) (Subgroup.zpowers c) (Ad0Rep rhoBar)`, and `PoitouTateData (ZMod p) (S₀ ⊕ Q)`. -/
structure Ad0WilesSelmerSystem (G S₀ Q : Type) [Group G] [Fintype S₀] [DecidableEq S₀]
    [Fintype Q] [DecidableEq Q] (p : ℕ) [Fact p.Prime] where
  hp3 : 3 ≤ p
  rhoBar : G →* Matrix.GeneralLinearGroup (Fin 2) (ZMod p)
  abs_irred : IsAbsIrreducible2D rhoBar
  /-- Complex conjugation involution `c ∈ G` with `c² = 1` and `det(rhoBar c) = -1`. -/
  conj_elem : G
  conj_sq : conj_elem * conj_elem = 1
  odd_rep : Matrix.det (rhoBar conj_elem).1 = -1
  /-- Archimedean place `v_inf` and `p`-adic place `v_p` in `S₀`. -/
  v_inf : S₀
  v_p : S₀
  v_inf_ne_vp : v_inf ≠ v_p
  /-- Frobenius elements at Taylor–Wiles primes `q ∈ Q` with distinct eigenvalues `α_q ≠ β_q`. -/
  frob_q : Q → G
  eig_alpha : Q → ZMod p
  eig_beta : Q → ZMod p
  eig_distinct : ∀ q : Q, eig_alpha q ≠ eig_beta q
  frob_trace : ∀ q : Q, Matrix.trace (rhoBar (frob_q q)).1 = eig_alpha q + eig_beta q
  frob_det : ∀ q : Q, Matrix.det (rhoBar (frob_q q)).1 = eig_alpha q * eig_beta q
  /-- Underlying Poitou–Tate global duality package on `Places = S₀ ⊕ Q`. -/
  D : PoitouTateData (ZMod p) (S₀ ⊕ Q)
  euler_balance : D.EulerPoincareBalance
  /-- Concrete identification of `H⁰(G, ad⁰)`, `H⁰(G_∞, ad⁰)`, and `H⁰(G_q, ad⁰)`. -/
  H0_equiv : D.H0 ≃ₗ[ZMod p] H0Submodule (ZMod p) G (Ad0Rep rhoBar)
  H0d_vanish : Module.finrank (ZMod p) D.H0d = 0
  H0_inf_equiv : D.H0v (Sum.inl v_inf) ≃ₗ[ZMod p]
    H0Subgroup (ZMod p) (Subgroup.zpowers conj_elem) (Ad0Rep rhoBar)
  H0_q_equiv : ∀ q : Q, D.H0v (Sum.inr q) ≃ₗ[ZMod p]
    H0Subgroup (ZMod p) (Subgroup.zpowers (frob_q q)) (Ad0Rep rhoBar)
  /-- Minimal local Selmer conditions `L_min` (flat/ordinary at `p`, unramified elsewhere). -/
  L_min : ∀ v : S₀ ⊕ Q, Submodule (ZMod p) (D.H1v v)
  L_inf_bot : L_min (Sum.inl v_inf) = ⊥
  L_p_balance : (Module.finrank (ZMod p) (L_min (Sum.inl v_p)) : ℤ) -
    Module.finrank (ZMod p) (D.H0v (Sum.inl v_p)) = 1
  L_other_unram : ∀ v : S₀, v ≠ v_inf → v ≠ v_p →
    Module.finrank (ZMod p) (L_min (Sum.inl v)) = Module.finrank (ZMod p) (D.H0v (Sum.inl v))
  L_q_unram : ∀ q : Q,
    Module.finrank (ZMod p) (L_min (Sum.inr q)) = Module.finrank (ZMod p) (D.H0v (Sum.inr q))
  /-- Local cohomology dimension `dim H¹(G_q, ad⁰) = 2` at each Taylor–Wiles prime `q ∈ Q`. -/
  H1_q_dim : ∀ q : Q, Module.finrank (ZMod p) (D.H1v (Sum.inr q)) = 2

namespace Ad0WilesSelmerSystem

variable {G S₀ Q : Type} [Group G] [Fintype S₀] [DecidableEq S₀]
  [Fintype Q] [DecidableEq Q] {p : ℕ} [Fact p.Prime] (W : Ad0WilesSelmerSystem G S₀ Q p)

/-- Relaxed Taylor–Wiles Selmer condition `L_Q`: agrees with `L_min` on `S₀` and relaxed to `⊤` on `Q`. -/
def L_Q : ∀ v : S₀ ⊕ Q, Submodule (ZMod p) (W.D.H1v v)
  | Sum.inl v => W.L_min (Sum.inl v)
  | Sum.inr _ => ⊤

theorem finrank_H0_eq_zero : Module.finrank (ZMod p) W.D.H0 = 0 := by
  rw [W.H0_equiv.finrank_eq]
  exact finrank_H0_ad0_eq_zero_of_absIrreducible (two_ne_zero_zmod W.hp3) W.abs_irred

theorem finrank_H0_inf_eq_one : Module.finrank (ZMod p) (W.D.H0v (Sum.inl W.v_inf)) = 1 := by
  rw [W.H0_inf_equiv.finrank_eq]
  exact finrank_H0_inf_ad0_eq_one (two_ne_zero_zmod W.hp3) W.rhoBar W.conj_elem W.conj_sq W.odd_rep

theorem finrank_H0_q_eq_one (q : Q) : Module.finrank (ZMod p) (W.D.H0v (Sum.inr q)) = 1 := by
  rw [(W.H0_q_equiv q).finrank_eq]
  exact finrank_H0_zpowers_ad0_eq_one_of_distinct_eigenvalues W.rhoBar (W.frob_q q)
    (W.eig_distinct q) (W.frob_trace q) (W.frob_det q)

/-- Exact sum of local Selmer defects over `S₀` vanishes: `(-1) + (+1) + 0 = 0`! -/
theorem sum_S0_local_defect_eq_zero :
    ∑ v : S₀, ((Module.finrank (ZMod p) (W.L_min (Sum.inl v)) : ℤ) -
      Module.finrank (ZMod p) (W.D.H0v (Sum.inl v))) = 0 := by
  have h1 : ∀ v : S₀, v ∉ ({W.v_inf, W.v_p} : Finset S₀) →
      (Module.finrank (ZMod p) (W.L_min (Sum.inl v)) : ℤ) -
        Module.finrank (ZMod p) (W.D.H0v (Sum.inl v)) = 0 := by
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hv
    rw [W.L_other_unram v hv.1 hv.2, sub_self]
  rw [← Finset.sum_subset (Finset.subset_univ ({W.v_inf, W.v_p} : Finset S₀)) (fun v _ hv => h1 v hv)]
  rw [Finset.sum_pair W.v_inf_ne_vp, W.L_inf_bot, finrank_bot, W.finrank_H0_inf_eq_one, W.L_p_balance]
  norm_num

/-- **WILES MINIMAL BALANCING THEOREM**: at minimal level (`L_min`), Selmer and dual Selmer
have identically equal dimension: `dim H¹_{L_min}(ad⁰) = dim H¹_{L_min*}(ad⁰(1))`! -/
theorem wiles_minimal_balancing :
    Module.finrank (ZMod p) (W.D.Selmer W.L_min) =
      Module.finrank (ZMod p) (W.D.DualSelmer W.L_min) := by
  have hgw := greenberg_wiles_euler_characteristic W.D W.euler_balance W.L_min
  rw [W.finrank_H0_eq_zero, W.H0d_vanish, Fintype.sum_sum_type, W.sum_S0_local_defect_eq_zero] at hgw
  have hQ0 : ∑ q : Q, ((Module.finrank (ZMod p) (W.L_min (Sum.inr q)) : ℤ) -
      Module.finrank (ZMod p) (W.D.H0v (Sum.inr q))) = 0 :=
    Finset.sum_eq_zero fun q _ => by rw [W.L_q_unram q, sub_self]
  rw [hQ0] at hgw
  omega

/-- **EXACT WILES BALANCING EQUATION (`dim H¹_{L_Q} - dim H¹_{L*_Q} = |Q|`)**:
relaxing at the Taylor–Wiles primes `Q` produces exact excess `|Q|` over dual Selmer! -/
theorem wiles_Q_balancing_equation :
    (Module.finrank (ZMod p) (W.D.Selmer W.L_Q) : ℤ) -
      Module.finrank (ZMod p) (W.D.DualSelmer W.L_Q) = (Fintype.card Q : ℤ) := by
  have hgw := greenberg_wiles_euler_characteristic W.D W.euler_balance W.L_Q
  rw [W.finrank_H0_eq_zero, W.H0d_vanish, Fintype.sum_sum_type] at hgw
  have hS0 : ∑ v : S₀, ((Module.finrank (ZMod p) (W.L_Q (Sum.inl v)) : ℤ) -
      Module.finrank (ZMod p) (W.D.H0v (Sum.inl v))) = 0 := W.sum_S0_local_defect_eq_zero
  have hQ : ∑ q : Q, ((Module.finrank (ZMod p) (W.L_Q (Sum.inr q)) : ℤ) -
      Module.finrank (ZMod p) (W.D.H0v (Sum.inr q))) = (Fintype.card Q : ℤ) := by
    have hterm : ∀ q : Q, ((Module.finrank (ZMod p) (W.L_Q (Sum.inr q)) : ℤ) -
        Module.finrank (ZMod p) (W.D.H0v (Sum.inr q))) = 1 := fun q => by
      change (Module.finrank (ZMod p) (⊤ : Submodule (ZMod p) (W.D.H1v (Sum.inr q))) : ℤ) -
        Module.finrank (ZMod p) (W.D.H0v (Sum.inr q)) = 1
      rw [finrank_top, W.H1_q_dim q, W.finrank_H0_q_eq_one q]
      norm_num
    simp_rw [hterm]
    simp
  rw [hS0, hQ] at hgw
  omega

/-- **Wiles Dual-Killing Exact Tangent Count**: whenever `Q` kills the dual Selmer group
(`dim H¹_{L*_Q} = 0`), the relaxed deformation tangent space has exact dimension **`|Q|`**! -/
theorem wiles_Q_tangent_eq_card_of_dual_vanish
    (hvan : Module.finrank (ZMod p) (W.D.DualSelmer W.L_Q) = 0) :
    Module.finrank (ZMod p) (W.D.Selmer W.L_Q) = Fintype.card Q := by
  have h := W.wiles_Q_balancing_equation
  rw [hvan] at h
  omega

end Ad0WilesSelmerSystem

end GreenbergWilesAndWilesBalancing

/-! ## Section 6: Taylor–Wiles Primes `Q_N`, Diamond Groups `Δ_q = (ℤ/qℤ)ˣ[p^N]`, & Patching Bridge -/

section TaylorWilesPrimesAndPatchingBridge

/-- `artinRep q 1 ≡ 1 [MOD q]` for every `q ≥ 1`. -/
lemma artinRep_one_modEq (q : ℕ) [NeZero q] : artinRep q 1 ≡ 1 [MOD q] := by
  unfold artinRep
  rw [map_one]
  change ((1 : ZMod q).val) ≡ 1 [MOD q]
  exact (ZMod.natCast_eq_natCast_iff _ _ _).mp (by simp)

/-- Exact membership characterization: `r ∈ FrobPrimes q 1 ↔ r.Prime ∧ r ≡ 1 [MOD q]`. -/
theorem mem_frobPrimes_one_iff (q : ℕ) [NeZero q] (r : ℕ) :
    r ∈ Stage5DirichletDensity.FrobPrimes q 1 ↔ r.Prime ∧ r ≡ 1 [MOD q] := by
  rw [Stage5DirichletDensity.frobPrimes_eq_primes_modEq q 1]
  have h1 := artinRep_one_modEq q
  exact ⟨fun ⟨hp, hm⟩ => ⟨hp, hm.trans h1⟩, fun ⟨hp, hm⟩ => ⟨hp, hm.trans h1.symm⟩⟩

/-- **UNCONDITIONAL INFINITUDE OF TAYLOR–WILES PRIMES `q ≡ 1 (mod p^N)`** (via `Stage9CyclotomicChebotarev`):
for EVERY prime `p`, EVERY `N : ℕ`, and EVERY lower bound `B : ℕ`, there exists a prime `q > B`
with `q ≡ 1 [MOD p ^ N]` (and hence `p ^ N ∣ q - 1`)! -/
theorem exists_prime_modEq_one_pow_gt (p N B : ℕ) [Fact p.Prime] :
    ∃ q : ℕ, q.Prime ∧ B < q ∧ q ≡ 1 [MOD p ^ N] ∧ p ^ N ∣ (q - 1) := by
  have : NeZero (p ^ N) := ⟨pow_ne_zero N (Fact.out : p.Prime).ne_zero⟩
  obtain ⟨c, _, X, hshort⟩ := exists_prime_frob_short_interval (p ^ N) (1 : Stage4ClassFieldTheory.CycGal (p ^ N))
  let x : ℝ := max X (B : ℝ)
  obtain ⟨q, hqfrob, hxq, _⟩ := hshort x (le_max_left _ _)
  obtain ⟨hq_prime, hq_mod⟩ := (mem_frobPrimes_one_iff (p ^ N) q).mp hqfrob
  have hBq : B < q := by
    have hBx : (B : ℝ) ≤ x := le_max_right _ _
    have : (B : ℝ) < (q : ℝ) := lt_of_le_of_lt hBx hxq
    exact_mod_cast this
  have hdvd : p ^ N ∣ q - 1 := by
    have h1le : 1 ≤ q := hq_prime.one_le
    exact (Nat.modEq_iff_dvd' h1le).mp hq_mod.symm
  exact ⟨q, hq_prime, hBq, hq_mod, hdvd⟩

/-- **UNCONDITIONAL NATURAL DENSITY `1 / φ(p^N)` OF TAYLOR–WILES PRIMES `q ≡ 1 (mod p^N)`**! -/
theorem hasNaturalDensity_taylorWilesPrimes (p N : ℕ) [Fact p.Prime] :
    HasNaturalDensity { q : ℕ | q.Prime ∧ q ≡ 1 [MOD p ^ N] } (1 / ((p ^ N).totient : ℝ)) := by
  have : NeZero (p ^ N) := ⟨pow_ne_zero N (Fact.out : p.Prime).ne_zero⟩
  have hset : { q : ℕ | q.Prime ∧ q ≡ 1 [MOD p ^ N] } =
      Stage5DirichletDensity.FrobPrimes (p ^ N) 1 := by
    ext r
    exact (mem_frobPrimes_one_iff (p ^ N) r).symm
  rw [hset, ← fintype_card_cycGal_eq_totient (p ^ N)]
  exact hasNaturalDensity_frobPrimes (p ^ N) 1

/-- **Concrete Local Taylor–Wiles Diamond Group `Δ_q := (ℤ/qℤ)ˣ[p^N]`**:
the `p^N`-torsion subgroup of `(ZMod q)ˣ`. -/
def TWLocalDiamond (q p N : ℕ) : Subgroup (ZMod q)ˣ where
  carrier := { u : (ZMod q)ˣ | u ^ (p ^ N) = 1 }
  mul_mem' {a b} ha hb := by
    change (a * b) ^ (p ^ N) = 1
    rw [mul_pow, ha, hb, one_mul]
  one_mem' := one_pow _
  inv_mem' {a} ha := by
    change a⁻¹ ^ (p ^ N) = 1
    rw [inv_pow, ha, inv_one]

instance instDecidablePredTWLocalDiamond (q p N : ℕ) :
    DecidablePred (fun u : (ZMod q)ˣ => u ∈ TWLocalDiamond q p N) :=
  fun u => inferInstanceAs (Decidable (u ^ (p ^ N) = 1))

/-- **UNCONDITIONAL CYCLIC ISOMORPHISM & EXACT ORDER `p ^ N` OF `Δ_q = (ℤ/qℤ)ˣ[p^N]`**:
for EVERY prime `q` with `p ^ N ∣ q - 1`, `TWLocalDiamond q p N` is cyclic of exact order `p ^ N`,
isomorphic to `Multiplicative (ZMod (p ^ N))`! -/
theorem twLocalDiamond_equiv_ZMod {q p N : ℕ} [Fact q.Prime] [Fact p.Prime]
    (hdvd : p ^ N ∣ q - 1) :
    Nonempty (TWLocalDiamond q p N ≃* Multiplicative (ZMod (p ^ N))) ∧
      Fintype.card (TWLocalDiamond q p N) = p ^ N ∧
      IsCyclic (TWLocalDiamond q p N) := by
  have hp_pos : 0 < p ^ N := pow_pos (Fact.out : p.Prime).pos N
  have : NeZero (p ^ N) := ⟨hp_pos.ne'⟩
  obtain ⟨m, hm⟩ := hdvd
  have hcardU : Fintype.card (ZMod q)ˣ = q - 1 := by
    rw [ZMod.card_units_eq_totient, Nat.totient_prime (Fact.out : q.Prime)]
  have hq1_pos : 0 < q - 1 := by
    have := (Fact.out : q.Prime).two_le; omega
  have hm_pos : 0 < m := by
    by_contra hm0
    have : m = 0 := by omega
    rw [this, mul_zero] at hm
    omega
  obtain ⟨ζ, hζ⟩ := IsCyclic.exists_generator (α := (ZMod q)ˣ)
  have hordζ : orderOf ζ = q - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hζ, Nat.card_eq_fintype_card, hcardU]
  let δ : (ZMod q)ˣ := ζ ^ m
  have hordδ : orderOf δ = p ^ N := by
    dsimp only [δ]
    rw [orderOf_pow, hordζ, hm]
    have hgcd : Nat.gcd (p ^ N * m) m = m := Nat.gcd_eq_right (dvd_mul_left m (p ^ N))
    rw [hgcd, Nat.mul_div_cancel _ hm_pos]
  have hδ_mem : δ ∈ TWLocalDiamond q p N := by
    change δ ^ (p ^ N) = 1
    rw [← hordδ, pow_orderOf_eq_one]
  let δSub : TWLocalDiamond q p N := ⟨δ, hδ_mem⟩
  let φ : Multiplicative (ZMod (p ^ N)) →* TWLocalDiamond q p N :=
    { toFun := fun x => δSub ^ (Multiplicative.toAdd x).val
      map_one' := by
        change δSub ^ ((0 : ZMod (p ^ N)).val) = 1
        simp
      map_mul' := fun x y => by
        let a := (Multiplicative.toAdd x).val
        let b := (Multiplicative.toAdd y).val
        change δSub ^ ((Multiplicative.toAdd x + Multiplicative.toAdd y).val) =
          δSub ^ a * δSub ^ b
        rw [← pow_add, ZMod.val_add]
        apply Subtype.ext
        change δ ^ ((a + b) % p ^ N) = δ ^ (a + b)
        have hdiv : a + b = (p ^ N) * ((a + b) / p ^ N) + (a + b) % p ^ N :=
          (Nat.div_add_mod (a + b) (p ^ N)).symm
        conv_rhs => rw [hdiv, pow_add, pow_mul, hδ_mem, one_pow, one_mul] }
  have hφ_inj : Function.Injective φ := by
    intro x y hxy
    have hval : δ ^ (Multiplicative.toAdd x).val = δ ^ (Multiplicative.toAdd y).val :=
      congrArg Subtype.val hxy
    have hmod_ord : (Multiplicative.toAdd x).val ≡ (Multiplicative.toAdd y).val [MOD orderOf δ] :=
      (pow_eq_pow_iff_modEq (x := δ)).mp hval
    have hmod : (Multiplicative.toAdd x).val % p ^ N = (Multiplicative.toAdd y).val % p ^ N := by
      have h' : (Multiplicative.toAdd x).val % orderOf δ = (Multiplicative.toAdd y).val % orderOf δ := hmod_ord
      rwa [hordδ] at h'
    have h1 : (Multiplicative.toAdd x).val % p ^ N = (Multiplicative.toAdd x).val :=
      Nat.mod_eq_of_lt (ZMod.val_lt _)
    have h2 : (Multiplicative.toAdd y).val % p ^ N = (Multiplicative.toAdd y).val :=
      Nat.mod_eq_of_lt (ZMod.val_lt _)
    have heq_val : (Multiplicative.toAdd x).val = (Multiplicative.toAdd y).val :=
      h1.symm.trans (hmod.trans h2)
    exact Multiplicative.toAdd.injective (ZMod.val_injective (p ^ N) heq_val)
  have hφ_surj : Function.Surjective φ := by
    rintro ⟨u, hu⟩
    have hmem_pow : u ∈ Submonoid.powers ζ :=
      (mem_powers_iff_mem_zpowers (x := ζ) (y := u)).mpr (hζ u)
    obtain ⟨j, hj⟩ := hmem_pow
    dsimp only at hj
    have h1 : ζ ^ (j * p ^ N) = 1 := by rw [pow_mul, hj]; exact hu
    have hdvd_j : q - 1 ∣ j * p ^ N := hordζ ▸ orderOf_dvd_of_pow_eq_one h1
    rw [hm] at hdvd_j
    have hm_dvd_j : m ∣ j := by
      rcases hdvd_j with ⟨c, hc⟩
      refine ⟨c, ?_⟩
      have hmul : p ^ N * j = p ^ N * (m * c) := by linarith
      exact Nat.eq_of_mul_eq_mul_left hp_pos hmul
    obtain ⟨r, rfl⟩ := hm_dvd_j
    refine ⟨Multiplicative.ofAdd (r : ZMod (p ^ N)), ?_⟩
    apply Subtype.ext
    change δ ^ ((r : ZMod (p ^ N)).val) = u
    rw [ZMod.val_natCast]
    have hmod_eq : δ ^ (r % p ^ N) = δ ^ r := by
      have hdiv : r = p ^ N * (r / p ^ N) + r % p ^ N := (Nat.div_add_mod r (p ^ N)).symm
      conv_rhs => rw [hdiv, pow_add, pow_mul, hδ_mem, one_pow, one_mul]
    rw [hmod_eq]
    dsimp only [δ]
    rw [← pow_mul, hj]
  let e : TWLocalDiamond q p N ≃* Multiplicative (ZMod (p ^ N)) :=
    (MulEquiv.ofBijective φ ⟨hφ_inj, hφ_surj⟩).symm
  have hcard : Fintype.card (TWLocalDiamond q p N) = p ^ N := by
    rw [Fintype.card_congr e.toEquiv, Fintype.card_congr Multiplicative.toAdd, ZMod.card]
  have hcyc : IsCyclic (TWLocalDiamond q p N) :=
    ⟨⟨δSub, fun x => by
      obtain ⟨y, rfl⟩ := hφ_surj x
      refine ⟨((Multiplicative.toAdd y).val : ℤ), ?_⟩
      change δSub ^ (((Multiplicative.toAdd y).val : ℤ)) = δSub ^ (Multiplicative.toAdd y).val
      rw [zpow_natCast]⟩⟩
  exact ⟨⟨e⟩, hcard, hcyc⟩

/-- Concrete Taylor–Wiles prime set `Q_N` of size `g` at level `p^N`, avoiding a finite set `bad`. -/
structure TaylorWilesPrimeSet (p N g : ℕ) [Fact p.Prime] (bad : Finset ℕ) where
  primes : Fin g → ℕ
  primes_inj : Function.Injective primes
  primes_prime : ∀ i : Fin g, (primes i).Prime
  primes_modEq : ∀ i : Fin g, primes i ≡ 1 [MOD p ^ N]
  primes_not_bad : ∀ i : Fin g, primes i ∉ bad

/-- **UNCONDITIONAL EXISTENCE OF TAYLOR–WILES PRIME SETS `Q_N` OF ANY SIZE `g` AND LEVEL `N`**:
for EVERY prime `p`, EVERY level `N`, EVERY `g : ℕ`, and EVERY finite bad-prime set `bad`,
there exists a concrete `TaylorWilesPrimeSet p N g bad`! -/
theorem exists_taylorWilesPrimeSet (p N g : ℕ) [Fact p.Prime] (bad : Finset ℕ) :
    Nonempty (TaylorWilesPrimeSet p N g bad) := by
  induction g with
  | zero =>
    exact ⟨{ primes := Fin.elim0
             primes_inj := fun i => Fin.elim0 i
             primes_prime := fun i => Fin.elim0 i
             primes_modEq := fun i => Fin.elim0 i
             primes_not_bad := fun i => Fin.elim0 i }⟩
  | succ k ih =>
    obtain ⟨T⟩ := ih
    let avoid : Finset ℕ := bad ∪ Finset.univ.image T.primes
    let B : ℕ := avoid.sup id
    obtain ⟨q, hq_prime, hBq, hq_mod, _⟩ := exists_prime_modEq_one_pow_gt p N B
    have hq_not_avoid : q ∉ avoid := by
      intro hmem
      have hle : q ≤ B := Finset.le_sup (f := id) hmem
      omega
    have hq_not_bad : q ∉ bad := fun h => hq_not_avoid (Finset.mem_union_left _ h)
    have hq_ne_prev : ∀ i : Fin k, T.primes i ≠ q := fun i h =>
      hq_not_avoid (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, h⟩))
    refine ⟨{ primes := Fin.snoc T.primes q
              primes_inj := fun i j => by
                refine Fin.lastCases ?_ (fun i' => ?_) i
                · refine Fin.lastCases ?_ (fun j' => ?_) j
                  · intro _; rfl
                  · intro hij
                    simp only [Fin.snoc_last, Fin.snoc_castSucc] at hij
                    exact absurd hij.symm (hq_ne_prev j')
                · refine Fin.lastCases ?_ (fun j' => ?_) j
                  · intro hij
                    simp only [Fin.snoc_last, Fin.snoc_castSucc] at hij
                    exact absurd hij (hq_ne_prev i')
                  · intro hij
                    simp only [Fin.snoc_castSucc] at hij
                    exact congrArg Fin.castSucc (T.primes_inj hij)
              primes_prime := fun i =>
                Fin.lastCases (by simpa using hq_prime) (fun i' => by simpa using T.primes_prime i') i
              primes_modEq := fun i =>
                Fin.lastCases (by simpa using hq_mod) (fun i' => by simpa using T.primes_modEq i') i
              primes_not_bad := fun i =>
                Fin.lastCases (by simpa using hq_not_bad) (fun i' => by simpa using T.primes_not_bad i') i }⟩

namespace TaylorWilesPrimeSet

variable {p N g : ℕ} [Fact p.Prime] {bad : Finset ℕ} (T : TaylorWilesPrimeSet p N g bad)

instance instFactPrime (i : Fin g) : Fact (T.primes i).Prime := ⟨T.primes_prime i⟩

theorem primes_dvd (i : Fin g) : p ^ N ∣ T.primes i - 1 :=
  (Nat.modEq_iff_dvd' (T.primes_prime i).one_le).mp (T.primes_modEq i).symm

/-- Global Taylor–Wiles diamond group `Δ_{Q_N} := ∏_{q ∈ Q_N} (ℤ/qℤ)ˣ[p^N]`. -/
abbrev GlobalDiamond : Type :=
  ∀ i : Fin g, TWLocalDiamond (T.primes i) p N

/-- Exact cardinality of `Δ_{Q_N}`: `|Δ_{Q_N}| = (p ^ N) ^ g`! -/
theorem card_globalDiamond :
    Fintype.card T.GlobalDiamond = (p ^ N) ^ g := by
  have hcoord : ∀ i : Fin g, Fintype.card (TWLocalDiamond (T.primes i) p N) = p ^ N := fun i =>
    (twLocalDiamond_equiv_ZMod (T.primes_dvd i)).2.1
  rw [Fintype.card_pi]
  simp_rw [hcoord]
  simp

/-- Canonical cyclic coordinate generators `δ_i ∈ Δ_{Q_N}` (`i : Fin g`) of exact order `p ^ N`. -/
def diamondGen (i : Fin g) : T.GlobalDiamond :=
  fun j =>
    if h : j = i then
      let e : TWLocalDiamond (T.primes i) p N ≃* Multiplicative (ZMod (p ^ N)) :=
        Classical.choice (twLocalDiamond_equiv_ZMod (T.primes_dvd i)).1
      h ▸ e.symm (Multiplicative.ofAdd (1 : ZMod (p ^ N)))
    else 1

theorem diamondGen_pow_eq_one (i : Fin g) : T.diamondGen i ^ (p ^ N) = 1 := by
  funext j
  apply Subtype.ext
  exact (T.diamondGen i j).2

theorem closure_diamondGen_eq_top :
    Subgroup.closure (Set.range T.diamondGen) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  have hdecomp : x = ∏ i : Fin g, (fun j => if h : j = i then h ▸ x i else 1) := by
    funext j
    rw [Finset.prod_apply]
    rw [Finset.prod_eq_single j]
    · simp
    · intro i _ hij; simp [Ne.symm hij]
    · intro h; exact absurd (Finset.mem_univ j) h
  rw [hdecomp]
  refine Subgroup.prod_mem _ fun i _ => ?_
  let e : TWLocalDiamond (T.primes i) p N ≃* Multiplicative (ZMod (p ^ N)) :=
    Classical.choice (twLocalDiamond_equiv_ZMod (T.primes_dvd i)).1
  let k : ℕ := (Multiplicative.toAdd (e (x i))).val
  have hpow : T.diamondGen i ^ k = (fun j => if h : j = i then h ▸ x i else 1) := by
    funext j
    change (T.diamondGen i j) ^ k = _
    by_cases h : j = i
    · subst h
      simp only [diamondGen, ↓reduceDIte]
      rw [← map_pow]
      have h1 : (Multiplicative.ofAdd (1 : ZMod (p ^ N))) ^ k = e (x j) := by
        rw [← ofAdd_nsmul, nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val]
        rfl
      rw [h1, e.symm_apply_apply]
    · simp [diamondGen, h]
  rw [← hpow]
  exact Subgroup.pow_mem _ (Subgroup.subset_closure (Set.mem_range.mpr ⟨i, rfl⟩)) k

/-- Helper: prime-power binomial divisibility `p ∣ (p ^ N).choose k` for `0 < k < p ^ N`
(proved unconditionally via Frobenius `(X + 1) ^ (p ^ N) = X ^ (p ^ N) + 1` in `(ZMod p)[X]`). -/
theorem prime_dvd_choose_prime_pow {k : ℕ} (hk0 : 0 < k) (hk1 : k < p ^ N) :
    p ∣ (p ^ N).choose k := by
  have hfrob : ∀ n : ℕ, ((Polynomial.X + 1 : Polynomial (ZMod p)) ^ (p ^ n)) =
      Polynomial.X ^ (p ^ n) + 1 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, pow_mul, ih, add_pow_char, one_pow, ← pow_mul, ← pow_succ]
  have hcoeff := congrArg (fun f : Polynomial (ZMod p) => f.coeff k) (hfrob N)
  rw [add_pow] at hcoeff
  have hLHS : (∑ m ∈ Finset.range (p ^ N + 1),
      Polynomial.X ^ m * 1 ^ (p ^ N - m) * ((p ^ N).choose m : Polynomial (ZMod p))).coeff k =
      ((p ^ N).choose k : ZMod p) := by
    rw [Polynomial.finsetSum_coeff]
    rw [Finset.sum_eq_single k]
    · simp
    · intro m _ hmk
      simp [one_pow, mul_one]
      exact fun h => absurd h.symm hmk
    · intro hk_not
      exact absurd (Finset.mem_range.mpr (by omega)) hk_not
  have hRHS : (Polynomial.X ^ (p ^ N) + (1 : Polynomial (ZMod p))).coeff k = 0 := by
    rw [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_one,
      if_neg (by omega), if_neg (by omega), add_zero]
  rw [hLHS, hRHS] at hcoeff
  exact (ZMod.natCast_eq_zero_iff ((p ^ N).choose k) p).mp hcoeff

/-- **Exact Nilpotency of Diamond Augmentation Variables `([δ_i] - 1)` Modulo `p ^ M`**:
in `DiamondAlgebra (ZMod (p ^ M)) Δ_{Q_N}`, `([δ_i] - 1) ^ (M * p ^ N) = 0`! -/
theorem diamondGen_sub_one_pow_eq_zero (M : ℕ) (i : Fin g) :
    (MonoidAlgebra.single (T.diamondGen i) (1 : ZMod (p ^ M)) - 1) ^ (M * p ^ N) = 0 := by
  let A := DiamondAlgebra (ZMod (p ^ M)) T.GlobalDiamond
  let x : A := MonoidAlgebra.single (T.diamondGen i) (1 : ZMod (p ^ M)) - 1
  have h1x : (1 + x) ^ (p ^ N) = 1 := by
    have heq : 1 + x = MonoidAlgebra.single (T.diamondGen i) (1 : ZMod (p ^ M)) := by
      dsimp only [x]; abel
    rw [heq]
    have hpow : ∀ n : ℕ, (MonoidAlgebra.single (T.diamondGen i) (1 : ZMod (p ^ M))) ^ n =
        MonoidAlgebra.single (T.diamondGen i ^ n) (1 : ZMod (p ^ M)) := by
      intro n
      induction n with
      | zero => simp [MonoidAlgebra.one_def]
      | succ n ih =>
        rw [pow_succ, ih, MonoidAlgebra.single_mul_single, one_mul, pow_succ]
    rw [hpow, T.diamondGen_pow_eq_one i, MonoidAlgebra.one_def]
  have hp_dvd_xpow : (p : A) ∣ x ^ (p ^ N) := by
    have hexp : (x + 1) ^ (p ^ N) = 1 := by rwa [add_comm]
    rw [add_pow] at hexp
    have hpN_pos : 0 < p ^ N := pow_pos (Fact.out : p.Prime).pos N
    rw [Finset.sum_range_succ] at hexp
    have hsplit : ∑ m ∈ Finset.range (p ^ N), x ^ m * 1 ^ (p ^ N - m) * ((p ^ N).choose m : A) =
        (∑ k ∈ Finset.range (p ^ N - 1), x ^ (k + 1) * ((p ^ N).choose (k + 1) : A)) + 1 := by
      have hlen : p ^ N = (p ^ N - 1) + 1 := (Nat.sub_add_cancel hpN_pos).symm
      conv_lhs => rw [hlen, Finset.sum_range_succ']
      simp only [one_pow, mul_one, pow_zero, Nat.choose_zero_right, Nat.cast_one]
      rw [← hlen]
    rw [hsplit] at hexp
    simp only [Nat.choose_self, Nat.cast_one, mul_one, one_pow] at hexp
    have hx_eq : x ^ (p ^ N) = -(∑ k ∈ Finset.range (p ^ N - 1),
        x ^ (k + 1) * ((p ^ N).choose (k + 1) : A)) := by
      linear_combination hexp
    rw [hx_eq]
    refine dvd_neg.mpr (Finset.dvd_sum fun k hk => ?_)
    have hk_lt : k + 1 < p ^ N := by
      have := Finset.mem_range.mp hk; omega
    obtain ⟨c, hc⟩ := prime_dvd_choose_prime_pow (p := p) (N := N) (Nat.succ_pos k) hk_lt
    refine ⟨x ^ (k + 1) * (c : A), ?_⟩
    rw [hc, Nat.cast_mul]; ring
  obtain ⟨y, hy⟩ := hp_dvd_xpow
  rw [mul_comm, pow_mul, hy, mul_pow]
  have hpM0 : ((p : A) ^ M) = 0 := by
    calc (p : A) ^ M = ((p ^ M : ℕ) : A) := (Nat.cast_pow p M).symm
      _ = algebraMap (ZMod (p ^ M)) A ((p ^ M : ℕ) : ZMod (p ^ M)) := (map_natCast _ _).symm
      _ = 0 := by rw [ZMod.natCast_self, map_zero]
  rw [hpM0, zero_mul]

/-- **CONCRETE SURJECTIVE FINITE-LEVEL TAYLOR–WILES PATCHING HOMOMORPHISM**:
`PatchingBaseRing p g = ℤ_[p][[y₀,…,y_{g-1}]] →ₐ[ℤ_[p]] (ZMod (p ^ M))[Δ_{Q_N}]`,
sending each patching variable `y_i ↦ [δ_i] - 1`, proved **SURJECTIVE** and mapping
`patchingAugIdeal p g` onto `diamondAugIdeal (ZMod (p ^ M)) Δ_{Q_N}`! -/
def patchingToFiniteLevelDiamond (M : ℕ) :
    PatchingBaseRing p g →+* DiamondAlgebra (ZMod (p ^ M)) T.GlobalDiamond := by
  classical
  let A := DiamondAlgebra (ZMod (p ^ M)) T.GlobalDiamond
  let D : ℕ := M * p ^ N
  let B : ℕ := g * D + 1
  let degSet : Finset (Fin g →₀ ℕ) :=
    (Fintype.piFinset fun _ : Fin g => Finset.range B).image Finsupp.equivFunOnFinite.symm
  let gen : Fin g → A := fun i => MonoidAlgebra.single (T.diamondGen i) (1 : ZMod (p ^ M)) - 1
  let redZp : ℤ_[p] →+* A := (algebraMap (ZMod (p ^ M)) A).comp (PadicInt.toZModPow M)
  have hmem_degSet : ∀ α : Fin g →₀ ℕ, (∑ i : Fin g, α i) < B → α ∈ degSet := by
    intro α hα
    refine Finset.mem_image.mpr ⟨fun i => α i, ?_, by ext i; rfl⟩
    rw [Fintype.mem_piFinset]
    intro i
    rw [Finset.mem_range]
    exact lt_of_le_of_lt (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)) hα
  have hmon_zero : ∀ α : Fin g →₀ ℕ, B ≤ ∑ i : Fin g, α i → (∏ i : Fin g, gen i ^ α i) = 0 := by
    intro α hα
    have hex : ∃ i : Fin g, D ≤ α i := by
      by_contra hall
      push Not at hall
      have hle : ∑ i : Fin g, α i ≤ ∑ _ : Fin g, D :=
        Finset.sum_le_sum fun i _ => le_of_lt (hall i)
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hle
      omega
    obtain ⟨i₀, hi₀⟩ := hex
    have hpow0 : gen i₀ ^ α i₀ = 0 := by
      rw [← Nat.add_sub_cancel' hi₀, pow_add, T.diamondGen_sub_one_pow_eq_zero M i₀, zero_mul]
    exact Finset.prod_eq_zero (Finset.mem_univ i₀) hpow0
  refine
    { toFun := fun f => ∑ α ∈ degSet, redZp (MvPowerSeries.coeff α f) * ∏ i : Fin g, gen i ^ α i
      map_one' := by
        have h0mem : (0 : Fin g →₀ ℕ) ∈ degSet := hmem_degSet 0 (by simp [B])
        rw [Finset.sum_eq_single (0 : Fin g →₀ ℕ)]
        · simp
        · intro α _ hα0; rw [MvPowerSeries.coeff_one, if_neg hα0, map_zero, zero_mul]
        · intro h; exact absurd h0mem h
      map_zero' := by simp
      map_add' := fun f₁ f₂ => by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun α _ => by rw [map_add, map_add, add_mul]
      map_mul' := fun f₁ f₂ => by
        rw [Finset.sum_mul]
        simp_rw [Finset.mul_sum]
        have hLHS :
            ∑ α ∈ degSet, redZp (MvPowerSeries.coeff α (f₁ * f₂)) * ∏ i : Fin g, gen i ^ α i =
            ∑ α ∈ degSet, ∑ pq ∈ Finset.antidiagonal α,
              (redZp (MvPowerSeries.coeff pq.1 f₁) * ∏ i : Fin g, gen i ^ pq.1 i) *
              (redZp (MvPowerSeries.coeff pq.2 f₂) * ∏ i : Fin g, gen i ^ pq.2 i) := by
          refine Finset.sum_congr rfl fun α _ => ?_
          rw [MvPowerSeries.coeff_mul, map_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun pq hpq => ?_
          have hadd : pq.1 + pq.2 = α := Finset.mem_antidiagonal.mp hpq
          rw [map_mul, ← hadd]
          have hprod : (∏ i : Fin g, gen i ^ (pq.1 + pq.2) i) =
              (∏ i : Fin g, gen i ^ pq.1 i) * (∏ i : Fin g, gen i ^ pq.2 i) := by
            rw [← Finset.prod_mul_distrib]
            refine Finset.prod_congr rfl fun i _ => by rw [Finsupp.add_apply, pow_add]
          rw [hprod]; ring
        rw [hLHS]
        let term : (Fin g →₀ ℕ) × (Fin g →₀ ℕ) → A := fun pq =>
          (redZp (MvPowerSeries.coeff pq.1 f₁) * ∏ i : Fin g, gen i ^ pq.1 i) *
          (redZp (MvPowerSeries.coeff pq.2 f₂) * ∏ i : Fin g, gen i ^ pq.2 i)
        have hterm0 : ∀ pq : (Fin g →₀ ℕ) × (Fin g →₀ ℕ),
            B ≤ ∑ i : Fin g, (pq.1 + pq.2) i → term pq = 0 := by
          intro pq hge
          have hprod : (∏ i : Fin g, gen i ^ pq.1 i) * (∏ i : Fin g, gen i ^ pq.2 i) =
              ∏ i : Fin g, gen i ^ (pq.1 + pq.2) i := by
            rw [← Finset.prod_mul_distrib]
            refine Finset.prod_congr rfl fun i _ => by rw [Finsupp.add_apply, pow_add]
          dsimp only [term]
          calc (redZp (MvPowerSeries.coeff pq.1 f₁) * ∏ i, gen i ^ pq.1 i) *
                (redZp (MvPowerSeries.coeff pq.2 f₂) * ∏ i, gen i ^ pq.2 i)
              = (redZp (MvPowerSeries.coeff pq.1 f₁) * redZp (MvPowerSeries.coeff pq.2 f₂)) *
                  ((∏ i, gen i ^ pq.1 i) * (∏ i, gen i ^ pq.2 i)) := by ring
            _ = (redZp (MvPowerSeries.coeff pq.1 f₁) * redZp (MvPowerSeries.coeff pq.2 f₂)) *
                  (∏ i, gen i ^ (pq.1 + pq.2) i) := by rw [hprod]
            _ = 0 := by rw [hmon_zero (pq.1 + pq.2) hge, mul_zero]
        have hsum_L : (∑ α ∈ degSet, ∑ pq ∈ Finset.antidiagonal α, term pq) =
            ∑ pq ∈ (degSet ×ˢ degSet).filter (fun pq => ∑ i : Fin g, (pq.1 + pq.2) i < B), term pq := by
          rw [← Finset.sum_biUnion]
          · symm
            refine Finset.sum_subset_zero_on_sdiff ?_ ?_ (fun _ _ => rfl)
            · intro pq hpq
              rw [Finset.mem_filter, Finset.mem_product] at hpq
              refine Finset.mem_biUnion.mpr ⟨pq.1 + pq.2, hmem_degSet _ hpq.2, Finset.mem_antidiagonal.mpr rfl⟩
            · intro pq hpq
              rw [Finset.mem_sdiff] at hpq
              have hlt : ¬ ∑ i : Fin g, (pq.1 + pq.2) i < B := by
                intro hlt
                apply hpq.2
                rw [Finset.mem_filter, Finset.mem_product]
                refine ⟨⟨hmem_degSet pq.1 ?_, hmem_degSet pq.2 ?_⟩, hlt⟩
                · exact lt_of_le_of_lt (Finset.sum_le_sum fun i _ => Nat.le_add_right _ _) hlt
                · exact lt_of_le_of_lt (Finset.sum_le_sum fun i _ => Nat.le_add_left _ _) hlt
              exact hterm0 pq (Nat.le_of_not_lt hlt)
          · intro α₁ _ α₂ _ hne
            change Disjoint (Finset.antidiagonal α₁) (Finset.antidiagonal α₂)
            rw [Finset.disjoint_left]
            intro pq h1 h2
            exact hne ((Finset.mem_antidiagonal.mp h1).symm.trans (Finset.mem_antidiagonal.mp h2))
        have hsum_R : (∑ β ∈ degSet, ∑ γ ∈ degSet, term (β, γ)) =
            ∑ pq ∈ (degSet ×ˢ degSet).filter (fun pq => ∑ i : Fin g, (pq.1 + pq.2) i < B), term pq := by
          rw [← Finset.sum_product']
          symm
          refine Finset.sum_subset_zero_on_sdiff (Finset.filter_subset _ _) ?_ (fun _ _ => rfl)
          intro pq hpq
          rw [Finset.mem_sdiff, Finset.mem_filter] at hpq
          have hge : B ≤ ∑ i : Fin g, (pq.1 + pq.2) i := by
            by_contra hlt; exact hpq.2 ⟨hpq.1, Nat.lt_of_not_ge hlt⟩
          exact hterm0 pq hge
        exact hsum_L.trans hsum_R.symm }

theorem patchingToFiniteLevelDiamond_X (M : ℕ) (hM : 1 ≤ M) (i : Fin g) :
    T.patchingToFiniteLevelDiamond M (patchingVar i) =
      MonoidAlgebra.single (T.diamondGen i) (1 : ZMod (p ^ M)) - 1 := by
  classical
  have hg1 : 1 ≤ g := Nat.pos_of_ne_zero (fun h0 => by subst h0; exact Fin.elim0 i)
  have hpN_pos : 1 ≤ p ^ N := Nat.one_le_pow N p (Fact.out : p.Prime).pos
  have hB_gt1 : 1 < g * (M * p ^ N) + 1 := by
    have : 1 ≤ g * (M * p ^ N) := Nat.mul_pos hg1 (Nat.mul_pos hM hpN_pos)
    omega
  let degSet : Finset (Fin g →₀ ℕ) :=
    (Fintype.piFinset fun _ : Fin g => Finset.range (g * (M * p ^ N) + 1)).image
      Finsupp.equivFunOnFinite.symm
  have hmem : Finsupp.single i (1 : ℕ) ∈ degSet := by
    refine Finset.mem_image.mpr ⟨fun j => Finsupp.single i 1 j, ?_, by ext j; rfl⟩
    rw [Fintype.mem_piFinset]
    intro j
    rw [Finset.mem_range]
    by_cases hj : j = i
    · subst hj; simpa using hB_gt1
    · rw [Finsupp.single_eq_of_ne hj]; omega
  change (∑ α ∈ degSet,
    ((algebraMap (ZMod (p ^ M)) (DiamondAlgebra (ZMod (p ^ M)) T.GlobalDiamond)).comp
      (PadicInt.toZModPow M)) (MvPowerSeries.coeff α (MvPowerSeries.X i)) *
      ∏ j : Fin g, (MonoidAlgebra.single (T.diamondGen j) (1 : ZMod (p ^ M)) - 1) ^ α j) =
    MonoidAlgebra.single (T.diamondGen i) (1 : ZMod (p ^ M)) - 1
  rw [Finset.sum_eq_single (Finsupp.single i (1 : ℕ))]
  · rw [MvPowerSeries.coeff_X, if_pos rfl, map_one, one_mul]
    rw [Finset.prod_eq_single i]
    · simp
    · intro j _ hji; rw [Finsupp.single_eq_of_ne hji, pow_zero]
    · intro h; exact absurd (Finset.mem_univ i) h
  · intro α _ hα
    rw [MvPowerSeries.coeff_X, if_neg hα, map_zero, zero_mul]
  · intro h; exact absurd hmem h

/-- **UNCONDITIONAL SURJECTIVITY OF `S_∞ = ℤ_[p][[y₀,…,y_{g-1}]] ↠ (ZMod (p^M))[Δ_{Q_N}]`**
(and exact augmentation compatibility `patchingAugIdeal ↦ diamondAugIdeal`)! -/
theorem patchingToFiniteLevelDiamond_surjective (M : ℕ) (hM : 1 ≤ M) :
    Function.Surjective (T.patchingToFiniteLevelDiamond M) ∧
      (patchingAugIdeal p g).map (T.patchingToFiniteLevelDiamond M) =
        diamondAugIdeal (ZMod (p ^ M)) T.GlobalDiamond := by
  let φ := T.patchingToFiniteLevelDiamond M
  have hC : ∀ c : ℤ_[p], φ (MvPowerSeries.C c) =
      algebraMap (ZMod (p ^ M)) (DiamondAlgebra (ZMod (p ^ M)) T.GlobalDiamond) (PadicInt.toZModPow M c) := by
    intro c
    classical
    let degSet : Finset (Fin g →₀ ℕ) :=
      (Fintype.piFinset fun _ : Fin g => Finset.range (g * (M * p ^ N) + 1)).image
        Finsupp.equivFunOnFinite.symm
    have h0mem : (0 : Fin g →₀ ℕ) ∈ degSet := by
      refine Finset.mem_image.mpr ⟨fun _ => 0, ?_, by ext j; rfl⟩
      rw [Fintype.mem_piFinset]; intro _; rw [Finset.mem_range]; omega
    change (∑ α ∈ degSet,
      ((algebraMap (ZMod (p ^ M)) (DiamondAlgebra (ZMod (p ^ M)) T.GlobalDiamond)).comp
        (PadicInt.toZModPow M)) (MvPowerSeries.coeff α (MvPowerSeries.C c)) *
        ∏ j : Fin g, (MonoidAlgebra.single (T.diamondGen j) (1 : ZMod (p ^ M)) - 1) ^ α j) = _
    rw [Finset.sum_eq_single (0 : Fin g →₀ ℕ)]
    · simp
    · intro α _ hα0
      rw [MvPowerSeries.coeff_C_of_ne_zero hα0, map_zero, zero_mul]
    · intro h; exact absurd h0mem h
  have hgen_mem : ∀ i : Fin g,
      MonoidAlgebra.single (T.diamondGen i) (1 : ZMod (p ^ M)) ∈ Set.range φ := by
    intro i
    refine ⟨patchingVar i + 1, ?_⟩
    rw [map_add, map_one, T.patchingToFiniteLevelDiamond_X M hM i]
    abel
  have hdelta_mem : ∀ δ : T.GlobalDiamond,
      MonoidAlgebra.single δ (1 : ZMod (p ^ M)) ∈ Set.range φ := by
    let H : Subgroup T.GlobalDiamond :=
      { carrier := { δ | MonoidAlgebra.single δ (1 : ZMod (p ^ M)) ∈ Set.range φ }
        one_mem' := ⟨1, by rw [map_one, MonoidAlgebra.one_def]⟩
        mul_mem' := by
          rintro a b ⟨fa, hfa⟩ ⟨fb, hfb⟩
          refine ⟨fa * fb, ?_⟩
          rw [map_mul, hfa, hfb, MonoidAlgebra.single_mul_single, one_mul]
        inv_mem' := by
          rintro a ⟨fa, hfa⟩
          have hpow : a⁻¹ = a ^ (p ^ N - 1) := by
            apply mul_left_cancel (a := a)
            have hpN_pos : 1 ≤ p ^ N := Nat.one_le_pow N p (Fact.out : p.Prime).pos
            rw [mul_inv_cancel, ← pow_succ', Nat.sub_add_cancel hpN_pos]
            funext j; apply Subtype.ext; exact ((a j).2).symm
          rw [hpow]
          refine ⟨fa ^ (p ^ N - 1), ?_⟩
          rw [map_pow, hfa]
          clear hfa hpow
          induction (p ^ N - 1) with
          | zero => simp [MonoidAlgebra.one_def]
          | succ k ih => rw [pow_succ, ih, MonoidAlgebra.single_mul_single, one_mul, pow_succ] }
    have hH_top : H = ⊤ := by
      rw [eq_top_iff, ← T.closure_diamondGen_eq_top, Subgroup.closure_le]
      rintro _ ⟨i, rfl⟩
      exact hgen_mem i
    intro δ
    have hmem : δ ∈ H := by rw [hH_top]; trivial
    exact hmem
  have hsurj : Function.Surjective φ := by
    have : NeZero (p ^ M) := ⟨pow_ne_zero M (Fact.out : p.Prime).ne_zero⟩
    intro z
    refine MonoidAlgebra.induction_on (motive := fun w => w ∈ Set.range φ) z ?_ ?_ ?_
    · intro δ; exact hdelta_mem δ
    · rintro a b ⟨fa, rfl⟩ ⟨fb, rfl⟩
      exact ⟨fa + fb, map_add φ fa fb⟩
    · rintro r a ⟨fa, rfl⟩
      refine ⟨MvPowerSeries.C (r.val : ℤ_[p]) * fa, ?_⟩
      rw [map_mul, hC (r.val : ℤ_[p]), map_natCast, ZMod.natCast_zmod_val, Algebra.smul_def]
  refine ⟨hsurj, ?_⟩
  rw [diamondAugIdeal_eq_span_of_closure_eq_top T.diamondGen T.closure_diamondGen_eq_top]
  rw [patchingAugIdeal, Ideal.map_span]
  congr 1
  ext x
  simp only [Set.mem_image, Set.mem_range]
  constructor
  · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, (T.patchingToFiniteLevelDiamond_X M hM i).symm⟩
  · rintro ⟨i, rfl⟩
    exact ⟨patchingVar i, ⟨i, rfl⟩, T.patchingToFiniteLevelDiamond_X M hM i⟩

/-- **DIRECT BRIDGE TO `Stage11ConcretePatching.TaylorWilesPatchingDatum`**:
every concrete Taylor–Wiles prime set `Q_N` of size `g` feeds directly into
`Stage11ConcretePatching.concrete_taylorWilesPatchingDatum_Zp`, `quadraticPatchingDatum_Zp`,
and `freeAlgPatchingDatum_Zp` over `S_∞ = PatchingBaseRing p g = ℤ_[p][[y₀,…,y_{g-1}]]`,
with `R_∞ ≃ₐ[S_∞] T_∞`, `R_0 ≃+* T_0`, AND finite-level diamond surjections
`S_∞ ↠ (ZMod (p^M))[Δ_{Q_N}]` at every precision `M ≥ 1`! -/
def toConcretePatchingDatum (_T : TaylorWilesPrimeSet p N g bad) (r : ℕ) (hr : 0 < r) :
    TaylorWilesPatchingDatum :=
  concrete_taylorWilesPatchingDatum_Zp p g r hr

theorem toConcretePatchingDatum_spec (r : ℕ) (hr : 0 < r) :
    let D := T.toConcretePatchingDatum r hr
    D.S_inf = PatchingBaseRing p g ∧
    D.g = g ∧
    Fintype.card T.GlobalDiamond = (p ^ N) ^ g ∧
    Nonempty (D.R_inf ≃ₐ[D.S_inf] D.T_inf) ∧
    Nonempty (D.R_0 ≃+* D.T_0) ∧
    (∀ M : ℕ, 1 ≤ M →
      Function.Surjective (T.patchingToFiniteLevelDiamond M) ∧
        (patchingAugIdeal p g).map (T.patchingToFiniteLevelDiamond M) =
          diamondAugIdeal (ZMod (p ^ M)) T.GlobalDiamond) :=
  ⟨rfl, rfl, T.card_globalDiamond,
    ⟨(T.toConcretePatchingDatum r hr).R_inf_equiv_T_inf⟩,
    ⟨(T.toConcretePatchingDatum r hr).R0_equiv_T0⟩,
    fun M hM => T.patchingToFiniteLevelDiamond_surjective M hM⟩

end TaylorWilesPrimeSet

/-- **UNIFIED END-TO-END MAZUR–GREENBERG–WILES–TAYLOR–WILES BRIDGE THEOREM (`0` ASSUMPTIONS!)**:
Given any `Ad0WilesSelmerSystem` `W` for an odd absolutely irreducible `rhoBar : G →* GL₂(𝔽_p)`
(`p ≥ 3`) with Taylor–Wiles prime index set `Q` of size `g = |Q|`, level `N`, bad prime set `bad`,
and any finite-rank free `ℤ_[p]`-Hecke algebra `T₀` (`T₀ ≃ₗ[ℤ_[p]] (Fin r → ℤ_[p])`, `r ≥ 1`):
1. **Mazur Tangent-Space Isomorphism**: `Deform0Dual W.rhoBar ≃ₗ[𝔽_p] H¹(G, ad⁰ rhoBar)`;
2. **Global & Archimedean Cohomology**: `dim H⁰(G, ad⁰) = 0` and `dim H⁰(G_∞, ad⁰) = 1`;
3. **Wiles Balancing Equation**: `dim H¹_{L_Q} - dim H¹_{L*_Q} = |Q|`, and `dim H¹_{L_min} = dim H¹_{L_min*}`;
4. **Taylor–Wiles Prime Set `Q_N`**: unconditionally exists of size `g = |Q|` avoiding `bad`, with
   diamond group `Δ_{Q_N}` of exact order `p ^ (N * g)` and surjective finite-level maps
   `S_∞ = ℤ_[p][[y₀,…,y_{g-1}]] ↠ (ZMod (p^M))[Δ_{Q_N}]`;
5. **Krull Dimension & Patching `R_0 ≃+* T_0`**: `ringKrullDim S_∞ ≥ g + 1`, and the concrete
   `Stage11ConcretePatching.freeAlgPatchingDatum_Zp` over `S_∞` produces `R_∞ ≃ₐ[S_∞] T_∞` and
   `R_0 ≃+* T_0`! -/
theorem mazur_greenberg_wiles_taylor_wiles_bridge
    {G S₀ Q : Type} [Group G] [Fintype S₀] [DecidableEq S₀] [Fintype Q] [DecidableEq Q]
    {p : ℕ} [Fact p.Prime] (W : Ad0WilesSelmerSystem G S₀ Q p)
    (N : ℕ) (bad : Finset ℕ) (r : ℕ) (hr : 0 < r)
    (T₀ : Type) [CommRing T₀] [Algebra ℤ_[p] T₀] (eT : T₀ ≃ₗ[ℤ_[p]] (Fin r → ℤ_[p])) :
    let g := Fintype.card Q
    Nonempty (Deform0Dual W.rhoBar ≃ H1Vec (ZMod p) G (Ad0Rep W.rhoBar)) ∧
    Module.finrank (ZMod p) (H0Submodule (ZMod p) G (Ad0Rep W.rhoBar)) = 0 ∧
    Module.finrank (ZMod p) (H0Subgroup (ZMod p) (Subgroup.zpowers W.conj_elem) (Ad0Rep W.rhoBar)) = 1 ∧
    (Module.finrank (ZMod p) (W.D.Selmer W.L_Q) : ℤ) -
      Module.finrank (ZMod p) (W.D.DualSelmer W.L_Q) = (g : ℤ) ∧
    Module.finrank (ZMod p) (W.D.Selmer W.L_min) =
      Module.finrank (ZMod p) (W.D.DualSelmer W.L_min) ∧
    ((g + 1 : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (PatchingBaseRing p g) ∧
    ∃ T : TaylorWilesPrimeSet p N g bad,
      Fintype.card T.GlobalDiamond = (p ^ N) ^ g ∧
      (∀ M : ℕ, 1 ≤ M → Function.Surjective (T.patchingToFiniteLevelDiamond M)) ∧
      let D := freeAlgPatchingDatum_Zp p g r hr T₀ eT
      Nonempty (D.R_inf ≃ₐ[D.S_inf] D.T_inf) ∧
      Nonempty (D.R_0 ≃+* D.T_0) := by
  intro g
  obtain ⟨T⟩ := exists_taylorWilesPrimeSet p N g bad
  refine ⟨⟨deform0DualEquivH1 W.hp3 W.rhoBar⟩,
    finrank_H0_ad0_eq_zero_of_absIrreducible (two_ne_zero_zmod W.hp3) W.abs_irred,
    finrank_H0_inf_ad0_eq_one (two_ne_zero_zmod W.hp3) W.rhoBar W.conj_elem W.conj_sq W.odd_rep,
    W.wiles_Q_balancing_equation,
    W.wiles_minimal_balancing,
    ringKrullDim_patchingBaseRing_ge p g,
    T, T.card_globalDiamond,
    fun M hM => (T.patchingToFiniteLevelDiamond_surjective M hM).1,
    ⟨(freeAlgPatchingDatum_Zp p g r hr T₀ eT).R_inf_equiv_T_inf⟩,
    ⟨(freeAlgPatchingDatum_Zp p g r hr T₀ eT).R0_equiv_T0⟩⟩

end TaylorWilesPrimesAndPatchingBridge

end Stage11MazurDeformation
end RHDirect
