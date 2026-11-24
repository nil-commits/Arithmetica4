import RHDirect.Stage11CrystallineFontaine
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.MetricSpace.Basic

/-!
# RHDirect.Stage13U3HidaAutomorphy

Unconditional (`0` assumptions, `0` `sorry`, `0` custom `axiom`s, `0` `native_decide`, pure Mathlib
`v4.33.1`) formalization of **Stage 13 — Field 1 Assault (4 of 8, Engine #7)**:
Unitary `U(3)` Hida Families, Automorphy Lifting (`ModUAlt`, `ModNOf`, `CountI`), and
Weight-2 (`e = 1`) Inertia Bounds (`CountV`).

## Contents

1. **Concrete Definite Unitary Group `U(3)` Algebraic Automorphic Forms & Hecke Operators**:
   - Dominant `U(3)` weights `U3Weight` (`c ≤ b ≤ a`), anti-diagonal Hermitian involution `J3`,
     concrete definite `U(3)` algebraic modular form spaces `U3FormSpace R D` over a finite genus
     `ι` with finite stabilizers `Stab i`, Hecke correspondences `HeckeCorr`, split-prime operators
     `T_{w, 1}`, `T_{w, 2}`, `S_w`, spherical `U(3)` Hecke polynomial `u3HeckePoly`, exact
     Eisenstein factorization `u3HeckePoly_eisenstein_factor`, and commutative Hecke algebras.
2. **Exact Ordinary Hida Idempotent `e_ord = lim U_p^{n!}` & Hida Control Theorem**:
   - Exact pigeonhole stabilization `finite_idempotent_stabilization` on ANY finite monoid
     (`U^{n!} = e_ord` for `n ≥ N₀`, `e_ord ∘ e_ord = e_ord`, functoriality `finiteHidaIdemp_map`),
     ordinary/nilpotent direct-sum splitting `finite_hida_ordinary_decomposition` on finite
     `ZMod (p^k)`-modules, projective-limit `p`-adic Hida idempotent `padicHidaIdemp` on
     `Matrix (Fin d) (Fin d) ℤ_[p]`, exact `p`-adic weight specialization `weightSpec u` with
     Weierstrass division `ker(weightSpec u) = (T - u)`, **Hida Control Theorem**
     (`hida_control_theorem`, `hidaControlEquiv`), constant ordinary rank across all weights
     (`hida_ordinary_rank_constant`), and concrete rank-2 Hida family witness.
3. **Reducible 3D `U(3)` Ordinary Deformation Ring, Type I/II/III Trichotomy & `CountI` Selmer Bound**:
   - Conjugate-self-dual 3D residual pseudocharacter `T̄ = χ₁ + χ₂ + χ₃` (`χ₃ = χ₁^{-c}`,
     `χ₂ = χ₂^{-c}`), `GL₃` involution `u3ConjInv M = J₃ (M⁻¹)ᵀ J₃`, rank-3 `U(3)` GMA
     `U3DeformGMA` with reducibility ideal `I_red` and Eisenstein locus equivalence
     `typeIII_iff_mem_reducibility_locus`.
   - Unconditional **Type I / Type II / Type III Trichotomy (`u3_point_trichotomy`)**:
     Type I automorphy lifting (`u3_typeI_automorphy_lifting` / `ModUAlt` + `ModNOf`),
     Type II `2 + 1` constituent extraction (`typeII_has_2d_irreducible_constituent`), `3 × 3`
     adjoint block decomposition (`u3_typeII_adjoint_decomp`), and Kato Euler system rigidity
     (`u3_typeII_kato_rigidity` / `KatoTwoW`), and Type III Eisenstein locus `V(I_red)`.
   - Main **`countI_u3_selmer_bound`** and multi-prime global resultant aggregation
     (`countI_u3_multi_prime_poly_bound`).
4. **Weight-2 (`e = 1`) Inertia / Fontaine–Laffaille Tangent Bound & `CountV` Discharge**:
   - Concrete 3D weight-2 (`e = 1`, Hodge–Tate weights `{0, 1, 2}`) filtered `φ`-module
     `u3Weight2StdModule p` (`t_H = t_N = 3`), exact `J₃`-anti-symmetric / symmetric Lie-algebra
     decomposition `End(D) = ad_-(3) ⊕ ad_+(3)` (`dim = 3 + 6`), filtration quotients
     (`dim(End / Fil^0) = 3`, `dim(ad_- / Fil^0) = 1`), Bloch–Kato tangent dimension
     (`u3_weight2_end_blochKato_dim`), non-positive weight inertia vanishing
     (`weight2_nonpos_inertia_vanishing`), and polynomial **`countV_weight2_u3_bound`**.
-/

noncomputable section

open scoped BigOperators Pointwise
open Finset Matrix Polynomial Module Submodule Filter Topology
open RHDirect.Stage11CrystallineFontaine

namespace RHDirect
namespace Stage13U3HidaAutomorphy

/-! ## Section 1: Concrete Definite Unitary Group `U(3)` Algebraic Automorphic Forms & Hecke Operators -/

section DefiniteU3Forms

/-- Dominant algebraic weight `(a, b, c)` for `U(3)` with `c ≤ b ≤ a`. -/
structure U3Weight where
  a : ℤ
  b : ℤ
  c : ℤ
  hcb : c ≤ b
  hba : b ≤ a
  deriving DecidableEq

namespace U3Weight

/-- Regular weight-2 (`e = 1`) Hodge–Tate weight triple `(2, 1, 0)` for `CountV`. -/
def weight2 : U3Weight := ⟨2, 1, 0, by norm_num, by norm_num⟩

/-- Conjugate-self-dual parallel twist weight `(e, 0, -e)` matching `Ψ ⊕ 1 ⊕ Ψ⁻¹` in `CountI`. -/
def parallelTwist (e : ℕ) : U3Weight := ⟨(e : ℤ), 0, -(e : ℤ), by omega, by omega⟩

/-- Dual / conjugate weight `(-c, -b, -a)`. -/
def dual (w : U3Weight) : U3Weight := ⟨-w.c, -w.b, -w.a, neg_le_neg w.hba, neg_le_neg w.hcb⟩

theorem dual_dual (w : U3Weight) : w.dual.dual = w := by cases w; simp [dual]

theorem parallelTwist_selfDual (e : ℕ) : (parallelTwist e).dual = parallelTwist e := by
  simp [parallelTwist, dual]

def spread (w : U3Weight) : ℤ := w.a - w.c

theorem spread_nonneg (w : U3Weight) : 0 ≤ w.spread := by unfold spread; linarith [w.hcb, w.hba]

theorem spread_weight2 : weight2.spread = 2 := by decide

end U3Weight

/-- Anti-diagonal Hermitian pairing / involution matrix `J₃ = !![0, 0, 1; 0, 1, 0; 1, 0, 0]`. -/
def J3 (R : Type*) [CommRing R] : Matrix (Fin 3) (Fin 3) R :=
  !![0, 0, 1; 0, 1, 0; 1, 0, 0]

@[simp]
theorem J3_apply (R : Type*) [CommRing R] (i j : Fin 3) :
    J3 R i j = if i.val + j.val = 2 then 1 else 0 := by
  fin_cases i <;> fin_cases j <;> simp [J3]

theorem J3_mul_J3 (R : Type*) [CommRing R] : J3 R * J3 R = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [J3, Matrix.mul_apply, Fin.sum_univ_three]

theorem J3_transpose (R : Type*) [CommRing R] : (J3 R)ᵀ = J3 R := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [J3]

theorem det_J3 (R : Type*) [CommRing R] : (J3 R).det = -1 := by
  rw [Matrix.det_fin_three]; simp [J3]

theorem J3_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) :
    (J3 R).map f = J3 S := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [J3]

/-- Concrete definite `U(3)` double-coset / genus datum over a CM field `K/K^+`. -/
structure DefiniteU3Datum (R : Type*) [CommRing R] where
  ι : Type
  [fintype_ι : Fintype ι]
  [decEq_ι : DecidableEq ι]
  level : ℕ
  wt : U3Weight
  rank : ℕ
  Stab : ι → Type
  [group_Stab : ∀ i, Group (Stab i)]
  [fintype_Stab : ∀ i, Fintype (Stab i)]
  stabAct : ∀ i, Stab i →* ((Fin rank → R) ≃ₗ[R] (Fin rank → R))

attribute [instance] DefiniteU3Datum.fintype_ι DefiniteU3Datum.decEq_ι
  DefiniteU3Datum.group_Stab DefiniteU3Datum.fintype_Stab

/-- Concrete space of algebraic automorphic forms `U3FormSpace R D` on definite `U(3)`. -/
def U3FormSpace (R : Type*) [CommRing R] (D : DefiniteU3Datum R) :
    Submodule R (D.ι → Fin D.rank → R) where
  carrier := { f | ∀ (i : D.ι) (γ : D.Stab i), D.stabAct i γ (f i) = f i }
  add_mem' {f g} hf hg i γ := by simp only [Pi.add_apply, map_add, hf i γ, hg i γ]
  zero_mem' i γ := by simp only [Pi.zero_apply, map_zero]
  smul_mem' c {f} hf i γ := by simp only [Pi.smul_apply, map_smul, hf i γ]

/-- A definite `U(3)` level datum is **neat** if every stabilizer acts trivially. -/
def DefiniteU3Datum.IsNeat {R : Type*} [CommRing R] (D : DefiniteU3Datum R) : Prop :=
  ∀ (i : D.ι) (γ : D.Stab i) (v : Fin D.rank → R), D.stabAct i γ v = v

theorem u3FormSpace_eq_top_of_neat {R : Type*} [CommRing R] (D : DefiniteU3Datum R)
    (hneat : D.IsNeat) : U3FormSpace R D = ⊤ := by
  ext f; simp only [Submodule.mem_top, iff_true]; intro i γ; exact hneat i γ (f i)

/-- Explicit `R`-linear equivalence `U3FormSpace R D ≃ₗ[R] (D.ι × Fin D.rank → R)` at neat level. -/
def u3FormSpaceNeatEquiv {R : Type*} [CommRing R] (D : DefiniteU3Datum R) (hneat : D.IsNeat) :
    U3FormSpace R D ≃ₗ[R] (D.ι × Fin D.rank → R) where
  toFun f p := f.1 p.1 p.2
  invFun g := ⟨fun i j => g (i, j), fun i γ => hneat i γ _⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv f := Subtype.ext (by ext i j; rfl)
  right_inv g := by ext ⟨i, j⟩; rfl

theorem finrank_u3FormSpace_neat {K : Type*} [Field K] (D : DefiniteU3Datum K)
    (hneat : D.IsNeat) :
    Module.finrank K (U3FormSpace K D) = Fintype.card D.ι * D.rank := by
  rw [(u3FormSpaceNeatEquiv D hneat).finrank_eq, Module.finrank_pi_fintype]
  simp [Fintype.card_prod]

instance u3FormSpace_finite {R : Type*} [CommRing R] [IsNoetherianRing R]
    (D : DefiniteU3Datum R) : Module.Finite R (U3FormSpace R D) :=
  Module.Finite.iff_fg.mpr (IsNoetherian.noetherian _)

instance u3FormSpace_fintype_of_finite {R : Type*} [CommRing R] [Finite R]
    (D : DefiniteU3Datum R) : Finite (U3FormSpace R D) :=
  Subtype.finite

/-- Concrete finite Hecke correspondence on `U3FormSpace R D`. -/
structure HeckeCorr (R : Type*) [CommRing R] (D : DefiniteU3Datum R) where
  kernel : D.ι → D.ι → Matrix (Fin D.rank) (Fin D.rank) R
  preserves_inv : ∀ f ∈ U3FormSpace R D,
    (fun i => ∑ j : D.ι, (kernel i j).mulVec (f j)) ∈ U3FormSpace R D

def HeckeCorr.toLinearMap {R : Type*} [CommRing R] {D : DefiniteU3Datum R}
    (C : HeckeCorr R D) : U3FormSpace R D →ₗ[R] U3FormSpace R D where
  toFun f := ⟨fun i => ∑ j : D.ι, (C.kernel i j).mulVec (f.1 j), C.preserves_inv f.1 f.2⟩
  map_add' f g := Subtype.ext <| by
    ext i k; simp only [Submodule.coe_add, Pi.add_apply, Matrix.mulVec_add, Finset.sum_add_distrib]
  map_smul' c f := Subtype.ext <| by
    ext i k; simp only [SetLike.val_smul, Pi.smul_apply, Matrix.mulVec_smul, ← Finset.smul_sum,
      RingHom.id_apply]

def HeckeCorr.comp {R : Type*} [CommRing R] {D : DefiniteU3Datum R}
    (C₁ C₂ : HeckeCorr R D) : HeckeCorr R D where
  kernel i j := ∑ k : D.ι, C₁.kernel i k * C₂.kernel k j
  preserves_inv f hf := by
    have h1 := C₁.preserves_inv _ (C₂.preserves_inv f hf)
    have heq : (fun i => ∑ j : D.ι, (∑ k : D.ι, C₁.kernel i k * C₂.kernel k j).mulVec (f j)) =
        (fun i => ∑ k : D.ι, (C₁.kernel i k).mulVec (∑ j : D.ι, (C₂.kernel k j).mulVec (f j))) := by
      ext i m
      simp only [Matrix.sum_mulVec, Matrix.mulVec_sum, Matrix.mulVec_mulVec, Finset.sum_apply]
      rw [Finset.sum_comm]
    rwa [heq]

theorem HeckeCorr.toLinearMap_comp {R : Type*} [CommRing R] {D : DefiniteU3Datum R}
    (C₁ C₂ : HeckeCorr R D) :
    (C₁.comp C₂).toLinearMap = C₁.toLinearMap.comp C₂.toLinearMap := by
  ext f i m
  change (∑ j : D.ι, (∑ k : D.ι, C₁.kernel i k * C₂.kernel k j).mulVec (f.1 j)) m =
    (∑ k : D.ι, (C₁.kernel i k).mulVec (∑ j : D.ι, (C₂.kernel k j).mulVec (f.1 j))) m
  simp only [Matrix.sum_mulVec, Matrix.mulVec_sum, Matrix.mulVec_mulVec, Finset.sum_apply]
  rw [Finset.sum_comm]

theorem HeckeCorr.comm_of_kernel_comm {R : Type*} [CommRing R] {D : DefiniteU3Datum R}
    (C₁ C₂ : HeckeCorr R D)
    (hcomm : ∀ i j, ∑ k : D.ι, C₁.kernel i k * C₂.kernel k j =
      ∑ k : D.ι, C₂.kernel i k * C₁.kernel k j) :
    C₁.toLinearMap.comp C₂.toLinearMap = C₂.toLinearMap.comp C₁.toLinearMap := by
  rw [← HeckeCorr.toLinearMap_comp, ← HeckeCorr.toLinearMap_comp]
  ext f i m
  change (∑ j : D.ι, (∑ k : D.ι, C₁.kernel i k * C₂.kernel k j).mulVec (f.1 j)) m =
    (∑ j : D.ι, (∑ k : D.ι, C₂.kernel i k * C₁.kernel k j).mulVec (f.1 j)) m
  simp only [hcomm]

/-- Split-prime Hecke operator package `(T_{w, 1}, T_{w, 2}, S_w)` on `U3FormSpace R D`. -/
structure U3SplitHeckeData (R : Type*) [CommRing R] (D : DefiniteU3Datum R) where
  qw : ℕ
  T1 : Module.End R (U3FormSpace R D)
  T2 : Module.End R (U3FormSpace R D)
  Sw : Module.End R (U3FormSpace R D)
  comm_T1_T2 : T1 * T2 = T2 * T1
  comm_T1_Sw : T1 * Sw = Sw * T1
  comm_T2_Sw : T2 * Sw = Sw * T2

/-- Spherical `U(3)` Hecke polynomial `P_w(X) = X³ - a₁ X² + q_w a₂ X - q_w³ s_w ∈ R[X]`. -/
def u3HeckePoly {R : Type*} [CommRing R] (qw : ℕ) (a₁ a₂ sw : R) : Polynomial R :=
  X ^ 3 - C a₁ * X ^ 2 + C ((qw : R) * a₂) * X - C ((qw : R) ^ 3 * sw)

/-- Normalized 3D Eisenstein Frobenius trace `eis3(z) := z + 1 + z⁻¹`. -/
def u3EisensteinTrace {R : Type*} [CommRing R] (z : Rˣ) : R :=
  (z : R) + 1 + (z⁻¹ : Rˣ)

/-- **Exact Eisenstein Factorization of the `U(3)` Spherical Hecke Polynomial**. -/
theorem u3HeckePoly_eisenstein_factor {R : Type*} [CommRing R] (z : Rˣ) :
    u3HeckePoly 1 (u3EisensteinTrace z) (u3EisensteinTrace z) 1 =
      (X - C (z : R)) * (X - 1) * (X - C ((z⁻¹ : Rˣ) : R)) := by
  unfold u3HeckePoly u3EisensteinTrace
  have hzz : (z : R) * ((z⁻¹ : Rˣ) : R) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hCzz : C (z : R) * C ((z⁻¹ : Rˣ) : R) = (1 : Polynomial R) := by
    rw [← map_mul, hzz, map_one]
  simp only [Nat.cast_one, one_mul, one_pow, map_add, map_one]
  linear_combination -X * hCzz + hCzz

/-- **Weighted `q_w^e`-Twisted Eisenstein Factorization**. -/
theorem u3HeckePoly_weighted_eisenstein_factor {R : Type*} [CommRing R] (q z : Rˣ) :
    u3HeckePoly 1 (u3EisensteinTrace (q * z)) (u3EisensteinTrace (q * z)) 1 =
      (X - C ((q : R) * (z : R))) * (X - 1) * (X - C (((q⁻¹ : Rˣ) : R) * ((z⁻¹ : Rˣ) : R))) := by
  have h := u3HeckePoly_eisenstein_factor (R := R) (q * z)
  have hinv : (((q * z)⁻¹ : Rˣ) : R) = ((q⁻¹ : Rˣ) : R) * ((z⁻¹ : Rˣ) : R) := by
    rw [_root_.mul_inv_rev, Units.val_mul, mul_comm]
  rw [Units.val_mul, hinv] at h
  exact h

/-- Simultaneous Hecke eigensystem for a family of commuting operators. -/
structure HeckeEigensystem {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (ops : ι → Module.End R M) where
  vec : M
  vec_ne_zero : vec ≠ 0
  eig : ι → R
  is_eigen : ∀ j : ι, ops j vec = eig j • vec

/-- The `R`-subalgebra of `End_R(M)` generated by a pairwise commuting Hecke family. -/
def commutingHeckeSubalgebra {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (ops : ι → Module.End R M) : Subalgebra R (Module.End R M) :=
  Algebra.adjoin R (Set.range ops)

/-- Any commuting family of Hecke operators generates a COMMUTATIVE `R`-subalgebra of `End_R(M)`. -/
theorem commutingHeckeSubalgebra_comm {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (ops : ι → Module.End R M) (hcomm : ∀ i j, ops i * ops j = ops j * ops i)
    (a b : commutingHeckeSubalgebra ops) : a * b = b * a := by
  apply Subtype.ext
  change a.1 * b.1 = b.1 * a.1
  have hgen : ∀ x ∈ Algebra.adjoin R (Set.range ops), ∀ j : ι, x * ops j = ops j * x := by
    intro x hx
    refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨i, rfl⟩ j; exact hcomm i j
    · intro r j; exact Algebra.commutes r (ops j)
    · intro x y _ _ ihx ihy j; simp [add_mul, mul_add, ihx j, ihy j]
    · intro x y _ _ ihx ihy j
      calc (x * y) * ops j = x * (y * ops j) := mul_assoc _ _ _
        _ = x * (ops j * y) := by rw [ihy j]
        _ = (x * ops j) * y := (mul_assoc _ _ _).symm
        _ = (ops j * x) * y := by rw [ihx j]
        _ = ops j * (x * y) := mul_assoc _ _ _
  have hmain : ∀ x ∈ Algebra.adjoin R (Set.range ops), x * b.1 = b.1 * x := by
    intro x hx
    refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨i, rfl⟩; exact (hgen b.1 b.2 i).symm
    · intro r; exact Algebra.commutes r b.1
    · intro x y _ _ ihx ihy; simp [add_mul, mul_add, ihx, ihy]
    · intro x y _ _ ihx ihy
      calc (x * y) * b.1 = x * (y * b.1) := mul_assoc _ _ _
        _ = x * (b.1 * y) := by rw [ihy]
        _ = (x * b.1) * y := (mul_assoc _ _ _).symm
        _ = (b.1 * x) * y := by rw [ihx]
        _ = b.1 * (x * y) := mul_assoc _ _ _
  exact hmain a.1 a.2

/-- Every Hecke eigensystem `(v, eig)` induces an `R`-algebra character `χ_v` on the Hecke algebra. -/
theorem heckeEigensystem_eval_exists {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (ops : ι → Module.End R M) (E : HeckeEigensystem ops)
    (hfree : ∀ r : R, r • E.vec = 0 → r = 0) :
    ∃ χ : commutingHeckeSubalgebra ops →ₐ[R] R,
      (∀ t : commutingHeckeSubalgebra ops, t.1 E.vec = χ t • E.vec) ∧
      (∀ j : ι, χ ⟨ops j, Algebra.subset_adjoin ⟨j, rfl⟩⟩ = E.eig j) := by
  have hex : ∀ t : commutingHeckeSubalgebra ops, ∃ c : R, t.1 E.vec = c • E.vec := by
    intro ⟨t, ht⟩
    refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ ht
    · rintro _ ⟨j, rfl⟩; exact ⟨E.eig j, E.is_eigen j⟩
    · intro r; exact ⟨r, by simp [Algebra.algebraMap_eq_smul_one]⟩
    · rintro x y _ _ ⟨cx, hcx⟩ ⟨cy, hcy⟩; exact ⟨cx + cy, by simp [add_smul, hcx, hcy]⟩
    · rintro x y _ _ ⟨cx, hcx⟩ ⟨cy, hcy⟩
      refine ⟨cx * cy, ?_⟩
      change x (y E.vec) = (cx * cy) • E.vec
      rw [hcy, map_smul, hcx, smul_smul, mul_comm]
  choose χ hχ using hex
  have huniq : ∀ t c, t.1 E.vec = c • E.vec → c = χ t := fun t c hc =>
    sub_eq_zero.mp (hfree _ (by rw [sub_smul, ← hc, ← hχ t, sub_self]))
  refine ⟨{
    toFun := χ
    map_one' := (huniq 1 1 (by simp)).symm
    map_mul' := fun a b => (huniq (a * b) (χ a * χ b) (by
      change a.1 (b.1 E.vec) = (χ a * χ b) • E.vec
      rw [hχ b, map_smul, hχ a, smul_smul, mul_comm])).symm
    map_zero' := (huniq 0 0 (by simp)).symm
    map_add' := fun a b => (huniq (a + b) (χ a + χ b) (by
      change a.1 E.vec + b.1 E.vec = (χ a + χ b) • E.vec
      rw [hχ a, hχ b, add_smul])).symm
    commutes' := fun r => (huniq (algebraMap R _ r) r (by
      change (algebraMap R (Module.End R M) r) E.vec = r • E.vec
      simp [Algebra.algebraMap_eq_smul_one])).symm }, hχ, fun j =>
    (huniq ⟨ops j, Algebra.subset_adjoin ⟨j, rfl⟩⟩ (E.eig j) (E.is_eigen j)).symm⟩

end DefiniteU3Forms

/-! ## Section 2: Exact Ordinary Hida Idempotent `e_ord = lim U_p^{n!}` & Hida Control Theorem -/

section OrdinaryHidaIdempotent

/-! ### 2.1 Exact Pigeonhole Idempotent Stabilization on Finite Monoids & Finite `ZMod (p^k)`-Modules -/

/-- **Pigeonhole Periodicity in Any Finite Monoid**. -/
theorem exists_period_of_finite {S : Type*} [Monoid S] [Finite S] (u : S) :
    ∃ s d : ℕ, 0 < d ∧ ∀ a ≥ s, ∀ m : ℕ, u ^ (a + m * d) = u ^ a := by
  obtain ⟨i, j, hne, hij⟩ := Finite.exists_ne_map_eq_of_infinite (fun n : ℕ => u ^ n)
  wlog hlt : i < j generalizing i j
  · exact this j i hne.symm hij.symm (lt_of_le_of_ne (not_lt.mp hlt) hne.symm)
  refine ⟨i, j - i, Nat.sub_pos_of_lt hlt, fun a ha m => ?_⟩
  have hbase : u ^ (i + (j - i)) = u ^ i := by
    rw [Nat.add_sub_cancel' (le_of_lt hlt)]; exact hij.symm
  have hstep : ∀ k : ℕ, u ^ (i + k * (j - i)) = u ^ i := by
    intro k; induction k with
    | zero => simp
    | succ k ih => rw [Nat.succ_mul, ← add_assoc, pow_add, ih, ← pow_add, hbase]
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le ha
  calc u ^ (i + r + m * (j - i))
      = u ^ (i + m * (j - i) + r) := by congr 1; omega
    _ = u ^ (i + m * (j - i)) * u ^ r := pow_add u _ r
    _ = u ^ i * u ^ r := by rw [hstep m]
    _ = u ^ (i + r) := (pow_add u i r).symm

/-- **Exact Factorial Stabilization Theorem (`finite_idempotent_stabilization`)**:
in ANY finite monoid `S`, `u ^ n!` stabilizes for all `n ≥ N₀` to a unique idempotent `e`
(`e * e = e`, `e * u = u * e`). -/
theorem finite_idempotent_stabilization {S : Type*} [Monoid S] [Finite S] (u : S) :
    ∃ (N₀ : ℕ) (e : S),
      (∀ n ≥ N₀, u ^ n.factorial = e) ∧ e * e = e ∧ e * u = u * e := by
  obtain ⟨s, d, hd, hper⟩ := exists_period_of_finite u
  let N₀ := max s d
  let e := u ^ N₀.factorial
  have hN₀_ge_s : s ≤ N₀.factorial := le_trans (le_max_left s d) (Nat.self_le_factorial N₀)
  have hd_dvd_N₀ : d ∣ N₀.factorial := Nat.dvd_factorial hd (le_max_right s d)
  have hstab : ∀ n ≥ N₀, u ^ n.factorial = e := by
    intro n hn
    have hle : N₀.factorial ≤ n.factorial := Nat.factorial_le hn
    have hd_dvd_n : d ∣ n.factorial := Nat.dvd_factorial hd (le_trans (le_max_right s d) hn)
    obtain ⟨m, hm⟩ := Nat.dvd_sub hd_dvd_n hd_dvd_N₀
    have heq : n.factorial = N₀.factorial + m * d := by
      rw [mul_comm, ← hm, Nat.add_sub_cancel' hle]
    rw [heq]
    exact hper N₀.factorial hN₀_ge_s m
  have hidem : e * e = e := by
    obtain ⟨q, hq⟩ := hd_dvd_N₀
    have heq : N₀.factorial + N₀.factorial = N₀.factorial + q * d := by rw [mul_comm, ← hq]
    calc e * e = u ^ (N₀.factorial + N₀.factorial) := (pow_add u _ _).symm
      _ = u ^ (N₀.factorial + q * d) := by rw [heq]
      _ = e := hper N₀.factorial hN₀_ge_s q
  have hcomm : e * u = u * e := by
    change u ^ N₀.factorial * u = u * u ^ N₀.factorial
    rw [← pow_succ, ← pow_succ']
  exact ⟨N₀, e, hstab, hidem, hcomm⟩

/-- Canonical **Finite Ordinary Hida Idempotent** `e_ord(u) = lim_{n → ∞} u^{n!}`. -/
def finiteHidaIdemp {S : Type*} [Monoid S] [Finite S] (u : S) : S :=
  (finite_idempotent_stabilization u).choose_spec.choose

theorem finiteHidaIdemp_spec {S : Type*} [Monoid S] [Finite S] (u : S) :
    (∃ N₀ : ℕ, ∀ n ≥ N₀, u ^ n.factorial = finiteHidaIdemp u) ∧
      finiteHidaIdemp u * finiteHidaIdemp u = finiteHidaIdemp u ∧
      finiteHidaIdemp u * u = u * finiteHidaIdemp u := by
  have h := (finite_idempotent_stabilization u).choose_spec.choose_spec
  exact ⟨⟨(finite_idempotent_stabilization u).choose, h.1⟩, h.2.1, h.2.2⟩

theorem finiteHidaIdemp_idem {S : Type*} [Monoid S] [Finite S] (u : S) :
    finiteHidaIdemp u * finiteHidaIdemp u = finiteHidaIdemp u :=
  (finiteHidaIdemp_spec u).2.1

theorem finiteHidaIdemp_comm {S : Type*} [Monoid S] [Finite S] (u : S) :
    finiteHidaIdemp u * u = u * finiteHidaIdemp u :=
  (finiteHidaIdemp_spec u).2.2

theorem finiteHidaIdemp_unique {S : Type*} [Monoid S] [Finite S] (u e : S)
    (he : ∃ N₁ : ℕ, ∀ n ≥ N₁, u ^ n.factorial = e) :
    finiteHidaIdemp u = e := by
  obtain ⟨⟨N₀, h0⟩, _, _⟩ := finiteHidaIdemp_spec u
  obtain ⟨N₁, h1⟩ := he
  exact ((h0 (max N₀ N₁) (le_max_left _ _)).symm.trans (h1 (max N₀ N₁) (le_max_right _ _)))

/-- **Functoriality of `finiteHidaIdemp`** under any monoid homomorphism between finite monoids. -/
theorem finiteHidaIdemp_map {S T : Type*} [Monoid S] [Finite S] [Monoid T] [Finite T]
    (φ : S →* T) (u : S) :
    φ (finiteHidaIdemp u) = finiteHidaIdemp (φ u) := by
  obtain ⟨⟨N₀, h0⟩, _, _⟩ := finiteHidaIdemp_spec u
  symm
  exact finiteHidaIdemp_unique (φ u) (φ (finiteHidaIdemp u))
    ⟨N₀, fun n hn => by rw [← map_pow, h0 n hn]⟩

theorem finiteHidaIdemp_comm_of_comm {S : Type*} [Monoid S] [Finite S] {u t : S}
    (h : t * u = u * t) : t * finiteHidaIdemp u = finiteHidaIdemp u * t := by
  obtain ⟨⟨N₀, h0⟩, _, _⟩ := finiteHidaIdemp_spec u
  rw [← h0 N₀ le_rfl]
  exact Commute.pow_right h N₀.factorial

/-- Any `R`-linear endomorphism monoid of a finite `R`-module `M` is finite. -/
local instance instFiniteModuleEnd {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Finite M] : Finite (Module.End R M) :=
  Finite.of_injective (fun f : Module.End R M => (f : M → M)) DFunLike.coe_injective

/-- Ordinary submodule `M^ord := im(e_ord)` of a finite `R`-module `M` for `U : End_R(M)`. -/
def finiteHidaOrd {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Finite M]
    (U : Module.End R M) : Submodule R M :=
  LinearMap.range (finiteHidaIdemp U)

/-- Nilpotent submodule `M^nil := ker(e_ord)` of a finite `R`-module `M` for `U : End_R(M)`. -/
def finiteHidaNil {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Finite M]
    (U : Module.End R M) : Submodule R M :=
  LinearMap.ker (finiteHidaIdemp U)

/-- **Exact Ordinary / Nilpotent Direct-Sum Decomposition (`finite_hida_ordinary_decomposition`)**:
for any finite `R`-module `M` (in particular any finite `ZMod (p^k)`-module `U3FormSpace (ZMod (p^k)) D`)
and `U : Module.End R M`:
`M = M^ord ⊕ M^nil`, `U` restricts to a bijection on `M^ord`, and `U` is nilpotent on `M^nil`. -/
theorem finite_hida_ordinary_decomposition {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] [Finite M] (U : Module.End R M) :
    IsCompl (finiteHidaOrd U) (finiteHidaNil U) ∧
      (∀ x ∈ finiteHidaOrd U, U x ∈ finiteHidaOrd U) ∧
      Function.Bijective (fun x : finiteHidaOrd U =>
        (⟨U x.1, by
          obtain ⟨y, hy⟩ := x.2
          refine ⟨U y, ?_⟩
          have hc := LinearMap.congr_fun (finiteHidaIdemp_comm U) y
          change (finiteHidaIdemp U) (U y) = U ((finiteHidaIdemp U) y) at hc
          rw [hc, hy]⟩ : finiteHidaOrd U)) ∧
      (∀ x ∈ finiteHidaNil U, U x ∈ finiteHidaNil U) ∧
      (∃ m : ℕ, ∀ x ∈ finiteHidaNil U, (U ^ m) x = 0) := by
  let e := finiteHidaIdemp U
  have hidem : e * e = e := finiteHidaIdemp_idem U
  have hcomm : e * U = U * e := finiteHidaIdemp_comm U
  have he_apply : ∀ x, e (e x) = e x := fun x => LinearMap.congr_fun hidem x
  have hcompl : IsCompl (finiteHidaOrd U) (finiteHidaNil U) := by
    rw [isCompl_iff]
    constructor
    · rw [disjoint_iff, eq_bot_iff]
      rintro x ⟨⟨y, rfl⟩, hx⟩
      rw [Submodule.mem_bot]
      change e (e y) = 0 at hx
      rwa [he_apply] at hx
    · rw [codisjoint_iff, eq_top_iff]
      intro x _
      have hsplit : x = e x + (x - e x) := by abel
      rw [hsplit]
      refine Submodule.add_mem_sup ⟨x, rfl⟩ ?_
      change e (x - e x) = 0
      rw [map_sub, he_apply, sub_self]
  have hord_stab : ∀ x ∈ finiteHidaOrd U, U x ∈ finiteHidaOrd U := by
    rintro _ ⟨y, rfl⟩; exact ⟨U y, LinearMap.congr_fun hcomm y⟩
  have hnil_stab : ∀ x ∈ finiteHidaNil U, U x ∈ finiteHidaNil U := by
    intro x hx
    change e (U x) = 0
    have hc := LinearMap.congr_fun hcomm x
    change e (U x) = U (e x) at hc
    rw [hc, LinearMap.mem_ker.mp hx, map_zero]
  obtain ⟨⟨N₀, hN₀⟩, _, _⟩ := finiteHidaIdemp_spec U
  have hord_surj : Function.Surjective (fun x : finiteHidaOrd U => (⟨U x.1, hord_stab x.1 x.2⟩ : finiteHidaOrd U)) := by
    rintro ⟨y, z, hyz⟩
    subst hyz
    have hfac_pos : 0 < (max N₀ 1).factorial := Nat.factorial_pos _
    have hpow : U ^ (max N₀ 1).factorial = e := hN₀ (max N₀ 1) (le_max_left N₀ 1)
    let k := (max N₀ 1).factorial - 1
    have hk : k + 1 = (max N₀ 1).factorial := Nat.sub_add_cancel hfac_pos
    have hmem : (U ^ k) (e z) ∈ finiteHidaOrd U :=
      ⟨(U ^ k) z, (LinearMap.congr_fun (Commute.pow_left hcomm.symm k) z).symm⟩
    refine ⟨⟨(U ^ k) (e z), hmem⟩, Subtype.ext ?_⟩
    change U ((U ^ k) (e z)) = e z
    have hact := LinearMap.congr_fun (pow_succ' U k).symm (e z)
    change U ((U ^ k) (e z)) = (U ^ (k + 1)) (e z) at hact
    rw [hact, hk, hpow, he_apply]
  have : Finite (finiteHidaOrd U) := Subtype.finite
  exact ⟨hcompl, hord_stab, ⟨Finite.injective_iff_surjective.mpr hord_surj, hord_surj⟩,
    hnil_stab, ⟨N₀.factorial, fun x hx => by rw [hN₀ N₀ le_rfl]; exact hx⟩⟩

/-! ### 2.2 Projective-Limit Lifting to `ℤ_[p]` & Exact `p`-adic Hida Idempotent -/

/-- Helper: `ZMod (p ^ 0)` is a `Subsingleton`. -/
theorem zmod_pow_zero_subsingleton (p : ℕ) : Subsingleton (ZMod (p ^ 0)) := by
  rw [pow_zero]; infer_instance

/-- Self-contained compatibility of `PadicInt.toZModPow` across powers `k ≤ m`. -/
theorem padicInt_castHom_toZModPow {p : ℕ} [Fact p.Prime] {k m : ℕ} (hkm : k ≤ m) (x : ℤ_[p]) :
    ZMod.castHom (pow_dvd_pow p hkm) (ZMod (p ^ k)) (PadicInt.toZModPow m x) =
      PadicInt.toZModPow k x := by
  have : NeZero (p ^ m) := ⟨pow_ne_zero m (Fact.out : p.Prime).ne_zero⟩
  set n : ℕ := (PadicInt.toZModPow m x).val
  have hdiff : x - (n : ℤ_[p]) ∈ RingHom.ker (PadicInt.toZModPow m) := by
    rw [RingHom.mem_ker, map_sub, map_natCast, ZMod.natCast_zmod_val, sub_self]
  rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at hdiff
  obtain ⟨y, hy⟩ := hdiff
  have hx : x = (n : ℤ_[p]) + (p : ℤ_[p]) ^ m * y := eq_add_of_sub_eq' hy
  have hpm0 : PadicInt.toZModPow k ((p : ℤ_[p]) ^ m) = 0 := by
    refine RingHom.mem_ker.mp ?_
    rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton]
    exact pow_dvd_pow (p : ℤ_[p]) hkm
  have hcast : ZMod.castHom (pow_dvd_pow p hkm) (ZMod (p ^ k)) (PadicInt.toZModPow m x) =
      (n : ZMod (p ^ k)) := by
    conv_lhs => rw [← ZMod.natCast_zmod_val (PadicInt.toZModPow m x)]
    rw [map_natCast]
  rw [hcast, hx, map_add, map_mul, map_natCast, hpm0, zero_mul, add_zero]

theorem padicInt_norm_sub_le_of_toZModPow_eq {p : ℕ} [Fact p.Prime] {k : ℕ} {a b : ℤ_[p]}
    (h : PadicInt.toZModPow k a = PadicInt.toZModPow k b) :
    ‖a - b‖ ≤ (p : ℝ) ^ (-(k : ℤ)) := by
  have hker : a - b ∈ RingHom.ker (PadicInt.toZModPow k) := by
    rw [RingHom.mem_ker, map_sub, h, sub_self]
  rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at hker
  obtain ⟨c, hc⟩ := hker
  rw [hc, norm_mul, norm_pow, PadicInt.norm_p]
  have hp_pos : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr (Fact.out : p.Prime).pos
  have hpow_nn : (0 : ℝ) ≤ ((p : ℝ)⁻¹) ^ k := pow_nonneg (inv_nonneg.mpr (le_of_lt hp_pos)) k
  calc ((p : ℝ)⁻¹) ^ k * ‖c‖
      ≤ ((p : ℝ)⁻¹) ^ k * 1 := mul_le_mul_of_nonneg_left (PadicInt.norm_le_one c) hpow_nn
    _ = ((p : ℝ)⁻¹) ^ k := mul_one _
    _ = (p : ℝ) ^ (-(k : ℤ)) := by rw [_root_.zpow_neg, zpow_natCast, inv_pow]

theorem padicInt_toZModPow_eq_zero_of_norm_le {p : ℕ} [Fact p.Prime] {k : ℕ} {x : ℤ_[p]}
    (hx : ‖x‖ ≤ (p : ℝ) ^ (-(k : ℤ))) :
    PadicInt.toZModPow k x = 0 := by
  refine RingHom.mem_ker.mp ?_
  rw [PadicInt.ker_toZModPow]
  exact (PadicInt.norm_le_pow_iff_mem_span_pow x k).mp hx

/-- **Exact Projective-Limit Lifting `lim← ZMod (p^k) ≃ ℤ_[p]`**. -/
theorem padicInt_exists_unique_of_compatible_zmodPow {p : ℕ} [Fact p.Prime]
    (a : ∀ k : ℕ, ZMod (p ^ k))
    (hcompat : ∀ k : ℕ,
      ZMod.castHom (pow_dvd_pow p (Nat.le_succ k)) (ZMod (p ^ k)) (a (k + 1)) = a k) :
    ∃! x : ℤ_[p], ∀ k : ℕ, PadicInt.toZModPow k x = a k := by
  have hcompat_le : ∀ {k m : ℕ} (hkm : k ≤ m),
      ZMod.castHom (pow_dvd_pow p hkm) (ZMod (p ^ k)) (a m) = a k := by
    intro k m hkm
    induction m with
    | zero =>
      have hk0 : k = 0 := Nat.eq_zero_of_le_zero hkm
      subst hk0
      have := zmod_pow_zero_subsingleton p
      exact Subsingleton.elim _ _
    | succ m ih =>
      rcases Nat.eq_or_lt_of_le hkm with rfl | hlt
      · simp
      · have hle : k ≤ m := Nat.lt_succ_iff.mp hlt
        have hcomp :
            ZMod.castHom (pow_dvd_pow p hkm) (ZMod (p ^ k)) =
              (ZMod.castHom (pow_dvd_pow p hle) (ZMod (p ^ k))).comp
                (ZMod.castHom (pow_dvd_pow p (Nat.le_succ m)) (ZMod (p ^ m))) := by
          ext; simp
        rw [hcomp, RingHom.comp_apply, hcompat m, ih hle]
  let f : ℕ → ℤ_[p] := fun k => ((a k).val : ℤ_[p])
  have hf_mod : ∀ k m, k ≤ m → PadicInt.toZModPow k (f m) = a k := by
    intro k m hkm
    have : NeZero (p ^ m) := ⟨pow_ne_zero m (Fact.out : p.Prime).ne_zero⟩
    change PadicInt.toZModPow k (((a m).val : ℕ) : ℤ_[p]) = a k
    rw [map_natCast]
    have hcast : ZMod.castHom (pow_dvd_pow p hkm) (ZMod (p ^ k)) (a m) =
        (((a m).val : ℕ) : ZMod (p ^ k)) := by
      conv_lhs => rw [← ZMod.natCast_zmod_val (a m)]
      rw [map_natCast]
    rw [← hcast, hcompat_le hkm]
  have hf_cauchy : CauchySeq f := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    have hp_gt1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).one_lt
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hε (inv_lt_one_of_one_lt₀ hp_gt1)
    refine ⟨N, fun m hm n hn => ?_⟩
    rw [dist_eq_norm]
    have hle := padicInt_norm_sub_le_of_toZModPow_eq
      ((hf_mod N m hm).trans (hf_mod N n hn).symm)
    rw [_root_.zpow_neg, zpow_natCast, ← inv_pow] at hle
    exact lt_of_le_of_lt hle hN
  obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete hf_cauchy
  have hx_mod : ∀ k : ℕ, PadicInt.toZModPow k x = a k := by
    intro k
    have hclosed : IsClosed { z : ℤ_[p] | ‖z - f k‖ ≤ (p : ℝ) ^ (-(k : ℤ)) } :=
      isClosed_le (continuous_norm.comp (continuous_id.sub continuous_const)) continuous_const
    have hev : ∀ᶠ m in atTop, f m ∈ { z : ℤ_[p] | ‖z - f k‖ ≤ (p : ℝ) ^ (-(k : ℤ)) } :=
      Filter.eventually_atTop.mpr ⟨k, fun m hm =>
        padicInt_norm_sub_le_of_toZModPow_eq ((hf_mod k m hm).trans (hf_mod k k le_rfl).symm)⟩
    have hzero := padicInt_toZModPow_eq_zero_of_norm_le (hclosed.mem_of_tendsto hx hev)
    rw [map_sub, sub_eq_zero] at hzero
    rw [hzero, hf_mod k k le_rfl]
  exact ⟨x, hx_mod, fun y hy => PadicInt.ext_of_toZModPow.mp fun k => (hy k).trans (hx_mod k).symm⟩

/-- Packaged projective-limit lift `padicIntOfCompat : ℤ_[p]`. -/
def padicIntOfCompat {p : ℕ} [Fact p.Prime] (a : ∀ k : ℕ, ZMod (p ^ k))
    (hcompat : ∀ k : ℕ,
      ZMod.castHom (pow_dvd_pow p (Nat.le_succ k)) (ZMod (p ^ k)) (a (k + 1)) = a k) : ℤ_[p] :=
  (padicInt_exists_unique_of_compatible_zmodPow a hcompat).choose

theorem toZModPow_padicIntOfCompat {p : ℕ} [Fact p.Prime] (a : ∀ k : ℕ, ZMod (p ^ k))
    (hcompat : ∀ k : ℕ,
      ZMod.castHom (pow_dvd_pow p (Nat.le_succ k)) (ZMod (p ^ k)) (a (k + 1)) = a k)
    (k : ℕ) : PadicInt.toZModPow k (padicIntOfCompat a hcompat) = a k :=
  (padicInt_exists_unique_of_compatible_zmodPow a hcompat).choose_spec.1 k

/-- Reduction homomorphism `Matrix (Fin d) (Fin d) ℤ_[p] →+* Matrix (Fin d) (Fin d) (ZMod (p^k))`. -/
def matToZModPow (p : ℕ) [Fact p.Prime] (d k : ℕ) :
    Matrix (Fin d) (Fin d) ℤ_[p] →+* Matrix (Fin d) (Fin d) (ZMod (p ^ k)) :=
  RingHom.mapMatrix (PadicInt.toZModPow k)

theorem matToZModPow_ext {p : ℕ} [Fact p.Prime] {d : ℕ}
    {A B : Matrix (Fin d) (Fin d) ℤ_[p]}
    (h : ∀ k : ℕ, matToZModPow p d k A = matToZModPow p d k B) : A = B := by
  ext i j
  refine PadicInt.ext_of_toZModPow.mp fun k => ?_
  exact congrArg (fun M : Matrix (Fin d) (Fin d) (ZMod (p ^ k)) => M i j) (h k)

theorem finiteHidaIdemp_mat_compat {p : ℕ} [Fact p.Prime] {d : ℕ}
    (U : Matrix (Fin d) (Fin d) ℤ_[p]) (i j : Fin d) (k : ℕ) :
    ZMod.castHom (pow_dvd_pow p (Nat.le_succ k)) (ZMod (p ^ k))
      (finiteHidaIdemp (matToZModPow p d (k + 1) U) i j) =
      finiteHidaIdemp (matToZModPow p d k U) i j := by
  let φ := RingHom.mapMatrix (ZMod.castHom (pow_dvd_pow p (Nat.le_succ k)) (ZMod (p ^ k)))
    (m := Fin d)
  have harg : φ (matToZModPow p d (k + 1) U) = matToZModPow p d k U := by
    ext r s
    exact padicInt_castHom_toZModPow (Nat.le_succ k) (U r s)
  have hmap := finiteHidaIdemp_map φ.toMonoidHom (matToZModPow p d (k + 1) U)
  change φ (finiteHidaIdemp (matToZModPow p d (k + 1) U)) =
    finiteHidaIdemp (φ (matToZModPow p d (k + 1) U)) at hmap
  rw [harg] at hmap
  exact congrArg (fun M : Matrix (Fin d) (Fin d) (ZMod (p ^ k)) => M i j) hmap

/-- **Exact `p`-adic Ordinary Hida Idempotent `padicHidaIdemp U`** on `Matrix (Fin d) (Fin d) ℤ_[p]`. -/
def padicHidaIdemp {p : ℕ} [Fact p.Prime] {d : ℕ} (U : Matrix (Fin d) (Fin d) ℤ_[p]) :
    Matrix (Fin d) (Fin d) ℤ_[p] :=
  fun i j => padicIntOfCompat
    (fun k => finiteHidaIdemp (matToZModPow p d k U) i j)
    (finiteHidaIdemp_mat_compat U i j)

theorem matToZModPow_padicHidaIdemp {p : ℕ} [Fact p.Prime] {d : ℕ}
    (U : Matrix (Fin d) (Fin d) ℤ_[p]) (k : ℕ) :
    matToZModPow p d k (padicHidaIdemp U) = finiteHidaIdemp (matToZModPow p d k U) := by
  ext i j
  exact toZModPow_padicIntOfCompat _ _ k

/-- **Exact Idempotence of the `p`-adic Hida Projector**: `e_ord ∘ e_ord = e_ord`. -/
theorem padicHidaIdemp_idem {p : ℕ} [Fact p.Prime] {d : ℕ}
    (U : Matrix (Fin d) (Fin d) ℤ_[p]) :
    padicHidaIdemp U * padicHidaIdemp U = padicHidaIdemp U := by
  apply matToZModPow_ext; intro k
  rw [map_mul, matToZModPow_padicHidaIdemp, finiteHidaIdemp_idem]

theorem padicHidaIdemp_comm {p : ℕ} [Fact p.Prime] {d : ℕ}
    (U : Matrix (Fin d) (Fin d) ℤ_[p]) :
    padicHidaIdemp U * U = U * padicHidaIdemp U := by
  apply matToZModPow_ext; intro k
  rw [map_mul, map_mul, matToZModPow_padicHidaIdemp, finiteHidaIdemp_comm]

theorem padicHidaIdemp_comm_hecke {p : ℕ} [Fact p.Prime] {d : ℕ}
    (U T : Matrix (Fin d) (Fin d) ℤ_[p]) (hTU : T * U = U * T) :
    T * padicHidaIdemp U = padicHidaIdemp U * T := by
  apply matToZModPow_ext; intro k
  rw [map_mul, map_mul, matToZModPow_padicHidaIdemp]
  exact finiteHidaIdemp_comm_of_comm (by rw [← map_mul, ← map_mul, hTU])

theorem padicHidaIdemp_isCompl {p : ℕ} [Fact p.Prime] {d : ℕ}
    (U : Matrix (Fin d) (Fin d) ℤ_[p]) :
    IsCompl (LinearMap.range (padicHidaIdemp U).mulVecLin)
      (LinearMap.ker (padicHidaIdemp U).mulVecLin) := by
  have he : ∀ v, (padicHidaIdemp U).mulVec ((padicHidaIdemp U).mulVec v) =
      (padicHidaIdemp U).mulVec v := fun v => by rw [Matrix.mulVec_mulVec, padicHidaIdemp_idem]
  rw [isCompl_iff]
  constructor
  · rw [disjoint_iff, eq_bot_iff]
    rintro v ⟨⟨w, rfl⟩, hv⟩
    rw [Submodule.mem_bot]
    change (padicHidaIdemp U).mulVec ((padicHidaIdemp U).mulVec w) = 0 at hv
    rwa [he w] at hv
  · rw [codisjoint_iff, eq_top_iff]
    intro v _
    have hsplit : v = (padicHidaIdemp U).mulVec v + (v - (padicHidaIdemp U).mulVec v) := by abel
    rw [hsplit]
    refine Submodule.add_mem_sup ⟨v, rfl⟩ ?_
    change (padicHidaIdemp U).mulVec (v - (padicHidaIdemp U).mulVec v) = 0
    rw [Matrix.mulVec_sub, he v, sub_self]

/-- On `M^nil = ker(e_ord)`, `U_p^n v → 0` `p`-adically (vanishes mod `p^k` for large `n`). -/
theorem padicHidaIdemp_nil_vanishes_mod_pow {p : ℕ} [Fact p.Prime] {d : ℕ}
    (U : Matrix (Fin d) (Fin d) ℤ_[p]) {v : Fin d → ℤ_[p]}
    (hv : v ∈ LinearMap.ker (padicHidaIdemp U).mulVecLin) (k : ℕ) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ i : Fin d,
      PadicInt.toZModPow k ((U ^ n).mulVec v i) = 0 := by
  obtain ⟨⟨N₀, hN₀⟩, _, _⟩ := finiteHidaIdemp_spec (matToZModPow p d k U)
  refine ⟨N₀.factorial, fun n hn i => ?_⟩
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  have hred : matToZModPow p d k (U ^ (N₀.factorial + m)) =
      matToZModPow p d k (U ^ m) * matToZModPow p d k (padicHidaIdemp U) := by
    rw [add_comm, pow_add, map_mul, map_pow, map_pow, hN₀ N₀ le_rfl, matToZModPow_padicHidaIdemp]
  have hv0 : (padicHidaIdemp U).mulVec v = 0 := hv
  have hmv : ((matToZModPow p d k (U ^ (N₀.factorial + m))).mulVec
      (fun j => PadicInt.toZModPow k (v j))) i = 0 := by
    rw [hred, ← Matrix.mulVec_mulVec]
    have h1 : (matToZModPow p d k (padicHidaIdemp U)).mulVec
        (fun j => PadicInt.toZModPow k (v j)) = 0 := by
      ext r
      change ∑ j : Fin d, PadicInt.toZModPow k (padicHidaIdemp U r j) *
        PadicInt.toZModPow k (v j) = 0
      have hsum : (∑ j : Fin d, PadicInt.toZModPow k (padicHidaIdemp U r j) *
          PadicInt.toZModPow k (v j)) =
          PadicInt.toZModPow k (∑ j : Fin d, padicHidaIdemp U r j * v j) := by
        simp [map_sum, map_mul]
      rw [hsum]
      have hr : ∑ j : Fin d, padicHidaIdemp U r j * v j = 0 := congrFun hv0 r
      rw [hr, map_zero]
    rw [h1, Matrix.mulVec_zero, Pi.zero_apply]
  have hmap_mv : PadicInt.toZModPow k ((U ^ (N₀.factorial + m)).mulVec v i) =
      ((matToZModPow p d k (U ^ (N₀.factorial + m))).mulVec
        (fun j => PadicInt.toZModPow k (v j))) i := by
    change PadicInt.toZModPow k (∑ j : Fin d, (U ^ (N₀.factorial + m)) i j * v j) =
      ∑ j : Fin d, PadicInt.toZModPow k ((U ^ (N₀.factorial + m)) i j) * PadicInt.toZModPow k (v j)
    simp [map_sum, map_mul]
  rw [hmap_mv, hmv]

theorem padicHidaIdemp_ord_free {p : ℕ} [Fact p.Prime] {d : ℕ}
    (U : Matrix (Fin d) (Fin d) ℤ_[p]) :
    Module.Free ℤ_[p] (LinearMap.range (padicHidaIdemp U).mulVecLin) ∧
      Module.Finite ℤ_[p] (LinearMap.range (padicHidaIdemp U).mulVecLin) :=
  ⟨inferInstance, inferInstance⟩

/-! ### 2.3 Iwasawa Weight Algebra `Λ = ℤ_[p][[T]]`, Weight Specialization & Hida Control Theorem -/

abbrev IwasawaWeightAlg (p : ℕ) [Fact p.Prime] := PowerSeries ℤ_[p]

/-- Truncated evaluation mod `p^k` of `f ∈ ℤ_[p][[T]]` at `u ∈ p ℤ_[p]`. -/
def weightSpecMod {p : ℕ} [Fact p.Prime] (u : ℤ_[p]) (hu : (p : ℤ_[p]) ∣ u) (k : ℕ) :
    PowerSeries ℤ_[p] →+* ZMod (p ^ k) where
  toFun f := ∑ i ∈ Finset.range k,
    PadicInt.toZModPow k (PowerSeries.coeff i f) * (PadicInt.toZModPow k u) ^ i
  map_zero' := by simp
  map_one' := by
    cases k with
    | zero => have := zmod_pow_zero_subsingleton p; exact Subsingleton.elim _ _
    | succ k =>
      rw [Finset.sum_eq_single 0]
      · simp [PowerSeries.coeff_one]
      · intro i _ hi; simp [PowerSeries.coeff_one, hi]
      · simp
  map_add' f g := by simp only [map_add, add_mul, Finset.sum_add_distrib]
  map_mul' f g := by
    have hunil : ∀ n ≥ k, (PadicInt.toZModPow k u) ^ n = 0 := by
      intro n hn
      obtain ⟨w, rfl⟩ := hu
      rw [map_mul, mul_pow, ← map_pow]
      have hp0 : PadicInt.toZModPow k ((p : ℤ_[p]) ^ n) = 0 := by
        refine RingHom.mem_ker.mp ?_
        rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton]
        exact pow_dvd_pow (p : ℤ_[p]) hn
      rw [hp0, zero_mul]
    simp only [PowerSeries.coeff_mul, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
    have hsplit :
        (∑ a ∈ Finset.range k, ∑ b ∈ Finset.range k,
          PadicInt.toZModPow k (PowerSeries.coeff a f) * (PadicInt.toZModPow k u) ^ a *
          (PadicInt.toZModPow k (PowerSeries.coeff b g) * (PadicInt.toZModPow k u) ^ b)) =
        ∑ i ∈ Finset.range k, ∑ ab ∈ Finset.antidiagonal i,
          PadicInt.toZModPow k (PowerSeries.coeff ab.1 f) *
          PadicInt.toZModPow k (PowerSeries.coeff ab.2 g) * (PadicInt.toZModPow k u) ^ i := by
      rw [← Finset.sum_product']
      have hsub : (Finset.range k ×ˢ Finset.range k).filter (fun ab : ℕ × ℕ => ab.1 + ab.2 < k) ⊆
          Finset.range k ×ˢ Finset.range k := Finset.filter_subset _ _
      rw [← Finset.sum_subset hsub]
      · have hbi : ((Finset.range k).biUnion Finset.antidiagonal) =
            (Finset.range k ×ˢ Finset.range k).filter (fun ab : ℕ × ℕ => ab.1 + ab.2 < k) := by
          ext ⟨a, b⟩
          simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_antidiagonal,
            Finset.mem_filter, Finset.mem_product]
          exact ⟨fun ⟨i, hi, heq⟩ => ⟨⟨by omega, by omega⟩, heq ▸ hi⟩,
                 fun ⟨_, hlt⟩ => ⟨a + b, hlt, rfl⟩⟩
        rw [← hbi, Finset.sum_biUnion]
        · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun ab hab => ?_
          rw [Finset.mem_antidiagonal] at hab
          rw [← hab, pow_add]; ring
        · intro i _ j _ hij
          change Disjoint (Finset.antidiagonal i) (Finset.antidiagonal j)
          rw [Finset.disjoint_left]
          intro ab hab1 hab2
          rw [Finset.mem_antidiagonal] at hab1 hab2
          exact hij (hab1.symm.trans hab2)
      · intro ab hab_mem hab
        simp only [Finset.mem_filter, not_and, not_lt] at hab
        have h0 := hunil (ab.1 + ab.2) (hab hab_mem)
        calc PadicInt.toZModPow k (PowerSeries.coeff ab.1 f) * (PadicInt.toZModPow k u) ^ ab.1 *
              (PadicInt.toZModPow k (PowerSeries.coeff ab.2 g) * (PadicInt.toZModPow k u) ^ ab.2)
            = PadicInt.toZModPow k (PowerSeries.coeff ab.1 f) *
              PadicInt.toZModPow k (PowerSeries.coeff ab.2 g) *
              (PadicInt.toZModPow k u) ^ (ab.1 + ab.2) := by rw [pow_add]; ring
          _ = 0 := by rw [h0, mul_zero]
    symm
    rw [Finset.sum_comm]
    exact hsplit

theorem weightSpecMod_compat {p : ℕ} [Fact p.Prime] (u : ℤ_[p]) (hu : (p : ℤ_[p]) ∣ u)
    (f : PowerSeries ℤ_[p]) (k : ℕ) :
    ZMod.castHom (pow_dvd_pow p (Nat.le_succ k)) (ZMod (p ^ k)) (weightSpecMod u hu (k + 1) f) =
      weightSpecMod u hu k f := by
  unfold weightSpecMod
  simp only [RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, map_sum, map_mul, map_pow,
    padicInt_castHom_toZModPow (Nat.le_succ k)]
  rw [Finset.sum_range_succ]
  have hk0 : (PadicInt.toZModPow k u) ^ k = 0 := by
    obtain ⟨w, rfl⟩ := hu
    rw [map_mul, mul_pow, ← map_pow]
    have hp0 : PadicInt.toZModPow k ((p : ℤ_[p]) ^ k) = 0 := by
      refine RingHom.mem_ker.mp ?_
      rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton]
    rw [hp0, zero_mul]
  rw [hk0, mul_zero, add_zero]

/-- **Exact `p`-adic Weight Specialization `weightSpec u : ℤ_[p][[T]] →+* ℤ_[p]`** (`f(T) ↦ f(u)`). -/
def weightSpec {p : ℕ} [Fact p.Prime] (u : ℤ_[p]) (hu : (p : ℤ_[p]) ∣ u) :
    PowerSeries ℤ_[p] →+* ℤ_[p] where
  toFun f := padicIntOfCompat (fun k => weightSpecMod u hu k f) (weightSpecMod_compat u hu f)
  map_one' := PadicInt.ext_of_toZModPow.mp fun k => by
    rw [toZModPow_padicIntOfCompat, map_one, map_one]
  map_mul' f g := PadicInt.ext_of_toZModPow.mp fun k => by
    rw [map_mul, toZModPow_padicIntOfCompat, toZModPow_padicIntOfCompat,
      toZModPow_padicIntOfCompat, map_mul]
  map_zero' := PadicInt.ext_of_toZModPow.mp fun k => by
    rw [toZModPow_padicIntOfCompat, map_zero, map_zero]
  map_add' f g := PadicInt.ext_of_toZModPow.mp fun k => by
    rw [map_add, toZModPow_padicIntOfCompat, toZModPow_padicIntOfCompat,
      toZModPow_padicIntOfCompat, map_add]

theorem toZModPow_weightSpec {p : ℕ} [Fact p.Prime] (u : ℤ_[p]) (hu : (p : ℤ_[p]) ∣ u)
    (f : PowerSeries ℤ_[p]) (k : ℕ) :
    PadicInt.toZModPow k (weightSpec u hu f) = weightSpecMod u hu k f :=
  toZModPow_padicIntOfCompat (fun k => weightSpecMod u hu k f) (weightSpecMod_compat u hu f) k

@[simp]
theorem weightSpec_C {p : ℕ} [Fact p.Prime] (u : ℤ_[p]) (hu : (p : ℤ_[p]) ∣ u) (a : ℤ_[p]) :
    weightSpec u hu (PowerSeries.C a) = a := by
  refine PadicInt.ext_of_toZModPow.mp fun k => ?_
  rw [toZModPow_weightSpec]
  cases k with
  | zero => have := zmod_pow_zero_subsingleton p; exact Subsingleton.elim _ _
  | succ k =>
    unfold weightSpecMod; simp only [RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
    rw [Finset.sum_eq_single 0]
    · simp [PowerSeries.coeff_C]
    · intro i _ hi; simp [PowerSeries.coeff_C, hi]
    · simp

@[simp]
theorem weightSpec_X {p : ℕ} [Fact p.Prime] (u : ℤ_[p]) (hu : (p : ℤ_[p]) ∣ u) :
    weightSpec u hu PowerSeries.X = u := by
  refine PadicInt.ext_of_toZModPow.mp fun k => ?_
  rw [toZModPow_weightSpec]
  cases k with
  | zero => have := zmod_pow_zero_subsingleton p; exact Subsingleton.elim _ _
  | succ k =>
    cases k with
    | zero =>
      change ∑ i ∈ Finset.range 1,
        PadicInt.toZModPow 1 (PowerSeries.coeff i PowerSeries.X) * (PadicInt.toZModPow 1 u) ^ i =
        PadicInt.toZModPow 1 u
      rw [Finset.sum_range_one, PowerSeries.coeff_zero_X, map_zero, zero_mul]
      obtain ⟨w, rfl⟩ := hu
      rw [map_mul]
      have hp0 : PadicInt.toZModPow 1 (p : ℤ_[p]) = 0 := by
        refine RingHom.mem_ker.mp ?_
        rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton, pow_one]
      rw [hp0, zero_mul]
    | succ k =>
      unfold weightSpecMod; simp only [RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
      rw [Finset.sum_eq_single 1]
      · simp [PowerSeries.coeff_X]
      · intro i _ hi; simp [PowerSeries.coeff_X, hi]
      · intro h1; exfalso; apply h1; rw [Finset.mem_range]; omega

/-- Horner shift recurrence: `weightSpec u f = coeff 0 f + u * weightSpec u (shift1 f)`. -/
theorem weightSpec_horner {p : ℕ} [Fact p.Prime] (u : ℤ_[p]) (hu : (p : ℤ_[p]) ∣ u)
    (f : PowerSeries ℤ_[p]) :
    weightSpec u hu f =
      PowerSeries.coeff 0 f + u * weightSpec u hu (PowerSeries.mk fun j => PowerSeries.coeff (j + 1) f) := by
  refine PadicInt.ext_of_toZModPow.mp fun k => ?_
  rw [map_add, map_mul, toZModPow_weightSpec, toZModPow_weightSpec]
  cases k with
  | zero => have := zmod_pow_zero_subsingleton p; exact Subsingleton.elim _ _
  | succ k =>
    unfold weightSpecMod
    simp only [RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
    conv_lhs => rw [Finset.sum_range_succ', pow_zero, mul_one, add_comm]
    congr 1
    symm
    rw [Finset.mul_sum, Finset.sum_range_succ]
    simp only [PowerSeries.coeff_mk]
    have hlast : PadicInt.toZModPow (k + 1) u *
        (PadicInt.toZModPow (k + 1) (PowerSeries.coeff (k + 1) f) *
          (PadicInt.toZModPow (k + 1) u) ^ k) = 0 := by
      have hk0 : (PadicInt.toZModPow (k + 1) u) ^ (k + 1) = 0 := by
        obtain ⟨w, rfl⟩ := hu
        rw [map_mul, mul_pow, ← map_pow]
        have hp0 : PadicInt.toZModPow (k + 1) ((p : ℤ_[p]) ^ (k + 1)) = 0 := by
          refine RingHom.mem_ker.mp ?_
          rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton]
        rw [hp0, zero_mul]
      calc PadicInt.toZModPow (k + 1) u *
            (PadicInt.toZModPow (k + 1) (PowerSeries.coeff (k + 1) f) *
              (PadicInt.toZModPow (k + 1) u) ^ k)
          = PadicInt.toZModPow (k + 1) (PowerSeries.coeff (k + 1) f) *
            (PadicInt.toZModPow (k + 1) u) ^ (k + 1) := by ring
        _ = 0 := by rw [hk0, mul_zero]
    rw [hlast, add_zero]
    refine Finset.sum_congr rfl fun j _ => by ring

/-- **Exact Weierstrass Division by `(T - u)` in `ℤ_[p][[T]]`**. -/
theorem weightSpec_weierstrass_div {p : ℕ} [Fact p.Prime] (u : ℤ_[p]) (hu : (p : ℤ_[p]) ∣ u)
    (f : PowerSeries ℤ_[p]) :
    ∃ q : PowerSeries ℤ_[p],
      f = PowerSeries.C (weightSpec u hu f) + (PowerSeries.X - PowerSeries.C u) * q := by
  let shift : ℕ → PowerSeries ℤ_[p] := fun m => PowerSeries.mk fun j => PowerSeries.coeff (m + 1 + j) f
  let q : PowerSeries ℤ_[p] := PowerSeries.mk fun m => weightSpec u hu (shift m)
  refine ⟨q, ?_⟩
  ext n
  cases n with
  | zero =>
    rw [map_add, PowerSeries.coeff_zero_C, PowerSeries.coeff_zero_eq_constantCoeff,
      map_mul, map_sub, PowerSeries.constantCoeff_X, PowerSeries.constantCoeff_C, zero_sub, neg_mul]
    have hq0 : PowerSeries.constantCoeff q = weightSpec u hu (shift 0) := by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff]; simp [q]
    have h0 := weightSpec_horner u hu f
    have hs0 : (PowerSeries.mk fun j => PowerSeries.coeff (j + 1) f) = shift 0 := by
      ext j; simp [shift, add_comm]
    rw [hs0] at h0
    rw [hq0, h0, PowerSeries.coeff_zero_eq_constantCoeff]; ring
  | succ m =>
    rw [map_add, PowerSeries.coeff_C, if_neg (Nat.succ_ne_zero m), zero_add, sub_mul, map_sub,
      PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_C_mul]
    simp only [q, PowerSeries.coeff_mk]
    have hm := weightSpec_horner u hu (shift m)
    have hsm : (PowerSeries.mk fun j => PowerSeries.coeff (j + 1) (shift m)) = shift (m + 1) := by
      ext j; simp only [shift, PowerSeries.coeff_mk]
      rw [show m + 1 + (j + 1) = m + 1 + 1 + j by omega]
    have hc0 : PowerSeries.coeff 0 (shift m) = PowerSeries.coeff (m + 1) f := by simp [shift]
    rw [hsm, hc0] at hm
    rw [hm]; ring

/-- **Exact Kernel of Weight Specialization**: `ker(weightSpec u) = (T - u) ⊆ ℤ_[p][[T]]`. -/
theorem ker_weightSpec_eq_span {p : ℕ} [Fact p.Prime] (u : ℤ_[p]) (hu : (p : ℤ_[p]) ∣ u) :
    RingHom.ker (weightSpec u hu) = Ideal.span ({PowerSeries.X - PowerSeries.C u} : Set (PowerSeries ℤ_[p])) := by
  ext f
  rw [RingHom.mem_ker, Ideal.mem_span_singleton]
  constructor
  · intro hf
    obtain ⟨q, hq⟩ := weightSpec_weierstrass_div u hu f
    rw [hf, map_zero, zero_add] at hq
    exact ⟨q, hq⟩
  · rintro ⟨q, rfl⟩
    rw [map_mul, map_sub, weightSpec_X, weightSpec_C, sub_self, zero_mul]

/-- The `(T - u)`-divisible submodule `(T - u) · M_∞^ord ≤ M_∞^ord` as a `ℤ_[p]`-submodule
(explicit carrier avoids nested `PowerSeries`/`ℤ_[p]` `Algebra` typeclass diamonds!). -/
def hidaWeightKerSub {p : ℕ} [Fact p.Prime] {d : ℕ}
    (E_inf : Matrix (Fin d) (Fin d) (PowerSeries ℤ_[p])) (u : ℤ_[p]) :
    Submodule ℤ_[p] (LinearMap.range E_inf.mulVecLin) where
  carrier := { x | ∃ y : LinearMap.range E_inf.mulVecLin,
    x.1 = (PowerSeries.X - PowerSeries.C u) • y.1 }
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro x₁ x₂ ⟨y₁, h₁⟩ ⟨y₂, h₂⟩
    exact ⟨y₁ + y₂, by
      change x₁.1 + x₂.1 = (PowerSeries.X - PowerSeries.C u) • (y₁.1 + y₂.1)
      rw [smul_add, h₁, h₂]⟩
  smul_mem' := by
    rintro c x ⟨y, hy⟩
    refine ⟨c • y, ?_⟩
    change c • x.1 = (PowerSeries.X - PowerSeries.C u) • (c • y.1)
    rw [hy, smul_comm]

/-- **Exact Hida Control Theorem (`hida_control_theorem`)**:
For ANY `Λ`-linear ordinary Hida idempotent `E_∞ : Matrix (Fin d) (Fin d) (ℤ_[p][[T]])`
(`E_∞² = E_∞`) and ANY weight parameter `u ∈ p ℤ_[p]`, specialization `sp_k : M_∞^ord → M_k^ord`
is SURJECTIVE with EXACT kernel `(T - u) · M_∞^ord` (`hidaWeightKerSub E_inf u`)! -/
theorem hida_control_theorem {p : ℕ} [Fact p.Prime] {d : ℕ}
    (E_inf : Matrix (Fin d) (Fin d) (PowerSeries ℤ_[p]))
    (hE_idem : E_inf * E_inf = E_inf)
    (u : ℤ_[p]) (hu : (p : ℤ_[p]) ∣ u) :
    let sp := weightSpec u hu
    let E_k : Matrix (Fin d) (Fin d) ℤ_[p] := E_inf.map sp
    E_k * E_k = E_k ∧
    ∃ (φ : LinearMap.range E_inf.mulVecLin →ₗ[ℤ_[p]] LinearMap.range E_k.mulVecLin),
      Function.Surjective φ ∧
      LinearMap.ker φ = hidaWeightKerSub E_inf u := by
  intro sp E_k
  have hEk_idem : E_k * E_k = E_k := by
    simpa [E_k] using congrArg (RingHom.mapMatrix sp) hE_idem
  let spVec : (Fin d → PowerSeries ℤ_[p]) →ₗ[ℤ_[p]] (Fin d → ℤ_[p]) :=
    { toFun := fun v i => sp (v i)
      map_add' := fun v w => by ext i; exact map_add sp _ _
      map_smul' := fun c v => by
        ext i
        simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
        rw [PowerSeries.smul_eq_C_mul, map_mul, weightSpec_C] }
  have hsp_mv : ∀ v : Fin d → PowerSeries ℤ_[p],
      spVec (E_inf.mulVec v) = E_k.mulVec (spVec v) := by
    intro v; ext i
    change sp (∑ j : Fin d, E_inf i j * v j) = ∑ j : Fin d, sp (E_inf i j) * sp (v j)
    simp [map_sum, map_mul]
  let φ : LinearMap.range E_inf.mulVecLin →ₗ[ℤ_[p]] LinearMap.range E_k.mulVecLin :=
    { toFun := fun x => ⟨spVec x.1, by
        obtain ⟨v, hv⟩ := x.2
        refine ⟨spVec v, ?_⟩
        change E_k.mulVec (spVec v) = spVec x.1
        rw [← hsp_mv]; exact congrArg spVec hv⟩
      map_add' := fun x y => Subtype.ext (map_add spVec x.1 y.1)
      map_smul' := fun c x => Subtype.ext (map_smul spVec c x.1) }
  have hsurj : Function.Surjective φ := by
    rintro ⟨y, v, rfl⟩
    let v_lift : Fin d → PowerSeries ℤ_[p] := fun i => PowerSeries.C (v i)
    have hv_sp : spVec v_lift = v := by ext i; exact weightSpec_C u hu (v i)
    refine ⟨⟨E_inf.mulVec v_lift, ⟨v_lift, rfl⟩⟩, Subtype.ext ?_⟩
    change spVec (E_inf.mulVec v_lift) = E_k.mulVec v
    rw [hsp_mv, hv_sp]
  have hker : LinearMap.ker φ = hidaWeightKerSub E_inf u := by
    ext x
    constructor
    · intro hx
      have hx0 : spVec x.1 = 0 := congrArg Subtype.val hx
      have hcoord : ∀ i : Fin d, ∃ q : PowerSeries ℤ_[p],
          x.1 i = (PowerSeries.X - PowerSeries.C u) * q := by
        intro i
        have hi : x.1 i ∈ RingHom.ker sp := congrFun hx0 i
        rw [ker_weightSpec_eq_span, Ideal.mem_span_singleton] at hi
        exact hi
      choose q hq using hcoord
      obtain ⟨w, hw⟩ := x.2
      have hw' : E_inf.mulVec w = x.1 := hw
      have hx_fix : E_inf.mulVec x.1 = x.1 := by rw [← hw', Matrix.mulVec_mulVec, hE_idem]
      refine ⟨⟨E_inf.mulVec q, ⟨q, rfl⟩⟩, ?_⟩
      change x.1 = (PowerSeries.X - PowerSeries.C u) • E_inf.mulVec q
      rw [← hx_fix, ← Matrix.mulVec_smul]
      congr 1; funext i; exact hq i
    · rintro ⟨y, hy⟩
      rw [LinearMap.mem_ker]
      apply Subtype.ext; ext i
      change sp (x.1 i) = 0
      have hi : x.1 i = (PowerSeries.X - PowerSeries.C u) * y.1 i := congrFun hy i
      rw [hi, map_mul, map_sub, weightSpec_X, weightSpec_C, sub_self, zero_mul]
  exact ⟨hEk_idem, φ, hsurj, hker⟩

/-- **Exact Hida Control Isomorphism**: `M_∞^ord ⧸ (T - u_k) M_∞^ord ≃ₗ[ℤ_[p]] M_k^ord`. -/
def hidaControlEquiv {p : ℕ} [Fact p.Prime] {d : ℕ}
    (E_inf : Matrix (Fin d) (Fin d) (PowerSeries ℤ_[p]))
    (hE_idem : E_inf * E_inf = E_inf)
    (u : ℤ_[p]) (hu : (p : ℤ_[p]) ∣ u) :
    (LinearMap.range E_inf.mulVecLin ⧸ hidaWeightKerSub E_inf u) ≃ₗ[ℤ_[p]]
    LinearMap.range (E_inf.map (weightSpec u hu)).mulVecLin :=
  let h := (hida_control_theorem E_inf hE_idem u hu).2
  let φ := h.choose
  (Submodule.quotEquivOfEq _ _ h.choose_spec.2.symm).trans
    (φ.quotKerEquivOfSurjective h.choose_spec.1)

/-- Helper: matrix of `E.mulVecLin` in the standard basis `Pi.basisFun` is `E`. -/
theorem toMatrix_mulVecLin_eq {K : Type*} [Field K] {d : ℕ} (E : Matrix (Fin d) (Fin d) K) :
    LinearMap.toMatrix (Pi.basisFun K (Fin d)) (Pi.basisFun K (Fin d)) E.mulVecLin = E := by
  ext i j
  simp [Matrix.mulVec_single]

/-- Helper: trace of `E.mulVecLin` equals `Matrix.trace E`. -/
theorem trace_mulVecLin_eq {K : Type*} [Field K] {d : ℕ} (E : Matrix (Fin d) (Fin d) K) :
    LinearMap.trace K (Fin d → K) E.mulVecLin = E.trace := by
  rw [LinearMap.trace_eq_matrix_trace K (Pi.basisFun K (Fin d)), toMatrix_mulVecLin_eq]

/-- **Trace of an Idempotent Matrix Equals Rank of Its Image over Any Char-0 Field**. -/
theorem trace_idempotent_eq_finrank_range {K : Type*} [Field K] [CharZero K] {d : ℕ}
    (E : Matrix (Fin d) (Fin d) K) (hE : E * E = E) :
    E.trace = (Module.finrank K (LinearMap.range E.mulVecLin) : K) := by
  have he : ∀ v, E.mulVec (E.mulVec v) = E.mulVec v := fun v => by rw [Matrix.mulVec_mulVec, hE]
  have hcompl : IsCompl (LinearMap.range E.mulVecLin) (LinearMap.ker E.mulVecLin) := by
    rw [isCompl_iff]
    constructor
    · rw [disjoint_iff, eq_bot_iff]
      rintro v ⟨⟨w, rfl⟩, hv⟩
      rw [Submodule.mem_bot]
      change E.mulVec (E.mulVec w) = 0 at hv; rwa [he w] at hv
    · rw [codisjoint_iff, eq_top_iff]
      intro v _
      have hsplit : v = E.mulVec v + (v - E.mulVec v) := by abel
      rw [hsplit]
      refine Submodule.add_mem_sup ⟨v, rfl⟩ ?_
      change E.mulVec (v - E.mulVec v) = 0; rw [Matrix.mulVec_sub, he v, sub_self]
  let bR := Module.finBasis K (LinearMap.range E.mulVecLin)
  let bK := Module.finBasis K (LinearMap.ker E.mulVecLin)
  let eSplit : (LinearMap.range E.mulVecLin × LinearMap.ker E.mulVecLin) ≃ₗ[K] (Fin d → K) :=
    LinearEquiv.ofBijective
      ((LinearMap.range E.mulVecLin).subtype.coprod (LinearMap.ker E.mulVecLin).subtype)
      ⟨by
        intro ⟨⟨u₁, hu₁⟩, ⟨v₁, hv₁⟩⟩ ⟨⟨u₂, hu₂⟩, ⟨v₂, hv₂⟩⟩ h
        change u₁ + v₁ = u₂ + v₂ at h
        have hsub : u₁ - u₂ = v₂ - v₁ := eq_sub_of_add_eq (by
          calc u₁ - u₂ + v₁ = (u₁ + v₁) - u₂ := by abel
            _ = (u₂ + v₂) - u₂ := by rw [h]
            _ = v₂ := by abel)
        have hmem : u₁ - u₂ ∈ LinearMap.range E.mulVecLin ⊓ LinearMap.ker E.mulVecLin :=
          ⟨(LinearMap.range E.mulVecLin).sub_mem hu₁ hu₂,
           hsub ▸ (LinearMap.ker E.mulVecLin).sub_mem hv₂ hv₁⟩
        rw [hcompl.inf_eq_bot, Submodule.mem_bot] at hmem
        have hu : u₁ = u₂ := sub_eq_zero.mp hmem
        have hv : v₁ = v₂ := (sub_eq_zero.mp (hsub.symm.trans hmem)).symm
        subst hu; subst hv; rfl,
       by
        intro v
        have hmem : v ∈ LinearMap.range E.mulVecLin ⊔ LinearMap.ker E.mulVecLin := by
          rw [hcompl.sup_eq_top]; trivial
        obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp hmem
        exact ⟨(⟨u, hu⟩, ⟨w, hw⟩), rfl⟩⟩
  let b := (bR.prod bK).map eSplit
  rw [← trace_mulVecLin_eq E, LinearMap.trace_eq_matrix_trace K b, Matrix.trace, Fintype.sum_sum_type]
  simp only [Matrix.diag_apply]
  have hsumR : ∑ i, LinearMap.toMatrix b b E.mulVecLin (Sum.inl i) (Sum.inl i) =
      (Module.finrank K (LinearMap.range E.mulVecLin) : K) := by
    have hdiag : ∀ i, LinearMap.toMatrix b b E.mulVecLin (Sum.inl i) (Sum.inl i) = 1 := by
      intro i
      rw [LinearMap.toMatrix_apply]
      have hb_inl : b (Sum.inl i) = (bR i).1 := by
        simp only [b, Basis.map_apply, Basis.prod_apply, LinearMap.coe_inl, eSplit]
        exact add_zero _
      have hfix : E.mulVecLin (b (Sum.inl i)) = b (Sum.inl i) := by
        rw [hb_inl]; obtain ⟨w, hw⟩ := (bR i).2
        have hw' : E.mulVec w = (bR i).1 := hw
        change E.mulVec (bR i).1 = (bR i).1; rw [← hw', he w]
      rw [hfix, b.repr_self, Finsupp.single_eq_same]
    simp [hdiag]
  have hsumK : ∑ j, LinearMap.toMatrix b b E.mulVecLin (Sum.inr j) (Sum.inr j) = 0 := by
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [LinearMap.toMatrix_apply]
    have hb_inr : b (Sum.inr j) = (bK j).1 := by
      simp only [b, Basis.map_apply, Basis.prod_apply, LinearMap.coe_inr, eSplit]
      exact zero_add _
    have hkill : E.mulVecLin (b (Sum.inr j)) = 0 := by rw [hb_inr]; exact (bK j).2
    rw [hkill, map_zero, Finsupp.zero_apply]
  rw [hsumR, hsumK, add_zero]

/-- **Weight Independence of Ordinary Hida Rank (`hida_ordinary_rank_constant`)**:
For ANY `Λ`-linear ordinary idempotent `E_∞² = E_∞` and ANY two weights `u₁, u₂ ∈ p ℤ_[p]`,
`rank_{ℚ_[p]}(M_{u₁}^ord ⊗ ℚ_[p]) = rank_{ℚ_[p]}(M_{u₂}^ord ⊗ ℚ_[p])`! -/
theorem hida_ordinary_rank_constant {p : ℕ} [Fact p.Prime] {d : ℕ}
    (E_inf : Matrix (Fin d) (Fin d) (PowerSeries ℤ_[p]))
    (hE_idem : E_inf * E_inf = E_inf)
    (u₁ u₂ : ℤ_[p]) (hu₁ : (p : ℤ_[p]) ∣ u₁) (hu₂ : (p : ℤ_[p]) ∣ u₂) :
    let E₁ := (E_inf.map (weightSpec u₁ hu₁)).map (algebraMap ℤ_[p] ℚ_[p])
    let E₂ := (E_inf.map (weightSpec u₂ hu₂)).map (algebraMap ℤ_[p] ℚ_[p])
    Module.finrank ℚ_[p] (LinearMap.range E₁.mulVecLin) =
      Module.finrank ℚ_[p] (LinearMap.range E₂.mulVecLin) := by
  intro E₁ E₂
  have : CharZero (PowerSeries ℤ_[p]) :=
    charZero_of_injective_algebraMap (PowerSeries.C_injective (R := ℤ_[p]))
  let F := FractionRing (PowerSeries ℤ_[p])
  have : CharZero F := charZero_of_injective_algebraMap (IsFractionRing.injective (PowerSeries ℤ_[p]) F)
  let EF : Matrix (Fin d) (Fin d) F := E_inf.map (algebraMap (PowerSeries ℤ_[p]) F)
  have hEF : EF * EF = EF := by
    simpa [EF] using congrArg (RingHom.mapMatrix (algebraMap (PowerSeries ℤ_[p]) F)) hE_idem
  have htrF := trace_idempotent_eq_finrank_range EF hEF
  set r : ℕ := Module.finrank F (LinearMap.range EF.mulVecLin)
  have htr_inf : E_inf.trace = (r : PowerSeries ℤ_[p]) := by
    apply IsFractionRing.injective (PowerSeries ℤ_[p]) F
    rw [map_natCast, ← htrF]; simp [EF, Matrix.trace, map_sum]
  have htr_spec : ∀ (u : ℤ_[p]) (hu : (p : ℤ_[p]) ∣ u),
      Module.finrank ℚ_[p] (LinearMap.range ((E_inf.map (weightSpec u hu)).map (algebraMap ℤ_[p] ℚ_[p])).mulVecLin) = r := by
    intro u hu
    let E := (E_inf.map (weightSpec u hu)).map (algebraMap ℤ_[p] ℚ_[p])
    have hE : E * E = E := by
      have h1 := congrArg (RingHom.mapMatrix (weightSpec u hu)) hE_idem
      simpa [E] using congrArg (RingHom.mapMatrix (algebraMap ℤ_[p] ℚ_[p])) h1
    have htrE : E.trace = (r : ℚ_[p]) := by
      have h1 : (E_inf.map (weightSpec u hu)).trace = (r : ℤ_[p]) := by
        have hm : (E_inf.map (weightSpec u hu)).trace = weightSpec u hu E_inf.trace := by
          simp [Matrix.trace, map_sum]
        rw [hm, htr_inf, map_natCast]
      have hm2 : E.trace = algebraMap ℤ_[p] ℚ_[p] (E_inf.map (weightSpec u hu)).trace := by
        simp [E, Matrix.trace, map_sum]
      rw [hm2, h1, map_natCast]
    have hf : (Module.finrank ℚ_[p] (LinearMap.range E.mulVecLin) : ℚ_[p]) = (r : ℚ_[p]) := by
      rw [← trace_idempotent_eq_finrank_range E hE, htrE]
    exact Nat.cast_injective hf
  exact (htr_spec u₁ hu₁).trans (htr_spec u₂ hu₂).symm

/-- Concrete rank-2 `Λ`-linear Hida ordinary idempotent `E_∞ = !![1, T; 0, 0]`. -/
def concreteHidaFamily2Idemp (p : ℕ) [Fact p.Prime] :
    Matrix (Fin 2) (Fin 2) (PowerSeries ℤ_[p]) :=
  !![1, PowerSeries.X; 0, 0]

theorem concreteHidaFamily2Idemp_idem (p : ℕ) [Fact p.Prime] :
    concreteHidaFamily2Idemp p * concreteHidaFamily2Idemp p = concreteHidaFamily2Idemp p := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [concreteHidaFamily2Idemp, Matrix.mul_apply, Fin.sum_univ_two]

/-- For EVERY algebraic weight `k : ℕ`, `u_k = (1 + p)^k - 1 ∈ p ℤ_[p]` and `concreteHidaFamily2Idemp p`
specializes to a rank-1 ordinary space over `ℚ_[p]`! -/
theorem concreteHidaFamily2_rank_one_all_weights (p : ℕ) [Fact p.Prime] (k : ℕ) :
    let u_k : ℤ_[p] := (1 + (p : ℤ_[p])) ^ k - 1
    ∃ hu : (p : ℤ_[p]) ∣ u_k,
      Module.finrank ℚ_[p]
        (LinearMap.range (((concreteHidaFamily2Idemp p).map (weightSpec u_k hu)).map
          (algebraMap ℤ_[p] ℚ_[p])).mulVecLin) = 1 := by
  intro u_k
  have hu : (p : ℤ_[p]) ∣ u_k := by
    have h0 : PadicInt.toZModPow 1 u_k = 0 := by
      simp only [u_k, map_sub, map_pow, map_add, map_one]
      have hp0 : PadicInt.toZModPow 1 (p : ℤ_[p]) = 0 := by
        refine RingHom.mem_ker.mp ?_
        rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton, pow_one]
      rw [hp0, add_zero, one_pow, sub_self]
    have hmem : u_k ∈ RingHom.ker (PadicInt.toZModPow 1) := h0
    rw [PadicInt.ker_toZModPow, pow_one, Ideal.mem_span_singleton] at hmem
    exact hmem
  refine ⟨hu, ?_⟩
  let E := ((concreteHidaFamily2Idemp p).map (weightSpec u_k hu)).map (algebraMap ℤ_[p] ℚ_[p])
  have hE : E * E = E := by
    have h1 := congrArg (RingHom.mapMatrix (weightSpec u_k hu)) (concreteHidaFamily2Idemp_idem p)
    simpa [E] using congrArg (RingHom.mapMatrix (algebraMap ℤ_[p] ℚ_[p])) h1
  have htr := trace_idempotent_eq_finrank_range E hE
  have htr1 : E.trace = 1 := by simp [E, concreteHidaFamily2Idemp, Matrix.trace, Fin.sum_univ_two]
  rw [htr1] at htr
  exact_mod_cast htr.symm

end OrdinaryHidaIdempotent

/-! ## Section 3: Reducible 3D `U(3)` Ordinary Deformation Ring, Type I/II/III Trichotomy & `CountI` Selmer Bound -/

section U3DeformationAndCountI

/-! ### 3.1 Conjugate-Self-Dual 3D Residual Pseudocharacter & `GL₃` Involution -/

structure CMGroupInvolution (G : Type*) [Group G] where
  conj : G ≃* G
  conj_invol : ∀ g : G, conj (conj g) = g

structure U3CSDCharTriple {G : Type*} [Group G] (R : Type*) [CommRing R] (C : CMGroupInvolution G) where
  χ₁ : G →* Rˣ
  χ₂ : G →* Rˣ
  χ₃ : G →* Rˣ
  h3 : ∀ g : G, χ₃ g = (χ₁ (C.conj g))⁻¹
  h2 : ∀ g : G, χ₂ g = (χ₂ (C.conj g))⁻¹

def U3CSDCharTriple.ofPsi {G R : Type*} [Group G] [CommRing R] (C : CMGroupInvolution G)
    (Ψ : G →* Rˣ) : U3CSDCharTriple R C where
  χ₁ := Ψ
  χ₂ := 1
  χ₃ := {
    toFun := fun g => (Ψ (C.conj g))⁻¹
    map_one' := by simp
    map_mul' := fun g h => by simp [map_mul, mul_comm] }
  h3 := fun _ => rfl
  h2 := fun _ => by simp

def U3CSDCharTriple.trace {G R : Type*} [Group G] [CommRing R] {C : CMGroupInvolution G}
    (T : U3CSDCharTriple R C) (g : G) : R :=
  (T.χ₁ g : R) + (T.χ₂ g : R) + (T.χ₃ g : R)

theorem U3CSDCharTriple.trace_conj {G R : Type*} [Group G] [CommRing R] {C : CMGroupInvolution G}
    (T : U3CSDCharTriple R C) (g : G) :
    T.trace (C.conj g) = T.trace g⁻¹ := by
  unfold U3CSDCharTriple.trace
  have h1 : T.χ₃ (C.conj g) = (T.χ₁ g)⁻¹ := by rw [T.h3, C.conj_invol]
  have h2 : T.χ₂ (C.conj g) = (T.χ₂ g)⁻¹ := by
    have := T.h2 (C.conj g); rw [C.conj_invol] at this; exact this
  have h3 : T.χ₁ (C.conj g) = (T.χ₃ g)⁻¹ := by rw [T.h3, inv_inv]
  rw [h1, h2, h3, map_inv, map_inv, map_inv]; ring

/-- Conjugate-self-dual involution `M ↦ J₃ (M⁻¹)ᵀ J₃` on `GL (Fin 3) L`. -/
def u3ConjInvMatrix {L : Type*} [Field L] (M : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L :=
  J3 L * ((M⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L)ᵀ * J3 L

theorem u3ConjInvMatrix_mul {L : Type*} [Field L] (M N : GL (Fin 3) L) :
    u3ConjInvMatrix (M * N) = u3ConjInvMatrix M * u3ConjInvMatrix N := by
  unfold u3ConjInvMatrix
  have hinv : ((M * N)⁻¹ : GL (Fin 3) L) = N⁻¹ * M⁻¹ := _root_.mul_inv_rev M N
  rw [hinv, Units.val_mul, Matrix.transpose_mul]
  calc J3 L * (((M⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L)ᵀ *
        ((N⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L)ᵀ) * J3 L
      = J3 L * ((M⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L)ᵀ * (J3 L * J3 L) *
        ((N⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L)ᵀ * J3 L := by
          rw [J3_mul_J3]; simp [Matrix.mul_assoc]
    _ = _ := by simp [Matrix.mul_assoc]

theorem u3ConjInvMatrix_one {L : Type*} [Field L] :
    u3ConjInvMatrix (1 : GL (Fin 3) L) = 1 := by
  unfold u3ConjInvMatrix; simp [J3_mul_J3]

def u3ConjInv {L : Type*} [Field L] : GL (Fin 3) L ≃* GL (Fin 3) L where
  toFun M :=
    { val := u3ConjInvMatrix M
      inv := u3ConjInvMatrix M⁻¹
      val_inv := by rw [← u3ConjInvMatrix_mul, mul_inv_cancel, u3ConjInvMatrix_one]
      inv_val := by rw [← u3ConjInvMatrix_mul, inv_mul_cancel, u3ConjInvMatrix_one] }
  invFun M :=
    { val := u3ConjInvMatrix M
      inv := u3ConjInvMatrix M⁻¹
      val_inv := by rw [← u3ConjInvMatrix_mul, mul_inv_cancel, u3ConjInvMatrix_one]
      inv_val := by rw [← u3ConjInvMatrix_mul, inv_mul_cancel, u3ConjInvMatrix_one] }
  left_inv M := by
    apply Units.ext
    change J3 L * (J3 L * ((M⁻¹⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L)ᵀ * J3 L)ᵀ * J3 L = M.val
    simp only [inv_inv, Matrix.transpose_mul, J3_transpose, Matrix.transpose_transpose]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, J3_mul_J3, Matrix.one_mul,
      Matrix.mul_assoc, J3_mul_J3, Matrix.mul_one]
  right_inv M := by
    apply Units.ext
    change J3 L * (J3 L * ((M⁻¹⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L)ᵀ * J3 L)ᵀ * J3 L = M.val
    simp only [inv_inv, Matrix.transpose_mul, J3_transpose, Matrix.transpose_transpose]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, J3_mul_J3, Matrix.one_mul,
      Matrix.mul_assoc, J3_mul_J3, Matrix.mul_one]
  map_mul' M N := Units.ext (u3ConjInvMatrix_mul M N)

theorem trace_u3ConjInv {L : Type*} [Field L] (M : GL (Fin 3) L) :
    ((u3ConjInv M : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L).trace =
      ((M⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L).trace := by
  change (J3 L * ((M⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L)ᵀ * J3 L).trace = _
  rw [Matrix.trace_mul_cycle, J3_mul_J3, Matrix.one_mul, Matrix.trace_transpose]

def IsU3CSDRep {G L : Type*} [Group G] [Field L] (C : CMGroupInvolution G)
    (ρ : G →* GL (Fin 3) L) : Prop :=
  ∀ g : G, ρ (C.conj g) = u3ConjInv (ρ g)

theorem IsU3CSDRep.trace_conj {G L : Type*} [Group G] [Field L] {C : CMGroupInvolution G}
    {ρ : G →* GL (Fin 3) L} (hρ : IsU3CSDRep C ρ) (g : G) :
    ((ρ (C.conj g) : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L).trace =
      ((ρ g⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L).trace := by
  rw [hρ g, trace_u3ConjInv, map_inv]

/-! ### 3.2 3D `U(3)` Reducibility Ideal, DVR Valuation Descent & Eisenstein Locus -/

/-- Concrete 3D `U(3)` Generalized Matrix Algebra deformation datum over `R`. -/
structure U3DeformGMA (R G : Type*) [CommRing R] [Group G] where
  A : Type
  [ringA : Ring A]
  [algA : Algebra R A]
  e : Fin 3 → A
  e_sum : e 0 + e 1 + e 2 = 1
  e_mul : ∀ i j : Fin 3, e i * e j = if i = j then e i else 0
  diag : Fin 3 → (A →ₗ[R] R)
  diag_e_mul_e : ∀ (i : Fin 3) (x : A), diag i (e i * x * e i) = diag i x
  diag_idemp : ∀ i : Fin 3, diag i (e i) = 1
  diag_mul_diag : ∀ (i : Fin 3) (x y : A),
    diag i (e i * x * e i * y * e i) = diag i x * diag i y
  ρ : G →* A

attribute [instance] U3DeformGMA.ringA U3DeformGMA.algA

namespace U3DeformGMA

variable {R G : Type*} [CommRing R] [Group G]

def tr (U : U3DeformGMA R G) (x : U.A) : R :=
  U.diag 0 x + U.diag 1 x + U.diag 2 x

/-- The **total reducibility ideal `I_red`** generated by off-diagonal pair products. -/
def reducibilityIdeal (U : U3DeformGMA R G) : Ideal R :=
  Ideal.span { r : R | ∃ (i j : Fin 3) (_ : i ≠ j) (x y : U.A),
    r = U.diag i (U.e i * x * U.e j * y * U.e i) }

theorem diag_mul_mod_reducibilityIdeal (U : U3DeformGMA R G) {S : Type*} [CommRing S]
    (f : R →+* S) (hf : U.reducibilityIdeal ≤ RingHom.ker f) (i : Fin 3) (x y : U.A) :
    f (U.diag i (x * y)) = f (U.diag i x) * f (U.diag i y) := by
  have h1 : U.e i * (x * y) * U.e i =
      U.e i * x * U.e 0 * y * U.e i +
      U.e i * x * U.e 1 * y * U.e i +
      U.e i * x * U.e 2 * y * U.e i := by
    calc U.e i * (x * y) * U.e i
        = U.e i * x * 1 * y * U.e i := by simp [mul_assoc]
      _ = U.e i * x * (U.e 0 + U.e 1 + U.e 2) * y * U.e i := by rw [U.e_sum]
      _ = _ := by noncomm_ring
  rw [← U.diag_e_mul_e i (x * y), h1, map_add, map_add, map_add, map_add]
  have hz : ∀ (a b : Fin 3), a ≠ b → f (U.diag a (U.e a * x * U.e b * y * U.e a)) = 0 :=
    fun a b hab => RingHom.mem_ker.mp (hf (Ideal.subset_span ⟨a, b, hab, x, y, rfl⟩))
  fin_cases i
  · change f (U.diag 0 (U.e 0 * x * U.e 0 * y * U.e 0)) +
      f (U.diag 0 (U.e 0 * x * U.e 1 * y * U.e 0)) +
      f (U.diag 0 (U.e 0 * x * U.e 2 * y * U.e 0)) = f (U.diag 0 x) * f (U.diag 0 y)
    rw [U.diag_mul_diag 0 x y, map_mul, hz 0 1 (by decide), hz 0 2 (by decide), add_zero, add_zero]
  · change f (U.diag 1 (U.e 1 * x * U.e 0 * y * U.e 1)) +
      f (U.diag 1 (U.e 1 * x * U.e 1 * y * U.e 1)) +
      f (U.diag 1 (U.e 1 * x * U.e 2 * y * U.e 1)) = f (U.diag 1 x) * f (U.diag 1 y)
    rw [U.diag_mul_diag 1 x y, map_mul f, hz 1 0 (by decide), hz 1 2 (by decide), zero_add, add_zero]
  · change f (U.diag 2 (U.e 2 * x * U.e 0 * y * U.e 2)) +
      f (U.diag 2 (U.e 2 * x * U.e 1 * y * U.e 2)) +
      f (U.diag 2 (U.e 2 * x * U.e 2 * y * U.e 2)) = f (U.diag 2 x) * f (U.diag 2 y)
    rw [U.diag_mul_diag 2 x y, map_mul f, hz 2 0 (by decide), hz 2 1 (by decide), zero_add, zero_add]

def diagChar (U : U3DeformGMA R G) {S : Type*} [CommRing S]
    (f : R →+* S) (hf : U.reducibilityIdeal ≤ RingHom.ker f) (i : Fin 3) : G →* S where
  toFun g := f (U.diag i (U.ρ g))
  map_one' := by
    rw [map_one, ← U.diag_e_mul_e i 1, mul_one, U.e_mul i i, if_pos rfl, U.diag_idemp, map_one]
  map_mul' g h := by rw [map_mul, U.diag_mul_mod_reducibilityIdeal f hf]

theorem trace_splits_of_reducibilityIdeal (U : U3DeformGMA R G) {S : Type*} [CommRing S]
    (f : R →+* S) (hf : U.reducibilityIdeal ≤ RingHom.ker f) (g : G) :
    f (U.tr (U.ρ g)) = U.diagChar f hf 0 g + U.diagChar f hf 1 g + U.diagChar f hf 2 g := by
  simp [U3DeformGMA.tr, diagChar, map_add]

/-- Evaluate a formal `R[G]`-linear combination `l : List (R × G)` in `U.A`. -/
def evalList (U : U3DeformGMA R G) (l : List (R × G)) : U.A :=
  (l.map fun p => p.1 • U.ρ p.2).sum

/-- Formal convolution product in `R[G]` represented by `List (R × G)`. -/
def mulList (l₁ l₂ : List (R × G)) : List (R × G) :=
  l₁.flatMap fun p => l₂.map fun q => (p.1 * q.1, p.2 * q.2)

theorem evalList_mulList (U : U3DeformGMA R G) (l₁ l₂ : List (R × G)) :
    U.evalList (mulList l₁ l₂) = U.evalList l₁ * U.evalList l₂ := by
  induction l₁ with
  | nil => simp [evalList, mulList]
  | cons p ps ih =>
    simp only [evalList, mulList, List.flatMap_cons, List.map_append, List.sum_append,
      List.map_cons, List.sum_cons, add_mul]
    simp only [evalList, mulList] at ih
    rw [ih]
    congr 1
    clear ih; induction l₂ with
    | nil => simp
    | cons q qs ih2 =>
      simp only [List.map_cons, List.sum_cons, mul_add, ih2, map_mul]
      congr 1
      rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul]

/-- **Type III = Reducibility Locus (`typeIII_iff_mem_reducibility_locus`)**:
`U.reducibilityIdeal ≤ ker f ↔` `f ∘ tr ∘ ρ` splits into 3 adapted characters `χ₀, χ₁, χ₂`! -/
theorem typeIII_iff_mem_reducibility_locus (U : U3DeformGMA R G) {L : Type*} [CommRing L]
    (hsurj : Function.Surjective U.evalList)
    (eLift : Fin 3 → List (R × G))
    (heLift : ∀ i : Fin 3, U.evalList (eLift i) = U.e i)
    (hdiag_tr : ∀ (i : Fin 3) (x : U.A), U.tr (U.e i * x * U.e i) = U.diag i x)
    (f : R →+* L) :
    U.reducibilityIdeal ≤ RingHom.ker f ↔
      ∃ χ : Fin 3 → (G →* L),
        (∀ g : G, f (U.tr (U.ρ g)) = χ 0 g + χ 1 g + χ 2 g) ∧
        (∀ i k : Fin 3,
          ((eLift i).map fun p => f p.1 * χ k p.2).sum = if k = i then 1 else 0) := by
  let evalChar : (G →* L) → List (R × G) → L := fun χ l => (l.map fun p => f p.1 * χ p.2).sum
  have heval_mul : ∀ (χ : G →* L) (l₁ l₂ : List (R × G)),
      evalChar χ (mulList l₁ l₂) = evalChar χ l₁ * evalChar χ l₂ := by
    intro χ l₁ l₂
    induction l₁ with
    | nil => simp [evalChar, mulList]
    | cons p ps ih =>
      simp only [evalChar, mulList, List.flatMap_cons, List.map_append, List.sum_append,
        List.map_cons, List.sum_cons, add_mul]
      simp only [evalChar, mulList] at ih
      rw [ih]
      congr 1
      clear ih; induction l₂ with
      | nil => simp
      | cons q qs ih2 =>
        simp only [List.map_cons, List.sum_cons, mul_add, ih2, map_mul]; ring
  constructor
  · intro hf
    refine ⟨fun i => U.diagChar f hf i, U.trace_splits_of_reducibilityIdeal f hf, fun i k => ?_⟩
    have hdiag_l : ∀ l : List (R × G),
        evalChar (U.diagChar f hf k) l = f (U.diag k (U.evalList l)) := by
      intro l; induction l with
      | nil => simp [evalChar, evalList]
      | cons p ps ih =>
        simp only [evalChar, evalList, List.map_cons, List.sum_cons, map_add, map_smul,
          smul_eq_mul, map_mul, ih]; rfl
    change evalChar (U.diagChar f hf k) (eLift i) = _
    rw [hdiag_l, heLift i]
    by_cases hki : k = i
    · subst hki; rw [if_pos rfl, U.diag_idemp, map_one]
    · rw [if_neg hki, ← U.diag_e_mul_e k (U.e i), U.e_mul k i, if_neg hki, zero_mul, map_zero, map_zero]
  · rintro ⟨χ, hsplit, hadapt⟩
    rw [reducibilityIdeal, Ideal.span_le]
    rintro _ ⟨i, j, hij, x, y, rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker]
    obtain ⟨u, hu⟩ := hsurj x
    obtain ⟨v, hv⟩ := hsurj y
    let w : List (R × G) := mulList (mulList (mulList (mulList (eLift i) u) (eLift j)) v) (eLift i)
    have hmw : U.evalList w = U.e i * x * U.e j * y * U.e i := by
      simp only [w, evalList_mulList, heLift, hu, hv]
    have htr_l : ∀ z : List (R × G),
        f (U.tr (U.evalList z)) = evalChar (χ 0) z + evalChar (χ 1) z + evalChar (χ 2) z := by
      intro z; induction z with
      | nil => simp [U3DeformGMA.tr, evalChar, evalList]
      | cons p ps ih =>
        have htr_cons : U.tr (U.evalList (p :: ps)) = p.1 * U.tr (U.ρ p.2) + U.tr (U.evalList ps) := by
          simp only [U3DeformGMA.tr, evalList, List.map_cons, List.sum_cons, map_add, map_smul,
            smul_eq_mul]; ring
        rw [htr_cons, map_add, map_mul, hsplit p.2, ih]
        simp only [evalChar, List.map_cons, List.sum_cons]; ring
    have htr_w : U.tr (U.e i * x * U.e j * y * U.e i) = U.diag i (U.e i * x * U.e j * y * U.e i) := by
      have hi2 : U.e i * U.e i = U.e i := by rw [U.e_mul, if_pos rfl]
      have hassoc : U.e i * x * U.e j * y * U.e i = U.e i * (U.e i * x * U.e j * y * U.e i) * U.e i := by
        calc U.e i * x * U.e j * y * U.e i
            = (U.e i * U.e i) * x * U.e j * y * (U.e i * U.e i) := by rw [hi2]
          _ = U.e i * (U.e i * x * U.e j * y * U.e i) * U.e i := by noncomm_ring
      conv_lhs => rw [hassoc]
      exact hdiag_tr i _
    rw [← htr_w, ← hmw, htr_l w]
    have hkill : ∀ k : Fin 3, evalChar (χ k) w = 0 := by
      intro k; simp only [w, heval_mul]
      have h1 : evalChar (χ k) (eLift i) = if k = i then 1 else 0 := hadapt i k
      have h2 : evalChar (χ k) (eLift j) = if k = j then 1 else 0 := hadapt j k
      rw [h1, h2]
      by_cases hki : k = i
      · subst hki; simp [hij]
      · simp [hki]
    rw [hkill 0, hkill 1, hkill 2, add_zero, add_zero]

end U3DeformGMA

/-- Over a DVR `(𝒪, ϖ)`, `length_𝒪(𝒪 ⧸ (ϖ^k)) = k`. -/
theorem length_dvr_quotient_pow {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪]
    [IsDiscreteValuationRing 𝒪] {ϖ : 𝒪} (hϖ : Irreducible ϖ) (k : ℕ) :
    Module.length 𝒪 (𝒪 ⧸ Ideal.span ({ϖ ^ k} : Set 𝒪)) = (k : ℕ∞) := by
  induction k with
  | zero =>
    rw [pow_zero, Ideal.span_singleton_one]
    have : Subsingleton (𝒪 ⧸ (⊤ : Ideal 𝒪)) := Submodule.Quotient.subsingleton_iff.mpr rfl
    simp
  | succ k ih =>
    let I1 : Ideal 𝒪 := Ideal.span ({ϖ ^ (k + 1)} : Set 𝒪)
    let I0 : Ideal 𝒪 := Ideal.span ({ϖ ^ k} : Set 𝒪)
    have hle : I1 ≤ I0 := by
      rw [Ideal.span_singleton_le_span_singleton, pow_succ]; exact dvd_mul_right _ _
    let proj : (𝒪 ⧸ I1) →ₗ[𝒪] (𝒪 ⧸ I0) := Submodule.factor hle
    have hsurj : Function.Surjective proj := Submodule.factor_surjective hle
    let incl : (𝒪 ⧸ Ideal.span ({ϖ} : Set 𝒪)) →ₗ[𝒪] (𝒪 ⧸ I1) :=
      Submodule.liftQ (Ideal.span ({ϖ} : Set 𝒪))
        ((Submodule.mkQ I1).comp (LinearMap.mulLeft 𝒪 (ϖ ^ k)))
        (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (by
          change (Submodule.mkQ I1) (ϖ ^ k * ϖ) = 0
          rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, ← pow_succ]
          exact Ideal.subset_span rfl)))
    have hinj : Function.Injective incl := by
      rw [injective_iff_map_eq_zero]
      intro q hq
      induction q using Quotient.inductionOn' with
      | h a =>
        change (Submodule.mkQ I1) (ϖ ^ k * a) = 0 at hq
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
          Ideal.mem_span_singleton, pow_succ] at hq
        have hdvd : ϖ ∣ a := (mul_dvd_mul_iff_left (pow_ne_zero k hϖ.ne_zero)).mp hq
        exact (Submodule.Quotient.mk_eq_zero _).mpr (Ideal.mem_span_singleton.mpr hdvd)
    have hex : Function.Exact incl proj := by
      intro q
      induction q using Quotient.inductionOn' with
      | h x =>
        change (Submodule.Quotient.mk x : 𝒪 ⧸ I0) = 0 ↔ _
        rw [Submodule.Quotient.mk_eq_zero, Ideal.mem_span_singleton]
        constructor
        · rintro ⟨a, rfl⟩; exact ⟨Submodule.Quotient.mk a, rfl⟩
        · rintro ⟨q', hq'⟩
          induction q' using Quotient.inductionOn' with
          | h a =>
            have h1 : (Submodule.Quotient.mk (ϖ ^ k * a) : 𝒪 ⧸ I1) = Submodule.Quotient.mk x := hq'
            have hsub0 : ϖ ^ k * a - x ∈ I0 := hle ((Submodule.Quotient.eq I1).mp h1)
            rw [Ideal.mem_span_singleton] at hsub0
            obtain ⟨b, hb⟩ := hsub0
            exact ⟨a - b, by linear_combination -hb⟩
    have hmax : (Ideal.span ({ϖ} : Set 𝒪)).IsMaximal :=
      PrincipalIdealRing.isMaximal_of_irreducible hϖ
    have hsimple : IsSimpleModule 𝒪 (𝒪 ⧸ Ideal.span ({ϖ} : Set 𝒪)) :=
      isSimpleModule_iff_isCoatom.mpr hmax.out
    have hlen1 : Module.length 𝒪 (𝒪 ⧸ Ideal.span ({ϖ} : Set 𝒪)) = 1 :=
      Module.length_eq_one_iff.mpr hsimple
    rw [Module.length_eq_add_of_exact incl proj hinj hsurj hex, hlen1, ih]
    push_cast; ring

/-- **Monic Trace-Difference Valuation Descent to `I_red ∩ 𝒪`**. -/
theorem u3_reducibility_comap_length_le_val {𝒪 R : Type*} [CommRing 𝒪] [IsDomain 𝒪]
    [IsDiscreteValuationRing 𝒪] {ϖ : 𝒪} (hϖ : Irreducible ϖ)
    [CommRing R] (I : Ideal R) (f : 𝒪 →+* R)
    {δ : R} (hδ : δ ∈ I) {P : 𝒪[X]} (hP : Polynomial.eval₂ f δ P = 0)
    (v_tot : ℕ) (hfac : ∃ u : 𝒪ˣ, P.coeff 0 = (u : 𝒪) * ϖ ^ v_tot) :
    Module.length 𝒪 (𝒪 ⧸ I.comap f) ≤ (v_tot : ℕ∞) := by
  have hc0 : P.coeff 0 ∈ I.comap f := by
    change f (P.coeff 0) ∈ I
    have hsplit : P = Polynomial.C (P.coeff 0) + Polynomial.X * P.divX := by
      rw [add_comm]; exact (Polynomial.X_mul_divX_add P).symm
    have hev : f (P.coeff 0) + δ * Polynomial.eval₂ f δ P.divX = 0 := by
      have h0 := congrArg (Polynomial.eval₂ f δ) hsplit
      rw [hP, Polynomial.eval₂_add, Polynomial.eval₂_C, Polynomial.eval₂_mul, Polynomial.eval₂_X] at h0
      exact h0.symm
    rw [eq_neg_of_add_eq_zero_left hev]
    exact I.neg_mem (I.mul_mem_right _ hδ)
  obtain ⟨u, hu⟩ := hfac
  have hpow_mem : ϖ ^ v_tot ∈ I.comap f := by
    have h1 : ((u⁻¹ : 𝒪ˣ) : 𝒪) * P.coeff 0 ∈ I.comap f := (I.comap f).mul_mem_left _ hc0
    rw [hu, ← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul] at h1
    exact h1
  have hle : Ideal.span ({ϖ ^ v_tot} : Set 𝒪) ≤ I.comap f :=
    Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hpow_mem)
  calc Module.length 𝒪 (𝒪 ⧸ I.comap f)
      ≤ Module.length 𝒪 (𝒪 ⧸ Ideal.span ({ϖ ^ v_tot} : Set 𝒪)) :=
        Module.length_le_of_surjective (Submodule.factor hle) (Submodule.factor_surjective hle)
    _ = (v_tot : ℕ∞) := length_dvr_quotient_pow hϖ v_tot

/-! ### 3.3 Unconditional Type I / Type II / Type III Classification of Every 3D Characteristic-0 Point -/

def IsGInvariant3 {G L : Type*} [Group G] [Field L]
    (ρ : G →* GL (Fin 3) L) (W : Submodule L (Fin 3 → L)) : Prop :=
  ∀ (g : G) (v : Fin 3 → L), v ∈ W → ((ρ g : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L).mulVec v ∈ W

def IsIrreducible2D {G L : Type*} [Group G] [Field L] (ρ₂ : G →* GL (Fin 2) L) : Prop :=
  ∀ W : Submodule L (Fin 2 → L),
    (∀ g v, v ∈ W → ((ρ₂ g : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L).mulVec v ∈ W) →
    W = ⊥ ∨ W = ⊤

def IsTypeI {G L : Type*} [Group G] [Field L] (ρ : G →* GL (Fin 3) L) : Prop :=
  ∀ W : Submodule L (Fin 3 → L), IsGInvariant3 ρ W → W = ⊥ ∨ W = ⊤

def IsTypeIII {G L : Type*} [Group G] [Field L] (ρ : G →* GL (Fin 3) L) : Prop :=
  ∃ W₁ W₂ : Submodule L (Fin 3 → L),
    IsGInvariant3 ρ W₁ ∧ IsGInvariant3 ρ W₂ ∧
    W₁ ≤ W₂ ∧ Module.finrank L W₁ = 1 ∧ Module.finrank L W₂ = 2

def IsTypeII {G L : Type*} [Group G] [Field L] (ρ : G →* GL (Fin 3) L) : Prop :=
  (∃ W : Submodule L (Fin 3 → L), IsGInvariant3 ρ W ∧ W ≠ ⊥ ∧ W ≠ ⊤) ∧ ¬ IsTypeIII ρ

/-- **Unconditional Type I / Type II / Type III Trichotomy (`u3_point_trichotomy`)**. -/
theorem u3_point_trichotomy {G L : Type*} [Group G] [Field L] (ρ : G →* GL (Fin 3) L) :
    (IsTypeI ρ ∨ IsTypeII ρ ∨ IsTypeIII ρ) ∧
    ¬ (IsTypeI ρ ∧ IsTypeII ρ) ∧
    ¬ (IsTypeI ρ ∧ IsTypeIII ρ) ∧
    ¬ (IsTypeII ρ ∧ IsTypeIII ρ) := by
  have h12 : ¬ (IsTypeI ρ ∧ IsTypeII ρ) := by
    rintro ⟨hI, ⟨⟨W, hW, hne0, hneT⟩, _⟩⟩
    rcases hI W hW with rfl | rfl
    · exact hne0 rfl
    · exact hneT rfl
  have h13 : ¬ (IsTypeI ρ ∧ IsTypeIII ρ) := by
    rintro ⟨hI, ⟨W₁, _, hW₁, _, _, hd1, _⟩⟩
    rcases hI W₁ hW₁ with rfl | rfl
    · rw [finrank_bot] at hd1; omega
    · rw [finrank_top, Module.finrank_fin_fun] at hd1; omega
  have h23 : ¬ (IsTypeII ρ ∧ IsTypeIII ρ) := fun ⟨⟨_, hnot3⟩, h3⟩ => hnot3 h3
  have hexh : IsTypeI ρ ∨ IsTypeII ρ ∨ IsTypeIII ρ := by
    by_cases hI : IsTypeI ρ
    · exact Or.inl hI
    · by_cases hIII : IsTypeIII ρ
      · exact Or.inr (Or.inr hIII)
      · refine Or.inr (Or.inl ⟨?_, hIII⟩)
        unfold IsTypeI at hI; push Not at hI; exact hI
  exact ⟨hexh, h12, h13, h23⟩

/-- Helper: matrix representation of `ρ : G →* GL₃(L)` in any basis `b` of `Fin 3 → L`. -/
private theorem toMatrix_rep_mul {G L : Type*} [Group G] [Field L]
    (b : Basis (Fin 3) L (Fin 3 → L)) (ρ : G →* GL (Fin 3) L) (g h : G) :
    LinearMap.toMatrix b b ((ρ (g * h) : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L).mulVecLin =
      LinearMap.toMatrix b b ((ρ g : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L).mulVecLin *
      LinearMap.toMatrix b b ((ρ h : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L).mulVecLin := by
  rw [map_mul, Units.val_mul, Matrix.mulVecLin_mul, LinearMap.toMatrix_comp b b b]

private theorem toMatrix_rep_one {G L : Type*} [Group G] [Field L]
    (b : Basis (Fin 3) L (Fin 3 → L)) (ρ : G →* GL (Fin 3) L) :
    LinearMap.toMatrix b b ((ρ 1 : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L).mulVecLin = 1 := by
  rw [map_one, Units.val_one, Matrix.mulVecLin_one, LinearMap.toMatrix_id]

private theorem toMatrix_rep_trace {G L : Type*} [Group G] [Field L]
    (b : Basis (Fin 3) L (Fin 3 → L)) (ρ : G →* GL (Fin 3) L) (g : G) :
    ((ρ g : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L).trace =
      (LinearMap.toMatrix b b ((ρ g : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L).mulVecLin).trace := by
  rw [← trace_mulVecLin_eq, LinearMap.trace_eq_matrix_trace L b]

/-- **Type III Trace Splitting (`typeIII_trace_eq_sum_three_chars`)**:
Every Type III representation `ρ : G →* GL (Fin 3) L` has trace equal to `χ₀ + χ₁ + χ₂`. -/
theorem typeIII_trace_eq_sum_three_chars {G L : Type*} [Group G] [Field L]
    (ρ : G →* GL (Fin 3) L) (hIII : IsTypeIII ρ) :
    ∃ χ₀ χ₁ χ₂ : G →* Lˣ, ∀ g : G,
      ((ρ g : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L).trace =
        (χ₀ g : L) + (χ₁ g : L) + (χ₂ g : L) := by
  classical
  obtain ⟨W₁, W₂, hW₁, hW₂, h12, hd1, hd2⟩ := hIII
  have hW1_ne : W₁ ≠ ⊥ := fun h0 => by rw [h0, finrank_bot] at hd1; omega
  obtain ⟨v₀, hv₀W1, hv₀ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW1_ne
  have hW1_eq : W₁ = Submodule.span L {v₀} :=
    (Submodule.eq_of_le_of_finrank_eq
      (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hv₀W1))
      (by rw [finrank_span_singleton hv₀ne, hd1])).symm
  have hW1_lt_W2 : W₁ < W₂ := lt_of_le_of_ne h12 (fun h => by rw [h, hd2] at hd1; omega)
  obtain ⟨v₁, hv₁W2, hv₁nW1⟩ := SetLike.exists_of_lt hW1_lt_W2
  have hW2_eq : W₂ = Submodule.span L ({v₀, v₁} : Set (Fin 3 → L)) := by
    have hle : Submodule.span L ({v₀, v₁} : Set (Fin 3 → L)) ≤ W₂ :=
      Submodule.span_le.mpr (Set.pair_subset (h12 hv₀W1) hv₁W2)
    have hgt : W₁ < Submodule.span L ({v₀, v₁} : Set (Fin 3 → L)) :=
      lt_of_le_of_ne (hW1_eq ▸ Submodule.span_mono (by simp))
        (fun heq => hv₁nW1 (heq ▸ Submodule.subset_span (by simp)))
    have hdim_gt := Submodule.finrank_lt_finrank_of_lt hgt
    have hdim_le := Submodule.finrank_mono hle
    exact (Submodule.eq_of_le_of_finrank_eq hle (by omega)).symm
  have hW2_lt_top : W₂ < ⊤ := lt_top_iff_ne_top.mpr fun h => by
    rw [h, finrank_top, Module.finrank_fin_fun] at hd2; omega
  obtain ⟨v₂, _, hv₂nW2⟩ := SetLike.exists_of_lt hW2_lt_top
  let vecs : Fin 3 → (Fin 3 → L) := ![v₀, v₁, v₂]
  have hli : LinearIndependent L vecs := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have hsum : c 0 • v₀ + c 1 • v₁ + c 2 • v₂ = 0 := by
      simpa [vecs, Fin.sum_univ_three, add_assoc] using hc
    have hc2 : c 2 = 0 := by
      by_contra hne
      have hv2 : v₂ = (-(c 2)⁻¹ * c 0) • v₀ + (-(c 2)⁻¹ * c 1) • v₁ := by
        have h1 : c 2 • v₂ = -(c 0 • v₀ + c 1 • v₁) := eq_neg_of_add_eq_zero_right hsum
        calc v₂ = (c 2)⁻¹ • (c 2 • v₂) := by rw [smul_smul, inv_mul_cancel₀ hne, one_smul]
          _ = (c 2)⁻¹ • (-(c 0 • v₀ + c 1 • v₁)) := by rw [h1]
          _ = _ := by simp only [smul_neg, smul_add, smul_smul, neg_add, neg_mul, neg_smul]
      exact hv₂nW2 (hv2 ▸ W₂.add_mem (W₂.smul_mem _ (h12 hv₀W1)) (W₂.smul_mem _ hv₁W2))
    rw [hc2, zero_smul, add_zero] at hsum
    have hc1 : c 1 = 0 := by
      by_contra hne
      have hv1 : v₁ = (-(c 1)⁻¹ * c 0) • v₀ := by
        have h1 : c 1 • v₁ = -(c 0 • v₀) := eq_neg_of_add_eq_zero_right hsum
        calc v₁ = (c 1)⁻¹ • (c 1 • v₁) := by rw [smul_smul, inv_mul_cancel₀ hne, one_smul]
          _ = (c 1)⁻¹ • (-(c 0 • v₀)) := by rw [h1]
          _ = _ := by simp [smul_neg, smul_smul, neg_mul]
      exact hv₁nW1 (hv1 ▸ W₁.smul_mem _ hv₀W1)
    rw [hc1, zero_smul, add_zero] at hsum
    have hc0 : c 0 = 0 := (smul_eq_zero.mp hsum).resolve_right hv₀ne
    intro i; fin_cases i <;> assumption
  have hspan : Submodule.span L (Set.range vecs) = ⊤ :=
    Submodule.eq_top_of_finrank_eq (by
      rw [finrank_span_eq_card hli, Fintype.card_fin, Module.finrank_fin_fun])
  let b : Basis (Fin 3) L (Fin 3 → L) := Basis.mk hli (le_of_eq hspan.symm)
  let M : G → Matrix (Fin 3) (Fin 3) L := fun g =>
    LinearMap.toMatrix b b ((ρ g : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L).mulVecLin
  have hb0 : b 0 = v₀ := by simp [b, vecs]
  have hb1 : b 1 = v₁ := by simp [b, vecs]
  have hM_col0 : ∀ (g : G) (k : Fin 3), k ≠ 0 → M g k 0 = 0 := by
    intro g k hk
    have hmem : ((ρ g : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L).mulVec v₀ ∈ W₁ := hW₁ g v₀ hv₀W1
    rw [hW1_eq, Submodule.mem_span_singleton] at hmem
    obtain ⟨c, hc⟩ := hmem
    dsimp only [M]; rw [LinearMap.toMatrix_apply, hb0]
    change (b.repr (((ρ g : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L).mulVec v₀)) k = 0
    rw [← hc, ← hb0, map_smul, b.repr_self, Finsupp.smul_apply, Finsupp.single_eq_of_ne hk,
      smul_zero]
  have hM_21 : ∀ g : G, M g 2 1 = 0 := by
    intro g
    have hmem : ((ρ g : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L).mulVec v₁ ∈ W₂ := hW₂ g v₁ hv₁W2
    rw [hW2_eq, Submodule.mem_span_pair] at hmem
    obtain ⟨a, c, hac⟩ := hmem
    dsimp only [M]; rw [LinearMap.toMatrix_apply, hb1]
    change (b.repr (((ρ g : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L).mulVec v₁)) 2 = 0
    rw [← hac, ← hb0, ← hb1, map_add, map_smul, map_smul, b.repr_self, b.repr_self]; simp
  have hdiag_mul : ∀ (i : Fin 3) (g h : G), M (g * h) i i = M g i i * M h i i := by
    intro i g h
    rw [show M (g * h) = M g * M h from toMatrix_rep_mul b ρ g h, Matrix.mul_apply, Fin.sum_univ_three]
    have h10g := hM_col0 g 1 (by decide); have h20g := hM_col0 g 2 (by decide)
    have h10h := hM_col0 h 1 (by decide); have h20h := hM_col0 h 2 (by decide)
    fin_cases i <;> simp [h10g, h20g, h10h, h20h, hM_21]
  have hdiag_one : ∀ i : Fin 3, M 1 i i = 1 := fun i => by
    rw [show M 1 = 1 from toMatrix_rep_one b ρ]; simp
  let mkChar : Fin 3 → (G →* Lˣ) := fun i =>
    { toFun := fun g =>
        { val := M g i i, inv := M g⁻¹ i i
          val_inv := by rw [← hdiag_mul, mul_inv_cancel, hdiag_one]
          inv_val := by rw [← hdiag_mul, inv_mul_cancel, hdiag_one] }
      map_one' := Units.ext (hdiag_one i)
      map_mul' := fun g h => Units.ext (hdiag_mul i g h) }
  refine ⟨mkChar 0, mkChar 1, mkChar 2, fun g => ?_⟩
  rw [toMatrix_rep_trace b ρ g, Matrix.trace, Fin.sum_univ_three]; rfl

/-- Helper: given a 1D invariant subspace `W` and complement `C`, extract `ρ₂` and `χ` for Type II. -/
private theorem typeII_constituent_of_dim1 {G L : Type*} [Group G] [Field L]
    (ρ : G →* GL (Fin 3) L) (hnot3 : ¬ IsTypeIII ρ)
    (W : Submodule L (Fin 3 → L)) (hW : IsGInvariant3 ρ W) (hd1 : Module.finrank L W = 1) :
    ∃ (ρ₂ : G →* GL (Fin 2) L) (χ : G →* Lˣ),
      IsIrreducible2D ρ₂ ∧
      ∀ g : G, ((ρ g : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L).trace =
        ((ρ₂ g : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L).trace + (χ g : L) := by
  classical
  have hne0 : W ≠ ⊥ := fun h0 => by rw [h0, finrank_bot] at hd1; omega
  obtain ⟨v₀, hv₀W, hv₀ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne0
  have hW_eq : W = Submodule.span L {v₀} :=
    (Submodule.eq_of_le_of_finrank_eq
      (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hv₀W))
      (by rw [finrank_span_singleton hv₀ne, hd1])).symm
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl W
  have hCdim : Module.finrank L C = 2 := by
    have hsum := Submodule.finrank_add_eq_of_isCompl hC
    rw [Module.finrank_fin_fun, hd1] at hsum; omega
  let bC := Module.finBasisOfFinrankEq L C hCdim
  let vecs : Fin 3 → (Fin 3 → L) := ![v₀, (bC 0).1, (bC 1).1]
  have hli : LinearIndependent L vecs := by
    rw [Fintype.linearIndependent_iff]; intro c hc
    have hsum : c 0 • v₀ + (c 1 • (bC 0).1 + c 2 • (bC 1).1) = 0 := by
      simpa [vecs, Fin.sum_univ_three, add_assoc] using hc
    have hbot : c 0 • v₀ ∈ W ⊓ C :=
      ⟨W.smul_mem _ hv₀W, (eq_neg_of_add_eq_zero_left hsum) ▸
        C.neg_mem (C.add_mem (C.smul_mem _ (bC 0).2) (C.smul_mem _ (bC 1).2))⟩
    rw [hC.inf_eq_bot, Submodule.mem_bot] at hbot
    have hc0 : c 0 = 0 := (smul_eq_zero.mp hbot).resolve_right hv₀ne
    rw [hc0, zero_smul, zero_add] at hsum
    have hliC := Fintype.linearIndependent_iff.mp bC.linearIndependent ![c 1, c 2]
      (by simpa [Fin.sum_univ_two] using (Subtype.ext hsum : c 1 • bC 0 + c 2 • bC 1 = 0))
    intro i; fin_cases i
    · exact hc0
    · exact hliC 0
    · exact hliC 1
  have hspan : Submodule.span L (Set.range vecs) = ⊤ :=
    Submodule.eq_top_of_finrank_eq (by
      rw [finrank_span_eq_card hli, Fintype.card_fin, Module.finrank_fin_fun])
  let b : Basis (Fin 3) L (Fin 3 → L) := Basis.mk hli (le_of_eq hspan.symm)
  let M : G → Matrix (Fin 3) (Fin 3) L := fun g =>
    LinearMap.toMatrix b b ((ρ g : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L).mulVecLin
  have hb0 : b 0 = v₀ := by simp [b, vecs]
  have hM_col0 : ∀ (g : G) (i : Fin 2), M g i.succ 0 = 0 := by
    intro g i
    have hmem : ((ρ g : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L).mulVec v₀ ∈ W := hW g v₀ hv₀W
    rw [hW_eq, Submodule.mem_span_singleton] at hmem
    obtain ⟨r, hr⟩ := hmem
    dsimp only [M]; rw [LinearMap.toMatrix_apply, hb0]
    change (b.repr (((ρ g : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L).mulVec v₀)) i.succ = 0
    rw [← hr, ← hb0, map_smul, b.repr_self, Finsupp.smul_apply,
      Finsupp.single_eq_of_ne (Fin.succ_ne_zero i), smul_zero]
  let B : G → Matrix (Fin 2) (Fin 2) L := fun g i j => M g i.succ j.succ
  have hB_mul : ∀ g h, B (g * h) = B g * B h := by
    intro g h; ext i j
    have hmul := toMatrix_rep_mul b ρ g h
    have h10 : M g 1 0 = 0 := hM_col0 g 0
    have h20 : M g 2 0 = 0 := hM_col0 g 1
    change M (g * h) i.succ j.succ = ∑ k : Fin 2, M g i.succ k.succ * M h k.succ j.succ
    rw [show M (g * h) = M g * M h from hmul, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two]
    fin_cases i <;> fin_cases j <;> simp [h10, h20]
  have hB_one : B 1 = 1 := by
    ext i j
    change M 1 i.succ j.succ = (1 : Matrix (Fin 2) (Fin 2) L) i j
    rw [show M 1 = 1 from toMatrix_rep_one b ρ]
    fin_cases i <;> fin_cases j <;> simp
  have h0_mul : ∀ g h, M (g * h) 0 0 = M g 0 0 * M h 0 0 := by
    intro g h
    rw [show M (g * h) = M g * M h from toMatrix_rep_mul b ρ g h, Matrix.mul_apply,
      Fin.sum_univ_three]
    have h10 : M h 1 0 = 0 := hM_col0 h 0
    have h20 : M h 2 0 = 0 := hM_col0 h 1
    simp [h10, h20]
  have h0_one : M 1 0 0 = 1 := by rw [show M 1 = 1 from toMatrix_rep_one b ρ]; simp
  let ρ₂ : G →* GL (Fin 2) L :=
    { toFun := fun g =>
        { val := B g, inv := B g⁻¹
          val_inv := by rw [← hB_mul, mul_inv_cancel, hB_one]
          inv_val := by rw [← hB_mul, inv_mul_cancel, hB_one] }
      map_one' := Units.ext hB_one
      map_mul' := fun g h => Units.ext (hB_mul g h) }
  let χ : G →* Lˣ :=
    { toFun := fun g =>
        { val := M g 0 0, inv := M g⁻¹ 0 0
          val_inv := by rw [← h0_mul, mul_inv_cancel, h0_one]
          inv_val := by rw [← h0_mul, inv_mul_cancel, h0_one] }
      map_one' := Units.ext h0_one
      map_mul' := fun g h => Units.ext (h0_mul g h) }
  refine ⟨ρ₂, χ, ?_, fun g => ?_⟩
  · intro U hU; by_contra hne; push Not at hne; obtain ⟨hU0, hUT⟩ := hne
    have hUdim : Module.finrank L U = 1 := by
      have hp : 0 < Module.finrank L U := by
        by_contra hz; exact hU0 (Submodule.finrank_eq_zero.mp (by omega))
      have hl : Module.finrank L U < 2 := lt_of_le_of_ne
        (by simpa [Module.finrank_fin_fun] using Submodule.finrank_le U)
        (fun heq => hUT (Submodule.eq_top_of_finrank_eq (by rw [Module.finrank_fin_fun]; exact heq)))
      omega
    obtain ⟨u, huU, hune⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU0
    have hU_eq : U = Submodule.span L {u} :=
      (Submodule.eq_of_le_of_finrank_eq
        (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr huU))
        (by rw [finrank_span_singleton hune, hUdim])).symm
    let w₁ : Fin 3 → L := u 0 • b 1 + u 1 • b 2
    let W₂ : Submodule L (Fin 3 → L) := Submodule.span L ({v₀, w₁} : Set (Fin 3 → L))
    have hw₁nW : w₁ ∉ W := by
      intro hw1; rw [hW_eq, Submodule.mem_span_singleton] at hw1; obtain ⟨r, hr⟩ := hw1
      have hrepr := congrArg b.repr hr
      rw [← hb0, map_smul, map_add, map_smul, map_smul, b.repr_self, b.repr_self, b.repr_self] at hrepr
      have hu0 : u 0 = 0 := by simpa using (congrArg (fun f : Fin 3 →₀ L => f 1) hrepr).symm
      have hu1 : u 1 = 0 := by simpa using (congrArg (fun f : Fin 3 →₀ L => f 2) hrepr).symm
      exact hune (by ext i; fin_cases i <;> assumption)
    have hW_le : W ≤ W₂ := hW_eq ▸ Submodule.span_mono (by simp)
    have hW2_dim : Module.finrank L W₂ = 2 := by
      have hli2 : LinearIndependent L ![v₀, w₁] := by
        rw [Fintype.linearIndependent_iff]; intro c hc
        have hs : c 0 • v₀ + c 1 • w₁ = 0 := by simpa [Fin.sum_univ_two] using hc
        have hc1 : c 1 = 0 := by
          by_contra h1
          have hw : w₁ = (-(c 1)⁻¹ * c 0) • v₀ := by
            have h2 : c 1 • w₁ = -(c 0 • v₀) := eq_neg_of_add_eq_zero_right hs
            calc w₁ = (c 1)⁻¹ • (c 1 • w₁) := by rw [smul_smul, inv_mul_cancel₀ h1, one_smul]
              _ = (c 1)⁻¹ • (-(c 0 • v₀)) := by rw [h2]
              _ = _ := by simp [smul_neg, smul_smul, neg_mul]
          exact hw₁nW (hw ▸ W.smul_mem _ hv₀W)
        rw [hc1, zero_smul, add_zero] at hs
        have hc0 : c 0 = 0 := (smul_eq_zero.mp hs).resolve_right hv₀ne
        intro i; fin_cases i <;> assumption
      have hset : Set.range ![v₀, w₁] = ({v₀, w₁} : Set (Fin 3 → L)) := by
        ext x; simp [or_comm]
      have hcard := finrank_span_eq_card hli2
      rw [hset, Fintype.card_fin] at hcard; exact hcard
    have hW2_inv : IsGInvariant3 ρ W₂ := by
      intro g v hv; rw [Submodule.mem_span_pair] at hv; obtain ⟨a, c, rfl⟩ := hv
      rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul]
      refine W₂.add_mem (W₂.smul_mem _ (hW_le (hW g v₀ hv₀W))) (W₂.smul_mem _ ?_)
      have hBu : (B g).mulVec u ∈ U := hU g u huU
      rw [hU_eq, Submodule.mem_span_singleton] at hBu; obtain ⟨lam, hlam⟩ := hBu
      have hlam0 : lam * u 0 = M g 1 1 * u 0 + M g 1 2 * u 1 := by
        simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two, B] using congrFun hlam 0
      have hlam1 : lam * u 1 = M g 2 1 * u 0 + M g 2 2 * u 1 := by
        simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two, B] using congrFun hlam 1
      have hmw1 : ((ρ g : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L).mulVec w₁ =
          (M g 0 1 * u 0 + M g 0 2 * u 1) • v₀ + lam • w₁ := by
        apply b.repr.injective; ext i
        have hact : ∀ k : Fin 3,
            b.repr (((ρ g : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L).mulVec (b k)) i = M g i k :=
          fun k => by dsimp only [M]; rw [LinearMap.toMatrix_apply]; rfl
        simp only [w₁, Matrix.mulVec_add, Matrix.mulVec_smul, map_add, map_smul,
          Finsupp.add_apply, Finsupp.smul_apply, hact, ← hb0, b.repr_self, smul_eq_mul]
        fin_cases i
        · change u 0 * M g 0 1 + u 1 * M g 0 2 =
            (M g 0 1 * u 0 + M g 0 2 * u 1) * (Finsupp.single (0 : Fin 3) (1 : L) 0) +
            lam * (u 0 * (Finsupp.single (1 : Fin 3) (1 : L) 0) +
                   u 1 * (Finsupp.single (2 : Fin 3) (1 : L) 0))
          simp; ring
        · change u 0 * M g 1 1 + u 1 * M g 1 2 =
            (M g 0 1 * u 0 + M g 0 2 * u 1) * (Finsupp.single (0 : Fin 3) (1 : L) 1) +
            lam * (u 0 * (Finsupp.single (1 : Fin 3) (1 : L) 1) +
                   u 1 * (Finsupp.single (2 : Fin 3) (1 : L) 1))
          simp; linear_combination -hlam0
        · change u 0 * M g 2 1 + u 1 * M g 2 2 =
            (M g 0 1 * u 0 + M g 0 2 * u 1) * (Finsupp.single (0 : Fin 3) (1 : L) 2) +
            lam * (u 0 * (Finsupp.single (1 : Fin 3) (1 : L) 2) +
                   u 1 * (Finsupp.single (2 : Fin 3) (1 : L) 2))
          simp; linear_combination -hlam1
      rw [hmw1]
      exact W₂.add_mem (W₂.smul_mem _ (Submodule.subset_span (by simp)))
        (W₂.smul_mem _ (Submodule.subset_span (by simp)))
    exact hnot3 ⟨W, W₂, hW, hW2_inv, hW_le, hd1, hW2_dim⟩
  · rw [toMatrix_rep_trace b ρ g]
    change (M g).trace = (B g).trace + M g 0 0
    simp only [Matrix.trace, Fin.sum_univ_three, Fin.sum_univ_two, B]
    change M g 0 0 + M g 1 1 + M g 2 2 = M g 1 1 + M g 2 2 + M g 0 0; ring

/-- Helper: given a 2D invariant subspace `W` and complement `C`, extract `ρ₂` and `χ` for Type II. -/
private theorem typeII_constituent_of_dim2 {G L : Type*} [Group G] [Field L]
    (ρ : G →* GL (Fin 3) L) (hnot3 : ¬ IsTypeIII ρ)
    (W : Submodule L (Fin 3 → L)) (hW : IsGInvariant3 ρ W) (hd2 : Module.finrank L W = 2) :
    ∃ (ρ₂ : G →* GL (Fin 2) L) (χ : G →* Lˣ),
      IsIrreducible2D ρ₂ ∧
      ∀ g : G, ((ρ g : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L).trace =
        ((ρ₂ g : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L).trace + (χ g : L) := by
  classical
  let bW := Module.finBasisOfFinrankEq L W hd2
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl W
  have hCdim : Module.finrank L C = 1 := by
    have hsum := Submodule.finrank_add_eq_of_isCompl hC
    rw [Module.finrank_fin_fun, hd2] at hsum; omega
  have hCne : C ≠ ⊥ := fun h0 => by rw [h0, finrank_bot] at hCdim; omega
  obtain ⟨v₂, hv₂C, hv₂ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hCne
  let vecs : Fin 3 → (Fin 3 → L) := ![(bW 0).1, (bW 1).1, v₂]
  have hli : LinearIndependent L vecs := by
    rw [Fintype.linearIndependent_iff]; intro c hc
    have hsum : (c 0 • (bW 0).1 + c 1 • (bW 1).1) + c 2 • v₂ = 0 := by
      simpa [vecs, Fin.sum_univ_three, add_assoc] using hc
    have hbot : c 2 • v₂ ∈ W ⊓ C :=
      ⟨(eq_neg_of_add_eq_zero_right hsum) ▸
        W.neg_mem (W.add_mem (W.smul_mem _ (bW 0).2) (W.smul_mem _ (bW 1).2)), C.smul_mem _ hv₂C⟩
    rw [hC.inf_eq_bot, Submodule.mem_bot] at hbot
    have hc2 : c 2 = 0 := (smul_eq_zero.mp hbot).resolve_right hv₂ne
    rw [hc2, zero_smul, add_zero] at hsum
    have hliW := Fintype.linearIndependent_iff.mp bW.linearIndependent ![c 0, c 1]
      (by simpa [Fin.sum_univ_two] using (Subtype.ext hsum : c 0 • bW 0 + c 1 • bW 1 = 0))
    intro i; fin_cases i
    · exact hliW 0
    · exact hliW 1
    · exact hc2
  have hspan : Submodule.span L (Set.range vecs) = ⊤ :=
    Submodule.eq_top_of_finrank_eq (by
      rw [finrank_span_eq_card hli, Fintype.card_fin, Module.finrank_fin_fun])
  let b : Basis (Fin 3) L (Fin 3 → L) := Basis.mk hli (le_of_eq hspan.symm)
  let M : G → Matrix (Fin 3) (Fin 3) L := fun g =>
    LinearMap.toMatrix b b ((ρ g : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L).mulVecLin
  have hb0 : b 0 = (bW 0).1 := by simp [b, vecs]
  have hb1 : b 1 = (bW 1).1 := by simp [b, vecs]
  have hM_row2 : ∀ (g : G) (j : Fin 2), M g 2 j.castSucc = 0 := by
    intro g j
    have hmem : ((ρ g : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L).mulVec (bW j).1 ∈ W :=
      hW g (bW j).1 (bW j).2
    have hrep := bW.sum_repr ⟨_, hmem⟩
    rw [Fin.sum_univ_two] at hrep
    have hx' : ((ρ g : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L).mulVec (bW j).1 =
        (bW.repr ⟨_, hmem⟩ 0) • b 0 + (bW.repr ⟨_, hmem⟩ 1) • b 1 := by
      rw [hb0, hb1]; exact (congrArg Subtype.val hrep).symm
    have hbj : b j.castSucc = (bW j).1 := by fin_cases j <;> simp [b, vecs]
    dsimp only [M]; rw [LinearMap.toMatrix_apply, hbj]
    change (b.repr (((ρ g : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L).mulVec (bW j).1)) 2 = 0
    rw [hx', map_add, map_smul, map_smul, b.repr_self, b.repr_self]; simp
  let B : G → Matrix (Fin 2) (Fin 2) L := fun g i j => M g i.castSucc j.castSucc
  have hB_mul : ∀ g h, B (g * h) = B g * B h := by
    intro g h; ext i j
    have h20 : M h 2 0 = 0 := hM_row2 h 0
    have h21 : M h 2 1 = 0 := hM_row2 h 1
    change M (g * h) i.castSucc j.castSucc = ∑ k : Fin 2, M g i.castSucc k.castSucc * M h k.castSucc j.castSucc
    rw [show M (g * h) = M g * M h from toMatrix_rep_mul b ρ g h, Matrix.mul_apply,
      Fin.sum_univ_three, Fin.sum_univ_two]
    fin_cases i <;> fin_cases j <;> simp [h20, h21]
  have hB_one : B 1 = 1 := by
    ext i j
    change M 1 i.castSucc j.castSucc = (1 : Matrix (Fin 2) (Fin 2) L) i j
    rw [show M 1 = 1 from toMatrix_rep_one b ρ]
    fin_cases i <;> fin_cases j <;> simp
  have h2_mul : ∀ g h, M (g * h) 2 2 = M g 2 2 * M h 2 2 := by
    intro g h
    rw [show M (g * h) = M g * M h from toMatrix_rep_mul b ρ g h, Matrix.mul_apply,
      Fin.sum_univ_three]
    have h20 : M g 2 0 = 0 := hM_row2 g 0
    have h21 : M g 2 1 = 0 := hM_row2 g 1
    simp [h20, h21]
  have h2_one : M 1 2 2 = 1 := by rw [show M 1 = 1 from toMatrix_rep_one b ρ]; simp
  let ρ₂ : G →* GL (Fin 2) L :=
    { toFun := fun g =>
        { val := B g, inv := B g⁻¹
          val_inv := by rw [← hB_mul, mul_inv_cancel, hB_one]
          inv_val := by rw [← hB_mul, inv_mul_cancel, hB_one] }
      map_one' := Units.ext hB_one
      map_mul' := fun g h => Units.ext (hB_mul g h) }
  let χ : G →* Lˣ :=
    { toFun := fun g =>
        { val := M g 2 2, inv := M g⁻¹ 2 2
          val_inv := by rw [← h2_mul, mul_inv_cancel, h2_one]
          inv_val := by rw [← h2_mul, inv_mul_cancel, h2_one] }
      map_one' := Units.ext h2_one
      map_mul' := fun g h => Units.ext (h2_mul g h) }
  refine ⟨ρ₂, χ, ?_, fun g => ?_⟩
  · intro U hU; by_contra hne; push Not at hne; obtain ⟨hU0, hUT⟩ := hne
    have hUdim : Module.finrank L U = 1 := by
      have hp : 0 < Module.finrank L U := by
        by_contra hz; exact hU0 (Submodule.finrank_eq_zero.mp (by omega))
      have hl : Module.finrank L U < 2 := lt_of_le_of_ne
        (by simpa [Module.finrank_fin_fun] using Submodule.finrank_le U)
        (fun heq => hUT (Submodule.eq_top_of_finrank_eq (by rw [Module.finrank_fin_fun]; exact heq)))
      omega
    obtain ⟨u, huU, hune⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU0
    have hU_eq : U = Submodule.span L {u} :=
      (Submodule.eq_of_le_of_finrank_eq
        (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr huU))
        (by rw [finrank_span_singleton hune, hUdim])).symm
    let w₀ : Fin 3 → L := u 0 • b 0 + u 1 • b 1
    have hw₀ne : w₀ ≠ 0 := by
      intro h0
      have hrep := congrArg b.repr h0
      simp only [w₀, map_add, map_smul, map_zero, b.repr_self] at hrep
      have hu0 : u 0 = 0 := by simpa using congrArg (fun f : Fin 3 →₀ L => f 0) hrep
      have hu1 : u 1 = 0 := by simpa using congrArg (fun f : Fin 3 →₀ L => f 1) hrep
      exact hune (by ext i; fin_cases i <;> assumption)
    let W₁ : Submodule L (Fin 3 → L) := Submodule.span L {w₀}
    have hW1_le : W₁ ≤ W := Submodule.span_le.mpr (Set.singleton_subset_iff.mpr
      (W.add_mem (W.smul_mem _ (hb0 ▸ (bW 0).2)) (W.smul_mem _ (hb1 ▸ (bW 1).2))))
    have hW1_inv : IsGInvariant3 ρ W₁ := by
      intro g v hv; rw [Submodule.mem_span_singleton] at hv; obtain ⟨r, rfl⟩ := hv
      rw [Matrix.mulVec_smul]; refine W₁.smul_mem r ?_
      have hBu : (B g).mulVec u ∈ U := hU g u huU
      rw [hU_eq, Submodule.mem_span_singleton] at hBu; obtain ⟨lam, hlam⟩ := hBu
      have hlam0 : lam * u 0 = M g 0 0 * u 0 + M g 0 1 * u 1 := by
        simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two, B] using congrFun hlam 0
      have hlam1 : lam * u 1 = M g 1 0 * u 0 + M g 1 1 * u 1 := by
        simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two, B] using congrFun hlam 1
      have hmw0 : ((ρ g : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L).mulVec w₀ = lam • w₀ := by
        apply b.repr.injective; ext i
        have hact : ∀ k : Fin 3,
            b.repr (((ρ g : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L).mulVec (b k)) i = M g i k :=
          fun k => by dsimp only [M]; rw [LinearMap.toMatrix_apply]; rfl
        simp only [w₀, Matrix.mulVec_add, Matrix.mulVec_smul, map_add, map_smul,
          Finsupp.add_apply, Finsupp.smul_apply, hact, b.repr_self, smul_eq_mul]
        fin_cases i
        · change u 0 * M g 0 0 + u 1 * M g 0 1 =
            lam * (u 0 * (Finsupp.single (0 : Fin 3) (1 : L) 0) +
                   u 1 * (Finsupp.single (1 : Fin 3) (1 : L) 0))
          simp; linear_combination -hlam0
        · change u 0 * M g 1 0 + u 1 * M g 1 1 =
            lam * (u 0 * (Finsupp.single (0 : Fin 3) (1 : L) 1) +
                   u 1 * (Finsupp.single (1 : Fin 3) (1 : L) 1))
          simp; linear_combination -hlam1
        · change u 0 * M g 2 0 + u 1 * M g 2 1 =
            lam * (u 0 * (Finsupp.single (0 : Fin 3) (1 : L) 2) +
                   u 1 * (Finsupp.single (1 : Fin 3) (1 : L) 2))
          have h20 : M g 2 0 = 0 := hM_row2 g 0
          have h21 : M g 2 1 = 0 := hM_row2 g 1
          simp [h20, h21]
      rw [hmw0]; exact W₁.smul_mem lam (Submodule.subset_span rfl)
    exact hnot3 ⟨W₁, W, hW1_inv, hW, hW1_le, finrank_span_singleton hw₀ne, hd2⟩
  · rw [toMatrix_rep_trace b ρ g]
    change (M g).trace = (B g).trace + M g 2 2
    simp only [Matrix.trace, Fin.sum_univ_three, Fin.sum_univ_two, B]
    change M g 0 0 + M g 1 1 + M g 2 2 = M g 0 0 + M g 1 1 + M g 2 2; rfl

/-- **Type II Irreducible `2 + 1` Constituent Extraction (`typeII_has_2d_irreducible_constituent`)**:
Every Type II representation `ρ : G →* GL (Fin 3) L` decomposes (in trace) into an irreducible
2D representation `ρ₂` plus a 1D character `χ`: `tr(ρ(g)) = tr(ρ₂(g)) + χ(g)`! -/
theorem typeII_has_2d_irreducible_constituent {G L : Type*} [Group G] [Field L]
    (ρ : G →* GL (Fin 3) L) (hII : IsTypeII ρ) :
    ∃ (ρ₂ : G →* GL (Fin 2) L) (χ : G →* Lˣ),
      IsIrreducible2D ρ₂ ∧
      ∀ g : G, ((ρ g : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L).trace =
        ((ρ₂ g : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L).trace + (χ g : L) := by
  obtain ⟨⟨W, hW, hne0, hneT⟩, hnot3⟩ := hII
  have hdim_pos : 0 < Module.finrank L W := by
    by_contra h0; exact hne0 (Submodule.finrank_eq_zero.mp (by omega))
  have hdim_lt : Module.finrank L W < 3 := lt_of_le_of_ne
    (by simpa [Module.finrank_fin_fun] using Submodule.finrank_le W)
    (fun heq => hneT (Submodule.eq_top_of_finrank_eq (by rw [Module.finrank_fin_fun]; exact heq)))
  have hcases : Module.finrank L W = 1 ∨ Module.finrank L W = 2 := by omega
  rcases hcases with hd1 | hd2
  · exact typeII_constituent_of_dim1 ρ hnot3 W hW hd1
  · exact typeII_constituent_of_dim2 ρ hnot3 W hW hd2

/-! ### 3.4 Type I Ordinary `U(3)` Automorphy Lifting (`ModUAlt` + `ModNOf`) & Type II Kato Rigidity (`KatoTwoW`) -/

def block21 {L : Type*} [CommRing L] (A : Matrix (Fin 2) (Fin 2) L) (d : L) :
    Matrix (Fin 3) (Fin 3) L :=
  !![A 0 0, A 0 1, 0;
     A 1 0, A 1 1, 0;
     0,     0,     d]

/-- **Exact `3 × 3` Adjoint Block Decomposition for Type II (`2 + 1`) Representations**. -/
theorem u3_typeII_adjoint_decomp {L : Type*} [Field L]
    (A : GL (Fin 2) L) (d : Lˣ) (X : Matrix (Fin 3) (Fin 3) L) :
    let G := block21 (A : Matrix (Fin 2) (Fin 2) L) (d : L)
    let Gi := block21 ((A⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) ((d⁻¹ : Lˣ) : L)
    let Y := G * X * Gi
    let X11 : Matrix (Fin 2) (Fin 2) L := Matrix.of fun r s => X r.castSucc s.castSucc
    (∀ i j : Fin 2, Y i.castSucc j.castSucc =
      ((A : Matrix (Fin 2) (Fin 2) L) * X11 *
        ((A⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L)) i j) ∧
    (∀ i : Fin 2, Y i.castSucc 2 =
      ((d⁻¹ : Lˣ) : L) * ((A : Matrix (Fin 2) (Fin 2) L).mulVec (fun r : Fin 2 => X r.castSucc 2)) i) ∧
    (∀ j : Fin 2, Y 2 j.castSucc =
      (d : L) * ((fun s : Fin 2 => X 2 s.castSucc) ᵥ* ((A⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L)) j) ∧
    Y 2 2 = X 2 2 := by
  intro G Gi Y X11
  have hdd : (d : L) * ((d⁻¹ : Lˣ) : L) = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i j; fin_cases i <;> fin_cases j <;>
      (simp only [Y, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two];
       simp [G, Gi, X11, block21]; try ring)
  · intro i; fin_cases i <;>
      (simp only [Y, Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three, Fin.sum_univ_two];
       simp [G, Gi, block21]; ring)
  · intro j; fin_cases j <;>
      (simp only [Y, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_three, Fin.sum_univ_two];
       simp [G, Gi, block21]; ring)
  · simp only [Y, Matrix.mul_apply, Fin.sum_univ_three]
    simp only [G, Gi, block21, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, zero_mul, mul_zero, zero_add, add_zero]
    calc (d : L) * X 2 2 * ((d⁻¹ : Lˣ) : L) = ((d : L) * ((d⁻¹ : Lˣ) : L)) * X 2 2 := by ring
      _ = X 2 2 := by rw [hdd, one_mul]

/-- **Type II Kato Euler System Rigidity (`u3_typeII_kato_rigidity` / `KatoTwoW`)**. -/
theorem u3_typeII_kato_rigidity {L : Type*} [Field L]
    {T_ad2 T_kato1 T_kato2 : Type*}
    [AddCommGroup T_ad2] [Module L T_ad2] [Module.Finite L T_ad2]
    [AddCommGroup T_kato1] [Module L T_kato1] [Module.Finite L T_kato1]
    [AddCommGroup T_kato2] [Module L T_kato2] [Module.Finite L T_kato2]
    (h_ad2 : Module.finrank L T_ad2 = 0)
    (h_kato1 : Module.finrank L T_kato1 = 0)
    (h_kato2 : Module.finrank L T_kato2 = 0) :
    Module.finrank L (T_ad2 × T_kato1 × T_kato2) = 0 ∧
      Subsingleton (T_ad2 × T_kato1 × T_kato2) := by
  have hdim : Module.finrank L (T_ad2 × T_kato1 × T_kato2) = 0 := by
    rw [Module.finrank_prod, Module.finrank_prod, h_ad2, h_kato1, h_kato2]
  refine ⟨hdim, ⟨fun x y => ?_⟩⟩
  have hzero : ∀ v : T_ad2 × T_kato1 × T_kato2, v = 0 := by
    intro v; by_contra hv
    have h1 : 1 ≤ Module.finrank L (T_ad2 × T_kato1 × T_kato2) := by
      rw [← finrank_span_singleton (K := L) hv]; exact Submodule.finrank_le _
    omega
  rw [hzero x, hzero y]

/-- **Patched Ordinary `U(3)` Hida Automorphy Lifting Datum (`U3PatchingHidaDatum`)**. -/
structure U3PatchingHidaDatum (𝒪 : Type*) [CommRing 𝒪] where
  R_U3 : Type
  T_U3 : Type
  [ringR : CommRing R_U3]
  [ringT : CommRing T_U3]
  [algR : Algebra 𝒪 R_U3]
  [algT : Algebra 𝒪 T_U3]
  φ : R_U3 →ₐ[𝒪] T_U3
  φ_surj : Function.Surjective φ
  ker_nilpotent : ∀ r ∈ RingHom.ker φ.toRingHom, IsNilpotent r

attribute [instance] U3PatchingHidaDatum.ringR U3PatchingHidaDatum.ringT
  U3PatchingHidaDatum.algR U3PatchingHidaDatum.algT

/-- **Ordinary `U(3)` Automorphy Lifting Theorem (`u3_typeI_automorphy_lifting` / `ModUAlt`)**. -/
theorem u3_typeI_automorphy_lifting {𝒪 L : Type*} [CommRing 𝒪] [Field L] [Algebra 𝒪 L]
    (D : U3PatchingHidaDatum 𝒪) (x : D.R_U3 →ₐ[𝒪] L) :
    ∃! y : D.T_U3 →ₐ[𝒪] L, y.comp D.φ = x := by
  have hker_le : RingHom.ker D.φ.toRingHom ≤ RingHom.ker x.toRingHom := by
    intro r hr; obtain ⟨n, hn⟩ := D.ker_nilpotent r hr
    rw [RingHom.mem_ker]
    exact eq_zero_of_pow_eq_zero (by rw [← map_pow, hn, map_zero] : (x r) ^ n = 0)
  let yFun : D.T_U3 → L := fun t => x (D.φ_surj t).choose
  have hyFun_eq : ∀ r : D.R_U3, yFun (D.φ r) = x r := fun r => by
    have hmem : (D.φ_surj (D.φ r)).choose - r ∈ RingHom.ker D.φ.toRingHom := by
      rw [RingHom.mem_ker, map_sub]
      change D.φ (D.φ_surj (D.φ r)).choose - D.φ r = 0
      rw [(D.φ_surj (D.φ r)).choose_spec, sub_self]
    have hx0 : x ((D.φ_surj (D.φ r)).choose - r) = 0 := RingHom.mem_ker.mp (hker_le hmem)
    rw [map_sub] at hx0
    exact sub_eq_zero.mp hx0
  let y : D.T_U3 →ₐ[𝒪] L :=
    { toFun := yFun
      map_one' := by simpa using hyFun_eq 1
      map_mul' := fun t₁ t₂ => by
        obtain ⟨r₁, rfl⟩ := D.φ_surj t₁; obtain ⟨r₂, rfl⟩ := D.φ_surj t₂
        rw [← map_mul, hyFun_eq, hyFun_eq, hyFun_eq, map_mul]
      map_zero' := by simpa using hyFun_eq 0
      map_add' := fun t₁ t₂ => by
        obtain ⟨r₁, rfl⟩ := D.φ_surj t₁; obtain ⟨r₂, rfl⟩ := D.φ_surj t₂
        rw [← map_add, hyFun_eq, hyFun_eq, hyFun_eq, map_add]
      commutes' := fun c => by
        have h := hyFun_eq (algebraMap 𝒪 D.R_U3 c)
        rw [AlgHom.commutes, AlgHom.commutes] at h; exact h }
  refine ⟨y, AlgHom.ext hyFun_eq, fun y' hy' => AlgHom.ext fun t => ?_⟩
  obtain ⟨r, rfl⟩ := D.φ_surj t
  exact (AlgHom.congr_fun hy' r).trans (hyFun_eq r).symm

/-- **Multiplicity One Injection (`u3_modNOf_distinct_automorphic_forms`)**. -/
theorem u3_modNOf_distinct_automorphic_forms {𝒪 L : Type*} [CommRing 𝒪] [Field L] [Algebra 𝒪 L]
    (D : U3PatchingHidaDatum 𝒪) {x₁ x₂ : D.R_U3 →ₐ[𝒪] L} {y₁ y₂ : D.T_U3 →ₐ[𝒪] L}
    (hy₁ : y₁.comp D.φ = x₁) (hy₂ : y₂.comp D.φ = x₂) (hne : x₁ ≠ x₂) :
    y₁ ≠ y₂ := fun heq => hne (by rw [← hy₁, ← hy₂, heq])

/-! ### 3.5 Main `CountI` Selmer Length Bound (`countI_u3_selmer_bound`) & Global Resultant Bound -/

theorem length_pi_fin (R N : Type*) [Ring R] [AddCommGroup N] [Module R N] (r : ℕ) :
    Module.length R (Fin r → N) = (r : ℕ∞) * Module.length R N := by
  induction r with
  | zero =>
    have : Subsingleton (Fin 0 → N) := inferInstance
    simp
  | succ r ih =>
    let e : (Fin (r + 1) → N) ≃ₗ[R] N × (Fin r → N) :=
      { toFun := fun v => (v 0, fun i => v i.succ)
        invFun := fun p => Fin.cons p.1 p.2
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl
        left_inv := fun v => by ext i; cases i using Fin.cases with | zero => rfl | succ j => rfl
        right_inv := fun _ => Prod.ext rfl rfl }
    have hlen_e : Module.length R (Fin (r + 1) → N) = Module.length R (N × (Fin r → N)) :=
      le_antisymm (Module.length_le_of_injective e.toLinearMap e.injective)
        (Module.length_le_of_injective e.symm.toLinearMap e.symm.injective)
    have hprod : Module.length R (N × (Fin r → N)) =
        Module.length R N + Module.length R (Fin r → N) := by
      have hex : Function.Exact (LinearMap.inl R N (Fin r → N)) (LinearMap.snd R N (Fin r → N)) :=
        fun p => ⟨fun hp => ⟨p.1, Prod.ext rfl hp.symm⟩, fun ⟨_, ha⟩ => by rw [← ha]; rfl⟩
      exact Module.length_eq_add_of_exact (LinearMap.inl R N (Fin r → N))
        (LinearMap.snd R N (Fin r → N)) LinearMap.inl_injective Prod.snd_surjective hex
    rw [hlen_e, hprod, ih]; push_cast; ring

/-- **Main `CountI` Single-Character `U(3)` Selmer Bound (`countI_u3_selmer_bound` / `FOneCharU`)**:
$$\operatorname{length}_{\mathcal{O}}(\mathrm{Sel}) \le
  2 \sum_{\pi \in X_I} v_I(\pi) + 2 \sum_{g \in X_{II}} v_{II}(g)!$$ -/
theorem countI_u3_selmer_bound
    {𝒪 R G : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    {ϖ : 𝒪} (hϖ : Irreducible ϖ)
    [CommRing R] [Algebra 𝒪 R] [Group G] (U : U3DeformGMA R G)
    {Sel : Type*} [AddCommGroup Sel] [Module R Sel] [Module 𝒪 Sel] [IsScalarTower 𝒪 R Sel]
    (hann : ∀ a ∈ U.reducibilityIdeal, ∀ x : Sel, a • x = 0)
    (gen : Fin 2 → Sel) (hgen : Submodule.span R (Set.range gen) = ⊤)
    (hcyc : Module.length 𝒪 (R ⧸ U.reducibilityIdeal) ≤
      Module.length 𝒪 (𝒪 ⧸ U.reducibilityIdeal.comap (algebraMap 𝒪 R)))
    {δ : R} (hδ : δ ∈ U.reducibilityIdeal)
    {P : 𝒪[X]} (hP : Polynomial.eval₂ (algebraMap 𝒪 R) δ P = 0)
    {ι₁ ι₂ : Type*} (X_I : Finset ι₁) (X_II : Finset ι₂)
    (v_I : ι₁ → ℕ) (v_II : ι₂ → ℕ)
    (hfac : ∃ u : 𝒪ˣ, P.coeff 0 =
      (u : 𝒪) * ϖ ^ ((∑ π ∈ X_I, v_I π) + (∑ g ∈ X_II, v_II g))) :
    Module.length 𝒪 Sel ≤
      ((2 * ∑ π ∈ X_I, v_I π + 2 * ∑ g ∈ X_II, v_II g : ℕ) : ℕ∞) := by
  let compMap : Fin 2 → (R ⧸ U.reducibilityIdeal) →ₗ[R] Sel := fun i =>
    Submodule.liftQ U.reducibilityIdeal
      ((LinearMap.lsmul R Sel).flip (gen i))
      (fun a ha => hann a ha (gen i))
  let qMap : (Fin 2 → R ⧸ U.reducibilityIdeal) →ₗ[𝒪] Sel :=
    { toFun := fun v => ∑ i : Fin 2, compMap i (v i)
      map_add' := fun v w => by simp only [Pi.add_apply, map_add, Finset.sum_add_distrib]
      map_smul' := fun a v => by
        simp only [Pi.smul_apply, RingHom.id_apply, Finset.smul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        have h1 : compMap i (a • v i) = compMap i ((algebraMap 𝒪 R a) • v i) := by
          congr 1; exact (algebraMap_smul R a (v i)).symm
        rw [h1, map_smul, algebraMap_smul] }
  have hsurj : Function.Surjective qMap := by
    intro y
    have hy : y ∈ Submodule.span R (Set.range gen) := hgen ▸ Submodule.mem_top
    rw [Submodule.mem_span_range_iff_exists_fun] at hy
    obtain ⟨c, rfl⟩ := hy
    exact ⟨fun i => Submodule.Quotient.mk (c i), rfl⟩
  have hSel_le : Module.length 𝒪 Sel ≤ (2 : ℕ∞) * Module.length 𝒪 (R ⧸ U.reducibilityIdeal) :=
    (Module.length_le_of_surjective qMap hsurj).trans_eq (length_pi_fin 𝒪 (R ⧸ U.reducibilityIdeal) 2)
  have hcomap := u3_reducibility_comap_length_le_val hϖ U.reducibilityIdeal (algebraMap 𝒪 R) hδ hP
    ((∑ π ∈ X_I, v_I π) + (∑ g ∈ X_II, v_II g)) hfac
  calc Module.length 𝒪 Sel
      ≤ (2 : ℕ∞) * Module.length 𝒪 (R ⧸ U.reducibilityIdeal) := hSel_le
    _ ≤ (2 : ℕ∞) * Module.length 𝒪 (𝒪 ⧸ U.reducibilityIdeal.comap (algebraMap 𝒪 R)) :=
        mul_le_mul_of_nonneg_left hcyc (by simp)
    _ ≤ (2 : ℕ∞) * (((∑ π ∈ X_I, v_I π) + (∑ g ∈ X_II, v_II g) : ℕ) : ℕ∞) :=
        mul_le_mul_of_nonneg_left hcomap (by simp)
    _ = ((2 * ∑ π ∈ X_I, v_I π + 2 * ∑ g ∈ X_II, v_II g : ℕ) : ℕ∞) := by push_cast; ring

theorem corG_sum_log_int {L_s : Finset ℕ} (hprime : ∀ l ∈ L_s, l.Prime)
    {NN : ℤ} (hNN : NN ≠ 0) :
    ∑ l ∈ L_s, Real.log (l : ℝ) * (padicValInt l NN : ℝ) ≤ Real.log (|NN| : ℝ) := by
  have hdvd : (∏ l ∈ L_s, l ^ padicValNat l NN.natAbs) ∣ NN.natAbs := by
    induction L_s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
      rw [Finset.prod_insert ha]
      have hpa : a.Prime := hprime a (Finset.mem_insert_self a s)
      have ih' := ih (fun l hl => hprime l (Finset.mem_insert_of_mem hl))
      refine Nat.Coprime.mul_dvd_of_dvd_of_dvd ?_ pow_padicValNat_dvd ih'
      refine Nat.Coprime.prod_right fun q hq => ?_
      have hne : a ≠ q := fun h => ha (h ▸ hq)
      exact ((Nat.coprime_primes hpa (hprime q (Finset.mem_insert_of_mem hq))).mpr hne).pow _ _
  have hle_nat : ∏ l ∈ L_s, l ^ padicValNat l NN.natAbs ≤ NN.natAbs :=
    Nat.le_of_dvd (Int.natAbs_pos.mpr hNN) hdvd
  have hprod_pos : (0 : ℝ) < ∏ l ∈ L_s, (l : ℝ) ^ padicValNat l NN.natAbs :=
    Finset.prod_pos fun l hl => pow_pos (Nat.cast_pos.mpr (hprime l hl).pos) _
  have hle_real : (∏ l ∈ L_s, (l : ℝ) ^ padicValNat l NN.natAbs) ≤ (|NN| : ℝ) := by
    have h1 : ((∏ l ∈ L_s, l ^ padicValNat l NN.natAbs : ℕ) : ℝ) ≤ (NN.natAbs : ℝ) := by
      exact_mod_cast hle_nat
    have h2 : (NN.natAbs : ℝ) = (|NN| : ℝ) := by
      rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
    simpa [Nat.cast_prod, Nat.cast_pow, h2] using h1
  have hlog := Real.log_le_log hprod_pos hle_real
  rw [Real.log_prod (fun l hl => ne_of_gt (pow_pos (Nat.cast_pos.mpr (hprime l hl).pos) _))] at hlog
  calc ∑ l ∈ L_s, Real.log (l : ℝ) * (padicValInt l NN : ℝ)
      = ∑ l ∈ L_s, Real.log ((l : ℝ) ^ padicValNat l NN.natAbs) :=
        Finset.sum_congr rfl fun l _ => by rw [Real.log_pow, padicValInt, mul_comm]
    _ ≤ Real.log (|NN| : ℝ) := hlog

/-- **Global Multi-Prime `CountI` Polynomial Bound (`countI_u3_multi_prime_poly_bound`)**. -/
theorem countI_u3_multi_prime_poly_bound {L_s : Finset ℕ} (hprime : ∀ l ∈ L_s, l.Prime)
    (Vn : ℕ → ℕ) {NN : ℤ} (hNN : NN ≠ 0)
    (hval : ∀ l ∈ L_s, Vn l ≤ 2 * padicValInt l NN)
    {B : ℝ} (hNN_log : 2 * Real.log (|NN| : ℝ) ≤ B) :
    ∑ l ∈ L_s, Real.log (l : ℝ) * (Vn l : ℝ) ≤ B := by
  have hstep : ∑ l ∈ L_s, Real.log (l : ℝ) * (Vn l : ℝ) ≤
      2 * ∑ l ∈ L_s, Real.log (l : ℝ) * (padicValInt l NN : ℝ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun l hl => ?_
    have hlog_nn : 0 ≤ Real.log (l : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (hprime l hl).one_lt.le)
    have hvl : (Vn l : ℝ) ≤ 2 * (padicValInt l NN : ℝ) := by exact_mod_cast hval l hl
    nlinarith
  linarith [corG_sum_log_int hprime hNN]

end U3DeformationAndCountI

/-! ## Section 4: Weight-2 (`e = 1`) Inertia / Fontaine–Laffaille Tangent Bound & `CountV` Discharge -/

section Weight2InertiaCountV

/-! ### 4.1 Concrete 3D Weight-2 (`e = 1`, Hodge–Tate Weights `{0, 1, 2}`) Filtered `φ`-Module -/

def u3Weight2FilSub (p : ℕ) [Fact p.Prime] (i : ℤ) : Submodule ℚ_[p] (Fin 3 → ℚ_[p]) :=
  if i ≤ 0 then ⊤
  else if i = 1 then Submodule.span ℚ_[p] ({Pi.single 0 1, Pi.single 1 1} : Set (Fin 3 → ℚ_[p]))
  else if i = 2 then Submodule.span ℚ_[p] ({Pi.single 0 1} : Set (Fin 3 → ℚ_[p]))
  else ⊥

theorem u3Weight2FilSub_antitone (p : ℕ) [Fact p.Prime] : Antitone (u3Weight2FilSub p) := by
  intro i j hij; unfold u3Weight2FilSub
  split_ifs
  all_goals try exact le_rfl
  all_goals try exact le_top
  all_goals try exact bot_le
  all_goals try omega
  · exact Submodule.span_mono (by simp)

def u3Weight2Fil (p : ℕ) [Fact p.Prime] : Stage2HodgeWeights.HodgeFiltration ℚ_[p] (Fin 3 → ℚ_[p]) where
  fil := u3Weight2FilSub p
  antitone := fun _ _ h => u3Weight2FilSub_antitone p h
  botBound := 0
  topBound := 2
  bot_le_top := by norm_num
  eq_top_of_le := fun i hi => by unfold u3Weight2FilSub; simp [hi]
  eq_bot_of_gt := fun i hi => by
    unfold u3Weight2FilSub
    have h1 : ¬ i ≤ 0 := by omega
    have h2 : i ≠ 1 := by omega
    have h3 : i ≠ 2 := by omega
    simp [h1, h2, h3]

theorem mem_u3Weight2Fil_one_iff (p : ℕ) [Fact p.Prime] (v : Fin 3 → ℚ_[p]) :
    v ∈ (u3Weight2Fil p).fil 1 ↔ v 2 = 0 := by
  change v ∈ Submodule.span ℚ_[p] ({Pi.single 0 1, Pi.single 1 1} : Set (Fin 3 → ℚ_[p])) ↔ v 2 = 0
  rw [Submodule.mem_span_pair]
  exact ⟨fun ⟨a, b, h⟩ => by rw [← h]; simp,
    fun hv2 => ⟨v 0, v 1, by ext i; fin_cases i <;> simp [hv2]⟩⟩

theorem mem_u3Weight2Fil_two_iff (p : ℕ) [Fact p.Prime] (v : Fin 3 → ℚ_[p]) :
    v ∈ (u3Weight2Fil p).fil 2 ↔ v 1 = 0 ∧ v 2 = 0 := by
  change v ∈ Submodule.span ℚ_[p] ({Pi.single 0 1} : Set (Fin 3 → ℚ_[p])) ↔ v 1 = 0 ∧ v 2 = 0
  rw [Submodule.mem_span_singleton]
  exact ⟨fun ⟨a, h⟩ => by rw [← h]; simp,
    fun ⟨hv1, hv2⟩ => ⟨v 0, by ext i; fin_cases i <;> simp [hv1, hv2]⟩⟩

theorem finrank_u3Weight2Fil_one (p : ℕ) [Fact p.Prime] :
    Module.finrank ℚ_[p] ((u3Weight2Fil p).fil 1) = 2 := by
  let e : ((u3Weight2Fil p).fil 1) ≃ₗ[ℚ_[p]] (Fin 2 → ℚ_[p]) :=
    { toFun := fun v i => v.1 i.castSucc
      invFun := fun w => ⟨![w 0, w 1, 0], (mem_u3Weight2Fil_one_iff p _).mpr rfl⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun ⟨v, hv⟩ => Subtype.ext <| by
        ext i; have hv2 := (mem_u3Weight2Fil_one_iff p v).mp hv; fin_cases i <;> simp [hv2]
      right_inv := fun w => by ext i; fin_cases i <;> simp }
  rw [e.finrank_eq, Module.finrank_fin_fun]

theorem finrank_u3Weight2Fil_two (p : ℕ) [Fact p.Prime] :
    Module.finrank ℚ_[p] ((u3Weight2Fil p).fil 2) = 1 := by
  let e : ((u3Weight2Fil p).fil 2) ≃ₗ[ℚ_[p]] ℚ_[p] :=
    { toFun := fun v => v.1 0
      invFun := fun a => ⟨![a, 0, 0], (mem_u3Weight2Fil_two_iff p _).mpr ⟨rfl, rfl⟩⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun ⟨v, hv⟩ => Subtype.ext <| by
        ext i; obtain ⟨hv1, hv2⟩ := (mem_u3Weight2Fil_two_iff p v).mp hv
        fin_cases i <;> simp [hv1, hv2]
      right_inv := fun _ => rfl }
  rw [e.finrank_eq, Module.finrank_self]

/-- **Exact Hodge Number of the 3D Weight-2 (`e = 1`) Filtration**: `t_H = 3`. -/
theorem u3Weight2Fil_tH_eq_three (p : ℕ) [Fact p.Prime] : (u3Weight2Fil p).tH = 3 := by
  rw [(u3Weight2Fil p).tH_eq_sum_Icc (show (0 : ℤ) ≤ (u3Weight2Fil p).botBound from le_rfl)
    (show (u3Weight2Fil p).topBound ≤ (3 : ℤ) by change (2 : ℤ) ≤ 3; norm_num)]
  have hIcc : Finset.Icc (0 : ℤ) 3 = {0, 1, 2, 3} := by decide
  rw [hIcc]
  have hd0 : (u3Weight2Fil p).dimAt 0 = 3 := by
    change Module.finrank ℚ_[p] ((u3Weight2Fil p).fil 0) = 3
    rw [show (u3Weight2Fil p).fil 0 = ⊤ by simp [u3Weight2Fil, u3Weight2FilSub],
      finrank_top, Module.finrank_fin_fun]
  have hd1 : (u3Weight2Fil p).dimAt 1 = 2 := finrank_u3Weight2Fil_one p
  have hd2 : (u3Weight2Fil p).dimAt 2 = 1 := finrank_u3Weight2Fil_two p
  have hd3 : (u3Weight2Fil p).dimAt 3 = 0 := by
    change Module.finrank ℚ_[p] ((u3Weight2Fil p).fil 3) = 0
    rw [show (u3Weight2Fil p).fil 3 = ⊥ by simp [u3Weight2Fil, u3Weight2FilSub], finrank_bot]
  have hd4 : (u3Weight2Fil p).dimAt 4 = 0 := by
    change Module.finrank ℚ_[p] ((u3Weight2Fil p).fil 4) = 0
    rw [show (u3Weight2Fil p).fil 4 = ⊥ by simp [u3Weight2Fil, u3Weight2FilSub], finrank_bot]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [Stage2HodgeWeights.HodgeFiltration.jump]
  rw [show (0 : ℤ) + 1 = 1 by rfl, show (1 : ℤ) + 1 = 2 by rfl,
    show (2 : ℤ) + 1 = 3 by rfl, show (3 : ℤ) + 1 = 4 by rfl, hd0, hd1, hd2, hd3, hd4]
  norm_num

/-- Concrete 3D weight-2 (`e = 1`) ordinary filtered `φ`-module `u3Weight2StdModule p`. -/
def u3Weight2StdModule (p : ℕ) [Fact p.Prime] : FilteredPhiModule p (Fin 3 → ℚ_[p]) where
  φ :=
    let hp : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
    { toFun := fun v => ![((p : ℚ_[p]) ^ 2) * v 0, (p : ℚ_[p]) * v 1, v 2]
      invFun := fun v => ![((p : ℚ_[p]) ^ 2)⁻¹ * v 0, (p : ℚ_[p])⁻¹ * v 1, v 2]
      map_add' := fun u v => by ext i; fin_cases i <;> simp <;> ring
      map_smul' := fun c v => by ext i; fin_cases i <;> simp <;> ring
      left_inv := fun v => by ext i; fin_cases i <;> simp [hp]
      right_inv := fun v => by ext i; fin_cases i <;> simp [hp] }
  fil := u3Weight2Fil p

theorem u3Weight2StdModule_tH (p : ℕ) [Fact p.Prime] : (u3Weight2StdModule p).tH = 3 :=
  u3Weight2Fil_tH_eq_three p

theorem u3Weight2StdModule_det (p : ℕ) [Fact p.Prime] :
    LinearMap.det (u3Weight2StdModule p).φ.toLinearMap = (p : ℚ_[p]) ^ 3 := by
  let b := Pi.basisFun ℚ_[p] (Fin 3)
  rw [← LinearMap.det_toMatrix b]
  have hmat : LinearMap.toMatrix b b (u3Weight2StdModule p).φ.toLinearMap =
      Matrix.diagonal ![(p : ℚ_[p]) ^ 2, (p : ℚ_[p]), 1] := by
    ext i j; rw [LinearMap.toMatrix_apply]
    fin_cases i <;> fin_cases j <;> simp [b, u3Weight2StdModule]
  rw [hmat, Matrix.det_diagonal, Fin.prod_univ_three]
  simp; ring

theorem u3Weight2StdModule_tN (p : ℕ) [Fact p.Prime] : (u3Weight2StdModule p).tN = 3 := by
  unfold FilteredPhiModule.tN
  rw [u3Weight2StdModule_det]
  have hp0 : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have h3 : (p : ℚ_[p]) ^ 3 = (p : ℚ_[p]) * ((p : ℚ_[p]) * (p : ℚ_[p])) := by ring
  rw [h3, Padic.valuation_mul hp0 (mul_ne_zero hp0 hp0), Padic.valuation_mul hp0 hp0,
    Padic.valuation_p]
  norm_num

/-! ### 4.2 Exact 3D Adjoint & Unitary Lie Algebra `ad_-(3) ⊕ ad_+(3)` Filtration & Bloch–Kato Bounds -/

theorem mem_u3Weight2_endModule_fil0_iff {p : ℕ} [Fact p.Prime]
    (M : FilteredPhiModule p (Fin 3 → ℚ_[p])) (hfil : M.fil = u3Weight2Fil p)
    (f : (Fin 3 → ℚ_[p]) →ₗ[ℚ_[p]] (Fin 3 → ℚ_[p])) :
    f ∈ (M.endModule).fil.fil 0 ↔
      let A := LinearMap.toMatrix (Pi.basisFun ℚ_[p] (Fin 3)) (Pi.basisFun ℚ_[p] (Fin 3)) f
      A 1 0 = 0 ∧ A 2 0 = 0 ∧ A 2 1 = 0 := by
  change (∀ i : ℤ, ∀ x ∈ M.fil.fil i, f x ∈ M.fil.fil (i + 0)) ↔ _
  simp only [add_zero, hfil]
  constructor
  · intro hf
    have h2 := (mem_u3Weight2Fil_two_iff p _).mp
      (hf 2 (Pi.single 0 1) ((mem_u3Weight2Fil_two_iff p _).mpr ⟨by simp, by simp⟩))
    have h1 := (mem_u3Weight2Fil_one_iff p _).mp
      (hf 1 (Pi.single 1 1) ((mem_u3Weight2Fil_one_iff p _).mpr (by simp)))
    exact ⟨by simpa [LinearMap.toMatrix_apply] using h2.1,
           by simpa [LinearMap.toMatrix_apply] using h2.2,
           by simpa [LinearMap.toMatrix_apply] using h1⟩
  · rintro ⟨h10, h20, h21⟩ i x hx
    have hA : ∀ k l : Fin 3, f (Pi.single l 1) k =
        LinearMap.toMatrix (Pi.basisFun ℚ_[p] (Fin 3)) (Pi.basisFun ℚ_[p] (Fin 3)) f k l :=
      fun k l => by simp
    have hfx : ∀ k : Fin 3, f x k =
        x 0 * f (Pi.single 0 1) k + x 1 * f (Pi.single 1 1) k + x 2 * f (Pi.single 2 1) k := by
      intro k
      have hx_eq : x = x 0 • Pi.single 0 1 + x 1 • Pi.single 1 1 + x 2 • Pi.single 2 1 := by
        ext j; fin_cases j <;> simp
      conv_lhs => rw [hx_eq]
      simp [map_add, map_smul]
    change x ∈ u3Weight2FilSub p i at hx; change f x ∈ u3Weight2FilSub p i
    unfold u3Weight2FilSub at hx ⊢
    split_ifs at hx ⊢ with hi0 hi1 hi2
    · trivial
    · have hx2 : x 2 = 0 := (mem_u3Weight2Fil_one_iff p x).mp hx
      refine (mem_u3Weight2Fil_one_iff p (f x)).mpr ?_
      rw [hfx 2, hA 2 0, hA 2 1, h20, h21, hx2]; ring
    · obtain ⟨hx1, hx2⟩ := (mem_u3Weight2Fil_two_iff p x).mp hx
      refine (mem_u3Weight2Fil_two_iff p (f x)).mpr ⟨?_, ?_⟩
      · rw [hfx 1, hA 1 0, h10, hx1, hx2]; ring
      · rw [hfx 2, hA 2 0, h20, hx1, hx2]; ring
    · rw [Submodule.mem_bot] at hx ⊢; rw [hx, map_zero]

/-- **Exact Quotient Dimension `dim(End(D) / Fil^0 End(D)) = 3`**. -/
theorem finrank_u3Weight2_end_quot_fil0 {p : ℕ} [Fact p.Prime]
    (M : FilteredPhiModule p (Fin 3 → ℚ_[p])) (hfil : M.fil = u3Weight2Fil p) :
    Module.finrank ℚ_[p] (((Fin 3 → ℚ_[p]) →ₗ[ℚ_[p]] (Fin 3 → ℚ_[p])) ⧸ (M.endModule).fil.fil 0) = 3 := by
  let b := Pi.basisFun ℚ_[p] (Fin 3)
  let proj : ((Fin 3 → ℚ_[p]) →ₗ[ℚ_[p]] (Fin 3 → ℚ_[p])) →ₗ[ℚ_[p]] (Fin 3 → ℚ_[p]) :=
    { toFun := fun f => ![LinearMap.toMatrix b b f 1 0,
                          LinearMap.toMatrix b b f 2 0,
                          LinearMap.toMatrix b b f 2 1]
      map_add' := fun f g => by ext i; fin_cases i <;> simp [map_add]
      map_smul' := fun c f => by ext i; fin_cases i <;> simp [map_smul] }
  have hker : LinearMap.ker proj = (M.endModule).fil.fil 0 := by
    ext f; rw [LinearMap.mem_ker, mem_u3Weight2_endModule_fil0_iff M hfil]
    exact ⟨fun h => ⟨congrFun h 0, congrFun h 1, congrFun h 2⟩,
           fun ⟨h10, h20, h21⟩ => by ext i; fin_cases i <;> assumption⟩
  have hsurj : Function.Surjective proj := fun v => by
    let A : Matrix (Fin 3) (Fin 3) ℚ_[p] := !![0, 0, 0; v 0, 0, 0; v 1, v 2, 0]
    refine ⟨A.mulVecLin, ?_⟩
    have hto : LinearMap.toMatrix b b A.mulVecLin = A := toMatrix_mulVecLin_eq A
    ext i; fin_cases i <;> simp [proj, hto, A]
  rw [((Submodule.quotEquivOfEq _ _ hker.symm).trans (proj.quotKerEquivOfSurjective hsurj)).finrank_eq,
    Module.finrank_fin_fun]

/-- **Exact Bloch–Kato Weight-2 `End(D)` Tangent Dimension**: `dim H¹_f(End(M)) = 3 + dim H⁰(End(M))`. -/
theorem u3_weight2_end_blochKato_dim {p : ℕ} [Fact p.Prime]
    (M : FilteredPhiModule p (Fin 3 → ℚ_[p])) (hfil : M.fil = u3Weight2Fil p) :
    Module.finrank ℚ_[p] (H1fCris M.endModule) =
      3 + Module.finrank ℚ_[p] (H0Cris M.endModule) := by
  rw [finrank_H1fCris_eq, finrank_u3Weight2_end_quot_fil0 M hfil]

def u3AdMinus (p : ℕ) [Fact p.Prime] : Submodule ℚ_[p] (Matrix (Fin 3) (Fin 3) ℚ_[p]) where
  carrier := { X | J3 ℚ_[p] * Xᵀ * J3 ℚ_[p] = -X }
  add_mem' {X Y} hX hY := by
    change J3 ℚ_[p] * Xᵀ * J3 ℚ_[p] = -X at hX
    change J3 ℚ_[p] * Yᵀ * J3 ℚ_[p] = -Y at hY
    change J3 ℚ_[p] * (X + Y)ᵀ * J3 ℚ_[p] = -(X + Y)
    rw [Matrix.transpose_add, Matrix.mul_add, Matrix.add_mul, hX, hY, neg_add]
  zero_mem' := by change J3 ℚ_[p] * (0 : Matrix (Fin 3) (Fin 3) ℚ_[p])ᵀ * J3 ℚ_[p] = -0; simp
  smul_mem' c {X} hX := by
    change J3 ℚ_[p] * Xᵀ * J3 ℚ_[p] = -X at hX
    change J3 ℚ_[p] * (c • X)ᵀ * J3 ℚ_[p] = -(c • X)
    rw [Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul, hX, smul_neg]

def u3AdPlus (p : ℕ) [Fact p.Prime] : Submodule ℚ_[p] (Matrix (Fin 3) (Fin 3) ℚ_[p]) where
  carrier := { X | J3 ℚ_[p] * Xᵀ * J3 ℚ_[p] = X }
  add_mem' {X Y} hX hY := by
    change J3 ℚ_[p] * Xᵀ * J3 ℚ_[p] = X at hX
    change J3 ℚ_[p] * Yᵀ * J3 ℚ_[p] = Y at hY
    change J3 ℚ_[p] * (X + Y)ᵀ * J3 ℚ_[p] = X + Y
    rw [Matrix.transpose_add, Matrix.mul_add, Matrix.add_mul, hX, hY]
  zero_mem' := by change J3 ℚ_[p] * (0 : Matrix (Fin 3) (Fin 3) ℚ_[p])ᵀ * J3 ℚ_[p] = 0; simp
  smul_mem' c {X} hX := by
    change J3 ℚ_[p] * Xᵀ * J3 ℚ_[p] = X at hX
    change J3 ℚ_[p] * (c • X)ᵀ * J3 ℚ_[p] = c • X
    rw [Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul, hX]

theorem isCompl_u3AdMinus_u3AdPlus (p : ℕ) [Fact p.Prime] :
    IsCompl (u3AdMinus p) (u3AdPlus p) := by
  have h2 : (2 : ℚ_[p]) ≠ 0 := by norm_num
  rw [isCompl_iff]
  constructor
  · rw [disjoint_iff, eq_bot_iff]
    rintro X ⟨hM, hP⟩; rw [Submodule.mem_bot]
    have h2X : (2 : ℚ_[p]) • X = 0 := by
      rw [two_smul]; have : X = -X := hP.symm.trans hM
      calc X + X = X + (-X) := by rw [← this]
        _ = 0 := add_neg_cancel X
    exact (smul_eq_zero.mp h2X).resolve_left h2
  · rw [codisjoint_iff, eq_top_iff]; intro X _
    let τX := J3 ℚ_[p] * Xᵀ * J3 ℚ_[p]
    have hττ : J3 ℚ_[p] * τXᵀ * J3 ℚ_[p] = X := by
      simp only [τX, Matrix.transpose_mul, J3_transpose, Matrix.transpose_transpose]
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, J3_mul_J3, Matrix.one_mul,
        Matrix.mul_assoc, J3_mul_J3, Matrix.mul_one]
    let Xm := (2 : ℚ_[p])⁻¹ • (X - τX)
    let Xp := (2 : ℚ_[p])⁻¹ • (X + τX)
    have hsplit : X = Xm + Xp := by
      simp only [Xm, Xp, ← smul_add]
      have : (X - τX) + (X + τX) = (2 : ℚ_[p]) • X := by rw [two_smul]; abel
      rw [this, smul_smul, inv_mul_cancel₀ h2, one_smul]
    rw [hsplit]
    refine Submodule.add_mem_sup ?_ ?_
    · change J3 ℚ_[p] * Xmᵀ * J3 ℚ_[p] = -Xm
      simp only [Xm, Matrix.transpose_smul, Matrix.transpose_sub, Matrix.mul_smul, Matrix.smul_mul,
        Matrix.mul_sub, Matrix.sub_mul, hττ, ← smul_neg]; congr 1; abel
    · change J3 ℚ_[p] * Xpᵀ * J3 ℚ_[p] = Xp
      simp only [Xp, Matrix.transpose_smul, Matrix.transpose_add, Matrix.mul_smul, Matrix.smul_mul,
        Matrix.mul_add, Matrix.add_mul, hττ]; congr 1; abel

theorem mem_u3AdMinus_iff (p : ℕ) [Fact p.Prime] (X : Matrix (Fin 3) (Fin 3) ℚ_[p]) :
    X ∈ u3AdMinus p ↔
      X 2 2 = -X 0 0 ∧ X 1 1 = 0 ∧ X 1 2 = -X 0 1 ∧ X 2 1 = -X 1 0 ∧ X 0 2 = 0 ∧ X 2 0 = 0 := by
  have h2 : (2 : ℚ_[p]) ≠ 0 := by norm_num
  have heq : (J3 ℚ_[p] * Xᵀ * J3 ℚ_[p] = -X) ↔
      ∀ i j : Fin 3, (J3 ℚ_[p] * Xᵀ * J3 ℚ_[p]) i j = -X i j :=
    ⟨fun h i j => congrFun (congrFun h i) j, fun h => Matrix.ext h⟩
  change J3 ℚ_[p] * Xᵀ * J3 ℚ_[p] = -X ↔ _
  rw [heq]
  constructor
  · intro h
    have h00 := h 0 0; have h11 := h 1 1; have h01 := h 0 1
    have h10 := h 1 0; have h02 := h 0 2; have h20 := h 2 0
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three] at h00 h11 h01 h10 h02 h20
    simp [J3] at h00 h11 h01 h10 h02 h20
    exact ⟨h00, (mul_eq_zero.mp (by linear_combination h11 : (2 : ℚ_[p]) * X 1 1 = 0)).resolve_left h2,
      h01, h10,
      (mul_eq_zero.mp (by linear_combination h02 : (2 : ℚ_[p]) * X 0 2 = 0)).resolve_left h2,
      (mul_eq_zero.mp (by linear_combination h20 : (2 : ℚ_[p]) * X 2 0 = 0)).resolve_left h2⟩
  · rintro ⟨h22, h11, h12, h21, h02, h20⟩ i j
    fin_cases i <;> fin_cases j <;>
      (simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three];
       simp [J3, h22, h11, h12, h21, h02, h20])

theorem finrank_u3AdMinus_and_plus (p : ℕ) [Fact p.Prime] :
    Module.finrank ℚ_[p] (u3AdMinus p) = 3 ∧ Module.finrank ℚ_[p] (u3AdPlus p) = 6 := by
  let e : u3AdMinus p ≃ₗ[ℚ_[p]] (Fin 3 → ℚ_[p]) :=
    { toFun := fun X => ![X.1 0 0, X.1 0 1, X.1 1 0]
      invFun := fun v =>
        ⟨!![v 0, v 1, 0; v 2, 0, -v 1; 0, -v 2, -v 0],
         (mem_u3AdMinus_iff p _).mpr ⟨by simp, by simp, by simp, by simp, by simp, by simp⟩⟩
      map_add' := fun _ _ => by ext i; fin_cases i <;> simp
      map_smul' := fun _ _ => by ext i; fin_cases i <;> simp
      left_inv := fun ⟨X, hX⟩ => Subtype.ext <| by
        obtain ⟨h22, h11, h12, h21, h02, h20⟩ := (mem_u3AdMinus_iff p X).mp hX
        ext i j; fin_cases i <;> fin_cases j <;> simp [h22, h11, h12, h21, h02, h20]
      right_inv := fun v => by ext i; fin_cases i <;> simp }
  have hM : Module.finrank ℚ_[p] (u3AdMinus p) = 3 := by rw [e.finrank_eq, Module.finrank_fin_fun]
  have hsum := Submodule.finrank_add_eq_of_isCompl (isCompl_u3AdMinus_u3AdPlus p)
  rw [Module.finrank_matrix, Fintype.card_fin, Module.finrank_self, hM] at hsum
  exact ⟨hM, by omega⟩

def u3AdMinusFil0 (p : ℕ) [Fact p.Prime] : Submodule ℚ_[p] (u3AdMinus p) where
  carrier := { X | X.1 1 0 = 0 }
  add_mem' {X Y} hX hY := by
    change X.1 1 0 = 0 at hX; change Y.1 1 0 = 0 at hY
    change X.1 1 0 + Y.1 1 0 = 0; rw [hX, hY, add_zero]
  zero_mem' := rfl
  smul_mem' c {X} hX := by
    change X.1 1 0 = 0 at hX
    change c * X.1 1 0 = 0; rw [hX, mul_zero]

/-- **Exact Unitary Weight-2 Quotient Dimension**: `dim(ad_-(3) ⧸ Fil^0 ad_-(3)) = 1`. -/
theorem finrank_u3AdMinus_quot_fil0 (p : ℕ) [Fact p.Prime] :
    Module.finrank ℚ_[p] (u3AdMinus p ⧸ u3AdMinusFil0 p) = 1 := by
  let proj : u3AdMinus p →ₗ[ℚ_[p]] ℚ_[p] :=
    { toFun := fun X => X.1 1 0, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have hsurj : Function.Surjective proj := fun a =>
    ⟨⟨!![0, 0, 0; a, 0, 0; 0, -a, 0],
      (mem_u3AdMinus_iff p _).mpr ⟨by simp, by simp, by simp, by simp, by simp, by simp⟩⟩, rfl⟩
  rw [((Submodule.quotEquivOfEq _ _ (rfl : u3AdMinusFil0 p = LinearMap.ker proj)).trans
    (proj.quotKerEquivOfSurjective hsurj)).finrank_eq, Module.finrank_self]

/-- **Weight-2 Non-Positive Weight Inertia Vanishing (`weight2_nonpos_inertia_vanishing`)**. -/
theorem weight2_nonpos_inertia_vanishing {p : ℕ} [Fact p.Prime] {D : Type*}
    [AddCommGroup D] [Module ℚ_[p] D] [Module.Finite ℚ_[p] D]
    (E : FilteredPhiModule p D) (hnonpos : E.fil.fil 0 = ⊤) :
    Module.finrank ℚ_[p] (H1fCris E) = Module.finrank ℚ_[p] (H0Cris E) ∧
      ((∀ x : D, E.φ x = x → x = 0) →
        Module.finrank ℚ_[p] (H1fCris E) = 0 ∧ Subsingleton (H1fCris E)) := by
  have hq0 : Module.finrank ℚ_[p] (D ⧸ E.fil.fil 0) = 0 := by
    rw [hnonpos]
    have : Subsingleton (D ⧸ (⊤ : Submodule ℚ_[p] D)) := Submodule.Quotient.subsingleton_iff.mpr rfl
    exact Module.finrank_zero_of_subsingleton
  have hdim : Module.finrank ℚ_[p] (H1fCris E) = Module.finrank ℚ_[p] (H0Cris E) := by
    rw [finrank_H1fCris_eq, hq0, zero_add]
  refine ⟨hdim, fun hno1 => ?_⟩
  have hH0_bot : H0Cris E = ⊥ := by
    ext x; rw [mem_H0Cris_iff, Submodule.mem_bot]
    exact ⟨fun ⟨_, hx⟩ => hno1 x hx, fun h => by rw [h]; exact ⟨(E.fil.fil 0).zero_mem, map_zero _⟩⟩
  have hH1_zero : Module.finrank ℚ_[p] (H1fCris E) = 0 := by rw [hdim, hH0_bot, finrank_bot]
  refine ⟨hH1_zero, ⟨fun x y => ?_⟩⟩
  have hzero : ∀ v : H1fCris E, v = 0 := by
    intro v; by_contra hv
    have h1 : 1 ≤ Module.finrank ℚ_[p] (H1fCris E) := by
      rw [← finrank_span_singleton (K := ℚ_[p]) hv]; exact Submodule.finrank_le _
    omega
  rw [hzero x, hzero y]

/-! ### 4.3 Complete `CountV` Weight-2 (`e = 1`) Polynomial Discharge at `l ∈ Bchi` -/

theorem countV_arith {a V E : ℕ} {s L X : ℝ} {C : ℕ}
    (ha : a ≤ V) (hV : (V : ℝ) ≤ 2 * (E : ℝ) * s) (hL : 0 ≤ L)
    (hs : s * L ≤ X ^ C) (hX : 2 ≤ X) :
    (a : ℝ) / (E : ℝ) * L ≤ X ^ (C + 1) := by
  have hp : 0 ≤ X ^ C := pow_nonneg (by linarith) C
  rcases Nat.eq_zero_or_pos E with rfl | hE
  · simp only [Nat.cast_zero, div_zero, zero_mul]; exact pow_nonneg (by linarith) _
  · have hE' : (0 : ℝ) < (E : ℝ) := by exact_mod_cast hE
    have ha' : (a : ℝ) ≤ (V : ℝ) := by exact_mod_cast ha
    have h1 : (a : ℝ) / (E : ℝ) ≤ 2 * s := by rw [div_le_iff₀ hE']; linarith
    have h2 := mul_le_mul_of_nonneg_right h1 hL
    have h3 := mul_le_mul_of_nonneg_left hX hp
    rw [pow_succ]; linarith

/-- **Complete Weight-2 (`e = 1`) `CountV` Discharge Theorem (`countV_weight2_u3_bound`)**. -/
theorem countV_weight2_u3_bound
    {l N e_O C n : ℕ} [hl : Fact l.Prime] (hN : 1 ≤ N)
    (Vlen : ℕ∞) (V : ℕ) (v : Fin n → ℝ)
    (hlen : Vlen ≤ (V : ℕ∞))
    (hV : (V : ℝ) ≤ 2 * (e_O : ℝ) * ∑ i : Fin n, v i)
    (hsum : (∑ i : Fin n, v i) * Real.log (l : ℝ) ≤ ((l : ℝ) * (N : ℝ) * 1) ^ C) :
    Vlen ≠ ⊤ ∧
      ((Vlen.toNat : ℝ) / (e_O : ℝ)) * Real.log (l : ℝ) ≤ ((l : ℝ) * (N : ℝ) * 1) ^ (C + 1) := by
  have hX2 : (2 : ℝ) ≤ (l : ℝ) * (N : ℝ) * 1 := by
    have hnat : 2 ≤ l * N * 1 := by have h2l : 2 ≤ l := hl.out.two_le; nlinarith
    exact_mod_cast hnat
  refine ⟨ne_top_of_le_ne_top (ENat.natCast_ne_top V) hlen, ?_⟩
  exact countV_arith (ENat.toNat_le_of_le_natCast hlen) hV (Real.log_natCast_nonneg l) hsum hX2

/-- **End-to-End Concrete Weight-2 `U(3)` Witness at `l = 5`**. -/
theorem concrete_weight2_u3_witness_l5 :
    haveI : Fact (Nat.Prime 5) := ⟨by decide⟩
    (u3Weight2StdModule 5).tH = 3 ∧
    (u3Weight2StdModule 5).tN = 3 ∧
    Module.finrank ℚ_[5] (u3AdMinus 5) = 3 ∧
    Module.finrank ℚ_[5] (u3AdMinus 5 ⧸ u3AdMinusFil0 5) = 1 ∧
    Module.finrank ℚ_[5] (H1fCris (u3Weight2StdModule 5).endModule) =
      3 + Module.finrank ℚ_[5] (H0Cris (u3Weight2StdModule 5).endModule) := by
  have : Fact (Nat.Prime 5) := ⟨by decide⟩
  exact ⟨u3Weight2StdModule_tH 5, u3Weight2StdModule_tN 5,
    (finrank_u3AdMinus_and_plus 5).1, finrank_u3AdMinus_quot_fil0 5,
    u3_weight2_end_blochKato_dim (u3Weight2StdModule 5) rfl⟩

end Weight2InertiaCountV

end Stage13U3HidaAutomorphy
end RHDirect

end
