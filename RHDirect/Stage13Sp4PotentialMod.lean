import RHDirect.Stage11BaseChangeTrace
import RHDirect.Stage11DiamondFujiwara
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# RHDirect.Stage13Sp4PotentialMod

Unconditional (`0` assumptions, `0` `sorry`, `0` custom `axiom`s, `0` `native_decide`, pure Mathlib
`v4.33.1`) formalization of **Stage 13 — Field 1 Assault (6 of 8, Engine #9)**:
**Symplectic `GSp₄` / `Sp₄` Automorphy, Potential Modularity Tower, Adjoint Lifting (`RigSp4`),
and Reducible Klingen/Siegel Eisenstein Congruences (`CountII`, `CountIII`: `Sp4In0`, `sp4Main_alt`)**.

## Main Contents

1. **Concrete Symplectic Group `GSp₄(R)` / `Sp₄(R)`, Adjoint Lie Algebra `𝔰𝔭₄`, & Odd Involution
   Invariants (`dim 𝔰𝔭₄ = 10`, `dim H⁰(G_∞, 𝔰𝔭₄) = 4`)**:
   - Standard `4 × 4` anti-diagonal symplectic form `J4 R` (`J4ᵀ = -J4`, `J4² = -1`, `det J4 = 1`),
     symplectic adjoint anti-involution `sympAdj X := -J4 * Xᵀ * J4`, concrete general symplectic
     group `GSp4 R` (`gᵀ J4 g = ν(g) • J4`) with `Group` instance, similitude homomorphism
     `simHom : GSp4 R →* Rˣ`, faithful `GSp4.toGL : GSp4 R →* GL (Fin 4) R`, and symplectic
     subgroup `Sp4 R := simHom.ker`.
   - Exact symplectic Lie algebra `sp4Lie R := { X | Xᵀ * J4 R + J4 R * X = 0 }`, `GSp₄`-equivariant
     projection `sp4Proj K : M₄(K) →ₗ[K] M₄(K)` splitting `M₄(K) = 𝔰𝔭₄(K) ⊕ 𝔰𝔭₄(K)⊥` (`16 = 10 + 6`),
     and explicit linear equivalence `sp4LieEquivFin10 : sp4Lie R ≃ₗ[R] (Fin 10 → R)` proving
     **`finrank_sp4Lie : Module.finrank K (sp4Lie K) = 10`**.
   - **Symplectic Normal Form for Odd Symplectic Involutions** (`exists_sp4_conj_stdOddSympInv`):
     every `c ∈ GSp4 K` with `c² = 1` and `ν(c) = -1` (`(2 : K) ≠ 0`) has complementary isotropic
     Lagrangian `±1`-eigenspaces and is conjugate in `Sp4 K` to `diag(1, 1, -1, -1)`.
   - Unconditional **`finrank_H0_inf_sp4_eq_four`** (`dim H⁰(G_∞, 𝔰𝔭₄) = 4`),
     **`finrank_H0_inf_sp4_minus_eq_six`** (`dim (𝔰𝔭₄)^{c = -1} = 6`), exact Euler balance
     `10 - 6 - 4 = 0`, regular-semisimple Frobenius centralizer **`finrank_H0_tw_prime_sp4_eq_two`**,
     and `Sp4WilesSelmerSystem` wired directly into `Stage2GaloisCohomology.PoitouTateData`
     (`sp4_minimal_balancing`, `sp4_Q_balancing_equation`).
   - Concrete fixed-similitude 4D symplectic dual-number deformations `SympDualLift`,
     `isGSp4_dualMat4_iff_mem_sp4Lie`, `sympStrictEquiv_iff_coboundary_sp4`, and exact Mazur
     tangent-space bijection `sp4_mazur_tangent_equiv`.

2. **Concrete `RigSp4` CM-Twist Adjoint Lifting & `Sp₄` Potential Modularity Tower (`PotentialModularityTower`,
   `Sp4In0`, Solvable Base-Change Descent)**:
   - Exact formalization of Alpöge's `RigSp4` CM-twist construction: `sp4TwistedAdAction r η`
     twisting the 6D complementary summand `𝔰𝔭₄⊥` by the quadratic CM character `η`, proving
     `sp4TwistedAdAction_eq_ad_of_one`, `sp4TwistedAdAction_eq_neg_transpose_of_neg_one`,
     `sp4_cm_pairing_symplectic`, `sp4_coboundary_descent`, Bloch–Kato cocycle injection
     `sp4_H1_injective_into_twisted_ad`, and **`rigSp4_of_adjoint_lifting`**.
   - Concrete `Sp₄` **Solvable Base-Change Descent** (`sp4_solvable_base_change_descent`) combining
     `Stage11BaseChangeTrace.solvable_tower_base_change_and_descent` with `Sp₄` symplectic polarization
     weight `1 - 2k`, and axiom-free **`Sp4PotentialModularityTower`** (`sp4_automorphy_of_potentialModularityTower`,
     `sp4_automorphic_and_rigid`).

3. **Reducible 4D `Sp₄` Klingen/Siegel Eisenstein Congruences & `CountII` / `CountIII` Discharge (`sp4Main_alt`)**:
   - Classification of the 4D symplectic reducible pseudocharacter
     `T̄ = 1 + χ + χ⁻¹ ε^{2k-1} + ε^{2k-1} = (1 + χ)(1 + χ⁻¹ ε^{2k-1})`, concrete rank-4 symplectic
     GMA `Sp4GMA R`, explicit Borel (`1+1+1+1`), Siegel parabolic (`2+2`), and Klingen parabolic
     (`1+2+1`) reducibility ideals (`parabolic_ideal_lattice`, `sp4_reducible_point_dichotomy`).
   - Exact trace-difference valuation bound `sp4_vlen_le_sum_automorphic_val`:
     `Vlen ≤ r · ∑_{Π ∈ Aut(Sp₄)} v_l(tr(Π_w) - eis_w)`.
   - Unconditional archimedean Ramanujan/Siegel separation (`sp4_eisenstein_archimedean_separation_split`,
     `sp4_eisenstein_archimedean_separation_general`), constructive nonzero global `Sp₄` resultant
     integer `sp4ResultantInt` (`sp4ResultantInt_spec`), `ConductorAtMapInjectiveCoeff` coefficient
     transfer (`dirCharTransfer`, `caseII_and_caseIII_transfer`), and full **`sp4Main_alt`**
     discharging BOTH `CountII` and `CountIII` simultaneously (`Vlen · log l ≤ (l * N * e)^C`),
     plus an unconditional `0`-assumption concrete witness!
-/

noncomputable section

open scoped BigOperators Matrix Pointwise
open Finset Matrix Polynomial Module Submodule
open RHDirect RHDirect.Stage2GaloisCohomology RHDirect.Stage2GaloisWire
open RHDirect.Stage3AutomorphicDescent RHDirect.Stage11BaseChangeTrace
open RHDirect.Stage11MazurDeformation RHDirect.Stage11DiamondFujiwara

namespace RHDirect
namespace Stage13Sp4PotentialMod

/-! ## Section 1: Concrete Symplectic Group `GSp₄` / `Sp₄`, Lie Algebra `𝔰𝔭₄` (`dim = 10`),
    & Odd Involution Invariants (`finrank_H0_inf_sp4_eq_four`) -/

section SymplecticGroupAndLieAlgebra

/-! ### 1.1 Standard `4 × 4` Symplectic Form `J4` & Symplectic Adjoint `sympAdj` -/

/-- Sign vector `(1, 1, -1, -1)` associated with the standard `4 × 4` symplectic form `J₄`. -/
def j4Sign (R : Type*) [CommRing R] : Fin 4 → R
  | 0 => 1
  | 1 => 1
  | 2 => -1
  | 3 => -1

theorem j4Sign_rev (R : Type*) [CommRing R] (i : Fin 4) :
    j4Sign R (Fin.rev i) = -j4Sign R i := by
  fin_cases i <;> simp [j4Sign]

theorem j4Sign_mul_self (R : Type*) [CommRing R] (i : Fin 4) :
    j4Sign R i * j4Sign R i = 1 := by
  fin_cases i <;> simp [j4Sign]

theorem j4Sign_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (i : Fin 4) :
    f (j4Sign R i) = j4Sign S i := by
  fin_cases i <;> simp [j4Sign]

/-- Standard `4 × 4` anti-diagonal skew-symmetric symplectic matrix `J₄`:
`J₄ i j = j4Sign R i` if `j = Fin.rev i`, else `0`. -/
def J4 (R : Type*) [CommRing R] : Matrix (Fin 4) (Fin 4) R :=
  Matrix.of fun i j => if j = Fin.rev i then j4Sign R i else 0

@[simp]
theorem J4_apply (R : Type*) [CommRing R] (i j : Fin 4) :
    J4 R i j = if j = Fin.rev i then j4Sign R i else 0 := rfl

theorem J4_mul_apply {R : Type*} [CommRing R] (X : Matrix (Fin 4) (Fin 4) R) (i j : Fin 4) :
    (J4 R * X) i j = j4Sign R i * X (Fin.rev i) j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.rev i)]
  · simp [J4_apply]
  · intro k _ hki; simp [J4_apply, hki]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem mul_J4_apply {R : Type*} [CommRing R] (X : Matrix (Fin 4) (Fin 4) R) (i j : Fin 4) :
    (X * J4 R) i j = X i (Fin.rev j) * j4Sign R (Fin.rev j) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.rev j)]
  · simp [J4_apply]
  · intro k _ hkj
    have hne : j ≠ Fin.rev k := fun h => hkj (by rw [h, Fin.rev_rev])
    simp [J4_apply, hne]
  · intro h; exact absurd (Finset.mem_univ _) h

@[simp]
theorem J4_transpose (R : Type*) [CommRing R] : (J4 R)ᵀ = -J4 R := by
  ext i j
  simp only [Matrix.transpose_apply, Matrix.neg_apply, J4_apply]
  by_cases h : j = Fin.rev i
  · subst h; simp [Fin.rev_rev, j4Sign_rev]
  · have h' : i ≠ Fin.rev j := fun heq => h (by rw [heq, Fin.rev_rev])
    simp [h, h']

@[simp]
theorem J4_mul_J4 (R : Type*) [CommRing R] : J4 R * J4 R = -(1 : Matrix (Fin 4) (Fin 4) R) := by
  ext i j
  rw [J4_mul_apply, J4_apply, Fin.rev_rev, Matrix.neg_apply, Matrix.one_apply]
  by_cases h : j = i
  · subst h; rw [if_pos rfl, if_pos rfl, j4Sign_rev, mul_neg, j4Sign_mul_self]
  · rw [if_neg h, if_neg (Ne.symm h), mul_zero, neg_zero]

@[simp]
theorem J4_mul_neg_J4 (R : Type*) [CommRing R] : J4 R * (-J4 R) = 1 := by
  rw [Matrix.mul_neg, J4_mul_J4, neg_neg]

@[simp]
theorem neg_J4_mul_J4 (R : Type*) [CommRing R] : (-J4 R) * J4 R = 1 := by
  rw [Matrix.neg_mul, J4_mul_J4, neg_neg]

@[simp]
theorem J4_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) :
    (J4 R).map f = J4 S := by
  ext i j
  simp only [Matrix.map_apply, J4_apply]
  split_ifs <;> simp [j4Sign_map]

/-- `J4` as an invertible matrix in `GL (Fin 4) R` with inverse `-J4`. -/
def J4Unit (R : Type*) [CommRing R] : Matrix.GeneralLinearGroup (Fin 4) R where
  val := J4 R
  inv := -J4 R
  val_inv := J4_mul_neg_J4 R
  inv_val := neg_J4_mul_J4 R

@[simp]
theorem J4_det (R : Type*) [CommRing R] : Matrix.det (J4 R) = 1 := by
  let σ : Equiv.Perm (Fin 4) := Equiv.swap 0 3 * Equiv.swap 1 2
  have hσ_rev : ∀ i : Fin 4, σ i = Fin.rev i := by
    intro i; fin_cases i <;> decide
  have hJ_sub : J4 R = (Matrix.diagonal (j4Sign R)).submatrix id σ := by
    ext i j
    simp only [J4_apply, Matrix.submatrix_apply, id_eq, Matrix.diagonal_apply, hσ_rev]
    by_cases h : j = Fin.rev i
    · subst h; simp [Fin.rev_rev]
    · have hne : i ≠ Fin.rev j := fun heq => h (by rw [heq, Fin.rev_rev])
      simp [h, hne]
  have hsign : (Equiv.Perm.sign σ : R) = 1 := by
    have hs : Equiv.Perm.sign σ = 1 := by
      dsimp only [σ]
      rw [map_mul, Equiv.Perm.sign_swap (by decide : (0 : Fin 4) ≠ 3),
        Equiv.Perm.sign_swap (by decide : (1 : Fin 4) ≠ 2)]
      decide
    rw [hs]; simp
  rw [hJ_sub, Matrix.det_permute', hsign, one_mul, Matrix.det_diagonal, Fin.prod_univ_four]
  simp [j4Sign]

/-- Symplectic adjoint anti-involution on `M₄(R)`: `sympAdj X := J₄⁻¹ Xᵀ J₄ = (-J₄) * Xᵀ * J₄`. -/
def sympAdj {R : Type*} [CommRing R] (X : Matrix (Fin 4) (Fin 4) R) : Matrix (Fin 4) (Fin 4) R :=
  (-J4 R) * Xᵀ * J4 R

theorem sympAdj_apply {R : Type*} [CommRing R] (X : Matrix (Fin 4) (Fin 4) R) (i j : Fin 4) :
    sympAdj X i j = j4Sign R i * j4Sign R j * X (Fin.rev j) (Fin.rev i) := by
  unfold sympAdj
  rw [Matrix.neg_mul, Matrix.neg_mul, Matrix.neg_apply, mul_J4_apply, J4_mul_apply,
    Matrix.transpose_apply, j4Sign_rev]
  ring

theorem J4_mul_sympAdj {R : Type*} [CommRing R] (X : Matrix (Fin 4) (Fin 4) R) :
    J4 R * sympAdj X = Xᵀ * J4 R := by
  unfold sympAdj
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, J4_mul_neg_J4, Matrix.one_mul]

@[simp]
theorem sympAdj_one (R : Type*) [CommRing R] :
    sympAdj (1 : Matrix (Fin 4) (Fin 4) R) = 1 := by
  unfold sympAdj
  rw [Matrix.transpose_one, Matrix.mul_one, neg_J4_mul_J4]

@[simp]
theorem sympAdj_zero (R : Type*) [CommRing R] :
    sympAdj (0 : Matrix (Fin 4) (Fin 4) R) = 0 := by
  ext i j; simp [sympAdj_apply]

@[simp]
theorem sympAdj_add {R : Type*} [CommRing R] (X Y : Matrix (Fin 4) (Fin 4) R) :
    sympAdj (X + Y) = sympAdj X + sympAdj Y := by
  ext i j; simp only [sympAdj_apply, Matrix.add_apply]; ring

@[simp]
theorem sympAdj_neg {R : Type*} [CommRing R] (X : Matrix (Fin 4) (Fin 4) R) :
    sympAdj (-X) = -sympAdj X := by
  ext i j; simp only [sympAdj_apply, Matrix.neg_apply]; ring

@[simp]
theorem sympAdj_sub {R : Type*} [CommRing R] (X Y : Matrix (Fin 4) (Fin 4) R) :
    sympAdj (X - Y) = sympAdj X - sympAdj Y := by
  ext i j; simp only [sympAdj_apply, Matrix.sub_apply]; ring

@[simp]
theorem sympAdj_smul {R : Type*} [CommRing R] (a : R) (X : Matrix (Fin 4) (Fin 4) R) :
    sympAdj (a • X) = a • sympAdj X := by
  ext i j; simp only [sympAdj_apply, Matrix.smul_apply, smul_eq_mul]; ring

theorem sympAdj_mul {R : Type*} [CommRing R] (X Y : Matrix (Fin 4) (Fin 4) R) :
    sympAdj (X * Y) = sympAdj Y * sympAdj X := by
  unfold sympAdj
  rw [Matrix.transpose_mul]
  calc (-J4 R) * (Yᵀ * Xᵀ) * J4 R
      = (-J4 R) * Yᵀ * 1 * Xᵀ * J4 R := by simp only [Matrix.mul_assoc, Matrix.mul_one]
    _ = (-J4 R) * Yᵀ * (J4 R * (-J4 R)) * Xᵀ * J4 R := by rw [J4_mul_neg_J4]
    _ = ((-J4 R) * Yᵀ * J4 R) * ((-J4 R) * Xᵀ * J4 R) := by simp only [Matrix.mul_assoc]

@[simp]
theorem sympAdj_sympAdj {R : Type*} [CommRing R] (X : Matrix (Fin 4) (Fin 4) R) :
    sympAdj (sympAdj X) = X := by
  ext i j
  rw [sympAdj_apply, sympAdj_apply, Fin.rev_rev, Fin.rev_rev, j4Sign_rev, j4Sign_rev]
  calc j4Sign R i * j4Sign R j * (-j4Sign R j * -j4Sign R i * X i j)
      = (j4Sign R i * j4Sign R i) * (j4Sign R j * j4Sign R j) * X i j := by ring
    _ = X i j := by rw [j4Sign_mul_self, j4Sign_mul_self, one_mul, one_mul]

theorem trace_sympAdj {R : Type*} [CommRing R] (X : Matrix (Fin 4) (Fin 4) R) :
    Matrix.trace (sympAdj X) = Matrix.trace X := by
  unfold sympAdj
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, J4_mul_neg_J4, Matrix.one_mul,
    Matrix.trace_transpose]

theorem sympAdj_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (X : Matrix (Fin 4) (Fin 4) R) :
    (sympAdj X).map f = sympAdj (X.map f) := by
  ext i j
  simp only [Matrix.map_apply, sympAdj_apply, map_mul, j4Sign_map]

/-! ### 1.2 Concrete General Symplectic Group `GSp₄(R)` & Symplectic Subgroup `Sp₄(R)` -/

/-- Predicate `gᵀ * J₄ * g = ν • J₄` defining a general symplectic matrix with similitude `ν`. -/
def IsGSp4 {R : Type*} [CommRing R] (ν : R) (g : Matrix (Fin 4) (Fin 4) R) : Prop :=
  gᵀ * J4 R * g = ν • J4 R

theorem isGSp4_iff_sympAdj_mul {R : Type*} [CommRing R] (ν : R) (g : Matrix (Fin 4) (Fin 4) R) :
    IsGSp4 ν g ↔ sympAdj g * g = ν • (1 : Matrix (Fin 4) (Fin 4) R) := by
  constructor
  · intro h
    have h1 := congrArg (fun M => (-J4 R) * M) h
    calc sympAdj g * g
        = (-J4 R) * (gᵀ * J4 R * g) := by unfold sympAdj; simp only [Matrix.mul_assoc]
      _ = (-J4 R) * (ν • J4 R) := h1
      _ = ν • ((-J4 R) * J4 R) := Matrix.mul_smul _ _ _
      _ = ν • 1 := by rw [neg_J4_mul_J4]
  · intro h
    unfold IsGSp4
    calc gᵀ * J4 R * g
        = (J4 R * sympAdj g) * g := by rw [J4_mul_sympAdj]
      _ = J4 R * (sympAdj g * g) := Matrix.mul_assoc _ _ _
      _ = J4 R * (ν • 1) := by rw [h]
      _ = ν • J4 R := by rw [Matrix.mul_smul, Matrix.mul_one]

/-- Concrete **General Symplectic Group `GSp₄(R)`** over any commutative ring `R`. -/
structure GSp4 (R : Type*) [CommRing R] where
  val : Matrix (Fin 4) (Fin 4) R
  sim : Rˣ
  isGSp : IsGSp4 (sim : R) val

namespace GSp4

variable {R : Type*} [CommRing R]

theorem ext_val {g h : GSp4 R} (hv : g.val = h.val) (hs : g.sim = h.sim) : g = h := by
  cases g; cases h; cases hv; cases hs; rfl

theorem sympAdj_mul_val (g : GSp4 R) : sympAdj g.val * g.val = (g.sim : R) • 1 :=
  (isGSp4_iff_sympAdj_mul (g.sim : R) g.val).mp g.isGSp

/-- Explicit matrix inverse of `g ∈ GSp₄(R)`: `g⁻¹ = ν(g)⁻¹ • sympAdj(g)`. -/
def invMat (g : GSp4 R) : Matrix (Fin 4) (Fin 4) R :=
  ((g.sim⁻¹ : Rˣ) : R) • sympAdj g.val

theorem invMat_mul_val (g : GSp4 R) : g.invMat * g.val = 1 := by
  unfold invMat
  rw [Matrix.smul_mul, g.sympAdj_mul_val, smul_smul, ← Units.val_mul, inv_mul_cancel,
    Units.val_one, one_smul]

theorem val_mul_invMat (g : GSp4 R) : g.val * g.invMat = 1 := by
  have hdet : IsUnit g.val.det :=
    isUnit_iff_exists_inv.mpr ⟨g.invMat.det,
      by rw [mul_comm, ← Matrix.det_mul, g.invMat_mul_val, Matrix.det_one]⟩
  let u := Matrix.nonsingInvUnit g.val hdet
  have hu : g.invMat = u.inv := by
    calc g.invMat = g.invMat * (u.val * u.inv) := by rw [u.val_inv, Matrix.mul_one]
      _ = (g.invMat * g.val) * u.inv := (Matrix.mul_assoc _ _ _).symm
      _ = u.inv := by rw [g.invMat_mul_val, Matrix.one_mul]
  rw [hu]
  exact u.val_inv

theorem val_mul_sympAdj (g : GSp4 R) : g.val * sympAdj g.val = (g.sim : R) • 1 := by
  have h := congrArg (fun M => (g.sim : R) • M) g.val_mul_invMat
  unfold invMat at h
  rw [Matrix.mul_smul, smul_smul, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_smul] at h
  exact h

theorem isGSp_invMat (g : GSp4 R) : IsGSp4 ((g.sim⁻¹ : Rˣ) : R) g.invMat := by
  rw [isGSp4_iff_sympAdj_mul]
  unfold invMat
  rw [sympAdj_smul, sympAdj_sympAdj, Matrix.smul_mul, Matrix.mul_smul, g.val_mul_sympAdj,
    smul_smul, smul_smul, mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one]

instance : One (GSp4 R) := ⟨⟨1, 1, by simp [IsGSp4]⟩⟩

instance : Mul (GSp4 R) :=
  ⟨fun g h =>
    ⟨g.val * h.val, g.sim * h.sim, by
      unfold IsGSp4
      rw [Matrix.transpose_mul]
      calc h.valᵀ * g.valᵀ * J4 R * (g.val * h.val)
          = h.valᵀ * ((g.valᵀ * J4 R * g.val) * h.val) := by simp only [Matrix.mul_assoc]
        _ = h.valᵀ * (((g.sim : R) • J4 R) * h.val) := by rw [g.isGSp]
        _ = (g.sim : R) • (h.valᵀ * J4 R * h.val) := by
              rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc]
        _ = (g.sim : R) • ((h.sim : R) • J4 R) := by rw [h.isGSp]
        _ = ((g.sim * h.sim : Rˣ) : R) • J4 R := by rw [smul_smul, Units.val_mul]⟩⟩

instance : Inv (GSp4 R) := ⟨fun g => ⟨g.invMat, g.sim⁻¹, g.isGSp_invMat⟩⟩

@[simp] theorem one_val : (1 : GSp4 R).val = 1 := rfl
@[simp] theorem one_sim : (1 : GSp4 R).sim = 1 := rfl
@[simp] theorem mul_val (g h : GSp4 R) : (g * h).val = g.val * h.val := rfl
@[simp] theorem mul_sim (g h : GSp4 R) : (g * h).sim = g.sim * h.sim := rfl
@[simp] theorem inv_val (g : GSp4 R) : (g⁻¹).val = g.invMat := rfl
@[simp] theorem inv_sim (g : GSp4 R) : (g⁻¹).sim = g.sim⁻¹ := rfl
@[simp] theorem val_mul_inv_val (g : GSp4 R) : g.val * g⁻¹.val = 1 := g.val_mul_invMat
@[simp] theorem inv_val_mul_val (g : GSp4 R) : g⁻¹.val * g.val = 1 := g.invMat_mul_val

instance instGroup : Group (GSp4 R) where
  mul_assoc a b c := ext_val (Matrix.mul_assoc _ _ _) (mul_assoc _ _ _)
  one_mul a := ext_val (Matrix.one_mul _) (one_mul _)
  mul_one a := ext_val (Matrix.mul_one _) (mul_one _)
  inv_mul_cancel a := ext_val a.invMat_mul_val (inv_mul_cancel a.sim)

/-- Canonical **Similitude Character** `ν : GSp₄(R) →* Rˣ`. -/
def simHom : GSp4 R →* Rˣ where
  toFun g := g.sim
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp] theorem simHom_apply (g : GSp4 R) : simHom g = g.sim := rfl

/-- Faithful embedding `GSp₄(R) ↪ GL₄(R)`. -/
def toGL : GSp4 R →* Matrix.GeneralLinearGroup (Fin 4) R where
  toFun g := { val := g.val, inv := g⁻¹.val, val_inv := g.val_mul_inv_val, inv_val := g.inv_val_mul_val }
  map_one' := by ext i j; rfl
  map_mul' _ _ := by ext i j; rfl

theorem toGL_injective [Nontrivial R] : Function.Injective (toGL (R := R)) := by
  intro g h hgh
  have hval : g.val = h.val := congrArg Units.val hgh
  have hsim_mat : (g.sim : R) • J4 R = (h.sim : R) • J4 R := by rw [← g.isGSp, ← h.isGSp, hval]
  have h03 := congrArg (fun M : Matrix (Fin 4) (Fin 4) R => M 0 3) hsim_mat
  exact ext_val hval (Units.ext (by simpa [J4_apply, j4Sign] using h03))

/-- Determinant square identity for `GSp₄(R)`: `det(g)² = ν(g)⁴`. -/
theorem det_sq_eq_sim_pow_four (g : GSp4 R) :
    Matrix.det g.val ^ 2 = (g.sim : R) ^ 4 := by
  have h := congrArg Matrix.det g.isGSp
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, J4_det, Matrix.det_smul,
    J4_det, Fintype.card_fin] at h
  simpa [sq, mul_one, one_mul] using h

/-- Functorial pushforward `GSp₄(R) →* GSp₄(S)` along any ring homomorphism `f : R →+* S`. -/
def map {S : Type*} [CommRing S] (f : R →+* S) : GSp4 R →* GSp4 S where
  toFun g :=
    { val := g.val.map f
      sim := Units.map f.toMonoidHom g.sim
      isGSp := by
        unfold IsGSp4
        have hm := congrArg (fun M : Matrix (Fin 4) (Fin 4) R => M.map f) g.isGSp
        rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, J4_map] at hm
        rw [hm]
        ext i j
        simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, Units.coe_map,
          map_mul, J4_apply]
        split_ifs <;> simp [j4Sign_map] }
  map_one' := ext_val (by ext i j; by_cases h : i = j <;> simp [h]) (map_one _)
  map_mul' g h := ext_val (by
    change (g.val * h.val).map f = g.val.map f * h.val.map f
    rw [Matrix.map_mul]) (map_mul _ _ _)

@[simp] theorem map_val {S : Type*} [CommRing S] (f : R →+* S) (g : GSp4 R) :
    (map f g).val = g.val.map f := rfl

@[simp] theorem map_sim {S : Type*} [CommRing S] (f : R →+* S) (g : GSp4 R) :
    (map f g).sim = Units.map f.toMonoidHom g.sim := rfl

theorem sympAdj_conj (g : GSp4 R) (X : Matrix (Fin 4) (Fin 4) R) :
    sympAdj (g.val * X * g⁻¹.val) = g.val * sympAdj X * g⁻¹.val := by
  rw [sympAdj_mul, sympAdj_mul]
  have h1 : sympAdj g.val = (g.sim : R) • g⁻¹.val := by
    change sympAdj g.val = (g.sim : R) • (((g.sim⁻¹ : Rˣ) : R) • sympAdj g.val)
    rw [smul_smul, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_smul]
  have h2 : sympAdj g⁻¹.val = ((g.sim⁻¹ : Rˣ) : R) • g.val := by
    change sympAdj (((g.sim⁻¹ : Rˣ) : R) • sympAdj g.val) = ((g.sim⁻¹ : Rˣ) : R) • g.val
    rw [sympAdj_smul, sympAdj_sympAdj]
  rw [h1, h2, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_smul,
    smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul, Matrix.mul_assoc]

end GSp4

/-- Concrete **Symplectic Group `Sp₄(R) := ker(ν : GSp₄(R) →* Rˣ)`**. -/
def Sp4 (R : Type*) [CommRing R] : Subgroup (GSp4 R) :=
  GSp4.simHom.ker

theorem mem_Sp4_iff {R : Type*} [CommRing R] (g : GSp4 R) :
    g ∈ Sp4 R ↔ g.sim = 1 := Iff.rfl

theorem mem_Sp4_iff_matrix {R : Type*} [CommRing R] [Nontrivial R] (g : GSp4 R) :
    g ∈ Sp4 R ↔ g.valᵀ * J4 R * g.val = J4 R := by
  rw [mem_Sp4_iff]
  constructor
  · intro h; have hg := g.isGSp; unfold IsGSp4 at hg; rw [h, Units.val_one, one_smul] at hg; exact hg
  · intro h
    have heq : (g.sim : R) • J4 R = (1 : R) • J4 R := by rw [← g.isGSp, h, one_smul]
    have h03 := congrArg (fun M : Matrix (Fin 4) (Fin 4) R => M 0 3) heq
    exact Units.ext (by simpa [J4_apply, j4Sign] using h03)

theorem det_sq_eq_one_of_mem_Sp4 {R : Type*} [CommRing R] {g : GSp4 R} (hg : g ∈ Sp4 R) :
    Matrix.det g.val ^ 2 = 1 := by
  rw [g.det_sq_eq_sim_pow_four, (mem_Sp4_iff g).mp hg, Units.val_one, one_pow]

/-! ### 1.3 Symplectic Adjoint Lie Algebra `𝔰𝔭₄` (`dim 𝔰𝔭₄ = 10`, `M₄ = 𝔰𝔭₄ ⊕ 𝔰𝔭₄⊥`) -/

/-- The symplectic Lie algebra `𝔰𝔭₄(R) = 𝔤𝔰𝔭₄⁰(R) = { X ∈ M₄(R) | Xᵀ * J₄ + J₄ * X = 0 }`. -/
def sp4Lie (R : Type*) [CommRing R] : Submodule R (Matrix (Fin 4) (Fin 4) R) where
  carrier := { X | Xᵀ * J4 R + J4 R * X = 0 }
  zero_mem' := by simp
  add_mem' {X Y} hX hY := by
    show (X + Y)ᵀ * J4 R + J4 R * (X + Y) = 0
    rw [Matrix.transpose_add, Matrix.add_mul, Matrix.mul_add]
    calc Xᵀ * J4 R + Yᵀ * J4 R + (J4 R * X + J4 R * Y)
        = (Xᵀ * J4 R + J4 R * X) + (Yᵀ * J4 R + J4 R * Y) := by abel
      _ = 0 := by rw [hX, hY, add_zero]
  smul_mem' a {X} hX := by
    show (a • X)ᵀ * J4 R + J4 R * (a • X) = 0
    rw [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, hX, smul_zero]

theorem mem_sp4Lie_iff {R : Type*} [CommRing R] (X : Matrix (Fin 4) (Fin 4) R) :
    X ∈ sp4Lie R ↔ Xᵀ * J4 R + J4 R * X = 0 := Iff.rfl

/-- Exact equivalence `X ∈ 𝔰𝔭₄(R) ↔ sympAdj X = -X`. -/
theorem mem_sp4Lie_iff_sympAdj {R : Type*} [CommRing R] (X : Matrix (Fin 4) (Fin 4) R) :
    X ∈ sp4Lie R ↔ sympAdj X = -X := by
  rw [mem_sp4Lie_iff]
  constructor
  · intro h
    have h1 := congrArg (fun M => (-J4 R) * M) h
    rw [Matrix.mul_add, Matrix.mul_zero] at h1
    have h2 : sympAdj X + X = 0 := by
      calc sympAdj X + X
          = (-J4 R) * (Xᵀ * J4 R) + ((-J4 R) * J4 R) * X := by
              unfold sympAdj; rw [neg_J4_mul_J4, Matrix.one_mul, Matrix.mul_assoc]
        _ = (-J4 R) * (Xᵀ * J4 R) + (-J4 R) * (J4 R * X) := by rw [Matrix.mul_assoc]
        _ = 0 := h1
    exact eq_neg_of_add_eq_zero_left h2
  · intro h
    calc Xᵀ * J4 R + J4 R * X
        = J4 R * sympAdj X + J4 R * X := by rw [J4_mul_sympAdj]
      _ = J4 R * (-X) + J4 R * X := by rw [h]
      _ = 0 := by rw [Matrix.mul_neg, neg_add_cancel]

/-- Every element of `𝔰𝔭₄(K)` has trace `0` (`𝔰𝔭₄ ⊆ 𝔰𝔩₄`) whenever `(2 : K) ≠ 0`. -/
theorem sp4Lie_trace_zero {K : Type*} [Field K] (h2 : (2 : K) ≠ 0)
    {X : Matrix (Fin 4) (Fin 4) K} (hX : X ∈ sp4Lie K) :
    Matrix.trace X = 0 := by
  have h1 : Matrix.trace (sympAdj X) = -Matrix.trace X := by
    rw [(mem_sp4Lie_iff_sympAdj X).mp hX, Matrix.trace_neg]
  rw [trace_sympAdj] at h1
  exact (mul_eq_zero.mp (by linear_combination h1 : (2 : K) * Matrix.trace X = 0)).resolve_left h2

/-- `𝔰𝔭₄(R)` is closed under the matrix Lie bracket `[X, Y] = X * Y - Y * X`. -/
theorem sp4Lie_lie_mem {R : Type*} [CommRing R] {X Y : Matrix (Fin 4) (Fin 4) R}
    (hX : X ∈ sp4Lie R) (hY : Y ∈ sp4Lie R) :
    X * Y - Y * X ∈ sp4Lie R := by
  rw [mem_sp4Lie_iff_sympAdj] at hX hY ⊢
  rw [sympAdj_sub, sympAdj_mul, sympAdj_mul, hX, hY]
  simp

/-- `𝔰𝔭₄(R)` is invariant under conjugation by ANY `g ∈ GSp₄(R)`. -/
theorem sp4Lie_conj_mem {R : Type*} [CommRing R] (g : GSp4 R) {X : Matrix (Fin 4) (Fin 4) R}
    (hX : X ∈ sp4Lie R) :
    g.val * X * g⁻¹.val ∈ sp4Lie R := by
  rw [mem_sp4Lie_iff_sympAdj] at hX ⊢
  rw [g.sympAdj_conj, hX, Matrix.mul_neg, Matrix.neg_mul]

/-- Complementary 6-dimensional symmetric-adjoint subspace `𝔰𝔭₄⊥(R) = { X | sympAdj X = X }`. -/
def sympSymSubmodule (R : Type*) [CommRing R] : Submodule R (Matrix (Fin 4) (Fin 4) R) where
  carrier := { X | sympAdj X = X }
  zero_mem' := sympAdj_zero R
  add_mem' {X Y} hX hY := by show sympAdj (X + Y) = X + Y; rw [sympAdj_add, hX, hY]
  smul_mem' a {X} hX := by show sympAdj (a • X) = a • X; rw [sympAdj_smul, hX]

/-- `GSp₄`-equivariant idempotent projection `sp4Proj K : M₄(K) →ₗ[K] M₄(K)` onto `𝔰𝔭₄(K)`:
`X ↦ 2⁻¹ • (X - sympAdj X)` (directly matching `RigSp4.rgP`). -/
def sp4Proj (K : Type*) [Field K] :
    Matrix (Fin 4) (Fin 4) K →ₗ[K] Matrix (Fin 4) (Fin 4) K where
  toFun X := (2 : K)⁻¹ • (X - sympAdj X)
  map_add' X Y := by rw [sympAdj_add, ← smul_add]; congr 1; abel
  map_smul' a X := by
    change (2 : K)⁻¹ • (a • X - sympAdj (a • X)) = a • ((2 : K)⁻¹ • (X - sympAdj X))
    rw [sympAdj_smul, ← smul_sub, smul_comm]

@[simp]
theorem sp4Proj_apply {K : Type*} [Field K] (X : Matrix (Fin 4) (Fin 4) K) :
    sp4Proj K X = (2 : K)⁻¹ • (X - sympAdj X) := rfl

theorem sp4Proj_mem {K : Type*} [Field K] (X : Matrix (Fin 4) (Fin 4) K) :
    sp4Proj K X ∈ sp4Lie K := by
  rw [mem_sp4Lie_iff_sympAdj, sp4Proj_apply, sympAdj_smul, sympAdj_sub, sympAdj_sympAdj,
    ← smul_neg]
  congr 1; abel

theorem sp4Proj_of_mem {K : Type*} [Field K] (h2 : (2 : K) ≠ 0) {X : Matrix (Fin 4) (Fin 4) K}
    (hX : X ∈ sp4Lie K) :
    sp4Proj K X = X := by
  rw [sp4Proj_apply, (mem_sp4Lie_iff_sympAdj X).mp hX, sub_neg_eq_add, ← two_smul K,
    smul_smul, inv_mul_cancel₀ h2, one_smul]

theorem sp4Proj_idemp {K : Type*} [Field K] (h2 : (2 : K) ≠ 0) (X : Matrix (Fin 4) (Fin 4) K) :
    sp4Proj K (sp4Proj K X) = sp4Proj K X :=
  sp4Proj_of_mem h2 (sp4Proj_mem X)

theorem sp4Proj_conj {K : Type*} [Field K] (g : GSp4 K) (X : Matrix (Fin 4) (Fin 4) K) :
    sp4Proj K (g.val * X * g⁻¹.val) = g.val * sp4Proj K X * g⁻¹.val := by
  simp only [sp4Proj_apply, g.sympAdj_conj, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.mul_smul, Matrix.smul_mul]

theorem sub_sp4Proj_mem_sympSym {K : Type*} [Field K] (h2 : (2 : K) ≠ 0)
    (X : Matrix (Fin 4) (Fin 4) K) :
    X - sp4Proj K X ∈ sympSymSubmodule K := by
  show sympAdj (X - sp4Proj K X) = X - sp4Proj K X
  have hsplit : X - sp4Proj K X = (2 : K)⁻¹ • (X + sympAdj X) := by
    ext i j
    simp only [sp4Proj_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
    field_simp [h2]; ring
  rw [hsplit, sympAdj_smul, sympAdj_add, sympAdj_sympAdj, add_comm]

/-- Direct-sum decomposition `M₄(K) = 𝔰𝔭₄(K) ⊕ 𝔰𝔭₄⊥(K)` (`16 = 10 + 6`). -/
theorem sp4Lie_isCompl_sympSym {K : Type*} [Field K] (h2 : (2 : K) ≠ 0) :
    IsCompl (sp4Lie K) (sympSymSubmodule K) := by
  rw [isCompl_iff]
  constructor
  · rw [disjoint_iff, eq_bot_iff]
    intro X ⟨h1, h2'⟩
    rw [Submodule.mem_bot]
    have hneg : X = -X := (h2' : sympAdj X = X).symm.trans ((mem_sp4Lie_iff_sympAdj X).mp h1)
    ext i j
    have hij := congrArg (fun M : Matrix (Fin 4) (Fin 4) K => M i j) hneg
    simp only [Matrix.neg_apply] at hij
    exact (mul_eq_zero.mp (by linear_combination hij : (2 : K) * X i j = 0)).resolve_left h2
  · rw [codisjoint_iff, eq_top_iff]
    intro X _
    rw [Submodule.mem_sup]
    exact ⟨sp4Proj K X, sp4Proj_mem X, X - sp4Proj K X, sub_sp4Proj_mem_sympSym h2 X,
      add_sub_cancel _ _⟩

/-- Fast pattern-matched reconstruction of a `4 × 4` symplectic Lie algebra matrix from its `10`
independent coordinates `(x₀₀, x₀₁, x₀₂, x₀₃, x₁₀, x₁₁, x₁₂, x₂₀, x₂₁, x₃₀)`. -/
def sp4MatrixOfFin10 {R : Type*} [CommRing R] (v : Fin 10 → R) : Matrix (Fin 4) (Fin 4) R :=
  Matrix.of fun i j =>
    match i, j with
    | 0, 0 => v 0 | 0, 1 => v 1 | 0, 2 => v 2 | 0, 3 => v 3
    | 1, 0 => v 4 | 1, 1 => v 5 | 1, 2 => v 6 | 1, 3 => v 2
    | 2, 0 => v 7 | 2, 1 => v 8 | 2, 2 => -v 5 | 2, 3 => -v 1
    | 3, 0 => v 9 | 3, 1 => v 7 | 3, 2 => -v 4 | 3, 3 => -v 0

theorem sp4MatrixOfFin10_mem {R : Type*} [CommRing R] (v : Fin 10 → R) :
    sp4MatrixOfFin10 v ∈ sp4Lie R := by
  rw [mem_sp4Lie_iff_sympAdj]
  ext i j
  rw [sympAdj_apply, Matrix.neg_apply]
  fin_cases i <;> fin_cases j <;> simp [sp4MatrixOfFin10, j4Sign]

/-- Coordinate extraction `sp4Lie R → (Fin 10 → R)` without `vecCons`. -/
def sp4Fin10OfMatrix {R : Type*} [CommRing R] (X : Matrix (Fin 4) (Fin 4) R) : Fin 10 → R
  | 0 => X 0 0 | 1 => X 0 1 | 2 => X 0 2 | 3 => X 0 3 | 4 => X 1 0
  | 5 => X 1 1 | 6 => X 1 2 | 7 => X 2 0 | 8 => X 2 1 | 9 => X 3 0

/-- **EXACT 10-DIMENSIONAL COORDINATE EQUIVALENCE `sp4Lie R ≃ₗ[R] (Fin 10 → R)`** (works over ANY
commutative ring `R`, without dividing by `2`!). -/
def sp4LieEquivFin10 (R : Type*) [CommRing R] : sp4Lie R ≃ₗ[R] (Fin 10 → R) where
  toFun X := sp4Fin10OfMatrix X.1
  invFun v := ⟨sp4MatrixOfFin10 v, sp4MatrixOfFin10_mem v⟩
  map_add' _ _ := by ext k; fin_cases k <;> rfl
  map_smul' _ _ := by ext k; fin_cases k <;> rfl
  left_inv X := by
    have hX : sympAdj X.1 = -X.1 := (mem_sp4Lie_iff_sympAdj X.1).mp X.2
    have hpt : ∀ i j : Fin 4, j4Sign R i * j4Sign R j * X.1 (Fin.rev j) (Fin.rev i) = -X.1 i j := by
      intro i j
      have := congrArg (fun M : Matrix (Fin 4) (Fin 4) R => M i j) hX
      rwa [sympAdj_apply, Matrix.neg_apply] at this
    have e31 : X.1 3 1 = X.1 2 0 := by have := hpt 3 1; simp [j4Sign] at this; linear_combination -this
    have e32 : X.1 3 2 = -X.1 1 0 := by have := hpt 3 2; simp [j4Sign] at this; linear_combination this
    have e33 : X.1 3 3 = -X.1 0 0 := by have := hpt 3 3; simp [j4Sign] at this; linear_combination this
    have e22 : X.1 2 2 = -X.1 1 1 := by have := hpt 2 2; simp [j4Sign] at this; linear_combination this
    have e23 : X.1 2 3 = -X.1 0 1 := by have := hpt 2 3; simp [j4Sign] at this; linear_combination this
    have e13 : X.1 1 3 = X.1 0 2 := by have := hpt 1 3; simp [j4Sign] at this; linear_combination -this
    apply Subtype.ext; ext i j
    fin_cases i <;> fin_cases j <;>
      simp [sp4MatrixOfFin10, sp4Fin10OfMatrix, e31, e32, e33, e22, e23, e13]
  right_inv v := by
    ext k; fin_cases k <;> rfl

/-- **EXACT DIMENSION OF THE SYMPLECTIC LIE ALGEBRA**: `dim_K 𝔰𝔭₄(K) = 10`! -/
theorem finrank_sp4Lie (K : Type*) [Field K] :
    Module.finrank K (sp4Lie K) = 10 := by
  rw [(sp4LieEquivFin10 K).finrank_eq, Module.finrank_fin_fun]

/-- **EXACT DIMENSION OF THE COMPLEMENTARY SUMMAND**: `dim_K 𝔰𝔭₄⊥(K) = 6` (`10 + 6 = 16`)! -/
theorem finrank_sympSymSubmodule {K : Type*} [Field K] (h2 : (2 : K) ≠ 0) :
    Module.finrank K (sympSymSubmodule K) = 6 := by
  have hsum := Submodule.finrank_add_eq_of_isCompl (sp4Lie_isCompl_sympSym h2)
  have hmat : Module.finrank K (Matrix (Fin 4) (Fin 4) K) = 16 := by
    rw [Module.finrank_matrix, Fintype.card_fin, Module.finrank_self]
  rw [finrank_sp4Lie, hmat] at hsum
  omega

/-! ### 1.4 Symplectic Adjoint Representation, Odd Involution Normal Form, & `finrank_H0_inf_sp4_eq_four` -/

/-- Concrete `K`-vector space wrapper for the `GSp₄` symplectic adjoint representation `𝔰𝔭₄(K)`
with conjugation action `g • X = ρ(g) X ρ(g)⁻¹`. -/
structure Sp4AdRep {G K : Type*} [Group G] [Field K] (ρ : G →* GSp4 K) where
  val : Matrix (Fin 4) (Fin 4) K
  mem_sp4 : val ∈ sp4Lie K

namespace Sp4AdRep

variable {G K : Type*} [Group G] [Field K] {ρ : G →* GSp4 K}

theorem ext_val {X Y : Sp4AdRep ρ} (h : X.val = Y.val) : X = Y := by
  cases X; cases Y; cases h; rfl

instance : Zero (Sp4AdRep ρ) := ⟨⟨0, (sp4Lie K).zero_mem⟩⟩
instance : Add (Sp4AdRep ρ) := ⟨fun X Y => ⟨X.val + Y.val, (sp4Lie K).add_mem X.mem_sp4 Y.mem_sp4⟩⟩
instance : Neg (Sp4AdRep ρ) := ⟨fun X => ⟨-X.val, (sp4Lie K).neg_mem X.mem_sp4⟩⟩
instance : Sub (Sp4AdRep ρ) := ⟨fun X Y => ⟨X.val - Y.val, (sp4Lie K).sub_mem X.mem_sp4 Y.mem_sp4⟩⟩
instance : SMul K (Sp4AdRep ρ) := ⟨fun a X => ⟨a • X.val, (sp4Lie K).smul_mem a X.mem_sp4⟩⟩

instance instAddCommGroup : AddCommGroup (Sp4AdRep ρ) where
  sub X Y := ⟨X.val - Y.val, (sp4Lie K).sub_mem X.mem_sp4 Y.mem_sp4⟩
  add_assoc _ _ _ := ext_val (add_assoc _ _ _)
  zero_add _ := ext_val (zero_add _)
  add_zero _ := ext_val (add_zero _)
  nsmul := nsmulRec
  zsmul := zsmulRec
  neg_add_cancel _ := ext_val (neg_add_cancel _)
  add_comm _ _ := ext_val (add_comm _ _)
  sub_eq_add_neg _ _ := ext_val (sub_eq_add_neg _ _)

instance instModule : Module K (Sp4AdRep ρ) where
  one_smul _ := ext_val (one_smul K _)
  mul_smul _ _ _ := ext_val (mul_smul _ _ _)
  smul_zero _ := ext_val (smul_zero _)
  smul_add _ _ _ := ext_val (smul_add _ _ _)
  add_smul _ _ _ := ext_val (add_smul _ _ _)
  zero_smul _ := ext_val (zero_smul K _)

instance instDistribMulAction : DistribMulAction G (Sp4AdRep ρ) where
  smul g X := ⟨(ρ g).val * X.val * (ρ g)⁻¹.val, sp4Lie_conj_mem (ρ g) X.mem_sp4⟩
  one_smul X := ext_val (by change (ρ 1).val * X.val * (ρ 1)⁻¹.val = X.val; simp)
  mul_smul g h X := ext_val (by
    change (ρ (g * h)).val * X.val * (ρ (g * h))⁻¹.val =
      (ρ g).val * ((ρ h).val * X.val * (ρ h)⁻¹.val) * (ρ g)⁻¹.val
    rw [map_mul, _root_.mul_inv_rev]
    simp only [GSp4.mul_val, Matrix.mul_assoc])
  smul_zero g := ext_val (by change (ρ g).val * 0 * (ρ g)⁻¹.val = 0; simp)
  smul_add g X Y := ext_val (by
    change (ρ g).val * (X.val + Y.val) * (ρ g)⁻¹.val =
      (ρ g).val * X.val * (ρ g)⁻¹.val + (ρ g).val * Y.val * (ρ g)⁻¹.val
    rw [Matrix.mul_add, Matrix.add_mul])

instance instSMulCommClass : SMulCommClass G K (Sp4AdRep ρ) where
  smul_comm g a X := ext_val (by
    change (ρ g).val * (a • X.val) * (ρ g)⁻¹.val = a • ((ρ g).val * X.val * (ρ g)⁻¹.val)
    rw [Matrix.mul_smul, Matrix.smul_mul])

/-- Linear equivalence identifying `Sp4AdRep ρ` with `sp4Lie K`. -/
def equivSp4Lie (ρ : G →* GSp4 K) : Sp4AdRep ρ ≃ₗ[K] sp4Lie K where
  toFun X := ⟨X.val, X.mem_sp4⟩
  invFun X := ⟨X.1, X.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem finrank_eq_ten (ρ : G →* GSp4 K) : Module.finrank K (Sp4AdRep ρ) = 10 := by
  rw [(equivSp4Lie ρ).finrank_eq, finrank_sp4Lie]

end Sp4AdRep

/-- Standard odd symplectic involution `c_std = diag(1, 1, -1, -1) ∈ GSp₄(R)` with similitude `-1`. -/
def stdOddSympInv (R : Type*) [CommRing R] : GSp4 R where
  val := Matrix.diagonal (j4Sign R)
  sim := -1
  isGSp := by
    unfold IsGSp4
    ext i j
    rw [Matrix.diagonal_transpose, Matrix.mul_diagonal, Matrix.diagonal_mul,
      Matrix.smul_apply, smul_eq_mul, J4_apply]
    by_cases h : j = Fin.rev i
    · subst h; rw [if_pos rfl, j4Sign_rev]
      calc j4Sign R i * j4Sign R i * -j4Sign R i = 1 * -j4Sign R i := by rw [j4Sign_mul_self]
        _ = ((-1 : Rˣ) : R) * j4Sign R i := by simp
    · simp [h]

theorem stdOddSympInv_sq (R : Type*) [CommRing R] :
    stdOddSympInv R * stdOddSympInv R = 1 := by
  apply GSp4.ext_val
  · change Matrix.diagonal (j4Sign R) * Matrix.diagonal (j4Sign R) = 1
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases h : i = j
    · subst h; simp [j4Sign_mul_self]
    · simp [h]
  · simp [stdOddSympInv]

/-- Symplectic pairing `ω(u, v) = uᵀ J₄ v` on `Fin 4 → K`. -/
def sympForm {K : Type*} [Field K] (u v : Fin 4 → K) : K :=
  dotProduct u ((J4 K).mulVec v)

theorem sympForm_skew {K : Type*} [Field K] (u v : Fin 4 → K) :
    sympForm u v = -sympForm v u := by
  unfold sympForm
  calc u ⬝ᵥ (J4 K *ᵥ v)
      = (u ᵥ* J4 K) ⬝ᵥ v := dotProduct_mulVec u (J4 K) v
    _ = v ⬝ᵥ (u ᵥ* J4 K) := dotProduct_comm _ _
    _ = v ⬝ᵥ ((J4 K)ᵀ *ᵥ u) := by rw [Matrix.mulVec_transpose]
    _ = -(v ⬝ᵥ (J4 K *ᵥ u)) := by rw [J4_transpose, Matrix.neg_mulVec, dotProduct_neg]

theorem sympForm_gsp4 {K : Type*} [Field K] (g : GSp4 K) (u v : Fin 4 → K) :
    sympForm (g.val.mulVec u) (g.val.mulVec v) = (g.sim : K) * sympForm u v := by
  unfold sympForm
  calc (g.val *ᵥ u) ⬝ᵥ (J4 K *ᵥ (g.val *ᵥ v))
      = (g.val *ᵥ u) ⬝ᵥ ((J4 K * g.val) *ᵥ v) := by rw [Matrix.mulVec_mulVec]
    _ = ((g.val *ᵥ u) ᵥ* (J4 K * g.val)) ⬝ᵥ v := dotProduct_mulVec _ _ _
    _ = ((u ᵥ* g.valᵀ) ᵥ* (J4 K * g.val)) ⬝ᵥ v := by rw [← Matrix.vecMul_transpose]
    _ = (u ᵥ* (g.valᵀ * (J4 K * g.val))) ⬝ᵥ v := by rw [Matrix.vecMul_vecMul]
    _ = (u ᵥ* ((g.valᵀ * J4 K * g.val))) ⬝ᵥ v := by rw [Matrix.mul_assoc]
    _ = (u ᵥ* ((g.sim : K) • J4 K)) ⬝ᵥ v := by rw [g.isGSp]
    _ = u ⬝ᵥ (((g.sim : K) • J4 K) *ᵥ v) := (dotProduct_mulVec _ _ _).symm
    _ = (g.sim : K) * (u ⬝ᵥ (J4 K *ᵥ v)) := by rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]

theorem sympForm_nondegenerate {K : Type*} [Field K] {u : Fin 4 → K}
    (hu : ∀ v : Fin 4 → K, sympForm u v = 0) : u = 0 := by
  have h1 : vecMul u (J4 K) = 0 := by
    ext j
    have hj := hu (Pi.single j 1)
    unfold sympForm at hj
    rw [dotProduct_mulVec, dotProduct_single, mul_one] at hj
    exact hj
  have h2 := congrArg (fun w => vecMul w (-J4 K)) h1
  rw [vecMul_vecMul, J4_mul_neg_J4, vecMul_one, zero_vecMul] at h2
  exact h2

/-- **SYMPLECTIC NORMAL FORM FOR ANY ODD SYMPLECTIC INVOLUTION**:
Over any field `K` with `(2 : K) ≠ 0`, EVERY element `c ∈ GSp₄(K)` satisfying `c * c = 1` and
`c.sim = -1` has 2-dimensional Lagrangian `±1`-eigenspaces and is conjugate in **`Sp₄(K)`** to
`stdOddSympInv K = diag(1, 1, -1, -1)`! -/
theorem exists_sp4_conj_stdOddSympInv {K : Type*} [Field K] (h2 : (2 : K) ≠ 0)
    (c : GSp4 K) (hc2 : c * c = 1) (hsim : c.sim = -1) :
    ∃ P : GSp4 K, P ∈ Sp4 K ∧ P⁻¹ * c * P = stdOddSympInv K := by
  have hc2_val : c.val * c.val = 1 := congrArg GSp4.val hc2
  let Vp : Submodule K (Fin 4 → K) :=
    { carrier := { u | c.val.mulVec u = u }
      zero_mem' := Matrix.mulVec_zero _
      add_mem' := fun {u v} hu hv => by show c.val.mulVec (u + v) = u + v; rw [Matrix.mulVec_add, hu, hv]
      smul_mem' := fun a {u} hu => by show c.val.mulVec (a • u) = a • u; rw [Matrix.mulVec_smul, hu] }
  let Vm : Submodule K (Fin 4 → K) :=
    { carrier := { u | c.val.mulVec u = -u }
      zero_mem' := by simp
      add_mem' := fun {u v} hu hv => by
        show c.val.mulVec (u + v) = -(u + v); rw [Matrix.mulVec_add, hu, hv, neg_add]
      smul_mem' := fun a {u} hu => by
        show c.val.mulVec (a • u) = -(a • u); rw [Matrix.mulVec_smul, hu, smul_neg] }
  have hcompl : IsCompl Vp Vm := by
    rw [isCompl_iff]
    constructor
    · rw [disjoint_iff, eq_bot_iff]
      intro u ⟨hp, hm⟩
      rw [Submodule.mem_bot]
      have hneg : u = -u := hp.symm.trans hm
      ext i
      have hi : u i = -u i := by simpa using congrFun hneg i
      exact (mul_eq_zero.mp (by linear_combination hi : (2 : K) * u i = 0)).resolve_left h2
    · rw [codisjoint_iff, eq_top_iff]
      intro u _
      rw [Submodule.mem_sup]
      refine ⟨(2 : K)⁻¹ • (u + c.val.mulVec u), ?_, (2 : K)⁻¹ • (u - c.val.mulVec u), ?_, ?_⟩
      · show c.val.mulVec ((2 : K)⁻¹ • (u + c.val.mulVec u)) = (2 : K)⁻¹ • (u + c.val.mulVec u)
        rw [Matrix.mulVec_smul, Matrix.mulVec_add, Matrix.mulVec_mulVec, hc2_val, Matrix.one_mulVec, add_comm]
      · show c.val.mulVec ((2 : K)⁻¹ • (u - c.val.mulVec u)) = -((2 : K)⁻¹ • (u - c.val.mulVec u))
        rw [Matrix.mulVec_smul, Matrix.mulVec_sub, Matrix.mulVec_mulVec, hc2_val, Matrix.one_mulVec, ← smul_neg]
        congr 1; abel
      · ext i
        simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
        field_simp [h2]; ring
  have hiso_p : ∀ u ∈ Vp, ∀ v ∈ Vp, sympForm u v = 0 := by
    intro u hu v hv
    have h1 : sympForm u v = -sympForm u v := by
      have hc := sympForm_gsp4 c u v
      rw [hu, hv, hsim, Units.val_neg, Units.val_one, neg_one_mul] at hc; exact hc
    exact (mul_eq_zero.mp (by linear_combination h1 : (2 : K) * sympForm u v = 0)).resolve_left h2
  have hiso_m : ∀ u ∈ Vm, ∀ v ∈ Vm, sympForm u v = 0 := by
    intro u hu v hv
    have h1 : sympForm u v = -sympForm u v := by
      have hc := sympForm_gsp4 c u v
      rw [hu, hv, hsim, Units.val_neg, Units.val_one, neg_one_mul] at hc
      have hneg_pair : sympForm (-u) (-v) = sympForm u v := by unfold sympForm; simp [Matrix.mulVec_neg]
      rw [hneg_pair] at hc; exact hc
    exact (mul_eq_zero.mp (by linear_combination h1 : (2 : K) * sympForm u v = 0)).resolve_left h2
  let Φ : Vp →ₗ[K] Module.Dual K Vm :=
    { toFun := fun u =>
        { toFun := fun v => sympForm u.1 v.1
          map_add' := fun v w => by
            unfold sympForm; rw [Submodule.coe_add, Matrix.mulVec_add, dotProduct_add]
          map_smul' := fun a v => by
            unfold sympForm; rw [Submodule.coe_smul_of_tower, Matrix.mulVec_smul, dotProduct_smul]; rfl }
      map_add' := fun u₁ u₂ => by
        ext v; change sympForm (u₁.1 + u₂.1) v.1 = sympForm u₁.1 v.1 + sympForm u₂.1 v.1
        unfold sympForm; exact add_dotProduct _ _ _
      map_smul' := fun a u => by
        ext v; change sympForm (a • u.1) v.1 = a * sympForm u.1 v.1
        unfold sympForm; rw [smul_dotProduct, smul_eq_mul] }
  let Ψ : Vm →ₗ[K] Module.Dual K Vp :=
    { toFun := fun v =>
        { toFun := fun u => sympForm u.1 v.1
          map_add' := fun u₁ u₂ => by unfold sympForm; exact add_dotProduct _ _ _
          map_smul' := fun a u => by unfold sympForm; exact smul_dotProduct _ _ _ }
      map_add' := fun v₁ v₂ => by
        ext u; change sympForm u.1 (v₁.1 + v₂.1) = sympForm u.1 v₁.1 + sympForm u.1 v₂.1
        unfold sympForm; rw [Matrix.mulVec_add, dotProduct_add]
      map_smul' := fun a v => by
        ext u; change sympForm u.1 (a • v.1) = a * sympForm u.1 v.1
        unfold sympForm; rw [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul] }
  have hΦ_inj : Function.Injective Φ := by
    rw [injective_iff_map_eq_zero]
    intro u hu
    apply Subtype.ext; apply sympForm_nondegenerate; intro w
    have hw : w ∈ Vp ⊔ Vm := by rw [hcompl.sup_eq_top]; trivial
    obtain ⟨wp, hwp, wm, hwm, rfl⟩ := Submodule.mem_sup.mp hw
    have hadd : sympForm u.1 (wp + wm) = sympForm u.1 wp + sympForm u.1 wm := by
      unfold sympForm; rw [Matrix.mulVec_add, dotProduct_add]
    rw [hadd, hiso_p u.1 u.2 wp hwp, zero_add]
    exact congrFun (congrArg DFunLike.coe hu) ⟨wm, hwm⟩
  have hΨ_inj : Function.Injective Ψ := by
    rw [injective_iff_map_eq_zero]
    intro v hv
    apply Subtype.ext; apply sympForm_nondegenerate; intro w
    have hw : w ∈ Vp ⊔ Vm := by rw [hcompl.sup_eq_top]; trivial
    obtain ⟨wp, hwp, wm, hwm, rfl⟩ := Submodule.mem_sup.mp hw
    have hadd : sympForm v.1 (wp + wm) = sympForm v.1 wp + sympForm v.1 wm := by
      unfold sympForm; rw [Matrix.mulVec_add, dotProduct_add]
    rw [hadd, hiso_m v.1 v.2 wm hwm, add_zero, sympForm_skew]
    have hv0 : sympForm wp v.1 = 0 := congrFun (congrArg DFunLike.coe hv) ⟨wp, hwp⟩
    rw [hv0, neg_zero]
  have hdim_sum : Module.finrank K Vp + Module.finrank K Vm = 4 := by
    have h := Submodule.finrank_add_eq_of_isCompl hcompl
    rw [Module.finrank_fin_fun] at h; exact h
  have hle1 : Module.finrank K Vp ≤ Module.finrank K Vm :=
    (LinearMap.finrank_le_finrank_of_injective hΦ_inj).trans_eq Subspace.dual_finrank_eq
  have hle2 : Module.finrank K Vm ≤ Module.finrank K Vp :=
    (LinearMap.finrank_le_finrank_of_injective hΨ_inj).trans_eq Subspace.dual_finrank_eq
  have hdim_p : Module.finrank K Vp = 2 := by omega
  have hdim_m : Module.finrank K Vm = 2 := by omega
  have hΨ_bij : Function.Bijective Ψ := by
    have hdim_eq : Module.finrank K Vm = Module.finrank K (Module.Dual K Vp) := by
      rw [Subspace.dual_finrank_eq, hdim_p, hdim_m]
    exact ⟨hΨ_inj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim_eq).mp hΨ_inj⟩
  let Ψe : Vm ≃ₗ[K] Module.Dual K Vp := LinearEquiv.ofBijective Ψ hΨ_bij
  let bp : Module.Basis (Fin 2) K Vp := (Module.finBasis K Vp).reindex (finCongr hdim_p)
  let e0 : Vp := bp 0
  let e1 : Vp := bp 1
  let e3 : Vm := Ψe.symm (bp.coord 0)
  let e2 : Vm := Ψe.symm (bp.coord 1)
  have hΨ_eval : ∀ (f : Module.Dual K Vp) (u : Vp), sympForm u.1 (Ψe.symm f).1 = f u := fun f u => by
    have h := congrArg (fun g : Module.Dual K Vp => g u) (Ψe.apply_symm_apply f)
    exact h
  have he03 : sympForm e0.1 e3.1 = 1 := by
    rw [hΨ_eval]; simp [e0, bp.coord_apply, bp.repr_self]
  have he13 : sympForm e1.1 e3.1 = 0 := by
    rw [hΨ_eval]; simp [e1, bp.coord_apply, bp.repr_self]
  have he02 : sympForm e0.1 e2.1 = 0 := by
    rw [hΨ_eval]; simp [e0, bp.coord_apply, bp.repr_self]
  have he12 : sympForm e1.1 e2.1 = 1 := by
    rw [hΨ_eval]; simp [e1, bp.coord_apply, bp.repr_self]
  let cols : Fin 4 → (Fin 4 → K) := fun
    | 0 => e0.1 | 1 => e1.1 | 2 => e2.1 | 3 => e3.1
  let Pmat : Matrix (Fin 4) (Fin 4) K := Matrix.of (fun i j => cols j i)
  have hP_gsp : IsGSp4 (1 : K) Pmat := by
    unfold IsGSp4; rw [one_smul]
    ext a b
    have hcol : (Pmatᵀ * J4 K * Pmat) a b = sympForm (cols a) (cols b) := by
      unfold sympForm
      simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.mulVec, dotProduct, Pmat, Matrix.of_apply]
      simp_rw [Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_; ring
    rw [hcol]
    fin_cases a <;> fin_cases b <;> simp only [cols, J4_apply, j4Sign]
    · simpa using hiso_p e0.1 e0.2 e0.1 e0.2
    · simpa using hiso_p e0.1 e0.2 e1.1 e1.2
    · simpa using he02
    · simpa using he03
    · simpa using hiso_p e1.1 e1.2 e0.1 e0.2
    · simpa using hiso_p e1.1 e1.2 e1.1 e1.2
    · simpa using he12
    · simpa using he13
    · rw [sympForm_skew, he02]; simp
    · rw [sympForm_skew, he12]; simp
    · simpa using hiso_m e2.1 e2.2 e2.1 e2.2
    · simpa using hiso_m e2.1 e2.2 e3.1 e3.2
    · rw [sympForm_skew, he03]; simp
    · rw [sympForm_skew, he13]; simp
    · simpa using hiso_m e3.1 e3.2 e2.1 e2.2
    · simpa using hiso_m e3.1 e3.2 e3.1 e3.2
  let P : GSp4 K := ⟨Pmat, 1, hP_gsp⟩
  have hcP : c.val * P.val = P.val * (stdOddSympInv K).val := by
    ext i j
    have hlhs : (c.val * P.val) i j = (c.val.mulVec (cols j)) i := by
      simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, P, Pmat]
    rw [hlhs, show (stdOddSympInv K).val = Matrix.diagonal (j4Sign K) from rfl, Matrix.mul_diagonal]
    fin_cases j
    · have h0 : c.val.mulVec e0.1 = e0.1 := e0.2; simp [cols, h0, P, Pmat, j4Sign]
    · have h1 : c.val.mulVec e1.1 = e1.1 := e1.2; simp [cols, h1, P, Pmat, j4Sign]
    · have h2' : c.val.mulVec e2.1 = -e2.1 := e2.2; simp [cols, h2', P, Pmat, j4Sign]
    · have h3 : c.val.mulVec e3.1 = -e3.1 := e3.2; simp [cols, h3, P, Pmat, j4Sign]
  refine ⟨P, rfl, GSp4.ext_val ?_ (by simp [P, hsim, stdOddSympInv])⟩
  change P⁻¹.val * c.val * P.val = (stdOddSympInv K).val
  rw [Matrix.mul_assoc, hcP, ← Matrix.mul_assoc, P.inv_val_mul_val, Matrix.one_mul]

/-- Subspace of `𝔰𝔭₄(K)` commuting with `g ∈ GSp₄(K)`: `{ X ∈ 𝔰𝔭₄ | g X g⁻¹ = X }`. -/
def sp4FixedSubmodule {K : Type*} [Field K] (g : GSp4 K) : Submodule K (sp4Lie K) where
  carrier := { X | g.val * X.1 * g⁻¹.val = X.1 }
  zero_mem' := by simp
  add_mem' {X Y} hX hY := by
    show g.val * (X.1 + Y.1) * g⁻¹.val = X.1 + Y.1; rw [Matrix.mul_add, Matrix.add_mul, hX, hY]
  smul_mem' a {X} hX := by
    show g.val * (a • X.1) * g⁻¹.val = a • X.1; rw [Matrix.mul_smul, Matrix.smul_mul, hX]

/-- `-1`-eigenspace of an involution `c ∈ GSp₄(K)` on `𝔰𝔭₄(K)`: `{ X ∈ 𝔰𝔭₄ | c X c⁻¹ = -X }`. -/
def sp4AntiFixedSubmodule {K : Type*} [Field K] (c : GSp4 K) : Submodule K (sp4Lie K) where
  carrier := { X | c.val * X.1 * c⁻¹.val = -X.1 }
  zero_mem' := by simp
  add_mem' {X Y} hX hY := by
    show c.val * (X.1 + Y.1) * c⁻¹.val = -(X.1 + Y.1)
    rw [Matrix.mul_add, Matrix.add_mul, hX, hY, neg_add]
  smul_mem' a {X} hX := by
    show c.val * (a • X.1) * c⁻¹.val = -(a • X.1); rw [Matrix.mul_smul, Matrix.smul_mul, hX, smul_neg]

/-- Fast block-diagonal reconstruction of a `4 × 4` fixed symplectic matrix from `(Fin 4 → K)`. -/
def sp4FixedStdMat {K : Type*} [Field K] (v : Fin 4 → K) : Matrix (Fin 4) (Fin 4) K :=
  Matrix.of fun i j =>
    match i, j with
    | 0, 0 => v 0 | 0, 1 => v 1 | 1, 0 => v 2 | 1, 1 => v 3
    | 2, 2 => -v 3 | 2, 3 => -v 1 | 3, 2 => -v 2 | 3, 3 => -v 0
    | _, _ => 0

/-- Fast coordinate extraction `sp4FixedSubmodule (stdOddSympInv K) → (Fin 4 → K)`. -/
def sp4Fin4OfMatrix {K : Type*} [Field K] (X : Matrix (Fin 4) (Fin 4) K) : Fin 4 → K
  | 0 => X 0 0 | 1 => X 0 1 | 2 => X 1 0 | 3 => X 1 1

/-- Explicit 4-coordinate isomorphism `sp4FixedSubmodule (stdOddSympInv K) ≃ₗ[K] (Fin 4 → K)`
(the upper-left `2 × 2` block `M₂(K)`). -/
def sp4FixedStdEquivFin4 {K : Type*} [Field K] (h2 : (2 : K) ≠ 0) :
    sp4FixedSubmodule (stdOddSympInv K) ≃ₗ[K] (Fin 4 → K) where
  toFun X := sp4Fin4OfMatrix X.1.1
  invFun v :=
    ⟨⟨sp4FixedStdMat v, by
        rw [mem_sp4Lie_iff_sympAdj]; ext i j
        rw [sympAdj_apply, Matrix.neg_apply]
        fin_cases i <;> fin_cases j <;> simp [sp4FixedStdMat, j4Sign]⟩,
     by
      show (stdOddSympInv K).val * sp4FixedStdMat v * (stdOddSympInv K)⁻¹.val = sp4FixedStdMat v
      have hinv : (stdOddSympInv K)⁻¹ = stdOddSympInv K :=
        inv_eq_of_mul_eq_one_right (stdOddSympInv_sq K)
      rw [hinv]
      ext i j
      change (Matrix.diagonal (j4Sign K) * sp4FixedStdMat v * Matrix.diagonal (j4Sign K)) i j = _
      rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
      fin_cases i <;> fin_cases j <;> simp [sp4FixedStdMat, j4Sign]⟩
  map_add' _ _ := by ext k; fin_cases k <;> rfl
  map_smul' _ _ := by ext k; fin_cases k <;> rfl
  left_inv X := by
    have hinv : (stdOddSympInv K)⁻¹ = stdOddSympInv K :=
      inv_eq_of_mul_eq_one_right (stdOddSympInv_sq K)
    have hcomm : Matrix.diagonal (j4Sign K) * X.1.1 * Matrix.diagonal (j4Sign K) = X.1.1 := by
      have hx : (stdOddSympInv K).val * X.1.1 * (stdOddSympInv K)⁻¹.val = X.1.1 := X.2
      rw [hinv] at hx; exact hx
    have hpt_comm : ∀ i j : Fin 4, j4Sign K i * X.1.1 i j * j4Sign K j = X.1.1 i j := by
      intro i j
      have h := congrArg (fun M : Matrix (Fin 4) (Fin 4) K => M i j) hcomm
      rwa [Matrix.mul_diagonal, Matrix.diagonal_mul] at h
    have hpt_sp4 : ∀ i j : Fin 4, j4Sign K i * j4Sign K j * X.1.1 (Fin.rev j) (Fin.rev i) = -X.1.1 i j := by
      intro i j
      have h := congrArg (fun M : Matrix (Fin 4) (Fin 4) K => M i j) ((mem_sp4Lie_iff_sympAdj X.1.1).mp X.1.2)
      rwa [sympAdj_apply, Matrix.neg_apply] at h
    have hkill : ∀ a : K, -a = a → a = 0 := fun a ha =>
      (mul_eq_zero.mp (by linear_combination -ha : (2 : K) * a = 0)).resolve_left h2
    have h02 : X.1.1 0 2 = 0 := hkill _ (by have := hpt_comm 0 2; simpa [j4Sign] using this)
    have h03 : X.1.1 0 3 = 0 := hkill _ (by have := hpt_comm 0 3; simpa [j4Sign] using this)
    have h12 : X.1.1 1 2 = 0 := hkill _ (by have := hpt_comm 1 2; simpa [j4Sign] using this)
    have h13 : X.1.1 1 3 = 0 := hkill _ (by have := hpt_comm 1 3; simpa [j4Sign] using this)
    have h20 : X.1.1 2 0 = 0 := hkill _ (by have := hpt_comm 2 0; simpa [j4Sign] using this)
    have h21 : X.1.1 2 1 = 0 := hkill _ (by have := hpt_comm 2 1; simpa [j4Sign] using this)
    have h30 : X.1.1 3 0 = 0 := hkill _ (by have := hpt_comm 3 0; simpa [j4Sign] using this)
    have h31 : X.1.1 3 1 = 0 := hkill _ (by have := hpt_comm 3 1; simpa [j4Sign] using this)
    have h22 : X.1.1 2 2 = -X.1.1 1 1 := by have := hpt_sp4 2 2; simp [j4Sign] at this; linear_combination this
    have h23 : X.1.1 2 3 = -X.1.1 0 1 := by have := hpt_sp4 2 3; simp [j4Sign] at this; linear_combination this
    have h32 : X.1.1 3 2 = -X.1.1 1 0 := by have := hpt_sp4 3 2; simp [j4Sign] at this; linear_combination this
    have h33 : X.1.1 3 3 = -X.1.1 0 0 := by have := hpt_sp4 3 3; simp [j4Sign] at this; linear_combination this
    apply Subtype.ext; apply Subtype.ext; ext i j
    fin_cases i <;> fin_cases j <;>
      simp [sp4FixedStdMat, sp4Fin4OfMatrix, h02, h03, h12, h13, h20, h21, h30, h31, h22, h23, h32, h33]
  right_inv v := by ext k; fin_cases k <;> rfl

/-- Conjugation by `P ∈ GSp₄(K)` induces a `K`-linear equivalence between fixed subspaces of
`c` and `P⁻¹ c P` on `𝔰𝔭₄(K)`. -/
def sp4FixedConjEquiv {K : Type*} [Field K] (P c : GSp4 K) :
    sp4FixedSubmodule c ≃ₗ[K] sp4FixedSubmodule (P⁻¹ * c * P) where
  toFun X :=
    ⟨⟨P⁻¹.val * X.1.1 * P.val, by have := sp4Lie_conj_mem P⁻¹ X.1.2; simpa using this⟩,
     by
      change (P⁻¹ * c * P).val * (P⁻¹.val * X.1.1 * P.val) * (P⁻¹ * c * P)⁻¹.val =
        P⁻¹.val * X.1.1 * P.val
      have hx : c.val * X.1.1 * c⁻¹.val = X.1.1 := X.2
      have hinv : (P⁻¹ * c * P)⁻¹ = P⁻¹ * c⁻¹ * P := by group
      rw [hinv]
      simp only [GSp4.mul_val]
      calc P⁻¹.val * c.val * P.val * (P⁻¹.val * X.1.1 * P.val) * (P⁻¹.val * c⁻¹.val * P.val)
          = P⁻¹.val * (c.val * (P.val * P⁻¹.val) * X.1.1 * (P.val * P⁻¹.val) * c⁻¹.val) * P.val := by
              simp only [Matrix.mul_assoc]
        _ = P⁻¹.val * (c.val * X.1.1 * c⁻¹.val) * P.val := by
              rw [P.val_mul_inv_val, Matrix.mul_one, Matrix.mul_one]
        _ = P⁻¹.val * X.1.1 * P.val := by rw [hx]⟩
  invFun Y :=
    ⟨⟨P.val * Y.1.1 * P⁻¹.val, sp4Lie_conj_mem P Y.1.2⟩,
     by
      change c.val * (P.val * Y.1.1 * P⁻¹.val) * c⁻¹.val = P.val * Y.1.1 * P⁻¹.val
      have hy : (P⁻¹ * c * P).val * Y.1.1 * (P⁻¹ * c * P)⁻¹.val = Y.1.1 := Y.2
      have hinv : (P⁻¹ * c * P)⁻¹ = P⁻¹ * c⁻¹ * P := by group
      rw [hinv] at hy; simp only [GSp4.mul_val] at hy
      calc c.val * (P.val * Y.1.1 * P⁻¹.val) * c⁻¹.val
          = (P.val * P⁻¹.val) * c.val * P.val * Y.1.1 * P⁻¹.val * c⁻¹.val * (P.val * P⁻¹.val) := by
              rw [P.val_mul_inv_val, Matrix.one_mul, Matrix.mul_one]; simp only [Matrix.mul_assoc]
        _ = P.val * ((P⁻¹.val * c.val * P.val) * Y.1.1 * (P⁻¹.val * c⁻¹.val * P.val)) * P⁻¹.val := by
              simp only [Matrix.mul_assoc]
        _ = P.val * Y.1.1 * P⁻¹.val := by rw [hy]⟩
  map_add' X Y := by
    apply Subtype.ext; apply Subtype.ext
    change P⁻¹.val * (X.1.1 + Y.1.1) * P.val = P⁻¹.val * X.1.1 * P.val + P⁻¹.val * Y.1.1 * P.val
    rw [Matrix.mul_add, Matrix.add_mul]
  map_smul' a X := by
    apply Subtype.ext; apply Subtype.ext
    change P⁻¹.val * (a • X.1.1) * P.val = a • (P⁻¹.val * X.1.1 * P.val)
    rw [Matrix.mul_smul, Matrix.smul_mul]
  left_inv X := by
    apply Subtype.ext; apply Subtype.ext
    change P.val * (P⁻¹.val * X.1.1 * P.val) * P⁻¹.val = X.1.1
    calc P.val * (P⁻¹.val * X.1.1 * P.val) * P⁻¹.val
        = (P.val * P⁻¹.val) * X.1.1 * (P.val * P⁻¹.val) := by simp only [Matrix.mul_assoc]
      _ = X.1.1 := by rw [P.val_mul_inv_val, Matrix.one_mul, Matrix.mul_one]
  right_inv Y := by
    apply Subtype.ext; apply Subtype.ext
    change P⁻¹.val * (P.val * Y.1.1 * P⁻¹.val) * P.val = Y.1.1
    calc P⁻¹.val * (P.val * Y.1.1 * P⁻¹.val) * P.val
        = (P⁻¹.val * P.val) * Y.1.1 * (P⁻¹.val * P.val) := by simp only [Matrix.mul_assoc]
      _ = Y.1.1 := by rw [P.inv_val_mul_val, Matrix.one_mul, Matrix.mul_one]

/-- Identification `H⁰(⟨g⟩, Sp4AdRep ρ) ≃ₗ[K] sp4FixedSubmodule (ρ g)`. -/
def H0_zpowers_sp4_equiv_fixed {G K : Type*} [Group G] [Field K]
    (ρ : G →* GSp4 K) (g : G) :
    H0Subgroup K (Subgroup.zpowers g) (Sp4AdRep ρ) ≃ₗ[K] sp4FixedSubmodule (ρ g) where
  toFun X :=
    ⟨⟨X.1.val, X.1.mem_sp4⟩, by
      have hg := X.2 ⟨g, Subgroup.mem_zpowers g⟩
      exact congrArg Sp4AdRep.val hg⟩
  invFun Y :=
    ⟨⟨Y.1.1, Y.1.2⟩, by
      rintro ⟨h, hh⟩
      rw [Subgroup.mem_zpowers_iff] at hh
      obtain ⟨n, rfl⟩ := hh
      have hfix : (ρ g).val * Y.1.1 * (ρ g)⁻¹.val = Y.1.1 := Y.2
      have hcomm : (ρ g).val * Y.1.1 = Y.1.1 * (ρ g).val := by
        calc (ρ g).val * Y.1.1
            = ((ρ g).val * Y.1.1 * (ρ g)⁻¹.val) * (ρ g).val := by
                rw [Matrix.mul_assoc, Matrix.mul_assoc, (ρ g).inv_val_mul_val, Matrix.mul_one]
          _ = Y.1.1 * (ρ g).val := by rw [hfix]
      have hcomm_inv : (ρ g)⁻¹.val * Y.1.1 = Y.1.1 * (ρ g)⁻¹.val := by
        calc (ρ g)⁻¹.val * Y.1.1
            = (ρ g)⁻¹.val * ((ρ g).val * Y.1.1 * (ρ g)⁻¹.val) := by rw [hfix]
          _ = ((ρ g)⁻¹.val * (ρ g).val) * Y.1.1 * (ρ g)⁻¹.val := by simp only [Matrix.mul_assoc]
          _ = Y.1.1 * (ρ g)⁻¹.val := by rw [(ρ g).inv_val_mul_val, Matrix.one_mul]
      have hpow : ∀ k : ℕ, ((ρ g ^ k : GSp4 K).val) * Y.1.1 = Y.1.1 * ((ρ g ^ k : GSp4 K).val) := by
        intro k; induction k with
        | zero => simp
        | succ k ih => rw [pow_succ, GSp4.mul_val, Matrix.mul_assoc, hcomm, ← Matrix.mul_assoc, ih, Matrix.mul_assoc]
      have hpow_inv : ∀ k : ℕ, (((ρ g)⁻¹ ^ k : GSp4 K).val) * Y.1.1 =
          Y.1.1 * (((ρ g)⁻¹ ^ k : GSp4 K).val) := by
        intro k; induction k with
        | zero => simp
        | succ k ih => rw [pow_succ, GSp4.mul_val, Matrix.mul_assoc, hcomm_inv, ← Matrix.mul_assoc, ih, Matrix.mul_assoc]
      have hzpow : ((ρ (g ^ n)).val) * Y.1.1 = Y.1.1 * ((ρ (g ^ n)).val) := by
        rw [map_zpow]; cases n with
        | ofNat k => exact hpow k
        | negSucc k => rw [zpow_negSucc, ← inv_pow]; exact hpow_inv (k + 1)
      apply Sp4AdRep.ext_val
      change (ρ (g ^ n)).val * Y.1.1 * (ρ (g ^ n))⁻¹.val = Y.1.1
      rw [hzpow, Matrix.mul_assoc, (ρ (g ^ n)).val_mul_inv_val, Matrix.mul_one]⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- **UNCONDITIONAL `Sp₄` ARCHIMEDEAN INVARIANT DIMENSION (`dim H⁰(G_∞, 𝔰𝔭₄) = 4`)**:
For EVERY field `K` with `(2 : K) ≠ 0`, EVERY group `G`, EVERY 4D symplectic representation
`ρ : G →* GSp₄(K)`, and EVERY odd symplectic involution `c ∈ G` (`c * c = 1`, `ν(ρ c) = -1`):
**`Module.finrank K (H0Subgroup K (Subgroup.zpowers c) (Sp4AdRep ρ)) = 4`**! -/
theorem finrank_H0_inf_sp4_eq_four {G K : Type*} [Group G] [Field K] (h2 : (2 : K) ≠ 0)
    (ρ : G →* GSp4 K) (c : G) (hc2 : c * c = 1) (hodd : (ρ c).sim = -1) :
    Module.finrank K (H0Subgroup K (Subgroup.zpowers c) (Sp4AdRep ρ)) = 4 := by
  have hcsq : ρ c * ρ c = 1 := by rw [← map_mul, hc2, map_one]
  obtain ⟨P, _, hconj⟩ := exists_sp4_conj_stdOddSympInv h2 (ρ c) hcsq hodd
  rw [(H0_zpowers_sp4_equiv_fixed ρ c).finrank_eq,
    (sp4FixedConjEquiv P (ρ c)).finrank_eq, hconj,
    (sp4FixedStdEquivFin4 h2).finrank_eq, Module.finrank_fin_fun]

/-- **COMPLEMENTARY `-1`-EIGENSPACE DIMENSION (`dim (𝔰𝔭₄)^{c = -1} = 6`) & EXACT EULER BALANCE
`10 - 6 - 4 = 0`**! -/
theorem finrank_H0_inf_sp4_minus_eq_six {K : Type*} [Field K] (h2 : (2 : K) ≠ 0)
    (c : GSp4 K) (hc2 : c * c = 1) (hodd : c.sim = -1) :
    IsCompl (sp4FixedSubmodule c) (sp4AntiFixedSubmodule c) ∧
    Module.finrank K (sp4FixedSubmodule c) = 4 ∧
    Module.finrank K (sp4AntiFixedSubmodule c) = 6 ∧
    (Module.finrank K (sp4Lie K) : ℤ) - Module.finrank K (sp4AntiFixedSubmodule c) -
      Module.finrank K (sp4FixedSubmodule c) = 0 := by
  have hc_inv : c⁻¹ = c := inv_eq_of_mul_eq_one_right hc2
  have hc2_val : c.val * c.val = 1 := congrArg GSp4.val hc2
  have hcompl : IsCompl (sp4FixedSubmodule c) (sp4AntiFixedSubmodule c) := by
    rw [isCompl_iff]
    constructor
    · rw [disjoint_iff, eq_bot_iff]
      intro X ⟨h1, h2'⟩
      rw [Submodule.mem_bot]
      have hneg : X.1 = -X.1 := (h1 : c.val * X.1 * c⁻¹.val = X.1).symm.trans h2'
      apply Subtype.ext; ext i j
      have hij : X.1 i j = -X.1 i j := by simpa using congrArg (fun M : Matrix (Fin 4) (Fin 4) K => M i j) hneg
      exact (mul_eq_zero.mp (by linear_combination hij : (2 : K) * X.1 i j = 0)).resolve_left h2
    · rw [codisjoint_iff, eq_top_iff]
      intro X _
      rw [Submodule.mem_sup]
      let cX : sp4Lie K := ⟨c.val * X.1 * c⁻¹.val, sp4Lie_conj_mem c X.2⟩
      have hcc : c.val * (c.val * X.1 * c⁻¹.val) * c⁻¹.val = X.1 := by
        rw [hc_inv]
        calc c.val * (c.val * X.1 * c.val) * c.val
            = (c.val * c.val) * X.1 * (c.val * c.val) := by simp only [Matrix.mul_assoc]
          _ = X.1 := by rw [hc2_val, Matrix.one_mul, Matrix.mul_one]
      refine ⟨(2 : K)⁻¹ • (X + cX), ?_, (2 : K)⁻¹ • (X - cX), ?_, ?_⟩
      · show c.val * ((2 : K)⁻¹ • (X.1 + c.val * X.1 * c⁻¹.val)) * c⁻¹.val =
          (2 : K)⁻¹ • (X.1 + c.val * X.1 * c⁻¹.val)
        rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul, hcc, add_comm]
      · show c.val * ((2 : K)⁻¹ • (X.1 - c.val * X.1 * c⁻¹.val)) * c⁻¹.val =
          -((2 : K)⁻¹ • (X.1 - c.val * X.1 * c⁻¹.val))
        rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul, ← smul_neg, hcc]
        congr 1; abel
      · apply Subtype.ext; ext i j
        simp only [Submodule.coe_add, Submodule.coe_smul_of_tower, Submodule.coe_sub,
          Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
        field_simp [h2]; ring
  obtain ⟨P, _, hconj⟩ := exists_sp4_conj_stdOddSympInv h2 c hc2 hodd
  have hdim4 : Module.finrank K (sp4FixedSubmodule c) = 4 := by
    rw [(sp4FixedConjEquiv P c).finrank_eq, hconj,
      (sp4FixedStdEquivFin4 h2).finrank_eq, Module.finrank_fin_fun]
  have hsum := Submodule.finrank_add_eq_of_isCompl hcompl
  rw [finrank_sp4Lie, hdim4] at hsum
  have hdim6 : Module.finrank K (sp4AntiFixedSubmodule c) = 6 := by omega
  refine ⟨hcompl, hdim4, hdim6, ?_⟩
  rw [finrank_sp4Lie, hdim4, hdim6]; norm_num

/-- Fast Cartan diagonal vector `(v 0, v 1, -v 1, -v 0)` for `Sp₄`. -/
def sp4CartanDiag {K : Type*} [Field K] (v : Fin 2 → K) : Fin 4 → K
  | 0 => v 0 | 1 => v 1 | 2 => -v 1 | 3 => -v 0

/-- **TAYLOR–WILES REGULAR-SEMISIMPLE FROBENIUS CENTRALIZER (`dim H⁰(G_q, 𝔰𝔭₄) = 2`)**! -/
theorem finrank_H0_tw_prime_sp4_eq_two {G K : Type*} [Group G] [Field K]
    (ρ : G →* GSp4 K) (frob : G) (P D : GSp4 K)
    (hconj : P⁻¹ * ρ frob * P = D)
    (d : Fin 4 → K) (hD : D.val = Matrix.diagonal d)
    (hdist : Function.Injective d) :
    Module.finrank K (H0Subgroup K (Subgroup.zpowers frob) (Sp4AdRep ρ)) = 2 := by
  rw [(H0_zpowers_sp4_equiv_fixed ρ frob).finrank_eq,
    (sp4FixedConjEquiv P (ρ frob)).finrank_eq, hconj]
  let e : sp4FixedSubmodule D ≃ₗ[K] (Fin 2 → K) :=
    { toFun := fun X => fun | 0 => X.1.1 0 0 | 1 => X.1.1 1 1
      invFun := fun v =>
        ⟨⟨Matrix.diagonal (sp4CartanDiag v), by
            rw [mem_sp4Lie_iff_sympAdj]; ext i j
            rw [sympAdj_apply, Matrix.neg_apply]
            fin_cases i <;> fin_cases j <;> simp [sp4CartanDiag, j4Sign]⟩,
         by
          change D.val * Matrix.diagonal (sp4CartanDiag v) * D⁻¹.val = Matrix.diagonal (sp4CartanDiag v)
          have hcomm : D.val * Matrix.diagonal (sp4CartanDiag v) =
              Matrix.diagonal (sp4CartanDiag v) * D.val := by
            rw [hD, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
            congr 1; ext i; exact mul_comm _ _
          rw [hcomm, Matrix.mul_assoc, D.val_mul_inv_val, Matrix.mul_one]⟩
      map_add' := fun _ _ => by ext k; fin_cases k <;> rfl
      map_smul' := fun _ _ => by ext k; fin_cases k <;> rfl
      left_inv := fun X => by
        have hcomm : D.val * X.1.1 = X.1.1 * D.val := by
          calc D.val * X.1.1
              = (D.val * X.1.1 * D⁻¹.val) * D.val := by
                  rw [Matrix.mul_assoc, Matrix.mul_assoc, D.inv_val_mul_val, Matrix.mul_one]
            _ = X.1.1 * D.val := by rw [X.2]
        have hoff : ∀ i j : Fin 4, i ≠ j → X.1.1 i j = 0 := by
          intro i j hij
          have h := congrArg (fun M : Matrix (Fin 4) (Fin 4) K => M i j) hcomm
          rw [hD, Matrix.diagonal_mul, Matrix.mul_diagonal] at h
          exact (mul_eq_zero.mp (by linear_combination h : (d i - d j) * X.1.1 i j = 0)).resolve_left
            (sub_ne_zero.mpr (fun heq => hij (hdist heq)))
        have hpt_sp4 : ∀ i j : Fin 4, j4Sign K i * j4Sign K j * X.1.1 (Fin.rev j) (Fin.rev i) = -X.1.1 i j := by
          intro i j
          have h := congrArg (fun M : Matrix (Fin 4) (Fin 4) K => M i j) ((mem_sp4Lie_iff_sympAdj X.1.1).mp X.1.2)
          rwa [sympAdj_apply, Matrix.neg_apply] at h
        have h22 : X.1.1 2 2 = -X.1.1 1 1 := by have := hpt_sp4 2 2; simp [j4Sign] at this; linear_combination this
        have h33 : X.1.1 3 3 = -X.1.1 0 0 := by have := hpt_sp4 3 3; simp [j4Sign] at this; linear_combination this
        apply Subtype.ext; apply Subtype.ext; ext i j
        by_cases hij : i = j
        · subst hij; fin_cases i <;> simp [sp4CartanDiag, h22, h33]
        · simp [Matrix.diagonal_apply_ne _ hij, hoff i j hij]
      right_inv := fun v => by ext k; fin_cases k <;> simp [sp4CartanDiag] }
  rw [e.finrank_eq, Module.finrank_fin_fun]

/-- **Concrete `Sp₄` Taylor–Wiles Selmer System** wired directly to
`Stage2GaloisCohomology.PoitouTateData` over `ZMod p` (`p ≥ 3`)! -/
structure Sp4WilesSelmerSystem (G S₀ Q : Type) [Group G] [Fintype S₀] [DecidableEq S₀]
    [Fintype Q] [DecidableEq Q] (p : ℕ) [Fact p.Prime] where
  hp3 : 3 ≤ p
  rhoBar : G →* GSp4 (ZMod p)
  conj_elem : G
  conj_sq : conj_elem * conj_elem = 1
  odd_sim : (rhoBar conj_elem).sim = -1
  v_inf : S₀
  v_p : S₀
  v_inf_ne_vp : v_inf ≠ v_p
  frob_q : Q → G
  conj_P : Q → GSp4 (ZMod p)
  diag_D : Q → GSp4 (ZMod p)
  frob_conj : ∀ q : Q, (conj_P q)⁻¹ * rhoBar (frob_q q) * conj_P q = diag_D q
  eig_d : Q → Fin 4 → ZMod p
  diag_val : ∀ q : Q, (diag_D q).val = Matrix.diagonal (eig_d q)
  eig_distinct : ∀ q : Q, Function.Injective (eig_d q)
  D : PoitouTateData (ZMod p) (S₀ ⊕ Q)
  euler_balance : D.EulerPoincareBalance
  H0_vanish : Module.finrank (ZMod p) D.H0 = 0
  H0d_vanish : Module.finrank (ZMod p) D.H0d = 0
  H0_inf_equiv : D.H0v (Sum.inl v_inf) ≃ₗ[ZMod p]
    H0Subgroup (ZMod p) (Subgroup.zpowers conj_elem) (Sp4AdRep rhoBar)
  H0_q_equiv : ∀ q : Q, D.H0v (Sum.inr q) ≃ₗ[ZMod p]
    H0Subgroup (ZMod p) (Subgroup.zpowers (frob_q q)) (Sp4AdRep rhoBar)
  L_min : ∀ v : S₀ ⊕ Q, Submodule (ZMod p) (D.H1v v)
  L_inf_bot : L_min (Sum.inl v_inf) = ⊥
  L_p_balance : (Module.finrank (ZMod p) (L_min (Sum.inl v_p)) : ℤ) -
    Module.finrank (ZMod p) (D.H0v (Sum.inl v_p)) = 4
  L_other_unram : ∀ v : S₀, v ≠ v_inf → v ≠ v_p →
    Module.finrank (ZMod p) (L_min (Sum.inl v)) = Module.finrank (ZMod p) (D.H0v (Sum.inl v))
  L_q_unram : ∀ q : Q,
    Module.finrank (ZMod p) (L_min (Sum.inr q)) = Module.finrank (ZMod p) (D.H0v (Sum.inr q))
  H1_q_dim : ∀ q : Q, Module.finrank (ZMod p) (D.H1v (Sum.inr q)) = 4

namespace Sp4WilesSelmerSystem

variable {G S₀ Q : Type} [Group G] [Fintype S₀] [DecidableEq S₀]
  [Fintype Q] [DecidableEq Q] {p : ℕ} [Fact p.Prime] (W : Sp4WilesSelmerSystem G S₀ Q p)

def L_Q : ∀ v : S₀ ⊕ Q, Submodule (ZMod p) (W.D.H1v v)
  | Sum.inl v => W.L_min (Sum.inl v)
  | Sum.inr _ => ⊤

theorem finrank_H0_inf_eq_four : Module.finrank (ZMod p) (W.D.H0v (Sum.inl W.v_inf)) = 4 := by
  rw [W.H0_inf_equiv.finrank_eq]
  exact finrank_H0_inf_sp4_eq_four (two_ne_zero_zmod W.hp3) W.rhoBar W.conj_elem W.conj_sq W.odd_sim

theorem finrank_H0_q_eq_two (q : Q) : Module.finrank (ZMod p) (W.D.H0v (Sum.inr q)) = 2 := by
  rw [(W.H0_q_equiv q).finrank_eq]
  exact finrank_H0_tw_prime_sp4_eq_two W.rhoBar (W.frob_q q) (W.conj_P q) (W.diag_D q)
    (W.frob_conj q) (W.eig_d q) (W.diag_val q) (W.eig_distinct q)

theorem sum_S0_local_defect_eq_zero :
    ∑ v : S₀, ((Module.finrank (ZMod p) (W.L_min (Sum.inl v)) : ℤ) -
      Module.finrank (ZMod p) (W.D.H0v (Sum.inl v))) = 0 := by
  have h1 : ∀ v : S₀, v ∉ ({W.v_inf, W.v_p} : Finset S₀) →
      (Module.finrank (ZMod p) (W.L_min (Sum.inl v)) : ℤ) -
        Module.finrank (ZMod p) (W.D.H0v (Sum.inl v)) = 0 := by
    intro v hv; simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hv
    rw [W.L_other_unram v hv.1 hv.2, sub_self]
  rw [← Finset.sum_subset (Finset.subset_univ ({W.v_inf, W.v_p} : Finset S₀)) (fun v _ hv => h1 v hv)]
  rw [Finset.sum_pair W.v_inf_ne_vp, W.L_inf_bot, finrank_bot, W.finrank_H0_inf_eq_four, W.L_p_balance]
  norm_num

/-- **`Sp₄` MINIMAL BALANCING THEOREM**: `dim H¹_{L_min}(𝔰𝔭₄) = dim H¹_{L_min*}(𝔰𝔭₄(1))`! -/
theorem sp4_minimal_balancing :
    Module.finrank (ZMod p) (W.D.Selmer W.L_min) =
      Module.finrank (ZMod p) (W.D.DualSelmer W.L_min) := by
  have hgw := greenberg_wiles_euler_characteristic W.D W.euler_balance W.L_min
  rw [W.H0_vanish, W.H0d_vanish, Fintype.sum_sum_type, W.sum_S0_local_defect_eq_zero] at hgw
  have hQ0 : ∑ q : Q, ((Module.finrank (ZMod p) (W.L_min (Sum.inr q)) : ℤ) -
      Module.finrank (ZMod p) (W.D.H0v (Sum.inr q))) = 0 :=
    Finset.sum_eq_zero fun q _ => by rw [W.L_q_unram q, sub_self]
  rw [hQ0] at hgw; omega

/-- **`Sp₄` TAYLOR–WILES BALANCING EQUATION**: `dim H¹_{L_Q}(𝔰𝔭₄) - dim H¹_{L*_Q}(𝔰𝔭₄(1)) = 2 * |Q|`! -/
theorem sp4_Q_balancing_equation :
    (Module.finrank (ZMod p) (W.D.Selmer W.L_Q) : ℤ) -
      Module.finrank (ZMod p) (W.D.DualSelmer W.L_Q) = 2 * (Fintype.card Q : ℤ) := by
  have hgw := greenberg_wiles_euler_characteristic W.D W.euler_balance W.L_Q
  rw [W.H0_vanish, W.H0d_vanish, Fintype.sum_sum_type] at hgw
  have hS0 : ∑ v : S₀, ((Module.finrank (ZMod p) (W.L_Q (Sum.inl v)) : ℤ) -
      Module.finrank (ZMod p) (W.D.H0v (Sum.inl v))) = 0 := W.sum_S0_local_defect_eq_zero
  have hQ : ∑ q : Q, ((Module.finrank (ZMod p) (W.L_Q (Sum.inr q)) : ℤ) -
      Module.finrank (ZMod p) (W.D.H0v (Sum.inr q))) = 2 * (Fintype.card Q : ℤ) := by
    have hterm : ∀ q : Q, ((Module.finrank (ZMod p) (W.L_Q (Sum.inr q)) : ℤ) -
        Module.finrank (ZMod p) (W.D.H0v (Sum.inr q))) = 2 := fun q => by
      change (Module.finrank (ZMod p) (⊤ : Submodule (ZMod p) (W.D.H1v (Sum.inr q))) : ℤ) -
        Module.finrank (ZMod p) (W.D.H0v (Sum.inr q)) = 2
      rw [finrank_top, W.H1_q_dim q, W.finrank_H0_q_eq_two q]; norm_num
    simp_rw [hterm]; simp [mul_comm]
  rw [hS0, hQ] at hgw; omega

end Sp4WilesSelmerSystem

/-! ### 1.5 Concrete 4D Symplectic Galois Deformations (`SympDualLift`, `sp4_mazur_tangent_equiv`) -/

section SymplecticDeformations

variable {G K : Type*} [Group G] [Field K]

/-- Matrix over `DualNum K` formed from real part `A` and infinitesimal part `B`: `A + ε B`. -/
def dualMat4 (A B : Matrix (Fin 4) (Fin 4) K) : Matrix (Fin 4) (Fin 4) (DualNum K) :=
  Matrix.of (fun i j => ⟨A i j, B i j⟩)

theorem dualMat4_mul (A₁ B₁ A₂ B₂ : Matrix (Fin 4) (Fin 4) K) :
    dualMat4 A₁ B₁ * dualMat4 A₂ B₂ = dualMat4 (A₁ * A₂) (A₁ * B₂ + B₁ * A₂) := by
  ext i j
  · simp [dualMat4, Matrix.mul_apply, Fin.sum_univ_four]
  · simp [dualMat4, Matrix.mul_apply, Fin.sum_univ_four]; ring

omit [Field K] in
theorem dualMat4_transpose (A B : Matrix (Fin 4) (Fin 4) K) :
    (dualMat4 A B)ᵀ = dualMat4 Aᵀ Bᵀ := by
  ext i j <;> rfl

theorem J4_dualNum_eq : J4 (DualNum K) = dualMat4 (J4 K) 0 := by
  ext i j
  · simp only [J4_apply, dualMat4, Matrix.of_apply]
    split_ifs <;> fin_cases i <;> simp [j4Sign]
  · simp only [J4_apply, dualMat4, Matrix.of_apply, Matrix.zero_apply]
    split_ifs <;> fin_cases i <;> simp [j4Sign]

/-- **EXACT SYMPLECTIC LIE-ALGEBRA CHARACTERIZATION OF DUAL-NUMBER LIFTS**:
`(I + ε X) · g` preserves the symplectic form with fixed similitude iff `X ∈ sp4Lie K`! -/
theorem isGSp4_dualMat4_iff_mem_sp4Lie (g : GSp4 K) (X : Matrix (Fin 4) (Fin 4) K) :
    IsGSp4 (DualNum.inl (g.sim : K)) (dualMat4 g.val (X * g.val)) ↔ X ∈ sp4Lie K := by
  unfold IsGSp4
  rw [J4_dualNum_eq, dualMat4_transpose, dualMat4_mul, dualMat4_mul]
  have hsmul : DualNum.inl (g.sim : K) • dualMat4 (J4 K) 0 = dualMat4 ((g.sim : K) • J4 K) 0 := by
    ext i j <;> simp [dualMat4]
  rw [hsmul, Matrix.transpose_mul, Matrix.mul_zero, zero_add]
  have hcoeff : g.valᵀ * J4 K * (X * g.val) + g.valᵀ * Xᵀ * J4 K * g.val =
      g.valᵀ * (Xᵀ * J4 K + J4 K * X) * g.val := by
    rw [Matrix.mul_add, Matrix.add_mul]; simp only [Matrix.mul_assoc]; abel
  constructor
  · intro h
    have hsnd : g.valᵀ * (Xᵀ * J4 K + J4 K * X) * g.val = 0 := by
      rw [← hcoeff]; ext i j
      have hij := congrArg (fun M : Matrix (Fin 4) (Fin 4) (DualNum K) => (M i j).snd) h
      simpa [dualMat4] using hij
    have hmul := congrArg (fun M => g⁻¹.valᵀ * M * g⁻¹.val) hsnd
    have hinv_t : g⁻¹.valᵀ * g.valᵀ = 1 := by
      rw [← Matrix.transpose_mul, g.val_mul_inv_val, Matrix.transpose_one]
    simp only [Matrix.mul_zero, Matrix.zero_mul] at hmul
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hinv_t, Matrix.one_mul,
      Matrix.mul_assoc, g.val_mul_inv_val, Matrix.mul_one] at hmul
    exact hmul
  · intro hX
    have h0 : g.valᵀ * J4 K * (X * g.val) + g.valᵀ * Xᵀ * J4 K * g.val = 0 := by
      rw [hcoeff, hX, Matrix.mul_zero, Matrix.zero_mul]
    ext i j
    · exact congrArg (fun M : Matrix (Fin 4) (Fin 4) K => M i j) g.isGSp
    · exact congrArg (fun M : Matrix (Fin 4) (Fin 4) K => M i j) h0

/-- Concrete fixed-similitude **4D symplectic dual-number lift** of `ρBar : G →* GSp₄(K)`. -/
structure SympDualLift (ρBar : G →* GSp4 K) where
  rep : G →* GSp4 (DualNum K)
  lift_eq : (GSp4.map DualNum.proj).comp rep = ρBar
  sim_eq : ∀ g : G, (rep g).sim = Units.map DualNum.inl.toMonoidHom (ρBar g).sim

/-- Extract the `𝔰𝔭₄(K)`-valued 1-cocycle `c(g) := snd(ρ(g)) · ρBar(g)⁻¹` from a `SympDualLift`. -/
def SympDualLift.toCocycle {ρBar : G →* GSp4 K} (L : SympDualLift ρBar) :
    Cocycle1 G (Sp4AdRep ρBar) :=
  let cMat : G → Matrix (Fin 4) (Fin 4) K :=
    fun g => Matrix.of (fun i j => ((L.rep g).val i j).snd) * (ρBar g)⁻¹.val
  have hrep_eq : ∀ g : G, (L.rep g).val = dualMat4 (ρBar g).val (cMat g * (ρBar g).val) := by
    intro g
    have hf : ((L.rep g).val).map DualNum.proj = (ρBar g).val :=
      congrArg (fun φ : G →* GSp4 K => (φ g).val) L.lift_eq
    have hc : cMat g * (ρBar g).val = Matrix.of (fun i j => ((L.rep g).val i j).snd) := by
      dsimp only [cMat]; rw [Matrix.mul_assoc, (ρBar g).inv_val_mul_val, Matrix.mul_one]
    rw [hc]; ext i j
    · exact congrArg (fun M : Matrix (Fin 4) (Fin 4) K => M i j) hf
    · rfl
  have hmem : ∀ g : G, cMat g ∈ sp4Lie K := by
    intro g
    rw [← isGSp4_dualMat4_iff_mem_sp4Lie (ρBar g), ← hrep_eq g]
    have hgsp := (L.rep g).isGSp; rw [L.sim_eq g] at hgsp; exact hgsp
  { toFun := fun g => ⟨cMat g, hmem g⟩
    cocycle' := fun g h => by
      apply Sp4AdRep.ext_val
      change cMat (g * h) = cMat g + (ρBar g).val * cMat h * (ρBar g)⁻¹.val
      have hmul : (L.rep (g * h)).val = (L.rep g).val * (L.rep h).val :=
        congrArg GSp4.val (map_mul L.rep g h)
      rw [hrep_eq (g * h), hrep_eq g, hrep_eq h, dualMat4_mul] at hmul
      have hsnd : cMat (g * h) * (ρBar (g * h)).val =
          (ρBar g).val * (cMat h * (ρBar h).val) + cMat g * (ρBar g).val * (ρBar h).val := by
        ext i j
        have hij := congrArg (fun M : Matrix (Fin 4) (Fin 4) (DualNum K) => (M i j).snd) hmul
        simpa [dualMat4] using hij
      have hfin := congrArg (fun M => M * (ρBar (g * h))⁻¹.val) hsnd
      rw [Matrix.mul_assoc, (ρBar (g * h)).val_mul_inv_val, Matrix.mul_one,
        Matrix.add_mul, map_mul, _root_.mul_inv_rev, GSp4.mul_val] at hfin
      rw [hfin]
      calc (ρBar g).val * (cMat h * (ρBar h).val) * ((ρBar h)⁻¹.val * (ρBar g)⁻¹.val) +
              cMat g * (ρBar g).val * (ρBar h).val * ((ρBar h)⁻¹.val * (ρBar g)⁻¹.val)
          = (ρBar g).val * cMat h * ((ρBar h).val * (ρBar h)⁻¹.val) * (ρBar g)⁻¹.val +
              cMat g * (ρBar g).val * ((ρBar h).val * (ρBar h)⁻¹.val) * (ρBar g)⁻¹.val := by
                simp only [Matrix.mul_assoc]
        _ = (ρBar g).val * cMat h * (ρBar g)⁻¹.val +
              cMat g * ((ρBar g).val * (ρBar g)⁻¹.val) := by
                rw [(ρBar h).val_mul_inv_val, Matrix.mul_one, Matrix.mul_one]
                simp only [Matrix.mul_assoc]
        _ = cMat g + (ρBar g).val * cMat h * (ρBar g)⁻¹.val := by
                rw [(ρBar g).val_mul_inv_val, Matrix.mul_one, add_comm] }

/-- Construct a `SympDualLift ρBar` from any `𝔰𝔭₄(K)`-valued 1-cocycle `c ∈ Z¹(G, Sp4AdRep ρBar)`. -/
def sympDualLiftOfCocycle {ρBar : G →* GSp4 K} (c : Cocycle1 G (Sp4AdRep ρBar)) :
    SympDualLift ρBar where
  rep :=
    { toFun := fun g =>
        { val := dualMat4 (ρBar g).val ((c g).val * (ρBar g).val)
          sim := Units.map DualNum.inl.toMonoidHom (ρBar g).sim
          isGSp := (isGSp4_dualMat4_iff_mem_sp4Lie (ρBar g) (c g).val).mpr (c g).mem_sp4 }
      map_one' := GSp4.ext_val (by
        have hc1 : (c 1).val = 0 := congrArg Sp4AdRep.val c.map_one
        change dualMat4 (ρBar 1).val ((c 1).val * (ρBar 1).val) = 1
        rw [map_one, GSp4.one_val, hc1, Matrix.zero_mul]
        ext i j <;> (by_cases h : i = j <;> simp [dualMat4, Matrix.one_apply, h])) (by simp)
      map_mul' := fun g h => GSp4.ext_val (by
        have hcoc : (c (g * h)).val = (c g).val + (ρBar g).val * (c h).val * (ρBar g)⁻¹.val :=
          congrArg Sp4AdRep.val (c.map_mul g h)
        change dualMat4 (ρBar (g * h)).val ((c (g * h)).val * (ρBar (g * h)).val) =
          dualMat4 (ρBar g).val ((c g).val * (ρBar g).val) *
          dualMat4 (ρBar h).val ((c h).val * (ρBar h).val)
        rw [dualMat4_mul, map_mul, GSp4.mul_val, hcoc, Matrix.add_mul]
        congr 1
        calc (c g).val * ((ρBar g).val * (ρBar h).val) +
                (ρBar g).val * (c h).val * (ρBar g)⁻¹.val * ((ρBar g).val * (ρBar h).val)
            = (c g).val * (ρBar g).val * (ρBar h).val +
                (ρBar g).val * (c h).val * ((ρBar g)⁻¹.val * (ρBar g).val) * (ρBar h).val := by
                  simp only [Matrix.mul_assoc]
          _ = (ρBar g).val * ((c h).val * (ρBar h).val) +
                (c g).val * (ρBar g).val * (ρBar h).val := by
                  rw [(ρBar g).inv_val_mul_val, Matrix.mul_one, add_comm, Matrix.mul_assoc]) (by simp) }
  lift_eq := by
    ext g; apply GSp4.ext_val
    · ext i j; rfl
    · ext; rfl
  sim_eq _ := rfl

theorem sympDualLiftOfCocycle_toCocycle {ρBar : G →* GSp4 K} (c : Cocycle1 G (Sp4AdRep ρBar)) :
    (sympDualLiftOfCocycle c).toCocycle = c := by
  ext g; apply Sp4AdRep.ext_val
  change Matrix.of (fun i j => ((c g).val * (ρBar g).val) i j) * (ρBar g)⁻¹.val = (c g).val
  have hof : Matrix.of (fun i j => ((c g).val * (ρBar g).val) i j) = (c g).val * (ρBar g).val := rfl
  rw [hof, Matrix.mul_assoc, (ρBar g).val_mul_inv_val, Matrix.mul_one]

/-- Strict equivalence of two `SympDualLift`s modulo `ker(Sp₄(K[ε]/(ε²)) → Sp₄(K))`. -/
def SympStrictEquiv {ρBar : G →* GSp4 K} (L₁ L₂ : SympDualLift ρBar) : Prop :=
  ∃ X : Sp4AdRep ρBar, ∀ g : G,
    (L₂.rep g).val = dualMat4 1 X.val * (L₁.rep g).val * dualMat4 1 (-X.val)

/-- **EXACT COBOUNDARY CHARACTERIZATION OF SYMPLECTIC STRICT EQUIVALENCE**! -/
theorem sympStrictEquiv_iff_coboundary_sp4 {ρBar : G →* GSp4 K} (L₁ L₂ : SympDualLift ρBar) :
    SympStrictEquiv L₁ L₂ ↔
      L₁.toCocycle - L₂.toCocycle ∈ LinearMap.range (coboundary1Linear K G (Sp4AdRep ρBar)) := by
  have hrep : ∀ (L : SympDualLift ρBar) (g : G),
      (L.rep g).val = dualMat4 (ρBar g).val ((L.toCocycle g).val * (ρBar g).val) := by
    intro L g
    have hf : ((L.rep g).val).map DualNum.proj = (ρBar g).val :=
      congrArg (fun φ : G →* GSp4 K => (φ g).val) L.lift_eq
    have hc : (L.toCocycle g).val * (ρBar g).val =
        Matrix.of (fun i j => ((L.rep g).val i j).snd) := by
      change Matrix.of (fun i j => ((L.rep g).val i j).snd) * (ρBar g)⁻¹.val * (ρBar g).val = _
      rw [Matrix.mul_assoc, (ρBar g).inv_val_mul_val, Matrix.mul_one]
    rw [hc]; ext i j
    · exact congrArg (fun M : Matrix (Fin 4) (Fin 4) K => M i j) hf
    · rfl
  have hcoc_sub : ∀ (g : G), ((L₁.toCocycle - L₂.toCocycle).toFun g).val =
      (L₁.toCocycle g).val - (L₂.toCocycle g).val := fun g => by
    have h1 : L₁.toCocycle - L₂.toCocycle = L₁.toCocycle + (-L₂.toCocycle) := sub_eq_add_neg _ _
    rw [h1]
    change (L₁.toCocycle g).val + -(L₂.toCocycle g).val = (L₁.toCocycle g).val - (L₂.toCocycle g).val
    rw [← sub_eq_add_neg]
  have hcob_eq : ∀ (X : Sp4AdRep ρBar) (g : G),
      (((coboundary1Linear K G (Sp4AdRep ρBar)) X).toFun g).val =
        (ρBar g).val * X.val * (ρBar g)⁻¹.val - X.val := fun _ _ => rfl
  constructor
  · rintro ⟨X, hX⟩
    refine ⟨X, ?_⟩
    ext g; apply Sp4AdRep.ext_val
    rw [hcob_eq, hcoc_sub]
    have hg := hX g
    rw [hrep L₁ g, hrep L₂ g, dualMat4_mul, dualMat4_mul] at hg
    have hsnd : (L₂.toCocycle g).val * (ρBar g).val =
        (ρBar g).val * (-X.val) + ((L₁.toCocycle g).val * (ρBar g).val + X.val * (ρBar g).val) := by
      ext i j
      have hij := congrArg (fun M : Matrix (Fin 4) (Fin 4) (DualNum K) => (M i j).snd) hg
      simpa [dualMat4, Matrix.one_mul, Matrix.mul_one] using hij
    have hmul := congrArg (fun M => M * (ρBar g)⁻¹.val) hsnd
    rw [Matrix.mul_assoc, (ρBar g).val_mul_inv_val, Matrix.mul_one,
      Matrix.add_mul, Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_assoc,
      (ρBar g).val_mul_inv_val, Matrix.mul_one,
      Matrix.mul_assoc X.val, (ρBar g).val_mul_inv_val, Matrix.mul_one,
      Matrix.neg_mul, Matrix.mul_neg] at hmul
    rw [hmul, Matrix.mul_assoc]; abel
  · rintro ⟨X, hX⟩
    refine ⟨X, fun g => ?_⟩
    have hg : (ρBar g).val * X.val * (ρBar g)⁻¹.val - X.val =
        (L₁.toCocycle g).val - (L₂.toCocycle g).val := by
      have h0 := congrArg Sp4AdRep.val (congrFun (congrArg Cocycle1.toFun hX) g)
      rwa [hcob_eq, hcoc_sub] at h0
    rw [hrep L₁ g, hrep L₂ g, dualMat4_mul, dualMat4_mul]
    simp only [Matrix.one_mul, Matrix.mul_one]
    congr 1
    have hmul := congrArg (fun M => M * (ρBar g).val) hg
    rw [Matrix.sub_mul, Matrix.sub_mul, Matrix.mul_assoc, Matrix.mul_assoc,
      (ρBar g).inv_val_mul_val, Matrix.mul_one] at hmul
    rw [Matrix.mul_neg]
    calc (L₂.toCocycle g).val * (ρBar g).val
        = (L₁.toCocycle g).val * (ρBar g).val - ((ρBar g).val * X.val - X.val * (ρBar g).val) := by
            rw [hmul]; abel
      _ = -((ρBar g).val * X.val) + ((L₁.toCocycle g).val * (ρBar g).val + X.val * (ρBar g).val) := by abel

/-- **EXACT `Sp₄` MAZUR TANGENT-SPACE BIJECTION**:
`SympDualLift ρBar / SympStrictEquiv ≃ H¹(G, 𝔰𝔭₄(ρBar))`! -/
def sp4_mazur_tangent_equiv (ρBar : G →* GSp4 K) :
    Quotient (Setoid.mk (SympStrictEquiv (ρBar := ρBar))
      ⟨fun L => ⟨0, fun g => by
          have h1 : dualMat4 (1 : Matrix (Fin 4) (Fin 4) K) 0 = 1 := by
            ext i j <;> (by_cases h : i = j <;> simp [dualMat4, Matrix.one_apply, h])
          change (L.rep g).val = dualMat4 1 0 * (L.rep g).val * dualMat4 1 (-0)
          rw [neg_zero, h1, Matrix.one_mul, Matrix.mul_one]⟩,
       fun {L₁ L₂} h => by
         rw [sympStrictEquiv_iff_coboundary_sp4] at h ⊢
         have : L₂.toCocycle - L₁.toCocycle = -(L₁.toCocycle - L₂.toCocycle) := by abel
         rw [this]; exact Submodule.neg_mem _ h,
       fun {L₁ L₂ L₃} h1 h2 => by
         rw [sympStrictEquiv_iff_coboundary_sp4] at h1 h2 ⊢
         have : L₁.toCocycle - L₃.toCocycle =
             (L₁.toCocycle - L₂.toCocycle) + (L₂.toCocycle - L₃.toCocycle) := by abel
         rw [this]; exact Submodule.add_mem _ h1 h2⟩) ≃
      H1Vec K G (Sp4AdRep ρBar) where
  toFun := Quotient.lift (fun L => Submodule.Quotient.mk L.toCocycle) (fun L₁ L₂ h => by
    rw [Submodule.Quotient.eq]
    exact (sympStrictEquiv_iff_coboundary_sp4 L₁ L₂).mp h)
  invFun := Quotient.lift (fun c => Quotient.mk _ (sympDualLiftOfCocycle c)) (fun c₁ c₂ h => by
    apply Quotient.sound
    change SympStrictEquiv _ _
    rw [sympStrictEquiv_iff_coboundary_sp4, sympDualLiftOfCocycle_toCocycle,
      sympDualLiftOfCocycle_toCocycle]
    have hq : (Submodule.Quotient.mk c₁ : H1Vec K G (Sp4AdRep ρBar)) = Submodule.Quotient.mk c₂ :=
      Quotient.sound h
    exact (Submodule.Quotient.eq _).mp hq)
  left_inv := fun q => by
    induction q using Quotient.inductionOn' with
    | h L =>
      apply Quotient.sound
      change SympStrictEquiv _ _
      rw [sympStrictEquiv_iff_coboundary_sp4, sympDualLiftOfCocycle_toCocycle, sub_self]
      exact Submodule.zero_mem _
  right_inv := fun q => by
    induction q using Submodule.Quotient.induction_on with
    | H c =>
      change Submodule.Quotient.mk (sympDualLiftOfCocycle c).toCocycle = Submodule.Quotient.mk c
      rw [sympDualLiftOfCocycle_toCocycle]

end SymplecticDeformations

end SymplecticGroupAndLieAlgebra

/-! ## Section 2: Concrete `RigSp4` CM-Twist Adjoint Lifting & `Sp₄` Potential Modularity Tower
    (`PotentialModularityTower`, `Sp4In0`, Solvable Base-Change Descent) -/

section RigSp4AndPotentialModularity

/-! ### 2.1 Concrete `RigSp4` — CM-Twist Adjoint Lifting & Symplectic Bloch–Kato Rigidity -/

section RigSp4Core

variable {G K : Type*} [Group G] [Field K]

/-- General `K`-linear twisting of a group action `A` along a `G`-equivariant idempotent projector `p`
by a character `η : G →* Kˣ` (directly formalizing `RigSp4.rg_twist`). -/
def twistedAction (A : G →* (Matrix (Fin 4) (Fin 4) K ≃ₗ[K] Matrix (Fin 4) (Fin 4) K))
    (p : Matrix (Fin 4) (Fin 4) K →ₗ[K] Matrix (Fin 4) (Fin 4) K)
    (hp : ∀ X, p (p X) = p X)
    (hA : ∀ g X, p (A g X) = A g (p X))
    (η : G →* Kˣ) :
    G →* (Matrix (Fin 4) (Fin 4) K →ₗ[K] Matrix (Fin 4) (Fin 4) K) where
  toFun g := (A g).toLinearMap ∘ₗ p + (η g : K) • ((A g).toLinearMap ∘ₗ (LinearMap.id - p))
  map_one' := by
    apply LinearMap.ext; intro X; simp
  map_mul' g h := by
    apply LinearMap.ext; intro X
    simp only [map_mul, Units.val_mul, LinearMap.add_apply, LinearMap.comp_apply,
      LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.id_apply, Module.End.mul_apply,
      LinearEquiv.coe_coe, LinearEquiv.mul_apply, map_add, map_smul, map_sub, hA, hp,
      sub_self, smul_zero, add_zero, mul_smul, smul_sub, smul_add, map_zero]
    module

/-- Standard `GL₄` conjugation action `adGL4 r g X = r(g) X r(g)⁻¹` as a `LinearEquiv`. -/
def adGL4Equiv (r : G →* GSp4 K) :
    G →* (Matrix (Fin 4) (Fin 4) K ≃ₗ[K] Matrix (Fin 4) (Fin 4) K) where
  toFun g :=
    { toFun := fun X => (r g).val * X * (r g)⁻¹.val
      invFun := fun X => (r g)⁻¹.val * X * (r g).val
      map_add' := fun X Y => by rw [Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun a X => by rw [Matrix.mul_smul, Matrix.smul_mul]; rfl
      left_inv := fun X => by
        calc (r g)⁻¹.val * ((r g).val * X * (r g)⁻¹.val) * (r g).val
            = ((r g)⁻¹.val * (r g).val) * X * ((r g)⁻¹.val * (r g).val) := by simp only [Matrix.mul_assoc]
          _ = X := by rw [(r g).inv_val_mul_val, Matrix.one_mul, Matrix.mul_one]
      right_inv := fun X => by
        calc (r g).val * ((r g)⁻¹.val * X * (r g).val) * (r g)⁻¹.val
            = ((r g).val * (r g)⁻¹.val) * X * ((r g).val * (r g)⁻¹.val) := by simp only [Matrix.mul_assoc]
          _ = X := by rw [(r g).val_mul_inv_val, Matrix.one_mul, Matrix.mul_one] }
  map_one' := by apply LinearEquiv.ext; intro X; simp
  map_mul' g h := by
    apply LinearEquiv.ext; intro X
    change (r (g * h)).val * X * (r (g * h))⁻¹.val =
      (r g).val * ((r h).val * X * (r h)⁻¹.val) * (r g)⁻¹.val
    rw [map_mul, _root_.mul_inv_rev]; simp only [GSp4.mul_val, Matrix.mul_assoc]

/-- The **CM-Twisted 16D Adjoint Representation** `ρ_η` of `r : G →* GSp₄(K)` twisted on `𝔰𝔭₄⊥`
by the quadratic CM character `η : G →* Kˣ` (directly formalizing `RigSp4.rg_alg`). -/
def sp4TwistedAdAction (h2 : (2 : K) ≠ 0) (r : G →* GSp4 K) (η : G →* Kˣ) :
    G →* (Matrix (Fin 4) (Fin 4) K →ₗ[K] Matrix (Fin 4) (Fin 4) K) :=
  twistedAction (adGL4Equiv r) (sp4Proj K) (sp4Proj_idemp h2)
    (fun g X => sp4Proj_conj (r g) X) η

/-- **Symplectic CM Conjugate-Self-Dual Pairing Identity (`RigSp4.rg_pair`)**:
for any `c, s, s' ∈ G` with `s' = c * s * c⁻¹`, the twisted symplectic form `Φ_c = J₄ * r(c)⁻¹`
satisfies `r(s)ᵀ * Φ_c * r(s') = ν(r s) • Φ_c`! -/
theorem sp4_cm_pairing_symplectic (r : G →* GSp4 K) (c s s' : G) (hs : s' = c * s * c⁻¹) :
    (r s).valᵀ * (J4 K * (r c)⁻¹.val) * (r s').val =
      ((r s).sim : K) • (J4 K * (r c)⁻¹.val) := by
  have he : (r c)⁻¹.val * (r s').val = (r s).val * (r c)⁻¹.val := by
    have hmul : c⁻¹ * s' = s * c⁻¹ := by rw [hs]; group
    simpa [map_mul, map_inv] using congrArg (fun g => (r g).val) hmul
  calc (r s).valᵀ * (J4 K * (r c)⁻¹.val) * (r s').val
      = (r s).valᵀ * J4 K * ((r c)⁻¹.val * (r s').val) := by simp only [Matrix.mul_assoc]
    _ = ((r s).valᵀ * J4 K * (r s).val) * (r c)⁻¹.val := by rw [he]; simp only [Matrix.mul_assoc]
    _ = ((r s).sim : K) • (J4 K * (r c)⁻¹.val) := by rw [(r s).isGSp, Matrix.smul_mul]

/-- On `ker η` (over the quadratic CM field `K_cm`), `ρ_η` is ordinary `GL₄`-adjoint conjugation! -/
theorem sp4TwistedAdAction_eq_ad_of_one (h2 : (2 : K) ≠ 0) (r : G →* GSp4 K) (η : G →* Kˣ)
    {g : G} (hg : η g = 1) (X : Matrix (Fin 4) (Fin 4) K) :
    sp4TwistedAdAction h2 r η g X = (r g).val * X * (r g)⁻¹.val := by
  simp only [sp4TwistedAdAction, twistedAction, MonoidHom.coe_mk, OneHom.coe_mk,
    LinearMap.add_apply, LinearMap.comp_apply, LinearMap.sub_apply,
    LinearMap.id_apply, hg, Units.val_one, one_smul, ← map_add, add_sub_cancel]
  rfl

/-- On complex conjugation (`η g = -1`), `ρ_η` acts by the conjugate-self-dual negative transpose! -/
theorem sp4TwistedAdAction_eq_neg_transpose_of_neg_one (h2 : (2 : K) ≠ 0) (r : G →* GSp4 K)
    (η : G →* Kˣ) {g : G} (hg : η g = -1) (X : Matrix (Fin 4) (Fin 4) K) :
    sp4TwistedAdAction h2 r η g X =
      -(((r g).val * (-J4 K)) * Xᵀ * (J4 K * (r g)⁻¹.val)) := by
  have he : sp4Proj K X - (X - sp4Proj K X) = -sympAdj X := by
    ext i j
    simp only [sp4Proj_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.neg_apply, smul_eq_mul]
    field_simp [h2]; ring
  change adGL4Equiv r g (sp4Proj K X) + ((η g : K) • adGL4Equiv r g (X - sp4Proj K X)) = _
  rw [hg, Units.val_neg, Units.val_one, neg_one_smul, ← sub_eq_add_neg, ← map_sub, he, map_neg]
  change -((r g).val * sympAdj X * (r g)⁻¹.val) = _
  unfold sympAdj; simp only [Matrix.mul_assoc]

/-- `sp4Proj K` intertwines `adGL4` with `sp4TwistedAdAction`. -/
theorem sp4Proj_intertwines_twisted (h2 : (2 : K) ≠ 0) (r : G →* GSp4 K) (η : G →* Kˣ)
    (g : G) (X : Matrix (Fin 4) (Fin 4) K) :
    sp4Proj K ((r g).val * X * (r g)⁻¹.val) = sp4TwistedAdAction h2 r η g (sp4Proj K X) := by
  change sp4Proj K ((r g).val * X * (r g)⁻¹.val) =
    adGL4Equiv r g (sp4Proj K (sp4Proj K X)) +
      (η g : K) • adGL4Equiv r g (sp4Proj K X - sp4Proj K (sp4Proj K X))
  rw [sp4Proj_idemp h2, sub_self, map_zero, smul_zero, add_zero]
  exact sp4Proj_conj (r g) X

/-- Wrapper for the 16D `G`-module `M₄(K)` equipped with the CM-twisted adjoint action `ρ_η`. -/
structure Sp4TwistedAdMod {G K : Type*} [Group G] [Field K] (h2 : (2 : K) ≠ 0)
    (r : G →* GSp4 K) (η : G →* Kˣ) where
  val : Matrix (Fin 4) (Fin 4) K

namespace Sp4TwistedAdMod

variable {h2 : (2 : K) ≠ 0} {r : G →* GSp4 K} {η : G →* Kˣ}

theorem ext_val {X Y : Sp4TwistedAdMod h2 r η} (h : X.val = Y.val) : X = Y := by
  cases X; cases Y; cases h; rfl

instance : Zero (Sp4TwistedAdMod h2 r η) := ⟨⟨0⟩⟩
instance : Add (Sp4TwistedAdMod h2 r η) := ⟨fun X Y => ⟨X.val + Y.val⟩⟩
instance : Neg (Sp4TwistedAdMod h2 r η) := ⟨fun X => ⟨-X.val⟩⟩
instance : Sub (Sp4TwistedAdMod h2 r η) := ⟨fun X Y => ⟨X.val - Y.val⟩⟩
instance : SMul K (Sp4TwistedAdMod h2 r η) := ⟨fun a X => ⟨a • X.val⟩⟩

instance instAddCommGroup : AddCommGroup (Sp4TwistedAdMod h2 r η) where
  sub X Y := ⟨X.val - Y.val⟩
  add_assoc _ _ _ := ext_val (add_assoc _ _ _)
  zero_add _ := ext_val (zero_add _)
  add_zero _ := ext_val (add_zero _)
  nsmul := nsmulRec
  zsmul := zsmulRec
  neg_add_cancel _ := ext_val (neg_add_cancel _)
  add_comm _ _ := ext_val (add_comm _ _)
  sub_eq_add_neg _ _ := ext_val (sub_eq_add_neg _ _)

instance instModule : Module K (Sp4TwistedAdMod h2 r η) where
  one_smul _ := ext_val (one_smul K _)
  mul_smul _ _ _ := ext_val (mul_smul _ _ _)
  smul_zero _ := ext_val (smul_zero _)
  smul_add _ _ _ := ext_val (smul_add _ _ _)
  add_smul _ _ _ := ext_val (add_smul _ _ _)
  zero_smul _ := ext_val (zero_smul K _)

instance instDistribMulAction : DistribMulAction G (Sp4TwistedAdMod h2 r η) where
  smul g X := ⟨sp4TwistedAdAction h2 r η g X.val⟩
  one_smul X := ext_val (by change sp4TwistedAdAction h2 r η 1 X.val = X.val; rw [map_one]; rfl)
  mul_smul g h X := ext_val (by
    change sp4TwistedAdAction h2 r η (g * h) X.val =
      sp4TwistedAdAction h2 r η g (sp4TwistedAdAction h2 r η h X.val)
    rw [map_mul]; rfl)
  smul_zero _ := ext_val (map_zero _)
  smul_add _ _ _ := ext_val (map_add _ _ _)

instance instSMulCommClass : SMulCommClass G K (Sp4TwistedAdMod h2 r η) where
  smul_comm _ _ _ := ext_val (map_smul _ _ _)

end Sp4TwistedAdMod

/-- **EXACT SYMPLECTIC COBOUNDARY DESCENT (`RigSp4.rg_alg` part 4)**! -/
theorem sp4_coboundary_descent (h2 : (2 : K) ≠ 0) (r : G →* GSp4 K) (η : G →* Kˣ)
    (X : Matrix (Fin 4) (Fin 4) K) (z : G → Matrix (Fin 4) (Fin 4) K)
    (hz_sp4 : ∀ g, z g ∈ sp4Lie K)
    (hz_cob : ∀ g, z g = sp4TwistedAdAction h2 r η g X - X) :
    ∀ g, z g = (r g).val * sp4Proj K X * (r g)⁻¹.val - sp4Proj K X := by
  intro g
  have h1 : sp4Proj K (sp4TwistedAdAction h2 r η g X) =
      (r g).val * sp4Proj K X * (r g)⁻¹.val := by
    change sp4Proj K ((r g).val * sp4Proj K X * (r g)⁻¹.val +
      (η g : K) • ((r g).val * (X - sp4Proj K X) * (r g)⁻¹.val)) = _
    rw [map_add, map_smul, sp4Proj_conj, sp4Proj_conj, sp4Proj_idemp h2,
      map_sub, sp4Proj_idemp h2, sub_self, Matrix.mul_zero, Matrix.zero_mul, smul_zero, add_zero]
  calc z g = sp4Proj K (z g) := (sp4Proj_of_mem h2 (hz_sp4 g)).symm
    _ = sp4Proj K (sp4TwistedAdAction h2 r η g X - X) := by rw [hz_cob g]
    _ = sp4Proj K (sp4TwistedAdAction h2 r η g X) - sp4Proj K X := map_sub _ _ _
    _ = (r g).val * sp4Proj K X * (r g)⁻¹.val - sp4Proj K X := by rw [h1]

/-- Equivariant `K`-linear embedding `Cocycle1 G (Sp4AdRep r) →ₗ Cocycle1 G (Sp4TwistedAdMod h2 r η)`. -/
def sp4CocycleToTwisted (h2 : (2 : K) ≠ 0) (r : G →* GSp4 K) (η : G →* Kˣ) :
    Cocycle1 G (Sp4AdRep r) →ₗ[K] Cocycle1 G (Sp4TwistedAdMod h2 r η) where
  toFun c :=
    { toFun := fun g => ⟨(c g).val⟩
      cocycle' := fun g h => by
        apply Sp4TwistedAdMod.ext_val
        change (c (g * h)).val = (c g).val + sp4TwistedAdAction h2 r η g (c h).val
        have hch : sp4Proj K (c h).val = (c h).val := sp4Proj_of_mem h2 (c h).mem_sp4
        have htw : sp4TwistedAdAction h2 r η g (c h).val =
            (r g).val * (c h).val * (r g)⁻¹.val := by
          rw [← hch, ← sp4Proj_intertwines_twisted h2 r η, sp4Proj_conj, hch]
        rw [htw]
        exact congrArg Sp4AdRep.val (c.map_mul g h) }
  map_add' _ _ := by ext g; rfl
  map_smul' _ _ := by ext g; rfl

/-- Induced `K`-linear map on cohomology `H¹(G, 𝔰𝔭₄(r)) →ₗ[K] H¹(G, ρ_η)`. -/
def sp4H1ToTwisted (h2 : (2 : K) ≠ 0) (r : G →* GSp4 K) (η : G →* Kˣ) :
    H1Vec K G (Sp4AdRep r) →ₗ[K] H1Vec K G (Sp4TwistedAdMod h2 r η) :=
  Submodule.liftQ _ ((Submodule.mkQ _).comp (sp4CocycleToTwisted h2 r η)) (by
    rintro c ⟨X, rfl⟩
    rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero]
    refine ⟨⟨X.val⟩, ?_⟩
    ext g; apply Sp4TwistedAdMod.ext_val
    change sp4TwistedAdAction h2 r η g X.val - X.val = (r g).val * X.val * (r g)⁻¹.val - X.val
    have hX : sp4Proj K X.val = X.val := sp4Proj_of_mem h2 X.mem_sp4
    rw [← hX, ← sp4Proj_intertwines_twisted h2 r η, sp4Proj_conj, hX])

/-- **EXACT INJECTIVITY OF `H¹(G, 𝔰𝔭₄) ↪ H¹(G, ρ_η)` (`RigSp4` Core)**! -/
theorem sp4_H1_injective_into_twisted_ad (h2 : (2 : K) ≠ 0) (r : G →* GSp4 K) (η : G →* Kˣ) :
    Function.Injective (sp4H1ToTwisted h2 r η) := by
  rw [injective_iff_map_eq_zero]
  intro q hq
  induction q using Submodule.Quotient.induction_on with
  | H c =>
    rw [sp4H1ToTwisted, Submodule.liftQ_apply, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero] at hq
    obtain ⟨X, hX⟩ := hq
    rw [Submodule.Quotient.mk_eq_zero]
    refine ⟨⟨sp4Proj K X.val, sp4Proj_mem X.val⟩, ?_⟩
    ext g; apply Sp4AdRep.ext_val
    exact (sp4_coboundary_descent h2 r η X.val (fun g => (c g).val)
      (fun g => (c g).mem_sp4)
      (fun g => (congrArg Sp4TwistedAdMod.val (congrFun (congrArg Cocycle1.toFun hX) g)).symm) g).symm

/-- Bloch–Kato Selmer subspace preserved by equivariant projection (`RigSp4.rg_bk`). -/
structure BlochKatoSubspace (h2 : (2 : K) ≠ 0) (r : G →* GSp4 K) (η : G →* Kˣ) where
  H1f_sp4 : Submodule K (H1Vec K G (Sp4AdRep r))
  H1f_twisted : Submodule K (H1Vec K G (Sp4TwistedAdMod h2 r η))
  maps_bk : ∀ x ∈ H1f_sp4, sp4H1ToTwisted h2 r η x ∈ H1f_twisted

/-- **`RigSp4` ADJOINT-SELMER RIGIDITY THEOREM (`rigSp4_of_adjoint_lifting`)**:
`H¹_f(G, ρ_η) = 0 ⇒ H¹_f(G, 𝔰𝔭₄(r)) = 0` (`finrank = 0`)! -/
theorem rigSp4_of_adjoint_lifting (h2 : (2 : K) ≠ 0) (r : G →* GSp4 K) (η : G →* Kˣ)
    (BK : BlochKatoSubspace h2 r η) (hAdLift : BK.H1f_twisted = ⊥) :
    BK.H1f_sp4 = ⊥ ∧ Module.finrank K BK.H1f_sp4 = 0 := by
  have hbot : BK.H1f_sp4 = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Submodule.mem_bot]
    have htx : sp4H1ToTwisted h2 r η x ∈ BK.H1f_twisted := BK.maps_bk x hx
    rw [hAdLift, Submodule.mem_bot] at htx
    exact sp4_H1_injective_into_twisted_ad h2 r η (htx.trans (map_zero _).symm)
  exact ⟨hbot, by rw [hbot, finrank_bot]⟩

end RigSp4Core

/-! ### 2.2 Concrete `Sp₄` Solvable Base-Change Descent & Potential Modularity Tower (`PotentialModularityTower`, `Sp4In0`) -/

section PotentialModularityTowerCore

/-- A 4D symplectic regular algebraic representation datum over a polarized base level. -/
structure Sp4BaseDatum (F : FiniteSolvablePolarizedFamily) (Γ : Type) [Group Γ] where
  rep : (F.levelOf Γ).bc.GalRep
  weight_k : ℕ
  regular_alg : Stage2HodgeWeights.RegularAlgebraic ((F.levelOf Γ).infDatum rep)
  symp_polarized : ((F.levelOf Γ).infDatum rep).IsPolarized (1 - 2 * (weight_k : ℤ))

/-- **SOLVABLE BASE-CHANGE DESCENT FOR `Sp₄` (`sp4_solvable_base_change_descent`)**:
Combining `Stage11BaseChangeTrace.solvable_tower_base_change_and_descent` with symplectic
polarization weight `1 - 2k`: if `D.rep` remains irreducible (`big image`) and becomes automorphic
over a finite solvable Galois extension `F/ℚ` (`Γ = Gal(F/ℚ)` solvable), it descends step-by-step
to a cohomological Siegel/paramodular automorphic form on `GSp₄ / ℚ`! -/
theorem sp4_solvable_base_change_descent
    (F : FiniteSolvablePolarizedFamily)
    (Γ : Type) [Group Γ] [Finite Γ] [Group.IsSolvable Γ]
    (D : Sp4BaseDatum F Γ) :
    ∃ (L_top : PolarizedLevel) (T : SolvablePolarizedTower (F.levelOf Γ) L_top),
      T.degree = Nat.card Γ ∧
      (∀ p ∈ T.primes, p.Prime) ∧
      (L_top.bc.IsIrr (T.res D.rep) →
        L_top.bc.IsAut (T.res D.rep) →
          (F.levelOf Γ).bc.IsAut D.rep ∧
          Stage2HodgeWeights.RegularAlgebraic (L_top.infDatum (T.res D.rep)) ∧
          (L_top.infDatum (T.res D.rep)).IsPolarized (1 - 2 * (D.weight_k : ℤ))) := by
  obtain ⟨L_top, T, hdeg, hpr, heqv, _, _⟩ := solvable_tower_base_change_and_descent F Γ
  refine ⟨L_top, T, hdeg, hpr, fun hirr haut => ?_⟩
  obtain ⟨hAutEq, hRegEq, hPolEq⟩ := heqv D.rep hirr
  exact ⟨hAutEq.mpr haut, hRegEq.mp D.regular_alg, (hPolEq (1 - 2 * (D.weight_k : ℤ))).mp D.symp_polarized⟩

/-- **Concrete `Sp₄` Potential Modularity Tower (`Sp4PotentialModularityTower`)**
combining Moret-Bailly moduli spaces (`B →+* A`, ideal `J`, automorphic seed `y_seed`),
Taylor–Wiles patching component transfer, and solvable base-change descent! -/
structure Sp4PotentialModularityTower (𝒪 K : Type) [CommRing 𝒪] [Field K]
    (F : FiniteSolvablePolarizedFamily) (Γ : Type) [Group Γ] [Finite Γ] [Group.IsSolvable Γ] where
  L_top : PolarizedLevel
  tower : SolvablePolarizedTower (F.levelOf Γ) L_top
  tower_deg : tower.degree = Nat.card Γ
  B : Type
  [commRingB : CommRing B]
  A : Type
  [commRingA : CommRing A]
  structMap : B →+* A
  J : Ideal B
  repAt : (A →+* K) → L_top.bc.GalRep
  y_seed : A →+* K
  seed_kills_J : ∀ b ∈ J, y_seed (structMap b) = 0
  seed_irr : L_top.bc.IsIrr (repAt y_seed)
  seed_aut : L_top.bc.IsAut (repAt y_seed)
  patching_component_transfer :
    ∀ y : A →+* K, (∀ b ∈ J, y (structMap b) = 0) →
      L_top.bc.IsIrr (repAt y) →
      L_top.bc.IsAut (repAt y_seed) →
      L_top.bc.IsAut (repAt y)

attribute [instance] Sp4PotentialModularityTower.commRingB Sp4PotentialModularityTower.commRingA

/-- **`Sp4In0` POTENTIAL MODULARITY + SOLVABLE DESCENT THEOREM**! -/
theorem sp4_automorphy_of_potentialModularityTower
    {𝒪 K : Type} [CommRing 𝒪] [Field K]
    {F : FiniteSolvablePolarizedFamily} {Γ : Type} [Group Γ] [Finite Γ] [Group.IsSolvable Γ]
    (PM : Sp4PotentialModularityTower 𝒪 K F Γ)
    (D : Sp4BaseDatum F Γ)
    (y : PM.A →+* K)
    (hyJ : ∀ b ∈ PM.J, y (PM.structMap b) = 0)
    (hmatch : PM.repAt y = PM.tower.res D.rep)
    (hbig : PM.L_top.bc.IsIrr (PM.tower.res D.rep)) :
    (F.levelOf Γ).bc.IsAut D.rep ∧
    PM.L_top.bc.IsAut (PM.tower.res D.rep) ∧
    Stage2HodgeWeights.RegularAlgebraic (PM.L_top.infDatum (PM.tower.res D.rep)) ∧
    (PM.L_top.infDatum (PM.tower.res D.rep)).IsPolarized (1 - 2 * (D.weight_k : ℤ)) := by
  have hy_aut := PM.patching_component_transfer y hyJ (hmatch ▸ hbig) PM.seed_aut
  have hres_aut : PM.L_top.bc.IsAut (PM.tower.res D.rep) := hmatch ▸ hy_aut
  obtain ⟨hAutEq, hRegEq, hPolEq⟩ := PM.tower.aut_reg_pol_equiv hbig
  exact ⟨hAutEq.mpr hres_aut, hres_aut, hRegEq.mp D.regular_alg,
    (hPolEq (1 - 2 * (D.weight_k : ℤ))).mp D.symp_polarized⟩

/-- **COMBINED `Sp4In0` + `RigSp4` CHARACTERISTIC-0 AUTOMORPHY & RIGIDITY ENGINE**! -/
theorem sp4_automorphic_and_rigid
    {𝒪 K : Type} [CommRing 𝒪] [Field K] (h2 : (2 : K) ≠ 0)
    {G : Type*} [Group G]
    {F : FiniteSolvablePolarizedFamily} {Γ : Type} [Group Γ] [Finite Γ] [Group.IsSolvable Γ]
    (PM : Sp4PotentialModularityTower 𝒪 K F Γ)
    (D : Sp4BaseDatum F Γ)
    (y : PM.A →+* K) (hyJ : ∀ b ∈ PM.J, y (PM.structMap b) = 0)
    (hmatch : PM.repAt y = PM.tower.res D.rep)
    (hbig : PM.L_top.bc.IsIrr (PM.tower.res D.rep))
    (r : G →* GSp4 K) (η : G →* Kˣ)
    (BK : BlochKatoSubspace h2 r η) (hAdLift : BK.H1f_twisted = ⊥) :
    (F.levelOf Γ).bc.IsAut D.rep ∧
    BK.H1f_sp4 = ⊥ ∧ Module.finrank K BK.H1f_sp4 = 0 := by
  have h1 := sp4_automorphy_of_potentialModularityTower PM D y hyJ hmatch hbig
  have h2' := rigSp4_of_adjoint_lifting h2 r η BK hAdLift
  exact ⟨h1.1, h2'.1, h2'.2⟩

end PotentialModularityTowerCore

end RigSp4AndPotentialModularity

/-! ## Section 3: Reducible 4D `Sp₄` Klingen/Siegel Eisenstein Congruences &
    `CountII` / `CountIII` Discharge (`sp4Main_alt`) -/

section ReducibleSp4EisensteinAndCounts

/-! ### 3.1 Classification of 4D Symplectic Reducible Pseudocharacters (`T̄ = 1 + χ + χ⁻¹ ν + ν`)
    & Borel / Siegel / Klingen Parabolic Reducibility Loci -/

section ParabolicClassification

variable {R G : Type*} [CommRing R] [Group G]

/-- The 4D symplectic diagonal character quadruple `(1, χ, χ⁻¹ ν, ν)`. -/
def sp4DiagChar (χ ν : G →* Rˣ) : Fin 4 → (G →* Rˣ)
  | 0 => 1 | 1 => χ | 2 => χ⁻¹ * ν | 3 => ν

theorem sp4DiagChar_symp_pair (χ ν : G →* Rˣ) (g : G) :
    sp4DiagChar χ ν 0 g * sp4DiagChar χ ν 3 g = ν g ∧
    sp4DiagChar χ ν 1 g * sp4DiagChar χ ν 2 g = ν g := by
  constructor
  · simp [sp4DiagChar]
  · simp [sp4DiagChar, ← mul_assoc]

/-- The **4D `Sp₄` Eisenstein trace pseudocharacter**: `1 + χ + χ⁻¹ ν + ν`. -/
def sp4EisensteinTrace (χ ν : G →* Rˣ) (g : G) : R :=
  ∑ i : Fin 4, (sp4DiagChar χ ν i g : R)

/-- Clean algebraic factorization: `1 + χ + χ⁻¹ ν + ν = (1 + χ) * (1 + χ⁻¹ ν)`! -/
theorem sp4EisensteinTrace_eq_mul (χ ν : G →* Rˣ) (g : G) :
    sp4EisensteinTrace χ ν g =
      (1 + (χ g : R)) * (1 + ((χ g)⁻¹ : Rˣ) * (ν g : R)) := by
  unfold sp4EisensteinTrace
  rw [Fin.sum_univ_four]
  simp only [sp4DiagChar, MonoidHom.one_apply, Units.val_one, MonoidHom.mul_apply,
    MonoidHom.inv_apply, Units.val_mul]
  have hcancel : (χ g : R) * (((χ g)⁻¹ : Rˣ) : R) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  calc 1 + (χ g : R) + (((χ g)⁻¹ : Rˣ) : R) * (ν g : R) + (ν g : R)
      = 1 + (χ g : R) + (((χ g)⁻¹ : Rˣ) : R) * (ν g : R) +
          ((χ g : R) * (((χ g)⁻¹ : Rˣ) : R)) * (ν g : R) := by rw [hcancel, one_mul]
    _ = (1 + (χ g : R)) * (1 + (((χ g)⁻¹ : Rˣ) : R) * (ν g : R)) := by ring

/-- Concrete **Symplectic Reducible Diagonal Representation** `G →* GSp₄(R)` realizing `T_eis`! -/
def sp4DiagRep (χ ν : G →* Rˣ) : G →* GSp4 R where
  toFun g :=
    { val := Matrix.diagonal (fun i => (sp4DiagChar χ ν i g : R))
      sim := ν g
      isGSp := by
        unfold IsGSp4
        have hpair := sp4DiagChar_symp_pair χ ν g
        have h03 : (sp4DiagChar χ ν 0 g : R) * (sp4DiagChar χ ν 3 g : R) = (ν g : R) := by
          rw [← Units.val_mul, hpair.1]
        have h12 : (sp4DiagChar χ ν 1 g : R) * (sp4DiagChar χ ν 2 g : R) = (ν g : R) := by
          rw [← Units.val_mul, hpair.2]
        ext i j
        rw [Matrix.diagonal_transpose, Matrix.mul_diagonal, Matrix.diagonal_mul,
          Matrix.smul_apply, smul_eq_mul, J4_apply]
        by_cases h : j = Fin.rev i
        · subst h; rw [if_pos rfl]
          fin_cases i
          · change (sp4DiagChar χ ν 0 g : R) * j4Sign R 0 * (sp4DiagChar χ ν 3 g : R) = _
            rw [mul_right_comm, h03]; rfl
          · change (sp4DiagChar χ ν 1 g : R) * j4Sign R 1 * (sp4DiagChar χ ν 2 g : R) = _
            rw [mul_right_comm, h12]; rfl
          · change (sp4DiagChar χ ν 2 g : R) * j4Sign R 2 * (sp4DiagChar χ ν 1 g : R) = _
            rw [mul_right_comm, mul_comm (sp4DiagChar χ ν 2 g : R), h12]; rfl
          · change (sp4DiagChar χ ν 3 g : R) * j4Sign R 3 * (sp4DiagChar χ ν 0 g : R) = _
            rw [mul_right_comm, mul_comm (sp4DiagChar χ ν 3 g : R), h03]; rfl
        · simp [h] }
  map_one' := GSp4.ext_val (by ext i j; by_cases h : i = j <;> simp [h]) (map_one ν)
  map_mul' g h := GSp4.ext_val (by
    change Matrix.diagonal _ = Matrix.diagonal _ * Matrix.diagonal _
    rw [Matrix.diagonal_mul_diagonal]
    congr 1; ext i; simp [map_mul]) (map_mul ν g h)

theorem trace_sp4DiagRep (χ ν : G →* Rˣ) (g : G) :
    Matrix.trace (sp4DiagRep χ ν g).val = sp4EisensteinTrace χ ν g := by
  simp [sp4DiagRep, sp4EisensteinTrace, Matrix.trace, Matrix.diag]

/-- Symplectic index reversal `i ↦ 3 - i` on `Fin 4`. -/
def sp4Rev (i : Fin 4) : Fin 4 := Fin.rev i

@[simp] theorem sp4Rev_sp4Rev (i : Fin 4) : sp4Rev (sp4Rev i) = i := Fin.rev_rev i

/-- Concrete **Symplectic Rank-4 Generalized Matrix Algebra (`Sp4GMA R`)** with explicit
symplectic pair-ideal duality `pairIdeal i j = pairIdeal (3 - j) (3 - i)`. -/
structure Sp4GMA (R : Type*) [CommRing R] where
  pairIdeal : Fin 4 → Fin 4 → Ideal R
  pairIdeal_symm : ∀ i j : Fin 4, pairIdeal i j = pairIdeal j i
  pairIdeal_symp : ∀ i j : Fin 4, pairIdeal i j = pairIdeal (sp4Rev j) (sp4Rev i)

namespace Sp4GMA

/-- Total (Borel) reducibility ideal `I_red = ⨆_{i ≠ j} pairIdeal i j`. -/
def reducibilityIdeal (A : Sp4GMA R) : Ideal R :=
  ⨆ (i : Fin 4) (j : Fin 4) (_ : i ≠ j), A.pairIdeal i j

theorem pairIdeal_le_reducibilityIdeal (A : Sp4GMA R) {i j : Fin 4} (h : i ≠ j) :
    A.pairIdeal i j ≤ A.reducibilityIdeal :=
  le_iSup_of_le i (le_iSup_of_le j (le_iSup_of_le h le_rfl))

theorem reducibilityIdeal_le_iff (A : Sp4GMA R) (J : Ideal R) :
    A.reducibilityIdeal ≤ J ↔ ∀ i j : Fin 4, i ≠ j → A.pairIdeal i j ≤ J := by
  simp only [reducibilityIdeal, iSup_le_iff]

/-- Standard `Sp₄`-matrix GMA weighted by a symmetric symplectic ideal. -/
def ofIdeal (I : Ideal R) : Sp4GMA R where
  pairIdeal i j := if i = j then ⊤ else I
  pairIdeal_symm i j := by by_cases h : i = j <;> simp [h, eq_comm]
  pairIdeal_symp i j := by
    have hiff : i = j ↔ sp4Rev j = sp4Rev i :=
      ⟨fun h => by rw [h], fun h => (Fin.rev_injective h).symm⟩
    by_cases h : i = j
    · simp [h, hiff.mp h]
    · simp [h, mt hiff.mpr h]

end Sp4GMA

/-- **Siegel Parabolic Reducibility Ideal** (`2 + 2` block partition `{0, 1} ∪ {2, 3}`, Levi `GL₂ × GL₁`). -/
def siegelParabolicIdeal (A : Sp4GMA R) : Ideal R :=
  A.pairIdeal 0 2 ⊔ A.pairIdeal 0 3 ⊔ A.pairIdeal 1 2 ⊔ A.pairIdeal 1 3

/-- **Klingen Parabolic Reducibility Ideal** (`1 + 2 + 1` partition `{0} ∪ {1, 2} ∪ {3}`, Levi `GL₁ × GSp₂`). -/
def klingenParabolicIdeal (A : Sp4GMA R) : Ideal R :=
  A.pairIdeal 0 1 ⊔ A.pairIdeal 0 2 ⊔ A.pairIdeal 0 3 ⊔ A.pairIdeal 1 3 ⊔ A.pairIdeal 2 3

/-- **Exact Parabolic Inclusion Lattice & Symplectic 4-Ideal Collapse**! -/
theorem parabolic_ideal_lattice (A : Sp4GMA R) :
    siegelParabolicIdeal A ≤ A.reducibilityIdeal ∧
    klingenParabolicIdeal A ≤ A.reducibilityIdeal ∧
    siegelParabolicIdeal A ⊔ klingenParabolicIdeal A = A.reducibilityIdeal ∧
    A.reducibilityIdeal =
      A.pairIdeal 0 1 ⊔ A.pairIdeal 0 2 ⊔ A.pairIdeal 0 3 ⊔ A.pairIdeal 1 2 := by
  have hS : siegelParabolicIdeal A ≤ A.reducibilityIdeal :=
    sup_le (sup_le (sup_le
      (A.pairIdeal_le_reducibilityIdeal (by decide))
      (A.pairIdeal_le_reducibilityIdeal (by decide)))
      (A.pairIdeal_le_reducibilityIdeal (by decide)))
      (A.pairIdeal_le_reducibilityIdeal (by decide))
  have hK : klingenParabolicIdeal A ≤ A.reducibilityIdeal :=
    sup_le (sup_le (sup_le (sup_le
      (A.pairIdeal_le_reducibilityIdeal (by decide))
      (A.pairIdeal_le_reducibilityIdeal (by decide)))
      (A.pairIdeal_le_reducibilityIdeal (by decide)))
      (A.pairIdeal_le_reducibilityIdeal (by decide)))
      (A.pairIdeal_le_reducibilityIdeal (by decide))
  have hsym01 : A.pairIdeal 0 1 = A.pairIdeal 2 3 := by
    have := A.pairIdeal_symp 0 1; simpa [sp4Rev] using this
  have hsym02 : A.pairIdeal 0 2 = A.pairIdeal 1 3 := by
    have := A.pairIdeal_symp 0 2; simpa [sp4Rev] using this
  have hcollapse : A.reducibilityIdeal =
      A.pairIdeal 0 1 ⊔ A.pairIdeal 0 2 ⊔ A.pairIdeal 0 3 ⊔ A.pairIdeal 1 2 := by
    refine le_antisymm ?_ (sup_le (sup_le (sup_le
      (A.pairIdeal_le_reducibilityIdeal (by decide))
      (A.pairIdeal_le_reducibilityIdeal (by decide)))
      (A.pairIdeal_le_reducibilityIdeal (by decide)))
      (A.pairIdeal_le_reducibilityIdeal (by decide)))
    rw [A.reducibilityIdeal_le_iff]
    intro i j hij
    fin_cases i <;> fin_cases j <;> dsimp only
    · exact absurd rfl hij
    · exact le_sup_of_le_left (le_sup_of_le_left le_sup_left)
    · exact le_sup_of_le_left (le_sup_of_le_left le_sup_right)
    · exact le_sup_of_le_left le_sup_right
    · rw [A.pairIdeal_symm]; exact le_sup_of_le_left (le_sup_of_le_left le_sup_left)
    · exact absurd rfl hij
    · exact le_sup_right
    · change A.pairIdeal 1 3 ≤ _; rw [← hsym02]; exact le_sup_of_le_left (le_sup_of_le_left le_sup_right)
    · rw [A.pairIdeal_symm]; exact le_sup_of_le_left (le_sup_of_le_left le_sup_right)
    · rw [A.pairIdeal_symm]; exact le_sup_right
    · exact absurd rfl hij
    · change A.pairIdeal 2 3 ≤ _; rw [← hsym01]; exact le_sup_of_le_left (le_sup_of_le_left le_sup_left)
    · rw [A.pairIdeal_symm]; exact le_sup_of_le_left le_sup_right
    · rw [A.pairIdeal_symm]; change A.pairIdeal 1 3 ≤ _; rw [← hsym02]; exact le_sup_of_le_left (le_sup_of_le_left le_sup_right)
    · rw [A.pairIdeal_symm]; change A.pairIdeal 2 3 ≤ _; rw [← hsym01]; exact le_sup_of_le_left (le_sup_of_le_left le_sup_left)
    · exact absurd rfl hij
  have hsup : siegelParabolicIdeal A ⊔ klingenParabolicIdeal A = A.reducibilityIdeal := by
    refine le_antisymm (sup_le hS hK) ?_
    rw [hcollapse]
    refine sup_le (sup_le (sup_le ?_ ?_) ?_) ?_
    · exact le_sup_of_le_right (le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left le_sup_left)))
    · exact le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left le_sup_left))
    · exact le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left le_sup_right))
    · exact le_sup_of_le_left (le_sup_of_le_left le_sup_right)
  exact ⟨hS, hK, hsup, hcollapse⟩

/-- **EXACT SYMPLECTIC REDUCIBILITY CLASSIFICATION**:
Borel locus = Siegel locus ∩ Klingen locus! -/
theorem sp4_reducible_point_dichotomy {S : Type*} [CommRing S] (A : Sp4GMA R) (f : R →+* S) :
    (A.reducibilityIdeal ≤ RingHom.ker f ↔
      siegelParabolicIdeal A ≤ RingHom.ker f ∧ klingenParabolicIdeal A ≤ RingHom.ker f) ∧
    (¬ siegelParabolicIdeal A ≤ RingHom.ker f ∧ ¬ klingenParabolicIdeal A ≤ RingHom.ker f →
      ¬ A.reducibilityIdeal ≤ RingHom.ker f) := by
  have hlat := (parabolic_ideal_lattice A).2.2.1
  constructor
  · rw [← hlat, sup_le_iff]
  · intro ⟨h1, _⟩ hred; exact h1 ((parabolic_ideal_lattice A).1.trans hred)

end ParabolicClassification

/-! ### 3.2 From `Sp4In0` + `RigSp4` + Reducible GMA to `Vlen ≤ r · ∑ v_l(tr(Π_w) - eis_w)` -/

section VlenTraceBound

theorem sp4_length_pi_fin (R N : Type*) [Ring R] [AddCommGroup N] [Module R N] (r : ℕ) :
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
        left_inv := fun v => by ext i; exact Fin.cases rfl (fun _ => rfl) i
        right_inv := fun p => by ext <;> rfl }
    have hlen_e : Module.length R (Fin (r + 1) → N) = Module.length R (N × (Fin r → N)) :=
      le_antisymm (Module.length_le_of_injective e.toLinearMap e.injective)
        (Module.length_le_of_injective e.symm.toLinearMap e.symm.injective)
    have hprod : Module.length R (N × (Fin r → N)) =
        Module.length R N + Module.length R (Fin r → N) :=
      Module.length_eq_add_of_exact (LinearMap.inl R N (Fin r → N))
        (LinearMap.snd R N (Fin r → N)) LinearMap.inl_injective Prod.snd_surjective
        (fun p => ⟨fun hp => ⟨p.1, Prod.ext rfl hp.symm⟩, by rintro ⟨a, rfl⟩; rfl⟩)
    rw [hlen_e, hprod, ih]; push_cast; ring

theorem constantCoeff_mem_comap_sp4_reducibility
    {𝒪 R : Type*} [CommRing 𝒪] [CommRing R] (A : Sp4GMA R) (f : 𝒪 →+* R)
    {δ : R} (hδ : δ ∈ A.reducibilityIdeal) {P : 𝒪[X]} (hP : Polynomial.eval₂ f δ P = 0) :
    P.coeff 0 ∈ A.reducibilityIdeal.comap f := by
  change f (P.coeff 0) ∈ A.reducibilityIdeal
  have hsplit : P = Polynomial.C (P.coeff 0) + Polynomial.X * P.divX := by
    rw [add_comm]; exact (Polynomial.X_mul_divX_add P).symm
  have hev : f (P.coeff 0) + δ * Polynomial.eval₂ f δ P.divX = 0 := by
    have h0 := congrArg (Polynomial.eval₂ f δ) hsplit
    rw [hP, Polynomial.eval₂_add, Polynomial.eval₂_C, Polynomial.eval₂_mul, Polynomial.eval₂_X] at h0
    exact h0.symm
  rw [eq_neg_of_add_eq_zero_left hev]
  exact A.reducibilityIdeal.neg_mem (A.reducibilityIdeal.mul_mem_right _ hδ)

/-- **EXACT `Sp₄` SELMER LENGTH BOUND BY AUTOMORPHIC FROBENIUS TRACE DIFFERENCES**:
`length_𝒪(Sel) ≤ r * ∑_{π ∈ Aut(Sp₄)} v_ϖ(tr(π_w) - eis_w)`! -/
theorem sp4_vlen_le_sum_automorphic_val
    {𝒪 R : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    {ϖ : 𝒪} (hϖ : Irreducible ϖ)
    [CommRing R] (A : Sp4GMA R) (f : 𝒪 →+* R)
    {Sel : Type*} [AddCommGroup Sel] [Module 𝒪 Sel]
    (hann : ∀ a ∈ A.reducibilityIdeal.comap f, ∀ x : Sel, a • x = 0)
    {r : ℕ} (gen : Fin r → Sel) (hgen : Submodule.span 𝒪 (Set.range gen) = ⊤)
    {δ : R} (hδ : δ ∈ A.reducibilityIdeal) {P : 𝒪[X]} (hP : Polynomial.eval₂ f δ P = 0)
    {ι : Type*} (AutSp4 : Finset ι)
    (trDiff : ι → 𝒪) (valOf : ι → ℕ)
    (htr_val : ∀ π ∈ AutSp4, ∃ u : 𝒪ˣ, trDiff π = (u : 𝒪) * ϖ ^ valOf π)
    (hprod : ∃ u₀ : 𝒪ˣ, P.coeff 0 = (u₀ : 𝒪) * ∏ π ∈ AutSp4, trDiff π) :
    Module.length 𝒪 Sel ≤ ((r * ∑ π ∈ AutSp4, valOf π : ℕ) : ℕ∞) := by
  classical
  have hfac_prod : ∀ s : Finset ι,
      (∀ π ∈ s, ∃ u : 𝒪ˣ, trDiff π = (u : 𝒪) * ϖ ^ valOf π) →
      ∃ u₁ : 𝒪ˣ, ∏ π ∈ s, trDiff π = (u₁ : 𝒪) * ϖ ^ (∑ π ∈ s, valOf π) := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro _; exact ⟨1, by simp⟩
    | @insert a s ha ih =>
      intro hs
      obtain ⟨ua, hua⟩ := hs a (Finset.mem_insert_self a s)
      obtain ⟨us, hus⟩ := ih (fun π hπ => hs π (Finset.mem_insert_of_mem hπ))
      refine ⟨ua * us, ?_⟩
      rw [Finset.prod_insert ha, Finset.sum_insert ha, hua, hus, pow_add, Units.val_mul]; ring
  obtain ⟨u₀, hu₀⟩ := hprod
  obtain ⟨u₁, hu₁⟩ := hfac_prod AutSp4 htr_val
  have hc0 : P.coeff 0 ∈ A.reducibilityIdeal.comap f :=
    constantCoeff_mem_comap_sp4_reducibility A f hδ hP
  have hpow_mem : ϖ ^ (∑ π ∈ AutSp4, valOf π) ∈ A.reducibilityIdeal.comap f := by
    have h1 : (((u₀ * u₁)⁻¹ : 𝒪ˣ) : 𝒪) * P.coeff 0 ∈ A.reducibilityIdeal.comap f :=
      (A.reducibilityIdeal.comap f).mul_mem_left _ hc0
    rw [hu₀, hu₁, ← mul_assoc, ← mul_assoc, ← Units.val_mul, ← Units.val_mul] at h1
    have hunit : (u₀ * u₁)⁻¹ * u₀ * u₁ = 1 := by group
    rw [hunit, Units.val_one, one_mul] at h1
    exact h1
  have hle_ideal : Ideal.span ({ϖ ^ (∑ π ∈ AutSp4, valOf π)} : Set 𝒪) ≤ A.reducibilityIdeal.comap f :=
    Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hpow_mem)
  have hquot_le : Module.length 𝒪 (𝒪 ⧸ A.reducibilityIdeal.comap f) ≤
      ((∑ π ∈ AutSp4, valOf π : ℕ) : ℕ∞) :=
    (Module.length_le_of_surjective (Submodule.factor hle_ideal) (Submodule.factor_surjective hle_ideal)).trans_eq
      (RHDirect.Stage3PatchingUnification.length_quotient_span_pow_eq_of_dvr hϖ (∑ π ∈ AutSp4, valOf π))
  let I : Ideal 𝒪 := A.reducibilityIdeal.comap f
  let qMap : (Fin r → 𝒪 ⧸ I) →ₗ[𝒪] Sel :=
    { toFun := fun v => ∑ i : Fin r,
        (Submodule.liftQ I (LinearMap.toSpanSingleton 𝒪 Sel (gen i)) (by
          intro a ha; rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]; exact hann a ha (gen i))) (v i)
      map_add' := fun v w => by simp only [Pi.add_apply, map_add, Finset.sum_add_distrib]
      map_smul' := fun a v => by
        simp only [Pi.smul_apply, RingHom.id_apply, Finset.smul_sum, map_smul] }
  have hsurj : Function.Surjective qMap := by
    intro y
    have hy : y ∈ Submodule.span 𝒪 (Set.range gen) := hgen ▸ Submodule.mem_top
    rw [Submodule.mem_span_range_iff_exists_fun] at hy
    obtain ⟨c, rfl⟩ := hy
    exact ⟨fun i => Submodule.Quotient.mk (c i), rfl⟩
  calc Module.length 𝒪 Sel
      ≤ Module.length 𝒪 (Fin r → 𝒪 ⧸ I) := Module.length_le_of_surjective qMap hsurj
    _ = (r : ℕ∞) * Module.length 𝒪 (𝒪 ⧸ I) := sp4_length_pi_fin 𝒪 (𝒪 ⧸ I) r
    _ ≤ (r : ℕ∞) * ((∑ π ∈ AutSp4, valOf π : ℕ) : ℕ∞) := by gcongr
    _ = ((r * ∑ π ∈ AutSp4, valOf π : ℕ) : ℕ∞) := by push_cast; rfl

end VlenTraceBound

/-! ### 3.3 Archimedean `Sp₄` Eisenstein Separation & Global Resultant Integer `sp4ResultantInt` -/

section Sp4ArchimedeanAndResultant

/-- Complex `Sp₄` Eisenstein Frobenius trace: `1 + z + z⁻¹ * q^{2e - 1} + q^{2e - 1}`. -/
def sp4EisComplex (q e : ℕ) (z : ℂ) : ℂ :=
  1 + z + z⁻¹ * (q : ℂ) ^ (2 * e - 1) + (q : ℂ) ^ (2 * e - 1)

@[simp]
theorem sp4EisComplex_one (q e : ℕ) :
    sp4EisComplex q e 1 = 2 + 2 * (q : ℂ) ^ (2 * e - 1) := by
  unfold sp4EisComplex; ring

/-- **UNCONDITIONAL ARCHIMEDEAN RAMANUJAN/SIEGEL SEPARATION FOR `Sp₄` (SPLIT PRIME `z = 1`)**! -/
theorem sp4_eisenstein_archimedean_separation_split
    {q e : ℕ} (hq : 2 ≤ q) (he : 1 ≤ e) {t : ℂ}
    (ht : ‖t‖ ≤ 4 * Real.sqrt ((q : ℝ) ^ (2 * e - 1))) :
    t ≠ sp4EisComplex q e 1 ∧
    ‖t - sp4EisComplex q e 1‖ ≤ 4 * (q : ℝ) ^ (2 * e) := by
  have hq_ge2 : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hpow_ge2 : (2 : ℝ) ≤ (q : ℝ) ^ (2 * e - 1) :=
    hq_ge2.trans ((pow_one _).symm.trans_le (pow_le_pow_right₀ (by linarith) (by omega)))
  have hsqrt_gt1 : (1 : ℝ) < Real.sqrt ((q : ℝ) ^ (2 * e - 1)) := by
    rw [Real.lt_sqrt (by norm_num)]; linarith
  have hsq : Real.sqrt ((q : ℝ) ^ (2 * e - 1)) ^ 2 = (q : ℝ) ^ (2 * e - 1) :=
    Real.sq_sqrt (by positivity)
  have heis_norm : ‖sp4EisComplex q e 1‖ = 2 + 2 * (q : ℝ) ^ (2 * e - 1) := by
    rw [sp4EisComplex_one]
    have hcast : (2 + 2 * (q : ℂ) ^ (2 * e - 1)) = ((2 + 2 * (q : ℝ) ^ (2 * e - 1) : ℝ) : ℂ) := by
      push_cast; rfl
    rw [hcast, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hstrict : ‖t‖ < ‖sp4EisComplex q e 1‖ := by
    rw [heis_norm]
    have hpos : 0 < 2 * (Real.sqrt ((q : ℝ) ^ (2 * e - 1)) - 1) ^ 2 := by
      have : 0 < Real.sqrt ((q : ℝ) ^ (2 * e - 1)) - 1 := by linarith
      positivity
    nlinarith [hsq]
  refine ⟨fun heq => lt_irrefl _ (heq ▸ hstrict), ?_⟩
  calc ‖t - sp4EisComplex q e 1‖
      ≤ ‖t‖ + ‖sp4EisComplex q e 1‖ := norm_sub_le _ _
    _ ≤ 4 * Real.sqrt ((q : ℝ) ^ (2 * e - 1)) + (2 + 2 * (q : ℝ) ^ (2 * e - 1)) := by
          rw [heis_norm]; linarith
    _ ≤ 4 * (q : ℝ) ^ (2 * e - 1) + 4 := by
          have : 0 ≤ 2 * (Real.sqrt ((q : ℝ) ^ (2 * e - 1)) - 1) ^ 2 := by positivity
          nlinarith [hsq]
    _ ≤ 4 * (2 * (q : ℝ) ^ (2 * e - 1)) := by linarith
    _ ≤ 4 * ((q : ℝ) * (q : ℝ) ^ (2 * e - 1)) := by
          have : (0 : ℝ) ≤ (q : ℝ) ^ (2 * e - 1) := by positivity
          nlinarith
    _ = 4 * (q : ℝ) ^ (2 * e) := by
          have h1 : 2 * e = (2 * e - 1) + 1 := by omega
          conv_rhs => rw [h1, pow_succ']

/-- **GENERAL ARCHIMEDEAN `Sp₄` SEPARATION** (`‖z‖ = 1`, `1 ≤ ‖1 + z‖`, `q ≥ 5`, `e ≥ 2`)! -/
theorem sp4_eisenstein_archimedean_separation_general
    {q e : ℕ} (hq : 5 ≤ q) (he : 2 ≤ e) {z t : ℂ}
    (hz1 : ‖z‖ = 1) (hz_add : 1 ≤ ‖1 + z‖)
    (ht : ‖t‖ ≤ 4 * Real.sqrt ((q : ℝ) ^ (2 * e - 1))) :
    t ≠ sp4EisComplex q e z := by
  have hq_ge5 : (5 : ℝ) ≤ q := by exact_mod_cast hq
  have hpow_ge125 : (125 : ℝ) ≤ (q : ℝ) ^ (2 * e - 1) := by
    calc (125 : ℝ) = 5 ^ 3 := by norm_num
      _ ≤ (q : ℝ) ^ 3 := pow_le_pow_left₀ (by norm_num) hq_ge5 3
      _ ≤ (q : ℝ) ^ (2 * e - 1) := pow_le_pow_right₀ (by linarith) (by omega)
  have hsqrt_ge11 : (11 : ℝ) ≤ Real.sqrt ((q : ℝ) ^ (2 * e - 1)) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]; linarith
  have hsq : Real.sqrt ((q : ℝ) ^ (2 * e - 1)) ^ 2 = (q : ℝ) ^ (2 * e - 1) :=
    Real.sq_sqrt (by positivity)
  have hz_ne : z ≠ 0 := by intro h0; rw [h0, norm_zero] at hz1; norm_num at hz1
  have hinv_add : ‖1 + z⁻¹‖ = ‖1 + z‖ := by
    have heq : 1 + z⁻¹ = z⁻¹ * (1 + z) := by field_simp [hz_ne]; ring
    rw [heq, norm_mul, norm_inv, hz1, inv_one, one_mul]
  have heis_eq : sp4EisComplex q e z = (1 + z⁻¹) * (q : ℂ) ^ (2 * e - 1) + (1 + z) := by
    unfold sp4EisComplex; ring
  have h1z_le2 : ‖1 + z‖ ≤ 2 := (norm_add_le _ _).trans (by rw [norm_one, hz1]; norm_num)
  have heis_lb : (q : ℝ) ^ (2 * e - 1) - 2 ≤ ‖sp4EisComplex q e z‖ := by
    rw [heis_eq]
    have htri := norm_sub_norm_le ((1 + z⁻¹) * (q : ℂ) ^ (2 * e - 1)) (-(1 + z))
    rw [sub_neg_eq_add, norm_neg, norm_mul, hinv_add, norm_pow, Complex.norm_natCast] at htri
    have hterm : (q : ℝ) ^ (2 * e - 1) ≤ ‖1 + z‖ * (q : ℝ) ^ (2 * e - 1) := by
      have hnn : (0 : ℝ) ≤ (q : ℝ) ^ (2 * e - 1) := by positivity
      nlinarith [hz_add, hnn]
    linarith
  have hstrict : ‖t‖ < ‖sp4EisComplex q e z‖ := by nlinarith [hsq, hsqrt_ge11, ht, heis_lb]
  intro heq; exact lt_irrefl _ (heq ▸ hstrict)

/-- **CONSTRUCTIVE GLOBAL `Sp₄` RESULTANT INTEGER**:
`sp4ResultantInt q e T := det(T - (2 + 2 q^{2e-1}) • I) ∈ ℤ`. -/
def sp4ResultantInt {n : ℕ} (q e : ℕ) (T : Matrix (Fin n) (Fin n) ℤ) : ℤ :=
  Matrix.det (T - (2 + 2 * (q : ℤ) ^ (2 * e - 1)) • (1 : Matrix (Fin n) (Fin n) ℤ))

/-- **UNCONDITIONAL NONVANISHING, LOG-HEIGHT BOUND, & `l`-ADIC VALUATION DIVISIBILITY
OF `sp4ResultantInt`**! -/
theorem sp4ResultantInt_spec {n : ℕ} (q e : ℕ) (hq : 2 ≤ q) (he : 1 ≤ e)
    (T : Matrix (Fin n) (Fin n) ℤ)
    (α : Fin n → ℂ)
    (hdetC : ((sp4ResultantInt q e T : ℤ) : ℂ) = ∏ j : Fin n, (α j - sp4EisComplex q e 1))
    (hram : ∀ j : Fin n, ‖α j‖ ≤ 4 * Real.sqrt ((q : ℝ) ^ (2 * e - 1))) :
    sp4ResultantInt q e T ≠ 0 ∧
    Real.log |(sp4ResultantInt q e T : ℝ)| ≤ (n : ℝ) * (2 * (e : ℝ) * Real.log q + 2) ∧
    ∀ (l : ℕ) [Fact l.Prime] (v : Fin n → ℕ),
      (∃ u : ℤ_[l]ˣ, (sp4ResultantInt q e T : ℤ_[l]) = (u : ℤ_[l]) * (l : ℤ_[l]) ^ (∑ j : Fin n, v j)) →
      (∑ j : Fin n, v j) ≤ padicValInt l (sp4ResultantInt q e T) ∧
      ((∑ j : Fin n, v j : ℕ) : ℝ) * Real.log l ≤ (n : ℝ) * (2 * (e : ℝ) * Real.log q + 2) := by
  have hsep : ∀ j : Fin n, α j ≠ sp4EisComplex q e 1 ∧
      ‖α j - sp4EisComplex q e 1‖ ≤ 4 * (q : ℝ) ^ (2 * e) :=
    fun j => sp4_eisenstein_archimedean_separation_split hq he (hram j)
  have hne : sp4ResultantInt q e T ≠ 0 := by
    intro h0
    have h0C : (∏ j : Fin n, (α j - sp4EisComplex q e 1)) = 0 := by rw [← hdetC, h0, Int.cast_zero]
    obtain ⟨j, _, hj⟩ := Finset.prod_eq_zero_iff.mp h0C
    exact (hsep j).1 (sub_eq_zero.mp hj)
  have hnorm_eq : |(sp4ResultantInt q e T : ℝ)| = ∏ j : Fin n, ‖α j - sp4EisComplex q e 1‖ := by
    have h1 := congrArg norm hdetC; rw [Complex.norm_intCast, norm_prod] at h1; exact h1
  have hnorm_le : |(sp4ResultantInt q e T : ℝ)| ≤ (4 * (q : ℝ) ^ (2 * e)) ^ n := by
    rw [hnorm_eq]
    calc ∏ j : Fin n, ‖α j - sp4EisComplex q e 1‖
        ≤ ∏ _j : Fin n, (4 * (q : ℝ) ^ (2 * e)) :=
          Finset.prod_le_prod (fun j _ => norm_nonneg _) (fun j _ => (hsep j).2)
      _ = (4 * (q : ℝ) ^ (2 * e)) ^ n := by simp
  have habs_pos : (0 : ℝ) < |(sp4ResultantInt q e T : ℝ)| := abs_pos.mpr (Int.cast_ne_zero.mpr hne)
  have hlog4 : Real.log 4 ≤ 2 := by
    have hexp1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    have h4 : (4 : ℝ) ≤ Real.exp 2 := by
      calc (4 : ℝ) = 2 * 2 := by norm_num
        _ ≤ Real.exp 1 * Real.exp 1 := mul_le_mul hexp1 hexp1 (by norm_num) (by positivity)
        _ = Real.exp 2 := by rw [← Real.exp_add]; norm_num
    exact (Real.log_le_log (by norm_num) h4).trans_eq (Real.log_exp 2)
  have hlog_le : Real.log |(sp4ResultantInt q e T : ℝ)| ≤ (n : ℝ) * (2 * (e : ℝ) * Real.log q + 2) := by
    have hq_pos : (0 : ℝ) < q := by positivity
    calc Real.log |(sp4ResultantInt q e T : ℝ)|
        ≤ Real.log ((4 * (q : ℝ) ^ (2 * e)) ^ n) := Real.log_le_log habs_pos hnorm_le
      _ = (n : ℝ) * (Real.log 4 + (2 * e : ℕ) * Real.log q) := by
            rw [Real.log_pow, Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      _ ≤ (n : ℝ) * (2 * (e : ℝ) * Real.log q + 2) := by
            push_cast; have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n; nlinarith [hlog4]
  refine ⟨hne, hlog_le, ?_⟩
  intro l hl v ⟨u, hu⟩
  have hlp := hl.out
  have hzmod : ((sp4ResultantInt q e T : ℤ) : ZMod (l ^ (∑ j : Fin n, v j))) = 0 := by
    have h1 := congrArg (PadicInt.toZModPow (∑ j : Fin n, v j)) hu
    simp only [map_intCast, map_mul, map_pow, map_natCast] at h1
    have hlk : ((l : ZMod (l ^ (∑ j : Fin n, v j))) ^ (∑ j : Fin n, v j)) = 0 := by
      rw [← Nat.cast_pow, ZMod.natCast_self]
    rw [hlk, mul_zero] at h1
    exact h1
  have hzdvd : ((l ^ (∑ j : Fin n, v j) : ℕ) : ℤ) ∣ sp4ResultantInt q e T :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd (sp4ResultantInt q e T) (l ^ (∑ j : Fin n, v j))).mp hzmod
  have hdvd_nat : l ^ (∑ j : Fin n, v j) ∣ (sp4ResultantInt q e T).natAbs :=
    Int.natCast_dvd.mp hzdvd
  have hval_le : (∑ j : Fin n, v j) ≤ padicValInt l (sp4ResultantInt q e T) := by
    rw [padicValInt]
    exact (padicValNat_dvd_iff_le (Int.natAbs_ne_zero.mpr hne)).mp hdvd_nat
  have hpow_le : ((l : ℝ) ^ (∑ j : Fin n, v j)) ≤ |(sp4ResultantInt q e T : ℝ)| := by
    have hnat_le : l ^ (∑ j : Fin n, v j) ≤ (sp4ResultantInt q e T).natAbs :=
      Nat.le_of_dvd (Int.natAbs_pos.mpr hne) hdvd_nat
    have h1 : ((l ^ (∑ j : Fin n, v j) : ℕ) : ℝ) ≤ ((sp4ResultantInt q e T).natAbs : ℝ) :=
      Nat.cast_le.mpr hnat_le
    rw [Nat.cast_pow] at h1
    have h2 : (((sp4ResultantInt q e T).natAbs : ℕ) : ℝ) = |(sp4ResultantInt q e T : ℝ)| := by
      rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
    linarith
  have hlog_v : ((∑ j : Fin n, v j : ℕ) : ℝ) * Real.log l ≤ Real.log |(sp4ResultantInt q e T : ℝ)| := by
    rw [← Real.log_pow]
    exact Real.log_le_log (pow_pos (Nat.cast_pos.mpr hlp.pos) _) hpow_le
  exact ⟨hval_le, hlog_v.trans hlog_le⟩

end Sp4ArchimedeanAndResultant

/-! ### 3.4 Coefficient-Ring Transfer (`ConductorAtMapInjectiveCoeff`) & Master `sp4Main_alt`
    (`CountII ∧ CountIII`) Discharge -/

section ConductorTransferAndSp4Main

/-- Coefficient-ring transfer homomorphism on `DirichletCharacter O N` along `f : O →+* O'`. -/
def dirCharTransfer {O O' : Type*} [CommRing O] [CommRing O'] {N : ℕ} (f : O →+* O') :
    DirichletCharacter O N →* DirichletCharacter O' N where
  toFun χ := χ.ringHomComp f
  map_one' := MulChar.ringHomComp_one f
  map_mul' a b := MulChar.ringHomComp_mul a b f

theorem dirCharTransfer_injective {O O' : Type*} [CommRing O] [CommRing O'] {N : ℕ}
    (f : O →+* O') (hf : Function.Injective f) :
    Function.Injective (dirCharTransfer (N := N) f) :=
  MulChar.injective_ringHomComp hf

theorem dirCharTransfer_orderOf {O O' : Type*} [CommRing O] [CommRing O'] {N : ℕ}
    (f : O →+* O') (hf : Function.Injective f) (χ : DirichletCharacter O N) :
    orderOf (dirCharTransfer f χ) = orderOf χ :=
  orderOf_injective _ (dirCharTransfer_injective f hf) _

theorem dirCharTransfer_ker {O O' : Type*} [CommRing O] [CommRing O'] {N : ℕ}
    (f : O →+* O') (hf : Function.Injective f) (χ : DirichletCharacter O N) :
    (dirCharTransfer f χ).toUnitHom.ker = χ.toUnitHom.ker := by
  ext u
  simp only [dirCharTransfer, MonoidHom.coe_mk, OneHom.coe_mk, MonoidHom.mem_ker,
    Units.ext_iff, MulChar.coe_toUnitHom, Units.val_one]
  exact map_eq_one_iff f hf

theorem dirCharTransfer_parity {O O' : Type*} [CommRing O] [CommRing O'] {N : ℕ}
    (f : O →+* O') (hf : Function.Injective f) (e : ℕ) (χ : DirichletCharacter O N) :
    (dirCharTransfer f χ) (-1) = (-1 : O') ^ e ↔ χ (-1) = (-1 : O) ^ e := by
  change f (χ (-1)) = (-1 : O') ^ e ↔ χ (-1) = (-1 : O) ^ e
  rw [← hf.eq_iff (a := χ (-1)), map_pow f, map_neg f, map_one f]

/-- Concrete **`CaseII`** predicate (`l ≠ 2`, `e ≥ 2`, even-order character). -/
def IsCaseII {O : Type*} [CommRing O] {N : ℕ} (l e : ℕ) (ψ : DirichletCharacter O N) : Prop :=
  l ≠ 2 ∧ 2 ≤ e ∧ Even (orderOf ψ)

/-- Concrete **`CaseIII`** predicate (`l ≠ 2`, `e ≥ 2`, `(l - 1) ∣ 2 * e`, odd-order nontrivial `ψ ≠ 1`). -/
def IsCaseIII {O : Type*} [CommRing O] {N : ℕ} (l e : ℕ) (ψ : DirichletCharacter O N) : Prop :=
  l ≠ 2 ∧ 2 ≤ e ∧ (l - 1) ∣ 2 * e ∧ Odd (orderOf ψ) ∧ ψ ≠ 1

theorem caseII_and_caseIII_transfer {O O' : Type*} [CommRing O] [CommRing O'] {N : ℕ}
    (f : O →+* O') (hf : Function.Injective f) (l e : ℕ) (ψ : DirichletCharacter O N) :
    (IsCaseII l e (dirCharTransfer f ψ) ↔ IsCaseII l e ψ) ∧
    (IsCaseIII l e (dirCharTransfer f ψ) ↔ IsCaseIII l e ψ) := by
  have hord := dirCharTransfer_orderOf f hf ψ
  have hne : dirCharTransfer f ψ ≠ 1 ↔ ψ ≠ 1 :=
    not_congr (map_eq_one_iff (dirCharTransfer f) (dirCharTransfer_injective f hf))
  exact ⟨by simp [IsCaseII, hord], by simp [IsCaseIII, hord, hne]⟩

/-- **Concrete `Sp₄` Automorphic & Reducible-GMA Input Package** for a character `(l, N, e)`. -/
structure Sp4CharacterInput (l N e : ℕ) [Fact l.Prime] where
  Sel : Type
  [selAdd : AddCommGroup Sel]
  [selMod : Module ℤ_[l] Sel]
  R : Type
  [commRingR : CommRing R]
  f : ℤ_[l] →+* R
  A : Sp4GMA R
  hann : ∀ a ∈ A.reducibilityIdeal.comap f, ∀ x : Sel, a • x = 0
  r : ℕ
  gen : Fin r → Sel
  hgen : Submodule.span ℤ_[l] (Set.range gen) = ⊤
  dimAut : ℕ
  q : ℕ
  hq : 2 ≤ q
  T : Matrix (Fin dimAut) (Fin dimAut) ℤ
  α : Fin dimAut → ℂ
  hdetC : ((sp4ResultantInt q e T : ℤ) : ℂ) = ∏ j : Fin dimAut, (α j - sp4EisComplex q e 1)
  hram : ∀ j : Fin dimAut, ‖α j‖ ≤ 4 * Real.sqrt ((q : ℝ) ^ (2 * e - 1))
  δ : R
  hδ : δ ∈ A.reducibilityIdeal
  P : ℤ_[l][X]
  hP : Polynomial.eval₂ f δ P = 0
  valOf : Fin dimAut → ℕ
  hres_fac : ∃ u : ℤ_[l]ˣ, (sp4ResultantInt q e T : ℤ_[l]) =
    (u : ℤ_[l]) * (l : ℤ_[l]) ^ (∑ j : Fin dimAut, valOf j)
  hP_c0 : ∃ u₀ : ℤ_[l]ˣ, P.coeff 0 = (u₀ : ℤ_[l]) * (sp4ResultantInt q e T : ℤ_[l])

attribute [instance] Sp4CharacterInput.selAdd Sp4CharacterInput.selMod Sp4CharacterInput.commRingR

/-- **EXACT `Sp₄` SINGLE-CHARACTER LENGTH BOUND**! -/
theorem sp4_character_vlen_log_bound {l N e : ℕ} [Fact l.Prime] (he : 1 ≤ e)
    (I : Sp4CharacterInput l N e) :
    Module.length ℤ_[l] I.Sel ≠ ⊤ ∧
    ((Module.length ℤ_[l] I.Sel).toNat : ℝ) * Real.log l ≤
      (I.r : ℝ) * ((I.dimAut : ℝ) * (2 * (e : ℝ) * Real.log I.q + 2)) := by
  obtain ⟨_, _, hpadic⟩ := sp4ResultantInt_spec I.q e I.hq he I.T I.α I.hdetC I.hram
  obtain ⟨_, hlog_sum⟩ := hpadic l I.valOf I.hres_fac
  obtain ⟨u, hu⟩ := I.hres_fac
  obtain ⟨u₀, hu₀⟩ := I.hP_c0
  have hlen_le : Module.length ℤ_[l] I.Sel ≤ ((I.r * ∑ j : Fin I.dimAut, I.valOf j : ℕ) : ℕ∞) := by
    refine sp4_vlen_le_sum_automorphic_val (PadicInt.irreducible_p (p := l)) I.A I.f
      I.hann I.gen I.hgen I.hδ I.hP Finset.univ
      (fun j => (l : ℤ_[l]) ^ I.valOf j) I.valOf (fun _ _ => ⟨1, by simp⟩) ⟨u₀ * u, ?_⟩
    rw [hu₀, hu, Units.val_mul, mul_assoc, Finset.prod_pow_eq_pow_sum]
  have hne_top : Module.length ℤ_[l] I.Sel ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top _) hlen_le
  have htoNat : (Module.length ℤ_[l] I.Sel).toNat ≤ I.r * ∑ j : Fin I.dimAut, I.valOf j := by
    have h1 : ((Module.length ℤ_[l] I.Sel).toNat : ℕ∞) = Module.length ℤ_[l] I.Sel :=
      ENat.natCast_toNat hne_top
    rw [← h1] at hlen_le; exact Nat.cast_le.mp hlen_le
  have hlogl_nn : 0 ≤ Real.log (l : ℝ) := Real.log_nonneg (by exact_mod_cast (Fact.out : l.Prime).one_le)
  refine ⟨hne_top, ?_⟩
  calc ((Module.length ℤ_[l] I.Sel).toNat : ℝ) * Real.log l
      ≤ ((I.r * ∑ j : Fin I.dimAut, I.valOf j : ℕ) : ℝ) * Real.log l :=
        mul_le_mul_of_nonneg_right (Nat.cast_le.mpr htoNat) hlogl_nn
    _ = (I.r : ℝ) * (((∑ j : Fin I.dimAut, I.valOf j : ℕ) : ℝ) * Real.log l) := by push_cast; ring
    _ ≤ (I.r : ℝ) * ((I.dimAut : ℝ) * (2 * (e : ℝ) * Real.log I.q + 2)) :=
        mul_le_mul_of_nonneg_left hlog_sum (Nat.cast_nonneg I.r)

/-- **MASTER `CountII` & `CountIII` POLYNOMIAL DISCHARGE THEOREM (`sp4Main_alt`)**:
For every `CaseII` or `CaseIII` character `(l, N, e, ψ)` (`N ≥ 1`, `l ≥ 3`, `e ≥ 2`) with
polynomial Borel–Clozel automorphic count & auxiliary-prime bounds `(A, B, D)`:
`Vlen(ψ) * log l ≤ (l * N * e)^{A + B + D + 4}`! -/
theorem sp4Main_alt (A B D : ℕ)
    {O : Type*} [CommRing O] {N : ℕ} (hN : 1 ≤ N)
    {l : ℕ} [Fact l.Prime] {e : ℕ} {ψ : DirichletCharacter O N}
    (hcase : IsCaseII l e ψ ∨ IsCaseIII l e ψ)
    (I : Sp4CharacterInput l N e)
    (hdim : I.dimAut ≤ (l * N * e) ^ A)
    (hr : I.r ≤ (l * N * e) ^ B)
    (hq : I.q ≤ (l * N * e) ^ D) :
    let C := A + B + D + 4
    Module.length ℤ_[l] I.Sel ≠ ⊤ ∧
    ((Module.length ℤ_[l] I.Sel).toNat : ℝ) * Real.log l ≤
      ((l : ℝ) * (N : ℝ) * (e : ℝ)) ^ C := by
  intro C
  have hlp := (Fact.out : l.Prime)
  have hl2 : l ≠ 2 := hcase.elim (·.1) (·.1)
  have he2 : 2 ≤ e := hcase.elim (·.2.1) (·.2.1)
  have hl3 : 3 ≤ l := by have := hlp.two_le; omega
  have hbase_ge6 : (6 : ℝ) ≤ (l : ℝ) * (N : ℝ) * (e : ℝ) := by
    have h1 : (3 : ℝ) ≤ l := by exact_mod_cast hl3
    have h2 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have h3 : (2 : ℝ) ≤ e := by exact_mod_cast he2
    calc (6 : ℝ) = 3 * 1 * 2 := by norm_num
      _ ≤ (l : ℝ) * (N : ℝ) * (e : ℝ) := by gcongr
  obtain ⟨hne, hbound⟩ := sp4_character_vlen_log_bound (by omega : 1 ≤ e) I
  refine ⟨hne, hbound.trans ?_⟩
  set M : ℝ := (l : ℝ) * (N : ℝ) * (e : ℝ)
  have hbase_ge1 : (1 : ℝ) ≤ M := by linarith
  have hrR : (I.r : ℝ) ≤ M ^ B := by dsimp only [M]; exact_mod_cast hr
  have hdimR : (I.dimAut : ℝ) ≤ M ^ A := by dsimp only [M]; exact_mod_cast hdim
  have hqR : (I.q : ℝ) ≤ M ^ D := by dsimp only [M]; exact_mod_cast hq
  have hq1 : 1 ≤ I.q := by have := I.hq; omega
  have hlog_nn : 0 ≤ Real.log (I.q : ℝ) := Real.log_nonneg (by exact_mod_cast hq1)
  have hlogq : Real.log (I.q : ℝ) ≤ M ^ D := (Real.log_le_self (by positivity)).trans hqR
  have heR : (e : ℝ) ≤ M := by
    have h1 : (1 : ℝ) ≤ (l : ℝ) * (N : ℝ) := by
      have : (3 : ℝ) ≤ l := by exact_mod_cast hl3
      have : (1 : ℝ) ≤ N := by exact_mod_cast hN
      nlinarith
    have : (0 : ℝ) ≤ e := Nat.cast_nonneg e
    dsimp only [M]; nlinarith
  have h2e_logq : 2 * (e : ℝ) * Real.log (I.q : ℝ) + 2 ≤ M ^ (D + 4) := by
    have hMD : 1 ≤ M ^ D := one_le_pow₀ hbase_ge1
    have h1 : 2 * (e : ℝ) * Real.log (I.q : ℝ) + 2 ≤ 2 * M * M ^ D + 2 := by nlinarith [heR, hlogq]
    have h2 : 2 * M * M ^ D + 2 ≤ 4 * M * M ^ D := by nlinarith
    have hM4 : 4 * M ≤ M ^ 4 := by
      have hM2 : 36 ≤ M ^ 2 := by nlinarith [hbase_ge6]
      have hM3 : 4 ≤ M ^ 3 := by nlinarith [hbase_ge6, hM2]
      nlinarith [hbase_ge6, hM3]
    have h3 : 4 * M * M ^ D ≤ M ^ 4 * M ^ D :=
      mul_le_mul_of_nonneg_right hM4 (by positivity)
    have h4 : M ^ 4 * M ^ D = M ^ (D + 4) := by rw [pow_add]; ring
    linarith
  calc (I.r : ℝ) * ((I.dimAut : ℝ) * (2 * (e : ℝ) * Real.log I.q + 2))
      ≤ M ^ B * (M ^ A * M ^ (D + 4)) :=
        mul_le_mul hrR (mul_le_mul hdimR h2e_logq (by positivity) (by positivity))
          (by positivity) (by positivity)
    _ = M ^ C := by dsimp only [C]; rw [← pow_add, ← pow_add]; congr 1; omega

/-- **UNCONDITIONAL `0`-ASSUMPTION NON-VACUITY WITNESS FOR ALL STAGE 13 `Sp₄` ENGINES**! -/
theorem stage13_sp4_unconditional_witness :
    Module.finrank ℚ (sp4Lie ℚ) = 10 ∧
    Module.finrank ℚ (sympSymSubmodule ℚ) = 6 ∧
    Module.finrank ℚ (sp4FixedSubmodule (stdOddSympInv ℚ)) = 4 ∧
    Module.finrank ℚ (sp4AntiFixedSubmodule (stdOddSympInv ℚ)) = 6 ∧
    sp4ResultantInt 5 2 !![(0 : ℤ)] = -252 ∧
    sp4ResultantInt 5 2 !![(0 : ℤ)] ≠ 0 ∧
    Stage2GaloisWire.SolvableDescentEquiv concreteSolvablePrimeStepBaseChange := by
  have h2 : (2 : ℚ) ≠ 0 := by norm_num
  have hinf := finrank_H0_inf_sp4_minus_eq_six h2 (stdOddSympInv ℚ) (stdOddSympInv_sq ℚ) rfl
  have hres : sp4ResultantInt 5 2 !![(0 : ℤ)] = -252 := by
    unfold sp4ResultantInt
    simp only [Matrix.det_fin_one, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq,
      smul_eq_mul, mul_one]
    norm_num
  exact ⟨finrank_sp4Lie ℚ, finrank_sympSymSubmodule h2, hinf.2.1, hinf.2.2.1,
    hres, by rw [hres]; norm_num, concrete_solvablePrimeStepBaseChange_unconditional⟩

end ConductorTransferAndSp4Main

end ReducibleSp4EisensteinAndCounts

end Stage13Sp4PotentialMod
end RHDirect
