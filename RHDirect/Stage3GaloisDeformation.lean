import RHDirect.Interfaces
import RHDirect.AutomorphicInputs
import RHDirect.Stage2GaloisCohomology
import RHDirect.TaylorWilesWindow
import Mathlib.Algebra.DualNumber
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.Operations

/-!
# RHDirect.Stage3GaloisDeformation

Deep Stage 3 formalization of **Mazur's Galois Deformation Theory, the Tangent-Space Isomorphism
`Deform_1(ρ̄) ≃ H¹(G, Ad(ρ̄))`, Taylor–Wiles Auxiliary-Prime Dual-Selmer Killing
(`H¹_{L_Q^⊥}(Ad*(1)) = 0`), Exact Presentation Balance, and Minimal-Generator Bounds for `R_Q`**
in pure Mathlib `v4.33.1`, building directly on `RHDirect.Stage2GaloisCohomology` and
`RHDirect.TaylorWilesWindow`.

## Contents

1. **Dual Numbers `k[ε]/(ε²)` & Matrix/GL Algebra over `DualNumber k`**
   - `matDual A B` (`A + ε B`), `matFst`, `matSnd`, `epsUnit A` (`1 + ε A ∈ GL_n(k[ε]/(ε²))`),
     `liftGL u C` (`(1 + ε C) u ∈ GL_n(k[ε]/(ε²))`), and the reduction map
     `reduceGL : GL_n(k[ε]/(ε²)) →* GL_n(k)`.
   - Exact Lie-algebra determinant identity `det_matDual_one` (`det(1 + ε C) = 1 + ε tr(C)`) and
     `det_liftGL_eq_inl_iff_trace_zero` (`det((1 + ε C) u) = det(u) ↔ tr(C) = 0`).

2. **Adjoint Representation `Ad(ρ̄)`, `Ad⁰(ρ̄)` & the Exact Mazur Tangent-Space Isomorphism**
   - `AdRep ρbar` (with conjugation `G`-action `g • X = ρ̄(g) X ρ̄(g)⁻¹`) and trace-zero submodule
     `Ad0Rep ρbar`.
   - `H1Space k G M` (`k`-vector space model of `H¹(G, M)`) with canonical equivalence
     `h1SpaceEquivH1Group : H1Space k G M ≃+ Stage2GaloisCohomology.H1Group G M`.
   - `FirstOrderLift ρbar` (group homomorphisms `ρ_ε : G →* GL_n(k[ε]/(ε²))` reducing to `ρ̄`),
     exact cocycle characterization `FirstOrderLift.liftGL_mul_iff_cocycle`, and bijection
     `FirstOrderLift.equivCocycle1 : FirstOrderLift ρbar ≃ Stage2GaloisCohomology.Cocycle1 G (AdRep ρbar)`.
   - Strict equivalence `FirstOrderLift.StrictEquiv` (conjugation by `1 + ε A`) ↔ 1-coboundaries
     (`coboundary1`), establishing **`mazurTangentEquiv : Deform1 ρbar ≃ H1Group G (AdRep ρbar)`**,
     the `k`-linear tangent-space isomorphism **`mazurTangentLinearEquiv`**, and the fixed-determinant
     sub-deformation bijection **`fixedDetDeformEquivH1Ad0 : FixedDetDeform1 ρbar ≃ H1Group G (Ad0Submodule ρbar)`**.

3. **Taylor–Wiles Auxiliary-Prime Selection & Dual-Selmer Killing (`H¹_{L_Q^⊥} = 0`)**
   - Abstract linear-algebraic Chebotarev killing induction (`exists_killing_set_le_finrank`,
     `exists_exact_killing_set_of_dim_one`, and optimality `finrank_le_card_of_kerOn_eq_bot`).
   - Application to `Stage2GaloisCohomology.PoitouTateData`: `relaxCond`,
     `dualSelmer_relaxCond_eq_inf_ker`, `taylor_wiles_exact_balance_of_dual_vanishing`,
     **`taylor_wiles_kill_dual_selmer`** (induction on `dim H¹_{L^⊥}` producing `Q` with
     `Q.card = dim H¹_{L^⊥}`, `H¹_{L_Q^⊥} = 0`, and exact presentation balance
     `dim H¹_{L_Q} = q + (dim H⁰ - dim H⁰*) + ∑_{v ∈ S} (dim L_v - dim H⁰_v)`),
     and the balanced Taylor–Wiles numerical coincidence **`taylor_wiles_balanced_g_eq_q`**
     (`dim H¹_{L_Q} = q`).

4. **Relative Cotangent Space `m_{R_Q} / (ϖ, m_{R_Q}²)`, Zariski Tangent Duality & Minimal Generators `μ`**
   - `RelCotangent m_Q ϖ` and third-isomorphism equivalence `relCotangentEquivCotangentQuot`
     with `m̄ / m̄²` of `R_Q / (ϖ)`.
   - `TangentHom k A π` and canonical Zariski tangent–cotangent duality
     `zariskiTangentEquivDualCotangent : TangentHom k A π ≃ Module.Dual k (CotangentSpace k A π)`.
   - Minimal generator count `minGenCount R M`, exact field identity `minGenCount_eq_finrank`,
     Nakayama lifting `nakayama_minGenCount_le`, and universal deformation ring theorems
     `universalDeformRing_minGen_eq_selmer_dim`, `universalDeformRing_presentation_balance`, and
     `universalDeformRing_balanced_minGen_eq_q`.

5. **Direct Bridges to `TaylorWilesWindow` and `Stage2GaloisCohomology`**
   - `patched_obstruction_bound_of_deform_generators` (connecting tangent-space generator count `μ`
     to `TaylorWilesWindow.patched_selmer_obstruction_bound`).
   - `TaylorWilesKilledSelmerFamily` and `vvle_of_taylor_wiles_dual_killing` (connecting directly
     to `Stage2GaloisCohomology.vvle_of_greenberg_wiles`).
   - `DeformationCohomologySystem` and `minimalGaloisCohomology_of_deformationSystem` (connecting
     directly to `Stage2GaloisCohomology.minimalGaloisCohomology_of_system`).

6. **Unconditional Non-Vacuity Witnesses**
   - Concrete witnesses over `k = ZMod 3` certifying that every structure and headline theorem is
     unconditionally inhabited.

Zero `sorry`, zero custom `axiom`s.
-/

noncomputable section

open scoped BigOperators
open Finset RHDirect RHDirect.Stage2GaloisCohomology

namespace RHDirect.Stage3GaloisDeformation

/-! ## Section 1: Dual Numbers `k[ε]/(ε²)` & Matrix / `GL_n` Algebra over `DualNumber k` -/

section DualMatrixAlgebra

variable {k : Type*} [CommRing k]

/-- Construct an element `a + ε b` of the dual-numbers ring `DualNumber k = k[ε]/(ε²)`. -/
def dualMk (a b : k) : DualNumber k :=
  TrivSqZeroExt.inl a + TrivSqZeroExt.inr b

@[simp] theorem dualMk_fst (a b : k) : (dualMk a b).fst = a := by
  simp [dualMk]

@[simp] theorem dualMk_snd (a b : k) : (dualMk a b).snd = b := by
  simp [dualMk]

theorem dualMk_eta (x : DualNumber k) : dualMk x.fst x.snd = x := by
  apply TrivSqZeroExt.ext <;> simp

theorem dualMk_add (a₁ b₁ a₂ b₂ : k) :
    dualMk a₁ b₁ + dualMk a₂ b₂ = dualMk (a₁ + a₂) (b₁ + b₂) := by
  apply TrivSqZeroExt.ext <;> simp

theorem dualMk_neg (a b : k) :
    -(dualMk a b) = dualMk (-a) (-b) := by
  apply TrivSqZeroExt.ext <;> simp

theorem dualMk_mul (a₁ b₁ a₂ b₂ : k) :
    dualMk a₁ b₁ * dualMk a₂ b₂ = dualMk (a₁ * a₂) (a₁ * b₂ + b₁ * a₂) := by
  apply TrivSqZeroExt.ext
  · simp
  · simp [smul_eq_mul]

theorem dualMk_zero : (dualMk (0 : k) 0) = 0 := by
  apply TrivSqZeroExt.ext <;> simp

theorem dualMk_one : (dualMk (1 : k) 0) = 1 := by
  apply TrivSqZeroExt.ext <;> simp

/-- `ε² = 0` in `DualNumber k`. -/
theorem dual_eps_sq : (DualNumber.eps : DualNumber k) ^ 2 = 0 := by
  rw [sq, DualNumber.eps_mul_eps]

/-- Matrix `A + ε B ∈ M_n(k[ε]/(ε²))` formed from `A, B : Matrix n n k`. -/
def matDual {n : Type*} (A B : Matrix n n k) : Matrix n n (DualNumber k) :=
  Matrix.of fun i j => dualMk (A i j) (B i j)

/-- Second-component (`ε`-coefficient) matrix additive homomorphism `M_n(k[ε]/(ε²)) →+ M_n(k)`. -/
def matSnd {n : Type*} : Matrix n n (DualNumber k) →+ Matrix n n k where
  toFun M := Matrix.of fun i j => (M i j).snd
  map_zero' := Matrix.ext fun _ _ => by simp
  map_add' _ _ := Matrix.ext fun _ _ => by simp

@[simp] theorem matDual_apply {n : Type*} (A B : Matrix n n k) (i j : n) :
    matDual A B i j = dualMk (A i j) (B i j) := rfl

@[simp] theorem matSnd_apply {n : Type*} (M : Matrix n n (DualNumber k)) (i j : n) :
    matSnd M i j = (M i j).snd := rfl

@[simp] theorem matSnd_matDual {n : Type*} (A B : Matrix n n k) : matSnd (matDual A B) = B :=
  Matrix.ext fun _ _ => by simp

theorem matDual_add {n : Type*} (A₁ B₁ A₂ B₂ : Matrix n n k) :
    matDual A₁ B₁ + matDual A₂ B₂ = matDual (A₁ + A₂) (B₁ + B₂) :=
  Matrix.ext fun i j => by
    change dualMk (A₁ i j) (B₁ i j) + dualMk (A₂ i j) (B₂ i j) =
      dualMk (A₁ i j + A₂ i j) (B₁ i j + B₂ i j)
    exact dualMk_add _ _ _ _

/-- Product of `1 + ε f(i)` over a finite set equals `1 + ε ∑ f(i)`. -/
theorem prod_dualMk_one {ι : Type*} (s : Finset ι) (f : ι → k) :
    ∏ i ∈ s, dualMk (1 : k) (f i) = dualMk (1 : k) (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [dualMk_one]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, ih, dualMk_mul, Finset.sum_insert ha]
    simp [add_comm]

/-- In `DualNumber k`, the product of two nilpotent elements (`fst = 0`) is `0`. -/
theorem dual_mul_eq_zero_of_fst_zero {x y : DualNumber k} (hx : x.fst = 0) (hy : y.fst = 0) :
    x * y = 0 := by
  apply TrivSqZeroExt.ext
  · simp [hx, hy]
  · simp [hx, hy]

section MatrixGL

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- First-component (mod `ε`) matrix reduction ring homomorphism `M_n(k[ε]/(ε²)) →+* M_n(k)`. -/
def matFst : Matrix n n (DualNumber k) →+* Matrix n n k :=
  RingHom.mapMatrix (TrivSqZeroExt.fstHom k k k)

@[simp] theorem matFst_apply (M : Matrix n n (DualNumber k)) (i j : n) :
    matFst M i j = (M i j).fst := rfl

@[simp] theorem matFst_matDual (A B : Matrix n n k) : matFst (matDual A B) = A :=
  Matrix.ext fun _ _ => by simp

theorem matDual_eta (M : Matrix n n (DualNumber k)) : matDual (matFst M) (matSnd M) = M :=
  Matrix.ext fun i j => dualMk_eta (M i j)

theorem matDual_ext_iff {A₁ B₁ A₂ B₂ : Matrix n n k} :
    matDual A₁ B₁ = matDual A₂ B₂ ↔ A₁ = A₂ ∧ B₁ = B₂ := by
  constructor
  · intro h
    exact ⟨by simpa using congrArg matFst h, by simpa using congrArg matSnd h⟩
  · rintro ⟨rfl, rfl⟩; rfl

omit [Fintype n] in
theorem matDual_one : matDual (1 : Matrix n n k) 0 = 1 :=
  Matrix.ext fun i j => by
    by_cases h : i = j
    · subst h
      simp [Matrix.one_apply_eq, dualMk_one]
    · simp [Matrix.one_apply_ne h, dualMk_zero]

omit [DecidableEq n] in
/-- Exact dual-matrix multiplication formula: `(A₁ + ε B₁)(A₂ + ε B₂) = A₁ A₂ + ε (A₁ B₂ + B₁ A₂)`. -/
theorem matDual_mul (A₁ B₁ A₂ B₂ : Matrix n n k) :
    matDual A₁ B₁ * matDual A₂ B₂ = matDual (A₁ * A₂) (A₁ * B₂ + B₁ * A₂) :=
  Matrix.ext fun i j => by
    apply TrivSqZeroExt.ext
    · simp only [Matrix.mul_apply, matDual_apply, TrivSqZeroExt.fst_sum, TrivSqZeroExt.fst_mul,
        dualMk_fst]
    · simp only [Matrix.mul_apply, Matrix.add_apply, matDual_apply, TrivSqZeroExt.snd_sum,
        TrivSqZeroExt.snd_mul, dualMk_fst, dualMk_snd, smul_eq_mul, op_smul_eq_mul]
      rw [← Finset.sum_add_distrib]

/-- Mod-`ε` reduction homomorphism `GL_n(k[ε]/(ε²)) →* GL_n(k)`. -/
def reduceGL : Matrix.GeneralLinearGroup n (DualNumber k) →* Matrix.GeneralLinearGroup n k :=
  Units.map (matFst (k := k) (n := n)).toMonoidHom

@[simp] theorem reduceGL_val (U : Matrix.GeneralLinearGroup n (DualNumber k)) :
    (reduceGL U).val = matFst U.val := rfl

/-- The strict-equivalence group element `1 + ε A ∈ GL_n(k[ε]/(ε²))` with inverse `1 - ε A`. -/
def epsUnit (A : Matrix n n k) : Matrix.GeneralLinearGroup n (DualNumber k) where
  val := matDual 1 A
  inv := matDual 1 (-A)
  val_inv := by rw [matDual_mul]; simp [matDual_one]
  inv_val := by rw [matDual_mul]; simp [matDual_one]

@[simp] theorem epsUnit_val (A : Matrix n n k) :
    (epsUnit A).val = matDual 1 A := rfl

@[simp] theorem epsUnit_inv_val (A : Matrix n n k) :
    (epsUnit A)⁻¹.val = matDual 1 (-A) := rfl

@[simp] theorem reduceGL_epsUnit (A : Matrix n n k) : reduceGL (epsUnit A) = 1 := by
  apply Units.ext
  simp

theorem epsUnit_zero : epsUnit (0 : Matrix n n k) = 1 := by
  apply Units.ext
  simp [matDual_one]

theorem epsUnit_mul (A B : Matrix n n k) : epsUnit A * epsUnit B = epsUnit (A + B) := by
  apply Units.ext
  change matDual 1 A * matDual 1 B = matDual 1 (A + B)
  rw [matDual_mul]
  simp [add_comm]

theorem epsUnit_inv (A : Matrix n n k) : (epsUnit A)⁻¹ = epsUnit (-A) := by
  apply Units.ext
  rfl

/-- Canonical constant embedding `GL_n(k) →* GL_n(k[ε]/(ε²))` sending `u ↦ u + ε · 0`. -/
def inlGL : Matrix.GeneralLinearGroup n k →* Matrix.GeneralLinearGroup n (DualNumber k) :=
  Units.map (RingHom.mapMatrix (TrivSqZeroExt.inlHom k k)).toMonoidHom

@[simp] theorem inlGL_val (u : Matrix.GeneralLinearGroup n k) :
    (inlGL u).val = matDual u.val 0 :=
  Matrix.ext fun i j => by
    apply TrivSqZeroExt.ext <;> simp [inlGL, dualMk]

/-- First-order matrix lift `(1 + ε C) u = u + ε (C u) ∈ GL_n(k[ε]/(ε²))` for `u ∈ GL_n(k)`
and `C ∈ M_n(k)`. -/
def liftGL (u : Matrix.GeneralLinearGroup n k) (C : Matrix n n k) :
    Matrix.GeneralLinearGroup n (DualNumber k) :=
  epsUnit C * inlGL u

theorem liftGL_val (u : Matrix.GeneralLinearGroup n k) (C : Matrix n n k) :
    (liftGL u C).val = matDual u.val (C * u.val) := by
  change (epsUnit C).val * (inlGL u).val = _
  rw [epsUnit_val, inlGL_val, matDual_mul]
  simp

@[simp] theorem reduceGL_liftGL (u : Matrix.GeneralLinearGroup n k) (C : Matrix n n k) :
    reduceGL (liftGL u C) = u := by
  apply Units.ext
  simp [liftGL_val]

theorem liftGL_injective (u : Matrix.GeneralLinearGroup n k) :
    Function.Injective (liftGL u) := by
  intro C₁ C₂ h
  have hval : matDual u.val (C₁ * u.val) = matDual u.val (C₂ * u.val) := by
    simpa [liftGL_val] using congrArg Units.val h
  have hsnd : C₁ * u.val = C₂ * u.val := (matDual_ext_iff.mp hval).2
  calc C₁ = C₁ * u.val * u⁻¹.val := by rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
    _ = C₂ * u.val * u⁻¹.val := by rw [hsnd]
    _ = C₂ := by rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]

/-- Every `U ∈ GL_n(k[ε]/(ε²))` reducing to `u ∈ GL_n(k)` decomposes uniquely as
`U = (1 + ε C) u` with `C = matSnd(U) · u⁻¹`. -/
theorem eq_liftGL_of_reduceGL {U : Matrix.GeneralLinearGroup n (DualNumber k)}
    {u : Matrix.GeneralLinearGroup n k} (hU : reduceGL U = u) :
    U = liftGL u (matSnd U.val * u⁻¹.val) := by
  apply Units.ext
  rw [liftGL_val, ← matDual_eta U.val]
  have hfst : matFst U.val = u.val := by
    simpa using congrArg Units.val hU
  rw [hfst, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one, matSnd_matDual]

/-- **Product Formula for First-Order Matrix Lifts**:
`(1 + ε C₁) u₁ · (1 + ε C₂) u₂ = (1 + ε (C₁ + u₁ C₂ u₁⁻¹)) (u₁ u₂)`. -/
theorem liftGL_mul_liftGL (u₁ u₂ : Matrix.GeneralLinearGroup n k) (C₁ C₂ : Matrix n n k) :
    liftGL u₁ C₁ * liftGL u₂ C₂ =
      liftGL (u₁ * u₂) (C₁ + u₁.val * C₂ * u₁⁻¹.val) := by
  apply Units.ext
  change (liftGL u₁ C₁).val * (liftGL u₂ C₂).val =
    (liftGL (u₁ * u₂) (C₁ + u₁.val * C₂ * u₁⁻¹.val)).val
  rw [liftGL_val, liftGL_val, liftGL_val, matDual_mul, matDual_ext_iff]
  refine ⟨rfl, ?_⟩
  change u₁.val * (C₂ * u₂.val) + C₁ * u₁.val * u₂.val =
    (C₁ + u₁.val * C₂ * u₁⁻¹.val) * (u₁.val * u₂.val)
  rw [Matrix.add_mul, add_comm]
  congr 1
  · rw [Matrix.mul_assoc]
  · calc u₁.val * (C₂ * u₂.val)
        = u₁.val * C₂ * (u₁⁻¹.val * u₁.val) * u₂.val := by
            rw [Units.inv_mul, Matrix.mul_one, Matrix.mul_assoc]
      _ = u₁.val * C₂ * u₁⁻¹.val * (u₁.val * u₂.val) := by simp [Matrix.mul_assoc]

/-- **Conjugation Formula by `1 + ε A`**:
`(1 + ε A) · ((1 + ε C) u) · (1 + ε A)⁻¹ = (1 + ε (C + A - u A u⁻¹)) u`. -/
theorem epsUnit_conj_liftGL (A : Matrix n n k) (u : Matrix.GeneralLinearGroup n k)
    (C : Matrix n n k) :
    epsUnit A * liftGL u C * (epsUnit A)⁻¹ =
      liftGL u (C + A - u.val * A * u⁻¹.val) := by
  apply Units.ext
  change (epsUnit A).val * (liftGL u C).val * (epsUnit A)⁻¹.val =
    (liftGL u (C + A - u.val * A * u⁻¹.val)).val
  rw [epsUnit_val, liftGL_val, epsUnit_inv_val, liftGL_val, matDual_mul, matDual_mul,
    matDual_ext_iff]
  refine ⟨by simp, ?_⟩
  simp only [Matrix.one_mul, Matrix.mul_one, Matrix.mul_neg, Matrix.sub_mul, Matrix.add_mul]
  have hcancel : u.val * A * u⁻¹.val * u.val = u.val * A := by
    rw [Matrix.mul_assoc (u.val * A), Units.inv_mul, Matrix.mul_one]
  rw [hcancel]
  abel

/-! ### Lie-Algebra Determinant Identity `det(1 + ε C) = 1 + ε tr(C)` -/

/-- **Exact First-Order Determinant Identity (Lie Algebra of `SL_n`)**:
for every `C : Matrix n n k`, `det(1 + ε C) = 1 + ε tr(C)`! -/
theorem det_matDual_one (C : Matrix n n k) :
    Matrix.det (matDual (1 : Matrix n n k) C) = dualMk (1 : k) (Matrix.trace C) := by
  classical
  rw [Matrix.det_apply]
  rw [Finset.sum_eq_single (1 : Equiv.Perm n)]
  · simp only [Equiv.Perm.sign_one, Equiv.Perm.coe_one, id_eq]
    have hdiag : ∀ i : n, matDual (1 : Matrix n n k) C i i = dualMk 1 (C i i) := fun i => by
      simp [Matrix.one_apply_eq]
    simp_rw [hdiag]
    rw [prod_dualMk_one]
    simp [Matrix.trace]
  · intro σ _ hσ
    have hne : ∃ i₁ : n, σ i₁ ≠ i₁ := by
      by_contra hall
      push Not at hall
      exact hσ (Equiv.ext hall)
    obtain ⟨i₁, hi₁⟩ := hne
    let i₂ : n := σ i₁
    have h12 : i₂ ≠ i₁ := hi₁
    have hi₂ : σ i₂ ≠ i₂ := fun heq => hi₁ (σ.injective heq)
    have hfst1 : (matDual (1 : Matrix n n k) C (σ i₁) i₁).fst = 0 := by
      simp [Matrix.one_apply_ne hi₁]
    have hfst2 : (matDual (1 : Matrix n n k) C (σ i₂) i₂).fst = 0 := by
      simp [Matrix.one_apply_ne hi₂]
    have hprod0 : ∏ i : n, matDual (1 : Matrix n n k) C (σ i) i = 0 := by
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i₁)]
      rw [← Finset.mul_prod_erase (Finset.univ.erase i₁) _
        (Finset.mem_erase.mpr ⟨h12, Finset.mem_univ i₂⟩)]
      rw [← mul_assoc, dual_mul_eq_zero_of_fst_zero hfst1 hfst2, zero_mul]
    rw [hprod0, smul_zero]
  · intro h; exact absurd (Finset.mem_univ 1) h

/-- Determinant of a first-order lift: `det((1 + ε C) u) = det(u) + ε (det(u) · tr(C))`. -/
theorem det_liftGL (u : Matrix.GeneralLinearGroup n k) (C : Matrix n n k) :
    Matrix.det (liftGL u C).val =
      dualMk (Matrix.det u.val) (Matrix.det u.val * Matrix.trace C) := by
  change Matrix.det ((epsUnit C).val * (inlGL u).val) = _
  rw [Matrix.det_mul, epsUnit_val, det_matDual_one]
  have hinl : Matrix.det (inlGL u).val = dualMk (Matrix.det u.val) 0 := by
    have hmap : (inlGL u).val = (TrivSqZeroExt.inlHom k k).mapMatrix u.val := rfl
    rw [hmap, ← RingHom.map_det]
    apply TrivSqZeroExt.ext <;> simp
  rw [hinl, dualMk_mul]
  simp [mul_comm]

/-- A first-order lift `(1 + ε C) u` preserves the determinant (`det((1 + ε C) u) = inl(det u)`)
**if and only if** `tr(C) = 0`! -/
theorem det_liftGL_eq_inl_iff_trace_zero (u : Matrix.GeneralLinearGroup n k) (C : Matrix n n k) :
    Matrix.det (liftGL u C).val = TrivSqZeroExt.inl (Matrix.det u.val) ↔ Matrix.trace C = 0 := by
  rw [det_liftGL]
  have hunit : IsUnit (Matrix.det u.val) := (Matrix.isUnit_iff_isUnit_det _).mp u.isUnit
  constructor
  · intro h
    have hsnd := congrArg TrivSqZeroExt.snd h
    simp only [dualMk_snd, TrivSqZeroExt.snd_inl] at hsnd
    rw [mul_comm] at hsnd
    exact hunit.mul_left_eq_zero.mp hsnd
  · intro htr
    rw [htr, mul_zero]
    apply TrivSqZeroExt.ext <;> simp

end MatrixGL

end DualMatrixAlgebra

/-! ## Section 2: Adjoint Representation `Ad(ρ̄)` & the Exact Mazur Tangent-Space Isomorphism -/

section MazurTangentSpace

variable {k : Type*} [CommRing k]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {G : Type*} [Group G]

/-- The adjoint representation `Ad(ρ̄) = M_n(k)` equipped with the conjugation action
`g • X = ρ̄(g) X ρ̄(g)⁻¹` of a residual representation `ρ̄ : G →* GL_n(k)`. -/
structure AdRep (ρbar : G →* Matrix.GeneralLinearGroup n k) where
  val : Matrix n n k

namespace AdRep

variable {ρbar : G →* Matrix.GeneralLinearGroup n k}

@[ext]
theorem ext {X Y : AdRep ρbar} (h : X.val = Y.val) : X = Y := by
  cases X; cases Y; congr

instance : AddCommGroup (AdRep ρbar) where
  add X Y := ⟨X.val + Y.val⟩
  zero := ⟨0⟩
  neg X := ⟨-X.val⟩
  add_assoc _ _ _ := ext (add_assoc _ _ _)
  zero_add _ := ext (zero_add _)
  add_zero _ := ext (add_zero _)
  add_comm _ _ := ext (add_comm _ _)
  neg_add_cancel _ := ext (neg_add_cancel _)
  nsmul m X := ⟨m • X.val⟩
  nsmul_zero _ := ext (zero_nsmul _)
  nsmul_succ m X := ext (succ_nsmul X.val m)
  zsmul m X := ⟨m • X.val⟩
  zsmul_zero' _ := ext (zero_zsmul _)
  zsmul_succ' m X := ext (by
    change ((m + 1 : ℕ) : ℤ) • X.val = (m : ℤ) • X.val + X.val
    rw [Nat.cast_add, Nat.cast_one, add_zsmul, one_zsmul])
  zsmul_neg' m X := ext (by
    change Int.negSucc m • X.val = -(((m + 1 : ℕ) : ℤ) • X.val)
    rw [negSucc_zsmul, natCast_zsmul])

@[simp] theorem add_val (X Y : AdRep ρbar) : (X + Y).val = X.val + Y.val := rfl
@[simp] theorem zero_val : (0 : AdRep ρbar).val = 0 := rfl
@[simp] theorem neg_val (X : AdRep ρbar) : (-X).val = -X.val := rfl
@[simp] theorem sub_val (X Y : AdRep ρbar) : (X - Y).val = X.val - Y.val := by
  change (X + -Y).val = _
  simp [sub_eq_add_neg]

instance : Module k (AdRep ρbar) where
  smul c X := ⟨c • X.val⟩
  one_smul _ := ext (one_smul _ _)
  mul_smul _ _ _ := ext (mul_smul _ _ _)
  smul_zero _ := ext (smul_zero _)
  smul_add _ _ _ := ext (smul_add _ _ _)
  add_smul _ _ _ := ext (add_smul _ _ _)
  zero_smul _ := ext (zero_smul _ _)

@[simp] theorem smul_k_val (c : k) (X : AdRep ρbar) : (c • X).val = c • X.val := rfl

/-- Conjugation action `g • X = ρ̄(g) X ρ̄(g)⁻¹` on `Ad(ρ̄)`. -/
instance : DistribMulAction G (AdRep ρbar) where
  smul g X := ⟨(ρbar g).val * X.val * (ρbar g)⁻¹.val⟩
  one_smul X := ext (by
    change (ρbar 1).val * X.val * (ρbar 1)⁻¹.val = X.val
    rw [map_one]
    simp)
  mul_smul g h X := ext (by
    change (ρbar (g * h)).val * X.val * (ρbar (g * h))⁻¹.val =
      (ρbar g).val * ((ρbar h).val * X.val * (ρbar h)⁻¹.val) * (ρbar g)⁻¹.val
    rw [map_mul, mul_inv_rev]
    simp [Matrix.mul_assoc])
  smul_zero g := ext (by
    change (ρbar g).val * 0 * (ρbar g)⁻¹.val = 0
    simp)
  smul_add g X Y := ext (by
    change (ρbar g).val * (X.val + Y.val) * (ρbar g)⁻¹.val =
      (ρbar g).val * X.val * (ρbar g)⁻¹.val + (ρbar g).val * Y.val * (ρbar g)⁻¹.val
    rw [Matrix.mul_add, Matrix.add_mul])

@[simp] theorem smul_G_val (g : G) (X : AdRep ρbar) :
    (g • X).val = (ρbar g).val * X.val * (ρbar g)⁻¹.val := rfl

instance : SMulCommClass G k (AdRep ρbar) where
  smul_comm g c X := ext (by
    change (ρbar g).val * (c • X.val) * (ρbar g)⁻¹.val =
      c • ((ρbar g).val * X.val * (ρbar g)⁻¹.val)
    simp)

/-- `Ad(ρ̄)` is `k`-linearly isomorphic to `Matrix n n k`. -/
def toMatrixLinearEquiv : AdRep ρbar ≃ₗ[k] Matrix n n k where
  toFun := AdRep.val
  invFun := AdRep.mk
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- Trace-zero adjoint submodule `Ad⁰(ρ̄) = { X ∈ M_n(k) | tr(X) = 0 }`. -/
def Ad0Submodule (ρbar : G →* Matrix.GeneralLinearGroup n k) : Submodule k (AdRep ρbar) where
  carrier := { X | Matrix.trace X.val = 0 }
  add_mem' {X Y} hX hY := by
    change Matrix.trace (X.val + Y.val) = 0
    rw [Matrix.trace_add]
    exact by rw [show Matrix.trace X.val = 0 from hX, show Matrix.trace Y.val = 0 from hY, add_zero]
  zero_mem' := by change Matrix.trace (0 : Matrix n n k) = 0; simp
  smul_mem' c {X} hX := by
    change Matrix.trace (c • X.val) = 0
    rw [Matrix.trace_smul, show Matrix.trace X.val = 0 from hX, smul_zero]

/-- `Ad⁰(ρ̄)` is `G`-stable under conjugation because `tr(u X u⁻¹) = tr(X)`. -/
instance : DistribMulAction G (Ad0Submodule ρbar) where
  smul g X := ⟨g • X.1, by
    change Matrix.trace ((ρbar g).val * X.1.val * (ρbar g)⁻¹.val) = 0
    rw [Matrix.trace_mul_cycle, Units.inv_mul, Matrix.one_mul]
    exact X.2⟩
  one_smul X := Subtype.ext (one_smul G X.1)
  mul_smul g h X := Subtype.ext (mul_smul g h X.1)
  smul_zero g := Subtype.ext (smul_zero g)
  smul_add g X Y := Subtype.ext (smul_add g X.1 Y.1)

instance : SMulCommClass G k (Ad0Submodule ρbar) where
  smul_comm g c X := Subtype.ext (smul_comm g c X.1)

end AdRep

/-! ### `k`-Module Structure on `Z¹(G, M)` and `H¹(G, M)` -/

section CohomologyModule

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [DistribMulAction G M] [SMulCommClass G R M]

/-- Scalar multiplication on 1-cocycles `Z¹(G, M)` when `G` acts `R`-linearly on `M`. -/
instance cocycle1Module : Module R (Cocycle1 G M) where
  smul r c :=
    { toFun := fun g => r • c g
      cocycle' := fun g h => by rw [c.map_mul, smul_add, ← smul_comm g r (c h)] }
  one_smul _ := Cocycle1.ext fun g => one_smul R _
  mul_smul _ _ _ := Cocycle1.ext fun g => mul_smul _ _ _
  smul_zero _ := Cocycle1.ext fun g => smul_zero _
  smul_add _ _ _ := Cocycle1.ext fun g => smul_add _ _ _
  add_smul _ _ _ := Cocycle1.ext fun g => add_smul _ _ _
  zero_smul _ := Cocycle1.ext fun g => zero_smul _ _

@[simp] theorem cocycle1_smul_apply (r : R) (c : Cocycle1 G M) (g : G) :
    (r • c) g = r • c g := rfl

/-- `R`-linear 1-coboundary map `d⁰ : M →ₗ[R] Z¹(G, M)`. -/
def coboundary1Lin (R G M : Type*) [CommRing R] [Group G] [AddCommGroup M] [Module R M]
    [DistribMulAction G M] [SMulCommClass G R M] : M →ₗ[R] Cocycle1 G M where
  toFun := coboundary1 G M
  map_add' := (coboundary1 G M).map_add
  map_smul' r m := Cocycle1.ext fun g => by
    change g • (r • m) - r • m = r • (g • m - m)
    rw [smul_comm, smul_sub]

/-- Coboundary submodule `B¹(G, M) ≤ Z¹(G, M)` over `R`. -/
def coboundary1Submodule (R G M : Type*) [CommRing R] [Group G] [AddCommGroup M] [Module R M]
    [DistribMulAction G M] [SMulCommClass G R M] : Submodule R (Cocycle1 G M) :=
  LinearMap.range (coboundary1Lin R G M)

theorem coboundary1Submodule_toAddSubgroup (R G M : Type*) [CommRing R] [Group G]
    [AddCommGroup M] [Module R M] [DistribMulAction G M] [SMulCommClass G R M] :
    (coboundary1Submodule R G M).toAddSubgroup = (coboundary1 G M).range := by
  ext c
  rfl

/-- `R`-module model of `H¹(G, M) := Z¹(G, M) ⧸ B¹(G, M)` (canonically additively isomorphic to
`Stage2GaloisCohomology.H1Group G M`). -/
abbrev H1Space (R G M : Type*) [CommRing R] [Group G] [AddCommGroup M] [Module R M]
    [DistribMulAction G M] [SMulCommClass G R M] : Type _ :=
  Cocycle1 G M ⧸ coboundary1Submodule R G M

/-- Canonical additive equivalence `H1Space R G M ≃+ Stage2GaloisCohomology.H1Group G M`. -/
def h1SpaceEquivH1Group (R G M : Type*) [CommRing R] [Group G] [AddCommGroup M] [Module R M]
    [DistribMulAction G M] [SMulCommClass G R M] :
    H1Space R G M ≃+ H1Group G M :=
  QuotientAddGroup.quotientAddEquivOfEq (coboundary1Submodule_toAddSubgroup R G M)

end CohomologyModule

/-! ### First-Order Matrix Deformations `ρ_ε = (1 + ε c) ρ̄` & Exact Mazur Bijection -/

/-- A **first-order lift** of `ρ̄ : G →* GL_n(k)` to `GL_n(k[ε]/(ε²))`: a group homomorphism
`ρ_ε : G →* GL_n(k[ε]/(ε²))` reducing mod `ε` to `ρ̄`. -/
structure FirstOrderLift (ρbar : G →* Matrix.GeneralLinearGroup n k) where
  toHom : G →* Matrix.GeneralLinearGroup n (DualNumber k)
  reduce_eq : ∀ g : G, reduceGL (toHom g) = ρbar g

namespace FirstOrderLift

variable {ρbar : G →* Matrix.GeneralLinearGroup n k}

@[ext]
theorem ext {ρ₁ ρ₂ : FirstOrderLift ρbar} (h : ∀ g, ρ₁.toHom g = ρ₂.toHom g) : ρ₁ = ρ₂ := by
  cases ρ₁; cases ρ₂
  congr
  exact MonoidHom.ext h

/-- Extract the matrix perturbation `c(g) = matSnd(ρ_ε(g)) · ρ̄(g)⁻¹ ∈ M_n(k)` from a
first-order lift `ρ_ε`. -/
def toMatrixFun (ρ : FirstOrderLift ρbar) (g : G) : Matrix n n k :=
  matSnd (ρ.toHom g).val * (ρbar g)⁻¹.val

/-- Reconstruction identity: every first-order lift has the exact form
`ρ_ε(g) = (1 + ε c(g)) ρ̄(g)`. -/
theorem eq_liftGL_toMatrixFun (ρ : FirstOrderLift ρbar) (g : G) :
    ρ.toHom g = liftGL (ρbar g) (ρ.toMatrixFun g) :=
  eq_liftGL_of_reduceGL (ρ.reduce_eq g)

/-- **Exact Mazur Cocycle Characterization**:
`g ↦ (1 + ε c(g)) ρ̄(g)` is a group homomorphism `G →* GL_n(k[ε]/(ε²))` **if and only if**
`c : G → M_n(k)` satisfies the exact 1-cocycle identity
`c(g h) = c(g) + ρ̄(g) c(h) ρ̄(g)⁻¹`! -/
theorem liftGL_mul_iff_cocycle (c : G → Matrix n n k) :
    (∀ g h : G, liftGL (ρbar (g * h)) (c (g * h)) =
      liftGL (ρbar g) (c g) * liftGL (ρbar h) (c h)) ↔
      (∀ g h : G, c (g * h) =
        c g + (ρbar g).val * c h * (ρbar g)⁻¹.val) := by
  constructor
  · intro hmul g h
    have h1 := hmul g h
    rw [liftGL_mul_liftGL, ← map_mul] at h1
    exact liftGL_injective (ρbar (g * h)) h1
  · intro hcoc g h
    rw [liftGL_mul_liftGL, ← map_mul, hcoc g h]

/-- Build the 1-cocycle `c ∈ Z¹(G, Ad(ρ̄))` attached to a first-order lift `ρ_ε`. -/
def toCocycle (ρ : FirstOrderLift ρbar) : Cocycle1 G (AdRep ρbar) where
  toFun g := ⟨ρ.toMatrixFun g⟩
  cocycle' g h := by
    apply AdRep.ext
    have hmul : liftGL (ρbar (g * h)) (ρ.toMatrixFun (g * h)) =
        liftGL (ρbar g) (ρ.toMatrixFun g) * liftGL (ρbar h) (ρ.toMatrixFun h) := by
      rw [← ρ.eq_liftGL_toMatrixFun, ← ρ.eq_liftGL_toMatrixFun, ← ρ.eq_liftGL_toMatrixFun,
        map_mul]
    rw [liftGL_mul_liftGL, ← map_mul] at hmul
    exact liftGL_injective (ρbar (g * h)) hmul

/-- Build the first-order lift `ρ_ε(g) = (1 + ε c(g)) ρ̄(g)` from a 1-cocycle
`c ∈ Z¹(G, Ad(ρ̄))`. -/
def ofCocycle (c : Cocycle1 G (AdRep ρbar)) : FirstOrderLift ρbar where
  toHom :=
    { toFun := fun g => liftGL (ρbar g) (c g).val
      map_one' := by
        rw [map_one, c.map_one]
        apply Units.ext
        rw [liftGL_val]
        simp [matDual_one]
      map_mul' := fun g h => by
        rw [liftGL_mul_liftGL, ← map_mul]
        congr 1
        exact congrArg AdRep.val (c.map_mul g h) }
  reduce_eq g := reduceGL_liftGL (ρbar g) (c g).val

@[simp] theorem ofCocycle_apply (c : Cocycle1 G (AdRep ρbar)) (g : G) :
    (ofCocycle c).toHom g = liftGL (ρbar g) (c g).val := rfl

theorem ofCocycle_toCocycle (ρ : FirstOrderLift ρbar) : ofCocycle (toCocycle ρ) = ρ :=
  FirstOrderLift.ext fun g => (ρ.eq_liftGL_toMatrixFun g).symm

theorem toCocycle_ofCocycle (c : Cocycle1 G (AdRep ρbar)) : toCocycle (ofCocycle c) = c :=
  Cocycle1.ext fun g => AdRep.ext (by
    change matSnd (liftGL (ρbar g) (c g).val).val * (ρbar g)⁻¹.val = (c g).val
    rw [liftGL_val, matSnd_matDual, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one])

/-- **Exact Mazur Bijection (`FirstOrderLift ρ̄ ≃ Z¹(G, Ad(ρ̄))`)**:
first-order lifts of `ρ̄` to `GL_n(k[ε]/(ε²))` correspond bijectively to 1-cocycles
`Stage2GaloisCohomology.Cocycle1 G (AdRep ρbar)`! -/
def equivCocycle1 (ρbar : G →* Matrix.GeneralLinearGroup n k) :
    FirstOrderLift ρbar ≃ Cocycle1 G (AdRep ρbar) where
  toFun := toCocycle
  invFun := ofCocycle
  left_inv := ofCocycle_toCocycle
  right_inv := toCocycle_ofCocycle

/-- **Strict Equivalence of First-Order Lifts**: `ρ₁ ~ ρ₂` iff `ρ₂` is conjugate to `ρ₁` by an
element `1 + ε A ∈ ker(GL_n(k[ε]/(ε²)) → GL_n(k))`. -/
def StrictEquiv (ρ₁ ρ₂ : FirstOrderLift ρbar) : Prop :=
  ∃ A : Matrix n n k, ∀ g : G, ρ₂.toHom g = epsUnit A * ρ₁.toHom g * (epsUnit A)⁻¹

/-- **Exact Coboundary Equivalence**: two first-order lifts `ρ₁, ρ₂` are strictly equivalent
(conjugate by `1 + ε A`) **if and only if** their cocycles differ by a 1-coboundary
`c₂(g) - c₁(g) = ρ̄(g) B ρ̄(g)⁻¹ - B`! -/
theorem strictEquiv_iff_coboundary (ρ₁ ρ₂ : FirstOrderLift ρbar) :
    StrictEquiv ρ₁ ρ₂ ↔
      ∃ B : AdRep ρbar, ∀ g : G,
        (toCocycle ρ₂ g).val - (toCocycle ρ₁ g).val =
          (ρbar g).val * B.val * (ρbar g)⁻¹.val - B.val := by
  constructor
  · rintro ⟨A, hA⟩
    refine ⟨⟨-A⟩, fun g => ?_⟩
    have hg := hA g
    rw [ρ₁.eq_liftGL_toMatrixFun g, ρ₂.eq_liftGL_toMatrixFun g, epsUnit_conj_liftGL] at hg
    have hc : ρ₂.toMatrixFun g =
        ρ₁.toMatrixFun g + A - (ρbar g).val * A * (ρbar g)⁻¹.val :=
      liftGL_injective (ρbar g) hg
    change ρ₂.toMatrixFun g - ρ₁.toMatrixFun g =
      (ρbar g).val * (-A) * (ρbar g)⁻¹.val - (-A)
    rw [hc, Matrix.mul_neg, Matrix.neg_mul]
    abel
  · rintro ⟨B, hB⟩
    refine ⟨-B.val, fun g => ?_⟩
    rw [ρ₁.eq_liftGL_toMatrixFun g, ρ₂.eq_liftGL_toMatrixFun g, epsUnit_conj_liftGL]
    congr 1
    have hg := hB g
    change ρ₂.toMatrixFun g - ρ₁.toMatrixFun g =
      (ρbar g).val * B.val * (ρbar g)⁻¹.val - B.val at hg
    rw [Matrix.mul_neg, Matrix.neg_mul]
    have hadd := congrArg (· + ρ₁.toMatrixFun g) hg
    simp only [sub_add_cancel] at hadd
    rw [hadd]
    abel

/-- Strict equivalence corresponds bijectively to membership in `(coboundary1 G (AdRep ρbar)).range`. -/
theorem strictEquiv_iff_mem_coboundary_range (ρ₁ ρ₂ : FirstOrderLift ρbar) :
    StrictEquiv ρ₁ ρ₂ ↔
      toCocycle ρ₂ - toCocycle ρ₁ ∈ (coboundary1 G (AdRep ρbar)).range := by
  rw [strictEquiv_iff_coboundary]
  constructor
  · rintro ⟨B, hB⟩
    exact ⟨B, Cocycle1.ext fun g => AdRep.ext (by simpa [coboundary1, Cocycle1.sub_apply] using (hB g).symm)⟩
  · rintro ⟨B, hB⟩
    refine ⟨B, fun g => ?_⟩
    have hg := congrArg (fun c : Cocycle1 G (AdRep ρbar) => (c g).val) hB
    simpa [coboundary1, Cocycle1.sub_apply] using hg.symm

theorem strictEquiv_equivalence (ρbar : G →* Matrix.GeneralLinearGroup n k) :
    Equivalence (StrictEquiv (ρbar := ρbar)) where
  refl ρ := ⟨0, fun g => by simp [epsUnit_zero]⟩
  symm := by
    rintro ρ₁ ρ₂ ⟨A, hA⟩
    refine ⟨-A, fun g => ?_⟩
    rw [hA g, ← epsUnit_inv]
    group
  trans := by
    rintro ρ₁ ρ₂ ρ₃ ⟨A, hA⟩ ⟨B, hB⟩
    refine ⟨B + A, fun g => ?_⟩
    rw [hB g, hA g, ← epsUnit_mul, mul_inv_rev]
    group

/-- Setoid of strict equivalence on first-order lifts of `ρ̄`. -/
def strictSetoid (ρbar : G →* Matrix.GeneralLinearGroup n k) : Setoid (FirstOrderLift ρbar) where
  r := StrictEquiv
  iseqv := strictEquiv_equivalence ρbar

end FirstOrderLift

/-- The **first-order deformation tangent space** `Deform_1(ρ̄)` = strict equivalence classes of
first-order lifts `ρ_ε : G →* GL_n(k[ε]/(ε²))` reducing to `ρ̄`. -/
def Deform1 (ρbar : G →* Matrix.GeneralLinearGroup n k) : Type _ :=
  Quotient (FirstOrderLift.strictSetoid ρbar)

/-- **THE MAZUR TANGENT-SPACE ISOMORPHISM (`Deform_1(ρ̄) ≃ H¹(G, Ad(ρ̄))`)**:
canonical bijection between strict equivalence classes of first-order matrix deformations
`ρ_ε = (1 + ε c) ρ̄` and the first Galois cohomology group
`Stage2GaloisCohomology.H1Group G (AdRep ρbar)`! -/
def mazurTangentEquiv (ρbar : G →* Matrix.GeneralLinearGroup n k) :
    Deform1 ρbar ≃ H1Group G (AdRep ρbar) where
  toFun := Quotient.lift
    (fun ρ => QuotientAddGroup.mk (FirstOrderLift.toCocycle ρ))
    (fun ρ₁ ρ₂ h => by
      rw [QuotientAddGroup.eq]
      have hmem : FirstOrderLift.toCocycle ρ₂ - FirstOrderLift.toCocycle ρ₁ ∈
          (coboundary1 G (AdRep ρbar)).range :=
        (FirstOrderLift.strictEquiv_iff_mem_coboundary_range ρ₁ ρ₂).mp h
      simpa [sub_eq_add_neg, add_comm] using hmem)
  invFun := Quotient.lift
    (fun c => Quotient.mk (FirstOrderLift.strictSetoid ρbar) (FirstOrderLift.ofCocycle c))
    (fun c₁ c₂ h => by
      apply Quotient.sound
      change FirstOrderLift.StrictEquiv (FirstOrderLift.ofCocycle c₁) (FirstOrderLift.ofCocycle c₂)
      rw [FirstOrderLift.strictEquiv_iff_mem_coboundary_range,
        FirstOrderLift.toCocycle_ofCocycle, FirstOrderLift.toCocycle_ofCocycle]
      have hmem : -c₁ + c₂ ∈ (coboundary1 G (AdRep ρbar)).range :=
        QuotientAddGroup.leftRel_apply.mp h
      simpa [sub_eq_add_neg, add_comm] using hmem)
  left_inv q := by
    induction q using Quotient.inductionOn' with
    | h ρ =>
      change Quotient.mk (FirstOrderLift.strictSetoid ρbar)
          (FirstOrderLift.ofCocycle (FirstOrderLift.toCocycle ρ)) =
        Quotient.mk (FirstOrderLift.strictSetoid ρbar) ρ
      rw [FirstOrderLift.ofCocycle_toCocycle]
  right_inv q := by
    induction q using Quotient.inductionOn' with
    | h c =>
      change (QuotientAddGroup.mk
          (FirstOrderLift.toCocycle (FirstOrderLift.ofCocycle c)) : H1Group G (AdRep ρbar)) =
        QuotientAddGroup.mk c
      rw [FirstOrderLift.toCocycle_ofCocycle]

/-- Canonical bijection `Deform_1(ρ̄) ≃ H1Space k G (AdRep ρbar)` onto the `k`-module model
of `H¹(G, Ad(ρ̄))`. -/
def mazurTangentEquivSpace (ρbar : G →* Matrix.GeneralLinearGroup n k) :
    Deform1 ρbar ≃ H1Space k G (AdRep ρbar) :=
  (mazurTangentEquiv ρbar).trans (h1SpaceEquivH1Group k G (AdRep ρbar)).symm.toEquiv

/-- Natural `AddCommGroup` structure on `Deform_1(ρ̄)` (Baer sum of first-order deformations
`[(1 + ε c₁) ρ̄] + [(1 + ε c₂) ρ̄] = [(1 + ε (c₁ + c₂)) ρ̄]`). -/
instance deform1AddCommGroup (ρbar : G →* Matrix.GeneralLinearGroup n k) :
    AddCommGroup (Deform1 ρbar) :=
  (mazurTangentEquivSpace ρbar).addCommGroup

/-- Natural `k`-module structure on `Deform_1(ρ̄)` (`a • [(1 + ε c) ρ̄] = [(1 + ε (a • c)) ρ̄]`). -/
instance deform1Module (ρbar : G →* Matrix.GeneralLinearGroup n k) :
    Module k (Deform1 ρbar) :=
  (mazurTangentEquivSpace ρbar).module k

/-- **Mazur `k`-Linear Tangent-Space Isomorphism**:
`Deform_1(ρ̄) ≃ₗ[k] H¹(G, Ad(ρ̄))` as `k`-vector spaces / `k`-modules! -/
def mazurTangentLinearEquiv (ρbar : G →* Matrix.GeneralLinearGroup n k) :
    Deform1 ρbar ≃ₗ[k] H1Space k G (AdRep ρbar) :=
  (mazurTangentEquivSpace ρbar).linearEquiv k

/-- **Fixed-Determinant First-Order Lifts** (`det(ρ_ε(g)) = det(ρ̄(g))` for all `g ∈ G`). -/
structure FixedDetLift (ρbar : G →* Matrix.GeneralLinearGroup n k) extends FirstOrderLift ρbar where
  det_eq : ∀ g : G,
    Matrix.det (toHom g).val = TrivSqZeroExt.inl (Matrix.det (ρbar g).val)

/-- Exact fixed-determinant cocycle bijection:
`FixedDetLift ρ̄ ≃ Z¹(G, Ad⁰(ρ̄))` (trace-zero 1-cocycles)! -/
def fixedDetLiftEquivCocycle1 (ρbar : G →* Matrix.GeneralLinearGroup n k) :
    FixedDetLift ρbar ≃ Cocycle1 G (AdRep.Ad0Submodule ρbar) where
  toFun ρ :=
    { toFun := fun g =>
        ⟨FirstOrderLift.toCocycle ρ.toFirstOrderLift g, by
          have hdet := ρ.det_eq g
          rw [ρ.toFirstOrderLift.eq_liftGL_toMatrixFun g, det_liftGL_eq_inl_iff_trace_zero] at hdet
          exact hdet⟩
      cocycle' := fun g h => Subtype.ext ((FirstOrderLift.toCocycle ρ.toFirstOrderLift).map_mul g h) }
  invFun c :=
    { toFirstOrderLift :=
        FirstOrderLift.ofCocycle
          { toFun := fun g => (c g).1
            cocycle' := fun g h => congrArg Subtype.val (c.map_mul g h) }
      det_eq := fun g => by
        rw [FirstOrderLift.ofCocycle_apply, det_liftGL_eq_inl_iff_trace_zero]
        exact (c g).2 }
  left_inv ρ := by
    cases ρ with | mk ρ0 hdet =>
      dsimp only
      congr 1
      exact FirstOrderLift.ofCocycle_toCocycle ρ0
  right_inv c :=
    Cocycle1.ext fun g => Subtype.ext (AdRep.ext (by
      change matSnd (liftGL (ρbar g) (c g).1.val).val * (ρbar g)⁻¹.val = (c g).1.val
      rw [liftGL_val, matSnd_matDual, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]))

/-- Strict equivalence on fixed-determinant lifts via conjugation by `1 + ε A` with `tr(A) = 0`. -/
def FixedDetStrictEquiv {ρbar : G →* Matrix.GeneralLinearGroup n k}
    (ρ₁ ρ₂ : FixedDetLift ρbar) : Prop :=
  ∃ A : AdRep.Ad0Submodule ρbar, ∀ g : G,
    ρ₂.toHom g = epsUnit A.1.val * ρ₁.toHom g * (epsUnit A.1.val)⁻¹

theorem fixedDetStrictEquiv_iff_mem_coboundary_range
    {ρbar : G →* Matrix.GeneralLinearGroup n k} (ρ₁ ρ₂ : FixedDetLift ρbar) :
    FixedDetStrictEquiv ρ₁ ρ₂ ↔
      fixedDetLiftEquivCocycle1 ρbar ρ₂ - fixedDetLiftEquivCocycle1 ρbar ρ₁ ∈
        (coboundary1 G (AdRep.Ad0Submodule ρbar)).range := by
  constructor
  · rintro ⟨A, hA⟩
    refine ⟨-A, Cocycle1.ext fun g => Subtype.ext (AdRep.ext ?_)⟩
    have hg := hA g
    rw [ρ₁.toFirstOrderLift.eq_liftGL_toMatrixFun g,
      ρ₂.toFirstOrderLift.eq_liftGL_toMatrixFun g, epsUnit_conj_liftGL] at hg
    have hc := liftGL_injective (ρbar g) hg
    have hgoal : (ρbar g).val * (-A.1.val) * (ρbar g)⁻¹.val - (-A.1.val) =
        ρ₂.toFirstOrderLift.toMatrixFun g - ρ₁.toFirstOrderLift.toMatrixFun g := by
      rw [hc, Matrix.mul_neg, Matrix.neg_mul]
      abel
    have hsmul : ((g • A).1).val = (ρbar g).val * A.1.val * (ρbar g)⁻¹.val := rfl
    simpa [coboundary1, Cocycle1.sub_apply, fixedDetLiftEquivCocycle1, FirstOrderLift.toCocycle,
      hsmul] using hgoal
  · rintro ⟨B, hB⟩
    refine ⟨-B, fun g => ?_⟩
    rw [ρ₁.toFirstOrderLift.eq_liftGL_toMatrixFun g,
      ρ₂.toFirstOrderLift.eq_liftGL_toMatrixFun g, epsUnit_conj_liftGL]
    congr 1
    have hg := congrArg (fun c : Cocycle1 G (AdRep.Ad0Submodule ρbar) => (c g).1.val) hB
    have hsmul : ((g • B).1).val = (ρbar g).val * B.1.val * (ρbar g)⁻¹.val := rfl
    have hg' : (ρbar g).val * B.1.val * (ρbar g)⁻¹.val - B.1.val =
        ρ₂.toFirstOrderLift.toMatrixFun g - ρ₁.toFirstOrderLift.toMatrixFun g := by
      simpa [coboundary1, Cocycle1.sub_apply, fixedDetLiftEquivCocycle1, FirstOrderLift.toCocycle,
        hsmul] using hg
    change ρ₂.toFirstOrderLift.toMatrixFun g =
      ρ₁.toFirstOrderLift.toMatrixFun g + (-B.1.val) -
        (ρbar g).val * (-B.1.val) * (ρbar g)⁻¹.val
    rw [Matrix.mul_neg, Matrix.neg_mul]
    have hadd := congrArg (· + ρ₁.toFirstOrderLift.toMatrixFun g) hg'.symm
    simp only [sub_add_cancel] at hadd
    rw [hadd]
    abel

theorem fixedDetStrictEquiv_equivalence (ρbar : G →* Matrix.GeneralLinearGroup n k) :
    Equivalence (FixedDetStrictEquiv (ρbar := ρbar)) where
  refl ρ := ⟨0, fun g => by simp [epsUnit_zero]⟩
  symm := by
    rintro ρ₁ ρ₂ ⟨A, hA⟩
    refine ⟨-A, fun g => ?_⟩
    change ρ₁.toHom g = epsUnit (-A.1.val) * ρ₂.toHom g * (epsUnit (-A.1.val))⁻¹
    rw [hA g, ← epsUnit_inv]
    group
  trans := by
    rintro ρ₁ ρ₂ ρ₃ ⟨A, hA⟩ ⟨B, hB⟩
    refine ⟨B + A, fun g => ?_⟩
    change ρ₃.toHom g = epsUnit (B.1.val + A.1.val) * ρ₁.toHom g * (epsUnit (B.1.val + A.1.val))⁻¹
    rw [hB g, hA g, ← epsUnit_mul, mul_inv_rev]
    group

/-- Setoid of fixed-determinant strict equivalence. -/
def fixedDetSetoid (ρbar : G →* Matrix.GeneralLinearGroup n k) : Setoid (FixedDetLift ρbar) where
  r := FixedDetStrictEquiv
  iseqv := fixedDetStrictEquiv_equivalence ρbar

/-- First-order fixed-determinant deformation tangent space `Deform_1^{det}(ρ̄)`. -/
def FixedDetDeform1 (ρbar : G →* Matrix.GeneralLinearGroup n k) : Type _ :=
  Quotient (fixedDetSetoid ρbar)

/-- **Fixed-Determinant Mazur Tangent-Space Isomorphism (`Deform_1^{det}(ρ̄) ≃ H¹(G, Ad⁰(ρ̄))`)**:
strict equivalence classes of fixed-determinant first-order lifts correspond bijectively to
`H¹(G, Ad⁰(ρ̄))` (trace-zero Galois cohomology)! -/
def fixedDetDeformEquivH1Ad0 (ρbar : G →* Matrix.GeneralLinearGroup n k) :
    FixedDetDeform1 ρbar ≃ H1Group G (AdRep.Ad0Submodule ρbar) where
  toFun := Quotient.lift
    (fun ρ => QuotientAddGroup.mk (fixedDetLiftEquivCocycle1 ρbar ρ))
    (fun ρ₁ ρ₂ h => by
      rw [QuotientAddGroup.eq]
      have hmem := (fixedDetStrictEquiv_iff_mem_coboundary_range ρ₁ ρ₂).mp h
      simpa [sub_eq_add_neg, add_comm] using hmem)
  invFun := Quotient.lift
    (fun c => Quotient.mk (fixedDetSetoid ρbar) ((fixedDetLiftEquivCocycle1 ρbar).symm c))
    (fun c₁ c₂ h => by
      apply Quotient.sound
      change FixedDetStrictEquiv _ _
      rw [fixedDetStrictEquiv_iff_mem_coboundary_range]
      rw [(fixedDetLiftEquivCocycle1 ρbar).apply_symm_apply,
        (fixedDetLiftEquivCocycle1 ρbar).apply_symm_apply]
      have hmem : -c₁ + c₂ ∈ (coboundary1 G (AdRep.Ad0Submodule ρbar)).range :=
        QuotientAddGroup.leftRel_apply.mp h
      simpa [sub_eq_add_neg, add_comm] using hmem)
  left_inv q := by
    induction q using Quotient.inductionOn' with
    | h ρ =>
      change Quotient.mk (fixedDetSetoid ρbar)
          ((fixedDetLiftEquivCocycle1 ρbar).symm (fixedDetLiftEquivCocycle1 ρbar ρ)) =
        Quotient.mk (fixedDetSetoid ρbar) ρ
      rw [(fixedDetLiftEquivCocycle1 ρbar).symm_apply_apply]
  right_inv q := by
    induction q using Quotient.inductionOn' with
    | h c =>
      change (QuotientAddGroup.mk
          (fixedDetLiftEquivCocycle1 ρbar ((fixedDetLiftEquivCocycle1 ρbar).symm c)) :
            H1Group G (AdRep.Ad0Submodule ρbar)) = QuotientAddGroup.mk c
      rw [(fixedDetLiftEquivCocycle1 ρbar).apply_symm_apply]

end MazurTangentSpace

/-! ## Section 3: Taylor–Wiles Auxiliary-Prime Selection & Dual-Selmer Killing (`H¹_{L_Q^⊥} = 0`) -/

section TaylorWilesDualKilling

section AbstractChebotarevKilling

variable {k V ι : Type*} [Field k] [AddCommGroup V] [Module k V]
variable {W : ι → Type*} [∀ v, AddCommGroup (W v)] [∀ v, Module k (W v)]

/-- Joint kernel `⋂_{v ∈ Q} ker(loc v)` inside `V` for a finite set of places `Q`. -/
def kerOn (loc : ∀ v : ι, V →ₗ[k] W v) (Q : Finset ι) : Submodule k V :=
  Q.inf fun v => LinearMap.ker (loc v)

@[simp] theorem kerOn_empty (loc : ∀ v : ι, V →ₗ[k] W v) : kerOn loc ∅ = ⊤ := by
  simp [kerOn]

theorem kerOn_insert [DecidableEq ι] (loc : ∀ v : ι, V →ₗ[k] W v) (v : ι) (Q : Finset ι) :
    kerOn loc (insert v Q) = LinearMap.ker (loc v) ⊓ kerOn loc Q := by
  simp [kerOn, Finset.inf_insert]

theorem mem_kerOn (loc : ∀ v : ι, V →ₗ[k] W v) (Q : Finset ι) (x : V) :
    x ∈ kerOn loc Q ↔ ∀ v ∈ Q, loc v x = 0 := by
  classical
  induction Q using Finset.induction_on with
  | empty => simp [kerOn_empty]
  | insert a s ha ih =>
    rw [kerOn_insert, Submodule.mem_inf, LinearMap.mem_ker, ih]
    constructor
    · rintro ⟨ha0, hs⟩ v hv
      rcases Finset.mem_insert.mp hv with rfl | hvs
      · exact ha0
      · exact hs v hvs
    · intro hall
      exact ⟨hall a (Finset.mem_insert_self a s), fun v hv => hall v (Finset.mem_insert_of_mem hv)⟩

section FinDimKilling

variable [FiniteDimensional k V]

/-- Single-step strict dimension drop: if `ψ ∈ U` has `loc v ψ ≠ 0`, then
`dim(U ⊓ ker(loc v)) < dim(U)`. -/
theorem finrank_inf_ker_lt (loc : ∀ v : ι, V →ₗ[k] W v) (U : Submodule k V)
    (v : ι) {ψ : V} (hψU : ψ ∈ U) (hψnz : loc v ψ ≠ 0) :
    Module.finrank k (U ⊓ LinearMap.ker (loc v) : Submodule k V) < Module.finrank k U := by
  have hlt : (U ⊓ LinearMap.ker (loc v) : Submodule k V) < U := by
    refine lt_of_le_of_ne inf_le_left ?_
    intro heq
    have hmem : ψ ∈ U ⊓ LinearMap.ker (loc v) := heq.symm ▸ hψU
    exact hψnz (LinearMap.mem_ker.mp hmem.2)
  exact Submodule.finrank_lt_finrank_of_lt hlt

/-- **Exact Single-Step Drop by `1`** when the target `W v` has dimension `≤ 1` (the Taylor–Wiles
codimension-1 local condition): if `ψ ∈ U` satisfies `loc v ψ ≠ 0`, then
`dim(U ⊓ ker(loc v)) + 1 = dim(U)`! -/
theorem finrank_inf_ker_add_one (loc : ∀ v : ι, V →ₗ[k] W v) [∀ v, FiniteDimensional k (W v)]
    (U : Submodule k V) (v : ι) (hW : Module.finrank k (W v) ≤ 1)
    {ψ : V} (hψU : ψ ∈ U) (hψnz : loc v ψ ≠ 0) :
    Module.finrank k (U ⊓ LinearMap.ker (loc v) : Submodule k V) + 1 = Module.finrank k U := by
  let f : U →ₗ[k] W v := (loc v).comp U.subtype
  have hrk := LinearMap.finrank_range_add_finrank_ker f
  have hker_eq : Module.finrank k (LinearMap.ker f) =
      Module.finrank k (U ⊓ LinearMap.ker (loc v) : Submodule k V) := by
    let e : LinearMap.ker f ≃ₗ[k] (U ⊓ LinearMap.ker (loc v) : Submodule k V) :=
      { toFun := fun x => ⟨x.1.1, x.1.2, x.2⟩
        invFun := fun y => ⟨⟨y.1, y.2.1⟩, y.2.2⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    exact e.finrank_eq
  have hran_le : Module.finrank k (LinearMap.range f) ≤ 1 :=
    (Submodule.finrank_le (LinearMap.range f)).trans hW
  have hran_ne : LinearMap.range f ≠ ⊥ := by
    intro hbot
    have hmem : loc v ψ ∈ LinearMap.range f := ⟨⟨ψ, hψU⟩, rfl⟩
    rw [hbot, Submodule.mem_bot] at hmem
    exact hψnz hmem
  have hran_pos : 0 < Module.finrank k (LinearMap.range f) :=
    Module.finrank_pos_iff_exists_ne_zero.mpr
      (let ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hran_ne;
        ⟨⟨y, hy⟩, by simpa using hy0⟩)
  have hran_eq : Module.finrank k (LinearMap.range f) = 1 := by omega
  rw [hran_eq, hker_eq] at hrk
  omega

/-- Dimension-step lower bound for intersecting with `kerOn loc S` when each `W v` has
dimension `≤ 1`. -/
theorem finrank_le_finrank_inf_kerOn_add_card [DecidableEq ι] (loc : ∀ v : ι, V →ₗ[k] W v)
    [∀ v, FiniteDimensional k (W v)]
    (hW : ∀ v : ι, Module.finrank k (W v) ≤ 1)
    (S : Finset ι) (T : Submodule k V) :
    Module.finrank k T ≤ Module.finrank k (T ⊓ kerOn loc S : Submodule k V) + S.card := by
  revert T
  induction S using Finset.induction_on with
  | empty => intro T; rw [kerOn_empty, inf_top_eq]; simp
  | insert a s ha ihs =>
    intro T
    rw [Finset.card_insert_of_notMem ha, kerOn_insert, ← inf_assoc]
    have h1 := ihs (T ⊓ LinearMap.ker (loc a))
    let f : T →ₗ[k] W a := (loc a).comp T.subtype
    have hrk := LinearMap.finrank_range_add_finrank_ker f
    have hker : Module.finrank k (LinearMap.ker f) =
        Module.finrank k (T ⊓ LinearMap.ker (loc a) : Submodule k V) := by
      let e : LinearMap.ker f ≃ₗ[k] (T ⊓ LinearMap.ker (loc a) : Submodule k V) :=
        { toFun := fun x => ⟨x.1.1, x.1.2, x.2⟩
          invFun := fun y => ⟨⟨y.1, y.2.1⟩, y.2.2⟩
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      exact e.finrank_eq
    have hran : Module.finrank k (LinearMap.range f) ≤ 1 :=
      (Submodule.finrank_le _).trans (hW a)
    omega

/-- **General Chebotarev Killing Induction**: if every nonzero `ψ ∈ V` is detected by some
`v : ι` (`loc v ψ ≠ 0`), then there exists a finite set `Q` of size `Q.card ≤ dim V` killing `V`
(`⋂_{v ∈ Q} ker(loc v) = ⊥`). -/
theorem exists_killing_set_le_finrank [DecidableEq ι] (loc : ∀ v : ι, V →ₗ[k] W v)
    (hCheb : ∀ ψ : V, ψ ≠ 0 → ∃ v : ι, loc v ψ ≠ 0) :
    ∃ Q : Finset ι, Q.card ≤ Module.finrank k V ∧ kerOn loc Q = ⊥ := by
  suffices hsub : ∀ n : ℕ, ∀ U : Submodule k V, Module.finrank k U ≤ n →
      ∃ Q : Finset ι, Q.card ≤ n ∧ U ⊓ kerOn loc Q = ⊥ by
    obtain ⟨Q, hcard, hbot⟩ := hsub (Module.finrank k V) ⊤ (by rw [finrank_top])
    rw [top_inf_eq] at hbot
    exact ⟨Q, hcard, hbot⟩
  intro n
  induction n with
  | zero =>
    intro U hU
    refine ⟨∅, by simp, ?_⟩
    rw [kerOn_empty, inf_top_eq]
    exact Submodule.finrank_eq_zero.mp (Nat.eq_zero_of_le_zero hU)
  | succ m ih =>
    intro U hU
    by_cases hbot : U = ⊥
    · refine ⟨∅, by simp, by rw [hbot, bot_inf_eq]⟩
    · obtain ⟨ψ, hψU, hψ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
      obtain ⟨v, hv⟩ := hCheb ψ hψ0
      have hlt := finrank_inf_ker_lt loc U v hψU hv
      obtain ⟨Q', hQ'card, hQ'bot⟩ := ih (U ⊓ LinearMap.ker (loc v)) (by omega)
      refine ⟨insert v Q', (Finset.card_insert_le v Q').trans (by omega), ?_⟩
      rw [kerOn_insert, ← inf_assoc]
      exact hQ'bot

/-- **Exact Taylor–Wiles Chebotarev Killing Induction**: when every prime `v : ι` has
1-dimensional local target (`dim(W v) ≤ 1`) and every nonzero `ψ ∈ V` is detected by some `v`,
induction on `d = dim V` produces a set `Q` of **EXACTLY `Q.card = dim V`** primes killing `V`
(`⋂_{v ∈ Q} ker(loc v) = ⊥`)! -/
theorem exists_exact_killing_set_of_dim_one [DecidableEq ι] (loc : ∀ v : ι, V →ₗ[k] W v)
    [∀ v, FiniteDimensional k (W v)]
    (hW : ∀ v : ι, Module.finrank k (W v) ≤ 1)
    (hCheb : ∀ ψ : V, ψ ≠ 0 → ∃ v : ι, loc v ψ ≠ 0) :
    ∃ Q : Finset ι, Q.card = Module.finrank k V ∧ kerOn loc Q = ⊥ := by
  suffices hsub : ∀ d : ℕ, ∀ U : Submodule k V, Module.finrank k U = d →
      ∃ Q : Finset ι, Q.card = d ∧ U ⊓ kerOn loc Q = ⊥ by
    obtain ⟨Q, hcard, hbot⟩ := hsub (Module.finrank k V) ⊤ (finrank_top k V)
    rw [top_inf_eq] at hbot
    exact ⟨Q, hcard, hbot⟩
  intro d
  induction d with
  | zero =>
    intro U hU
    refine ⟨∅, rfl, ?_⟩
    rw [kerOn_empty, inf_top_eq]
    exact Submodule.finrank_eq_zero.mp hU
  | succ m ih =>
    intro U hU
    have hne : U ≠ ⊥ := by
      intro hbot
      rw [hbot, finrank_bot] at hU
      omega
    obtain ⟨ψ, hψU, hψ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    obtain ⟨v, hv⟩ := hCheb ψ hψ0
    have hdrop := finrank_inf_ker_add_one loc U v (hW v) hψU hv
    obtain ⟨Q', hQ'card, hQ'bot⟩ := ih (U ⊓ LinearMap.ker (loc v)) (by omega)
    by_cases hvQ : v ∈ Q'
    · have hUle := finrank_le_finrank_inf_kerOn_add_card loc hW Q' U
      have hinf0 : U ⊓ kerOn loc Q' = ⊥ := by
        have hsub1 : U ⊓ kerOn loc Q' ≤ (U ⊓ LinearMap.ker (loc v)) ⊓ kerOn loc Q' := by
          intro x ⟨hxU, hxQ⟩
          exact ⟨⟨hxU, LinearMap.mem_ker.mpr ((mem_kerOn loc Q' x).mp hxQ v hvQ)⟩, hxQ⟩
        exact le_bot_iff.mp (hsub1.trans hQ'bot.le)
      rw [hinf0, finrank_bot, zero_add] at hUle
      omega
    · refine ⟨insert v Q', by rw [Finset.card_insert_of_notMem hvQ, hQ'card], ?_⟩
      rw [kerOn_insert, ← inf_assoc]
      exact hQ'bot

/-- Lower-bound optimality: when every local target `W v` has dimension `≤ 1`, any killing set
`Q` (`kerOn loc Q = ⊥`) must have `Q.card ≥ dim V`. -/
theorem finrank_le_card_of_kerOn_eq_bot [DecidableEq ι] (loc : ∀ v : ι, V →ₗ[k] W v)
    [∀ v, FiniteDimensional k (W v)]
    (hW : ∀ v : ι, Module.finrank k (W v) ≤ 1)
    (Q : Finset ι) (hbot : kerOn loc Q = ⊥) :
    Module.finrank k V ≤ Q.card := by
  have h := finrank_le_finrank_inf_kerOn_add_card loc hW Q ⊤
  rw [top_inf_eq, finrank_top, hbot, finrank_bot, zero_add] at h
  exact h

end FinDimKilling

end AbstractChebotarevKilling

/-! ### Taylor–Wiles Dual-Selmer Killing & Exact Presentation Balance on `PoitouTateData` -/

section PoitouTateTaylorWiles

variable {k : Type*} [Field k]
variable {Places : Type*} [Fintype Places] [DecidableEq Places]
variable (D : PoitouTateData k Places)

/-- Localization of dual cohomology at a single place `v : Places`. -/
def loc1DualAt (v : Places) : D.H1d →ₗ[k] D.H1dv v :=
  (LinearMap.proj v).comp D.loc1Dual

@[simp] theorem loc1DualAt_apply (v : Places) (ψ : D.H1d) :
    loc1DualAt D v ψ = D.loc1Dual ψ v := rfl

/-- **Taylor–Wiles Relaxed Local Conditions `L_Q`**:
at every auxiliary prime `v ∈ Q`, relax the local Selmer condition `L_v` to the full local
cohomology `⊤ = H¹(G_v, Ad(ρ̄))` (so its dual condition becomes `L_v^⊥ = ⊥ = 0`), while keeping
`L_v` unchanged for `v ∉ Q`. -/
def relaxCond (L : ∀ v : Places, Submodule k (D.H1v v)) (Q : Finset Places) :
    ∀ v : Places, Submodule k (D.H1v v) :=
  fun v => if v ∈ Q then ⊤ else L v

theorem relaxCond_of_mem (L : ∀ v : Places, Submodule k (D.H1v v)) (Q : Finset Places)
    {v : Places} (hv : v ∈ Q) :
    relaxCond D L Q v = ⊤ :=
  if_pos hv

theorem relaxCond_of_notMem (L : ∀ v : Places, Submodule k (D.H1v v)) (Q : Finset Places)
    {v : Places} (hv : v ∉ Q) :
    relaxCond D L Q v = L v :=
  if_neg hv

theorem le_relaxCond (L : ∀ v : Places, Submodule k (D.H1v v)) (Q : Finset Places) (v : Places) :
    L v ≤ relaxCond D L Q v := by
  by_cases hv : v ∈ Q
  · rw [relaxCond_of_mem D L Q hv]; exact le_top
  · rw [relaxCond_of_notMem D L Q hv]

/-- Relaxing local conditions on `Q` enlarges the Selmer group: `H¹_L ≤ H¹_{L_Q}`. -/
theorem selmer_le_relaxCond (L : ∀ v : Places, Submodule k (D.H1v v)) (Q : Finset Places) :
    D.Selmer L ≤ D.Selmer (relaxCond D L Q) := by
  intro x hx v _
  exact le_relaxCond D L Q v (hx v (Set.mem_univ v))

/-- **Exact Dual-Selmer Characterization under Taylor–Wiles Relaxation**:
a dual cohomology class `ψ ∈ H¹(G_S, Ad*(1))` lies in `H¹_{L_Q^⊥}` **if and only if**
`ψ ∈ H¹_{L^⊥}` AND `loc_v*(ψ) = 0` for every auxiliary prime `v ∈ Q`! -/
theorem mem_dualSelmer_relaxCond (L : ∀ v : Places, Submodule k (D.H1v v))
    (Q : Finset Places) (ψ : D.H1d) :
    ψ ∈ D.DualSelmer (relaxCond D L Q) ↔
      ψ ∈ D.DualSelmer L ∧ ∀ v ∈ Q, D.loc1Dual ψ v = 0 := by
  constructor
  · intro hψ
    refine ⟨fun v _ => ?_, fun v hvQ => ?_⟩
    · have hv := hψ v (Set.mem_univ v)
      exact (D.pair11 v).ortho_antitone (le_relaxCond D L Q v) hv
    · have hv : D.loc1Dual ψ v ∈ (D.pair11 v).ortho (relaxCond D L Q v) :=
        hψ v (Set.mem_univ v)
      rw [relaxCond_of_mem D L Q hvQ, LocalDualityPairing.ortho_top] at hv
      exact hv
  · rintro ⟨hψ, hvan⟩ v _
    change D.loc1Dual ψ v ∈ (D.pair11 v).ortho (relaxCond D L Q v)
    by_cases hvQ : v ∈ Q
    · rw [relaxCond_of_mem D L Q hvQ, LocalDualityPairing.ortho_top, Submodule.mem_bot]
      exact hvan v hvQ
    · rw [relaxCond_of_notMem D L Q hvQ]
      exact hψ v (Set.mem_univ v)

/-- Submodule form: `H¹_{L_Q^⊥} = H¹_{L^⊥} ⊓ ⋂_{v ∈ Q} ker(loc_v*)`. -/
theorem dualSelmer_relaxCond_eq_inf_ker (L : ∀ v : Places, Submodule k (D.H1v v))
    (Q : Finset Places) :
    D.DualSelmer (relaxCond D L Q) =
      D.DualSelmer L ⊓ kerOn (loc1DualAt D) Q := by
  ext ψ
  rw [mem_dualSelmer_relaxCond, Submodule.mem_inf, mem_kerOn]
  rfl

/-- Local dimension increment at a single place `v` when relaxing `L_v` to `⊤`:
`dim H¹_v - dim L_v = dim L_v^⊥`. -/
theorem finrank_top_sub_eq_finrank_ortho (L : ∀ v : Places, Submodule k (D.H1v v)) (v : Places) :
    (Module.finrank k (⊤ : Submodule k (D.H1v v)) : ℤ) - Module.finrank k (L v) =
      Module.finrank k ((D.pair11 v).ortho (L v)) := by
  rw [finrank_top]
  have h := (D.pair11 v).ortho_finrank_add (L v)
  omega

/-- **Exact Presentation Balance for ANY Dual-Killing Set `Q` of Taylor–Wiles Primes**:
if `Q` is disjoint from `S`, every `v ∉ S` is unramified (`dim L_v = dim H⁰_v`), every `v ∈ Q`
is a codimension-1 Taylor–Wiles prime (`dim L_v^⊥ = 1`), and `H¹_{L_Q^⊥} = 0`, then:
```
dim H¹_{L_Q}(Ad(ρ̄)) = Q.card + (dim H⁰(Ad) - dim H⁰(Ad*(1))) + ∑_{v ∈ S} (dim L_v - dim H⁰_v)
```
proved directly from `Stage2GaloisCohomology.PoitouTateData.greenberg_wiles_of_dual_vanishing`! -/
theorem taylor_wiles_exact_balance_of_dual_vanishing
    (hbal : D.EulerPoincareBalance)
    (L : ∀ v : Places, Submodule k (D.H1v v))
    (S Q : Finset Places) (hdisj : Disjoint Q S)
    (hunram : ∀ v : Places, v ∉ S → Module.finrank k (L v) = Module.finrank k (D.H0v v))
    (hTW : ∀ v ∈ Q, Module.finrank k ((D.pair11 v).ortho (L v)) = 1)
    (hvan : Module.finrank k (D.DualSelmer (relaxCond D L Q)) = 0) :
    (Module.finrank k (D.Selmer (relaxCond D L Q)) : ℤ) =
      (Q.card : ℤ) +
        ((Module.finrank k D.H0 : ℤ) - Module.finrank k D.H0d) +
        ∑ v ∈ S, ((Module.finrank k (L v) : ℤ) - Module.finrank k (D.H0v v)) := by
  have hgw := D.greenberg_wiles_of_dual_vanishing hbal (relaxCond D L Q) hvan
  have hsum :
      ∑ v : Places, ((Module.finrank k (relaxCond D L Q v) : ℤ) - Module.finrank k (D.H0v v)) =
        (Q.card : ℤ) +
          ∑ v ∈ S, ((Module.finrank k (L v) : ℤ) - Module.finrank k (D.H0v v)) := by
    let f : Places → ℤ := fun v =>
      (Module.finrank k (relaxCond D L Q v) : ℤ) - Module.finrank k (D.H0v v)
    have hsplit : ∑ v : Places, f v =
        (∑ v ∈ Q ∪ S, f v) + ∑ v ∈ (Finset.univ \ (Q ∪ S)), f v := by
      rw [← Finset.sum_union Finset.disjoint_sdiff]
      have hunion : (Q ∪ S) ∪ (Finset.univ \ (Q ∪ S)) = Finset.univ :=
        Finset.union_sdiff_of_subset (Finset.subset_univ _)
      rw [hunion]
    have hrest : ∑ v ∈ (Finset.univ \ (Q ∪ S)), f v = 0 := by
      refine Finset.sum_eq_zero fun v hv => ?_
      have hv' := (Finset.mem_sdiff.mp hv).2
      have hvQ : v ∉ Q := fun h => hv' (Finset.mem_union_left S h)
      have hvS : v ∉ S := fun h => hv' (Finset.mem_union_right Q h)
      dsimp only [f]
      rw [relaxCond_of_notMem D L Q hvQ, hunram v hvS, sub_self]
    have hQS : ∑ v ∈ Q ∪ S, f v = (∑ v ∈ Q, f v) + ∑ v ∈ S, f v :=
      Finset.sum_union hdisj
    have hQsum : ∑ v ∈ Q, f v = (Q.card : ℤ) := by
      have hterm : ∀ v ∈ Q, f v = 1 := fun v hvQ => by
        have hvS : v ∉ S := Finset.disjoint_left.mp hdisj hvQ
        dsimp only [f]
        rw [relaxCond_of_mem D L Q hvQ]
        have htop := finrank_top_sub_eq_finrank_ortho D L v
        rw [hTW v hvQ, hunram v hvS] at htop
        exact htop
      rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul, mul_one]
    have hSsum : ∑ v ∈ S, f v =
        ∑ v ∈ S, ((Module.finrank k (L v) : ℤ) - Module.finrank k (D.H0v v)) := by
      refine Finset.sum_congr rfl fun v hvS => ?_
      have hvQ : v ∉ Q := Finset.disjoint_right.mp hdisj hvS
      dsimp only [f]
      rw [relaxCond_of_notMem D L Q hvQ]
    change ∑ v : Places, f v = _
    rw [hsplit, hrest, add_zero, hQS, hQsum, hSsum]
  rw [hsum] at hgw
  linarith

/-- **THE TAYLOR–WILES AUXILIARY-PRIME DUAL-SELMER KILLING & EXACT PRESENTATION BALANCE THEOREM**:
Given `D : PoitouTateData k Places` satisfying Euler–Poincaré balance `hbal`, base ramification
places `S : Finset Places`, local conditions `L` unramified outside `S` (`dim L_v = dim H⁰_v`
for `v ∉ S`), and a candidate set `TW : Places → Prop` of Taylor–Wiles primes disjoint from `S`
with codimension `dim L_v^⊥ = 1`:

If for every nonzero dual Selmer class `ψ ∈ H¹_{L^⊥}` there exists a Taylor–Wiles prime `v` (`TW v`)
with `loc_v*(ψ) ≠ 0` (**Chebotarev / big-image hypothesis**), then by induction on
`q = dim H¹_{L^⊥}` there exists a finite set `Q : Finset Places` of Taylor–Wiles primes such that:
1. `∀ v ∈ Q, TW v` (and `Disjoint Q S`),
2. **`Q.card = Module.finrank k (D.DualSelmer L)`** (`q = dim H¹_{L^⊥}`),
3. **`Module.finrank k (D.DualSelmer (relaxCond D L Q)) = 0`** (`H¹_{L_Q^⊥}(Ad*(1)) = 0`),
4. **Exact Presentation Balance**:
   `dim H¹_{L_Q}(Ad(ρ̄)) = q + (dim H⁰(Ad) - dim H⁰(Ad*(1))) + ∑_{v ∈ S} (dim L_v - dim H⁰_v)`,
5. **Exact Selmer Preservation** (via `greenberg_wiles_killing_dual`):
   `D.Selmer (relaxCond D L Q) = D.Selmer L`! -/
theorem taylor_wiles_kill_dual_selmer
    (hbal : D.EulerPoincareBalance)
    (L : ∀ v : Places, Submodule k (D.H1v v))
    (S : Finset Places)
    (TW : Places → Prop)
    (hTW_disj : ∀ v, TW v → v ∉ S)
    (hunram : ∀ v : Places, v ∉ S → Module.finrank k (L v) = Module.finrank k (D.H0v v))
    (hTW_codim : ∀ v, TW v → Module.finrank k ((D.pair11 v).ortho (L v)) = 1)
    (hCheb : ∀ ψ : D.DualSelmer L, ψ ≠ 0 → ∃ v : Places, TW v ∧ D.loc1Dual ψ.1 v ≠ 0) :
    ∃ Q : Finset Places,
      (∀ v ∈ Q, TW v) ∧
      Disjoint Q S ∧
      Q.card = Module.finrank k (D.DualSelmer L) ∧
      Module.finrank k (D.DualSelmer (relaxCond D L Q)) = 0 ∧
      (Module.finrank k (D.Selmer (relaxCond D L Q)) : ℤ) =
        (Q.card : ℤ) +
          ((Module.finrank k D.H0 : ℤ) - Module.finrank k D.H0d) +
          ∑ v ∈ S, ((Module.finrank k (L v) : ℤ) - Module.finrank k (D.H0v v)) ∧
      D.Selmer (relaxCond D L Q) = D.Selmer L := by
  let TWType := { v : Places // TW v }
  let locTW : ∀ v : TWType, D.DualSelmer L →ₗ[k] (D.pair11 v.1).ortho (L v.1) :=
    fun v =>
      { toFun := fun ψ => ⟨D.loc1Dual ψ.1 v.1, ψ.2 v.1 (Set.mem_univ v.1)⟩
        map_add' := fun _ _ => Subtype.ext (by simp)
        map_smul' := fun _ _ => Subtype.ext (by simp) }
  have hW : ∀ v : TWType, Module.finrank k ((D.pair11 v.1).ortho (L v.1)) ≤ 1 :=
    fun v => (hTW_codim v.1 v.2).le
  have hCheb' : ∀ ψ : D.DualSelmer L, ψ ≠ 0 → ∃ v : TWType, locTW v ψ ≠ 0 := by
    intro ψ hψ
    obtain ⟨v, hvTW, hvnz⟩ := hCheb ψ hψ
    exact ⟨⟨v, hvTW⟩, fun h0 => hvnz (congrArg Subtype.val h0)⟩
  obtain ⟨Qsub, hQsub_card, hQsub_bot⟩ :=
    exists_exact_killing_set_of_dim_one locTW hW hCheb'
  let Q : Finset Places := Qsub.map ⟨Subtype.val, Subtype.val_injective⟩
  have hQ_TW : ∀ v ∈ Q, TW v := by
    intro v hv
    obtain ⟨⟨w, hw⟩, _, rfl⟩ := Finset.mem_map.mp hv
    exact hw
  have hQ_disj : Disjoint Q S :=
    Finset.disjoint_left.mpr fun v hvQ => hTW_disj v (hQ_TW v hvQ)
  have hQ_card : Q.card = Module.finrank k (D.DualSelmer L) := by
    rw [Finset.card_map, hQsub_card]
  have hDual_bot : D.DualSelmer (relaxCond D L Q) = ⊥ := by
    rw [eq_bot_iff]
    intro ψ hψ
    rw [mem_dualSelmer_relaxCond] at hψ
    have hmem : (⟨ψ, hψ.1⟩ : D.DualSelmer L) ∈ kerOn locTW Qsub := by
      rw [mem_kerOn]
      intro v hv
      apply Subtype.ext
      exact hψ.2 v.1 (Finset.mem_map.mpr ⟨v, hv, rfl⟩)
    rw [hQsub_bot, Submodule.mem_bot] at hmem
    exact congrArg Subtype.val hmem
  have hDual_van : Module.finrank k (D.DualSelmer (relaxCond D L Q)) = 0 := by
    rw [hDual_bot, finrank_bot]
  have hpres := taylor_wiles_exact_balance_of_dual_vanishing D hbal L S Q hQ_disj hunram
    (fun v hv => hTW_codim v (hQ_TW v hv)) hDual_van
  have hsel_eq : D.Selmer (relaxCond D L Q) = D.Selmer L := by
    have hkill := D.greenberg_wiles_killing_dual L (relaxCond D L Q) hDual_van
    have hdiff : ∑ v : Places,
        ((Module.finrank k (relaxCond D L Q v) : ℤ) - Module.finrank k (L v)) =
          (Q.card : ℤ) := by
      have hterm : ∀ v : Places,
          ((Module.finrank k (relaxCond D L Q v) : ℤ) - Module.finrank k (L v)) =
            if v ∈ Q then 1 else 0 := by
        intro v
        by_cases hvQ : v ∈ Q
        · rw [relaxCond_of_mem D L Q hvQ, if_pos hvQ,
            finrank_top_sub_eq_finrank_ortho, hTW_codim v (hQ_TW v hvQ)]
          rfl
        · rw [relaxCond_of_notMem D L Q hvQ, if_neg hvQ, sub_self]
      simp_rw [hterm]
      rw [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter]
    rw [hdiff, hQ_card] at hkill
    have hdim : Module.finrank k (D.Selmer L) =
        Module.finrank k (D.Selmer (relaxCond D L Q)) := by omega
    exact (Submodule.eq_of_le_of_finrank_eq (selmer_le_relaxCond D L Q) hdim).symm
  exact ⟨Q, hQ_TW, hQ_disj, hQ_card, hDual_van, hpres, hsel_eq⟩

/-- **Balanced Taylor–Wiles Numerical Coincidence (`g = q`)**:
in the balanced setting (`H⁰(Ad⁰) = 0`, `H⁰(Ad⁰*(1)) = 0`, and
`∑_{v ∈ S} (dim L_v - dim H⁰_v) = 0`), adding `q = dim H¹_{L^⊥}` Taylor–Wiles primes yields
**`dim H¹_{L_Q}(Ad⁰(ρ̄)) = q = Q.card`**! -/
theorem taylor_wiles_balanced_g_eq_q
    (hbal : D.EulerPoincareBalance)
    (L : ∀ v : Places, Submodule k (D.H1v v))
    (S : Finset Places)
    (TW : Places → Prop)
    (hTW_disj : ∀ v, TW v → v ∉ S)
    (hunram : ∀ v : Places, v ∉ S → Module.finrank k (L v) = Module.finrank k (D.H0v v))
    (hTW_codim : ∀ v, TW v → Module.finrank k ((D.pair11 v).ortho (L v)) = 1)
    (hCheb : ∀ ψ : D.DualSelmer L, ψ ≠ 0 → ∃ v : Places, TW v ∧ D.loc1Dual ψ.1 v ≠ 0)
    (h0 : Module.finrank k D.H0 = 0)
    (h0d : Module.finrank k D.H0d = 0)
    (hlocS : ∑ v ∈ S, ((Module.finrank k (L v) : ℤ) - Module.finrank k (D.H0v v)) = 0) :
    ∃ Q : Finset Places,
      (∀ v ∈ Q, TW v) ∧
      Disjoint Q S ∧
      Q.card = Module.finrank k (D.DualSelmer L) ∧
      Module.finrank k (D.DualSelmer (relaxCond D L Q)) = 0 ∧
      Module.finrank k (D.Selmer (relaxCond D L Q)) = Q.card := by
  obtain ⟨Q, hTW, hdisj, hcard, hvan, hpres, _⟩ :=
    taylor_wiles_kill_dual_selmer D hbal L S TW hTW_disj hunram hTW_codim hCheb
  rw [h0, h0d, hlocS] at hpres
  refine ⟨Q, hTW, hdisj, hcard, hvan, ?_⟩
  omega

end PoitouTateTaylorWiles

end TaylorWilesDualKilling

/-! ## Section 4: Relative Cotangent Space `m_{R_Q} / (ϖ, m_{R_Q}²)`, Zariski Tangent Duality & Minimal Generators `μ` -/

section TangentCotangentMinimalGenerators

/-! ### Relative Cotangent Space `m_{R_Q} ⧸ (ϖ R_Q + m_{R_Q}²)` & Third-Isomorphism Reduction -/

section RelativeCotangent

variable {R : Type*} [CommRing R]

/-- The ideal `ϖ R + m²` inside a ring `R` with maximal ideal `m` and uniformizer `ϖ`. -/
def relCotangentIdeal (m : Ideal R) (ϖ : R) : Ideal R :=
  Ideal.span ({ϖ} : Set R) ⊔ m ^ 2

theorem relCotangentIdeal_le (m : Ideal R) (ϖ : R) (hϖ : ϖ ∈ m) :
    relCotangentIdeal m ϖ ≤ m :=
  sup_le ((Ideal.span_singleton_le_iff_mem m).mpr hϖ) (Ideal.pow_le_self (by norm_num))

/-- The **relative cotangent space** `m ⧸ (ϖ R + m²)` as an `R`-module. -/
abbrev RelCotangent (m : Ideal R) (ϖ : R) : Type _ :=
  m ⧸ Submodule.comap m.subtype (relCotangentIdeal m ϖ)

/-- The **cotangent space** `m ⧸ m²` of a ring `A` at an ideal `m : Ideal A`. -/
abbrev CotangentMod {A : Type*} [CommRing A] (m : Ideal A) : Type _ :=
  m ⧸ Submodule.comap m.subtype (m ^ 2)

/-- **Relative Cotangent Reduction Theorem (Third Isomorphism Theorem)**:
for any ideal `m : Ideal R` and uniformizer `ϖ : R`, letting `Rbar := R ⧸ (ϖ)` and
`mbar := m.map (Ideal.Quotient.mk (ϖ))`, there is a canonical `R`-linear isomorphism:
`m ⧸ (ϖ R + m²) ≃ₗ[R] mbar ⧸ mbar²`! -/
def relCotangentEquivCotangentQuot (m : Ideal R) (ϖ : R) :
    RelCotangent m ϖ ≃ₗ[R]
      CotangentMod (m.map (Ideal.Quotient.mk (Ideal.span ({ϖ} : Set R)))) := by
  let Iϖ : Ideal R := Ideal.span ({ϖ} : Set R)
  let q : R →+* R ⧸ Iϖ := Ideal.Quotient.mk Iϖ
  let mbar : Ideal (R ⧸ Iϖ) := m.map q
  let mkM : m → mbar := fun x => ⟨q x.1, Ideal.mem_map_of_mem q x.2⟩
  let φ : m →ₗ[R] CotangentMod mbar :=
    { toFun := fun x => Submodule.Quotient.mk (mkM x)
      map_add' := fun x y => by
        change Submodule.Quotient.mk (mkM (x + y)) =
          Submodule.Quotient.mk (mkM x) + Submodule.Quotient.mk (mkM y)
        rw [← Submodule.Quotient.mk_add]
        exact congrArg Submodule.Quotient.mk (Subtype.ext (map_add q x.1 y.1))
      map_smul' := fun r x => by
        change Submodule.Quotient.mk (mkM (r • x)) =
          r • Submodule.Quotient.mk (mkM x)
        rw [← Submodule.Quotient.mk_smul]
        exact congrArg Submodule.Quotient.mk (Subtype.ext (map_mul q r x.1)) }
  have hker : LinearMap.ker φ = Submodule.comap m.subtype (relCotangentIdeal m ϖ) := by
    ext ⟨x, hx⟩
    simp only [LinearMap.mem_ker, Submodule.mem_comap, Submodule.coe_subtype, relCotangentIdeal]
    change Submodule.Quotient.mk (mkM ⟨x, hx⟩) = (0 : CotangentMod mbar) ↔ x ∈ Iϖ ⊔ m ^ 2
    rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.coe_subtype]
    have hpow : mbar ^ 2 = (m ^ 2).map q := (Ideal.map_pow q m 2).symm
    rw [hpow, Ideal.mem_map_iff_of_surjective q Ideal.Quotient.mk_surjective]
    constructor
    · rintro ⟨y, hy, hyx⟩
      have hsub : x - y ∈ Iϖ := by
        rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub]
        exact sub_eq_zero.mpr hyx.symm
      have heq : x = (x - y) + y := by ring
      rw [heq]
      exact Submodule.add_mem_sup hsub hy
    · intro hxsup
      obtain ⟨a, ha, y, hy, rfl⟩ := Submodule.mem_sup.mp hxsup
      refine ⟨y, hy, ?_⟩
      change q y = q (a + y)
      rw [map_add, Ideal.Quotient.eq_zero_iff_mem.mpr ha, zero_add]
  have hsurj : Function.Surjective φ := by
    intro z
    induction z using Quotient.inductionOn' with
    | h y =>
      obtain ⟨x, hx, hqx⟩ :=
        (Ideal.mem_map_iff_of_surjective q Ideal.Quotient.mk_surjective).mp y.2
      refine ⟨⟨x, hx⟩, ?_⟩
      change Submodule.Quotient.mk (mkM ⟨x, hx⟩) = Submodule.Quotient.mk y
      congr 1
      exact Subtype.ext hqx
  exact (Submodule.quotEquivOfEq _ _ hker.symm).trans
    (LinearMap.quotKerEquivOfSurjective φ hsurj)

end RelativeCotangent

/-! ### Zariski Tangent–Cotangent Duality over a Field `k` -/

section ZariskiTangentDuality

variable {k A : Type*} [Field k] [CommRing A] [Algebra k A]

/-- Square-ideal submodule `m_A²` inside `m_A = ker π` as a `k`-subspace. -/
def cotangentSqSub (k A : Type*) [Field k] [CommRing A] [Algebra k A] (π : A →ₐ[k] k) :
    Submodule k (RingHom.ker π.toRingHom) :=
  Submodule.restrictScalars k
    (Submodule.comap (RingHom.ker π.toRingHom).subtype ((RingHom.ker π.toRingHom) ^ 2))

/-- Cotangent space `m_A ⧸ m_A²` as a `k`-vector space for an augmented `k`-algebra
`π : A →ₐ[k] k` with augmentation ideal `m_A = ker π`. -/
abbrev CotangentSpace (k A : Type*) [Field k] [CommRing A] [Algebra k A] (π : A →ₐ[k] k) :
    Type _ :=
  (RingHom.ker π.toRingHom) ⧸ cotangentSqSub k A π

/-- **Zariski Tangent Homomorphisms** `TangentHom k A π`: `k`-algebra homomorphisms
`φ : A →ₐ[k] k[ε]/(ε²)` reducing mod `ε` to `π : A →ₐ[k] k`. -/
structure TangentHom (k A : Type*) [Field k] [CommRing A] [Algebra k A] (π : A →ₐ[k] k) where
  toAlgHom : A →ₐ[k] DualNumber k
  fst_eq : ∀ a : A, (toAlgHom a).fst = π a

namespace TangentHom

variable {π : A →ₐ[k] k}

@[ext]
theorem ext {φ₁ φ₂ : TangentHom k A π} (h : ∀ a, φ₁.toAlgHom a = φ₂.toAlgHom a) : φ₁ = φ₂ := by
  cases φ₁; cases φ₂
  congr
  exact AlgHom.ext h

/-- A `k`-algebra lift `φ : A →ₐ[k] DualNumber k` of `π` vanishes in its `ε`-coordinate on
`m_A² = (ker π)²`. -/
theorem snd_eq_zero_of_mem_ker_sq (φ : TangentHom k A π) {x : A}
    (hx : x ∈ (RingHom.ker π.toRingHom) ^ 2) :
    (φ.toAlgHom x).snd = 0 := by
  rw [sq] at hx
  refine Submodule.mul_induction_on hx ?_ ?_
  · intro a ha b hb
    rw [map_mul, TrivSqZeroExt.snd_mul, φ.fst_eq a, φ.fst_eq b]
    have ha0 : π a = 0 := ha
    have hb0 : π b = 0 := hb
    simp [ha0, hb0]
  · intro a b ha hb
    rw [map_add, TrivSqZeroExt.snd_add, ha, hb, add_zero]

/-- Forward map `TangentHom k A π → Dual k (CotangentSpace k A π)`. -/
def toDualCotangent (φ : TangentHom k A π) : Module.Dual k (CotangentSpace k A π) :=
  Submodule.liftQ (cotangentSqSub k A π)
    { toFun := fun x => (φ.toAlgHom x.1).snd
      map_add' := fun x y => by
        change (φ.toAlgHom (x.1 + y.1)).snd = (φ.toAlgHom x.1).snd + (φ.toAlgHom y.1).snd
        rw [map_add, TrivSqZeroExt.snd_add]
      map_smul' := fun c x => by
        change (φ.toAlgHom (c • x.1)).snd = c * (φ.toAlgHom x.1).snd
        rw [map_smul]
        simp [smul_eq_mul] }
    (fun x hx => LinearMap.mem_ker.mpr (φ.snd_eq_zero_of_mem_ker_sq hx))

/-- Backward map `Dual k (CotangentSpace k A π) → TangentHom k A π`. -/
def ofDualCotangent (ℓ : Module.Dual k (CotangentSpace k A π)) : TangentHom k A π where
  toAlgHom :=
    let m := RingHom.ker π.toRingHom
    let m2 : Submodule k m := cotangentSqSub k A π
    let proj : A → m := fun a =>
      ⟨a - algebraMap k A (π a), by
        change π (a - algebraMap k A (π a)) = 0
        rw [map_sub, AlgHom.commutes]
        simp⟩
    let δ : A → k := fun a => ℓ (m2.mkQ (proj a))
    { toFun := fun a => dualMk (π a) (δ a)
      map_one' := by
        have hproj : proj 1 = 0 := Subtype.ext (by
          change (1 : A) - algebraMap k A (π 1) = 0
          rw [map_one, map_one, sub_self])
        have hδ : δ 1 = 0 := by dsimp only [δ]; rw [hproj, map_zero, map_zero]
        rw [map_one, hδ]
        exact dualMk_one
      map_zero' := by
        have hproj : proj 0 = 0 := Subtype.ext (by
          change (0 : A) - algebraMap k A (π 0) = 0
          rw [map_zero, map_zero, sub_self])
        have hδ : δ 0 = 0 := by dsimp only [δ]; rw [hproj, map_zero, map_zero]
        rw [map_zero, hδ]
        exact dualMk_zero
      map_add' := fun a b => by
        have hproj : proj (a + b) = proj a + proj b := Subtype.ext (by
          change (a + b) - algebraMap k A (π (a + b)) =
            (a - algebraMap k A (π a)) + (b - algebraMap k A (π b))
          rw [map_add, map_add]
          abel)
        have hδ : δ (a + b) = δ a + δ b := by
          dsimp only [δ]; rw [hproj, map_add, map_add]
        rw [map_add, hδ]
        exact (dualMk_add (π a) (δ a) (π b) (δ b)).symm
      map_mul' := fun a b => by
        have hprod_mem : (proj a).1 * (proj b).1 ∈ m ^ 2 := by
          rw [sq]
          exact Ideal.mul_mem_mul (proj a).2 (proj b).2
        have hdecomp : proj (a * b) - (π a • proj b + π b • proj a) ∈ m2 := by
          change (proj (a * b) - (π a • proj b + π b • proj a)).1 ∈ m ^ 2
          have heq : (proj (a * b) - (π a • proj b + π b • proj a)).1 =
              (proj a).1 * (proj b).1 := by
            change (a * b - algebraMap k A (π (a * b))) -
                (π a • (b - algebraMap k A (π b)) + π b • (a - algebraMap k A (π a))) =
              (a - algebraMap k A (π a)) * (b - algebraMap k A (π b))
            simp only [map_mul, Algebra.smul_def]
            ring
          rw [heq]
          exact hprod_mem
        have hq : m2.mkQ (proj (a * b)) =
            π a • m2.mkQ (proj b) + π b • m2.mkQ (proj a) := by
          rw [← map_smul, ← map_smul, ← map_add, ← sub_eq_zero, ← map_sub,
            Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
          exact hdecomp
        have hδ : δ (a * b) = π a * δ b + δ a * π b := by
          dsimp only [δ]
          rw [hq, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
          ring
        rw [map_mul, hδ, dualMk_mul]
      commutes' := fun c => by
        have hproj : proj (algebraMap k A c) = 0 := Subtype.ext (by
          change algebraMap k A c - algebraMap k A (π (algebraMap k A c)) = 0
          rw [AlgHom.commutes]
          simp)
        have hδ : δ (algebraMap k A c) = 0 := by
          dsimp only [δ]; rw [hproj, map_zero, map_zero]
        rw [hδ, TrivSqZeroExt.algebraMap_eq_inl]
        apply TrivSqZeroExt.ext
        · simp [AlgHom.commutes]
        · simp }
  fst_eq a := by simp

end TangentHom

/-- **ZARISKI TANGENT–COTANGENT DUALITY**:
for any augmented `k`-algebra `(A, π : A →ₐ[k] k)`, the Zariski tangent space `TangentHom k A π`
is canonically bijective to the dual of the cotangent space `Module.Dual k (m_A ⧸ m_A²)`! -/
def zariskiTangentEquivDualCotangent (π : A →ₐ[k] k) :
    TangentHom k A π ≃ Module.Dual k (CotangentSpace k A π) where
  toFun := TangentHom.toDualCotangent
  invFun := TangentHom.ofDualCotangent
  left_inv φ := TangentHom.ext fun a => by
    apply TrivSqZeroExt.ext
    · simp [TangentHom.ofDualCotangent, φ.fst_eq a]
    · simp only [TangentHom.ofDualCotangent, TangentHom.toDualCotangent, AlgHom.coe_mk,
        RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, dualMk_snd, Submodule.mkQ_apply,
        Submodule.liftQ_apply, LinearMap.coe_mk, AddHom.coe_mk]
      rw [map_sub, AlgHom.commutes, TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.snd_sub]
      simp
  right_inv ℓ := by
    ext x
    simp only [LinearMap.comp_apply, Submodule.mkQ_apply, TangentHom.toDualCotangent,
      TangentHom.ofDualCotangent, Submodule.liftQ_apply, LinearMap.coe_mk, AddHom.coe_mk,
      AlgHom.coe_mk, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, dualMk_snd]
    have hx0 : π x.1 = 0 := x.2
    congr 1
    apply congrArg Submodule.Quotient.mk
    apply Subtype.ext
    simp [hx0]

/-- Natural `k`-vector space structure on `TangentHom k A π` transferred from
`Module.Dual k (CotangentSpace k A π)`. -/
instance tangentHomAddCommGroup (π : A →ₐ[k] k) : AddCommGroup (TangentHom k A π) :=
  (zariskiTangentEquivDualCotangent π).addCommGroup

instance tangentHomModule (π : A →ₐ[k] k) : Module k (TangentHom k A π) :=
  (zariskiTangentEquivDualCotangent π).module k

/-- `k`-linear Zariski tangent–cotangent duality:
`TangentHom k A π ≃ₗ[k] Module.Dual k (CotangentSpace k A π)`. -/
def zariskiTangentLinearEquiv (π : A →ₐ[k] k) :
    TangentHom k A π ≃ₗ[k] Module.Dual k (CotangentSpace k A π) :=
  (zariskiTangentEquivDualCotangent π).linearEquiv k

/-- **Cotangent Dimension = Zariski Tangent Dimension**:
for finite-dimensional cotangent space, `dim_k(m_A ⧸ m_A²) = dim_k(TangentHom k A π)`. -/
theorem finrank_cotangentSpace_eq_finrank_tangentHom (π : A →ₐ[k] k)
    [FiniteDimensional k (CotangentSpace k A π)] :
    Module.finrank k (CotangentSpace k A π) = Module.finrank k (TangentHom k A π) := by
  rw [(zariskiTangentLinearEquiv π).finrank_eq, Subspace.dual_finrank_eq]

end ZariskiTangentDuality

/-! ### Minimal Generator Count `μ(M)` & Nakayama Generator Lifting -/

section MinimalGenerators

/-- The **minimal number of generators** `μ_R(M)` of an `R`-module `M`:
the least `r : ℕ` admitting an `R`-linear surjection `(Fin r → R) ↠ M`. -/
def minGenCount (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M] : ℕ :=
  sInf { r : ℕ | ∃ f : (Fin r → R) →ₗ[R] M, Function.Surjective f }

/-- Over a field `k`, the minimal generator count `μ_k(V)` equals `Module.finrank k V`! -/
theorem minGenCount_eq_finrank {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] :
    minGenCount k V = Module.finrank k V := by
  let S : Set ℕ := { r : ℕ | ∃ f : (Fin r → k) →ₗ[k] V, Function.Surjective f }
  have hmem : Module.finrank k V ∈ S := by
    let b := Module.finBasis k V
    exact ⟨b.equivFun.symm.toLinearMap, b.equivFun.symm.surjective⟩
  have hlb : ∀ r ∈ S, Module.finrank k V ≤ r := by
    rintro r ⟨f, hf⟩
    have hle := LinearMap.finrank_le_finrank_of_surjective hf
    simpa [Module.finrank_fin_fun] using hle
  exact le_antisymm (Nat.sInf_le hmem) (le_csInf ⟨_, hmem⟩ hlb)

/-- **Nakayama Minimal-Generator Lifting Theorem**:
over a local ring `(R, m)`, if `M` is a finitely generated `R`-module and `M ⧸ m M` is generated
by `r` elements, then `M` itself is generated by `r` elements over `R` (`μ_R(M) ≤ r`)! -/
theorem nakayama_exists_surjective_of_quotient {R M : Type*} [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] {r : ℕ}
    (g : (Fin r → R) →ₗ[R] M ⧸ (IsLocalRing.maximalIdeal R • (⊤ : Submodule R M)))
    (hg : Function.Surjective g) :
    ∃ f : (Fin r → R) →ₗ[R] M, Function.Surjective f := by
  let m := IsLocalRing.maximalIdeal R
  let q := (m • (⊤ : Submodule R M)).mkQ
  have hlift : ∀ i : Fin r, ∃ v : M, q v = g (Pi.single i 1) :=
    fun i => Submodule.mkQ_surjective _ (g (Pi.single i 1))
  choose v hv using hlift
  let f : (Fin r → R) →ₗ[R] M := Fintype.linearCombination R v
  refine ⟨f, ?_⟩
  rw [← LinearMap.range_eq_top]
  have hsup : (⊤ : Submodule R M) ≤ LinearMap.range f ⊔ m • (⊤ : Submodule R M) := by
    intro x _
    obtain ⟨c, hc⟩ := hg (q x)
    have hfc : q (f c) = q x := by
      have hc_eq : c = ∑ i : Fin r, c i • Pi.single i (1 : R) := by
        ext j
        simp [Finset.sum_apply, Pi.single_apply]
      calc q (f c)
          = q (∑ i : Fin r, c i • v i) := rfl
        _ = ∑ i : Fin r, c i • q (v i) := by simp [map_sum, map_smul]
        _ = ∑ i : Fin r, c i • g (Pi.single i 1) := by simp [hv]
        _ = g (∑ i : Fin r, c i • Pi.single i (1 : R)) := by simp [map_sum, map_smul]
        _ = g c := by rw [← hc_eq]
        _ = q x := hc
    have hdiff : x - f c ∈ m • (⊤ : Submodule R M) := by
      rw [← Submodule.Quotient.mk_eq_zero]
      change q (x - f c) = 0
      rw [map_sub, hfc, sub_self]
    have hx_eq : x = f c + (x - f c) := by abel
    rw [hx_eq]
    exact Submodule.add_mem_sup ⟨c, rfl⟩ hdiff
  have hjac : m ≤ Ideal.jacobson ⊥ := IsLocalRing.maximalIdeal_le_jacobson ⊥
  exact top_le_iff.mp
    (Submodule.le_of_le_smul_of_le_jacobson_bot
      (Module.Finite.fg_top (R := R) (M := M)) hjac hsup)

/-- Corollary: `minGenCount R M ≤ r` whenever `M ⧸ m M` is generated by `r` elements. -/
theorem nakayama_minGenCount_le {R M : Type*} [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] {r : ℕ}
    (g : (Fin r → R) →ₗ[R] M ⧸ (IsLocalRing.maximalIdeal R • (⊤ : Submodule R M)))
    (hg : Function.Surjective g) :
    minGenCount R M ≤ r :=
  Nat.sInf_le (nakayama_exists_surjective_of_quotient g hg)

end MinimalGenerators

/-! ### Universal Deformation Ring `R_Q` Presentation Bound -/

section UniversalDeformationRing

/-- **Universal `L_Q`-Deformation Ring Package**:
models a complete local `𝒪`-algebra `R_Q` with maximal ideal `m_Q`, uniformizer `ϖ ∈ m_Q`,
mod-`ϖ` fiber `R̄_Q = R_Q ⧸ (ϖ)` (a `k`-algebra with residue map `π : R̄_Q →ₐ[k] k`), and the
Mazur representability isomorphism identifying Zariski tangent vectors `TangentHom k R̄_Q π`
with the Selmer tangent space `D.Selmer L_Q`! -/
structure UniversalDeformRingData.{u, v, w} {k : Type u} [Field k] {Places : Type v}
    [Fintype Places] [DecidableEq Places]
    (D : PoitouTateData k Places) (L_Q : ∀ v : Places, Submodule k (D.H1v v)) where
  R_Q : Type w
  [commRing_RQ : CommRing R_Q]
  m_Q : Ideal R_Q
  ϖ : R_Q
  ϖ_mem : ϖ ∈ m_Q
  Rbar : Type w
  [commRing_Rbar : CommRing Rbar]
  [alg_Rbar : Algebra k Rbar]
  π : Rbar →ₐ[k] k
  [fd_cotangent : FiniteDimensional k (CotangentSpace k Rbar π)]
  /-- Exact additive identification of `m_{R_Q} ⧸ (ϖ R_Q + m_{R_Q}²)` with the mod-`ϖ`
  cotangent space `m̄ ⧸ m̄²` (realized concretely via `relCotangentEquivCotangentQuot` when
  `Rbar = R_Q ⧸ (ϖ)`). -/
  relCotangentEquiv : RelCotangent m_Q ϖ ≃+ CotangentSpace k Rbar π
  /-- Universal deformation representability on dual numbers:
  `Hom_{k-alg, π}(R_Q / ϖ, k[ε]/(ε²)) ≃ₗ[k] H¹_{L_Q}(Ad(ρ̄))` (combining representability of the
  `L_Q`-deformation functor with `mazurTangentLinearEquiv`). -/
  tangentEquivSelmer : TangentHom k Rbar π ≃ₗ[k] D.Selmer L_Q

attribute [instance] UniversalDeformRingData.commRing_RQ UniversalDeformRingData.commRing_Rbar
  UniversalDeformRingData.alg_Rbar UniversalDeformRingData.fd_cotangent

/-- **Exact Tangent-Space Generator Count for `R_Q`**:
`μ_k(m_{R_Q} / (ϖ, m_{R_Q}²)) = dim_k(m_{R_Q} / (ϖ, m_{R_Q}²)) = dim_k H¹_{L_Q}(Ad(ρ̄))`! -/
theorem universalDeformRing_minGen_eq_selmer_dim {k : Type*} [Field k]
    {Places : Type*} [Fintype Places] [DecidableEq Places]
    {D : PoitouTateData k Places} {L_Q : ∀ v : Places, Submodule k (D.H1v v)}
    (U : UniversalDeformRingData D L_Q) :
    minGenCount k (CotangentSpace k U.Rbar U.π) = Module.finrank k (D.Selmer L_Q) ∧
      Module.finrank k (CotangentSpace k U.Rbar U.π) = Module.finrank k (D.Selmer L_Q) := by
  have hdim : Module.finrank k (CotangentSpace k U.Rbar U.π) = Module.finrank k (D.Selmer L_Q) := by
    rw [finrank_cotangentSpace_eq_finrank_tangentHom U.π, U.tangentEquivSelmer.finrank_eq]
  exact ⟨(minGenCount_eq_finrank (k := k)).trans hdim, hdim⟩

/-- **Exact Presentation Balance for the Minimal Generator Count of `R_Q`**:
combining `universalDeformRing_minGen_eq_selmer_dim` with
`taylor_wiles_exact_balance_of_dual_vanishing`, whenever `Q` kills `H¹_{L_Q^⊥}`:
```
μ(m_{R_Q} / (ϖ, m_{R_Q}²)) = Q.card + (dim H⁰(Ad) - dim H⁰(Ad*(1))) + ∑_{v ∈ S} (dim L_v - dim H⁰_v)
``` -/
theorem universalDeformRing_presentation_balance {k : Type*} [Field k]
    {Places : Type*} [Fintype Places] [DecidableEq Places]
    {D : PoitouTateData k Places} (hbal : D.EulerPoincareBalance)
    (L : ∀ v : Places, Submodule k (D.H1v v))
    (S Q : Finset Places) (hdisj : Disjoint Q S)
    (hunram : ∀ v : Places, v ∉ S → Module.finrank k (L v) = Module.finrank k (D.H0v v))
    (hTW : ∀ v ∈ Q, Module.finrank k ((D.pair11 v).ortho (L v)) = 1)
    (hvan : Module.finrank k (D.DualSelmer (relaxCond D L Q)) = 0)
    (U : UniversalDeformRingData D (relaxCond D L Q)) :
    (minGenCount k (CotangentSpace k U.Rbar U.π) : ℤ) =
      (Q.card : ℤ) +
        ((Module.finrank k D.H0 : ℤ) - Module.finrank k D.H0d) +
        ∑ v ∈ S, ((Module.finrank k (L v) : ℤ) - Module.finrank k (D.H0v v)) := by
  rw [(universalDeformRing_minGen_eq_selmer_dim U).1]
  exact taylor_wiles_exact_balance_of_dual_vanishing D hbal L S Q hdisj hunram hTW hvan

/-- **Balanced Taylor–Wiles Generator Bound (`μ(R_Q) = q`)**:
in the balanced case (`H⁰ = H⁰* = 0`, `∑_{v ∈ S} (dim L_v - dim H⁰_v) = 0`), the minimal
number of generators of `m_{R_Q} / (ϖ, m_{R_Q}²)` equals `Q.card = q`! -/
theorem universalDeformRing_balanced_minGen_eq_q {k : Type*} [Field k]
    {Places : Type*} [Fintype Places] [DecidableEq Places]
    {D : PoitouTateData k Places} (hbal : D.EulerPoincareBalance)
    (L : ∀ v : Places, Submodule k (D.H1v v))
    (S Q : Finset Places) (hdisj : Disjoint Q S)
    (hunram : ∀ v : Places, v ∉ S → Module.finrank k (L v) = Module.finrank k (D.H0v v))
    (hTW : ∀ v ∈ Q, Module.finrank k ((D.pair11 v).ortho (L v)) = 1)
    (hvan : Module.finrank k (D.DualSelmer (relaxCond D L Q)) = 0)
    (h0 : Module.finrank k D.H0 = 0) (h0d : Module.finrank k D.H0d = 0)
    (hlocS : ∑ v ∈ S, ((Module.finrank k (L v) : ℤ) - Module.finrank k (D.H0v v)) = 0)
    (U : UniversalDeformRingData D (relaxCond D L Q)) :
    minGenCount k (CotangentSpace k U.Rbar U.π) = Q.card := by
  have h := universalDeformRing_presentation_balance hbal L S Q hdisj hunram hTW hvan U
  rw [h0, h0d, hlocS] at h
  omega

/-- Inside an ideal `m : Ideal R`, the `R`-submodule `m • ⊤` of `m` equals `m²` pulled back into `m`. -/
theorem ideal_smul_top_eq_comap_sq {R : Type*} [CommRing R] (m : Ideal R) :
    m • (⊤ : Submodule R m) = Submodule.comap m.subtype (m ^ 2) := by
  refine le_antisymm ?_ ?_
  · rw [Submodule.smul_le]
    intro a ha x _
    change a * x.1 ∈ m ^ 2
    rw [sq]
    exact Ideal.mul_mem_mul ha x.2
  · intro x hx
    change x.1 ∈ m ^ 2 at hx
    rw [sq] at hx
    have haux : ∀ y : R, y ∈ m * m →
        ∃ hy : y ∈ m, (⟨y, hy⟩ : m) ∈ m • (⊤ : Submodule R m) := by
      intro y hy
      refine Submodule.mul_induction_on hy ?_ ?_
      · intro a ha b hb
        refine ⟨Ideal.mul_mem_right b m ha, ?_⟩
        have heq : (⟨a * b, Ideal.mul_mem_right b m ha⟩ : m) = a • (⟨b, hb⟩ : m) :=
          Subtype.ext rfl
        rw [heq]
        exact Submodule.smul_mem_smul ha Submodule.mem_top
      · rintro y₁ y₂ ⟨hy₁, h₁⟩ ⟨hy₂, h₂⟩
        refine ⟨m.add_mem hy₁ hy₂, ?_⟩
        have heq : (⟨y₁ + y₂, m.add_mem hy₁ hy₂⟩ : m) = ⟨y₁, hy₁⟩ + ⟨y₂, hy₂⟩ :=
          Subtype.ext rfl
        rw [heq]
        exact Submodule.add_mem _ h₁ h₂
    obtain ⟨_, hmem⟩ := haux x.1 hx
    exact hmem

/-- **Nakayama Maximal-Ideal Generator Bound for `R_Q / (ϖ)`**:
when `R̄_Q = R_Q / (ϖ)` is a local `k`-algebra with maximal ideal `m̄ = ker π` finitely generated
over `R̄_Q`, Nakayama's Lemma lifts a basis of the cotangent space `m̄ / m̄²` to a generating set of
`m̄`, proving `μ_{R̄_Q}(m̄) ≤ dim_k H¹_{L_Q}(Ad(ρ̄))`! -/
theorem universalDeformRing_maximalIdeal_minGen_le {k : Type*} [Field k]
    {Places : Type*} [Fintype Places] [DecidableEq Places]
    {D : PoitouTateData k Places} {L_Q : ∀ v : Places, Submodule k (D.H1v v)}
    (U : UniversalDeformRingData D L_Q)
    [IsLocalRing U.Rbar]
    (hm : IsLocalRing.maximalIdeal U.Rbar = RingHom.ker U.π.toRingHom)
    [Module.Finite U.Rbar (RingHom.ker U.π.toRingHom)] :
    minGenCount U.Rbar (RingHom.ker U.π.toRingHom) ≤ Module.finrank k (D.Selmer L_Q) := by
  let m : Ideal U.Rbar := RingHom.ker U.π.toRingHom
  have hdim : Module.finrank k (CotangentSpace k U.Rbar U.π) = Module.finrank k (D.Selmer L_Q) :=
    (universalDeformRing_minGen_eq_selmer_dim U).2
  let r := Module.finrank k (D.Selmer L_Q)
  let b : Module.Basis (Fin r) k (CotangentSpace k U.Rbar U.π) :=
    (Module.finBasis k (CotangentSpace k U.Rbar U.π)).reindex (finCongr hdim)
  have hlift : ∀ i : Fin r, ∃ v : m, Submodule.Quotient.mk v = b i :=
    fun i => Submodule.Quotient.mk_surjective _ (b i)
  choose v hv using hlift
  let g : (Fin r → U.Rbar) →ₗ[U.Rbar]
      m ⧸ (IsLocalRing.maximalIdeal U.Rbar • (⊤ : Submodule U.Rbar m)) :=
    Fintype.linearCombination U.Rbar (fun i => Submodule.Quotient.mk (v i))
  have hg : Function.Surjective g := by
    intro q
    induction q using Quotient.inductionOn' with
    | h x =>
      let c : Fin r → k := fun i => b.repr (Submodule.Quotient.mk x) i
      refine ⟨fun i => algebraMap k U.Rbar (c i), ?_⟩
      let qm := (IsLocalRing.maximalIdeal U.Rbar • (⊤ : Submodule U.Rbar m)).mkQ
      have hgv : g (fun i => algebraMap k U.Rbar (c i)) =
          qm (∑ i : Fin r, (algebraMap k U.Rbar (c i)) • v i) := by
        change ∑ i : Fin r, (algebraMap k U.Rbar (c i)) • qm (v i) = _
        rw [map_sum]
        refine Finset.sum_congr rfl fun i _ => (map_smul qm _ _).symm
      rw [hgv]
      change Submodule.Quotient.mk (p := IsLocalRing.maximalIdeal U.Rbar • (⊤ : Submodule U.Rbar m))
          (∑ i : Fin r, (algebraMap k U.Rbar (c i)) • v i) =
        Submodule.Quotient.mk (p := IsLocalRing.maximalIdeal U.Rbar • (⊤ : Submodule U.Rbar m)) x
      rw [Submodule.Quotient.eq, hm, ideal_smul_top_eq_comap_sq m]
      have hcomb : (cotangentSqSub k U.Rbar U.π).mkQ (∑ i : Fin r, c i • v i) =
          (cotangentSqSub k U.Rbar U.π).mkQ x := by
        rw [map_sum]
        have hterm : ∀ i : Fin r,
            (cotangentSqSub k U.Rbar U.π).mkQ (c i • v i) = c i • b i := fun i => by
          rw [map_smul, Submodule.mkQ_apply, hv i]
        simp_rw [hterm]
        exact b.sum_repr (Submodule.Quotient.mk x)
      have hdiff : (∑ i : Fin r, c i • v i) - x ∈ cotangentSqSub k U.Rbar U.π :=
        (Submodule.Quotient.eq (cotangentSqSub k U.Rbar U.π)).mp hcomb
      have heq_sum : (∑ i : Fin r, (algebraMap k U.Rbar (c i)) • v i) = ∑ i : Fin r, c i • v i := by
        refine Finset.sum_congr rfl fun i _ => ?_
        apply Subtype.ext
        change algebraMap k U.Rbar (c i) * (v i).1 = c i • (v i).1
        rw [Algebra.smul_def]
      rw [heq_sum]
      exact hdiff
  exact nakayama_minGenCount_le g hg

end UniversalDeformationRing

end TangentCotangentMinimalGenerators

/-! ## Section 5: Direct Bridges to `TaylorWilesWindow` and `Stage2GaloisCohomology` -/

section DownstreamBridges

/-! ### Bridge 1: Tangent-Space Generator Bound → `TaylorWilesWindow.patched_selmer_obstruction_bound` -/

/-- **Deformation-Generator → Patched-Selmer Length Bound**:
if a patched module `P : TaylorWilesWindow.PatchedModuleBoundData R_inf` has generator rank
bounded by the universal deformation ring's tangent-space generator count
`μ(m_{R_Q} / (ϖ, m_{R_Q}²)) = dim H¹_{L_Q}`, and a Selmer module `Sel` embeds into `P.M_0` with
obstruction quotient length `≤ obsLen`, then `length(Sel) ≠ ⊤` and
`(length(Sel)).toNat ≤ dim H¹_{L_Q} * obsLen`! -/
theorem patched_obstruction_bound_of_deform_generators
    {k : Type*} [Field k] {Places : Type*} [Fintype Places] [DecidableEq Places]
    {D : PoitouTateData k Places} {L_Q : ∀ v : Places, Submodule k (D.H1v v)}
    (U : UniversalDeformRingData D L_Q)
    {R_inf Sel : Type*} [CommRing R_inf] [AddCommGroup Sel] [Module R_inf Sel]
    (P : TaylorWilesWindow.PatchedModuleBoundData R_inf)
    (hgen : P.genRank ≤ minGenCount k (CotangentSpace k U.Rbar U.π))
    (ι : Sel →ₗ[R_inf] P.M_0) (hι : Function.Injective ι)
    {obsLen : ℕ} (hobs : Module.length R_inf (R_inf ⧸ P.obsIdeal) ≤ (obsLen : ℕ∞)) :
    Module.length R_inf Sel ≠ ⊤ ∧
      (Module.length R_inf Sel).toNat ≤ Module.finrank k (D.Selmer L_Q) * obsLen := by
  obtain ⟨hfin, hle⟩ := TaylorWilesWindow.patched_selmer_obstruction_bound P ι hι hobs
  rw [(universalDeformRing_minGen_eq_selmer_dim U).1] at hgen
  exact ⟨hfin, hle.trans (Nat.mul_le_mul_right obsLen hgen)⟩

/-! ### Bridge 2: Taylor–Wiles Dual-Selmer Killing → `Stage2GaloisCohomology.vvle_of_greenberg_wiles` -/

/-- A `Stage2GaloisCohomology.CohomologySelmerFamily` equipped at every `(E, l, e)` with a base
ramification set `S`, unramified local conditions outside `S`, and Taylor–Wiles Chebotarev
auxiliary primes `TW` killing the dual Selmer group! -/
structure TaylorWilesKilledSelmerFamily where
  base : CohomologySelmerFamily
  S : ∀ (E : Type) [Field E] [NumberField E] (l : Nat.Primes) (e : ℕ),
    Finset (base.Places E l e)
  TW : ∀ (E : Type) [Field E] [NumberField E] (l : Nat.Primes) (e : ℕ),
    base.Places E l e → Prop
  hTW_disj : ∀ (E : Type) [Field E] [NumberField E] (l : Nat.Primes) (e : ℕ) (v : base.Places E l e),
    TW E l e v → v ∉ S E l e
  hunram : ∀ (E : Type) [Field E] [NumberField E] (l : Nat.Primes) (e : ℕ) (v : base.Places E l e),
    v ∉ S E l e →
      Module.finrank (base.k E l e) (base.locCond E l e v) =
        Module.finrank (base.k E l e) ((base.pt E l e).H0v v)
  hTW_codim : ∀ (E : Type) [Field E] [NumberField E] (l : Nat.Primes) (e : ℕ) (v : base.Places E l e),
    TW E l e v →
      Module.finrank (base.k E l e)
        (((base.pt E l e).pair11 v).ortho (base.locCond E l e v)) = 1
  hCheb : ∀ (E : Type) [Field E] [NumberField E] (l : Nat.Primes) (e : ℕ)
    (ψ : (base.pt E l e).DualSelmer (base.locCond E l e)),
    ψ ≠ 0 → ∃ v : base.Places E l e, TW E l e v ∧ (base.pt E l e).loc1Dual ψ.1 v ≠ 0

/-- Chosen dual-killing Taylor–Wiles prime set `Q(E, l, e)` at every `(E, l, e)`. -/
def TaylorWilesKilledSelmerFamily.killingSet (F : TaylorWilesKilledSelmerFamily)
    (E : Type) [Field E] [NumberField E] (l : Nat.Primes) (e : ℕ) :
    Finset (F.base.Places E l e) :=
  (taylor_wiles_kill_dual_selmer (F.base.pt E l e) (F.base.bal E l e) (F.base.locCond E l e)
    (F.S E l e) (F.TW E l e) (F.hTW_disj E l e) (F.hunram E l e) (F.hTW_codim E l e)
    (F.hCheb E l e)).choose

theorem TaylorWilesKilledSelmerFamily.killingSet_spec (F : TaylorWilesKilledSelmerFamily)
    (E : Type) [Field E] [NumberField E] (l : Nat.Primes) (e : ℕ) :
    let Q := F.killingSet E l e
    (∀ v ∈ Q, F.TW E l e v) ∧
    Disjoint Q (F.S E l e) ∧
    Q.card = Module.finrank (F.base.k E l e) ((F.base.pt E l e).DualSelmer (F.base.locCond E l e)) ∧
    Module.finrank (F.base.k E l e)
      ((F.base.pt E l e).DualSelmer (relaxCond (F.base.pt E l e) (F.base.locCond E l e) Q)) = 0 ∧
    (Module.finrank (F.base.k E l e)
      ((F.base.pt E l e).Selmer (relaxCond (F.base.pt E l e) (F.base.locCond E l e) Q)) : ℤ) =
      (Q.card : ℤ) +
        ((Module.finrank (F.base.k E l e) (F.base.pt E l e).H0 : ℤ) -
          Module.finrank (F.base.k E l e) (F.base.pt E l e).H0d) +
        ∑ v ∈ F.S E l e,
          ((Module.finrank (F.base.k E l e) (F.base.locCond E l e v) : ℤ) -
            Module.finrank (F.base.k E l e) ((F.base.pt E l e).H0v v)) ∧
    (F.base.pt E l e).Selmer (relaxCond (F.base.pt E l e) (F.base.locCond E l e) Q) =
      (F.base.pt E l e).Selmer (F.base.locCond E l e) :=
  (taylor_wiles_kill_dual_selmer (F.base.pt E l e) (F.base.bal E l e) (F.base.locCond E l e)
    (F.S E l e) (F.TW E l e) (F.hTW_disj E l e) (F.hunram E l e) (F.hTW_codim E l e)
    (F.hCheb E l e)).choose_spec

/-- Relaxed `CohomologySelmerFamily` with local conditions `L_{Q(E, l, e)}` whose dual Selmer
groups vanish identically at every `(E, l, e)`. -/
def TaylorWilesKilledSelmerFamily.relaxedFamily (F : TaylorWilesKilledSelmerFamily) :
    CohomologySelmerFamily where
  k := F.base.k
  Places := F.base.Places
  pt := F.base.pt
  bal := F.base.bal
  locCond E _ _ l e :=
    relaxCond (F.base.pt E l e) (F.base.locCond E l e) (F.killingSet E l e)

/-- **Taylor–Wiles Dual-Selmer Killing → `Stage2GaloisCohomology.vvle_of_greenberg_wiles` Bridge**:
for any `TaylorWilesKilledSelmerFamily`, the killed-dual presentation bound
`Q.card + (dim H⁰ - dim H⁰*) + ∑_{v ∈ S} (dim L_v - dim H⁰_v)` directly implies BOTH
`VVle F.relaxedFamily.toSelmerSystem E t B` AND `VVle F.base.toSelmerSystem E t B`! -/
theorem vvle_of_taylor_wiles_dual_killing (F : TaylorWilesKilledSelmerFamily)
    (E : Type) [Field E] [NumberField E] (t : ℕ) (B : ℝ)
    (hsum : ∀ P : Finset Nat.Primes,
      ∑ l ∈ P, Real.log (l : ℕ) * ∑ e ∈ Finset.Ico 1 t,
        (((F.killingSet E l e).card : ℤ) +
          ((Module.finrank (F.base.k E l e) (F.base.pt E l e).H0 : ℤ) -
            Module.finrank (F.base.k E l e) (F.base.pt E l e).H0d) +
          ∑ v ∈ F.S E l e,
            ((Module.finrank (F.base.k E l e) (F.base.locCond E l e v) : ℤ) -
              Module.finrank (F.base.k E l e) ((F.base.pt E l e).H0v v)) : ℝ) ≤ B) :
    VVle F.relaxedFamily.toSelmerSystem E t B ∧ VVle F.base.toSelmerSystem E t B := by
  have hrel : VVle F.relaxedFamily.toSelmerSystem E t B := by
    refine vvle_of_greenberg_wiles F.relaxedFamily E t B (fun P => ?_)
    have heq :
        ∑ l ∈ P, Real.log (l : ℕ) * ∑ e ∈ Finset.Ico 1 t,
          (((Module.finrank (F.relaxedFamily.k E l e)
              ((F.relaxedFamily.pt E l e).DualSelmer (F.relaxedFamily.locCond E l e)) : ℤ) +
            (Module.finrank (F.relaxedFamily.k E l e) (F.relaxedFamily.pt E l e).H0 : ℤ) -
            (Module.finrank (F.relaxedFamily.k E l e) (F.relaxedFamily.pt E l e).H0d : ℤ) +
            ∑ v : F.relaxedFamily.Places E l e,
              ((Module.finrank (F.relaxedFamily.k E l e) (F.relaxedFamily.locCond E l e v) : ℤ) -
                Module.finrank (F.relaxedFamily.k E l e) ((F.relaxedFamily.pt E l e).H0v v)) : ℤ) : ℝ) =
        ∑ l ∈ P, Real.log (l : ℕ) * ∑ e ∈ Finset.Ico 1 t,
          (((F.killingSet E l e).card : ℤ) +
            ((Module.finrank (F.base.k E l e) (F.base.pt E l e).H0 : ℤ) -
              Module.finrank (F.base.k E l e) (F.base.pt E l e).H0d) +
            ∑ v ∈ F.S E l e,
              ((Module.finrank (F.base.k E l e) (F.base.locCond E l e v) : ℤ) -
                Module.finrank (F.base.k E l e) ((F.base.pt E l e).H0v v)) : ℝ) := by
      refine Finset.sum_congr rfl fun l _ => ?_
      congr 1
      refine Finset.sum_congr rfl fun e _ => ?_
      obtain ⟨_, _, _, hvan, hpres, _⟩ := F.killingSet_spec E l e
      have hgw := (F.base.pt E l e).greenberg_wiles_of_dual_vanishing (F.base.bal E l e)
        (relaxCond (F.base.pt E l e) (F.base.locCond E l e) (F.killingSet E l e)) hvan
      have hz :
          ((Module.finrank (F.base.k E l e)
              ((F.base.pt E l e).DualSelmer
                (relaxCond (F.base.pt E l e) (F.base.locCond E l e) (F.killingSet E l e))) : ℤ) +
            (Module.finrank (F.base.k E l e) (F.base.pt E l e).H0 : ℤ) -
            (Module.finrank (F.base.k E l e) (F.base.pt E l e).H0d : ℤ) +
            ∑ v : F.base.Places E l e,
              ((Module.finrank (F.base.k E l e)
                  (relaxCond (F.base.pt E l e) (F.base.locCond E l e) (F.killingSet E l e) v) : ℤ) -
                Module.finrank (F.base.k E l e) ((F.base.pt E l e).H0v v))) =
          ((F.killingSet E l e).card : ℤ) +
            ((Module.finrank (F.base.k E l e) (F.base.pt E l e).H0 : ℤ) -
              Module.finrank (F.base.k E l e) (F.base.pt E l e).H0d) +
            ∑ v ∈ F.S E l e,
              ((Module.finrank (F.base.k E l e) (F.base.locCond E l e v) : ℤ) -
                Module.finrank (F.base.k E l e) ((F.base.pt E l e).H0v v)) := by
        rw [hvan, Nat.cast_zero, zero_add]
        linarith
      exact_mod_cast hz
    rw [heq]
    exact hsum P
  have hbase : VVle F.base.toSelmerSystem E t B := by
    have hsha_eq : ∀ (l : Nat.Primes) (e : ℕ),
        F.base.toSelmerSystem.shaLen E l e = F.relaxedFamily.toSelmerSystem.shaLen E l e := by
      intro l e
      obtain ⟨_, _, _, _, _, hsel_eq⟩ := F.killingSet_spec E l e
      change Module.length (F.base.k E l e) ((F.base.pt E l e).Selmer (F.base.locCond E l e)) =
        Module.length (F.base.k E l e)
          ((F.base.pt E l e).Selmer
            (relaxCond (F.base.pt E l e) (F.base.locCond E l e) (F.killingSet E l e)))
      rw [hsel_eq]
    refine ⟨fun l e he1 he2 => by rw [hsha_eq]; exact hrel.1 l e he1 he2, fun P => ?_⟩
    have hsum_eq :
        ∑ l ∈ P, Real.log (l : ℕ) * ∑ e ∈ Finset.Ico 1 t,
          ((F.base.toSelmerSystem.shaLen E l e).toNat : ℝ) =
        ∑ l ∈ P, Real.log (l : ℕ) * ∑ e ∈ Finset.Ico 1 t,
          ((F.relaxedFamily.toSelmerSystem.shaLen E l e).toNat : ℝ) := by
      refine Finset.sum_congr rfl fun l _ => ?_
      congr 1
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [hsha_eq]
    rw [hsum_eq]
    exact hrel.2 P
  exact ⟨hrel, hbase⟩

/-! ### Bridge 3: Complete Deformation-Cohomology System → `Stage2GaloisCohomology.minimalGaloisCohomology_of_system` -/

/-- Unified Stage 3 **Galois Deformation & Cohomology System**:
packages:
1. a `Stage2GaloisCohomology.GaloisCohomologySystem` (`coh`),
2. a residual matrix representation `ρbar : G_S →* GL_n(k)` (with Mazur tangent space
   `Deform_1(ρ̄) ≃ H¹(G_S, Ad(ρ̄))`),
3. base ramification set `S`, local Selmer conditions `L`, and Taylor–Wiles Chebotarev primes `TW`
   killing `H¹_{L^⊥}`! -/
structure DeformationCohomologySystem where
  coh : GaloisCohomologySystem
  dim : ℕ
  ρbar : coh.G_S →* Matrix.GeneralLinearGroup (Fin dim) coh.k
  S : Finset coh.Places
  L : ∀ v : coh.Places, Submodule coh.k (coh.ptData.H1v v)
  TW : coh.Places → Prop
  hTW_disj : ∀ v, TW v → v ∉ S
  hunram : ∀ v : coh.Places, v ∉ S →
    Module.finrank coh.k (L v) = Module.finrank coh.k (coh.ptData.H0v v)
  hTW_codim : ∀ v, TW v → Module.finrank coh.k ((coh.ptData.pair11 v).ortho (L v)) = 1
  hCheb : ∀ ψ : coh.ptData.DualSelmer L, ψ ≠ 0 →
    ∃ v : coh.Places, TW v ∧ coh.ptData.loc1Dual ψ.1 v ≠ 0

/-- **Master Stage 3 Discharge Theorem**:
every `DeformationCohomologySystem` SIMULTANEOUSLY proves:
1. All **5/5** live fields of `RHDirect.MinimalGaloisCohomology` (via
   `Stage2GaloisCohomology.minimalGaloisCohomology_of_system`),
2. The **Mazur Tangent-Space Isomorphism** `Deform_1(ρ̄) ≃ H¹(G_S, Ad(ρ̄))`,
3. **Taylor–Wiles Dual-Selmer Killing & Exact Presentation Balance** with
   `q = dim H¹_{L^⊥}` auxiliary primes (`H¹_{L_Q^⊥} = 0`)! -/
theorem minimalGaloisCohomology_of_deformationSystem (D : DeformationCohomologySystem) :
    MinimalGaloisCohomology (concreteCohomologyCarrier D.coh) ∧
      Nonempty (Deform1 D.ρbar ≃ H1Group D.coh.G_S (AdRep D.ρbar)) ∧
      ∃ Q : Finset D.coh.Places,
        (∀ v ∈ Q, D.TW v) ∧
        Disjoint Q D.S ∧
        Q.card = Module.finrank D.coh.k (D.coh.ptData.DualSelmer D.L) ∧
        Module.finrank D.coh.k (D.coh.ptData.DualSelmer (relaxCond D.coh.ptData D.L Q)) = 0 ∧
        (Module.finrank D.coh.k (D.coh.ptData.Selmer (relaxCond D.coh.ptData D.L Q)) : ℤ) =
          (Q.card : ℤ) +
            ((Module.finrank D.coh.k D.coh.ptData.H0 : ℤ) -
              Module.finrank D.coh.k D.coh.ptData.H0d) +
            ∑ v ∈ D.S, ((Module.finrank D.coh.k (D.L v) : ℤ) -
              Module.finrank D.coh.k (D.coh.ptData.H0v v)) := by
  refine ⟨minimalGaloisCohomology_of_system D.coh, ⟨mazurTangentEquiv D.ρbar⟩, ?_⟩
  obtain ⟨Q, hTW, hdisj, hcard, hvan, hpres, _⟩ :=
    taylor_wiles_kill_dual_selmer D.coh.ptData D.coh.eulerBalance D.L D.S D.TW
      D.hTW_disj D.hunram D.hTW_codim D.hCheb
  exact ⟨Q, hTW, hdisj, hcard, hvan, hpres⟩

end DownstreamBridges

/-! ## Section 6: Unconditional Non-Vacuity Witnesses (over `k = ZMod 3`) -/

section NonVacuity

/-- **Non-Vacuity Witness 1 (Mazur Tangent Space + Fixed-Determinant Subspace)**:
over `k = ZMod 3`, `n = Fin 2`, `G = Multiplicative (ZMod 2)` (modeling complex conjugation
`Gal(ℂ/ℝ)`), both `Deform_1(ρ̄) ≃ₗ[k] H¹(G, Ad(ρ̄))` and
`Deform_1^{det}(ρ̄) ≃ H¹(G, Ad⁰(ρ̄))` are unconditionally inhabited. -/
theorem exists_mazur_tangent_nonvacuous :
    ∃ (ρbar : Multiplicative (ZMod 2) →* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)),
      Nonempty (Deform1 ρbar ≃ₗ[ZMod 3] H1Space (ZMod 3) (Multiplicative (ZMod 2)) (AdRep ρbar)) ∧
      Nonempty (FixedDetDeform1 ρbar ≃ H1Group (Multiplicative (ZMod 2)) (AdRep.Ad0Submodule ρbar)) :=
  ⟨1,
    ⟨mazurTangentLinearEquiv (1 : Multiplicative (ZMod 2) →* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))⟩,
    ⟨fixedDetDeformEquivH1Ad0 (1 : Multiplicative (ZMod 2) →* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))⟩⟩

/-- **Non-Vacuity Witness 2 (Taylor–Wiles Dual-Selmer Killing + Exact Presentation Balance +
`MinimalGaloisCohomology` Discharge)**:
realizes `cyclotomicToyPoitouTate 3` (`Places = Bool`, `S = {false}`, `TW = (· = true)`)
with a genuinely **1-dimensional** initial dual Selmer group `H¹_{L^⊥}` (`dim = 1`), killed by
adding `Q = {true}` (`Q.card = 1`), yielding `H¹_{L_Q^⊥} = 0`, exact presentation balance
`dim H¹_{L_Q} = 1`, AND all 5/5 fields of `MinimalGaloisCohomology` — with **ZERO** hypotheses! -/
theorem exists_deformationCohomologySystem_nonvacuous :
    ∃ (D : DeformationCohomologySystem),
      Module.finrank D.coh.k (D.coh.ptData.DualSelmer D.L) = 1 ∧
      MinimalGaloisCohomology (concreteCohomologyCarrier D.coh) ∧
      ∃ Q : Finset D.coh.Places,
        Q.card = 1 ∧
        Module.finrank D.coh.k (D.coh.ptData.DualSelmer (relaxCond D.coh.ptData D.L Q)) = 0 ∧
        Module.finrank D.coh.k (D.coh.ptData.Selmer (relaxCond D.coh.ptData D.L Q)) = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let coh : GaloisCohomologySystem :=
    { k := ZMod 3
      Places := Bool
      ptData := cyclotomicToyPoitouTate 3
      eulerBalance := cyclotomicToy_eulerBalance 3
      G_S := Multiplicative (ZMod 2)
      M := ZMod 3
      act_M :=
        { smul := fun _ m => m
          one_smul := fun _ => rfl
          mul_smul := fun _ _ _ => rfl
          smul_zero := fun _ => rfl
          smul_add := fun _ _ _ => rfl }
      N_triv := ⊤
      htriv := fun _ _ => rfl
      Q_ray := Unit
      qMap := 1
      hfactor := fun φ => ⟨1, by
        ext x
        have hord : (x : Multiplicative (ZMod 2)) ^ 2 = 1 := by
          change Multiplicative.ofAdd (2 • Multiplicative.toAdd (x : Multiplicative (ZMod 2))) = 1
          have h2 : (2 : ZMod 2) = 0 := rfl
          simp [nsmul_eq_mul, h2]
        have hφ2 : (φ x) ^ 2 = 1 := by
          rw [← map_pow]
          have hx2 : x ^ 2 = 1 := Subtype.ext hord
          rw [hx2, map_one]
        have hadd : (2 : ℕ) • Multiplicative.toAdd (φ x) = 0 := hφ2
        have h2 : (2 : ZMod 3) ≠ 0 := by
          intro h
          have hv : (2 : ℕ) = 0 := congrArg ZMod.val h
          exact Nat.succ_ne_zero 1 hv
        have h0 : Multiplicative.toAdd (φ x) = 0 := by
          have : (2 : ZMod 3) * Multiplicative.toAdd (φ x) = 0 := by
            simpa [nsmul_eq_mul] using hadd
          exact (mul_eq_zero.mp this).resolve_left h2
        exact h0⟩
      l_tower := 3
      l_ge_two := by decide
      iwLen := fun n => n
      μ := 0
      lam := 1
      nu := 0
      n₀ := 0
      iwGrowth := fun n _ => by simp
      iwLinear := ⟨1, fun n _ => by omega⟩ }
  -- Local condition `L`: at `true` (`p`), `L true = {(a, 0)}` (dim 1 = dim H⁰_p), with
  -- `L_true^⊥ = {(0, b)}` (dim 1), matching `im(loc1Dual) = {(0, b)}` so `dim DualSelmer L = 1`!
  let L_true : Submodule (ZMod 3) (ZMod 3 × ZMod 3) :=
    LinearMap.range (LinearMap.inl (ZMod 3) (ZMod 3) (ZMod 3))
  let L : ∀ b : Bool, Submodule (ZMod 3) (coh.ptData.H1v b)
    | false => ⊥
    | true => L_true
  have hL_true_dim : Module.finrank (ZMod 3) L_true = 1 := by
    let e : ZMod 3 ≃ₗ[ZMod 3] L_true :=
      LinearEquiv.ofInjective (LinearMap.inl (ZMod 3) (ZMod 3) (ZMod 3))
        (fun a b h => congrArg Prod.fst h)
    rw [← e.finrank_eq, Module.finrank_self]
  have hL_true_ortho_dim :
      Module.finrank (ZMod 3) ((coh.ptData.pair11 true).ortho (L true)) = 1 := by
    have hadd := (coh.ptData.pair11 true).ortho_finrank_add (L true)
    have h2 : Module.finrank (ZMod 3) (ZMod 3 × ZMod 3) = 2 := by
      rw [Module.finrank_prod, Module.finrank_self]
    change Module.finrank (ZMod 3) L_true +
      Module.finrank (ZMod 3) ((coh.ptData.pair11 true).ortho (L true)) =
        Module.finrank (ZMod 3) (ZMod 3 × ZMod 3) at hadd
    rw [hL_true_dim, h2] at hadd
    omega
  let D : DeformationCohomologySystem :=
    { coh := coh
      dim := 2
      ρbar := 1
      S := {false}
      L := L
      TW := fun b => b = true
      hTW_disj := fun b hb => by subst hb; simp
      hunram := fun b hb => by
        cases b
        · exact absurd (Finset.mem_singleton_self false) hb
        · change Module.finrank (ZMod 3) L_true = Module.finrank (ZMod 3) (ZMod 3)
          rw [hL_true_dim, Module.finrank_self]
      hTW_codim := fun b hb => by subst hb; exact hL_true_ortho_dim
      hCheb := fun ψ hψ => by
        refine ⟨true, rfl, ?_⟩
        intro h0
        have hψ0 : ψ.1 = 0 := congrArg Prod.snd h0
        exact hψ (Subtype.ext hψ0) }
  have hDual_top : D.coh.ptData.DualSelmer D.L = ⊤ := by
    rw [eq_top_iff]
    intro a _ b _
    cases b
    · intro x _
      dsimp only [D, coh, cyclotomicToyPoitouTate, zeroPairing]
      rfl
    · rintro x ⟨c, rfl⟩
      let a' : ZMod 3 := a
      change (c : ZMod 3) * 0 + 0 * a' = 0
      ring
  have hDual_dim : Module.finrank D.coh.k (D.coh.ptData.DualSelmer D.L) = 1 := by
    rw [hDual_top, finrank_top]
    exact Module.finrank_self (ZMod 3)
  obtain ⟨hMin, _, Q, _, _, hQcard, hQvan, hQpres⟩ :=
    minimalGaloisCohomology_of_deformationSystem D
  rw [hDual_dim] at hQcard
  have hSel_dim :
      Module.finrank D.coh.k (D.coh.ptData.Selmer (relaxCond D.coh.ptData D.L Q)) = 1 := by
    have hS : ∑ v ∈ D.S, ((Module.finrank D.coh.k (D.L v) : ℤ) -
        Module.finrank D.coh.k (D.coh.ptData.H0v v)) = -1 := by
      change ∑ v ∈ ({false} : Finset Bool),
        ((Module.finrank (ZMod 3) (L v) : ℤ) - Module.finrank (ZMod 3) (ZMod 3)) = -1
      rw [Finset.sum_singleton]
      have h0 : Module.finrank (ZMod 3) (L false) = 0 := finrank_bot (ZMod 3) PUnit
      rw [h0, Module.finrank_self]
      norm_num
    have hH0 : Module.finrank D.coh.k D.coh.ptData.H0 = 1 := Module.finrank_self (ZMod 3)
    have hH0d : Module.finrank D.coh.k D.coh.ptData.H0d = 0 := by
      change Module.finrank (ZMod 3) PUnit = 0
      exact Module.finrank_zero_of_subsingleton
    rw [hQcard, hH0, hH0d, hS] at hQpres
    omega
  exact ⟨D, hDual_dim, hMin, Q, hQcard, hQvan, hSel_dim⟩

/-- **Non-Vacuity Witness 3 (Zariski Tangent–Cotangent Duality & `minGenCount = 1`)**:
for the dual-numbers ring `A = DualNumber k` with augmentation `fstHom`, the cotangent
space `m_A ⧸ m_A²` has exact dimension and minimal generator count `1`! -/
theorem dualNumber_minGenCount_eq_one (k : Type*) [Field k] :
    let π : DualNumber k →ₐ[k] k :=
      { toRingHom := TrivSqZeroExt.fstHom k k k
        commutes' := fun c => by simp }
    Module.finrank k (CotangentSpace k (DualNumber k) π) = 1 ∧
      minGenCount k (CotangentSpace k (DualNumber k) π) = 1 := by
  intro π
  let e : CotangentSpace k (DualNumber k) π ≃ₗ[k] k :=
    LinearEquiv.ofBijective
      (Submodule.liftQ (cotangentSqSub k (DualNumber k) π)
        { toFun := fun x => x.1.snd
          map_add' := fun x y => TrivSqZeroExt.snd_add x.1 y.1
          map_smul' := fun c x => by
            change (c • x.1).snd = c * x.1.snd
            simp [smul_eq_mul] }
        (fun x hx => by
          rw [LinearMap.mem_ker]
          change x.1.snd = 0
          have hsq : x.1 ∈ (RingHom.ker π.toRingHom) ^ 2 := hx
          rw [sq] at hsq
          refine Submodule.mul_induction_on hsq ?_ ?_
          · intro a ha b hb
            have ha0 : a.fst = 0 := ha
            have hb0 : b.fst = 0 := hb
            rw [dual_mul_eq_zero_of_fst_zero ha0 hb0]
            rfl
          · intro a b ha hb
            rw [TrivSqZeroExt.snd_add, ha, hb, add_zero]))
      ⟨by
        intro q₁ q₂ h
        induction q₁ using Quotient.inductionOn' with
        | h x₁ =>
          induction q₂ using Quotient.inductionOn' with
          | h x₂ =>
            have hsnd : x₁.1.snd = x₂.1.snd := h
            have hfst1 : x₁.1.fst = 0 := x₁.2
            have hfst2 : x₂.1.fst = 0 := x₂.2
            have hval : x₁ = x₂ := Subtype.ext (TrivSqZeroExt.ext (hfst1.trans hfst2.symm) hsnd)
            rw [hval]
      , fun c => ⟨Submodule.Quotient.mk ⟨TrivSqZeroExt.inr c, by simp [π]⟩, by
          change (TrivSqZeroExt.inr c : DualNumber k).snd = c
          simp⟩⟩
  have hfd : FiniteDimensional k (CotangentSpace k (DualNumber k) π) :=
    Module.Finite.equiv e.symm
  have hdim : Module.finrank k (CotangentSpace k (DualNumber k) π) = 1 := by
    rw [e.finrank_eq, Module.finrank_self]
  exact ⟨hdim, (minGenCount_eq_finrank (k := k)).trans hdim⟩

end NonVacuity

end RHDirect.Stage3GaloisDeformation

end
