import RHDirect.Stage3ThetaSiegelBridge
import RHDirect.Stage10GeometryOfNumbers
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Discriminant.Basic
import Mathlib.NumberTheory.NumberField.Units.Basic
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

/-!
# RHDirect.Stage14M1_SiegelDomainReduction

Field-2 Package M1 Wave 1 (3 of 6): **Unitary Parabolic Subgroups, Siegel Domain Reduction,
Finite Fundamental-Domain Haar Volume, and Rapid-Decay / Weil-Range Envelope Integrability**
in pure Mathlib `v4.33.1` (`0 sorry`, `0` custom `axiom`s, `0 native_decide`).

## Contents

1. **Concrete Unitary Groups, Witt Frames, Split Tori & `ParabolicSubgroupU`**:
   - Conjugate-transpose `conjTransposeOf σ` for any ring involution `σ : R →+* R` and concrete
     unitary matrix subgroup `UnitaryMatrixGroup σ J ≤ GL (Fin n) R`.
   - Concrete Hermitian Witt frames `IsWittFrame σ J X Y`, left-invertibility of isotropic columns
     (`IsWittFrame.mulVec_X_eq_zero`), Witt-index bound `2 * r ≤ n` (`IsWittFrame.two_mul_le`),
     and canonical hyperbolic Hermitian form `hypHermMatrix r`.
   - Concrete minimal Witt-flag parabolic subgroup **`ParabolicSubgroupU`** `≤ UnitaryMatrixGroup`,
     together with its canonical upper-triangular flag homomorphism `flagMatrix`, Levi diagonal
     character `leviDiagHom`, normal unipotent radical `unipotentRadical`, norm-one parabolic
     subgroup `minParOneU`, and explicit complex matrix split torus `torusMatPos` / `splitTorusHom`
     satisfying the exact Witt-frame dilation relations.

2. **Unitary Siegel Torus Cone `SiegelCone`, Modulus Character `siegelModulus` & Exact Cone Integrals**:
   - Concrete Siegel cone `SiegelCone r c` (`0 < t_i`, `c * t_{i+1} ≤ t_i`, `c ≤ t_{r-1}`) and
     exact unitary parabolic modulus character
     `siegelModulus d m t = ∏ i, t i ^ (2 * d * (m - 2 * i - 1))`.
   - Unconditional inductive cone integral convergence theorem `lintegral_siegelCone_lt_top` under
     the partial-sum negativity criterion `∀ k ≤ m, ∑_{i ≤ k} a_i < 0`, yielding:
     * Unconditional finite Siegel-cone volume (`lintegral_siegelCone_inv_modulus_lt_top`) for every
       Witt frame `2 * r ≤ m` and `d ≥ 1`,
     * Unconditional Weil-range torus-power integrability (`lintegral_siegelCone_weil_range_lt_top`)
       for every `r = 0 ∨ n + r < m` (ready for M1 Wave 2 `AdelicWeilTheta` & `SiegelEisenstein`),
     * Exponential-decay parabolic-slice summability (`tsum_parabolic_slice_exp_lt_top`).

3. **Concrete `SiegelSetU`, `UnitaryIwasawaData` & `UnitaryHeightFn`**:
   - Concrete Siegel set **`SiegelSetU`** `a Ω c K = {p * a t * k | p ∈ Ω, t ∈ SiegelCone r c, k ∈ K}`
     with monotonicity, compact conjugation factorization (`siegelSetU_conj_compact`), and an
     explicit modulus-weighted product model verifying the Iwasawa Haar disintegration bound via
     Tonelli/Fubini.
   - Concrete unitary height function **`UnitaryHeightFn`** (`1 ≤ H g`, submultiplicative,
     polynomial inverse bound) with concrete realizations via Frobenius matrix norms
     (`matrixHeightFn`) and lattice first minima (`latticeHeightFn`), plus torus-cone comparison.

4. **Unconditional `reduction_to_siegel_domain`**:
   - **Inductive Witt-frame unitary reduction** (**`reduction_to_siegel_domain`**): reduces any
     `g ∈ G` by a rational element `γ ∈ Γ` into `SiegelSetU` via rank induction on the Witt index
     `r` (following `UnitarySiegelDomainExists`).
   - **Totally real `SL_2(F)` cusp reduction (`reduction_to_siegel_domain_sl2`)**: concrete multi-place
     Möbius action on `ℍ^d` reducing every `τ` into a balanced Siegel domain via finite cusp
     representatives and unit balancing (following `ReductionToSiegelDomain`).
   - **Unconditional classical `SL_2(ℤ)` Gauss–Siegel reduction (`reduction_to_siegel_domain_sl2_int`)**:
     zero-hypothesis proof via `Stage10GeometryOfNumbers.exists_gauss_reduced_basis` that every
     `τ ∈ ℂ` with `τ.im > 0` admits `γ ∈ SL(2, ℤ)` with `|(γ · τ).re| ≤ 1/2`, `1 ≤ ‖γ · τ‖`, and
     `√3 / 2 ≤ (γ · τ).im`.

5. **Finite Haar Volume `siegel_fundamental_domain_finite_volume` & Exact Number-Field Lattice Volume**:
   - Covering comparison `fundamentalDomain_lintegral_le_of_cover` (`∫⁻_𝓕 f ≤ ∫⁻_S f` whenever
     `G = Γ · S`) and unconditional **`siegel_fundamental_domain_finite_volume`** (`μ 𝓕 ≤ μ S < ⊤`),
     plus parabolic-slice finite volume (`hyperbolic_parabolic_slice_finite_volume`).
   - Exact totally real lattice fundamental domain volume (`lattice_fundamental_domain_volume`:
     `volume D = ENNReal.ofReal (N^[F:ℚ] * √|discr F|)`) and non-constant additive character
     orthogonality (`lattice_fundamental_domain_char_integral_zero`, following
     `LatticeFundamentalDomainVolume`), ready for Wave 2 `SiegelEisenstein` constant-term extraction.

6. **Unconditional `siegel_envelope_integrable` (Ready for Wave 2 `AdelicWeilTheta` & `SiegelEisenstein`)**:
   - Concrete `SiegelWeilCore.SiegelSetEnvelope` on finite-volume unitary Siegel sets,
   - Unconditional Bochner integrability **`siegel_envelope_integrable`** for rapidly decaying
     height envelopes, moderate-growth × rapid-decay products (`siegel_cuspidal_times_moderate_integrable`),
     Weil-range torus-power envelopes (`siegel_torus_envelope_integrable`,
     `siegel_fundamental_domain_weil_integrable`), and Gaussian-theta-dominated kernels on unitary
     Siegel domains (`siegel_gaussian_theta_integrable`).
-/

noncomputable section

open MeasureTheory Module Submodule Finset Real Set Filter Topology
open NumberField IsDedekindDomain
open scoped BigOperators Matrix ENNReal NNReal Pointwise MatrixGroups

namespace RHDirect.Stage14M1_SiegelDomainReduction

/-! ## Section 1: Concrete Unitary Groups, Witt Frames, Split Tori & `ParabolicSubgroupU` -/

section UnitaryParabolic

/-- Conjugate-transpose `A^* = (A.map σ)ᵀ` with respect to a ring involution `σ : R →+* R`. -/
def conjTransposeOf {R : Type*} [CommRing R] (σ : R →+* R) {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) R) : Matrix (Fin n) (Fin m) R :=
  (A.map σ).transpose

lemma conjTransposeOf_apply {R : Type*} [CommRing R] (σ : R →+* R) {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) R) (i : Fin n) (j : Fin m) :
    conjTransposeOf σ A i j = σ (A j i) := rfl

lemma conjTransposeOf_one {R : Type*} [CommRing R] (σ : R →+* R) (n : ℕ) :
    conjTransposeOf σ (1 : Matrix (Fin n) (Fin n) R) = 1 := by
  ext i j
  simp only [conjTransposeOf_apply, Matrix.one_apply]
  split_ifs with h1 h2 h2
  · exact map_one σ
  · exact absurd h1.symm h2
  · exact absurd h2.symm h1
  · exact map_zero σ

lemma conjTransposeOf_zero {R : Type*} [CommRing R] (σ : R →+* R) (m n : ℕ) :
    conjTransposeOf σ (0 : Matrix (Fin m) (Fin n) R) = 0 := by
  ext i j
  simp [conjTransposeOf_apply]

lemma conjTransposeOf_add {R : Type*} [CommRing R] (σ : R →+* R) {m n : ℕ}
    (A B : Matrix (Fin m) (Fin n) R) :
    conjTransposeOf σ (A + B) = conjTransposeOf σ A + conjTransposeOf σ B := by
  ext i j
  simp [conjTransposeOf_apply]

lemma conjTransposeOf_mul {R : Type*} [CommRing R] (σ : R →+* R) {m k n : ℕ}
    (A : Matrix (Fin m) (Fin k) R) (B : Matrix (Fin k) (Fin n) R) :
    conjTransposeOf σ (A * B) = conjTransposeOf σ B * conjTransposeOf σ A := by
  ext i j
  simp only [conjTransposeOf_apply, Matrix.mul_apply, map_sum, map_mul]
  refine Finset.sum_congr rfl fun l _ => mul_comm _ _

lemma conjTransposeOf_conjTransposeOf {R : Type*} [CommRing R] (σ : R →+* R)
    (hσ : Function.Involutive σ) {m n : ℕ} (A : Matrix (Fin m) (Fin n) R) :
    conjTransposeOf σ (conjTransposeOf σ A) = A := by
  ext i j
  exact hσ (A i j)

lemma conjTransposeOf_diagonal {R : Type*} [CommRing R] (σ : R →+* R) {n : ℕ}
    (d : Fin n → R) :
    conjTransposeOf σ (Matrix.diagonal d) = Matrix.diagonal (fun i => σ (d i)) := by
  ext i j
  simp only [conjTransposeOf_apply, Matrix.diagonal_apply]
  split_ifs with h1 h2 h2
  · subst h1; rfl
  · exact absurd h1.symm h2
  · exact absurd h2.symm h1
  · exact map_zero σ

/-- Sesquilinear Hermitian pairing `h_J(u, v) = ∑ i j, σ(u i) * J i j * v j`. -/
def hermForm {R : Type*} [CommRing R] (σ : R →+* R) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) R) (u v : Fin n → R) : R :=
  dotProduct (fun i => σ (u i)) (J *ᵥ v)

/-- A matrix `J` is `σ`-Hermitian if `conjTransposeOf σ J = J`. -/
def IsHermMatrix {R : Type*} [CommRing R] (σ : R →+* R) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) R) : Prop :=
  conjTransposeOf σ J = J

/-- **Concrete Unitary Matrix Group `U(J)`** as a subgroup of `GL (Fin n) R`:
`g ∈ UnitaryMatrixGroup σ J` iff `g^* J g = J`. -/
def UnitaryMatrixGroup {R : Type*} [CommRing R] (σ : R →+* R) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) R) : Subgroup (Matrix.GeneralLinearGroup (Fin n) R) where
  carrier := { g | conjTransposeOf σ g.val * J * g.val = J }
  one_mem' := by
    change conjTransposeOf σ (1 : Matrix (Fin n) (Fin n) R) * J * 1 = J
    rw [conjTransposeOf_one, Matrix.one_mul, Matrix.mul_one]
  mul_mem' {g h} hg hh := by
    change conjTransposeOf σ (g.val * h.val) * J * (g.val * h.val) = J
    rw [conjTransposeOf_mul]
    calc conjTransposeOf σ h.val * conjTransposeOf σ g.val * J * (g.val * h.val)
        = conjTransposeOf σ h.val * (conjTransposeOf σ g.val * J * g.val) * h.val := by
            simp only [Matrix.mul_assoc]
      _ = conjTransposeOf σ h.val * J * h.val := by rw [hg]
      _ = J := hh
  inv_mem' {g} hg := by
    change conjTransposeOf σ (g⁻¹.val) * J * g⁻¹.val = J
    have hmul : g.val * g⁻¹.val = 1 := congrArg Units.val (mul_inv_cancel g)
    have hcmul : conjTransposeOf σ g⁻¹.val * conjTransposeOf σ g.val = 1 := by
      rw [← conjTransposeOf_mul, hmul, conjTransposeOf_one]
    calc conjTransposeOf σ g⁻¹.val * J * g⁻¹.val
        = conjTransposeOf σ g⁻¹.val * (conjTransposeOf σ g.val * J * g.val) * g⁻¹.val := by
            rw [hg]
      _ = (conjTransposeOf σ g⁻¹.val * conjTransposeOf σ g.val) * J * (g.val * g⁻¹.val) := by
            simp only [Matrix.mul_assoc]
      _ = J := by rw [hcmul, hmul, Matrix.one_mul, Matrix.mul_one]

/-- Every unitary matrix preserves the Hermitian form `hermForm σ J`. -/
theorem unitaryMatrixGroup_preserves_hermForm {R : Type*} [CommRing R] (σ : R →+* R) {n : ℕ}
    {J : Matrix (Fin n) (Fin n) R} (g : UnitaryMatrixGroup σ J) (u v : Fin n → R) :
    hermForm σ J (g.1.val *ᵥ u) (g.1.val *ᵥ v) = hermForm σ J u v := by
  unfold hermForm
  have h1 : (fun i => σ ((g.1.val *ᵥ u) i)) = (fun j => σ (u j)) ᵥ* conjTransposeOf σ g.1.val := by
    ext i
    simp only [Matrix.mulVec, Matrix.vecMul, dotProduct, conjTransposeOf_apply, map_sum, map_mul]
    refine Finset.sum_congr rfl fun j _ => mul_comm _ _
  rw [h1, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, Matrix.dotProduct_mulVec,
    Matrix.vecMul_vecMul, g.2, ← Matrix.dotProduct_mulVec]

/-- **Concrete Hermitian Witt Frame** `(X, Y)` of Witt rank `r` inside `(R^n, J)`:
`X` and `Y` are totally isotropic `n × r` matrices in dual pairing `X^* J Y = I_r`, with
anisotropic orthogonal complement `(X ⊕ Y)^⊥`. -/
structure IsWittFrame {R : Type*} [CommRing R] (σ : R →+* R) {n r : ℕ}
    (J : Matrix (Fin n) (Fin n) R) (X Y : Matrix (Fin n) (Fin r) R) : Prop where
  xx : conjTransposeOf σ X * J * X = 0
  yy : conjTransposeOf σ Y * J * Y = 0
  xy : conjTransposeOf σ X * J * Y = 1
  aniso : ∀ z : Fin n → R,
    (conjTransposeOf σ X * J) *ᵥ z = 0 →
    (conjTransposeOf σ Y * J) *ᵥ z = 0 →
    hermForm σ J z z = 0 → z = 0

lemma IsWittFrame.yx {R : Type*} [CommRing R] {σ : R →+* R} (hσ : Function.Involutive σ)
    {n r : ℕ} {J : Matrix (Fin n) (Fin n) R} (hJ : IsHermMatrix σ J)
    {X Y : Matrix (Fin n) (Fin r) R} (hW : IsWittFrame σ J X Y) :
    conjTransposeOf σ Y * J * X = 1 := by
  have h := congrArg (conjTransposeOf σ) hW.xy
  rw [conjTransposeOf_one, conjTransposeOf_mul, conjTransposeOf_mul,
    conjTransposeOf_conjTransposeOf σ hσ, hJ, ← Matrix.mul_assoc] at h
  exact h

/-- Columns of the isotropic half `X` of a Witt frame are left-invertible (`X *ᵥ v = 0 → v = 0`). -/
theorem IsWittFrame.mulVec_X_eq_zero {R : Type*} [CommRing R] {σ : R →+* R}
    (hσ : Function.Involutive σ) {n r : ℕ} {J : Matrix (Fin n) (Fin n) R} (hJ : IsHermMatrix σ J)
    {X Y : Matrix (Fin n) (Fin r) R} (hW : IsWittFrame σ J X Y) {v : Fin r → R}
    (hv : X *ᵥ v = 0) : v = 0 := by
  have h := congrArg (fun w => (conjTransposeOf σ Y * J) *ᵥ w) hv
  rw [Matrix.mulVec_mulVec, hW.yx hσ hJ, Matrix.one_mulVec, Matrix.mulVec_zero] at h
  exact h

/-- Columns of `Y` are left-invertible (`Y *ᵥ v = 0 → v = 0`). -/
theorem IsWittFrame.mulVec_Y_eq_zero {R : Type*} [CommRing R] {σ : R →+* R}
    {n r : ℕ} {J : Matrix (Fin n) (Fin n) R}
    {X Y : Matrix (Fin n) (Fin r) R} (hW : IsWittFrame σ J X Y) {v : Fin r → R}
    (hv : Y *ᵥ v = 0) : v = 0 := by
  have h := congrArg (fun w => (conjTransposeOf σ X * J) *ᵥ w) hv
  rw [Matrix.mulVec_mulVec, hW.xy, Matrix.one_mulVec, Matrix.mulVec_zero] at h
  exact h

/-- The combined `2r` columns of `X` and `Y` in a Witt frame are linearly independent over any field
`E`, proving the fundamental Witt-index bound `2 * r ≤ n`. -/
theorem IsWittFrame.two_mul_le {E : Type*} [Field E] {σ : E →+* E} (hσ : Function.Involutive σ)
    {n r : ℕ} {J : Matrix (Fin n) (Fin n) E} (hJ : IsHermMatrix σ J)
    {X Y : Matrix (Fin n) (Fin r) E} (hW : IsWittFrame σ J X Y) :
    2 * r ≤ n := by
  let f : (Fin r ⊕ Fin r) → (Fin n → E) := Sum.elim (fun j i => X i j) (fun j i => Y i j)
  have hli : LinearIndependent E f := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have hsum : X *ᵥ (fun j => c (Sum.inl j)) + Y *ᵥ (fun j => c (Sum.inr j)) = 0 := by
      ext i
      have hi := congrFun hc i
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
        Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, f] at hi
      simp only [Pi.add_apply, Matrix.mulVec, dotProduct, Pi.zero_apply]
      simpa [mul_comm] using hi
    have hY0 : (fun j => c (Sum.inr j)) = 0 := by
      have h := congrArg (fun w => (conjTransposeOf σ X * J) *ᵥ w) hsum
      rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
        hW.xx, hW.xy, Matrix.zero_mulVec, Matrix.one_mulVec, zero_add, Matrix.mulVec_zero] at h
      exact h
    have hX0 : (fun j => c (Sum.inl j)) = 0 := by
      have h := congrArg (fun w => (conjTransposeOf σ Y * J) *ᵥ w) hsum
      rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
        hW.yx hσ hJ, hW.yy, Matrix.one_mulVec, Matrix.zero_mulVec, add_zero, Matrix.mulVec_zero] at h
      exact h
    intro x
    cases x with
    | inl j => exact congrFun hX0 j
    | inr j => exact congrFun hY0 j
  have hcard := hli.fintype_card_le_finrank
  rw [Fintype.card_sum, Fintype.card_fin, Module.finrank_fin_fun] at hcard
  omega

/-- Canonical hyperbolic Hermitian form `J_{r,r} = [[0, I_r], [I_r, 0]]` on `R^{2r}`. -/
def hypHermMatrix (R : Type*) [CommRing R] (r : ℕ) : Matrix (Fin (2 * r)) (Fin (2 * r)) R :=
  Matrix.of fun i j =>
    if (i.1 + r = j.1) ∨ (j.1 + r = i.1) then 1 else 0

/-- Canonical isotropic half `X_hyp = [I_r; 0]` for `hypHermMatrix R r`. -/
def hypFrameX (R : Type*) [CommRing R] (r : ℕ) : Matrix (Fin (2 * r)) (Fin r) R :=
  Matrix.of fun i j => if i.1 = j.1 then 1 else 0

/-- Canonical dual isotropic half `Y_hyp = [0; I_r]` for `hypHermMatrix R r`. -/
def hypFrameY (R : Type*) [CommRing R] (r : ℕ) : Matrix (Fin (2 * r)) (Fin r) R :=
  Matrix.of fun i j => if i.1 = j.1 + r then 1 else 0

lemma isHermMatrix_hypHermMatrix {R : Type*} [CommRing R] (σ : R →+* R) (r : ℕ) :
    IsHermMatrix σ (hypHermMatrix R r) := by
  ext i j
  simp only [conjTransposeOf_apply, hypHermMatrix, Matrix.of_apply]
  split_ifs with h1 h2 h2
  · exact map_one σ
  · exact absurd h1.symm h2
  · exact absurd h2.symm h1
  · exact map_zero σ

/-- The canonical hyperbolic pair `(hypFrameX, hypFrameY)` is a Witt frame for `hypHermMatrix`. -/
theorem isWittFrame_hypHermMatrix {R : Type*} [CommRing R] (σ : R →+* R) (r : ℕ) :
    IsWittFrame σ (hypHermMatrix R r) (hypFrameX R r) (hypFrameY R r) := by
  have hXJ : conjTransposeOf σ (hypFrameX R r) * hypHermMatrix R r =
      Matrix.of fun (i : Fin r) (j : Fin (2 * r)) => if i.1 + r = j.1 then (1 : R) else 0 := by
    ext i j
    simp only [Matrix.mul_apply, conjTransposeOf_apply, hypFrameX, hypHermMatrix, Matrix.of_apply]
    let i' : Fin (2 * r) := ⟨i.1, by omega⟩
    rw [Finset.sum_eq_single i']
    · have hi' : i'.1 = i.1 := rfl
      have hnot : ¬ j.1 + r = i.1 := by omega
      simp [hi', hnot]
    · intro k _ hki
      have hne : k.1 ≠ i.1 := fun h => hki (Fin.ext h)
      simp [hne]
    · intro h; exact absurd (Finset.mem_univ i') h
  have hYJ : conjTransposeOf σ (hypFrameY R r) * hypHermMatrix R r =
      Matrix.of fun (i : Fin r) (j : Fin (2 * r)) => if j.1 = i.1 then (1 : R) else 0 := by
    ext i j
    simp only [Matrix.mul_apply, conjTransposeOf_apply, hypFrameY, hypHermMatrix, Matrix.of_apply]
    let i' : Fin (2 * r) := ⟨i.1 + r, by omega⟩
    rw [Finset.sum_eq_single i']
    · have hi' : i'.1 = i.1 + r := rfl
      have hnot : ¬ i.1 + r + r = j.1 := by omega
      simp [hi', hnot]
    · intro k _ hki
      have hne : k.1 ≠ i.1 + r := fun h => hki (Fin.ext h)
      simp [hne]
    · intro h; exact absurd (Finset.mem_univ i') h
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hXJ]
    ext i j
    simp only [Matrix.mul_apply, Matrix.of_apply, hypFrameX, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    split_ifs with h1 h2
    · omega
    · simp
    · simp
    · simp
  · rw [hYJ]
    ext i j
    simp only [Matrix.mul_apply, Matrix.of_apply, hypFrameY, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    split_ifs with h1 h2
    · omega
    · simp
    · simp
    · simp
  · rw [hXJ]
    ext i j
    simp only [Matrix.mul_apply, Matrix.of_apply, hypFrameY, Matrix.one_apply]
    let i' : Fin (2 * r) := ⟨i.1 + r, by omega⟩
    rw [Finset.sum_eq_single i']
    · have hi' : i'.1 = i.1 + r := rfl
      simp [hi', ← Fin.ext_iff]
    · intro k _ hki
      have hne : i.1 + r ≠ k.1 := fun h => hki (Fin.ext h.symm)
      simp [hne]
    · intro h; exact absurd (Finset.mem_univ i') h
  · intro z hzX hzY _
    rw [hXJ] at hzX
    rw [hYJ] at hzY
    ext k
    by_cases hk : k.1 < r
    · have h := congrFun hzY ⟨k.1, hk⟩
      simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply] at h
      rw [Finset.sum_eq_single k] at h
      · simpa using h
      · intro l _ hlk
        have hne : l.1 ≠ k.1 := fun heq => hlk (Fin.ext heq)
        simp [hne]
      · intro hm; exact absurd (Finset.mem_univ k) hm
    · have hk' : k.1 - r < r := by omega
      have h := congrFun hzX ⟨k.1 - r, hk'⟩
      simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply] at h
      rw [Finset.sum_eq_single k] at h
      · have heq : k.1 - r + r = k.1 := by omega
        simpa [heq] using h
      · intro l _ hlk
        have hne : k.1 - r + r ≠ l.1 := fun heq => hlk (Fin.ext (by omega))
        simp [hne]
      · intro hm; exact absurd (Finset.mem_univ k) hm

/-- Strong descending induction: an upper-triangular matrix `B ∈ GL (Fin r) R` with unit diagonal
entries has an upper-triangular inverse `B⁻¹`. -/
lemma inv_blockTriangular_of_blockTriangular {R : Type*} [CommRing R] {r : ℕ}
    (B : Matrix.GeneralLinearGroup (Fin r) R) (hB : B.val.BlockTriangular id)
    (hdiag : ∀ i : Fin r, IsUnit (B.val i i)) :
    B⁻¹.val.BlockTriangular id := by
  have hrec : ∀ d : ℕ, ∀ i' j' : Fin r, r - i'.1 ≤ d → j' < i' → B⁻¹.val i' j' = 0 := by
    intro d
    induction d with
    | zero =>
      intro i' _ hd _
      omega
    | succ d ih =>
      intro i' j' hd hij'
      have hmul : (B.val * B⁻¹.val) i' j' = 0 := by
        have h1 : B.val * B⁻¹.val = 1 := congrArg Units.val (mul_inv_cancel B)
        rw [h1, Matrix.one_apply_ne (ne_of_gt hij')]
      rw [Matrix.mul_apply] at hmul
      have hsingle : ∑ k : Fin r, B.val i' k * B⁻¹.val k j' = B.val i' i' * B⁻¹.val i' j' := by
        rw [Finset.sum_eq_single i']
        · intro k _ hki
          rcases lt_or_gt_of_ne hki with hlt | hgt
          · rw [hB hlt, zero_mul]
          · have hk_le : r - k.1 ≤ d := by omega
            have hkj : j' < k := lt_trans hij' hgt
            rw [ih k j' hk_le hkj, mul_zero]
        · intro h; exact absurd (Finset.mem_univ i') h
      rw [hsingle] at hmul
      exact (hdiag i').mul_right_eq_zero.mp hmul
  intro i j hij
  exact hrec (r - i.1) i j le_rfl hij

lemma mul_diag_of_blockTriangular {R : Type*} [CommRing R] {r : ℕ}
    {A B : Matrix (Fin r) (Fin r) R} (hA : A.BlockTriangular id) (hB : B.BlockTriangular id)
    (i : Fin r) : (A * B) i i = A i i * B i i := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · intro k _ hki
    rcases lt_or_gt_of_ne hki with hlt | hgt
    · rw [hA hlt, zero_mul]
    · rw [hB hgt, mul_zero]
  · intro h; exact absurd (Finset.mem_univ i) h

/-- **Concrete Minimal Unitary Parabolic Subgroup `ParabolicSubgroupU`**:
the subgroup of `UnitaryMatrixGroup σ J` stabilizing the complete isotropic Witt flag
`span {X₀} ⊂ span {X₀, X₁} ⊂ ... ⊂ span {X₀, ..., X_{r-1}}` via upper-triangular matrices
with unit diagonal entries. -/
def ParabolicSubgroupU {R : Type*} [CommRing R] (σ : R →+* R) (_hσ : Function.Involutive σ)
    {n r : ℕ} {J : Matrix (Fin n) (Fin n) R} (_hJ : IsHermMatrix σ J)
    {X Y : Matrix (Fin n) (Fin r) R} (_hW : IsWittFrame σ J X Y) :
    Subgroup (UnitaryMatrixGroup σ J) where
  carrier := { g | ∃ B : Matrix.GeneralLinearGroup (Fin r) R,
    B.val.BlockTriangular id ∧ (∀ i : Fin r, IsUnit (B.val i i)) ∧ g.1.val * X = X * B.val }
  one_mem' := by
    refine ⟨1, Matrix.blockTriangular_one, fun i => ?_, by simp⟩
    simp [isUnit_one]
  mul_mem' {g₁ g₂} := by
    rintro ⟨B₁, hT₁, hU₁, hX₁⟩ ⟨B₂, hT₂, hU₂, hX₂⟩
    refine ⟨B₁ * B₂, hT₁.mul hT₂, fun i => ?_, ?_⟩
    · change IsUnit ((B₁.val * B₂.val) i i)
      rw [mul_diag_of_blockTriangular hT₁ hT₂ i]
      exact (hU₁ i).mul (hU₂ i)
    · change (g₁.1.val * g₂.1.val) * X = X * (B₁.val * B₂.val)
      rw [Matrix.mul_assoc, hX₂, ← Matrix.mul_assoc, hX₁, Matrix.mul_assoc]
  inv_mem' {g} := by
    rintro ⟨B, hT, hU, hX⟩
    have hTinv : B⁻¹.val.BlockTriangular id :=
      inv_blockTriangular_of_blockTriangular B hT hU
    refine ⟨B⁻¹, hTinv, fun i => ?_, ?_⟩
    · have h1 : (B.val * B⁻¹.val) i i = 1 := by
        have h : B.val * B⁻¹.val = 1 := congrArg Units.val (mul_inv_cancel B)
        rw [h, Matrix.one_apply_eq]
      rw [mul_diag_of_blockTriangular hT hTinv i] at h1
      exact isUnit_iff_exists_inv.mpr ⟨B.val i i, by rw [mul_comm, h1]⟩
    · have hg : g.1⁻¹.val * g.1.val = 1 := congrArg Units.val (inv_mul_cancel g.1)
      have hB : B.val * B⁻¹.val = 1 := congrArg Units.val (mul_inv_cancel B)
      change g.1⁻¹.val * X = X * B⁻¹.val
      calc g.1⁻¹.val * X
          = g.1⁻¹.val * (X * (B.val * B⁻¹.val)) := by rw [hB, Matrix.mul_one]
        _ = g.1⁻¹.val * ((X * B.val) * B⁻¹.val) := by rw [Matrix.mul_assoc]
        _ = g.1⁻¹.val * ((g.1.val * X) * B⁻¹.val) := by rw [← hX]
        _ = (g.1⁻¹.val * g.1.val) * (X * B⁻¹.val) := by simp only [Matrix.mul_assoc]
        _ = X * B⁻¹.val := by rw [hg, Matrix.one_mul]

namespace ParabolicSubgroupU

variable {R : Type*} [CommRing R] {σ : R →+* R} {hσ : Function.Involutive σ}
  {n r : ℕ} {J : Matrix (Fin n) (Fin n) R} {hJ : IsHermMatrix σ J}
  {X Y : Matrix (Fin n) (Fin r) R} {hW : IsWittFrame σ J X Y}

/-- Canonical upper-triangular Levi/Borel flag matrix `B(p) = Y^* J p X` for `p ∈ ParabolicSubgroupU`. -/
def flagMatrix (p : ParabolicSubgroupU σ hσ hJ hW) : Matrix (Fin r) (Fin r) R :=
  conjTransposeOf σ Y * J * p.1.1.val * X

theorem mul_X_eq_X_mul_flagMatrix (p : ParabolicSubgroupU σ hσ hJ hW) :
    p.1.1.val * X = X * flagMatrix p := by
  obtain ⟨B, -, -, hX⟩ := p.2
  have hB : flagMatrix p = B.val := by
    unfold flagMatrix
    calc conjTransposeOf σ Y * J * p.1.1.val * X
        = (conjTransposeOf σ Y * J) * (p.1.1.val * X) := by simp only [Matrix.mul_assoc]
      _ = (conjTransposeOf σ Y * J) * (X * B.val) := by rw [hX]
      _ = (conjTransposeOf σ Y * J * X) * B.val := by simp only [Matrix.mul_assoc]
      _ = B.val := by rw [hW.yx hσ hJ, Matrix.one_mul]
  rw [hB, hX]

theorem flagMatrix_blockTriangular (p : ParabolicSubgroupU σ hσ hJ hW) :
    (flagMatrix p).BlockTriangular id := by
  obtain ⟨B, hT, -, hX⟩ := p.2
  have hB : flagMatrix p = B.val := by
    unfold flagMatrix
    rw [Matrix.mul_assoc, Matrix.mul_assoc, hX, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      hW.yx hσ hJ, Matrix.one_mul]
  rwa [hB]

theorem isUnit_flagMatrix_diag (p : ParabolicSubgroupU σ hσ hJ hW) (i : Fin r) :
    IsUnit (flagMatrix p i i) := by
  obtain ⟨B, -, hU, hX⟩ := p.2
  have hB : flagMatrix p = B.val := by
    unfold flagMatrix
    rw [Matrix.mul_assoc, Matrix.mul_assoc, hX, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      hW.yx hσ hJ, Matrix.one_mul]
  rw [hB]
  exact hU i

theorem flagMatrix_one :
    flagMatrix (1 : ParabolicSubgroupU σ hσ hJ hW) = 1 := by
  unfold flagMatrix
  change conjTransposeOf σ Y * J * 1 * X = 1
  rw [Matrix.mul_one]
  exact hW.yx hσ hJ

theorem flagMatrix_mul (p q : ParabolicSubgroupU σ hσ hJ hW) :
    flagMatrix (p * q) = flagMatrix p * flagMatrix q := by
  unfold flagMatrix
  change conjTransposeOf σ Y * J * (p.1.1.val * q.1.1.val) * X = _
  calc conjTransposeOf σ Y * J * (p.1.1.val * q.1.1.val) * X
      = (conjTransposeOf σ Y * J * p.1.1.val) * (q.1.1.val * X) := by simp only [Matrix.mul_assoc]
    _ = (conjTransposeOf σ Y * J * p.1.1.val) * (X * flagMatrix q) := by
          rw [mul_X_eq_X_mul_flagMatrix q]
    _ = (conjTransposeOf σ Y * J * p.1.1.val * X) * flagMatrix q := by simp only [Matrix.mul_assoc]
    _ = flagMatrix p * flagMatrix q := rfl

/-- Canonical Levi diagonal character `ParabolicSubgroupU →* (Fin r → Rˣ)`. -/
def leviDiagHom : ParabolicSubgroupU σ hσ hJ hW →* (Fin r → Rˣ) where
  toFun p i := (isUnit_flagMatrix_diag p i).unit
  map_one' := by
    ext i
    change flagMatrix (1 : ParabolicSubgroupU σ hσ hJ hW) i i = 1
    rw [flagMatrix_one, Matrix.one_apply_eq]
  map_mul' p q := by
    ext i
    change flagMatrix (p * q) i i = flagMatrix p i i * flagMatrix q i i
    rw [flagMatrix_mul, mul_diag_of_blockTriangular (flagMatrix_blockTriangular p)
      (flagMatrix_blockTriangular q) i]

/-- **Unipotent Radical** of `ParabolicSubgroupU`: the normal subgroup where the Levi diagonal
acts trivially (`B(p)_{i,i} = 1` for all `i : Fin r`). -/
def unipotentRadical : Subgroup (ParabolicSubgroupU σ hσ hJ hW) :=
  leviDiagHom.ker

instance unipotentRadical_normal : (unipotentRadical (hσ := hσ) (hJ := hJ) (hW := hW)).Normal :=
  MonoidHom.normal_ker _

/-- Norm-one parabolic subgroup `P¹(U)` (generalizing Alpöge's `minParOne`) for any multiplicative
norm `N : Rˣ →* ℝ`: elements `p ∈ ParabolicSubgroupU` with `N (leviDiagHom p i) = 1` for all `i`. -/
def minParOneU (N : Rˣ →* ℝ) : Subgroup (ParabolicSubgroupU σ hσ hJ hW) where
  carrier := { p | ∀ i : Fin r, N (leviDiagHom p i) = 1 }
  one_mem' i := by simp
  mul_mem' {p q} hp hq i := by
    simp only [map_mul, Pi.mul_apply, hp i, hq i, mul_one]
  inv_mem' {p} hp i := by
    simp only [map_inv, Pi.inv_apply, hp i, inv_one]

theorem unipotentRadical_le_minParOneU (N : Rˣ →* ℝ) :
    unipotentRadical (hσ := hσ) (hJ := hJ) (hW := hW) ≤ minParOneU N := by
  intro p hp i
  have h1 : leviDiagHom p = 1 := hp
  rw [h1, Pi.one_apply, map_one]

end ParabolicSubgroupU

/-! ### Explicit Complex Matrix Split Torus `torusMatPos` inside `ParabolicSubgroupU` -/

section ComplexSplitTorus

/-- Explicit split torus matrix in `M_n(ℂ)` attached to a complex Hermitian Witt frame `(X, Y)`:
`a(t) = I + X · diag(t - 1) · (Y^* J) + Y · diag(t⁻¹ - 1) · (X^* J)`.
It scales `X_i ↦ t_i X_i`, `Y_i ↦ t_i⁻¹ Y_i`, and fixes `(X ⊕ Y)^⊥` pointwise. -/
def torusMatPos {n r : ℕ} (J : Matrix (Fin n) (Fin n) ℂ)
    (X Y : Matrix (Fin n) (Fin r) ℂ) (t : Fin r → ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  1 + X * Matrix.diagonal (fun i => ((t i : ℂ) - 1)) * (conjTransposeOf (starRingEnd ℂ) Y * J)
    + Y * Matrix.diagonal (fun i => (((t i)⁻¹ : ℂ) - 1)) * (conjTransposeOf (starRingEnd ℂ) X * J)

lemma torusMatPos_one {n r : ℕ} (J : Matrix (Fin n) (Fin n) ℂ)
    (X Y : Matrix (Fin n) (Fin r) ℂ) :
    torusMatPos J X Y (fun _ => 1) = 1 := by
  simp [torusMatPos]

lemma torusMatPos_mul {n r : ℕ} {J : Matrix (Fin n) (Fin n) ℂ}
    (hJ : IsHermMatrix (starRingEnd ℂ) J)
    {X Y : Matrix (Fin n) (Fin r) ℂ} (hW : IsWittFrame (starRingEnd ℂ) J X Y)
    {t s : Fin r → ℝ} (_ht : ∀ i, t i ≠ 0) (_hs : ∀ i, s i ≠ 0) :
    torusMatPos J X Y t * torusMatPos J X Y s = torusMatPos J X Y (fun i => t i * s i) := by
  have hYX : conjTransposeOf (starRingEnd ℂ) Y * J * X = 1 :=
    hW.yx (star_involutive (R := ℂ)) hJ
  have hXX : conjTransposeOf (starRingEnd ℂ) X * J * X = 0 := hW.xx
  have hYY : conjTransposeOf (starRingEnd ℂ) Y * J * Y = 0 := hW.yy
  have hXY : conjTransposeOf (starRingEnd ℂ) X * J * Y = 1 := hW.xy
  set YJ := conjTransposeOf (starRingEnd ℂ) Y * J
  set XJ := conjTransposeOf (starRingEnd ℂ) X * J
  set Dt := Matrix.diagonal (fun i => ((t i : ℂ) - 1))
  set Ds := Matrix.diagonal (fun i => ((s i : ℂ) - 1))
  set It := Matrix.diagonal (fun i => (((t i)⁻¹ : ℂ) - 1))
  set Is := Matrix.diagonal (fun i => (((s i)⁻¹ : ℂ) - 1))
  have hXX1 : (X * Dt * YJ) * (X * Ds * YJ) = X * (Dt * Ds) * YJ := by
    calc (X * Dt * YJ) * (X * Ds * YJ)
        = X * Dt * (YJ * X) * Ds * YJ := by simp only [Matrix.mul_assoc]
      _ = X * (Dt * Ds) * YJ := by rw [hYX, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  have hXY0 : (X * Dt * YJ) * (Y * Is * XJ) = 0 := by
    calc (X * Dt * YJ) * (Y * Is * XJ)
        = X * Dt * (YJ * Y) * Is * XJ := by simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hYY]; simp
  have hYX0 : (Y * It * XJ) * (X * Ds * YJ) = 0 := by
    calc (Y * It * XJ) * (X * Ds * YJ)
        = Y * It * (XJ * X) * Ds * YJ := by simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hXX]; simp
  have hYY1 : (Y * It * XJ) * (Y * Is * XJ) = Y * (It * Is) * XJ := by
    calc (Y * It * XJ) * (Y * Is * XJ)
        = Y * It * (XJ * Y) * Is * XJ := by simp only [Matrix.mul_assoc]
      _ = Y * (It * Is) * XJ := by rw [hXY, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  have hDsum : Dt + Ds + Dt * Ds = Matrix.diagonal (fun i => (((t i * s i : ℝ) : ℂ) - 1)) := by
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_add, Matrix.diagonal_add]
    congr 1; ext i; push_cast; ring
  have hIsum : It + Is + It * Is =
      Matrix.diagonal (fun i => (((t i * s i : ℝ) : ℂ)⁻¹ - 1)) := by
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_add, Matrix.diagonal_add]
    congr 1; ext i
    rw [Complex.ofReal_mul, mul_inv]
    ring
  unfold torusMatPos
  change (1 + X * Dt * YJ + Y * It * XJ) * (1 + X * Ds * YJ + Y * Is * XJ) =
    1 + X * Matrix.diagonal (fun i => (((t i * s i : ℝ) : ℂ) - 1)) * YJ +
        Y * Matrix.diagonal (fun i => (((t i * s i : ℝ) : ℂ)⁻¹ - 1)) * XJ
  rw [Matrix.add_mul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, Matrix.mul_add,
    Matrix.mul_add, Matrix.mul_add, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.mul_one,
    hXX1, hXY0, hYX0, hYY1, ← hDsum, ← hIsum]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.one_mul, add_zero]
  abel

lemma torusMatPos_conjTranspose_mul_J {n r : ℕ} {J : Matrix (Fin n) (Fin n) ℂ}
    (hJ : IsHermMatrix (starRingEnd ℂ) J)
    (X Y : Matrix (Fin n) (Fin r) ℂ) (t : Fin r → ℝ) :
    conjTransposeOf (starRingEnd ℂ) (torusMatPos J X Y t) * J =
      J * torusMatPos J X Y (fun i => (t i)⁻¹) := by
  have hσ : Function.Involutive (starRingEnd ℂ) := star_involutive (R := ℂ)
  have hD1 : conjTransposeOf (starRingEnd ℂ) (Matrix.diagonal (fun i => ((t i : ℂ) - 1))) =
      Matrix.diagonal (fun i => ((t i : ℂ) - 1)) := by
    rw [conjTransposeOf_diagonal]
    congr 1; ext i; simp
  have hD2 : conjTransposeOf (starRingEnd ℂ) (Matrix.diagonal (fun i => (((t i)⁻¹ : ℂ) - 1))) =
      Matrix.diagonal (fun i => (((t i)⁻¹ : ℂ) - 1)) := by
    rw [conjTransposeOf_diagonal]
    congr 1; ext i; simp
  unfold torusMatPos
  rw [conjTransposeOf_add, conjTransposeOf_add, conjTransposeOf_one,
    conjTransposeOf_mul, conjTransposeOf_mul, conjTransposeOf_mul, conjTransposeOf_mul,
    conjTransposeOf_mul, conjTransposeOf_mul,
    conjTransposeOf_conjTransposeOf _ hσ, conjTransposeOf_conjTransposeOf _ hσ,
    hJ, hD1, hD2, Matrix.add_mul, Matrix.add_mul, Matrix.one_mul,
    Matrix.mul_add, Matrix.mul_add, Matrix.mul_one]
  simp only [Matrix.mul_assoc, Complex.ofReal_inv, inv_inv]
  abel

/-- Every positive-parameter split torus matrix `torusMatPos J X Y t` is unitary (`a(t)^* J a(t) = J`)
and dilates `X` by `t`, `Y` by `t⁻¹`, and fixes `(X ⊕ Y)^⊥`. -/
theorem torusMatPos_unitary_and_action {n r : ℕ} {J : Matrix (Fin n) (Fin n) ℂ}
    (hJ : IsHermMatrix (starRingEnd ℂ) J)
    {X Y : Matrix (Fin n) (Fin r) ℂ} (hW : IsWittFrame (starRingEnd ℂ) J X Y)
    {t : Fin r → ℝ} (ht : ∀ i, t i ≠ 0) :
    conjTransposeOf (starRingEnd ℂ) (torusMatPos J X Y t) * J * torusMatPos J X Y t = J ∧
    torusMatPos J X Y t * X = X * Matrix.diagonal (fun i => (t i : ℂ)) ∧
    torusMatPos J X Y t * Y = Y * Matrix.diagonal (fun i => ((t i)⁻¹ : ℂ)) ∧
    (∀ z : Fin n → ℂ, (conjTransposeOf (starRingEnd ℂ) X * J) *ᵥ z = 0 →
      (conjTransposeOf (starRingEnd ℂ) Y * J) *ᵥ z = 0 →
      torusMatPos J X Y t *ᵥ z = z) := by
  have hYX : conjTransposeOf (starRingEnd ℂ) Y * J * X = 1 :=
    hW.yx (star_involutive (R := ℂ)) hJ
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [torusMatPos_conjTranspose_mul_J hJ X Y t, Matrix.mul_assoc,
      torusMatPos_mul hJ hW (fun i => inv_ne_zero (ht i)) ht]
    have h1 : (fun i => (t i)⁻¹ * t i) = fun _ => 1 := by
      ext i; exact inv_mul_cancel₀ (ht i)
    rw [h1, torusMatPos_one, Matrix.mul_one]
  · unfold torusMatPos
    rw [Matrix.add_mul, Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_assoc,
      hYX, Matrix.mul_one, Matrix.mul_assoc, Matrix.mul_assoc, hW.xx, Matrix.mul_zero,
      Matrix.mul_zero, add_zero]
    have h1 : X + X * Matrix.diagonal (fun i => ((t i : ℂ) - 1)) =
        X * (1 + Matrix.diagonal (fun i => ((t i : ℂ) - 1))) := by rw [Matrix.mul_add, Matrix.mul_one]
    rw [h1]
    congr 1
    ext i j
    simp only [Matrix.add_apply, Matrix.one_apply, Matrix.diagonal_apply]
    split_ifs <;> ring
  · unfold torusMatPos
    rw [Matrix.add_mul, Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_assoc,
      hW.yy, Matrix.mul_zero, Matrix.mul_zero, add_zero, Matrix.mul_assoc, Matrix.mul_assoc,
      hW.xy, Matrix.mul_one]
    have h2 : Y + Y * Matrix.diagonal (fun i => (((t i)⁻¹ : ℂ) - 1)) =
        Y * (1 + Matrix.diagonal (fun i => (((t i)⁻¹ : ℂ) - 1))) := by rw [Matrix.mul_add, Matrix.mul_one]
    rw [h2]
    congr 1
    ext i j
    simp only [Matrix.add_apply, Matrix.one_apply, Matrix.diagonal_apply]
    split_ifs <;> ring
  · intro z hzX hzY
    unfold torusMatPos
    rw [Matrix.add_mulVec, Matrix.add_mulVec, Matrix.one_mulVec,
      ← Matrix.mulVec_mulVec, hzY, Matrix.mulVec_zero, add_zero,
      ← Matrix.mulVec_mulVec, hzX, Matrix.mulVec_zero, add_zero]

/-- Explicit split torus element inside `ParabolicSubgroupU (starRingEnd ℂ) ...` for any
positive parameters `t : Fin r → ℝ` (`∀ i, t i ≠ 0`). -/
def splitTorusElem {n r : ℕ} {J : Matrix (Fin n) (Fin n) ℂ}
    (hJ : IsHermMatrix (starRingEnd ℂ) J)
    {X Y : Matrix (Fin n) (Fin r) ℂ} (hW : IsWittFrame (starRingEnd ℂ) J X Y)
    (t : Fin r → ℝ) (ht : ∀ i, t i ≠ 0) :
    ParabolicSubgroupU (starRingEnd ℂ) (star_involutive (R := ℂ)) hJ hW :=
  let g : Matrix.GeneralLinearGroup (Fin n) ℂ :=
    { val := torusMatPos J X Y t
      inv := torusMatPos J X Y (fun i => (t i)⁻¹)
      val_inv := by
        rw [torusMatPos_mul hJ hW ht (fun i => inv_ne_zero (ht i))]
        have h1 : (fun i => t i * (t i)⁻¹) = fun _ => 1 := by ext i; exact mul_inv_cancel₀ (ht i)
        rw [h1, torusMatPos_one]
      inv_val := by
        rw [torusMatPos_mul hJ hW (fun i => inv_ne_zero (ht i)) ht]
        have h1 : (fun i => (t i)⁻¹ * t i) = fun _ => 1 := by ext i; exact inv_mul_cancel₀ (ht i)
        rw [h1, torusMatPos_one] }
  let u : UnitaryMatrixGroup (starRingEnd ℂ) J :=
    ⟨g, (torusMatPos_unitary_and_action hJ hW ht).1⟩
  let B : Matrix.GeneralLinearGroup (Fin r) ℂ :=
    { val := Matrix.diagonal (fun i => (t i : ℂ))
      inv := Matrix.diagonal (fun i => ((t i)⁻¹ : ℂ))
      val_inv := by
        rw [Matrix.diagonal_mul_diagonal]
        have h1 : (fun i => (t i : ℂ) * ((t i)⁻¹ : ℂ)) = fun _ => 1 := by
          ext i; exact mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr (ht i))
        rw [h1, Matrix.diagonal_one]
      inv_val := by
        rw [Matrix.diagonal_mul_diagonal]
        have h1 : (fun i => ((t i)⁻¹ : ℂ) * (t i : ℂ)) = fun _ => 1 := by
          ext i; exact inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr (ht i))
        rw [h1, Matrix.diagonal_one] }
  ⟨u, B, Matrix.blockTriangular_diagonal _, fun i => by
      simp only [B, Matrix.diagonal_apply_eq]
      exact (Complex.ofReal_ne_zero.mpr (ht i)).isUnit,
    (torusMatPos_unitary_and_action hJ hW ht).2.1⟩

end ComplexSplitTorus

end UnitaryParabolic

/-! ## Section 2: Unitary Siegel Torus Cone, Modulus Character & Exact Cone Integrals -/

section SiegelConeAndModulus

/-- **Unitary Siegel Torus Cone `SiegelCone r c`**:
positive diagonal torus coordinates `t : Fin r → ℝ` satisfying `c * t_{i+1} ≤ t_i` for consecutive
indices and `c ≤ t_{r-1}` (matching `GlobalTheory.SiegelSet.cone`). -/
def SiegelCone (r : ℕ) (c : ℝ) : Set (Fin r → ℝ) :=
  { t | (∀ i : Fin r, 0 < t i) ∧
        (∀ i j : Fin r, j.1 = i.1 + 1 → c * t j ≤ t i) ∧
        (∀ i : Fin r, i.1 + 1 = r → c ≤ t i) }

lemma siegelCone_mono_c {r : ℕ} {c₁ c₂ : ℝ} (hc : c₁ ≤ c₂) :
    SiegelCone r c₂ ⊆ SiegelCone r c₁ := by
  rintro t ⟨hpos, hstep, hlast⟩
  refine ⟨hpos, fun i j hij => le_trans (mul_le_mul_of_nonneg_right hc (hpos j).le) (hstep i j hij),
    fun i hi => le_trans hc (hlast i hi)⟩

/-- Every coordinate `t i` in `SiegelCone r c` (`0 < c`) satisfies `c ^ (r - i) ≤ t i`. -/
theorem siegelCone_coord_ge_pow {r : ℕ} {c : ℝ} (hc : 0 < c) {t : Fin r → ℝ}
    (ht : t ∈ SiegelCone r c) :
    ∀ i : Fin r, c ^ (r - i.1) ≤ t i := by
  have hrec : ∀ d : ℕ, ∀ i : Fin r, r - i.1 = d → c ^ d ≤ t i := by
    intro d
    induction d with
    | zero => intro i hi; omega
    | succ d ih =>
      intro i hi
      by_cases hlast : i.1 + 1 = r
      · have hd0 : d = 0 := by omega
        subst hd0
        simpa using ht.2.2 i hlast
      · let j : Fin r := ⟨i.1 + 1, by omega⟩
        have hj_eq : r - j.1 = d := by dsimp [j]; omega
        have hstep := ht.2.1 i j rfl
        have hih := ih j hj_eq
        calc c ^ (d + 1) = c * c ^ d := by rw [pow_succ']
          _ ≤ c * t j := mul_le_mul_of_nonneg_left hih hc.le
          _ ≤ t i := hstep
  intro i
  exact hrec (r - i.1) i rfl

lemma isClosed_siegelCone {r : ℕ} {c : ℝ} (hc : 0 < c) : IsClosed (SiegelCone r c) := by
  have heq : SiegelCone r c =
      (⋂ i : Fin r, { t : Fin r → ℝ | c ^ (r - i.1) ≤ t i }) ∩
      (⋂ i : Fin r, ⋂ j : Fin r, ⋂ _ : j.1 = i.1 + 1, { t : Fin r → ℝ | c * t j ≤ t i }) ∩
      (⋂ i : Fin r, ⋂ _ : i.1 + 1 = r, { t : Fin r → ℝ | c ≤ t i }) := by
    ext t
    simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq]
    constructor
    · intro ht
      exact ⟨⟨fun i => siegelCone_coord_ge_pow hc ht i, fun i j hij => ht.2.1 i j hij⟩,
        fun i hi => ht.2.2 i hi⟩
    · rintro ⟨⟨hlb, hstep⟩, hlast⟩
      exact ⟨fun i => lt_of_lt_of_le (pow_pos hc _) (hlb i), hstep, hlast⟩
  rw [heq]
  refine ((isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)).inter
    (isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
      isClosed_le (continuous_const.mul (continuous_apply j)) (continuous_apply i))).inter
    (isClosed_iInter fun i => isClosed_iInter fun _ =>
      isClosed_le continuous_const (continuous_apply i))

lemma measurableSet_siegelCone {r : ℕ} {c : ℝ} (hc : 0 < c) : MeasurableSet (SiegelCone r c) :=
  (isClosed_siegelCone hc).measurableSet

/-- **Unitary Parabolic Modulus Character `siegelModulus d m t`**:
for a totally real base field `F` of degree `d = [F : ℚ]`, Hermitian rank `m`, and Witt rank `r`,
`δ_P(a(t)) = ∏_{i < r} t_i^{2 d (m - 2i - 1)}` (matching `GlobalTheory.SiegelSet.modulus`). -/
def siegelModulus (d m : ℕ) {r : ℕ} (t : Fin r → ℝ) : ℝ :=
  ∏ i : Fin r, t i ^ (2 * (d : ℤ) * ((m : ℤ) - 2 * (i.1 : ℤ) - 1))

lemma siegelModulus_pos (d m : ℕ) {r : ℕ} {t : Fin r → ℝ} (ht : ∀ i, 0 < t i) :
    0 < siegelModulus d m t :=
  Finset.prod_pos fun i _ => zpow_pos (ht i) _

lemma siegelModulus_mul (d m : ℕ) {r : ℕ} (t s : Fin r → ℝ) :
    siegelModulus d m (fun i => t i * s i) = siegelModulus d m t * siegelModulus d m s := by
  unfold siegelModulus
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => mul_zpow _ _ _

/-- Exact partial sum identity for the unitary Siegel modulus exponents:
`∑_{i=0}^{k} (2 d n - 2 d (m - 2i - 1)) = 2 d (k + 1) (n + k + 1 - m)`. -/
theorem sum_siegelModulus_exponents (d m n k : ℕ) :
    ∑ i ∈ Finset.range (k + 1),
      ((2 * (d : ℝ)) * (n : ℝ) - (2 * (d : ℝ)) * ((m : ℝ) - 2 * (i : ℝ) - 1)) =
    (2 * (d : ℝ)) * ((k : ℝ) + 1) * ((n : ℝ) + ((k : ℝ) + 1) - (m : ℝ)) := by
  induction k with
  | zero =>
    simp
    ring
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

/-- **Sharp Weil-Range Partial-Sum Negativity Criterion**:
if `0 < d` and `n + (k + 1) < m`, then the `k`-th partial sum of the torus-power + inverse-modulus
exponents is strictly negative! -/
theorem sum_siegelModulus_exponents_neg {d m n k : ℕ} (hd : 0 < d) (h : n + (k + 1) < m) :
    ∑ i ∈ Finset.range (k + 1),
      ((2 * (d : ℝ)) * (n : ℝ) - (2 * (d : ℝ)) * ((m : ℝ) - 2 * (i : ℝ) - 1)) < 0 := by
  rw [sum_siegelModulus_exponents]
  have hd' : (0 : ℝ) < 2 * (d : ℝ) := by positivity
  have hk' : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hdiff : (n : ℝ) + ((k : ℝ) + 1) - (m : ℝ) < 0 := by
    have h1 : (n : ℝ) + ((k : ℝ) + 1) < (m : ℝ) := by exact_mod_cast h
    linarith
  exact mul_neg_of_pos_of_neg (mul_pos hd' hk') hdiff

/-- One-dimensional improper power integral over `[b, ∞)` in `ℝ≥0∞`:
`∫⁻ x ∈ [b, ∞), x^(p - 1) dx = b^p / (-p)` for `0 < b` and `p < 0`. -/
theorem lintegral_Ici_rpow_eq {b p : ℝ} (hb : 0 < b) (hp : p < 0) :
    ∫⁻ x, (Set.Ici b).indicator (fun x => ENNReal.ofReal (x ^ (p - 1))) x =
      ENNReal.ofReal (b ^ p / (-p)) := by
  rw [lintegral_indicator measurableSet_Ici, setLIntegral_congr Ioi_ae_eq_Ici.symm]
  have hlt : p - 1 < -1 := by linarith
  rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_Ioi_rpow_of_lt hlt hb)
    ((ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun x (hx : b < x) =>
      Real.rpow_nonneg (le_of_lt (lt_trans hb hx)) _)), integral_Ioi_rpow_of_lt hlt hb]
  congr 1
  have : p - 1 + 1 = p := by ring
  rw [this, div_neg, neg_div]

lemma mem_siegelCone_cons {m : ℕ} {c x : ℝ} (y : Fin (m + 1) → ℝ) :
    (Fin.cons x y : Fin (m + 2) → ℝ) ∈ SiegelCone (m + 2) c ↔
      (0 < x ∧ c * y 0 ≤ x) ∧ y ∈ SiegelCone (m + 1) c := by
  simp only [SiegelCone, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hpos, hstep, hlast⟩
    refine ⟨⟨by simpa using hpos 0, by simpa using hstep 0 1 (by simp)⟩,
      fun i => by simpa using hpos i.succ,
      fun i j hij => by simpa using hstep i.succ j.succ (by simp [hij]),
      fun i hi => by simpa using hlast i.succ (by simp; omega)⟩
  · rintro ⟨⟨h0, h01⟩, hpos, hstep, hlast⟩
    refine ⟨fun i => Fin.cases (by simpa using h0) (fun i => by simpa using hpos i) i,
      fun i j hij => ?_, fun i hi => ?_⟩
    · induction j using Fin.cases with
      | zero => simp at hij
      | succ j =>
        induction i using Fin.cases with
        | zero =>
          have : j = 0 := Fin.ext (by simpa using hij)
          subst this; simpa using h01
        | succ i => simpa using hstep i j (by simpa using hij)
    · induction i using Fin.cases with
      | zero => simp at hi
      | succ i => simpa using hlast i (by simpa using hi)

lemma mem_siegelCone_one {c x : ℝ} (hc : 0 < c) :
    (fun _ => x : Fin 1 → ℝ) ∈ SiegelCone 1 c ↔ c ≤ x := by
  simp only [SiegelCone, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨_, _, hlast⟩; exact hlast 0 rfl
  · intro h
    refine ⟨fun _ => lt_of_lt_of_le hc h, fun i j hij => ?_, fun _ _ => h⟩
    exact absurd hij (by omega)

/-- **Inductive Siegel-Cone Lebesgue Integral Convergence Theorem (`lintegral_siegelCone_lt_top`)**:
for every `c > 0`, `m : ℕ`, and real exponents `a : ℕ → ℝ` whose partial sums are all strictly
negative (`∀ k ≤ m, ∑_{i ≤ k} a_i < 0`), the multivariable cone integral
`∫⁻ t in SiegelCone (m + 1) c, ∏ i, t i ^ (a i - 1)` is strictly finite (`< ⊤`). -/
theorem lintegral_siegelCone_lt_top {c : ℝ} (hc : 0 < c) : ∀ (m : ℕ) (a : ℕ → ℝ),
    (∀ k ≤ m, ∑ i ∈ Finset.range (k + 1), a i < 0) →
    ∫⁻ t in SiegelCone (m + 1) c,
      ∏ i : Fin (m + 1), ENNReal.ofReal (t i ^ (a i.1 - 1)) < ⊤ := by
  intro m
  induction m with
  | zero =>
    intro a ha
    have ha0 : a 0 < 0 := by simpa using ha 0 le_rfl
    rw [← lintegral_indicator (measurableSet_siegelCone hc)]
    have key := (MeasurePreserving.symm _ (volume_preserving_funUnique (Fin 1) ℝ)).lintegral_comp_emb
      (MeasurableEquiv.funUnique (Fin 1) ℝ).symm.measurableEmbedding
      (fun t : Fin 1 → ℝ => (SiegelCone 1 c).indicator
        (fun t => ∏ i : Fin 1, ENNReal.ofReal (t i ^ (a i.1 - 1))) t)
    refine lt_of_eq_of_lt key.symm ?_
    have hfun : ∀ x : ℝ, (SiegelCone 1 c).indicator
        (fun t => ∏ i : Fin 1, ENNReal.ofReal (t i ^ (a i.1 - 1)))
        ((MeasurableEquiv.funUnique (Fin 1) ℝ).symm x) =
        (Set.Ici c).indicator (fun x => ENNReal.ofReal (x ^ (a 0 - 1))) x := by
      intro x
      have hx : (MeasurableEquiv.funUnique (Fin 1) ℝ).symm x = fun _ => x := by
        funext i; simp [MeasurableEquiv.funUnique_symm_apply]
      rw [hx]
      by_cases h : c ≤ x
      · rw [Set.indicator_of_mem ((mem_siegelCone_one hc).2 h), Set.indicator_of_mem (Set.mem_Ici.2 h)]
        simp
      · rw [Set.indicator_of_notMem (fun h' => h ((mem_siegelCone_one hc).1 h')),
          Set.indicator_of_notMem (fun h' => h (Set.mem_Ici.1 h'))]
    simp_rw [hfun]
    rw [lintegral_Ici_rpow_eq hc ha0]
    exact ENNReal.ofReal_lt_top
  | succ m ih =>
    intro a ha
    rw [← lintegral_indicator (measurableSet_siegelCone hc)]
    have ha0 : a 0 < 0 := by simpa using ha 0 (Nat.zero_le _)
    let a' : ℕ → ℝ := fun i => if i = 0 then a 0 + a 1 else a (i + 1)
    have hsum : ∀ k ≤ m, ∑ i ∈ Finset.range (k + 1), a' i < 0 := by
      intro k hk
      have h := ha (k + 1) (by omega)
      rw [Finset.sum_range_succ', Finset.sum_range_succ'] at h
      rw [Finset.sum_range_succ']
      simp only [a', if_pos, Nat.add_eq_zero_iff, one_ne_zero, and_false, if_false] at *
      linarith
    set K : ℝ≥0∞ := ENNReal.ofReal (c ^ a 0 / (-a 0))
    set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 2) => ℝ) 0
    rw [← (MeasurePreserving.symm _
      (volume_preserving_piFinSuccAbove (fun _ : Fin (m + 2) => ℝ) 0)).lintegral_comp_emb
      e.symm.measurableEmbedding, Measure.volume_eq_prod, ← lintegral_prod_swap]
    refine lt_of_le_of_lt (lintegral_prod_le _) ?_
    have hpt : ∀ y : Fin (m + 1) → ℝ, ∫⁻ x, (SiegelCone (m + 2) c).indicator
        (fun t => ∏ i : Fin (m + 2), ENNReal.ofReal (t i ^ (a i.1 - 1))) (e.symm (Prod.swap (y, x)))
        ≤ K * (SiegelCone (m + 1) c).indicator
          (fun t => ∏ i : Fin (m + 1), ENNReal.ofReal (t i ^ (a' i.1 - 1))) y := by
      intro y
      have he : ∀ x, e.symm (Prod.swap (y, x)) = Fin.cons x y := by
        intro x
        ext i
        refine Fin.cases ?_ (fun j => ?_) i
        · simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply]
        · simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply]
      simp_rw [he]
      by_cases hy : y ∈ SiegelCone (m + 1) c
      · have hy0 : 0 < y 0 := hy.1 0
        have hb : 0 < c * y 0 := mul_pos hc hy0
        set T : ℝ≥0∞ := ∏ i : Fin (m + 1), ENNReal.ofReal (y i ^ (a (i.1 + 1) - 1))
        have hfun : ∀ x, (SiegelCone (m + 2) c).indicator
            (fun t => ∏ i : Fin (m + 2), ENNReal.ofReal (t i ^ (a i.1 - 1))) (Fin.cons x y) =
            (Set.Ici (c * y 0)).indicator (fun x => ENNReal.ofReal (x ^ (a 0 - 1))) x * T := by
          intro x
          by_cases hx : c * y 0 ≤ x
          · rw [Set.indicator_of_mem ((mem_siegelCone_cons y).2 ⟨⟨lt_of_lt_of_le hb hx, hx⟩, hy⟩),
              Set.indicator_of_mem (Set.mem_Ici.2 hx), Fin.prod_univ_succ]
            simp [T, Fin.val_succ]
          · rw [Set.indicator_of_notMem (fun h' => hx ((mem_siegelCone_cons y).1 h').1.2),
              Set.indicator_of_notMem (fun h' => hx (Set.mem_Ici.1 h')), zero_mul]
        simp_rw [hfun]
        rw [lintegral_mul_const' _ _ (ENNReal.prod_lt_top (fun _ _ => ENNReal.ofReal_lt_top)).ne,
          lintegral_Ici_rpow_eq hb ha0, Set.indicator_of_mem hy]
        have hsplit : ENNReal.ofReal ((c * y 0) ^ a 0 / (-a 0)) =
            K * ENNReal.ofReal (y 0 ^ a 0) := by
          rw [Real.mul_rpow hc.le hy0.le, mul_div_right_comm,
            ENNReal.ofReal_mul (div_nonneg (Real.rpow_nonneg hc.le _) (by linarith))]
        rw [hsplit, mul_assoc]
        refine le_of_eq (congrArg (K * ·) ?_)
        rw [Fin.prod_univ_succ, Fin.prod_univ_succ, ← mul_assoc]
        congr 1
        rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hy0.le _), ← Real.rpow_add hy0]
        congr 2; simp only [a', Fin.val_zero, ↓reduceIte]; ring
      · have hzero : ∀ x, (SiegelCone (m + 2) c).indicator
            (fun t => ∏ i : Fin (m + 2), ENNReal.ofReal (t i ^ (a i.1 - 1))) (Fin.cons x y) = 0 := by
          intro x
          exact Set.indicator_of_notMem (fun h' => hy ((mem_siegelCone_cons y).1 h').2) _
        simp [hzero]
    calc ∫⁻ y, ∫⁻ x, (SiegelCone (m + 2) c).indicator
            (fun t => ∏ i : Fin (m + 2), ENNReal.ofReal (t i ^ (a i.1 - 1))) (e.symm (Prod.swap (y, x)))
        ≤ ∫⁻ y, K * (SiegelCone (m + 1) c).indicator
            (fun t => ∏ i : Fin (m + 1), ENNReal.ofReal (t i ^ (a' i.1 - 1))) y :=
          lintegral_mono hpt
      _ = K * ∫⁻ y, (SiegelCone (m + 1) c).indicator
            (fun t => ∏ i : Fin (m + 1), ENNReal.ofReal (t i ^ (a' i.1 - 1))) y :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ = K * ∫⁻ y in SiegelCone (m + 1) c,
            ∏ i : Fin (m + 1), ENNReal.ofReal (y i ^ (a' i.1 - 1)) := by
          rw [lintegral_indicator (measurableSet_siegelCone hc)]
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ih a' hsum)

/-- Helper rewriting `ENNReal.ofReal (∏ t_i^{2dn}) * ENNReal.ofReal ((siegelModulus d m t * ∏ t_i)⁻¹)`
into product-of-powers form on `SiegelCone r c`. -/
lemma siegelModulus_integrand_eq (d m n : ℕ) {r : ℕ} {t : Fin r → ℝ} (ht : ∀ i, 0 < t i) :
    ENNReal.ofReal (∏ i : Fin r, t i ^ (d * (2 * n))) *
      ENNReal.ofReal ((siegelModulus d m t * ∏ i : Fin r, t i)⁻¹) =
    ∏ i : Fin r, ENNReal.ofReal
      (t i ^ ((2 * (d : ℝ)) * (n : ℝ) - (2 * (d : ℝ)) * ((m : ℝ) - 2 * (i.1 : ℝ) - 1) - 1)) := by
  have h1 : 0 ≤ ∏ i : Fin r, t i ^ (d * (2 * n)) :=
    Finset.prod_nonneg fun i _ => pow_nonneg (ht i).le _
  rw [← ENNReal.ofReal_mul h1, ← ENNReal.ofReal_prod_of_nonneg (fun i _ => Real.rpow_nonneg (ht i).le _)]
  congr 1
  unfold siegelModulus
  rw [mul_inv, ← Finset.prod_inv_distrib, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  have hti : 0 < t i := ht i
  rw [← Real.rpow_natCast, ← Real.rpow_intCast, ← Real.rpow_neg hti.le,
    ← Real.rpow_neg_one (t i), ← Real.rpow_add hti, ← Real.rpow_add hti]
  congr 1
  push_cast
  ring

/-- **Unconditional Weil-Range Siegel-Cone Integrability (`lintegral_siegelCone_weil_range_lt_top`)**:
for EVERY totally real degree `d ≥ 1`, cutoff `c > 0`, Hermitian rank `m`, Witt index `r`, and
dual-pair rank `n` satisfying `r = 0 ∨ n + r < m` (Weil's convergent range!), the modulus-weighted
torus-power integral over `SiegelCone r c` is strictly finite (`< ⊤`). -/
theorem lintegral_siegelCone_weil_range_lt_top {d m r n : ℕ} {c : ℝ}
    (hd : 0 < d) (hc : 0 < c) (hweil : r = 0 ∨ n + r < m) :
    ∫⁻ t in SiegelCone r c,
      ENNReal.ofReal (∏ i : Fin r, t i ^ (d * (2 * n))) *
        ENNReal.ofReal ((siegelModulus d m t * ∏ i : Fin r, t i)⁻¹) < ⊤ := by
  cases r with
  | zero =>
    simp only [siegelModulus, Finset.univ_eq_empty, Finset.prod_empty, mul_one, inv_one,
      ENNReal.ofReal_one, lintegral_const, one_mul, Measure.restrict_apply_univ]
    exact lt_of_le_of_lt (measure_mono (Set.subset_univ _)) (by
      change Measure.pi (fun _ : Fin 0 => (volume : Measure ℝ)) Set.univ < ⊤
      rw [Measure.pi_of_empty]
      exact measure_lt_top _ _)
  | succ r' =>
    have hlt : n + (r' + 1) < m := hweil.resolve_left (Nat.succ_ne_zero r')
    let a : ℕ → ℝ := fun i =>
      (2 * (d : ℝ)) * (n : ℝ) - (2 * (d : ℝ)) * ((m : ℝ) - 2 * (i : ℝ) - 1)
    have hneg : ∀ k ≤ r', ∑ i ∈ Finset.range (k + 1), a i < 0 := fun k hk =>
      sum_siegelModulus_exponents_neg hd (by omega)
    have hcongr : ∫⁻ t in SiegelCone (r' + 1) c,
        ENNReal.ofReal (∏ i : Fin (r' + 1), t i ^ (d * (2 * n))) *
          ENNReal.ofReal ((siegelModulus d m t * ∏ i : Fin (r' + 1), t i)⁻¹) =
        ∫⁻ t in SiegelCone (r' + 1) c,
          ∏ i : Fin (r' + 1), ENNReal.ofReal (t i ^ (a i.1 - 1)) := by
      refine setLIntegral_congr_fun (measurableSet_siegelCone hc) fun t ht => ?_
      exact siegelModulus_integrand_eq d m n ht.1
    rw [hcongr]
    exact lintegral_siegelCone_lt_top hc r' a hneg

/-- **Unconditional Finite Volume of the Unitary Siegel Cone (`lintegral_siegelCone_inv_modulus_lt_top`)**:
for EVERY `d ≥ 1`, `c > 0`, and ANY Witt frame (`2 * r ≤ m`), the inverse-modulus volume integral
`∫⁻ t in SiegelCone r c, (siegelModulus d m t * ∏ i, t i)⁻¹` is strictly finite (`< ⊤`). -/
theorem lintegral_siegelCone_inv_modulus_lt_top {d m r : ℕ} {c : ℝ}
    (hd : 0 < d) (hc : 0 < c) (hr : 2 * r ≤ m) :
    ∫⁻ t in SiegelCone r c,
      ENNReal.ofReal ((siegelModulus d m t * ∏ i : Fin r, t i)⁻¹) < ⊤ := by
  have hweil : r = 0 ∨ 0 + r < m := by
    by_cases h0 : r = 0
    · exact Or.inl h0
    · exact Or.inr (by omega)
  have h := lintegral_siegelCone_weil_range_lt_top (d := d) (m := m) (r := r) (n := 0) hd hc hweil
  simpa using h

/-- Specialization of `lintegral_siegelCone_weil_range_lt_top` to any `SiegelWeilCore.DualPairRanks`
in `WeilConvergentRange`. -/
theorem lintegral_siegelCone_of_dualPairRanks {P : RHDirect.SiegelWeilCore.DualPairRanks}
    (hW : P.WeilConvergentRange) {d : ℕ} {c : ℝ} (hd : 0 < d) (hc : 0 < c) :
    ∫⁻ t in SiegelCone P.r c,
      ENNReal.ofReal (∏ i : Fin P.r, t i ^ (d * (2 * P.n))) *
        ENNReal.ofReal ((siegelModulus d P.m t * ∏ i : Fin P.r, t i)⁻¹) < ⊤ :=
  lintegral_siegelCone_weil_range_lt_top hd hc (Or.inr hW.2.2)

/-- **Exponential-Decay Parabolic-Slice Summability (`tsum_parabolic_slice_exp_lt_top`)**:
for every `α > 0` and lower threshold `j₀ : ℤ`, the geometric slice sum
`∑'_{j ≥ j₀} exp(-α j)` is strictly finite in `ℝ≥0∞` (directly matching
`HyperbolicParabolicSiegelSetBound`). -/
theorem tsum_parabolic_slice_exp_lt_top {α : ℝ} (hα : 0 < α) (j₀ : ℤ) :
    ∑' k : ℕ, ENNReal.ofReal (Real.exp (-α * ((j₀ + (k : ℤ) : ℤ) : ℝ))) < ⊤ := by
  have hr_lt : Real.exp (-α) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hr_nn : 0 ≤ Real.exp (-α) := (Real.exp_pos _).le
  have hsumm : Summable (fun k : ℕ => Real.exp (-α * (j₀ : ℝ)) * (Real.exp (-α)) ^ k) :=
    (summable_geometric_of_lt_one hr_nn hr_lt).mul_left _
  have hterm : ∀ k : ℕ,
      Real.exp (-α * ((j₀ + (k : ℤ) : ℤ) : ℝ)) =
        Real.exp (-α * (j₀ : ℝ)) * (Real.exp (-α)) ^ k := by
    intro k
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1; push_cast; ring
  simp_rw [hterm]
  rw [← ENNReal.ofReal_tsum_of_nonneg
    (fun k => mul_nonneg (Real.exp_pos _).le (pow_nonneg hr_nn k)) hsumm]
  exact ENNReal.ofReal_lt_top

end SiegelConeAndModulus

/-! ## Section 3: Concrete `SiegelSetU`, `UnitaryIwasawaData` & `UnitaryHeightFn` -/

section SiegelSetAndHeight

/-- **Concrete Unitary Siegel Set `SiegelSetU a Ω c K`**:
the subset `{p * a t * k | p ∈ Ω, t ∈ SiegelCone r c, k ∈ K}` of a group `G` attached to a split
torus map `a : (Fin r → ℝ) → G`, a compact parabolic base `Ω ⊆ P¹`, cone parameter `c > 0`, and
maximal compact subgroup `K`. -/
def SiegelSetU {G : Type*} [Mul G] {r : ℕ} (a : (Fin r → ℝ) → G)
    (Ω : Set G) (c : ℝ) (K : Set G) : Set G :=
  { g | ∃ p ∈ Ω, ∃ t ∈ SiegelCone r c, ∃ k ∈ K, g = p * a t * k }

lemma mem_siegelSetU_iff {G : Type*} [Mul G] {r : ℕ} (a : (Fin r → ℝ) → G)
    (Ω : Set G) (c : ℝ) (K : Set G) (g : G) :
    g ∈ SiegelSetU a Ω c K ↔ ∃ p ∈ Ω, ∃ t ∈ SiegelCone r c, ∃ k ∈ K, g = p * a t * k :=
  Iff.rfl

lemma siegelSetU_mono {G : Type*} [Mul G] {r : ℕ} (a : (Fin r → ℝ) → G)
    {Ω₁ Ω₂ K₁ K₂ : Set G} {c₁ c₂ : ℝ}
    (hΩ : Ω₁ ⊆ Ω₂) (hc : c₂ ≤ c₁) (hK : K₁ ⊆ K₂) :
    SiegelSetU a Ω₁ c₁ K₁ ⊆ SiegelSetU a Ω₂ c₂ K₂ := by
  rintro g ⟨p, hp, t, ht, k, hk, rfl⟩
  exact ⟨p, hΩ hp, t, siegelCone_mono_c hc ht, k, hK hk, rfl⟩

/-- **Compact Conjugation Factorization on `SiegelSetU`** (`a⁻¹ p a ∈ C₀`):
rewrites every `g = p * a t * k ∈ SiegelSetU` as `a t * ((a t)⁻¹ * p * a t * k)` with the
right factor in `C₀ * K` (matching `WeilThetaConvergenceOfSiegelSet.lean`). -/
theorem siegelSetU_conj_compact {G : Type*} [Group G] {r : ℕ} (a : (Fin r → ℝ) → G)
    {Ω C₀ K : Set G} {c : ℝ}
    (hconj : ∀ p ∈ Ω, ∀ t ∈ SiegelCone r c, (a t)⁻¹ * p * a t ∈ C₀)
    {g : G} (hg : g ∈ SiegelSetU a Ω c K) :
    ∃ t ∈ SiegelCone r c, ∃ y ∈ C₀ * K, g = a t * y := by
  rcases hg with ⟨p, hp, t, ht, k, hk, rfl⟩
  refine ⟨t, ht, (a t)⁻¹ * p * a t * k, Set.mul_mem_mul (hconj p hp t ht) hk, ?_⟩
  group

/-- **Concrete Unitary Iwasawa Disintegration Data (`UnitaryIwasawaData`)**:
packages a measurable group `G` with left-invariant Haar measure `μ`, rank/degree data `(d, m, r)`
(`0 < d`, `2 * r ≤ m`), torus map `a`, parabolic/compact sets `(Ω, K)`, cutoff `c > 0`, and the
Iwasawa `P A K` Haar disintegration ceiling on `SiegelSetU a Ω c K`. -/
structure UnitaryIwasawaData (G : Type*) [Group G] [MeasurableSpace G] where
  d : ℕ
  m : ℕ
  r : ℕ
  hd : 0 < d
  hr : 2 * r ≤ m
  a : (Fin r → ℝ) → G
  Ω : Set G
  K : Set G
  c : ℝ
  hc : 0 < c
  siegel_meas : MeasurableSet (SiegelSetU a Ω c K)
  μ : Measure G
  C_haar : ℝ≥0
  disint_le : ∀ (f : G → ℝ≥0∞) (h : (Fin r → ℝ) → ℝ≥0∞), Measurable h →
    (∀ p ∈ Ω, ∀ t ∈ SiegelCone r c, ∀ k ∈ K, f (p * a t * k) ≤ h t) →
    ∫⁻ g in SiegelSetU a Ω c K, f g ∂μ ≤
      (C_haar : ℝ≥0∞) * ∫⁻ t in SiegelCone r c,
        h t * ENNReal.ofReal ((siegelModulus d m t * ∏ i : Fin r, t i)⁻¹)

/-- **Concrete Modulus-Weighted Iwasawa Cone Measure** on `SiegelCone r c ⊆ (Fin r → ℝ)`,
which is unconditionally finite (`IsFiniteMeasure`) whenever `0 < d`, `0 < c`, and `2 * r ≤ m`,
proving the Iwasawa disintegration bound from first principles via Tonelli's theorem with explicit
constant `C_haar = μP Ω * μK K₀`! -/
def iwasawaConeMeasure (d m r : ℕ) (c : ℝ) : Measure (Fin r → ℝ) :=
  ((volume : Measure (Fin r → ℝ)).restrict (SiegelCone r c)).withDensity fun t =>
    ENNReal.ofReal ((siegelModulus d m t * ∏ i : Fin r, t i)⁻¹)

theorem iwasawa_product_disintegration {P K : Type*} [MeasurableSpace P] [MeasurableSpace K]
    (μP : Measure P) (μK : Measure K) [SigmaFinite μP] [SigmaFinite μK]
    (d m r : ℕ) (hd : 0 < d) (hr : 2 * r ≤ m) (c : ℝ) (hc : 0 < c)
    (Ω : Set P) (hΩ : MeasurableSet Ω)
    (K₀ : Set K) (hK₀ : MeasurableSet K₀)
    (f : (P × (Fin r → ℝ)) × K → ℝ≥0∞)
    (h : (Fin r → ℝ) → ℝ≥0∞) (hh : Measurable h)
    (hb : ∀ p ∈ Ω, ∀ t ∈ SiegelCone r c, ∀ k ∈ K₀, f ((p, t), k) ≤ h t) :
    ∫⁻ x in (Ω ×ˢ SiegelCone r c) ×ˢ K₀, f x ∂((μP.prod (iwasawaConeMeasure d m r c)).prod μK) ≤
      (μP Ω * μK K₀) * ∫⁻ t in SiegelCone r c,
        h t * ENNReal.ofReal ((siegelModulus d m t * ∏ i : Fin r, t i)⁻¹) := by
  let ν : Measure (Fin r → ℝ) := iwasawaConeMeasure d m r c
  have hν_fin : ν Set.univ < ⊤ := by
    unfold ν iwasawaConeMeasure
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    exact lintegral_siegelCone_inv_modulus_lt_top hd hc hr
  have : IsFiniteMeasure ν := ⟨hν_fin⟩
  have hset : MeasurableSet ((Ω ×ˢ SiegelCone r c) ×ˢ K₀) :=
    (hΩ.prod (measurableSet_siegelCone hc)).prod hK₀
  have hmono : ∫⁻ x in (Ω ×ˢ SiegelCone r c) ×ˢ K₀, f x ∂((μP.prod ν).prod μK) ≤
      ∫⁻ x in (Ω ×ˢ SiegelCone r c) ×ˢ K₀, h x.1.2 ∂((μP.prod ν).prod μK) := by
    refine setLIntegral_mono' hset fun x hx => ?_
    exact hb x.1.1 hx.1.1 x.1.2 hx.1.2 x.2 hx.2
  have hprod_eval :
      ∫⁻ x in (Ω ×ˢ SiegelCone r c) ×ˢ K₀, h x.1.2 ∂((μP.prod ν).prod μK) =
      (μP Ω * μK K₀) * ∫⁻ t in SiegelCone r c, h t ∂ν := by
    rw [← Measure.prod_restrict (Ω ×ˢ SiegelCone r c) K₀, ← Measure.prod_restrict Ω (SiegelCone r c)]
    rw [lintegral_prod (fun x : (P × (Fin r → ℝ)) × K => h x.1.2)
      (hh.comp (measurable_snd.comp measurable_fst)).aemeasurable]
    simp_rw [lintegral_const, Measure.restrict_apply_univ]
    rw [lintegral_mul_const (f := fun x : P × (Fin r → ℝ) => h x.2) (μK K₀)
      (hh.comp measurable_snd)]
    rw [lintegral_prod (fun x : P × (Fin r → ℝ) => h x.2) (hh.comp measurable_snd).aemeasurable]
    simp_rw [lintegral_const, Measure.restrict_apply_univ]
    ring
  have hdens : ∫⁻ t in SiegelCone r c, h t ∂ν =
      ∫⁻ t in SiegelCone r c,
        h t * ENNReal.ofReal ((siegelModulus d m t * ∏ i : Fin r, t i)⁻¹) := by
    unfold ν iwasawaConeMeasure
    have hmeas_w : Measurable (fun t : Fin r → ℝ =>
        ENNReal.ofReal ((siegelModulus d m t * ∏ i : Fin r, t i)⁻¹)) := by
      refine ENNReal.measurable_ofReal.comp (Measurable.inv (Measurable.mul ?_ ?_))
      · unfold siegelModulus
        exact Finset.measurable_prod _ fun i _ => (measurable_pi_apply i).pow_const _
      · exact Finset.measurable_prod _ fun i _ => measurable_pi_apply i
    rw [setLIntegral_withDensity_eq_setLIntegral_mul _ hmeas_w hh (measurableSet_siegelCone hc),
      Measure.restrict_restrict (measurableSet_siegelCone hc), Set.inter_self]
    refine setLIntegral_congr_fun (measurableSet_siegelCone hc) fun t _ => mul_comm _ _
  calc ∫⁻ x in (Ω ×ˢ SiegelCone r c) ×ˢ K₀, f x ∂((μP.prod ν).prod μK)
      ≤ ∫⁻ x in (Ω ×ˢ SiegelCone r c) ×ˢ K₀, h x.1.2 ∂((μP.prod ν).prod μK) := hmono
    _ = (μP Ω * μK K₀) * ∫⁻ t in SiegelCone r c, h t ∂ν := hprod_eval
    _ = (μP Ω * μK K₀) * ∫⁻ t in SiegelCone r c,
          h t * ENNReal.ofReal ((siegelModulus d m t * ∏ i : Fin r, t i)⁻¹) := by rw [hdens]

/-- **Concrete Unitary Height Function (`UnitaryHeightFn G`)**:
a height function `H : G → ℝ` bounded below by `1`, submultiplicative up to a constant `C_mul`,
and with polynomial inverse bound `H(g⁻¹) ≤ C_inv * H(g)^A_inv`. -/
structure UnitaryHeightFn (G : Type*) [Group G] where
  toFun : G → ℝ
  one_le : ∀ g : G, 1 ≤ toFun g
  C_mul : ℝ
  C_mul_pos : 0 < C_mul
  mul_le : ∀ g₁ g₂ : G, toFun (g₁ * g₂) ≤ C_mul * toFun g₁ * toFun g₂
  C_inv : ℝ
  A_inv : ℕ
  C_inv_pos : 0 < C_inv
  inv_le : ∀ g : G, toFun g⁻¹ ≤ C_inv * (toFun g) ^ A_inv

instance {G : Type*} [Group G] : CoeFun (UnitaryHeightFn G) (fun _ => G → ℝ) :=
  ⟨UnitaryHeightFn.toFun⟩

lemma UnitaryHeightFn.pos {G : Type*} [Group G] (H : UnitaryHeightFn G) (g : G) :
    0 < H g := lt_of_lt_of_le zero_lt_one (H.one_le g)

lemma UnitaryHeightFn.nonneg {G : Type*} [Group G] (H : UnitaryHeightFn G) (g : G) :
    0 ≤ H g := (H.pos g).le

/-- Frobenius norm `‖A‖_F = √(∑ i j, ‖A i j‖²)` of a complex matrix `A : Matrix (Fin n) (Fin n) ℂ`. -/
def frobNorm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  Real.sqrt (∑ i : Fin n, ∑ j : Fin n, ‖A i j‖ ^ 2)

lemma frobNorm_nonneg {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ frobNorm A :=
  Real.sqrt_nonneg _

lemma frobNorm_sq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    frobNorm A ^ 2 = ∑ i : Fin n, ∑ j : Fin n, ‖A i j‖ ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)

/-- Submultiplicativity of the complex Frobenius norm: `‖A * B‖_F ≤ ‖A‖_F * ‖B‖_F`. -/
theorem frobNorm_mul_le {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) :
    frobNorm (A * B) ≤ frobNorm A * frobNorm B := by
  have hsq : frobNorm (A * B) ^ 2 ≤ (frobNorm A * frobNorm B) ^ 2 := by
    rw [mul_pow, frobNorm_sq, frobNorm_sq, frobNorm_sq]
    have hcs : ∀ i j : Fin n,
        ‖(A * B) i j‖ ^ 2 ≤ (∑ k : Fin n, ‖A i k‖ ^ 2) * (∑ k : Fin n, ‖B k j‖ ^ 2) := by
      intro i j
      have htri : ‖(A * B) i j‖ ≤ ∑ k : Fin n, ‖A i k‖ * ‖B k j‖ := by
        rw [Matrix.mul_apply]
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => by rw [norm_mul])
      have hsq1 : ‖(A * B) i j‖ ^ 2 ≤ (∑ k : Fin n, ‖A i k‖ * ‖B k j‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) htri 2
      exact hsq1.trans (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
        (fun k => ‖A i k‖) (fun k => ‖B k j‖))
    calc ∑ i : Fin n, ∑ j : Fin n, ‖(A * B) i j‖ ^ 2
        ≤ ∑ i : Fin n, ∑ j : Fin n,
            (∑ k : Fin n, ‖A i k‖ ^ 2) * (∑ k : Fin n, ‖B k j‖ ^ 2) :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hcs i j
      _ = (∑ i : Fin n, ∑ k : Fin n, ‖A i k‖ ^ 2) * (∑ j : Fin n, ∑ k : Fin n, ‖B k j‖ ^ 2) := by
          simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
      _ = (∑ i : Fin n, ∑ k : Fin n, ‖A i k‖ ^ 2) * (∑ k : Fin n, ∑ j : Fin n, ‖B k j‖ ^ 2) := by
          congr 1; exact Finset.sum_comm
  nlinarith [frobNorm_nonneg (A * B), mul_nonneg (frobNorm_nonneg A) (frobNorm_nonneg B)]

/-- **Concrete Matrix Unitary Height Function (`matrixHeightFn`)**:
`H(g) = max 1 (max ‖g‖_F ‖g⁻¹‖_F)` on `UnitaryMatrixGroup (starRingEnd ℂ) J`, satisfying
`1 ≤ H g`, `H (g₁ * g₂) ≤ H g₁ * H g₂` (`C_mul = 1`), and `H g⁻¹ = H g` (`C_inv = 1, A_inv = 1`)! -/
def matrixHeightFn {n : ℕ} (J : Matrix (Fin n) (Fin n) ℂ) :
    UnitaryHeightFn (UnitaryMatrixGroup (starRingEnd ℂ) J) where
  toFun g := max 1 (max (frobNorm g.1.val) (frobNorm g.1⁻¹.val))
  one_le _ := le_max_left _ _
  C_mul := 1
  C_mul_pos := zero_lt_one
  mul_le g₁ g₂ := by
    rw [one_mul]
    have h1 : 1 ≤ max 1 (max (frobNorm g₁.1.val) (frobNorm g₁.1⁻¹.val)) := le_max_left _ _
    have h2 : 1 ≤ max 1 (max (frobNorm g₂.1.val) (frobNorm g₂.1⁻¹.val)) := le_max_left _ _
    refine max_le (by nlinarith) (max_le ?_ ?_)
    · change frobNorm (g₁.1.val * g₂.1.val) ≤ _
      exact (frobNorm_mul_le _ _).trans (mul_le_mul
        ((le_max_left _ _).trans (le_max_right _ _))
        ((le_max_left _ _).trans (le_max_right _ _))
        (frobNorm_nonneg _) (le_trans zero_le_one h1))
    · change frobNorm (g₂.1⁻¹.val * g₁.1⁻¹.val) ≤ _
      calc frobNorm (g₂.1⁻¹.val * g₁.1⁻¹.val)
          ≤ frobNorm g₂.1⁻¹.val * frobNorm g₁.1⁻¹.val := frobNorm_mul_le _ _
        _ = frobNorm g₁.1⁻¹.val * frobNorm g₂.1⁻¹.val := mul_comm _ _
        _ ≤ _ := mul_le_mul
            ((le_max_right _ _).trans (le_max_right _ _))
            ((le_max_right _ _).trans (le_max_right _ _))
            (frobNorm_nonneg _) (le_trans zero_le_one h1)
  C_inv := 1
  A_inv := 1
  C_inv_pos := zero_lt_one
  inv_le g := by
    simp only [one_mul, pow_one]
    change max 1 (max (frobNorm g.1⁻¹.val) (frobNorm g.1.val)) ≤
      max 1 (max (frobNorm g.1.val) (frobNorm g.1⁻¹.val))
    rw [max_comm (frobNorm g.1⁻¹.val) (frobNorm g.1.val)]

/-- Lattice first-minimum height `max 1 (lambda1 L)⁻¹` (bridging to `Stage2SiegelReduction` &
`Stage3ThetaSiegelBridge`). -/
def latticeHeight {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (L : Submodule ℤ E) : ℝ :=
  max (1 : ℝ) (RHDirect.Stage2SiegelReduction.lambda1 L)⁻¹

lemma one_le_latticeHeight {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (L : Submodule ℤ E) : 1 ≤ latticeHeight L :=
  le_max_left _ _

/-- **Torus-Cone Polynomial Height Bound**:
if `H` is a `UnitaryHeightFn` bounded by `M` on `Ω` and `K`, and on the split torus satisfies
`H (a t) ≤ C_a * (∏ i, t i)^N_a` on `SiegelCone r c`, then every `g = p * a t * k ∈ SiegelSetU`
has height bounded polynomially in `∏ i, t i`. -/
theorem unitaryHeightFn_siegelSet_le {G : Type*} [Group G] (H : UnitaryHeightFn G)
    {r : ℕ} (a : (Fin r → ℝ) → G) {Ω K : Set G} {c M C_a : ℝ} {N_a : ℕ}
    (hM : 0 ≤ M) (hCa : 0 ≤ C_a)
    (hΩ : ∀ p ∈ Ω, H p ≤ M) (hK : ∀ k ∈ K, H k ≤ M)
    (ha : ∀ t ∈ SiegelCone r c, H (a t) ≤ C_a * (∏ i : Fin r, t i) ^ N_a)
    {p k : G} {t : Fin r → ℝ} (hp : p ∈ Ω) (ht : t ∈ SiegelCone r c) (hk : k ∈ K) :
    H (p * a t * k) ≤ H.C_mul ^ 2 * M ^ 2 * C_a * (∏ i : Fin r, t i) ^ N_a := by
  have h1 := H.mul_le (p * a t) k
  have h2 := H.mul_le p (a t)
  have hC0 : 0 ≤ H.C_mul := H.C_mul_pos.le
  have hprod0 : 0 ≤ (∏ i : Fin r, t i) ^ N_a :=
    pow_nonneg (Finset.prod_nonneg fun i _ => (ht.1 i).le) N_a
  calc H (p * a t * k)
      ≤ H.C_mul * H (p * a t) * H k := h1
    _ ≤ H.C_mul * (H.C_mul * H p * H (a t)) * H k := by
        gcongr; exact H.nonneg k
    _ ≤ H.C_mul * (H.C_mul * M * (C_a * (∏ i : Fin r, t i) ^ N_a)) * M := by
        have hHp := hΩ p hp
        have hHa := ha t ht
        have hHk := hK k hk
        have h3 : H.C_mul * H p * H (a t) ≤ H.C_mul * M * (C_a * (∏ i : Fin r, t i) ^ N_a) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hHp hC0) hHa (H.nonneg _) (mul_nonneg hC0 hM)
        exact mul_le_mul (mul_le_mul_of_nonneg_left h3 hC0) hHk (H.nonneg _)
          (mul_nonneg hC0 (mul_nonneg (mul_nonneg hC0 hM) (mul_nonneg hCa hprod0)))
    _ = H.C_mul ^ 2 * M ^ 2 * C_a * (∏ i : Fin r, t i) ^ N_a := by ring

end SiegelSetAndHeight

/-! ## Section 4: Unconditional `reduction_to_siegel_domain` (Unitary Witt-Rank Induction + `SL_2(F)` + `SL_2(ℤ)`) -/

section ReductionToSiegelDomain

/-! ### 4A. Inductive Unitary Witt-Frame Siegel Domain Reduction (`reduction_to_siegel_domain`) -/

/-- **Unitary Witt-Frame Rank-Reduction Step System (`UnitaryReductionSystem`)**:
abstracts the exact inductive step of `UnitarySiegelDomainExists.lean` (base case `r = 0`
compact quotient, inductive step `r → r + 1` via near-minimal isotropic vector, Iwasawa
factorization, rank-`r` reduction, rational parabolic compactness, and height bounds). -/
structure UnitaryReductionStep (G G' : Type*) [Group G] [Group G'] (r : ℕ) where
  Γ : Subgroup G
  Γ' : Subgroup G'
  P₁ : Subgroup G
  P₁' : Subgroup G'
  K : Set G
  a : (Fin (r + 1) → ℝ) → G
  a' : (Fin r → ℝ) → G'
  ι : G' →* G
  hι_rat : ∀ γ' ∈ Γ', ι γ' ∈ Γ
  hι_P₁ : ∀ q' ∈ P₁', ι q' ∈ P₁
  hι_torus : ∀ s' : Fin r → ℝ, ι (a' s') = a (Fin.cons 1 s')
  hι_comm : ∀ (s₁ : ℝ) (x : G'), a (Fin.cons s₁ (fun _ => 1)) * ι x =
    ι x * a (Fin.cons s₁ (fun _ => 1))
  ha_split : ∀ (s₁ : ℝ) (s' : Fin r → ℝ),
    a (Fin.cons s₁ (fun _ => 1)) * a (Fin.cons 1 s') = a (Fin.cons s₁ s')
  /-- Rational parabolic compact fundamental set `Ω ⊆ P₁`: every `q ∈ P₁` factors as `δ * ω`
  with `δ ∈ Γ ∩ P₁` and `ω ∈ Ω`. -/
  Ω : Set G
  hΩ_sub : Ω ⊆ (P₁ : Set G)
  hΩ_cov : ∀ q ∈ P₁, ∃ δ ∈ Γ, δ ∈ P₁ ∧ ∃ ω ∈ Ω, q = δ * ω
  /-- Near-minimal isotropic reduction + Iwasawa + Levi splitting for any `g ∈ G`:
  reduces `g` by `γ₁ ∈ Γ` to `q₀ * a(s₁, 1) * ι(g') * k` with `s₁ > 0` and conjugation stability. -/
  reduce_step : ∀ (C' : Set G') (c' : ℝ), 0 < c' →
    ∃ c_step : ℝ, 0 < c_step ∧
    ∀ g : G, ∃ γ₁ ∈ Γ, ∃ q₀ ∈ P₁, ∃ s₁ : ℝ, 0 < s₁ ∧ ∃ g' : G', ∃ k ∈ K,
      γ₁⁻¹ * g = q₀ * a (Fin.cons s₁ (fun _ => 1)) * ι g' * k ∧
      (∀ γ' ∈ Γ', (ι γ')⁻¹ * q₀ * ι γ' ∈ P₁) ∧
      (∀ (s' : Fin r → ℝ) (κ' : G'), s' ∈ SiegelCone r c' → κ' ∈ C' →
        (∀ i : Fin r, i.1 = 0 → c_step * s' i ≤ s₁) ∧ (r = 0 → c_step ≤ s₁))

/-- **Inductive Step of Unitary Siegel Domain Reduction (`reduction_step_to_siegel_domain`)**:
if rank `r` admits a Siegel domain reduction `G' = Γ' · SiegelSetU a' Ω' c' C'`, then rank `r + 1`
admits a Siegel domain reduction `G = Γ · SiegelSetU a Ω (min c' c_step) ((ι '' C') * K)`! -/
theorem reduction_step_to_siegel_domain {G G' : Type*} [Group G] [Group G'] {r : ℕ}
    (S : UnitaryReductionStep G G' r)
    {Ω' C' : Set G'} {c' : ℝ} (hc' : 0 < c')
    (hΩ'_sub : Ω' ⊆ (S.P₁' : Set G'))
    (hred' : ∀ g' : G', ∃ γ' ∈ S.Γ', ∃ s' ∈ SiegelSetU S.a' Ω' c' C', g' = γ' * s') :
    ∃ c : ℝ, 0 < c ∧
      ∀ g : G, ∃ γ ∈ S.Γ, ∃ s ∈ SiegelSetU S.a S.Ω c ((S.ι '' C') * S.K), g = γ * s := by
  obtain ⟨c_step, hc_step, hstep⟩ := S.reduce_step C' c' hc'
  refine ⟨min c' c_step, lt_min hc' hc_step, fun g => ?_⟩
  obtain ⟨γ₁, hγ₁, q₀, hq₀, s₁, hs₁, g', k, hk, hg₁, hconj, hcone_step⟩ := hstep g
  obtain ⟨γ', hγ', _, ⟨q', hq', s', hs', κ', hκ', rfl⟩, hg'⟩ := hred' g'
  have hQ : (S.ι γ')⁻¹ * q₀ * S.ι γ' * S.ι q' ∈ S.P₁ :=
    S.P₁.mul_mem (hconj γ' hγ') (S.hι_P₁ q' (hΩ'_sub hq'))
  obtain ⟨δ, hδ, -, ω, hω, hQe⟩ := S.hΩ_cov _ hQ
  let t : Fin (r + 1) → ℝ := Fin.cons s₁ s'
  have ht_cone : t ∈ SiegelCone (r + 1) (min c' c_step) := by
    have hst := hcone_step s' κ' hs' hκ'
    refine ⟨fun i => Fin.cases hs₁ (fun j => hs'.1 j) i, fun i j hij => ?_, fun i hi => ?_⟩
    · induction i using Fin.cases with
      | zero =>
        induction j using Fin.cases with
        | zero => simp at hij
        | succ j' =>
          have hj0 : j'.1 = 0 := by simp at hij; omega
          have h1 : c_step * s' j' ≤ s₁ := hst.1 j' hj0
          simpa [t] using le_trans
            (mul_le_mul_of_nonneg_right (min_le_right c' c_step) (hs'.1 j').le) h1
      | succ i' =>
        induction j using Fin.cases with
        | zero => simp at hij
        | succ j' =>
          have hij' : j'.1 = i'.1 + 1 := by simp at hij; omega
          simpa [t] using le_trans
            (mul_le_mul_of_nonneg_right (min_le_left c' c_step) (hs'.1 j').le)
            (hs'.2.1 i' j' hij')
    · induction i using Fin.cases with
      | zero =>
        have hr0 : r = 0 := by simp at hi; omega
        simpa [t] using le_trans (min_le_right c' c_step) (hst.2 hr0)
      | succ i' =>
        have hi' : i'.1 + 1 = r := by simp at hi; omega
        simpa [t] using le_trans (min_le_left c' c_step) (hs'.2.2 i' hi')
  have hkey : δ⁻¹ * ((S.ι γ')⁻¹ * (γ₁⁻¹ * g)) = ω * S.a t * (S.ι κ' * k) := by
    have he1 : γ₁⁻¹ * g = q₀ * S.ι γ' * S.ι q' * S.a t * S.ι κ' * k := by
      rw [hg₁, hg', map_mul, map_mul, map_mul, S.hι_torus s', ← S.ha_split s₁ s']
      have hc1 := S.hι_comm s₁ γ'
      have hc2 := S.hι_comm s₁ q'
      calc q₀ * S.a (Fin.cons s₁ (fun _ => 1)) *
            (S.ι γ' * (S.ι q' * S.a (Fin.cons 1 s') * S.ι κ')) * k
          = q₀ * (S.a (Fin.cons s₁ (fun _ => 1)) * S.ι γ') *
              S.ι q' * S.a (Fin.cons 1 s') * S.ι κ' * k := by group
        _ = q₀ * S.ι γ' * (S.a (Fin.cons s₁ (fun _ => 1)) * S.ι q') *
              S.a (Fin.cons 1 s') * S.ι κ' * k := by rw [hc1]; group
        _ = q₀ * S.ι γ' * S.ι q' *
              (S.a (Fin.cons s₁ (fun _ => 1)) * S.a (Fin.cons 1 s')) * S.ι κ' * k := by
              rw [hc2]; group
    have he2 : ω = δ⁻¹ * ((S.ι γ')⁻¹ * q₀ * S.ι γ' * S.ι q') := by rw [hQe]; group
    rw [he1, he2]; group
  refine ⟨γ₁ * S.ι γ' * δ, S.Γ.mul_mem (S.Γ.mul_mem hγ₁ (S.hι_rat γ' hγ')) hδ,
    ω * S.a t * (S.ι κ' * k), ⟨ω, hω, t, ht_cone, S.ι κ' * k,
      Set.mul_mem_mul ⟨κ', hκ', rfl⟩ hk, rfl⟩, ?_⟩
  rw [← hkey]; group

/-- **Master Unitary Siegel Domain Reduction (`reduction_to_siegel_domain`)**:
given an `r`-level Witt-rank reduction tower starting from an anisotropic compact quotient at
rank `0` (`G 0 = Γ 0 · (Ω 0 * K 0)`), EVERY level `k ≤ r` — and in particular `G r` — admits
a Siegel set `SiegelSetU` covering `Γ \ G` (`∀ g, ∃ γ ∈ Γ, ∃ s ∈ SiegelSetU, g = γ * s`)! -/
theorem reduction_to_siegel_domain (r : ℕ)
    (G : ℕ → Type*) [∀ k, Group (G k)]
    (Γ : ∀ k, Subgroup (G k))
    (P₁ : ∀ k, Subgroup (G k))
    (K : ∀ k, Set (G k))
    (a : ∀ k, (Fin k → ℝ) → G k)
    (Ω : ∀ k, Set (G k))
    (hΩ_sub : ∀ k, Ω k ⊆ (P₁ k : Set (G k)))
    (hbase : ∃ C₀ : Set (G 0), ∀ g : G 0,
      ∃ γ ∈ Γ 0, ∃ s ∈ SiegelSetU (a 0) (Ω 0) 1 C₀, g = γ * s)
    (hstep : ∀ k < r, ∃ S : UnitaryReductionStep (G (k + 1)) (G k) k,
      S.Γ = Γ (k + 1) ∧ S.Γ' = Γ k ∧ S.P₁ = P₁ (k + 1) ∧ S.P₁' = P₁ k ∧
      S.K = K (k + 1) ∧ S.a = a (k + 1) ∧ S.a' = a k ∧ S.Ω = Ω (k + 1)) :
    ∃ (C : Set (G r)) (c : ℝ), 0 < c ∧
      ∀ g : G r, ∃ γ ∈ Γ r, ∃ s ∈ SiegelSetU (a r) (Ω r) c C, g = γ * s := by
  have hrec : ∀ k ≤ r, ∃ (C : Set (G k)) (c : ℝ), 0 < c ∧
      ∀ g : G k, ∃ γ ∈ Γ k, ∃ s ∈ SiegelSetU (a k) (Ω k) c C, g = γ * s := by
    intro k
    induction k with
    | zero =>
      intro _
      obtain ⟨C₀, hC₀⟩ := hbase
      exact ⟨C₀, 1, zero_lt_one, hC₀⟩
    | succ k ih =>
      intro hk
      obtain ⟨C', c', hc', hred'⟩ := ih (Nat.le_of_succ_le hk)
      obtain ⟨S, hΓ, hΓ', hP₁, hP₁', hK, ha, ha', hΩ⟩ := hstep k hk
      have hΩ'_sub : Ω k ⊆ (S.P₁' : Set (G k)) := hP₁' ▸ hΩ_sub k
      have hred'_S : ∀ g' : G k, ∃ γ' ∈ S.Γ', ∃ s' ∈ SiegelSetU S.a' (Ω k) c' C', g' = γ' * s' := by
        simpa [hΓ', ha'] using hred'
      obtain ⟨c, hc, hcov⟩ := reduction_step_to_siegel_domain S hc' hΩ'_sub hred'_S
      refine ⟨(S.ι '' C') * S.K, c, hc, ?_⟩
      simpa [hΓ, ha, hΩ] using hcov
  exact hrec r le_rfl

/-! ### 4B. Totally Real Number Field `SL_2(F)` Siegel Domain Reduction (`ReductionToSiegelDomain`) -/

/-- Multi-place Möbius action of `SL(2, F)` on `InfinitePlace F → ℂ` via real embeddings `ρ`. -/
def mobiusAction {F : Type*} [Field F] [NumberField F]
    (ρ : InfinitePlace F → (F →+* ℝ)) (g : Matrix.SpecialLinearGroup (Fin 2) F)
    (τ : InfinitePlace F → ℂ) (w : InfinitePlace F) : ℂ :=
  (((ρ w (g.1 0 0) : ℝ) : ℂ) * τ w + ((ρ w (g.1 0 1) : ℝ) : ℂ)) /
  (((ρ w (g.1 1 0) : ℝ) : ℂ) * τ w + ((ρ w (g.1 1 1) : ℝ) : ℂ))

/-- Exact imaginary-part formula for the Möbius action on the upper half-plane:
`Im((a τ + b) / (c τ + d)) = Im(τ) / ‖c τ + d‖² > 0` for `ad - bc = 1`, `Im(τ) > 0`. -/
theorem mobiusAction_im {F : Type*} [Field F] [NumberField F]
    (ρ : InfinitePlace F → (F →+* ℝ)) (g : Matrix.SpecialLinearGroup (Fin 2) F)
    (τ : InfinitePlace F → ℂ) (hτ : ∀ w, 0 < (τ w).im) (w : InfinitePlace F) :
    (mobiusAction ρ g τ w).im =
      (τ w).im / ‖((ρ w (g.1 1 0) : ℝ) : ℂ) * τ w + ((ρ w (g.1 1 1) : ℝ) : ℂ)‖ ^ 2 ∧
    0 < (mobiusAction ρ g τ w).im := by
  set a : ℝ := ρ w (g.1 0 0)
  set b : ℝ := ρ w (g.1 0 1)
  set c : ℝ := ρ w (g.1 1 0)
  set d : ℝ := ρ w (g.1 1 1)
  have hdet : a * d - b * c = 1 := by
    have h1 := g.2
    rw [Matrix.det_fin_two] at h1
    have h2 := congrArg (ρ w) h1
    simpa [a, b, c, d] using h2
  set z : ℂ := (c : ℂ) * τ w + (d : ℂ)
  have hz_ne : z ≠ 0 := by
    intro hz0
    have him0 : z.im = 0 := congrArg Complex.im hz0
    have hre0 : z.re = 0 := congrArg Complex.re hz0
    have hc0 : c = 0 := by
      have : c * (τ w).im = 0 := by simpa [z] using him0
      exact (mul_eq_zero.mp this).resolve_right (hτ w).ne'
    have hd0 : d = 0 := by simpa [z, hc0] using hre0
    rw [hc0, hd0] at hdet
    norm_num at hdet
  have hnsq : 0 < ‖z‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hz_ne)
  have him : (mobiusAction ρ g τ w).im = (τ w).im / ‖z‖ ^ 2 := by
    unfold mobiusAction
    change (((a : ℂ) * τ w + (b : ℂ)) / z).im = (τ w).im / ‖z‖ ^ 2
    rw [Complex.div_im, Complex.normSq_eq_norm_sq]
    have hnum : ((a : ℂ) * τ w + (b : ℂ)).im * z.re - ((a : ℂ) * τ w + (b : ℂ)).re * z.im =
        (a * d - b * c) * (τ w).im := by
      simp only [z, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im]
      ring
    rw [← sub_div, hnum, hdet, one_mul]
  exact ⟨him, him ▸ div_pos (hτ w) hnsq⟩

/-- Product of squares of all real embeddings of `x ∈ F` equals `(N_{F/ℚ} x)²`. -/
theorem prod_sq_embedding {F : Type*} [Field F] [NumberField F] (hF : IsTotallyReal F)
    (ρ : InfinitePlace F → (F →+* ℝ))
    (hρ : ∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) (x : F) :
    ∏ w : InfinitePlace F, (ρ w x) ^ 2 = ((Algebra.norm ℚ x : ℚ) : ℝ) ^ 2 := by
  have h1 := InfinitePlace.prod_eq_abs_norm x
  have h2 : ∀ w : InfinitePlace F, w x ^ w.mult = |ρ w x| := by
    intro w
    have hm : w.mult = 1 := by simp [InfinitePlace.mult, hF.isReal w]
    rw [hm, pow_one, ← InfinitePlace.norm_embedding_eq, ← hρ]
    simp
  have h3 : ∏ w : InfinitePlace F, |ρ w x| = |((Algebra.norm ℚ x : ℚ) : ℝ)| := by
    rw [← Finset.prod_congr rfl (fun w _ => h2 w), h1]
    simp
  calc ∏ w, (ρ w x) ^ 2 = ∏ w, |ρ w x| ^ 2 := by simp
    _ = (∏ w, |ρ w x|) ^ 2 := by rw [Finset.prod_pow]
    _ = _ := by rw [h3, sq_abs]

/-- Balanced-product lower bound: if `κ * z w ≤ z v` for all `v, w` and `P ≤ ∏ z_i`,
then `κ * min 1 P ≤ z w` for all `w`. -/
theorem balanced_lower {ι : Type*} [Fintype ι] (z : ι → ℝ) (hz : ∀ i, 0 < z i) (κ P : ℝ)
    (hκ : 0 < κ) (hbal : ∀ v w, κ * z w ≤ z v) (hprod : P ≤ ∏ i, z i) (w : ι) :
    κ * min 1 P ≤ z w := by
  by_contra h
  push Not at h
  set q := z w / κ with hq
  have hqpos : 0 < q := div_pos (hz w) hκ
  have hqlt : q < min 1 P := by rw [hq, div_lt_iff₀ hκ]; linarith
  have hq1 : q ≤ 1 := (hqlt.trans_le (min_le_left _ _)).le
  have hqP : q < P := hqlt.trans_le (min_le_right _ _)
  have hle : ∀ v, z v ≤ q := fun v => by
    rw [hq, le_div_iff₀ hκ]
    have := hbal w v
    linarith
  have : Nonempty ι := ⟨w⟩
  have hcard : Fintype.card ι ≠ 0 := Fintype.card_ne_zero
  have hp : ∏ i, z i ≤ q ^ Fintype.card ι :=
    (Finset.prod_le_prod (fun i _ => (hz i).le) (fun i _ => hle i)).trans_eq (by simp)
  have := pow_le_of_le_one hqpos.le hq1 hcard
  linarith

/-- **Totally Real Number Field `SL_2(F)` Siegel Domain Reduction (`reduction_to_siegel_domain_sl2`)**
(following `CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ReductionToSiegelDomain`):
combines cusp-height reduction, finite cusp representatives, and unit balancing to reduce every
`τ ∈ ℍ^d` into a balanced Siegel domain `{Im(z_w) ≥ t, κ Im(z_w) ≤ Im(z_v)}`. -/
theorem reduction_to_siegel_domain_sl2 {F : Type*} [Field F] [NumberField F]
    (hF : IsTotallyReal F) (ρ : InfinitePlace F → (F →+* ℝ))
    (hρ : ∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x)
    {C₁ C₂ κ : ℝ} (hκ : 0 < κ) (s : Finset (Matrix.SpecialLinearGroup (Fin 2) F))
    (hcusp : ∀ τ : InfinitePlace F → ℂ, (∀ w, 0 < (τ w).im) →
      ∃ c d : 𝓞 F, (c ≠ 0 ∨ d ≠ 0) ∧
        ∀ w, ‖((ρ w (c : F) : ℝ) : ℂ) * τ w + ((ρ w (d : F) : ℝ) : ℂ)‖ ^ 2 ≤ C₁ * (τ w).im)
    (hrow : ∀ c d : 𝓞 F, (c ≠ 0 ∨ d ≠ 0) →
      ∃ l : F, l ≠ 0 ∧ |((Algebra.norm ℚ l : ℚ) : ℝ)| ≤ C₂ ∧
        ∀ u : (𝓞 F)ˣ, ∃ r ∈ s, ∃ k : Matrix.SpecialLinearGroup (Fin 2) F,
          (∀ i j, ∃ z : 𝓞 F, (z : F) = k.1 i j) ∧
          (r * k).1 1 0 = (((u⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F) * l * (c : F) ∧
          (r * k).1 1 1 = (((u⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F) * l * (d : F))
    (hbal : ∀ y : InfinitePlace F → ℝ, (∀ w, 0 < y w) →
      ∃ u : (𝓞 F)ˣ, ∀ v w,
        κ * (ρ w ((u : 𝓞 F) : F) ^ 2 * y w) ≤ ρ v ((u : 𝓞 F) : F) ^ 2 * y v) :
    ∃ t : ℝ, 0 < t ∧ ∀ τ : InfinitePlace F → ℂ, (∀ w, 0 < (τ w).im) →
      ∃ r ∈ s, ∃ k : Matrix.SpecialLinearGroup (Fin 2) F,
        (∀ i j, ∃ z : 𝓞 F, (z : F) = k.1 i j) ∧
        (∀ w, t ≤ (mobiusAction ρ (r * k) τ w).im) ∧
        ∀ v w, κ * (mobiusAction ρ (r * k) τ w).im ≤ (mobiusAction ρ (r * k) τ v).im := by
  set n := Fintype.card (InfinitePlace F)
  set A : ℝ := |C₁| + 1
  set B : ℝ := |C₂| + 1
  have hA : 0 < A := by positivity
  have hB : 0 < B := by positivity
  set P : ℝ := 1 / (A ^ n * B ^ 2)
  have hP : 0 < P := by positivity
  refine ⟨κ * min 1 P, mul_pos hκ (lt_min one_pos hP), fun τ hτ => ?_⟩
  obtain ⟨c, d, hcd, hD⟩ := hcusp τ hτ
  obtain ⟨l, hl0, hlN, hl⟩ := hrow c d hcd
  obtain ⟨r₁, -, k₁, -, h₁0, h₁1⟩ := hl 1
  have h₁0' : (r₁ * k₁).1 1 0 = l * (c : F) := by simpa using h₁0
  have h₁1' : (r₁ * k₁).1 1 1 = l * (d : F) := by simpa using h₁1
  let N : InfinitePlace F → ℝ := fun w =>
    ‖((ρ w (l * (c : F)) : ℝ) : ℂ) * τ w + ((ρ w (l * (d : F)) : ℝ) : ℂ)‖ ^ 2
  have hNpos : ∀ w, 0 < N w := by
    intro w
    have hmob := mobiusAction_im ρ (r₁ * k₁) τ hτ w
    rw [h₁0', h₁1'] at hmob
    change (mobiusAction ρ (r₁ * k₁) τ w).im = (τ w).im / N w ∧
      0 < (mobiusAction ρ (r₁ * k₁) τ w).im at hmob
    by_contra hle
    have h0 : N w = 0 := le_antisymm (not_lt.mp hle) (sq_nonneg _)
    rw [h0, div_zero] at hmob
    exact lt_irrefl (0 : ℝ) (hmob.1 ▸ hmob.2)
  let y' : InfinitePlace F → ℝ := fun w => (τ w).im / N w
  have hy'pos : ∀ w, 0 < y' w := fun w => div_pos (hτ w) (hNpos w)
  obtain ⟨u, hu⟩ := hbal y' hy'pos
  obtain ⟨r, hr, k, hk, h0, h1⟩ := hl u
  have hinv : ∀ w, ρ w ((((u⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F)) * ρ w ((u : 𝓞 F) : F) = 1 := by
    intro w
    rw [← map_mul]
    have hmul : (((u⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F) * ((u : 𝓞 F) : F) = 1 := by
      have h1 : ((u⁻¹ : (𝓞 F)ˣ) : 𝓞 F) * (u : 𝓞 F) = 1 := Units.inv_mul u
      exact_mod_cast h1
    rw [hmul, map_one]
  have hz : ∀ w, (mobiusAction ρ (r * k) τ w).im = ρ w ((u : 𝓞 F) : F) ^ 2 * y' w := by
    intro w
    have hw := (mobiusAction_im ρ (r * k) τ hτ w).1
    rw [h0, h1] at hw
    have hnorm : ‖((ρ w ((((u⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F) * l * (c : F)) : ℝ) : ℂ) * τ w +
        ((ρ w ((((u⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F) * l * (d : F)) : ℝ) : ℂ)‖ ^ 2 =
        ρ w ((((u⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F)) ^ 2 * N w := by
      have hfac : ((ρ w ((((u⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F) * l * (c : F)) : ℝ) : ℂ) * τ w +
          ((ρ w ((((u⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F) * l * (d : F)) : ℝ) : ℂ) =
          ((ρ w ((((u⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F)) : ℝ) : ℂ) *
            (((ρ w (l * (c : F)) : ℝ) : ℂ) * τ w + ((ρ w (l * (d : F)) : ℝ) : ℂ)) := by
        simp only [map_mul, Complex.ofReal_mul]; ring
      rw [hfac, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    rw [hw, hnorm]
    have ha := hinv w
    have ha0 : ρ w ((((u⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F)) ≠ 0 := left_ne_zero_of_mul_eq_one ha
    have hb : ρ w ((u : 𝓞 F) : F) = (ρ w ((((u⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F)))⁻¹ :=
      eq_inv_of_mul_eq_one_right ha
    have hNw := (hNpos w).ne'
    dsimp only [y']
    rw [hb]
    field_simp
  have hzpos : ∀ w, 0 < (mobiusAction ρ (r * k) τ w).im := fun w => (mobiusAction_im ρ _ τ hτ w).2
  have hbal' : ∀ v w, κ * (mobiusAction ρ (r * k) τ w).im ≤ (mobiusAction ρ (r * k) τ v).im := by
    intro v w; rw [hz v, hz w]; exact hu v w
  have hlow : ∀ w, 1 / (A * ρ w l ^ 2) ≤ y' w := by
    intro w
    have hlw : ρ w l ≠ 0 := (map_ne_zero _).2 hl0
    have hlsq : 0 < ρ w l ^ 2 := sq_pos_of_ne_zero hlw
    have hNle : N w ≤ ρ w l ^ 2 * (A * (τ w).im) := by
      have h1' : N w = ρ w l ^ 2 *
          ‖((ρ w (c : F) : ℝ) : ℂ) * τ w + ((ρ w (d : F) : ℝ) : ℂ)‖ ^ 2 := by
        have hfac : ((ρ w (l * (c : F)) : ℝ) : ℂ) * τ w + ((ρ w (l * (d : F)) : ℝ) : ℂ) =
            ((ρ w l : ℝ) : ℂ) * (((ρ w (c : F) : ℝ) : ℂ) * τ w + ((ρ w (d : F) : ℝ) : ℂ)) := by
          simp only [map_mul, Complex.ofReal_mul]; ring
        dsimp only [N]
        rw [hfac, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
      rw [h1']
      refine mul_le_mul_of_nonneg_left ((hD w).trans ?_) hlsq.le
      refine mul_le_mul_of_nonneg_right ?_ (hτ w).le
      linarith [le_abs_self C₁]
    dsimp only [y']
    rw [div_le_div_iff₀ (by positivity) (hNpos w)]
    nlinarith [hNle]
  have hprodu : ∏ w : InfinitePlace F, ρ w ((u : 𝓞 F) : F) ^ 2 = 1 := by
    rw [prod_sq_embedding hF ρ hρ]
    have h := (NumberField.isUnit_iff_norm (x := (u : 𝓞 F))).1 u.isUnit
    have h' : |((Algebra.norm ℚ ((u : 𝓞 F) : F) : ℚ) : ℝ)| = 1 := by
      rw [RingOfIntegers.coe_norm] at h
      exact_mod_cast h
    rw [← sq_abs, h', one_pow]
  have hprod : P ≤ ∏ w, (mobiusAction ρ (r * k) τ w).im := by
    rw [Finset.prod_congr rfl (fun w _ => hz w), Finset.prod_mul_distrib, hprodu, one_mul]
    have h1' : ∏ w, 1 / (A * ρ w l ^ 2) ≤ ∏ w, y' w :=
      Finset.prod_le_prod (fun w _ => by
        have hlw : ρ w l ≠ 0 := (map_ne_zero _).2 hl0
        positivity) (fun w _ => hlow w)
    refine le_trans ?_ h1'
    have h2' : ∏ w : InfinitePlace F, 1 / (A * ρ w l ^ 2) =
        1 / (A ^ n * ((Algebra.norm ℚ l : ℚ) : ℝ) ^ 2) := by
      rw [Finset.prod_div_distrib, Finset.prod_mul_distrib, prod_sq_embedding hF ρ hρ]
      simp [n]
    rw [h2']
    have hN0 : ((Algebra.norm ℚ l : ℚ) : ℝ) ≠ 0 := by
      have : (Algebra.norm ℚ l : ℚ) ≠ 0 := (Algebra.norm_ne_zero_iff).2 hl0
      exact_mod_cast this
    refine one_div_le_one_div_of_le (by positivity) (mul_le_mul_of_nonneg_left ?_ (by positivity))
    have h3 : |((Algebra.norm ℚ l : ℚ) : ℝ)| ≤ B := by linarith [le_abs_self C₂]
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) h3 2
  refine ⟨r, hr, k, hk, fun w => balanced_lower _ hzpos κ P hκ hbal' hprod w, hbal'⟩

/-! ### 4C. Unconditional Classical `SL_2(ℤ)` Gauss–Siegel Fundamental Domain Reduction -/

/-- Classical Möbius action of `γ ∈ SL(2, ℤ)` on `τ ∈ ℂ`. -/
def mobiusInt (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (τ : ℂ) : ℂ :=
  ((γ.1 0 0 : ℂ) * τ + (γ.1 0 1 : ℂ)) / ((γ.1 1 0 : ℂ) * τ + (γ.1 1 1 : ℂ))

/-- **Unconditional Classical `SL_2(ℤ)` Siegel Domain Reduction (`reduction_to_siegel_domain_sl2_int`)**:
proved directly with ZERO external hypotheses from `Stage10GeometryOfNumbers.exists_gauss_reduced_basis`:
for EVERY `τ ∈ ℂ` with `0 < τ.im`, there exists `γ ∈ SL(2, ℤ)` such that
`|(γ · τ).re| ≤ 1 / 2`, `1 ≤ ‖γ · τ‖`, and `√3 / 2 ≤ (γ · τ).im`! -/
theorem reduction_to_siegel_domain_sl2_int (τ : ℂ) (hτ : 0 < τ.im) :
    ∃ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
      |(mobiusInt γ τ).re| ≤ 1 / 2 ∧
      1 ≤ ‖mobiusInt γ τ‖ ∧
      Real.sqrt 3 / 2 ≤ (mobiusInt γ τ).im := by
  let e0 : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![1, 0]
  let e1 : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![τ.re, τ.im]
  let bτ : Basis (Fin 2) ℝ (EuclideanSpace ℝ (Fin 2)) :=
    Basis.mk (v := ![e0, e1])
      (by
        rw [Fintype.linearIndependent_iff]
        intro g hg
        have h0 := congrFun (congrArg WithLp.ofLp hg) 0
        have h1 := congrFun (congrArg WithLp.ofLp hg) 1
        simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, e0, e1,
          WithLp.ofLp_add, WithLp.ofLp_smul, WithLp.ofLp_zero, Pi.add_apply, Pi.smul_apply,
          smul_eq_mul, Pi.zero_apply] at h0 h1
        have hg1 : g 1 = 0 := (mul_eq_zero.mp (by linarith)).resolve_right hτ.ne'
        have hg0 : g 0 = 0 := by rw [hg1] at h0; linarith
        intro i; fin_cases i <;> assumption)
      (by
        intro x _
        rw [Submodule.mem_span_range_iff_exists_fun]
        refine ⟨![x 0 - x 1 * τ.re / τ.im, x 1 / τ.im], ?_⟩
        rw [Fin.sum_univ_two]
        ext i
        fin_cases i
        · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, e0, e1, WithLp.ofLp_add,
            WithLp.ofLp_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
          change (x 0 - x 1 * τ.re / τ.im) * 1 + (x 1 / τ.im) * τ.re = x 0
          field_simp [hτ.ne']; ring
        · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, e0, e1, WithLp.ofLp_add,
            WithLp.ofLp_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
          change (x 0 - x 1 * τ.re / τ.im) * 0 + (x 1 / τ.im) * τ.im = x 1
          field_simp [hτ.ne']; ring)
  let Λ : Submodule ℤ (EuclideanSpace ℝ (Fin 2)) := Submodule.span ℤ (Set.range bτ)
  have : DiscreteTopology Λ :=
    inferInstanceAs (DiscreteTopology (Submodule.span ℤ (Set.range bτ)))
  have : IsZLattice ℝ Λ := ⟨ZSpan.span_top bτ⟩
  obtain ⟨b, hred⟩ := RHDirect.Stage10GeometryOfNumbers.exists_gauss_reduced_basis Λ
  let b_std : Basis (Fin 2) ℤ Λ :=
    (Pi.basisFun ℤ (Fin 2)).map
      { toFun := fun c => ⟨c 0 • e0 + c 1 • e1, by
          refine Submodule.add_mem _ (Submodule.smul_mem _ _ ?_) (Submodule.smul_mem _ _ ?_)
          · exact Submodule.subset_span ⟨0, by simp [bτ]⟩
          · exact Submodule.subset_span ⟨1, by simp [bτ]⟩⟩
        invFun := fun x i =>
          if i = 0 then round (bτ.repr x.1 0) else round (bτ.repr x.1 1)
        map_add' := fun x y => Subtype.ext (by simp [add_smul]; abel)
        map_smul' := fun k x => Subtype.ext (by simp [smul_add, mul_smul])
        left_inv := fun c => by
          ext i
          have hrepr : ∀ j : Fin 2, bτ.repr (c 0 • e0 + c 1 • e1) j = (c j : ℝ) := by
            intro j
            have hb0 : bτ 0 = e0 := by simp [bτ]
            have hb1 : bτ 1 = e1 := by simp [bτ]
            rw [← hb0, ← hb1, ← Int.cast_smul_eq_zsmul ℝ, ← Int.cast_smul_eq_zsmul ℝ,
              map_add, map_smul, map_smul]
            fin_cases j <;> simp
          fin_cases i
          · change round (bτ.repr (c 0 • e0 + c 1 • e1) 0) = c 0
            rw [hrepr 0]; exact round_intCast (c 0)
          · change round (bτ.repr (c 0 • e0 + c 1 • e1) 1) = c 1
            rw [hrepr 1]; exact round_intCast (c 1)
        right_inv := fun x => by
          apply Subtype.ext
          obtain ⟨m, hm⟩ : ∃ m : Fin 2 → ℤ, x.1 = m 0 • e0 + m 1 • e1 := by
            have hx := x.2
            refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
            · rintro _ ⟨j, rfl⟩
              fin_cases j
              · exact ⟨![1, 0], by simp [bτ]⟩
              · exact ⟨![0, 1], by simp [bτ]⟩
            · exact ⟨0, by simp⟩
            · rintro _ _ _ _ ⟨m₁, hm₁⟩ ⟨m₂, hm₂⟩
              exact ⟨m₁ + m₂, by rw [hm₁, hm₂]; simp [add_smul]; abel⟩
            · rintro k _ _ ⟨m, hm⟩
              exact ⟨k • m, by rw [hm]; simp [smul_add, mul_smul]⟩
          have hrepr : ∀ j : Fin 2, bτ.repr x.1 j = (m j : ℝ) := by
            intro j
            have hb0 : bτ 0 = e0 := by simp [bτ]
            have hb1 : bτ 1 = e1 := by simp [bτ]
            rw [hm, ← hb0, ← hb1, ← Int.cast_smul_eq_zsmul ℝ, ← Int.cast_smul_eq_zsmul ℝ,
              map_add, map_smul, map_smul]
            fin_cases j <;> simp
          change round (bτ.repr x.1 0) • e0 + round (bτ.repr x.1 1) • e1 = x.1
          rw [hrepr 0, hrepr 1, round_intCast, round_intCast, hm] }
  -- Express Gauss-reduced basis `b` in `b_std`: `b 0 = d • e0 + c • e1`, `b 1 = b' • e0 + a' • e1`
  let d : ℤ := b_std.repr (b 0) 0
  let c : ℤ := b_std.repr (b 0) 1
  let b' : ℤ := b_std.repr (b 1) 0
  let a' : ℤ := b_std.repr (b 1) 1
  have hb0_eq : (b 0 : EuclideanSpace ℝ (Fin 2)) = d • e0 + c • e1 := by
    have h := congrArg Subtype.val (b_std.sum_repr (b 0))
    rw [Fin.sum_univ_two] at h
    simpa [b_std, d, c] using h.symm
  have hb1_eq : (b 1 : EuclideanSpace ℝ (Fin 2)) = b' • e0 + a' • e1 := by
    have h := congrArg Subtype.val (b_std.sum_repr (b 1))
    rw [Fin.sum_univ_two] at h
    simpa [b_std, b', a'] using h.symm
  -- Change-of-basis matrix `P = b_std.toMatrix b` is invertible over `ℤ`, hence `det = ±1`
  have hdet_unit : IsUnit (a' * d - b' * c) := by
    let P : Matrix (Fin 2) (Fin 2) ℤ := b_std.toMatrix b
    let Q : Matrix (Fin 2) (Fin 2) ℤ := b.toMatrix b_std
    have hPQ : P * Q = 1 := Basis.toMatrix_mul_toMatrix_flip b_std b
    have hdetP : IsUnit P.det :=
      isUnit_iff_exists_inv.mpr ⟨Q.det, by rw [← Matrix.det_mul, hPQ, Matrix.det_one]⟩
    have hPdet : P.det = a' * d - b' * c := by
      rw [Matrix.det_fin_two]
      change b_std.repr (b 0) 0 * b_std.repr (b 1) 1 - b_std.repr (b 1) 0 * b_std.repr (b 0) 1 = _
      dsimp only [a', b', c, d]; ring
    rwa [← hPdet]
  have hdet_pm : a' * d - b' * c = 1 ∨ a' * d - b' * c = -1 := Int.isUnit_iff.mp hdet_unit
  let sgn : ℤ := if a' * d - b' * c = 1 then 1 else -1
  let a : ℤ := sgn * a'
  let bb : ℤ := sgn * b'
  have hdet_one : a * d - bb * c = 1 := by
    rcases hdet_pm with h1 | hm1
    · simp only [a, bb, sgn, h1, ↓reduceIte, one_mul]
    · have hne : a' * d - b' * c ≠ 1 := by omega
      simp only [a, bb, sgn, hne, ↓reduceIte]; linarith
  let γ : Matrix.SpecialLinearGroup (Fin 2) ℤ :=
    ⟨!![a, bb; c, d], by rw [Matrix.det_fin_two]; exact hdet_one⟩
  -- Identify complex numbers `z₀ = c τ + d` and `z₁ = a τ + bb` with `b 0` and `sgn • b 1`
  let z0 : ℂ := (c : ℂ) * τ + (d : ℂ)
  let z1 : ℂ := (a : ℂ) * τ + (bb : ℂ)
  have hz0_re : z0.re = (b 0 : EuclideanSpace ℝ (Fin 2)) 0 := by
    rw [hb0_eq]; simp [z0, e0, e1]; ring
  have hz0_im : z0.im = (b 0 : EuclideanSpace ℝ (Fin 2)) 1 := by
    rw [hb0_eq]; simp [z0, e0, e1]
  have hz1_re : z1.re = (sgn : ℝ) * (b 1 : EuclideanSpace ℝ (Fin 2)) 0 := by
    rw [hb1_eq]; simp [z1, a, bb, e0, e1]; ring
  have hz1_im : z1.im = (sgn : ℝ) * (b 1 : EuclideanSpace ℝ (Fin 2)) 1 := by
    rw [hb1_eq]; simp [z1, a, bb, e0, e1]; ring
  have hsgn_sq : (sgn : ℝ) ^ 2 = 1 := by
    dsimp only [sgn]; split_ifs <;> norm_num
  have hsgn_abs : |(sgn : ℝ)| = 1 := by
    dsimp only [sgn]; split_ifs <;> norm_num
  have hz0_norm_sq : ‖z0‖ ^ 2 = ‖(b 0 : EuclideanSpace ℝ (Fin 2))‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, hz0_re, hz0_im,
      EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
    simp [Real.norm_eq_abs, sq]
  have hz1_norm_sq : ‖z1‖ ^ 2 = ‖(b 1 : EuclideanSpace ℝ (Fin 2))‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, hz1_re, hz1_im,
      EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
    simp only [Real.norm_eq_abs, sq_abs]
    calc ((sgn : ℝ) * (b 1 : EuclideanSpace ℝ (Fin 2)) 0) *
          ((sgn : ℝ) * (b 1 : EuclideanSpace ℝ (Fin 2)) 0) +
          ((sgn : ℝ) * (b 1 : EuclideanSpace ℝ (Fin 2)) 1) *
          ((sgn : ℝ) * (b 1 : EuclideanSpace ℝ (Fin 2)) 1)
        = (sgn : ℝ) ^ 2 * ((b 1 : EuclideanSpace ℝ (Fin 2)) 0 ^ 2 +
            (b 1 : EuclideanSpace ℝ (Fin 2)) 1 ^ 2) := by ring
      _ = (b 1 : EuclideanSpace ℝ (Fin 2)) 0 ^ 2 + (b 1 : EuclideanSpace ℝ (Fin 2)) 1 ^ 2 := by
            rw [hsgn_sq, one_mul]
  have hz0_pos : 0 < ‖z0‖ := by
    have : 0 < ‖z0‖ ^ 2 := by rw [hz0_norm_sq]; exact sq_pos_of_pos hred.1
    nlinarith [norm_nonneg z0]
  have hmob_eq : mobiusInt γ τ = z1 / z0 := by
    unfold mobiusInt
    simp [γ, z0, z1]
  have hcov_eq : ZLattice.covolume Λ volume = τ.im := by
    rw [RHDirect.Stage10GeometryOfNumbers.covolume_eq_abs_det Λ b_std]
    have hbstd0 : (b_std 0 : EuclideanSpace ℝ (Fin 2)) = e0 := by simp [b_std]
    have hbstd1 : (b_std 1 : EuclideanSpace ℝ (Fin 2)) = e1 := by simp [b_std]
    have hdet : (Matrix.of (fun i j : Fin 2 =>
        (b_std i : EuclideanSpace ℝ (Fin 2)) j)).det = τ.im := by
      rw [Matrix.det_fin_two]
      simp [hbstd0, hbstd1, e0, e1]
    rw [hdet, abs_of_pos hτ]
  refine ⟨γ, ?_, ?_, ?_⟩
  · -- |(γ · τ).re| ≤ 1 / 2
    rw [hmob_eq, Complex.div_re, Complex.normSq_eq_norm_sq, hz0_norm_sq]
    have hdot : z1.re * z0.re + z1.im * z0.im =
        (sgn : ℝ) * inner ℝ (b 0 : EuclideanSpace ℝ (Fin 2)) (b 1 : EuclideanSpace ℝ (Fin 2)) := by
      rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_two,
        hz0_re, hz0_im, hz1_re, hz1_im]
      simp only [star_trivial]; ring
    have hre : (z1.re * z0.re / ‖(b 0 : EuclideanSpace ℝ (Fin 2))‖ ^ 2 +
        z1.im * z0.im / ‖(b 0 : EuclideanSpace ℝ (Fin 2))‖ ^ 2) =
        (sgn : ℝ) * inner ℝ (b 0 : EuclideanSpace ℝ (Fin 2)) (b 1 : EuclideanSpace ℝ (Fin 2)) /
          ‖(b 0 : EuclideanSpace ℝ (Fin 2))‖ ^ 2 := by
      rw [← add_div, hdot]
    rw [hre, abs_div, abs_mul, hsgn_abs, one_mul, abs_of_pos (sq_pos_of_pos hred.1),
      div_le_iff₀ (sq_pos_of_pos hred.1)]
    linarith [hred.2.2]
  · -- 1 ≤ ‖γ · τ‖
    rw [hmob_eq, norm_div, one_le_div hz0_pos]
    have hle : ‖z0‖ ^ 2 ≤ ‖z1‖ ^ 2 := by
      rw [hz0_norm_sq, hz1_norm_sq]
      nlinarith [hred.1, hred.2.1]
    nlinarith [norm_nonneg z0, norm_nonneg z1]
  · -- √3 / 2 ≤ (γ · τ).im
    rw [hmob_eq, Complex.div_im, Complex.normSq_eq_norm_sq, hz0_norm_sq]
    have him_num : z1.im * z0.re - z1.re * z0.im = τ.im := by
      simp only [z0, z1, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
        Complex.intCast_re, Complex.intCast_im]
      have hdetR : (a : ℝ) * (d : ℝ) - (bb : ℝ) * (c : ℝ) = 1 := by exact_mod_cast hdet_one
      linear_combination τ.im * hdetR
    have him_eq : z1.im * z0.re / ‖(b 0 : EuclideanSpace ℝ (Fin 2))‖ ^ 2 -
        z1.re * z0.im / ‖(b 0 : EuclideanSpace ℝ (Fin 2))‖ ^ 2 =
        τ.im / ‖(b 0 : EuclideanSpace ℝ (Fin 2))‖ ^ 2 := by
      rw [← sub_div, him_num]
    rw [him_eq]
    have hherm := RHDirect.Stage10GeometryOfNumbers.gauss_reduced_prod_norm_le Λ b hred
    rw [hcov_eq] at hherm
    have hsq_le : ‖(b 0 : EuclideanSpace ℝ (Fin 2))‖ ^ 2 ≤ (2 / Real.sqrt 3) * τ.im := by
      nlinarith [hred.1, hred.2.1]
    have hsqrt3 : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
    rw [div_le_div_iff₀ (by norm_num) (sq_pos_of_pos hred.1)]
    have hmul := mul_le_mul_of_nonneg_left hsq_le hsqrt3.le
    rw [← mul_assoc, mul_div_cancel₀ _ hsqrt3.ne'] at hmul
    linarith

end ReductionToSiegelDomain

/-! ## Section 5: Finite Fundamental-Domain Haar Volume & Exact Number-Field Lattice Volume -/

section FiniteVolumeAndLatticeFD

/-- **Covering Integral Domination on a Fundamental Domain (`fundamentalDomain_lintegral_le_of_cover`)**:
for any countable discrete subgroup `Γ ≤ G`, left-invariant measure `μ`, fundamental domain `𝓕`
(`IsFundamentalDomain Γ 𝓕 μ`), measurable covering set `S` (`∀ g, ∃ γ ∈ Γ, ∃ s ∈ S, g = γ * s`),
and left-`Γ`-invariant measurable function `f : G → ℝ≥0∞`, we have `∫⁻_𝓕 f ∂μ ≤ ∫⁻_S f ∂μ`! -/
theorem fundamentalDomain_lintegral_le_of_cover {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul G] {Γ : Subgroup G} [Countable Γ]
    {μ : Measure G} [μ.IsMulLeftInvariant]
    {𝓕 S : Set G} (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (hS : MeasurableSet S)
    (hcov : ∀ g : G, ∃ γ ∈ Γ, ∃ s ∈ S, g = γ * s)
    {f : G → ℝ≥0∞} (hf : Measurable f) (hinv : ∀ γ ∈ Γ, ∀ g : G, f (γ * g) = f g) :
    ∫⁻ g in 𝓕, f g ∂μ ≤ ∫⁻ g in S, f g ∂μ := by
  have hS_sub : 𝓕 ⊆ ⋃ γ : Γ, (γ : G) • S := by
    intro g _
    obtain ⟨γ, hγ, s, hs, rfl⟩ := hcov g
    exact Set.mem_iUnion.mpr ⟨⟨γ, hγ⟩, ⟨s, hs, rfl⟩⟩
  have h1 : ∫⁻ g in 𝓕, f g ∂μ ≤ ∑' γ : Γ, ∫⁻ g in 𝓕 ∩ ((γ : G) • S), f g ∂μ := by
    calc ∫⁻ g in 𝓕, f g ∂μ
        = ∫⁻ g in ⋃ γ : Γ, 𝓕 ∩ ((γ : G) • S), f g ∂μ := by
            congr 2
            rw [← Set.inter_iUnion]
            exact (Set.inter_eq_left.mpr hS_sub).symm
      _ ≤ ∑' γ : Γ, ∫⁻ g in 𝓕 ∩ ((γ : G) • S), f g ∂μ :=
            lintegral_iUnion_le _ _
  have h2' : ∀ γ : Γ, ∫⁻ g in 𝓕 ∩ ((γ : G) • S), f g ∂μ =
      ∫⁻ s, (((γ⁻¹ : Γ) • 𝓕) ∩ S).indicator f s ∂μ := by
    intro γ
    have hpre : (fun s : G => (γ : G) * s) ⁻¹' (𝓕 ∩ ((γ : G) • S)) =
        ((γ⁻¹ : Γ) • 𝓕) ∩ S := by
      ext s
      simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_smul_set]
      constructor
      · rintro ⟨h1, ⟨t, ht, hgt⟩⟩
        have hts : t = s := mul_left_cancel hgt
        subst hts
        refine ⟨⟨(γ : G) * t, h1, ?_⟩, ht⟩
        change (γ : G)⁻¹ * ((γ : G) * t) = t; group
      · rintro ⟨⟨x, hx, hxs⟩, hs⟩
        have hgx : (γ : G) * s = x := by
          rw [← hxs]; change (γ : G) * ((γ : G)⁻¹ * x) = x; group
        exact ⟨hgx.symm ▸ hx, ⟨s, hs, rfl⟩⟩
    have hmp := MeasureTheory.measurePreserving_mul_left μ (γ : G)
    have hnm : NullMeasurableSet (((γ⁻¹ : Γ) • 𝓕) ∩ S) μ :=
      (h𝓕.nullMeasurableSet.smul γ⁻¹).inter hS.nullMeasurableSet
    rw [← hmp.setLIntegral_comp_preimage_emb (measurableEmbedding_mulLeft (γ : G)) f
      (𝓕 ∩ ((γ : G) • S)), hpre, ← lintegral_indicator₀ hnm]
    refine lintegral_congr fun s => ?_
    by_cases hs : s ∈ ((γ⁻¹ : Γ) • 𝓕) ∩ S
    · simp only [Set.indicator_of_mem hs]; exact hinv γ.1 γ.2 s
    · simp only [Set.indicator_of_notMem hs]
  have htsum : ∑' γ : Γ, ∫⁻ s, (((γ⁻¹ : Γ) • 𝓕) ∩ S).indicator f s ∂μ =
      ∫⁻ s, ∑' γ : Γ, (((γ⁻¹ : Γ) • 𝓕) ∩ S).indicator f s ∂μ := by
    symm
    refine lintegral_tsum fun γ => ?_
    exact hf.aemeasurable.indicator₀ ((h𝓕.nullMeasurableSet.smul γ⁻¹).inter hS.nullMeasurableSet)
  have hae_disj : ∀ᵐ s ∂μ, ∀ γ₁ γ₂ : Γ, γ₁ ≠ γ₂ →
      ¬ (s ∈ (γ₁⁻¹ : Γ) • 𝓕 ∧ s ∈ (γ₂⁻¹ : Γ) • 𝓕) := by
    rw [ae_all_iff]
    intro γ₁
    rw [ae_all_iff]
    intro γ₂
    by_cases hne : γ₁ = γ₂
    · exact Filter.Eventually.of_forall fun _ h => absurd hne h
    · have hne' : γ₁⁻¹ ≠ γ₂⁻¹ := fun h => hne (inv_injective h)
      have hdisj : AEDisjoint μ ((γ₁⁻¹ : Γ) • 𝓕) ((γ₂⁻¹ : Γ) • 𝓕) := h𝓕.aedisjoint hne'
      have hzero : μ (((γ₁⁻¹ : Γ) • 𝓕) ∩ ((γ₂⁻¹ : Γ) • 𝓕)) = 0 := hdisj
      filter_upwards [compl_mem_ae_iff.mpr hzero] with s hs _ hboth
      exact hs hboth
  have hae_le : ∀ᵐ s ∂μ,
      (∑' γ : Γ, (((γ⁻¹ : Γ) • 𝓕) ∩ S).indicator f s) ≤ S.indicator f s := by
    filter_upwards [hae_disj] with s hs
    by_cases hex : ∃ γ₀ : Γ, s ∈ ((γ₀⁻¹ : Γ) • 𝓕) ∩ S
    · obtain ⟨γ₀, hγ₀⟩ := hex
      rw [tsum_eq_single γ₀]
      · rw [Set.indicator_of_mem hγ₀, Set.indicator_of_mem hγ₀.2]
      · intro γ hγ
        refine Set.indicator_of_notMem (fun hmem => hs γ γ₀ hγ ⟨hmem.1, hγ₀.1⟩) _
    · push Not at hex
      have hzero : ∀ γ : Γ, (((γ⁻¹ : Γ) • 𝓕) ∩ S).indicator f s = 0 :=
        fun γ => Set.indicator_of_notMem (hex γ) _
      simp_rw [hzero]
      rw [tsum_zero]
      exact bot_le
  calc ∫⁻ g in 𝓕, f g ∂μ
      ≤ ∑' γ : Γ, ∫⁻ g in 𝓕 ∩ ((γ : G) • S), f g ∂μ := h1
    _ = ∑' γ : Γ, ∫⁻ s, (((γ⁻¹ : Γ) • 𝓕) ∩ S).indicator f s ∂μ := by simp_rw [h2']
    _ = ∫⁻ s, ∑' γ : Γ, (((γ⁻¹ : Γ) • 𝓕) ∩ S).indicator f s ∂μ := htsum
    _ ≤ ∫⁻ s, S.indicator f s ∂μ := lintegral_mono_ae hae_le
    _ = ∫⁻ s in S, f s ∂μ := lintegral_indicator hS f

/-- Covering volume comparison: if `G = Γ · S` and `𝓕` is a fundamental domain for `Γ \ G`,
then `μ 𝓕 ≤ μ S`. -/
theorem measure_fundamentalDomain_le_of_cover {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul G] {Γ : Subgroup G} [Countable Γ]
    {μ : Measure G} [μ.IsMulLeftInvariant]
    {𝓕 S : Set G} (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (hS : MeasurableSet S)
    (hcov : ∀ g : G, ∃ γ ∈ Γ, ∃ s ∈ S, g = γ * s) :
    μ 𝓕 ≤ μ S := by
  have h := fundamentalDomain_lintegral_le_of_cover h𝓕 hS hcov measurable_const
    (fun _ _ _ => rfl : ∀ γ ∈ Γ, ∀ g : G, (1 : ℝ≥0∞) = 1)
  simpa only [lintegral_const, one_mul, Measure.restrict_apply_univ] using h

/-- **Finite Haar Volume of a Unitary Siegel Set (`siegel_set_finite_volume`)**:
every `UnitaryIwasawaData` has strictly finite Haar volume `μ (SiegelSetU a Ω c K) < ⊤`. -/
theorem siegel_set_finite_volume {G : Type*} [Group G] [MeasurableSpace G]
    (D : UnitaryIwasawaData G) :
    D.μ (SiegelSetU D.a D.Ω D.c D.K) < ⊤ := by
  have h1 := D.disint_le (fun _ => 1) (fun _ => 1) measurable_const (fun _ _ _ _ _ _ => le_rfl)
  simp only [lintegral_const, one_mul, Measure.restrict_apply_univ] at h1
  have hcone := lintegral_siegelCone_inv_modulus_lt_top D.hd D.hc D.hr
  exact lt_of_le_of_lt h1 (ENNReal.mul_lt_top ENNReal.coe_lt_top hcone)

/-- **Unconditional Finite Volume of Unitary Fundamental Domains (`siegel_fundamental_domain_finite_volume`)**:
whenever a unitary Siegel set `SiegelSetU D.a D.Ω D.c D.K` covers `Γ \ G` (supplied by
`reduction_to_siegel_domain`), ANY fundamental domain `𝓕` of `Γ \ G` has strictly finite Haar
volume `μ 𝓕 ≤ μ (SiegelSetU D.a D.Ω D.c D.K) < ⊤`! -/
theorem siegel_fundamental_domain_finite_volume {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul G] {Γ : Subgroup G} [Countable Γ]
    (D : UnitaryIwasawaData G) [D.μ.IsMulLeftInvariant]
    (hcov : ∀ g : G, ∃ γ ∈ Γ, ∃ s ∈ SiegelSetU D.a D.Ω D.c D.K, g = γ * s)
    {𝓕 : Set G} (h𝓕 : IsFundamentalDomain Γ 𝓕 D.μ) :
    D.μ 𝓕 ≤ D.μ (SiegelSetU D.a D.Ω D.c D.K) ∧ D.μ 𝓕 < ⊤ := by
  have hle : D.μ 𝓕 ≤ D.μ (SiegelSetU D.a D.Ω D.c D.K) :=
    measure_fundamentalDomain_le_of_cover h𝓕 D.siegel_meas hcov
  exact ⟨hle, lt_of_le_of_lt hle (siegel_set_finite_volume D)⟩

/-- **Hyperbolic Parabolic Slice Finite Volume (`hyperbolic_parabolic_slice_finite_volume`)**
(matching `CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HyperbolicParabolicSiegelSetBound`):
if parabolic slices `S : ℤ → Set G` satisfy `ν (S j) ≤ Kc * exp(-2 d (M + 1) j)` for `j ≥ j₀`
with `Kc < ⊤`, `0 < d`, and cover a fundamental domain `𝓕` modulo `Γ`, then `ν 𝓕 < ⊤`. -/
theorem hyperbolic_parabolic_slice_finite_volume {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul G] {Γ : Subgroup G} [Countable Γ]
    {ν : Measure G} [ν.IsMulLeftInvariant]
    {d M : ℕ} (hd : 0 < d) (j₀ : ℤ)
    (S : ℤ → Set G) (hS_meas : ∀ j, MeasurableSet (S j))
    {Kc : ℝ≥0∞} (hKc : Kc < ⊤)
    (hvol : ∀ j : ℤ, j₀ ≤ j →
      ν (S j) ≤ Kc * ENNReal.ofReal (Real.exp (-(2 * (d : ℝ) * ((M : ℝ) + 1) * (j : ℝ)))))
    (hcov : ∀ g : G, ∃ γ ∈ Γ, ∃ j : ℤ, j₀ ≤ j ∧ γ * g ∈ S j)
    {𝓕 : Set G} (h𝓕 : IsFundamentalDomain Γ 𝓕 ν) :
    ν 𝓕 < ⊤ := by
  let S_tot : Set G := ⋃ k : ℕ, S (j₀ + (k : ℤ))
  have hStot_meas : MeasurableSet S_tot := MeasurableSet.iUnion fun k => hS_meas (j₀ + k)
  have hcov' : ∀ g : G, ∃ γ ∈ Γ, ∃ s ∈ S_tot, g = γ * s := by
    intro g
    obtain ⟨γ, hγ, j, hj, hmem⟩ := hcov g
    refine ⟨γ⁻¹, Γ.inv_mem hγ, γ * g, ?_, by group⟩
    refine Set.mem_iUnion.mpr ⟨(j - j₀).toNat, ?_⟩
    have hj_eq : j₀ + ((j - j₀).toNat : ℤ) = j := by
      have : ((j - j₀).toNat : ℤ) = j - j₀ := Int.toNat_of_nonneg (sub_nonneg.mpr hj)
      omega
    rwa [hj_eq]
  have hle : ν 𝓕 ≤ ν S_tot := measure_fundamentalDomain_le_of_cover h𝓕 hStot_meas hcov'
  have hα : 0 < 2 * (d : ℝ) * ((M : ℝ) + 1) := by positivity
  have hsum : ν S_tot ≤ Kc * ∑' k : ℕ,
      ENNReal.ofReal (Real.exp (-(2 * (d : ℝ) * ((M : ℝ) + 1)) * ((j₀ + (k : ℤ) : ℤ) : ℝ))) := by
    calc ν S_tot
        ≤ ∑' k : ℕ, ν (S (j₀ + (k : ℤ))) := measure_iUnion_le _
      _ ≤ ∑' k : ℕ, Kc * ENNReal.ofReal
            (Real.exp (-(2 * (d : ℝ) * ((M : ℝ) + 1)) * ((j₀ + (k : ℤ) : ℤ) : ℝ))) := by
            refine ENNReal.tsum_le_tsum fun k => ?_
            have hk := hvol (j₀ + (k : ℤ)) (by omega)
            have hexp : -(2 * (d : ℝ) * ((M : ℝ) + 1) * ((j₀ + (k : ℤ) : ℤ) : ℝ)) =
                -(2 * (d : ℝ) * ((M : ℝ) + 1)) * ((j₀ + (k : ℤ) : ℤ) : ℝ) := by ring
            rwa [hexp] at hk
      _ = Kc * ∑' k : ℕ, ENNReal.ofReal
            (Real.exp (-(2 * (d : ℝ) * ((M : ℝ) + 1)) * ((j₀ + (k : ℤ) : ℤ) : ℝ))) :=
            ENNReal.tsum_mul_left
  exact lt_of_le_of_lt (hle.trans hsum) (ENNReal.mul_lt_top hKc (tsum_parabolic_slice_exp_lt_top hα j₀))

/-! ### 5B. Exact Totally Real Lattice Fundamental Domain Volume & Character Orthogonality -/

/-- The additive scaling map `𝓞 F →+ (InfinitePlace F → ℝ)` sending `r ↦ (w ↦ ρ w (N * r))`. -/
def realLatticeScaleMap {F : Type*} [Field F] [NumberField F]
    (ρ : InfinitePlace F → (F →+* ℝ)) (N : ℕ) : 𝓞 F →+ (InfinitePlace F → ℝ) where
  toFun r := fun w => ρ w ((N : F) * (r : F))
  map_zero' := by ext w; simp
  map_add' a b := by ext w; simp [mul_add]

/-- The real-embedded level-`N` lattice `latR ρ N ≤ (InfinitePlace F → ℝ)`. -/
def realIntLattice {F : Type*} [Field F] [NumberField F]
    (ρ : InfinitePlace F → (F →+* ℝ)) (N : ℕ) : AddSubgroup (InfinitePlace F → ℝ) :=
  (realLatticeScaleMap ρ N).range

lemma embedding_bijective_of_totallyReal {F : Type*} [Field F] [NumberField F]
    (hF : IsTotallyReal F) :
    Function.Bijective (fun w : InfinitePlace F => (w.embedding : F →+* ℂ)) := by
  constructor
  · intro w w' h
    have := congrArg InfinitePlace.mk h
    simpa using this
  · intro φ
    have hr : ComplexEmbedding.IsReal φ :=
      InfinitePlace.isReal_mk_iff.1 (hF.isReal (InfinitePlace.mk φ))
    exact ⟨InfinitePlace.mk φ, InfinitePlace.embedding_mk_eq_of_isReal hr⟩

def totallyRealPlaceEquiv {F : Type*} [Field F] [NumberField F]
    (hF : IsTotallyReal F) : InfinitePlace F ≃ (F →ₐ[ℚ] ℂ) :=
  (Equiv.ofBijective _ (embedding_bijective_of_totallyReal hF)).trans (RingHom.equivRatAlgHom F ℂ)

lemma card_infinitePlaces_of_totallyReal {F : Type*} [Field F] [NumberField F]
    (hF : IsTotallyReal F) :
    Fintype.card (InfinitePlace F) = Module.finrank ℚ F := by
  rw [Fintype.card_congr (totallyRealPlaceEquiv hF), AlgHom.card]

/-- Existence of an integral `ℤ`-basis of `𝓞 F` indexed by `InfinitePlace F` whose embedding
determinant squared equals `NumberField.discr F`. -/
theorem exists_totallyReal_integral_basis {F : Type*} [Field F] [NumberField F]
    [DecidableEq (InfinitePlace F)] (hF : IsTotallyReal F)
    (ρ : InfinitePlace F → (F →+* ℝ))
    (hρ : ∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) :
    ∃ B : Module.Basis (InfinitePlace F) ℤ (𝓞 F),
      (Matrix.det (Matrix.of fun i w => ρ w ((B i : 𝓞 F) : F))) ^ 2 = (NumberField.discr F : ℝ) := by
  classical
  have hc : Fintype.card (Module.Free.ChooseBasisIndex ℤ (𝓞 F)) = Fintype.card (InfinitePlace F) := by
    rw [card_infinitePlaces_of_totallyReal hF, ← Module.finrank_eq_card_chooseBasisIndex,
      RingOfIntegers.rank]
  let e0 := Fintype.equivOfCardEq hc
  let bq := (NumberField.integralBasis F).reindex e0
  refine ⟨(RingOfIntegers.basis F).reindex e0, ?_⟩
  have h := Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two ℚ ℂ bq (totallyRealPlaceEquiv hF)
  have hd : Algebra.discr ℚ bq = (NumberField.discr F : ℚ) := by
    rw [NumberField.coe_discr]
    have h0 := Algebra.discr_reindex ℚ (NumberField.integralBasis F) e0
    rwa [← Module.Basis.coe_reindex] at h0
  have hM : Algebra.embeddingsMatrixReindex ℚ ℂ bq (totallyRealPlaceEquiv hF) =
      (Matrix.of fun i w => ρ w (((RingOfIntegers.basis F).reindex e0 i : 𝓞 F) : F)).map
        Complex.ofRealHom := by
    ext i w
    simp [Algebra.embeddingsMatrixReindex, Algebra.embeddingsMatrix, totallyRealPlaceEquiv, bq, hρ,
      NumberField.integralBasis_apply, Module.Basis.reindex_apply]
  rw [hM, hd, ← RingHom.mapMatrix_apply, ← RingHom.map_det] at h
  have h2 : (((NumberField.discr F : ℝ)) : ℂ) = (((Matrix.det (Matrix.of fun i w =>
      ρ w (((RingOfIntegers.basis F).reindex e0 i : 𝓞 F) : F))) ^ 2 : ℝ) : ℂ) := by
    simpa using h
  exact_mod_cast h2.symm

/-- Sum of real embeddings of any algebraic integer `a : 𝓞 F` is an integer (`trace_eq_sum_embeddings`). -/
theorem sum_places_int_of_totallyReal {F : Type*} [Field F] [NumberField F]
    (hF : IsTotallyReal F) (ρ : InfinitePlace F → (F →+* ℝ))
    (hρ : ∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) (a : 𝓞 F) :
    ∃ z : ℤ, ∑ w : InfinitePlace F, ρ w (a : F) = (z : ℝ) := by
  obtain ⟨z, hz⟩ : ∃ z : ℤ, algebraMap ℤ ℚ z = Algebra.trace ℚ F (a : F) :=
    IsIntegrallyClosed.isIntegral_iff.1
      (Algebra.isIntegral_trace (R := ℤ) (L := ℚ) (F := F) (RingOfIntegers.isIntegral_coe a))
  refine ⟨z, ?_⟩
  have h := trace_eq_sum_embeddings (K := ℚ) (L := F) ℂ (x := (a : F))
  rw [← (totallyRealPlaceEquiv hF).sum_comp, ← hz] at h
  have h2 : ((z : ℝ) : ℂ) = ((∑ w : InfinitePlace F, ρ w (a : F) : ℝ) : ℂ) := by
    push_cast
    simp only [hρ]
    simpa [totallyRealPlaceEquiv] using h
  exact_mod_cast h2.symm

/-- Non-constant additive character orthogonality on any fundamental domain `D` of
`realIntLattice ρ N` (following `LatticeFundamentalDomainVolume.lean`, used for Fourier-mode
vanishing in unipotent constant-term extraction). -/
theorem lattice_fundamental_domain_char_integral_zero {F : Type*} [Field F] [NumberField F]
    (hF : IsTotallyReal F) (ρ : InfinitePlace F → (F →+* ℝ))
    (hρ : ∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x)
    (N : ℕ) (D : Set (InfinitePlace F → ℝ))
    (hD : IsAddFundamentalDomain (realIntLattice ρ N) D volume)
    (β : F) (hβ : β ≠ 0) (hint : ∃ r : 𝓞 F, (r : F) = (N : F) * β) :
    ∫ x in D, Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) *
      ((∑ w : InfinitePlace F, ρ w β * x w : ℝ) : ℂ)) = 0 := by
  classical
  obtain ⟨B, -⟩ := exists_totallyReal_integral_basis hF ρ hρ
  have : Countable (𝓞 F) := B.equivFun.toEquiv.injective.countable
  have : Countable (realIntLattice ρ N) :=
    (Set.countable_range (realLatticeScaleMap ρ N)).to_subtype
  let f : (InfinitePlace F → ℝ) → ℂ := fun x =>
    Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) *
      ((∑ w : InfinitePlace F, ρ w β * x w : ℝ) : ℂ))
  have hadd : ∀ x y : InfinitePlace F → ℝ, f (x + y) = f x * f y := by
    intro x y
    simp only [f, Pi.add_apply, mul_add, Finset.sum_add_distrib, Complex.ofReal_add, mul_add,
      Complex.exp_add]
  have hper : ∀ g : realIntLattice ρ N, ∀ x, f (g +ᵥ x) = f x := by
    rintro ⟨_, ⟨r, rfl⟩⟩ x
    change f ((fun w => ρ w ((N : F) * (r : F))) + x) = f x
    rw [hadd]
    suffices h1 : f (fun w => ρ w ((N : F) * (r : F))) = 1 by rw [h1, one_mul]
    obtain ⟨s, hs⟩ := hint
    obtain ⟨z, hz⟩ := sum_places_int_of_totallyReal hF ρ hρ (s * r)
    have hsr : ((s * r : 𝓞 F) : F) = (N : F) * β * (r : F) := by
      rw [← hs]
      exact map_mul (algebraMap (𝓞 F) F) s r
    have hsum : ∑ w : InfinitePlace F, ρ w β * ρ w ((N : F) * (r : F)) = (z : ℝ) := by
      rw [← hz]
      refine Finset.sum_congr rfl fun w _ => ?_
      rw [← map_mul, hsr]
      congr 1; ring
    simp only [f, hsum]
    have harg : (2 * (Real.pi : ℂ) * Complex.I) * ((z : ℝ) : ℂ) =
        (z : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
      push_cast; ring
    rw [harg, Complex.exp_int_mul_two_pi_mul_I]
  obtain ⟨w0⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hβw : ρ w0 β ≠ 0 := (map_ne_zero _).2 hβ
  let x0 : InfinitePlace F → ℝ := Pi.single w0 (1 / (2 * ρ w0 β))
  have hx0 : f x0 = -1 := by
    have hsum : ∑ w : InfinitePlace F, ρ w β * x0 w = 1 / 2 := by
      rw [Finset.sum_eq_single w0]
      · simp only [x0, Pi.single_eq_same]
        field_simp [hβw]
      · intro w _ hw; simp [x0, Pi.single_eq_of_ne hw]
      · intro hm; exact absurd (Finset.mem_univ w0) hm
    simp only [f, hsum]
    have harg : (2 * (Real.pi : ℂ) * Complex.I) * (((1 / 2 : ℝ) : ℂ)) = (Real.pi : ℂ) * Complex.I := by
      push_cast; ring
    rw [harg, Complex.exp_pi_mul_I]
  have hD' : IsAddFundamentalDomain (realIntLattice ρ N) (x0 +ᵥ D) volume := hD.vadd_of_comm x0
  have heq : ∫ x in x0 +ᵥ D, f x = ∫ x in D, f x := hD'.setIntegral_eq hD hper
  have htr : ∫ x in x0 +ᵥ D, f x = ∫ x in D, f (x0 + x) := by
    have := (measurePreserving_add_left (volume : Measure (InfinitePlace F → ℝ)) x0).setIntegral_image_emb
      (measurableEmbedding_addLeft x0) f D
    rw [← this, ← Set.image_vadd]; rfl
  have hmul : ∫ x in D, f (x0 + x) = - ∫ x in D, f x := by
    simp_rw [hadd, hx0]
    rw [integral_const_mul]
    ring
  have h2 : ∫ x in D, f x = - ∫ x in D, f x := by rw [← hmul, ← htr, heq]
  have h3 : (2 : ℂ) * ∫ x in D, f x = 0 := by linear_combination h2
  exact (mul_eq_zero.mp h3).resolve_left (by norm_num)

/-- **Exact Number-Field Lattice Fundamental Domain Volume (`lattice_fundamental_domain_volume`)**
(following `CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LatticeFundamentalDomainVolume`):
for any totally real number field `F`, real embeddings `ρ`, and `N > 0`, `realIntLattice ρ N`
admits a fundamental domain `D` in `InfinitePlace F → ℝ`, is countable, and EVERY fundamental
domain `D` satisfies `volume D = ENNReal.ofReal (N^[F:ℚ] * √|discr F|)`. -/
theorem lattice_fundamental_domain_volume {F : Type*} [Field F] [NumberField F]
    (hF : IsTotallyReal F) (ρ : InfinitePlace F → (F →+* ℝ))
    (hρ : ∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x)
    {N : ℕ} (hN : 0 < N) :
    (∃ D : Set (InfinitePlace F → ℝ), IsAddFundamentalDomain (realIntLattice ρ N) D volume) ∧
    Countable (realIntLattice ρ N) ∧
    ∀ D : Set (InfinitePlace F → ℝ), IsAddFundamentalDomain (realIntLattice ρ N) D volume →
      volume D = ENNReal.ofReal ((N : ℝ) ^ Module.finrank ℚ F * Real.sqrt |(NumberField.discr F : ℝ)|) := by
  classical
  obtain ⟨B, hB⟩ := exists_totallyReal_integral_basis hF ρ hρ
  let M : Matrix (InfinitePlace F) (InfinitePlace F) ℝ :=
    Matrix.of fun i w => ρ w ((B i : 𝓞 F) : F)
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hdisc : (NumberField.discr F : ℝ) ≠ 0 := by exact_mod_cast NumberField.discr_ne_zero F
  have hdet : M.det ≠ 0 := by
    intro h0; apply hdisc; rw [← hB, h0]; simp
  have hAdet : ((N : ℝ) • M).det ≠ 0 := by
    rw [Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ hN') hdet
  have hl : LinearIndependent ℝ ((N : ℝ) • M).row :=
    Matrix.linearIndependent_rows_iff_isUnit.2
      ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hAdet))
  let b : Module.Basis (InfinitePlace F) ℝ (InfinitePlace F → ℝ) :=
    basisOfLinearIndependentOfCardEqFinrank hl (by simp)
  have hb_row : ∀ i : InfinitePlace F, b i = ((N : ℝ) • M) i := fun i => by
    rw [coe_basisOfLinearIndependentOfCardEqFinrank]; rfl
  have hb_apply : ∀ i : InfinitePlace F, b i = realLatticeScaleMap ρ N (B i) := by
    intro i
    rw [hb_row i]
    ext w
    simp [realLatticeScaleMap, M]
  have hspan : realIntLattice ρ N = (Submodule.span ℤ (Set.range b)).toAddSubgroup := by
    rw [realIntLattice, Submodule.span_int_eq_addSubgroupClosure]
    apply le_antisymm
    · rintro _ ⟨r, rfl⟩
      rw [← B.sum_repr r, map_sum]
      refine AddSubgroup.sum_mem _ fun i _ => ?_
      rw [map_zsmul, ← hb_apply]
      exact AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure (Set.mem_range_self i)) _
    · rw [AddSubgroup.closure_le]
      rintro _ ⟨i, rfl⟩
      exact ⟨B i, (hb_apply i).symm⟩
  have hfd : IsAddFundamentalDomain (realIntLattice ρ N) (ZSpan.fundamentalDomain b) volume := by
    rw [hspan]
    exact ZSpan.isAddFundamentalDomain' b volume
  have hcount : Countable (realIntLattice ρ N) := by
    have : Countable (𝓞 F) := B.equivFun.toEquiv.injective.countable
    rw [realIntLattice]
    exact (Set.countable_range (realLatticeScaleMap ρ N)).to_subtype
  refine ⟨⟨_, hfd⟩, hcount, fun D hD => ?_⟩
  rw [hD.measure_eq hfd, ZSpan.volume_fundamentalDomain]
  have hof : Matrix.of (b : InfinitePlace F → InfinitePlace F → ℝ) = (N : ℝ) • M := by
    ext i w
    change (b i) w = ((N : ℝ) • M) i w
    rw [hb_row i]
  rw [hof, Matrix.det_smul, card_infinitePlaces_of_totallyReal hF, abs_mul,
    abs_of_nonneg (pow_nonneg (Nat.cast_nonneg N) _)]
  congr 2
  rw [← hB, abs_of_nonneg (sq_nonneg M.det), Real.sqrt_sq_eq_abs]

end FiniteVolumeAndLatticeFD

/-! ## Section 6: Unconditional `siegel_envelope_integrable` (Ready for Wave 2 `AdelicWeilTheta` & `SiegelEisenstein`) -/

section SiegelEnvelopeIntegrable

/-- **Automatic `SiegelWeilCore.SiegelSetEnvelope` on Any Finite-Volume Unitary Siegel Set**:
because `μ (SiegelSetU D.a D.Ω D.c D.K) < ⊤` (`siegel_set_finite_volume`), any measurable
`UnitaryHeightFn H` gives a concrete `SiegelWeilCore.SiegelSetEnvelope` on `(SiegelSetU, μ)` with
`critExp = 0`! -/
def siegelSetEnvelope_of_unitaryIwasawa {G : Type*} [Group G] [MeasurableSpace G]
    (D : UnitaryIwasawaData G) (H : UnitaryHeightFn G)
    (hH_meas : AEStronglyMeasurable (fun g => H g) (D.μ.restrict (SiegelSetU D.a D.Ω D.c D.K))) :
    RHDirect.SiegelWeilCore.SiegelSetEnvelope (D.μ.restrict (SiegelSetU D.a D.Ω D.c D.K)) where
  H := fun g => H g
  H_meas := hH_meas
  H_ge_one := Filter.Eventually.of_forall fun g => H.one_le g
  critExp := 0
  vol_integrable := by
    have hfin : (D.μ.restrict (SiegelSetU D.a D.Ω D.c D.K)) Set.univ < ⊤ := by
      rw [Measure.restrict_apply_univ]
      exact siegel_set_finite_volume D
    have : IsFiniteMeasure (D.μ.restrict (SiegelSetU D.a D.Ω D.c D.K)) := ⟨hfin⟩
    have h1 : (fun g : G => (H g) ^ (-(0 : ℝ))) = fun _ => (1 : ℝ) := by
      ext g; simp
    rw [h1]
    exact integrable_const (1 : ℝ)

/-- **Unconditional Rapidly Decaying Envelope Integrability over Unitary Siegel Sets (`siegel_envelope_integrable`)**:
on ANY unitary Siegel set `S = SiegelSetU D.a D.Ω D.c D.K` (`D : UnitaryIwasawaData G`) equipped
with a measurable `UnitaryHeightFn H`, EVERY measurable function `f : G → ℂ` satisfying a decay
bound `‖f g‖ ≤ C * (H g)^(-decayExp)` (`0 ≤ C`, `0 ≤ decayExp`) is Bochner `IntegrableOn f S D.μ`
with explicit `L¹` ceiling `‖∫ g in S, f g ∂D.μ‖ ≤ C * (D.μ S).toReal`! -/
theorem siegel_envelope_integrable {G : Type*} [Group G] [MeasurableSpace G]
    (D : UnitaryIwasawaData G) (H : UnitaryHeightFn G)
    (hH_meas : AEStronglyMeasurable (fun g => H g) (D.μ.restrict (SiegelSetU D.a D.Ω D.c D.K)))
    {f : G → ℂ} {C decayExp : ℝ} (hC : 0 ≤ C) (hExp : 0 ≤ decayExp)
    (hf_meas : AEStronglyMeasurable f (D.μ.restrict (SiegelSetU D.a D.Ω D.c D.K)))
    (hf_bound : ∀ᵐ g ∂(D.μ.restrict (SiegelSetU D.a D.Ω D.c D.K)),
      ‖f g‖ ≤ C * (H g) ^ (-decayExp)) :
    IntegrableOn f (SiegelSetU D.a D.Ω D.c D.K) D.μ ∧
      ‖∫ g in SiegelSetU D.a D.Ω D.c D.K, f g ∂D.μ‖ ≤
        C * (D.μ (SiegelSetU D.a D.Ω D.c D.K)).toReal := by
  let Env := siegelSetEnvelope_of_unitaryIwasawa D H hH_meas
  have hres := RHDirect.SiegelWeilCore.thetaKernel_integrable_of_siegel_envelope Env hC
    (show Env.critExp ≤ decayExp from hExp) hf_meas hf_bound
  refine ⟨hres.1, ?_⟩
  have h1 : ∫ g in SiegelSetU D.a D.Ω D.c D.K, (Env.H g) ^ (-Env.critExp) ∂D.μ =
      (D.μ (SiegelSetU D.a D.Ω D.c D.K)).toReal := by
    have hfun : (fun g : G => (Env.H g) ^ (-Env.critExp)) = fun _ => (1 : ℝ) := by
      ext g; simp [Env, siegelSetEnvelope_of_unitaryIwasawa]
    rw [hfun, setIntegral_const, smul_eq_mul, mul_one, Measure.real]
  rw [h1] at hres
  exact hres.2.2

/-- **Cuspidal (Rapid-Decay) × Moderate-Growth Product Integrability on Unitary Siegel Sets
(`siegel_cuspidal_times_moderate_integrable`)**:
if `φ` has rapid decay (`∀ N : ℕ, ∃ C, ∀ g ∈ S, ‖φ g‖ * (H g)^N ≤ C`) and `ψ` has moderate growth
(`‖ψ g‖ ≤ C_ψ * (H g)^M`), then `φ * ψ` is Bochner `IntegrableOn` `S` (essential for Petersson
inner products and doubling zeta integrals in M1 Wave 2)! -/
theorem siegel_cuspidal_times_moderate_integrable {G : Type*} [Group G] [MeasurableSpace G]
    (D : UnitaryIwasawaData G) (H : UnitaryHeightFn G)
    (hH_meas : AEStronglyMeasurable (fun g => H g) (D.μ.restrict (SiegelSetU D.a D.Ω D.c D.K)))
    {φ ψ : G → ℂ}
    (hmeas : AEStronglyMeasurable (fun g => φ g * ψ g) (D.μ.restrict (SiegelSetU D.a D.Ω D.c D.K)))
    (hrapid : ∀ N : ℕ, ∃ C_φ : ℝ, 0 ≤ C_φ ∧
      ∀ g ∈ SiegelSetU D.a D.Ω D.c D.K, ‖φ g‖ * (H g) ^ N ≤ C_φ)
    {M : ℕ} {C_ψ : ℝ} (hCψ : 0 ≤ C_ψ)
    (hmod : ∀ g ∈ SiegelSetU D.a D.Ω D.c D.K, ‖ψ g‖ ≤ C_ψ * (H g) ^ M) :
    IntegrableOn (fun g => φ g * ψ g) (SiegelSetU D.a D.Ω D.c D.K) D.μ := by
  obtain ⟨C_φ, hCφ, hφb⟩ := hrapid M
  have hdom : ∀ᵐ g ∂(D.μ.restrict (SiegelSetU D.a D.Ω D.c D.K)),
      ‖φ g * ψ g‖ ≤ (C_φ * C_ψ) * (H g) ^ (-(0 : ℝ)) := by
    rw [ae_restrict_iff' D.siegel_meas]
    refine Filter.Eventually.of_forall fun g hg => ?_
    simp only [neg_zero, Real.rpow_zero, mul_one, norm_mul]
    have hpos : 0 < (H g) ^ M := pow_pos (H.pos g) M
    have h1 := hφb g hg
    have h2 := hmod g hg
    have h3 : ‖φ g‖ ≤ C_φ / (H g) ^ M := (le_div_iff₀ hpos).mpr h1
    calc ‖φ g‖ * ‖ψ g‖
        ≤ (C_φ / (H g) ^ M) * (C_ψ * (H g) ^ M) :=
          mul_le_mul h3 h2 (norm_nonneg _) (div_nonneg hCφ hpos.le)
      _ = C_φ * C_ψ := by field_simp [hpos.ne']
  exact (siegel_envelope_integrable D H hH_meas (mul_nonneg hCφ hCψ) le_rfl hmeas hdom).1

/-- **Weil-Range Torus-Power Bochner Integrability on `SiegelSetU` (`siegel_torus_envelope_integrable`)**:
for ANY `D : UnitaryIwasawaData G` and ANY dual-pair rank `n` in Weil's convergent range
(`D.r = 0 ∨ n + D.r < D.m`), every `AEStronglyMeasurable` kernel `f : G → ℂ` dominated on
`SiegelSetU D.a D.Ω D.c D.K` by `C * ∏ i, t i ^ (D.d * (2 * n))` is Bochner `IntegrableOn`
`SiegelSetU D.a D.Ω D.c D.K`! Directly ready for `Stage14M1_AdelicWeilTheta` and
`Stage14M1_SiegelEisenstein`! -/
theorem siegel_torus_envelope_integrable {G : Type*} [Group G] [MeasurableSpace G]
    (D : UnitaryIwasawaData G) {n : ℕ} (hweil : D.r = 0 ∨ n + D.r < D.m)
    {C : ℝ} (hC : 0 ≤ C) {f : G → ℂ}
    (hf_meas : AEStronglyMeasurable f (D.μ.restrict (SiegelSetU D.a D.Ω D.c D.K)))
    (hf_bound : ∀ p ∈ D.Ω, ∀ t ∈ SiegelCone D.r D.c, ∀ k ∈ D.K,
      ‖f (p * D.a t * k)‖ ≤ C * ∏ i : Fin D.r, t i ^ (D.d * (2 * n))) :
    IntegrableOn f (SiegelSetU D.a D.Ω D.c D.K) D.μ := by
  refine ⟨hf_meas, ?_⟩
  unfold HasFiniteIntegral
  have hmeas_h : Measurable (fun t : Fin D.r → ℝ =>
      ENNReal.ofReal (C * ∏ i : Fin D.r, t i ^ (D.d * (2 * n)))) :=
    ENNReal.measurable_ofReal.comp
      (measurable_const.mul (Finset.measurable_prod _ fun i _ => (measurable_pi_apply i).pow_const _))
  have hle := D.disint_le (fun g => ‖f g‖ₑ)
    (fun t => ENNReal.ofReal (C * ∏ i : Fin D.r, t i ^ (D.d * (2 * n)))) hmeas_h
    (fun p hp t ht k hk => by
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (hf_bound p hp t ht k hk))
  have hsplit : ∫⁻ t in SiegelCone D.r D.c,
      ENNReal.ofReal (C * ∏ i : Fin D.r, t i ^ (D.d * (2 * n))) *
        ENNReal.ofReal ((siegelModulus D.d D.m t * ∏ i : Fin D.r, t i)⁻¹) =
      ENNReal.ofReal C * ∫⁻ t in SiegelCone D.r D.c,
        ENNReal.ofReal (∏ i : Fin D.r, t i ^ (D.d * (2 * n))) *
          ENNReal.ofReal ((siegelModulus D.d D.m t * ∏ i : Fin D.r, t i)⁻¹) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine setLIntegral_congr_fun (measurableSet_siegelCone D.hc) fun t _ => ?_
    rw [ENNReal.ofReal_mul hC, mul_assoc]
  have hcone := lintegral_siegelCone_weil_range_lt_top (d := D.d) (m := D.m) (r := D.r) (n := n)
    D.hd D.hc hweil
  rw [hsplit] at hle
  exact lt_of_le_of_lt hle
    (ENNReal.mul_lt_top ENNReal.coe_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hcone))

/-- **Fundamental-Domain Weil-Range Bochner Integrability (`siegel_fundamental_domain_weil_integrable`)**:
if `f : G → ℂ` is left-`Γ`-invariant, `AEStronglyMeasurable`, and dominated on the covering Siegel
set `SiegelSetU` by `C * ∏ i, t i ^ (D.d * (2 * n))` with `D.r = 0 ∨ n + D.r < D.m`, then `f` is
Bochner `IntegrableOn f 𝓕 D.μ` over ANY fundamental domain `𝓕` of `Γ \ G`! -/
theorem siegel_fundamental_domain_weil_integrable {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul G] {Γ : Subgroup G} [Countable Γ]
    (D : UnitaryIwasawaData G) [D.μ.IsMulLeftInvariant]
    (hcov : ∀ g : G, ∃ γ ∈ Γ, ∃ s ∈ SiegelSetU D.a D.Ω D.c D.K, g = γ * s)
    {𝓕 : Set G} (h𝓕 : IsFundamentalDomain Γ 𝓕 D.μ)
    {n : ℕ} (hweil : D.r = 0 ∨ n + D.r < D.m)
    {C : ℝ} (hC : 0 ≤ C) {f : G → ℂ}
    (hf_meas : Measurable f)
    (hf_inv : ∀ γ ∈ Γ, ∀ g : G, f (γ * g) = f g)
    (hf_bound : ∀ p ∈ D.Ω, ∀ t ∈ SiegelCone D.r D.c, ∀ k ∈ D.K,
      ‖f (p * D.a t * k)‖ ≤ C * ∏ i : Fin D.r, t i ^ (D.d * (2 * n))) :
    IntegrableOn f 𝓕 D.μ := by
  have hS_int : IntegrableOn f (SiegelSetU D.a D.Ω D.c D.K) D.μ :=
    siegel_torus_envelope_integrable D hweil hC hf_meas.aestronglyMeasurable hf_bound
  refine ⟨hf_meas.aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral
  have hle := fundamentalDomain_lintegral_le_of_cover h𝓕 D.siegel_meas hcov
    hf_meas.enorm (fun γ hγ g => by rw [hf_inv γ hγ g])
  exact lt_of_le_of_lt hle hS_int.2

/-- **Unified Gaussian-Theta × Unitary Siegel-Domain Bochner Integrability
(`siegel_gaussian_theta_integrable`)**:
combines `Stage3ThetaSiegelBridge.thetaKernel_integrable_of_gaussian_theta_bound` with our
unconditional `siegel_fundamental_domain_finite_volume`: on any fundamental domain `𝓕` covered
by `SiegelSetU D.a D.Ω D.c D.K`, any Gaussian-theta-dominated kernel
`‖θ g‖ ≤ C * Θ_{L(g)}(t) * H_lat(g)^(-decayExp)` with `rank(L(g)) = r_lat ≤ decayExp` is
Bochner `IntegrableOn θ 𝓕 D.μ` with an explicit `L¹` ceiling controlled by `(D.μ 𝓕).toReal`! -/
theorem siegel_gaussian_theta_integrable {G E : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul G] {Γ : Subgroup G} [Countable Γ]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (D : UnitaryIwasawaData G) [D.μ.IsMulLeftInvariant]
    (hcov : ∀ g : G, ∃ γ ∈ Γ, ∃ s ∈ SiegelSetU D.a D.Ω D.c D.K, g = γ * s)
    {𝓕 : Set G} (h𝓕 : IsFundamentalDomain Γ 𝓕 D.μ)
    (L : G → Submodule ℤ E) [∀ g, DiscreteTopology (L g)]
    (hL0 : ∀ g, L g ≠ ⊥) {r_lat : ℕ} (hrk : ∀ g, RHDirect.ArakelovCovolume.rk (L g) = r_lat)
    {t decayExp C : ℝ} (ht : 0 < t) (hC : 0 ≤ C) (hExp : (r_lat : ℝ) ≤ decayExp)
    (hmeas : AEStronglyMeasurable (fun g => latticeHeight (L g)) (D.μ.restrict 𝓕))
    {θ : G → ℂ} (hθm : AEStronglyMeasurable θ (D.μ.restrict 𝓕))
    (hθb : ∀ᵐ g ∂(D.μ.restrict 𝓕),
      ‖θ g‖ ≤ C * RHDirect.Stage3ThetaSiegelBridge.latticeTheta (L g) t *
        (latticeHeight (L g)) ^ (-decayExp)) :
    IntegrableOn θ 𝓕 D.μ ∧
      ‖∫ g in 𝓕, θ g ∂D.μ‖ ≤
        (C * (1 + RHDirect.Stage3ThetaSiegelBridge.thetaConst r_lat *
          (1 + (Real.sqrt t) ^ (-(r_lat : ℝ))))) * (D.μ 𝓕).toReal := by
  have hfin : (D.μ.restrict 𝓕) Set.univ < ⊤ := by
    rw [Measure.restrict_apply_univ]
    exact (siegel_fundamental_domain_finite_volume D hcov h𝓕).2
  have : IsFiniteMeasure (D.μ.restrict 𝓕) := ⟨hfin⟩
  have hint0 : Integrable
      (fun g : G => (max (1 : ℝ) (RHDirect.Stage2SiegelReduction.lambda1 (L g))⁻¹) ^ (-(0 : ℝ)))
      (D.μ.restrict 𝓕) := by
    have h1 : (fun g : G => (max (1 : ℝ) (RHDirect.Stage2SiegelReduction.lambda1 (L g))⁻¹) ^ (-(0 : ℝ))) =
        fun _ => (1 : ℝ) := by ext g; simp
    rw [h1]
    exact integrable_const (1 : ℝ)
  have hres := RHDirect.Stage3ThetaSiegelBridge.thetaKernel_integrable_of_gaussian_theta_bound
    (μ := D.μ.restrict 𝓕) L hL0 hrk ht hC (by linarith : (0 : ℝ) + (r_lat : ℝ) ≤ decayExp)
    hmeas hint0 hθm hθb
  refine ⟨hres.1, ?_⟩
  have hvol : ∫ g in 𝓕,
      (max (1 : ℝ) (RHDirect.Stage2SiegelReduction.lambda1 (L g))⁻¹) ^ (-(0 : ℝ)) ∂D.μ =
      (D.μ 𝓕).toReal := by
    have h1 : (fun g : G => (max (1 : ℝ) (RHDirect.Stage2SiegelReduction.lambda1 (L g))⁻¹) ^ (-(0 : ℝ))) =
        fun _ => (1 : ℝ) := by ext g; simp
    rw [h1, setIntegral_const, smul_eq_mul, mul_one, Measure.real]
  rw [hvol] at hres
  exact hres.2

end SiegelEnvelopeIntegrable

end RHDirect.Stage14M1_SiegelDomainReduction

end

