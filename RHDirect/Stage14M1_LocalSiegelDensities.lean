import RHDirect.Stage9SpecialValues
import RHDirect.Stage11RallisMassFiber
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.LinearAlgebra.Matrix.Nondegenerate

/-!
# RHDirect.Stage14M1_LocalSiegelDensities

Unconditional (`0` `sorry`, `0` custom `axiom`s, `0` `opaque`, `0` `native_decide`) formalization of
local Hermitian lattices, exact finite-field unitary group cardinalities, Hensel-stabilized local
representation densities, unramified Euler factors, and the global Siegel density Euler product for
Hermitian forms over CM extensions `E / F`.
-/

noncomputable section

open Finset BigOperators Matrix

namespace RHDirect.Stage14M1_LocalSiegelDensities

/-! ## Section 1: Finite-Field Quadratic Extensions, Norm/Trace & `|U_n(𝔽_q)|` -/

section FiniteFieldHermitian

/-- Conjugate-transpose (Hermitian adjoint) of a matrix with respect to an involution `σ`. -/
def hermConj {R : Type*} [NonAssocSemiring R] (σ : R →+* R) {m n : ℕ}
    (X : Matrix (Fin m) (Fin n) R) : Matrix (Fin n) (Fin m) R :=
  Matrix.of fun i j => σ (X j i)

@[simp]
lemma hermConj_apply {R : Type*} [NonAssocSemiring R] (σ : R →+* R) {m n : ℕ}
    (X : Matrix (Fin m) (Fin n) R) (i : Fin n) (j : Fin m) :
    hermConj σ X i j = σ (X j i) := rfl

lemma hermConj_mul {R : Type*} [CommRing R] (σ : R →+* R) {m n p : ℕ}
    (A : Matrix (Fin m) (Fin n) R) (B : Matrix (Fin n) (Fin p) R) :
    hermConj σ (A * B) = hermConj σ B * hermConj σ A := by
  ext i j
  simp [hermConj, Matrix.mul_apply, map_sum, map_mul, mul_comm]

lemma hermConj_one {R : Type*} [CommRing R] (σ : R →+* R) (n : ℕ) :
    hermConj σ (1 : Matrix (Fin n) (Fin n) R) = 1 := by
  ext i j
  by_cases h : i = j <;> simp [hermConj, Matrix.one_apply, h, eq_comm]

lemma hermConj_add {R : Type*} [CommRing R] (σ : R →+* R) {m n : ℕ}
    (A B : Matrix (Fin m) (Fin n) R) :
    hermConj σ (A + B) = hermConj σ A + hermConj σ B := by
  ext i j; simp [hermConj]

lemma hermConj_smul {R : Type*} [CommRing R] (σ : R →+* R) {m n : ℕ}
    (c : R) (A : Matrix (Fin m) (Fin n) R) :
    hermConj σ (c • A) = σ c • hermConj σ A := by
  ext i j; simp [hermConj]

lemma hermConj_involutive {R : Type*} [CommRing R] (σ : R →+* R)
    (hσ : ∀ x, σ (σ x) = x) {m n : ℕ} (A : Matrix (Fin m) (Fin n) R) :
    hermConj σ (hermConj σ A) = A := by
  ext i j; simp [hermConj, hσ]

/-- A matrix `H` is `σ`-Hermitian if `hermConj σ H = H`, i.e., `σ (H j i) = H i j`. -/
def IsHermMatrix {R : Type*} [NonAssocSemiring R] (σ : R →+* R) {n : ℕ}
    (H : Matrix (Fin n) (Fin n) R) : Prop :=
  ∀ i j, σ (H j i) = H i j

lemma isHermMatrix_iff_hermConj {R : Type*} [NonAssocSemiring R] (σ : R →+* R) {n : ℕ}
    (H : Matrix (Fin n) (Fin n) R) :
    IsHermMatrix σ H ↔ hermConj σ H = H := by
  constructor
  · intro h; ext i j; exact h i j
  · intro h i j; exact congr_fun (congr_fun h i) j

lemma isHermMatrix_one {R : Type*} [CommRing R] (σ : R →+* R) (n : ℕ) :
    IsHermMatrix σ (1 : Matrix (Fin n) (Fin n) R) := by
  rw [isHermMatrix_iff_hermConj]
  exact hermConj_one σ n

lemma isHermMatrix_congr {R : Type*} [CommRing R] (σ : R →+* R) {m n : ℕ}
    {H : Matrix (Fin m) (Fin m) R} (hH : IsHermMatrix σ H)
    (hσ : ∀ x, σ (σ x) = x) (X : Matrix (Fin m) (Fin n) R) :
    IsHermMatrix σ (hermConj σ X * H * X) := by
  rw [isHermMatrix_iff_hermConj] at hH ⊢
  rw [hermConj_mul, hermConj_mul, hermConj_involutive σ hσ, hH, Matrix.mul_assoc]

/-- The Hermitian form `⟪x, y⟫_H = ∑ i j, σ (x i) * H i j * y j`. -/
def hermPairing {R : Type*} [CommRing R] (σ : R →+* R) {n : ℕ}
    (H : Matrix (Fin n) (Fin n) R) (x y : Fin n → R) : R :=
  ∑ i : Fin n, ∑ j : Fin n, σ (x i) * H i j * y j

lemma hermPairing_eq_dotProduct {R : Type*} [CommRing R] (σ : R →+* R) {n : ℕ}
    (H : Matrix (Fin n) (Fin n) R) (x y : Fin n → R) :
    hermPairing σ H x y = dotProduct (fun i => σ (x i)) (H *ᵥ y) := by
  simp only [hermPairing, dotProduct, Matrix.mulVec]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

lemma hermPairing_mulVec {R : Type*} [CommRing R] (σ : R →+* R) {m n : ℕ}
    (H : Matrix (Fin m) (Fin m) R) (X : Matrix (Fin m) (Fin n) R) (u v : Fin n → R) :
    hermPairing σ H (X *ᵥ u) (X *ᵥ v) = hermPairing σ (hermConj σ X * H * X) u v := by
  rw [hermPairing_eq_dotProduct, hermPairing_eq_dotProduct]
  have h1 : (fun i => σ ((X *ᵥ u) i)) = (fun i => σ (u i)) ᵥ* (hermConj σ X) := by
    ext i
    simp [Matrix.mulVec, Matrix.vecMul, dotProduct, hermConj, mul_comm]
  calc (fun i => σ ((X *ᵥ u) i)) ⬝ᵥ (H *ᵥ (X *ᵥ v))
      = ((fun i => σ (u i)) ᵥ* hermConj σ X) ⬝ᵥ (H *ᵥ (X *ᵥ v)) := by rw [h1]
    _ = (fun i => σ (u i)) ⬝ᵥ (hermConj σ X *ᵥ (H *ᵥ (X *ᵥ v))) :=
        (Matrix.dotProduct_mulVec _ _ _).symm
    _ = (fun i => σ (u i)) ⬝ᵥ ((hermConj σ X * H * X) *ᵥ v) := by
        simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]

lemma hermPairing_one {R : Type*} [CommRing R] (σ : R →+* R) {n : ℕ} (x y : Fin n → R) :
    hermPairing σ (1 : Matrix (Fin n) (Fin n) R) x y = ∑ i : Fin n, σ (x i) * y i := by
  simp [hermPairing, Matrix.one_apply]

lemma hermPairing_skew {R : Type*} [CommRing R] (σ : R →+* R) (hσ : ∀ x, σ (σ x) = x)
    {n : ℕ} {H : Matrix (Fin n) (Fin n) R} (hH : IsHermMatrix σ H) (x y : Fin n → R) :
    σ (hermPairing σ H y x) = hermPairing σ H x y := by
  unfold hermPairing
  simp only [map_sum, map_mul, hσ]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hH i j]
  ring

section QuadFiniteField

variable {k₁ k₂ : Type*} [Field k₁] [Fintype k₁] [DecidableEq k₁]
  [Field k₂] [Fintype k₂] [DecidableEq k₂] [Algebra k₁ k₂]

omit [DecidableEq k₁] [DecidableEq k₂] in
/-- In a quadratic extension of finite fields `k₂ / k₁` with `|k₁| = q`, `|k₂| = q^2`. -/
theorem card_quad_ext_eq_sq (hdim : Module.finrank k₁ k₂ = 2) :
    Fintype.card k₂ = (Fintype.card k₁) ^ 2 := by
  have h := Module.card_eq_pow_finrank (K := k₁) (V := k₂)
  rw [hdim] at h
  simpa using h

omit [DecidableEq k₁] [DecidableEq k₂] in
/-- Frobenius power `x ^ (Fintype.card k₁)` is prime-power Frobenius on `k₂`. -/
private lemma card_k1_is_prime_pow :
    ∃ p d : ℕ, p.Prime ∧ 0 < d ∧ ringChar k₂ = p ∧ Fintype.card k₁ = p ^ d := by
  have : CharP k₁ (ringChar k₁) := ringChar.charP k₁
  obtain ⟨d, hp, hcard⟩ := FiniteField.card k₁ (ringChar k₁)
  have hp0 : ((ringChar k₁ : ℕ) : k₂) = 0 := by
    rw [← map_natCast (algebraMap k₁ k₂), CharP.cast_eq_zero, map_zero]
  have hdvd : ringChar k₂ ∣ ringChar k₁ := ringChar.dvd hp0
  have hprime2 : (ringChar k₂).Prime := by
    have : CharP k₂ (ringChar k₂) := ringChar.charP k₂
    exact (CharP.char_is_prime_or_zero k₂ (ringChar k₂)).resolve_right
      (CharP.char_ne_zero_of_finite k₂ _)
  have hchar2 : ringChar k₂ = ringChar k₁ := (hp.eq_one_or_self_of_dvd _ hdvd).resolve_left hprime2.ne_one
  exact ⟨ringChar k₁, d.val, hp, d.pos, hchar2, hcard⟩

/-- The `k₁`-Frobenius endomorphism `x ↦ x ^ (Fintype.card k₁)` on `k₂`. -/
def quadFrobHom (k₁ k₂ : Type*) [Field k₁] [Fintype k₁] [Field k₂] [Fintype k₂] [Algebra k₁ k₂] :
    k₂ →ₐ[k₁] k₂ where
  toFun x := x ^ (Fintype.card k₁)
  map_one' := one_pow _
  map_mul' x y := mul_pow x y _
  map_zero' := zero_pow (Fintype.card_pos (α := k₁)).ne'
  map_add' x y := by
    classical
    obtain ⟨p, d, hp, _, hchar, hcard⟩ := card_k1_is_prime_pow (k₁ := k₁) (k₂ := k₂)
    have : Fact p.Prime := ⟨hp⟩
    have : CharP k₂ p := hchar ▸ ringChar.charP k₂
    rw [hcard]
    exact add_pow_char_pow x y p d
  commutes' a := by
    rw [← map_pow, FiniteField.pow_card]

/-- **Frobenius Identification**: Any nontrivial `σ : k₂ ≃ₐ[k₁] k₂` on a quadratic extension
of finite fields satisfies `σ x = x ^ (Fintype.card k₁)`. -/
theorem sigma_eq_pow_card (hdim : Module.finrank k₁ k₂ = 2)
    (σ : k₂ ≃ₐ[k₁] k₂) (hσ : σ ≠ AlgEquiv.refl) :
    ∀ x : k₂, σ x = x ^ (Fintype.card k₁) := by
  set q := Fintype.card k₁
  have hq2 : 2 ≤ q := Fintype.one_lt_card
  have hq1 : 1 ≤ q := by omega
  have hcard2 : Fintype.card k₂ = q ^ 2 := card_quad_ext_eq_sq hdim
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := k₂ˣ)
  have hord : orderOf g = q ^ 2 - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card,
      Fintype.card_units, hcard2]
  have hg_not_mem : (g : k₂) ∉ Set.range (algebraMap k₁ k₂) := by
    rintro ⟨a, ha⟩
    have ha0 : a ≠ 0 := by
      intro h0; subst h0; simp only [map_zero] at ha; exact g.ne_zero ha.symm
    have hpow : g ^ (q - 1) = 1 := by
      ext
      push_cast
      rw [← ha, ← map_pow, FiniteField.pow_card_sub_one_eq_one a ha0, map_one]
    have hdvd : q ^ 2 - 1 ∣ q - 1 := hord ▸ orderOf_dvd_of_pow_eq_one hpow
    have hle : q ^ 2 - 1 ≤ q - 1 := Nat.le_of_dvd (Nat.sub_pos_of_lt hq2) hdvd
    have h1 : 1 ≤ q ^ 2 := one_le_pow₀ hq1
    zify [hq1, h1] at hle
    nlinarith
  have hdep : ¬ LinearIndependent k₁ ![ (1 : k₂), (g : k₂), (g : k₂) ^ 2 ] := by
    intro hli
    have hle := hli.fintype_card_le_finrank
    rw [Fintype.card_fin, hdim] at hle
    omega
  rw [Fintype.not_linearIndependent_iff] at hdep
  obtain ⟨c, hsum, i₀, hi₀⟩ := hdep
  have hquad : c 2 • (g : k₂) ^ 2 + c 1 • (g : k₂) + c 0 • (1 : k₂) = 0 := by
    rw [Fin.sum_univ_three] at hsum
    simpa [add_comm, add_left_comm, add_assoc] using hsum
  have hc2_ne : c 2 ≠ 0 := by
    intro hc2
    rw [hc2, zero_smul, zero_add] at hquad
    have hc1 : c 1 = 0 := by
      by_contra hc1
      have hlin : (g : k₂) = algebraMap k₁ k₂ (-(c 0) / c 1) := by
        have h1 : algebraMap k₁ k₂ (c 1) * (g : k₂) + algebraMap k₁ k₂ (c 0) = 0 := by
          simpa [Algebra.smul_def] using hquad
        have hc1' : algebraMap k₁ k₂ (c 1) ≠ 0 := (map_ne_zero _).mpr hc1
        rw [map_div₀, map_neg]
        apply eq_div_of_mul_eq hc1'
        linear_combination h1
      exact hg_not_mem ⟨_, hlin.symm⟩
    have hc0 : c 0 = 0 := by
      rw [hc1, zero_smul, zero_add] at hquad
      have h0 : algebraMap k₁ k₂ (c 0) = 0 := by
        simpa [Algebra.smul_def] using hquad
      exact (map_eq_zero _).mp h0
    fin_cases i₀ <;> exact hi₀ (by assumption)
  have hroot_unique : ∀ y : k₂,
      c 2 • y ^ 2 + c 1 • y + c 0 • (1 : k₂) = 0 → y ≠ (g : k₂) →
        y = - (g : k₂) - algebraMap k₁ k₂ (c 1 / c 2) := by
    intro y hy hne
    have hsub : algebraMap k₁ k₂ (c 2) * (y ^ 2 - (g : k₂) ^ 2) +
        algebraMap k₁ k₂ (c 1) * (y - (g : k₂)) = 0 := by
      have h1 : algebraMap k₁ k₂ (c 2) * y ^ 2 + algebraMap k₁ k₂ (c 1) * y +
          algebraMap k₁ k₂ (c 0) = 0 := by
        simpa [Algebra.smul_def] using hy
      have h2 : algebraMap k₁ k₂ (c 2) * (g : k₂) ^ 2 + algebraMap k₁ k₂ (c 1) * (g : k₂) +
          algebraMap k₁ k₂ (c 0) = 0 := by
        simpa [Algebra.smul_def] using hquad
      linear_combination h1 - h2
    have hfac : (y - (g : k₂)) * (algebraMap k₁ k₂ (c 2) * (y + (g : k₂)) +
        algebraMap k₁ k₂ (c 1)) = 0 := by
      linear_combination hsub
    rcases mul_eq_zero.mp hfac with h0 | hlin
    · exact absurd (sub_eq_zero.mp h0) hne
    · have hc2' : algebraMap k₁ k₂ (c 2) ≠ 0 := (map_ne_zero _).mpr hc2_ne
      rw [map_div₀]
      apply eq_of_sub_eq_zero
      apply (mul_left_cancel₀ hc2')
      calc algebraMap k₁ k₂ (c 2) * (y - (-(g : k₂) - algebraMap k₁ k₂ (c 1) / algebraMap k₁ k₂ (c 2)))
          = algebraMap k₁ k₂ (c 2) * (y + (g : k₂)) +
              algebraMap k₁ k₂ (c 2) * (algebraMap k₁ k₂ (c 1) / algebraMap k₁ k₂ (c 2)) := by ring
        _ = algebraMap k₁ k₂ (c 2) * (y + (g : k₂)) + algebraMap k₁ k₂ (c 1) := by
            rw [mul_div_cancel₀ _ hc2']
        _ = 0 := hlin
        _ = algebraMap k₁ k₂ (c 2) * 0 := (mul_zero _).symm
  have hσ_root : c 2 • (σ (g : k₂)) ^ 2 + c 1 • (σ (g : k₂)) + c 0 • (1 : k₂) = 0 := by
    have h := congrArg σ hquad
    simpa [map_add, map_smul, map_pow, map_one, map_zero] using h
  have hfrob_root : c 2 • ((g : k₂) ^ q) ^ 2 + c 1 • ((g : k₂) ^ q) + c 0 • (1 : k₂) = 0 := by
    have h := congrArg (quadFrobHom k₁ k₂) hquad
    simpa [quadFrobHom, map_add, map_smul, map_pow, map_one, map_zero] using h
  have hσ_ne_g : σ (g : k₂) ≠ (g : k₂) := by
    intro hfix
    apply hσ
    ext x
    by_cases hx : x = 0
    · subst hx; simp
    · let u : k₂ˣ := Units.mk0 x hx
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hg u)
      have hxu : x = ((g ^ m : k₂ˣ) : k₂) := by rw [hm]; rfl
      rw [hxu]
      simp only [Units.val_zpow_eq_zpow_val, map_zpow₀, hfix]
      rfl
  have hfrob_ne_g : (g : k₂) ^ q ≠ (g : k₂) := by
    intro heq
    have hpow : g ^ (q - 1) = 1 := by
      have h1 : g ^ q = g := by ext; simpa using heq
      have hq1' : q = (q - 1) + 1 := (Nat.sub_add_cancel hq1).symm
      rw [hq1', pow_succ] at h1
      have h1' : g ^ (q - 1) * g = 1 * g := by simpa [one_mul] using h1
      exact mul_right_cancel h1'
    have hdvd : q ^ 2 - 1 ∣ q - 1 := hord ▸ orderOf_dvd_of_pow_eq_one hpow
    have hle : q ^ 2 - 1 ≤ q - 1 := Nat.le_of_dvd (Nat.sub_pos_of_lt hq2) hdvd
    have h1 : 1 ≤ q ^ 2 := one_le_pow₀ hq1
    zify [hq1, h1] at hle
    nlinarith
  have hσg : σ (g : k₂) = (g : k₂) ^ q :=
    (hroot_unique _ hσ_root hσ_ne_g).trans (hroot_unique _ hfrob_root hfrob_ne_g).symm
  intro x
  by_cases hx : x = 0
  · subst hx; rw [map_zero, zero_pow (Fintype.card_pos (α := k₁)).ne']
  · let u : k₂ˣ := Units.mk0 x hx
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hg u)
    have hxu : x = ((g ^ m : k₂ˣ) : k₂) := by rw [hm]; rfl
    rw [hxu]
    simp only [Units.val_zpow_eq_zpow_val, map_zpow₀, hσg]
    rw [← zpow_natCast, ← zpow_natCast, ← _root_.zpow_mul, ← _root_.zpow_mul, mul_comm]

theorem sigma_involutive (hdim : Module.finrank k₁ k₂ = 2)
    (σ : k₂ ≃ₐ[k₁] k₂) (hσ : σ ≠ AlgEquiv.refl) :
    ∀ x : k₂, σ (σ x) = x := by
  intro x
  rw [sigma_eq_pow_card hdim σ hσ, sigma_eq_pow_card hdim σ hσ, ← pow_mul, ← sq,
    ← card_quad_ext_eq_sq hdim, FiniteField.pow_card]

theorem sigma_norm_eq_pow (hdim : Module.finrank k₁ k₂ = 2)
    (σ : k₂ ≃ₐ[k₁] k₂) (hσ : σ ≠ AlgEquiv.refl) (x : k₂) :
    x * σ x = x ^ (Fintype.card k₁ + 1) := by
  rw [sigma_eq_pow_card hdim σ hσ, pow_succ']

omit [DecidableEq k₁] in
private lemma fixed_by_pow_card_mem_base (hdim : Module.finrank k₁ k₂ = 2)
    {y : k₂} (hy : y ^ Fintype.card k₁ = y) :
    ∃ a : k₁, y = algebraMap k₁ k₂ a := by
  classical
  have _ := hdim
  let fixed : Finset k₂ := Finset.univ.filter fun z : k₂ => z ^ Fintype.card k₁ = z
  let base : Finset k₂ := Finset.univ.image (algebraMap k₁ k₂)
  have hsub_fin : base ⊆ fixed := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨a, _, rfl⟩
    simp only [fixed, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← map_pow, FiniteField.pow_card]
  have hbase_card : base.card = Fintype.card k₁ := by
    rw [Finset.card_image_of_injective _ (RingHom.injective _), Finset.card_univ]
  have hfixed_card : fixed.card ≤ Fintype.card k₁ := by
    let P : Polynomial k₂ := Polynomial.X ^ Fintype.card k₁ - Polynomial.X
    have hq1 : 1 < Fintype.card k₁ := Fintype.one_lt_card
    have hlt : (Polynomial.X : Polynomial k₂).natDegree <
        (Polynomial.X ^ Fintype.card k₁ : Polynomial k₂).natDegree := by
      simp [hq1]
    have hnat : P.natDegree = Fintype.card k₁ := by
      simpa [P] using Polynomial.natDegree_sub_eq_left_of_natDegree_lt hlt
    have hPne : P ≠ 0 := by
      intro h0
      rw [h0, Polynomial.natDegree_zero] at hnat
      omega
    have hmem : ∀ z ∈ fixed, z ∈ P.roots := by
      intro z hz
      rw [Polynomial.mem_roots hPne]
      have hz' := (Finset.mem_filter.mp hz).2
      simp [P, hz']
    have hsub : fixed ⊆ P.roots.toFinset :=
      fun z hz => Multiset.mem_toFinset.mpr (hmem z hz)
    calc fixed.card ≤ P.roots.toFinset.card := Finset.card_le_card hsub
      _ ≤ Multiset.card P.roots := Multiset.toFinset_card_le _
      _ ≤ P.natDegree := Polynomial.card_roots' P
      _ = Fintype.card k₁ := hnat
  have heq : base = fixed := Finset.eq_of_subset_of_card_le hsub_fin (hbase_card ▸ hfixed_card)
  have hmem_fixed : y ∈ fixed := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy⟩
  rw [← heq] at hmem_fixed
  obtain ⟨a, _, ha⟩ := Finset.mem_image.mp hmem_fixed
  exact ⟨a, ha.symm⟩

theorem sigma_norm_mem_base (hdim : Module.finrank k₁ k₂ = 2)
    (σ : k₂ ≃ₐ[k₁] k₂) (hσ : σ ≠ AlgEquiv.refl) (x : k₂) :
    ∃ a : k₁, x * σ x = algebraMap k₁ k₂ a := by
  have hfix : σ (x * σ x) = x * σ x := by
    rw [map_mul, sigma_involutive hdim σ hσ, mul_comm]
  have hsub : (x * σ x) ^ (Fintype.card k₁) = x * σ x := by
    rw [← sigma_eq_pow_card hdim σ hσ]; exact hfix
  exact fixed_by_pow_card_mem_base hdim hsub

/-- Cardinality of the norm-1 torus `{u : k₂ˣ // u * σ u = 1}` is `q + 1`. -/
theorem card_norm_one_units (hdim : Module.finrank k₁ k₂ = 2)
    (σ : k₂ ≃ₐ[k₁] k₂) (hσ : σ ≠ AlgEquiv.refl) :
    Fintype.card { u : k₂ˣ // (u : k₂) * σ u = 1 } = Fintype.card k₁ + 1 := by
  classical
  set q := Fintype.card k₁
  have hq2 : 2 ≤ q := Fintype.one_lt_card
  have hq1 : 1 ≤ q := by omega
  have hcard2 : Fintype.card k₂ = q ^ 2 := card_quad_ext_eq_sq hdim
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := k₂ˣ)
  have hord : orderOf g = q ^ 2 - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card,
      Fintype.card_units, hcard2]
  have hq_sq : q ^ 2 - 1 = (q - 1) * (q + 1) := by
    have h1 : 1 ≤ q ^ 2 := one_le_pow₀ hq1
    zify [hq1, h1]
    ring
  have heq_set : ∀ u : k₂ˣ, ((u : k₂) * σ u = 1) ↔ u ^ (q + 1) = 1 := by
    intro u
    rw [sigma_norm_eq_pow hdim σ hσ (u : k₂), ← Units.val_pow_eq_pow_val, Units.val_eq_one]
  let φ : Fin (q + 1) → { u : k₂ˣ // (u : k₂) * σ u = 1 } := fun i =>
    ⟨g ^ (i.1 * (q - 1)), by
      rw [heq_set]
      rw [← pow_mul, show i.1 * (q - 1) * (q + 1) = i.1 * (q ^ 2 - 1) by rw [hq_sq]; ring,
        mul_comm i.1, pow_mul, ← hord, pow_orderOf_eq_one, one_pow]⟩
  have hbij : Function.Bijective φ := by
    constructor
    · intro i j hij
      have hpow : g ^ (i.1 * (q - 1)) = g ^ (j.1 * (q - 1)) := congrArg Subtype.val hij
      have hle_case : ∀ a b : Fin (q + 1), a.1 ≤ b.1 →
          g ^ (a.1 * (q - 1)) = g ^ (b.1 * (q - 1)) → a = b := by
        intro a b hab heq_ab
        have hdiff : g ^ ((b.1 - a.1) * (q - 1)) = 1 := by
          have hmul : g ^ (a.1 * (q - 1)) * g ^ ((b.1 - a.1) * (q - 1)) = g ^ (b.1 * (q - 1)) := by
            rw [← pow_add, ← add_mul, Nat.add_sub_cancel' hab]
          rw [← heq_ab] at hmul
          exact mul_left_cancel (a := g ^ (a.1 * (q - 1))) (by simpa using hmul)
        have hdvd : q ^ 2 - 1 ∣ (b.1 - a.1) * (q - 1) := hord ▸ orderOf_dvd_of_pow_eq_one hdiff
        rw [hq_sq] at hdvd
        have hdvd' : q + 1 ∣ b.1 - a.1 := by
          rw [mul_comm (q - 1) (q + 1)] at hdvd
          exact Nat.dvd_of_mul_dvd_mul_right (Nat.sub_pos_of_lt hq2) hdvd
        have hlt : b.1 - a.1 < q + 1 := by omega
        have h0 : b.1 - a.1 = 0 := Nat.eq_zero_of_dvd_of_lt hdvd' hlt
        exact Fin.ext (by omega)
      rcases le_total i.1 j.1 with hle | hle
      · exact hle_case i j hle hpow
      · exact (hle_case j i hle hpow.symm).symm
    · rintro ⟨u, hu⟩
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg u)
      have hkm : ∃ m < q ^ 2 - 1, g ^ m = u := by
        have hord_pos : (0 : ℤ) < (q ^ 2 - 1 : ℕ) := by
          have : 4 ≤ q ^ 2 := by nlinarith
          omega
        have hnn := Int.emod_nonneg k hord_pos.ne'
        refine ⟨Int.toNat (k % (q ^ 2 - 1 : ℕ)), ?_, ?_⟩
        · have hmod := Int.emod_lt_of_pos k hord_pos
          omega
        · calc g ^ Int.toNat (k % (q ^ 2 - 1 : ℕ))
              = g ^ (Int.toNat (k % (q ^ 2 - 1 : ℕ)) : ℤ) := (zpow_natCast _ _).symm
            _ = g ^ (k % (orderOf g : ℕ)) := by rw [Int.toNat_of_nonneg hnn, hord]
            _ = g ^ k := by
                have hk_eq := Int.mul_ediv_add_emod k (orderOf g : ℕ)
                conv_rhs => rw [← hk_eq, _root_.zpow_add, _root_.zpow_mul, zpow_natCast,
                  pow_orderOf_eq_one, _root_.one_zpow, one_mul]
            _ = u := hk
      obtain ⟨m, hm_lt, rfl⟩ := hkm
      have hm_pow : (g ^ m) ^ (q + 1) = 1 := (heq_set _).mp hu
      rw [← pow_mul] at hm_pow
      have hdvd : q ^ 2 - 1 ∣ m * (q + 1) := hord ▸ orderOf_dvd_of_pow_eq_one hm_pow
      rw [hq_sq] at hdvd
      have hdvd_m : q - 1 ∣ m :=
        Nat.dvd_of_mul_dvd_mul_right (by omega : 0 < q + 1) hdvd
      obtain ⟨i, hi_eq⟩ := hdvd_m
      have hi_lt : i < q + 1 := by
        rw [hi_eq, hq_sq, mul_comm (q - 1) (q + 1), mul_comm (q - 1) i] at hm_lt
        exact Nat.lt_of_mul_lt_mul_right hm_lt
      refine ⟨⟨i, hi_lt⟩, Subtype.ext ?_⟩
      show g ^ (i * (q - 1)) = g ^ m
      rw [hi_eq, mul_comm]
  rw [← Fintype.card_of_bijective hbij, Fintype.card_fin]

/-- Norm surjectivity `k₂ˣ →* k₁ˣ` and exact fiber cardinality `q + 1` for nonzero targets. -/
theorem card_norm_fiber_nonzero (hdim : Module.finrank k₁ k₂ = 2)
    (σ : k₂ ≃ₐ[k₁] k₂) (hσ : σ ≠ AlgEquiv.refl) (a : k₁) (ha : a ≠ 0) :
    Fintype.card { x : k₂ // x * σ x = algebraMap k₁ k₂ a } = Fintype.card k₁ + 1 := by
  classical
  set q := Fintype.card k₁
  have hq2 : 2 ≤ q := Fintype.one_lt_card
  have hq1 : 1 ≤ q := by omega
  have hcard2 : Fintype.card k₂ = q ^ 2 := card_quad_ext_eq_sq hdim
  let NFun : k₂ˣ → k₁ˣ := fun u =>
    Units.mk0 (Classical.choose (sigma_norm_mem_base hdim σ hσ (u : k₂))) (by
      intro hb
      have hspec := Classical.choose_spec (sigma_norm_mem_base hdim σ hσ (u : k₂))
      rw [hb, map_zero] at hspec
      rcases mul_eq_zero.mp hspec with h0 | h0
      · exact u.ne_zero h0
      · exact u.ne_zero (by simpa [sigma_involutive hdim σ hσ] using congrArg σ h0))
  have hNFun_spec : ∀ u : k₂ˣ, algebraMap k₁ k₂ (NFun u : k₁) = (u : k₂) * σ u := fun u =>
    (Classical.choose_spec (sigma_norm_mem_base hdim σ hσ (u : k₂))).symm
  let N : k₂ˣ →* k₁ˣ :=
    { toFun := NFun
      map_one' := by
        ext
        apply (RingHom.injective (algebraMap k₁ k₂))
        rw [hNFun_spec 1, Units.val_one, map_one, one_mul]
        exact (map_one _).symm
      map_mul' := fun u v => by
        ext
        apply (RingHom.injective (algebraMap k₁ k₂))
        rw [Units.val_mul, map_mul, hNFun_spec (u * v), hNFun_spec u, hNFun_spec v,
          Units.val_mul, map_mul]
        ring }
  have hN_spec : ∀ u : k₂ˣ, algebraMap k₁ k₂ (N u : k₁) = (u : k₂) * σ u := hNFun_spec
  have hker_card : Fintype.card N.ker = q + 1 := by
    let e : N.ker ≃ { u : k₂ˣ // (u : k₂) * σ u = 1 } :=
      { toFun := fun ⟨u, hu⟩ => ⟨u, by
          rw [← hN_spec u, MonoidHom.mem_ker.mp hu, Units.val_one, map_one]⟩
        invFun := fun ⟨u, hu⟩ => ⟨u, by
          rw [MonoidHom.mem_ker]
          ext
          apply (RingHom.injective (algebraMap k₁ k₂))
          rw [hN_spec u, hu, Units.val_one, map_one]⟩
        left_inv := fun ⟨_, _⟩ => rfl
        right_inv := fun ⟨_, _⟩ => rfl }
    rw [Fintype.card_congr e]
    exact card_norm_one_units hdim σ hσ
  have him_card : Fintype.card (k₂ˣ ⧸ N.ker) = q - 1 := by
    have hmul := Subgroup.card_eq_card_quotient_mul_card_subgroup N.ker
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
      hker_card, Fintype.card_units, hcard2] at hmul
    have hq_sq : q ^ 2 - 1 = (q - 1) * (q + 1) := by
      have h1 : 1 ≤ q ^ 2 := one_le_pow₀ hq1
      zify [hq1, h1]
      ring
    rw [hq_sq] at hmul
    exact Nat.mul_right_cancel (by omega : 0 < q + 1) hmul.symm
  have hN_surj : Function.Surjective N := by
    have hinj := QuotientGroup.kerLift_injective N
    have hcard_eq : Fintype.card (k₂ˣ ⧸ N.ker) = Fintype.card k₁ˣ := by
      rw [him_card, Fintype.card_units]
    have hbij := (Fintype.bijective_iff_injective_and_card (QuotientGroup.kerLift N)).mpr
      ⟨hinj, hcard_eq⟩
    intro y
    obtain ⟨q0, hq0⟩ := hbij.2 y
    induction q0 using Quotient.inductionOn' with
    | h u => exact ⟨u, hq0⟩
  obtain ⟨u₀, hu₀⟩ := hN_surj (Units.mk0 a ha)
  have hu₀' : (u₀ : k₂) * σ u₀ = algebraMap k₁ k₂ a := by
    rw [← hN_spec u₀, hu₀]; rfl
  let e : { x : k₂ // x * σ x = algebraMap k₁ k₂ a } ≃
      { u : k₂ˣ // (u : k₂) * σ u = 1 } :=
    { toFun := fun ⟨x, hx⟩ =>
        let ux := Units.mk0 x (by
          intro h0; subst h0; simp only [zero_mul] at hx
          exact ha ((RingHom.injective (algebraMap k₁ k₂)) (by simpa using hx.symm)))
        ⟨ux * u₀⁻¹, by
          simp only [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀]
          have hx' : (ux : k₂) * σ ux = algebraMap k₁ k₂ a := hx
          calc (ux : k₂) * (u₀ : k₂)⁻¹ * (σ (ux : k₂) * (σ (u₀ : k₂))⁻¹)
              = ((ux : k₂) * σ (ux : k₂)) * ((u₀ : k₂) * σ (u₀ : k₂))⁻¹ := by
                  rw [mul_inv]; ring
            _ = algebraMap k₁ k₂ a * (algebraMap k₁ k₂ a)⁻¹ := by rw [hx', hu₀']
            _ = 1 := mul_inv_cancel₀ ((map_ne_zero _).mpr ha)⟩
      invFun := fun ⟨w, hw⟩ =>
        ⟨(w * u₀ : k₂ˣ), by
          simp only [Units.val_mul, map_mul]
          calc (w : k₂) * (u₀ : k₂) * (σ (w : k₂) * σ (u₀ : k₂))
              = ((w : k₂) * σ (w : k₂)) * ((u₀ : k₂) * σ (u₀ : k₂)) := by ring
            _ = 1 * algebraMap k₁ k₂ a := by rw [hw, hu₀']
            _ = algebraMap k₁ k₂ a := one_mul _⟩
      left_inv := fun ⟨x, hx⟩ => by ext; simp
      right_inv := fun ⟨w, hw⟩ => by ext; simp }
  rw [Fintype.card_congr e]
  exact card_norm_one_units hdim σ hσ

omit [Fintype k₁] [DecidableEq k₁] in
/-- Existence of an element with nonzero trace `x + σ x ≠ 0` in **all** characteristics. -/
theorem exists_trace_ne_zero (σ : k₂ ≃ₐ[k₁] k₂) (hσ : σ ≠ AlgEquiv.refl) :
    ∃ x : k₂, x + σ x ≠ 0 := by
  by_cases h2 : (2 : k₂) = 0
  · have : ∃ x : k₂, σ x ≠ x := by
      by_contra h
      push Not at h
      exact hσ (AlgEquiv.ext h)
    obtain ⟨x, hx⟩ := this
    refine ⟨x, ?_⟩
    intro hadd
    apply hx
    have hneg : σ x = -x := eq_neg_of_add_eq_zero_right hadd
    have hneg_x : -x = x := by
      have : x + x = 0 := by rw [← two_mul, h2, zero_mul]
      exact (eq_neg_of_add_eq_zero_left this).symm
    rw [hneg, hneg_x]
  · refine ⟨1, ?_⟩
    simpa [one_add_one_eq_two] using h2

/-- Trace `x ↦ x + σ x` maps `k₂` into `range (algebraMap k₁ k₂)`. -/
theorem trace_mem_base (hdim : Module.finrank k₁ k₂ = 2)
    (σ : k₂ ≃ₐ[k₁] k₂) (hσ : σ ≠ AlgEquiv.refl) (x : k₂) :
    ∃ a : k₁, x + σ x = algebraMap k₁ k₂ a := by
  have hfix : σ (x + σ x) = x + σ x := by
    rw [map_add, sigma_involutive hdim σ hσ, add_comm]
  have hsub : (x + σ x) ^ (Fintype.card k₁) = x + σ x := by
    rw [← sigma_eq_pow_card hdim σ hσ]; exact hfix
  exact fixed_by_pow_card_mem_base hdim hsub

theorem trace_surjective (hdim : Module.finrank k₁ k₂ = 2)
    (σ : k₂ ≃ₐ[k₁] k₂) (hσ : σ ≠ AlgEquiv.refl) :
    ∀ a : k₁, ∃ x : k₂, x + σ x = algebraMap k₁ k₂ a := by
  obtain ⟨x₀, hx₀⟩ := exists_trace_ne_zero σ hσ
  obtain ⟨t₀, ht₀⟩ := trace_mem_base hdim σ hσ x₀
  have ht₀_ne : t₀ ≠ 0 := by
    intro h0; subst h0; simp only [map_zero] at ht₀; exact hx₀ ht₀
  intro a
  refine ⟨algebraMap k₁ k₂ (a / t₀) * x₀, ?_⟩
  rw [map_mul, AlgEquiv.commutes, ← mul_add, ht₀, ← map_mul, div_mul_cancel₀ a ht₀_ne]

/-- Cardinality of every trace fiber `{x : k₂ // x + σ x = algebraMap k₁ k₂ a}` is `q`. -/
theorem card_trace_fiber (hdim : Module.finrank k₁ k₂ = 2)
    (σ : k₂ ≃ₐ[k₁] k₂) (hσ : σ ≠ AlgEquiv.refl) (a : k₁) :
    Fintype.card { x : k₂ // x + σ x = algebraMap k₁ k₂ a } = Fintype.card k₁ := by
  classical
  set q := Fintype.card k₁
  have hcard2 : Fintype.card k₂ = q ^ 2 := card_quad_ext_eq_sq hdim
  let TrFun : k₂ → k₁ := fun x => Classical.choose (trace_mem_base hdim σ hσ x)
  have hTr_spec : ∀ x : k₂, algebraMap k₁ k₂ (TrFun x) = x + σ x := fun x =>
    (Classical.choose_spec (trace_mem_base hdim σ hσ x)).symm
  let Tr : k₂ →+ k₁ :=
    { toFun := TrFun
      map_zero' := by
        apply (RingHom.injective (algebraMap k₁ k₂))
        rw [hTr_spec 0, map_zero, map_zero, add_zero]
      map_add' := fun x y => by
        apply (RingHom.injective (algebraMap k₁ k₂))
        rw [map_add, hTr_spec (x + y), hTr_spec x, hTr_spec y, map_add]
        ring }
  have hTr_surj : Function.Surjective Tr := by
    intro b
    obtain ⟨x, hx⟩ := trace_surjective hdim σ hσ b
    refine ⟨x, (RingHom.injective (algebraMap k₁ k₂)) ?_⟩
    change algebraMap k₁ k₂ (TrFun x) = algebraMap k₁ k₂ b
    rw [hTr_spec x, hx]
  have hker_card : Fintype.card Tr.ker = q := by
    have hmul := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup Tr.ker
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
      hcard2] at hmul
    have hquot : Fintype.card (k₂ ⧸ Tr.ker) = q := by
      let e := QuotientAddGroup.quotientKerEquivOfSurjective Tr hTr_surj
      exact Fintype.card_congr e.toEquiv
    rw [hquot] at hmul
    have hqpos : 0 < q := Fintype.card_pos
    have hmul' : q * q = q * Fintype.card Tr.ker := by
      simpa [sq] using hmul
    exact (Nat.mul_left_cancel hqpos hmul').symm
  obtain ⟨x₀, hx₀⟩ := trace_surjective hdim σ hσ a
  let e : { x : k₂ // x + σ x = algebraMap k₁ k₂ a } ≃ Tr.ker :=
    { toFun := fun ⟨x, hx⟩ => ⟨x - x₀, by
        rw [AddMonoidHom.mem_ker]
        apply (RingHom.injective (algebraMap k₁ k₂))
        change algebraMap k₁ k₂ (TrFun (x - x₀)) = algebraMap k₁ k₂ 0
        rw [hTr_spec, map_zero, map_sub]
        calc x - x₀ + (σ x - σ x₀) = (x + σ x) - (x₀ + σ x₀) := by ring
          _ = 0 := by rw [hx, hx₀, sub_self]⟩
      invFun := fun ⟨y, hy⟩ => ⟨y + x₀, by
        have hy' : algebraMap k₁ k₂ (TrFun y) = 0 := by
          change algebraMap k₁ k₂ (Tr y) = 0
          rw [AddMonoidHom.mem_ker.mp hy, map_zero]
        rw [hTr_spec] at hy'
        rw [map_add, show y + x₀ + (σ y + σ x₀) = (y + σ y) + (x₀ + σ x₀) by ring,
          hy', hx₀, zero_add]⟩
      left_inv := fun ⟨x, _⟩ => by ext; simp
      right_inv := fun ⟨y, _⟩ => by ext; simp }
  rw [Fintype.card_congr e, hker_card]

/-! ### Hermitian Sphere Counts & Exact Finite Unitary Group Cardinality -/

/-- Cardinality of the standard Hermitian sphere `{v : Fin n → k₂ // ∑ i, σ (v i) * v i = algebraMap k₁ k₂ a}`. -/
def stdHermSphereCount (k₁ k₂ : Type*) [Field k₁] [Fintype k₁] [Field k₂] [Fintype k₂]
    [Algebra k₁ k₂] (σ : k₂ ≃ₐ[k₁] k₂) (n : ℕ) (a : k₁) : ℕ :=
  Nat.card { v : Fin n → k₂ // ∑ i : Fin n, σ (v i) * v i = algebraMap k₁ k₂ a }

private lemma herm_sum_norm_mem_base (hdim : Module.finrank k₁ k₂ = 2)
    (σ : k₂ ≃ₐ[k₁] k₂) (hσ : σ ≠ AlgEquiv.refl) {n : ℕ} (w : Fin n → k₂) :
    ∃ c : k₁, ∑ i : Fin n, σ (w i) * w i = algebraMap k₁ k₂ c := by
  classical
  have hsum : ∀ s : Finset (Fin n),
      ∃ c : k₁, ∑ i ∈ s, σ (w i) * w i = algebraMap k₁ k₂ c := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨0, by simp⟩
    | insert a s ha ih =>
      obtain ⟨ca, hca⟩ := sigma_norm_mem_base hdim σ hσ (w a)
      obtain ⟨cs, hcs⟩ := ih
      refine ⟨ca + cs, ?_⟩
      rw [Finset.sum_insert ha, map_add, ← hca, ← hcs, mul_comm (w a)]
  exact hsum Finset.univ

/-- Recurrence for `stdHermSphereCount`:
`S_{n+1}(a) = (q + 1) * q^{2n} - q * S_n(a)` in `ℤ`. -/
theorem stdHermSphereCount_succ (hdim : Module.finrank k₁ k₂ = 2)
    (σ : k₂ ≃ₐ[k₁] k₂) (hσ : σ ≠ AlgEquiv.refl) (n : ℕ) (a : k₁) :
    (stdHermSphereCount k₁ k₂ σ (n + 1) a : ℤ) =
      ((Fintype.card k₁ : ℤ) + 1) * (Fintype.card k₁ : ℤ) ^ (2 * n) -
        (Fintype.card k₁ : ℤ) * (stdHermSphereCount k₁ k₂ σ n a : ℤ) := by
  classical
  set q := Fintype.card k₁
  have hcard2 : Fintype.card k₂ = q ^ 2 := card_quad_ext_eq_sq hdim
  let g : (Fin n → k₂) → k₁ := fun w =>
    Classical.choose (herm_sum_norm_mem_base hdim σ hσ w)
  have hg : ∀ w : Fin n → k₂,
      ∑ i : Fin n, σ (w i) * w i = algebraMap k₁ k₂ (g w) := fun w =>
    Classical.choose_spec (herm_sum_norm_mem_base hdim σ hσ w)
  have hsum_all : (∑ b : k₁, stdHermSphereCount k₁ k₂ σ n b) = q ^ (2 * n) := by
    have hpart := Finset.card_eq_sum_card_fiberwise (f := g) (s := Finset.univ) (t := Finset.univ)
      (fun _ _ => Finset.mem_univ _)
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, hcard2, ← pow_mul] at hpart
    rw [hpart]
    refine Finset.sum_congr rfl fun b _ => ?_
    unfold stdHermSphereCount
    rw [Nat.card_eq_fintype_card, ← Fintype.card_coe]
    refine Fintype.card_congr ?_
    refine
      { toFun := fun ⟨w, hw⟩ => ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          (RingHom.injective (algebraMap k₁ k₂)) ((hg w).symm.trans hw)⟩⟩
        invFun := fun ⟨w, hw⟩ => ⟨w, by
          have hgw : g w = b := (Finset.mem_filter.mp hw).2
          rw [hg w, hgw]⟩
        left_inv := fun ⟨_, _⟩ => rfl
        right_inv := fun ⟨_, _⟩ => rfl }
  let T := { x : k₂ × (Fin n → k₂) // σ x.1 * x.1 + ∑ i : Fin n, σ (x.2 i) * x.2 i =
    algebraMap k₁ k₂ a }
  have e_split : { v : Fin (n + 1) → k₂ // ∑ i : Fin (n + 1), σ (v i) * v i = algebraMap k₁ k₂ a } ≃ T :=
    { toFun := fun ⟨v, hv⟩ => ⟨(v 0, Fin.tail v), by
        rw [Fin.sum_univ_succ] at hv
        exact hv⟩
      invFun := fun ⟨⟨x, w⟩, hxw⟩ => ⟨Fin.cons x w, by
        rw [Fin.sum_univ_succ]
        exact hxw⟩
      left_inv := fun ⟨v, _⟩ => by ext i; cases i using Fin.cases <;> rfl
      right_inv := fun ⟨⟨_, _⟩, _⟩ => rfl }
  let normOf : k₂ → k₁ := fun x => Classical.choose (sigma_norm_mem_base hdim σ hσ x)
  have hnorm_spec : ∀ x, x * σ x = algebraMap k₁ k₂ (normOf x) := fun x =>
    Classical.choose_spec (sigma_norm_mem_base hdim σ hσ x)
  have hT_card : Fintype.card T =
      ∑ x : k₂, stdHermSphereCount k₁ k₂ σ n (a - normOf x) := by
    have hpart := Finset.card_eq_sum_card_fiberwise
      (f := fun p : T => p.1.1) (s := Finset.univ) (t := Finset.univ)
      (fun _ _ => Finset.mem_univ _)
    rw [Finset.card_univ] at hpart
    rw [hpart]
    refine Finset.sum_congr rfl fun x0 _ => ?_
    unfold stdHermSphereCount
    rw [Nat.card_eq_fintype_card, ← Fintype.card_coe]
    refine Fintype.card_congr ?_
    refine
      { toFun := fun ⟨⟨⟨x', w⟩, hxw⟩, hmem⟩ => ⟨w, by
          have hx' : x' = x0 := (Finset.mem_filter.mp hmem).2
          rw [hx'] at hxw
          rw [map_sub, ← hnorm_spec x0]
          have h1 : σ x0 * x0 = x0 * σ x0 := mul_comm _ _
          linear_combination hxw - h1⟩
        invFun := fun ⟨w, hw⟩ => ⟨⟨(x0, w), by
          rw [map_sub, ← hnorm_spec x0] at hw
          have h1 : σ x0 * x0 = x0 * σ x0 := mul_comm _ _
          linear_combination hw + h1⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩
        left_inv := fun ⟨⟨⟨x', w⟩, hxw⟩, hmem⟩ => by
          have hx' : x' = x0 := (Finset.mem_filter.mp hmem).2
          subst hx'; rfl
        right_inv := fun ⟨_, _⟩ => rfl }
  have hfib_sum : (∑ x : k₂, stdHermSphereCount k₁ k₂ σ n (a - normOf x)) =
      ∑ c : k₁, Fintype.card { x : k₂ // normOf x = c } *
        stdHermSphereCount k₁ k₂ σ n (a - c) := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := normOf) (t := Finset.univ)
      (fun _ _ => Finset.mem_univ _)]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.sum_congr rfl (fun x hx => by rw [(Finset.mem_filter.mp hx).2]),
      Finset.sum_const, smul_eq_mul]
    congr 1
    rw [← Fintype.card_coe]
    exact Fintype.card_congr
      { toFun := fun ⟨x, hx⟩ => ⟨x, (Finset.mem_filter.mp hx).2⟩
        invFun := fun ⟨x, hx⟩ => ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩⟩
        left_inv := fun ⟨_, _⟩ => rfl
        right_inv := fun ⟨_, _⟩ => rfl }
  have hcard_norm_0 : Fintype.card { x : k₂ // normOf x = 0 } = 1 := by
    have heq : ∀ x : k₂, normOf x = 0 ↔ x = 0 := by
      intro x
      constructor
      · intro h0
        have h1 : x * σ x = 0 := by rw [hnorm_spec x, h0, map_zero]
        rcases mul_eq_zero.mp h1 with h | h
        · exact h
        · have := congrArg σ h
          simpa [sigma_involutive hdim σ hσ] using this
      · intro h0; subst h0
        apply (RingHom.injective (algebraMap k₁ k₂))
        simpa [map_zero] using (hnorm_spec 0).symm
    refine Fintype.card_eq_one_iff.mpr ⟨⟨0, (heq 0).mpr rfl⟩, fun ⟨x, hx⟩ => ?_⟩
    ext; exact (heq x).mp hx
  have hcard_norm_ne : ∀ c : k₁, c ≠ 0 → Fintype.card { x : k₂ // normOf x = c } = q + 1 := by
    intro c hc
    have heq : Fintype.card { x : k₂ // normOf x = c } =
        Fintype.card { x : k₂ // x * σ x = algebraMap k₁ k₂ c } :=
      Fintype.card_congr
        { toFun := fun ⟨x, hx⟩ => ⟨x, by rw [hnorm_spec x, hx]⟩
          invFun := fun ⟨x, hx⟩ => ⟨x, (RingHom.injective (algebraMap k₁ k₂)) (by rw [← hnorm_spec x, hx])⟩
          left_inv := fun ⟨_, _⟩ => rfl
          right_inv := fun ⟨_, _⟩ => rfl }
    rw [heq]
    exact card_norm_fiber_nonzero hdim σ hσ c hc
  have hsplit_sum :
      (∑ c : k₁, (Fintype.card { x : k₂ // normOf x = c } : ℤ) *
          (stdHermSphereCount k₁ k₂ σ n (a - c) : ℤ)) =
        (stdHermSphereCount k₁ k₂ σ n a : ℤ) +
          ((q : ℤ) + 1) * ∑ c ∈ Finset.univ.erase (0 : k₁),
            (stdHermSphereCount k₁ k₂ σ n (a - c) : ℤ) := by
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (0 : k₁)),
      hcard_norm_0, sub_zero, Nat.cast_one, one_mul]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun c hc => ?_
    have hc0 : c ≠ 0 := (Finset.mem_erase.mp hc).1
    rw [hcard_norm_ne c hc0]
    push_cast; rfl
  have hsub_sum :
      (∑ c ∈ Finset.univ.erase (0 : k₁), (stdHermSphereCount k₁ k₂ σ n (a - c) : ℤ)) =
        (q : ℤ) ^ (2 * n) - (stdHermSphereCount k₁ k₂ σ n a : ℤ) := by
    have hbij : (∑ c : k₁, stdHermSphereCount k₁ k₂ σ n (a - c)) =
        ∑ b : k₁, stdHermSphereCount k₁ k₂ σ n b :=
      Fintype.sum_equiv (Equiv.subLeft a) _ _ (fun _ => rfl)
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (0 : k₁)), sub_zero] at hbij
    rw [hsum_all] at hbij
    zify at hbij
    linarith
  have hfin : (stdHermSphereCount k₁ k₂ σ (n + 1) a : ℤ) =
      ∑ x : k₂, (stdHermSphereCount k₁ k₂ σ n (a - normOf x) : ℤ) := by
    have hcard_eq : stdHermSphereCount k₁ k₂ σ (n + 1) a =
        ∑ x : k₂, stdHermSphereCount k₁ k₂ σ n (a - normOf x) := by
      change Nat.card _ = ∑ x : k₂, stdHermSphereCount k₁ k₂ σ n (a - normOf x)
      rw [Nat.card_eq_fintype_card, Fintype.card_congr e_split, hT_card]
    exact_mod_cast hcard_eq
  rw [hfin, show (∑ x : k₂, (stdHermSphereCount k₁ k₂ σ n (a - normOf x) : ℤ)) =
      ∑ c : k₁, (Fintype.card { x : k₂ // normOf x = c } : ℤ) *
        (stdHermSphereCount k₁ k₂ σ n (a - c) : ℤ) by exact_mod_cast hfib_sum,
    hsplit_sum, hsub_sum]
  ring

/-- Exact closed form for `stdHermSphereCount` at both `a = 0` and `a ≠ 0` (`n ≥ 1`). -/
theorem card_std_sphere_exact (hdim : Module.finrank k₁ k₂ = 2)
    (σ : k₂ ≃ₐ[k₁] k₂) (hσ : σ ≠ AlgEquiv.refl) {n : ℕ} (hn : 1 ≤ n) (a : k₁) :
    (a = 0 → (stdHermSphereCount k₁ k₂ σ n a : ℤ) =
      (Fintype.card k₁ : ℤ) ^ (2 * n - 1) +
        (-1 : ℤ) ^ n * ((Fintype.card k₁ : ℤ) - 1) * (Fintype.card k₁ : ℤ) ^ (n - 1)) ∧
    (a ≠ 0 → (stdHermSphereCount k₁ k₂ σ n a : ℤ) =
      (Fintype.card k₁ : ℤ) ^ (n - 1) * ((Fintype.card k₁ : ℤ) ^ n - (-1 : ℤ) ^ n)) := by
  classical
  set q := Fintype.card k₁
  induction n, hn using Nat.le_induction with
  | base =>
    constructor
    · intro ha0
      subst ha0
      have h1 : stdHermSphereCount k₁ k₂ σ 1 0 = 1 := by
        unfold stdHermSphereCount
        rw [Nat.card_eq_fintype_card]
        refine Fintype.card_eq_one_iff.mpr ⟨⟨0, by simp⟩, fun ⟨v, hv⟩ => ?_⟩
        ext i
        fin_cases i
        simp only [Fin.sum_univ_one, Fin.isValue, map_zero] at hv
        rcases mul_eq_zero.mp hv with h | h
        · have := congrArg σ h
          simpa [sigma_involutive hdim σ hσ] using this
        · exact h
      rw [h1]
      simp
    · intro ha
      have h1 : stdHermSphereCount k₁ k₂ σ 1 a = q + 1 := by
        unfold stdHermSphereCount
        rw [Nat.card_eq_fintype_card]
        have heq : Fintype.card { v : Fin 1 → k₂ // ∑ i : Fin 1, σ (v i) * v i = algebraMap k₁ k₂ a } =
            Fintype.card { x : k₂ // x * σ x = algebraMap k₁ k₂ a } :=
          Fintype.card_congr
            { toFun := fun ⟨v, hv⟩ => ⟨v 0, by simpa [Fin.sum_univ_one, mul_comm] using hv⟩
              invFun := fun ⟨x, hx⟩ => ⟨fun _ => x, by simpa [Fin.sum_univ_one, mul_comm] using hx⟩
              left_inv := fun ⟨v, _⟩ => by ext i; fin_cases i; rfl
              right_inv := fun ⟨_, _⟩ => rfl }
        rw [heq]
        exact card_norm_fiber_nonzero hdim σ hσ a ha
      rw [h1]
      simp
  | succ m hm ih =>
    have hrec := stdHermSphereCount_succ hdim σ hσ m a
    have h2m_eq : 2 * m = (2 * m - 1) + 1 := by omega
    have h2m2_eq : 2 * (m + 1) - 1 = (2 * m - 1) + 2 := by omega
    have hm_eq : m = (m - 1) + 1 := by omega
    have hp2m : (q : ℤ) ^ (2 * m) = (q : ℤ) ^ (2 * m - 1) * (q : ℤ) := by
      conv_lhs => rw [h2m_eq, pow_succ]
    have hp2m2 : (q : ℤ) ^ (2 * (m + 1) - 1) = (q : ℤ) ^ (2 * m - 1) * (q : ℤ) ^ 2 := by
      conv_lhs => rw [h2m2_eq, pow_add]
    have hpm : (q : ℤ) ^ m = (q : ℤ) ^ (m - 1) * (q : ℤ) := by
      conv_lhs => rw [hm_eq, pow_succ]
    have hpneg : (-1 : ℤ) ^ (m + 1) = (-1 : ℤ) ^ m * (-1 : ℤ) := pow_succ _ _
    constructor
    · intro ha0
      have ihm := ih.1 ha0
      rw [hrec, ihm]
      change ((q : ℤ) + 1) * (q : ℤ) ^ (2 * m) -
          (q : ℤ) * ((q : ℤ) ^ (2 * m - 1) + (-1 : ℤ) ^ m * ((q : ℤ) - 1) * (q : ℤ) ^ (m - 1)) =
        (q : ℤ) ^ (2 * (m + 1) - 1) + (-1 : ℤ) ^ (m + 1) * ((q : ℤ) - 1) * (q : ℤ) ^ m
      rw [hp2m, hp2m2, hpm, hpneg]
      ring
    · intro ha
      have ihm := ih.2 ha
      rw [hrec, ihm]
      change ((q : ℤ) + 1) * (q : ℤ) ^ (2 * m) -
          (q : ℤ) * ((q : ℤ) ^ (m - 1) * ((q : ℤ) ^ m - (-1 : ℤ) ^ m)) =
        (q : ℤ) ^ m * ((q : ℤ) ^ (m + 1) - (-1 : ℤ) ^ (m + 1))
      have hp2m' : (q : ℤ) ^ (2 * m) = (q : ℤ) ^ m * (q : ℤ) ^ m := by
        conv_lhs => rw [show 2 * m = m + m by omega, pow_add]
      have hpm1 : (q : ℤ) ^ (m + 1) = (q : ℤ) ^ m * (q : ℤ) := pow_succ _ _
      rw [hp2m', hpm1, hpneg, hpm]
      ring

theorem card_std_sphere_one (hdim : Module.finrank k₁ k₂ = 2)
    (σ : k₂ ≃ₐ[k₁] k₂) (hσ : σ ≠ AlgEquiv.refl) {n : ℕ} (hn : 1 ≤ n) :
    (stdHermSphereCount k₁ k₂ σ n 1 : ℤ) =
      (Fintype.card k₁ : ℤ) ^ (n - 1) * ((Fintype.card k₁ : ℤ) ^ n - (-1 : ℤ) ^ n) :=
  (card_std_sphere_exact hdim σ hσ hn 1).2 one_ne_zero

/-- Any nonzero nondegenerate Hermitian space `(Fin n → k₂, H)` has a unit vector `⟪u, u⟫_H = 1`. -/
theorem exists_unit_vec_of_isHermMatrix (hdim : Module.finrank k₁ k₂ = 2)
    (σ : k₂ ≃ₐ[k₁] k₂) (hσ : σ ≠ AlgEquiv.refl) {n : ℕ} (hn : 1 ≤ n)
    {H : Matrix (Fin n) (Fin n) k₂} (hH : IsHermMatrix σ.toRingHom H) (hdet : H.det ≠ 0) :
    ∃ u : Fin n → k₂, hermPairing σ.toRingHom H u u = 1 := by
  have hinv : IsUnit H.det := isUnit_iff_ne_zero.mpr hdet
  have hmul_ne : ∃ x y : Fin n → k₂, hermPairing σ.toRingHom H x y ≠ 0 := by
    let e0 : Fin n → k₂ := Pi.single ⟨0, hn⟩ (1 : k₂)
    have hHe0 : H *ᵥ e0 ≠ 0 := by
      intro h0
      have h0' : H⁻¹ *ᵥ (H *ᵥ e0) = 0 := by rw [h0, Matrix.mulVec_zero]
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul H hinv, Matrix.one_mulVec] at h0'
      have := congrFun h0' ⟨0, hn⟩
      simp [e0] at this
    have hex : ∃ i, (H *ᵥ e0) i ≠ 0 := Function.ne_iff.mp hHe0
    obtain ⟨i, hi⟩ := hex
    refine ⟨Pi.single i (1 : k₂), e0, ?_⟩
    rw [hermPairing_eq_dotProduct]
    have hdot : dotProduct (fun j => σ.toRingHom (Pi.single (M := fun _ => k₂) i (1 : k₂) j))
        (H *ᵥ e0) = (H *ᵥ e0) i := by
      unfold dotProduct
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hj
        simp [hj]
      · intro hi_mem
        exact absurd (Finset.mem_univ i) hi_mem
    exact hdot ▸ hi
  have hne0 : ∃ v : Fin n → k₂, hermPairing σ.toRingHom H v v ≠ 0 := by
    by_contra h
    push Not at h
    obtain ⟨x, y, hxy⟩ := hmul_ne
    obtain ⟨α, hα⟩ := exists_trace_ne_zero σ hσ
    let c : k₂ := α / hermPairing σ.toRingHom H x y
    let y' : Fin n → k₂ := c • y
    have hxy' : hermPairing σ.toRingHom H x y' = α := by
      have hsm : hermPairing σ.toRingHom H x (c • y) = c * hermPairing σ.toRingHom H x y := by
        simp only [hermPairing, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        ring
      rw [hsm, div_mul_cancel₀ _ hxy]
    have h0 := h (x + y')
    have hsum : hermPairing σ.toRingHom H (x + y') (x + y') =
        hermPairing σ.toRingHom H x x + hermPairing σ.toRingHom H x y' +
          hermPairing σ.toRingHom H y' x + hermPairing σ.toRingHom H y' y' := by
      simp only [hermPairing, Pi.add_apply, map_add, add_mul, mul_add, Finset.sum_add_distrib]
      ring
    rw [hsum, h x, h y', zero_add, add_zero] at h0
    have hskew : hermPairing σ.toRingHom H y' x = σ (hermPairing σ.toRingHom H x y') :=
      (hermPairing_skew σ.toRingHom (sigma_involutive hdim σ hσ) hH y' x).symm
    rw [hskew, hxy'] at h0
    exact hα h0
  obtain ⟨v, hv⟩ := hne0
  have hv_fix : σ (hermPairing σ.toRingHom H v v) = hermPairing σ.toRingHom H v v :=
    hermPairing_skew σ.toRingHom (sigma_involutive hdim σ hσ) hH v v
  obtain ⟨a, ha⟩ : ∃ a : k₁, hermPairing σ.toRingHom H v v = algebraMap k₁ k₂ a := by
    have hqpow : (hermPairing σ.toRingHom H v v) ^ Fintype.card k₁ =
        hermPairing σ.toRingHom H v v := by
      rw [← sigma_eq_pow_card hdim σ hσ]; exact hv_fix
    exact fixed_by_pow_card_mem_base hdim hqpow
  have ha0 : a ≠ 0 := by
    intro h0; subst h0; simp only [map_zero] at ha; exact hv ha
  have hsurj_norm : ∃ c : k₂, c * σ c = algebraMap k₁ k₂ a⁻¹ := by
    have hpos : 0 < Fintype.card { x : k₂ // x * σ x = algebraMap k₁ k₂ a⁻¹ } := by
      rw [card_norm_fiber_nonzero hdim σ hσ a⁻¹ (inv_ne_zero ha0)]
      omega
    obtain ⟨⟨c, hc⟩⟩ := Fintype.card_pos_iff.mp hpos
    exact ⟨c, hc⟩
  obtain ⟨c, hc⟩ := hsurj_norm
  refine ⟨c • v, ?_⟩
  have hsm : hermPairing σ.toRingHom H (c • v) (c • v) =
      (c * σ c) * hermPairing σ.toRingHom H v v := by
    simp only [hermPairing, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    change σ.toRingHom c * σ.toRingHom (v i) * H i j * (c * v j) =
      c * σ.toRingHom c * (σ.toRingHom (v i) * H i j * v j)
    ring
  rw [hsm, hc, ha, ← map_mul, inv_mul_cancel₀ ha0, map_one]

/-- Block diagonal matrix `diag(1, A)` of size `(m + 1) × (m + 1)`. -/
def blockOneMatrix {R : Type*} [Zero R] [One R] {m : ℕ}
    (A : Matrix (Fin m) (Fin m) R) : Matrix (Fin (m + 1)) (Fin (m + 1)) R :=
  Matrix.of fun i j =>
    Fin.cases (Fin.cases 1 (fun _ => 0) j) (fun i' => Fin.cases 0 (fun j' => A i' j') j) i

lemma det_blockOneMatrix {R : Type*} [CommRing R] {m : ℕ}
    (A : Matrix (Fin m) (Fin m) R) : (blockOneMatrix A).det = A.det := by
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  have h00 : blockOneMatrix A 0 0 = 1 := rfl
  have hsub0 : (blockOneMatrix A).submatrix Fin.succ (0 : Fin (m + 1)).succAbove = A := by
    ext a b; rfl
  rw [h00, hsub0]
  have htail : ∑ i : Fin m, (-1 : R) ^ (i.succ : ℕ) * blockOneMatrix A 0 i.succ *
      ((blockOneMatrix A).submatrix Fin.succ i.succ.succAbove).det = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    have h0i : blockOneMatrix A 0 i.succ = 0 := rfl
    rw [h0i, mul_zero, zero_mul]
  rw [htail]
  simp

/-- Every nondegenerate Hermitian matrix `H` over `k₂` is congruent to the identity matrix `1`:
there exists `U ∈ GL (Fin n) k₂` with `hermConj σ U * H * U = 1`. -/
theorem exists_orthonormal_basis_of_isHermMatrix (hdim : Module.finrank k₁ k₂ = 2)
    (σ : k₂ ≃ₐ[k₁] k₂) (hσ : σ ≠ AlgEquiv.refl) :
    ∀ {n : ℕ} (H : Matrix (Fin n) (Fin n) k₂), IsHermMatrix σ.toRingHom H → H.det ≠ 0 →
      ∃ U : Matrix (Fin n) (Fin n) k₂, IsUnit U.det ∧ hermConj σ.toRingHom U * H * U = 1 := by
  intro n
  induction n with
  | zero =>
    intro H _ _
    refine ⟨1, by simp, ?_⟩
    ext i; exact Fin.elim0 i
  | succ m ih =>
    intro H hH hdet
    have hm1 : 1 ≤ m + 1 := by omega
    obtain ⟨u, hu⟩ := exists_unit_vec_of_isHermMatrix hdim σ hσ hm1 hH hdet
    let φ : (Fin (m + 1) → k₂) →ₗ[k₂] k₂ :=
      { toFun := fun w => hermPairing σ.toRingHom H u w
        map_add' := fun w₁ w₂ => by
          simp only [hermPairing, Pi.add_apply, mul_add, Finset.sum_add_distrib]
        map_smul' := fun c w => by
          simp only [hermPairing, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
          ring }
    have hφ_surj : LinearMap.range φ = ⊤ := by
      rw [Submodule.eq_top_iff']
      intro c
      refine ⟨c • u, ?_⟩
      rw [LinearMap.map_smul, smul_eq_mul]
      change c * hermPairing σ.toRingHom H u u = c
      rw [hu, mul_one]
    have hker_dim : Module.finrank k₂ (LinearMap.ker φ) = m := by
      have hrk := LinearMap.finrank_range_add_finrank_ker φ
      rw [hφ_surj, finrank_top, Module.finrank_fin_fun, Module.finrank_self] at hrk
      omega
    let b := Module.finBasisOfFinrankEq k₂ (LinearMap.ker φ) hker_dim
    let V₀ : Matrix (Fin (m + 1)) (Fin m) k₂ := Matrix.of fun i j => (b j).1 i
    let P : Matrix (Fin (m + 1)) (Fin (m + 1)) k₂ := Matrix.of fun i j =>
      Fin.cases (u i) (fun j' => V₀ i j') j
    let H' : Matrix (Fin m) (Fin m) k₂ := hermConj σ.toRingHom V₀ * H * V₀
    have hP_gram : hermConj σ.toRingHom P * H * P = blockOneMatrix H' := by
      ext i j
      have hcol : ∀ a b : Fin (m + 1),
          (hermConj σ.toRingHom P * H * P) a b =
            hermPairing σ.toRingHom H (fun r => P r a) (fun r => P r b) := by
        intro a b
        simp only [Matrix.mul_apply, hermConj_apply, hermPairing, Finset.sum_mul]
        rw [Finset.sum_comm]
      rw [hcol i j]
      cases i using Fin.cases with
      | zero =>
        cases j using Fin.cases with
        | zero =>
          simpa [P, blockOneMatrix] using hu
        | succ j' =>
          have hmem : hermPairing σ.toRingHom H u (b j').1 = 0 := LinearMap.mem_ker.mp (b j').2
          simpa [P, V₀, blockOneMatrix] using hmem
      | succ i' =>
        cases j using Fin.cases with
        | zero =>
          have h0 : hermPairing σ.toRingHom H u (b i').1 = 0 := LinearMap.mem_ker.mp (b i').2
          have hskew : σ.toRingHom (hermPairing σ.toRingHom H u (b i').1) =
              hermPairing σ.toRingHom H (b i').1 u :=
            hermPairing_skew σ.toRingHom (sigma_involutive hdim σ hσ) hH (b i').1 u
          rw [h0, map_zero] at hskew
          simpa [P, V₀, blockOneMatrix] using hskew.symm
        | succ j' =>
          have hH' : H' i' j' = hermPairing σ.toRingHom H (fun r => V₀ r i') (fun r => V₀ r j') := by
            simp only [H', Matrix.mul_apply, hermConj_apply, hermPairing, Finset.sum_mul]
            rw [Finset.sum_comm]
          simp [P, blockOneMatrix, hH']
    have hP_li : LinearIndependent k₂ (fun j : Fin (m + 1) => fun i : Fin (m + 1) => P i j) := by
      rw [Fintype.linearIndependent_iff]
      intro c hc
      have h0 : hermPairing σ.toRingHom H u (∑ j : Fin (m + 1), c j • fun i => P i j) = 0 := by
        rw [hc]
        simp [hermPairing]
      have h0_eval : c 0 = 0 := by
        have hlin : hermPairing σ.toRingHom H u (∑ j : Fin (m + 1), c j • fun i => P i j) =
            ∑ j : Fin (m + 1), c j * hermPairing σ.toRingHom H u (fun i => P i j) := by
          change φ (∑ j, c j • fun i => P i j) = ∑ j, c j * φ (fun i => P i j)
          simp only [map_sum, LinearMap.map_smul, smul_eq_mul]
        rw [hlin, Fin.sum_univ_succ] at h0
        have htail : ∑ j : Fin m, c j.succ * hermPairing σ.toRingHom H u (fun i => P i j.succ) = 0 := by
          refine Finset.sum_eq_zero fun j _ => ?_
          have hmem : hermPairing σ.toRingHom H u (b j).1 = 0 := LinearMap.mem_ker.mp (b j).2
          have hj0 : hermPairing σ.toRingHom H u (fun i => P i j.succ) = 0 := by
            simpa [P, V₀] using hmem
          rw [hj0, mul_zero]
        rw [htail, add_zero] at h0
        have hu0 : hermPairing σ.toRingHom H u (fun i => P i 0) = 1 := by simpa [P] using hu
        rwa [hu0, mul_one] at h0
      rw [Fin.sum_univ_succ, h0_eval, zero_smul, zero_add] at hc
      have hc_ker : ∑ j : Fin m, c j.succ • b j = 0 := by
        ext i
        have := congrFun hc i
        simpa [P, V₀] using this
      have hbi := b.linearIndependent
      rw [Fintype.linearIndependent_iff] at hbi
      have hcs := hbi (fun j => c j.succ) hc_ker
      intro j
      cases j using Fin.cases with
      | zero => exact h0_eval
      | succ j' => exact hcs j'
    have hP_det : P.det ≠ 0 := by
      intro hdet0
      obtain ⟨c, hc0, hPc⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet0
      apply hc0
      apply funext
      apply (Fintype.linearIndependent_iff.mp hP_li) c
      ext i
      have hi := congrFun hPc i
      simpa [Matrix.mulVec, dotProduct, mul_comm] using hi
    have hH'_herm : IsHermMatrix σ.toRingHom H' :=
      isHermMatrix_congr σ.toRingHom hH (sigma_involutive hdim σ hσ) V₀
    have hgram_det : (hermConj σ.toRingHom P * H * P).det ≠ 0 := by
      have hconj_det : (hermConj σ.toRingHom P).det = σ P.det := by
        change (P.map σ.toRingHom).transpose.det = σ.toRingHom P.det
        rw [Matrix.det_transpose]
        exact (RingHom.map_det σ.toRingHom P).symm
      rw [Matrix.det_mul, Matrix.det_mul, hconj_det]
      exact mul_ne_zero (mul_ne_zero ((map_ne_zero _).mpr hP_det) hdet) hP_det
    have hH'_det : H'.det ≠ 0 := by
      rw [hP_gram, det_blockOneMatrix] at hgram_det
      exact hgram_det
    obtain ⟨U', hU'_unit, hU'⟩ := ih H' hH'_herm hH'_det
    let Q : Matrix (Fin (m + 1)) (Fin (m + 1)) k₂ := blockOneMatrix U'
    refine ⟨P * Q, ?_, ?_⟩
    · rw [Matrix.det_mul, show Q.det = U'.det from det_blockOneMatrix U']
      exact (isUnit_iff_ne_zero.mpr hP_det).mul hU'_unit
    · have hPQ_assoc : hermConj σ.toRingHom (P * Q) * H * (P * Q) =
          hermConj σ.toRingHom Q * (hermConj σ.toRingHom P * H * P) * Q := by
        rw [hermConj_mul]
        simp only [Matrix.mul_assoc]
      rw [hPQ_assoc, hP_gram]
      ext i j
      have hPQ_entry : (hermConj σ.toRingHom Q * blockOneMatrix H' * Q) i j =
          blockOneMatrix (hermConj σ.toRingHom U' * H' * U') i j := by
        simp only [Matrix.mul_apply, hermConj_apply, Q, blockOneMatrix]
        rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i', rfl⟩
        · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j', rfl⟩ <;> simp [Fin.sum_univ_succ]
        · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j', rfl⟩
          · simp [Fin.sum_univ_succ]
          · simp only [Fin.sum_univ_succ, Fin.cases_zero, Fin.cases_succ, Matrix.of_apply,
              map_zero, zero_mul, zero_add, mul_zero, Finset.sum_const_zero]
      rw [hPQ_entry, hU']
      rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i', rfl⟩
      · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j', rfl⟩
        · simp [blockOneMatrix, Matrix.one_apply]
        · simp [blockOneMatrix, Matrix.one_apply, (Fin.succ_ne_zero j').symm]
      · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j', rfl⟩
        · simp [blockOneMatrix, Matrix.one_apply, Fin.succ_ne_zero i']
        · simp [blockOneMatrix, Matrix.one_apply]

/-- The finite unitary group `U(H)(k₂/k₁)` of matrices preserving `H`. -/
def FiniteUnitaryGroup (k₁ k₂ : Type*) [Field k₁] [Fintype k₁] [Field k₂] [Fintype k₂]
    [Algebra k₁ k₂] (σ : k₂ ≃ₐ[k₁] k₂) {n : ℕ} (H : Matrix (Fin n) (Fin n) k₂) : Type _ :=
  { U : Matrix (Fin n) (Fin n) k₂ // hermConj σ.toRingHom U * H * U = H }

instance (k₁ k₂ : Type*) [Field k₁] [Fintype k₁] [Field k₂] [Fintype k₂]
    [Algebra k₁ k₂] (σ : k₂ ≃ₐ[k₁] k₂) {n : ℕ} (H : Matrix (Fin n) (Fin n) k₂)
    [DecidableEq k₂] : Fintype (FiniteUnitaryGroup k₁ k₂ σ H) :=
  inferInstanceAs (Fintype { U : Matrix (Fin n) (Fin n) k₂ // hermConj σ.toRingHom U * H * U = H })

/-- Exact integer formula for `|U_n(𝔽_q)|`: `q^{n(n-1)/2} ∏_{j=1}^n (q^j - (-1)^j)`. -/
def unitaryGroupOrderZ (q n : ℕ) : ℤ :=
  (q : ℤ) ^ (n * (n - 1) / 2) * ∏ j ∈ Finset.Icc 1 n, ((q : ℤ) ^ j - (-1 : ℤ) ^ j)

/-- Exact real formula for `|U_n(𝔽_q)|`: `q^{n(n-1)/2} ∏_{j=1}^n (q^j - (-1)^j)`. -/
def unitaryGroupOrder (q n : ℕ) : ℝ :=
  (q : ℝ) ^ (n * (n - 1) / 2) * ∏ j ∈ Finset.Icc 1 n, ((q : ℝ) ^ j - (-1 : ℝ) ^ j)

lemma unitaryGroupOrder_eq_cast (q n : ℕ) :
    unitaryGroupOrder q n = (unitaryGroupOrderZ q n : ℝ) := by
  unfold unitaryGroupOrder unitaryGroupOrderZ
  push_cast
  rfl

lemma unitaryGroupOrder_pos {q : ℕ} (hq : 2 ≤ q) (n : ℕ) : 0 < unitaryGroupOrder q n := by
  unfold unitaryGroupOrder
  refine mul_pos (pow_pos (by exact_mod_cast (by omega : 0 < q)) _) ?_
  refine Finset.prod_pos fun j hj => ?_
  have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
  have hqj : (2 : ℝ) ≤ (q : ℝ) ^ j := by
    calc (2 : ℝ) ≤ (q : ℝ) ^ 1 := by rw [pow_one]; exact_mod_cast hq
      _ ≤ (q : ℝ) ^ j := pow_le_pow_right₀ (by exact_mod_cast (by omega : 1 ≤ q)) hj1
  have hneg : (-1 : ℝ) ^ j ≤ 1 := by
    rcases Nat.even_or_odd j with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · simp
    · rw [pow_succ, pow_mul]; norm_num
  linarith

/-- Equivalence between `FiniteUnitaryGroup σ H` and `FiniteUnitaryGroup σ 1` when `H` is
nondegenerate Hermitian. -/
theorem card_finiteUnitaryGroup_eq_std (hdim : Module.finrank k₁ k₂ = 2)
    (σ : k₂ ≃ₐ[k₁] k₂) (hσ : σ ≠ AlgEquiv.refl)
    {n : ℕ} (H : Matrix (Fin n) (Fin n) k₂) (hH : IsHermMatrix σ.toRingHom H) (hdet : H.det ≠ 0) :
    Fintype.card (FiniteUnitaryGroup k₁ k₂ σ H) =
      Fintype.card (FiniteUnitaryGroup k₁ k₂ σ (1 : Matrix (Fin n) (Fin n) k₂)) := by
  obtain ⟨P, hP_unit, hP⟩ := exists_orthonormal_basis_of_isHermMatrix hdim σ hσ H hH hdet
  let Pinv : Matrix (Fin n) (Fin n) k₂ := P⁻¹
  have hPPinv : P * Pinv = 1 := Matrix.mul_nonsing_inv P hP_unit
  have hPinvP : Pinv * P = 1 := Matrix.nonsing_inv_mul P hP_unit
  have hH_eq : H = hermConj σ.toRingHom Pinv * Pinv := by
    calc H = 1 * H * 1 := by rw [Matrix.one_mul, Matrix.mul_one]
      _ = (hermConj σ.toRingHom Pinv * hermConj σ.toRingHom P) * H * (P * Pinv) := by
          rw [← hermConj_mul, hPPinv, hermConj_one]
      _ = hermConj σ.toRingHom Pinv * (hermConj σ.toRingHom P * H * P) * Pinv := by
          simp only [Matrix.mul_assoc]
      _ = hermConj σ.toRingHom Pinv * 1 * Pinv := by rw [hP]
      _ = hermConj σ.toRingHom Pinv * Pinv := by rw [Matrix.mul_one]
  let e : FiniteUnitaryGroup k₁ k₂ σ H ≃
      FiniteUnitaryGroup k₁ k₂ σ (1 : Matrix (Fin n) (Fin n) k₂) :=
    { toFun := fun ⟨U, hU⟩ => ⟨Pinv * U * P, by
        rw [Matrix.mul_one]
        have hstep1 : hermConj σ.toRingHom (Pinv * U * P) * (Pinv * U * P) =
            hermConj σ.toRingHom P * ((hermConj σ.toRingHom U *
              (hermConj σ.toRingHom Pinv * Pinv) * U) * P) := by
          rw [hermConj_mul, hermConj_mul]
          simp only [Matrix.mul_assoc]
        rw [hstep1, ← hH_eq, hU]
        calc hermConj σ.toRingHom P * (H * P)
            = hermConj σ.toRingHom P * H * P := (Matrix.mul_assoc _ _ _).symm
          _ = 1 := hP⟩
      invFun := fun ⟨V, hV⟩ => ⟨P * V * Pinv, by
        have hV' : hermConj σ.toRingHom V * V = 1 := by simpa using hV
        have hstep1 : hermConj σ.toRingHom (P * V * Pinv) * H * (P * V * Pinv) =
            hermConj σ.toRingHom Pinv * (hermConj σ.toRingHom V *
              (hermConj σ.toRingHom P * H * P) * V) * Pinv := by
          rw [hermConj_mul, hermConj_mul]
          simp only [Matrix.mul_assoc]
        rw [hstep1, hP, Matrix.mul_one, hV', Matrix.mul_one, ← hH_eq]⟩
      left_inv := fun ⟨U, _⟩ => Subtype.ext (by
        calc P * (Pinv * U * P) * Pinv
            = (P * Pinv) * U * (P * Pinv) := by simp only [Matrix.mul_assoc]
          _ = U := by rw [hPPinv, Matrix.one_mul, Matrix.mul_one])
      right_inv := fun ⟨V, _⟩ => Subtype.ext (by
        calc Pinv * (P * V * Pinv) * P
            = (Pinv * P) * V * (Pinv * P) := by simp only [Matrix.mul_assoc]
          _ = V := by rw [hPinvP, Matrix.one_mul, Matrix.mul_one]) }
  exact Fintype.card_congr e

omit [DecidableEq k₁] in
/-- Exact finite-field isometric embedding count `#{X : Mat_{m × n}(k₂) | X^* H X = T}`
for nondegenerate Hermitian `H` (`m × m`) and `T` (`n × n`) with `n ≤ m`. -/
theorem card_finite_herm_rep (hdim : Module.finrank k₁ k₂ = 2)
    (σ : k₂ ≃ₐ[k₁] k₂) (hσ : σ ≠ AlgEquiv.refl) :
    ∀ (m n : ℕ), n ≤ m →
      ∀ (H : Matrix (Fin m) (Fin m) k₂), IsHermMatrix σ.toRingHom H → H.det ≠ 0 →
        ∀ (T : Matrix (Fin n) (Fin n) k₂), IsHermMatrix σ.toRingHom T → T.det ≠ 0 →
      (Fintype.card { X : Matrix (Fin m) (Fin n) k₂ // hermConj σ.toRingHom X * H * X = T } : ℤ) =
        ∏ j ∈ Finset.Icc (m - n + 1) m,
          (Fintype.card k₁ : ℤ) ^ (j - 1) * ((Fintype.card k₁ : ℤ) ^ j - (-1 : ℤ) ^ j) := by
  classical
  set q := Fintype.card k₁
  intro m n hnm H hH hHdet T hT hTdet
  obtain ⟨P, hP_unit, hP⟩ := exists_orthonormal_basis_of_isHermMatrix hdim σ hσ H hH hHdet
  obtain ⟨Q, hQ_unit, hQ⟩ := exists_orthonormal_basis_of_isHermMatrix hdim σ hσ T hT hTdet
  let Pinv : Matrix (Fin m) (Fin m) k₂ := P⁻¹
  let Qinv : Matrix (Fin n) (Fin n) k₂ := Q⁻¹
  have hPPinv : P * Pinv = 1 := Matrix.mul_nonsing_inv P hP_unit
  have hPinvP : Pinv * P = 1 := Matrix.nonsing_inv_mul P hP_unit
  have hQQinv : Q * Qinv = 1 := Matrix.mul_nonsing_inv Q hQ_unit
  have hQinvQ : Qinv * Q = 1 := Matrix.nonsing_inv_mul Q hQ_unit
  have hH_eq : H = hermConj σ.toRingHom Pinv * Pinv := by
    calc H = 1 * H * 1 := by rw [Matrix.one_mul, Matrix.mul_one]
      _ = (hermConj σ.toRingHom Pinv * hermConj σ.toRingHom P) * H * (P * Pinv) := by
          rw [← hermConj_mul, hPPinv, hermConj_one]
      _ = hermConj σ.toRingHom Pinv * (hermConj σ.toRingHom P * H * P) * Pinv := by
          simp only [Matrix.mul_assoc]
      _ = hermConj σ.toRingHom Pinv * 1 * Pinv := by rw [hP]
      _ = hermConj σ.toRingHom Pinv * Pinv := by rw [Matrix.mul_one]
  have hT_eq : T = hermConj σ.toRingHom Qinv * Qinv := by
    calc T = 1 * T * 1 := by rw [Matrix.one_mul, Matrix.mul_one]
      _ = (hermConj σ.toRingHom Qinv * hermConj σ.toRingHom Q) * T * (Q * Qinv) := by
          rw [← hermConj_mul, hQQinv, hermConj_one]
      _ = hermConj σ.toRingHom Qinv * (hermConj σ.toRingHom Q * T * Q) * Qinv := by
          simp only [Matrix.mul_assoc]
      _ = hermConj σ.toRingHom Qinv * 1 * Qinv := by rw [hQ]
      _ = hermConj σ.toRingHom Qinv * Qinv := by rw [Matrix.mul_one]
  let eRed : { X : Matrix (Fin m) (Fin n) k₂ // hermConj σ.toRingHom X * H * X = T } ≃
      { Y : Matrix (Fin m) (Fin n) k₂ // hermConj σ.toRingHom Y * Y = 1 } :=
    { toFun := fun ⟨X, hX⟩ => ⟨Pinv * X * Q, by
        have hstep1 : hermConj σ.toRingHom (Pinv * X * Q) * (Pinv * X * Q) =
            hermConj σ.toRingHom Q * (hermConj σ.toRingHom X *
              (hermConj σ.toRingHom Pinv * Pinv) * X) * Q := by
          rw [hermConj_mul, hermConj_mul]
          simp only [Matrix.mul_assoc]
        rw [hstep1, ← hH_eq, hX, hQ]⟩
      invFun := fun ⟨Y, hY⟩ => ⟨P * Y * Qinv, by
        have hstep1 : hermConj σ.toRingHom (P * Y * Qinv) * H * (P * Y * Qinv) =
            hermConj σ.toRingHom Qinv * (hermConj σ.toRingHom Y *
              (hermConj σ.toRingHom P * H * P) * Y) * Qinv := by
          rw [hermConj_mul, hermConj_mul]
          simp only [Matrix.mul_assoc]
        rw [hstep1, hP, Matrix.mul_one, hY, Matrix.mul_one, ← hT_eq]⟩
      left_inv := fun ⟨X, _⟩ => Subtype.ext (by
        calc P * (Pinv * X * Q) * Qinv
            = (P * Pinv) * X * (Q * Qinv) := by simp only [Matrix.mul_assoc]
          _ = X := by rw [hPPinv, hQQinv, Matrix.one_mul, Matrix.mul_one])
      right_inv := fun ⟨Y, _⟩ => Subtype.ext (by
        calc Pinv * (P * Y * Qinv) * Q
            = (Pinv * P) * Y * (Qinv * Q) := by simp only [Matrix.mul_assoc]
          _ = Y := by rw [hPinvP, hQinvQ, Matrix.one_mul, Matrix.mul_one]) }
  rw [Fintype.card_congr eRed]
  clear H hH hHdet T hT hTdet P hP_unit hP Pinv hPPinv hPinvP hH_eq Q hQ_unit hQ Qinv hQQinv hQinvQ hT_eq eRed
  induction n with
  | zero =>
    have hcard1 : Fintype.card { Y : Matrix (Fin m) (Fin 0) k₂ //
        hermConj σ.toRingHom Y * Y = 1 } = 1 :=
      Fintype.card_eq_one_iff.mpr ⟨⟨0, by ext i; exact Fin.elim0 i⟩, fun ⟨Y, _⟩ => by
        ext i j; exact Fin.elim0 j⟩
    rw [hcard1]
    have hIcc : Finset.Icc (m - 0 + 1) m = ∅ := by
      simp
    rw [hIcc, Finset.prod_empty]
    rfl
  | succ r ih =>
    have hrm : r ≤ m := by omega
    have ihr := ih hrm
    let castR : Fin r → Fin (r + 1) := Fin.castSucc
    let lastR : Fin (r + 1) := Fin.last r
    let Frame (k : ℕ) := { Y : Matrix (Fin m) (Fin k) k₂ // hermConj σ.toRingHom Y * Y = 1 }
    let projFrame : Frame (r + 1) → Frame r := fun ⟨Y, hY⟩ =>
      ⟨Matrix.of fun i j => Y i (castR j), by
        ext a b
        have hab := congrFun (congrFun hY (castR a)) (castR b)
        have hne : (castR a = castR b) ↔ (a = b) := Fin.castSucc_inj
        simpa [Matrix.mul_apply, hermConj_apply, Matrix.one_apply, hne] using hab⟩
    have hfib_equiv : ∀ Y₀ : Frame r,
        { Y : Frame (r + 1) // projFrame Y = Y₀ } ≃
          { v : Fin m → k₂ // (∀ j : Fin r, ∑ i : Fin m, σ (Y₀.1 i j) * v i = 0) ∧
            ∑ i : Fin m, σ (v i) * v i = 1 } := fun ⟨Y₀, hY₀⟩ =>
      { toFun := fun x => ⟨fun i => x.1.1 i lastR,
          ⟨fun j => by
            have hj_eq : ∀ i, x.1.1 i (castR j) = Y₀ i j := fun i =>
              congrFun (congrFun (congrArg Subtype.val x.2) i) j
            have hjl := congrFun (congrFun x.1.2 (castR j)) lastR
            have hne : castR j ≠ lastR := Fin.castSucc_ne_last j
            simpa [Matrix.mul_apply, hermConj_apply, Matrix.one_apply, hne, hj_eq] using hjl,
           by
            have hll := congrFun (congrFun x.1.2 lastR) lastR
            simpa [Matrix.mul_apply, hermConj_apply, Matrix.one_apply] using hll⟩⟩
        invFun := fun x =>
          ⟨⟨Matrix.of fun i j => Fin.lastCases (x.1 i) (fun j' => Y₀ i j') j, by
            ext a b
            cases a using Fin.lastCases with
            | last =>
              cases b using Fin.lastCases with
              | last =>
                simpa [Matrix.mul_apply, hermConj_apply, Matrix.one_apply] using x.2.2
              | cast b' =>
                have hb' := x.2.1 b'
                have hsk := congrArg σ hb'
                simp only [map_sum, map_mul, sigma_involutive hdim σ hσ, map_zero] at hsk
                have hne : lastR ≠ castR b' := (Fin.castSucc_ne_last b').symm
                rw [Matrix.one_apply, if_neg hne]
                simpa [Matrix.mul_apply, hermConj_apply, mul_comm] using hsk
            | cast a' =>
              cases b using Fin.lastCases with
              | last =>
                have hne : castR a' ≠ lastR := Fin.castSucc_ne_last a'
                simpa [Matrix.mul_apply, hermConj_apply, Matrix.one_apply, hne] using x.2.1 a'
              | cast b' =>
                have hab := congrFun (congrFun hY₀ a') b'
                simpa [Matrix.mul_apply, hermConj_apply, Matrix.one_apply, Fin.castSucc_inj] using hab⟩,
          Subtype.ext (by ext i j; simp [projFrame, castR])⟩
        left_inv := fun x => Subtype.ext (Subtype.ext (by
          ext i j
          cases j using Fin.lastCases with
          | last => simp [lastR]
          | cast j' =>
            have hj_eq : x.1.1 i (castR j') = Y₀ i j' :=
              congrFun (congrFun (congrArg Subtype.val x.2) i) j'
            simp [castR, hj_eq]))
        right_inv := fun x => Subtype.ext (by ext i; simp [lastR]) }
    have hpart := Finset.card_eq_sum_card_fiberwise (f := projFrame) (s := Finset.univ)
      (t := Finset.univ) (fun _ _ => Finset.mem_univ _)
    rw [Finset.card_univ] at hpart
    have hfib_card : ∀ Y₀ : { Y₀ : Matrix (Fin m) (Fin r) k₂ // hermConj σ.toRingHom Y₀ * Y₀ = 1 },
        (Fintype.card { v : Fin m → k₂ // (∀ j : Fin r, ∑ i : Fin m, σ (Y₀.1 i j) * v i = 0) ∧
          ∑ i : Fin m, σ (v i) * v i = 1 } : ℤ) =
          (q : ℤ) ^ ((m - r) - 1) * ((q : ℤ) ^ (m - r) - (-1 : ℤ) ^ (m - r)) := by
      intro ⟨Y₀, hY₀⟩
      let ψ : (Fin m → k₂) →ₗ[k₂] (Fin r → k₂) :=
        { toFun := fun v j => ∑ i : Fin m, σ (Y₀ i j) * v i
          map_add' := fun u v => by
            ext j; simp [mul_add, Finset.sum_add_distrib]
          map_smul' := fun c v => by
            ext j; simp [Finset.mul_sum, mul_left_comm] }
      have hψ_surj : LinearMap.range ψ = ⊤ := by
        rw [Submodule.eq_top_iff']
        intro w
        refine ⟨Y₀ *ᵥ w, ?_⟩
        ext j
        have hmul : (hermConj σ.toRingHom Y₀ * Y₀) *ᵥ w = w := by rw [hY₀, Matrix.one_mulVec]
        have hj := congrFun hmul j
        simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply, hermConj_apply,
          Finset.sum_mul] at hj
        rw [Finset.sum_comm] at hj
        calc ψ (Y₀ *ᵥ w) j
            = ∑ i : Fin m, σ (Y₀ i j) * ∑ k : Fin r, Y₀ i k * w k := by
                simp only [ψ, LinearMap.coe_mk, AddHom.coe_mk, Matrix.mulVec, dotProduct]
          _ = ∑ i : Fin m, ∑ k : Fin r, σ (Y₀ i j) * Y₀ i k * w k := by
                refine Finset.sum_congr rfl fun i _ => ?_
                rw [Finset.mul_sum]
                refine Finset.sum_congr rfl fun k _ => by ring
          _ = w j := hj
      have hker_dim : Module.finrank k₂ (LinearMap.ker ψ) = m - r := by
        have hrk := LinearMap.finrank_range_add_finrank_ker ψ
        rw [hψ_surj, finrank_top, Module.finrank_fin_fun, Module.finrank_fin_fun] at hrk
        omega
      let b := Module.finBasisOfFinrankEq k₂ (LinearMap.ker ψ) hker_dim
      let V : Matrix (Fin m) (Fin (m - r)) k₂ := Matrix.of fun i j => (b j).1 i
      let H_sub : Matrix (Fin (m - r)) (Fin (m - r)) k₂ := hermConj σ.toRingHom V * V
      have hH_sub_herm : IsHermMatrix σ.toRingHom H_sub := by
        simpa [H_sub, Matrix.mul_one] using
          isHermMatrix_congr σ.toRingHom (isHermMatrix_one σ.toRingHom m)
            (sigma_involutive hdim σ hσ) V
      have hH_sub_det : H_sub.det ≠ 0 := by
        intro hdet0
        obtain ⟨c, hc0, hHc⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet0
        let v : Fin m → k₂ := V *ᵥ c
        have hv_ker : v ∈ LinearMap.ker ψ := by
          have hv_sum : v = (∑ j : Fin (m - r), c j • (b j).1) := by
            ext i
            simp [v, V, Matrix.mulVec, dotProduct, Finset.sum_apply, smul_eq_mul, mul_comm]
          rw [hv_sum]
          exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (b j).2
        have hv_orth_ker : ∀ w ∈ LinearMap.ker ψ, ∑ i : Fin m, σ (w i) * v i = 0 := by
          intro w hw
          obtain ⟨d, hd⟩ : ∃ d : Fin (m - r) → k₂, w = V *ᵥ d := by
            let d := b.repr ⟨w, hw⟩
            refine ⟨d, ?_⟩
            have hrep := b.sum_repr ⟨w, hw⟩
            ext i
            have hi := congrFun (congrArg Subtype.val hrep) i
            simp only [V, Matrix.mulVec, dotProduct, Matrix.of_apply, d,
              AddSubmonoidClass.coe_finsetSum, SetLike.val_smul, Finset.sum_apply,
              Pi.smul_apply, smul_eq_mul] at hi ⊢
            rw [← hi]
            refine Finset.sum_congr rfl fun j _ => mul_comm _ _
          rw [hd]
          have hdot : (∑ i : Fin m, σ ((V *ᵥ d) i) * v i) =
              dotProduct (fun j => σ (d j)) (H_sub *ᵥ c) := by
            have h1 := (hermPairing_one σ.toRingHom (V *ᵥ d) (V *ᵥ c)).symm
            rw [hermPairing_mulVec, Matrix.mul_one, hermPairing_eq_dotProduct] at h1
            exact h1
          rw [hdot, hHc, dotProduct_zero]
        have hv_orth_all : ∀ x : Fin m → k₂, ∑ i : Fin m, σ (x i) * v i = 0 := by
          intro x
          let y := Y₀ *ᵥ (ψ x)
          let w := x - y
          have hw_ker : w ∈ LinearMap.ker ψ := by
            rw [LinearMap.mem_ker, map_sub]
            have hψy : ψ y = ψ x := by
              ext j
              have hmul : (hermConj σ.toRingHom Y₀ * Y₀) *ᵥ (ψ x) = ψ x := by
                rw [hY₀, Matrix.one_mulVec]
              have hj := congrFun hmul j
              simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply, hermConj_apply,
                Finset.sum_mul] at hj
              rw [Finset.sum_comm] at hj
              calc ψ y j
                  = ∑ i : Fin m, σ (Y₀ i j) * ∑ k : Fin r, Y₀ i k * (ψ x) k := by
                      simp only [ψ, LinearMap.coe_mk, AddHom.coe_mk, y, Matrix.mulVec, dotProduct]
                _ = ∑ i : Fin m, ∑ k : Fin r, σ (Y₀ i j) * Y₀ i k * (ψ x) k := by
                      refine Finset.sum_congr rfl fun i _ => ?_
                      rw [Finset.mul_sum]
                      refine Finset.sum_congr rfl fun k _ => by ring
                _ = ψ x j := hj
            rw [hψy, sub_self]
          have hy_orth : ∑ i : Fin m, σ (y i) * v i = 0 := by
            have hv0 := LinearMap.mem_ker.mp hv_ker
            have hsum : ∑ i : Fin m, σ ((Y₀ *ᵥ (ψ x)) i) * v i =
                ∑ j : Fin r, σ (ψ x j) * (ψ v j) := by
              calc ∑ i : Fin m, σ ((Y₀ *ᵥ (ψ x)) i) * v i
                  = ∑ i : Fin m, ∑ j : Fin r, σ (ψ x j) * (σ (Y₀ i j) * v i) := by
                      refine Finset.sum_congr rfl fun i _ => ?_
                      simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Finset.sum_mul]
                      refine Finset.sum_congr rfl fun j _ => by ring
                _ = ∑ j : Fin r, ∑ i : Fin m, σ (ψ x j) * (σ (Y₀ i j) * v i) := Finset.sum_comm
                _ = ∑ j : Fin r, σ (ψ x j) * (ψ v j) := by
                      refine Finset.sum_congr rfl fun j _ => ?_
                      rw [← Finset.mul_sum]; rfl
            rw [hsum, hv0]
            simp
          have hx_eq : x = y + w := (add_sub_cancel y x).symm
          rw [hx_eq]
          simp only [Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib, hy_orth,
            hv_orth_ker w hw_ker, add_zero]
        have hv0 : v = 0 := by
          ext i
          have h := hv_orth_all (Pi.single i 1)
          simp only [Pi.single_apply, apply_ite σ, map_one, map_zero, ite_mul, one_mul,
            zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] at h
          exact h
        have hbc : ∑ j : Fin (m - r), c j • b j = 0 := by
          ext i
          have hi := congrFun hv0 i
          simpa [v, V, Matrix.mulVec, dotProduct, Finset.sum_apply, smul_eq_mul,
            mul_comm] using hi
        have hli := b.linearIndependent
        rw [Fintype.linearIndependent_iff] at hli
        exact hc0 (funext (hli c hbc))
      obtain ⟨U_sub, hU_sub_unit, hU_sub⟩ :=
        exists_orthonormal_basis_of_isHermMatrix hdim σ hσ H_sub hH_sub_herm hH_sub_det
      let W_mat : Matrix (Fin m) (Fin (m - r)) k₂ := V * U_sub
      have hW_mat : hermConj σ.toRingHom W_mat * W_mat = 1 := by
        rw [hermConj_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (hermConj σ.toRingHom V),
          show hermConj σ.toRingHom V * V = H_sub from rfl, ← Matrix.mul_assoc, hU_sub]
      have hb_span : ∀ v ∈ LinearMap.ker ψ, ∃! w : Fin (m - r) → k₂, v = W_mat *ᵥ w := by
        intro v hv
        let d := b.repr ⟨v, hv⟩
        have hv_d : v = V *ᵥ d := by
          have hrep := b.sum_repr ⟨v, hv⟩
          ext i
          have hi := congrFun (congrArg Subtype.val hrep) i
          simp only [V, Matrix.mulVec, dotProduct, Matrix.of_apply, d,
            AddSubmonoidClass.coe_finsetSum, SetLike.val_smul, Finset.sum_apply,
            Pi.smul_apply, smul_eq_mul] at hi ⊢
          rw [← hi]
          exact Finset.sum_congr rfl fun j _ => mul_comm _ _
        refine ⟨U_sub⁻¹ *ᵥ d, ?_, ?_⟩
        · dsimp only [W_mat]
          rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_nonsing_inv U_sub hU_sub_unit,
            Matrix.mul_one, hv_d]
        · intro w hw
          have hWU : W_mat *ᵥ (U_sub⁻¹ *ᵥ d) = v := by
            dsimp only [W_mat]
            rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_nonsing_inv U_sub hU_sub_unit,
              Matrix.mul_one, hv_d]
          have hmul : (hermConj σ.toRingHom W_mat * W_mat) *ᵥ w =
              hermConj σ.toRingHom W_mat *ᵥ v := by
            rw [← Matrix.mulVec_mulVec, hw]
          rw [hW_mat, Matrix.one_mulVec] at hmul
          have hmul2 : (hermConj σ.toRingHom W_mat * W_mat) *ᵥ (U_sub⁻¹ *ᵥ d) =
              hermConj σ.toRingHom W_mat *ᵥ v := by
            rw [← Matrix.mulVec_mulVec, hWU]
          rw [hW_mat, Matrix.one_mulVec] at hmul2
          exact hmul.trans hmul2.symm
      let toSphere :
          { v : Fin m → k₂ // (∀ j : Fin r, ∑ i : Fin m, σ (Y₀ i j) * v i = 0) ∧
            ∑ i : Fin m, σ (v i) * v i = 1 } →
          { w : Fin (m - r) → k₂ // ∑ i : Fin (m - r), σ (w i) * w i = 1 } :=
        fun ⟨v, hv_orth, hv_norm⟩ =>
          have hv_ker : v ∈ LinearMap.ker ψ := by
            rw [LinearMap.mem_ker]; ext j; exact hv_orth j
          let w := Classical.choose (hb_span v hv_ker)
          ⟨w, by
            have hw : v = W_mat *ᵥ w := (Classical.choose_spec (hb_span v hv_ker)).1
            have hpair := hermPairing_mulVec σ.toRingHom
              (1 : Matrix (Fin m) (Fin m) k₂) W_mat w w
            rw [Matrix.mul_one, hW_mat, hermPairing_one, hermPairing_one, ← hw] at hpair
            exact hpair.symm.trans hv_norm⟩
      let invSphere :
          { w : Fin (m - r) → k₂ // ∑ i : Fin (m - r), σ (w i) * w i = 1 } →
          { v : Fin m → k₂ // (∀ j : Fin r, ∑ i : Fin m, σ (Y₀ i j) * v i = 0) ∧
            ∑ i : Fin m, σ (v i) * v i = 1 } :=
        fun ⟨w, hw⟩ => ⟨W_mat *ᵥ w,
          ⟨fun j => by
            have hmem : V *ᵥ (U_sub *ᵥ w) ∈ LinearMap.ker ψ := by
              have hsum : V *ᵥ (U_sub *ᵥ w) =
                  ∑ k : Fin (m - r), (U_sub *ᵥ w) k • (b k).1 := by
                ext i
                simp [V, Matrix.mulVec, dotProduct, Finset.sum_apply, smul_eq_mul,
                  mul_comm]
              rw [hsum]
              exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (b k).2
            rw [LinearMap.mem_ker] at hmem
            have hj := congrFun hmem j
            simpa [W_mat, Matrix.mulVec_mulVec, ψ] using hj,
          by
            have hpair := hermPairing_mulVec σ.toRingHom
              (1 : Matrix (Fin m) (Fin m) k₂) W_mat w w
            rw [Matrix.mul_one, hW_mat, hermPairing_one, hermPairing_one] at hpair
            exact hpair.trans hw⟩⟩
      let e_sphere :
          { v : Fin m → k₂ // (∀ j : Fin r, ∑ i : Fin m, σ (Y₀ i j) * v i = 0) ∧
            ∑ i : Fin m, σ (v i) * v i = 1 } ≃
          { w : Fin (m - r) → k₂ // ∑ i : Fin (m - r), σ (w i) * w i = 1 } :=
        { toFun := toSphere
          invFun := invSphere
          left_inv := fun ⟨v, hv_orth, hv_norm⟩ => by
            apply Subtype.ext
            have hv_ker : v ∈ LinearMap.ker ψ := by
              rw [LinearMap.mem_ker]; ext j; exact hv_orth j
            exact (Classical.choose_spec (hb_span v hv_ker)).1.symm
          right_inv := fun ⟨w, hw⟩ => by
            apply Subtype.ext
            let v := W_mat *ᵥ w
            have hv_ker : v ∈ LinearMap.ker ψ := by
              have hsum : V *ᵥ (U_sub *ᵥ w) =
                  ∑ k : Fin (m - r), (U_sub *ᵥ w) k • (b k).1 := by
                ext i
                simp [V, Matrix.mulVec, dotProduct, Finset.sum_apply, smul_eq_mul,
                  mul_comm]
              rw [show v = V *ᵥ (U_sub *ᵥ w) by simp [v, W_mat, Matrix.mulVec_mulVec], hsum]
              exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (b k).2
            exact ((Classical.choose_spec (hb_span v hv_ker)).2 w rfl).symm }
      rw [Fintype.card_congr e_sphere, ← Nat.card_eq_fintype_card]
      simpa [stdHermSphereCount, q] using card_std_sphere_one hdim σ hσ (by omega : 1 ≤ m - r)
    have hfib_sum : (Fintype.card (Frame (r + 1)) : ℤ) =
        ∑ Y₀ : Frame r, (q : ℤ) ^ ((m - r) - 1) * ((q : ℤ) ^ (m - r) - (-1 : ℤ) ^ (m - r)) := by
      rw [hpart]
      push_cast
      refine Finset.sum_congr rfl fun Y₀ _ => ?_
      rw [← Fintype.card_coe]
      have hcoe : Fintype.card ↥(Finset.univ.filter fun a => projFrame a = Y₀) =
          Fintype.card { Y : Frame (r + 1) // projFrame Y = Y₀ } :=
        Fintype.card_congr
          { toFun := fun ⟨Y, hY⟩ => ⟨Y, (Finset.mem_filter.mp hY).2⟩
            invFun := fun ⟨Y, hY⟩ => ⟨Y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hY⟩⟩
            left_inv := fun ⟨_, _⟩ => rfl
            right_inv := fun ⟨_, _⟩ => rfl }
      rw [hcoe, Fintype.card_congr (hfib_equiv Y₀), hfib_card Y₀]
    rw [show (Fintype.card { Y : Matrix (Fin m) (Fin (r + 1)) k₂ // hermConj σ.toRingHom Y * Y = 1 } : ℤ) =
        (Fintype.card (Frame (r + 1)) : ℤ) from rfl, hfib_sum, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
    rw [show (Fintype.card (Frame r) : ℤ) =
        (Fintype.card { Y : Matrix (Fin m) (Fin r) k₂ // hermConj σ.toRingHom Y * Y = 1 } : ℤ) from rfl,
      ihr]
    have hIcc : Finset.Icc (m - (r + 1) + 1) m =
        insert (m - r) (Finset.Icc (m - r + 1) m) := by
      ext j
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    have hnotmem : m - r ∉ Finset.Icc (m - r + 1) m := by
      simp [Finset.mem_Icc]
    rw [hIcc, Finset.prod_insert hnotmem]
    ring

/-- **Exact Cardinality of the Finite-Field Unitary Group `|U_n(𝔽_q)|`**:
`|U_n(𝔽_q)| = q^{n(n-1)/2} ∏_{j=1}^n (q^j - (-1)^j)`. -/
theorem card_finiteUnitaryGroup_eq (hdim : Module.finrank k₁ k₂ = 2)
    (σ : k₂ ≃ₐ[k₁] k₂) (hσ : σ ≠ AlgEquiv.refl)
    {n : ℕ} (H : Matrix (Fin n) (Fin n) k₂) (hH : IsHermMatrix σ.toRingHom H) (hdet : H.det ≠ 0) :
    (Fintype.card (FiniteUnitaryGroup k₁ k₂ σ H) : ℤ) =
      unitaryGroupOrderZ (Fintype.card k₁) n := by
  rw [card_finiteUnitaryGroup_eq_std hdim σ hσ H hH hdet]
  have hrep := card_finite_herm_rep hdim σ hσ n n le_rfl 1 (isHermMatrix_one σ.toRingHom n)
    (by simp) 1 (isHermMatrix_one σ.toRingHom n) (by simp)
  have hU_eq : Fintype.card (FiniteUnitaryGroup k₁ k₂ σ (1 : Matrix (Fin n) (Fin n) k₂)) =
      Fintype.card { X : Matrix (Fin n) (Fin n) k₂ //
        hermConj σ.toRingHom X * 1 * X = 1 } :=
    Fintype.card_congr (Equiv.refl _)
  rw [hU_eq, hrep, Nat.sub_self, zero_add]
  unfold unitaryGroupOrderZ
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  congr 2
  clear hrep hU_eq H hH hdet
  induction n with
  | zero => simp
  | succ k ih =>
    have hIcc : Finset.Icc 1 (k + 1) = insert (k + 1) (Finset.Icc 1 k) := by
      ext j; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have hnot : k + 1 ∉ Finset.Icc 1 k := by simp [Finset.mem_Icc]
    rw [hIcc, Finset.sum_insert hnot, ih]
    simp only [Nat.add_sub_cancel]
    have htri : (k + 1) * k / 2 = k + k * (k - 1) / 2 := by
      cases k with
      | zero => simp
      | succ m =>
        have h2 : (m + 2) * (m + 1) = 2 * (m + 1) + (m + 1) * m := by ring
        rw [h2, Nat.mul_add_div (by omega : 0 < 2)]
        simp only [Nat.add_sub_cancel]
    rw [htri]

theorem card_finiteUnitaryGroup_real (hdim : Module.finrank k₁ k₂ = 2)
    (σ : k₂ ≃ₐ[k₁] k₂) (hσ : σ ≠ AlgEquiv.refl)
    {n : ℕ} (H : Matrix (Fin n) (Fin n) k₂) (hH : IsHermMatrix σ.toRingHom H) (hdet : H.det ≠ 0) :
    (Fintype.card (FiniteUnitaryGroup k₁ k₂ σ H) : ℝ) =
      unitaryGroupOrder (Fintype.card k₁) n := by
  rw [unitaryGroupOrder_eq_cast, ← card_finiteUnitaryGroup_eq hdim σ hσ H hH hdet]
  rfl

omit [DecidableEq k₁] in
/-- Normalized finite-field representation count in the inert case equals
`∏_{j=m-n+1}^m (1 - (-1)^j q^{-j})`. -/
theorem card_finite_herm_rep_div (hdim : Module.finrank k₁ k₂ = 2)
    (σ : k₂ ≃ₐ[k₁] k₂) (hσ : σ ≠ AlgEquiv.refl)
    {m n : ℕ} (hnm : n ≤ m)
    (H : Matrix (Fin m) (Fin m) k₂) (hH : IsHermMatrix σ.toRingHom H) (hHdet : H.det ≠ 0)
    (T : Matrix (Fin n) (Fin n) k₂) (hT : IsHermMatrix σ.toRingHom T) (hTdet : T.det ≠ 0) :
    (Fintype.card { X : Matrix (Fin m) (Fin n) k₂ // hermConj σ.toRingHom X * H * X = T } : ℝ) /
        (Fintype.card k₁ : ℝ) ^ (2 * m * n - n ^ 2) =
      ∏ j ∈ Finset.Icc (m - n + 1) m,
        (1 - (-1 : ℝ) ^ j * (Fintype.card k₁ : ℝ) ^ (-(j : ℤ))) := by
  set q := Fintype.card k₁
  have hq0 : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_pos.ne'
  have hrep : (Fintype.card { X : Matrix (Fin m) (Fin n) k₂ //
      hermConj σ.toRingHom X * H * X = T } : ℝ) =
      ∏ j ∈ Finset.Icc (m - n + 1) m,
        (q : ℝ) ^ (j - 1) * ((q : ℝ) ^ j - (-1 : ℝ) ^ j) := by
    have h := card_finite_herm_rep hdim σ hσ m n hnm H hH hHdet T hT hTdet
    exact_mod_cast h
  rw [hrep]
  have hpow_sum : ∑ j ∈ Finset.Icc (m - n + 1) m, (2 * j - 1) = 2 * m * n - n ^ 2 := by
    have hsub : ∀ k, (∑ j ∈ Finset.Icc 1 k, (2 * j - 1)) = k ^ 2 := by
      intro k
      induction k with
      | zero => simp
      | succ r ih =>
        have hIcc : Finset.Icc 1 (r + 1) = insert (r + 1) (Finset.Icc 1 r) := by
          ext j; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
        rw [hIcc, Finset.sum_insert (by simp [Finset.mem_Icc]), ih]
        have hr2 : (r + 1) ^ 2 = r ^ 2 + 2 * r + 1 := by ring
        omega
    have hsplit : ∑ j ∈ Finset.Icc 1 m, (2 * j - 1) =
        (∑ j ∈ Finset.Icc 1 (m - n), (2 * j - 1)) +
          ∑ j ∈ Finset.Icc (m - n + 1) m, (2 * j - 1) := by
      have hdisj : Disjoint (Finset.Icc 1 (m - n)) (Finset.Icc (m - n + 1) m) := by
        rw [Finset.disjoint_left]; intro j h1 h2
        simp only [Finset.mem_Icc] at h1 h2; omega
      have hunion : Finset.Icc 1 (m - n) ∪ Finset.Icc (m - n + 1) m = Finset.Icc 1 m := by
        ext j; simp only [Finset.mem_union, Finset.mem_Icc]; omega
      rw [← Finset.sum_union hdisj, hunion]
    rw [hsub m, hsub (m - n)] at hsplit
    have hsq_le : (m - n) ^ 2 ≤ m ^ 2 := Nat.pow_le_pow_left (Nat.sub_le m n) 2
    have hn2_le : n ^ 2 ≤ 2 * m * n := by nlinarith
    have hsq : m ^ 2 - (m - n) ^ 2 = 2 * m * n - n ^ 2 := by
      zify [hnm, hsq_le, hn2_le]; ring
    omega
  have hprod_split : (∏ j ∈ Finset.Icc (m - n + 1) m,
      (q : ℝ) ^ (j - 1) * ((q : ℝ) ^ j - (-1 : ℝ) ^ j)) =
      (q : ℝ) ^ (2 * m * n - n ^ 2) *
        ∏ j ∈ Finset.Icc (m - n + 1) m, (1 - (-1 : ℝ) ^ j * (q : ℝ) ^ (-(j : ℤ))) := by
    rw [← hpow_sum, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j hj => ?_
    have hj1 : 1 ≤ j := by
      have := (Finset.mem_Icc.mp hj).1; omega
    have h2j : 2 * j - 1 = (j - 1) + j := by omega
    rw [h2j, pow_add, mul_assoc]
    congr 1
    rw [mul_sub, mul_one, _root_.zpow_neg, zpow_natCast, mul_left_comm,
      mul_inv_cancel₀ (pow_ne_zero j hq0), mul_one]
  rw [hprod_split, mul_div_cancel_left₀ _ (pow_ne_zero _ hq0)]

end QuadFiniteField

section SplitFiniteField

variable {k₁ : Type*} [Field k₁] [Fintype k₁] [DecidableEq k₁]

/-- Exact finite-field representation count in the **split** case:
`#{(X₁, X₂) ∈ Mat_{m×n}(k₁)² | X₂ᵀ A X₁ = T₁}` for `A ∈ GL_m(k₁)`, `T₁ ∈ GL_n(k₁)`, `n ≤ m`. -/
theorem card_finite_split_rep {m n : ℕ} (hnm : n ≤ m)
    (A : Matrix (Fin m) (Fin m) k₁) (hA : A.det ≠ 0)
    (T₁ : Matrix (Fin n) (Fin n) k₁) (hT : T₁.det ≠ 0) :
    (Fintype.card { X : Matrix (Fin m) (Fin n) k₁ × Matrix (Fin m) (Fin n) k₁ //
        X.2.transpose * A * X.1 = T₁ } : ℝ) /
        (Fintype.card k₁ : ℝ) ^ (2 * m * n - n ^ 2) =
      ∏ j ∈ Finset.Icc (m - n + 1) m, (1 - (Fintype.card k₁ : ℝ) ^ (-(j : ℤ))) := by
  classical
  set q := Fintype.card k₁
  have hq0 : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_pos.ne'
  let Tinv := T₁⁻¹
  have hTTinv : T₁ * Tinv = 1 := Matrix.mul_nonsing_inv T₁ (isUnit_iff_ne_zero.mpr hT)
  have hTinvT : Tinv * T₁ = 1 := Matrix.nonsing_inv_mul T₁ (isUnit_iff_ne_zero.mpr hT)
  let Ainv := A⁻¹
  have hAAinv : A * Ainv = 1 := Matrix.mul_nonsing_inv A (isUnit_iff_ne_zero.mpr hA)
  have hAinvA : Ainv * A = 1 := Matrix.nonsing_inv_mul A (isUnit_iff_ne_zero.mpr hA)
  let eRed : { X : Matrix (Fin m) (Fin n) k₁ × Matrix (Fin m) (Fin n) k₁ //
      X.2.transpose * A * X.1 = T₁ } ≃
      { Y : Matrix (Fin m) (Fin n) k₁ × Matrix (Fin m) (Fin n) k₁ //
        Y.2.transpose * Y.1 = 1 } :=
    { toFun := fun ⟨⟨X₁, X₂⟩, hX⟩ => ⟨(A * X₁, X₂ * Tinv.transpose), by
        dsimp only
        rw [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc,
          ← Matrix.mul_assoc X₂.transpose A X₁, hX, hTinvT]⟩
      invFun := fun ⟨⟨Y₁, Y₂⟩, hY⟩ => ⟨(Ainv * Y₁, Y₂ * T₁.transpose), by
        have hY' : Y₂.transpose * Y₁ = 1 := hY
        dsimp only
        rw [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc,
          Matrix.mul_assoc T₁, ← Matrix.mul_assoc A Ainv Y₁, hAAinv, Matrix.one_mul,
          hY', Matrix.mul_one]⟩
      left_inv := fun ⟨⟨X₁, X₂⟩, _⟩ => Subtype.ext (by
        dsimp only
        exact Prod.ext
          (by rw [← Matrix.mul_assoc, hAinvA, Matrix.one_mul])
          (by rw [Matrix.mul_assoc, ← Matrix.transpose_mul, hTTinv, Matrix.transpose_one, Matrix.mul_one]))
      right_inv := fun ⟨⟨Y₁, Y₂⟩, _⟩ => Subtype.ext (by
        dsimp only
        exact Prod.ext
          (by rw [← Matrix.mul_assoc, hAAinv, Matrix.one_mul])
          (by rw [Matrix.mul_assoc, ← Matrix.transpose_mul, hTinvT, Matrix.transpose_one, Matrix.mul_one])) }
  rw [Fintype.card_congr eRed]
  let InjMat := { Y₁ : Matrix (Fin m) (Fin n) k₁ // LinearIndependent k₁ (fun j => fun i => Y₁ i j) }
  let SplitPair := Σ (Y₁ : InjMat), { Y₂ : Matrix (Fin m) (Fin n) k₁ // Y₂.transpose * Y₁.1 = 1 }
  let eSigma : { Y : Matrix (Fin m) (Fin n) k₁ × Matrix (Fin m) (Fin n) k₁ //
      Y.2.transpose * Y.1 = 1 } ≃ SplitPair :=
    { toFun := fun ⟨⟨Y₁, Y₂⟩, hY⟩ => ⟨⟨Y₁, by
        rw [Fintype.linearIndependent_iff]
        intro c hc
        have h1 : Y₂.transpose *ᵥ (∑ j : Fin n, c j • fun i => Y₁ i j) = 0 := by
          rw [hc, Matrix.mulVec_zero]
        have h2 : Y₂.transpose *ᵥ (∑ j : Fin n, c j • fun i => Y₁ i j) =
            (Y₂.transpose * Y₁) *ᵥ c := by
          ext k
          simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
            Finset.mul_sum, Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
          ring
        rw [h2, hY, Matrix.one_mulVec] at h1
        exact congrFun h1⟩, ⟨Y₂, hY⟩⟩
      invFun := fun ⟨⟨Y₁, _⟩, ⟨Y₂, hY⟩⟩ => ⟨(Y₁, Y₂), hY⟩
      left_inv := fun ⟨⟨_, _⟩, _⟩ => rfl
      right_inv := fun ⟨⟨_, _⟩, _⟩ => rfl }
  have hfib : ∀ Y₁ : InjMat,
      Fintype.card { Y₂ : Matrix (Fin m) (Fin n) k₁ // Y₂.transpose * Y₁.1 = 1 } =
        q ^ ((m - n) * n) := by
    intro ⟨Y₁, hY₁⟩
    let L : Matrix (Fin m) (Fin n) k₁ →ₗ[k₁] Matrix (Fin n) (Fin n) k₁ :=
      { toFun := fun Y₂ => Y₂.transpose * Y₁
        map_add' := fun A B => by rw [Matrix.transpose_add, Matrix.add_mul]
        map_smul' := fun c A => by rw [Matrix.transpose_smul, Matrix.smul_mul]; rfl }
    have hcols_surj : Function.Surjective L := by
      let f : (Fin n → k₁) →ₗ[k₁] (Fin m → k₁) := Matrix.mulVecLin Y₁
      have hf_inj : Function.Injective f := by
        rw [injective_iff_map_eq_zero]
        intro c hc
        rw [Fintype.linearIndependent_iff] at hY₁
        apply funext
        apply hY₁ c
        ext i
        have hi := congrFun hc i
        simpa [f, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, mul_comm] using hi
      obtain ⟨g, hg⟩ := f.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hf_inj)
      let Z : Matrix (Fin n) (Fin m) k₁ := Matrix.of fun i j => g (Pi.single j (1 : k₁)) i
      have hZY : Z * Y₁ = 1 := by
        ext a b
        have hgb : g (f (Pi.single (M := fun _ => k₁) b (1 : k₁))) a =
            (Pi.single (M := fun _ => k₁) b (1 : k₁)) a := by
          simpa [LinearMap.comp_apply, LinearMap.id_apply] using
            congrFun (LinearMap.congr_fun hg (Pi.single (M := fun _ => k₁) b (1 : k₁))) a
        have hfb : f (Pi.single (M := fun _ => k₁) b (1 : k₁)) = fun j => Y₁ j b := by
          ext j
          simp only [f, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct]
          rw [Finset.sum_eq_single b]
          · simp
          · intro x _ hx; simp [Pi.single_eq_of_ne hx]
          · intro hb; exact absurd (Finset.mem_univ b) hb
        have hdecomp : (fun j => Y₁ j b) = ∑ j : Fin m, Y₁ j b • Pi.single j (1 : k₁) := by
          ext j; simp [Finset.sum_apply, Pi.single_apply]
        rw [hfb, hdecomp, map_sum] at hgb
        simp only [LinearMap.map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
          Pi.single_apply] at hgb
        simpa [Z, Matrix.mul_apply, Matrix.one_apply, mul_comm] using hgb
      intro M
      refine ⟨Z.transpose * M.transpose, ?_⟩
      change (Z.transpose * M.transpose).transpose * Y₁ = M
      rw [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_transpose,
        Matrix.mul_assoc, hZY, Matrix.mul_one]
    have hker_dim : Module.finrank k₁ (LinearMap.ker L) = (m - n) * n := by
      have hrk := LinearMap.finrank_range_add_finrank_ker L
      rw [LinearMap.range_eq_top.mpr hcols_surj, finrank_top, Module.finrank_matrix,
        Module.finrank_matrix, Fintype.card_fin, Fintype.card_fin, Module.finrank_self,
        mul_one, mul_one] at hrk
      have hmn : n * n ≤ m * n := Nat.mul_le_mul_right n hnm
      zify [hnm, hmn] at hrk ⊢
      linarith
    have hker_card : Fintype.card (LinearMap.ker L) = q ^ ((m - n) * n) := by
      have h := Module.card_eq_pow_finrank (K := k₁) (V := LinearMap.ker L)
      rwa [hker_dim] at h
    obtain ⟨Y₂₀, hY₂₀⟩ := hcols_surj 1
    let e_fib : { Y₂ : Matrix (Fin m) (Fin n) k₁ // Y₂.transpose * Y₁ = 1 } ≃ LinearMap.ker L :=
      { toFun := fun ⟨Y₂, hY₂⟩ => ⟨Y₂ - Y₂₀, by
          rw [LinearMap.mem_ker, map_sub]
          change L Y₂ - L Y₂₀ = 0
          rw [show L Y₂ = 1 from hY₂, hY₂₀, sub_self]⟩
        invFun := fun ⟨W, hW⟩ => ⟨W + Y₂₀, by
          change L (W + Y₂₀) = 1
          rw [map_add, LinearMap.mem_ker.mp hW, zero_add, hY₂₀]⟩
        left_inv := fun ⟨Y₂, _⟩ => by ext i j; simp
        right_inv := fun ⟨W, _⟩ => by ext i j; simp }
    rw [Fintype.card_congr e_fib, hker_card]
  have hInj_card : (Fintype.card InjMat : ℝ) =
      ∏ i ∈ Finset.range n, ((q : ℝ) ^ m - (q : ℝ) ^ i) := by
    clear eRed eSigma hfib A hA T₁ hT Tinv hTTinv hTinvT Ainv hAAinv hAinvA
    induction n with
    | zero =>
      have h1 : Fintype.card { Y₁ : Matrix (Fin m) (Fin 0) k₁ //
          LinearIndependent k₁ (fun j => fun i => Y₁ i j) } = 1 :=
        Fintype.card_eq_one_iff.mpr ⟨⟨0, linearIndependent_empty_type⟩, fun ⟨Y, _⟩ => by
          ext i j; exact Fin.elim0 j⟩
      rw [h1]; simp
    | succ r ih =>
      have ihr := ih (by omega : r ≤ m)
      let Inj (k : ℕ) := { Y₁ : Matrix (Fin m) (Fin k) k₁ // LinearIndependent k₁ (fun j => fun i => Y₁ i j) }
      let projInj : Inj (r + 1) → Inj r := fun Y₁ =>
        ⟨Matrix.of fun i j => Y₁.1 i j.castSucc, Y₁.2.comp Fin.castSucc (Fin.castSucc_injective r)⟩
      have hfib_equiv : ∀ Y₀ : Inj r,
          { Y₁ : Inj (r + 1) // projInj Y₁ = Y₀ } ≃
            { v : Fin m → k₁ // v ∉ Submodule.span k₁ (Set.range (fun j : Fin r => fun i => Y₀.1 i j)) } :=
        fun ⟨Y₀, hY₀⟩ =>
        { toFun := fun x => ⟨fun i => x.1.1 i (Fin.last r), by
            intro hmem
            have hnot : Fin.last r ∉ Set.range (Fin.castSucc : Fin r → Fin (r + 1)) := by
              rintro ⟨j, hj⟩; exact Fin.castSucc_ne_last j hj
            have h := x.1.2.notMem_span_image hnot
            apply h
            have hrange : (fun j : Fin (r + 1) => fun i => x.1.1 i j) '' Set.range Fin.castSucc =
                Set.range (fun j : Fin r => fun i => Y₀ i j) := by
              ext v
              simp only [Set.mem_image, Set.mem_range, exists_exists_eq_and]
              constructor <;> rintro ⟨j, rfl⟩ <;> refine ⟨j, ?_⟩
              · ext i; simpa [projInj] using (congrFun (congrFun (congrArg Subtype.val x.2) i) j).symm
              · ext i; simpa [projInj] using congrFun (congrFun (congrArg Subtype.val x.2) i) j
            rw [hrange]
            exact hmem⟩
          invFun := fun x =>
            ⟨⟨Matrix.of fun i j => Fin.lastCases (x.1 i) (fun j' => Y₀ i j') j, by
              rw [Fintype.linearIndependent_iff]
              intro c hc
              have hc' : c (Fin.last r) • x.1 + ∑ j : Fin r, c j.castSucc • (fun i => Y₀ i j) = 0 := by
                have h := hc
                rw [Fin.sum_univ_castSucc] at h
                simpa [add_comm] using h
              have hclast : c (Fin.last r) = 0 := by
                by_contra hne
                apply x.2
                have hv_eq : x.1 = ∑ j : Fin r, (-(c (Fin.last r))⁻¹ * c j.castSucc) • (fun i => Y₀ i j) := by
                  have h1 : x.1 = (c (Fin.last r))⁻¹ • (c (Fin.last r) • x.1) := by
                    rw [smul_smul, inv_mul_cancel₀ hne, one_smul]
                  rw [show c (Fin.last r) • x.1 = -(∑ j : Fin r, c j.castSucc • (fun i => Y₀ i j)) from
                    eq_neg_of_add_eq_zero_left hc'] at h1
                  rw [h1, smul_neg, Finset.smul_sum, ← Finset.sum_neg_distrib]
                  refine Finset.sum_congr rfl fun j _ => ?_
                  rw [smul_smul, ← neg_smul, neg_mul]
                rw [hv_eq]
                exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
              rw [hclast, zero_smul, zero_add] at hc'
              have hY₀' := (Fintype.linearIndependent_iff.mp hY₀) (fun j => c j.castSucc) hc'
              intro j
              cases j using Fin.lastCases with
              | last => exact hclast
              | cast j' => exact hY₀' j'⟩,
            Subtype.ext (by ext i j; simp [projInj])⟩
          left_inv := fun x => Subtype.ext (Subtype.ext (by
            ext i j
            cases j using Fin.lastCases with
            | last => simp
            | cast j' => simpa [projInj] using (congrFun (congrFun (congrArg Subtype.val x.2) i) j').symm))
          right_inv := fun x => Subtype.ext (by ext i; simp) }
      have hspan_card : ∀ Y₀ : Inj r,
          (Fintype.card { v : Fin m → k₁ //
            v ∉ Submodule.span k₁ (Set.range (fun j : Fin r => fun i => Y₀.1 i j)) } : ℝ) =
            (q : ℝ) ^ m - (q : ℝ) ^ r := by
        intro ⟨Y₀, hY₀⟩
        let S := Submodule.span k₁ (Set.range (fun j : Fin r => fun i => Y₀ i j))
        have hS_dim : Module.finrank k₁ S = r := by
          have := finrank_span_eq_card hY₀
          simpa using this
        have hS_card : Fintype.card S = q ^ r := by
          have h := Module.card_eq_pow_finrank (K := k₁) (V := S)
          rwa [hS_dim] at h
        have hcomp : Fintype.card { v : Fin m → k₁ // v ∉ S } + Fintype.card S = q ^ m := by
          have h1 := Fintype.card_subtype_compl (fun v : Fin m → k₁ => v ∈ S)
          have hle : Fintype.card S ≤ Fintype.card (Fin m → k₁) := Fintype.card_subtype_le _
          have h2 : Fintype.card (Fin m → k₁) = q ^ m := by
            rw [Fintype.card_fun, Fintype.card_fin]
          rw [h2] at h1 hle
          change Fintype.card { v : Fin m → k₁ // ¬ v ∈ S } = q ^ m - Fintype.card S at h1
          omega
        have hcast : (Fintype.card { v : Fin m → k₁ // v ∉ S } : ℝ) + ((q ^ r : ℕ) : ℝ) =
            ((q ^ m : ℕ) : ℝ) := by
          rw [← hS_card]; exact_mod_cast hcomp
        push_cast at hcast
        linarith
      have hpart := Finset.card_eq_sum_card_fiberwise (f := projInj) (s := Finset.univ)
        (t := Finset.univ) (fun _ _ => Finset.mem_univ _)
      rw [Finset.card_univ] at hpart
      have hstep : (Fintype.card (Inj (r + 1)) : ℝ) =
          ∑ _Y₀ : Inj r, ((q : ℝ) ^ m - (q : ℝ) ^ r) := by
        rw [hpart]
        push_cast
        refine Finset.sum_congr rfl fun Y₀ _ => ?_
        rw [← Fintype.card_coe]
        have hcoe : Fintype.card ↥(Finset.univ.filter fun a => projInj a = Y₀) =
            Fintype.card { Y₁ : Inj (r + 1) // projInj Y₁ = Y₀ } :=
          Fintype.card_congr
            { toFun := fun ⟨Y, hY⟩ => ⟨Y, (Finset.mem_filter.mp hY).2⟩
              invFun := fun ⟨Y, hY⟩ => ⟨Y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hY⟩⟩
              left_inv := fun ⟨_, _⟩ => rfl
              right_inv := fun ⟨_, _⟩ => rfl }
        rw [hcoe, Fintype.card_congr (hfib_equiv Y₀), hspan_card Y₀]
      rw [show (Fintype.card { Y₁ : Matrix (Fin m) (Fin (r + 1)) k₁ //
          LinearIndependent k₁ (fun j => fun i => Y₁ i j) } : ℝ) =
          (Fintype.card (Inj (r + 1)) : ℝ) from rfl, hstep, Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul,
        show (Fintype.card (Inj r) : ℝ) =
          (Fintype.card { Y₁ : Matrix (Fin m) (Fin r) k₁ //
            LinearIndependent k₁ (fun j => fun i => Y₁ i j) } : ℝ) from rfl,
        ihr, Finset.prod_range_succ]
  rw [Fintype.card_congr eSigma, Fintype.card_sigma]
  push_cast
  rw [Finset.sum_congr rfl (fun Y₁ _ => by rw [hfib Y₁]), Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, hInj_card]
  have hreidx : (∏ i ∈ Finset.range n, ((q : ℝ) ^ m - (q : ℝ) ^ i)) =
      ∏ j ∈ Finset.Icc (m - n + 1) m, ((q : ℝ) ^ m - (q : ℝ) ^ (m - j)) := by
    refine Finset.prod_bij (fun i _ => m - i) ?_ ?_ ?_ ?_
    · intro i hi
      rw [Finset.mem_range] at hi
      rw [Finset.mem_Icc]; omega
    · intro i₁ hi₁ i₂ hi₂ heq
      rw [Finset.mem_range] at hi₁ hi₂
      omega
    · intro j hj
      rw [Finset.mem_Icc] at hj
      refine ⟨m - j, Finset.mem_range.mpr (by omega), by omega⟩
    · intro i hi
      rw [Finset.mem_range] at hi
      rw [show m - (m - i) = i by omega]
  rw [hreidx]
  have hpow_tot : 2 * m * n - n ^ 2 = (m - n) * n + m * n := by
    have hn2 : n ^ 2 ≤ 2 * m * n := by nlinarith
    zify [hnm, hn2]; ring
  rw [hpow_tot, pow_add]
  have hmn_card : (Finset.Icc (m - n + 1) m).card = n := by
    rw [Nat.card_Icc]; omega
  have hqm_prod : (q : ℝ) ^ (m * n) = ∏ _j ∈ Finset.Icc (m - n + 1) m, (q : ℝ) ^ m := by
    rw [Finset.prod_const, hmn_card, ← pow_mul]
  push_cast
  rw [mul_comm ((q : ℝ) ^ ((m - n) * n)) ((q : ℝ) ^ (m * n)),
    mul_div_mul_right _ _ (pow_ne_zero _ hq0),
    hqm_prod, ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun j hj => ?_
  have hjm : j ≤ m := (Finset.mem_Icc.mp hj).2
  rw [sub_div, div_self (pow_ne_zero m hq0)]
  congr 1
  rw [_root_.zpow_neg, zpow_natCast, div_eq_mul_inv]
  have hpow_eq : (q : ℝ) ^ (m - j) * (q : ℝ) ^ j = (q : ℝ) ^ m := by
    rw [← pow_add, Nat.sub_add_cancel hjm]
  have hj0 : (q : ℝ) ^ j ≠ 0 := pow_ne_zero j hq0
  have hm0 : (q : ℝ) ^ m ≠ 0 := pow_ne_zero m hq0
  rw [← hpow_eq]
  field_simp [hj0, hm0]

end SplitFiniteField

end FiniteFieldHermitian

/-! ## Section 2: Unramified DVR / Local Models & Concrete `LocalHermLattice v` -/

section LocalLattices

/-- Splitting type of an unramified finite place in a quadratic CM extension `E / F`. -/
inductive PlaceSplitting : Type
  | inert
  | split
  deriving DecidableEq, Repr

/-- Quadratic character value `χ_v ∈ {-1, 1}` attached to an unramified place splitting. -/
def PlaceSplitting.chi : PlaceSplitting → ℝ
  | .inert => -1
  | .split => 1

/-- Integer quadratic character value attached to an unramified place splitting. -/
def PlaceSplitting.chiZ : PlaceSplitting → ℤ
  | .inert => -1
  | .split => 1

lemma PlaceSplitting.chi_sq (sp : PlaceSplitting) : sp.chi ^ 2 = 1 := by
  cases sp <;> norm_num [PlaceSplitting.chi]

lemma PlaceSplitting.abs_chi (sp : PlaceSplitting) : |sp.chi| = 1 := by
  cases sp <;> norm_num [PlaceSplitting.chi]

/-- Induced involution on the quotient ring `S ⧸ Ideal.span {ϖ ^ k}` when `σ ϖ = ϖ`. -/
def modInv {S : Type*} [CommRing S] (σ : S →+* S) (ϖ : S) (hσ_pi : σ ϖ = ϖ) (k : ℕ) :
    (S ⧸ Ideal.span {ϖ ^ k}) →+* (S ⧸ Ideal.span {ϖ ^ k}) :=
  Ideal.quotientMap (Ideal.span {ϖ ^ k}) σ (fun x hx => by
    rw [Ideal.mem_span_singleton] at hx
    rw [Ideal.mem_comap, Ideal.mem_span_singleton]
    rcases hx with ⟨r, rfl⟩
    exact ⟨σ r, by rw [map_mul, map_pow, hσ_pi]⟩)

lemma modInv_mk {S : Type*} [CommRing S] (σ : S →+* S) (ϖ : S) (hσ_pi : σ ϖ = ϖ)
    (k : ℕ) (x : S) :
    modInv σ ϖ hσ_pi k (Ideal.Quotient.mk (Ideal.span {ϖ ^ k}) x) =
      Ideal.Quotient.mk (Ideal.span {ϖ ^ k}) (σ x) := rfl

lemma modInv_involutive {S : Type*} [CommRing S] (σ : S →+* S) (hσ_inv : ∀ x, σ (σ x) = x)
    (ϖ : S) (hσ_pi : σ ϖ = ϖ) (k : ℕ) (x : S ⧸ Ideal.span {ϖ ^ k}) :
    modInv σ ϖ hσ_pi k (modInv σ ϖ hσ_pi k x) = x := by
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp [modInv_mk, hσ_inv]

/-- Canonical projection `S ⧸ (ϖ ^ a) →+* S ⧸ (ϖ ^ b)` for `b ≤ a`. -/
def modProj {S : Type*} [CommRing S] (ϖ : S) {a b : ℕ} (hab : b ≤ a) :
    (S ⧸ Ideal.span {ϖ ^ a}) →+* (S ⧸ Ideal.span {ϖ ^ b}) :=
  Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow ϖ hab))

lemma modProj_mk {S : Type*} [CommRing S] (ϖ : S) {a b : ℕ} (hab : b ≤ a) (x : S) :
    modProj ϖ hab (Ideal.Quotient.mk (Ideal.span {ϖ ^ a}) x) =
      Ideal.Quotient.mk (Ideal.span {ϖ ^ b}) x :=
  Ideal.Quotient.factor_mk _ x

lemma modProj_surjective {S : Type*} [CommRing S] (ϖ : S) {a b : ℕ} (hab : b ≤ a) :
    Function.Surjective (modProj ϖ hab) := by
  intro y
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
  exact ⟨Ideal.Quotient.mk _ x, modProj_mk ϖ hab x⟩

lemma modProj_modInv {S : Type*} [CommRing S] (σ : S →+* S) (ϖ : S) (hσ_pi : σ ϖ = ϖ)
    {a b : ℕ} (hab : b ≤ a) (x : S ⧸ Ideal.span {ϖ ^ a}) :
    modProj ϖ hab (modInv σ ϖ hσ_pi a x) = modInv σ ϖ hσ_pi b (modProj ϖ hab x) := by
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

universe u

/-- Witness identifying the mod-`ϖ` residue algebra `(R₁, σ₁)` as either an unramified inert
quadratic field extension `k₂ / k₁` or a split étale quadratic algebra `k₁ × k₁`. -/
inductive UnramifiedResWitness (k₁ R₁ : Type u) [Field k₁] [Fintype k₁] [DecidableEq k₁]
    [CommRing R₁] (σ₁ : R₁ →+* R₁) : Type (u + 1) where
  | inert (k₂ : Type u) [Field k₂] [Fintype k₂] [DecidableEq k₂] [Algebra k₁ k₂]
      (hdim : Module.finrank k₁ k₂ = 2) (σ₂ : k₂ ≃ₐ[k₁] k₂) (hσ₂ : σ₂ ≠ AlgEquiv.refl)
      (iso : R₁ ≃+* k₂) (hσ_iso : ∀ x, iso (σ₁ x) = σ₂ (iso x)) :
      UnramifiedResWitness k₁ R₁ σ₁
  | split (iso : R₁ ≃+* k₁ × k₁)
      (hσ_iso : ∀ x, iso (σ₁ x) = ((iso x).2, (iso x).1)) :
      UnramifiedResWitness k₁ R₁ σ₁

/-- Concrete local unramified DVR / quadratic-extension datum `(S, σ, ϖ)` with finite residue
field `k₁` of cardinality `q ≥ 2` and residue algebra `S ⧸ (ϖ)` either inert or split. -/
structure LocalHermBase where
  S : Type u
  [commRingS : CommRing S]
  σ : S →+* S
  hσ_inv : ∀ x : S, σ (σ x) = x
  ϖ : S
  hσ_pi : σ ϖ = ϖ
  hreg : ∀ x : S, ϖ * x = 0 → x = 0
  k₁ : Type u
  [fieldK₁ : Field k₁]
  [fintypeK₁ : Fintype k₁]
  [decEqK₁ : DecidableEq k₁]
  witness : UnramifiedResWitness k₁ (S ⧸ Ideal.span {ϖ ^ 1}) (modInv σ ϖ hσ_pi 1)

attribute [instance] LocalHermBase.commRingS LocalHermBase.fieldK₁ LocalHermBase.fintypeK₁
  LocalHermBase.decEqK₁

namespace LocalHermBase

/-- Residue field cardinality `q = |k₁|`. -/
def q (B : LocalHermBase) : ℕ := Fintype.card B.k₁

lemma two_le_q (B : LocalHermBase) : 2 ≤ B.q := by
  have hpos := Fintype.one_lt_card_iff.mpr ⟨(0 : B.k₁), 1, zero_ne_one⟩
  exact hpos

lemma q_pos (B : LocalHermBase) : 0 < B.q := by
  have := B.two_le_q; omega

lemma q_real_ne_zero (B : LocalHermBase) : (B.q : ℝ) ≠ 0 :=
  Nat.cast_ne_zero.mpr B.q_pos.ne'

/-- Splitting type (`.inert` or `.split`) of `B`. -/
def splitting (B : LocalHermBase) : PlaceSplitting :=
  UnramifiedResWitness.casesOn (motive := fun _ => PlaceSplitting) B.witness
    (fun _ _ _ _ _ _ _ _ _ _ => PlaceSplitting.inert)
    (fun _ _ => PlaceSplitting.split)

/-- Precision-`k` quotient ring `S ⧸ (ϖ ^ k)`. -/
abbrev ModRing (B : LocalHermBase) (k : ℕ) : Type _ :=
  B.S ⧸ Ideal.span {B.ϖ ^ k}

/-- Precision-`k` induced involution on `B.ModRing k`. -/
def modInvAt (B : LocalHermBase) (k : ℕ) : B.ModRing k →+* B.ModRing k :=
  modInv B.σ B.ϖ B.hσ_pi k

/-- Reduction of an `S`-matrix modulo `ϖ ^ k`. -/
def modMat (B : LocalHermBase) (k : ℕ) {m n : ℕ} (M : Matrix (Fin m) (Fin n) B.S) :
    Matrix (Fin m) (Fin n) (B.ModRing k) :=
  M.map (Ideal.Quotient.mk (Ideal.span {B.ϖ ^ k}))

lemma modMat_isHerm (B : LocalHermBase) (k : ℕ) {n : ℕ} {H : Matrix (Fin n) (Fin n) B.S}
    (hH : IsHermMatrix B.σ H) :
    IsHermMatrix (B.modInvAt k) (B.modMat k H) := by
  intro i j
  simp only [modMat, Matrix.map_apply, modInvAt, modInv_mk, hH i j]

lemma modProj_modMat (B : LocalHermBase) {a b : ℕ} (hab : b ≤ a) {m n : ℕ}
    (M : Matrix (Fin m) (Fin n) B.S) :
    (B.modMat a M).map (modProj B.ϖ hab) = B.modMat b M := by
  ext i j
  simp [modMat, modProj_mk]

lemma hermConj_mapMatrix {R₁ R₂ : Type*} [CommRing R₁] [CommRing R₂]
    (σ₁ : R₁ →+* R₁) (σ₂ : R₂ →+* R₂) (f : R₁ →+* R₂)
    (hcomm : ∀ x, f (σ₁ x) = σ₂ (f x)) {m n : ℕ} (M : Matrix (Fin m) (Fin n) R₁) :
    (hermConj σ₁ M).map f = hermConj σ₂ (M.map f) := by
  ext i j
  simp [hermConj, hcomm]

private lemma map_mul_mat {R₁ R₂ : Type*} [CommRing R₁] [CommRing R₂] (f : R₁ →+* R₂)
    {a b c : ℕ} (A : Matrix (Fin a) (Fin b) R₁) (B : Matrix (Fin b) (Fin c) R₁) :
    (A * B).map f = A.map f * B.map f := by
  ext i j
  simp [Matrix.mul_apply, map_sum, map_mul]

private lemma map_sub_mat {R₁ R₂ : Type*} [CommRing R₁] [CommRing R₂] (f : R₁ →+* R₂)
    {a b : ℕ} (A B : Matrix (Fin a) (Fin b) R₁) :
    (A - B).map f = A.map f - B.map f := by
  ext i j; simp

private lemma map_add_mat {R₁ R₂ : Type*} [CommRing R₁] [CommRing R₂] (f : R₁ →+* R₂)
    {a b : ℕ} (A B : Matrix (Fin a) (Fin b) R₁) :
    (A + B).map f = A.map f + B.map f := by
  ext i j; simp

lemma hreg_pow (B : LocalHermBase) : ∀ (k : ℕ) (x : B.S), B.ϖ ^ k * x = 0 → x = 0
  | 0, x, hx => by simpa using hx
  | k + 1, x, hx => by
      have hx' : B.ϖ * (B.ϖ ^ k * x) = 0 := by
        calc B.ϖ * (B.ϖ ^ k * x) = (B.ϖ * B.ϖ ^ k) * x := (mul_assoc _ _ _).symm
          _ = B.ϖ ^ (k + 1) * x := by rw [← pow_succ']
          _ = 0 := hx
      exact hreg_pow B k x (B.hreg _ hx')

lemma modRing_one_finite (B : LocalHermBase) : Finite (B.ModRing 1) := by
  cases hw : B.witness with
  | inert k₂ hdim σ₂ hσ₂ iso hσ_iso =>
      exact Finite.of_equiv k₂ iso.toEquiv.symm
  | split iso hσ_iso =>
      exact Finite.of_equiv (B.k₁ × B.k₁) iso.toEquiv.symm

lemma card_modRing_one (B : LocalHermBase) : Nat.card (B.ModRing 1) = B.q ^ 2 := by
  cases hw : B.witness with
  | inert k₂ hdim σ₂ hσ₂ iso hσ_iso =>
      rw [Nat.card_congr iso.toEquiv, Nat.card_eq_fintype_card,
        card_quad_ext_eq_sq (k₁ := B.k₁) (k₂ := k₂) hdim]
      rfl
  | split iso hσ_iso =>
      rw [Nat.card_congr iso.toEquiv, Nat.card_eq_fintype_card, Fintype.card_prod, ← sq]
      rfl

/-- Fixed-point subring `{ x : B.ModRing 1 // B.modInvAt 1 x = x }` has cardinality `B.q`. -/
lemma card_modRing_one_fixed (B : LocalHermBase) :
    Nat.card { x : B.ModRing 1 // B.modInvAt 1 x = x } = B.q := by
  classical
  cases hw : B.witness with
  | inert k₂ hdim σ₂ hσ₂ iso hσ_iso =>
      have heq1 : { x : B.ModRing 1 // B.modInvAt 1 x = x } ≃ { y : k₂ // σ₂ y = y } :=
        { toFun := fun x => ⟨iso x.1, by
            dsimp only [modInvAt] at *
            rw [← hσ_iso x.1]; exact congrArg iso x.2⟩
          invFun := fun y => ⟨iso.symm y.1, by
            apply iso.injective
            dsimp only [modInvAt]
            rw [hσ_iso, iso.apply_symm_apply]
            exact y.2⟩
          left_inv := fun x => Subtype.ext (iso.symm_apply_apply x.1)
          right_inv := fun y => Subtype.ext (iso.apply_symm_apply y.1) }
      have heq2 : { y : k₂ // σ₂ y = y } ≃ B.k₁ :=
        { toFun := fun ⟨y, hy⟩ =>
            Classical.choose (fixed_by_pow_card_mem_base (k₁ := B.k₁) (k₂ := k₂) hdim (by
              rw [← sigma_eq_pow_card (k₁ := B.k₁) (k₂ := k₂) hdim σ₂ hσ₂]
              exact hy))
          invFun := fun a => ⟨algebraMap B.k₁ k₂ a, σ₂.commutes a⟩
          left_inv := fun ⟨y, hy⟩ => Subtype.ext <|
            (Classical.choose_spec (fixed_by_pow_card_mem_base (k₁ := B.k₁) (k₂ := k₂) hdim (by
              rw [← sigma_eq_pow_card (k₁ := B.k₁) (k₂ := k₂) hdim σ₂ hσ₂]
              exact hy))).symm
          right_inv := fun a => by
            apply (algebraMap B.k₁ k₂).injective
            exact (Classical.choose_spec (fixed_by_pow_card_mem_base (k₁ := B.k₁) (k₂ := k₂) hdim
              (by rw [← sigma_eq_pow_card (k₁ := B.k₁) (k₂ := k₂) hdim σ₂ hσ₂]
                  exact σ₂.commutes a))).symm }
      rw [Nat.card_congr heq1, Nat.card_congr heq2, Nat.card_eq_fintype_card]
      rfl
  | split iso hσ_iso =>
      have heq1 : { x : B.ModRing 1 // B.modInvAt 1 x = x } ≃ B.k₁ :=
        { toFun := fun x => (iso x.1).1
          invFun := fun a => ⟨iso.symm (a, a), by
            apply iso.injective
            dsimp only [modInvAt]
            rw [hσ_iso, iso.apply_symm_apply]⟩
          left_inv := fun x => Subtype.ext <| by
            apply iso.injective
            rw [iso.apply_symm_apply]
            have h12 : (iso (B.modInvAt 1 x.1)).1 = (iso x.1).1 := congrArg Prod.fst (congrArg iso x.2)
            dsimp only [modInvAt] at h12
            rw [hσ_iso] at h12
            exact Prod.ext rfl h12.symm
          right_inv := fun a => by simp }
      rw [Nat.card_congr heq1, Nat.card_eq_fintype_card]
      rfl

/-- In ALL characteristics (including char 2), there exists `e : B.ModRing 1` with `e + σ₁ e = 1`. -/
lemma exists_trace_one_modOne (B : LocalHermBase) :
    ∃ e : B.ModRing 1, e + B.modInvAt 1 e = 1 := by
  cases hw : B.witness with
  | inert k₂ hdim σ₂ hσ₂ iso hσ_iso =>
      obtain ⟨e₀, he₀⟩ := exists_trace_ne_zero (k₁ := B.k₁) (k₂ := k₂) σ₂ hσ₂
      let t : k₂ := e₀ + σ₂ e₀
      have ht_fixed : σ₂ t = t := by
        simp only [t, map_add, sigma_involutive (k₁ := B.k₁) (k₂ := k₂) hdim σ₂ hσ₂, add_comm]
      have ht_inv : σ₂ t⁻¹ = t⁻¹ := by
        rw [map_inv₀, ht_fixed]
      refine ⟨iso.symm (e₀ * t⁻¹), ?_⟩
      apply iso.injective
      dsimp only [modInvAt]
      rw [map_add, map_one, hσ_iso, iso.apply_symm_apply, map_mul, ht_inv, ← add_mul]
      exact mul_inv_cancel₀ he₀
  | split iso hσ_iso =>
      refine ⟨iso.symm (1, 0), ?_⟩
      apply iso.injective
      dsimp only [modInvAt]
      rw [map_add, map_one, hσ_iso, iso.apply_symm_apply]
      ext <;> simp

/-- Exact cardinality of `n × n` Hermitian matrices over `B.ModRing 1` is `q ^ (n^2)`. -/
lemma card_herm_modRing_one (B : LocalHermBase) (n : ℕ) :
    Nat.card { A : Matrix (Fin n) (Fin n) (B.ModRing 1) // IsHermMatrix (B.modInvAt 1) A } =
      B.q ^ (n ^ 2) := by
  classical
  have : Finite (B.ModRing 1) := B.modRing_one_finite
  let σ₁ := B.modInvAt 1
  let Fix := { x : B.ModRing 1 // σ₁ x = x }
  let Upper := { p : Fin n × Fin n // p.1 < p.2 }
  let e_herm : { A : Matrix (Fin n) (Fin n) (B.ModRing 1) // IsHermMatrix σ₁ A } ≃
      (Fin n → Fix) × (Upper → B.ModRing 1) :=
    { toFun := fun ⟨A, hA⟩ =>
        (fun i => ⟨A i i, hA i i⟩, fun ⟨p, _⟩ => A p.1 p.2)
      invFun := fun ⟨dg, up⟩ =>
        ⟨Matrix.of fun i j =>
          if hij : i < j then up ⟨(i, j), hij⟩
          else if hji : j < i then σ₁ (up ⟨(j, i), hji⟩)
          else (dg i).1,
         fun i j => by
          change σ₁ (if hji : j < i then up ⟨(j, i), hji⟩
            else if hij : i < j then σ₁ (up ⟨(i, j), hij⟩)
            else (dg j).1) =
            if hij : i < j then up ⟨(i, j), hij⟩
            else if hji : j < i then σ₁ (up ⟨(j, i), hji⟩)
            else (dg i).1
          rcases lt_trichotomy i j with hij | rfl | hji
          · have hnot : ¬ (j < i) := not_lt_of_gt hij
            dsimp only [σ₁, LocalHermBase.modInvAt]
            rw [dif_neg hnot, dif_pos hij, modInv_involutive _ B.hσ_inv, dif_pos hij]
          · simp [(dg i).2]
          · have hnot : ¬ (i < j) := not_lt_of_gt hji
            simp [hji, hnot]⟩
      left_inv := fun ⟨A, hA⟩ => Subtype.ext (by
        ext i j
        change (if hij : i < j then A i j else if hji : j < i then σ₁ (A j i) else A i i) = A i j
        rcases lt_trichotomy i j with hij | rfl | hji
        · simp [hij]
        · simp
        · have hnot : ¬ (i < j) := not_lt_of_gt hji
          simp [hnot, hji, hA i j])
      right_inv := fun ⟨dg, up⟩ => by
        ext1
        · ext i
          change (if hij : i < i then up ⟨(i, i), hij⟩
            else if hji : i < i then σ₁ (up ⟨(i, i), hji⟩)
            else (dg i).1) = (dg i).1
          simp
        · ext ⟨⟨i, j⟩, hij⟩
          change (if h : i < j then up ⟨(i, j), h⟩ else _) = up ⟨(i, j), hij⟩
          simp [hij] }
  have hupper_card : ∀ k : ℕ, Nat.card { p : Fin k × Fin k // p.1 < p.2 } = k * (k - 1) / 2 := by
    intro k
    induction k with
    | zero =>
      have : IsEmpty { p : Fin 0 × Fin 0 // p.1 < p.2 } := ⟨fun ⟨p, _⟩ => Fin.elim0 p.1⟩
      rw [Nat.card_of_isEmpty]
    | succ r ih =>
      let U (m : ℕ) := { p : Fin m × Fin m // p.1 < p.2 }
      let eSplit : U (r + 1) ≃ U r ⊕ Fin r :=
        { toFun := fun ⟨⟨i, j⟩, hij⟩ =>
            Fin.lastCases
              (fun hij' => Sum.inr ⟨i.val, by
                have hi : (i : ℕ) < r := by
                  simpa [Fin.lt_def] using hij'
                exact hi⟩)
              (fun j' hij' => Sum.inl ⟨⟨⟨i.val, by
                have hij_nat : (i : ℕ) < (j' : ℕ) := by simpa [Fin.lt_def] using hij'
                omega⟩, j'⟩, by
                simpa [Fin.lt_def] using hij'⟩)
              j hij
          invFun := fun
            | Sum.inl ⟨⟨i, j⟩, hij⟩ => ⟨⟨i.castSucc, j.castSucc⟩, Fin.castSucc_lt_castSucc_iff.mpr hij⟩
            | Sum.inr i => ⟨⟨i.castSucc, Fin.last r⟩, Fin.castSucc_lt_last i⟩
          left_inv := fun ⟨⟨i, j⟩, hij⟩ => by
            cases j using Fin.lastCases with
            | last =>
              apply Subtype.ext; ext <;> simp
            | cast j' =>
              apply Subtype.ext; ext <;> simp
          right_inv := fun
            | Sum.inl ⟨⟨i, j⟩, hij⟩ => by
              simp only [Fin.lastCases_castSucc]; apply congrArg Sum.inl
              apply Subtype.ext; ext <;> rfl
            | Sum.inr i => by
              simp [Fin.lastCases_last] }
      have hcard_sum : Nat.card (U (r + 1)) = Nat.card (U r) + r := by
        rw [Nat.card_congr eSplit, Nat.card_sum, Nat.card_eq_fintype_card (α := Fin r),
          Fintype.card_fin]
      rw [show Nat.card { p : Fin (r + 1) × Fin (r + 1) // p.1 < p.2 } = Nat.card (U (r + 1)) from rfl,
        hcard_sum, ih]
      have hev : 2 ∣ r * (r - 1) := by
        rcases Nat.even_or_odd r with ⟨t, rfl⟩ | ⟨t, rfl⟩
        · exact ⟨t * (t + t - 1), by ring⟩
        · exact ⟨(2 * t + 1) * t, by simp; ring⟩
      rcases hev with ⟨t, ht⟩
      rw [ht, Nat.mul_div_cancel_left _ (by omega)]
      cases r with
      | zero => simp at ht; subst ht; simp
      | succ s =>
        simp only [Nat.add_sub_cancel] at ht ⊢
        have hs : (s + 1 + 1) * (s + 1) = (s + 1) * s + 2 * (s + 1) := by ring
        rw [hs, ht, show 2 * t + 2 * (s + 1) = 2 * (t + (s + 1)) by ring,
          Nat.mul_div_cancel_left _ (by omega)]
  have hFix_card : Nat.card Fix = B.q := B.card_modRing_one_fixed
  have hMod_card : Nat.card (B.ModRing 1) = B.q ^ 2 := B.card_modRing_one
  have hev_n : 2 ∣ n * (n - 1) := by
    rcases Nat.even_or_odd n with ⟨t, rfl⟩ | ⟨t, rfl⟩
    · exact ⟨t * (t + t - 1), by ring⟩
    · exact ⟨(2 * t + 1) * t, by simp; ring⟩
  rcases hev_n with ⟨t, ht⟩
  have hn_sq : n + 2 * t = n ^ 2 := by
    cases n with
    | zero => simp at ht; subst ht; simp
    | succ s =>
      have : (s + 1) + (s + 1) * s = (s + 1) ^ 2 := by ring
      simpa [← ht] using this
  rw [Nat.card_congr e_herm, Nat.card_prod, Nat.card_fun, Nat.card_fun, hFix_card, hMod_card,
    Nat.card_eq_fintype_card (α := Fin n), Fintype.card_fin, hupper_card n, ht,
    Nat.mul_div_cancel_left _ (by omega), ← pow_mul, ← pow_add, hn_sq]

/-- Concrete local `LocalHermBase` over `Polynomial k₂` for an inert quadratic finite field extension `k₂ / k₁`. -/
def ofInertField (k₁ k₂ : Type u) [Field k₁] [Fintype k₁] [DecidableEq k₁]
    [Field k₂] [Fintype k₂] [DecidableEq k₂] [Algebra k₁ k₂]
    (hdim : Module.finrank k₁ k₂ = 2) (σ₂ : k₂ ≃ₐ[k₁] k₂) (hσ₂ : σ₂ ≠ AlgEquiv.refl) :
    LocalHermBase where
  S := Polynomial k₂
  σ := Polynomial.mapRingHom σ₂.toRingHom
  hσ_inv := fun f => by
    ext i
    simp [sigma_involutive hdim σ₂ hσ₂]
  ϖ := Polynomial.X
  hσ_pi := Polynomial.map_X _
  hreg := fun f hf => (mul_eq_zero.mp hf).resolve_left Polynomial.X_ne_zero
  k₁ := k₁
  witness := by
    let ev : Polynomial k₂ →+* k₂ := Polynomial.evalRingHom 0
    have hev_eval : ∀ q : Polynomial k₂, ev q = q.coeff 0 := fun q => by
      change q.eval 0 = q.coeff 0
      induction q using Polynomial.induction_on' with
      | add a b ha hb => simp [Polynomial.eval_add, Polynomial.coeff_add, ha, hb]
      | monomial n a => cases n <;> simp [Polynomial.eval_monomial, Polynomial.coeff_monomial]
    have hev_surj : Function.Surjective ev := fun a =>
      ⟨Polynomial.C a, by simp [ev]⟩
    have hev_ker : RingHom.ker ev = Ideal.span {(Polynomial.X : Polynomial k₂) ^ 1} := by
      ext p
      rw [pow_one, RingHom.mem_ker, hev_eval, Ideal.mem_span_singleton, Polynomial.X_dvd_iff]
    let iso : (Polynomial k₂ ⧸ Ideal.span {(Polynomial.X : Polynomial k₂) ^ 1}) ≃+* k₂ :=
      (Ideal.quotEquivOfEq hev_ker.symm).trans (RingHom.quotientKerEquivOfSurjective hev_surj)
    refine UnramifiedResWitness.inert k₂ hdim σ₂ hσ₂ iso (fun x => ?_)
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    change ev (Polynomial.map σ₂.toRingHom p) = σ₂ (ev p)
    rw [hev_eval, hev_eval, Polynomial.coeff_map]
    rfl

/-- Concrete local `LocalHermBase` over `Polynomial k₁ × Polynomial k₁` for a split place over `k₁`. -/
def ofSplitField (k₁ : Type u) [Field k₁] [Fintype k₁] [DecidableEq k₁] : LocalHermBase.{u} where
  S := Polynomial k₁ × Polynomial k₁
  σ :=
    { toFun := fun fg => (fg.2, fg.1)
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  hσ_inv := fun ⟨_, _⟩ => rfl
  ϖ := (Polynomial.X, Polynomial.X)
  hσ_pi := rfl
  hreg := fun ⟨f, g⟩ hfg => by
    have h1 := congrArg Prod.fst hfg
    have h2 := congrArg Prod.snd hfg
    have hf : f = 0 := (mul_eq_zero.mp h1).resolve_left Polynomial.X_ne_zero
    have hg : g = 0 := (mul_eq_zero.mp h2).resolve_left Polynomial.X_ne_zero
    exact Prod.ext hf hg
  k₁ := k₁
  witness := by
    let ev1 : Polynomial k₁ × Polynomial k₁ →+* k₁ :=
      (Polynomial.evalRingHom 0).comp (RingHom.fst _ _)
    let ev2 : Polynomial k₁ × Polynomial k₁ →+* k₁ :=
      (Polynomial.evalRingHom 0).comp (RingHom.snd _ _)
    let ev : Polynomial k₁ × Polynomial k₁ →+* k₁ × k₁ := RingHom.prod ev1 ev2
    have hev_surj : Function.Surjective ev := fun ⟨a, b⟩ =>
      ⟨(Polynomial.C a, Polynomial.C b), by simp [ev, ev1, ev2]⟩
    have hev1 : ∀ q : Polynomial k₁, Polynomial.eval 0 q = q.coeff 0 := fun q => by
      induction q using Polynomial.induction_on' with
      | add p q hp hq => simp [hp, hq]
      | monomial n a => cases n <;> simp
    have hev_ker : RingHom.ker ev =
        Ideal.span {((Polynomial.X, Polynomial.X) : Polynomial k₁ × Polynomial k₁) ^ 1} := by
      ext ⟨f, g⟩
      rw [pow_one, RingHom.mem_ker, Ideal.mem_span_singleton]
      simp only [ev, ev1, ev2, RingHom.prod_apply, RingHom.comp_apply, RingHom.coe_fst,
        RingHom.coe_snd, Polynomial.coe_evalRingHom, hev1]
      rw [Prod.ext_iff, Prod.fst_zero, Prod.snd_zero,
        ← Polynomial.X_dvd_iff, ← Polynomial.X_dvd_iff]
      constructor
      · rintro ⟨⟨qf, hqf⟩, ⟨qg, hqg⟩⟩
        exact ⟨(qf, qg), Prod.ext hqf hqg⟩
      · rintro ⟨⟨qf, qg⟩, hq⟩
        exact ⟨⟨qf, congrArg Prod.fst hq⟩, ⟨qg, congrArg Prod.snd hq⟩⟩
    let iso : ((Polynomial k₁ × Polynomial k₁) ⧸
        Ideal.span {((Polynomial.X, Polynomial.X) : Polynomial k₁ × Polynomial k₁) ^ 1}) ≃+*
        k₁ × k₁ :=
      (Ideal.quotEquivOfEq hev_ker.symm).trans (RingHom.quotientKerEquivOfSurjective hev_surj)
    refine UnramifiedResWitness.split iso (fun x => ?_)
    obtain ⟨⟨f, g⟩, rfl⟩ := Ideal.Quotient.mk_surjective x
    rfl

private def galoisField_two_frob_equiv (p : ℕ) [Fact p.Prime] :
    GaloisField p 2 ≃ₐ[ZMod p] GaloisField p 2 :=
  letI : Fintype (GaloisField p 2) := Fintype.ofFinite _
  AlgEquiv.ofBijective (quadFrobHom (ZMod p) (GaloisField p 2))
    (Finite.injective_iff_bijective.mp
      (quadFrobHom (ZMod p) (GaloisField p 2)).toRingHom.injective)

lemma galoisField_two_frob_ne_refl (p : ℕ) [Fact p.Prime] :
    galoisField_two_frob_equiv p ≠ AlgEquiv.refl := by
  let : Fintype (GaloisField p 2) := Fintype.ofFinite _
  let : DecidableEq (GaloisField p 2) := Classical.decEq _
  intro h
  have hcard1 : Fintype.card (ZMod p) = p := ZMod.card p
  have hdim : Module.finrank (ZMod p) (GaloisField p 2) = 2 := by
    have hcard2 : Fintype.card (GaloisField p 2) = p ^ 2 := by
      rw [← Nat.card_eq_fintype_card, GaloisField.card p 2 (by decide)]
    have hmod := Module.card_eq_pow_finrank (K := ZMod p) (V := GaloisField p 2)
    rw [hcard1, hcard2] at hmod
    have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
    exact Nat.pow_right_injective hp1 hmod.symm
  have hall : ∀ y : GaloisField p 2, y ^ p = y := fun y => by
    have hy := AlgEquiv.ext_iff.mp h y
    simp only [galoisField_two_frob_equiv, AlgEquiv.coe_ofBijective, quadFrobHom, AlgHom.coe_mk,
      RingHom.coe_mk, hcard1, AlgEquiv.coe_refl, id_eq] at hy
    exact hy
  have hpoly : (Finset.univ : Finset (GaloisField p 2)).card ≤ p := by
    have hsub : (Finset.univ : Finset (GaloisField p 2)) ⊆
        (Polynomial.X ^ p - Polynomial.X : Polynomial (GaloisField p 2)).roots.toFinset := by
      intro y _
      rw [Multiset.mem_toFinset, Polynomial.mem_roots]
      · simp [hall y]
      · intro h0
        have hc : (Polynomial.X ^ p - Polynomial.X : Polynomial (GaloisField p 2)).coeff p = 0 := by
          rw [h0, Polynomial.coeff_zero]
        have hp1 : p ≠ 1 := (Fact.out : p.Prime).ne_one
        simp [Polynomial.coeff_X_pow, Polynomial.coeff_X, hp1.symm] at hc
    calc (Finset.univ : Finset (GaloisField p 2)).card
        ≤ (Polynomial.X ^ p - Polynomial.X : Polynomial (GaloisField p 2)).roots.toFinset.card :=
          Finset.card_le_card hsub
      _ ≤ (Polynomial.X ^ p - Polynomial.X : Polynomial (GaloisField p 2)).roots.card :=
          Multiset.toFinset_card_le _
      _ ≤ (Polynomial.X ^ p - Polynomial.X : Polynomial (GaloisField p 2)).natDegree :=
          Polynomial.card_roots' _
      _ ≤ p := by
          refine (Polynomial.natDegree_sub_le _ _).trans ?_
          simp [Polynomial.natDegree_X]
          exact (Fact.out : p.Prime).pos
  have hcard2 : Fintype.card (GaloisField p 2) = p ^ 2 := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card p 2 (by decide)]
  rw [Finset.card_univ, hcard2] at hpoly
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  nlinarith

/-- Concrete `LocalHermBase` at a rational prime `p` with splitting `sp`. -/
def ofPrime (p : ℕ) (hp : p.Prime) (sp : PlaceSplitting) : LocalHermBase.{0} :=
  letI : Fact p.Prime := ⟨hp⟩
  letI : Fintype (GaloisField p 2) := Fintype.ofFinite _
  letI : DecidableEq (GaloisField p 2) := Classical.decEq _
  match sp with
  | .inert =>
      ofInertField (ZMod p) (GaloisField p 2) (by
        have h1 : Fintype.card (ZMod p) = p := ZMod.card p
        have h2 : Fintype.card (GaloisField p 2) = p ^ 2 := by
          rw [← Nat.card_eq_fintype_card, GaloisField.card p 2 (by decide)]
        have hmod := Module.card_eq_pow_finrank (K := ZMod p) (V := GaloisField p 2)
        rw [h1, h2] at hmod
        exact Nat.pow_right_injective hp.one_lt hmod.symm)
        (galoisField_two_frob_equiv p) (galoisField_two_frob_ne_refl p)
  | .split => ofSplitField (ZMod p)

lemma splitting_ofPrime (p : ℕ) (hp : p.Prime) (sp : PlaceSplitting) :
    (ofPrime p hp sp).splitting = sp := by
  cases sp <;> simp [ofPrime, splitting, ofInertField, ofSplitField]

lemma q_ofPrime (p : ℕ) (hp : p.Prime) (sp : PlaceSplitting) :
    (ofPrime p hp sp).q = p := by
  have : NeZero p := ⟨hp.ne_zero⟩
  unfold q
  rw [← Nat.card_eq_fintype_card]
  cases sp <;> simp only [ofPrime, ofInertField, ofSplitField] <;>
    rw [Nat.card_eq_fintype_card, ZMod.card]

end LocalHermBase

/-- Concrete local Hermitian lattice `L_v` at a finite place `v`, with local unramified base
`base`, rank `m ≥ 1`, Hermitian Gram matrix `gram`, and mod-`ϖ` unimodularity. -/
structure LocalHermLattice {ι : Type*} (v : ι) where
  place : ι
  base : LocalHermBase.{0}
  rank : ℕ
  rank_pos : 1 ≤ rank
  gram : Matrix (Fin rank) (Fin rank) base.S
  herm : IsHermMatrix base.σ gram
  unimodular : IsUnit (base.modMat 1 gram).det

namespace LocalHermLattice

/-- Standard unimodular identity lattice of rank `m ≥ 1` over a local base `B` at place `v`. -/
def std {ι : Type*} (v : ι) (B : LocalHermBase) (m : ℕ) (hm : 1 ≤ m) :
    LocalHermLattice v where
  place := v
  base := B
  rank := m
  rank_pos := hm
  gram := 1
  herm := isHermMatrix_one B.σ m
  unimodular := by
    have h1 : B.modMat 1 (1 : Matrix (Fin m) (Fin m) B.S) = 1 := by
      ext i j
      by_cases hij : i = j <;> simp [LocalHermBase.modMat, Matrix.one_apply, hij]
    rw [h1, Matrix.det_one]
    exact isUnit_one

/-- Concrete local Hermitian lattice of rank `m ≥ 1` at a prime `p` with splitting `sp`. -/
def ofPrime (p : ℕ) (hp : p.Prime) (sp : PlaceSplitting) (m : ℕ) (hm : 1 ≤ m) :
    LocalHermLattice p :=
  std p (LocalHermBase.ofPrime p hp sp) m hm

end LocalHermLattice

end LocalLattices

/-! ## Section 3: Hensel Lifting & Exact `LocalRepresentationDensity` -/

section HenselRepresentationDensity

namespace LocalHermBase

/-- The additive step embedding `S ⧸ (ϖ) →+ S ⧸ (ϖ ^ (k + 1))` sending `x ↦ ϖ^k * x`. -/
def liftStep (B : LocalHermBase) (k : ℕ) : B.ModRing 1 →+ B.ModRing (k + 1) :=
  QuotientAddGroup.lift (Ideal.span {B.ϖ ^ 1}).toAddSubgroup
    { toFun := fun x => Ideal.Quotient.mk (Ideal.span {B.ϖ ^ (k + 1)}) (B.ϖ ^ k * x)
      map_zero' := by simp
      map_add' := fun a b => by simp [mul_add, map_add] }
    (fun x hx => by
      change x ∈ Ideal.span {B.ϖ ^ 1} at hx
      rw [pow_one, Ideal.mem_span_singleton] at hx
      rcases hx with ⟨y, rfl⟩
      change Ideal.Quotient.mk (Ideal.span {B.ϖ ^ (k + 1)}) (B.ϖ ^ k * (B.ϖ * y)) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
      exact ⟨y, by rw [← mul_assoc, ← pow_succ]⟩)

lemma liftStep_mk (B : LocalHermBase) (k : ℕ) (x : B.S) :
    B.liftStep k (Ideal.Quotient.mk (Ideal.span {B.ϖ ^ 1}) x) =
      Ideal.Quotient.mk (Ideal.span {B.ϖ ^ (k + 1)}) (B.ϖ ^ k * x) := rfl

lemma liftStep_injective (B : LocalHermBase) (k : ℕ) : Function.Injective (B.liftStep k) := by
  rw [injective_iff_map_eq_zero]
  intro u hu
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective u
  rw [liftStep_mk, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at hu
  rcases hu with ⟨y, hy⟩
  have heq : B.ϖ ^ k * (x - B.ϖ * y) = 0 := by
    calc B.ϖ ^ k * (x - B.ϖ * y) = B.ϖ ^ k * x - (B.ϖ ^ k * B.ϖ) * y := by ring
      _ = B.ϖ ^ k * x - B.ϖ ^ (k + 1) * y := by rw [pow_succ]
      _ = 0 := sub_eq_zero.mpr hy
  have hxy : x = B.ϖ * y := sub_eq_zero.mp (B.hreg_pow k _ heq)
  rw [Ideal.Quotient.eq_zero_iff_mem, pow_one, Ideal.mem_span_singleton]
  exact ⟨y, hxy⟩

lemma modProj_liftStep (B : LocalHermBase) (k : ℕ) (u : B.ModRing 1) :
    modProj B.ϖ (Nat.le_succ k) (B.liftStep k u) = 0 := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective u
  rw [liftStep_mk, modProj_mk, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  exact ⟨x, rfl⟩

lemma exists_liftStep_of_modProj_eq_zero (B : LocalHermBase) (k : ℕ) {z : B.ModRing (k + 1)}
    (hz : modProj B.ϖ (Nat.le_succ k) z = 0) :
    ∃ u : B.ModRing 1, B.liftStep k u = z := by
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective z
  rw [modProj_mk, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at hz
  rcases hz with ⟨x, rfl⟩
  exact ⟨Ideal.Quotient.mk _ x, rfl⟩

lemma liftStep_mul_liftStep (B : LocalHermBase) {k : ℕ} (hk : 1 ≤ k)
    (u v : B.ModRing 1) :
    B.liftStep k u * B.liftStep k v = 0 := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective u
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective v
  rw [liftStep_mk, liftStep_mk, ← map_mul, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  refine ⟨B.ϖ ^ (k - 1) * x * y, ?_⟩
  have hpow : B.ϖ ^ k * B.ϖ ^ k = B.ϖ ^ (k + 1) * B.ϖ ^ (k - 1) := by
    rw [← pow_add, ← pow_add, show k + k = (k + 1) + (k - 1) by omega]
  calc (B.ϖ ^ k * x) * (B.ϖ ^ k * y) = (B.ϖ ^ k * B.ϖ ^ k) * x * y := by ring
    _ = B.ϖ ^ (k + 1) * (B.ϖ ^ (k - 1) * x * y) := by rw [hpow]; ring

lemma mul_liftStep_left (B : LocalHermBase) (k : ℕ) (a : B.ModRing (k + 1)) (u : B.ModRing 1) :
    a * B.liftStep k u = B.liftStep k (modProj B.ϖ (by omega : 1 ≤ k + 1) a * u) := by
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective u
  rw [liftStep_mk, modProj_mk, ← map_mul, ← map_mul, liftStep_mk]
  congr 1; ring

lemma mul_liftStep_right (B : LocalHermBase) (k : ℕ) (u : B.ModRing 1) (a : B.ModRing (k + 1)) :
    B.liftStep k u * a = B.liftStep k (u * modProj B.ϖ (by omega : 1 ≤ k + 1) a) := by
  rw [mul_comm, B.mul_liftStep_left, mul_comm]

lemma modInv_liftStep (B : LocalHermBase) (k : ℕ) (u : B.ModRing 1) :
    B.modInvAt (k + 1) (B.liftStep k u) = B.liftStep k (B.modInvAt 1 u) := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective u
  simp only [liftStep_mk, modInvAt, modInv_mk, map_mul, map_pow, B.hσ_pi]

lemma modRing_finite (B : LocalHermBase) (k : ℕ) : Finite (B.ModRing k) := by
  induction k with
  | zero =>
    have : Subsingleton (B.ModRing 0) :=
      ⟨fun a b => by
        obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
        obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective b
        apply Ideal.Quotient.eq.mpr
        rw [pow_zero, Ideal.span_singleton_one]
        trivial⟩
    exact Finite.of_subsingleton
  | succ k ih =>
    let π := modProj B.ϖ (Nat.le_succ k)
    have hsurj : Function.Surjective π := modProj_surjective B.ϖ (Nat.le_succ k)
    let sec : B.ModRing k → B.ModRing (k + 1) := Function.surjInv hsurj
    have hsec : ∀ y, π (sec y) = y := Function.surjInv_eq hsurj
    have hdiff_zero : ∀ x : B.ModRing (k + 1), π (x - sec (π x)) = 0 := fun x => by
      rw [map_sub, hsec, sub_self]
    let e : B.ModRing (k + 1) ≃ B.ModRing k × B.ModRing 1 :=
      { toFun := fun x =>
          (π x, Classical.choose (B.exists_liftStep_of_modProj_eq_zero k (hdiff_zero x)))
        invFun := fun ⟨y, u⟩ => sec y + B.liftStep k u
        left_inv := fun x => by
          have hc := Classical.choose_spec (B.exists_liftStep_of_modProj_eq_zero k (hdiff_zero x))
          dsimp only
          rw [hc, add_sub_cancel]
        right_inv := fun ⟨y, u⟩ => by
          ext1
          · simp [π, map_add, hsec, modProj_liftStep]
          · apply B.liftStep_injective k
            have hc := Classical.choose_spec
              (B.exists_liftStep_of_modProj_eq_zero k (hdiff_zero (sec y + B.liftStep k u)))
            dsimp only
            rw [hc]
            have hpi : π (sec y + B.liftStep k u) = y := by
              simp [π, map_add, hsec, modProj_liftStep]
            rw [hpi]
            ring }
    have : Finite (B.ModRing 1) := B.modRing_one_finite
    exact Finite.of_equiv (B.ModRing k × B.ModRing 1) e.symm

/-- Precision-`k` congruence representation set `{ X ∈ Mat_{m × n}(S / ϖ^k) | X^* H X ≡ T mod ϖ^k }`. -/
abbrev RepSet (B : LocalHermBase) (k : ℕ) {m n : ℕ}
    (H : Matrix (Fin m) (Fin m) B.S) (T : Matrix (Fin n) (Fin n) B.S) : Type _ :=
  { X : Matrix (Fin m) (Fin n) (B.ModRing k) //
    hermConj (B.modInvAt k) X * (B.modMat k H) * X = B.modMat k T }

/-- Precision-`k` congruence representation count `N_{ϖ^k}(H, T)`. -/
def repCount (B : LocalHermBase) (k : ℕ) {m n : ℕ}
    (H : Matrix (Fin m) (Fin m) B.S) (T : Matrix (Fin n) (Fin n) B.S) : ℕ :=
  Nat.card (RepSet B k H T)

/-- Normalized precision-`k` local representation density `N_{ϖ^k}(H, T) / q^{k(2mn - n^2)}`. -/
def normalizedRepDensity (B : LocalHermBase) (k : ℕ) {m n : ℕ}
    (H : Matrix (Fin m) (Fin m) B.S) (T : Matrix (Fin n) (Fin n) B.S) : ℝ :=
  (repCount B k H T : ℝ) / (B.q : ℝ) ^ (k * (2 * m * n - n ^ 2))

/-- Hensel lifting recursion: for `1 ≤ k`, `n ≤ m`, and Hermitian unimodular `H, T` mod `ϖ`,
each solution mod `ϖ^k` has exactly `q^{2mn - n^2}` lifts mod `ϖ^{k+1}`. -/
theorem repCount_hensel_succ (B : LocalHermBase) {k : ℕ} (hk : 1 ≤ k)
    {m n : ℕ} (hnm : n ≤ m)
    (H : Matrix (Fin m) (Fin m) B.S) (hH : IsHermMatrix B.σ H)
    (hH_unit : IsUnit (B.modMat 1 H).det)
    (T : Matrix (Fin n) (Fin n) B.S) (hT : IsHermMatrix B.σ T)
    (hT_unit : IsUnit (B.modMat 1 T).det) :
    repCount B (k + 1) H T = B.q ^ (2 * m * n - n ^ 2) * repCount B k H T := by
  classical
  have _ := hH_unit
  have : Finite (B.ModRing 1) := B.modRing_one_finite
  have : Finite (B.ModRing k) := B.modRing_finite k
  have : Finite (B.ModRing (k + 1)) := B.modRing_finite (k + 1)
  let : Fintype (B.ModRing 1) := Fintype.ofFinite _
  let : Fintype (B.ModRing k) := Fintype.ofFinite _
  let : Fintype (B.ModRing (k + 1)) := Fintype.ofFinite _
  let : DecidableEq (B.ModRing 1) := Classical.decEq _
  let : DecidableEq (B.ModRing k) := Classical.decEq _
  let : DecidableEq (B.ModRing (k + 1)) := Classical.decEq _
  let π := modProj B.ϖ (Nat.le_succ k)
  let π₁ := modProj B.ϖ (by omega : 1 ≤ k + 1)
  let π₀₁ := modProj B.ϖ hk
  let liftMat {a b : ℕ} (M : Matrix (Fin a) (Fin b) (B.ModRing 1)) :
      Matrix (Fin a) (Fin b) (B.ModRing (k + 1)) :=
    Matrix.of fun i j => B.liftStep k (M i j)
  have hπ_lift : ∀ {a b : ℕ} (M : Matrix (Fin a) (Fin b) (B.ModRing 1)),
      (liftMat M).map π = 0 := fun M => by
    ext i j; exact modProj_liftStep B k (M i j)
  have hlift_inj : ∀ {a b : ℕ} {M₁ M₂ : Matrix (Fin a) (Fin b) (B.ModRing 1)},
      liftMat M₁ = liftMat M₂ → M₁ = M₂ := fun h => by
    ext i j; exact B.liftStep_injective k (congrFun (congrFun h i) j)
  have hlift_add : ∀ {a b : ℕ} (M₁ M₂ : Matrix (Fin a) (Fin b) (B.ModRing 1)),
      liftMat (M₁ + M₂) = liftMat M₁ + liftMat M₂ := fun M₁ M₂ => by
    ext i j; simp [liftMat, map_add]
  have hlift_herm : ∀ {a b : ℕ} (M : Matrix (Fin a) (Fin b) (B.ModRing 1)),
      hermConj (B.modInvAt (k + 1)) (liftMat M) = liftMat (hermConj (B.modInvAt 1) M) := fun M => by
    ext i j; simp [liftMat, hermConj, modInv_liftStep]
  have hmul_left : ∀ {a b c : ℕ} (A : Matrix (Fin a) (Fin b) (B.ModRing (k + 1)))
      (M : Matrix (Fin b) (Fin c) (B.ModRing 1)),
      A * liftMat M = liftMat (A.map π₁ * M) := fun A M => by
    ext i j
    simp only [Matrix.mul_apply, liftMat, Matrix.of_apply, mul_liftStep_left, ← map_sum,
      Matrix.map_apply, π₁]
  have hmul_right : ∀ {a b c : ℕ} (M : Matrix (Fin a) (Fin b) (B.ModRing 1))
      (A : Matrix (Fin b) (Fin c) (B.ModRing (k + 1))),
      liftMat M * A = liftMat (M * A.map π₁) := fun M A => by
    ext i j
    simp only [Matrix.mul_apply, liftMat, Matrix.of_apply, mul_liftStep_right, ← map_sum,
      Matrix.map_apply, π₁]
  have hmul_quad : ∀ {a b c d : ℕ} (M₁ : Matrix (Fin a) (Fin b) (B.ModRing 1))
      (A : Matrix (Fin b) (Fin c) (B.ModRing (k + 1)))
      (M₂ : Matrix (Fin c) (Fin d) (B.ModRing 1)),
      liftMat M₁ * A * liftMat M₂ = 0 := fun M₁ A M₂ => by
    rw [hmul_right]
    ext i j
    simp only [Matrix.mul_apply, liftMat, Matrix.of_apply, liftStep_mul_liftStep B hk,
      Finset.sum_const_zero, Matrix.zero_apply]
  have hermConj_modProj : ∀ {a b : ℕ} (hab : b ≤ a) {r s : ℕ}
      (M : Matrix (Fin r) (Fin s) (B.ModRing a)),
      (hermConj (B.modInvAt a) M).map (modProj B.ϖ hab) =
        hermConj (B.modInvAt b) (M.map (modProj B.ϖ hab)) := fun {a b} hab {r s} M => by
    ext i j
    simp only [Matrix.map_apply, hermConj_apply, modInvAt, modProj_modInv]
  let projRep : RepSet B (k + 1) H T → RepSet B k H T := fun X =>
    ⟨X.1.map π, by
      have h := congrArg (fun M => Matrix.map M π) X.2
      dsimp only [π] at h ⊢
      rw [map_mul_mat, map_mul_mat, hermConj_modProj, modProj_modMat, modProj_modMat] at h
      exact h⟩
  have hfib_card : ∀ X₀ : RepSet B k H T,
      Nat.card { X : RepSet B (k + 1) H T // projRep X = X₀ } = B.q ^ (2 * m * n - n ^ 2) := by
    intro X₀
    have hlift_mat : ∃ Xtilde : Matrix (Fin m) (Fin n) B.S, B.modMat k Xtilde = X₀.1 := by
      refine ⟨Matrix.of fun i j => Classical.choose (Ideal.Quotient.mk_surjective (X₀.1 i j)), ?_⟩
      ext i j
      exact Classical.choose_spec (Ideal.Quotient.mk_surjective (X₀.1 i j))
    obtain ⟨Xtilde, hXtilde⟩ := hlift_mat
    let X' := B.modMat (k + 1) Xtilde
    let X₁ := B.modMat 1 Xtilde
    let Hk1 := B.modMat (k + 1) H
    let Tk1 := B.modMat (k + 1) T
    let H₁ := B.modMat 1 H
    let T₁ := B.modMat 1 T
    have hπX' : X'.map π = X₀.1 := by
      rw [← hXtilde]; exact B.modProj_modMat (Nat.le_succ k) Xtilde
    have hπ1X' : X'.map π₁ = X₁ := B.modProj_modMat _ Xtilde
    have hπ1H : Hk1.map π₁ = H₁ := B.modProj_modMat _ H
    have hX1_sol : hermConj (B.modInvAt 1) X₁ * H₁ * X₁ = T₁ := by
      have h := congrArg (fun M => Matrix.map M π₀₁) X₀.2
      rw [show (X₀.1 : Matrix (Fin m) (Fin n) (B.ModRing k)) = B.modMat k Xtilde from hXtilde.symm] at h
      dsimp only [π₀₁] at h
      rw [map_mul_mat, map_mul_mat, hermConj_modProj, modProj_modMat, modProj_modMat, modProj_modMat] at h
      exact h
    let resMat : Matrix (Fin n) (Fin n) (B.ModRing (k + 1)) :=
      hermConj (B.modInvAt (k + 1)) X' * Hk1 * X' - Tk1
    have hres_proj : resMat.map π = 0 := by
      dsimp only [resMat, π]
      rw [map_sub_mat, map_mul_mat, map_mul_mat, hermConj_modProj,
        show X'.map (modProj B.ϖ (Nat.le_succ k)) = X₀.1 from hπX',
        modProj_modMat, modProj_modMat, X₀.2, sub_self]
    let R₀ : Matrix (Fin n) (Fin n) (B.ModRing 1) :=
      Matrix.of fun i j => Classical.choose (B.exists_liftStep_of_modProj_eq_zero k (by
        simpa [Matrix.map_apply] using congrFun (congrFun hres_proj i) j))
    have hR₀ : liftMat R₀ = resMat := by
      ext i j
      exact Classical.choose_spec (B.exists_liftStep_of_modProj_eq_zero k (by
        simpa [Matrix.map_apply] using congrFun (congrFun hres_proj i) j))
    have hres_herm : IsHermMatrix (B.modInvAt (k + 1)) resMat := by
      have h1 : IsHermMatrix (B.modInvAt (k + 1)) (hermConj (B.modInvAt (k + 1)) X' * Hk1 * X') :=
        isHermMatrix_congr (B.modInvAt (k + 1)) (B.modMat_isHerm (k + 1) hH)
          (modInv_involutive B.σ B.hσ_inv B.ϖ B.hσ_pi (k + 1)) X'
      have h2 : IsHermMatrix (B.modInvAt (k + 1)) Tk1 := B.modMat_isHerm (k + 1) hT
      intro i j
      simp only [resMat, Matrix.sub_apply, map_sub, h1 i j, h2 i j]
    have hR₀_herm : IsHermMatrix (B.modInvAt 1) R₀ := by
      rw [isHermMatrix_iff_hermConj]
      apply hlift_inj
      rw [← hlift_herm, hR₀]
      exact (isHermMatrix_iff_hermConj _ _).mp hres_herm
    let Herm1 : AddSubgroup (Matrix (Fin n) (Fin n) (B.ModRing 1)) :=
      { carrier := { A | IsHermMatrix (B.modInvAt 1) A }
        zero_mem' := fun i j => by simp
        add_mem' := fun {A C} hA hC i j => by simp [map_add, hA i j, hC i j]
        neg_mem' := fun {A} hA i j => by simp [map_neg, hA i j] }
    have hσ₁ : ∀ x, B.modInvAt 1 (B.modInvAt 1 x) = x :=
      modInv_involutive _ B.hσ_inv _ B.hσ_pi 1
    let D : Matrix (Fin m) (Fin n) (B.ModRing 1) →+ Herm1 :=
      { toFun := fun Δ =>
          ⟨hermConj (B.modInvAt 1) X₁ * H₁ * Δ + hermConj (B.modInvAt 1) Δ * H₁ * X₁, by
            change IsHermMatrix (B.modInvAt 1) _
            rw [isHermMatrix_iff_hermConj, hermConj_add]
            have hH₁ : hermConj (B.modInvAt 1) H₁ = H₁ :=
              (isHermMatrix_iff_hermConj _ _).mp (B.modMat_isHerm 1 hH)
            have hstep : hermConj (B.modInvAt 1) (hermConj (B.modInvAt 1) X₁ * H₁ * Δ) =
                hermConj (B.modInvAt 1) Δ * H₁ * X₁ := by
              rw [hermConj_mul, hermConj_mul, hermConj_involutive _ hσ₁, hH₁, Matrix.mul_assoc]
            have hstep' : hermConj (B.modInvAt 1) (hermConj (B.modInvAt 1) Δ * H₁ * X₁) =
                hermConj (B.modInvAt 1) X₁ * H₁ * Δ := by
              rw [hermConj_mul, hermConj_mul, hermConj_involutive _ hσ₁, hH₁, Matrix.mul_assoc]
            rw [hstep, hstep', add_comm]⟩
        map_zero' := Subtype.ext (by
          have h0 : hermConj (B.modInvAt 1) (0 : Matrix (Fin m) (Fin n) (B.ModRing 1)) = 0 := by
            ext i j; simp [hermConj]
          change hermConj (B.modInvAt 1) X₁ * H₁ * 0 + hermConj (B.modInvAt 1) 0 * H₁ * X₁ = 0
          rw [h0, Matrix.mul_zero, Matrix.zero_mul, Matrix.zero_mul, add_zero])
        map_add' := fun Δ₁ Δ₂ => Subtype.ext (by
          change hermConj (B.modInvAt 1) X₁ * H₁ * (Δ₁ + Δ₂) +
              hermConj (B.modInvAt 1) (Δ₁ + Δ₂) * H₁ * X₁ =
            (hermConj (B.modInvAt 1) X₁ * H₁ * Δ₁ + hermConj (B.modInvAt 1) Δ₁ * H₁ * X₁) +
              (hermConj (B.modInvAt 1) X₁ * H₁ * Δ₂ + hermConj (B.modInvAt 1) Δ₂ * H₁ * X₁)
          rw [hermConj_add, Matrix.mul_add, Matrix.add_mul, Matrix.add_mul]
          abel) }
    have hD_surj : Function.Surjective D := by
      intro ⟨A, hA⟩
      obtain ⟨e, he⟩ := B.exists_trace_one_modOne
      let Btri : Matrix (Fin n) (Fin n) (B.ModRing 1) := Matrix.of fun i j =>
        if i < j then A i j else if i = j then e * A i i else 0
      have hBtri : Btri + hermConj (B.modInvAt 1) Btri = A := by
        ext i j
        rcases lt_trichotomy i j with hij | rfl | hji
        · have hnot : ¬ (j < i) := not_lt_of_gt hij
          simp [Btri, hermConj, hij, hnot, hij.ne.symm]
        · have hdiag : B.modInvAt 1 (A i i) = A i i := hA i i
          simp only [Btri, Matrix.add_apply, hermConj_apply, Matrix.of_apply, lt_self_iff_false,
            ↓reduceIte, map_mul, hdiag, ← add_mul, he, one_mul]
        · have hnot : ¬ (i < j) := not_lt_of_gt hji
          simp [Btri, hermConj, hji, hnot, hji.ne', hA i j]
      let Δ : Matrix (Fin m) (Fin n) (B.ModRing 1) := X₁ * T₁⁻¹ * Btri
      refine ⟨Δ, Subtype.ext ?_⟩
      have hhalf : hermConj (B.modInvAt 1) X₁ * H₁ * Δ = Btri := by
        calc hermConj (B.modInvAt 1) X₁ * H₁ * (X₁ * T₁⁻¹ * Btri)
            = (hermConj (B.modInvAt 1) X₁ * H₁ * X₁) * T₁⁻¹ * Btri := by
                simp only [Matrix.mul_assoc]
          _ = T₁ * T₁⁻¹ * Btri := by rw [hX1_sol]
          _ = Btri := by rw [Matrix.mul_nonsing_inv T₁ hT_unit, Matrix.one_mul]
      have hH₁ : hermConj (B.modInvAt 1) H₁ = H₁ :=
        (isHermMatrix_iff_hermConj _ _).mp (B.modMat_isHerm 1 hH)
      have hother : hermConj (B.modInvAt 1) Δ * H₁ * X₁ = hermConj (B.modInvAt 1) Btri := by
        have hrev := congrArg (hermConj (B.modInvAt 1)) hhalf
        rw [hermConj_mul (B.modInvAt 1) (hermConj (B.modInvAt 1) X₁ * H₁) Δ,
          hermConj_mul (B.modInvAt 1) (hermConj (B.modInvAt 1) X₁) H₁,
          hH₁, hermConj_involutive _ hσ₁, ← Matrix.mul_assoc] at hrev
        exact hrev
      change hermConj (B.modInvAt 1) X₁ * H₁ * Δ + hermConj (B.modInvAt 1) Δ * H₁ * X₁ = A
      rw [hhalf, hother, hBtri]
    have hquad_eq : ∀ Δ : Matrix (Fin m) (Fin n) (B.ModRing 1),
        hermConj (B.modInvAt (k + 1)) (X' + liftMat Δ) * Hk1 * (X' + liftMat Δ) - Tk1 =
          liftMat (R₀ + (D Δ).1) := by
      intro Δ
      have hπX1 : (hermConj (B.modInvAt (k + 1)) X').map π₁ = hermConj (B.modInvAt 1) X₁ := by
        dsimp only [π₁]
        rw [hermConj_modProj, hπ1X']
      have h1 : hermConj (B.modInvAt (k + 1)) X' * Hk1 * liftMat Δ =
          liftMat (hermConj (B.modInvAt 1) X₁ * H₁ * Δ) := by
        rw [hmul_left, map_mul_mat, hπX1, hπ1H]
      have h2 : hermConj (B.modInvAt (k + 1)) (liftMat Δ) * Hk1 * X' =
          liftMat (hermConj (B.modInvAt 1) Δ * H₁ * X₁) := by
        rw [hlift_herm, Matrix.mul_assoc, hmul_right, map_mul_mat,
          hπ1H, hπ1X', ← Matrix.mul_assoc]
      have h3 : hermConj (B.modInvAt (k + 1)) (liftMat Δ) * Hk1 * liftMat Δ = 0 := by
        rw [hlift_herm]; exact hmul_quad _ Hk1 Δ
      rw [hlift_add, hR₀, hermConj_add, Matrix.add_mul, Matrix.mul_add, Matrix.add_mul,
        Matrix.add_mul, h1, h2, h3, add_zero,
        add_assoc (hermConj (B.modInvAt (k + 1)) X' * Hk1 * X'), ← hlift_add]
      dsimp only [resMat, D, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
      rw [add_comm (hermConj (B.modInvAt 1) Δ * H₁ * X₁)]
      abel
    let target : Herm1 := ⟨-R₀, by
      intro i j
      simp only [Matrix.neg_apply, map_neg, hR₀_herm i j]⟩
    let extractMat {a b : ℕ} (M : Matrix (Fin a) (Fin b) (B.ModRing (k + 1)))
        (hM : M.map π = 0) : Matrix (Fin a) (Fin b) (B.ModRing 1) :=
      Matrix.of fun i j => Classical.choose (B.exists_liftStep_of_modProj_eq_zero k (by
        have hij := congrFun (congrFun hM i) j
        simpa [Matrix.map_apply] using hij))
    have hextract : ∀ {a b : ℕ} (M : Matrix (Fin a) (Fin b) (B.ModRing (k + 1)))
        (hM : M.map π = 0), liftMat (extractMat M hM) = M := fun M hM => by
      ext i j
      exact Classical.choose_spec (B.exists_liftStep_of_modProj_eq_zero k (by
        have hij := congrFun (congrFun hM i) j
        simpa [Matrix.map_apply] using hij))
    let eFib : { X : RepSet B (k + 1) H T // projRep X = X₀ } ≃
        { Δ : Matrix (Fin m) (Fin n) (B.ModRing 1) // D Δ = target } :=
      { toFun := fun x =>
          have hdiff : (x.1.1 - X').map π = 0 := by
            simp only [map_sub_mat, hπX']
            exact sub_eq_zero.mpr (congrArg Subtype.val x.2)
          let Δ : Matrix (Fin m) (Fin n) (B.ModRing 1) := extractMat (x.1.1 - X') hdiff
          ⟨Δ, Subtype.ext <| by
            have hΔ : liftMat Δ = x.1.1 - X' := hextract (x.1.1 - X') hdiff
            have hX : x.1.1 = X' + liftMat Δ := by rw [hΔ, add_sub_cancel]
            have hsol : hermConj (B.modInvAt (k + 1)) (X' + liftMat Δ) * Hk1 * (X' + liftMat Δ) - Tk1 = 0 :=
              sub_eq_zero.mpr (by rw [← hX]; exact x.1.2)
            rw [hquad_eq Δ] at hsol
            have hzero : (D Δ).1 + R₀ = 0 := by
              rw [add_comm]
              exact hlift_inj (hsol.trans (by ext i j; simp [liftMat]))
            exact eq_neg_of_add_eq_zero_left hzero⟩
        invFun := fun y =>
          ⟨⟨X' + liftMat y.1, by
            apply sub_eq_zero.mp
            rw [hquad_eq y.1]
            have hsum : R₀ + (D y.1).1 = 0 := by
              have hval := congrArg Subtype.val y.2
              change (D y.1).1 = -R₀ at hval
              rw [hval, add_neg_cancel]
            rw [hsum]
            ext i j; simp [liftMat]⟩,
           Subtype.ext (by simp [projRep, map_add_mat, hπX', hπ_lift])⟩
        left_inv := fun x => by
          apply Subtype.ext; apply Subtype.ext
          dsimp only
          have hm : ((x.1 : Matrix (Fin m) (Fin n) (B.ModRing (k + 1))) - X').map ⇑π = 0 := by
            rw [map_sub_mat]
            have hx : (x.1 : Matrix (Fin m) (Fin n) (B.ModRing (k + 1))).map ⇑π = X₀.1 :=
              congrArg Subtype.val x.2
            rw [hx, hπX', sub_self]
          rw [hextract _ hm, add_sub_cancel]
        right_inv := fun y => by
          apply Subtype.ext; apply hlift_inj
          dsimp only
          have hm : (X' + liftMat y.1 - X').map ⇑π = 0 := by
            rw [add_sub_cancel_left]
            exact hπ_lift y.1
          rw [hextract _ hm, add_sub_cancel_left] }
    have hfib_ker : ∀ y : Herm1, Nat.card { Δ : Matrix (Fin m) (Fin n) (B.ModRing 1) // D Δ = y } =
        Nat.card D.ker := by
      intro y
      obtain ⟨Δ₀, hΔ₀⟩ := hD_surj y
      refine Nat.card_congr
        { toFun := fun ⟨Δ, hΔ⟩ => ⟨Δ - Δ₀, by
            rw [AddMonoidHom.mem_ker, map_sub, hΔ, hΔ₀, sub_self]⟩
          invFun := fun ⟨W, hW⟩ => ⟨W + Δ₀, by
            rw [map_add, AddMonoidHom.mem_ker.mp hW, zero_add, hΔ₀]⟩
          left_inv := fun ⟨Δ, _⟩ => Subtype.ext (sub_add_cancel Δ Δ₀)
          right_inv := fun ⟨W, _⟩ => Subtype.ext (add_sub_cancel_right W Δ₀) }
    have hker_prod : Nat.card (Matrix (Fin m) (Fin n) (B.ModRing 1)) =
        Nat.card Herm1 * Nat.card D.ker := by
      have hpart := Finset.card_eq_sum_card_fiberwise (f := D) (s := Finset.univ)
        (t := Finset.univ) (fun _ _ => Finset.mem_univ _)
      rw [Finset.card_univ] at hpart
      have hsum : ∑ y : Herm1, (Finset.univ.filter fun a => D a = y).card =
          ∑ _y : Herm1, Nat.card D.ker := by
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [← Fintype.card_coe]
        have hcoe : Fintype.card ↥(Finset.univ.filter fun a => D a = y) =
            Nat.card { Δ : Matrix (Fin m) (Fin n) (B.ModRing 1) // D Δ = y } := by
          rw [Nat.card_eq_fintype_card]
          exact Fintype.card_congr
            { toFun := fun ⟨a, ha⟩ => ⟨a, (Finset.mem_filter.mp ha).2⟩
              invFun := fun ⟨a, ha⟩ => ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩⟩
              left_inv := fun ⟨_, _⟩ => rfl
              right_inv := fun ⟨_, _⟩ => rfl }
        rw [hcoe, hfib_ker y]
      rw [Nat.card_eq_fintype_card, hpart, hsum, Finset.sum_const, Finset.card_univ, smul_eq_mul,
        ← Nat.card_eq_fintype_card]
    have hMat_card : Nat.card (Matrix (Fin m) (Fin n) (B.ModRing 1)) = B.q ^ (2 * m * n) := by
      have eMat : Matrix (Fin m) (Fin n) (B.ModRing 1) ≃ (Fin m × Fin n → B.ModRing 1) :=
        { toFun := fun M p => M p.1 p.2
          invFun := fun f => Matrix.of fun i j => f (i, j)
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      rw [Nat.card_congr eMat, Nat.card_fun, B.card_modRing_one, Nat.card_prod,
        Nat.card_fin, Nat.card_fin, ← pow_mul]
      congr 1; ring
    have hHerm_card : Nat.card Herm1 = B.q ^ (n ^ 2) := B.card_herm_modRing_one n
    have hle_exp : n ^ 2 ≤ 2 * m * n := by nlinarith
    have hker_eq : Nat.card D.ker = B.q ^ (2 * m * n - n ^ 2) := by
      have hmul : B.q ^ (n ^ 2) * Nat.card D.ker = B.q ^ (n ^ 2) * B.q ^ (2 * m * n - n ^ 2) := by
        calc B.q ^ (n ^ 2) * Nat.card D.ker
            = Nat.card Herm1 * Nat.card D.ker := by rw [hHerm_card]
          _ = B.q ^ (2 * m * n) := by rw [← hker_prod, hMat_card]
          _ = B.q ^ (n ^ 2) * B.q ^ (2 * m * n - n ^ 2) := by
              rw [← pow_add, Nat.add_sub_of_le hle_exp]
      exact mul_left_cancel₀ (pow_ne_zero _ B.q_pos.ne') hmul
    rw [Nat.card_congr eFib, hfib_ker target, hker_eq]
  have hpart_rep := Finset.card_eq_sum_card_fiberwise (f := projRep) (s := Finset.univ)
    (t := Finset.univ) (fun _ _ => Finset.mem_univ _)
  rw [Finset.card_univ] at hpart_rep
  have hsum_rep : ∑ X₀ : RepSet B k H T, (Finset.univ.filter fun a => projRep a = X₀).card =
      ∑ _X₀ : RepSet B k H T, B.q ^ (2 * m * n - n ^ 2) := by
    refine Finset.sum_congr rfl fun X₀ _ => ?_
    rw [← Fintype.card_coe, ← Nat.card_eq_fintype_card]
    have hcoe : Nat.card ↥(Finset.univ.filter fun a => projRep a = X₀) =
        Nat.card { X : RepSet B (k + 1) H T // projRep X = X₀ } :=
      Nat.card_congr
        { toFun := fun ⟨X, hX⟩ => ⟨X, (Finset.mem_filter.mp hX).2⟩
          invFun := fun ⟨X, hX⟩ => ⟨X, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hX⟩⟩
          left_inv := fun ⟨_, _⟩ => rfl
          right_inv := fun ⟨_, _⟩ => rfl }
    rw [hcoe, hfib_card X₀]
  rw [repCount, repCount, Nat.card_eq_fintype_card, hpart_rep, hsum_rep, Finset.sum_const,
    Finset.card_univ, smul_eq_mul, ← Nat.card_eq_fintype_card, mul_comm]

/-- Stabilization theorem: for all `k ≥ 1`, `normalizedRepDensity B k H T = normalizedRepDensity B 1 H T`. -/
theorem normalizedRepDensity_const_of_unimodular (B : LocalHermBase) {k : ℕ} (hk : 1 ≤ k)
    {m n : ℕ} (hnm : n ≤ m)
    (H : Matrix (Fin m) (Fin m) B.S) (hH : IsHermMatrix B.σ H)
    (hH_unit : IsUnit (B.modMat 1 H).det)
    (T : Matrix (Fin n) (Fin n) B.S) (hT : IsHermMatrix B.σ T)
    (hT_unit : IsUnit (B.modMat 1 T).det) :
    normalizedRepDensity B k H T = normalizedRepDensity B 1 H T := by
  induction k, hk using Nat.le_induction with
  | base => rfl
  | succ k hk ih =>
      unfold normalizedRepDensity
      rw [repCount_hensel_succ B hk hnm H hH hH_unit T hT hT_unit]
      push_cast
      have hpow : (B.q : ℝ) ^ ((k + 1) * (2 * m * n - n ^ 2)) =
          (B.q : ℝ) ^ (2 * m * n - n ^ 2) * (B.q : ℝ) ^ (k * (2 * m * n - n ^ 2)) := by
        rw [← pow_add]
        congr 1; ring
      rw [hpow, mul_div_mul_left _ _ (pow_ne_zero _ B.q_real_ne_zero)]
      exact ih

end LocalHermBase

/-- Local representation density `α_v(L, T)` defined as the `liminf` of the precision-`k`
normalized representation counts `N_{ϖ^k}(L, T) / q_v^{k(2mn - n^2)}`. -/
def LocalRepresentationDensity {ι : Type*} {v : ι} (L : LocalHermLattice v)
    {n : ℕ} (T : Matrix (Fin n) (Fin n) L.base.S) : ℝ :=
  Filter.liminf (fun k => L.base.normalizedRepDensity k L.gram T) Filter.atTop

/-- For unimodular `L` and `T` (`n ≤ rank L`), `LocalRepresentationDensity L T` stabilizes at `k = 1`. -/
theorem localRepresentationDensity_eq_one {ι : Type*} {v : ι} (L : LocalHermLattice v)
    {n : ℕ} (hnm : n ≤ L.rank)
    (T : Matrix (Fin n) (Fin n) L.base.S) (hT : IsHermMatrix L.base.σ T)
    (hT_unit : IsUnit (L.base.modMat 1 T).det) :
    LocalRepresentationDensity L T = L.base.normalizedRepDensity 1 L.gram T := by
  unfold LocalRepresentationDensity
  have hev : ∀ᶠ k in Filter.atTop,
      L.base.normalizedRepDensity k L.gram T = L.base.normalizedRepDensity 1 L.gram T := by
    refine Filter.eventually_atTop.mpr ⟨1, fun k hk => ?_⟩
    exact L.base.normalizedRepDensity_const_of_unimodular hk hnm L.gram L.herm L.unimodular T hT hT_unit
  rw [Filter.liminf_congr hev]
  exact Filter.liminf_const _

end HenselRepresentationDensity

/-! ## Section 4: `local_density_euler_factor` & Exact Unramified `siegel_density_unramified_exact` -/

section ExactUnramifiedSiegelDensity

/-- Local unramified Siegel density Euler factor at residue cardinality `q` and splitting character
`eps ∈ {-1, 1}` for ranks `n ≤ m`:
`∏_{j = m - n + 1}^m (1 - eps^j * q^{-j})`. -/
def local_density_euler_factor (q eps : ℝ) (m n : ℕ) : ℝ :=
  ∏ j ∈ Finset.Icc (m - n + 1) m, (1 - eps ^ j * q ^ (-(j : ℤ)))

lemma local_density_euler_factor_pos {q eps : ℝ} (hq : 2 ≤ q) (heps : |eps| ≤ 1)
    (m n : ℕ) : 0 < local_density_euler_factor q eps m n := by
  unfold local_density_euler_factor
  refine Finset.prod_pos fun j hj => ?_
  have hj1 : 1 ≤ j := by
    have := (Finset.mem_Icc.mp hj).1
    omega
  have hpow : |eps ^ j| ≤ 1 := by
    rw [abs_pow]
    exact pow_le_one₀ (abs_nonneg eps) heps
  have hq1 : (1 : ℝ) < q := by linarith
  have hqj : (2 : ℝ) ≤ q ^ j := by
    calc (2 : ℝ) ≤ q ^ 1 := by simpa using hq
      _ ≤ q ^ j := pow_le_pow_right₀ (by linarith) hj1
  have hterm : eps ^ j * q ^ (-(j : ℤ)) ≤ 1 / 2 := by
    have h1 : eps ^ j ≤ 1 := (abs_le.mp hpow).2
    have h2 : 0 ≤ q ^ (-(j : ℤ)) := by positivity
    have h3 : q ^ (-(j : ℤ)) ≤ 1 / 2 := by
      rw [_root_.zpow_neg, zpow_natCast, inv_eq_one_div]
      exact one_div_le_one_div_of_le (by norm_num) hqj
    calc eps ^ j * q ^ (-(j : ℤ)) ≤ 1 * q ^ (-(j : ℤ)) := mul_le_mul_of_nonneg_right h1 h2
      _ = q ^ (-(j : ℤ)) := one_mul _
      _ ≤ 1 / 2 := h3
  linarith

lemma local_density_euler_factor_le_two_pow {q eps : ℝ} (hq : 2 ≤ q) (heps : |eps| ≤ 1)
    (m n : ℕ) (hnm : n ≤ m) :
    local_density_euler_factor q eps m n ≤ (3 / 2 : ℝ) ^ n := by
  unfold local_density_euler_factor
  have hcard : (Finset.Icc (m - n + 1) m).card = n := by
    rw [Nat.card_Icc]; omega
  calc ∏ j ∈ Finset.Icc (m - n + 1) m, (1 - eps ^ j * q ^ (-(j : ℤ)))
      ≤ ∏ _j ∈ Finset.Icc (m - n + 1) m, (3 / 2 : ℝ) := by
          refine Finset.prod_le_prod (fun j hj => ?_) (fun j hj => ?_)
          · have hj1 : 1 ≤ j := by have := (Finset.mem_Icc.mp hj).1; omega
            have hpow : |eps ^ j| ≤ 1 := by rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) heps
            have hqj : (2 : ℝ) ≤ q ^ j := by
              calc (2 : ℝ) ≤ q ^ 1 := by simpa using hq
                _ ≤ q ^ j := pow_le_pow_right₀ (by linarith) hj1
            have h3 : q ^ (-(j : ℤ)) ≤ 1 / 2 := by
              rw [_root_.zpow_neg, zpow_natCast, inv_eq_one_div]
              exact one_div_le_one_div_of_le (by norm_num) hqj
            have h1 : eps ^ j * q ^ (-(j : ℤ)) ≤ 1 * q ^ (-(j : ℤ)) :=
              mul_le_mul_of_nonneg_right (abs_le.mp hpow).2 (by positivity)
            linarith
          · have hj1 : 1 ≤ j := by have := (Finset.mem_Icc.mp hj).1; omega
            have hpow : |eps ^ j| ≤ 1 := by rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) heps
            have hqj : (2 : ℝ) ≤ q ^ j := by
              calc (2 : ℝ) ≤ q ^ 1 := by simpa using hq
                _ ≤ q ^ j := pow_le_pow_right₀ (by linarith) hj1
            have h3 : q ^ (-(j : ℤ)) ≤ 1 / 2 := by
              rw [_root_.zpow_neg, zpow_natCast, inv_eq_one_div]
              exact one_div_le_one_div_of_le (by norm_num) hqj
            have hneg : -(1 : ℝ) * q ^ (-(j : ℤ)) ≤ eps ^ j * q ^ (-(j : ℤ)) :=
              mul_le_mul_of_nonneg_right (abs_le.mp hpow).1 (by positivity)
            linarith
    _ = (3 / 2 : ℝ) ^ n := by rw [Finset.prod_const, hcard]

/-- At precision `k = 1`, the normalized representation density on any `LocalHermBase` (inert or
split) equals `local_density_euler_factor B.q B.splitting.chi m n`. -/
theorem normalizedRepDensity_one_eq_eulerFactor (B : LocalHermBase) {m n : ℕ} (hnm : n ≤ m)
    (H : Matrix (Fin m) (Fin m) B.S) (hH : IsHermMatrix B.σ H)
    (hH_unit : IsUnit (B.modMat 1 H).det)
    (T : Matrix (Fin n) (Fin n) B.S) (hT : IsHermMatrix B.σ T)
    (hT_unit : IsUnit (B.modMat 1 T).det) :
    B.normalizedRepDensity 1 H T = local_density_euler_factor B.q B.splitting.chi m n := by
  classical
  unfold LocalHermBase.normalizedRepDensity LocalHermBase.repCount local_density_euler_factor
  rw [one_mul]
  cases hw : B.witness with
  | inert k₂ hdim σ₂ hσ₂ iso hσ_iso =>
      let Hk : Matrix (Fin m) (Fin m) k₂ := (B.modMat 1 H).map iso.toRingHom
      let Tk : Matrix (Fin n) (Fin n) k₂ := (B.modMat 1 T).map iso.toRingHom
      have hHk_herm : IsHermMatrix σ₂.toRingHom Hk := fun i j => by
        have hij := B.modMat_isHerm 1 hH i j
        change σ₂ (iso (B.modMat 1 H j i)) = iso (B.modMat 1 H i j)
        rw [← hσ_iso]
        exact congrArg iso hij
      have hTk_herm : IsHermMatrix σ₂.toRingHom Tk := fun i j => by
        have hij := B.modMat_isHerm 1 hT i j
        change σ₂ (iso (B.modMat 1 T j i)) = iso (B.modMat 1 T i j)
        rw [← hσ_iso]
        exact congrArg iso hij
      have hHk_det : Hk.det ≠ 0 := by
        have hdet : Hk.det = iso ((B.modMat 1 H).det) :=
          (RingHom.map_det iso.toRingHom (B.modMat 1 H)).symm
        rw [hdet]
        exact (hH_unit.map iso.toRingHom).ne_zero
      have hTk_det : Tk.det ≠ 0 := by
        have hdet : Tk.det = iso ((B.modMat 1 T).det) :=
          (RingHom.map_det iso.toRingHom (B.modMat 1 T)).symm
        rw [hdet]
        exact (hT_unit.map iso.toRingHom).ne_zero
      let eRep : B.RepSet 1 H T ≃
          { X : Matrix (Fin m) (Fin n) k₂ // hermConj σ₂.toRingHom X * Hk * X = Tk } :=
        { toFun := fun ⟨X, hX⟩ =>
            ⟨X.map iso.toRingHom, by
              have hcomm : ∀ x, iso.toRingHom (B.modInvAt 1 x) = σ₂.toRingHom (iso.toRingHom x) :=
                fun x => hσ_iso x
              have h := congrArg (fun M => Matrix.map M iso.toRingHom) hX
              rw [LocalHermBase.map_mul_mat, LocalHermBase.map_mul_mat,
                LocalHermBase.hermConj_mapMatrix _ _ _ hcomm] at h
              exact h⟩
          invFun := fun ⟨X, hX⟩ =>
            ⟨X.map iso.symm.toRingHom, by
              have hcomm : ∀ y, iso.symm.toRingHom (σ₂.toRingHom y) =
                  B.modInvAt 1 (iso.symm.toRingHom y) := fun y => by
                apply iso.injective
                dsimp only [LocalHermBase.modInvAt]
                change iso (iso.symm (σ₂ y)) = iso ((modInv B.σ B.ϖ B.hσ_pi 1) (iso.symm y))
                rw [hσ_iso, iso.apply_symm_apply, iso.apply_symm_apply]
              have h := congrArg (fun M => Matrix.map M iso.symm.toRingHom) hX
              rw [LocalHermBase.map_mul_mat, LocalHermBase.map_mul_mat,
                LocalHermBase.hermConj_mapMatrix _ _ _ hcomm] at h
              have hH_back : Hk.map iso.symm.toRingHom = B.modMat 1 H := by
                ext i j; simp [Hk]
              have hT_back : Tk.map iso.symm.toRingHom = B.modMat 1 T := by
                ext i j; simp [Tk]
              rwa [hH_back, hT_back] at h⟩
          left_inv := fun ⟨X, _⟩ => Subtype.ext (by ext i j; simp)
          right_inv := fun ⟨X, _⟩ => Subtype.ext (by ext i j; simp) }
      have hcard : Nat.card (B.RepSet 1 H T) =
          Fintype.card { X : Matrix (Fin m) (Fin n) k₂ // hermConj σ₂.toRingHom X * Hk * X = Tk } := by
        rw [Nat.card_congr eRep, Nat.card_eq_fintype_card]
      have hsp : B.splitting = PlaceSplitting.inert := by
        unfold LocalHermBase.splitting; rw [hw]
      rw [hcard, hsp, PlaceSplitting.chi]
      simpa [LocalHermBase.q] using
        card_finite_herm_rep_div (k₁ := B.k₁) (k₂ := k₂) hdim σ₂ hσ₂ hnm Hk hHk_herm hHk_det
          Tk hTk_herm hTk_det
  | split iso hσ_iso =>
      let fstHom : B.k₁ × B.k₁ →+* B.k₁ := RingHom.fst B.k₁ B.k₁
      let sndHom : B.k₁ × B.k₁ →+* B.k₁ := RingHom.snd B.k₁ B.k₁
      let Hp : Matrix (Fin m) (Fin m) (B.k₁ × B.k₁) := (B.modMat 1 H).map iso.toRingHom
      let Tp : Matrix (Fin n) (Fin n) (B.k₁ × B.k₁) := (B.modMat 1 T).map iso.toRingHom
      let A : Matrix (Fin m) (Fin m) B.k₁ := Hp.map fstHom
      let T₁ : Matrix (Fin n) (Fin n) B.k₁ := Tp.map fstHom
      have hHp_snd : Hp.map sndHom = A.transpose := by
        ext i j
        have hij := congrArg iso (B.modMat_isHerm 1 hH i j)
        dsimp only [LocalHermBase.modInvAt] at hij
        rw [hσ_iso] at hij
        exact (congrArg Prod.snd hij).symm
      have hTp_snd : Tp.map sndHom = T₁.transpose := by
        ext i j
        have hij := congrArg iso (B.modMat_isHerm 1 hT i j)
        dsimp only [LocalHermBase.modInvAt] at hij
        rw [hσ_iso] at hij
        exact (congrArg Prod.snd hij).symm
      have hAdet : A.det ≠ 0 := by
        have hunit : IsUnit (A.det) := by
          have hdet : A.det = fstHom (iso ((B.modMat 1 H).det)) := by
            have := RingHom.map_det (fstHom.comp iso.toRingHom) (B.modMat 1 H)
            simpa [A, Hp, Matrix.map_map] using this.symm
          rw [hdet]
          exact hH_unit.map (fstHom.comp iso.toRingHom)
        exact hunit.ne_zero
      have hT1det : T₁.det ≠ 0 := by
        have hunit : IsUnit (T₁.det) := by
          have hdet : T₁.det = fstHom (iso ((B.modMat 1 T).det)) := by
            have := RingHom.map_det (fstHom.comp iso.toRingHom) (B.modMat 1 T)
            simpa [T₁, Tp, Matrix.map_map] using this.symm
          rw [hdet]
          exact hT_unit.map (fstHom.comp iso.toRingHom)
        exact hunit.ne_zero
      let swapHom : B.k₁ × B.k₁ →+* B.k₁ × B.k₁ :=
        { toFun := fun p => (p.2, p.1)
          map_one' := rfl
          map_mul' := fun _ _ => rfl
          map_zero' := rfl
          map_add' := fun _ _ => rfl }
      let eRep : B.RepSet 1 H T ≃
          { X : Matrix (Fin m) (Fin n) B.k₁ × Matrix (Fin m) (Fin n) B.k₁ //
            X.2.transpose * A * X.1 = T₁ } :=
        { toFun := fun ⟨X, hX⟩ =>
            let Xp : Matrix (Fin m) (Fin n) (B.k₁ × B.k₁) := X.map iso.toRingHom
            ⟨(Xp.map fstHom, Xp.map sndHom), by
              have hcomm : ∀ x, iso.toRingHom (B.modInvAt 1 x) = swapHom (iso.toRingHom x) :=
                fun x => hσ_iso x
              have hp := congrArg (fun M => Matrix.map M iso.toRingHom) hX
              rw [LocalHermBase.map_mul_mat, LocalHermBase.map_mul_mat,
                LocalHermBase.hermConj_mapMatrix _ _ _ hcomm] at hp
              have hfst := congrArg (fun M => Matrix.map M fstHom) hp
              rw [LocalHermBase.map_mul_mat, LocalHermBase.map_mul_mat] at hfst
              have hadj_fst : (hermConj swapHom Xp).map fstHom = (Xp.map sndHom).transpose := by
                ext i j; rfl
              rw [hadj_fst] at hfst
              exact hfst⟩
          invFun := fun ⟨⟨X₁, X₂⟩, hX⟩ =>
            let Xp : Matrix (Fin m) (Fin n) (B.k₁ × B.k₁) := Matrix.of fun i j => (X₁ i j, X₂ i j)
            ⟨Xp.map iso.symm.toRingHom, by
              have hcomm : ∀ y, iso.symm.toRingHom (swapHom y) =
                  B.modInvAt 1 (iso.symm.toRingHom y) := fun y => by
                apply iso.injective
                dsimp only [LocalHermBase.modInvAt]
                change iso (iso.symm (swapHom y)) = iso ((modInv B.σ B.ϖ B.hσ_pi 1) (iso.symm y))
                rw [hσ_iso]
                simp only [RingEquiv.apply_symm_apply]
                rfl
              have hp_eq : hermConj swapHom Xp * Hp * Xp = Tp := by
                have hX2 : X₁.transpose * A.transpose * X₂ = T₁.transpose := by
                  have ht := congrArg Matrix.transpose hX
                  simpa [Matrix.transpose_mul, Matrix.mul_assoc] using ht
                ext i j
                · have h1 := congrFun (congrFun hX i) j
                  simpa [Matrix.mul_apply, hermConj_apply, swapHom, Xp, A, T₁, Hp, Tp,
                    fstHom, Prod.fst_sum, Prod.fst_mul] using h1
                · have h2 := congrFun (congrFun hX2 i) j
                  have hA_tr : ∀ r s, (Hp r s).2 = A s r := fun r s =>
                    congrFun (congrFun hHp_snd r) s
                  have hT_tr : (Tp i j).2 = T₁ j i := congrFun (congrFun hTp_snd i) j
                  simpa [Matrix.mul_apply, hermConj_apply, swapHom, Xp, hA_tr, hT_tr,
                    Prod.snd_sum, Prod.snd_mul, mul_assoc] using h2
              have hp := congrArg (fun M => Matrix.map M iso.symm.toRingHom) hp_eq
              rw [LocalHermBase.map_mul_mat, LocalHermBase.map_mul_mat,
                LocalHermBase.hermConj_mapMatrix _ _ _ hcomm] at hp
              have hH_back : Hp.map iso.symm.toRingHom = B.modMat 1 H := by
                ext i j; simp [Hp]
              have hT_back : Tp.map iso.symm.toRingHom = B.modMat 1 T := by
                ext i j; simp [Tp]
              rwa [hH_back, hT_back] at hp⟩
          left_inv := fun ⟨X, _⟩ => Subtype.ext (by ext i j; simp [fstHom, sndHom, Prod.mk.eta])
          right_inv := fun ⟨⟨X₁, X₂⟩, _⟩ => Subtype.ext (Prod.ext
            (by ext i j; simp [fstHom]) (by ext i j; simp [sndHom])) }
      have hcard : (Nat.card (B.RepSet 1 H T) : ℝ) =
          (Fintype.card { X : Matrix (Fin m) (Fin n) B.k₁ × Matrix (Fin m) (Fin n) B.k₁ //
            X.2.transpose * A * X.1 = T₁ } : ℝ) := by
        rw [Nat.card_congr eRep, Nat.card_eq_fintype_card]
      have hsp : B.splitting = PlaceSplitting.split := by
        unfold LocalHermBase.splitting; rw [hw]
      rw [hcard, hsp, PlaceSplitting.chi]
      simpa [LocalHermBase.q] using card_finite_split_rep hnm A hAdet T₁ hT1det

/-- **Main Exact Local Siegel Density Theorem** (`siegel_density_unramified_exact`):
For any finite place `v`, any unimodular local Hermitian lattice `L` of rank `m ≥ 1`, any `n ≤ m`,
and any unimodular Hermitian matrix `T` (`n × n`),
`LocalRepresentationDensity L T = ∏_{j = m - n + 1}^m (1 - χ_v^j q_v^{-j})`. -/
theorem siegel_density_unramified_exact {ι : Type*} {v : ι} (L : LocalHermLattice v)
    {n : ℕ} (hnm : n ≤ L.rank)
    (T : Matrix (Fin n) (Fin n) L.base.S) (hT : IsHermMatrix L.base.σ T)
    (hT_unit : IsUnit (L.base.modMat 1 T).det) :
    LocalRepresentationDensity L T =
      local_density_euler_factor L.base.q L.base.splitting.chi L.rank n := by
  rw [localRepresentationDensity_eq_one L hnm T hT hT_unit]
  exact normalizedRepDensity_one_eq_eulerFactor L.base hnm L.gram L.herm L.unimodular T hT hT_unit

/-- Precision-`k` stabilization form of `siegel_density_unramified_exact` for all `k ≥ 1`. -/
theorem normalizedRepDensity_unramified_exact {ι : Type*} {v : ι} (L : LocalHermLattice v)
    {k : ℕ} (hk : 1 ≤ k) {n : ℕ} (hnm : n ≤ L.rank)
    (T : Matrix (Fin n) (Fin n) L.base.S) (hT : IsHermMatrix L.base.σ T)
    (hT_unit : IsUnit (L.base.modMat 1 T).det) :
    L.base.normalizedRepDensity k L.gram T =
      local_density_euler_factor L.base.q L.base.splitting.chi L.rank n := by
  rw [L.base.normalizedRepDensity_const_of_unimodular hk hnm L.gram L.herm L.unimodular T hT hT_unit]
  exact normalizedRepDensity_one_eq_eulerFactor L.base hnm L.gram L.herm L.unimodular T hT hT_unit

/-- Specialization to a concrete prime place `p` (`LocalHermLattice.ofPrime`). -/
theorem siegel_density_unramified_at_prime (p : ℕ) (hp : p.Prime) (sp : PlaceSplitting)
    (m n : ℕ) (hm : 1 ≤ m) (hnm : n ≤ m) :
    LocalRepresentationDensity (LocalHermLattice.ofPrime p hp sp m hm)
      (1 : Matrix (Fin n) (Fin n) (LocalHermBase.ofPrime p hp sp).S) =
      local_density_euler_factor p sp.chi m n := by
  let B := LocalHermBase.ofPrime p hp sp
  let L : LocalHermLattice p := LocalHermLattice.std p B m hm
  have hT := isHermMatrix_one B.σ n
  have hT_unit : IsUnit (B.modMat 1 (1 : Matrix (Fin n) (Fin n) B.S)).det := by
    have h1 : B.modMat 1 (1 : Matrix (Fin n) (Fin n) B.S) = 1 := by
      ext i j; by_cases hij : i = j <;> simp [LocalHermBase.modMat, Matrix.one_apply, hij]
    rw [h1, Matrix.det_one]; exact isUnit_one
  have hdens : LocalRepresentationDensity L (1 : Matrix (Fin n) (Fin n) B.S) =
      local_density_euler_factor B.q B.splitting.chi L.rank n :=
    siegel_density_unramified_exact L hnm (1 : Matrix (Fin n) (Fin n) B.S) hT hT_unit
  change LocalRepresentationDensity L (1 : Matrix (Fin n) (Fin n) B.S) =
    local_density_euler_factor p sp.chi m n
  rw [hdens, show L.rank = m from rfl, LocalHermBase.q_ofPrime, LocalHermBase.splitting_ofPrime]

end ExactUnramifiedSiegelDensity

/-! ## Section 5: Convergent Euler Product & Global Siegel Densities (`siegel_densities_of_hermitian_form`) -/

section GlobalSiegelEulerProduct

/-- Real quadratic character value `χ(n).re ∈ {-1, 0, 1}`. -/
def quadChiR {D : ℕ} [NeZero D] (χ : DirichletCharacter ℂ D) (n : ℕ) : ℝ :=
  (χ n).re

/-- Single-index Euler factor at prime `p` and index `j`:
`(1 - p^{-j})` when `Even j`, and `(1 - χ(p).re * p^{-j})` when `Odd j`. -/
def globalEulerSingleFactor {D : ℕ} [NeZero D] (χ : DirichletCharacter ℂ D)
    (j : ℕ) (p : Nat.Primes) : ℝ :=
  if Even j then (1 - (p : ℝ) ^ (-(j : ℤ))) else (1 - quadChiR χ p * (p : ℝ) ^ (-(j : ℤ)))

/-- Local Euler factor of the global Siegel–Weil product at prime `p` for ranks `n < m`. -/
def globalEulerTerm {D : ℕ} [NeZero D] (χ : DirichletCharacter ℂ D)
    (m n : ℕ) (p : Nat.Primes) : ℝ :=
  ∏ j ∈ Finset.Icc (m - n + 1) m, globalEulerSingleFactor χ j p

/-- Global inverse L-value product `∏_{j = m - n + 1}^m hermLVal χ j⁻¹` matching
`Stage11RallisMassFiber.hermLVal`. -/
def siegelProductLValue {D : ℕ} [NeZero D] (χ : DirichletCharacter ℂ D)
    (m n : ℕ) : ℝ :=
  ∏ j ∈ Finset.Icc (m - n + 1) m, (Stage11RallisMassFiber.hermLVal χ j)⁻¹

/-- At any unramified prime `p` with splitting `sp` matching `χ p` (`sp.chi = (χ p).re`),
`globalEulerTerm χ m n p = local_density_euler_factor p sp.chi m n`. -/
theorem unramified_eulerTerm_eq_local_density {D : ℕ} [NeZero D] (χ : DirichletCharacter ℂ D)
    (m n : ℕ) (p : Nat.Primes) (sp : PlaceSplitting) (hsp : sp.chi = quadChiR χ p) :
    globalEulerTerm χ m n p = local_density_euler_factor (p : ℝ) sp.chi m n := by
  unfold globalEulerTerm local_density_euler_factor globalEulerSingleFactor
  refine Finset.prod_congr rfl fun j _ => ?_
  by_cases hj : Even j
  · have hpow : sp.chi ^ j = 1 := by
      rcases hj with ⟨k, rfl⟩
      rw [← two_mul, pow_mul, sp.chi_sq, one_pow]
    simp [hj, hpow]
  · have hodd : Odd j := Nat.not_even_iff_odd.mp hj
    have hpow : sp.chi ^ j = sp.chi := by
      rcases hodd with ⟨k, rfl⟩
      rw [pow_add, pow_mul, sp.chi_sq, one_pow, one_mul, pow_one]
    rw [hpow, hsp]
    simp [hj]

/-- Bridge to concrete `LocalHermLattice.ofPrime` at unramified primes `p`. -/
theorem unramified_local_density_eq_globalEulerTerm {D : ℕ} [NeZero D]
    (χ : DirichletCharacter ℂ D) (p : Nat.Primes) (sp : PlaceSplitting)
    (hsp : sp.chi = quadChiR χ p) (m n : ℕ) (hm : 1 ≤ m) (hnm : n ≤ m) :
    LocalRepresentationDensity (LocalHermLattice.ofPrime p p.prop sp m hm)
      (1 : Matrix (Fin n) (Fin n) (LocalHermBase.ofPrime p p.prop sp).S) =
      globalEulerTerm χ m n p := by
  rw [siegel_density_unramified_at_prime p p.prop sp m n hm hnm,
    unramified_eulerTerm_eq_local_density χ m n p sp hsp]

private lemma hasProd_real_of_complex_inv {f : Nat.Primes → ℂ} {L : ℂ}
    (hf : HasProd (fun p => (f p)⁻¹) L) (hL : L ≠ 0)
    {g : Nat.Primes → ℝ} (hg : ∀ p, ‖f p‖ = g p) :
    HasProd g ‖L‖⁻¹ := by
  have h1 : HasProd f L⁻¹ := by
    simpa only [inv_inv] using hf.inv₀ hL
  have h2 : HasProd (fun p => ‖f p‖) ‖L⁻¹‖ := by
    change Filter.Tendsto (fun s : Finset Nat.Primes => ∏ p ∈ s, ‖f p‖) Filter.atTop (nhds ‖L⁻¹‖)
    simp_rw [← norm_prod]
    exact h1.norm
  simp only [hg, norm_inv] at h2
  exact h2

/-- Single-index Euler product convergence for `j ≥ 2` and quadratic character `χ`. -/
theorem single_factor_hasProd {D : ℕ} [NeZero D] (χ : DirichletCharacter ℂ D)
    (hquad : ∀ n : ℕ, χ n = 0 ∨ χ n = 1 ∨ χ n = -1) {j : ℕ} (hj : 2 ≤ j) :
    HasProd (globalEulerSingleFactor χ j) (Stage11RallisMassFiber.hermLVal χ j)⁻¹ := by
  have hre : 1 < ((j : ℂ)).re := by
    simp only [Complex.natCast_re]
    exact_mod_cast (by omega : 1 < j)
  by_cases hev : Even j
  · have hζ := riemannZeta_eulerProduct_hasProd hre
    have hζ0 : riemannZeta (j : ℂ) ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hre
    have hf0 : ∀ p : Nat.Primes, (1 - (p : ℂ) ^ (-(j : ℂ))) ≠ 0 := fun p => by
      have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast p.prop.two_le
      have hsub : (1 : ℝ) - (p : ℝ) ^ (-(j : ℤ)) > 0 := by
        have hqj : (2 : ℝ) ≤ (p : ℝ) ^ j := by
          calc (2 : ℝ) ≤ (p : ℝ) ^ 1 := by simpa using hp2
            _ ≤ (p : ℝ) ^ j := pow_le_pow_right₀ (by linarith) (by omega)
        rw [_root_.zpow_neg, zpow_natCast, inv_eq_one_div]
        have : (1 : ℝ) / (p : ℝ) ^ j ≤ 1 / 2 :=
          one_div_le_one_div_of_le (by norm_num) hqj
        linarith
      have hcast : ((1 - (p : ℝ) ^ (-(j : ℤ)) : ℝ) : ℂ) = 1 - (p : ℂ) ^ (-(j : ℂ)) := by
        push_cast
        congr 1
        rw [← Complex.cpow_intCast]; simp
      rw [← hcast]
      exact Complex.ofReal_ne_zero.mpr hsub.ne'
    have hnorm : ∀ p : Nat.Primes,
        ‖1 - (p : ℂ) ^ (-(j : ℂ))‖ = globalEulerSingleFactor χ j p := fun p => by
      have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast p.prop.two_le
      have hsub : 0 ≤ (1 : ℝ) - (p : ℝ) ^ (-(j : ℤ)) := by
        have hqj : (2 : ℝ) ≤ (p : ℝ) ^ j := by
          calc (2 : ℝ) ≤ (p : ℝ) ^ 1 := by simpa using hp2
            _ ≤ (p : ℝ) ^ j := pow_le_pow_right₀ (by linarith) (by omega)
        rw [_root_.zpow_neg, zpow_natCast, inv_eq_one_div]
        have : (1 : ℝ) / (p : ℝ) ^ j ≤ 1 / 2 :=
          one_div_le_one_div_of_le (by norm_num) hqj
        linarith
      have hcast : ((1 - (p : ℝ) ^ (-(j : ℤ)) : ℝ) : ℂ) = 1 - (p : ℂ) ^ (-(j : ℂ)) := by
        push_cast; congr 1; rw [← Complex.cpow_intCast]; simp
      rw [← hcast, Complex.norm_real, Real.norm_of_nonneg hsub]
      simp [globalEulerSingleFactor, hev]
    simpa [Stage11RallisMassFiber.hermLVal, hev] using
      hasProd_real_of_complex_inv hζ hζ0 hnorm
  · have hL : HasProd (fun p : Nat.Primes => (1 - χ p * (p : ℂ) ^ (-(j : ℂ)))⁻¹)
        (χ.LFunction (j : ℂ)) := by
      rw [DirichletCharacter.LFunction_eq_LSeries χ hre]
      exact DirichletCharacter.LSeries_eulerProduct_hasProd χ hre
    have hL0 : χ.LFunction (j : ℂ) ≠ 0 := by
      have hb := (Stage11RallisMassFiber.hermLVal_bounds_ge_two χ hj).1
      have hpos : 0 < Stage11RallisMassFiber.hermLVal χ j := by linarith
      simpa [Stage11RallisMassFiber.hermLVal, hev, norm_pos_iff] using hpos
    have hχ_real : ∀ n : ℕ, ((quadChiR χ n : ℝ) : ℂ) = χ n := fun n => by
      rcases hquad n with h | h | h <;> simp [quadChiR, h]
    have hnorm : ∀ p : Nat.Primes,
        ‖1 - χ p * (p : ℂ) ^ (-(j : ℂ))‖ = globalEulerSingleFactor χ j p := fun p => by
      have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast p.prop.two_le
      have hchi_le : |quadChiR χ p| ≤ 1 := by
        rcases hquad p with h | h | h <;> simp [quadChiR, h]
      have hsub : 0 ≤ (1 : ℝ) - quadChiR χ p * (p : ℝ) ^ (-(j : ℤ)) := by
        have hqj : (2 : ℝ) ≤ (p : ℝ) ^ j := by
          calc (2 : ℝ) ≤ (p : ℝ) ^ 1 := by simpa using hp2
            _ ≤ (p : ℝ) ^ j := pow_le_pow_right₀ (by linarith) (by omega)
        have h3 : (p : ℝ) ^ (-(j : ℤ)) ≤ 1 / 2 := by
          rw [_root_.zpow_neg, zpow_natCast, inv_eq_one_div]
          exact one_div_le_one_div_of_le (by norm_num) hqj
        have h1 : quadChiR χ p * (p : ℝ) ^ (-(j : ℤ)) ≤ 1 * (p : ℝ) ^ (-(j : ℤ)) :=
          mul_le_mul_of_nonneg_right (abs_le.mp hchi_le).2 (by positivity)
        linarith
      have hcast : ((1 - quadChiR χ p * (p : ℝ) ^ (-(j : ℤ)) : ℝ) : ℂ) =
          1 - χ p * (p : ℂ) ^ (-(j : ℂ)) := by
        push_cast; rw [hχ_real]
        congr 2; rw [← Complex.cpow_intCast]; simp
      rw [← hcast, Complex.norm_real, Real.norm_of_nonneg hsub]
      simp [globalEulerSingleFactor, hev]
    simpa [Stage11RallisMassFiber.hermLVal, hev] using
      hasProd_real_of_complex_inv hL hL0 hnorm

/-- **Global Siegel–Weil Convergent Euler Product Theorem** (`siegel_densities_of_hermitian_form`):
In the Siegel–Weil convergent range `n < m`, the Euler product of local Siegel densities over all
primes `p` converges (`HasProd` and `Multipliable`) to `∏_{j=m-n+1}^m (hermLVal χ j)⁻¹`, satisfies
exact equality with `LocalRepresentationDensity` at every unramified prime, and is bounded above
and below away from zero by `(4 / 7)^n ≤ · ≤ 4^n`. -/
theorem siegel_densities_of_hermitian_form {D : ℕ} [NeZero D] (χ : DirichletCharacter ℂ D)
    (hquad : ∀ n : ℕ, χ n = 0 ∨ χ n = 1 ∨ χ n = -1)
    {m n : ℕ} (hnm : n < m) :
    HasProd (globalEulerTerm χ m n) (siegelProductLValue χ m n) ∧
      Multipliable (globalEulerTerm χ m n) ∧
      ((4 / 7 : ℝ) ^ n ≤ siegelProductLValue χ m n ∧ siegelProductLValue χ m n ≤ (4 : ℝ) ^ n) := by
  have hj2 : ∀ j ∈ Finset.Icc (m - n + 1) m, 2 ≤ j := fun j hj => by
    have h1 := (Finset.mem_Icc.mp hj).1
    omega
  have hhas : HasProd (globalEulerTerm χ m n) (siegelProductLValue χ m n) := by
    unfold HasProd globalEulerTerm siegelProductLValue
    simp_rw [Finset.prod_comm (s := _) (t := Finset.Icc (m - n + 1) m)]
    exact tendsto_finsetProd (Finset.Icc (m - n + 1) m) fun j hj =>
      single_factor_hasProd χ hquad (hj2 j hj)
  have hcard : (Finset.Icc (m - n + 1) m).card = n := by
    rw [Nat.card_Icc]; omega
  have hlo : (4 / 7 : ℝ) ^ n ≤ siegelProductLValue χ m n := by
    unfold siegelProductLValue
    calc (4 / 7 : ℝ) ^ n = ∏ _j ∈ Finset.Icc (m - n + 1) m, (4 / 7 : ℝ) := by
          rw [Finset.prod_const, hcard]
      _ ≤ ∏ j ∈ Finset.Icc (m - n + 1) m, (Stage11RallisMassFiber.hermLVal χ j)⁻¹ := by
          refine Finset.prod_le_prod (fun _ _ => by positivity) (fun j hj => ?_)
          have hb := Stage11RallisMassFiber.hermLVal_bounds_ge_two χ (hj2 j hj)
          have hpos : 0 < Stage11RallisMassFiber.hermLVal χ j := by linarith [hb.1]
          rw [show (4 / 7 : ℝ) = (7 / 4 : ℝ)⁻¹ by norm_num]
          exact inv_anti₀ hpos hb.2
  have hhi : siegelProductLValue χ m n ≤ (4 : ℝ) ^ n := by
    unfold siegelProductLValue
    calc ∏ j ∈ Finset.Icc (m - n + 1) m, (Stage11RallisMassFiber.hermLVal χ j)⁻¹
        ≤ ∏ _j ∈ Finset.Icc (m - n + 1) m, (4 : ℝ) := by
          refine Finset.prod_le_prod (fun j hj => ?_) (fun j hj => ?_)
          · have hb := Stage11RallisMassFiber.hermLVal_bounds_ge_two χ (hj2 j hj)
            exact inv_nonneg.mpr (by linarith [hb.1])
          · have hb := Stage11RallisMassFiber.hermLVal_bounds_ge_two χ (hj2 j hj)
            rw [show (4 : ℝ) = (1 / 4 : ℝ)⁻¹ by norm_num]
            exact inv_anti₀ (by norm_num) hb.1
      _ = (4 : ℝ) ^ n := by rw [Finset.prod_const, hcard]
  exact ⟨hhas, hhas.multipliable, hlo, hhi⟩

/-- Packaged Wave-2 handoff structure for `SiegelEisenstein`, `TamagawaVolumeMass`, and
`FormalDegreeDiscrete`. -/
structure SiegelDensityGlobalPackage {D : ℕ} [NeZero D] (χ : DirichletCharacter ℂ D)
    (m n : ℕ) where
  rank_lt : n < m
  eulerValue : ℝ
  hasProd_euler : HasProd (globalEulerTerm χ m n) eulerValue
  multipliable_euler : Multipliable (globalEulerTerm χ m n)
  lower_bound : (4 / 7 : ℝ) ^ n ≤ eulerValue
  upper_bound : eulerValue ≤ (4 : ℝ) ^ n
  unramified_local_match : ∀ (p : Nat.Primes) (sp : PlaceSplitting),
    sp.chi = quadChiR χ p →
    LocalRepresentationDensity (LocalHermLattice.ofPrime p p.prop sp m (by omega))
      (1 : Matrix (Fin n) (Fin n) (LocalHermBase.ofPrime p p.prop sp).S) =
      globalEulerTerm χ m n p

/-- Canonical unconditional constructor of `SiegelDensityGlobalPackage` in the Siegel–Weil range `n < m`. -/
def mkSiegelDensityGlobalPackage {D : ℕ} [NeZero D] (χ : DirichletCharacter ℂ D)
    (hquad : ∀ a : ℕ, χ a = 0 ∨ χ a = 1 ∨ χ a = -1)
    {m n : ℕ} (hnm : n < m) : SiegelDensityGlobalPackage χ m n :=
  let h := siegel_densities_of_hermitian_form χ hquad hnm
  { rank_lt := hnm
    eulerValue := siegelProductLValue χ m n
    hasProd_euler := h.1
    multipliable_euler := h.2.1
    lower_bound := h.2.2.1
    upper_bound := h.2.2.2
    unramified_local_match := fun p sp hsp =>
      unramified_local_density_eq_globalEulerTerm χ p sp hsp m n (by omega) hnm.le }

end GlobalSiegelEulerProduct

end RHDirect.Stage14M1_LocalSiegelDensities
