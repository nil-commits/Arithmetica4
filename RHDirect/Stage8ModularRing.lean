import RHDirect.Stage7EisensteinSeries
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.RingTheory.AlgebraicIndependent.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.NumberTheory.ModularForms.CuspFormSubmodule
import Mathlib.NumberTheory.ModularForms.Discriminant
import Mathlib.NumberTheory.ModularForms.LevelOne.Basic
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing
import Mathlib.NumberTheory.ModularForms.QExpansion

/-!
# RHDirect.Stage8ModularRing

**EXACT GRADED-RING STRUCTURE `M_*(SL₂(ℤ)) ≃ₐ[ℂ] ℂ[E₄, E₆]`, EXACT DIMENSION FORMULAS
`dim M_k(SL₂(ℤ))` & `dim S_k(SL₂(ℤ))` FOR ALL `k : ℕ`, AND KLEIN'S MODULAR `j`-INVARIANT**
in pure Mathlib `v4.33.1`.

## Main Results (0 `sorry`, 0 custom `axiom`s, 0 assumptions)
1. **Nonvanishing of `Δ` & Exact Weight-12 Cusp-Form Shift Equivalence**:
   - `discriminant_ne_zero`: `∀ τ : UpperHalfPlane, ModularForm.discriminant τ ≠ 0`.
   - `cuspFormEquivModularFormShift`: `CuspForm SL2ZRange (k + 12) ≃ₗ[ℂ] ModularForm SL2ZRange k`
     with inverse `g ↦ Δ * g`.
   - `mem_cuspForm_iff_exists_discriminant_mul`: `f.IsCuspForm ↔ ∃ g, ∀ τ, f τ = Δ τ * g τ`.
   - `exists_four_mul_add_six_mul_eq`: Frobenius coin representation `4a + 6b = k` for all even `k ≥ 4`.
   - `modularFormSplitEquiv` & `isCompl_span_monomialE4E6_cuspFormSubmodule`:
     exact splitting `M_k(SL₂(ℤ)) = ℂ • (E₄^a E₆^b) ⊕ S_k(SL₂(ℤ))`.
2. **Elliptic Special Values of `E₄` and `E₆` at `i` and `ρ = e^{2πi/3}`**:
   - `E6_at_I : E6 UpperHalfPlane.I = 0` and `E4_at_I_ne_zero : E4 UpperHalfPlane.I ≠ 0`.
   - `E4_at_rhoPoint : E4 rhoPoint = 0` and `E6_at_rhoPoint_ne_zero : E6 rhoPoint ≠ 0`.
3. **Unconditional Monomial Basis, Graded-Ring Isomorphism `M_*(SL₂(ℤ)) ≃ₐ[ℂ] ℂ[E₄, E₆]`,
   and Exact Dimension Formulas**:
   - `span_monomialE4E6_eq_top`: `{E₄^a E₆^b | 4a + 6b = k}` spans `M_k(SL₂(ℤ))` (strong induction).
   - `linearIndependent_monomialE4E6`: `{E₄^a E₆^b | 4a + 6b = k}` is `ℂ`-linearly independent
     (direct strong induction using `E₆(i) = 0, E₄(i) ≠ 0` and `ModularForm.mul_ne_zero`).
   - `basisModularFormSL2Z`: explicit `ℂ`-basis of `ModularForm SL2ZRange k`.
   - `algebraicIndependent_E4_E6` & `modularFormGradedRingEquiv`:
     `MvPolynomial (Fin 2) ℂ ≃ₐ[ℂ] DirectSum ℤ (ModularForm SL2ZRange)`.
   - `finrank_modularForm_SL2Z` & `finrank_cuspForm_SL2Z`: exact closed-form dimensions for all `k : ℕ`.
4. **Klein's Modular `j`-Invariant (`j(τ) = E₄(τ)³ / Δ(τ) = 1728 E₄(τ)³ / (E₄(τ)³ - E₆(τ)²)`):**
   - `jInvariant_SL2Z_invariant`: exact `SL₂(ℤ)`-invariance `j(γ • τ) = j(τ)`.
   - `jInvariant_at_I : jInvariant UpperHalfPlane.I = 1728` and `jInvariant_at_rhoPoint : jInvariant rhoPoint = 0`.
   - Exact leading `q`-expansion coefficients of `E₄³`, `E₆²`, `Δ` (`q - 24 q² + 252 q³ + ...`),
     and `q · j(τ)` (`1 + 744 q + 196884 q² + ...`).
   - `jInvariant_laurent_asymptotic`: `j(τ) - (q⁻¹ + 744 + 196884 q) = O(q²)` as `Im(τ) → ∞`.
-/

open Complex Real Filter Module Submodule Finset
open RHDirect.Stage5ThetaModular RHDirect.Stage7EisensteinSeries
open scoped BigOperators UpperHalfPlane ModularForm Topology Manifold

namespace RHDirect.Stage8ModularRing

noncomputable section

/-! ## Section 1: Nonvanishing of `Δ`, Exact Weight-12 Shift Equivalence, & Weight-`k` Splitting -/

section DiscriminantShiftAndSplitting

/-- Nonvanishing of the modular discriminant `Δ(τ) ≠ 0` everywhere on the upper half-plane. -/
theorem discriminant_ne_zero (τ : UpperHalfPlane) :
    ModularForm.discriminant τ ≠ 0 :=
  ModularForm.discriminant_ne_zero τ

/-- Linear equivalence induced by weight equality `k₁ = k₂` via `ModularForm.mcast`. -/
def mcastLinearEquiv {k₁ k₂ : ℤ} (h : k₁ = k₂) :
    ModularForm SL2ZRange k₁ ≃ₗ[ℂ] ModularForm SL2ZRange k₂ where
  toFun f := ModularForm.mcast h f rfl
  invFun g := ModularForm.mcast h.symm g rfl
  map_add' f g := by ext τ; simp [ModularForm.mcast_apply]
  map_smul' c f := by ext τ; simp [ModularForm.mcast_apply]
  left_inv f := by ext τ; simp [ModularForm.mcast_apply]
  right_inv g := by ext τ; simp [ModularForm.mcast_apply]

@[simp]
theorem mcastLinearEquiv_apply {k₁ k₂ : ℤ} (h : k₁ = k₂)
    (f : ModularForm SL2ZRange k₁) (τ : UpperHalfPlane) :
    mcastLinearEquiv h f τ = f τ :=
  ModularForm.mcast_apply h f rfl τ

/-- **Exact Weight-12 Cusp-Form Shift Linear Equivalence**:
`S_{k+12}(SL₂(ℤ)) ≃ₗ[ℂ] M_k(SL₂(ℤ))`, sending `f ↦ f / Δ` with inverse `g ↦ Δ * g`. -/
def cuspFormEquivModularFormShift (k : ℤ) :
    CuspForm SL2ZRange (k + 12) ≃ₗ[ℂ] ModularForm SL2ZRange k :=
  (CuspForm.discriminantEquiv (k := k + 12)).trans
    (mcastLinearEquiv (add_sub_cancel_right k 12))

@[simp]
theorem cuspFormEquivModularFormShift_apply (k : ℤ)
    (f : CuspForm SL2ZRange (k + 12)) (τ : UpperHalfPlane) :
    cuspFormEquivModularFormShift k f τ = f τ / ModularForm.discriminant τ := by
  simp [cuspFormEquivModularFormShift, CuspForm.discriminantEquiv_apply]

@[simp]
theorem cuspFormEquivModularFormShift_symm_apply (k : ℤ)
    (g : ModularForm SL2ZRange k) (τ : UpperHalfPlane) :
    (cuspFormEquivModularFormShift k).symm g τ = ModularForm.discriminant τ * g τ := by
  have h := ModularForm.discriminant_mul_discriminantEquiv_apply
    ((cuspFormEquivModularFormShift k).symm g) τ
  have hright := (cuspFormEquivModularFormShift k).apply_symm_apply g
  have hval := congrArg (fun u : ModularForm SL2ZRange k => u τ) hright
  rw [cuspFormEquivModularFormShift_apply] at hval
  have hΔ : ModularForm.discriminant τ ≠ 0 := discriminant_ne_zero τ
  calc ((cuspFormEquivModularFormShift k).symm g) τ
      = ModularForm.discriminant τ *
          (((cuspFormEquivModularFormShift k).symm g) τ / ModularForm.discriminant τ) := by
          field_simp [hΔ]
    _ = ModularForm.discriminant τ * g τ := by rw [hval]

/-- **Exact Divisibility Characterization of Level-1 Cusp Forms**:
`f ∈ S_{k+12}(SL₂(ℤ))` if and only if `f = Δ · g` for some `g ∈ M_k(SL₂(ℤ))`. -/
theorem mem_cuspForm_iff_exists_discriminant_mul {k : ℤ}
    (f : ModularForm SL2ZRange (k + 12)) :
    f.IsCuspForm ↔ ∃ g : ModularForm SL2ZRange k,
      ∀ τ : UpperHalfPlane, f τ = ModularForm.discriminant τ * g τ := by
  constructor
  · intro hf
    have h0 : PowerSeries.coeff 0 (UpperHalfPlane.qExpansion 1 (f : UpperHalfPlane → ℂ)) = 0 :=
      (ModularForm.isCuspForm_iff_coeffZero_eq_zero f).mp hf
    refine ⟨cuspFormEquivModularFormShift k (f.toCuspForm h0), fun τ => ?_⟩
    rw [cuspFormEquivModularFormShift_apply, ModularForm.toCuspForm_apply]
    have hΔ : ModularForm.discriminant τ ≠ 0 := discriminant_ne_zero τ
    field_simp [hΔ]
  · rintro ⟨g, hg⟩
    let hcusp : CuspForm SL2ZRange (k + 12) := (cuspFormEquivModularFormShift k).symm g
    have heq : f = CuspForm.toModularFormₗ hcusp := by
      ext τ
      rw [CuspForm.toModularFormₗ_apply, cuspFormEquivModularFormShift_symm_apply, hg τ]
    rw [heq]
    exact ModularForm.CuspForm.isCuspForm_toModularFormₗ hcusp

/-- **Frobenius Coin Theorem for `{4, 6}`**: every even `k ≥ 4` can be written as `4a + 6b = k`
with `a, b ∈ ℕ`. -/
theorem exists_four_mul_add_six_mul_eq {k : ℕ} (hk4 : 4 ≤ k) (heven : Even k) :
    ∃ a b : ℕ, 4 * a + 6 * b = k := by
  rcases heven with ⟨m, rfl⟩
  by_cases hm : Even m
  · rcases hm with ⟨r, rfl⟩
    exact ⟨r, 0, by omega⟩
  · have hm_odd : Odd m := Nat.not_even_iff_odd.mp hm
    rcases hm_odd with ⟨r, rfl⟩
    have hr : 1 ≤ r := by omega
    exact ⟨r - 1, 1, by omega⟩

/-- Evaluation lemma for `ModularForm.pow`. -/
lemma modularForm_pow_apply {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.HasDetPlusMinusOne] {k : ℤ}
    (f : ModularForm Γ k) (n : ℕ) (τ : UpperHalfPlane) :
    (f.pow n) τ = f τ ^ n := by
  induction n with
  | zero =>
    change (ModularForm.mcast (by simp : (0 : ℤ) = (0 : ℕ) * k) (1 : ModularForm Γ 0) rfl) τ = 1
    rw [ModularForm.mcast_apply]
    rfl
  | succ n ih =>
    have hpow : (f.pow (n + 1) : UpperHalfPlane → ℂ) =
        (ModularForm.mcast (by push_cast; ring : (n : ℤ) * k + k = ((n + 1 : ℕ) : ℤ) * k)
          ((f.pow n).mul f) rfl : UpperHalfPlane → ℂ) := by
      have h1 := ModularForm.gnpow_eq_pow f (n + 1)
      have h2 := ModularForm.gnpow_eq_pow f n
      rfl
    change (f.pow n) τ * f τ = f τ ^ (n + 1)
    rw [ih, pow_succ]

/-- Canonical weight-`(4a + 6b)` monomial `E₄^a · E₆^b` as a Mathlib level-1 modular form. -/
def monomialE4E6 (a b : ℕ) : ModularForm SL2ZRange ((4 * a + 6 * b : ℕ) : ℤ) :=
  ModularForm.mcast (by push_cast; ring : (a : ℤ) * 4 + (b : ℤ) * 6 = ((4 * a + 6 * b : ℕ) : ℤ))
    ((ModularForm.E₄.pow a).mul (ModularForm.E₆.pow b)) rfl

@[simp]
theorem monomialE4E6_apply (a b : ℕ) (τ : UpperHalfPlane) :
    monomialE4E6 a b τ = ModularForm.E₄ τ ^ a * ModularForm.E₆ τ ^ b := by
  unfold monomialE4E6
  rw [ModularForm.mcast_apply]
  change (ModularForm.E₄.pow a) τ * (ModularForm.E₆.pow b) τ = _
  rw [modularForm_pow_apply, modularForm_pow_apply]

/-- Monomial `E₄^a · E₆^b` cast to weight `k` given `4a + 6b = k`. -/
def monomialE4E6At (k a b : ℕ) (h : 4 * a + 6 * b = k) : ModularForm SL2ZRange (k : ℤ) :=
  ModularForm.mcast (by exact_mod_cast h : ((4 * a + 6 * b : ℕ) : ℤ) = (k : ℤ))
    (monomialE4E6 a b) rfl

@[simp]
theorem monomialE4E6At_apply (k a b : ℕ) (h : 4 * a + 6 * b = k) (τ : UpperHalfPlane) :
    monomialE4E6At k a b h τ = ModularForm.E₄ τ ^ a * ModularForm.E₆ τ ^ b := by
  unfold monomialE4E6At
  rw [ModularForm.mcast_apply, monomialE4E6_apply]

/-- Every monomial `E₄^a · E₆^b` has constant term `1` in its `q`-expansion at `i∞`. -/
theorem monomialE4E6_qExpansion_coeff_zero (a b : ℕ) :
    PowerSeries.coeff 0
      (UpperHalfPlane.qExpansion 1 (monomialE4E6 a b : UpperHalfPlane → ℂ)) = 1 := by
  unfold monomialE4E6
  rw [ModularForm.qExpansion_mcast,
    ModularForm.qExpansion_mul zero_lt_one one_mem_strictPeriods_SL,
    ModularForm.qExpansion_pow zero_lt_one one_mem_strictPeriods_SL,
    ModularForm.qExpansion_pow zero_lt_one one_mem_strictPeriods_SL,
    PowerSeries.coeff_zero_eq_constantCoeff, map_mul, map_pow, map_pow,
    ← PowerSeries.coeff_zero_eq_constantCoeff,
    EisensteinSeries.E_qExpansion_coeff_zero (k := 4) (by norm_num) (by decide),
    EisensteinSeries.E_qExpansion_coeff_zero (k := 6) (by norm_num) (by decide)]
  simp

theorem monomialE4E6At_qExpansion_coeff_zero (k a b : ℕ) (h : 4 * a + 6 * b = k) :
    PowerSeries.coeff 0
      (UpperHalfPlane.qExpansion 1 (monomialE4E6At k a b h : UpperHalfPlane → ℂ)) = 1 := by
  unfold monomialE4E6At
  rw [ModularForm.qExpansion_mcast]
  exact monomialE4E6_qExpansion_coeff_zero a b

/-- **Exact Weight-`k` Splitting** (`M_k(SL₂(ℤ)) ≃ₗ[ℂ] ℂ × S_k(SL₂(ℤ))`):
for every even `k ≥ 4` and any `(a, b)` with `4a + 6b = k`, every `f ∈ M_k(SL₂(ℤ))` decomposes
uniquely as `c • (E₄^a E₆^b) + h` with `c ∈ ℂ` and `h ∈ S_k(SL₂(ℤ))`. -/
def modularFormSplitEquiv {k : ℕ} (a b : ℕ) (hab : 4 * a + 6 * b = k) :
    ModularForm SL2ZRange (k : ℤ) ≃ₗ[ℂ] ℂ × CuspForm SL2ZRange (k : ℤ) where
  toFun f :=
    (PowerSeries.coeff 0 (UpperHalfPlane.qExpansion 1 (f : UpperHalfPlane → ℂ)),
      (f - (PowerSeries.coeff 0 (UpperHalfPlane.qExpansion 1 (f : UpperHalfPlane → ℂ))) •
          monomialE4E6At k a b hab).toCuspForm
        ((ModularForm.isCuspForm_iff_coeffZero_eq_zero _).mp
          (ModularForm.sub_smul_isCuspForm f (monomialE4E6At k a b hab)
            (monomialE4E6At_qExpansion_coeff_zero k a b hab))))
  invFun p := p.1 • monomialE4E6At k a b hab + CuspForm.toModularFormₗ p.2
  map_add' f g := by
    have hqadd : PowerSeries.coeff 0
        (UpperHalfPlane.qExpansion 1 ((f + g : ModularForm SL2ZRange (k : ℤ)) : UpperHalfPlane → ℂ)) =
        PowerSeries.coeff 0 (UpperHalfPlane.qExpansion 1 (f : UpperHalfPlane → ℂ)) +
        PowerSeries.coeff 0 (UpperHalfPlane.qExpansion 1 (g : UpperHalfPlane → ℂ)) := by
      rw [FunLike.coe_add, ModularForm.qExpansion_add zero_lt_one one_mem_strictPeriods_SL,
        map_add]
    ext
    · exact hqadd
    · rename_i τ
      simp only [Prod.snd_add, add_apply, ModularForm.toCuspForm_apply,
        sub_apply, smul_apply, smul_eq_mul, hqadd]
      ring
  map_smul' c f := by
    have hqsmul : PowerSeries.coeff 0
        (UpperHalfPlane.qExpansion 1 ((c • f : ModularForm SL2ZRange (k : ℤ)) : UpperHalfPlane → ℂ)) =
        c * PowerSeries.coeff 0 (UpperHalfPlane.qExpansion 1 (f : UpperHalfPlane → ℂ)) := by
      rw [FunLike.coe_smul, ModularForm.qExpansion_smul zero_lt_one one_mem_strictPeriods_SL,
        map_smul, smul_eq_mul]
    ext
    · exact hqsmul
    · rename_i τ
      simp only [RingHom.id_apply, Prod.smul_snd, smul_apply, ModularForm.toCuspForm_apply,
        sub_apply, smul_eq_mul, hqsmul]
      ring
  left_inv f := by
    ext τ
    simp only [add_apply, smul_apply, smul_eq_mul,
      CuspForm.toModularFormₗ_apply, ModularForm.toCuspForm_apply, sub_apply]
    ring
  right_inv p := by
    have hq0 : PowerSeries.coeff 0
        (UpperHalfPlane.qExpansion 1
          ((p.1 • monomialE4E6At k a b hab + CuspForm.toModularFormₗ p.2 :
            ModularForm SL2ZRange (k : ℤ)) : UpperHalfPlane → ℂ)) = p.1 := by
      rw [FunLike.coe_add, ModularForm.qExpansion_add zero_lt_one one_mem_strictPeriods_SL,
        FunLike.coe_smul, ModularForm.qExpansion_smul zero_lt_one one_mem_strictPeriods_SL,
        map_add, map_smul, smul_eq_mul, monomialE4E6At_qExpansion_coeff_zero, mul_one,
        (ModularForm.isCuspForm_iff_coeffZero_eq_zero _).mp
          (ModularForm.CuspForm.isCuspForm_toModularFormₗ p.2),
        add_zero]
    ext
    · exact hq0
    · rename_i τ
      simp only [ModularForm.toCuspForm_apply, sub_apply, add_apply,
        smul_apply, smul_eq_mul, CuspForm.toModularFormₗ_apply, hq0]
      ring

/-- Direct-sum submodule complement: `M_k(SL₂(ℤ)) = (ℂ • E₄^a E₆^b) ⊕ S_k(SL₂(ℤ))`. -/
theorem isCompl_span_monomialE4E6_cuspFormSubmodule {k : ℕ} (a b : ℕ) (hab : 4 * a + 6 * b = k) :
    IsCompl (Submodule.span ℂ {monomialE4E6At k a b hab})
      (ModularForm.cuspFormSubmodule SL2ZRange (k : ℤ)) := by
  constructor
  · rw [Submodule.disjoint_def]
    intro f hf1 hf2
    rw [Submodule.mem_span_singleton] at hf1
    rcases hf1 with ⟨c, rfl⟩
    rw [ModularForm.mem_cuspFormSubmodule_iff, ModularForm.isCuspForm_iff_coeffZero_eq_zero] at hf2
    rw [FunLike.coe_smul, ModularForm.qExpansion_smul zero_lt_one one_mem_strictPeriods_SL,
      map_smul, smul_eq_mul, monomialE4E6At_qExpansion_coeff_zero, mul_one] at hf2
    rw [hf2, zero_smul]
  · rw [codisjoint_iff, eq_top_iff]
    intro f _
    set c : ℂ := PowerSeries.coeff 0 (UpperHalfPlane.qExpansion 1 (f : UpperHalfPlane → ℂ))
    have h1 : c • monomialE4E6At k a b hab ∈ Submodule.span ℂ {monomialE4E6At k a b hab} :=
      Submodule.smul_mem _ c (Submodule.subset_span (Set.mem_singleton _))
    have h2 : f - c • monomialE4E6At k a b hab ∈
        ModularForm.cuspFormSubmodule SL2ZRange (k : ℤ) := by
      rw [ModularForm.mem_cuspFormSubmodule_iff]
      exact ModularForm.sub_smul_isCuspForm f (monomialE4E6At k a b hab)
        (monomialE4E6At_qExpansion_coeff_zero k a b hab)
    have hsum : c • monomialE4E6At k a b hab + (f - c • monomialE4E6At k a b hab) = f :=
      add_sub_cancel _ _
    rw [← hsum]
    exact Submodule.add_mem_sup h1 h2

end DiscriminantShiftAndSplitting

/-! ## Section 2: Elliptic Special Values of `E₄` and `E₆` at `i` and `ρ = e^{2πi/3}` -/

section EllipticSpecialValues

/-- The elliptic point `ρ = e^{2πi/3} = -1/2 + i√3/2` in the upper half-plane. -/
def rhoPoint : UpperHalfPlane :=
  ⟨Complex.exp (2 * (Real.pi : ℂ) * Complex.I / 3), by
    have harg : (2 * (Real.pi : ℂ) * Complex.I / 3) = ((2 * Real.pi / 3 : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [harg, Complex.exp_mul_I, Complex.add_im, ← Complex.ofReal_cos, Complex.ofReal_im,
      Complex.mul_im, ← Complex.ofReal_sin, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    simp only [mul_zero, mul_one, zero_add]
    have hsin : Real.sin (2 * Real.pi / 3) = Real.sqrt 3 / 2 := by
      rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring, Real.sin_pi_sub, Real.sin_pi_div_three]
    rw [hsin]
    positivity⟩

/-- Explicit algebraic form of `ρ = e^{2πi/3} = -1/2 + (√3 / 2) i`. -/
theorem coe_rhoPoint :
    (rhoPoint : ℂ) = -(1 / 2 : ℂ) + ((Real.sqrt 3 / 2 : ℝ) : ℂ) * Complex.I := by
  change Complex.exp (2 * (Real.pi : ℂ) * Complex.I / 3) = _
  have harg : (2 * (Real.pi : ℂ) * Complex.I / 3) = ((2 * Real.pi / 3 : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [harg, Complex.exp_mul_I]
  have hcos : Real.cos (2 * Real.pi / 3) = -(1 / 2 : ℝ) := by
    rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring, Real.cos_pi_sub, Real.cos_pi_div_three]
  have hsin : Real.sin (2 * Real.pi / 3) = Real.sqrt 3 / 2 := by
    rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring, Real.sin_pi_sub, Real.sin_pi_div_three]
  rw [← Complex.ofReal_cos, ← Complex.ofReal_sin, hcos, hsin]
  push_cast
  ring

/-- Minimal polynomial identity `ρ² + ρ + 1 = 0`. -/
theorem rhoPoint_sq_add_add_one : (rhoPoint : ℂ) ^ 2 + (rhoPoint : ℂ) + 1 = 0 := by
  rw [coe_rhoPoint]
  have hsq : ((Real.sqrt 3 : ℝ) : ℂ) ^ 2 = 3 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num
  push_cast
  calc (-(1 / 2 : ℂ) + (Real.sqrt 3 : ℂ) / 2 * Complex.I) ^ 2 +
        (-(1 / 2 : ℂ) + (Real.sqrt 3 : ℂ) / 2 * Complex.I) + 1
      = (3 / 4 : ℂ) + ((Real.sqrt 3 : ℂ) ^ 2 / 4) * Complex.I ^ 2 := by ring
    _ = (3 / 4 : ℂ) + (3 / 4 : ℂ) * (-1) := by rw [hsq, Complex.I_sq]
    _ = 0 := by norm_num

/-- Cube-root-of-unity identity `ρ³ = 1`. -/
theorem rhoPoint_cube : (rhoPoint : ℂ) ^ 3 = 1 := by
  have h := rhoPoint_sq_add_add_one
  linear_combination ((rhoPoint : ℂ) - 1) * h

/-- `S` fixes `i`: `S • i = i`. -/
theorem S_smul_I : ModularGroup.S • UpperHalfPlane.I = UpperHalfPlane.I := by
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.modular_S_smul]
  simp

/-- `S * T` fixes `ρ`: `S • (T • ρ) = ρ`. -/
theorem ST_smul_rhoPoint :
    ModularGroup.S • (ModularGroup.T • rhoPoint) = rhoPoint := by
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.modular_S_smul]
  change (-((ModularGroup.T • rhoPoint : UpperHalfPlane) : ℂ))⁻¹ = (rhoPoint : ℂ)
  have hT : ((ModularGroup.T • rhoPoint : UpperHalfPlane) : ℂ) = (rhoPoint : ℂ) + 1 := by
    simpa [zpow_one] using ModularGroup.coe_T_zpow_smul_eq rhoPoint (n := 1)
  rw [hT]
  rw [inv_eq_iff_eq_inv]
  apply eq_inv_of_mul_eq_one_left
  have hsq := rhoPoint_sq_add_add_one
  linear_combination -hsq

/-- **Special Value `E₆(i) = 0`** (from `S • i = i` and weight-6 modularity `E₆(S • i) = i⁶ E₆(i) = -E₆(i)`). -/
theorem E6_at_I : E6 UpperHalfPlane.I = 0 := by
  have h := E6_S_smul UpperHalfPlane.I
  rw [S_smul_I] at h
  have hI6 : ((UpperHalfPlane.I : ℂ) ^ 6) = -1 := by
    change Complex.I ^ 6 = -1
    calc Complex.I ^ 6 = (Complex.I ^ 2) ^ 3 := by ring
      _ = (-1) ^ 3 := by rw [Complex.I_sq]
      _ = -1 := by norm_num
  rw [hI6] at h
  linear_combination (1 / 2 : ℂ) * h

theorem modularForm_E6_at_I : ModularForm.E₆ UpperHalfPlane.I = 0 := by
  rw [← E6_eq_modularForm_E6]
  exact E6_at_I

/-- **Nonvanishing `E₄(i) ≠ 0`** (from `Δ(i) = E₄(i)³ / 1728 ≠ 0`). -/
theorem E4_at_I_ne_zero : E4 UpperHalfPlane.I ≠ 0 := by
  intro h0
  have hΔ := discriminant_eq_E4_cube_sub_E6_sq UpperHalfPlane.I
  rw [h0, E6_at_I] at hΔ
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sub_self, zero_div] at hΔ
  exact discriminant_ne_zero UpperHalfPlane.I hΔ

theorem modularForm_E4_at_I_ne_zero : ModularForm.E₄ UpperHalfPlane.I ≠ 0 := by
  rw [← E4_eq_modularForm_E4]
  exact E4_at_I_ne_zero

/-- **Special Value `E₄(ρ) = 0`** (from `S • (T • ρ) = ρ` and weight-4 modularity). -/
theorem E4_at_rhoPoint : E4 rhoPoint = 0 := by
  have hS := E4_S_smul (ModularGroup.T • rhoPoint)
  rw [ST_smul_rhoPoint, E4_T_smul] at hS
  have hT : ((ModularGroup.T • rhoPoint : UpperHalfPlane) : ℂ) = (rhoPoint : ℂ) + 1 := by
    simpa [zpow_one] using ModularGroup.coe_T_zpow_smul_eq rhoPoint (n := 1)
  rw [hT] at hS
  have hpow4 : ((rhoPoint : ℂ) + 1) ^ 4 = (rhoPoint : ℂ) ^ 2 := by
    have hsq := rhoPoint_sq_add_add_one
    have hcube := rhoPoint_cube
    have h1 : (rhoPoint : ℂ) + 1 = -((rhoPoint : ℂ) ^ 2) := by linear_combination hsq
    rw [h1]
    calc (-((rhoPoint : ℂ) ^ 2)) ^ 4 = ((rhoPoint : ℂ) ^ 3) ^ 2 * (rhoPoint : ℂ) ^ 2 := by ring
      _ = 1 ^ 2 * (rhoPoint : ℂ) ^ 2 := by rw [hcube]
      _ = (rhoPoint : ℂ) ^ 2 := by ring
  rw [hpow4] at hS
  have hne : (rhoPoint : ℂ) ^ 2 ≠ 1 := by
    intro h1
    have hsq := rhoPoint_sq_add_add_one
    have hr : (rhoPoint : ℂ) = -2 := by linear_combination hsq - h1
    have him := congrArg Complex.im hr
    simp only [Complex.neg_im] at him
    exact (ne_of_gt rhoPoint.im_pos) (by simpa using him)
  have hfac : (1 - (rhoPoint : ℂ) ^ 2) * E4 rhoPoint = 0 := by
    linear_combination hS
  have h1ne : 1 - (rhoPoint : ℂ) ^ 2 ≠ 0 := sub_ne_zero.mpr hne.symm
  exact (mul_eq_zero.mp hfac).resolve_left h1ne

theorem modularForm_E4_at_rhoPoint : ModularForm.E₄ rhoPoint = 0 := by
  rw [← E4_eq_modularForm_E4]
  exact E4_at_rhoPoint

/-- **Nonvanishing `E₆(ρ) ≠ 0`** (from `Δ(ρ) = -E₆(ρ)² / 1728 ≠ 0`). -/
theorem E6_at_rhoPoint_ne_zero : E6 rhoPoint ≠ 0 := by
  intro h0
  have hΔ := discriminant_eq_E4_cube_sub_E6_sq rhoPoint
  rw [E4_at_rhoPoint, h0] at hΔ
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sub_self, zero_div] at hΔ
  exact discriminant_ne_zero rhoPoint hΔ

theorem modularForm_E6_at_rhoPoint_ne_zero : ModularForm.E₆ rhoPoint ≠ 0 := by
  rw [← E6_eq_modularForm_E6]
  exact E6_at_rhoPoint_ne_zero

end EllipticSpecialValues

/-! ## Section 3: Unconditional Basis, Graded-Ring Isomorphism `M_*(SL₂(ℤ)) ≃ₐ[ℂ] ℂ[E₄, E₆]`, & Dimension Formulas -/

section StructureTheoremAndDimension

/-- Finset of all exponent pairs `(a, b) ∈ ℕ × ℕ` with `4a + 6b = k`. -/
def weightMonomialPairs (k : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (k + 1) ×ˢ Finset.range (k + 1)).filter (fun p => 4 * p.1 + 6 * p.2 = k)

lemma mem_weightMonomialPairs {k : ℕ} {p : ℕ × ℕ} :
    p ∈ weightMonomialPairs k ↔ 4 * p.1 + 6 * p.2 = k := by
  unfold weightMonomialPairs
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨⟨by omega, by omega⟩, h⟩

/-- Index type of weight-`k` monomials `{ (a, b) ∈ ℕ × ℕ | 4a + 6b = k }`. -/
abbrev WeightMonomialIndex (k : ℕ) : Type :=
  {p : ℕ × ℕ // 4 * p.1 + 6 * p.2 = k}

instance fintypeWeightMonomialIndex (k : ℕ) : Fintype (WeightMonomialIndex k) :=
  Fintype.ofFinset (weightMonomialPairs k) (fun _ => mem_weightMonomialPairs)

lemma card_weightMonomialIndex_eq_card_pairs (k : ℕ) :
    Fintype.card (WeightMonomialIndex k) = (weightMonomialPairs k).card := by
  exact Fintype.card_ofFinset (weightMonomialPairs k) (fun _ => mem_weightMonomialPairs)

/-- Weight-12 recurrence for the number of monomials `{4a + 6b = k}`:
for every even `k`, `|weightMonomialPairs (k + 12)| = |weightMonomialPairs k| + 1`. -/
lemma card_weightMonomialPairs_add_twelve {k : ℕ} (heven : Even k) :
    (weightMonomialPairs (k + 12)).card = (weightMonomialPairs k).card + 1 := by
  let S_hi : Finset (ℕ × ℕ) := (weightMonomialPairs (k + 12)).filter (fun p => 2 ≤ p.2)
  let S_lo : Finset (ℕ × ℕ) := (weightMonomialPairs (k + 12)).filter (fun p => ¬ (2 ≤ p.2))
  have hpart : (weightMonomialPairs (k + 12)).card = S_hi.card + S_lo.card := by
    rw [← Finset.card_union_of_disjoint
      (Finset.disjoint_filter.mpr fun _ _ h1 h2 => h2 h1),
      Finset.filter_union_filter_not_eq]
  have hhi : S_hi.card = (weightMonomialPairs k).card := by
    refine Finset.card_bij (fun p _ => (p.1, p.2 - 2)) ?_ ?_ ?_
    · intro p hp
      simp only [S_hi, Finset.mem_filter, mem_weightMonomialPairs] at hp
      rw [mem_weightMonomialPairs]
      omega
    · intro p₁ hp₁ p₂ hp₂ heq
      simp only [S_hi, Finset.mem_filter, mem_weightMonomialPairs] at hp₁ hp₂
      simp only [Prod.mk.injEq] at heq
      ext <;> omega
    · intro q hq
      rw [mem_weightMonomialPairs] at hq
      refine ⟨(q.1, q.2 + 2), ?_, by simp⟩
      simp only [S_hi, Finset.mem_filter, mem_weightMonomialPairs]
      exact ⟨by omega, by omega⟩
  have hlo : S_lo.card = 1 := by
    rcases heven with ⟨m, rfl⟩
    by_cases hm : Even m
    · rcases hm with ⟨r, rfl⟩
      have hset : S_lo = {(r + 3, 0)} := by
        ext ⟨a, b⟩
        simp only [S_lo, Finset.mem_filter, mem_weightMonomialPairs, Finset.mem_singleton,
          Prod.mk.injEq]
        omega
      rw [hset, Finset.card_singleton]
    · rcases Nat.not_even_iff_odd.mp hm with ⟨r, rfl⟩
      have hset : S_lo = {(r + 2, 1)} := by
        ext ⟨a, b⟩
        simp only [S_lo, Finset.mem_filter, mem_weightMonomialPairs, Finset.mem_singleton,
          Prod.mk.injEq]
        omega
      rw [hset, Finset.card_singleton]
  omega

/-- **Exact Combinatorial Count of Weight-`k` Monomials `{E₄^a E₆^b | 4a + 6b = k}`**:
`card { (a, b) | 4a + 6b = k } = if Odd k ∨ k = 2 then 0 else if k % 12 = 2 then k / 12 else k / 12 + 1`. -/
theorem card_weightMonomialPairs (k : ℕ) :
    (weightMonomialPairs k).card =
      if Odd k ∨ k = 2 then 0 else if k % 12 = 2 then k / 12 else k / 12 + 1 := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    by_cases hodd : Odd k
    · have hempty : weightMonomialPairs k = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro p hp
        rw [mem_weightMonomialPairs] at hp
        rcases hodd with ⟨m, hm⟩
        omega
      rw [hempty, Finset.card_empty, if_pos (Or.inl hodd)]
    · have heven : Even k := Nat.not_odd_iff_even.mp hodd
      by_cases hk12 : k < 12
      · interval_cases k <;> try (exfalso; exact hodd (by decide))
        · decide
        · decide
        · decide
        · decide
        · decide
        · decide
      · have hge : 12 ≤ k := Nat.le_of_not_lt hk12
        set k' := k - 12
        have hk_eq : k = k' + 12 := by omega
        have heven' : Even k' := by
          rcases heven with ⟨m, hm⟩
          exact ⟨m - 6, by omega⟩
        have hodd' : ¬ Odd k' := Nat.not_odd_iff_even.mpr heven'
        have hstep : (weightMonomialPairs k).card = (weightMonomialPairs k').card + 1 := by
          rw [hk_eq]
          exact card_weightMonomialPairs_add_twelve heven'
        have hih := ih k' (by omega)
        rw [hstep, hih]
        have hnotk : ¬ (Odd k ∨ k = 2) := by
          rintro (h | h)
          · exact hodd h
          · omega
        rw [if_neg hnotk]
        by_cases hk'2 : k' = 2
        · have hk14 : k = 14 := by omega
          rw [if_pos (Or.inr hk'2), hk14]
          norm_num
        · have hnotk' : ¬ (Odd k' ∨ k' = 2) := by
            rintro (h | h)
            · exact hodd' h
            · exact hk'2 h
          rw [if_neg hnotk']
          have hmod : k % 12 = k' % 12 := by omega
          have hdiv : k / 12 = k' / 12 + 1 := by omega
          rw [hmod, hdiv]
          split_ifs <;> omega

/-- The family of weight-`k` monomials `p ↦ E₄^{p.1} E₆^{p.2}` in `ModularForm SL2ZRange k`. -/
def monomialFamily (k : ℕ) : WeightMonomialIndex k → ModularForm SL2ZRange (k : ℤ) :=
  fun p => monomialE4E6At k p.1.1 p.1.2 p.2

/-- **UNCONDITIONAL SPANNING THEOREM**: for every `k : ℕ`, the monomials
`{E₄^a · E₆^b | 4a + 6b = k}` span `ModularForm SL2ZRange k` over `ℂ`. -/
theorem span_monomialE4E6_eq_top (k : ℕ) :
    Submodule.span ℂ (Set.range (monomialFamily k)) = ⊤ := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    rw [eq_top_iff]
    intro f _
    by_cases hodd : Odd k
    · have hf0 : f = 0 := ModularForm.levelOne_odd_weight_eq_zero (by exact_mod_cast hodd) f
      rw [hf0]
      exact Submodule.zero_mem _
    · have heven : Even k := Nat.not_odd_iff_even.mp hodd
      by_cases hk0 : k = 0
      · subst hk0
        rcases ModularFormClass.levelOne_weight_zero_const f with ⟨c, hc⟩
        have hf_eq : f = c • monomialFamily 0 ⟨(0, 0), rfl⟩ := by
          ext τ
          have hτ := congrFun hc τ
          simp only [Function.const_apply] at hτ
          rw [hτ, smul_apply, smul_eq_mul]
          have h1 : monomialFamily 0 ⟨(0, 0), rfl⟩ τ = 1 := by
            dsimp only [monomialFamily]
            rw [monomialE4E6At_apply]
            simp
          rw [h1, mul_one]
        rw [hf_eq]
        exact Submodule.smul_mem _ c (Submodule.subset_span (Set.mem_range_self _))
      · by_cases hk2 : k = 2
        · subst hk2
          have hrank : Module.rank ℂ (ModularForm SL2ZRange 2) = 0 :=
            ModularForm.levelOne_weight_two_rank_zero
          have : Subsingleton (ModularForm SL2ZRange 2) := rank_zero_iff.mp hrank
          rw [Subsingleton.elim f 0]
          exact Submodule.zero_mem _
        · have hk4 : 4 ≤ k := by
            rcases heven with ⟨m, hm⟩
            omega
          obtain ⟨a₀, b₀, hab₀⟩ := exists_four_mul_add_six_mul_eq hk4 heven
          let p₀ : WeightMonomialIndex k := ⟨(a₀, b₀), hab₀⟩
          set c : ℂ := PowerSeries.coeff 0 (UpperHalfPlane.qExpansion 1 (f : UpperHalfPlane → ℂ))
          set h : ModularForm SL2ZRange (k : ℤ) := f - c • monomialFamily k p₀
          have hh_cusp : h.IsCuspForm :=
            ModularForm.sub_smul_isCuspForm f (monomialFamily k p₀)
              (monomialE4E6At_qExpansion_coeff_zero k a₀ b₀ hab₀)
          have hdecomp : f = c • monomialFamily k p₀ + h := by simp [h]
          rw [hdecomp]
          refine Submodule.add_mem _
            (Submodule.smul_mem _ c (Submodule.subset_span (Set.mem_range_self p₀))) ?_
          by_cases hk12 : k < 12
          · have h0 : PowerSeries.coeff 0
                (UpperHalfPlane.qExpansion 1 (h : UpperHalfPlane → ℂ)) = 0 :=
              (ModularForm.isCuspForm_iff_coeffZero_eq_zero h).mp hh_cusp
            have hh0 : h = 0 :=
              modularForm_SL2Z_eq_zero_of_coeff_zero_eq_zero (by exact_mod_cast hk12) h h0
            rw [hh0]
            exact Submodule.zero_mem _
          · set k' : ℕ := k - 12
            have hk_eq : (k : ℤ) = (k' : ℤ) + 12 := by omega
            have hcast : (mcastLinearEquiv hk_eq h).IsCuspForm := by
              rw [ModularForm.isCuspForm_iff_coeffZero_eq_zero] at hh_cusp ⊢
              unfold mcastLinearEquiv
              simpa [ModularForm.qExpansion_mcast] using hh_cusp
            have h0' : PowerSeries.coeff 0
                (UpperHalfPlane.qExpansion 1
                  ((mcastLinearEquiv hk_eq h : ModularForm SL2ZRange ((k' : ℤ) + 12)) :
                    UpperHalfPlane → ℂ)) = 0 :=
              (ModularForm.isCuspForm_iff_coeffZero_eq_zero _).mp hcast
            set g : ModularForm SL2ZRange (k' : ℤ) :=
              cuspFormEquivModularFormShift (k' : ℤ) ((mcastLinearEquiv hk_eq h).toCuspForm h0')
            have hg_mul : ∀ τ : UpperHalfPlane, h τ = ModularForm.discriminant τ * g τ := by
              intro τ
              have hval := cuspFormEquivModularFormShift_apply (k' : ℤ)
                ((mcastLinearEquiv hk_eq h).toCuspForm h0') τ
              rw [ModularForm.toCuspForm_apply, mcastLinearEquiv_apply] at hval
              have hΔ := discriminant_ne_zero τ
              calc h τ = ModularForm.discriminant τ * (h τ / ModularForm.discriminant τ) := by
                    field_simp [hΔ]
                _ = ModularForm.discriminant τ * g τ := by rw [← hval]
            have hg_mem : g ∈ Submodule.span ℂ (Set.range (monomialFamily k')) := by
              rw [ih k' (by omega)]
              trivial
            -- Multiplication by `Δ = (E₄³ - E₆²) / 1728` as a `ℂ`-linear map `M_{k'} → M_k`.
            let mulΔ : ModularForm SL2ZRange (k' : ℤ) →ₗ[ℂ] ModularForm SL2ZRange (k : ℤ) :=
              (mcastLinearEquiv hk_eq.symm).toLinearMap.comp
                (CuspForm.toModularFormₗ.comp (cuspFormEquivModularFormShift (k' : ℤ)).symm.toLinearMap)
            have hmulΔ_apply : ∀ u : ModularForm SL2ZRange (k' : ℤ), ∀ τ : UpperHalfPlane,
                mulΔ u τ = ModularForm.discriminant τ * u τ := by
              intro u τ
              simp [mulΔ]
            have hh_eq_mulΔ : h = mulΔ g := by
              ext τ
              rw [hg_mul τ, hmulΔ_apply g τ]
            rw [hh_eq_mulΔ]
            -- Show `mulΔ` maps every `monomialFamily k' q` into `span (range (monomialFamily k))`.
            have hmap_span : Submodule.map mulΔ (Submodule.span ℂ (Set.range (monomialFamily k'))) ≤
                Submodule.span ℂ (Set.range (monomialFamily k)) := by
              rw [Submodule.map_span, Submodule.span_le]
              rintro _ ⟨_, ⟨q, rfl⟩, rfl⟩
              let q₁ : WeightMonomialIndex k := ⟨(q.1.1 + 3, q.1.2), by have := q.2; omega⟩
              let q₂ : WeightMonomialIndex k := ⟨(q.1.1, q.1.2 + 2), by have := q.2; omega⟩
              have hcomb : mulΔ (monomialFamily k' q) =
                  ((1 / 1728 : ℂ) • monomialFamily k q₁) - ((1 / 1728 : ℂ) • monomialFamily k q₂) := by
                ext τ
                rw [hmulΔ_apply, sub_apply, smul_apply, smul_apply, smul_eq_mul, smul_eq_mul,
                  ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq]
                simp only [monomialFamily, monomialE4E6At_apply, q₁, q₂]
                ring
              rw [hcomb]
              exact Submodule.sub_mem _
                (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self q₁)))
                (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self q₂)))
            exact hmap_span (Submodule.mem_map_of_mem hg_mem)

/-- **UNCONDITIONAL LINEAR INDEPENDENCE OF `{E₄^a · E₆^b | 4a + 6b = k}`**:
proved directly by strong induction on `k` using `E₆(i) = 0, E₄(i) ≠ 0` and `ModularForm.mul_ne_zero`! -/
theorem linearIndependent_monomialE4E6 (k : ℕ) :
    LinearIndependent ℂ (monomialFamily k) := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    rw [Fintype.linearIndependent_iff]
    intro c hc
    -- Step 1: Any term with `b = 0` vanishes by evaluating at `i` (since `E₆(i) = 0, E₄(i) ≠ 0`).
    have hb0 : ∀ p : WeightMonomialIndex k, p.1.2 = 0 → c p = 0 := by
      intro p hp
      have heval := congrArg (fun f : ModularForm SL2ZRange (k : ℤ) => f UpperHalfPlane.I) hc
      rw [zero_apply] at heval
      have hsum_eval :
          (∑ q : WeightMonomialIndex k, c q • monomialFamily k q) UpperHalfPlane.I =
          ∑ q : WeightMonomialIndex k, c q * (monomialFamily k q UpperHalfPlane.I) := by
        have hlin : ∀ s : Finset (WeightMonomialIndex k),
            (∑ q ∈ s, c q • monomialFamily k q) UpperHalfPlane.I =
            ∑ q ∈ s, c q * (monomialFamily k q UpperHalfPlane.I) := by
          intro s
          induction s using Finset.induction_on with
          | empty => simp
          | insert a s ha ihs =>
            rw [Finset.sum_insert ha, Finset.sum_insert ha, add_apply,
              smul_apply, smul_eq_mul, ihs]
        exact hlin Finset.univ
      rw [hsum_eval] at heval
      have hsingle : (∑ q : WeightMonomialIndex k, c q * monomialFamily k q UpperHalfPlane.I) =
          c p * (ModularForm.E₄ UpperHalfPlane.I ^ p.1.1) := by
        rw [Finset.sum_eq_single p]
        · simp [monomialFamily, hp]
        · intro q _ hqp
          have hq2 : q.1.2 ≠ 0 := by
            intro hq0
            apply hqp
            apply Subtype.ext
            ext
            · have hp' := p.2; have hq' := q.2; omega
            · omega
          simp [monomialFamily, modularForm_E6_at_I, zero_pow hq2]
        · intro hp_abs; exact absurd (Finset.mem_univ p) hp_abs
      rw [hsingle] at heval
      have hne : ModularForm.E₄ UpperHalfPlane.I ^ p.1.1 ≠ 0 :=
        pow_ne_zero p.1.1 modularForm_E4_at_I_ne_zero
      exact (mul_eq_zero.mp heval).resolve_right hne
    -- Step 2: Handle `b ≥ 1` by factoring out `E₆` and invoking IH at `k - 6 < k`.
    intro p
    by_cases hp0 : p.1.2 = 0
    · exact hb0 p hp0
    · have hk6 : 6 ≤ k := by have := p.2; omega
      set k' : ℕ := k - 6
      let lift : WeightMonomialIndex k' → WeightMonomialIndex k :=
        fun q => ⟨(q.1.1, q.1.2 + 1), by have := q.2; omega⟩
      let c' : WeightMonomialIndex k' → ℂ := fun q => c (lift q)
      set g : ModularForm SL2ZRange (k' : ℤ) := ∑ q : WeightMonomialIndex k', c' q • monomialFamily k' q
      have hE6g_zero : ModularForm.E₆.mul g = 0 := by
        ext τ
        change ModularForm.E₆ τ * g τ = 0
        have hsum_apply : ∀ {m : ℕ} (d : WeightMonomialIndex m → ℂ) (s : Finset (WeightMonomialIndex m)),
            (∑ q ∈ s, d q • monomialFamily m q) τ =
            ∑ q ∈ s, d q * (monomialFamily m q τ) := by
          intro m d s
          induction s using Finset.induction_on with
          | empty => simp
          | insert a s ha ihs =>
            rw [Finset.sum_insert ha, Finset.sum_insert ha, add_apply,
              smul_apply, smul_eq_mul, ihs]
        have hgτ : g τ = ∑ q : WeightMonomialIndex k', c' q * monomialFamily k' q τ :=
          hsum_apply c' Finset.univ
        have hcτ : (∑ r : WeightMonomialIndex k, c r * monomialFamily k r τ) = 0 := by
          have h1 := congrArg (fun f : ModularForm SL2ZRange (k : ℤ) => f τ) hc
          rw [hsum_apply c Finset.univ, zero_apply] at h1
          exact h1
        rw [hgτ, Finset.mul_sum]
        have hmatch : (∑ q : WeightMonomialIndex k', ModularForm.E₆ τ * (c' q * monomialFamily k' q τ)) =
            ∑ r : WeightMonomialIndex k, c r * monomialFamily k r τ := by
          symm
          rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun r : WeightMonomialIndex k => r.1.2 ≠ 0)]
          have hzero_part :
              (∑ r ∈ Finset.univ.filter (fun r : WeightMonomialIndex k => ¬ r.1.2 ≠ 0),
                c r * monomialFamily k r τ) = 0 := by
            refine Finset.sum_eq_zero fun r hr => ?_
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hr
            rw [hb0 r hr, zero_mul]
          rw [hzero_part, add_zero]
          refine Finset.sum_bij (fun r hr =>
              ⟨(r.1.1, r.1.2 - 1), by
                simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr
                have := r.2; omega⟩)
            (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
          · intro r₁ hr₁ r₂ hr₂ heq
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr₁ hr₂
            simp only [Subtype.mk.injEq, Prod.mk.injEq] at heq
            apply Subtype.ext; ext <;> omega
          · intro q _
            refine ⟨lift q, ?_, ?_⟩
            · simp [lift]
            · apply Subtype.ext; ext <;> simp [lift]
          · intro r hr
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr
            have hlift_eq : lift ⟨(r.1.1, r.1.2 - 1), by have := r.2; omega⟩ = r := by
              apply Subtype.ext; ext
              · rfl
              · exact Nat.sub_add_cancel (Nat.pos_of_ne_zero hr)
            dsimp only [c']
            rw [hlift_eq]
            simp only [monomialFamily, monomialE4E6At_apply]
            have hpow : ModularForm.E₆ τ ^ r.1.2 = ModularForm.E₆ τ * ModularForm.E₆ τ ^ (r.1.2 - 1) := by
              conv_lhs => rw [← Nat.sub_add_cancel (Nat.pos_of_ne_zero hr), pow_succ']
            rw [hpow]
            ring
        rw [hmatch, hcτ]
      have hE6_ne : (ModularForm.E₆ : ModularForm SL2ZRange 6) ≠ 0 := by
        intro h0
        have hval := congrArg (fun f : ModularForm SL2ZRange 6 => f rhoPoint) h0
        exact modularForm_E6_at_rhoPoint_ne_zero hval
      have hg_zero : g = 0 := by
        by_contra hgne
        exact ModularForm.mul_ne_zero ⟨1, one_mem_strictPeriods_SL, zero_lt_one⟩ hE6_ne hgne hE6g_zero
      have hc'_zero := (Fintype.linearIndependent_iff.mp (ih k' (by omega))) c' hg_zero
      let q : WeightMonomialIndex k' := ⟨(p.1.1, p.1.2 - 1), by have := p.2; omega⟩
      have hp_eq : lift q = p := by
        apply Subtype.ext; ext
        · rfl
        · exact Nat.sub_add_cancel (Nat.pos_of_ne_zero hp0)
      simpa [c', hp_eq] using hc'_zero q

/-- **EXPLICIT `ℂ`-BASIS OF `M_k(SL₂(ℤ))`** indexed by `{(a, b) ∈ ℕ × ℕ | 4a + 6b = k}`:
`p ↦ E₄^{p.1} E₆^{p.2}`. -/
def basisModularFormSL2Z (k : ℕ) :
    Module.Basis (WeightMonomialIndex k) ℂ (ModularForm SL2ZRange (k : ℤ)) :=
  Module.Basis.mk (linearIndependent_monomialE4E6 k) (by rw [span_monomialE4E6_eq_top k])

@[simp]
theorem basisModularFormSL2Z_apply (k : ℕ) (p : WeightMonomialIndex k) :
    basisModularFormSL2Z k p = monomialE4E6At k p.1.1 p.1.2 p.2 := by
  simp [basisModularFormSL2Z, monomialFamily]

/-- **EXACT DIMENSION FORMULA FOR `M_k(SL₂(ℤ))` FOR ALL `k : ℕ`**:
$$\dim_{\mathbb{C}} M_k(\mathrm{SL}_2(\mathbb{Z})) =
  \begin{cases} 0 & \text{if } k \text{ is odd or } k = 2, \\
  \lfloor k/12 \rfloor & \text{if } k \equiv 2 \pmod{12}, \\
  \lfloor k/12 \rfloor + 1 & \text{otherwise.} \end{cases}$$ -/
theorem finrank_modularForm_SL2Z (k : ℕ) :
    Module.finrank ℂ (ModularForm SL2ZRange (k : ℤ)) =
      if Odd k ∨ k = 2 then 0 else if k % 12 = 2 then k / 12 else k / 12 + 1 := by
  rw [Module.finrank_eq_card_basis (basisModularFormSL2Z k),
    card_weightMonomialIndex_eq_card_pairs k, card_weightMonomialPairs k]

/-- **EXACT DIMENSION FORMULA FOR `S_k(SL₂(ℤ))` FOR ALL `k : ℕ`**:
$$\dim_{\mathbb{C}} S_k(\mathrm{SL}_2(\mathbb{Z})) =
  \begin{cases} 0 & \text{if } k \text{ is odd or } k < 12 \text{ or } k = 14, \\
  \lfloor k/12 \rfloor - 1 & \text{if } k \equiv 2 \pmod{12}, \\
  \lfloor k/12 \rfloor & \text{otherwise.} \end{cases}$$ -/
theorem finrank_cuspForm_SL2Z (k : ℕ) :
    Module.finrank ℂ (CuspForm SL2ZRange (k : ℤ)) =
      if Odd k ∨ k < 12 ∨ k = 14 then 0 else if k % 12 = 2 then k / 12 - 1 else k / 12 := by
  by_cases hk12 : k < 12
  · have hsub : Subsingleton (CuspForm SL2ZRange (k : ℤ)) :=
      ⟨fun f g => (cuspForm_SL2Z_eq_zero_of_weight_lt_twelve (by exact_mod_cast hk12) f).trans
        (cuspForm_SL2Z_eq_zero_of_weight_lt_twelve (by exact_mod_cast hk12) g).symm⟩
    rw [Module.finrank_zero_of_subsingleton]
    rw [if_pos (Or.inr (Or.inl hk12))]
  · set k' : ℕ := k - 12
    have hk_eq : (k : ℤ) = (k' : ℤ) + 12 := by omega
    let eqCusp : CuspForm SL2ZRange (k : ℤ) ≃ₗ[ℂ] CuspForm SL2ZRange ((k' : ℤ) + 12) :=
      { toFun := fun f =>
          let f' := mcastLinearEquiv hk_eq (CuspForm.toModularFormₗ f)
          f'.toCuspForm (by
            rw [← ModularForm.isCuspForm_iff_coeffZero_eq_zero]
            have hc := ModularForm.CuspForm.isCuspForm_toModularFormₗ f
            rw [ModularForm.isCuspForm_iff_coeffZero_eq_zero] at hc ⊢
            simpa [f', mcastLinearEquiv, ModularForm.qExpansion_mcast] using hc)
        invFun := fun g =>
          let g' := mcastLinearEquiv hk_eq.symm (CuspForm.toModularFormₗ g)
          g'.toCuspForm (by
            rw [← ModularForm.isCuspForm_iff_coeffZero_eq_zero]
            have hc := ModularForm.CuspForm.isCuspForm_toModularFormₗ g
            rw [ModularForm.isCuspForm_iff_coeffZero_eq_zero] at hc ⊢
            simpa [g', mcastLinearEquiv, ModularForm.qExpansion_mcast] using hc)
        map_add' := fun f₁ f₂ => by ext τ; simp
        map_smul' := fun c f => by ext τ; simp
        left_inv := fun f => by ext τ; simp
        right_inv := fun g => by ext τ; simp }
    have hfin := LinearEquiv.finrank_eq (eqCusp.trans (cuspFormEquivModularFormShift (k' : ℤ)))
    rw [hfin, finrank_modularForm_SL2Z k']
    have hodd_iff : Odd k' ↔ Odd k := by
      constructor
      · rintro ⟨m, hm⟩; exact ⟨m + 6, by omega⟩
      · rintro ⟨m, hm⟩; exact ⟨m - 6, by omega⟩
    by_cases hodd : Odd k
    · have hodd' : Odd k' := hodd_iff.mpr hodd
      rw [if_pos (Or.inl hodd'), if_pos (Or.inl hodd)]
    · have hodd' : ¬ Odd k' := fun h => hodd (hodd_iff.mp h)
      by_cases hk14 : k = 14
      · have hk'2 : k' = 2 := by omega
        rw [if_pos (Or.inr hk'2), if_pos (Or.inr (Or.inr hk14))]
      · have hnotk' : ¬ (Odd k' ∨ k' = 2) := by
          rintro (h | h)
          · exact hodd' h
          · omega
        have hnotk : ¬ (Odd k ∨ k < 12 ∨ k = 14) := by
          rintro (h | h | h)
          · exact hodd h
          · exact hk12 h
          · exact hk14 h
        rw [if_neg hnotk', if_neg hnotk]
        have hmod : k % 12 = k' % 12 := by omega
        have hdiv : k / 12 = k' / 12 + 1 := by omega
        rw [hmod, hdiv]
        split_ifs <;> omega

/-- Explicit small-weight dimensions of `M_k(SL₂(ℤ))` and `S_k(SL₂(ℤ))`. -/
theorem finrank_modularForm_SL2Z_small :
    Module.finrank ℂ (ModularForm SL2ZRange 0) = 1 ∧
    Module.finrank ℂ (ModularForm SL2ZRange 2) = 0 ∧
    Module.finrank ℂ (ModularForm SL2ZRange 4) = 1 ∧
    Module.finrank ℂ (ModularForm SL2ZRange 6) = 1 ∧
    Module.finrank ℂ (ModularForm SL2ZRange 8) = 1 ∧
    Module.finrank ℂ (ModularForm SL2ZRange 10) = 1 ∧
    Module.finrank ℂ (ModularForm SL2ZRange 12) = 2 ∧
    Module.finrank ℂ (ModularForm SL2ZRange 14) = 1 ∧
    Module.finrank ℂ (ModularForm SL2ZRange 16) = 2 ∧
    Module.finrank ℂ (ModularForm SL2ZRange 24) = 3 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [Nat.odd_iff] using finrank_modularForm_SL2Z 0
  · simpa [Nat.odd_iff] using finrank_modularForm_SL2Z 2
  · simpa [Nat.odd_iff] using finrank_modularForm_SL2Z 4
  · simpa [Nat.odd_iff] using finrank_modularForm_SL2Z 6
  · simpa [Nat.odd_iff] using finrank_modularForm_SL2Z 8
  · simpa [Nat.odd_iff] using finrank_modularForm_SL2Z 10
  · simpa [Nat.odd_iff] using finrank_modularForm_SL2Z 12
  · simpa [Nat.odd_iff] using finrank_modularForm_SL2Z 14
  · simpa [Nat.odd_iff] using finrank_modularForm_SL2Z 16
  · simpa [Nat.odd_iff] using finrank_modularForm_SL2Z 24

theorem finrank_cuspForm_SL2Z_small :
    Module.finrank ℂ (CuspForm SL2ZRange 12) = 1 ∧
    Module.finrank ℂ (CuspForm SL2ZRange 14) = 0 ∧
    Module.finrank ℂ (CuspForm SL2ZRange 16) = 1 ∧
    Module.finrank ℂ (CuspForm SL2ZRange 24) = 2 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [Nat.odd_iff] using finrank_cuspForm_SL2Z 12
  · simpa [Nat.odd_iff] using finrank_cuspForm_SL2Z 14
  · simpa [Nat.odd_iff] using finrank_cuspForm_SL2Z 16
  · simpa [Nat.odd_iff] using finrank_cuspForm_SL2Z 24

/-! ### Full Graded-Ring Isomorphism `MvPolynomial (Fin 2) ℂ ≃ₐ[ℂ] DirectSum ℤ (ModularForm SL2ZRange)` -/

/-- The graded algebra generators `(E₄, E₆)` inside `DirectSum ℤ (ModularForm SL2ZRange)`. -/
def E4E6Generators : Fin 2 → DirectSum ℤ (ModularForm SL2ZRange) :=
  ![DirectSum.of (ModularForm SL2ZRange) 4 ModularForm.E₄,
    DirectSum.of (ModularForm SL2ZRange) 6 ModularForm.E₆]

/-- The canonical `ℂ`-algebra homomorphism `ℂ[X₀, X₁] → M_*(SL₂(ℤ))` sending `X₀ ↦ E₄, X₁ ↦ E₆`. -/
def modularFormEvalHom :
    MvPolynomial (Fin 2) ℂ →ₐ[ℂ] DirectSum ℤ (ModularForm SL2ZRange) :=
  MvPolynomial.aeval E4E6Generators

private lemma directSum_of_smul (k : ℤ) (c : ℂ) (f : ModularForm SL2ZRange k) :
    c • DirectSum.of (ModularForm SL2ZRange) k f =
      DirectSum.of (ModularForm SL2ZRange) k (c • f) := by
  exact (DirectSum.lof ℂ ℤ (ModularForm SL2ZRange) k).map_smul c f |>.symm

private lemma directSum_of_pow_eq {k : ℤ} (f : ModularForm SL2ZRange k) (n : ℕ) :
    (DirectSum.of (ModularForm SL2ZRange) k f) ^ n =
      DirectSum.of (ModularForm SL2ZRange) ((n : ℤ) * k) (f.pow n) := by
  induction n with
  | zero =>
    rw [pow_zero]
    have h1 : (1 : DirectSum ℤ (ModularForm SL2ZRange)) =
        DirectSum.of (ModularForm SL2ZRange) 0 1 := rfl
    rw [h1]
    have hgr : (⟨0, (1 : ModularForm SL2ZRange 0)⟩ : GradedMonoid (ModularForm SL2ZRange)) =
        ⟨((0 : ℕ) : ℤ) * k, f.pow 0⟩ := by
      apply ModularForm.gradedMonoid_eq_of_cast (by simp)
      ext τ
      rw [ModularForm.mcast_apply, modularForm_pow_apply, pow_zero]
      rfl
    exact congrArg (fun x : GradedMonoid (ModularForm SL2ZRange) =>
      DirectSum.of (ModularForm SL2ZRange) x.1 x.2) hgr
  | succ n ih =>
    rw [pow_succ, ih, DirectSum.of_mul_of]
    have hdeg : (n : ℤ) * k + k = ((n + 1 : ℕ) : ℤ) * k := by push_cast; ring
    have hgr : (⟨(n : ℤ) * k + k, GradedMonoid.GMul.mul (f.pow n) f⟩ :
        GradedMonoid (ModularForm SL2ZRange)) =
        ⟨((n + 1 : ℕ) : ℤ) * k, f.pow (n + 1)⟩ := by
      apply ModularForm.gradedMonoid_eq_of_cast hdeg
      ext τ
      rw [ModularForm.mcast_apply]
      change (f.pow n) τ * f τ = (f.pow (n + 1)) τ
      rw [modularForm_pow_apply, modularForm_pow_apply, pow_succ]
    exact congrArg (fun x : GradedMonoid (ModularForm SL2ZRange) =>
      DirectSum.of (ModularForm SL2ZRange) x.1 x.2) hgr

/-- Image of a monomial `X₀^a X₁^b` under `modularFormEvalHom` is `DirectSum.of _ (4a+6b) (monomialE4E6 a b)`. -/
lemma modularFormEvalHom_monomial_pow (a b : ℕ) :
    modularFormEvalHom (MvPolynomial.X 0 ^ a * MvPolynomial.X 1 ^ b) =
      DirectSum.of (ModularForm SL2ZRange) ((4 * a + 6 * b : ℕ) : ℤ) (monomialE4E6 a b) := by
  rw [map_mul, map_pow, map_pow]
  simp only [modularFormEvalHom, MvPolynomial.aeval_X, E4E6Generators, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  rw [directSum_of_pow_eq, directSum_of_pow_eq, DirectSum.of_mul_of]
  have hdeg : (a : ℤ) * 4 + (b : ℤ) * 6 = ((4 * a + 6 * b : ℕ) : ℤ) := by push_cast; ring
  have hgr : (⟨(a : ℤ) * 4 + (b : ℤ) * 6,
        GradedMonoid.GMul.mul (ModularForm.E₄.pow a) (ModularForm.E₆.pow b)⟩ :
      GradedMonoid (ModularForm SL2ZRange)) =
      ⟨((4 * a + 6 * b : ℕ) : ℤ), monomialE4E6 a b⟩ := by
    apply ModularForm.gradedMonoid_eq_of_cast hdeg
    ext τ
    rw [ModularForm.mcast_apply, monomialE4E6_apply]
    change (ModularForm.E₄.pow a) τ * (ModularForm.E₆.pow b) τ = _
    rw [modularForm_pow_apply, modularForm_pow_apply]
  exact congrArg (fun x : GradedMonoid (ModularForm SL2ZRange) =>
    DirectSum.of (ModularForm SL2ZRange) x.1 x.2) hgr

/-- Image of a general `MvPolynomial.monomial d c` under `modularFormEvalHom`. -/
lemma modularFormEvalHom_monomial (d : Fin 2 →₀ ℕ) (c : ℂ) :
    modularFormEvalHom (MvPolynomial.monomial d c) =
      DirectSum.of (ModularForm SL2ZRange) ((4 * d 0 + 6 * d 1 : ℕ) : ℤ)
        (c • monomialE4E6 (d 0) (d 1)) := by
  have hmon : MvPolynomial.monomial d c =
      MvPolynomial.C c * (MvPolynomial.X 0 ^ d 0 * MvPolynomial.X 1 ^ d 1) := by
    rw [MvPolynomial.monomial_eq,
      Finsupp.prod_fintype d (fun n e => MvPolynomial.X n ^ e) (fun _ => pow_zero _),
      Fin.prod_univ_two]
  rw [hmon, map_mul, modularFormEvalHom_monomial_pow]
  have hC : modularFormEvalHom (MvPolynomial.C c) =
      algebraMap ℂ (DirectSum ℤ (ModularForm SL2ZRange)) c := MvPolynomial.aeval_C _ c
  rw [hC, ← Algebra.smul_def, directSum_of_smul]

/-- **SURJECTIVITY OF `ℂ[X₀, X₁] → M_*(SL₂(ℤ))`**: `E₄` and `E₆` generate the full graded ring
of level-1 modular forms `M_*(SL₂(ℤ))`. -/
theorem modularFormEvalHom_surjective : Function.Surjective modularFormEvalHom := by
  intro x
  induction x using DirectSum.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | of k f =>
    by_cases hk : k < 0
    · have hf0 : f = 0 := by
        ext τ
        exact congrFun (ModularFormClass.levelOne_neg_weight_eq_zero hk f) τ
      exact ⟨0, by rw [map_zero, hf0, map_zero]⟩
    · lift k to ℕ using (not_lt.mp hk)
      have hdecomp : ∃ c : WeightMonomialIndex k → ℂ,
          f = ∑ p : WeightMonomialIndex k, c p • monomialFamily k p := by
        refine ⟨fun p => (basisModularFormSL2Z k).repr f p, ?_⟩
        conv_lhs => rw [← (basisModularFormSL2Z k).sum_repr f]
        refine Finset.sum_congr rfl fun p _ => by
          rw [basisModularFormSL2Z_apply]; rfl
      rcases hdecomp with ⟨c, rfl⟩
      refine ⟨∑ p : WeightMonomialIndex k,
          MvPolynomial.C (c p) * (MvPolynomial.X 0 ^ p.1.1 * MvPolynomial.X 1 ^ p.1.2), ?_⟩
      rw [map_sum, map_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [map_mul, modularFormEvalHom_monomial_pow]
      have hC : modularFormEvalHom (MvPolynomial.C (c p)) =
          algebraMap ℂ (DirectSum ℤ (ModularForm SL2ZRange)) (c p) := MvPolynomial.aeval_C _ _
      rw [hC, ← Algebra.smul_def, directSum_of_smul]
      have hp_int : ((4 * p.1.1 + 6 * p.1.2 : ℕ) : ℤ) = (k : ℤ) := by exact_mod_cast p.2
      have hgr : (⟨((4 * p.1.1 + 6 * p.1.2 : ℕ) : ℤ), c p • monomialE4E6 p.1.1 p.1.2⟩ :
          GradedMonoid (ModularForm SL2ZRange)) =
          ⟨(k : ℤ), c p • monomialFamily k p⟩ := by
        apply ModularForm.gradedMonoid_eq_of_cast hp_int
        ext τ
        rw [ModularForm.mcast_apply, smul_apply, smul_apply, monomialE4E6_apply]
        simp [monomialFamily]
      exact congrArg (fun u : GradedMonoid (ModularForm SL2ZRange) =>
        DirectSum.of (ModularForm SL2ZRange) u.1 u.2) hgr
  | add x y ihx ihy =>
    rcases ihx with ⟨px, rfl⟩
    rcases ihy with ⟨py, rfl⟩
    exact ⟨px + py, map_add _ _ _⟩

/-- **INJECTIVITY / ALGEBRAIC INDEPENDENCE OF `(E₄, E₆)` IN `M_*(SL₂(ℤ))`**:
there is no nonzero polynomial relation `P(E₄, E₆) = 0` in the graded ring `M_*(SL₂(ℤ))`. -/
theorem modularFormEvalHom_injective : Function.Injective modularFormEvalHom := by
  rw [injective_iff_map_eq_zero]
  intro P hP
  ext d
  rw [MvPolynomial.coeff_zero]
  set k : ℕ := 4 * d 0 + 6 * d 1
  -- Project `modularFormEvalHom P = 0` onto the degree-`k` graded piece!
  have hP_sum : P = ∑ e ∈ P.support, MvPolynomial.monomial e (P.coeff e) :=
    P.as_sum
  have hdeg_zero : (modularFormEvalHom P) (k : ℤ) = 0 := by rw [hP]; rfl
  rw [hP_sum, map_sum] at hdeg_zero
  have hds_sum : ∀ (s : Finset (Fin 2 →₀ ℕ)) (F : (Fin 2 →₀ ℕ) → DirectSum ℤ (ModularForm SL2ZRange)),
      (∑ e ∈ s, F e) (k : ℤ) = ∑ e ∈ s, (F e) (k : ℤ) := by
    intro s F
    induction s using Finset.induction_on with
    | empty => rfl
    | insert a s ha ihs =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, DirectSum.add_apply, ihs]
  -- Evaluate the `k`-th component of the DirectSum.
  have hcomp :
      (∑ e ∈ P.support, modularFormEvalHom (MvPolynomial.monomial e (P.coeff e))) (k : ℤ) =
      ∑ p : WeightMonomialIndex k,
        (P.coeff (Finsupp.equivFunOnFinite.symm ![p.1.1, p.1.2])) • monomialFamily k p := by
    rw [hds_sum]
    have hterm : ∀ e ∈ P.support,
        (modularFormEvalHom (MvPolynomial.monomial e (P.coeff e))) (k : ℤ) =
        if h : 4 * e 0 + 6 * e 1 = k then
          P.coeff e • monomialFamily k ⟨(e 0, e 1), h⟩
        else 0 := by
      intro e _
      rw [modularFormEvalHom_monomial]
      by_cases he : 4 * e 0 + 6 * e 1 = k
      · rw [dif_pos he]
        have he_int : ((4 * e 0 + 6 * e 1 : ℕ) : ℤ) = (k : ℤ) := by exact_mod_cast he
        have hgr : (⟨((4 * e 0 + 6 * e 1 : ℕ) : ℤ), P.coeff e • monomialE4E6 (e 0) (e 1)⟩ :
            GradedMonoid (ModularForm SL2ZRange)) =
            ⟨(k : ℤ), P.coeff e • monomialFamily k ⟨(e 0, e 1), he⟩⟩ := by
          apply ModularForm.gradedMonoid_eq_of_cast he_int
          ext τ
          rw [ModularForm.mcast_apply, smul_apply, smul_apply, monomialE4E6_apply]
          simp [monomialFamily]
        have hof := congrArg (fun u : GradedMonoid (ModularForm SL2ZRange) =>
          (DirectSum.of (ModularForm SL2ZRange) u.1 u.2) (k : ℤ)) hgr
        simpa using hof
      · rw [dif_neg he]
        exact DirectSum.of_eq_of_ne _ _ _ (by omega)
    rw [Finset.sum_congr rfl hterm,
      ← Finset.sum_filter_add_sum_filter_not P.support (fun e => 4 * e 0 + 6 * e 1 = k)]
    have hzero_rest :
        (∑ e ∈ P.support.filter (fun e => ¬ 4 * e 0 + 6 * e 1 = k),
          if h : 4 * e 0 + 6 * e 1 = k then P.coeff e • monomialFamily k ⟨(e 0, e 1), h⟩ else 0) = 0 :=
      Finset.sum_eq_zero fun e he => by
        rw [dif_neg (Finset.mem_filter.mp he).2]
    rw [hzero_rest, add_zero]
    symm
    let emb : WeightMonomialIndex k → (Fin 2 →₀ ℕ) :=
      fun p => Finsupp.equivFunOnFinite.symm ![p.1.1, p.1.2]
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun p => emb p ∈ P.support)]
    have hnot : (∑ p ∈ Finset.univ.filter (fun p => emb p ∉ P.support),
        P.coeff (emb p) • monomialFamily k p) = 0 := by
      refine Finset.sum_eq_zero fun p hp => ?_
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, MvPolynomial.mem_support_iff,
        not_not] at hp
      rw [hp, zero_smul]
    rw [hnot, add_zero]
    refine Finset.sum_bij (fun p _ => emb p) ?_ ?_ ?_ ?_
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
      refine ⟨hp, ?_⟩
      simpa [emb] using p.2
    · intro p₁ _ p₂ _ heq
      have h0 := congrFun (congrArg DFunLike.coe heq) 0
      have h1 := congrFun (congrArg DFunLike.coe heq) 1
      simp [emb] at h0 h1
      apply Subtype.ext; ext <;> assumption
    · intro e he
      simp only [Finset.mem_filter] at he
      refine ⟨⟨(e 0, e 1), he.2⟩, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        have heq : emb ⟨(e 0, e 1), he.2⟩ = e := by
          ext i; fin_cases i <;> simp [emb]
        rw [heq]
        exact he.1
      · ext i; fin_cases i <;> simp [emb]
    · intro p hp
      have hp2 : 4 * (emb p) 0 + 6 * (emb p) 1 = k := by simpa [emb] using p.2
      rw [dif_pos hp2]
      have hsub : (⟨((emb p) 0, (emb p) 1), hp2⟩ : WeightMonomialIndex k) = p := by
        apply Subtype.ext; ext <;> simp [emb]
      rw [hsub]
  rw [hcomp] at hdeg_zero
  have hcoeffs := (Fintype.linearIndependent_iff.mp (linearIndependent_monomialE4E6 k)) _ hdeg_zero
  have hd_eq : Finsupp.equivFunOnFinite.symm ![(d 0), (d 1)] = d := by
    ext i; fin_cases i <;> simp
  simpa [hd_eq] using hcoeffs ⟨(d 0, d 1), rfl⟩

/-- **Algebraic Independence of `E₄` and `E₆` over `ℂ`** in the graded ring `M_*(SL₂(ℤ))`. -/
theorem algebraicIndependent_E4_E6 :
    AlgebraicIndependent ℂ E4E6Generators :=
  modularFormEvalHom_injective

/-- **EXACT STRUCTURE THEOREM FOR LEVEL-1 MODULAR FORMS**:
$$M_*(\mathrm{SL}_2(\mathbb{Z})) \simeq_{\mathbb{C}\text{-Alg}} \mathbb{C}[E_4, E_6].$$ -/
def modularFormGradedRingEquiv :
    MvPolynomial (Fin 2) ℂ ≃ₐ[ℂ] DirectSum ℤ (ModularForm SL2ZRange) :=
  AlgEquiv.ofBijective modularFormEvalHom
    ⟨modularFormEvalHom_injective, modularFormEvalHom_surjective⟩

@[simp]
theorem modularFormGradedRingEquiv_X_zero :
    modularFormGradedRingEquiv (MvPolynomial.X 0) =
      DirectSum.of (ModularForm SL2ZRange) 4 ModularForm.E₄ := by
  simp [modularFormGradedRingEquiv, modularFormEvalHom, E4E6Generators]

@[simp]
theorem modularFormGradedRingEquiv_X_one :
    modularFormGradedRingEquiv (MvPolynomial.X 1) =
      DirectSum.of (ModularForm SL2ZRange) 6 ModularForm.E₆ := by
  simp [modularFormGradedRingEquiv, modularFormEvalHom, E4E6Generators]

end StructureTheoremAndDimension

/-! ## Section 4: Klein's Modular `j`-Invariant (`SL₂(ℤ)`-Invariance, Special Values, & Laurent Expansion) -/

section KleinJInvariant

/-- **Klein's Modular `j`-Invariant** on the upper half-plane:
$$j(\tau) = \frac{E_4(\tau)^3}{\Delta(\tau)} = \frac{1728\, E_4(\tau)^3}{E_4(\tau)^3 - E_6(\tau)^2},$$
where `Δ(τ) = ModularForm.discriminant τ = (E₄(τ)³ - E₆(τ)²) / 1728 = q ∏_{n≥1} (1 - qⁿ)²⁴`. -/
def jInvariant (τ : UpperHalfPlane) : ℂ :=
  E4 τ ^ 3 / ModularForm.discriminant τ

/-- Equivalent classical formula `j(τ) = 1728 E₄(τ)³ / (E₄(τ)³ - E₆(τ)²)`. -/
theorem jInvariant_eq_1728_mul_div (τ : UpperHalfPlane) :
    jInvariant τ = 1728 * E4 τ ^ 3 / (E4 τ ^ 3 - E6 τ ^ 2) := by
  unfold jInvariant
  rw [discriminant_eq_E4_cube_sub_E6_sq τ]
  have hne : E4 τ ^ 3 - E6 τ ^ 2 ≠ 0 := by
    intro h0
    have hΔ := discriminant_eq_E4_cube_sub_E6_sq τ
    rw [h0, zero_div] at hΔ
    exact discriminant_ne_zero τ hΔ
  field_simp [hne]

/-- **Full `SL₂(ℤ)`-Invariance of Klein's `j`-Invariant**: `j(γ • τ) = j(τ)` for every `γ ∈ SL₂(ℤ)`. -/
theorem jInvariant_SL2Z_invariant (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (τ : UpperHalfPlane) :
    jInvariant (γ • τ) = jInvariant τ := by
  unfold jInvariant
  have hE4_slash : ((ModularForm.E₄ : UpperHalfPlane → ℂ) ∣[(4 : ℤ)] γ) τ = ModularForm.E₄ τ :=
    congrFun (ModularForm.E₄.slash_action_eq' _ ⟨γ, rfl⟩) τ
  have hΔ_slash : ((CuspForm.discriminant : UpperHalfPlane → ℂ) ∣[(12 : ℤ)] γ) τ =
      CuspForm.discriminant τ :=
    congrFun (CuspForm.discriminant.slash_action_eq' _ ⟨γ, rfl⟩) τ
  rw [ModularForm.SL_slash_apply] at hE4_slash hΔ_slash
  have hE4 : E4 (γ • τ) * UpperHalfPlane.denom γ τ ^ (-(4 : ℤ)) = E4 τ := by
    simpa [E4_eq_modularForm_E4] using hE4_slash
  have hΔ : ModularForm.discriminant (γ • τ) * UpperHalfPlane.denom γ τ ^ (-(12 : ℤ)) =
      ModularForm.discriminant τ := by
    simpa [CuspForm.coe_discriminant] using hΔ_slash
  have hd : UpperHalfPlane.denom γ τ ≠ 0 := UpperHalfPlane.denom_ne_zero γ τ
  have hE4' : E4 (γ • τ) = E4 τ * UpperHalfPlane.denom γ τ ^ (4 : ℤ) := by
    calc E4 (γ • τ)
        = (E4 (γ • τ) * UpperHalfPlane.denom γ τ ^ (-(4 : ℤ))) *
            UpperHalfPlane.denom γ τ ^ (4 : ℤ) := by
            rw [mul_assoc, ← zpow_add₀ hd, neg_add_cancel, zpow_zero, mul_one]
      _ = E4 τ * UpperHalfPlane.denom γ τ ^ (4 : ℤ) := by rw [hE4]
  have hΔ' : ModularForm.discriminant (γ • τ) =
      ModularForm.discriminant τ * UpperHalfPlane.denom γ τ ^ (12 : ℤ) := by
    calc ModularForm.discriminant (γ • τ)
        = (ModularForm.discriminant (γ • τ) * UpperHalfPlane.denom γ τ ^ (-(12 : ℤ))) *
            UpperHalfPlane.denom γ τ ^ (12 : ℤ) := by
            rw [mul_assoc, ← zpow_add₀ hd, neg_add_cancel, zpow_zero, mul_one]
      _ = ModularForm.discriminant τ * UpperHalfPlane.denom γ τ ^ (12 : ℤ) := by rw [hΔ]
  rw [hE4', hΔ']
  have hd12 : UpperHalfPlane.denom γ τ ^ (12 : ℤ) ≠ 0 := zpow_ne_zero 12 hd
  have hpow : (E4 τ * UpperHalfPlane.denom γ τ ^ (4 : ℤ)) ^ 3 =
      E4 τ ^ 3 * UpperHalfPlane.denom γ τ ^ (12 : ℤ) := by
    rw [mul_pow]
    congr 1
    rw [← zpow_natCast, ← zpow_mul]
    norm_num
  rw [hpow, mul_div_mul_right _ _ hd12]

theorem jInvariant_S_smul (τ : UpperHalfPlane) :
    jInvariant (ModularGroup.S • τ) = jInvariant τ :=
  jInvariant_SL2Z_invariant ModularGroup.S τ

theorem jInvariant_T_smul (τ : UpperHalfPlane) :
    jInvariant (ModularGroup.T • τ) = jInvariant τ :=
  jInvariant_SL2Z_invariant ModularGroup.T τ

/-- **Elliptic Special Value `j(i) = 1728`** (from `E₆(i) = 0` and `E₄(i) ≠ 0`). -/
theorem jInvariant_at_I : jInvariant UpperHalfPlane.I = 1728 := by
  rw [jInvariant_eq_1728_mul_div, E6_at_I]
  have hne : E4 UpperHalfPlane.I ^ 3 ≠ 0 := pow_ne_zero 3 E4_at_I_ne_zero
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sub_zero]
  field_simp [E4_at_I_ne_zero, hne]

/-- **Elliptic Special Value `j(e^{2πi/3}) = 0`** (from `E₄(ρ) = 0`). -/
theorem jInvariant_at_rhoPoint : jInvariant rhoPoint = 0 := by
  unfold jInvariant
  rw [E4_at_rhoPoint]
  simp

/-! ### Exact Leading `q`-Expansion Coefficients of `E₄³`, `E₆²`, `Δ`, and `q · j(τ)` -/

private lemma sigma_three_eval :
    ArithmeticFunction.sigma 3 1 = 1 ∧
    ArithmeticFunction.sigma 3 2 = 9 ∧
    ArithmeticFunction.sigma 3 3 = 28 := by
  refine ⟨by decide, by decide, by decide⟩

private lemma sigma_five_eval :
    ArithmeticFunction.sigma 5 1 = 1 ∧
    ArithmeticFunction.sigma 5 2 = 33 ∧
    ArithmeticFunction.sigma 5 3 = 244 := by
  refine ⟨by decide, by decide, by decide⟩

lemma E4_qExpansion_coeffs_small :
    PowerSeries.coeff 0 (UpperHalfPlane.qExpansion 1 E4) = 1 ∧
    PowerSeries.coeff 1 (UpperHalfPlane.qExpansion 1 E4) = 240 ∧
    PowerSeries.coeff 2 (UpperHalfPlane.qExpansion 1 E4) = 2160 ∧
    PowerSeries.coeff 3 (UpperHalfPlane.qExpansion 1 E4) = 6720 := by
  have ⟨h1, h2, h3⟩ := sigma_three_eval
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [E4_qExpansion_coeff 0]; simp
  · rw [E4_qExpansion_coeff 1, if_neg (by decide), h1]; norm_num
  · rw [E4_qExpansion_coeff 2, if_neg (by decide), h2]; norm_num
  · rw [E4_qExpansion_coeff 3, if_neg (by decide), h3]; norm_num

lemma E6_qExpansion_coeffs_small :
    PowerSeries.coeff 0 (UpperHalfPlane.qExpansion 1 E6) = 1 ∧
    PowerSeries.coeff 1 (UpperHalfPlane.qExpansion 1 E6) = -504 ∧
    PowerSeries.coeff 2 (UpperHalfPlane.qExpansion 1 E6) = -16632 ∧
    PowerSeries.coeff 3 (UpperHalfPlane.qExpansion 1 E6) = -122976 := by
  have ⟨h1, h2, h3⟩ := sigma_five_eval
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [E6_qExpansion_coeff 0]; simp
  · rw [E6_qExpansion_coeff 1, if_neg (by decide), h1]; norm_num
  · rw [E6_qExpansion_coeff 2, if_neg (by decide), h2]; norm_num
  · rw [E6_qExpansion_coeff 3, if_neg (by decide), h3]; norm_num

private lemma powerSeries_coeff_mul_zero (f g : PowerSeries ℂ) :
    PowerSeries.coeff 0 (f * g) = PowerSeries.coeff 0 f * PowerSeries.coeff 0 g := by
  rw [PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => PowerSeries.coeff i f * PowerSeries.coeff j g)]
  simp

private lemma powerSeries_coeff_mul_one (f g : PowerSeries ℂ) :
    PowerSeries.coeff 1 (f * g) =
      PowerSeries.coeff 0 f * PowerSeries.coeff 1 g +
      PowerSeries.coeff 1 f * PowerSeries.coeff 0 g := by
  rw [PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => PowerSeries.coeff i f * PowerSeries.coeff j g)]
  simp [Finset.sum_range_succ]

private lemma powerSeries_coeff_mul_two (f g : PowerSeries ℂ) :
    PowerSeries.coeff 2 (f * g) =
      PowerSeries.coeff 0 f * PowerSeries.coeff 2 g +
      PowerSeries.coeff 1 f * PowerSeries.coeff 1 g +
      PowerSeries.coeff 2 f * PowerSeries.coeff 0 g := by
  rw [PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => PowerSeries.coeff i f * PowerSeries.coeff j g)]
  simp [Finset.sum_range_succ]

private lemma powerSeries_coeff_mul_three (f g : PowerSeries ℂ) :
    PowerSeries.coeff 3 (f * g) =
      PowerSeries.coeff 0 f * PowerSeries.coeff 3 g +
      PowerSeries.coeff 1 f * PowerSeries.coeff 2 g +
      PowerSeries.coeff 2 f * PowerSeries.coeff 1 g +
      PowerSeries.coeff 3 f * PowerSeries.coeff 0 g := by
  rw [PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => PowerSeries.coeff i f * PowerSeries.coeff j g)]
  simp [Finset.sum_range_succ]

/-- Exact leading `q`-expansion coefficients of `E₄³`: `1 + 720 q + 179280 q² + 16954560 q³ + ...`. -/
theorem E4_cube_qExpansion_coeffs :
    PowerSeries.coeff 0 (UpperHalfPlane.qExpansion 1 (monomialE4E6 3 0 : UpperHalfPlane → ℂ)) = 1 ∧
    PowerSeries.coeff 1 (UpperHalfPlane.qExpansion 1 (monomialE4E6 3 0 : UpperHalfPlane → ℂ)) = 720 ∧
    PowerSeries.coeff 2 (UpperHalfPlane.qExpansion 1 (monomialE4E6 3 0 : UpperHalfPlane → ℂ)) = 179280 ∧
    PowerSeries.coeff 3 (UpperHalfPlane.qExpansion 1 (monomialE4E6 3 0 : UpperHalfPlane → ℂ)) = 16954560 := by
  have hq : UpperHalfPlane.qExpansion 1 (monomialE4E6 3 0 : UpperHalfPlane → ℂ) =
      UpperHalfPlane.qExpansion 1 E4 * (UpperHalfPlane.qExpansion 1 E4 * UpperHalfPlane.qExpansion 1 E4) := by
    have hfun : (monomialE4E6 3 0 : UpperHalfPlane → ℂ) =
        (ModularForm.E₄.pow 3 : UpperHalfPlane → ℂ) := by
      funext τ
      rw [monomialE4E6_apply, modularForm_pow_apply]
      simp
    rw [hfun, ModularForm.qExpansion_pow zero_lt_one one_mem_strictPeriods_SL, ← E4_eq_coe]
    ring
  have ⟨c0, c1, c2, c3⟩ := E4_qExpansion_coeffs_small
  rw [hq]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [powerSeries_coeff_mul_zero, c0]
  · simp [powerSeries_coeff_mul_zero, powerSeries_coeff_mul_one, c0, c1]; norm_num
  · simp [powerSeries_coeff_mul_zero, powerSeries_coeff_mul_one, powerSeries_coeff_mul_two,
      c0, c1, c2]; norm_num
  · simp [powerSeries_coeff_mul_zero, powerSeries_coeff_mul_one, powerSeries_coeff_mul_two,
      powerSeries_coeff_mul_three, c0, c1, c2, c3]; norm_num

/-- Exact leading `q`-expansion coefficients of `E₆²`: `1 - 1008 q + 220752 q² + 16519104 q³ + ...`. -/
theorem E6_sq_qExpansion_coeffs :
    PowerSeries.coeff 0 (UpperHalfPlane.qExpansion 1 (monomialE4E6 0 2 : UpperHalfPlane → ℂ)) = 1 ∧
    PowerSeries.coeff 1 (UpperHalfPlane.qExpansion 1 (monomialE4E6 0 2 : UpperHalfPlane → ℂ)) = -1008 ∧
    PowerSeries.coeff 2 (UpperHalfPlane.qExpansion 1 (monomialE4E6 0 2 : UpperHalfPlane → ℂ)) = 220752 ∧
    PowerSeries.coeff 3 (UpperHalfPlane.qExpansion 1 (monomialE4E6 0 2 : UpperHalfPlane → ℂ)) = 16519104 := by
  have hq : UpperHalfPlane.qExpansion 1 (monomialE4E6 0 2 : UpperHalfPlane → ℂ) =
      UpperHalfPlane.qExpansion 1 E6 * UpperHalfPlane.qExpansion 1 E6 := by
    have hfun : (monomialE4E6 0 2 : UpperHalfPlane → ℂ) =
        (ModularForm.E₆.pow 2 : UpperHalfPlane → ℂ) := by
      funext τ
      rw [monomialE4E6_apply, modularForm_pow_apply]
      simp
    rw [hfun, ModularForm.qExpansion_pow zero_lt_one one_mem_strictPeriods_SL, ← E6_eq_coe, sq]
  have ⟨d0, d1, d2, d3⟩ := E6_qExpansion_coeffs_small
  rw [hq]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [powerSeries_coeff_mul_zero, d0]
  · simp [powerSeries_coeff_mul_one, d0, d1]; norm_num
  · simp [powerSeries_coeff_mul_two, d0, d1, d2]; norm_num
  · simp [powerSeries_coeff_mul_three, d0, d1, d2, d3]; norm_num

/-- Exact Ramanujan `τ`-function leading coefficients of `Δ(τ) = q - 24 q² + 252 q³ + ...`. -/
theorem discriminant_qExpansion_coeffs :
    PowerSeries.coeff 0 (UpperHalfPlane.qExpansion 1 ModularForm.discriminant) = 0 ∧
    PowerSeries.coeff 1 (UpperHalfPlane.qExpansion 1 ModularForm.discriminant) = 1 ∧
    PowerSeries.coeff 2 (UpperHalfPlane.qExpansion 1 ModularForm.discriminant) = -24 ∧
    PowerSeries.coeff 3 (UpperHalfPlane.qExpansion 1 ModularForm.discriminant) = 252 := by
  let diff12 : ModularForm SL2ZRange 12 := (monomialE4E6 3 0) - (monomialE4E6 0 2)
  have hΔ_eq : (ModularForm.discriminant : UpperHalfPlane → ℂ) =
      (1 / 1728 : ℂ) • (diff12 : UpperHalfPlane → ℂ) := by
    funext τ
    rw [ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq τ]
    change _ = (1 / 1728 : ℂ) * (monomialE4E6 3 0 τ - monomialE4E6 0 2 τ)
    simp only [monomialE4E6_apply, pow_zero, one_mul, mul_one]
    ring
  have hqΔ : UpperHalfPlane.qExpansion 1 ModularForm.discriminant =
      (1 / 1728 : ℂ) • (UpperHalfPlane.qExpansion 1 (monomialE4E6 3 0 : UpperHalfPlane → ℂ) -
        UpperHalfPlane.qExpansion 1 (monomialE4E6 0 2 : UpperHalfPlane → ℂ)) := by
    rw [hΔ_eq,
      ModularForm.qExpansion_smul zero_lt_one one_mem_strictPeriods_SL (1 / 1728 : ℂ) diff12,
      show (diff12 : UpperHalfPlane → ℂ) =
        (monomialE4E6 3 0 : UpperHalfPlane → ℂ) - (monomialE4E6 0 2 : UpperHalfPlane → ℂ) from
          FunLike.coe_sub _ _,
      ModularForm.qExpansion_sub zero_lt_one one_mem_strictPeriods_SL]
  have ⟨a0, a1, a2, a3⟩ := E4_cube_qExpansion_coeffs
  have ⟨b0, b1, b2, b3⟩ := E6_sq_qExpansion_coeffs
  rw [hqΔ]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [map_smul, map_sub, a0, a1, a2, a3, b0, b1, b2, b3] <;> norm_num

/-- Normalized holomorphic `q · j(τ)` function (regular at the cusp `i∞` with value `1`). -/
def qMulJInvariant (τ : UpperHalfPlane) : ℂ :=
  Function.Periodic.qParam 1 (τ : ℂ) * jInvariant τ

/-- Normalized nonvanishing cusp factor `Δ(τ) / q(τ) = ∏_{n≥1} (1 - qⁿ)²⁴`. -/
def discriminantDivQ (τ : UpperHalfPlane) : ℂ :=
  ModularForm.discriminant τ / Function.Periodic.qParam 1 (τ : ℂ)

private lemma qParam_ne_zero (τ : UpperHalfPlane) :
    Function.Periodic.qParam (1 : ℝ) (τ : ℂ) ≠ 0 := by
  unfold Function.Periodic.qParam
  exact Complex.exp_ne_zero _

private lemma norm_qParam_lt_one (τ : UpperHalfPlane) :
    ‖Function.Periodic.qParam (1 : ℝ) (τ : ℂ)‖ < 1 := by
  unfold Function.Periodic.qParam
  rw [Complex.norm_exp]
  have hre : (2 * (Real.pi : ℂ) * Complex.I * (τ : ℂ) / (1 : ℝ)).re = -2 * Real.pi * τ.im := by
    simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  rw [hre]
  exact Real.exp_lt_one_iff.mpr (by have := Real.pi_pos; have := τ.im_pos; nlinarith)

private lemma isBoundedAtImInfty_of_tendsto_one {f : UpperHalfPlane → ℂ}
    (hf : Filter.Tendsto f UpperHalfPlane.atImInfty (nhds 1)) :
    UpperHalfPlane.IsBoundedAtImInfty f := by
  rw [UpperHalfPlane.isBoundedAtImInfty_iff]
  have hev : ∀ᶠ τ : UpperHalfPlane in UpperHalfPlane.atImInfty, ‖f τ‖ ≤ 2 := by
    filter_upwards [hf.eventually (Metric.ball_mem_nhds (1 : ℂ) zero_lt_one)] with τ hτ
    rw [dist_eq_norm] at hτ
    have htri : ‖f τ‖ ≤ ‖f τ - 1‖ + ‖(1 : ℂ)‖ := by
      simpa using norm_add_le (f τ - 1) 1
    simp only [norm_one] at htri
    linarith
  rw [UpperHalfPlane.atImInfty, Filter.eventually_comap] at hev
  rcases Filter.eventually_atTop.mp hev with ⟨A, hA⟩
  exact ⟨2, A, fun τ hτ => hA τ.im hτ τ rfl⟩

/-- **Analytic Laurent Expansion of Klein's `j`-Invariant (`j(τ) = q⁻¹ + 744 + 196884 q + O(q²)`):**
as `Im(τ) → ∞`,
$$j(\tau) - \bigl(q^{-1} + 744 + 196884\, q\bigr) = O(q^2), \qquad q = e^{2\pi i \tau}.$$ -/
theorem jInvariant_laurent_asymptotic :
    (fun τ : UpperHalfPlane =>
      jInvariant τ - ((Function.Periodic.qParam (1 : ℝ) (τ : ℂ))⁻¹ + 744 +
        196884 * Function.Periodic.qParam (1 : ℝ) (τ : ℂ)))
      =O[UpperHalfPlane.atImInfty]
    (fun τ : UpperHalfPlane => Function.Periodic.qParam (1 : ℝ) (τ : ℂ) ^ 2) := by
  set fE : ℂ → ℂ := UpperHalfPlane.cuspFunction 1 (monomialE4E6 3 0 : UpperHalfPlane → ℂ)
  set fΔ : ℂ → ℂ := UpperHalfPlane.cuspFunction 1 (CuspForm.discriminant : UpperHalfPlane → ℂ)
  set F : ℂ → ℂ := fun q => q * fE q - (1 + 744 * q + 196884 * q ^ 2) * fΔ q
  set a : ℕ → ℂ := fun m => PowerSeries.coeff m (UpperHalfPlane.qExpansion 1 (monomialE4E6 3 0 : UpperHalfPlane → ℂ))
  set b : ℕ → ℂ := fun m => PowerSeries.coeff m (UpperHalfPlane.qExpansion 1 ModularForm.discriminant)
  have hE_bdd : UpperHalfPlane.IsBoundedAtImInfty (monomialE4E6 3 0 : UpperHalfPlane → ℂ) := by
    refine isBoundedAtImInfty_of_tendsto_one ?_
    have h := tendsto_E4_atImInfty.pow 3
    rw [one_pow] at h
    refine h.congr fun τ => ?_
    rw [monomialE4E6_apply, E4_eq_modularForm_E4, pow_zero, mul_one]
  have hΔ_bdd : UpperHalfPlane.IsBoundedAtImInfty (CuspForm.discriminant : UpperHalfPlane → ℂ) := by
    rw [CuspForm.coe_discriminant]
    exact ModularForm.discriminant_isZeroAtImInfty.isBoundedAtImInfty
  have hhasE : ∀ q : ℂ, ‖q‖ < 1 → HasSum (fun m => a m • q ^ m) (fE q) := fun q hq =>
    UpperHalfPlane.hasSum_qExpansion_of_norm_lt zero_lt_one
      (SlashInvariantFormClass.periodic_comp_ofComplex (monomialE4E6 3 0) one_mem_strictPeriods_SL)
      (monomialE4E6 3 0).holo' hE_bdd hq
  have hhasΔ : ∀ q : ℂ, ‖q‖ < 1 → HasSum (fun m => b m • q ^ m) (fΔ q) := fun q hq => by
    have h := UpperHalfPlane.hasSum_qExpansion_of_norm_lt zero_lt_one
      (SlashInvariantFormClass.periodic_comp_ofComplex CuspForm.discriminant one_mem_strictPeriods_SL)
      CuspForm.discriminant.holo' hΔ_bdd hq
    simpa [b, fΔ, CuspForm.coe_discriminant] using h
  let d : ℕ → ℂ := fun m =>
    (if m = 0 then 0 else a (m - 1)) -
      (b m + (if m = 0 then 0 else 744 * b (m - 1)) +
        (if m < 2 then 0 else 196884 * b (m - 2)))
  have hhasF : ∀ q : ℂ, ‖q‖ < 1 → HasSum (fun m => d m • q ^ m) (F q) := by
    intro q hq
    have h1 : HasSum (fun m => (if m = 0 then (0 : ℂ) else a (m - 1)) • q ^ m) (q * fE q) := by
      have hmul : HasSum (fun n => a n • q ^ (n + 1)) (q * fE q) := by
        have h' := (hhasE q hq).mul_left q
        refine h'.congr_fun fun n => ?_
        simp only [smul_eq_mul, pow_succ']
        ring
      refine (hasSum_nat_add_iff' 1
        (f := fun m => (if m = 0 then (0 : ℂ) else a (m - 1)) • q ^ m)).mp ?_
      simpa [Finset.sum_range_one] using hmul
    have h2 : HasSum (fun m => b m • q ^ m) (fΔ q) := hhasΔ q hq
    have h3 : HasSum (fun m => (if m = 0 then (0 : ℂ) else 744 * b (m - 1)) • q ^ m) (744 * q * fΔ q) := by
      have hmul : HasSum (fun n => (744 * b n) • q ^ (n + 1)) (744 * q * fΔ q) := by
        have h' := (hhasΔ q hq).mul_left (744 * q)
        refine h'.congr_fun fun n => ?_
        simp only [smul_eq_mul, pow_succ']
        ring
      refine (hasSum_nat_add_iff' 1
        (f := fun m => (if m = 0 then (0 : ℂ) else 744 * b (m - 1)) • q ^ m)).mp ?_
      simpa [Finset.sum_range_one] using hmul
    have h4 : HasSum (fun m => (if m < 2 then (0 : ℂ) else 196884 * b (m - 2)) • q ^ m)
        (196884 * q ^ 2 * fΔ q) := by
      have hmul : HasSum (fun n => (196884 * b n) • q ^ (n + 2)) (196884 * q ^ 2 * fΔ q) := by
        have h' := (hhasΔ q hq).mul_left (196884 * q ^ 2)
        refine h'.congr_fun fun n => ?_
        simp only [smul_eq_mul, pow_add]
        ring
      refine (hasSum_nat_add_iff' 2
        (f := fun m => (if m < 2 then (0 : ℂ) else 196884 * b (m - 2)) • q ^ m)).mp ?_
      have hfin : (∑ i ∈ Finset.range 2, (if i < 2 then (0 : ℂ) else 196884 * b (i - 2)) • q ^ i) = 0 := by
        simp [Finset.sum_range_succ]
      rw [hfin, sub_zero]
      refine hmul.congr_fun fun n => ?_
      have hnot : ¬ (n + 2 < 2) := by omega
      simp [hnot]
    have hcomb := h1.sub ((h2.add h3).add h4)
    have hval : q * fE q - (fΔ q + 744 * q * fΔ q + 196884 * q ^ 2 * fΔ q) = F q := by
      dsimp only [F]; ring
    rw [hval] at hcomb
    refine hcomb.congr_fun fun m => ?_
    simp only [d, sub_smul, add_smul]
  have ⟨ha0, ha1, ha2, _⟩ := E4_cube_qExpansion_coeffs
  have ⟨hb0, hb1, hb2, hb3⟩ := discriminant_qExpansion_coeffs
  have hd_zero : ∀ k < 4, d k = 0 := by
    intro k hk
    interval_cases k
    · dsimp only [d, a, b]; simp [hb0]
    · dsimp only [d, a, b]; simp [ha0, hb0, hb1]
    · dsimp only [d, a, b]; simp [ha1, hb0, hb1, hb2]; norm_num
    · dsimp only [d, a, b]; simp [ha2, hb1, hb2, hb3]; norm_num
  -- Factor out `q^4` from `F(q)` on `‖q‖ ≤ 1/2` to obtain `F(q) =O[nhds 0] (fun q => q^4)`!
  have hF_O4 : F =O[nhds (0 : ℂ)] (fun q : ℂ => q ^ 4) := by
    have h34_lt : ‖(3 / 4 : ℂ)‖ < 1 := by norm_num
    have hterm_tendsto : Filter.Tendsto (fun m : ℕ => ‖d m • (3 / 4 : ℂ) ^ m‖) Filter.atTop (nhds 0) := by
      have h0 := ((hhasF (3 / 4) h34_lt).summable).tendsto_atTop_zero
      simpa using h0.norm
    have hM_ex : ∃ M : ℝ, 0 ≤ M ∧ ∀ m : ℕ, ‖d m‖ * (3 / 4 : ℝ) ^ m ≤ M := by
      have hev : ∀ᶠ m : ℕ in Filter.atTop, ‖d m • (3 / 4 : ℂ) ^ m‖ < 1 :=
        hterm_tendsto.eventually (gt_mem_nhds zero_lt_one)
      rcases Filter.eventually_atTop.mp hev with ⟨N, hN⟩
      let M : ℝ := max 1 (∑ i ∈ Finset.range N, ‖d i‖ * (3 / 4 : ℝ) ^ i)
      refine ⟨M, le_trans zero_le_one (le_max_left _ _), fun m => ?_⟩
      by_cases hm : m < N
      · exact (Finset.single_le_sum (f := fun i => ‖d i‖ * (3 / 4 : ℝ) ^ i)
          (fun i _ => by positivity) (Finset.mem_range.mpr hm)).trans (le_max_right _ _)
      · have hlt := hN m (Nat.le_of_not_lt hm)
        have hnorm : ‖d m • (3 / 4 : ℂ) ^ m‖ = ‖d m‖ * (3 / 4 : ℝ) ^ m := by
          rw [smul_eq_mul, norm_mul, norm_pow]
          have h34 : ‖(3 / 4 : ℂ)‖ = (3 / 4 : ℝ) := by norm_num
          rw [h34]
        rw [hnorm] at hlt
        exact (le_of_lt hlt).trans (le_max_left _ _)
    rcases hM_ex with ⟨M, hM_nn, hM⟩
    have hsum_norm : Summable (fun m : ℕ => ‖d (m + 4)‖ * (1 / 2 : ℝ) ^ m) := by
      have hgeo : Summable (fun m : ℕ => (M * (4 / 3 : ℝ) ^ 4) * (2 / 3 : ℝ) ^ m) :=
        (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
      refine Summable.of_nonneg_of_le (fun m => by positivity) (fun m => ?_) hgeo
      have hdm := hM (m + 4)
      have hpow_half : (1 / 2 : ℝ) ^ m = (3 / 4 : ℝ) ^ m * (2 / 3 : ℝ) ^ m := by
        rw [← mul_pow]; norm_num
      calc ‖d (m + 4)‖ * (1 / 2 : ℝ) ^ m
          = (‖d (m + 4)‖ * (3 / 4 : ℝ) ^ (m + 4)) * (4 / 3 : ℝ) ^ 4 * (2 / 3 : ℝ) ^ m := by
              rw [hpow_half, pow_add]; ring
        _ ≤ M * (4 / 3 : ℝ) ^ 4 * (2 / 3 : ℝ) ^ m := by
              gcongr
    set C : ℝ := ∑' m : ℕ, ‖d (m + 4)‖ * (1 / 2 : ℝ) ^ m
    rw [Asymptotics.isBigO_iff]
    refine ⟨C, ?_⟩
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1 / 2)] with q hq
    rw [Metric.mem_ball, dist_zero_right] at hq
    have hq_lt1 : ‖q‖ < 1 := lt_trans hq (by norm_num)
    have hF_shift : HasSum (fun m : ℕ => d (m + 4) • q ^ (m + 4)) (F q) := by
      have h := (hasSum_nat_add_iff' 4 (f := fun m => d m • q ^ m)).mpr (hhasF q hq_lt1)
      have hfin : (∑ i ∈ Finset.range 4, d i • q ^ i) = 0 :=
        Finset.sum_eq_zero fun i hi => by rw [hd_zero i (Finset.mem_range.mp hi), zero_smul]
      rw [hfin, sub_zero] at h
      exact h
    have hterm_le : ∀ m : ℕ, ‖d (m + 4) • q ^ (m + 4)‖ ≤ (‖d (m + 4)‖ * (1 / 2 : ℝ) ^ m) * ‖q ^ 4‖ := by
      intro m
      rw [smul_eq_mul, norm_mul, norm_pow, pow_add, norm_pow]
      have hpow_le : ‖q‖ ^ m ≤ (1 / 2 : ℝ) ^ m := pow_le_pow_left₀ (norm_nonneg q) (le_of_lt hq) m
      calc ‖d (m + 4)‖ * (‖q‖ ^ m * ‖q‖ ^ 4)
          = (‖d (m + 4)‖ * ‖q‖ ^ m) * ‖q‖ ^ 4 := by ring
        _ ≤ (‖d (m + 4)‖ * (1 / 2 : ℝ) ^ m) * ‖q‖ ^ 4 := by gcongr
    have hsum_abs : Summable (fun m : ℕ => ‖d (m + 4) • q ^ (m + 4)‖) :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm_le (hsum_norm.mul_right _)
    calc ‖F q‖
        = ‖∑' m : ℕ, d (m + 4) • q ^ (m + 4)‖ := by rw [hF_shift.tsum_eq]
      _ ≤ ∑' m : ℕ, ‖d (m + 4) • q ^ (m + 4)‖ := norm_tsum_le_tsum_norm hsum_abs
      _ ≤ ∑' m : ℕ, (‖d (m + 4)‖ * (1 / 2 : ℝ) ^ m) * ‖q ^ 4‖ :=
          Summable.tsum_le_tsum hterm_le hsum_abs (hsum_norm.mul_right _)
      _ = C * ‖q ^ 4‖ := by rw [tsum_mul_right]
  -- Pull back `hF_O4` along `qParam 1 τ → 0` and divide by `qParam 1 τ * Δ(τ) = qParam 1 τ ^ 2 * P(τ)`.
  have hF_comp : (fun τ : UpperHalfPlane => F (Function.Periodic.qParam (1 : ℝ) (τ : ℂ)))
      =O[UpperHalfPlane.atImInfty]
      (fun τ : UpperHalfPlane => Function.Periodic.qParam (1 : ℝ) (τ : ℂ) ^ 4) :=
    hF_O4.comp_tendsto (UpperHalfPlane.qParam_tendsto_atImInfty zero_lt_one)
  rw [Asymptotics.isBigO_iff] at hF_comp ⊢
  rcases hF_comp with ⟨C, hC⟩
  have hP_ev : ∀ᶠ τ : UpperHalfPlane in UpperHalfPlane.atImInfty,
      (1 / 2 : ℝ) ≤ ‖∏' n : ℕ, (1 - ModularForm.eta_q n (τ : ℂ)) ^ 24‖ := by
    have hball := ModularForm.tendsto_atImInfty_tprod_one_sub_eta_q_pow.eventually
      (Metric.ball_mem_nhds (1 : ℂ) (by norm_num : (0 : ℝ) < 1 / 2))
    filter_upwards [hball] with τ hτ
    rw [dist_eq_norm] at hτ
    have htri : (1 : ℝ) - ‖∏' n : ℕ, (1 - ModularForm.eta_q n (τ : ℂ)) ^ 24‖ ≤
        ‖(1 : ℂ) - ∏' n : ℕ, (1 - ModularForm.eta_q n (τ : ℂ)) ^ 24‖ := by
      simpa [norm_one] using norm_sub_norm_le (1 : ℂ) (∏' n : ℕ, (1 - ModularForm.eta_q n (τ : ℂ)) ^ 24)
    rw [norm_sub_rev] at htri
    linarith
  refine ⟨2 * max C 0, ?_⟩
  filter_upwards [hC, hP_ev] with τ hτC hτP
  set q : ℂ := Function.Periodic.qParam (1 : ℝ) (τ : ℂ)
  set P : ℂ := ∏' n : ℕ, (1 - ModularForm.eta_q n (τ : ℂ)) ^ 24
  have hq_ne : q ≠ 0 := qParam_ne_zero τ
  have hΔ_ne : ModularForm.discriminant τ ≠ 0 := discriminant_ne_zero τ
  have hΔ_prod : ModularForm.discriminant τ = q * P := ModularForm.discriminant_eq_q_prod τ
  have hfE_val : fE q = E4 τ ^ 3 := by
    have h := SlashInvariantFormClass.eq_cuspFunction (monomialE4E6 3 0) τ one_mem_strictPeriods_SL one_ne_zero
    rw [monomialE4E6_apply, ← E4_eq_modularForm_E4] at h
    simpa [fE, q] using h
  have hfΔ_val : fΔ q = ModularForm.discriminant τ := by
    have h := SlashInvariantFormClass.eq_cuspFunction CuspForm.discriminant τ one_mem_strictPeriods_SL one_ne_zero
    simpa [fΔ, q, CuspForm.coe_discriminant] using h
  have hdiff_eq : jInvariant τ - (q⁻¹ + 744 + 196884 * q) = F q / (q * ModularForm.discriminant τ) := by
    unfold jInvariant
    dsimp only [F]
    rw [hfE_val, hfΔ_val]
    field_simp [hq_ne, hΔ_ne]
  rw [hdiff_eq, hΔ_prod, norm_div, norm_mul, norm_mul]
  have hP_pos : (0 : ℝ) < ‖P‖ := lt_of_lt_of_le (by norm_num) hτP
  have hq_pos : (0 : ℝ) < ‖q‖ := norm_pos_iff.mpr hq_ne
  have hC_nn : 0 ≤ max C 0 := le_max_right _ _
  have hF_le : ‖F q‖ ≤ max C 0 * ‖q ^ 4‖ :=
    hτC.trans (mul_le_mul_of_nonneg_right (le_max_left C 0) (norm_nonneg _))
  rw [norm_pow] at hF_le ⊢
  rw [div_le_iff₀ (by positivity)]
  have hmul_le : max C 0 * ‖q‖ ^ 4 ≤ 2 * max C 0 * ‖q‖ ^ 2 * (‖q‖ * (‖q‖ * ‖P‖)) := by
    have hstep : (1 : ℝ) ≤ 2 * ‖P‖ := by linarith
    calc max C 0 * ‖q‖ ^ 4
        = (max C 0 * ‖q‖ ^ 4) * 1 := by ring
      _ ≤ (max C 0 * ‖q‖ ^ 4) * (2 * ‖P‖) := by gcongr
      _ = 2 * max C 0 * ‖q‖ ^ 2 * (‖q‖ * (‖q‖ * ‖P‖)) := by ring
  exact hF_le.trans hmul_le

private lemma periodic_qParam_comp_ofComplex :
    Function.Periodic
      ((fun τ : UpperHalfPlane => Function.Periodic.qParam (1 : ℝ) (τ : ℂ)) ∘
        (UpperHalfPlane.ofComplex : ℂ → UpperHalfPlane)) (1 : ℝ) := by
  intro z
  by_cases hz : 0 < z.im
  · have hz1 : 0 < (z + 1).im := by simpa using hz
    simp only [Function.comp_apply, Complex.ofReal_one,
      UpperHalfPlane.ofComplex_apply_of_im_pos hz1, UpperHalfPlane.ofComplex_apply_of_im_pos hz]
    unfold Function.Periodic.qParam
    have hadd : 2 * (Real.pi : ℂ) * Complex.I * (z + 1) / ((1 : ℝ) : ℂ) =
        2 * (Real.pi : ℂ) * Complex.I * z / ((1 : ℝ) : ℂ) + 2 * (Real.pi : ℂ) * Complex.I := by
      push_cast; ring
    rw [hadd, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
  · have hz1 : ¬ 0 < (z + 1).im := by simpa using hz
    simp only [Function.comp_apply, Complex.ofReal_one,
      UpperHalfPlane.ofComplex_apply_of_im_nonpos (not_lt.mp hz1),
      UpperHalfPlane.ofComplex_apply_of_im_nonpos (not_lt.mp hz)]

private lemma mdifferentiable_qParam :
    MDiff (fun τ : UpperHalfPlane => Function.Periodic.qParam (1 : ℝ) (τ : ℂ)) := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  have hdiff : DifferentiableOn ℂ (fun z : ℂ => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * z / (1 : ℝ)))
      {z : ℂ | 0 < z.im} := by
    refine Differentiable.differentiableOn ?_
    exact (((differentiable_const _).mul differentiable_id).div_const _).cexp
  refine hdiff.congr fun z hz => ?_
  simp only [Function.comp_apply, UpperHalfPlane.ofComplex_apply_of_im_pos hz]
  rfl

private lemma analyticAt_cuspFunction_qParam :
    AnalyticAt ℂ (UpperHalfPlane.cuspFunction 1 (fun τ : UpperHalfPlane => Function.Periodic.qParam (1 : ℝ) (τ : ℂ))) 0 := by
  refine UpperHalfPlane.analyticAt_cuspFunction_zero zero_lt_one periodic_qParam_comp_ofComplex
    mdifferentiable_qParam ?_
  rw [UpperHalfPlane.isBoundedAtImInfty_iff]
  exact ⟨1, 0, fun τ _ => le_of_lt (norm_qParam_lt_one τ)⟩

private lemma qExpansion_qParam :
    UpperHalfPlane.qExpansion 1 (fun τ : UpperHalfPlane => Function.Periodic.qParam (1 : ℝ) (τ : ℂ)) =
      PowerSeries.X := by
  let fC : C(UpperHalfPlane, ℂ) :=
    ⟨fun τ => Function.Periodic.qParam (1 : ℝ) (τ : ℂ), mdifferentiable_qParam.continuous⟩
  have hsum : ∀ τ : UpperHalfPlane,
      HasSum (fun n : ℕ => (PowerSeries.coeff n (PowerSeries.X : PowerSeries ℂ)) •
          Function.Periodic.qParam (1 : ℝ) (τ : ℂ) ^ n) (fC τ) := by
    intro τ
    have hsingle : HasSum (fun n : ℕ => if n = 1 then Function.Periodic.qParam (1 : ℝ) (τ : ℂ) else 0)
        (fC τ) := hasSum_ite_eq 1 _
    refine hsingle.congr_fun fun n => ?_
    rw [PowerSeries.coeff_X]
    split_ifs with hn
    · subst hn; simp
    · simp
  ext m
  exact (UpperHalfPlane.qExpansion_coeff_unique fC zero_lt_one
    analyticAt_cuspFunction_qParam hsum m).symm

private lemma analyticAt_cuspFunction_discriminantDivQ :
    AnalyticAt ℂ (UpperHalfPlane.cuspFunction 1 discriminantDivQ) 0 := by
  have hper : Function.Periodic (discriminantDivQ ∘ (UpperHalfPlane.ofComplex : ℂ → UpperHalfPlane)) (1 : ℝ) := by
    intro z
    by_cases hz : 0 < z.im
    · have hz1 : 0 < (z + 1).im := by simpa using hz
      have hof1 : UpperHalfPlane.ofComplex (z + 1) = ModularGroup.T • UpperHalfPlane.ofComplex z := by
        apply UpperHalfPlane.ext
        rw [UpperHalfPlane.ofComplex_apply_of_im_pos hz1,
          show ((ModularGroup.T • UpperHalfPlane.ofComplex z : UpperHalfPlane) : ℂ) =
            (UpperHalfPlane.ofComplex z : ℂ) + 1 by
            simpa [zpow_one] using ModularGroup.coe_T_zpow_smul_eq (UpperHalfPlane.ofComplex z) (n := 1),
          UpperHalfPlane.ofComplex_apply_of_im_pos hz]
      simp only [Function.comp_apply, Complex.ofReal_one, discriminantDivQ]
      have hqper := periodic_qParam_comp_ofComplex z
      simp only [Function.comp_apply, Complex.ofReal_one] at hqper
      rw [hqper, hof1]
      have hΔT := congrFun (CuspForm.discriminant.slash_action_eq' _ ⟨ModularGroup.T, rfl⟩)
        (UpperHalfPlane.ofComplex z)
      change SlashAction.map 12 (sl2ZToGL2R ModularGroup.T) ModularForm.discriminant
        (UpperHalfPlane.ofComplex z) = ModularForm.discriminant (UpperHalfPlane.ofComplex z) at hΔT
      rw [slash_T_apply] at hΔT
      rw [hΔT]
    · have hz1 : ¬ 0 < (z + 1).im := by simpa using hz
      simp only [Function.comp_apply, Complex.ofReal_one,
        UpperHalfPlane.ofComplex_apply_of_im_nonpos (not_lt.mp hz1),
        UpperHalfPlane.ofComplex_apply_of_im_nonpos (not_lt.mp hz)]
  have hmdiff : MDiff discriminantDivQ := by
    rw [UpperHalfPlane.mdifferentiable_iff]
    have hΔd : DifferentiableOn ℂ (ModularForm.discriminant ∘ UpperHalfPlane.ofComplex) {z : ℂ | 0 < z.im} := by
      have := UpperHalfPlane.mdifferentiable_iff.mp CuspForm.discriminant.holo'
      simpa [CuspForm.coe_discriminant] using this
    have hqd : DifferentiableOn ℂ ((fun τ : UpperHalfPlane => Function.Periodic.qParam (1 : ℝ) (τ : ℂ)) ∘
        UpperHalfPlane.ofComplex) {z : ℂ | 0 < z.im} :=
      UpperHalfPlane.mdifferentiable_iff.mp mdifferentiable_qParam
    refine (hΔd.div hqd (fun z _ => ?_)).congr fun z _ => rfl
    simp only [Function.comp_apply]
    exact qParam_ne_zero _
  have hbdd : UpperHalfPlane.IsBoundedAtImInfty discriminantDivQ := by
    refine isBoundedAtImInfty_of_tendsto_one ?_
    refine ModularForm.tendsto_atImInfty_tprod_one_sub_eta_q_pow.congr fun τ => ?_
    unfold discriminantDivQ
    rw [ModularForm.discriminant_eq_q_prod τ, mul_div_cancel_left₀ _ (qParam_ne_zero τ)]
  exact UpperHalfPlane.analyticAt_cuspFunction_zero zero_lt_one hper hmdiff hbdd

private lemma analyticAt_cuspFunction_qMulJInvariant :
    AnalyticAt ℂ (UpperHalfPlane.cuspFunction 1 qMulJInvariant) 0 := by
  have hper : Function.Periodic (qMulJInvariant ∘ (UpperHalfPlane.ofComplex : ℂ → UpperHalfPlane)) (1 : ℝ) := by
    intro z
    by_cases hz : 0 < z.im
    · have hz1 : 0 < (z + 1).im := by simpa using hz
      have hof1 : UpperHalfPlane.ofComplex (z + 1) = ModularGroup.T • UpperHalfPlane.ofComplex z := by
        apply UpperHalfPlane.ext
        rw [UpperHalfPlane.ofComplex_apply_of_im_pos hz1,
          show ((ModularGroup.T • UpperHalfPlane.ofComplex z : UpperHalfPlane) : ℂ) =
            (UpperHalfPlane.ofComplex z : ℂ) + 1 by
            simpa [zpow_one] using ModularGroup.coe_T_zpow_smul_eq (UpperHalfPlane.ofComplex z) (n := 1),
          UpperHalfPlane.ofComplex_apply_of_im_pos hz]
      simp only [Function.comp_apply, Complex.ofReal_one, qMulJInvariant]
      have hqper := periodic_qParam_comp_ofComplex z
      simp only [Function.comp_apply, Complex.ofReal_one] at hqper
      rw [hqper, hof1, jInvariant_T_smul]
    · have hz1 : ¬ 0 < (z + 1).im := by simpa using hz
      simp only [Function.comp_apply, Complex.ofReal_one,
        UpperHalfPlane.ofComplex_apply_of_im_nonpos (not_lt.mp hz1),
        UpperHalfPlane.ofComplex_apply_of_im_nonpos (not_lt.mp hz)]
  have hmdiff : MDiff qMulJInvariant := by
    rw [UpperHalfPlane.mdifferentiable_iff]
    have hE4d : DifferentiableOn ℂ ((monomialE4E6 3 0 : UpperHalfPlane → ℂ) ∘ UpperHalfPlane.ofComplex)
        {z : ℂ | 0 < z.im} :=
      UpperHalfPlane.mdifferentiable_iff.mp (monomialE4E6 3 0).holo'
    have hΔd : DifferentiableOn ℂ (ModularForm.discriminant ∘ UpperHalfPlane.ofComplex) {z : ℂ | 0 < z.im} := by
      have := UpperHalfPlane.mdifferentiable_iff.mp CuspForm.discriminant.holo'
      simpa [CuspForm.coe_discriminant] using this
    have hqd : DifferentiableOn ℂ ((fun τ : UpperHalfPlane => Function.Periodic.qParam (1 : ℝ) (τ : ℂ)) ∘
        UpperHalfPlane.ofComplex) {z : ℂ | 0 < z.im} :=
      UpperHalfPlane.mdifferentiable_iff.mp mdifferentiable_qParam
    refine ((hqd.mul (hE4d.div hΔd (fun z _ => discriminant_ne_zero _)))).congr fun z _ => ?_
    simp only [Function.comp_apply, Pi.mul_apply, Pi.div_apply, qMulJInvariant, jInvariant,
      monomialE4E6_apply, pow_zero, mul_one, E4_eq_modularForm_E4]
  have hbdd : UpperHalfPlane.IsBoundedAtImInfty qMulJInvariant := by
    refine isBoundedAtImInfty_of_tendsto_one ?_
    have hnum : Filter.Tendsto (fun τ : UpperHalfPlane => E4 τ ^ 3) UpperHalfPlane.atImInfty (nhds 1) := by
      simpa using tendsto_E4_atImInfty.pow 3
    have hdiv : Filter.Tendsto (fun τ : UpperHalfPlane => E4 τ ^ 3 /
        (∏' n : ℕ, (1 - ModularForm.eta_q n (τ : ℂ)) ^ 24)) UpperHalfPlane.atImInfty (nhds (1 / 1)) :=
      hnum.div ModularForm.tendsto_atImInfty_tprod_one_sub_eta_q_pow one_ne_zero
    rw [div_one] at hdiv
    refine hdiv.congr fun τ => ?_
    unfold qMulJInvariant jInvariant
    rw [ModularForm.discriminant_eq_q_prod τ]
    have hq_ne := qParam_ne_zero τ
    field_simp [hq_ne]
  exact UpperHalfPlane.analyticAt_cuspFunction_zero zero_lt_one hper hmdiff hbdd

/-- **Famous Leading Coefficients of Klein's `j`-Invariant (`q · j(τ) = 1 + 744 q + 196884 q² + ...`)**:
- `coeff 0 (qExpansion 1 (q · j)) = 1` (the `q⁻¹` pole residue),
- `coeff 1 (qExpansion 1 (q · j)) = 744` (constant term of `j(τ)`),
- `coeff 2 (qExpansion 1 (q · j)) = 196884` (the Monstrous Moonshine coefficient `196883 + 1`). -/
theorem qMulJInvariant_qExpansion_coeffs :
    PowerSeries.coeff 0 (UpperHalfPlane.qExpansion 1 qMulJInvariant) = 1 ∧
    PowerSeries.coeff 1 (UpperHalfPlane.qExpansion 1 qMulJInvariant) = 744 ∧
    PowerSeries.coeff 2 (UpperHalfPlane.qExpansion 1 qMulJInvariant) = 196884 := by
  have hmul1 : (fun τ : UpperHalfPlane => Function.Periodic.qParam (1 : ℝ) (τ : ℂ)) * discriminantDivQ =
      ModularForm.discriminant := by
    funext τ
    simp only [Pi.mul_apply, discriminantDivQ]
    exact mul_div_cancel₀ _ (qParam_ne_zero τ)
  have hq1 : PowerSeries.X * UpperHalfPlane.qExpansion 1 discriminantDivQ =
      UpperHalfPlane.qExpansion 1 ModularForm.discriminant := by
    rw [← qExpansion_qParam,
      ← UpperHalfPlane.qExpansion_mul analyticAt_cuspFunction_qParam analyticAt_cuspFunction_discriminantDivQ,
      hmul1]
  have ⟨_, hb1, hb2, hb3⟩ := discriminant_qExpansion_coeffs
  have hd0 : PowerSeries.coeff 0 (UpperHalfPlane.qExpansion 1 discriminantDivQ) = 1 := by
    have h := congrArg (PowerSeries.coeff 1) hq1
    rw [powerSeries_coeff_mul_one, PowerSeries.coeff_X, PowerSeries.coeff_X, hb1] at h
    simpa using h
  have hd1 : PowerSeries.coeff 1 (UpperHalfPlane.qExpansion 1 discriminantDivQ) = -24 := by
    have h := congrArg (PowerSeries.coeff 2) hq1
    rw [powerSeries_coeff_mul_two, PowerSeries.coeff_X, PowerSeries.coeff_X, PowerSeries.coeff_X, hb2] at h
    simpa using h
  have hd2 : PowerSeries.coeff 2 (UpperHalfPlane.qExpansion 1 discriminantDivQ) = 252 := by
    have h := congrArg (PowerSeries.coeff 3) hq1
    rw [powerSeries_coeff_mul_three, PowerSeries.coeff_X, PowerSeries.coeff_X, PowerSeries.coeff_X,
      PowerSeries.coeff_X, hb3] at h
    simpa using h
  have hmul2 : discriminantDivQ * qMulJInvariant = (monomialE4E6 3 0 : UpperHalfPlane → ℂ) := by
    funext τ
    simp only [Pi.mul_apply, discriminantDivQ, qMulJInvariant, jInvariant, monomialE4E6_apply,
      pow_zero, mul_one, E4_eq_modularForm_E4]
    have hq_ne := qParam_ne_zero τ
    have hΔ_ne := discriminant_ne_zero τ
    field_simp [hq_ne, hΔ_ne]
  have hq2 : UpperHalfPlane.qExpansion 1 discriminantDivQ * UpperHalfPlane.qExpansion 1 qMulJInvariant =
      UpperHalfPlane.qExpansion 1 (monomialE4E6 3 0 : UpperHalfPlane → ℂ) := by
    rw [← UpperHalfPlane.qExpansion_mul analyticAt_cuspFunction_discriminantDivQ
      analyticAt_cuspFunction_qMulJInvariant, hmul2]
  have ⟨ha0, ha1, ha2, _⟩ := E4_cube_qExpansion_coeffs
  have hc0 : PowerSeries.coeff 0 (UpperHalfPlane.qExpansion 1 qMulJInvariant) = 1 := by
    have h := congrArg (PowerSeries.coeff 0) hq2
    rw [powerSeries_coeff_mul_zero, hd0, ha0, one_mul] at h
    exact h
  have hc1 : PowerSeries.coeff 1 (UpperHalfPlane.qExpansion 1 qMulJInvariant) = 744 := by
    have h := congrArg (PowerSeries.coeff 1) hq2
    rw [powerSeries_coeff_mul_one, hd0, hd1, hc0, ha1] at h
    linear_combination h
  have hc2 : PowerSeries.coeff 2 (UpperHalfPlane.qExpansion 1 qMulJInvariant) = 196884 := by
    have h := congrArg (PowerSeries.coeff 2) hq2
    rw [powerSeries_coeff_mul_two, hd0, hd1, hd2, hc0, hc1, ha2] at h
    linear_combination h
  exact ⟨hc0, hc1, hc2⟩

end KleinJInvariant

end

end RHDirect.Stage8ModularRing
