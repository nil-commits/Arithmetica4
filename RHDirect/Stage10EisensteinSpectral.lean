import RHDirect.Stage5ThetaModular
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Convolution
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.ZetaValues

/-!
# RHDirect.Stage10EisensteinSpectral

Unconditional formalization of the **Real-Analytic Eisenstein Series `E(τ, s)` on `SL₂(ℤ) \ ℍ`**,
its **Hyperbolic Laplacian Eigenvalue Equation `Δ_ℍ E(τ, s) = s (1 - s) E(τ, s)`**, its
**2D Theta Modular Transformation `θ_τ(1/t) = t · θ_τ(t)` & Global Meromorphic Continuation /
Functional Equation `E*(τ, 1 - s) = E*(τ, s)`**, its **Exact Constant Term
`∫_0^1 E(x + i y, s) dx = y^s + (Λ(2s - 1) / Λ(2s)) y^{1 - s}`**, and the **Spectral Scattering
Matrix Functional Equation & Unitarity on `Re(s) = 1/2`** in pure Mathlib `v4.33.1`.

Zero `sorry`, zero custom `axiom`s, zero assumptions.
-/

open Complex Real Filter MeasureTheory Module Submodule Finset
open RHDirect.ArakelovCovolume RHDirect.Stage3ThetaSiegelBridge
open RHDirect.Stage4SelbergTrace RHDirect.Stage5ThetaModular
open scoped BigOperators UpperHalfPlane Topology ComplexConjugate Matrix

namespace RHDirect.Stage10EisensteinSpectral

noncomputable section

/-! ### Elementary Positive-Real `cpow` Helpers -/

lemma ofReal_inv_cpow {a : ℝ} (ha : 0 < a) (z : ℂ) :
    ((a⁻¹ : ℝ) : ℂ) ^ z = (a : ℂ) ^ (-z) := by
  have haC : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
  have hinvC : ((a⁻¹ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (inv_pos.mpr ha).ne'
  rw [Complex.cpow_def_of_ne_zero hinvC, Complex.cpow_def_of_ne_zero haC,
    ← Complex.ofReal_log (inv_pos.mpr ha).le, Real.log_inv,
    ← Complex.ofReal_log ha.le, Complex.ofReal_neg]
  congr 1; ring

lemma ofReal_mul_cpow {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (z : ℂ) :
    ((a * b : ℝ) : ℂ) ^ z = (a : ℂ) ^ z * (b : ℂ) ^ z := by
  have haC : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
  have hbC : (b : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hb.ne'
  have habC : ((a * b : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (mul_pos ha hb).ne'
  rw [Complex.cpow_def_of_ne_zero habC, Complex.cpow_def_of_ne_zero haC,
    Complex.cpow_def_of_ne_zero hbC, ← Complex.exp_add,
    ← Complex.ofReal_log (mul_pos ha hb).le, Real.log_mul ha.ne' hb.ne',
    ← Complex.ofReal_log ha.le, ← Complex.ofReal_log hb.le, Complex.ofReal_add]
  congr 1; ring

lemma ofReal_div_cpow {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (z : ℂ) :
    ((a / b : ℝ) : ℂ) ^ z = (a : ℂ) ^ z * (b : ℂ) ^ (-z) := by
  rw [div_eq_mul_inv, ofReal_mul_cpow ha (inv_pos.mpr hb) z, ofReal_inv_cpow hb z]

lemma ofReal_sq_cpow {a : ℝ} (ha : 0 < a) (z : ℂ) :
    ((a ^ 2 : ℝ) : ℂ) ^ z = (a : ℂ) ^ (2 * z) := by
  have haC : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
  have ha2C : ((a ^ 2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (sq_pos_of_pos ha).ne'
  rw [Complex.cpow_def_of_ne_zero ha2C, Complex.cpow_def_of_ne_zero haC,
    ← Complex.ofReal_log (sq_pos_of_pos ha).le, Real.log_pow,
    ← Complex.ofReal_log ha.le]
  push_cast
  congr 1; ring

/-! ## Section 1: 2D Modular Lattice `tauLattice τ`, Real-Analytic Eisenstein Series & `SL₂(ℤ)`-Invariance -/

section RealAnalyticEisenstein

/-- Standard 2D modular lattice generator vector `v₁(τ) = (x / √y, √y) ∈ ℝ²`. -/
def tauVec1 (τ : UpperHalfPlane) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 ![τ.re / Real.sqrt τ.im, Real.sqrt τ.im]

/-- Standard 2D modular lattice generator vector `v₂(τ) = (1 / √y, 0) ∈ ℝ²`. -/
def tauVec2 (τ : UpperHalfPlane) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 ![1 / Real.sqrt τ.im, 0]

/-- Explicit linear map `(m, n) ↦ m • v₁(τ) + n • v₂(τ) ∈ ℝ²`. -/
def tauLatticeMap (τ : UpperHalfPlane) (p : ℤ × ℤ) : EuclideanSpace ℝ (Fin 2) :=
  p.1 • tauVec1 τ + p.2 • tauVec2 τ

/-- The rank-2 unimodular lattice `L_τ = ℤ v₁(τ) + ℤ v₂(τ) ⊂ ℝ²` associated to `τ ∈ ℍ`. -/
def tauLattice (τ : UpperHalfPlane) : Submodule ℤ (EuclideanSpace ℝ (Fin 2)) :=
  Submodule.span ℤ ({tauVec1 τ, tauVec2 τ} : Set (EuclideanSpace ℝ (Fin 2)))

/-- Exact norm-squared formula: `‖(c : ℂ) * τ + d‖² = (c * τ.re + d)² + (c * τ.im)²`. -/
lemma norm_sq_int_mul_tau_add (τ : UpperHalfPlane) (c d : ℤ) :
    ‖(c : ℂ) * (τ : ℂ) + (d : ℂ)‖ ^ 2 =
      ((c : ℝ) * τ.re + (d : ℝ)) ^ 2 + ((c : ℝ) * τ.im) ^ 2 := by
  have hre : ((c : ℂ) * (τ : ℂ) + (d : ℂ)).re = (c : ℝ) * τ.re + (d : ℝ) := by
    simp [Complex.add_re, Complex.mul_re]
  have him : ((c : ℂ) * (τ : ℂ) + (d : ℂ)).im = (c : ℝ) * τ.im := by
    simp [Complex.add_im, Complex.mul_im]
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, hre, him, sq, sq]

/-- For `(c, d) ≠ (0, 0)` and `τ ∈ ℍ`, `‖(c : ℂ) * τ + d‖ > 0`. -/
lemma norm_int_mul_tau_add_pos (τ : UpperHalfPlane) {p : ℤ × ℤ} (hp : p ≠ (0, 0)) :
    0 < ‖(p.1 : ℂ) * (τ : ℂ) + (p.2 : ℂ)‖ := by
  rw [norm_pos_iff]
  intro h0
  have him : ((p.1 : ℂ) * (τ : ℂ) + (p.2 : ℂ)).im = 0 := by rw [h0]; simp
  simp only [Complex.add_im, Complex.mul_im, Complex.intCast_re, Complex.intCast_im,
    zero_mul, add_zero] at him
  have hp1 : p.1 = 0 := by
    have : (p.1 : ℝ) = 0 := (mul_eq_zero.mp him).resolve_right τ.im_pos.ne'
    exact_mod_cast this
  rw [hp1] at h0
  simp only [Int.cast_zero, zero_mul, zero_add] at h0
  have hp2 : p.2 = 0 := by exact_mod_cast h0
  exact hp (Prod.ext hp1 hp2)

/-- Exact squared norm of `tauLatticeMap τ p`:
`‖tauLatticeMap τ p‖² = ‖p.1 * τ + p.2‖² / τ.im`. -/
lemma norm_sq_tauLatticeMap (τ : UpperHalfPlane) (p : ℤ × ℤ) :
    ‖tauLatticeMap τ p‖ ^ 2 = ‖(p.1 : ℂ) * (τ : ℂ) + (p.2 : ℂ)‖ ^ 2 / τ.im := by
  have hy : 0 < τ.im := τ.im_pos
  have hsq : Real.sqrt τ.im ^ 2 = τ.im := Real.sq_sqrt hy.le
  have hsq4 : Real.sqrt τ.im ^ 4 = τ.im ^ 2 := by
    calc Real.sqrt τ.im ^ 4 = (Real.sqrt τ.im ^ 2) ^ 2 := by ring
      _ = τ.im ^ 2 := by rw [hsq]
  have hsq_ne : Real.sqrt τ.im ≠ 0 := (Real.sqrt_pos.mpr hy).ne'
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
  have h0 : tauLatticeMap τ p 0 = ((p.1 : ℝ) * τ.re + (p.2 : ℝ)) / Real.sqrt τ.im := by
    simp only [tauLatticeMap, tauVec1, tauVec2, PiLp.add_apply, PiLp.smul_apply,
      zsmul_eq_mul, Matrix.cons_val_zero]
    field_simp [hsq_ne]
  have h1 : tauLatticeMap τ p 1 = (p.1 : ℝ) * Real.sqrt τ.im := by
    simp only [tauLatticeMap, tauVec1, tauVec2, PiLp.add_apply, PiLp.smul_apply,
      zsmul_eq_mul, Matrix.cons_val_one, Matrix.cons_val_zero, mul_zero, add_zero]
  rw [h0, h1, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs,
    norm_sq_int_mul_tau_add]
  field_simp [hsq_ne, hy.ne']
  rw [hsq4, hsq]
  ring

lemma tauLatticeMap_mem (τ : UpperHalfPlane) (p : ℤ × ℤ) :
    tauLatticeMap τ p ∈ tauLattice τ := by
  refine Submodule.add_mem _ (Submodule.smul_mem _ _ ?_) (Submodule.smul_mem _ _ ?_)
  · exact Submodule.subset_span (Set.mem_insert _ _)
  · exact Submodule.subset_span (Set.mem_insert_of_mem _ rfl)

/-- Coordinate recovery from `tauLatticeMap τ`: `p ↦ tauLatticeMap τ p` is injective. -/
lemma tauLatticeMap_injective (τ : UpperHalfPlane) :
    Function.Injective (tauLatticeMap τ) := by
  intro p q hpq
  have hy : 0 < τ.im := τ.im_pos
  have hsq_ne : Real.sqrt τ.im ≠ 0 := (Real.sqrt_pos.mpr hy).ne'
  have h1 : tauLatticeMap τ p 1 = tauLatticeMap τ q 1 := congrArg (fun v => v 1) hpq
  simp only [tauLatticeMap, tauVec1, tauVec2, PiLp.add_apply, PiLp.smul_apply,
    zsmul_eq_mul, Matrix.cons_val_one, Matrix.cons_val_zero, mul_zero, add_zero] at h1
  have hp1 : p.1 = q.1 := by
    have : (p.1 : ℝ) = (q.1 : ℝ) := mul_right_cancel₀ hsq_ne h1
    exact_mod_cast this
  have h0 : tauLatticeMap τ p 0 = tauLatticeMap τ q 0 := congrArg (fun v => v 0) hpq
  simp only [tauLatticeMap, tauVec1, tauVec2, PiLp.add_apply, PiLp.smul_apply,
    zsmul_eq_mul, Matrix.cons_val_zero, hp1] at h0
  have hp2 : p.2 = q.2 := by
    have hsub : ((p.2 : ℝ) - (q.2 : ℝ)) * (1 / Real.sqrt τ.im) = 0 := by linarith
    have hinv_ne : (1 / Real.sqrt τ.im : ℝ) ≠ 0 := one_div_ne_zero hsq_ne
    have : (p.2 : ℝ) = (q.2 : ℝ) := sub_eq_zero.mp ((mul_eq_zero.mp hsub).resolve_right hinv_ne)
    exact_mod_cast this
  exact Prod.ext hp1 hp2

/-- Explicit `ℤ`-linear equivalence `(Fin 2 → ℤ) ≃ₗ[ℤ] tauLattice τ`. -/
def tauLatticeEquivFin2 (τ : UpperHalfPlane) : (Fin 2 → ℤ) ≃ₗ[ℤ] tauLattice τ :=
  LinearEquiv.ofBijective
    { toFun := fun c => ⟨tauLatticeMap τ (c 0, c 1), tauLatticeMap_mem τ (c 0, c 1)⟩
      map_add' := fun a b => by
        apply Subtype.ext
        change tauLatticeMap τ (a 0 + b 0, a 1 + b 1) =
          tauLatticeMap τ (a 0, a 1) + tauLatticeMap τ (b 0, b 1)
        simp only [tauLatticeMap, add_zsmul]
        abel
      map_smul' := fun r a => by
        apply Subtype.ext
        change tauLatticeMap τ (r * a 0, r * a 1) = r • tauLatticeMap τ (a 0, a 1)
        simp only [tauLatticeMap, smul_add, mul_zsmul] }
    (by
      constructor
      · intro a b hab
        have h := tauLatticeMap_injective τ (congrArg Subtype.val hab)
        funext i
        fin_cases i
        · exact congrArg Prod.fst h
        · exact congrArg Prod.snd h
      · intro ⟨v, hv⟩
        rw [tauLattice, Submodule.mem_span_pair] at hv
        rcases hv with ⟨a, b, rfl⟩
        exact ⟨![a, b], Subtype.ext rfl⟩)

/-- Canonical `ℤ`-basis of `tauLattice τ`. -/
def tauLatticeBasis (τ : UpperHalfPlane) : Basis (Fin 2) ℤ (tauLattice τ) :=
  (Pi.basisFun ℤ (Fin 2)).map (tauLatticeEquivFin2 τ)

lemma tauLatticeBasis_zero (τ : UpperHalfPlane) :
    ((tauLatticeBasis τ 0 : tauLattice τ) : EuclideanSpace ℝ (Fin 2)) = tauVec1 τ := by
  simp [tauLatticeBasis, tauLatticeEquivFin2, tauLatticeMap]

lemma tauLatticeBasis_one (τ : UpperHalfPlane) :
    ((tauLatticeBasis τ 1 : tauLattice τ) : EuclideanSpace ℝ (Fin 2)) = tauVec2 τ := by
  simp [tauLatticeBasis, tauLatticeEquivFin2, tauLatticeMap]

/-- `tauLattice τ` is discrete (`DiscreteTopology (tauLattice τ)`). -/
instance discreteTopology_tauLattice (τ : UpperHalfPlane) :
    DiscreteTopology (tauLattice τ) := by
  let f : tauLattice τ → ℤ × ℤ := fun v =>
    ((tauLatticeEquivFin2 τ).symm v 0, (tauLatticeEquivFin2 τ).symm v 1)
  have hf_inj : Function.Injective f := by
    intro v w h
    apply (tauLatticeEquivFin2 τ).symm.injective
    funext i
    fin_cases i
    · exact congrArg Prod.fst h
    · exact congrArg Prod.snd h
  have hhy : 0 < τ.im := τ.im_pos
  have hsq_ne : Real.sqrt τ.im ≠ 0 := (Real.sqrt_pos.mpr hhy).ne'
  have hf1 : ∀ v : tauLattice τ, ((f v).1 : ℝ) = (v : EuclideanSpace ℝ (Fin 2)) 1 / Real.sqrt τ.im := by
    intro v
    have hv : (v : EuclideanSpace ℝ (Fin 2)) = tauLatticeMap τ (f v) := by
      have h := congrArg Subtype.val ((tauLatticeEquivFin2 τ).apply_symm_apply v)
      exact h.symm
    have h1 : (v : EuclideanSpace ℝ (Fin 2)) 1 = ((f v).1 : ℝ) * Real.sqrt τ.im := by
      rw [hv]
      simp [tauLatticeMap, tauVec1, tauVec2]
    rw [h1, mul_div_cancel_right₀ _ hsq_ne]
  have hf2 : ∀ v : tauLattice τ, ((f v).2 : ℝ) =
      Real.sqrt τ.im * (v : EuclideanSpace ℝ (Fin 2)) 0 -
        (τ.re / Real.sqrt τ.im) * (v : EuclideanSpace ℝ (Fin 2)) 1 := by
    intro v
    have hv : (v : EuclideanSpace ℝ (Fin 2)) = tauLatticeMap τ (f v) := by
      have h := congrArg Subtype.val ((tauLatticeEquivFin2 τ).apply_symm_apply v)
      exact h.symm
    have h0 : (v : EuclideanSpace ℝ (Fin 2)) 0 =
        ((f v).1 : ℝ) * (τ.re / Real.sqrt τ.im) + ((f v).2 : ℝ) * (1 / Real.sqrt τ.im) := by
      rw [hv]; simp [tauLatticeMap, tauVec1, tauVec2]
    have h1 : (v : EuclideanSpace ℝ (Fin 2)) 1 = ((f v).1 : ℝ) * Real.sqrt τ.im := by
      rw [hv]; simp [tauLatticeMap, tauVec1, tauVec2]
    rw [h0, h1]
    field_simp [hsq_ne]
    ring
  have hf_cont : Continuous f := by
    refine Continuous.prodMk ?_ ?_
    · refine Int.isClosedEmbedding_coe_real.isInducing.continuous_iff.mpr ?_
      have heq : (fun v : tauLattice τ => (((f v).1 : ℤ) : ℝ)) =
          fun v : tauLattice τ => (v : EuclideanSpace ℝ (Fin 2)) 1 / Real.sqrt τ.im :=
        funext hf1
      change Continuous (fun v : tauLattice τ => (((f v).1 : ℤ) : ℝ))
      rw [heq]
      exact ((EuclideanSpace.proj (1 : Fin 2)).continuous.comp continuous_subtype_val).div_const _
    · refine Int.isClosedEmbedding_coe_real.isInducing.continuous_iff.mpr ?_
      have heq : (fun v : tauLattice τ => (((f v).2 : ℤ) : ℝ)) =
          fun v : tauLattice τ =>
            Real.sqrt τ.im * (v : EuclideanSpace ℝ (Fin 2)) 0 -
              (τ.re / Real.sqrt τ.im) * (v : EuclideanSpace ℝ (Fin 2)) 1 :=
        funext hf2
      change Continuous (fun v : tauLattice τ => (((f v).2 : ℤ) : ℝ))
      rw [heq]
      exact (continuous_const.mul ((EuclideanSpace.proj (0 : Fin 2)).continuous.comp continuous_subtype_val)).sub
        (continuous_const.mul ((EuclideanSpace.proj (1 : Fin 2)).continuous.comp continuous_subtype_val))
  exact DiscreteTopology.of_continuous_injective hf_cont hf_inj

/-- Rank of `tauLattice τ` is `2`. -/
lemma rk_tauLattice (τ : UpperHalfPlane) : rk (tauLattice τ) = 2 := by
  unfold rk
  simpa using Module.finrank_eq_card_basis (tauLatticeBasis τ)

/-- Exact covolume `covol (tauLattice τ) = 1`. -/
lemma covol_tauLattice (τ : UpperHalfPlane) : covol (tauLattice τ) = 1 := by
  rw [covol_eq_sqrt_det_gram (tauLattice τ) (tauLatticeBasis τ)]
  have hhy : 0 < τ.im := τ.im_pos
  have hsq : Real.sqrt τ.im ^ 2 = τ.im := Real.sq_sqrt hhy.le
  have hsq_ne : Real.sqrt τ.im ≠ 0 := (Real.sqrt_pos.mpr hhy).ne'
  have hdet : (Matrix.gram ℝ (fun i : Fin 2 =>
      ((tauLatticeBasis τ i : tauLattice τ) : EuclideanSpace ℝ (Fin 2)))).det = 1 := by
    rw [Matrix.det_fin_two]
    simp only [Matrix.gram_apply, tauLatticeBasis_zero, tauLatticeBasis_one,
      PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply, conj_trivial,
      tauVec1, tauVec2, Matrix.cons_val_zero, Matrix.cons_val_one]
    field_simp [hsq_ne]
    rw [hsq]
    ring
  rw [hdet, Real.sqrt_one]

/-- Equivalence between `ℤ × ℤ` and `tauLattice τ`. -/
def intProdEquivTauLattice (τ : UpperHalfPlane) : (ℤ × ℤ) ≃ tauLattice τ where
  toFun p := ⟨tauLatticeMap τ p, tauLatticeMap_mem τ p⟩
  invFun v := ((tauLatticeEquivFin2 τ).symm v 0, (tauLatticeEquivFin2 τ).symm v 1)
  left_inv p := by
    dsimp only
    have h : tauLatticeEquivFin2 τ ![p.1, p.2] = ⟨tauLatticeMap τ p, tauLatticeMap_mem τ p⟩ := rfl
    rw [← h, LinearEquiv.symm_apply_apply]
    rfl
  right_inv v := by
    dsimp only
    exact (tauLatticeEquivFin2 τ).apply_symm_apply v

/-- Equivalence between `{p : ℤ × ℤ // p ≠ (0, 0)}` and `{v : tauLattice τ // (v : ℝ²) ≠ 0}`. -/
def intProdNeZeroEquivTauLattice (τ : UpperHalfPlane) :
    { p : ℤ × ℤ // p ≠ (0, 0) } ≃ { v : tauLattice τ // (v : EuclideanSpace ℝ (Fin 2)) ≠ 0 } where
  toFun p := ⟨intProdEquivTauLattice τ p.1, by
    intro h0
    have hinj : tauLatticeMap τ p.1 = tauLatticeMap τ (0, 0) := by
      simpa [intProdEquivTauLattice, tauLatticeMap] using h0
    exact p.2 (tauLatticeMap_injective τ hinj)⟩
  invFun v := ⟨(intProdEquivTauLattice τ).symm v.1, by
    intro h0
    apply v.2
    have h1 := congrArg Subtype.val ((intProdEquivTauLattice τ).apply_symm_apply v.1)
    rw [h0] at h1
    simpa [intProdEquivTauLattice, tauLatticeMap] using h1.symm⟩
  left_inv p := Subtype.ext ((intProdEquivTauLattice τ).left_inv p.1)
  right_inv v := Subtype.ext ((intProdEquivTauLattice τ).right_inv v.1)

/-- Elementary `cpow` conversion for each Eisenstein term:
`((τ.im : ℂ) / ((‖p.1 * τ + p.2‖ : ℂ) ^ 2)) ^ s = (‖tauLatticeMap τ p‖ : ℂ) ^ (-(2 * s))`. -/
lemma eisensteinTerm_eq_epsteinZeta_term (τ : UpperHalfPlane) (s : ℂ)
    {p : ℤ × ℤ} (hp : p ≠ (0, 0)) :
    ((τ.im : ℂ) / ((‖(p.1 : ℂ) * (τ : ℂ) + (p.2 : ℂ)‖ : ℂ) ^ 2)) ^ s =
      ((‖tauLatticeMap τ p‖ : ℝ) : ℂ) ^ (-(2 * s)) := by
  have hy : 0 < τ.im := τ.im_pos
  have hnorm_pos : 0 < ‖(p.1 : ℂ) * (τ : ℂ) + (p.2 : ℂ)‖ := norm_int_mul_tau_add_pos τ hp
  have hv_sq : ‖tauLatticeMap τ p‖ ^ 2 = ‖(p.1 : ℂ) * (τ : ℂ) + (p.2 : ℂ)‖ ^ 2 / τ.im :=
    norm_sq_tauLatticeMap τ p
  have hv_pos : 0 < ‖tauLatticeMap τ p‖ := by
    have : 0 < ‖tauLatticeMap τ p‖ ^ 2 := by rw [hv_sq]; positivity
    exact (sq_pos_iff.mp this) |> fun h => lt_of_le_of_ne (norm_nonneg _) (Ne.symm h)
  have hbase : (τ.im : ℂ) / ((‖(p.1 : ℂ) * (τ : ℂ) + (p.2 : ℂ)‖ : ℂ) ^ 2) =
      (((‖tauLatticeMap τ p‖ ^ 2 : ℝ)⁻¹ : ℝ) : ℂ) := by
    rw [hv_sq, inv_div, Complex.ofReal_div, Complex.ofReal_pow]
  rw [hbase, ofReal_inv_cpow (sq_pos_of_pos hv_pos) s, ofReal_sq_cpow hv_pos (-s)]
  congr 1; ring

/-! ### Concrete Definitions of `epsteinEisenstein`, `primitiveEisenstein`, & `realEisenstein` -/

/-- **Completed Lattice / Epstein Eisenstein Series** on `UpperHalfPlane`:
$$E_{\mathrm{Ep}}(\tau, s) = \frac{1}{2} \sum_{(c, d) \in \mathbb{Z}^2 \setminus \{(0, 0)\}}
  \left(\frac{\operatorname{Im} \tau}{|c \tau + d|^2}\right)^s.$$ -/
def epsteinEisenstein (τ : UpperHalfPlane) (s : ℂ) : ℂ :=
  (1 / 2 : ℂ) * ∑' p : { p : ℤ × ℤ // p ≠ (0, 0) },
    ((τ.im : ℂ) / ((‖(p.1.1 : ℂ) * (τ : ℂ) + (p.1.2 : ℂ)‖ : ℂ) ^ 2)) ^ s

/-- **Primitive (Coprime) Real-Analytic Eisenstein Series** on `UpperHalfPlane`:
$$E_{\mathrm{prim}}(\tau, s) = \frac{1}{2} \sum_{\substack{(c, d) \in \mathbb{Z}^2 \\ \gcd(c, d) = 1}}
  \left(\frac{\operatorname{Im} \tau}{|c \tau + d|^2}\right)^s.$$ -/
def primitiveEisenstein (τ : UpperHalfPlane) (s : ℂ) : ℂ :=
  (1 / 2 : ℂ) * ∑' p : { p : ℤ × ℤ // IsCoprime p.1 p.2 },
    ((τ.im : ℂ) / ((‖(p.1.1 : ℂ) * (τ : ℂ) + (p.1.2 : ℂ)‖ : ℂ) ^ 2)) ^ s

/-- **Real-Analytic Eisenstein Series `E(τ, s)` on `SL₂(ℤ) \ ℍ`**:
$$E(\tau, s) = \frac{E_{\mathrm{Ep}}(\tau, s)}{\zeta(2 s)}
  = \frac{1}{2} \sum_{\gcd(c, d) = 1} \left(\frac{\operatorname{Im} \tau}{|c \tau + d|^2}\right)^s.$$ -/
def realEisenstein (τ : UpperHalfPlane) (s : ℂ) : ℂ :=
  epsteinEisenstein τ s / riemannZeta (2 * s)

/-- Exact identification with `Stage5ThetaModular.epsteinZeta`:
`epsteinEisenstein τ s = (1 / 2) * epsteinZeta (tauLattice τ) (2 * s)`. -/
theorem epsteinEisenstein_eq_half_epsteinZeta (τ : UpperHalfPlane) (s : ℂ) :
    epsteinEisenstein τ s = (1 / 2 : ℂ) * epsteinZeta (tauLattice τ) (2 * s) := by
  unfold epsteinEisenstein epsteinZeta
  congr 1
  rw [← (intProdNeZeroEquivTauLattice τ).tsum_eq]
  refine tsum_congr fun p => ?_
  exact eisensteinTerm_eq_epsteinZeta_term τ s p.2

/-- **Unconditional Absolute Summability** of the Eisenstein lattice series on `Re(s) > 1`. -/
theorem epsteinEisenstein_summable_norm (τ : UpperHalfPlane) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun p : { p : ℤ × ℤ // p ≠ (0, 0) } =>
      ‖((τ.im : ℂ) / ((‖(p.1.1 : ℂ) * (τ : ℂ) + (p.1.2 : ℂ)‖ : ℂ) ^ 2)) ^ s‖) := by
  have hs2 : (rk (tauLattice τ) : ℝ) < (2 * s).re := by
    rw [rk_tauLattice]; simp; linarith
  have hsum := summable_norm_epsteinZeta (tauLattice τ) hs2
  have heqv := (Equiv.summable_iff (intProdNeZeroEquivTauLattice τ)).mpr hsum
  refine heqv.congr fun p => ?_
  rw [eisensteinTerm_eq_epsteinZeta_term τ s p.2]
  rfl

/-- **Unconditional Summability** of `epsteinEisenstein τ s` on `Re(s) > 1`. -/
theorem epsteinEisenstein_summable (τ : UpperHalfPlane) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun p : { p : ℤ × ℤ // p ≠ (0, 0) } =>
      ((τ.im : ℂ) / ((‖(p.1.1 : ℂ) * (τ : ℂ) + (p.1.2 : ℂ)‖ : ℂ) ^ 2)) ^ s) :=
  (epsteinEisenstein_summable_norm τ hs).of_norm

/-- Positive-integer scaling equivalence for GCD factorization:
`(ℕ+ × {p : ℤ × ℤ // IsCoprime p.1 p.2}) ≃ {p : ℤ × ℤ // p ≠ (0, 0)}`. -/
def gcdFactorEquiv :
    (ℕ+ × { p : ℤ × ℤ // IsCoprime p.1 p.2 }) ≃ { p : ℤ × ℤ // p ≠ (0, 0) } where
  toFun x := ⟨((x.1 : ℤ) * x.2.1.1, (x.1 : ℤ) * x.2.1.2), by
    intro h0
    have h1 : (x.1 : ℤ) * x.2.1.1 = 0 := congrArg Prod.fst h0
    have h2 : (x.1 : ℤ) * x.2.1.2 = 0 := congrArg Prod.snd h0
    have hx1 : (x.1 : ℤ) ≠ 0 := by exact_mod_cast x.1.pos.ne'
    have hp1 : x.2.1.1 = 0 := (mul_eq_zero.mp h1).resolve_left hx1
    have hp2 : x.2.1.2 = 0 := (mul_eq_zero.mp h2).resolve_left hx1
    have hcop := x.2.2
    rw [hp1, hp2] at hcop
    rcases hcop with ⟨a, b, hab⟩
    norm_num at hab⟩
  invFun p :=
    let g : ℕ := Int.gcd p.1.1 p.1.2
    have hg_pos : 0 < g := by
      refine Nat.pos_of_ne_zero fun h0 => p.2 ?_
      have h1 : p.1.1 = 0 := (Int.gcd_eq_zero_iff.mp h0).1
      have h2 : p.1.2 = 0 := (Int.gcd_eq_zero_iff.mp h0).2
      exact Prod.ext h1 h2
    (⟨g, hg_pos⟩,
     ⟨(p.1.1 / (g : ℤ), p.1.2 / (g : ℤ)), by
       rw [Int.isCoprime_iff_gcd_eq_one]
       have hd1 : (g : ℤ) ∣ p.1.1 := Int.gcd_dvd_left p.1.1 p.1.2
       have hd2 : (g : ℤ) ∣ p.1.2 := Int.gcd_dvd_right p.1.1 p.1.2
       have hmul : g * Int.gcd (p.1.1 / (g : ℤ)) (p.1.2 / (g : ℤ)) = g := by
         calc g * Int.gcd (p.1.1 / (g : ℤ)) (p.1.2 / (g : ℤ))
             = Int.gcd ((g : ℤ) * (p.1.1 / (g : ℤ))) ((g : ℤ) * (p.1.2 / (g : ℤ))) := by
                 rw [Int.gcd_mul_left, Int.natAbs_natCast]
           _ = Int.gcd p.1.1 p.1.2 := by
                 rw [Int.mul_ediv_cancel' hd1, Int.mul_ediv_cancel' hd2]
           _ = g := rfl
       exact Nat.eq_of_mul_eq_mul_left hg_pos (by simpa using hmul)⟩)
  left_inv x := by
    rcases x with ⟨d, ⟨⟨c, e⟩, hcop⟩⟩
    have hg : Int.gcd ((d : ℤ) * c) ((d : ℤ) * e) = (d : ℕ) := by
      rw [Int.gcd_mul_left, Int.natAbs_natCast, Int.isCoprime_iff_gcd_eq_one.mp hcop, mul_one]
    have hd_ne : (d : ℤ) ≠ 0 := by exact_mod_cast d.pos.ne'
    apply Prod.ext
    · apply Subtype.ext; exact hg
    · apply Subtype.ext; apply Prod.ext
      · dsimp only; rw [hg, Int.mul_ediv_cancel_left c hd_ne]
      · dsimp only; rw [hg, Int.mul_ediv_cancel_left e hd_ne]
  right_inv p := by
    apply Subtype.ext
    dsimp only
    exact Prod.ext
      (Int.mul_ediv_cancel' (Int.gcd_dvd_left p.1.1 p.1.2))
      (Int.mul_ediv_cancel' (Int.gcd_dvd_right p.1.1 p.1.2))

/-- Canonical equivalence `ℕ ≃ ℕ+`. -/
def natEquivPNat : ℕ ≃ ℕ+ where
  toFun n := ⟨n + 1, Nat.succ_pos n⟩
  invFun d := d.1 - 1
  left_inv n := Nat.add_sub_cancel n 1
  right_inv d := Subtype.ext (Nat.sub_add_cancel d.2)

/-- Exact GCD factorization: for `Re(s) > 1`,
`epsteinEisenstein τ s = riemannZeta (2 * s) * primitiveEisenstein τ s`. -/
theorem epsteinEisenstein_eq_zeta_mul_primitiveEisenstein (τ : UpperHalfPlane)
    {s : ℂ} (hs : 1 < s.re) :
    epsteinEisenstein τ s = riemannZeta (2 * s) * primitiveEisenstein τ s := by
  have hs2 : 1 < (2 * s).re := by simp; linarith
  have hzeta : riemannZeta (2 * s) = ∑' d : ℕ+, ((d : ℕ) : ℂ) ^ (-(2 * s)) := by
    rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs2, ← natEquivPNat.tsum_eq]
    refine tsum_congr fun n => ?_
    rw [one_div, Complex.cpow_neg]
    change (((n : ℂ) + 1) ^ (2 * s))⁻¹ = (((n + 1 : ℕ) : ℂ) ^ (2 * s))⁻¹
    push_cast; rfl
  have hsum_d_norm : Summable (fun d : ℕ+ => ‖((d : ℕ) : ℂ) ^ (-(2 * s))‖) := by
    have hnat : Summable (fun n : ℕ => (((n + 1 : ℕ) : ℝ) ^ (2 * s).re)⁻¹) :=
      (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow_inv.mpr hs2)
    refine (Equiv.summable_iff natEquivPNat).mp (hnat.congr fun n => ?_)
    have hpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    change (((n + 1 : ℕ) : ℝ) ^ (2 * s).re)⁻¹ = ‖(((n + 1 : ℕ) : ℂ)) ^ (-(2 * s))‖
    rw [show (((n + 1 : ℕ) : ℂ)) = ((((n + 1 : ℕ) : ℝ)) : ℂ) by push_cast; rfl,
      Complex.norm_cpow_eq_rpow_re_of_pos hpos, Complex.neg_re, Real.rpow_neg hpos.le]
  have hsum_p_norm : Summable (fun p : { p : ℤ × ℤ // IsCoprime p.1 p.2 } =>
      ‖((τ.im : ℂ) / ((‖(p.1.1 : ℂ) * (τ : ℂ) + (p.1.2 : ℂ)‖ : ℂ) ^ 2)) ^ s‖) := by
    have hfull := epsteinEisenstein_summable_norm τ hs
    let incl : { p : ℤ × ℤ // IsCoprime p.1 p.2 } → { p : ℤ × ℤ // p ≠ (0, 0) } :=
      fun p => gcdFactorEquiv (1, p)
    have hinj : Function.Injective incl := fun p q h =>
      congrArg Prod.snd (gcdFactorEquiv.injective h)
    refine (hfull.comp_injective hinj).congr fun p => ?_
    simp [incl, gcdFactorEquiv]
  have hterm_split : ∀ x : ℕ+ × { p : ℤ × ℤ // IsCoprime p.1 p.2 },
      ((τ.im : ℂ) / ((‖(((gcdFactorEquiv x).1.1 : ℂ) * (τ : ℂ) + ((gcdFactorEquiv x).1.2 : ℂ))‖ : ℂ) ^ 2)) ^ s =
        ((x.1 : ℕ) : ℂ) ^ (-(2 * s)) *
          ((τ.im : ℂ) / ((‖(x.2.1.1 : ℂ) * (τ : ℂ) + (x.2.1.2 : ℂ)‖ : ℂ) ^ 2)) ^ s := by
    rintro ⟨d, ⟨⟨c, e⟩, hcop⟩⟩
    have hd_pos : (0 : ℝ) < (d : ℕ) := by exact_mod_cast d.pos
    have hp_ne : (c, e) ≠ (0, 0) := by
      intro h0
      have hc : c = 0 := congrArg Prod.fst h0
      have he : e = 0 := congrArg Prod.snd h0
      rw [hc, he] at hcop
      rcases hcop with ⟨a, b, hab⟩; norm_num at hab
    have hnorm_pos : 0 < ‖(c : ℂ) * (τ : ℂ) + (e : ℂ)‖ := norm_int_mul_tau_add_pos τ hp_ne
    have hmul_norm : ‖(((d : ℤ) * c : ℤ) : ℂ) * (τ : ℂ) + (((d : ℤ) * e : ℤ) : ℂ)‖ =
        ((d : ℕ) : ℝ) * ‖(c : ℂ) * (τ : ℂ) + (e : ℂ)‖ := by
      have h1 : (((d : ℤ) * c : ℤ) : ℂ) * (τ : ℂ) + (((d : ℤ) * e : ℤ) : ℂ) =
          (((d : ℕ) : ℝ) : ℂ) * ((c : ℂ) * (τ : ℂ) + (e : ℂ)) := by push_cast; ring
      rw [h1, norm_mul, Complex.norm_real, Real.norm_of_nonneg hd_pos.le]
    dsimp only [gcdFactorEquiv, Equiv.coe_fn_mk]
    rw [hmul_norm]
    have hbase : (τ.im : ℂ) / (((((d : ℕ) : ℝ) * ‖(c : ℂ) * (τ : ℂ) + (e : ℂ)‖ : ℝ) : ℂ) ^ 2) =
        ((((((d : ℕ) : ℝ) ^ 2)⁻¹ * (τ.im / ‖(c : ℂ) * (τ : ℂ) + (e : ℂ)‖ ^ 2) : ℝ) : ℂ)) := by
      push_cast
      have hdC : ((d : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr d.pos.ne'
      have hnC : (‖(c : ℂ) * (τ : ℂ) + (e : ℂ)‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hnorm_pos.ne'
      field_simp [hdC, hnC]
    rw [hbase, ofReal_mul_cpow (inv_pos.mpr (sq_pos_of_pos hd_pos))
      (div_pos τ.im_pos (sq_pos_of_pos hnorm_pos)) s,
      ofReal_inv_cpow (sq_pos_of_pos hd_pos) s, ofReal_sq_cpow hd_pos (-s)]
    have hexp : 2 * (-s) = -(2 * s) := by ring
    rw [hexp, Complex.ofReal_div, Complex.ofReal_pow]
    push_cast; rfl
  have hprod_sum : Summable (fun x : ℕ+ × { p : ℤ × ℤ // IsCoprime p.1 p.2 } =>
      ((x.1 : ℕ) : ℂ) ^ (-(2 * s)) *
        ((τ.im : ℂ) / ((‖(x.2.1.1 : ℂ) * (τ : ℂ) + (x.2.1.2 : ℂ)‖ : ℂ) ^ 2)) ^ s) :=
    ((Summable.mul_of_nonneg hsum_d_norm hsum_p_norm (fun _ => norm_nonneg _)
      (fun _ => norm_nonneg _)).congr fun x => (norm_mul _ _).symm).of_norm
  unfold epsteinEisenstein primitiveEisenstein
  rw [← gcdFactorEquiv.tsum_eq]
  simp_rw [hterm_split]
  rw [← hsum_d_norm.of_norm.tsum_mul_tsum hsum_p_norm.of_norm hprod_sum, ← hzeta]
  ring

/-- **Exact Factorization `epsteinEisenstein τ s = riemannZeta (2 * s) * realEisenstein τ s`**
for all `Re(s) > 1`. -/
theorem epsteinEisenstein_eq_zeta_mul_realEisenstein (τ : UpperHalfPlane)
    {s : ℂ} (hs : 1 < s.re) :
    epsteinEisenstein τ s = riemannZeta (2 * s) * realEisenstein τ s := by
  have hz : riemannZeta (2 * s) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by simp; linarith)
  unfold realEisenstein
  exact (mul_div_cancel₀ _ hz).symm

/-- **Exact Identification `realEisenstein τ s = primitiveEisenstein τ s`** on `Re(s) > 1`. -/
theorem realEisenstein_eq_primitiveEisenstein (τ : UpperHalfPlane)
    {s : ℂ} (hs : 1 < s.re) :
    realEisenstein τ s = primitiveEisenstein τ s := by
  have hz : riemannZeta (2 * s) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by simp; linarith)
  unfold realEisenstein
  rw [epsteinEisenstein_eq_zeta_mul_primitiveEisenstein τ hs, mul_div_cancel_left₀ _ hz]

/-! ### Exact `SL₂(ℤ)`-Invariance of `epsteinEisenstein` and `realEisenstein` -/

/-- Right-multiplication of a row vector `(m, n) ∈ ℤ²` by `γ ∈ SL₂(ℤ)`. -/
def sl2ZRowAction (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (p : ℤ × ℤ) : ℤ × ℤ :=
  (p.1 * γ 0 0 + p.2 * γ 1 0, p.1 * γ 0 1 + p.2 * γ 1 1)

/-- `sl2ZRowAction γ` is a bijection on `ℤ × ℤ` (with inverse `sl2ZRowAction γ⁻¹`). -/
def sl2ZRowEquiv (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : (ℤ × ℤ) ≃ (ℤ × ℤ) where
  toFun := sl2ZRowAction γ
  invFun := sl2ZRowAction γ⁻¹
  left_inv p := by
    have hmul : (γ : Matrix (Fin 2) (Fin 2) ℤ) * ((γ⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
    have h00 : γ 0 0 * (γ⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℤ) 0 0 +
        γ 0 1 * (γ⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℤ) 1 0 = 1 := by
      have := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M 0 0) hmul
      simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
    have h01 : γ 0 0 * (γ⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℤ) 0 1 +
        γ 0 1 * (γ⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℤ) 1 1 = 0 := by
      have := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M 0 1) hmul
      simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
    have h10 : γ 1 0 * (γ⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℤ) 0 0 +
        γ 1 1 * (γ⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℤ) 1 0 = 0 := by
      have := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M 1 0) hmul
      simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
    have h11 : γ 1 0 * (γ⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℤ) 0 1 +
        γ 1 1 * (γ⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℤ) 1 1 = 1 := by
      have := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M 1 1) hmul
      simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
    apply Prod.ext <;> dsimp only [sl2ZRowAction]
    · linear_combination p.1 * h00 + p.2 * h10
    · linear_combination p.1 * h01 + p.2 * h11
  right_inv p := by
    have hmul : ((γ⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) * (γ : Matrix (Fin 2) (Fin 2) ℤ) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
    have h00 : (γ⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℤ) 0 0 * γ 0 0 +
        (γ⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℤ) 0 1 * γ 1 0 = 1 := by
      have := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M 0 0) hmul
      simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
    have h01 : (γ⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℤ) 0 0 * γ 0 1 +
        (γ⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℤ) 0 1 * γ 1 1 = 0 := by
      have := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M 0 1) hmul
      simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
    have h10 : (γ⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℤ) 1 0 * γ 0 0 +
        (γ⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℤ) 1 1 * γ 1 0 = 0 := by
      have := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M 1 0) hmul
      simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
    have h11 : (γ⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℤ) 1 0 * γ 0 1 +
        (γ⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℤ) 1 1 * γ 1 1 = 1 := by
      have := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M 1 1) hmul
      simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
    apply Prod.ext <;> dsimp only [sl2ZRowAction]
    · linear_combination p.1 * h00 + p.2 * h10
    · linear_combination p.1 * h01 + p.2 * h11

lemma sl2ZRowAction_zero (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    sl2ZRowAction γ (0, 0) = (0, 0) := by
  simp [sl2ZRowAction]

/-- Bijection on `{p : ℤ × ℤ // p ≠ (0, 0)}` induced by `γ ∈ SL₂(ℤ)`. -/
def sl2ZRowEquivNeZero (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    { p : ℤ × ℤ // p ≠ (0, 0) } ≃ { p : ℤ × ℤ // p ≠ (0, 0) } where
  toFun p := ⟨sl2ZRowAction γ p.1, fun h0 =>
    p.2 ((sl2ZRowEquiv γ).injective (h0.trans (sl2ZRowAction_zero γ).symm))⟩
  invFun p := ⟨sl2ZRowAction γ⁻¹ p.1, fun h0 =>
    p.2 ((sl2ZRowEquiv γ).symm.injective (h0.trans (sl2ZRowAction_zero γ⁻¹).symm))⟩
  left_inv p := Subtype.ext ((sl2ZRowEquiv γ).left_inv p.1)
  right_inv p := Subtype.ext ((sl2ZRowEquiv γ).right_inv p.1)

/-- Key Möbius-action cocycle identity for `γ ∈ SL₂(ℤ)` and `p ∈ ℤ²`:
`Im(γ • τ) / ‖p.1 * (γ • τ) + p.2‖² = Im(τ) / ‖(sl2ZRowAction γ p).1 * τ + (sl2ZRowAction γ p).2‖²`. -/
lemma im_div_norm_sq_SL2Z_smul (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (τ : UpperHalfPlane) (p : ℤ × ℤ) :
    (γ • τ).im / ‖(p.1 : ℂ) * ((γ • τ : UpperHalfPlane) : ℂ) + (p.2 : ℂ)‖ ^ 2 =
      τ.im / ‖((sl2ZRowAction γ p).1 : ℂ) * (τ : ℂ) + ((sl2ZRowAction γ p).2 : ℂ)‖ ^ 2 := by
  have hdenom_ne : UpperHalfPlane.denom γ τ ≠ 0 := UpperHalfPlane.denom_ne_zero γ τ
  have hnum_eq : UpperHalfPlane.num γ τ = (γ 0 0 : ℂ) * (τ : ℂ) + (γ 0 1 : ℂ) := by
    simp [UpperHalfPlane.num]
  have hden_eq : UpperHalfPlane.denom γ τ = (γ 1 0 : ℂ) * (τ : ℂ) + (γ 1 1 : ℂ) := by
    simp [UpperHalfPlane.denom]
  have hcoe : ((γ • τ : UpperHalfPlane) : ℂ) =
      ((γ 0 0 : ℂ) * (τ : ℂ) + (γ 0 1 : ℂ)) / ((γ 1 0 : ℂ) * (τ : ℂ) + (γ 1 1 : ℂ)) := by
    have h := congrArg (fun z : UpperHalfPlane => (z : ℂ)) (UpperHalfPlane.specialLinearGroup_apply γ τ)
    simpa using h
  have him : (γ • τ).im = τ.im / ‖UpperHalfPlane.denom γ τ‖ ^ 2 := by
    rw [ModularGroup.im_smul_eq_div_normSq, Complex.normSq_eq_norm_sq]
  have hden' : (γ 1 0 : ℂ) * (τ : ℂ) + (γ 1 1 : ℂ) ≠ 0 := by rwa [← hden_eq]
  have hlin : (p.1 : ℂ) * ((γ • τ : UpperHalfPlane) : ℂ) + (p.2 : ℂ) =
      (((sl2ZRowAction γ p).1 : ℂ) * (τ : ℂ) + ((sl2ZRowAction γ p).2 : ℂ)) /
        UpperHalfPlane.denom γ τ := by
    rw [hcoe, hden_eq, eq_div_iff hden', add_mul, mul_assoc, div_mul_cancel₀ _ hden']
    simp only [sl2ZRowAction]
    push_cast
    ring
  rw [him, hlin, norm_div, div_pow]
  have hd_pos : 0 < ‖UpperHalfPlane.denom γ τ‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hdenom_ne)
  field_simp [hd_pos.ne']

/-- **Exact `SL₂(ℤ)`-Invariance of `epsteinEisenstein`** (for ALL `τ ∈ ℍ`, `s ∈ ℂ`, `γ ∈ SL₂(ℤ)`). -/
theorem epsteinEisenstein_SL2Z_invariant (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (τ : UpperHalfPlane) (s : ℂ) :
    epsteinEisenstein (γ • τ) s = epsteinEisenstein τ s := by
  unfold epsteinEisenstein
  congr 1
  calc (∑' p : { p : ℤ × ℤ // p ≠ (0, 0) },
          (((γ • τ).im : ℂ) / ((‖(p.1.1 : ℂ) * ((γ • τ : UpperHalfPlane) : ℂ) + (p.1.2 : ℂ)‖ : ℂ) ^ 2)) ^ s)
      = ∑' p : { p : ℤ × ℤ // p ≠ (0, 0) },
          ((τ.im : ℂ) / ((‖(((sl2ZRowEquivNeZero γ p).1.1 : ℂ) * (τ : ℂ) + ((sl2ZRowEquivNeZero γ p).1.2 : ℂ))‖ : ℂ) ^ 2)) ^ s := by
          refine tsum_congr fun p => ?_
          have h := congrArg (fun r : ℝ => (r : ℂ)) (im_div_norm_sq_SL2Z_smul γ τ p.1)
          simp only [Complex.ofReal_div, Complex.ofReal_pow] at h
          dsimp only [sl2ZRowEquivNeZero, Equiv.coe_fn_mk]
          rw [h]
    _ = ∑' p : { p : ℤ × ℤ // p ≠ (0, 0) },
          ((τ.im : ℂ) / ((‖(p.1.1 : ℂ) * (τ : ℂ) + (p.1.2 : ℂ)‖ : ℂ) ^ 2)) ^ s :=
          (sl2ZRowEquivNeZero γ).tsum_eq (fun p : { p : ℤ × ℤ // p ≠ (0, 0) } =>
            ((τ.im : ℂ) / ((‖(p.1.1 : ℂ) * (τ : ℂ) + (p.1.2 : ℂ)‖ : ℂ) ^ 2)) ^ s)

/-- **Exact `SL₂(ℤ)`-Invariance of `realEisenstein`**:
`∀ γ ∈ SL₂(ℤ), realEisenstein (γ • τ) s = realEisenstein τ s`. -/
theorem realEisenstein_SL2Z_invariant (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (τ : UpperHalfPlane) (s : ℂ) :
    realEisenstein (γ • τ) s = realEisenstein τ s := by
  unfold realEisenstein
  rw [epsteinEisenstein_SL2Z_invariant]

end RealAnalyticEisenstein

/-! ## Section 2: Concrete Hyperbolic Laplacian `Δ_ℍ` & Eigenvalue Equation `Δ_ℍ E(τ, s) = s(1 - s) E(τ, s)` -/

section HyperbolicLaplacian

/-- Horizontal slice `x ↦ f(x + i y)` via `UpperHalfPlane.ofComplex`. -/
def uhpSliceX (f : UpperHalfPlane → ℂ) (y : ℝ) (x : ℝ) : ℂ :=
  f (UpperHalfPlane.ofComplex ((x : ℂ) + Complex.I * (y : ℂ)))

/-- Vertical slice `y ↦ f(x + i y)` via `UpperHalfPlane.ofComplex`. -/
def uhpSliceY (f : UpperHalfPlane → ℂ) (x : ℝ) (y : ℝ) : ℂ :=
  f (UpperHalfPlane.ofComplex ((x : ℂ) + Complex.I * (y : ℂ)))

/-- Second partial derivative `∂²f/∂x²` on `UpperHalfPlane`. -/
def partialXX (f : UpperHalfPlane → ℂ) (τ : UpperHalfPlane) : ℂ :=
  deriv (fun x : ℝ => deriv (uhpSliceX f τ.im) x) τ.re

/-- Second partial derivative `∂²f/∂y²` on `UpperHalfPlane`. -/
def partialYY (f : UpperHalfPlane → ℂ) (τ : UpperHalfPlane) : ℂ :=
  deriv (fun y : ℝ => deriv (uhpSliceY f τ.re) y) τ.im

/-- **Concrete Hyperbolic Laplacian on `ℍ`**:
$$\Delta_{\mathbb{H}} f(\tau) = -y^2 \left(\frac{\partial^2 f}{\partial x^2} +
  \frac{\partial^2 f}{\partial y^2}\right), \qquad \tau = x + i y.$$ -/
def hypLaplacian (f : UpperHalfPlane → ℂ) (τ : UpperHalfPlane) : ℂ :=
  -((τ.im : ℂ) ^ 2) * (partialXX f τ + partialYY f τ)

lemma ofComplex_re_add_I_im_eq {x y : ℝ} (hy : 0 < y) :
    ((UpperHalfPlane.ofComplex ((x : ℂ) + Complex.I * (y : ℂ)) : UpperHalfPlane) : ℂ) =
      (x : ℂ) + Complex.I * (y : ℂ) := by
  have him : 0 < ((x : ℂ) + Complex.I * (y : ℂ)).im := by simp [hy]
  rw [UpperHalfPlane.ofComplex_apply_of_im_pos him]

lemma ofComplex_im_eq {x y : ℝ} (hy : 0 < y) :
    (UpperHalfPlane.ofComplex ((x : ℂ) + Complex.I * (y : ℂ))).im = y := by
  have h := ofComplex_re_add_I_im_eq (x := x) hy
  have := congrArg Complex.im h
  simpa using this

lemma ofComplex_self (τ : UpperHalfPlane) :
    UpperHalfPlane.ofComplex ((τ.re : ℂ) + Complex.I * (τ.im : ℂ)) = τ := by
  apply UpperHalfPlane.ext
  rw [ofComplex_re_add_I_im_eq τ.im_pos, mul_comm Complex.I]
  exact Complex.re_add_im (τ : ℂ)

/-- Derivative of `t ↦ (t : ℂ) ^ w` at any `t > 0`. -/
lemma hasDerivAt_ofReal_cpow {t : ℝ} (ht : 0 < t) (w : ℂ) :
    HasDerivAt (fun u : ℝ => (u : ℂ) ^ w) (w * (t : ℂ) ^ (w - 1)) t := by
  have hslit : (t : ℂ) ∈ Complex.slitPlane := Or.inl (by simpa using ht)
  have hc := (HasDerivAt.cpow_const (hasDerivAt_id (t : ℂ)) (c := w) hslit).comp_ofReal
  simpa [mul_comm] using hc

/-- **Hyperbolic Laplacian Eigenvalue on `τ ↦ Im(τ)^s`**:
`hypLaplacian (fun τ => (τ.im : ℂ) ^ s) τ = s * (1 - s) * (τ.im : ℂ) ^ s`. -/
theorem hypLaplacian_im_rpow (τ : UpperHalfPlane) (s : ℂ) :
    hypLaplacian (fun τ => (τ.im : ℂ) ^ s) τ = s * (1 - s) * (τ.im : ℂ) ^ s := by
  have hy : 0 < τ.im := τ.im_pos
  have hyC : (τ.im : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
  have hxx : partialXX (fun τ => (τ.im : ℂ) ^ s) τ = 0 := by
    unfold partialXX
    have hconst : uhpSliceX (fun τ => (τ.im : ℂ) ^ s) τ.im = fun _ => (τ.im : ℂ) ^ s := by
      funext x; unfold uhpSliceX; dsimp only; rw [ofComplex_im_eq hy]
    rw [hconst]
    simp only [deriv_const]
  have hyy : partialYY (fun τ => (τ.im : ℂ) ^ s) τ = s * (s - 1) * (τ.im : ℂ) ^ (s - 2) := by
    unfold partialYY
    have hd1 : (fun y : ℝ => deriv (uhpSliceY (fun τ => (τ.im : ℂ) ^ s) τ.re) y) =ᶠ[nhds τ.im]
        fun y : ℝ => s * (y : ℂ) ^ (s - 1) := by
      filter_upwards [isOpen_Ioi.mem_nhds hy] with y hy0
      have hev : uhpSliceY (fun τ => (τ.im : ℂ) ^ s) τ.re =ᶠ[nhds y] fun u : ℝ => (u : ℂ) ^ s := by
        filter_upwards [isOpen_Ioi.mem_nhds hy0] with u hu
        unfold uhpSliceY; dsimp only; rw [ofComplex_im_eq hu]
      rw [hev.deriv_eq]
      exact (hasDerivAt_ofReal_cpow hy0 s).deriv
    rw [hd1.deriv_eq]
    have hd2 : HasDerivAt (fun y : ℝ => s * (y : ℂ) ^ (s - 1))
        (s * ((s - 1) * (τ.im : ℂ) ^ (s - 1 - 1))) τ.im :=
      (hasDerivAt_ofReal_cpow hy (s - 1)).const_mul s
    rw [hd2.deriv]
    have hexp : s - 1 - 1 = s - 2 := by ring
    rw [hexp]; ring
  unfold hypLaplacian
  rw [hxx, hyy, zero_add]
  have hpow : (τ.im : ℂ) ^ (s - 2) = (τ.im : ℂ) ^ s * ((τ.im : ℂ) ^ 2)⁻¹ := by
    rw [Complex.cpow_sub _ _ hyC, div_eq_mul_inv, Complex.cpow_ofNat]
  rw [hpow]
  field_simp [hyC]
  ring

/-! ### Explicit Partial Derivatives of Each Eisenstein Term `(y / ((c x + d)² + (c y)²))^s` -/

private def quadQ (c d x y : ℝ) : ℝ := (c * x + d) ^ 2 + (c * y) ^ 2
private def quadQx (c d x : ℝ) : ℝ := 2 * c * (c * x + d)
private def quadQy (c y : ℝ) : ℝ := 2 * c ^ 2 * y
private def quadQ2 (c : ℝ) : ℝ := 2 * c ^ 2

private lemma quadQ_pos {c d x y : ℝ} (hy : 0 < y) (hcd : (c, d) ≠ (0, 0)) :
    0 < quadQ c d x y := by
  unfold quadQ
  by_cases hc : c = 0
  · subst hc
    have hd : d ≠ 0 := fun h => hcd (Prod.ext rfl h)
    have : 0 < d ^ 2 := sq_pos_of_ne_zero hd
    simpa using this
  · have : 0 < (c * y) ^ 2 := sq_pos_of_ne_zero (mul_ne_zero hc hy.ne')
    linarith [sq_nonneg (c * x + d)]

private def termFun (c d : ℝ) (s : ℂ) (x y : ℝ) : ℂ :=
  (y : ℂ) ^ s * (quadQ c d x y : ℂ) ^ (-s)

private def termDx (c d : ℝ) (s : ℂ) (x y : ℝ) : ℂ :=
  (y : ℂ) ^ s * (-s * (quadQ c d x y : ℂ) ^ (-s - 1) * (quadQx c d x : ℂ))

private def termDxx (c d : ℝ) (s : ℂ) (x y : ℝ) : ℂ :=
  (y : ℂ) ^ s *
    (s * (s + 1) * (quadQ c d x y : ℂ) ^ (-s - 2) * (quadQx c d x : ℂ) ^ 2 -
      s * (quadQ c d x y : ℂ) ^ (-s - 1) * (quadQ2 c : ℂ))

private def termDy (c d : ℝ) (s : ℂ) (x y : ℝ) : ℂ :=
  s * (y : ℂ) ^ (s - 1) * (quadQ c d x y : ℂ) ^ (-s) +
    (y : ℂ) ^ s * (-s * (quadQ c d x y : ℂ) ^ (-s - 1) * (quadQy c y : ℂ))

private def termDyy (c d : ℝ) (s : ℂ) (x y : ℝ) : ℂ :=
  s * (s - 1) * (y : ℂ) ^ (s - 2) * (quadQ c d x y : ℂ) ^ (-s) +
    2 * s * (y : ℂ) ^ (s - 1) * (-s * (quadQ c d x y : ℂ) ^ (-s - 1) * (quadQy c y : ℂ)) +
    (y : ℂ) ^ s *
      (s * (s + 1) * (quadQ c d x y : ℂ) ^ (-s - 2) * (quadQy c y : ℂ) ^ 2 -
        s * (quadQ c d x y : ℂ) ^ (-s - 1) * (quadQ2 c : ℂ))

private lemma hasDerivAt_quadQ_real_x (c d x y : ℝ) :
    HasDerivAt (fun u : ℝ => quadQ c d u y) (quadQx c d x) x := by
  unfold quadQ quadQx
  have h1 : HasDerivAt (fun u : ℝ => c * u + d) c x := by
    simpa using ((hasDerivAt_id x).const_mul c).add_const d
  have h2 : HasDerivAt (fun u : ℝ => (c * u + d) ^ 2) (2 * (c * x + d) * c) x := by
    simpa [pow_one] using h1.fun_pow 2
  refine (h2.add_const ((c * y) ^ 2)).congr_deriv ?_; ring

private lemma hasDerivAt_quadQ_real_y (c d x y : ℝ) :
    HasDerivAt (fun v : ℝ => quadQ c d x v) (quadQy c y) y := by
  unfold quadQ quadQy
  have h1 : HasDerivAt (fun v : ℝ => c * v) c y := by
    simpa using (hasDerivAt_id y).const_mul c
  have h2 : HasDerivAt (fun v : ℝ => (c * v) ^ 2) (2 * (c * y) * c) y := by
    simpa [pow_one] using h1.fun_pow 2
  refine (h2.const_add ((c * x + d) ^ 2)).congr_deriv ?_; ring

private lemma hasDerivAt_quadQ_cpow_x (c d x y : ℝ) (hy : 0 < y) (hcd : (c, d) ≠ (0, 0)) (w : ℂ) :
    HasDerivAt (fun u : ℝ => (quadQ c d u y : ℂ) ^ w)
      (w * (quadQ c d x y : ℂ) ^ (w - 1) * (quadQx c d x : ℂ)) x := by
  have hQ : 0 < quadQ c d x y := quadQ_pos hy hcd
  have h := (hasDerivAt_ofReal_cpow hQ w).scomp x (hasDerivAt_quadQ_real_x c d x y)
  simpa [Function.comp_def, Complex.real_smul, mul_comm, mul_left_comm, mul_assoc] using h

private lemma hasDerivAt_quadQ_cpow_y (c d x y : ℝ) (hy : 0 < y) (hcd : (c, d) ≠ (0, 0)) (w : ℂ) :
    HasDerivAt (fun v : ℝ => (quadQ c d x v : ℂ) ^ w)
      (w * (quadQ c d x y : ℂ) ^ (w - 1) * (quadQy c y : ℂ)) y := by
  have hQ : 0 < quadQ c d x y := quadQ_pos hy hcd
  have h := (hasDerivAt_ofReal_cpow hQ w).scomp y (hasDerivAt_quadQ_real_y c d x y)
  simpa [Function.comp_def, Complex.real_smul, mul_comm, mul_left_comm, mul_assoc] using h

private lemma hasDerivAt_termFun_x {c d x y : ℝ} (hy : 0 < y) (hcd : (c, d) ≠ (0, 0)) (s : ℂ) :
    HasDerivAt (fun u : ℝ => termFun c d s u y) (termDx c d s x y) x :=
  (hasDerivAt_quadQ_cpow_x c d x y hy hcd (-s)).const_mul ((y : ℂ) ^ s)

private lemma hasDerivAt_termDx_x {c d x y : ℝ} (hy : 0 < y) (hcd : (c, d) ≠ (0, 0)) (s : ℂ) :
    HasDerivAt (fun u : ℝ => termDx c d s u y) (termDxx c d s x y) x := by
  have hqx : HasDerivAt (fun u : ℝ => (quadQx c d u : ℂ)) (quadQ2 c : ℂ) x := by
    have hR : HasDerivAt (fun u : ℝ => quadQx c d u) (quadQ2 c) x := by
      unfold quadQx quadQ2
      have h1 : HasDerivAt (fun u : ℝ => c * u + d) c x := by
        simpa using ((hasDerivAt_id x).const_mul c).add_const d
      refine (h1.const_mul (2 * c)).congr_deriv ?_; ring
    exact hR.ofReal_comp
  have hp := (hasDerivAt_quadQ_cpow_x c d x y hy hcd (-s - 1)).const_mul (-s)
  have hmul := (hp.mul hqx).const_mul ((y : ℂ) ^ s)
  refine hmul.congr_deriv ?_
  unfold termDxx
  have hexp : -s - 1 - 1 = -s - 2 := by ring
  rw [hexp]; ring

private lemma hasDerivAt_termFun_y {c d x y : ℝ} (hy : 0 < y) (hcd : (c, d) ≠ (0, 0)) (s : ℂ) :
    HasDerivAt (fun v : ℝ => termFun c d s x v) (termDy c d s x y) y := by
  have h1 := hasDerivAt_ofReal_cpow hy s
  have h2 := hasDerivAt_quadQ_cpow_y c d x y hy hcd (-s)
  refine (h1.mul h2).congr_deriv ?_
  unfold termDy; ring

private lemma hasDerivAt_termDy_y {c d x y : ℝ} (hy : 0 < y) (hcd : (c, d) ≠ (0, 0)) (s : ℂ) :
    HasDerivAt (fun v : ℝ => termDy c d s x v) (termDyy c d s x y) y := by
  have hqy : HasDerivAt (fun v : ℝ => (quadQy c v : ℂ)) (quadQ2 c : ℂ) y := by
    have hR : HasDerivAt (fun v : ℝ => quadQy c v) (quadQ2 c) y := by
      unfold quadQy quadQ2
      simpa using (hasDerivAt_id y).const_mul (2 * c ^ 2)
    exact hR.ofReal_comp
  have hA1 : HasDerivAt (fun v : ℝ => s * (v : ℂ) ^ (s - 1))
      (s * ((s - 1) * (y : ℂ) ^ (s - 1 - 1))) y :=
    (hasDerivAt_ofReal_cpow hy (s - 1)).const_mul s
  have hA2 := hasDerivAt_quadQ_cpow_y c d x y hy hcd (-s)
  have hA := hA1.mul hA2
  have hB1 := hasDerivAt_ofReal_cpow hy s
  have hB2a := (hasDerivAt_quadQ_cpow_y c d x y hy hcd (-s - 1)).const_mul (-s)
  have hB2 := hB2a.mul hqy
  have hB := hB1.mul hB2
  refine (hA.add hB).congr_deriv ?_
  unfold termDyy
  dsimp only [Pi.mul_apply]
  have hexp1 : s - 1 - 1 = s - 2 := by ring
  have hexp2 : -s - 1 - 1 = -s - 2 := by ring
  rw [hexp1, hexp2]; ring

/-- **Exact Algebraic Eigenvalue Cancellation for Every Individual Term**:
`-y² (termDxx + termDyy) = s (1 - s) termFun`. -/
private lemma termDxx_add_termDyy_eigenvalue {c d x y : ℝ} (hy : 0 < y) (hcd : (c, d) ≠ (0, 0))
    (s : ℂ) :
    -((y : ℂ) ^ 2) * (termDxx c d s x y + termDyy c d s x y) =
      s * (1 - s) * termFun c d s x y := by
  have hQ : 0 < quadQ c d x y := quadQ_pos hy hcd
  have hyC : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
  have hQC : (quadQ c d x y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hQ.ne'
  have hy1 : (y : ℂ) ^ (s - 1) = (y : ℂ) ^ s * (y : ℂ)⁻¹ := by
    rw [Complex.cpow_sub _ _ hyC, div_eq_mul_inv, Complex.cpow_one]
  have hy2 : (y : ℂ) ^ (s - 2) = (y : ℂ) ^ s * ((y : ℂ) ^ 2)⁻¹ := by
    rw [Complex.cpow_sub _ _ hyC, div_eq_mul_inv, Complex.cpow_ofNat]
  have hQ1 : (quadQ c d x y : ℂ) ^ (-s - 1) = (quadQ c d x y : ℂ) ^ (-s) * (quadQ c d x y : ℂ)⁻¹ := by
    rw [Complex.cpow_sub _ _ hQC, div_eq_mul_inv, Complex.cpow_one]
  have hQ2 : (quadQ c d x y : ℂ) ^ (-s - 2) =
      (quadQ c d x y : ℂ) ^ (-s) * ((quadQ c d x y : ℂ) ^ 2)⁻¹ := by
    rw [Complex.cpow_sub _ _ hQC, div_eq_mul_inv, Complex.cpow_ofNat]
  unfold termDxx termDyy termFun
  rw [hy1, hy2, hQ1, hQ2]
  field_simp [hyC, hQC]
  unfold quadQ quadQx quadQy quadQ2
  push_cast
  ring

private lemma int_pair_ne_zero_cast {c d : ℤ} (hcd : (c, d) ≠ (0, 0)) :
    ((c : ℝ), (d : ℝ)) ≠ (0, 0) := by
  intro h0
  rcases Prod.mk.inj h0 with ⟨hc, hd⟩
  exact hcd (Prod.ext (by exact_mod_cast hc) (by exact_mod_cast hd))

/-- Identification of the Eisenstein summand on `x + i y` (`y > 0`) with `termFun`. -/
private lemma eisensteinTerm_eq_termFun {c d : ℤ} (hcd : (c, d) ≠ (0, 0)) (s : ℂ)
    {x y : ℝ} (hy : 0 < y) :
    let τ : UpperHalfPlane := UpperHalfPlane.ofComplex ((x : ℂ) + Complex.I * (y : ℂ))
    ((τ.im : ℂ) / ((‖(c : ℂ) * (τ : ℂ) + (d : ℂ)‖ : ℂ) ^ 2)) ^ s =
      termFun (c : ℝ) (d : ℝ) s x y := by
  intro τ
  have him : τ.im = y := ofComplex_im_eq hy
  have hcoe : (τ : ℂ) = (x : ℂ) + Complex.I * (y : ℂ) := ofComplex_re_add_I_im_eq hy
  have hre : τ.re = x := by
    have := congrArg Complex.re hcoe
    simpa using this
  have hnorm_sq : ‖(c : ℂ) * (τ : ℂ) + (d : ℂ)‖ ^ 2 = quadQ (c : ℝ) (d : ℝ) x y := by
    rw [norm_sq_int_mul_tau_add, hre, him]; rfl
  have hQ_pos : 0 < quadQ (c : ℝ) (d : ℝ) x y := quadQ_pos hy (int_pair_ne_zero_cast hcd)
  rw [him, ← Complex.ofReal_pow, hnorm_sq, ← Complex.ofReal_div,
    ofReal_div_cpow hy hQ_pos s]
  rfl

/-- **Hyperbolic Laplacian Eigenvalue on Every Individual Eisenstein Term**:
for `(c, d) ≠ (0, 0)` and ALL `τ ∈ ℍ`, `s ∈ ℂ`,
`hypLaplacian (fun τ => (τ.im / ‖c τ + d‖²) ^ s) τ = s * (1 - s) * (τ.im / ‖c τ + d‖²) ^ s`. -/
theorem hypLaplacian_term {c d : ℤ} (hcd : (c, d) ≠ (0, 0)) (τ : UpperHalfPlane) (s : ℂ) :
    hypLaplacian (fun τ => ((τ.im : ℂ) / ((‖(c : ℂ) * (τ : ℂ) + (d : ℂ)‖ : ℂ) ^ 2)) ^ s) τ =
      s * (1 - s) * ((τ.im : ℂ) / ((‖(c : ℂ) * (τ : ℂ) + (d : ℂ)‖ : ℂ) ^ 2)) ^ s := by
  have hy : 0 < τ.im := τ.im_pos
  have hcdR : ((c : ℝ), (d : ℝ)) ≠ (0, 0) := int_pair_ne_zero_cast hcd
  have hxx : partialXX (fun τ => ((τ.im : ℂ) / ((‖(c : ℂ) * (τ : ℂ) + (d : ℂ)‖ : ℂ) ^ 2)) ^ s) τ =
      termDxx (c : ℝ) (d : ℝ) s τ.re τ.im := by
    unfold partialXX
    have hfun : uhpSliceX (fun τ => ((τ.im : ℂ) / ((‖(c : ℂ) * (τ : ℂ) + (d : ℂ)‖ : ℂ) ^ 2)) ^ s) τ.im =
        fun x => termFun (c : ℝ) (d : ℝ) s x τ.im := by
      funext x; exact eisensteinTerm_eq_termFun hcd s hy
    rw [hfun]
    have hd1 : (fun x : ℝ => deriv (fun u => termFun (c : ℝ) (d : ℝ) s u τ.im) x) =
        fun x : ℝ => termDx (c : ℝ) (d : ℝ) s x τ.im := by
      funext x; exact (hasDerivAt_termFun_x hy hcdR s).deriv
    rw [hd1]
    exact (hasDerivAt_termDx_x hy hcdR s).deriv
  have hyy : partialYY (fun τ => ((τ.im : ℂ) / ((‖(c : ℂ) * (τ : ℂ) + (d : ℂ)‖ : ℂ) ^ 2)) ^ s) τ =
      termDyy (c : ℝ) (d : ℝ) s τ.re τ.im := by
    unfold partialYY
    have hd1 : (fun y : ℝ =>
          deriv (uhpSliceY (fun τ => ((τ.im : ℂ) / ((‖(c : ℂ) * (τ : ℂ) + (d : ℂ)‖ : ℂ) ^ 2)) ^ s) τ.re) y)
        =ᶠ[nhds τ.im] fun y : ℝ => termDy (c : ℝ) (d : ℝ) s τ.re y := by
      filter_upwards [isOpen_Ioi.mem_nhds hy] with y hy0
      have hev : uhpSliceY (fun τ => ((τ.im : ℂ) / ((‖(c : ℂ) * (τ : ℂ) + (d : ℂ)‖ : ℂ) ^ 2)) ^ s) τ.re =ᶠ[nhds y]
          fun v => termFun (c : ℝ) (d : ℝ) s τ.re v := by
        filter_upwards [isOpen_Ioi.mem_nhds hy0] with v hv
        exact eisensteinTerm_eq_termFun hcd s hv
      rw [hev.deriv_eq]
      exact (hasDerivAt_termFun_y hy0 hcdR s).deriv
    rw [hd1.deriv_eq]
    exact (hasDerivAt_termDy_y hy hcdR s).deriv
  have hval : ((τ.im : ℂ) / ((‖(c : ℂ) * (τ : ℂ) + (d : ℂ)‖ : ℂ) ^ 2)) ^ s =
      termFun (c : ℝ) (d : ℝ) s τ.re τ.im := by
    have h := eisensteinTerm_eq_termFun hcd s hy (x := τ.re)
    simpa only [ofComplex_self τ] using h
  unfold hypLaplacian
  rw [hxx, hyy, hval]
  exact termDxx_add_termDyy_eigenvalue hy hcdR s

/-! ### Uniform Neighborhood Derivative Bounds & Term-by-Term Laplacian on `E(τ, s)` -/

private lemma quadQ_lower_bound_box {c d x₀ y₀ x y : ℝ} (hy₀ : 0 < y₀)
    (hx : |x - x₀| ≤ y₀ / 2) (hy : y₀ / 2 ≤ y) :
    quadQ c d x₀ y₀ / 8 ≤ quadQ c d x y := by
  unfold quadQ
  have h1 : (c * x₀ + d) ^ 2 ≤ 2 * (c * x + d) ^ 2 + 2 * (c * (x - x₀)) ^ 2 := by
    have : c * x₀ + d = (c * x + d) - c * (x - x₀) := by ring
    rw [this]; nlinarith [sq_nonneg ((c * x + d) + c * (x - x₀))]
  have h2 : (c * (x - x₀)) ^ 2 ≤ (c * (y₀ / 2)) ^ 2 := by
    have hab : |c * (x - x₀)| ≤ |c * (y₀ / 2)| := by
      rw [abs_mul, abs_mul, abs_of_pos (half_pos hy₀)]
      exact mul_le_mul_of_nonneg_left hx (abs_nonneg c)
    nlinarith [sq_abs (c * (x - x₀)), sq_abs (c * (y₀ / 2)), abs_nonneg (c * (x - x₀)),
      abs_nonneg (c * (y₀ / 2))]
  have h3 : (c * (y₀ / 2)) ^ 2 ≤ (c * y) ^ 2 := by
    have hnn : 0 ≤ c ^ 2 := sq_nonneg c
    have : (y₀ / 2) ^ 2 ≤ y ^ 2 := by nlinarith
    calc (c * (y₀ / 2)) ^ 2 = c ^ 2 * (y₀ / 2) ^ 2 := by ring
      _ ≤ c ^ 2 * y ^ 2 := mul_le_mul_of_nonneg_left this hnn
      _ = (c * y) ^ 2 := by ring
  have h4 : (c * y₀) ^ 2 = 4 * (c * (y₀ / 2)) ^ 2 := by ring
  linarith [sq_nonneg (c * x + d), sq_nonneg (c * y)]

private lemma abs_quadQx_le {c d x y : ℝ} (hy : 0 < y) :
    |quadQx c d x| ≤ quadQ c d x y / y := by
  unfold quadQx quadQ
  rw [le_div_iff₀ hy]
  have h1 : |2 * c * (c * x + d)| * y = 2 * |c * y| * |c * x + d| := by
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_mul, abs_of_pos hy]
    ring
  rw [h1]
  have h2 := sq_nonneg (|c * y| - |c * x + d|)
  rw [sub_sq, sq_abs, sq_abs] at h2
  linarith

private lemma abs_quadQy_le {c d x y : ℝ} (hy : 0 < y) :
    |quadQy c y| ≤ 2 * quadQ c d x y / y := by
  unfold quadQy quadQ
  rw [le_div_iff₀ hy, abs_of_nonneg (by positivity)]
  have : 2 * c ^ 2 * y * y = 2 * (c * y) ^ 2 := by ring
  linarith [sq_nonneg (c * x + d)]

private lemma abs_quadQ2_le {c d x y : ℝ} (hy : 0 < y) :
    |quadQ2 c| ≤ 2 * quadQ c d x y / y ^ 2 := by
  unfold quadQ2 quadQ
  rw [le_div_iff₀ (sq_pos_of_pos hy), abs_of_nonneg (by positivity)]
  have : 2 * c ^ 2 * y ^ 2 = 2 * (c * y) ^ 2 := by ring
  linarith [sq_nonneg (c * x + d)]

private lemma norm_quadQ_cpow_neg_le {c d x₀ y₀ x y : ℝ} (hy₀ : 0 < y₀)
    (hcd : (c, d) ≠ (0, 0)) (hx : |x - x₀| ≤ y₀ / 2) (hy : y₀ / 2 ≤ y)
    {s : ℂ} (hs : 0 < s.re) :
    ‖(quadQ c d x y : ℂ) ^ (-s)‖ ≤ 8 ^ s.re * quadQ c d x₀ y₀ ^ (-s.re) := by
  have hy_pos : 0 < y := lt_of_lt_of_le (half_pos hy₀) hy
  have hQ : 0 < quadQ c d x y := quadQ_pos hy_pos hcd
  have hQ0 : 0 < quadQ c d x₀ y₀ := quadQ_pos hy₀ hcd
  have hlb : quadQ c d x₀ y₀ / 8 ≤ quadQ c d x y := quadQ_lower_bound_box hy₀ hx hy
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hQ, Complex.neg_re]
  calc quadQ c d x y ^ (-s.re)
      ≤ (quadQ c d x₀ y₀ / 8) ^ (-s.re) :=
        Real.rpow_le_rpow_of_nonpos (div_pos hQ0 (by norm_num)) hlb (neg_nonpos.mpr hs.le)
    _ = 8 ^ s.re * quadQ c d x₀ y₀ ^ (-s.re) := by
        rw [Real.div_rpow hQ0.le (by norm_num : (0 : ℝ) ≤ 8),
          Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 8), div_inv_eq_mul, mul_comm]

private lemma summable_quadQ_rpow_neg (τ : UpperHalfPlane) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun p : { p : ℤ × ℤ // p ≠ (0, 0) } =>
      quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) τ.re τ.im ^ (-s.re)) := by
  have hfull := epsteinEisenstein_summable_norm τ hs
  have hy : 0 < τ.im := τ.im_pos
  have hscaled := hfull.mul_left (τ.im ^ (-s.re))
  refine hscaled.congr fun p => ?_
  have hQ : 0 < quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) τ.re τ.im :=
    quadQ_pos hy (int_pair_ne_zero_cast p.2)
  have hnorm_sq : ‖(p.1.1 : ℂ) * (τ : ℂ) + (p.1.2 : ℂ)‖ ^ 2 =
      quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) τ.re τ.im := norm_sq_int_mul_tau_add τ p.1.1 p.1.2
  have hterm : ‖((τ.im : ℂ) / ((‖(p.1.1 : ℂ) * (τ : ℂ) + (p.1.2 : ℂ)‖ : ℂ) ^ 2)) ^ s‖ =
      τ.im ^ s.re * quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) τ.re τ.im ^ (-s.re) := by
    rw [← Complex.ofReal_pow, hnorm_sq, ← Complex.ofReal_div,
      ofReal_div_cpow hy hQ s, norm_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos hy,
      Complex.norm_cpow_eq_rpow_re_of_pos hQ, Complex.neg_re]
  rw [hterm, ← mul_assoc, ← Real.rpow_add hy, neg_add_cancel, Real.rpow_zero, one_mul]

/-- **Concrete Hyperbolic Laplacian Eigenvalue Equation for `epsteinEisenstein`**:
for every `τ ∈ ℍ` and `Re(s) > 1`,
`hypLaplacian (fun τ => epsteinEisenstein τ s) τ = s * (1 - s) * epsteinEisenstein τ s`. -/
theorem hypLaplacian_epsteinEisenstein (τ : UpperHalfPlane) {s : ℂ} (hs : 1 < s.re) :
    hypLaplacian (fun τ => epsteinEisenstein τ s) τ = s * (1 - s) * epsteinEisenstein τ s := by
  have hy : 0 < τ.im := τ.im_pos
  have hs0 : 0 < s.re := lt_trans zero_lt_one hs
  have hQsum := summable_quadQ_rpow_neg τ hs
  let Ix : Set ℝ := Set.Ioo (τ.re - τ.im / 2) (τ.re + τ.im / 2)
  let Iy : Set ℝ := Set.Ioo (τ.im / 2) (3 * τ.im / 2)
  have hIx_mem : τ.re ∈ Ix := ⟨by linarith, by linarith⟩
  have hIy_mem : τ.im ∈ Iy := ⟨by linarith, by linarith⟩
  have hcdR : ∀ p : { p : ℤ × ℤ // p ≠ (0, 0) }, ((p.1.1 : ℝ), (p.1.2 : ℝ)) ≠ (0, 0) :=
    fun p => int_pair_ne_zero_cast p.2
  have hdx0 : |τ.re - τ.re| ≤ τ.im / 2 := by rw [sub_self, abs_zero]; linarith
  -- Uniform norm bounds for termDx, termDxx on Ix (at y = τ.im)
  let Cx1 : ℝ := τ.im ^ s.re * ‖s‖ * (8 ^ s.re / τ.im)
  have hbound_x1 : ∀ p : { p : ℤ × ℤ // p ≠ (0, 0) }, ∀ x ∈ Ix,
      ‖termDx (p.1.1 : ℝ) (p.1.2 : ℝ) s x τ.im‖ ≤
        Cx1 * quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) τ.re τ.im ^ (-s.re) := by
    intro p x hx
    have hQ : 0 < quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) x τ.im := quadQ_pos hy (hcdR p)
    have hQ_ne : (quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) x τ.im : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hQ.ne'
    have hdx : |x - τ.re| ≤ τ.im / 2 := abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hqpow := norm_quadQ_cpow_neg_le hy (hcdR p) hdx (by linarith : τ.im / 2 ≤ τ.im) hs0
    have hqx := abs_quadQx_le (c := (p.1.1 : ℝ)) (d := (p.1.2 : ℝ)) (x := x) hy
    unfold termDx
    rw [Complex.cpow_sub _ _ hQ_ne, Complex.cpow_one, div_eq_mul_inv]
    simp only [norm_mul, norm_neg, norm_inv, Complex.norm_cpow_eq_rpow_re_of_pos hy,
      Complex.norm_real, Real.norm_of_nonneg hQ.le, Real.norm_eq_abs]
    have hmul_le : ‖(quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) x τ.im : ℂ) ^ (-s)‖ *
        (quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) x τ.im)⁻¹ * |quadQx (p.1.1 : ℝ) (p.1.2 : ℝ) x| ≤
        (8 ^ s.re / τ.im) * quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) τ.re τ.im ^ (-s.re) := by
      calc ‖(quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) x τ.im : ℂ) ^ (-s)‖ *
            (quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) x τ.im)⁻¹ * |quadQx (p.1.1 : ℝ) (p.1.2 : ℝ) x|
          ≤ ‖(quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) x τ.im : ℂ) ^ (-s)‖ *
            (quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) x τ.im)⁻¹ * (quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) x τ.im / τ.im) :=
              mul_le_mul_of_nonneg_left hqx (by positivity)
        _ = ‖(quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) x τ.im : ℂ) ^ (-s)‖ / τ.im := by
              field_simp [hQ.ne', hy.ne']
        _ ≤ (8 ^ s.re * quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) τ.re τ.im ^ (-s.re)) / τ.im :=
              div_le_div_of_nonneg_right hqpow hy.le
        _ = (8 ^ s.re / τ.im) * quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) τ.re τ.im ^ (-s.re) := by ring
    calc τ.im ^ s.re * (‖s‖ * (‖(quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) x τ.im : ℂ) ^ (-s)‖ *
            (quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) x τ.im)⁻¹) * |quadQx (p.1.1 : ℝ) (p.1.2 : ℝ) x|)
        = τ.im ^ s.re * ‖s‖ * (‖(quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) x τ.im : ℂ) ^ (-s)‖ *
            (quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) x τ.im)⁻¹ * |quadQx (p.1.1 : ℝ) (p.1.2 : ℝ) x|) := by ring
      _ ≤ τ.im ^ s.re * ‖s‖ * ((8 ^ s.re / τ.im) * quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) τ.re τ.im ^ (-s.re)) :=
            mul_le_mul_of_nonneg_left hmul_le (by positivity)
      _ = Cx1 * quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) τ.re τ.im ^ (-s.re) := by dsimp only [Cx1]; ring
  let Cx2 : ℝ := τ.im ^ s.re * (‖s * (s + 1)‖ * (8 ^ s.re / τ.im ^ 2) + ‖s‖ * (2 * 8 ^ s.re / τ.im ^ 2))
  have hbound_x2 : ∀ p : { p : ℤ × ℤ // p ≠ (0, 0) }, ∀ x ∈ Ix,
      ‖termDxx (p.1.1 : ℝ) (p.1.2 : ℝ) s x τ.im‖ ≤
        Cx2 * quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) τ.re τ.im ^ (-s.re) := by
    intro p x hx
    have hQ : 0 < quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) x τ.im := quadQ_pos hy (hcdR p)
    have hQ_ne : (quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) x τ.im : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hQ.ne'
    have hdx : |x - τ.re| ≤ τ.im / 2 := abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hqpow := norm_quadQ_cpow_neg_le hy (hcdR p) hdx (by linarith : τ.im / 2 ≤ τ.im) hs0
    have hqx := abs_quadQx_le (c := (p.1.1 : ℝ)) (d := (p.1.2 : ℝ)) (x := x) hy
    have hq2 := abs_quadQ2_le (c := (p.1.1 : ℝ)) (d := (p.1.2 : ℝ)) (x := x) hy
    unfold termDxx
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy]
    have htri := norm_sub_le
      (s * (s + 1) * (quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) x τ.im : ℂ) ^ (-s - 2) * (quadQx (p.1.1 : ℝ) (p.1.2 : ℝ) x : ℂ) ^ 2)
      (s * (quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) x τ.im : ℂ) ^ (-s - 1) * (quadQ2 (p.1.1 : ℝ) : ℂ))
    have ht1 : ‖s * (s + 1) * (quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) x τ.im : ℂ) ^ (-s - 2) *
        (quadQx (p.1.1 : ℝ) (p.1.2 : ℝ) x : ℂ) ^ 2‖ ≤
        ‖s * (s + 1)‖ * (8 ^ s.re / τ.im ^ 2) * quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) τ.re τ.im ^ (-s.re) := by
      rw [Complex.cpow_sub _ _ hQ_ne, Complex.cpow_ofNat, div_eq_mul_inv]
      simp only [norm_mul, norm_inv, norm_pow, Complex.norm_real, Real.norm_of_nonneg hQ.le,
        Real.norm_eq_abs]
      have hsq_le : |quadQx (p.1.1 : ℝ) (p.1.2 : ℝ) x| ^ 2 ≤
          (quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) x τ.im / τ.im) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) hqx 2
      calc ‖s‖ * ‖s + 1‖ * (‖(quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) x τ.im : ℂ) ^ (-s)‖ *
              (quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) x τ.im ^ 2)⁻¹) * |quadQx (p.1.1 : ℝ) (p.1.2 : ℝ) x| ^ 2
          ≤ ‖s‖ * ‖s + 1‖ * (‖(quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) x τ.im : ℂ) ^ (-s)‖ *
              (quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) x τ.im ^ 2)⁻¹) *
              (quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) x τ.im / τ.im) ^ 2 :=
              mul_le_mul_of_nonneg_left hsq_le (by positivity)
        _ = ‖s‖ * ‖s + 1‖ * (‖(quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) x τ.im : ℂ) ^ (-s)‖ / τ.im ^ 2) := by
              field_simp [hQ.ne', hy.ne']
        _ ≤ ‖s‖ * ‖s + 1‖ * ((8 ^ s.re * quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) τ.re τ.im ^ (-s.re)) / τ.im ^ 2) :=
              mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hqpow (sq_nonneg _)) (by positivity)
        _ = ‖s‖ * ‖s + 1‖ * (8 ^ s.re / τ.im ^ 2) * quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) τ.re τ.im ^ (-s.re) := by ring
    have ht2 : ‖s * (quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) x τ.im : ℂ) ^ (-s - 1) * (quadQ2 (p.1.1 : ℝ) : ℂ)‖ ≤
        ‖s‖ * (2 * 8 ^ s.re / τ.im ^ 2) * quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) τ.re τ.im ^ (-s.re) := by
      rw [Complex.cpow_sub _ _ hQ_ne, Complex.cpow_one, div_eq_mul_inv]
      simp only [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hQ.le, Real.norm_eq_abs]
      calc ‖s‖ * (‖(quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) x τ.im : ℂ) ^ (-s)‖ *
              (quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) x τ.im)⁻¹) * |quadQ2 (p.1.1 : ℝ)|
          ≤ ‖s‖ * (‖(quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) x τ.im : ℂ) ^ (-s)‖ *
              (quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) x τ.im)⁻¹) * (2 * quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) x τ.im / τ.im ^ 2) :=
              mul_le_mul_of_nonneg_left hq2 (by positivity)
        _ = ‖s‖ * (2 * ‖(quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) x τ.im : ℂ) ^ (-s)‖ / τ.im ^ 2) := by
              field_simp [hQ.ne', hy.ne']
        _ ≤ ‖s‖ * (2 * (8 ^ s.re * quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) τ.re τ.im ^ (-s.re)) / τ.im ^ 2) :=
              mul_le_mul_of_nonneg_left
                (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hqpow (by norm_num)) (sq_nonneg _))
                (norm_nonneg _)
        _ = ‖s‖ * (2 * 8 ^ s.re / τ.im ^ 2) * quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) τ.re τ.im ^ (-s.re) := by ring
    calc τ.im ^ s.re * ‖s * (s + 1) * (quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) x τ.im : ℂ) ^ (-s - 2) *
            (quadQx (p.1.1 : ℝ) (p.1.2 : ℝ) x : ℂ) ^ 2 -
            s * (quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) x τ.im : ℂ) ^ (-s - 1) * (quadQ2 (p.1.1 : ℝ) : ℂ)‖
        ≤ τ.im ^ s.re * (‖s * (s + 1)‖ * (8 ^ s.re / τ.im ^ 2) * quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) τ.re τ.im ^ (-s.re) +
            ‖s‖ * (2 * 8 ^ s.re / τ.im ^ 2) * quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) τ.re τ.im ^ (-s.re)) :=
          mul_le_mul_of_nonneg_left (htri.trans (add_le_add ht1 ht2)) (by positivity)
      _ = Cx2 * quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) τ.re τ.im ^ (-s.re) := by dsimp only [Cx2]; ring
  -- Uniform norm bounds for termDy, termDyy on Iy (at x = τ.re)
  let M0 : ℝ := (3 * τ.im / 2) ^ s.re
  let M1 : ℝ := (3 * τ.im / 2) ^ (s.re - 1)
  let M2 : ℝ := max ((τ.im / 2) ^ (s.re - 2)) ((3 * τ.im / 2) ^ (s.re - 2))
  have hys0 : ∀ y ∈ Iy, ‖(y : ℂ) ^ s‖ ≤ M0 := fun y hyI => by
    have hy0 : 0 < y := lt_trans (half_pos hy) hyI.1
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hy0]
    exact Real.rpow_le_rpow hy0.le hyI.2.le hs0.le
  have hys1 : ∀ y ∈ Iy, ‖(y : ℂ) ^ (s - 1)‖ ≤ M1 := fun y hyI => by
    have hy0 : 0 < y := lt_trans (half_pos hy) hyI.1
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hy0]
    simp only [Complex.sub_re, Complex.one_re]
    exact Real.rpow_le_rpow hy0.le hyI.2.le (by linarith)
  have hys2 : ∀ y ∈ Iy, ‖(y : ℂ) ^ (s - 2)‖ ≤ M2 := fun y hyI => by
    have hy0 : 0 < y := lt_trans (half_pos hy) hyI.1
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hy0]
    simp only [Complex.sub_re, Complex.re_ofNat]
    by_cases hge : 2 ≤ s.re
    · exact (Real.rpow_le_rpow hy0.le hyI.2.le (by linarith)).trans (le_max_right _ _)
    · exact (Real.rpow_le_rpow_of_nonpos (half_pos hy) hyI.1.le (by linarith)).trans (le_max_left _ _)
  let Cy1 : ℝ := ‖s‖ * M1 * 8 ^ s.re + M0 * ‖s‖ * (4 * 8 ^ s.re / τ.im)
  have hbound_y1 : ∀ p : { p : ℤ × ℤ // p ≠ (0, 0) }, ∀ y ∈ Iy,
      ‖termDy (p.1.1 : ℝ) (p.1.2 : ℝ) s τ.re y‖ ≤
        Cy1 * quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) τ.re τ.im ^ (-s.re) := by
    intro p y hyI
    have hy0 : 0 < y := lt_trans (half_pos hy) hyI.1
    have hQ : 0 < quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) τ.re y := quadQ_pos hy0 (hcdR p)
    have hQ_ne : (quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) τ.re y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hQ.ne'
    have hqpow := norm_quadQ_cpow_neg_le hy (hcdR p) hdx0 hyI.1.le hs0
    have hqy := abs_quadQy_le (c := (p.1.1 : ℝ)) (d := (p.1.2 : ℝ)) (x := τ.re) hy0
    have hinv_y : 2 / y ≤ 4 / τ.im := by
      rw [div_le_div_iff₀ hy0 hy]; linarith [hyI.1]
    unfold termDy
    have ht1 : ‖s * (y : ℂ) ^ (s - 1) * (quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) τ.re y : ℂ) ^ (-s)‖ ≤
        ‖s‖ * M1 * 8 ^ s.re * quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) τ.re τ.im ^ (-s.re) := by
      rw [norm_mul, norm_mul]
      calc ‖s‖ * ‖(y : ℂ) ^ (s - 1)‖ * ‖(quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) τ.re y : ℂ) ^ (-s)‖
          ≤ ‖s‖ * M1 * (8 ^ s.re * quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) τ.re τ.im ^ (-s.re)) :=
            mul_le_mul (mul_le_mul_of_nonneg_left (hys1 y hyI) (norm_nonneg _)) hqpow (norm_nonneg _)
              (mul_nonneg (norm_nonneg _) (by positivity))
        _ = ‖s‖ * M1 * 8 ^ s.re * quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) τ.re τ.im ^ (-s.re) := by ring
    have ht2 : ‖(y : ℂ) ^ s * (-s * (quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) τ.re y : ℂ) ^ (-s - 1) *
        (quadQy (p.1.1 : ℝ) y : ℂ))‖ ≤
        M0 * ‖s‖ * (4 * 8 ^ s.re / τ.im) * quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) τ.re τ.im ^ (-s.re) := by
      rw [Complex.cpow_sub _ _ hQ_ne, Complex.cpow_one, div_eq_mul_inv]
      simp only [norm_mul, norm_neg, norm_inv, Complex.norm_real, Real.norm_of_nonneg hQ.le,
        Real.norm_eq_abs]
      have hmid : ‖(quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) τ.re y : ℂ) ^ (-s)‖ *
          (quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) τ.re y)⁻¹ * |quadQy (p.1.1 : ℝ) y| ≤
          (4 * 8 ^ s.re / τ.im) * quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) τ.re τ.im ^ (-s.re) := by
        calc ‖(quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) τ.re y : ℂ) ^ (-s)‖ *
              (quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) τ.re y)⁻¹ * |quadQy (p.1.1 : ℝ) y|
            ≤ ‖(quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) τ.re y : ℂ) ^ (-s)‖ *
              (quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) τ.re y)⁻¹ * (2 * quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) τ.re y / y) :=
                mul_le_mul_of_nonneg_left hqy (by positivity)
          _ = (2 / y) * ‖(quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) τ.re y : ℂ) ^ (-s)‖ := by
                field_simp [hQ.ne', hy0.ne']
          _ ≤ (4 / τ.im) * (8 ^ s.re * quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) τ.re τ.im ^ (-s.re)) :=
                mul_le_mul hinv_y hqpow (norm_nonneg _) (by positivity)
          _ = (4 * 8 ^ s.re / τ.im) * quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) τ.re τ.im ^ (-s.re) := by ring
      calc ‖(y : ℂ) ^ s‖ * (‖s‖ * (‖(quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) τ.re y : ℂ) ^ (-s)‖ *
              (quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) τ.re y)⁻¹) * |quadQy (p.1.1 : ℝ) y|)
          = ‖(y : ℂ) ^ s‖ * ‖s‖ * (‖(quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) τ.re y : ℂ) ^ (-s)‖ *
              (quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) τ.re y)⁻¹ * |quadQy (p.1.1 : ℝ) y|) := by ring
        _ ≤ M0 * ‖s‖ * ((4 * 8 ^ s.re / τ.im) * quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) τ.re τ.im ^ (-s.re)) :=
              mul_le_mul (mul_le_mul_of_nonneg_right (hys0 y hyI) (norm_nonneg _)) hmid
                (by positivity) (mul_nonneg (by positivity) (norm_nonneg _))
        _ = M0 * ‖s‖ * (4 * 8 ^ s.re / τ.im) * quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) τ.re τ.im ^ (-s.re) := by ring
    calc ‖_ + _‖
        ≤ ‖s * (y : ℂ) ^ (s - 1) * (quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) τ.re y : ℂ) ^ (-s)‖ +
          ‖(y : ℂ) ^ s * (-s * (quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) τ.re y : ℂ) ^ (-s - 1) *
            (quadQy (p.1.1 : ℝ) y : ℂ))‖ := norm_add_le _ _
      _ ≤ _ := add_le_add ht1 ht2
      _ = Cy1 * quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) τ.re τ.im ^ (-s.re) := by dsimp only [Cy1]; ring
  let Cy2 : ℝ :=
    ‖s * (s - 1)‖ * M2 * 8 ^ s.re +
    ‖2 * s‖ * M1 * ‖s‖ * (4 * 8 ^ s.re / τ.im) +
    M0 * (‖s * (s + 1)‖ * (16 * 8 ^ s.re / τ.im ^ 2) + ‖s‖ * (8 * 8 ^ s.re / τ.im ^ 2))
  have hbound_y2 : ∀ p : { p : ℤ × ℤ // p ≠ (0, 0) }, ∀ y ∈ Iy,
      ‖termDyy (p.1.1 : ℝ) (p.1.2 : ℝ) s τ.re y‖ ≤
        Cy2 * quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) τ.re τ.im ^ (-s.re) := by
    intro p y hyI
    have hy0 : 0 < y := lt_trans (half_pos hy) hyI.1
    have hQ : 0 < quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) τ.re y := quadQ_pos hy0 (hcdR p)
    have hQ_ne : (quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) τ.re y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hQ.ne'
    have hqpow := norm_quadQ_cpow_neg_le hy (hcdR p) hdx0 hyI.1.le hs0
    have hqy := abs_quadQy_le (c := (p.1.1 : ℝ)) (d := (p.1.2 : ℝ)) (x := τ.re) hy0
    have hq2 := abs_quadQ2_le (c := (p.1.1 : ℝ)) (d := (p.1.2 : ℝ)) (x := τ.re) hy0
    have hinv_y : 2 / y ≤ 4 / τ.im := by
      rw [div_le_div_iff₀ hy0 hy]; linarith [hyI.1]
    have hinv_y2 : 1 / y ^ 2 ≤ 4 / τ.im ^ 2 := by
      rw [div_le_div_iff₀ (sq_pos_of_pos hy0) (sq_pos_of_pos hy)]
      nlinarith [hyI.1]
    unfold termDyy
    have hA : ‖s * (s - 1) * (y : ℂ) ^ (s - 2) * (quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) τ.re y : ℂ) ^ (-s)‖ ≤
        ‖s * (s - 1)‖ * M2 * 8 ^ s.re * quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) τ.re τ.im ^ (-s.re) := by
      rw [norm_mul, norm_mul]
      have hM2_nn : 0 ≤ M2 := le_trans (by positivity) (le_max_left _ _)
      calc ‖s * (s - 1)‖ * ‖(y : ℂ) ^ (s - 2)‖ * ‖(quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) τ.re y : ℂ) ^ (-s)‖
          ≤ ‖s * (s - 1)‖ * M2 * (8 ^ s.re * quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) τ.re τ.im ^ (-s.re)) :=
            mul_le_mul (mul_le_mul_of_nonneg_left (hys2 y hyI) (norm_nonneg _)) hqpow
              (norm_nonneg _) (mul_nonneg (norm_nonneg _) hM2_nn)
        _ = ‖s * (s - 1)‖ * M2 * 8 ^ s.re * quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) τ.re τ.im ^ (-s.re) := by ring
    have hB : ‖2 * s * (y : ℂ) ^ (s - 1) * (-s * (quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) τ.re y : ℂ) ^ (-s - 1) *
        (quadQy (p.1.1 : ℝ) y : ℂ))‖ ≤
        ‖2 * s‖ * M1 * ‖s‖ * (4 * 8 ^ s.re / τ.im) * quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) τ.re τ.im ^ (-s.re) := by
      rw [Complex.cpow_sub _ _ hQ_ne, Complex.cpow_one, div_eq_mul_inv]
      simp only [norm_mul, norm_neg, norm_inv, Complex.norm_real, Real.norm_of_nonneg hQ.le,
        Real.norm_eq_abs]
      have hmid : ‖(quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) τ.re y : ℂ) ^ (-s)‖ *
          (quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) τ.re y)⁻¹ * |quadQy (p.1.1 : ℝ) y| ≤
          (4 * 8 ^ s.re / τ.im) * quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) τ.re τ.im ^ (-s.re) := by
        calc ‖(quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) τ.re y : ℂ) ^ (-s)‖ *
              (quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) τ.re y)⁻¹ * |quadQy (p.1.1 : ℝ) y|
            ≤ ‖(quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) τ.re y : ℂ) ^ (-s)‖ *
              (quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) τ.re y)⁻¹ * (2 * quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) τ.re y / y) :=
                mul_le_mul_of_nonneg_left hqy (by positivity)
          _ = (2 / y) * ‖(quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) τ.re y : ℂ) ^ (-s)‖ := by
                field_simp [hQ.ne', hy0.ne']
          _ ≤ (4 / τ.im) * (8 ^ s.re * quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) τ.re τ.im ^ (-s.re)) :=
                mul_le_mul hinv_y hqpow (norm_nonneg _) (by positivity)
          _ = (4 * 8 ^ s.re / τ.im) * quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) τ.re τ.im ^ (-s.re) := by ring
      calc ‖(2 : ℂ)‖ * ‖s‖ * ‖(y : ℂ) ^ (s - 1)‖ * (‖s‖ * (‖(quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) τ.re y : ℂ) ^ (-s)‖ *
              (quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) τ.re y)⁻¹) * |quadQy (p.1.1 : ℝ) y|)
          = (‖(2 : ℂ)‖ * ‖s‖ * ‖(y : ℂ) ^ (s - 1)‖ * ‖s‖) * (‖(quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) τ.re y : ℂ) ^ (-s)‖ *
              (quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) τ.re y)⁻¹ * |quadQy (p.1.1 : ℝ) y|) := by ring
        _ ≤ (‖(2 : ℂ)‖ * ‖s‖ * M1 * ‖s‖) * ((4 * 8 ^ s.re / τ.im) * quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) τ.re τ.im ^ (-s.re)) :=
              mul_le_mul
                (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hys1 y hyI) (by positivity)) (norm_nonneg _))
                hmid (by positivity) (by positivity)
        _ = ‖(2 : ℂ)‖ * ‖s‖ * M1 * ‖s‖ * (4 * 8 ^ s.re / τ.im) * quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) τ.re τ.im ^ (-s.re) := by ring
    have hC : ‖(y : ℂ) ^ s * (s * (s + 1) * (quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) τ.re y : ℂ) ^ (-s - 2) *
        (quadQy (p.1.1 : ℝ) y : ℂ) ^ 2 -
        s * (quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) τ.re y : ℂ) ^ (-s - 1) * (quadQ2 (p.1.1 : ℝ) : ℂ))‖ ≤
        M0 * (‖s * (s + 1)‖ * (16 * 8 ^ s.re / τ.im ^ 2) + ‖s‖ * (8 * 8 ^ s.re / τ.im ^ 2)) *
          quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) τ.re τ.im ^ (-s.re) := by
      rw [norm_mul]
      have hC1 : ‖s * (s + 1) * (quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) τ.re y : ℂ) ^ (-s - 2) *
          (quadQy (p.1.1 : ℝ) y : ℂ) ^ 2‖ ≤
          ‖s * (s + 1)‖ * (16 * 8 ^ s.re / τ.im ^ 2) * quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) τ.re τ.im ^ (-s.re) := by
        rw [Complex.cpow_sub _ _ hQ_ne, Complex.cpow_ofNat, div_eq_mul_inv]
        simp only [norm_mul, norm_inv, norm_pow, Complex.norm_real, Real.norm_of_nonneg hQ.le,
          Real.norm_eq_abs]
        have hsq_le : |quadQy (p.1.1 : ℝ) y| ^ 2 ≤ (2 * quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) τ.re y / y) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) hqy 2
        have h4 : 4 / y ^ 2 ≤ 16 / τ.im ^ 2 := by
          have := mul_le_mul_of_nonneg_left hinv_y2 (by norm_num : (0 : ℝ) ≤ 4)
          linarith [show 4 * (1 / y ^ 2) = 4 / y ^ 2 by ring,
            show 4 * (4 / τ.im ^ 2) = 16 / τ.im ^ 2 by ring]
        calc ‖s‖ * ‖s + 1‖ * (‖(quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) τ.re y : ℂ) ^ (-s)‖ *
                (quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) τ.re y ^ 2)⁻¹) * |quadQy (p.1.1 : ℝ) y| ^ 2
            ≤ ‖s‖ * ‖s + 1‖ * (‖(quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) τ.re y : ℂ) ^ (-s)‖ *
                (quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) τ.re y ^ 2)⁻¹) *
                (2 * quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) τ.re y / y) ^ 2 :=
                mul_le_mul_of_nonneg_left hsq_le (by positivity)
          _ = ‖s‖ * ‖s + 1‖ * ((4 / y ^ 2) * ‖(quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) τ.re y : ℂ) ^ (-s)‖) := by
                field_simp [hQ.ne', hy0.ne']; ring
          _ ≤ ‖s‖ * ‖s + 1‖ * ((16 / τ.im ^ 2) * (8 ^ s.re * quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) τ.re τ.im ^ (-s.re))) :=
                mul_le_mul_of_nonneg_left (mul_le_mul h4 hqpow (norm_nonneg _) (by positivity)) (by positivity)
          _ = ‖s‖ * ‖s + 1‖ * (16 * 8 ^ s.re / τ.im ^ 2) * quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) τ.re τ.im ^ (-s.re) := by ring
      have hC2 : ‖s * (quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) τ.re y : ℂ) ^ (-s - 1) * (quadQ2 (p.1.1 : ℝ) : ℂ)‖ ≤
          ‖s‖ * (8 * 8 ^ s.re / τ.im ^ 2) * quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) τ.re τ.im ^ (-s.re) := by
        rw [Complex.cpow_sub _ _ hQ_ne, Complex.cpow_one, div_eq_mul_inv]
        simp only [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hQ.le, Real.norm_eq_abs]
        have h2 : 2 / y ^ 2 ≤ 8 / τ.im ^ 2 := by
          have := mul_le_mul_of_nonneg_left hinv_y2 (by norm_num : (0 : ℝ) ≤ 2)
          linarith [show 2 * (1 / y ^ 2) = 2 / y ^ 2 by ring,
            show 2 * (4 / τ.im ^ 2) = 8 / τ.im ^ 2 by ring]
        calc ‖s‖ * (‖(quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) τ.re y : ℂ) ^ (-s)‖ *
                (quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) τ.re y)⁻¹) * |quadQ2 (p.1.1 : ℝ)|
            ≤ ‖s‖ * (‖(quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) τ.re y : ℂ) ^ (-s)‖ *
                (quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) τ.re y)⁻¹) * (2 * quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) τ.re y / y ^ 2) :=
                mul_le_mul_of_nonneg_left hq2 (by positivity)
          _ = ‖s‖ * ((2 / y ^ 2) * ‖(quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) τ.re y : ℂ) ^ (-s)‖) := by
                field_simp [hQ.ne', hy0.ne']
          _ ≤ ‖s‖ * ((8 / τ.im ^ 2) * (8 ^ s.re * quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) τ.re τ.im ^ (-s.re))) :=
                mul_le_mul_of_nonneg_left (mul_le_mul h2 hqpow (norm_nonneg _) (by positivity)) (norm_nonneg _)
          _ = ‖s‖ * (8 * 8 ^ s.re / τ.im ^ 2) * quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) τ.re τ.im ^ (-s.re) := by ring
      calc ‖(y : ℂ) ^ s‖ * ‖_ - _‖
          ≤ M0 * (‖s * (s + 1)‖ * (16 * 8 ^ s.re / τ.im ^ 2) * quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) τ.re τ.im ^ (-s.re) +
              ‖s‖ * (8 * 8 ^ s.re / τ.im ^ 2) * quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) τ.re τ.im ^ (-s.re)) :=
            mul_le_mul (hys0 y hyI) ((norm_sub_le _ _).trans (add_le_add hC1 hC2)) (norm_nonneg _) (by positivity)
        _ = M0 * (‖s * (s + 1)‖ * (16 * 8 ^ s.re / τ.im ^ 2) + ‖s‖ * (8 * 8 ^ s.re / τ.im ^ 2)) *
              quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) τ.re τ.im ^ (-s.re) := by ring
    calc ‖_ + _ + _‖
        ≤ ‖s * (s - 1) * (y : ℂ) ^ (s - 2) * (quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) τ.re y : ℂ) ^ (-s)‖ +
          ‖2 * s * (y : ℂ) ^ (s - 1) * (-s * (quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) τ.re y : ℂ) ^ (-s - 1) *
            (quadQy (p.1.1 : ℝ) y : ℂ))‖ +
          ‖(y : ℂ) ^ s * (s * (s + 1) * (quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) τ.re y : ℂ) ^ (-s - 2) *
            (quadQy (p.1.1 : ℝ) y : ℂ) ^ 2 -
            s * (quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) τ.re y : ℂ) ^ (-s - 1) * (quadQ2 (p.1.1 : ℝ) : ℂ))‖ :=
          (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ _ := add_le_add (add_le_add hA hB) hC
      _ = Cy2 * quadQ (p.1.1 : ℝ) (p.1.2 : ℝ) τ.re τ.im ^ (-s.re) := by dsimp only [Cy2]; ring
  -- Summability at τ
  have hsum_term : Summable (fun p : { p : ℤ × ℤ // p ≠ (0, 0) } =>
      termFun (p.1.1 : ℝ) (p.1.2 : ℝ) s τ.re τ.im) := by
    refine (epsteinEisenstein_summable τ hs).congr fun p => ?_
    have h := eisensteinTerm_eq_termFun p.2 s hy (x := τ.re)
    simpa only [ofComplex_self τ] using h
  have hsum_dx : Summable (fun p : { p : ℤ × ℤ // p ≠ (0, 0) } =>
      termDx (p.1.1 : ℝ) (p.1.2 : ℝ) s τ.re τ.im) :=
    Summable.of_norm_bounded (hQsum.mul_left Cx1) (fun p => hbound_x1 p τ.re hIx_mem)
  have hsum_dxx : Summable (fun p : { p : ℤ × ℤ // p ≠ (0, 0) } =>
      termDxx (p.1.1 : ℝ) (p.1.2 : ℝ) s τ.re τ.im) :=
    Summable.of_norm_bounded (hQsum.mul_left Cx2) (fun p => hbound_x2 p τ.re hIx_mem)
  have hsum_dy : Summable (fun p : { p : ℤ × ℤ // p ≠ (0, 0) } =>
      termDy (p.1.1 : ℝ) (p.1.2 : ℝ) s τ.re τ.im) :=
    Summable.of_norm_bounded (hQsum.mul_left Cy1) (fun p => hbound_y1 p τ.im hIy_mem)
  have hsum_dyy : Summable (fun p : { p : ℤ × ℤ // p ≠ (0, 0) } =>
      termDyy (p.1.1 : ℝ) (p.1.2 : ℝ) s τ.re τ.im) :=
    Summable.of_norm_bounded (hQsum.mul_left Cy2) (fun p => hbound_y2 p τ.im hIy_mem)
  -- Apply `hasDerivAt_tsum_of_isPreconnected` twice in x and twice in y
  have hxx : partialXX (fun τ => epsteinEisenstein τ s) τ =
      (1 / 2 : ℂ) * ∑' p : { p : ℤ × ℤ // p ≠ (0, 0) }, termDxx (p.1.1 : ℝ) (p.1.2 : ℝ) s τ.re τ.im := by
    unfold partialXX
    have hslice : uhpSliceX (fun τ => epsteinEisenstein τ s) τ.im =
        fun x => (1 / 2 : ℂ) * ∑' p : { p : ℤ × ℤ // p ≠ (0, 0) }, termFun (p.1.1 : ℝ) (p.1.2 : ℝ) s x τ.im := by
      funext x; unfold uhpSliceX epsteinEisenstein; dsimp only
      congr 1; refine tsum_congr fun p : { p : ℤ × ℤ // p ≠ (0, 0) } => eisensteinTerm_eq_termFun p.2 s hy
    rw [hslice]
    have hd1 : (fun x : ℝ => deriv (fun u => (1 / 2 : ℂ) * ∑' p : { p : ℤ × ℤ // p ≠ (0, 0) },
          termFun (p.1.1 : ℝ) (p.1.2 : ℝ) s u τ.im) x) =ᶠ[nhds τ.re]
        fun x : ℝ => (1 / 2 : ℂ) * ∑' p : { p : ℤ × ℤ // p ≠ (0, 0) },
          termDx (p.1.1 : ℝ) (p.1.2 : ℝ) s x τ.im := by
      filter_upwards [isOpen_Ioo.mem_nhds hIx_mem] with x hx
      have hd := hasDerivAt_tsum_of_isPreconnected (hQsum.mul_left Cx1) isOpen_Ioo
        isPreconnected_Ioo (fun p u _ => hasDerivAt_termFun_x hy (hcdR p) s)
        hbound_x1 hIx_mem hsum_term hx
      exact (hd.const_mul (1 / 2 : ℂ)).deriv
    rw [hd1.deriv_eq]
    have hd2 := hasDerivAt_tsum_of_isPreconnected (hQsum.mul_left Cx2) isOpen_Ioo
      isPreconnected_Ioo (fun p u _ => hasDerivAt_termDx_x hy (hcdR p) s)
      hbound_x2 hIx_mem hsum_dx hIx_mem
    exact (hd2.const_mul (1 / 2 : ℂ)).deriv
  have hyy : partialYY (fun τ => epsteinEisenstein τ s) τ =
      (1 / 2 : ℂ) * ∑' p : { p : ℤ × ℤ // p ≠ (0, 0) }, termDyy (p.1.1 : ℝ) (p.1.2 : ℝ) s τ.re τ.im := by
    unfold partialYY
    have hd1 : (fun y : ℝ => deriv (uhpSliceY (fun τ => epsteinEisenstein τ s) τ.re) y) =ᶠ[nhds τ.im]
        fun y : ℝ => (1 / 2 : ℂ) * ∑' p : { p : ℤ × ℤ // p ≠ (0, 0) },
          termDy (p.1.1 : ℝ) (p.1.2 : ℝ) s τ.re y := by
      filter_upwards [isOpen_Ioo.mem_nhds hIy_mem] with y hyI
      have hev : uhpSliceY (fun τ => epsteinEisenstein τ s) τ.re =ᶠ[nhds y]
          fun v => (1 / 2 : ℂ) * ∑' p : { p : ℤ × ℤ // p ≠ (0, 0) },
            termFun (p.1.1 : ℝ) (p.1.2 : ℝ) s τ.re v := by
        filter_upwards [isOpen_Ioo.mem_nhds hyI] with v hv
        have hv0 : 0 < v := lt_trans (half_pos hy) hv.1
        unfold uhpSliceY epsteinEisenstein; dsimp only
        congr 1; refine tsum_congr fun p : { p : ℤ × ℤ // p ≠ (0, 0) } => eisensteinTerm_eq_termFun p.2 s hv0
      rw [hev.deriv_eq]
      have hd := hasDerivAt_tsum_of_isPreconnected (hQsum.mul_left Cy1) isOpen_Ioo
        isPreconnected_Ioo (fun p v hv => hasDerivAt_termFun_y (lt_trans (half_pos hy) hv.1) (hcdR p) s)
        hbound_y1 hIy_mem hsum_term hyI
      exact (hd.const_mul (1 / 2 : ℂ)).deriv
    rw [hd1.deriv_eq]
    have hd2 := hasDerivAt_tsum_of_isPreconnected (hQsum.mul_left Cy2) isOpen_Ioo
      isPreconnected_Ioo (fun p v hv => hasDerivAt_termDy_y (lt_trans (half_pos hy) hv.1) (hcdR p) s)
      hbound_y2 hIy_mem hsum_dy hIy_mem
    exact (hd2.const_mul (1 / 2 : ℂ)).deriv
  -- Combine via termwise eigenvalue identity
  have hep_eq : epsteinEisenstein τ s =
      (1 / 2 : ℂ) * ∑' p : { p : ℤ × ℤ // p ≠ (0, 0) }, termFun (p.1.1 : ℝ) (p.1.2 : ℝ) s τ.re τ.im := by
    unfold epsteinEisenstein
    congr 1; refine tsum_congr fun p => ?_
    have h := eisensteinTerm_eq_termFun p.2 s hy (x := τ.re)
    simpa only [ofComplex_self τ] using h
  unfold hypLaplacian
  rw [hxx, hyy, hep_eq]
  rw [← mul_add, ← hsum_dxx.tsum_add hsum_dyy, ← mul_assoc,
    show -((τ.im : ℂ) ^ 2) * (1 / 2 : ℂ) = (1 / 2 : ℂ) * (-((τ.im : ℂ) ^ 2)) by ring,
    mul_assoc, ← tsum_mul_left]
  have hcongr : (∑' p : { p : ℤ × ℤ // p ≠ (0, 0) },
      -((τ.im : ℂ) ^ 2) * (termDxx (p.1.1 : ℝ) (p.1.2 : ℝ) s τ.re τ.im +
        termDyy (p.1.1 : ℝ) (p.1.2 : ℝ) s τ.re τ.im)) =
      ∑' p : { p : ℤ × ℤ // p ≠ (0, 0) },
        (s * (1 - s)) * termFun (p.1.1 : ℝ) (p.1.2 : ℝ) s τ.re τ.im :=
    tsum_congr fun p => termDxx_add_termDyy_eigenvalue hy (hcdR p) s
  rw [hcongr, tsum_mul_left]
  ring

/-- Linearity of `hypLaplacian` under division by a constant `c : ℂ`. -/
lemma hypLaplacian_div_const (f : UpperHalfPlane → ℂ) (c : ℂ) (τ : UpperHalfPlane) :
    hypLaplacian (fun w => f w / c) τ = hypLaplacian f τ / c := by
  unfold hypLaplacian partialXX partialYY uhpSliceX uhpSliceY
  simp only [deriv_div_const]
  ring

/-- **EXACT HYPERBOLIC LAPLACIAN EIGENVALUE EQUATION FOR THE REAL-ANALYTIC EISENSTEIN SERIES**:
for EVERY `τ ∈ ℍ` and EVERY `s ∈ ℂ` with `Re(s) > 1`,
$$\Delta_{\mathbb{H}} E(\tau, s) = s (1 - s) E(\tau, s).$$ -/
theorem hypLaplacian_realEisenstein (τ : UpperHalfPlane) {s : ℂ} (hs : 1 < s.re) :
    hypLaplacian (fun τ => realEisenstein τ s) τ = s * (1 - s) * realEisenstein τ s := by
  unfold realEisenstein
  rw [hypLaplacian_div_const, hypLaplacian_epsteinEisenstein τ hs, mul_div_assoc]

end HyperbolicLaplacian

/-! ## Section 3: 2D Binary Theta Transformation `θ_τ(1/t) = t θ_τ(t)`, Meromorphic Continuation & Functional Equation -/

section BinaryThetaAndFunctionalEquation

/-- **2D Binary-Quadratic-Form Theta Function** associated to `τ ∈ ℍ`:
$$\theta_\tau(t) = \sum_{(m, n) \in \mathbb{Z}^2}
  \exp\!\left(-\pi t \frac{|m \tau + n|^2}{\operatorname{Im} \tau}\right).$$ -/
def binaryTheta (τ : UpperHalfPlane) (t : ℝ) : ℝ :=
  ∑' p : ℤ × ℤ, Real.exp (-Real.pi * t * (‖(p.1 : ℂ) * (τ : ℂ) + (p.2 : ℂ)‖ ^ 2 / τ.im))

/-- Exact identification `binaryTheta τ t = latticeTheta (tauLattice τ) t`. -/
theorem binaryTheta_eq_latticeTheta (τ : UpperHalfPlane) (t : ℝ) :
    binaryTheta τ t = latticeTheta (tauLattice τ) t := by
  unfold binaryTheta latticeTheta gaussianTerm
  rw [← (intProdEquivTauLattice τ).tsum_eq]
  refine tsum_congr fun p => ?_
  change Real.exp (-Real.pi * t * (‖(p.1 : ℂ) * (τ : ℂ) + (p.2 : ℂ)‖ ^ 2 / τ.im)) =
    Real.exp (-Real.pi * t * ‖tauLatticeMap τ p‖ ^ 2)
  rw [norm_sq_tauLatticeMap]

/-- `SL₂(ℤ)`-invariance of `binaryTheta`: `binaryTheta (γ • τ) t = binaryTheta τ t`. -/
theorem binaryTheta_SL2Z_invariant (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (τ : UpperHalfPlane) (t : ℝ) :
    binaryTheta (γ • τ) t = binaryTheta τ t := by
  unfold binaryTheta
  calc (∑' p : ℤ × ℤ, Real.exp (-Real.pi * t * (‖(p.1 : ℂ) * ((γ • τ : UpperHalfPlane) : ℂ) + (p.2 : ℂ)‖ ^ 2 / (γ • τ).im)))
      = ∑' p : ℤ × ℤ, Real.exp (-Real.pi * t * (‖((sl2ZRowEquiv γ p).1 : ℂ) * (τ : ℂ) + ((sl2ZRowEquiv γ p).2 : ℂ)‖ ^ 2 / τ.im)) := by
          refine tsum_congr fun p => ?_
          have h := im_div_norm_sq_SL2Z_smul γ τ p
          have hrec : ‖(p.1 : ℂ) * ((γ • τ : UpperHalfPlane) : ℂ) + (p.2 : ℂ)‖ ^ 2 / (γ • τ).im =
              ‖((sl2ZRowAction γ p).1 : ℂ) * (τ : ℂ) + ((sl2ZRowAction γ p).2 : ℂ)‖ ^ 2 / τ.im := by
            simpa only [inv_div] using congrArg Inv.inv h
          dsimp only [sl2ZRowEquiv, Equiv.coe_fn_mk]
          rw [hrec]
    _ = ∑' p : ℤ × ℤ, Real.exp (-Real.pi * t * (‖(p.1 : ℂ) * (τ : ℂ) + (p.2 : ℂ)‖ ^ 2 / τ.im)) :=
          (sl2ZRowEquiv γ).tsum_eq (fun p : ℤ × ℤ =>
            Real.exp (-Real.pi * t * (‖(p.1 : ℂ) * (τ : ℂ) + (p.2 : ℂ)‖ ^ 2 / τ.im)))

/-- 1D shifted Gaussian Poisson summation derived directly from Mathlib's
`Complex.tsum_exp_neg_quadratic`: for every `a > 0` and `u : ℝ`,
$$\sum_{n \in \mathbb{Z}} e^{-\pi a (n + u)^2}
  = \frac{1}{\sqrt{a}} \sum_{k \in \mathbb{Z}} e^{-\pi k^2 / a - 2 \pi i u k}.$$ -/
private lemma tsum_cexp_neg_pi_mul_shift_sq {a : ℝ} (ha : 0 < a) (u : ℝ) :
    (∑' n : ℤ, Complex.exp (-(Real.pi : ℂ) * (a : ℂ) * ((n : ℂ) + (u : ℂ)) ^ 2)) =
      ((Real.sqrt a : ℝ) : ℂ)⁻¹ *
        ∑' k : ℤ, Complex.exp (-(Real.pi : ℂ) / (a : ℂ) * (k : ℂ) ^ 2 -
          2 * (Real.pi : ℂ) * Complex.I * (u : ℂ) * (k : ℂ)) := by
  have ha_inv_re : 0 < (((a⁻¹ : ℝ) : ℂ)).re := by simpa using inv_pos.mpr ha
  have hq := Complex.tsum_exp_neg_quadratic ha_inv_re (-Complex.I * (u : ℂ))
  have hsqrt_inv : (((a⁻¹ : ℝ) : ℂ)) ^ (1 / 2 : ℂ) = ((Real.sqrt a : ℝ) : ℂ)⁻¹ := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; rfl,
      ← Complex.ofReal_cpow (inv_pos.mpr ha).le, Real.inv_rpow ha.le,
      ← Real.sqrt_eq_rpow, Complex.ofReal_inv]
  have hsqrt_ne : ((Real.sqrt a : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr ha).ne'
  have hlhs_congr : (∑' k : ℤ, Complex.exp (-(Real.pi : ℂ) * ((a⁻¹ : ℝ) : ℂ) * (k : ℂ) ^ 2 +
      2 * (Real.pi : ℂ) * (-Complex.I * (u : ℂ)) * (k : ℂ))) =
      ∑' k : ℤ, Complex.exp (-(Real.pi : ℂ) / (a : ℂ) * (k : ℂ) ^ 2 -
        2 * (Real.pi : ℂ) * Complex.I * (u : ℂ) * (k : ℂ)) := by
    refine tsum_congr fun k => ?_; congr 1
    rw [Complex.ofReal_inv]; ring
  have hrhs_congr : (∑' n : ℤ, Complex.exp (-(Real.pi : ℂ) / ((a⁻¹ : ℝ) : ℂ) *
      ((n : ℂ) + Complex.I * (-Complex.I * (u : ℂ))) ^ 2)) =
      ∑' n : ℤ, Complex.exp (-(Real.pi : ℂ) * (a : ℂ) * ((n : ℂ) + (u : ℂ)) ^ 2) := by
    refine tsum_congr fun n => ?_; congr 1
    have hI : Complex.I * (-Complex.I * (u : ℂ)) = (u : ℂ) := by
      calc Complex.I * (-Complex.I * (u : ℂ)) = -(Complex.I * Complex.I) * (u : ℂ) := by ring
        _ = -(-1) * (u : ℂ) := by rw [Complex.I_mul_I]
        _ = (u : ℂ) := by ring
    rw [hI, Complex.ofReal_inv, div_inv_eq_mul]
  rw [hlhs_congr, hrhs_congr, hsqrt_inv, one_div, inv_inv] at hq
  calc (∑' n : ℤ, Complex.exp (-(Real.pi : ℂ) * (a : ℂ) * ((n : ℂ) + (u : ℂ)) ^ 2))
      = ((Real.sqrt a : ℝ) : ℂ)⁻¹ * (((Real.sqrt a : ℝ) : ℂ) *
          ∑' n : ℤ, Complex.exp (-(Real.pi : ℂ) * (a : ℂ) * ((n : ℂ) + (u : ℂ)) ^ 2)) := by
          rw [← mul_assoc, inv_mul_cancel₀ hsqrt_ne, one_mul]
    _ = ((Real.sqrt a : ℝ) : ℂ)⁻¹ *
          ∑' k : ℤ, Complex.exp (-(Real.pi : ℂ) / (a : ℂ) * (k : ℂ) ^ 2 -
            2 * (Real.pi : ℂ) * Complex.I * (u : ℂ) * (k : ℂ)) := by rw [← hq]

/-- **EXACT 2D THETA MODULAR TRANSFORMATION (`0` ASSUMPTIONS!)**:
for EVERY `τ ∈ ℍ` and EVERY `t > 0`,
$$\theta_\tau(1 / t) = t \cdot \theta_\tau(t).$$ -/
theorem binaryTheta_inv_eq (τ : UpperHalfPlane) {t : ℝ} (ht : 0 < t) :
    binaryTheta τ (1 / t) = t * binaryTheta τ t := by
  have hy : 0 < τ.im := τ.im_pos
  have hty : 0 < t * τ.im := mul_pos ht hy
  have htdy : 0 < t / τ.im := div_pos ht hy
  have hydt : 0 < τ.im / t := div_pos hy ht
  have hinv_t : 0 < 1 / t := one_div_pos.mpr ht
  -- Summability of the 2D Gaussian on `ℤ × ℤ` at `t` and `1/t`
  have hsum_t : Summable (fun p : ℤ × ℤ =>
      Complex.exp (-(Real.pi : ℂ) * (t : ℂ) * (((‖(p.1 : ℂ) * (τ : ℂ) + (p.2 : ℂ)‖ ^ 2 / τ.im : ℝ) : ℂ)))) := by
    have hreal : Summable (fun p : ℤ × ℤ =>
        Real.exp (-Real.pi * t * (‖(p.1 : ℂ) * (τ : ℂ) + (p.2 : ℂ)‖ ^ 2 / τ.im))) := by
      have hlat := (Equiv.summable_iff (intProdEquivTauLattice τ)).mpr (summable_gaussianTerm (tauLattice τ) ht)
      refine hlat.congr fun p => ?_
      change Real.exp (-Real.pi * t * ‖tauLatticeMap τ p‖ ^ 2) = _
      rw [norm_sq_tauLatticeMap]
    refine (hreal.congr fun p => ?_).of_norm
    rw [Complex.norm_exp]
    congr 1
    simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.neg_im, mul_zero, sub_zero]
  have hsum_inv : Summable (fun p : ℤ × ℤ =>
      Complex.exp (-(Real.pi : ℂ) * ((1 / t : ℝ) : ℂ) * (((‖(p.1 : ℂ) * (τ : ℂ) + (p.2 : ℂ)‖ ^ 2 / τ.im : ℝ) : ℂ)))) := by
    have hreal : Summable (fun p : ℤ × ℤ =>
        Real.exp (-Real.pi * (1 / t) * (‖(p.1 : ℂ) * (τ : ℂ) + (p.2 : ℂ)‖ ^ 2 / τ.im))) := by
      have hlat := (Equiv.summable_iff (intProdEquivTauLattice τ)).mpr (summable_gaussianTerm (tauLattice τ) hinv_t)
      refine hlat.congr fun p => ?_
      change Real.exp (-Real.pi * (1 / t) * ‖tauLatticeMap τ p‖ ^ 2) = _
      rw [norm_sq_tauLatticeMap]
    refine (hreal.congr fun p => ?_).of_norm
    rw [Complex.norm_exp]
    congr 1
    simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.neg_im, mul_zero, sub_zero]
  -- Summability of the mixed 2D Fourier sum `(m, k) ↦ exp(-π t y m² - π (y/t) k² - 2π i m k x)`
  have hsum_mk : Summable (Function.uncurry fun m k : ℤ =>
      Complex.exp (-(Real.pi : ℂ) * (t : ℂ) * (τ.im : ℂ) * (m : ℂ) ^ 2 -
        (Real.pi : ℂ) * ((τ.im / t : ℝ) : ℂ) * (k : ℂ) ^ 2 -
        2 * (Real.pi : ℂ) * Complex.I * ((m : ℂ) * (τ.re : ℂ)) * (k : ℂ))) := by
    have h1 : Summable (fun m : ℤ => Real.exp (-Real.pi * (t * τ.im) * (m : ℝ) ^ 2)) := by
      simpa using summable_theta1D one_pos hty
    have h2 : Summable (fun k : ℤ => Real.exp (-Real.pi * (τ.im / t) * (k : ℝ) ^ 2)) := by
      simpa using summable_theta1D one_pos hydt
    have hprod := Summable.mul_of_nonneg h1 h2 (fun _ => (Real.exp_pos _).le) (fun _ => (Real.exp_pos _).le)
    refine (hprod.congr fun mk => ?_).of_norm
    dsimp only [Function.uncurry]
    rw [Complex.norm_exp, ← Real.exp_add]
    congr 1
    simp only [Complex.sub_re, Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.intCast_re, Complex.intCast_im, Complex.I_re, Complex.I_im,
      Complex.mul_im, Complex.neg_im, Complex.re_ofNat, Complex.im_ofNat, sq]
    ring
  -- Step 1: Work in ℂ, factor `binaryTheta τ t` into iterated sums over `m` and `n`
  have hC_eq : (binaryTheta τ t : ℂ) = ((t⁻¹ : ℝ) : ℂ) * (binaryTheta τ (1 / t) : ℂ) := by
    have hbt_t : (binaryTheta τ t : ℂ) =
        ∑' m : ℤ, ∑' n : ℤ,
          Complex.exp (-(Real.pi : ℂ) * (t : ℂ) * (τ.im : ℂ) * (m : ℂ) ^ 2) *
          Complex.exp (-(Real.pi : ℂ) * ((t / τ.im : ℝ) : ℂ) * ((n : ℂ) + ((m : ℝ) * τ.re : ℝ)) ^ 2) := by
      unfold binaryTheta
      rw [Complex.ofReal_tsum]
      have hcongr : (fun p : ℤ × ℤ =>
          ((Real.exp (-Real.pi * t * (‖(p.1 : ℂ) * (τ : ℂ) + (p.2 : ℂ)‖ ^ 2 / τ.im)) : ℝ) : ℂ)) =
          fun p : ℤ × ℤ =>
            Complex.exp (-(Real.pi : ℂ) * (t : ℂ) * (((‖(p.1 : ℂ) * (τ : ℂ) + (p.2 : ℂ)‖ ^ 2 / τ.im : ℝ) : ℂ))) := by
        funext p; rw [Complex.ofReal_exp]; push_cast; ring
      rw [hcongr, hsum_t.tsum_prod]
      refine tsum_congr fun m => tsum_congr fun n => ?_
      rw [← Complex.exp_add]
      congr 1
      rw [norm_sq_int_mul_tau_add]
      push_cast
      have hyC : (τ.im : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
      field_simp [hyC]
      ring
    -- Apply 1D shifted Poisson summation to the inner `n`-sum
    have hstep1 : (binaryTheta τ t : ℂ) =
        ((Real.sqrt (t / τ.im) : ℝ) : ℂ)⁻¹ *
          ∑' m : ℤ, ∑' k : ℤ,
            Complex.exp (-(Real.pi : ℂ) * (t : ℂ) * (τ.im : ℂ) * (m : ℂ) ^ 2 -
              (Real.pi : ℂ) * ((τ.im / t : ℝ) : ℂ) * (k : ℂ) ^ 2 -
              2 * (Real.pi : ℂ) * Complex.I * ((m : ℂ) * (τ.re : ℂ)) * (k : ℂ)) := by
      rw [hbt_t, ← tsum_mul_left]
      refine tsum_congr fun m => ?_
      rw [tsum_mul_left, tsum_cexp_neg_pi_mul_shift_sq htdy ((m : ℝ) * τ.re)]
      rw [← mul_assoc, mul_comm (Complex.exp _) ((Real.sqrt (t / τ.im) : ℝ) : ℂ)⁻¹, mul_assoc,
        ← tsum_mul_left]
      congr 1
      refine tsum_congr fun k => ?_
      rw [← Complex.exp_add]
      congr 1
      push_cast
      have htC : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
      have hyC : (τ.im : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
      field_simp [htC, hyC]
      ring
    -- Swap `∑' m` and `∑' k` via `Summable.tsum_comm`, then apply 1D Poisson to the `m`-sum
    have hstep2 : (binaryTheta τ t : ℂ) =
        ((Real.sqrt (t / τ.im) : ℝ) : ℂ)⁻¹ * ((Real.sqrt (t * τ.im) : ℝ) : ℂ)⁻¹ *
          ∑' k : ℤ, ∑' j : ℤ,
            Complex.exp (-(Real.pi : ℂ) * ((1 / t : ℝ) : ℂ) *
              (((‖(k : ℂ) * (τ : ℂ) + (j : ℂ)‖ ^ 2 / τ.im : ℝ) : ℂ))) := by
      have hcomm : (∑' m : ℤ, ∑' k : ℤ,
          Complex.exp (-(Real.pi : ℂ) * (t : ℂ) * (τ.im : ℂ) * (m : ℂ) ^ 2 -
            (Real.pi : ℂ) * ((τ.im / t : ℝ) : ℂ) * (k : ℂ) ^ 2 -
            2 * (Real.pi : ℂ) * Complex.I * ((m : ℂ) * (τ.re : ℂ)) * (k : ℂ))) =
          ∑' k : ℤ, ∑' m : ℤ,
          Complex.exp (-(Real.pi : ℂ) * (t : ℂ) * (τ.im : ℂ) * (m : ℂ) ^ 2 -
            (Real.pi : ℂ) * ((τ.im / t : ℝ) : ℂ) * (k : ℂ) ^ 2 -
            2 * (Real.pi : ℂ) * Complex.I * ((m : ℂ) * (τ.re : ℂ)) * (k : ℂ)) :=
        hsum_mk.tsum_comm.symm
      rw [hstep1, hcomm, mul_assoc (((Real.sqrt (t / τ.im) : ℝ) : ℂ)⁻¹)]
      congr 1
      rw [← tsum_mul_left]
      refine tsum_congr fun k => ?_
      have hfactor : (∑' m : ℤ,
          Complex.exp (-(Real.pi : ℂ) * (t : ℂ) * (τ.im : ℂ) * (m : ℂ) ^ 2 -
            (Real.pi : ℂ) * ((τ.im / t : ℝ) : ℂ) * (k : ℂ) ^ 2 -
            2 * (Real.pi : ℂ) * Complex.I * ((m : ℂ) * (τ.re : ℂ)) * (k : ℂ))) =
          Complex.exp (-(Real.pi : ℂ) * ((τ.im / t : ℝ) : ℂ) * (k : ℂ) ^ 2) *
            ∑' m : ℤ, Complex.exp (-(Real.pi : ℂ) * ((t * τ.im : ℝ) : ℂ) * (m : ℂ) ^ 2 +
              2 * (Real.pi : ℂ) * (-Complex.I * ((k : ℂ) * (τ.re : ℂ))) * (m : ℂ)) := by
        rw [← tsum_mul_left]
        refine tsum_congr fun m => ?_
        rw [← Complex.exp_add]; congr 1; push_cast; ring
      rw [hfactor, Complex.tsum_exp_neg_quadratic (by simpa using hty)]
      have hsqrt_ty : (((t * τ.im : ℝ) : ℂ)) ^ (1 / 2 : ℂ) = ((Real.sqrt (t * τ.im) : ℝ) : ℂ) := by
        rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; rfl,
          ← Complex.ofReal_cpow hty.le, ← Real.sqrt_eq_rpow]
      rw [hsqrt_ty, one_div, ← mul_assoc,
        mul_comm (Complex.exp _) ((Real.sqrt (t * τ.im) : ℝ) : ℂ)⁻¹, mul_assoc, ← tsum_mul_left]
      congr 1
      refine tsum_congr fun j => ?_
      rw [← Complex.exp_add]
      congr 1
      have hI : Complex.I * (-Complex.I * ((k : ℂ) * (τ.re : ℂ))) = (k : ℂ) * (τ.re : ℂ) := by
        calc Complex.I * (-Complex.I * ((k : ℂ) * (τ.re : ℂ)))
            = -(Complex.I * Complex.I) * ((k : ℂ) * (τ.re : ℂ)) := by ring
          _ = -(-1) * ((k : ℂ) * (τ.re : ℂ)) := by rw [Complex.I_mul_I]
          _ = (k : ℂ) * (τ.re : ℂ) := by ring
      rw [hI, norm_sq_int_mul_tau_add]
      push_cast
      have htC : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
      have hyC : (τ.im : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
      field_simp [htC, hyC]
      ring
    -- Combine prefactors `1/√(t/y) * 1/√(t*y) = 1/t` and repack `∑' k, ∑' j`
    have hpref : ((Real.sqrt (t / τ.im) : ℝ) : ℂ)⁻¹ * ((Real.sqrt (t * τ.im) : ℝ) : ℂ)⁻¹ =
        ((t⁻¹ : ℝ) : ℂ) := by
      rw [← mul_inv, ← Complex.ofReal_mul, ← Real.sqrt_mul htdy.le,
        show (t / τ.im) * (t * τ.im) = t ^ 2 by field_simp [hy.ne'],
        Real.sqrt_sq ht.le, Complex.ofReal_inv]
    rw [hstep2, hpref, ← hsum_inv.tsum_prod]
    congr 1
    unfold binaryTheta
    rw [Complex.ofReal_tsum]
    refine tsum_congr fun p => ?_
    rw [Complex.ofReal_exp]; congr 1; push_cast; ring
  have hR : binaryTheta τ t = t⁻¹ * binaryTheta τ (1 / t) := by
    rw [← Complex.ofReal_mul] at hC_eq
    exact Complex.ofReal_injective hC_eq
  calc binaryTheta τ (1 / t)
      = t * (t⁻¹ * binaryTheta τ (1 / t)) := by rw [← mul_assoc, mul_inv_cancel₀ ht.ne', one_mul]
    _ = t * binaryTheta τ t := by rw [← hR]

/-! ### Self-Duality (Up to `90°` Rotation) of `tauLattice τ` -/

/-- Counterclockwise `90°` rotation `(a, b) ↦ (-b, a)` on `ℝ²`. -/
private def rot90Vec (v : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 ![-v 1, v 0]

private lemma norm_sq_rot90Vec (v : EuclideanSpace ℝ (Fin 2)) :
    ‖rot90Vec v‖ ^ 2 = ‖v‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Fin.sum_univ_two, Fin.sum_univ_two]
  simp [rot90Vec, Real.norm_eq_abs, add_comm]

/-- Membership characterization of `dualLattice (tauLattice τ)`:
`v ∈ (L_τ)* ↔ ∃ m n : ℤ, v = rot90Vec (tauLatticeMap τ (m, n))`. -/
private lemma mem_dualLattice_tauLattice_iff (τ : UpperHalfPlane) (v : EuclideanSpace ℝ (Fin 2)) :
    v ∈ dualLattice (tauLattice τ) ↔ ∃ p : ℤ × ℤ, v = rot90Vec (tauLatticeMap τ p) := by
  have hy : 0 < τ.im := τ.im_pos
  have hsq : Real.sqrt τ.im ^ 2 = τ.im := Real.sq_sqrt hy.le
  have hsq_ne : Real.sqrt τ.im ≠ 0 := (Real.sqrt_pos.mpr hy).ne'
  constructor
  · intro hv
    have hv_int : ∀ w ∈ tauLattice τ, ∃ m : ℤ, inner ℝ v w = (m : ℝ) := hv.2
    obtain ⟨k1, hk1⟩ := hv_int (tauVec1 τ) (Submodule.subset_span (Set.mem_insert _ _))
    obtain ⟨k2, hk2⟩ := hv_int (tauVec2 τ) (Submodule.subset_span (Set.mem_insert_of_mem _ rfl))
    have hinner1 : v 0 * (τ.re / Real.sqrt τ.im) + v 1 * Real.sqrt τ.im = (k1 : ℝ) := by
      simpa only [PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply, conj_trivial,
        tauVec1, Matrix.cons_val_zero, Matrix.cons_val_one, mul_comm] using hk1
    have hinner2 : v 0 * (1 / Real.sqrt τ.im) = (k2 : ℝ) := by
      simpa only [PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply, conj_trivial,
        tauVec2, Matrix.cons_val_zero, Matrix.cons_val_one, zero_mul, add_zero, mul_comm] using hk2
    have hv0 : v 0 = (k2 : ℝ) * Real.sqrt τ.im := by
      have := congrArg (· * Real.sqrt τ.im) hinner2
      have hsimp : v 0 * (1 / Real.sqrt τ.im) * Real.sqrt τ.im = v 0 := by field_simp [hsq_ne]
      linarith
    have hv1 : v 1 = (-(k2 : ℝ) * τ.re + (k1 : ℝ)) / Real.sqrt τ.im := by
      rw [hv0] at hinner1
      have hsimp : (k2 : ℝ) * Real.sqrt τ.im * (τ.re / Real.sqrt τ.im) = (k2 : ℝ) * τ.re := by
        field_simp [hsq_ne]
      rw [hsimp] at hinner1
      field_simp [hsq_ne]
      linarith
    refine ⟨(-k2, k1), ?_⟩
    ext i
    fin_cases i
    · change v 0 = rot90Vec (tauLatticeMap τ (-k2, k1)) 0
      simp only [rot90Vec, tauLatticeMap, tauVec1, tauVec2, PiLp.add_apply, PiLp.smul_apply,
        zsmul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one, Int.cast_neg, mul_zero, add_zero,
        neg_mul, neg_neg, hv0]
    · change v 1 = rot90Vec (tauLatticeMap τ (-k2, k1)) 1
      simp only [rot90Vec, tauLatticeMap, tauVec1, tauVec2, PiLp.add_apply, PiLp.smul_apply,
        zsmul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one, Int.cast_neg]
      rw [hv1]
      field_simp [hsq_ne]
  · rintro ⟨p, rfl⟩
    refine ⟨?_, fun w hw => ?_⟩
    · have hdecomp : rot90Vec (tauLatticeMap τ p) =
          (rot90Vec (tauLatticeMap τ p) 1 / Real.sqrt τ.im) • tauVec1 τ +
            (rot90Vec (tauLatticeMap τ p) 0 * Real.sqrt τ.im -
              rot90Vec (tauLatticeMap τ p) 1 * (τ.re / Real.sqrt τ.im)) • tauVec2 τ := by
        ext i
        fin_cases i
        · change rot90Vec (tauLatticeMap τ p) 0 =
            ((rot90Vec (tauLatticeMap τ p) 1 / Real.sqrt τ.im) • tauVec1 τ +
              (rot90Vec (tauLatticeMap τ p) 0 * Real.sqrt τ.im -
                rot90Vec (tauLatticeMap τ p) 1 * (τ.re / Real.sqrt τ.im)) • tauVec2 τ) 0
          simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, tauVec1, tauVec2,
            Matrix.cons_val_zero]
          field_simp [hsq_ne]; ring
        · change rot90Vec (tauLatticeMap τ p) 1 =
            ((rot90Vec (tauLatticeMap τ p) 1 / Real.sqrt τ.im) • tauVec1 τ +
              (rot90Vec (tauLatticeMap τ p) 0 * Real.sqrt τ.im -
                rot90Vec (tauLatticeMap τ p) 1 * (τ.re / Real.sqrt τ.im)) • tauVec2 τ) 1
          simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, tauVec1, tauVec2,
            Matrix.cons_val_one, Matrix.cons_val_zero, mul_zero, add_zero]
          field_simp [hsq_ne]
      rw [hdecomp]
      refine Submodule.add_mem _ (Submodule.smul_mem _ _ ?_) (Submodule.smul_mem _ _ ?_)
      · exact Submodule.subset_span (Submodule.subset_span (Set.mem_insert _ _))
      · exact Submodule.subset_span (Submodule.subset_span (Set.mem_insert_of_mem _ rfl))
    · rw [tauLattice, Submodule.mem_span_pair] at hw
      rcases hw with ⟨a, b, rfl⟩
      refine ⟨a * p.2 - b * p.1, ?_⟩
      simp only [PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply, conj_trivial,
        rot90Vec, tauLatticeMap, tauVec1, tauVec2, PiLp.add_apply, PiLp.smul_apply,
        zsmul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one, mul_zero, add_zero]
      push_cast
      field_simp [hsq_ne]
      ring

/-- Isometric bijection `tauLattice τ ≃ dualLattice (tauLattice τ)` via `90°` rotation. -/
private def tauLatticeEquivDual (τ : UpperHalfPlane) :
    tauLattice τ ≃ dualLattice (tauLattice τ) where
  toFun v := ⟨rot90Vec (v : EuclideanSpace ℝ (Fin 2)), by
    rw [mem_dualLattice_tauLattice_iff]
    refine ⟨(intProdEquivTauLattice τ).symm v, ?_⟩
    have h := congrArg Subtype.val ((intProdEquivTauLattice τ).apply_symm_apply v)
    exact congrArg rot90Vec h.symm⟩
  invFun w := ⟨WithLp.toLp 2 ![(w : EuclideanSpace ℝ (Fin 2)) 1, -(w : EuclideanSpace ℝ (Fin 2)) 0], by
    obtain ⟨p, hp⟩ := (mem_dualLattice_tauLattice_iff τ (w : EuclideanSpace ℝ (Fin 2))).mp w.2
    have hback : WithLp.toLp 2 ![(w : EuclideanSpace ℝ (Fin 2)) 1, -(w : EuclideanSpace ℝ (Fin 2)) 0] =
        tauLatticeMap τ p := by
      rw [hp]; ext i; fin_cases i <;> simp [rot90Vec]
    rw [hback]; exact tauLatticeMap_mem τ p⟩
  left_inv v := by apply Subtype.ext; ext i; fin_cases i <;> simp [rot90Vec]
  right_inv w := by apply Subtype.ext; ext i; fin_cases i <;> simp [rot90Vec]

/-- `dualLattice (tauLattice τ)` is discrete. -/
instance discreteTopology_dualLattice_tauLattice (τ : UpperHalfPlane) :
    DiscreteTopology (dualLattice (tauLattice τ)) := by
  have hcont : Continuous (tauLatticeEquivDual τ).symm := by
    refine Continuous.subtype_mk ?_ _
    refine (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp ?_
    refine continuous_pi fun i => ?_
    fin_cases i
    · exact (EuclideanSpace.proj (1 : Fin 2)).continuous.comp continuous_subtype_val
    · exact ((EuclideanSpace.proj (0 : Fin 2)).continuous.comp continuous_subtype_val).neg
  exact DiscreteTopology.of_continuous_injective hcont (tauLatticeEquivDual τ).symm.injective

/-- Exact theta-series self-duality: `latticeTheta (dualLattice (tauLattice τ)) t = binaryTheta τ t`. -/
lemma latticeTheta_dual_tauLattice_eq (τ : UpperHalfPlane) (t : ℝ) :
    latticeTheta (dualLattice (tauLattice τ)) t = binaryTheta τ t := by
  rw [binaryTheta_eq_latticeTheta]
  unfold latticeTheta gaussianTerm
  rw [← (tauLatticeEquivDual τ).tsum_eq]
  refine tsum_congr fun v => ?_
  change Real.exp (-Real.pi * t * ‖rot90Vec (v : EuclideanSpace ℝ (Fin 2))‖ ^ 2) = _
  rw [norm_sq_rot90Vec]

/-! ### Completed Eisenstein Series `completedEisenstein τ s`: Global Meromorphic Continuation, Poles & Functional Equation -/

/-- **Completed Real-Analytic Eisenstein Series `E*(τ, s)` (Global Meromorphic Continuation)**:
$$E^*(\tau, s) = \frac{1}{2} \int_1^\infty (\theta_\tau(t) - 1)\left(t^s + t^{1 - s}\right) \frac{dt}{t}
  - \frac{1}{2 s} - \frac{1}{2 (1 - s)}.$$
On `Re(s) > 1`, this agrees identically with `π^{-s} Γ(s) E_Ep(τ, s) = Λ(2s) E(τ, s)`. -/
def completedEisenstein (τ : UpperHalfPlane) (s : ℂ) : ℂ :=
  (1 / 2 : ℂ) * (∫ t in Set.Ioi (1 : ℝ),
      ((binaryTheta τ t - 1 : ℝ) : ℂ) * ((t : ℂ) ^ s + (t : ℂ) ^ (1 - s)) * (t : ℂ)⁻¹) -
    1 / (2 * s) - 1 / (2 * (1 - s))

/-- Exact identification with `Stage5ThetaModular.completedEpsteinZetaExt`:
`completedEisenstein τ s = (1 / 2) * completedEpsteinZetaExt (tauLattice τ) (2 * s)`. -/
theorem completedEisenstein_eq_half_completedEpsteinZetaExt (τ : UpperHalfPlane) (s : ℂ) :
    completedEisenstein τ s = (1 / 2 : ℂ) * completedEpsteinZetaExt (tauLattice τ) (2 * s) := by
  have hint_upper : ∀ w : ℂ, IntegrableOn
      (fun t : ℝ => ((binaryTheta τ t - 1 : ℝ) : ℂ) * (t : ℂ) ^ (w - 1)) (Set.Ioi (1 : ℝ)) volume := by
    intro w
    let f : ℝ → ℂ := (Set.Ioi (1 : ℝ)).indicator (fun t => ((latticeTheta (tauLattice τ) t - 1 : ℝ) : ℂ))
    have hloc : LocallyIntegrableOn f (Set.Ioi 0) volume := by
      have hcont : ContinuousOn (fun t : ℝ => ((latticeTheta (tauLattice τ) t - 1 : ℝ) : ℂ)) (Set.Ioi 0) :=
        Complex.continuous_ofReal.comp_continuousOn ((continuousOn_latticeTheta (tauLattice τ)).sub continuousOn_const)
      intro x hx
      obtain ⟨u, hu, hint⟩ := (hcont.locallyIntegrableOn (μ := volume) measurableSet_Ioi) x hx
      exact ⟨u, hu, hint.indicator measurableSet_Ioi⟩
    have hmconv : MellinConvergent f w := by
      refine mellinConvergent_of_isBigO_rpow hloc (a := w.re + 1) (b := w.re - 1) ?_ (by linarith) ?_ (by linarith)
      · have htop := isBigO_latticeTheta_sub_one_atTop (tauLattice τ) (w.re + 1)
        refine htop.congr' ?_ EventuallyEq.rfl
        filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
        dsimp only [f]
        exact (Set.indicator_of_mem (ht : t ∈ Set.Ioi (1 : ℝ))
          (fun u : ℝ => ((latticeTheta (tauLattice τ) u - 1 : ℝ) : ℂ))).symm
      · refine (Asymptotics.isBigO_zero (fun t : ℝ => t ^ (-(w.re - 1)))
          (nhdsWithin (0 : ℝ) (Set.Ioi 0))).congr' ?_ EventuallyEq.rfl
        filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with t ht
        dsimp only [f]
        exact (Set.indicator_of_notMem (not_lt.mpr ht.2.le : t ∉ Set.Ioi (1 : ℝ))
          (fun u : ℝ => ((latticeTheta (tauLattice τ) u - 1 : ℝ) : ℂ))).symm
    have hsub : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (w - 1) • f t) (Set.Ioi (1 : ℝ)) volume :=
      hmconv.mono_set (Set.Ioi_subset_Ioi zero_le_one)
    refine hsub.congr_fun (fun t ht => ?_) measurableSet_Ioi
    dsimp only [f]
    rw [Set.indicator_of_mem ht, smul_eq_mul, mul_comm, binaryTheta_eq_latticeTheta]
  have hsplit_int : (∫ t in Set.Ioi (1 : ℝ),
      ((binaryTheta τ t - 1 : ℝ) : ℂ) * ((t : ℂ) ^ s + (t : ℂ) ^ (1 - s)) * (t : ℂ)⁻¹) =
      upperMellinTheta (tauLattice τ) (2 * s) +
        upperMellinTheta (dualLattice (tauLattice τ)) (2 - 2 * s) := by
    have hpt : Set.EqOn
        (fun t : ℝ => ((binaryTheta τ t - 1 : ℝ) : ℂ) * ((t : ℂ) ^ s + (t : ℂ) ^ (1 - s)) * (t : ℂ)⁻¹)
        (fun t : ℝ => ((binaryTheta τ t - 1 : ℝ) : ℂ) * (t : ℂ) ^ (s - 1) +
          ((binaryTheta τ t - 1 : ℝ) : ℂ) * (t : ℂ) ^ ((1 - s) - 1)) (Set.Ioi 1) := by
      intro t ht
      have ht0 : 0 < t := lt_trans zero_lt_one ht
      have htC : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht0.ne'
      dsimp only
      have h1 : (t : ℂ) ^ (s - 1) = (t : ℂ) ^ s * (t : ℂ)⁻¹ := by
        rw [Complex.cpow_sub _ _ htC, Complex.cpow_one, div_eq_mul_inv]
      have h2 : (t : ℂ) ^ ((1 - s) - 1) = (t : ℂ) ^ (1 - s) * (t : ℂ)⁻¹ := by
        rw [Complex.cpow_sub _ _ htC, Complex.cpow_one, div_eq_mul_inv]
      rw [h1, h2]
      ring
    rw [setIntegral_congr_fun measurableSet_Ioi hpt,
      MeasureTheory.integral_add (hint_upper s) (hint_upper (1 - s))]
    unfold upperMellinTheta
    congr 1
    · refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
      rw [binaryTheta_eq_latticeTheta, show (2 * s) / 2 - 1 = s - 1 by ring]
    · refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
      rw [latticeTheta_dual_tauLattice_eq, show (2 - 2 * s) / 2 - 1 = (1 - s) - 1 by ring]
  unfold completedEisenstein completedEpsteinZetaExt
  rw [hsplit_int, rk_tauLattice, covol_tauLattice]
  push_cast
  simp only [inv_one, one_mul, mul_one]
  have hp1 : (1 / 2 : ℂ) * (2 / (2 * s - 2)) = -(1 / (2 * (1 - s))) := by
    by_cases hs1 : s = 1
    · subst hs1; simp
    · have h1 : 2 * s - 2 ≠ 0 := by intro h; apply hs1; linear_combination h / 2
      have h2 : 2 * (1 - s) ≠ 0 := by intro h; apply hs1; linear_combination -h / 2
      field_simp [h1, h2]; ring
  have hp2 : (1 / 2 : ℂ) * (2 / (2 * s)) = 1 / (2 * s) := by
    by_cases hs0 : s = 0
    · subst hs0; simp
    · field_simp [hs0]
  linear_combination -hp1 + hp2

/-- **EXACT MELLIN-SPLIT AGREEMENT ON `Re(s) > 1`**:
`completedEisenstein τ s = π^{-s} Γ(s) epsteinEisenstein τ s`. -/
theorem completedEisenstein_eq_mellin_split (τ : UpperHalfPlane) {s : ℂ} (hs : 1 < s.re) :
    completedEisenstein τ s =
      (Real.pi : ℂ) ^ (-s) * Complex.Gamma s * epsteinEisenstein τ s := by
  rw [completedEisenstein_eq_half_completedEpsteinZetaExt]
  have hagree : completedEpsteinZetaExt (tauLattice τ) (2 * s) =
      completedEpsteinZeta (tauLattice τ) (2 * s) := by
    refine completedEpsteinZetaExt_eq_completedEpsteinZeta_of_theta_functional_eq (tauLattice τ) ?_
      (by rw [rk_tauLattice]; simp; linarith)
    intro t ht
    rw [rk_tauLattice, covol_tauLattice, inv_one, mul_one,
      latticeTheta_dual_tauLattice_eq, ← binaryTheta_eq_latticeTheta]
    have hinv := binaryTheta_inv_eq τ ht
    have hpow : t ^ (-(((2 : ℕ) : ℝ) / 2)) = t⁻¹ := by
      push_cast
      rw [show -((2 : ℝ) / 2) = (-1 : ℝ) by norm_num, Real.rpow_neg_one]
    rw [hpow, ← one_div, hinv]
    field_simp [ht.ne']
  rw [hagree, epsteinEisenstein_eq_half_epsteinZeta]
  unfold completedEpsteinZeta
  have h1 : -(2 * s) / 2 = -s := by ring
  have h2 : (2 * s) / 2 = s := by ring
  rw [h1, h2]; ring

/-- **EXACT COMPLETED-ZETA PRODUCT IDENTITY ON `Re(s) > 1`**:
`completedEisenstein τ s = completedRiemannZeta (2 * s) * realEisenstein τ s`. -/
theorem completedEisenstein_eq_completedRiemannZeta_mul (τ : UpperHalfPlane)
    {s : ℂ} (hs : 1 < s.re) :
    completedEisenstein τ s = completedRiemannZeta (2 * s) * realEisenstein τ s := by
  rw [completedEisenstein_eq_mellin_split τ hs, epsteinEisenstein_eq_zeta_mul_realEisenstein τ hs]
  have hs20 : 2 * s ≠ 0 := fun h => by
    have : (2 * s).re = 0 := by rw [h]; simp
    simp at this; linarith
  rw [riemannZeta_def_of_ne_zero hs20, Complex.Gammaℝ_def]
  have h1 : -(2 * s) / 2 = -s := by ring
  have h2 : (2 * s) / 2 = s := by ring
  rw [h1, h2]
  have hpi : (Real.pi : ℂ) ^ (-s) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'))
  have hgam : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by linarith)
  field_simp [hpi, hgam]

/-- **Holomorphicity of `completedEisenstein τ` on `ℂ \ {0, 1}`** (`DifferentiableAt` away from `0, 1`). -/
theorem completedEisenstein_differentiableAt (τ : UpperHalfPlane) {s : ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    DifferentiableAt ℂ (completedEisenstein τ) s := by
  have heq : completedEisenstein τ = fun z => (1 / 2 : ℂ) * completedEpsteinZetaExt (tauLattice τ) (2 * z) :=
    funext (completedEisenstein_eq_half_completedEpsteinZetaExt τ)
  rw [heq]
  have h2s0 : 2 * s ≠ 0 := mul_ne_zero two_ne_zero hs0
  have h2s2 : 2 * s ≠ (rk (tauLattice τ) : ℂ) := by
    rw [rk_tauLattice]; push_cast
    intro h; apply hs1; linear_combination h / 2
  have hdiff := differentiableAt_completedEpsteinZetaExt (tauLattice τ) h2s0 h2s2
  have hmul : DifferentiableAt ℂ (fun z : ℂ => 2 * z) s := differentiableAt_id.const_mul 2
  exact (hdiff.comp s hmul).const_mul (1 / 2 : ℂ)

/-- **Global Meromorphicity on `ℂ \ {0, 1}`** (`DifferentiableOn` on `{0, 1}ᶜ`). -/
theorem completedEisenstein_meromorphic (τ : UpperHalfPlane) :
    DifferentiableOn ℂ (completedEisenstein τ) ({(0 : ℂ), (1 : ℂ)}ᶜ) := by
  intro s hs
  have hs0 : s ≠ 0 := fun h => hs (by simp [h])
  have hs1 : s ≠ 1 := fun h => hs (by simp [h])
  exact (completedEisenstein_differentiableAt τ hs0 hs1).differentiableWithinAt

private lemma tauLattice_ne_bot (τ : UpperHalfPlane) : tauLattice τ ≠ ⊥ := by
  intro hbot
  have hmem : tauVec2 τ ∈ (⊥ : Submodule ℤ (EuclideanSpace ℝ (Fin 2))) :=
    hbot ▸ Submodule.subset_span (Set.mem_insert_of_mem _ rfl)
  have h0 : tauVec2 τ = 0 := by simpa using hmem
  have hval : tauVec2 τ 0 = 0 := by rw [h0]; rfl
  simp only [tauVec2, Matrix.cons_val_zero] at hval
  exact one_div_ne_zero (Real.sqrt_pos.mpr τ.im_pos).ne' hval

/-- **Exact Simple Pole Residue `-1/2` at `s = 0` (independent of `τ`)**:
`lim_{s → 0, s ≠ 0} s * completedEisenstein τ s = -1 / 2`. -/
theorem completedEisenstein_residue_zero (τ : UpperHalfPlane) :
    Tendsto (fun s : ℂ => s * completedEisenstein τ s)
      (nhdsWithin 0 {(0 : ℂ)}ᶜ) (nhds (-1 / 2)) := by
  have hres := completedEpsteinZetaExt_residue_zero (tauLattice τ) (tauLattice_ne_bot τ)
  have hmap : Tendsto (fun s : ℂ => (2 : ℂ) * s) (nhdsWithin 0 {(0 : ℂ)}ᶜ) (nhdsWithin 0 {(0 : ℂ)}ᶜ) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have h0 : Tendsto (fun s : ℂ => (2 : ℂ) * s) (nhds 0) (nhds ((2 : ℂ) * 0)) :=
        (continuous_const.mul continuous_id).continuousAt.tendsto
      rw [mul_zero] at h0
      exact h0.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      exact mul_ne_zero two_ne_zero hs
  have hcomp := (hres.comp hmap).const_mul (1 / 4 : ℂ)
  have hval : (1 / 4 : ℂ) * (-2 : ℂ) = -1 / 2 := by ring
  rw [hval] at hcomp
  refine hcomp.congr fun s => ?_
  dsimp only [Function.comp_def]
  rw [completedEisenstein_eq_half_completedEpsteinZetaExt]
  ring

/-- **Exact Simple Pole Residue `+1/2` at `s = 1` (independent of `τ`)**:
`lim_{s → 1, s ≠ 1} (s - 1) * completedEisenstein τ s = 1 / 2`. -/
theorem completedEisenstein_residue_one (τ : UpperHalfPlane) :
    Tendsto (fun s : ℂ => (s - 1) * completedEisenstein τ s)
      (nhdsWithin 1 {(1 : ℂ)}ᶜ) (nhds (1 / 2)) := by
  have hres := completedEpsteinZetaExt_residue_rk (tauLattice τ) (tauLattice_ne_bot τ)
  rw [rk_tauLattice, covol_tauLattice] at hres
  push_cast at hres
  simp only [inv_one, mul_one] at hres
  have hmap : Tendsto (fun s : ℂ => (2 : ℂ) * s) (nhdsWithin 1 {(1 : ℂ)}ᶜ) (nhdsWithin 2 {(2 : ℂ)}ᶜ) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have h0 : Tendsto (fun s : ℂ => (2 : ℂ) * s) (nhds 1) (nhds ((2 : ℂ) * 1)) :=
        (continuous_const.mul continuous_id).continuousAt.tendsto
      rw [mul_one] at h0
      exact h0.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      have hne : s ≠ 1 := hs
      intro h2
      have h2' : (2 : ℂ) * s = 2 := Set.mem_singleton_iff.mp h2
      apply hne; linear_combination h2' / 2
  have hcomp := (hres.comp hmap).const_mul (1 / 4 : ℂ)
  have hval : (1 / 4 : ℂ) * (2 : ℂ) = 1 / 2 := by ring
  rw [hval] at hcomp
  refine hcomp.congr fun s => ?_
  dsimp only [Function.comp_def]
  rw [completedEisenstein_eq_half_completedEpsteinZetaExt]
  ring

/-- Exact Basel evaluation `riemannZeta 2 = Real.pi ^ 2 / 6`. -/
lemma riemannZeta_two_eq : riemannZeta 2 = (Real.pi : ℂ) ^ 2 / 6 := by
  rw [zeta_eq_tsum_one_div_nat_cpow (by norm_num : 1 < (2 : ℂ).re)]
  have hbasel : (∑' n : ℕ, 1 / (n : ℝ) ^ 2) = Real.pi ^ 2 / 6 := hasSum_zeta_two.tsum_eq
  have hC := congrArg (fun r : ℝ => (r : ℂ)) hbasel
  rw [Complex.ofReal_tsum] at hC
  rw [show (Real.pi : ℂ) ^ 2 / 6 = ((Real.pi ^ 2 / 6 : ℝ) : ℂ) by push_cast; rfl, ← hC]
  refine tsum_congr fun n => ?_
  push_cast
  rw [Complex.cpow_ofNat]

/-- Exact value `completedRiemannZeta 2 = Real.pi / 6`. -/
theorem completedRiemannZeta_two : completedRiemannZeta 2 = (Real.pi : ℂ) / 6 := by
  have h20 : (2 : ℂ) ≠ 0 := two_ne_zero
  have hz := riemannZeta_def_of_ne_zero h20
  rw [riemannZeta_two_eq, Complex.Gammaℝ_def, show -(2 : ℂ) / 2 = -1 by ring,
    show (2 : ℂ) / 2 = 1 by ring, Complex.Gamma_one, mul_one,
    Complex.cpow_neg_one] at hz
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
  have h1 := congrArg (· * (Real.pi : ℂ)⁻¹) hz
  rw [div_mul_cancel₀ _ (inv_ne_zero hpi)] at h1
  rw [← h1]
  field_simp [hpi]

/-- **Exact Simple Pole Residue `3 / π = 1 / vol(SL₂(ℤ) \ ℍ)` of the Meromorphically Continued
Eisenstein Series `E(τ, s) = E*(τ, s) / Λ(2s)` at `s = 1`**:
$$\operatorname{Res}_{s = 1} E(\tau, s) = \frac{3}{\pi}.$$ -/
theorem realEisensteinExt_residue_one (τ : UpperHalfPlane) :
    Tendsto (fun s : ℂ => (s - 1) * (completedEisenstein τ s / completedRiemannZeta (2 * s)))
      (nhdsWithin 1 {(1 : ℂ)}ᶜ) (nhds (3 / (Real.pi : ℂ))) := by
  have hnum := completedEisenstein_residue_one τ
  have hden_cont : ContinuousAt (fun s : ℂ => completedRiemannZeta (2 * s)) 1 := by
    have hdiff : DifferentiableAt ℂ completedRiemannZeta ((2 : ℂ) * 1) := by
      rw [mul_one]; exact differentiableAt_completedZeta two_ne_zero (by norm_num)
    have hmul : ContinuousAt (fun s : ℂ => (2 : ℂ) * s) 1 :=
      (continuous_const.mul continuous_id).continuousAt
    exact ContinuousAt.comp (f := fun s : ℂ => (2 : ℂ) * s) (g := completedRiemannZeta)
      hdiff.continuousAt hmul
  have hden : Tendsto (fun s : ℂ => completedRiemannZeta (2 * s))
      (nhdsWithin 1 {(1 : ℂ)}ᶜ) (nhds ((Real.pi : ℂ) / 6)) := by
    have h2 : completedRiemannZeta ((2 : ℂ) * 1) = (Real.pi : ℂ) / 6 := by
      rw [mul_one, completedRiemannZeta_two]
    rw [← h2]
    exact hden_cont.tendsto.mono_left nhdsWithin_le_nhds
  have hpi6 : ((Real.pi : ℂ) / 6) ≠ 0 :=
    div_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_pos.ne') (by norm_num)
  have hdiv := hnum.div hden hpi6
  have hval : (1 / 2 : ℂ) / ((Real.pi : ℂ) / 6) = 3 / (Real.pi : ℂ) := by
    have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
    field_simp [hpi]; ring
  rw [hval] at hdiv
  refine hdiv.congr fun s => ?_
  dsimp only [Pi.div_apply]
  ring

/-- **EXACT `SL₂(ℤ)`-INVARIANCE OF `completedEisenstein` FOR ALL `τ ∈ ℍ` AND ALL `s ∈ ℂ`**. -/
theorem completedEisenstein_SL2Z_invariant (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (τ : UpperHalfPlane) (s : ℂ) :
    completedEisenstein (γ • τ) s = completedEisenstein τ s := by
  unfold completedEisenstein
  simp_rw [binaryTheta_SL2Z_invariant]

/-- **EXACT GLOBAL FUNCTIONAL EQUATION OF THE COMPLETED EISENSTEIN SERIES (`0` ASSUMPTIONS!)**:
for EVERY `τ ∈ ℍ` and EVERY `s ∈ ℂ`,
$$E^*(\tau, 1 - s) = E^*(\tau, s).$$ -/
theorem completedEisenstein_functional_equation (τ : UpperHalfPlane) (s : ℂ) :
    completedEisenstein τ (1 - s) = completedEisenstein τ s := by
  unfold completedEisenstein
  have hsub : 1 - (1 - s) = s := by ring
  rw [hsub]
  have hint : (∫ t in Set.Ioi (1 : ℝ),
      ((binaryTheta τ t - 1 : ℝ) : ℂ) * ((t : ℂ) ^ (1 - s) + (t : ℂ) ^ s) * (t : ℂ)⁻¹) =
      ∫ t in Set.Ioi (1 : ℝ),
      ((binaryTheta τ t - 1 : ℝ) : ℂ) * ((t : ℂ) ^ s + (t : ℂ) ^ (1 - s)) * (t : ℂ)⁻¹ := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    rw [add_comm ((t : ℂ) ^ (1 - s))]
  rw [hint]
  ring

end BinaryThetaAndFunctionalEquation

/-! ## Section 4: Exact Constant Term `∫₀¹ E(x + i y, s) dx`, Totient Series & Unitary Scattering Matrix -/

section ConstantTermAndScatteringMatrix

/-! ### Part 4A: Gaussian–Gamma Fubini Integral `∫_{-∞}^∞ (t² + 1)^{-s} dt = √π Γ(s - 1/2) / Γ(s)` -/

/-- Real integrability of `t ↦ (t² + 1)^{-σ}` on `ℝ` for every `σ > 1 / 2`. -/
lemma integrable_one_add_sq_rpow_neg {σ : ℝ} (hσ : 1 / 2 < σ) :
    Integrable (fun t : ℝ => (t ^ 2 + 1) ^ (-σ)) volume := by
  have hσ0 : 0 < σ := by linarith
  have hcont : Continuous (fun t : ℝ => (t ^ 2 + 1) ^ (-σ)) :=
    Continuous.rpow_const (by fun_prop) (fun t => Or.inl (by positivity))
  have hint_pos : IntegrableOn (fun t : ℝ => (t ^ 2 + 1) ^ (-σ)) (Set.Ioi 1) volume := by
    have hdom : IntegrableOn (fun t : ℝ => t ^ (-2 * σ)) (Set.Ioi 1) volume :=
      integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one
    refine hdom.mono' hcont.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := lt_trans zero_lt_one ht
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (by positivity) _)]
    calc (t ^ 2 + 1) ^ (-σ)
        ≤ (t ^ 2) ^ (-σ) :=
          Real.rpow_le_rpow_of_nonpos (sq_pos_of_pos ht0) (by linarith) (neg_nonpos.mpr hσ0.le)
      _ = t ^ (-2 * σ) := by
          rw [← Real.rpow_natCast t 2, ← Real.rpow_mul ht0.le]; push_cast; congr 1; ring
  have hint_neg : IntegrableOn (fun t : ℝ => (t ^ 2 + 1) ^ (-σ)) (Set.Iio (-1)) volume := by
    have hcomp := hint_pos.comp_neg
    have hset : -Set.Ioi (1 : ℝ) = Set.Iio (-1 : ℝ) := by
      ext x; simp [lt_neg]
    rw [hset] at hcomp
    refine hcomp.congr_fun (fun t _ => by simp) measurableSet_Iio
  have hint_mid : IntegrableOn (fun t : ℝ => (t ^ 2 + 1) ^ (-σ)) (Set.Icc (-1) 1) volume :=
    hcont.integrableOn_Icc
  have hunion : (Set.Iio (-1 : ℝ) ∪ Set.Icc (-1) 1) ∪ Set.Ioi (1 : ℝ) = Set.univ := by
    ext x; simp only [Set.mem_union, Set.mem_Iio, Set.mem_Icc, Set.mem_Ioi, Set.mem_univ, iff_true]
    by_cases h1 : x < -1
    · exact Or.inl (Or.inl h1)
    · by_cases h2 : x ≤ 1
      · exact Or.inl (Or.inr ⟨not_lt.mp h1, h2⟩)
      · exact Or.inr (not_le.mp h2)
  rw [← integrableOn_univ, ← hunion]
  exact (hint_neg.union hint_mid).union hint_pos

/-- Complex integrability of `t ↦ (t² + 1)^{-s}` on `ℝ` for `Re(s) > 1 / 2`. -/
lemma integrable_one_add_sq_cpow_neg {s : ℂ} (hs : 1 / 2 < s.re) :
    Integrable (fun t : ℝ => ((t ^ 2 + 1 : ℝ) : ℂ) ^ (-s)) volume := by
  have hcont : Continuous (fun t : ℝ => ((t ^ 2 + 1 : ℝ) : ℂ) ^ (-s)) := by
    refine Continuous.cpow ?_ continuous_const ?_
    · exact Complex.continuous_ofReal.comp (by fun_prop)
    · intro t; exact Or.inl (by rw [Complex.ofReal_re]; positivity)
  refine (integrable_one_add_sq_rpow_neg hs).mono' hcont.aestronglyMeasurable ?_
  filter_upwards with t
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (by positivity), Complex.neg_re]

/-- **Exact Gaussian–Gamma Fubini Evaluation**:
for every `s : ℂ` with `1 / 2 < s.re`,
$$\int_{-\infty}^{\infty} (t^2 + 1)^{-s}\,dt = \frac{\sqrt{\pi}\,\Gamma(s - 1/2)}{\Gamma(s)}.$$ -/
theorem integral_one_add_sq_cpow_neg {s : ℂ} (hs : 1 / 2 < s.re) :
    ∫ t : ℝ, ((t ^ 2 + 1 : ℝ) : ℂ) ^ (-s) =
      ((Real.sqrt Real.pi : ℝ) : ℂ) * Complex.Gamma (s - 1 / 2) / Complex.Gamma s := by
  have hs0 : 0 < s.re := by linarith
  have hs_half : 0 < (s - 1 / 2).re := by simp; linarith
  have hgam_ne : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hs0
  let ν : Measure ℝ := volume.restrict (Set.Ioi (0 : ℝ))
  let F : ℝ → ℝ → ℂ := fun t u =>
    ((Real.exp (-((t ^ 2 + 1) * u)) : ℝ) : ℂ) * (u : ℂ) ^ (s - 1)
  -- Joint integrability of `F` on `ℝ × (0, ∞)` via Tonelli (`integrable_prod_iff'`)
  have hF_meas : AEStronglyMeasurable (Function.uncurry F) (volume.prod ν) := by
    have hcont : ContinuousOn (Function.uncurry F) (Set.univ ×ˢ Set.Ioi (0 : ℝ)) := by
      intro p hp
      have hu : 0 < p.2 := hp.2
      have h1 : ContinuousAt (fun q : ℝ × ℝ => ((Real.exp (-((q.1 ^ 2 + 1) * q.2)) : ℝ) : ℂ)) p :=
        (Complex.continuous_ofReal.comp (Real.continuous_exp.comp (by fun_prop))).continuousAt
      have h2 : ContinuousAt (fun q : ℝ × ℝ => (q.2 : ℂ) ^ (s - 1)) p :=
        (continuousAt_ofReal_cpow_const hu (s - 1)).comp continuous_snd.continuousAt
      exact (h1.mul h2).continuousWithinAt
    have hmeas_set : MeasurableSet ((Set.univ : Set ℝ) ×ˢ Set.Ioi (0 : ℝ)) :=
      MeasurableSet.univ.prod measurableSet_Ioi
    have hsub : AEStronglyMeasurable (Function.uncurry F)
        ((volume.prod ν).restrict ((Set.univ : Set ℝ) ×ˢ Set.Ioi (0 : ℝ))) :=
      hcont.aestronglyMeasurable hmeas_set
    have hprod_eq : (volume.prod ν).restrict ((Set.univ : Set ℝ) ×ˢ Set.Ioi (0 : ℝ)) = volume.prod ν := by
      have h1 : (volume : Measure ℝ).restrict (Set.univ : Set ℝ) = volume := Measure.restrict_univ
      have h2 : ν.restrict (Set.Ioi (0 : ℝ)) = ν :=
        Measure.restrict_restrict_of_subset (Set.Subset.refl (Set.Ioi (0 : ℝ)))
      calc (volume.prod ν).restrict ((Set.univ : Set ℝ) ×ˢ Set.Ioi (0 : ℝ))
          = ((volume : Measure ℝ).restrict (Set.univ : Set ℝ)).prod (ν.restrict (Set.Ioi (0 : ℝ))) :=
            (Measure.prod_restrict (Set.univ : Set ℝ) (Set.Ioi (0 : ℝ))).symm
        _ = volume.prod ν := by rw [h1, h2]
    rwa [hprod_eq] at hsub
  have hF_int_t : ∀ᵐ u ∂ν, Integrable (fun t : ℝ => F t u) volume := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : 0 < u := hu
    have hgauss : Integrable (fun t : ℝ => Real.exp (-u * t ^ 2)) volume :=
      integrable_exp_neg_mul_sq hu0
    have hcont : Continuous (fun t : ℝ => F t u) :=
      (Complex.continuous_ofReal.comp (Real.continuous_exp.comp (by fun_prop))).mul continuous_const
    refine ((hgauss.const_mul (Real.exp (-u) * u ^ (s.re - 1)))).mono' hcont.aestronglyMeasurable ?_
    filter_upwards with t
    dsimp only [F]
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le,
      Complex.norm_cpow_eq_rpow_re_of_pos hu0, Complex.sub_re, Complex.one_re,
      show -((t ^ 2 + 1) * u) = -u + (-u * t ^ 2) by ring, Real.exp_add]
    have : Real.exp (-u) * Real.exp (-u * t ^ 2) * u ^ (s.re - 1) =
        Real.exp (-u) * u ^ (s.re - 1) * Real.exp (-u * t ^ 2) := by ring
    exact le_of_eq this
  have hnorm_inner : ∀ u ∈ Set.Ioi (0 : ℝ),
      (∫ t : ℝ, ‖F t u‖) = Real.sqrt Real.pi * (Real.exp (-u) * u ^ (s.re - 1 / 2 - 1)) := by
    intro u hu
    have hu0 : 0 < u := hu
    have hpt : (fun t : ℝ => ‖F t u‖) =
        fun t : ℝ => (Real.exp (-u) * u ^ (s.re - 1)) * Real.exp (-u * t ^ 2) := by
      funext t
      dsimp only [F]
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le,
        Complex.norm_cpow_eq_rpow_re_of_pos hu0, Complex.sub_re, Complex.one_re,
        show -((t ^ 2 + 1) * u) = -u + (-u * t ^ 2) by ring, Real.exp_add]
      ring
    rw [hpt, MeasureTheory.integral_const_mul, integral_gaussian u,
      Real.sqrt_div Real.pi_pos.le, Real.sqrt_eq_rpow u, div_eq_mul_inv,
      ← Real.rpow_neg hu0.le]
    have hpow : u ^ (s.re - 1) * u ^ (-(1 / 2 : ℝ)) = u ^ (s.re - 1 / 2 - 1) := by
      rw [← Real.rpow_add hu0]; congr 1; ring
    calc Real.exp (-u) * u ^ (s.re - 1) * (Real.sqrt Real.pi * u ^ (-(1 / 2 : ℝ)))
        = Real.sqrt Real.pi * (Real.exp (-u) * (u ^ (s.re - 1) * u ^ (-(1 / 2 : ℝ)))) := by ring
      _ = Real.sqrt Real.pi * (Real.exp (-u) * u ^ (s.re - 1 / 2 - 1)) := by rw [hpow]
  have hF_int_u : Integrable (fun u : ℝ => ∫ t : ℝ, ‖F t u‖) ν := by
    have hgam_int : IntegrableOn (fun u : ℝ => Real.exp (-(1 * u)) * u ^ ((s.re - 1 / 2) - 1))
        (Set.Ioi 0) volume :=
      integrableOn_exp_neg_mul_rpow one_pos (by linarith)
    exact IntegrableOn.congr_fun (hgam_int.const_mul (Real.sqrt Real.pi))
      (fun u hu => by rw [one_mul, hnorm_inner u hu]) measurableSet_Ioi
  have hF_prod : Integrable (Function.uncurry F) (volume.prod ν) :=
    (MeasureTheory.integrable_prod_iff' hF_meas).mpr ⟨hF_int_t, hF_int_u⟩
  -- Apply Fubini (`integral_integral_swap`)
  have hswap : (∫ t : ℝ, (∫ u : ℝ, F t u ∂ν)) = ∫ u : ℝ, (∫ t : ℝ, F t u) ∂ν :=
    MeasureTheory.integral_integral_swap hF_prod
  -- Evaluate LHS: `∫ t, ∫ u in Ioi 0, F t u = (∫ t, (t² + 1)^{-s}) * Γ(s)`
  have hlhs : (∫ t : ℝ, (∫ u : ℝ, F t u ∂ν)) =
      (∫ t : ℝ, ((t ^ 2 + 1 : ℝ) : ℂ) ^ (-s)) * Complex.Gamma s := by
    have hinner : ∀ t : ℝ, (∫ u : ℝ, F t u ∂ν) =
        ((t ^ 2 + 1 : ℝ) : ℂ) ^ (-s) * Complex.Gamma s := fun t =>
      mellin_exp_neg_mul (by positivity : 0 < t ^ 2 + 1) hs0
    simp_rw [hinner]
    exact MeasureTheory.integral_mul_const _ _
  -- Evaluate RHS: `∫ u in Ioi 0, ∫ t, F t u = √π * Γ(s - 1/2)`
  have hrhs : (∫ u : ℝ, (∫ t : ℝ, F t u) ∂ν) =
      ((Real.sqrt Real.pi : ℝ) : ℂ) * Complex.Gamma (s - 1 / 2) := by
    have hinner : Set.EqOn (fun u : ℝ => ∫ t : ℝ, F t u)
        (fun u : ℝ => ((Real.sqrt Real.pi : ℝ) : ℂ) *
          (((Real.exp (-(1 * u)) : ℝ) : ℂ) * (u : ℂ) ^ ((s - 1 / 2) - 1))) (Set.Ioi 0) := by
      intro u hu
      have hu0 : 0 < u := hu
      dsimp only
      have hpt : (fun t : ℝ => F t u) =
          fun t : ℝ => (((Real.exp (-u) : ℝ) : ℂ) * (u : ℂ) ^ (s - 1)) *
            ((Real.exp (-u * t ^ 2) : ℝ) : ℂ) := by
        funext t
        dsimp only [F]
        rw [show -((t ^ 2 + 1) * u) = -u + (-u * t ^ 2) by ring, Real.exp_add, Complex.ofReal_mul]
        ring
      have hgC : (∫ a : ℝ, ((Real.exp (-u * a ^ 2) : ℝ) : ℂ)) =
          ((∫ a : ℝ, Real.exp (-u * a ^ 2) : ℝ) : ℂ) := integral_ofReal
      rw [hpt, MeasureTheory.integral_const_mul, hgC, integral_gaussian u,
        Real.sqrt_div Real.pi_pos.le, Real.sqrt_eq_rpow u, div_eq_mul_inv,
        ← Real.rpow_neg hu0.le, Complex.ofReal_mul, Complex.ofReal_cpow hu0.le]
      have hpow : (u : ℂ) ^ (s - 1) * (u : ℂ) ^ ((-(1 / 2 : ℝ) : ℝ) : ℂ) =
          (u : ℂ) ^ ((s - 1 / 2) - 1) := by
        rw [← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hu0.ne')]
        congr 1; push_cast; ring
      rw [one_mul]
      calc ((Real.exp (-u) : ℝ) : ℂ) * (u : ℂ) ^ (s - 1) *
              (((Real.sqrt Real.pi : ℝ) : ℂ) * (u : ℂ) ^ ((-(1 / 2 : ℝ) : ℝ) : ℂ))
          = ((Real.sqrt Real.pi : ℝ) : ℂ) *
              (((Real.exp (-u) : ℝ) : ℂ) * ((u : ℂ) ^ (s - 1) * (u : ℂ) ^ ((-(1 / 2 : ℝ) : ℝ) : ℂ))) := by ring
        _ = ((Real.sqrt Real.pi : ℝ) : ℂ) *
              (((Real.exp (-u) : ℝ) : ℂ) * (u : ℂ) ^ ((s - 1 / 2) - 1)) := by rw [hpow]
    dsimp only [ν]
    rw [setIntegral_congr_fun measurableSet_Ioi hinner, MeasureTheory.integral_const_mul,
      mellin_exp_neg_mul one_pos hs_half, Complex.ofReal_one, Complex.one_cpow, one_mul]
  rw [hlhs, hrhs] at hswap
  exact (eq_div_iff hgam_ne).mpr hswap

/-! ### Part 4B: Affine Periodization `∑'_{d ∈ ℤ} ∫₀¹ f(c x + d) dx = ∫_{-∞}^∞ f(u) du` -/

/-- Bijection `ℤ ≃ ℤ × Fin c` via Euclidean division by `c > 0`. -/
private def intEquivProdFin {c : ℕ} (hc : 0 < c) : ℤ ≃ ℤ × Fin c where
  toFun d := (d / (c : ℤ), ⟨(d % (c : ℤ)).toNat, by
    have hnn : 0 ≤ d % (c : ℤ) := Int.emod_nonneg d (by exact_mod_cast hc.ne')
    have hlt : d % (c : ℤ) < (c : ℤ) := Int.emod_lt_of_pos d (by exact_mod_cast hc)
    omega⟩)
  invFun kr := kr.1 * (c : ℤ) + (kr.2.1 : ℤ)
  left_inv d := by
    have hnn : 0 ≤ d % (c : ℤ) := Int.emod_nonneg d (by exact_mod_cast hc.ne')
    have htoNat : ((d % (c : ℤ)).toNat : ℤ) = d % (c : ℤ) := Int.toNat_of_nonneg hnn
    dsimp only
    rw [htoNat]
    exact Int.ediv_mul_add_emod d (c : ℤ)
  right_inv kr := by
    rcases kr with ⟨k, ⟨r, hr⟩⟩
    have hcZ : (0 : ℤ) < (c : ℤ) := by exact_mod_cast hc
    have hr_nn : (0 : ℤ) ≤ (r : ℤ) := by positivity
    have hr_lt : (r : ℤ) < (c : ℤ) := by exact_mod_cast hr
    have hdiv : (k * (c : ℤ) + (r : ℤ)) / (c : ℤ) = k := by
      rw [Int.add_ediv_of_dvd_left (dvd_mul_left _ _), Int.mul_ediv_cancel _ hcZ.ne',
        Int.ediv_eq_zero_of_lt hr_nn hr_lt, add_zero]
    have hmod : (k * (c : ℤ) + (r : ℤ)) % (c : ℤ) = (r : ℤ) := by
      rw [Int.add_emod, Int.mul_emod_left, zero_add, Int.emod_emod,
        Int.emod_eq_of_lt hr_nn hr_lt]
    apply Prod.ext
    · exact hdiv
    · apply Fin.ext; dsimp only; rw [hmod]; omega

/-- Disjointness and full covering of `ℝ` by `Ioc (k c + r) ((k + 1) c + r)`. -/
private lemma ioc_shift_pairwise_disjoint {c : ℕ} (hc : 0 < c) (r : Fin c) :
    Pairwise (Function.onFun Disjoint fun k : ℤ =>
      Set.Ioc (((k * (c : ℤ) + (r.1 : ℤ) : ℤ) : ℝ)) (((k * (c : ℤ) + (r.1 : ℤ) : ℤ) : ℝ) + (c : ℝ))) := by
  intro k₁ k₂ hne
  have hcR : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hc
  rw [Function.onFun, Set.disjoint_left]
  intro u hu1 hu2
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hk : (k₁ : ℝ) + 1 ≤ (k₂ : ℝ) := by exact_mod_cast Int.add_one_le_iff.mpr hlt
    have hle : ((k₁ * (c : ℤ) + (r.1 : ℤ) : ℤ) : ℝ) + (c : ℝ) ≤
        ((k₂ * (c : ℤ) + (r.1 : ℤ) : ℤ) : ℝ) := by push_cast; nlinarith
    linarith [hu1.2, hu2.1]
  · have hk : (k₂ : ℝ) + 1 ≤ (k₁ : ℝ) := by exact_mod_cast Int.add_one_le_iff.mpr hgt
    have hle : ((k₂ * (c : ℤ) + (r.1 : ℤ) : ℤ) : ℝ) + (c : ℝ) ≤
        ((k₁ * (c : ℤ) + (r.1 : ℤ) : ℤ) : ℝ) := by push_cast; nlinarith
    linarith [hu2.2, hu1.1]

private lemma iUnion_ioc_shift_eq_univ {c : ℕ} (hc : 0 < c) (r : Fin c) :
    (⋃ k : ℤ, Set.Ioc (((k * (c : ℤ) + (r.1 : ℤ) : ℤ) : ℝ))
      (((k * (c : ℤ) + (r.1 : ℤ) : ℤ) : ℝ) + (c : ℝ))) = Set.univ := by
  have hcR : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hc
  ext u
  simp only [Set.mem_iUnion, Set.mem_Ioc, Set.mem_univ, iff_true]
  let k : ℤ := ⌈(u - (r.1 : ℝ)) / (c : ℝ)⌉ - 1
  refine ⟨k, ?_, ?_⟩
  · have hlt : (k : ℝ) < (u - (r.1 : ℝ)) / (c : ℝ) := by
      dsimp only [k]; push_cast
      linarith [Int.ceil_lt_add_one ((u - (r.1 : ℝ)) / (c : ℝ))]
    have hmul := (lt_div_iff₀ hcR).mp hlt
    push_cast; linarith
  · have hle : (u - (r.1 : ℝ)) / (c : ℝ) ≤ (k : ℝ) + 1 := by
      dsimp only [k]; push_cast
      linarith [Int.le_ceil ((u - (r.1 : ℝ)) / (c : ℝ))]
    have hmul := (div_le_iff₀ hcR).mp hle
    push_cast; linarith

/-- Change of variables for `Ioc 0 1` under `x ↦ c * x + d` (`c > 0`, Bochner integral in any Banach space `E`). -/
private lemma setIntegral_Ioc_zero_one_affine {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {c : ℕ} (hc : 0 < c) (d : ℤ) :
    (∫ x in Set.Ioc (0 : ℝ) 1, f ((c : ℝ) * x + (d : ℝ))) =
      ((c : ℝ)⁻¹ : ℝ) • ∫ u in Set.Ioc (d : ℝ) ((d : ℝ) + (c : ℝ)), f u := by
  have hcR : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hc
  have hind : (fun x : ℝ => (Set.Ioc (0 : ℝ) 1).indicator (fun x => f ((c : ℝ) * x + (d : ℝ))) x) =
      fun x : ℝ => (Set.Ioc (d : ℝ) ((d : ℝ) + (c : ℝ))).indicator f ((c : ℝ) * x + (d : ℝ)) := by
    funext x
    by_cases hx : x ∈ Set.Ioc (0 : ℝ) 1
    · have hu : (c : ℝ) * x + (d : ℝ) ∈ Set.Ioc (d : ℝ) ((d : ℝ) + (c : ℝ)) :=
        ⟨by nlinarith [hx.1], by nlinarith [hx.2]⟩
      rw [Set.indicator_of_mem hx, Set.indicator_of_mem hu]
    · have hu : (c : ℝ) * x + (d : ℝ) ∉ Set.Ioc (d : ℝ) ((d : ℝ) + (c : ℝ)) := by
        intro h; apply hx
        exact ⟨by nlinarith [h.1], by nlinarith [h.2]⟩
      rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hu]
  rw [← MeasureTheory.integral_indicator measurableSet_Ioc, hind]
  let g : ℝ → E := fun u => (Set.Ioc (d : ℝ) ((d : ℝ) + (c : ℝ))).indicator f (u + (d : ℝ))
  change (∫ x : ℝ, g ((c : ℝ) * x)) = _
  rw [Measure.integral_comp_mul_left g (c : ℝ), abs_of_pos (inv_pos.mpr hcR)]
  congr 1
  dsimp only [g]
  rw [MeasureTheory.integral_add_right_eq_self
    ((Set.Ioc (d : ℝ) ((d : ℝ) + (c : ℝ))).indicator f) (d : ℝ),
    MeasureTheory.integral_indicator measurableSet_Ioc]

/-- **Exact Bochner Affine Periodization Identity (any Banach space `E`)**:
`∑' d : ℤ, ∫ x in Ioc 0 1, f (c * x + d) = ∫ u : ℝ, f u`. -/
private lemma tsum_setIntegral_Ioc_zero_one_affine {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {f : ℝ → E} (hf : Integrable f volume) {c : ℕ} (hc : 0 < c) :
    (∑' d : ℤ, ∫ x in Set.Ioc (0 : ℝ) 1, f ((c : ℝ) * x + (d : ℝ))) = ∫ u : ℝ, f u := by
  have hcR : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hc
  simp_rw [setIntegral_Ioc_zero_one_affine hc]
  have hprod_sum : Summable (fun kr : ℤ × Fin c =>
      ∫ u in Set.Ioc (((kr.1 * (c : ℤ) + (kr.2.1 : ℤ) : ℤ) : ℝ))
        (((kr.1 * (c : ℤ) + (kr.2.1 : ℤ) : ℤ) : ℝ) + (c : ℝ)), f u) := by
    refine Summable.of_norm ?_
    have hnorm_le : ∀ kr : ℤ × Fin c,
        ‖∫ u in Set.Ioc (((kr.1 * (c : ℤ) + (kr.2.1 : ℤ) : ℤ) : ℝ))
          (((kr.1 * (c : ℤ) + (kr.2.1 : ℤ) : ℤ) : ℝ) + (c : ℝ)), f u‖ ≤
        ∫ u in Set.Ioc (((kr.1 * (c : ℤ) + (kr.2.1 : ℤ) : ℤ) : ℝ))
          (((kr.1 * (c : ℤ) + (kr.2.1 : ℤ) : ℤ) : ℝ) + (c : ℝ)), ‖f u‖ := fun _ =>
      MeasureTheory.norm_integral_le_integral_norm _
    have hsum_r : ∀ r : Fin c, Summable (fun k : ℤ =>
        ∫ u in Set.Ioc (((k * (c : ℤ) + (r.1 : ℤ) : ℤ) : ℝ))
          (((k * (c : ℤ) + (r.1 : ℤ) : ℤ) : ℝ) + (c : ℝ)), ‖f u‖) := by
      intro r
      have hint_u : IntegrableOn (fun u => ‖f u‖)
          (⋃ k : ℤ, Set.Ioc (((k * (c : ℤ) + (r.1 : ℤ) : ℤ) : ℝ))
            (((k * (c : ℤ) + (r.1 : ℤ) : ℤ) : ℝ) + (c : ℝ))) volume := by
        rw [iUnion_ioc_shift_eq_univ hc r, integrableOn_univ]; exact hf.norm
      exact (MeasureTheory.hasSum_integral_iUnion (fun _ => measurableSet_Ioc)
        (ioc_shift_pairwise_disjoint hc r) hint_u).summable
    have hsum_prod : Summable (fun kr : ℤ × Fin c =>
        ∫ u in Set.Ioc (((kr.1 * (c : ℤ) + (kr.2.1 : ℤ) : ℤ) : ℝ))
          (((kr.1 * (c : ℤ) + (kr.2.1 : ℤ) : ℤ) : ℝ) + (c : ℝ)), ‖f u‖) := by
      rw [← (Equiv.prodComm (Fin c) ℤ).summable_iff]
      exact (summable_prod_of_nonneg (fun _ => MeasureTheory.integral_nonneg fun _ => norm_nonneg _)).mpr
        ⟨fun r => hsum_r r, (hasSum_fintype _).summable⟩
    exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hnorm_le hsum_prod
  have hsum_d : Summable (fun d : ℤ => ∫ u in Set.Ioc (d : ℝ) ((d : ℝ) + (c : ℝ)), f u) :=
    (Equiv.summable_iff (intEquivProdFin hc).symm).mp hprod_sum
  have hsmul_tsum : (∑' d : ℤ, ((c : ℝ)⁻¹ : ℝ) • ∫ u in Set.Ioc (d : ℝ) ((d : ℝ) + (c : ℝ)), f u) =
      ((c : ℝ)⁻¹ : ℝ) • ∑' d : ℤ, ∫ u in Set.Ioc (d : ℝ) ((d : ℝ) + (c : ℝ)), f u :=
    ((((c : ℝ)⁻¹ : ℝ) • ContinuousLinearMap.id ℝ E).map_tsum hsum_d).symm
  rw [hsmul_tsum, ← (intEquivProdFin hc).symm.tsum_eq]
  have hcongr_symm : (∑' kr : ℤ × Fin c,
      ∫ u in Set.Ioc (((intEquivProdFin hc).symm kr : ℤ) : ℝ)
        ((((intEquivProdFin hc).symm kr : ℤ) : ℝ) + (c : ℝ)), f u) =
      ∑' kr : ℤ × Fin c,
      ∫ u in Set.Ioc (((kr.1 * (c : ℤ) + (kr.2.1 : ℤ) : ℤ) : ℝ))
        (((kr.1 * (c : ℤ) + (kr.2.1 : ℤ) : ℤ) : ℝ) + (c : ℝ)), f u := rfl
  rw [hcongr_symm, hprod_sum.tsum_prod]
  have hcomm : (∑' k : ℤ, ∑' r : Fin c,
      ∫ u in Set.Ioc (((k * (c : ℤ) + (r.1 : ℤ) : ℤ) : ℝ))
        (((k * (c : ℤ) + (r.1 : ℤ) : ℤ) : ℝ) + (c : ℝ)), f u) =
      ∑' r : Fin c, ∑' k : ℤ,
      ∫ u in Set.Ioc (((k * (c : ℤ) + (r.1 : ℤ) : ℤ) : ℝ))
        (((k * (c : ℤ) + (r.1 : ℤ) : ℤ) : ℝ) + (c : ℝ)), f u :=
    hprod_sum.tsum_comm.symm
  rw [hcomm]
  have hinner : ∀ r : Fin c,
      (∑' k : ℤ, ∫ u in Set.Ioc (((k * (c : ℤ) + (r.1 : ℤ) : ℤ) : ℝ))
        (((k * (c : ℤ) + (r.1 : ℤ) : ℤ) : ℝ) + (c : ℝ)), f u) = ∫ u : ℝ, f u := by
    intro r
    have hint_u : IntegrableOn f
        (⋃ k : ℤ, Set.Ioc (((k * (c : ℤ) + (r.1 : ℤ) : ℤ) : ℝ))
          (((k * (c : ℤ) + (r.1 : ℤ) : ℤ) : ℝ) + (c : ℝ))) volume := by
      rw [iUnion_ioc_shift_eq_univ hc r, integrableOn_univ]; exact hf
    have hhas := MeasureTheory.hasSum_integral_iUnion (fun _ => measurableSet_Ioc)
      (ioc_shift_pairwise_disjoint hc r) hint_u
    rw [iUnion_ioc_shift_eq_univ hc r, Measure.restrict_univ] at hhas
    exact hhas.tsum_eq
  simp_rw [hinner, tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul ℝ c, smul_smul, inv_mul_cancel₀ hcR.ne', one_smul]

/-- **Exact `ENNReal` Affine Periodization Identity for Nonnegative Integrable Functions**:
`∑' d : ℤ, ∫⁻ x in Ioc 0 1, ENNReal.ofReal (g (c * x + d)) = ENNReal.ofReal (∫ u : ℝ, g u)`. -/
private lemma tsum_setLIntegral_ofReal_Ioc_zero_one_affine {g : ℝ → ℝ}
    (hg_int : Integrable g volume) (hg_nn : ∀ u, 0 ≤ g u) {c : ℕ} (hc : 0 < c) :
    (∑' d : ℤ, ∫⁻ x in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal (g ((c : ℝ) * x + (d : ℝ)))) =
      ENNReal.ofReal (∫ u : ℝ, g u) := by
  have hcR : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hc
  have hterm : ∀ d : ℤ,
      (∫⁻ x in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal (g ((c : ℝ) * x + (d : ℝ)))) =
        ENNReal.ofReal (∫ x in Set.Ioc (0 : ℝ) 1, g ((c : ℝ) * x + (d : ℝ))) := by
    intro d
    have hg_aff : Integrable (fun x : ℝ => g ((c : ℝ) * x + (d : ℝ))) volume :=
      (hg_int.comp_add_right (d : ℝ)).comp_mul_left' hcR.ne'
    exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hg_aff.integrableOn
      (Eventually.of_forall fun _ => hg_nn _)).symm
  simp_rw [hterm]
  have hsum_real : Summable (fun d : ℤ => ∫ x in Set.Ioc (0 : ℝ) 1, g ((c : ℝ) * x + (d : ℝ))) := by
    simp_rw [setIntegral_Ioc_zero_one_affine hc, smul_eq_mul]
    rw [← (intEquivProdFin hc).symm.summable_iff]
    refine Summable.mul_left ((c : ℝ)⁻¹) ?_
    rw [← (Equiv.prodComm (Fin c) ℤ).summable_iff]
    refine (summable_prod_of_nonneg (fun _ => MeasureTheory.integral_nonneg fun _ => hg_nn _)).mpr
      ⟨fun r => ?_, (hasSum_fintype _).summable⟩
    have hint_u : IntegrableOn g
        (⋃ k : ℤ, Set.Ioc (((k * (c : ℤ) + (r.1 : ℤ) : ℤ) : ℝ))
          (((k * (c : ℤ) + (r.1 : ℤ) : ℤ) : ℝ) + (c : ℝ))) volume := by
      rw [iUnion_ioc_shift_eq_univ hc r, integrableOn_univ]; exact hg_int
    exact (MeasureTheory.hasSum_integral_iUnion (fun _ => measurableSet_Ioc)
      (ioc_shift_pairwise_disjoint hc r) hint_u).summable
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => MeasureTheory.integral_nonneg fun _ => hg_nn _) hsum_real,
    tsum_setIntegral_Ioc_zero_one_affine hg_int hc]

/-! ### Part 4C: Exact 0-th Fourier Coefficient (Constant Term) of `realEisenstein` -/

/-- Exact evaluation of `∫_{-∞}^∞ (y / (u² + (c y)²))^s du = c^{1 - 2s} y^{1 - s} ∫ (t² + 1)^{-s} dt`. -/
private lemma integral_eisenstein_line {y : ℝ} (hy : 0 < y) {c : ℕ} (hc : 0 < c)
    {s : ℂ} (hs : 1 / 2 < s.re) :
    (∫ u : ℝ, (y : ℂ) ^ s * ((u ^ 2 + ((c : ℝ) * y) ^ 2 : ℝ) : ℂ) ^ (-s)) =
      ((c : ℕ) : ℂ) ^ (1 - 2 * s) * (y : ℂ) ^ (1 - s) *
        (((Real.sqrt Real.pi : ℝ) : ℂ) * Complex.Gamma (s - 1 / 2) / Complex.Gamma s) := by
  have hcR : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hc
  have hcy : 0 < (c : ℝ) * y := mul_pos hcR hy
  have hscale : (∫ u : ℝ, (y : ℂ) ^ s * ((u ^ 2 + ((c : ℝ) * y) ^ 2 : ℝ) : ℂ) ^ (-s)) =
      ((c : ℝ) * y : ℝ) • ∫ t : ℝ, (y : ℂ) ^ s *
        ((((c : ℝ) * y * t) ^ 2 + ((c : ℝ) * y) ^ 2 : ℝ) : ℂ) ^ (-s) := by
    have hcomp := Measure.integral_comp_mul_left
      (fun u : ℝ => (y : ℂ) ^ s * ((u ^ 2 + ((c : ℝ) * y) ^ 2 : ℝ) : ℂ) ^ (-s)) ((c : ℝ) * y)
    rw [abs_of_pos (inv_pos.mpr hcy)] at hcomp
    have := congrArg (((c : ℝ) * y) • ·) hcomp
    rw [smul_smul, mul_inv_cancel₀ hcy.ne', one_smul] at this
    exact this.symm
  rw [hscale, Complex.real_smul]
  have hpt : (fun t : ℝ => (y : ℂ) ^ s * ((((c : ℝ) * y * t) ^ 2 + ((c : ℝ) * y) ^ 2 : ℝ) : ℂ) ^ (-s)) =
      fun t : ℝ => ((y : ℂ) ^ s * (((c : ℝ) * y : ℝ) : ℂ) ^ (-(2 * s))) *
        ((t ^ 2 + 1 : ℝ) : ℂ) ^ (-s) := by
    funext t
    have hfac : ((c : ℝ) * y * t) ^ 2 + ((c : ℝ) * y) ^ 2 = ((c : ℝ) * y) ^ 2 * (t ^ 2 + 1) := by ring
    rw [hfac, ofReal_mul_cpow (sq_pos_of_pos hcy) (by positivity) (-s),
      ofReal_sq_cpow hcy (-s), show 2 * (-s) = -(2 * s) by ring]
    ring
  rw [hpt, MeasureTheory.integral_const_mul, integral_one_add_sq_cpow_neg hs]
  rw [← mul_assoc]
  congr 1
  rw [ofReal_mul_cpow hcR hy (-(2 * s)), Complex.ofReal_mul]
  have hc_pow : ((c : ℝ) : ℂ) * ((c : ℝ) : ℂ) ^ (-(2 * s)) = ((c : ℕ) : ℂ) ^ (1 - 2 * s) := by
    have hcC : ((c : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hcR.ne'
    calc ((c : ℝ) : ℂ) * ((c : ℝ) : ℂ) ^ (-(2 * s))
        = ((c : ℝ) : ℂ) ^ (1 : ℂ) * ((c : ℝ) : ℂ) ^ (-(2 * s)) := by rw [Complex.cpow_one]
      _ = ((c : ℝ) : ℂ) ^ (1 + -(2 * s)) := (Complex.cpow_add _ _ hcC).symm
      _ = ((c : ℕ) : ℂ) ^ (1 - 2 * s) := by rw [← sub_eq_add_neg]; push_cast; rfl
  have hy_pow : (y : ℂ) * (y : ℂ) ^ s * (y : ℂ) ^ (-(2 * s)) = (y : ℂ) ^ (1 - s) := by
    have hyC : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
    calc (y : ℂ) * (y : ℂ) ^ s * (y : ℂ) ^ (-(2 * s))
        = (y : ℂ) ^ (1 : ℂ) * (y : ℂ) ^ s * (y : ℂ) ^ (-(2 * s)) := by rw [Complex.cpow_one]
      _ = (y : ℂ) ^ (1 + s) * (y : ℂ) ^ (-(2 * s)) := by rw [← Complex.cpow_add _ _ hyC]
      _ = (y : ℂ) ^ (1 + s + -(2 * s)) := (Complex.cpow_add _ _ hyC).symm
      _ = (y : ℂ) ^ (1 - s) := by congr 1; ring
  calc ((c : ℝ) : ℂ) * (y : ℂ) * ((y : ℂ) ^ s * (((c : ℝ) : ℂ) ^ (-(2 * s)) * (y : ℂ) ^ (-(2 * s))))
      = (((c : ℝ) : ℂ) * ((c : ℝ) : ℂ) ^ (-(2 * s))) * ((y : ℂ) * (y : ℂ) ^ s * (y : ℂ) ^ (-(2 * s))) := by ring
    _ = ((c : ℕ) : ℂ) ^ (1 - 2 * s) * (y : ℂ) ^ (1 - s) := by rw [hc_pow, hy_pow]

/-- Exact completed-zeta ratio identity on `Re(s) > 1`:
`completedRiemannZeta (2 * s - 1) / completedRiemannZeta (2 * s) = (√π Γ(s - 1/2) / Γ(s)) * (ζ(2s - 1) / ζ(2s))`. -/
lemma completedRiemannZeta_ratio_eq {s : ℂ} (hs : 1 < s.re) :
    completedRiemannZeta (2 * s - 1) / completedRiemannZeta (2 * s) =
      (((Real.sqrt Real.pi : ℝ) : ℂ) * Complex.Gamma (s - 1 / 2) / Complex.Gamma s) *
        (riemannZeta (2 * s - 1) / riemannZeta (2 * s)) := by
  have h2s0 : 2 * s ≠ 0 := fun h => by
    have : (2 * s).re = 0 := by rw [h]; simp
    simp at this; linarith
  have h2s10 : 2 * s - 1 ≠ 0 := fun h => by
    have : (2 * s - 1).re = 0 := by rw [h]; simp
    simp at this; linarith
  have hG1 : Complex.Gammaℝ (2 * s - 1) ≠ 0 := by
    rw [Complex.Gammaℝ_def]
    refine mul_ne_zero (Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_pos.ne')))
      (Complex.Gamma_ne_zero_of_re_pos (by simp; linarith))
  have hG2 : Complex.Gammaℝ (2 * s) ≠ 0 := by
    rw [Complex.Gammaℝ_def]
    refine mul_ne_zero (Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_pos.ne')))
      (Complex.Gamma_ne_zero_of_re_pos (by simp; linarith))
  have hlam1 : completedRiemannZeta (2 * s - 1) = riemannZeta (2 * s - 1) * Complex.Gammaℝ (2 * s - 1) := by
    rw [riemannZeta_def_of_ne_zero h2s10, div_mul_cancel₀ _ hG1]
  have hlam2 : completedRiemannZeta (2 * s) = riemannZeta (2 * s) * Complex.Gammaℝ (2 * s) := by
    rw [riemannZeta_def_of_ne_zero h2s0, div_mul_cancel₀ _ hG2]
  rw [hlam1, hlam2, Complex.Gammaℝ_def, Complex.Gammaℝ_def]
  have hpiC : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
  have hpi_ratio : (Real.pi : ℂ) ^ (-(2 * s - 1) / 2) / (Real.pi : ℂ) ^ (-(2 * s) / 2) =
      ((Real.sqrt Real.pi : ℝ) : ℂ) := by
    rw [← Complex.cpow_sub _ _ hpiC, show -(2 * s - 1) / 2 - -(2 * s) / 2 = ((1 / 2 : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cpow Real.pi_pos.le, ← Real.sqrt_eq_rpow]
  have hgam_eq1 : (2 * s - 1) / 2 = s - 1 / 2 := by ring
  have hgam_eq2 : (2 * s) / 2 = s := by ring
  rw [hgam_eq1, hgam_eq2]
  have hpi_ne : (Real.pi : ℂ) ^ (-(2 * s) / 2) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl hpiC)
  have hgam_ne : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by linarith)
  have hzeta_ne : riemannZeta (2 * s) ≠ 0 := riemannZeta_ne_zero_of_one_lt_re (by simp; linarith)
  rw [← hpi_ratio]
  field_simp [hpi_ne, hgam_ne, hzeta_ne]

/-- **EXACT 0-TH FOURIER COEFFICIENT (CONSTANT TERM) OF THE REAL-ANALYTIC EISENSTEIN SERIES (`0` ASSUMPTIONS!)**:
for EVERY `y > 0` and EVERY `s ∈ ℂ` with `Re(s) > 1`,
$$\int_0^1 E(x + i y, s)\,dx = y^s + \frac{\Lambda(2 s - 1)}{\Lambda(2 s)}\, y^{1 - s}.$$ -/
theorem realEisenstein_constant_term_eq {y : ℝ} (hy : 0 < y) {s : ℂ} (hs : 1 < s.re) :
    (∫ x in (0 : ℝ)..1, realEisenstein ⟨(x : ℂ) + Complex.I * (y : ℂ), by simp [hy]⟩ s) =
      (y : ℂ) ^ s + (completedRiemannZeta (2 * s - 1) / completedRiemannZeta (2 * s)) * (y : ℂ) ^ (1 - s) := by
  have hs_half : 1 / 2 < s.re := by linarith
  have hs2 : 1 < (2 * s).re := by simp; linarith
  have hs2m1 : 1 < (2 * s - 1).re := by simp; linarith
  have hzeta_ne : riemannZeta (2 * s) ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs2
  -- First compute `∫ x in Ioc 0 1, epsteinEisenstein (x + i y) s`
  have hep_split : ∀ x : ℝ,
      epsteinEisenstein ⟨(x : ℂ) + Complex.I * (y : ℂ), by simp [hy]⟩ s =
        riemannZeta (2 * s) * (y : ℂ) ^ s +
        ∑' cd : ℕ+ × ℤ, termFun (cd.1 : ℝ) (cd.2 : ℝ) s x y := by
    intro x
    let τx : UpperHalfPlane := ⟨(x : ℂ) + Complex.I * (y : ℂ), by simp [hy]⟩
    have hsum_all := epsteinEisenstein_summable τx hs
    -- Split `{p : ℤ × ℤ // p ≠ (0, 0)}` into `(c = 0, d ≠ 0) ⊕ (c > 0, d ∈ ℤ) ⊕ (c < 0, d ∈ ℤ)`
    let eSplit : ((ℕ+ ⊕ ℕ+) ⊕ ((ℕ+ × ℤ) ⊕ (ℕ+ × ℤ))) ≃ { p : ℤ × ℤ // p ≠ (0, 0) } :=
      { toFun := fun t => match t with
          | Sum.inl (Sum.inl d) => ⟨(0, (d.1 : ℤ)), by
              intro h; have h2 : (d.1 : ℤ) = 0 := (Prod.mk.inj h).2
              have hpos : 0 < (d.1 : ℤ) := Nat.cast_pos.mpr d.pos; omega⟩
          | Sum.inl (Sum.inr d) => ⟨(0, -(d.1 : ℤ)), by
              intro h; have h2 : -(d.1 : ℤ) = 0 := (Prod.mk.inj h).2
              have hpos : 0 < (d.1 : ℤ) := Nat.cast_pos.mpr d.pos; omega⟩
          | Sum.inr (Sum.inl cd) => ⟨((cd.1.1 : ℤ), cd.2), by
              intro h; have h1 : (cd.1.1 : ℤ) = 0 := (Prod.mk.inj h).1
              have hpos : 0 < (cd.1.1 : ℤ) := Nat.cast_pos.mpr cd.1.pos; omega⟩
          | Sum.inr (Sum.inr cd) => ⟨(-(cd.1.1 : ℤ), -cd.2), by
              intro h; have h1 : -(cd.1.1 : ℤ) = 0 := (Prod.mk.inj h).1
              have hpos : 0 < (cd.1.1 : ℤ) := Nat.cast_pos.mpr cd.1.pos; omega⟩
        invFun := fun p =>
          if hc_pos : 0 < p.1.1 then Sum.inr (Sum.inl (⟨p.1.1.toNat, by omega⟩, p.1.2))
          else if hc_neg : p.1.1 < 0 then Sum.inr (Sum.inr (⟨(-p.1.1).toNat, by omega⟩, -p.1.2))
          else if hd_pos : 0 < p.1.2 then Sum.inl (Sum.inl ⟨p.1.2.toNat, by omega⟩)
          else Sum.inl (Sum.inr ⟨(-p.1.2).toNat, by
            have hc0 : p.1.1 = 0 := by omega
            have hd0 : p.1.2 ≠ 0 := fun h => p.2 (Prod.ext hc0 h)
            omega⟩)
        left_inv := fun t => by
          rcases t with (⟨d, hd⟩ | ⟨d, hd⟩) | (⟨⟨c, hc⟩, e⟩ | ⟨⟨c, hc⟩, e⟩) <;>
            dsimp only
          · rw [dif_neg (lt_irrefl 0), dif_neg (lt_irrefl 0),
              dif_pos (Nat.cast_pos.mpr hd)]
            congr 2
          · rw [dif_neg (lt_irrefl 0), dif_neg (lt_irrefl 0),
              dif_neg (by have : (0 : ℤ) < (d : ℤ) := Nat.cast_pos.mpr hd; omega)]
            congr 2
            exact Subtype.ext (by simp only [neg_neg, Int.toNat_natCast])
          · rw [dif_pos (Nat.cast_pos.mpr hc)]
            congr 2
          · rw [dif_neg (by have : (0 : ℤ) < (c : ℤ) := Nat.cast_pos.mpr hc; omega),
              dif_pos (by have : (0 : ℤ) < (c : ℤ) := Nat.cast_pos.mpr hc; omega)]
            congr 2
            exact Prod.ext (Subtype.ext (by simp only [neg_neg, Int.toNat_natCast])) (neg_neg e)
        right_inv := fun ⟨⟨c, d⟩, hcd⟩ => by
          dsimp only
          by_cases hc_pos : 0 < c
          · simp only [dif_pos hc_pos]
            exact Subtype.ext (Prod.ext (by dsimp only; omega) rfl)
          · by_cases hc_neg : c < 0
            · simp only [dif_neg hc_pos, dif_pos hc_neg]; apply Subtype.ext; apply Prod.ext <;> (dsimp only; omega)
            · have hc0 : c = 0 := by omega
              have hd0 : d ≠ 0 := fun h => hcd (Prod.ext hc0 h)
              by_cases hd_pos : 0 < d
              · simp only [dif_neg hc_pos, dif_neg hc_neg, dif_pos hd_pos]
                apply Subtype.ext; apply Prod.ext <;> (dsimp only; omega)
              · simp only [dif_neg hc_pos, dif_neg hc_neg, dif_neg hd_pos]
                apply Subtype.ext; apply Prod.ext <;> (dsimp only; omega) }
    let g := fun p : { p : ℤ × ℤ // p ≠ (0, 0) } =>
      ((τx.im : ℂ) / ((‖(p.1.1 : ℂ) * (τx : ℂ) + (p.1.2 : ℂ)‖ : ℂ) ^ 2)) ^ s
    have hsum_e : Summable (g ∘ eSplit) := (Equiv.summable_iff eSplit).mpr hsum_all
    have hsum_L := hsum_e.comp_injective Sum.inl_injective
    have hsum_R := hsum_e.comp_injective Sum.inr_injective
    have hsum_LL := hsum_L.comp_injective Sum.inl_injective
    have hsum_LR := hsum_L.comp_injective Sum.inr_injective
    have hsum_RL := hsum_R.comp_injective Sum.inl_injective
    have hsum_RR := hsum_R.comp_injective Sum.inr_injective
    have hzeta2s : riemannZeta (2 * s) = ∑' d : ℕ+, ((d : ℕ) : ℂ) ^ (-(2 * s)) := by
      rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs2, ← natEquivPNat.tsum_eq]
      refine tsum_congr fun n => ?_
      rw [one_div, Complex.cpow_neg]
      change (((n : ℂ) + 1) ^ (2 * s))⁻¹ = (((n + 1 : ℕ) : ℂ) ^ (2 * s))⁻¹
      push_cast; rfl
    have hLL_val : (∑' d : ℕ+, g (eSplit (Sum.inl (Sum.inl d)))) = riemannZeta (2 * s) * (y : ℂ) ^ s := by
      rw [hzeta2s, ← tsum_mul_right]
      refine tsum_congr fun d => ?_
      have hd_pos : (0 : ℝ) < (d : ℕ) := by exact_mod_cast d.pos
      dsimp only [g, eSplit, Equiv.coe_fn_mk]
      have him : τx.im = y := by simp [τx]
      have hnorm : ‖((0 : ℤ) : ℂ) * (τx : ℂ) + ((d.1 : ℤ) : ℂ)‖ = ((d : ℕ) : ℝ) := by
        simp; rfl
      rw [him, hnorm, ← Complex.ofReal_pow, ← Complex.ofReal_div,
        ofReal_div_cpow hy (sq_pos_of_pos hd_pos) s, ofReal_sq_cpow hd_pos (-s),
        show 2 * (-s) = -(2 * s) by ring]
      push_cast; ring
    have hLR_val : (∑' d : ℕ+, g (eSplit (Sum.inl (Sum.inr d)))) = riemannZeta (2 * s) * (y : ℂ) ^ s := by
      rw [← hLL_val]
      refine tsum_congr fun d => ?_
      dsimp only [g, eSplit, Equiv.coe_fn_mk]
      simp
    have hRL_val : (∑' cd : ℕ+ × ℤ, g (eSplit (Sum.inr (Sum.inl cd)))) =
        ∑' cd : ℕ+ × ℤ, termFun (cd.1 : ℝ) (cd.2 : ℝ) s x y := by
      refine tsum_congr fun cd => ?_
      have hof : UpperHalfPlane.ofComplex ((x : ℂ) + Complex.I * (y : ℂ)) = τx := by
        apply UpperHalfPlane.ext; exact ofComplex_re_add_I_im_eq hy
      have hcd_ne : ((cd.1.1 : ℤ), cd.2) ≠ (0, 0) := fun h =>
        (by exact_mod_cast cd.1.pos.ne' : (cd.1.1 : ℤ) ≠ 0) (Prod.mk.inj h).1
      have h := eisensteinTerm_eq_termFun hcd_ne s hy (x := x)
      rw [hof] at h
      exact h
    have hRR_val : (∑' cd : ℕ+ × ℤ, g (eSplit (Sum.inr (Sum.inr cd)))) =
        ∑' cd : ℕ+ × ℤ, termFun (cd.1 : ℝ) (cd.2 : ℝ) s x y := by
      rw [← hRL_val]
      refine tsum_congr fun cd => ?_
      dsimp only [g, eSplit, Equiv.coe_fn_mk]
      have hneg : ((-(cd.1.1 : ℤ) : ℤ) : ℂ) * (τx : ℂ) + ((-cd.2 : ℤ) : ℂ) =
          -(((cd.1.1 : ℤ) : ℂ) * (τx : ℂ) + (cd.2 : ℂ)) := by push_cast; ring
      rw [hneg, norm_neg]
    unfold epsteinEisenstein
    change (1 / 2 : ℂ) * ∑' p, g p = _
    rw [← eSplit.tsum_eq g]
    change (1 / 2 : ℂ) * ∑' i, (g ∘ eSplit) i = _
    rw [hsum_L.tsum_sum hsum_R]
    change (1 / 2 : ℂ) *
      ((∑' i, ((g ∘ eSplit) ∘ Sum.inl) i) + (∑' i, ((g ∘ eSplit) ∘ Sum.inr) i)) = _
    rw [hsum_LL.tsum_sum hsum_LR, hsum_RL.tsum_sum hsum_RR]
    change (1 / 2 : ℂ) *
      ((∑' d : ℕ+, g (eSplit (Sum.inl (Sum.inl d)))) +
       (∑' d : ℕ+, g (eSplit (Sum.inl (Sum.inr d)))) +
       ((∑' cd : ℕ+ × ℤ, g (eSplit (Sum.inr (Sum.inl cd)))) +
        (∑' cd : ℕ+ × ℤ, g (eSplit (Sum.inr (Sum.inr cd)))))) = _
    rw [hLL_val, hLR_val, hRL_val, hRR_val]
    ring
  -- Check Tonelli condition `∑' cd : ℕ+ × ℤ, ∫⁻ x in Ioc 0 1, ‖termFun cd.1 cd.2 s x y‖ₑ ≠ ⊤`
  have htonelli : (∑' cd : ℕ+ × ℤ,
      ∫⁻ x in Set.Ioc (0 : ℝ) 1, ‖termFun (cd.1 : ℝ) (cd.2 : ℝ) s x y‖ₑ) ≠ ⊤ := by
    have hinner : ∀ c : ℕ+,
        (∑' d : ℤ, ∫⁻ x in Set.Ioc (0 : ℝ) 1, ‖termFun (c : ℝ) (d : ℝ) s x y‖ₑ) =
        ENNReal.ofReal (((c : ℕ) : ℝ) ^ (1 - 2 * s.re) * y ^ (1 - s.re) *
          ∫ t : ℝ, (t ^ 2 + 1) ^ (-s.re)) := by
      intro c
      have hcR : (0 : ℝ) < (c : ℝ) := by exact_mod_cast c.pos
      have hcy : 0 < (c : ℝ) * y := mul_pos hcR hy
      let gReal : ℝ → ℝ := fun u => y ^ s.re * (u ^ 2 + ((c : ℝ) * y) ^ 2) ^ (-s.re)
      have hfn_int : Integrable gReal volume := by
        have h1 := integrable_one_add_sq_rpow_neg hs_half
        have hcomp : Integrable (fun u : ℝ => (((c : ℝ) * y)⁻¹ * u) ^ 2 + 1 |> (· ^ (-s.re))) volume :=
          h1.comp_mul_left' (inv_pos.mpr hcy).ne'
        refine (hcomp.const_mul (y ^ s.re * (((c : ℝ) * y) ^ 2) ^ (-s.re))).congr ?_
        filter_upwards with u
        dsimp only [gReal]
        have hfac : u ^ 2 + ((c : ℝ) * y) ^ 2 = ((c : ℝ) * y) ^ 2 * ((((c : ℝ) * y)⁻¹ * u) ^ 2 + 1) := by
          field_simp [hcy.ne']
        rw [hfac, Real.mul_rpow (sq_nonneg _) (by positivity)]; ring
      have hcongr_d : ∀ d : ℤ,
          (∫⁻ x in Set.Ioc (0 : ℝ) 1, ‖termFun (c : ℝ) (d : ℝ) s x y‖ₑ) =
            ∫⁻ x in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal (gReal ((c : ℝ) * x + (d : ℝ))) := by
        intro d
        refine setLIntegral_congr_fun measurableSet_Ioc fun x _ => ?_
        have hQ : 0 < quadQ (c : ℝ) (d : ℝ) x y :=
          quadQ_pos hy (fun h => hcR.ne' (Prod.mk.inj h).1)
        dsimp only [gReal, termFun]
        rw [enorm_eq_nnnorm, ENNReal.ofReal_eq_coe_nnreal (by positivity)]
        congr 1; apply Subtype.ext
        change ‖(y : ℂ) ^ s * (quadQ (c : ℝ) (d : ℝ) x y : ℂ) ^ (-s)‖ = _
        rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy,
          Complex.norm_cpow_eq_rpow_re_of_pos hQ, Complex.neg_re]
        rfl
      simp_rw [hcongr_d]
      rw [tsum_setLIntegral_ofReal_Ioc_zero_one_affine hfn_int (fun _ => by positivity) c.pos]
      congr 1
      have hreal_val : (∫ u : ℝ, gReal u) =
          ((c : ℕ) : ℝ) ^ (1 - 2 * s.re) * y ^ (1 - s.re) * ∫ t : ℝ, (t ^ 2 + 1) ^ (-s.re) := by
        dsimp only [gReal]
        have hscale := Measure.integral_comp_mul_left
          (fun u : ℝ => y ^ s.re * (u ^ 2 + ((c : ℝ) * y) ^ 2) ^ (-s.re)) ((c : ℝ) * y)
        rw [abs_of_pos (inv_pos.mpr hcy), smul_eq_mul] at hscale
        have h1 : (∫ u : ℝ, y ^ s.re * (u ^ 2 + ((c : ℝ) * y) ^ 2) ^ (-s.re)) =
            ((c : ℝ) * y) * ∫ t : ℝ, y ^ s.re * (((c : ℝ) * y * t) ^ 2 + ((c : ℝ) * y) ^ 2) ^ (-s.re) := by
          have := congrArg (((c : ℝ) * y) * ·) hscale
          rw [← mul_assoc, mul_inv_cancel₀ hcy.ne', one_mul] at this
          exact this.symm
        rw [h1]
        have hpt : (fun t : ℝ => y ^ s.re * (((c : ℝ) * y * t) ^ 2 + ((c : ℝ) * y) ^ 2) ^ (-s.re)) =
            fun t : ℝ => (y ^ s.re * ((c : ℝ) * y) ^ (-2 * s.re)) * (t ^ 2 + 1) ^ (-s.re) := by
          funext t
          have hfac : ((c : ℝ) * y * t) ^ 2 + ((c : ℝ) * y) ^ 2 = ((c : ℝ) * y) ^ 2 * (t ^ 2 + 1) := by ring
          rw [hfac, Real.mul_rpow (sq_nonneg _) (by positivity), ← Real.rpow_natCast _ 2,
            ← Real.rpow_mul hcy.le]
          push_cast; ring_nf
        rw [hpt, MeasureTheory.integral_const_mul, ← mul_assoc]
        congr 1
        rw [Real.mul_rpow hcR.le hy.le]
        have hc_p : (c : ℝ) * (c : ℝ) ^ (-2 * s.re) = ((c : ℕ) : ℝ) ^ (1 - 2 * s.re) := by
          calc (c : ℝ) * (c : ℝ) ^ (-2 * s.re)
              = (c : ℝ) ^ (1 : ℝ) * (c : ℝ) ^ (-2 * s.re) := by rw [Real.rpow_one]
            _ = (c : ℝ) ^ (1 + -2 * s.re) := (Real.rpow_add hcR _ _).symm
            _ = ((c : ℕ) : ℝ) ^ (1 - 2 * s.re) := by congr 1; ring
        have hy_p : y * y ^ s.re * y ^ (-2 * s.re) = y ^ (1 - s.re) := by
          calc y * y ^ s.re * y ^ (-2 * s.re)
              = y ^ (1 : ℝ) * y ^ s.re * y ^ (-2 * s.re) := by rw [Real.rpow_one]
            _ = y ^ (1 + s.re) * y ^ (-2 * s.re) := by rw [← Real.rpow_add hy]
            _ = y ^ (1 + s.re + -2 * s.re) := (Real.rpow_add hy _ _).symm
            _ = y ^ (1 - s.re) := by congr 1; ring
        calc (c : ℝ) * y * (y ^ s.re * ((c : ℝ) ^ (-2 * s.re) * y ^ (-2 * s.re)))
            = ((c : ℝ) * (c : ℝ) ^ (-2 * s.re)) * (y * y ^ s.re * y ^ (-2 * s.re)) := by ring
          _ = ((c : ℕ) : ℝ) ^ (1 - 2 * s.re) * y ^ (1 - s.re) := by rw [hc_p, hy_p]
      exact hreal_val
    rw [ENNReal.tsum_prod']
    simp_rw [hinner]
    have hsum_c : Summable (fun c : ℕ+ =>
        ((c : ℕ) : ℝ) ^ (1 - 2 * s.re) * y ^ (1 - s.re) * ∫ t : ℝ, (t ^ 2 + 1) ^ (-s.re)) := by
      have hnat : Summable (fun n : ℕ => (((n + 1 : ℕ) : ℝ) ^ (2 * s.re - 1))⁻¹) :=
        (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow_inv.mpr (by linarith))
      have hpnat : Summable (fun c : ℕ+ => ((c : ℕ) : ℝ) ^ (1 - 2 * s.re)) := by
        refine (Equiv.summable_iff natEquivPNat).mp (hnat.congr fun n => ?_)
        have hpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
        change (((n + 1 : ℕ) : ℝ) ^ (2 * s.re - 1))⁻¹ = ((n + 1 : ℕ) : ℝ) ^ (1 - 2 * s.re)
        rw [← Real.rpow_neg hpos.le]; congr 1; ring
      exact (hpnat.mul_right _).mul_right _
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun c => mul_nonneg (mul_nonneg (by positivity) (by positivity))
      (MeasureTheory.integral_nonneg fun _ => Real.rpow_nonneg (by positivity) _)) hsum_c]
    exact ENNReal.ofReal_ne_top
  -- Interchange `∫ x in Ioc 0 1` and `∑' cd : ℕ+ × ℤ` via `MeasureTheory.integral_tsum`
  have hmeas_cd : ∀ cd : ℕ+ × ℤ,
      AEStronglyMeasurable (fun x : ℝ => termFun (cd.1 : ℝ) (cd.2 : ℝ) s x y)
        (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    intro cd
    have hcR : (0 : ℝ) < (cd.1 : ℝ) := by exact_mod_cast cd.1.pos
    have hcont : Continuous (fun x : ℝ => termFun (cd.1 : ℝ) (cd.2 : ℝ) s x y) := by
      unfold termFun
      refine continuous_const.mul (Continuous.cpow ?_ continuous_const ?_)
      · exact Complex.continuous_ofReal.comp (by unfold quadQ; fun_prop)
      · intro x; exact Or.inl (by simpa using quadQ_pos hy (fun h => hcR.ne' (Prod.mk.inj h).1))
    exact hcont.aestronglyMeasurable
  have hint_tsum : (∫ x in Set.Ioc (0 : ℝ) 1,
      ∑' cd : ℕ+ × ℤ, termFun (cd.1 : ℝ) (cd.2 : ℝ) s x y) =
      riemannZeta (2 * s - 1) * (y : ℂ) ^ (1 - s) *
        (((Real.sqrt Real.pi : ℝ) : ℂ) * Complex.Gamma (s - 1 / 2) / Complex.Gamma s) := by
    rw [MeasureTheory.integral_tsum hmeas_cd htonelli]
    have hsum_int : Summable (fun cd : ℕ+ × ℤ =>
        ∫ x in Set.Ioc (0 : ℝ) 1, termFun (cd.1 : ℝ) (cd.2 : ℝ) s x y) := by
      have hfin := ENNReal.summable_toReal htonelli
      refine Summable.of_norm (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun cd => ?_) hfin)
      have hint_cd : IntegrableOn (fun x : ℝ => termFun (cd.1 : ℝ) (cd.2 : ℝ) s x y) (Set.Ioc 0 1) volume := by
        have hne : (∫⁻ x in Set.Ioc (0 : ℝ) 1, ‖termFun (cd.1 : ℝ) (cd.2 : ℝ) s x y‖ₑ) ≠ ⊤ :=
          ne_top_of_le_ne_top htonelli (ENNReal.le_tsum cd)
        exact ⟨hmeas_cd cd, lt_top_iff_ne_top.mpr hne⟩
      calc ‖∫ x in Set.Ioc (0 : ℝ) 1, termFun (cd.1 : ℝ) (cd.2 : ℝ) s x y‖
          ≤ ∫ x in Set.Ioc (0 : ℝ) 1, ‖termFun (cd.1 : ℝ) (cd.2 : ℝ) s x y‖ :=
            MeasureTheory.norm_integral_le_integral_norm _
        _ = (∫⁻ x in Set.Ioc (0 : ℝ) 1, ‖termFun (cd.1 : ℝ) (cd.2 : ℝ) s x y‖ₑ).toReal := by
            rw [← MeasureTheory.ofReal_integral_norm_eq_lintegral_enorm hint_cd,
              ENNReal.toReal_ofReal (MeasureTheory.integral_nonneg fun _ => norm_nonneg _)]
    rw [hsum_int.tsum_prod]
    have hinner_c : ∀ c : ℕ+,
        (∑' d : ℤ, ∫ x in Set.Ioc (0 : ℝ) 1, termFun (c : ℝ) (d : ℝ) s x y) =
          ((c : ℕ) : ℂ) ^ (1 - 2 * s) * (y : ℂ) ^ (1 - s) *
            (((Real.sqrt Real.pi : ℝ) : ℂ) * Complex.Gamma (s - 1 / 2) / Complex.Gamma s) := by
      intro c
      have hcR : (0 : ℝ) < (c : ℝ) := by exact_mod_cast c.pos
      have hcy : 0 < (c : ℝ) * y := mul_pos hcR hy
      let fc : ℝ → ℂ := fun u => (y : ℂ) ^ s * ((u ^ 2 + ((c : ℝ) * y) ^ 2 : ℝ) : ℂ) ^ (-s)
      have hfc_int : Integrable fc volume := by
        have h1 := integrable_one_add_sq_cpow_neg hs_half
        have hcomp : Integrable (fun u : ℝ => (((((c : ℝ) * y)⁻¹ * u) ^ 2 + 1 : ℝ) : ℂ) ^ (-s)) volume :=
          h1.comp_mul_left' (inv_pos.mpr hcy).ne'
        refine (hcomp.const_mul ((y : ℂ) ^ s * ((((c : ℝ) * y) ^ 2 : ℝ) : ℂ) ^ (-s))).congr ?_
        filter_upwards with u
        dsimp only [fc]
        have hfac : u ^ 2 + ((c : ℝ) * y) ^ 2 = ((c : ℝ) * y) ^ 2 * ((((c : ℝ) * y)⁻¹ * u) ^ 2 + 1) := by
          field_simp [hcy.ne']
        rw [hfac, ofReal_mul_cpow (sq_pos_of_pos hcy) (by positivity) (-s)]; ring
      have hcongr : ∀ d : ℤ,
          (∫ x in Set.Ioc (0 : ℝ) 1, termFun (c : ℝ) (d : ℝ) s x y) =
            ∫ x in Set.Ioc (0 : ℝ) 1, fc ((c : ℝ) * x + (d : ℝ)) := fun d => rfl
      simp_rw [hcongr]
      rw [tsum_setIntegral_Ioc_zero_one_affine hfc_int c.pos]
      exact integral_eisenstein_line hy c.pos hs_half
    simp_rw [hinner_c, tsum_mul_right]
    have hzeta2m1 : (∑' c : ℕ+, ((c : ℕ) : ℂ) ^ (1 - 2 * s)) = riemannZeta (2 * s - 1) := by
      rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs2m1, ← natEquivPNat.tsum_eq]
      refine tsum_congr fun n => ?_
      rw [one_div, ← Complex.cpow_neg]
      change (((n + 1 : ℕ) : ℂ) ^ (1 - 2 * s)) = (((n : ℂ) + 1) ^ (-(2 * s - 1)))
      push_cast; congr 1; ring
    rw [hzeta2m1]
  -- Assemble the full constant term for `epsteinEisenstein` and divide by `riemannZeta (2 * s)`
  have hint_tsum_int : IntegrableOn (fun x : ℝ => ∑' cd : ℕ+ × ℤ, termFun (cd.1 : ℝ) (cd.2 : ℝ) s x y)
      (Set.Ioc (0 : ℝ) 1) volume := by
    refine ⟨AEStronglyMeasurable.tsum hmeas_cd, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    refine lt_of_le_of_lt ?_ (lt_top_iff_ne_top.mpr htonelli)
    calc ∫⁻ x in Set.Ioc (0 : ℝ) 1, ‖∑' cd : ℕ+ × ℤ, termFun (cd.1 : ℝ) (cd.2 : ℝ) s x y‖ₑ
        ≤ ∫⁻ x in Set.Ioc (0 : ℝ) 1, ∑' cd : ℕ+ × ℤ, ‖termFun (cd.1 : ℝ) (cd.2 : ℝ) s x y‖ₑ :=
          MeasureTheory.lintegral_mono fun x => enorm_tsum_le_tsum_enorm
      _ = ∑' cd : ℕ+ × ℤ, ∫⁻ x in Set.Ioc (0 : ℝ) 1, ‖termFun (cd.1 : ℝ) (cd.2 : ℝ) s x y‖ₑ :=
          MeasureTheory.lintegral_tsum fun cd => (hmeas_cd cd).enorm
  have hconst_int : IntegrableOn (fun _ : ℝ => riemannZeta (2 * s) * (y : ℂ) ^ s)
      (Set.Ioc (0 : ℝ) 1) volume :=
    integrableOn_const (hs := measure_Ioc_lt_top.ne)
  rw [intervalIntegral.integral_of_le zero_le_one]
  unfold realEisenstein
  simp_rw [hep_split, MeasureTheory.integral_div]
  rw [MeasureTheory.integral_add hconst_int hint_tsum_int,
    MeasureTheory.setIntegral_const, Measure.real_def, Real.volume_Ioc, sub_zero,
    ENNReal.ofReal_one, ENNReal.toReal_one, one_smul, hint_tsum, add_div,
    mul_div_cancel_left₀ _ hzeta_ne, completedRiemannZeta_ratio_eq hs]
  ring

/-! ### Part 4D: Bonus Euler Totient Dirichlet Series `∑ φ(c) c^{-2s} = ζ(2s - 1) / ζ(2s)` -/

/-- **Exact Euler Totient Dirichlet Series Identity**:
for every `s : ℂ` with `Re(s) > 1`,
$$\sum_{c \ge 1} \frac{\varphi(c)}{c^{2 s}} = \frac{\zeta(2 s - 1)}{\zeta(2 s)}.$$ -/
theorem tsum_totient_div_cpow_eq {s : ℂ} (hs : 1 < s.re) :
    (∑' c : ℕ+, (Nat.totient (c : ℕ) : ℂ) * ((c : ℕ) : ℂ) ^ (-(2 * s))) =
      riemannZeta (2 * s - 1) / riemannZeta (2 * s) := by
  have hs2 : 1 < (2 * s).re := by simp; linarith
  have hs2m1 : 1 < (2 * s - 1).re := by simp; linarith
  have hzeta_ne : riemannZeta (2 * s) ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs2
  have hzeta2s : riemannZeta (2 * s) = ∑' d : ℕ+, ((d : ℕ) : ℂ) ^ (-(2 * s)) := by
    rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs2, ← natEquivPNat.tsum_eq]
    refine tsum_congr fun n => ?_
    rw [one_div, Complex.cpow_neg]
    change (((n : ℂ) + 1) ^ (2 * s))⁻¹ = (((n + 1 : ℕ) : ℂ) ^ (2 * s))⁻¹
    push_cast; rfl
  have hzeta2m1 : riemannZeta (2 * s - 1) = ∑' n : ℕ+, ((n : ℕ) : ℂ) ^ (1 - 2 * s) := by
    rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs2m1, ← natEquivPNat.tsum_eq]
    refine tsum_congr fun n => ?_
    rw [one_div, ← Complex.cpow_neg]
    change (((n : ℂ) + 1) ^ (-(2 * s - 1))) = (((n + 1 : ℕ) : ℂ) ^ (1 - 2 * s))
    push_cast; congr 1; ring
  have hsum_d_norm : Summable (fun d : ℕ+ => ‖((d : ℕ) : ℂ) ^ (-(2 * s))‖) := by
    have hnat : Summable (fun n : ℕ => (((n + 1 : ℕ) : ℝ) ^ (2 * s).re)⁻¹) :=
      (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow_inv.mpr hs2)
    refine (Equiv.summable_iff natEquivPNat).mp (hnat.congr fun n => ?_)
    have hpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    change (((n + 1 : ℕ) : ℝ) ^ (2 * s).re)⁻¹ = ‖(((n + 1 : ℕ) : ℂ)) ^ (-(2 * s))‖
    rw [show (((n + 1 : ℕ) : ℂ)) = ((((n + 1 : ℕ) : ℝ)) : ℂ) by push_cast; rfl,
      Complex.norm_cpow_eq_rpow_re_of_pos hpos, Complex.neg_re, Real.rpow_neg hpos.le]
  have hsum_tot_norm : Summable (fun c : ℕ+ =>
      ‖(Nat.totient (c : ℕ) : ℂ) * ((c : ℕ) : ℂ) ^ (-(2 * s))‖) := by
    have hnat : Summable (fun n : ℕ => (((n + 1 : ℕ) : ℝ) ^ (2 * s.re - 1))⁻¹) :=
      (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow_inv.mpr (by linarith))
    have hpnat : Summable (fun c : ℕ+ => ((c : ℕ) : ℝ) ^ (1 - 2 * s.re)) := by
      refine (Equiv.summable_iff natEquivPNat).mp (hnat.congr fun n => ?_)
      have hpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
      change (((n + 1 : ℕ) : ℝ) ^ (2 * s.re - 1))⁻¹ = ((n + 1 : ℕ) : ℝ) ^ (1 - 2 * s.re)
      rw [← Real.rpow_neg hpos.le]; congr 1; ring
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun c => ?_) hpnat
    have hc_pos : (0 : ℝ) < (c : ℕ) := by exact_mod_cast c.pos
    rw [norm_mul, Complex.norm_natCast,
      show ((c : ℕ) : ℂ) = (((c : ℕ) : ℝ) : ℂ) by push_cast; rfl,
      Complex.norm_cpow_eq_rpow_re_of_pos hc_pos, Complex.neg_re]
    have htot_le : (Nat.totient (c : ℕ) : ℝ) ≤ (c : ℕ) := by exact_mod_cast Nat.totient_le c
    calc (Nat.totient (c : ℕ) : ℝ) * ((c : ℕ) : ℝ) ^ (-(2 * s).re)
        ≤ ((c : ℕ) : ℝ) * ((c : ℕ) : ℝ) ^ (-(2 * s).re) :=
          mul_le_mul_of_nonneg_right htot_le (Real.rpow_nonneg hc_pos.le _)
      _ = ((c : ℕ) : ℝ) ^ (1 : ℝ) * ((c : ℕ) : ℝ) ^ (-(2 * s).re) := by rw [Real.rpow_one]
      _ = ((c : ℕ) : ℝ) ^ (1 + -(2 * s).re) := (Real.rpow_add hc_pos _ _).symm
      _ = ((c : ℕ) : ℝ) ^ (1 - 2 * s.re) := by simp [sub_eq_add_neg]
  have hprod_sum : Summable (fun p : ℕ+ × ℕ+ =>
      ((Nat.totient (p.1 : ℕ) : ℂ) * ((p.1 : ℕ) : ℂ) ^ (-(2 * s))) *
        ((p.2 : ℕ) : ℂ) ^ (-(2 * s))) :=
    ((Summable.mul_of_nonneg hsum_tot_norm hsum_d_norm (fun _ => norm_nonneg _)
      (fun _ => norm_nonneg _)).congr fun p => (norm_mul _ _).symm).of_norm
  suffices hmul : (∑' c : ℕ+, (Nat.totient (c : ℕ) : ℂ) * ((c : ℕ) : ℂ) ^ (-(2 * s))) *
      riemannZeta (2 * s) = riemannZeta (2 * s - 1) by
    exact (eq_div_iff hzeta_ne).mpr hmul
  rw [hzeta2s, hzeta2m1, hsum_tot_norm.of_norm.tsum_mul_tsum hsum_d_norm.of_norm hprod_sum]
  -- Bijection `(Σ n : ℕ+, { d : ℕ // d ∈ (n : ℕ).divisors }) ≃ ℕ+ × ℕ+`
  let eDiv : (Σ n : ℕ+, { d : ℕ // d ∈ (n : ℕ).divisors }) ≃ ℕ+ × ℕ+ :=
    { toFun := fun ⟨n, d⟩ =>
        have hd_pos : 0 < d.1 := Nat.pos_of_mem_divisors d.2
        have hq_pos : 0 < (n : ℕ) / d.1 :=
          Nat.div_pos (Nat.le_of_dvd n.pos (Nat.dvd_of_mem_divisors d.2)) hd_pos
        ((⟨d.1, hd_pos⟩ : ℕ+), (⟨(n : ℕ) / d.1, hq_pos⟩ : ℕ+))
      invFun := fun p => ⟨p.1 * p.2, ⟨(p.1 : ℕ), Nat.mem_divisors.mpr ⟨⟨(p.2 : ℕ), rfl⟩, (p.1 * p.2).pos.ne'⟩⟩⟩
      left_inv := fun ⟨n, ⟨dval, hdmem⟩⟩ => by
        have hd_pos : 0 < dval := Nat.pos_of_mem_divisors hdmem
        have hq_pos : 0 < (n : ℕ) / dval :=
          Nat.div_pos (Nat.le_of_dvd n.pos (Nat.dvd_of_mem_divisors hdmem)) hd_pos
        have hm : (⟨dval, hd_pos⟩ : ℕ+) * (⟨(n : ℕ) / dval, hq_pos⟩ : ℕ+) = n :=
          Subtype.ext (Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hdmem))
        refine Sigma.ext hm ?_
        exact (Subtype.heq_iff_coe_eq (fun x => by
          change x ∈ (((⟨dval, hd_pos⟩ : ℕ+) * (⟨(n : ℕ) / dval, hq_pos⟩ : ℕ+) : ℕ+) : ℕ).divisors ↔
            x ∈ (n : ℕ).divisors
          rw [hm]; exact Iff.rfl)).mpr rfl
      right_inv := fun p => by
        apply Prod.ext
        · apply Subtype.ext; rfl
        · apply Subtype.ext; change ((p.1 : ℕ) * (p.2 : ℕ)) / (p.1 : ℕ) = (p.2 : ℕ)
          exact Nat.mul_div_cancel_left _ p.1.pos }
  have hsum_sig : Summable (fun x : Σ n : ℕ+, { d : ℕ // d ∈ (n : ℕ).divisors } =>
      ((Nat.totient ((eDiv x).1 : ℕ) : ℂ) * (((eDiv x).1 : ℕ) : ℂ) ^ (-(2 * s))) *
        (((eDiv x).2 : ℕ) : ℂ) ^ (-(2 * s))) :=
    (Equiv.summable_iff eDiv).mpr hprod_sum
  rw [← eDiv.tsum_eq, hsum_sig.tsum_sigma' (fun _ => (hasSum_fintype _).summable)]
  refine tsum_congr fun n => ?_
  have hterm_eq : ∀ d : { d : ℕ // d ∈ (n : ℕ).divisors },
      ((Nat.totient ((eDiv ⟨n, d⟩).1 : ℕ) : ℂ) * (((eDiv ⟨n, d⟩).1 : ℕ) : ℂ) ^ (-(2 * s))) *
        (((eDiv ⟨n, d⟩).2 : ℕ) : ℂ) ^ (-(2 * s)) =
      (Nat.totient d.1 : ℂ) * ((n : ℕ) : ℂ) ^ (-(2 * s)) := by
    intro d
    have hd_pos : 0 < d.1 := Nat.pos_of_mem_divisors d.2
    have hq_pos : 0 < (n : ℕ) / d.1 :=
      Nat.div_pos (Nat.le_of_dvd n.pos (Nat.dvd_of_mem_divisors d.2)) hd_pos
    have ha_pos : (0 : ℝ) < (d.1 : ℝ) := by exact_mod_cast hd_pos
    have hb_pos : (0 : ℝ) < ((n : ℕ) / d.1 : ℕ) := by exact_mod_cast hq_pos
    have hn_eq : ((n : ℕ) : ℝ) = (d.1 : ℝ) * (((n : ℕ) / d.1 : ℕ) : ℝ) := by
      exact_mod_cast (Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors d.2)).symm
    have h1 : ((eDiv ⟨n, d⟩).1 : ℕ) = d.1 := rfl
    have h2 : ((eDiv ⟨n, d⟩).2 : ℕ) = (n : ℕ) / d.1 := rfl
    rw [h1, h2, mul_assoc, show ((d.1 : ℕ) : ℂ) ^ (-(2 * s)) * (((n : ℕ) / d.1 : ℕ) : ℂ) ^ (-(2 * s)) =
        ((n : ℕ) : ℂ) ^ (-(2 * s)) by
      rw [show ((d.1 : ℕ) : ℂ) = ((d.1 : ℝ) : ℂ) by push_cast; rfl,
        show (((n : ℕ) / d.1 : ℕ) : ℂ) = ((((n : ℕ) / d.1 : ℕ) : ℝ) : ℂ) by push_cast; rfl,
        ← ofReal_mul_cpow ha_pos hb_pos (-(2 * s)), ← hn_eq]
      push_cast; rfl]
  simp_rw [hterm_eq]
  rw [tsum_fintype, ← Finset.sum_mul,
    Finset.sum_coe_sort (s := (n : ℕ).divisors) (f := fun d => (Nat.totient d : ℂ))]
  have hsum_tot : (∑ d ∈ (n : ℕ).divisors, (Nat.totient d : ℂ)) = ((n : ℕ) : ℂ) := by
    exact_mod_cast Nat.sum_totient (n : ℕ)
  rw [hsum_tot]
  have hnC : ((n : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.pos.ne'
  calc ((n : ℕ) : ℂ) * ((n : ℕ) : ℂ) ^ (-(2 * s))
      = ((n : ℕ) : ℂ) ^ (1 : ℂ) * ((n : ℕ) : ℂ) ^ (-(2 * s)) := by rw [Complex.cpow_one]
    _ = ((n : ℕ) : ℂ) ^ (1 + -(2 * s)) := (Complex.cpow_add _ _ hnC).symm
    _ = ((n : ℕ) : ℂ) ^ (1 - 2 * s) := by rw [← sub_eq_add_neg]

/-! ### Part 4E: Spectral Scattering Matrix `φ(s) = Λ(2s - 1) / Λ(2s)`, Functional Equation & Critical-Line Unitarity -/

/-- **Spectral Scattering Matrix `φ(s)` on `SL₂(ℤ) \ ℍ`**:
$$\varphi(s) = \frac{\Lambda(2 s - 1)}{\Lambda(2 s)}.$$ -/
def scatteringMatrix (s : ℂ) : ℂ :=
  completedRiemannZeta (2 * s - 1) / completedRiemannZeta (2 * s)

/-- Conjugation symmetry of `Complex.Gammaℝ`: `Gammaℝ (conj s) = conj (Gammaℝ s)`. -/
lemma Gammaℝ_conj (s : ℂ) : Complex.Gammaℝ (conj s) = conj (Complex.Gammaℝ s) := by
  rw [Complex.Gammaℝ_def, Complex.Gammaℝ_def, map_mul, ← Complex.Gamma_conj,
    show conj s / 2 = conj (s / 2) by simp [map_ofNat]]
  congr 1
  have hpiC : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
  rw [Complex.cpow_def_of_ne_zero hpiC, Complex.cpow_def_of_ne_zero hpiC,
    ← Complex.exp_conj, map_mul, ← Complex.ofReal_log Real.pi_pos.le, Complex.conj_ofReal]
  congr 2
  simp [map_ofNat]

/-- Conjugation symmetry of `completedRiemannZeta` away from `{0, 1}`:
`completedRiemannZeta (conj s) = conj (completedRiemannZeta s)`. -/
theorem completedRiemannZeta_conj {s : ℂ} (hs0 : s ≠ 0) :
    completedRiemannZeta (conj s) = conj (completedRiemannZeta s) := by
  have hcs0 : conj s ≠ 0 := by
    intro h; apply hs0; exact (map_eq_zero (starRingEnd ℂ)).mp h
  have h1 : riemannZeta (conj s) = completedRiemannZeta (conj s) / Complex.Gammaℝ (conj s) :=
    riemannZeta_def_of_ne_zero hcs0
  have h2 : riemannZeta s = completedRiemannZeta s / Complex.Gammaℝ s :=
    riemannZeta_def_of_ne_zero hs0
  by_cases hG : Complex.Gammaℝ s = 0
  · -- Only occurs at negative even integers, where `completedRiemannZeta` is not needed for critical line,
    -- wait: let's prove it for ALL `s` directly via `completedRiemannZeta_one_sub` when `Re(s) ≤ 0`!
    by_cases hre : 0 < s.re
    · exfalso
      rw [Complex.Gammaℝ_def] at hG
      exact mul_ne_zero
        (Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_pos.ne')))
        (Complex.Gamma_ne_zero_of_re_pos (by simp; linarith)) hG
    · -- Use functional equation `Λ(s) = Λ(1 - s)`: if `Re(s) ≤ 0`, then `Re(1 - s) ≥ 1 > 0`!
      have h1s_re : 0 < (1 - s).re := by simp; linarith
      have h1s0 : 1 - s ≠ 0 := fun h => by have := congrArg Complex.re h; simp at this; linarith
      have h1cs0 : 1 - conj s ≠ 0 := fun h => by
        have : conj (1 - s) = 0 := by simpa using h
        exact h1s0 ((map_eq_zero (starRingEnd ℂ)).mp this)
      have hG1 : Complex.Gammaℝ (1 - s) ≠ 0 := by
        rw [Complex.Gammaℝ_def]
        exact mul_ne_zero
          (Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_pos.ne')))
          (Complex.Gamma_ne_zero_of_re_pos (by simp; linarith))
      have hG1c : Complex.Gammaℝ (conj (1 - s)) ≠ 0 := by
        rw [Gammaℝ_conj]; exact (map_ne_zero (starRingEnd ℂ)).mpr hG1
      have ha : completedRiemannZeta (1 - s) = riemannZeta (1 - s) * Complex.Gammaℝ (1 - s) := by
        rw [riemannZeta_def_of_ne_zero h1s0, div_mul_cancel₀ _ hG1]
      have hb : completedRiemannZeta (conj (1 - s)) =
          riemannZeta (conj (1 - s)) * Complex.Gammaℝ (conj (1 - s)) := by
        have hne : conj (1 - s) ≠ 0 := (map_ne_zero (starRingEnd ℂ)).mpr h1s0
        rw [riemannZeta_def_of_ne_zero hne, div_mul_cancel₀ _ hG1c]
      rw [← completedRiemannZeta_one_sub (conj s), ← completedRiemannZeta_one_sub s,
        show 1 - conj s = conj (1 - s) by simp, hb, ha, map_mul, riemannZeta_conj, Gammaℝ_conj]
  · have hGc : Complex.Gammaℝ (conj s) ≠ 0 := by
      rw [Gammaℝ_conj]; exact (map_ne_zero (starRingEnd ℂ)).mpr hG
    have ha : completedRiemannZeta s = riemannZeta s * Complex.Gammaℝ s := by
      rw [h2, div_mul_cancel₀ _ hG]
    have hb : completedRiemannZeta (conj s) = riemannZeta (conj s) * Complex.Gammaℝ (conj s) := by
      rw [h1, div_mul_cancel₀ _ hGc]
    rw [hb, ha, map_mul, riemannZeta_conj, Gammaℝ_conj]

/-- Nonvanishing of `completedRiemannZeta` on the vertical line `Re(w) = 1`:
for every `t : ℝ`, `completedRiemannZeta (1 + Complex.I * (t : ℂ)) ≠ 0`. -/
theorem completedRiemannZeta_one_add_I_mul_ne_zero (t : ℝ) :
    completedRiemannZeta (1 + Complex.I * (t : ℂ)) ≠ 0 := by
  have hw0 : (1 : ℂ) + Complex.I * (t : ℂ) ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this
  have hG : Complex.Gammaℝ (1 + Complex.I * (t : ℂ)) ≠ 0 := by
    rw [Complex.Gammaℝ_def]
    exact mul_ne_zero
      (Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_pos.ne')))
      (Complex.Gamma_ne_zero_of_re_pos (by simp))
  have hlam : completedRiemannZeta (1 + Complex.I * (t : ℂ)) =
      riemannZeta (1 + Complex.I * (t : ℂ)) * Complex.Gammaℝ (1 + Complex.I * (t : ℂ)) := by
    rw [riemannZeta_def_of_ne_zero hw0, div_mul_cancel₀ _ hG]
  rw [hlam]
  refine mul_ne_zero ?_ hG
  by_cases ht : t = 0
  · subst ht; simpa using riemannZeta_one_ne_zero
  · exact riemannZeta_ne_zero_of_one_le_re (by simp)

/-- **EXACT SCATTERING MATRIX FUNCTIONAL EQUATION**:
$$\varphi(s) \cdot \varphi(1 - s) = 1$$
for every `s : ℂ` where `Λ(2s) ≠ 0` and `Λ(2s - 1) ≠ 0`. -/
theorem scatteringMatrix_functional_eq {s : ℂ}
    (h1 : completedRiemannZeta (2 * s) ≠ 0) (h2 : completedRiemannZeta (2 * s - 1) ≠ 0) :
    scatteringMatrix s * scatteringMatrix (1 - s) = 1 := by
  unfold scatteringMatrix
  have hfe1 : completedRiemannZeta (2 * (1 - s) - 1) = completedRiemannZeta (2 * s) := by
    rw [show 2 * (1 - s) - 1 = 1 - 2 * s by ring, completedRiemannZeta_one_sub]
  have hfe2 : completedRiemannZeta (2 * (1 - s)) = completedRiemannZeta (2 * s - 1) := by
    rw [show 2 * (1 - s) = 1 - (2 * s - 1) by ring, completedRiemannZeta_one_sub]
  rw [hfe1, hfe2]
  field_simp [h1, h2]

/-- **UNCONDITIONAL UNITARITY OF THE SCATTERING MATRIX ON THE CRITICAL LINE `Re(s) = 1 / 2`**:
for EVERY `t : ℝ` (ZERO assumptions!),
$$\|\varphi(1/2 + i t)\| = 1.$$ -/
theorem norm_scatteringMatrix_half_add_I_mul (t : ℝ) :
    ‖scatteringMatrix ((1 / 2 : ℂ) + Complex.I * (t : ℂ))‖ = 1 := by
  unfold scatteringMatrix
  have h2s : 2 * ((1 / 2 : ℂ) + Complex.I * (t : ℂ)) = 1 + Complex.I * ((2 * t : ℝ) : ℂ) := by
    push_cast; ring
  have h2sm1 : 2 * ((1 / 2 : ℂ) + Complex.I * (t : ℂ)) - 1 =
      1 - conj (1 + Complex.I * ((2 * t : ℝ) : ℂ)) := by
    simp only [map_add, map_one, map_mul, Complex.conj_I, Complex.conj_ofReal]
    push_cast; ring
  have hne : completedRiemannZeta (1 + Complex.I * ((2 * t : ℝ) : ℂ)) ≠ 0 :=
    completedRiemannZeta_one_add_I_mul_ne_zero (2 * t)
  have hw0 : (1 : ℂ) + Complex.I * ((2 * t : ℝ) : ℂ) ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this
  rw [h2sm1, h2s, completedRiemannZeta_one_sub, completedRiemannZeta_conj hw0,
    norm_div, RCLike.norm_conj, div_self (norm_ne_zero_iff.mpr hne)]

/-- **UNCONDITIONAL CRITICAL-LINE SCATTERING FUNCTIONAL EQUATION (ZERO SIDE CONDITIONS!)**:
`∀ t : ℝ, scatteringMatrix (1/2 + I * t) * scatteringMatrix (1 - (1/2 + I * t)) = 1`. -/
theorem scatteringMatrix_half_add_I_mul_functional_eq (t : ℝ) :
    scatteringMatrix ((1 / 2 : ℂ) + Complex.I * (t : ℂ)) *
      scatteringMatrix (1 - ((1 / 2 : ℂ) + Complex.I * (t : ℂ))) = 1 := by
  have h1 : completedRiemannZeta (2 * ((1 / 2 : ℂ) + Complex.I * (t : ℂ))) ≠ 0 := by
    rw [show 2 * ((1 / 2 : ℂ) + Complex.I * (t : ℂ)) = 1 + Complex.I * ((2 * t : ℝ) : ℂ) by push_cast; ring]
    exact completedRiemannZeta_one_add_I_mul_ne_zero (2 * t)
  have h2 : completedRiemannZeta (2 * ((1 / 2 : ℂ) + Complex.I * (t : ℂ)) - 1) ≠ 0 := by
    rw [show 2 * ((1 / 2 : ℂ) + Complex.I * (t : ℂ)) - 1 = 1 - (1 + Complex.I * ((-2 * t : ℝ) : ℂ)) by push_cast; ring,
      completedRiemannZeta_one_sub]
    exact completedRiemannZeta_one_add_I_mul_ne_zero (-2 * t)
  exact scatteringMatrix_functional_eq h1 h2

end ConstantTermAndScatteringMatrix

/-! ## Section 5: Unified Stage-10 Master Discharge Theorem -/

/-- **UNIFIED STAGE-10 REAL-ANALYTIC EISENSTEIN SERIES & SPECTRAL SCATTERING MASTER DISCHARGE
(`0` ASSUMPTIONS!)**:
bundles all unconditional Stage-10 theorems on `SL₂(ℤ) \ ℍ`:
1. `SL₂(ℤ)`-invariance of `realEisenstein` and `completedEisenstein`,
2. Exact hyperbolic Laplacian eigenvalue `Δ_ℍ E(τ, s) = s (1 - s) E(τ, s)` for `Re(s) > 1`,
3. Exact 2D theta modular transformation `θ_τ(1 / t) = t · θ_τ(t)` for `t > 0`,
4. Global meromorphic continuation of `E*(τ, s)` on `ℂ \ {0, 1}` with exact functional equation
   `E*(τ, 1 - s) = E*(τ, s)` and residue `3 / π` at `s = 1`,
5. Exact 0-th Fourier coefficient `∫₀¹ E(x + i y, s) dx = y^s + φ(s) y^{1 - s}` for `Re(s) > 1`,
6. Unconditional critical-line scattering unitarity `‖φ(1 / 2 + i t)‖ = 1` for all `t ∈ ℝ`. -/
theorem stage10_eisenstein_spectral_master_discharge :
    (∀ (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (τ : UpperHalfPlane) (s : ℂ),
      realEisenstein (γ • τ) s = realEisenstein τ s) ∧
    (∀ (τ : UpperHalfPlane) {s : ℂ}, 1 < s.re →
      hypLaplacian (fun w => realEisenstein w s) τ = s * (1 - s) * realEisenstein τ s) ∧
    (∀ (τ : UpperHalfPlane) {t : ℝ}, 0 < t →
      binaryTheta τ (1 / t) = t * binaryTheta τ t) ∧
    (∀ (τ : UpperHalfPlane) (s : ℂ),
      completedEisenstein τ (1 - s) = completedEisenstein τ s) ∧
    (∀ (τ : UpperHalfPlane),
      DifferentiableOn ℂ (completedEisenstein τ) ({(0 : ℂ), (1 : ℂ)}ᶜ)) ∧
    (∀ {y : ℝ} (hy : 0 < y) {s : ℂ}, 1 < s.re →
      (∫ x in (0 : ℝ)..1, realEisenstein ⟨(x : ℂ) + Complex.I * (y : ℂ), by simp [hy]⟩ s) =
        (y : ℂ) ^ s + scatteringMatrix s * (y : ℂ) ^ (1 - s)) ∧
    (∀ t : ℝ, ‖scatteringMatrix ((1 / 2 : ℂ) + Complex.I * (t : ℂ))‖ = 1) :=
  ⟨realEisenstein_SL2Z_invariant,
   fun τ _ hs => hypLaplacian_realEisenstein τ hs,
   fun τ _ ht => binaryTheta_inv_eq τ ht,
   completedEisenstein_functional_equation,
   completedEisenstein_meromorphic,
   fun hy _ hs => realEisenstein_constant_term_eq hy hs,
   norm_scatteringMatrix_half_add_I_mul⟩

end
end RHDirect.Stage10EisensteinSpectral
