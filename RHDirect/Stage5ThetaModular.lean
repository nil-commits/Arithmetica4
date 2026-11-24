import RHDirect.Stage4SelbergTrace
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.Modular
import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable
import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable
import Mathlib.NumberTheory.ModularForms.SlashActions

/-!
# RHDirect.Stage5ThetaModular

Concrete `UpperHalfPlane` Lattice Theta Modularity, Even Unimodular `E₈` / `E₈^k` Weight-`4k`
`SL₂(ℤ)` Slash-Invariance, and Global Mellin–Epstein Completed Zeta Functional Equation
in pure Mathlib `v4.33.1` (0 `sorry`, 0 custom `axiom`s).
-/

open Complex Real Filter MeasureTheory Module Submodule Finset
open RHDirect.ArakelovCovolume RHDirect.Stage3ThetaSiegelBridge RHDirect.Stage4SelbergTrace
open scoped BigOperators UpperHalfPlane ModularForm Topology ENNReal Manifold

namespace RHDirect.Stage5ThetaModular

noncomputable section

/-! ## Section 1: Complex Upper-Half-Plane Lattice Theta Series `Θ_L(τ)` -/

section ComplexLatticeTheta

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Complex Gaussian lattice summand `v ↦ exp(π i τ ‖v‖²)`. -/
def complexGaussianTerm (τ : ℂ) (v : E) : ℂ :=
  Complex.exp ((Real.pi : ℂ) * Complex.I * τ * ((‖v‖ ^ 2 : ℝ) : ℂ))

/-- Complex lattice theta function `Θ_L(τ) = ∑'_{v ∈ L} exp(π i τ ‖v‖²)` on `ℂ`
(convergent on the upper half-plane `{τ : ℂ | 0 < τ.im}`). -/
def complexLatticeThetaFun (L : Submodule ℤ E) (τ : ℂ) : ℂ :=
  ∑' v : L, complexGaussianTerm τ (v : E)

/-- **Complex Upper-Half-Plane Lattice Theta Series** `Θ_L : ℍ → ℂ`. -/
def complexLatticeTheta (L : Submodule ℤ E) (τ : UpperHalfPlane) : ℂ :=
  complexLatticeThetaFun L (τ : ℂ)

/-- An **integral lattice** has integer squared norms: `∀ v ∈ L, ‖v‖² ∈ ℤ`. -/
def IsIntegralLattice (L : Submodule ℤ E) : Prop :=
  ∀ v ∈ L, ∃ m : ℤ, ‖v‖ ^ 2 = (m : ℝ)

/-- An **even lattice** has even integer squared norms: `∀ v ∈ L, ‖v‖² ∈ 2ℤ`. -/
def IsEvenLattice (L : Submodule ℤ E) : Prop :=
  ∀ v ∈ L, ∃ m : ℤ, ‖v‖ ^ 2 = 2 * (m : ℝ)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma IsEvenLattice.isIntegral {L : Submodule ℤ E} (hL : IsEvenLattice L) :
    IsIntegralLattice L := by
  intro v hv
  obtain ⟨m, hm⟩ := hL v hv
  exact ⟨2 * m, by push_cast; linarith⟩

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
@[simp]
lemma complexGaussianTerm_zero (τ : ℂ) : complexGaussianTerm τ (0 : E) = 1 := by
  simp [complexGaussianTerm]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma norm_complexGaussianTerm (τ : ℂ) (v : E) :
    ‖complexGaussianTerm τ v‖ = gaussianTerm τ.im v := by
  unfold complexGaussianTerm gaussianTerm
  rw [Complex.norm_exp]
  congr 1
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]
  ring

/-- **Unconditional Absolute Summability of the Complex Gaussian Lattice Summands**:
for every discrete `ℤ`-lattice `L ⊂ E` and every `τ ∈ ℂ` with `0 < τ.im`,
`v ↦ ‖exp(π i τ ‖v‖²)‖` is summable on `L`. -/
theorem summable_norm_complexGaussianTerm (L : Submodule ℤ E) [DiscreteTopology L]
    {τ : ℂ} (hτ : 0 < τ.im) :
    Summable (fun v : L => ‖complexGaussianTerm τ (v : E)‖) := by
  simpa only [norm_complexGaussianTerm] using summable_gaussianTerm L hτ

/-- **Unconditional Summability of the Complex Lattice Theta Series** on `{τ : ℂ | 0 < τ.im}`. -/
theorem summable_complexGaussianTerm (L : Submodule ℤ E) [DiscreteTopology L]
    {τ : ℂ} (hτ : 0 < τ.im) :
    Summable (fun v : L => complexGaussianTerm τ (v : E)) :=
  (summable_norm_complexGaussianTerm L hτ).of_norm

/-- Norm upper bound on `UpperHalfPlane`: `‖Θ_L(τ)‖ ≤ Θ_L(Im τ)`. -/
theorem norm_complexLatticeTheta_le (L : Submodule ℤ E) [DiscreteTopology L]
    (τ : UpperHalfPlane) :
    ‖complexLatticeTheta L τ‖ ≤ latticeTheta L τ.im := by
  unfold complexLatticeTheta complexLatticeThetaFun latticeTheta
  have h1 := norm_tsum_le_tsum_norm (summable_norm_complexGaussianTerm L τ.im_pos)
  exact h1.trans_eq (tsum_congr fun v => norm_complexGaussianTerm (τ : ℂ) (v : E))

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- **Exact Restriction to the Positive Imaginary Axis**:
for every `t : ℝ`, `Θ_L(i t) = (latticeTheta L t : ℂ)`. -/
theorem complexLatticeThetaFun_imaginary_axis (L : Submodule ℤ E) (t : ℝ) :
    complexLatticeThetaFun L (Complex.I * (t : ℂ)) = (latticeTheta L t : ℂ) := by
  unfold complexLatticeThetaFun latticeTheta
  rw [Complex.ofReal_tsum]
  refine tsum_congr fun v => ?_
  unfold complexGaussianTerm gaussianTerm
  rw [Complex.ofReal_exp]
  congr 1
  simp only [Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_pow]
  linear_combination (Real.pi : ℂ) * (t : ℂ) * ((‖(v : E)‖ : ℂ) ^ 2) * Complex.I_mul_I

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- **Exact `UpperHalfPlane` Restriction to the Positive Imaginary Axis**:
for every `t > 0`, `complexLatticeTheta L ⟨I * t, ht⟩ = (latticeTheta L t : ℂ)`. -/
theorem complexLatticeTheta_imaginary_axis (L : Submodule ℤ E) {t : ℝ} (ht : 0 < t) :
    complexLatticeTheta L ⟨Complex.I * (t : ℂ), by simp [ht]⟩ = (latticeTheta L t : ℂ) :=
  complexLatticeThetaFun_imaginary_axis L t

/-- **Holomorphicity of `Θ_L(τ)` on the Upper Half-Plane `{τ : ℂ | 0 < τ.im}`**
(via Weierstrass M-test on horizontal strips `{τ | δ < τ.im}` and
`Complex.differentiableOn_tsum_of_summable_norm`). -/
theorem differentiableOn_complexLatticeThetaFun (L : Submodule ℤ E) [DiscreteTopology L] :
    DifferentiableOn ℂ (complexLatticeThetaFun L) {z : ℂ | 0 < z.im} := by
  intro z₀ hz₀
  have hδ : 0 < z₀.im / 2 := half_pos hz₀
  let U : Set ℂ := {z : ℂ | z₀.im / 2 < z.im}
  have hU_open : IsOpen U := isOpen_lt continuous_const Complex.continuous_im
  have hz₀U : z₀ ∈ U := by
    change z₀.im / 2 < z₀.im
    linarith [hz₀]
  have hdiffU : DifferentiableOn ℂ (complexLatticeThetaFun L) U := by
    refine Complex.differentiableOn_tsum_of_summable_norm
      (u := fun v : L => gaussianTerm (z₀.im / 2) (v : E))
      (summable_gaussianTerm L hδ) ?_ hU_open ?_
    · intro v
      unfold complexGaussianTerm
      refine (Differentiable.cexp ?_).differentiableOn
      fun_prop
    · intro v w hw
      rw [norm_complexGaussianTerm]
      unfold gaussianTerm
      apply Real.exp_le_exp.mpr
      have hw' : z₀.im / 2 < w.im := hw
      have hnn : 0 ≤ Real.pi * ‖(v : E)‖ ^ 2 := mul_nonneg Real.pi_pos.le (sq_nonneg _)
      nlinarith
  exact (hdiffU.differentiableAt (hU_open.mem_nhds hz₀U)).differentiableWithinAt

/-- **Holomorphicity of `complexLatticeTheta L` as a function on `UpperHalfPlane`**. -/
theorem differentiableOn_complexLatticeTheta (L : Submodule ℤ E) [DiscreteTopology L] :
    DifferentiableOn ℂ (complexLatticeTheta L ∘ (UpperHalfPlane.ofComplex : ℂ → UpperHalfPlane))
      {z : ℂ | 0 < z.im} := by
  refine (differentiableOn_complexLatticeThetaFun L).congr fun z hz => ?_
  simp only [Function.comp_apply, complexLatticeTheta]
  congr 1
  have h1 : UpperHalfPlane.ofComplex z = ⟨z, hz⟩ := UpperHalfPlane.ofComplex_apply_of_im_pos hz
  rw [h1]

/-- **Complex-Manifold Holomorphicity `MDiff (complexLatticeTheta L)` on `UpperHalfPlane`**. -/
theorem mdifferentiable_complexLatticeTheta (L : Submodule ℤ E) [DiscreteTopology L] :
    MDiff (complexLatticeTheta L) :=
  UpperHalfPlane.mdifferentiable_iff.mpr (differentiableOn_complexLatticeTheta L)

/-- Continuity of the real-axis Gaussian lattice theta series `latticeTheta L` on `(0, ∞)`. -/
theorem continuousOn_latticeTheta (L : Submodule ℤ E) [DiscreteTopology L] :
    ContinuousOn (latticeTheta L) (Set.Ioi 0) := by
  have hcontC : ContinuousOn (fun t : ℝ => (latticeTheta L t : ℂ)) (Set.Ioi 0) := by
    have hcomp : ContinuousOn (fun t : ℝ => complexLatticeThetaFun L (Complex.I * (t : ℂ)))
        (Set.Ioi 0) := by
      refine (differentiableOn_complexLatticeThetaFun L).continuousOn.comp ?_ ?_
      · exact (continuous_const.mul Complex.continuous_ofReal).continuousOn
      · intro t ht
        change 0 < (Complex.I * (t : ℂ)).im
        simpa using ht
    exact hcomp.congr fun t _ => (complexLatticeThetaFun_imaginary_axis L t).symm
  have hre : (fun t : ℝ => ((latticeTheta L t : ℂ)).re) = latticeTheta L := by
    funext t; exact Complex.ofReal_re _
  rw [← hre]
  exact Complex.continuous_re.comp_continuousOn hcontC

/-! ### Translation Periodicity (`τ ↦ τ + 2` for Integral Lattices, `τ ↦ τ + 1` for Even Lattices) -/

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- For every **integral lattice** `L` (`∀ v ∈ L, ‖v‖² ∈ ℤ`), `Θ_L(τ + 2) = Θ_L(τ)`. -/
theorem complexLatticeThetaFun_add_two_of_integral {L : Submodule ℤ E} (hL : IsIntegralLattice L)
    (τ : ℂ) :
    complexLatticeThetaFun L (τ + 2) = complexLatticeThetaFun L τ := by
  unfold complexLatticeThetaFun
  refine tsum_congr fun v => ?_
  obtain ⟨m, hm⟩ := hL (v : E) v.2
  unfold complexGaussianTerm
  rw [show (Real.pi : ℂ) * Complex.I * (τ + 2) * ((‖(v : E)‖ ^ 2 : ℝ) : ℂ) =
      (Real.pi : ℂ) * Complex.I * τ * ((‖(v : E)‖ ^ 2 : ℝ) : ℂ) +
      (m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) by
    rw [hm]; push_cast; ring]
  rw [Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- For every **integral lattice** `L`, `Θ_L(T² • τ) = Θ_L(τ)` on `UpperHalfPlane`. -/
theorem complexLatticeTheta_T_sq_smul_of_integral {L : Submodule ℤ E} (hL : IsIntegralLattice L)
    (τ : UpperHalfPlane) :
    complexLatticeTheta L ((ModularGroup.T ^ (2 : ℤ)) • τ) = complexLatticeTheta L τ := by
  unfold complexLatticeTheta
  rw [ModularGroup.coe_T_zpow_smul_eq]
  simpa using complexLatticeThetaFun_add_two_of_integral hL (τ : ℂ)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- For every **even lattice** `L` (`∀ v ∈ L, ‖v‖² ∈ 2ℤ`), `Θ_L(τ + 1) = Θ_L(τ)`. -/
theorem complexLatticeThetaFun_add_one_of_even {L : Submodule ℤ E} (hL : IsEvenLattice L)
    (τ : ℂ) :
    complexLatticeThetaFun L (τ + 1) = complexLatticeThetaFun L τ := by
  unfold complexLatticeThetaFun
  refine tsum_congr fun v => ?_
  obtain ⟨m, hm⟩ := hL (v : E) v.2
  unfold complexGaussianTerm
  rw [show (Real.pi : ℂ) * Complex.I * (τ + 1) * ((‖(v : E)‖ ^ 2 : ℝ) : ℂ) =
      (Real.pi : ℂ) * Complex.I * τ * ((‖(v : E)‖ ^ 2 : ℝ) : ℂ) +
      (m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) by
    rw [hm]; push_cast; ring]
  rw [Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- For every **even lattice** `L`, `Θ_L(T • τ) = Θ_L(τ)` on `UpperHalfPlane`. -/
theorem complexLatticeTheta_T_smul_of_even {L : Submodule ℤ E} (hL : IsEvenLattice L)
    (τ : UpperHalfPlane) :
    complexLatticeTheta L (ModularGroup.T • τ) = complexLatticeTheta L τ := by
  unfold complexLatticeTheta
  have hT : ((ModularGroup.T • τ : UpperHalfPlane) : ℂ) = (τ : ℂ) + 1 := by
    simpa [zpow_one] using ModularGroup.coe_T_zpow_smul_eq τ (n := 1)
  rw [hT]
  exact complexLatticeThetaFun_add_one_of_even hL (τ : ℂ)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- For every **even lattice** `L` and every `n : ℤ`, `Θ_L(T^n • τ) = Θ_L(τ)`. -/
theorem complexLatticeTheta_T_zpow_smul_of_even {L : Submodule ℤ E} (hL : IsEvenLattice L)
    (n : ℤ) (τ : UpperHalfPlane) :
    complexLatticeTheta L ((ModularGroup.T ^ n) • τ) = complexLatticeTheta L τ := by
  unfold complexLatticeTheta
  rw [ModularGroup.coe_T_zpow_smul_eq]
  unfold complexLatticeThetaFun
  refine tsum_congr fun v => ?_
  obtain ⟨m, hm⟩ := hL (v : E) v.2
  unfold complexGaussianTerm
  rw [show (Real.pi : ℂ) * Complex.I * ((τ : ℂ) + (n : ℂ)) * ((‖(v : E)‖ ^ 2 : ℝ) : ℂ) =
      (Real.pi : ℂ) * Complex.I * (τ : ℂ) * ((‖(v : E)‖ ^ 2 : ℝ) : ℂ) +
      ((n * m : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) by
    rw [hm]; push_cast; ring]
  rw [Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

end ComplexLatticeTheta

/-! ## Section 2: Exact Modular Inversion Law, Concrete `E₈` / `E₈^k` Lattices & `SL₂(ℤ)` Weight-`4k` Slash-Invariance -/

section ComplexModularInversion

/-! ### Part 2A: Exact Complex 1D & Orthogonal-Lattice Modular Inversion via `Complex.tsum_exp_neg_mul_int_sq` -/

/-- Complex 1D scaled theta series `θ_a(τ) = ∑'_{n ∈ ℤ} exp(π i τ (a n)²)`. -/
def complexTheta1D (a : ℝ) (τ : ℂ) : ℂ :=
  ∑' n : ℤ, Complex.exp ((Real.pi : ℂ) * Complex.I * τ * (((a * (n : ℝ)) ^ 2 : ℝ) : ℂ))

lemma norm_complexTheta1D_term (a : ℝ) (τ : ℂ) (n : ℤ) :
    ‖Complex.exp ((Real.pi : ℂ) * Complex.I * τ * (((a * (n : ℝ)) ^ 2 : ℝ) : ℂ))‖ =
      Real.exp (-Real.pi * τ.im * (a * (n : ℝ)) ^ 2) := by
  rw [Complex.norm_exp]
  congr 1
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]
  ring

theorem summable_norm_complexTheta1D {a : ℝ} (ha : 0 < a) {τ : ℂ} (hτ : 0 < τ.im) :
    Summable (fun n : ℤ =>
      ‖Complex.exp ((Real.pi : ℂ) * Complex.I * τ * (((a * (n : ℝ)) ^ 2 : ℝ) : ℂ))‖) := by
  simpa only [norm_complexTheta1D_term] using summable_theta1D ha hτ

theorem summable_complexTheta1D {a : ℝ} (ha : 0 < a) {τ : ℂ} (hτ : 0 < τ.im) :
    Summable (fun n : ℤ =>
      Complex.exp ((Real.pi : ℂ) * Complex.I * τ * (((a * (n : ℝ)) ^ 2 : ℝ) : ℂ))) :=
  (summable_norm_complexTheta1D ha hτ).of_norm

/-- Complex multi-dimensional product factorization for `tsum` over `Fin r → ℤ`:
if each coordinate factor `f i : ℤ → ℂ` is absolutely summable, then
`∑' c : Fin r → ℤ, ∏ i, f i (c i) = ∏ i, ∑' n : ℤ, f i n`. -/
theorem summable_norm_and_tsum_pi_fin_prod_complex :
    ∀ {r : ℕ} (f : Fin r → ℤ → ℂ),
      (∀ i, Summable (fun n : ℤ => ‖f i n‖)) →
      Summable (fun c : Fin r → ℤ => ‖∏ i : Fin r, f i (c i)‖) ∧
        (∑' c : Fin r → ℤ, ∏ i : Fin r, f i (c i)) = ∏ i : Fin r, ∑' n : ℤ, f i n
  | 0, f, _ => by
      refine ⟨(hasSum_fintype _).summable, ?_⟩
      rw [tsum_fintype, Finset.univ_unique, Finset.sum_singleton]
      simp
  | r + 1, f, hsum => by
      let f' : Fin r → ℤ → ℂ := fun i => f i.succ
      have ⟨hsum', htsum'⟩ := summable_norm_and_tsum_pi_fin_prod_complex f'
        (fun i => hsum i.succ)
      let e : (ℤ × (Fin r → ℤ)) ≃ (Fin (r + 1) → ℤ) :=
        { toFun := fun p => Fin.cons p.1 p.2
          invFun := fun c => (c 0, fun i => c i.succ)
          left_inv := fun p => by ext <;> simp
          right_inv := fun c => by
            funext i
            refine Fin.cases rfl (fun _ => rfl) i }
      have hprod_norm : Summable (fun p : ℤ × (Fin r → ℤ) =>
          ‖f 0 p.1‖ * ‖∏ i : Fin r, f' i (p.2 i)‖) :=
        Summable.mul_of_nonneg (hsum 0) hsum' (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
      have hprod_sum : Summable (fun p : ℤ × (Fin r → ℤ) =>
          f 0 p.1 * ∏ i : Fin r, f' i (p.2 i)) :=
        (hprod_norm.congr fun p => (norm_mul _ _).symm).of_norm
      have hcomp : (fun c : Fin (r + 1) → ℤ => ∏ i : Fin (r + 1), f i (c i)) ∘ e =
          fun p : ℤ × (Fin r → ℤ) => f 0 p.1 * ∏ i : Fin r, f' i (p.2 i) := by
        funext p
        dsimp only [Function.comp_apply, e, f']
        rw [Fin.prod_univ_succ]
        simp
      have hcomp_norm : (fun c : Fin (r + 1) → ℤ => ‖∏ i : Fin (r + 1), f i (c i)‖) ∘ e =
          fun p : ℤ × (Fin r → ℤ) => ‖f 0 p.1‖ * ‖∏ i : Fin r, f' i (p.2 i)‖ := by
        funext p
        change ‖((fun c : Fin (r + 1) → ℤ => ∏ i : Fin (r + 1), f i (c i)) ∘ e) p‖ = _
        rw [hcomp, norm_mul]
      have hsum_full : Summable (fun c : Fin (r + 1) → ℤ => ‖∏ i : Fin (r + 1), f i (c i)‖) := by
        rw [← Equiv.summable_iff e, hcomp_norm]
        exact hprod_norm
      refine ⟨hsum_full, ?_⟩
      have h0_sum : Summable (f 0) := (hsum 0).of_norm
      have hr_sum : Summable (fun c' : Fin r → ℤ => ∏ i : Fin r, f' i (c' i)) := hsum'.of_norm
      rw [Fin.prod_univ_succ, ← htsum', h0_sum.tsum_mul_tsum hr_sum hprod_sum, ← hcomp]
      exact (e.tsum_eq (fun c : Fin (r + 1) → ℤ => ∏ i : Fin (r + 1), f i (c i))).symm

lemma arg_ne_pi_of_re_pos {z : ℂ} (hz : 0 < z.re) : z.arg ≠ Real.pi := by
  intro hpi
  have hneg : z.re < 0 := (Complex.arg_eq_pi_iff.mp hpi).1
  linarith

/-- Helper: for any `z : ℂ` with `0 < z.re`, `c > 0`, and `w : ℂ`,
`(z * (c : ℂ)) ^ w = z ^ w * (c : ℂ) ^ w`. -/
lemma cpow_mul_ofReal_pos {z : ℂ} (hz : 0 < z.re) {c : ℝ} (hc : 0 < c) (w : ℂ) :
    (z * (c : ℂ)) ^ w = z ^ w * (c : ℂ) ^ w := by
  have hz_ne : z ≠ 0 := fun h => by rw [h] at hz; simp at hz
  have hc_ne : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
  rw [Complex.cpow_def_of_ne_zero (mul_ne_zero hz_ne hc_ne),
    Complex.cpow_def_of_ne_zero hz_ne, Complex.cpow_def_of_ne_zero hc_ne, ← Complex.exp_add]
  congr 1
  have hlog : Complex.log (z * (c : ℂ)) = Complex.log z + Complex.log (c : ℂ) := by
    refine Complex.log_mul hz_ne hc_ne ⟨?_, ?_⟩
    · rw [Complex.arg_ofReal_of_nonneg hc.le, add_zero]
      exact Complex.neg_pi_lt_arg z
    · rw [Complex.arg_ofReal_of_nonneg hc.le, add_zero]
      exact Complex.arg_le_pi z
  rw [hlog]; ring

/-- Helper: for any `z : ℂ` with `0 < z.re` and `a > 0`,
`(z⁻¹ * (a : ℂ)^2) ^ (1 / 2 : ℂ) = (z ^ (1 / 2 : ℂ))⁻¹ * (a : ℂ)`. -/
lemma cpow_half_inv_mul_sq {z : ℂ} (hz : 0 < z.re) {a : ℝ} (ha : 0 < a) :
    (z⁻¹ * ((a : ℂ) ^ 2)) ^ ((1 : ℂ) / 2) = (z ^ ((1 : ℂ) / 2))⁻¹ * (a : ℂ) := by
  have hz_ne : z ≠ 0 := fun h => by rw [h] at hz; simp at hz
  have hinv_re : 0 < z⁻¹.re := by
    rw [Complex.inv_re]
    exact div_pos hz (Complex.normSq_pos.mpr hz_ne)
  have harg_z : z.arg ≠ Real.pi := arg_ne_pi_of_re_pos hz
  have ha2_pos : (0 : ℝ) < a ^ 2 := sq_pos_of_pos ha
  rw [← Complex.ofReal_pow, cpow_mul_ofReal_pos hinv_re ha2_pos]
  have ha_half : ((a ^ 2 : ℝ) : ℂ) ^ ((1 : ℂ) / 2) = (a : ℂ) := by
    have h1 : ((1 : ℂ) / 2) = (((1 : ℝ) / 2 : ℝ) : ℂ) := by push_cast; rfl
    rw [h1, ← Complex.ofReal_cpow ha2_pos.le]
    congr 1
    rw [← Real.rpow_natCast a 2, ← Real.rpow_mul ha.le]
    norm_num
  have hz_inv_cpow : z⁻¹ ^ ((1 : ℂ) / 2) = (z ^ ((1 : ℂ) / 2))⁻¹ := by
    rw [Complex.inv_cpow_eq_ite, if_neg harg_z]
  rw [hz_inv_cpow, ha_half]

/-- **Exact 1D Complex Upper-Half-Plane Theta Inversion**
(directly from Mathlib's `Complex.tsum_exp_neg_mul_int_sq`):
for every `a > 0` and every `τ : UpperHalfPlane`,
`θ_a(S • τ) = (-i τ)^{1/2} · a⁻¹ · θ_{a⁻¹}(τ)`. -/
theorem complexTheta1D_S_smul {a : ℝ} (ha : 0 < a) (τ : UpperHalfPlane) :
    complexTheta1D a ((ModularGroup.S • τ : UpperHalfPlane) : ℂ) =
      (-Complex.I * (τ : ℂ)) ^ ((1 : ℂ) / 2) * (a : ℂ)⁻¹ * complexTheta1D a⁻¹ (τ : ℂ) := by
  unfold complexTheta1D
  have hS : ((ModularGroup.S • τ : UpperHalfPlane) : ℂ) = (-(τ : ℂ))⁻¹ := by
    rw [UpperHalfPlane.modular_S_smul]
  rw [hS]
  have hz_re : 0 < (-Complex.I * (τ : ℂ)).re := by
    simp [τ.im_pos]
  have hz_ne : (-Complex.I * (τ : ℂ)) ≠ 0 := fun h => by rw [h] at hz_re; simp at hz_re
  have hτ_ne : (τ : ℂ) ≠ 0 := τ.ne_zero
  let w : ℂ := (-Complex.I * (τ : ℂ))⁻¹ * ((a : ℂ) ^ 2)
  have hw_re : 0 < w.re := by
    dsimp only [w]
    rw [show ((a : ℂ) ^ 2) = (((a ^ 2 : ℝ) : ℂ)) by push_cast; rfl, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    have hinv_re : 0 < (-Complex.I * (τ : ℂ))⁻¹.re := by
      rw [Complex.inv_re]
      exact div_pos hz_re (Complex.normSq_pos.mpr hz_ne)
    exact mul_pos hinv_re (sq_pos_of_pos ha)
  have hI_inv : Complex.I * (-(τ : ℂ))⁻¹ = -((-Complex.I * (τ : ℂ))⁻¹) := by
    rw [mul_inv, inv_neg, inv_neg, Complex.inv_I]
    ring
  have hlhs : ∀ n : ℤ,
      Complex.exp ((Real.pi : ℂ) * Complex.I * (-(τ : ℂ))⁻¹ * (((a * (n : ℝ)) ^ 2 : ℝ) : ℂ)) =
        Complex.exp (-(Real.pi : ℂ) * w * (n : ℂ) ^ 2) := by
    intro n
    congr 1
    dsimp only [w]
    push_cast
    calc (Real.pi : ℂ) * Complex.I * (-(τ : ℂ))⁻¹ * ((a : ℂ) * (n : ℂ)) ^ 2
        = (Real.pi : ℂ) * (Complex.I * (-(τ : ℂ))⁻¹) * ((a : ℂ) * (n : ℂ)) ^ 2 := by ring
      _ = (Real.pi : ℂ) * (-((-Complex.I * (τ : ℂ))⁻¹)) * ((a : ℂ) * (n : ℂ)) ^ 2 := by
            rw [hI_inv]
      _ = -(Real.pi : ℂ) * ((-Complex.I * (τ : ℂ))⁻¹ * (a : ℂ) ^ 2) * (n : ℂ) ^ 2 := by ring
  have hrhs : ∀ n : ℤ,
      Complex.exp (-(Real.pi : ℂ) / w * (n : ℂ) ^ 2) =
        Complex.exp ((Real.pi : ℂ) * Complex.I * (τ : ℂ) * (((a⁻¹ * (n : ℝ)) ^ 2 : ℝ) : ℂ)) := by
    intro n
    congr 1
    dsimp only [w]
    push_cast
    have haC : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
    field_simp [hτ_ne, haC, Complex.I_ne_zero]
  simp_rw [hlhs]
  rw [Complex.tsum_exp_neg_mul_int_sq hw_re]
  simp_rw [hrhs]
  congr 1
  dsimp only [w]
  rw [cpow_half_inv_mul_sq hz_re ha, one_div, mul_inv, inv_inv]

section OrthogonalComplexTheta

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Exact Product Factorization of `complexLatticeTheta`** on an orthogonal lattice:
`Θ_L(τ) = ∏ i : Fin r, complexTheta1D ‖b_i‖ τ`. -/
theorem complexLatticeTheta_eq_prod_complexTheta1D {L : Submodule ℤ E} [DiscreteTopology L] {r : ℕ}
    (b : Basis (Fin r) ℤ L) (hb : IsOrthogonalBasis b) (τ : UpperHalfPlane) :
    complexLatticeTheta L τ = ∏ i : Fin r, complexTheta1D ‖(b i : E)‖ (τ : ℂ) := by
  let e : (Fin r → ℤ) ≃ L :=
    { toFun := fun c => ∑ i : Fin r, c i • b i
      invFun := fun v i => b.repr v i
      left_inv := fun c => by
        funext i
        simp only [map_sum, map_zsmul, Basis.repr_self, Finsupp.finsetSum_apply,
          Finsupp.smul_apply, smul_eq_mul]
        rw [Finset.sum_eq_single i]
        · simp
        · intro j _ hj; simp [Finsupp.single_eq_of_ne (Ne.symm hj)]
        · intro h; exact absurd (Finset.mem_univ i) h
      right_inv := fun v => b.sum_repr v }
  unfold complexLatticeTheta complexLatticeThetaFun
  rw [← e.tsum_eq]
  have hterm : ∀ c : Fin r → ℤ,
      complexGaussianTerm (τ : ℂ) ((e c : L) : E) =
        ∏ i : Fin r,
          Complex.exp ((Real.pi : ℂ) * Complex.I * (τ : ℂ) *
            (((‖(b i : E)‖ * (c i : ℝ)) ^ 2 : ℝ) : ℂ)) := by
    intro c
    unfold complexGaussianTerm
    have hcoe : ((e c : L) : E) = ∑ i : Fin r, c i • (b i : E) := by
      simp [e]
    rw [hcoe, norm_sq_sum_orthogonalBasis b hb c, Complex.ofReal_sum, Finset.mul_sum,
      Complex.exp_sum]
  simp_rw [hterm]
  exact (summable_norm_and_tsum_pi_fin_prod_complex
    (fun i n => Complex.exp ((Real.pi : ℂ) * Complex.I * (τ : ℂ) *
      (((‖(b i : E)‖ * (n : ℝ)) ^ 2 : ℝ) : ℂ)))
    (fun i => summable_norm_complexTheta1D (norm_basis_pos b i) τ.im_pos)).2

/-- **EXACT COMPLEX UPPER-HALF-PLANE MODULAR INVERSION LAW FOR ORTHOGONAL LATTICES**:
for every discrete orthogonal `ℤ`-lattice `L ⊂ E` of rank `r` and EVERY `τ : UpperHalfPlane`:
$$\Theta_L(S \cdot \tau) = (-i \tau)^{r/2} \cdot \operatorname{covol}(L)^{-1} \cdot \Theta_{L^*}(\tau).$$ -/
theorem complexLatticeTheta_S_smul_orthogonal {L : Submodule ℤ E} [DiscreteTopology L] {r : ℕ}
    (b : Basis (Fin r) ℤ L) (hb : IsOrthogonalBasis b) (τ : UpperHalfPlane) :
    complexLatticeTheta L (ModularGroup.S • τ) =
      (-Complex.I * (τ : ℂ)) ^ ((r : ℂ) / 2) * ((covol L : ℝ) : ℂ)⁻¹ *
        complexLatticeTheta (dualLattice L) τ := by
  have : DiscreteTopology (dualLattice L) := discreteTopology_dualLattice_of_orthogonal b hb
  rw [complexLatticeTheta_eq_prod_complexTheta1D b hb (ModularGroup.S • τ),
    complexLatticeTheta_eq_prod_complexTheta1D (dualBasis b hb) (dualBasis_isOrthogonal b hb) τ,
    covol_of_orthogonalBasis b hb, Complex.ofReal_prod]
  have hfac : ∀ i : Fin r,
      complexTheta1D ‖(b i : E)‖ ((ModularGroup.S • τ : UpperHalfPlane) : ℂ) =
        (-Complex.I * (τ : ℂ)) ^ ((1 : ℂ) / 2) * ((‖(b i : E)‖ : ℂ)⁻¹) *
          complexTheta1D ‖((dualBasis b hb i : dualLattice L) : E)‖ (τ : ℂ) := by
    intro i
    rw [dualBasis_coe, norm_dualVec]
    exact complexTheta1D_S_smul (norm_basis_pos b i) τ
  simp_rw [hfac, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Finset.prod_inv_distrib]
  have hpow : ((-Complex.I * (τ : ℂ)) ^ ((1 : ℂ) / 2)) ^ r =
      (-Complex.I * (τ : ℂ)) ^ ((r : ℂ) / 2) := by
    rw [← Complex.cpow_nat_mul]
    congr 1; ring
  rw [hpow]

/-- **General Analytic Continuation Theorem on `UpperHalfPlane`** (via the Identity Theorem):
for ANY two discrete lattices `L, L' ⊂ E`, rank `r : ℕ`, and scaling constant `C : ℂ`,
if the real-axis theta inversion identity
`Θ_L(t) = t^{-r/2} · C · Θ_{L'}(t⁻¹)` holds for all `t > 0`,
then the full complex upper-half-plane modular inversion law
`Θ_L(S • τ) = (-i τ)^{r/2} · C · Θ_{L'}(τ)` holds for ALL `τ : UpperHalfPlane`! -/
theorem complexLatticeTheta_S_smul_of_real_functional_eq
    (L L' : Submodule ℤ E) [DiscreteTopology L] [DiscreteTopology L']
    (r : ℕ) (C : ℂ)
    (hreal : ∀ t : ℝ, 0 < t →
      (latticeTheta L t : ℂ) = (t : ℂ) ^ (-((r : ℂ) / 2)) * C * (latticeTheta L' t⁻¹ : ℂ))
    (τ : UpperHalfPlane) :
    complexLatticeTheta L (ModularGroup.S • τ) =
      (-Complex.I * (τ : ℂ)) ^ ((r : ℂ) / 2) * C * complexLatticeTheta L' τ := by
  let U : Set ℂ := {z : ℂ | 0 < z.im}
  have hU_open : IsOpen U := isOpen_lt continuous_const Complex.continuous_im
  have hU_conv : Convex ℝ U := by
    intro x hx y hy a b ha hb hab
    change 0 < (a • x + b • y).im
    simp only [Complex.add_im, Complex.real_smul, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, add_zero]
    have hx' : 0 < x.im := hx
    have hy' : 0 < y.im := hy
    rcases eq_or_lt_of_le ha with rfl | ha'
    · have hb1 : b = 1 := by linarith
      rw [hb1]; linarith
    · nlinarith
  have hU_conn : IsPreconnected U := hU_conv.isPreconnected
  let f : ℂ → ℂ := fun z => complexLatticeThetaFun L ((-z)⁻¹)
  let g : ℂ → ℂ := fun z =>
    (-Complex.I * z) ^ ((r : ℂ) / 2) * C * complexLatticeThetaFun L' z
  have hS_maps : Set.MapsTo (fun z : ℂ => (-z)⁻¹) U U := by
    intro z hz
    have hz_im : 0 < z.im := hz
    change 0 < ((-z)⁻¹).im
    have hz_ne : z ≠ 0 := fun h => by rw [h] at hz_im; simp at hz_im
    rw [Complex.inv_im, Complex.neg_im, neg_neg, Complex.normSq_neg]
    exact div_pos hz_im (Complex.normSq_pos.mpr hz_ne)
  have hf_diff : DifferentiableOn ℂ f U := by
    refine (differentiableOn_complexLatticeThetaFun L).comp ?_ hS_maps
    intro z hz
    have hz_im : 0 < z.im := hz
    have hz_ne : -z ≠ 0 := neg_ne_zero.mpr (fun h => by rw [h] at hz_im; simp at hz_im)
    exact (differentiableAt_id.neg.inv hz_ne).differentiableWithinAt
  have hg_diff : DifferentiableOn ℂ g U := by
    have hpow : DifferentiableOn ℂ (fun z : ℂ => (-Complex.I * z) ^ ((r : ℂ) / 2)) U := by
      intro z hz
      have hz_im : 0 < z.im := hz
      have hre : 0 < (-Complex.I * z).re := by simp [hz_im]
      have hslit : (-Complex.I * z) ∈ Complex.slitPlane := Or.inl hre
      exact ((differentiableAt_const (-Complex.I)).mul differentiableAt_id).cpow_const
        hslit |>.differentiableWithinAt
    exact ((hpow.mul (differentiableOn_const C)).mul (differentiableOn_complexLatticeThetaFun L'))
  have hf_an : AnalyticOnNhd ℂ f U := hf_diff.analyticOnNhd hU_open
  have hg_an : AnalyticOnNhd ℂ g U := hg_diff.analyticOnNhd hU_open
  have hI_mem : Complex.I ∈ U := by change 0 < Complex.I.im; simp
  have hfreq : ∃ᶠ z in nhdsWithin Complex.I {Complex.I}ᶜ, f z = g z := by
    rw [Filter.frequently_iff]
    intro s hs
    rw [Metric.mem_nhdsWithin_iff] at hs
    obtain ⟨ε, hε, hball⟩ := hs
    let δ : ℝ := min (ε / 2) (1 / 2)
    have hδ_pos : 0 < δ := lt_min (half_pos hε) (by norm_num)
    have hδ_lt : δ < ε := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hε)
    have ht_pos : 0 < 1 + δ := by linarith
    let z : ℂ := Complex.I * ((1 + δ : ℝ) : ℂ)
    have hz_ne : z ≠ Complex.I := by
      intro h
      have him := congrArg Complex.im h
      simp [z] at him
      linarith
    have hz_dist : dist z Complex.I < ε := by
      rw [Complex.dist_eq]
      have hsub : z - Complex.I = Complex.I * (δ : ℂ) := by
        dsimp only [z]; push_cast; ring
      rw [hsub, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
        Real.norm_of_nonneg hδ_pos.le]
      exact hδ_lt
    refine ⟨z, hball ⟨hz_dist, hz_ne⟩, ?_⟩
    dsimp only [f, g, z]
    have hinv_eq : (-(Complex.I * ((1 + δ : ℝ) : ℂ)))⁻¹ =
        Complex.I * (((1 + δ)⁻¹ : ℝ) : ℂ) := by
      rw [Complex.ofReal_inv, inv_neg, mul_inv, Complex.inv_I]
      ring
    have hmulI : -Complex.I * (Complex.I * ((1 + δ : ℝ) : ℂ)) = ((1 + δ : ℝ) : ℂ) := by
      linear_combination -((1 + δ : ℝ) : ℂ) * Complex.I_mul_I
    rw [hinv_eq, hmulI, complexLatticeThetaFun_imaginary_axis,
      complexLatticeThetaFun_imaginary_axis, hreal (1 + δ)⁻¹ (inv_pos.mpr ht_pos), inv_inv]
    congr 2
    have h1 : (((1 + δ)⁻¹ : ℝ) : ℂ) = ((1 + δ : ℝ) : ℂ)⁻¹ := Complex.ofReal_inv _
    rw [h1]
    have harg : (((1 + δ : ℝ) : ℂ)).arg ≠ Real.pi := by
      rw [Complex.arg_ofReal_of_nonneg ht_pos.le]
      exact Real.pi_pos.ne
    rw [Complex.inv_cpow_eq_ite, if_neg harg, ← Complex.cpow_neg, neg_neg]
  have heqOn : Set.EqOn f g U :=
    hf_an.eqOn_of_preconnected_of_frequently_eq hg_an hU_conn hI_mem hfreq
  have hτU : (τ : ℂ) ∈ U := τ.im_pos
  have hres := heqOn hτU
  dsimp only [f, g] at hres
  unfold complexLatticeTheta
  rwa [UpperHalfPlane.modular_S_smul]

end OrthogonalComplexTheta

/-! ### Part 2B: `SL₂(ℤ)` Generation by `S, T` & General Weight-`4k` Slash-Invariance -/

lemma mul_S_bottom_row (g : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    (g * ModularGroup.S : Matrix.SpecialLinearGroup (Fin 2) ℤ) 1 0 = g 1 1 ∧
    (g * ModularGroup.S : Matrix.SpecialLinearGroup (Fin 2) ℤ) 1 1 = -g 1 0 := by
  constructor <;>
    simp [Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_S, Matrix.mul_apply, Fin.sum_univ_two]

lemma mul_T_zpow_bottom_row (g : Matrix.SpecialLinearGroup (Fin 2) ℤ) (n : ℤ) :
    (g * ModularGroup.T ^ n : Matrix.SpecialLinearGroup (Fin 2) ℤ) 1 0 = g 1 0 ∧
    (g * ModularGroup.T ^ n : Matrix.SpecialLinearGroup (Fin 2) ℤ) 1 1 = g 1 0 * n + g 1 1 := by
  constructor <;>
    simp [Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_T_zpow, Matrix.mul_apply,
      Fin.sum_univ_two, mul_comm]

/-- **`SL₂(ℤ)` is Generated by `S` and `T`** (elementary Euclidean descent on `|g 1 0|`):
`Subgroup.closure {ModularGroup.S, ModularGroup.T} = ⊤`. -/
theorem SL2Z_closure_S_T_eq_top :
    Subgroup.closure ({ModularGroup.S, ModularGroup.T} :
      Set (Matrix.SpecialLinearGroup (Fin 2) ℤ)) = ⊤ := by
  let H := Subgroup.closure ({ModularGroup.S, ModularGroup.T} :
    Set (Matrix.SpecialLinearGroup (Fin 2) ℤ))
  have hS : ModularGroup.S ∈ H := Subgroup.subset_closure (by simp)
  have hT : ModularGroup.T ∈ H := Subgroup.subset_closure (by simp)
  have hneg1 : (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) ∈ H := by
    have hSS : ModularGroup.S * ModularGroup.S = -1 := Subtype.ext ModularGroup.S_mul_S_eq
    rw [← hSS]
    exact H.mul_mem hS hS
  have hbase : ∀ g : Matrix.SpecialLinearGroup (Fin 2) ℤ, g 1 0 = 0 → g ∈ H := by
    intro g hg0
    have hdet : g 0 0 * g 1 1 = 1 := by
      have hd := g.2
      rw [Matrix.det_fin_two, hg0, mul_zero, sub_zero] at hd
      exact hd
    rcases Int.mul_eq_one_iff_eq_one_or_neg_one.mp hdet with ⟨ha, hd⟩ | ⟨ha, hd⟩
    · have hgT : g = ModularGroup.T ^ (g 0 1) := by
        apply Subtype.ext; ext i j
        fin_cases i <;> fin_cases j <;> simp [ModularGroup.coe_T_zpow, ha, hd, hg0]
      rw [hgT]; exact H.zpow_mem hT (g 0 1)
    · have hgT : g = (-1) * ModularGroup.T ^ (-g 0 1) := by
        apply Subtype.ext; ext i j
        fin_cases i <;> fin_cases j <;>
          simp [ModularGroup.coe_T_zpow, ha, hd, hg0]
      rw [hgT]; exact H.mul_mem hneg1 (H.zpow_mem hT (-g 0 1))
  have hmain : ∀ m : ℕ, ∀ g : Matrix.SpecialLinearGroup (Fin 2) ℤ, (g 1 0).natAbs = m → g ∈ H := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro g hgm
      by_cases hm0 : m = 0
      · exact hbase g (Int.natAbs_eq_zero.mp (hgm.trans hm0))
      · have hc_ne : g 1 0 ≠ 0 := fun h => hm0 (by rw [← hgm, h]; rfl)
        let q : ℤ := -(g 1 1 / g 1 0)
        let g₁ := g * ModularGroup.T ^ q
        let g₂ := g₁ * ModularGroup.S
        have hg₁_11 : g₁ 1 1 = g 1 1 % g 1 0 := by
          rw [(mul_T_zpow_bottom_row g q).2]
          dsimp only [q]
          have hdiv := Int.emod_add_mul_ediv (g 1 1) (g 1 0)
          linarith
        have hg₂_10 : g₂ 1 0 = g 1 1 % g 1 0 := by
          rw [(mul_S_bottom_row g₁).1, hg₁_11]
        have hlt : (g₂ 1 0).natAbs < m := by
          rw [hg₂_10, ← hgm]
          have hnn : 0 ≤ g 1 1 % g 1 0 := Int.emod_nonneg (g 1 1) hc_ne
          have hlt' : g 1 1 % g 1 0 < ((g 1 0).natAbs : ℤ) := Int.emod_lt (g 1 1) hc_ne
          omega
        have hg₂_mem : g₂ ∈ H := ih (g₂ 1 0).natAbs hlt g₂ rfl
        have hfactor : g = g₂ * ModularGroup.S⁻¹ * (ModularGroup.T ^ q)⁻¹ := by
          dsimp only [g₂, g₁]
          group
        rw [hfactor]
        exact H.mul_mem (H.mul_mem hg₂_mem (H.inv_mem hS)) (H.inv_mem (H.zpow_mem hT q))
  rw [eq_top_iff]
  intro g _
  exact hmain (g 1 0).natAbs g rfl

/-- Canonical embedding `SL₂(ℤ) →* GL₂(ℝ)` matching Mathlib's `ModularForm.slash_def`. -/
def sl2ZToGL2R : Matrix.SpecialLinearGroup (Fin 2) ℤ →* GL (Fin 2) ℝ :=
  (Matrix.SpecialLinearGroup.toGL (n := Fin 2) (R := ℝ)).comp
    (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ))

/-- Exact evaluation of Mathlib's `SlashAction.map k (sl2ZToGL2R γ) f τ` for `γ ∈ SL₂(ℤ)`. -/
theorem slash_sl2Z_apply (k : ℤ) (f : UpperHalfPlane → ℂ)
    (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (τ : UpperHalfPlane) :
    SlashAction.map k (sl2ZToGL2R γ) f τ =
      f (γ • τ) * (UpperHalfPlane.denom (sl2ZToGL2R γ) (τ : ℂ)) ^ (-k) := by
  rw [ModularForm.slash_apply]
  have hdet : ((sl2ZToGL2R γ).det : ℝ) = 1 := by simp [sl2ZToGL2R]
  have hσ : UpperHalfPlane.σ (sl2ZToGL2R γ) = ContinuousAlgEquiv.refl ℝ ℂ := by
    simp [UpperHalfPlane.σ, hdet]
  rw [hσ, ContinuousAlgEquiv.refl_apply, hdet, abs_one, Complex.ofReal_one, one_zpow, mul_one]
  rfl

/-- Exact `S`-slash action formula: `(f |_k S)(τ) = f(S • τ) * τ^(-k)`. -/
theorem slash_S_apply (k : ℤ) (f : UpperHalfPlane → ℂ) (τ : UpperHalfPlane) :
    SlashAction.map k (sl2ZToGL2R ModularGroup.S) f τ = f (ModularGroup.S • τ) * (τ : ℂ) ^ (-k) := by
  rw [slash_sl2Z_apply]
  congr 2
  exact ModularGroup.denom_S τ

/-- Exact `T`-slash action formula: `(f |_k T)(τ) = f(T • τ)`. -/
theorem slash_T_apply (k : ℤ) (f : UpperHalfPlane → ℂ) (τ : UpperHalfPlane) :
    SlashAction.map k (sl2ZToGL2R ModularGroup.T) f τ = f (ModularGroup.T • τ) := by
  rw [slash_sl2Z_apply]
  have hdenom : UpperHalfPlane.denom (sl2ZToGL2R ModularGroup.T) (τ : ℂ) = 1 := by
    change UpperHalfPlane.denom
      (Matrix.SpecialLinearGroup.toGL ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) ModularGroup.T)) (τ : ℂ) = 1
    rw [ModularGroup.denom_apply]
    simp [ModularGroup.coe_T]
  rw [hdenom, one_zpow, mul_one]

/-- **Master `SL₂(ℤ)` Weight-`k` Slash-Invariance Criterion from Generators `S` and `T`**:
if `f : UpperHalfPlane → ℂ` satisfies `f(S • τ) = τ^k * f(τ)` and `f(T • τ) = f(τ)` for all `τ`,
then `f` is weight-`k` slash-invariant under EVERY `γ ∈ SL₂(ℤ)`! -/
theorem slash_SL2Z_invariant_of_S_T (k : ℤ) (f : UpperHalfPlane → ℂ)
    (hS : ∀ τ : UpperHalfPlane, f (ModularGroup.S • τ) = (τ : ℂ) ^ k * f τ)
    (hT : ∀ τ : UpperHalfPlane, f (ModularGroup.T • τ) = f τ)
    (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    SlashAction.map k (sl2ZToGL2R γ) f = f := by
  have hS_slash : SlashAction.map k (sl2ZToGL2R ModularGroup.S) f = f := by
    ext τ
    rw [slash_S_apply, hS τ, mul_comm ((τ : ℂ) ^ k), mul_assoc, ← zpow_add₀ τ.ne_zero,
      add_neg_cancel, zpow_zero, mul_one]
  have hT_slash : SlashAction.map k (sl2ZToGL2R ModularGroup.T) f = f := by
    ext τ
    rw [slash_T_apply, hT τ]
  let Stab : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ) :=
    { carrier := {g | SlashAction.map k (sl2ZToGL2R g) f = f}
      one_mem' := by
        change SlashAction.map k (sl2ZToGL2R 1) f = f
        rw [map_one, SlashAction.slash_one]
      mul_mem' := by
        intro a b ha hb
        change SlashAction.map k (sl2ZToGL2R (a * b)) f = f
        rw [map_mul, SlashAction.slash_mul, ha, hb]
      inv_mem' := by
        intro a ha
        change SlashAction.map k (sl2ZToGL2R a⁻¹) f = f
        calc SlashAction.map k (sl2ZToGL2R a⁻¹) f
            = SlashAction.map k (sl2ZToGL2R a⁻¹) (SlashAction.map k (sl2ZToGL2R a) f) := by
                rw [ha]
          _ = SlashAction.map k (sl2ZToGL2R (a * a⁻¹)) f := by
                rw [map_mul, SlashAction.slash_mul]
          _ = f := by rw [mul_inv_cancel, map_one, SlashAction.slash_one] }
  have htop : (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) ≤ Stab := by
    rw [← SL2Z_closure_S_T_eq_top, Subgroup.closure_le]
    rintro g (rfl | rfl)
    · exact hS_slash
    · exact hT_slash
  exact htop (Subgroup.mem_top γ)

/-- Algebraic simplification: for every `k : ℕ` and `τ : UpperHalfPlane`,
`(-I * τ) ^ ((8 * k : ℕ) / 2 : ℂ) = τ ^ (4 * k)`. -/
lemma neg_I_mul_cpow_four_mul (k : ℕ) (τ : UpperHalfPlane) :
    (-Complex.I * (τ : ℂ)) ^ (((8 * k : ℕ) : ℂ) / 2) = (τ : ℂ) ^ (4 * k) := by
  have hexp : (((8 * k : ℕ) : ℂ) / 2) = ((4 * k : ℕ) : ℂ) := by
    push_cast; ring
  rw [hexp, Complex.cpow_natCast, mul_pow]
  have hI4 : (-Complex.I) ^ (4 * k) = 1 := by
    rw [pow_mul]
    have h4 : (-Complex.I) ^ 4 = 1 := by
      calc (-Complex.I) ^ 4 = ((-Complex.I) ^ 2) ^ 2 := by ring
        _ = (-1 : ℂ) ^ 2 := by rw [neg_sq, Complex.I_sq]
        _ = 1 := by norm_num
    rw [h4, one_pow]
  rw [hI4, one_mul]

/-- **General Weight-`4k` `SL₂(ℤ)` Slash-Invariance for Any Even Unimodular Rank-`8k` Lattice**:
if `L` is an even lattice of rank `8k` satisfying `Θ_L(S • τ) = (-i τ)^{4k} Θ_L(τ)`, then
`SlashAction.map (4 * k : ℤ) (sl2ZToGL2R γ) (complexLatticeTheta L) = complexLatticeTheta L`
for EVERY `γ ∈ SL₂(ℤ)`! -/
theorem even_unimodular_weight_4k_slash_SL2Z
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) (k : ℕ) (hEven : IsEvenLattice L)
    (hS_theta : ∀ τ : UpperHalfPlane,
      complexLatticeTheta L (ModularGroup.S • τ) =
        (-Complex.I * (τ : ℂ)) ^ (((8 * k : ℕ) : ℂ) / 2) * complexLatticeTheta L τ)
    (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    SlashAction.map ((4 * k : ℕ) : ℤ) (sl2ZToGL2R γ) (complexLatticeTheta L) =
      complexLatticeTheta L := by
  refine slash_SL2Z_invariant_of_S_T ((4 * k : ℕ) : ℤ) (complexLatticeTheta L) ?_ ?_ γ
  · intro τ
    rw [hS_theta τ, neg_I_mul_cpow_four_mul, zpow_natCast]
  · intro τ
    exact complexLatticeTheta_T_smul_of_even hEven τ

/-- **Orthogonal Unimodular Lattice `ℤ^{8k}` Theorem** (invariant under `S` of weight `4k` and `T²`):
for any orthonormal `ℤ`-basis `b : Basis (Fin (8 * k)) ℤ L` (`‖b_i‖ = 1`),
`Θ_L(S • τ) = τ^{4k} Θ_L(τ)` and `Θ_L(T² • τ) = Θ_L(τ)`! -/
theorem complexLatticeTheta_orthonormal_8k_S_and_T2
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {L : Submodule ℤ E} [DiscreteTopology L] {k : ℕ}
    (b : Basis (Fin (8 * k)) ℤ L) (hb : IsOrthogonalBasis b)
    (hunit : ∀ i, ‖(b i : E)‖ = 1) (τ : UpperHalfPlane) :
    complexLatticeTheta L (ModularGroup.S • τ) = (τ : ℂ) ^ (4 * k) * complexLatticeTheta L τ ∧
      complexLatticeTheta L ((ModularGroup.T ^ (2 : ℤ)) • τ) = complexLatticeTheta L τ := by
  have hcov : covol L = 1 := by
    rw [covol_of_orthogonalBasis b hb]
    simp [hunit]
  have hdual : dualLattice L = L := by
    rw [dualLattice_eq_span_dualVec b hb]
    have hdv : dualVec b = fun i => (b i : E) := by
      funext i; simp [dualVec, hunit i]
    rw [hdv]
    have : Set.range (fun i => (b i : E)) = L.subtype '' Set.range b := Set.range_comp _ _
    rw [this, ← Submodule.map_span, b.span_eq, Submodule.map_subtype_top]
  have hInt : IsIntegralLattice L := by
    intro v hv
    let x : L := ⟨v, hv⟩
    have hx : v = ∑ i : Fin (8 * k), b.repr x i • (b i : E) := by
      have h1 := congrArg (fun y : L => (y : E)) (b.sum_repr x).symm
      simpa only [Submodule.coe_sum, Submodule.coe_smul] using h1
    refine ⟨∑ i : Fin (8 * k), (b.repr x i) ^ 2, ?_⟩
    rw [hx, norm_sq_sum_orthogonalBasis b hb]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hunit i, one_mul]
  constructor
  · have hS := complexLatticeTheta_S_smul_orthogonal b hb τ
    rw [hcov, hdual, neg_I_mul_cpow_four_mul] at hS
    simpa using hS
  · exact complexLatticeTheta_T_sq_smul_of_integral hInt τ

/-! ### Part 2C: Concrete Even Unimodular `E₈` Lattice & `E₈^k` Weight-`4k` Modular Forms for `SL₂(ℤ)` -/

/-- Auxiliary Jacobi theta functions `θ₃, θ₄, θ₂` on `ℂ`:
- `theta3 τ = ∑'_{n ∈ ℤ} exp(π i n² τ) = jacobiTheta τ`
- `theta4 τ = ∑'_{n ∈ ℤ} (-1)^n exp(π i n² τ) = jacobiTheta₂ (1/2) τ`
- `theta2 τ = ∑'_{n ∈ ℤ} exp(π i (n + 1/2)² τ)` -/
def theta3 (τ : ℂ) : ℂ := ∑' n : ℤ, Complex.exp ((Real.pi : ℂ) * Complex.I * (n : ℂ) ^ 2 * τ)
def theta4 (τ : ℂ) : ℂ :=
  ∑' n : ℤ, (-1 : ℂ) ^ n * Complex.exp ((Real.pi : ℂ) * Complex.I * (n : ℂ) ^ 2 * τ)
def theta2 (τ : ℂ) : ℂ :=
  ∑' n : ℤ, Complex.exp ((Real.pi : ℂ) * Complex.I * ((n : ℂ) + 1 / 2) ^ 2 * τ)

lemma theta3_eq_jacobiTheta (τ : ℂ) : theta3 τ = jacobiTheta τ := rfl

lemma theta4_eq_jacobiTheta₂ (τ : ℂ) : theta4 τ = jacobiTheta₂ (1 / 2) τ := by
  unfold theta4 jacobiTheta₂ jacobiTheta₂_term
  refine tsum_congr fun n => ?_
  rw [Complex.exp_add]
  congr 1
  have h1 : 2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (1 / 2) =
      (n : ℂ) * ((Real.pi : ℂ) * Complex.I) := by ring
  rw [h1, Complex.exp_int_mul, Complex.exp_pi_mul_I]

lemma theta3_S_smul (τ : UpperHalfPlane) :
    theta3 ((ModularGroup.S • τ : UpperHalfPlane) : ℂ) =
      (-Complex.I * (τ : ℂ)) ^ ((1 : ℂ) / 2) * theta3 (τ : ℂ) := by
  rw [theta3_eq_jacobiTheta, theta3_eq_jacobiTheta]
  exact jacobiTheta_S_smul τ

lemma neg_I_mul_neg_inv_eq_inv (τ : UpperHalfPlane) :
    -Complex.I * (-1 / (τ : ℂ)) = (-Complex.I * (τ : ℂ))⁻¹ := by
  rw [mul_inv, inv_neg, Complex.inv_I]
  field_simp [τ.ne_zero]

lemma theta4_S_smul (τ : UpperHalfPlane) :
    theta4 ((ModularGroup.S • τ : UpperHalfPlane) : ℂ) =
      (-Complex.I * (τ : ℂ)) ^ ((1 : ℂ) / 2) * theta2 (τ : ℂ) := by
  rw [theta4_eq_jacobiTheta₂]
  have hS : ((ModularGroup.S • τ : UpperHalfPlane) : ℂ) = -1 / (τ : ℂ) := by
    rw [UpperHalfPlane.modular_S_smul]
    field_simp [τ.ne_zero]
  rw [hS]
  have hfe := jacobiTheta₂_functional_equation (1 / 2 : ℂ) (-1 / (τ : ℂ))
  have hτ_ne : (τ : ℂ) ≠ 0 := τ.ne_zero
  have hinv_inv : -1 / (-1 / (τ : ℂ)) = (τ : ℂ) := by field_simp [hτ_ne]
  have hz_div : (1 / 2 : ℂ) / (-1 / (τ : ℂ)) = -(τ : ℂ) / 2 := by field_simp [hτ_ne]
  have hz_re : 0 < (-Complex.I * (τ : ℂ)).re := by simp [τ.im_pos]
  have harg_z : (-Complex.I * (τ : ℂ)).arg ≠ Real.pi := arg_ne_pi_of_re_pos hz_re
  have hpow_inv : 1 / (-Complex.I * (-1 / (τ : ℂ))) ^ ((1 : ℂ) / 2) =
      (-Complex.I * (τ : ℂ)) ^ ((1 : ℂ) / 2) := by
    rw [neg_I_mul_neg_inv_eq_inv τ, Complex.inv_cpow_eq_ite, if_neg harg_z, one_div, inv_inv]
  rw [hfe, hinv_inv, hz_div, hpow_inv, mul_assoc]
  congr 1
  unfold jacobiTheta₂ jacobiTheta₂_term theta2
  rw [← tsum_mul_left]
  rw [← (Equiv.neg ℤ).tsum_eq]
  refine tsum_congr fun n => ?_
  rw [← Complex.exp_add]
  congr 1
  simp only [Equiv.neg_apply, Int.cast_neg]
  field_simp [hτ_ne]
  ring

lemma theta2_S_smul (τ : UpperHalfPlane) :
    theta2 ((ModularGroup.S • τ : UpperHalfPlane) : ℂ) =
      (-Complex.I * (τ : ℂ)) ^ ((1 : ℂ) / 2) * theta4 (τ : ℂ) := by
  have h := theta4_S_smul (ModularGroup.S • τ)
  have hSS_mat : ModularGroup.S * ModularGroup.S = -1 := Subtype.ext ModularGroup.S_mul_S_eq
  have hSS : ModularGroup.S • (ModularGroup.S • τ) = τ := by
    rw [← mul_smul, hSS_mat, ModularGroup.SL_neg_smul, one_smul]
  rw [hSS] at h
  have hS : ((ModularGroup.S • τ : UpperHalfPlane) : ℂ) = -1 / (τ : ℂ) := by
    rw [UpperHalfPlane.modular_S_smul]; field_simp [τ.ne_zero]
  have hz_re : 0 < (-Complex.I * (τ : ℂ)).re := by simp [τ.im_pos]
  have harg_z : (-Complex.I * (τ : ℂ)).arg ≠ Real.pi := arg_ne_pi_of_re_pos hz_re
  have hpow : (-Complex.I * ((ModularGroup.S • τ : UpperHalfPlane) : ℂ)) ^ ((1 : ℂ) / 2) =
      ((-Complex.I * (τ : ℂ)) ^ ((1 : ℂ) / 2))⁻¹ := by
    rw [hS, neg_I_mul_neg_inv_eq_inv τ, Complex.inv_cpow_eq_ite, if_neg harg_z]
  rw [hpow] at h
  have hne : (-Complex.I * (τ : ℂ)) ^ ((1 : ℂ) / 2) ≠ 0 := by
    have hz_ne : -Complex.I * (τ : ℂ) ≠ 0 := fun hc => by rw [hc] at hz_re; simp at hz_re
    exact Complex.cpow_ne_zero_iff.mpr (Or.inl hz_ne)
  calc theta2 ((ModularGroup.S • τ : UpperHalfPlane) : ℂ)
      = (-Complex.I * (τ : ℂ)) ^ ((1 : ℂ) / 2) *
          (((-Complex.I * (τ : ℂ)) ^ ((1 : ℂ) / 2))⁻¹ *
            theta2 ((ModularGroup.S • τ : UpperHalfPlane) : ℂ)) := by
          rw [← mul_assoc, mul_inv_cancel₀ hne, one_mul]
    _ = (-Complex.I * (τ : ℂ)) ^ ((1 : ℂ) / 2) * theta4 (τ : ℂ) := by rw [← h]

lemma summable_norm_theta3 {τ : ℂ} (hτ : 0 < τ.im) :
    Summable (fun n : ℤ => ‖Complex.exp ((Real.pi : ℂ) * Complex.I * (n : ℂ) ^ 2 * τ)‖) := by
  have h := summable_norm_complexTheta1D (a := 1) one_pos hτ
  refine h.congr fun n => ?_
  congr 2; push_cast; ring

lemma summable_norm_theta4 {τ : ℂ} (hτ : 0 < τ.im) :
    Summable (fun n : ℤ =>
      ‖(-1 : ℂ) ^ n * Complex.exp ((Real.pi : ℂ) * Complex.I * (n : ℂ) ^ 2 * τ)‖) := by
  refine (summable_norm_theta3 hτ).congr fun n => ?_
  rw [norm_mul, norm_zpow, norm_neg, norm_one, one_zpow, one_mul]

lemma summable_norm_theta2 {τ : ℂ} (hτ : 0 < τ.im) :
    Summable (fun n : ℤ =>
      ‖Complex.exp ((Real.pi : ℂ) * Complex.I * ((n : ℂ) + 1 / 2) ^ 2 * τ)‖) := by
  have h := summable_of_sum_le (c := 6 + 4 / Real.sqrt τ.im)
    (fun _ : ℤ => (Real.exp_pos _).le)
    (fun s => sum_int_exp_shifted_le hτ (1 / 2) s)
  refine h.congr fun n => ?_
  rw [Complex.norm_exp]
  congr 1
  have hsq : (((n : ℂ) + 1 / 2) ^ 2) = ((((n : ℝ) + 1 / 2) ^ 2 : ℝ) : ℂ) := by
    push_cast; ring
  rw [hsq]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]
  ring

lemma tsum_neg_one_pow_theta2_eq_zero {τ : ℂ} :
    (∑' n : ℤ, (-1 : ℂ) ^ n *
      Complex.exp ((Real.pi : ℂ) * Complex.I * ((n : ℂ) + 1 / 2) ^ 2 * τ)) = 0 := by
  let f : ℤ → ℂ := fun n =>
    (-1 : ℂ) ^ n * Complex.exp ((Real.pi : ℂ) * Complex.I * ((n : ℂ) + 1 / 2) ^ 2 * τ)
  let e : ℤ ≃ ℤ :=
    { toFun := fun n => -n - 1
      invFun := fun n => -n - 1
      left_inv := fun n => by ring
      right_inv := fun n => by ring }
  have hanti : ∀ n : ℤ, f (e n) = -f n := by
    intro n
    change (-1 : ℂ) ^ (-n - 1) *
        Complex.exp ((Real.pi : ℂ) * Complex.I * (((-n - 1 : ℤ) : ℂ) + 1 / 2) ^ 2 * τ) =
      -((-1 : ℂ) ^ n * Complex.exp ((Real.pi : ℂ) * Complex.I * ((n : ℂ) + 1 / 2) ^ 2 * τ))
    have hsq : (((-n - 1 : ℤ) : ℂ) + 1 / 2) ^ 2 = ((n : ℂ) + 1 / 2) ^ 2 := by
      push_cast; ring
    have hpow : (-1 : ℂ) ^ (-n - 1) = -((-1 : ℂ) ^ n) := by
      rw [show (-n - 1 : ℤ) = (n + 2 * (-n)) + (-1) by ring,
        zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0),
        zpow_mul]
      norm_num
    rw [hsq, hpow]; ring
  have h1 : (∑' n : ℤ, f n) = ∑' n : ℤ, f (e n) := (e.tsum_eq f).symm
  have h2 : (∑' n : ℤ, f (e n)) = -(∑' n : ℤ, f n) := by
    simp_rw [hanti, tsum_neg]
  have h3 : (2 : ℂ) * (∑' n : ℤ, f n) = 0 := by
    linear_combination h1.trans h2
  exact (mul_eq_zero.mp h3).resolve_left (by norm_num)

/-- **The Concrete Even Unimodular `E₈` Lattice** inside `ℝ⁸ = EuclideanSpace ℝ (Fin 8)`:
`E₈ = { v ∈ ℝ⁸ | (∀ i, 2 v_i ∈ ℤ) ∧ (∀ i j, v_i - v_j ∈ ℤ) ∧ (∑ i, v_i ∈ 2ℤ) }`. -/
def E8Lattice : Submodule ℤ (EuclideanSpace ℝ (Fin 8)) where
  carrier := { v | (∀ i : Fin 8, ∃ n : ℤ, 2 * v i = (n : ℝ)) ∧
    (∀ i j : Fin 8, ∃ m : ℤ, v i - v j = (m : ℝ)) ∧
    (∃ s : ℤ, ∑ i : Fin 8, v i = 2 * (s : ℝ)) }
  zero_mem' := ⟨fun _ => ⟨0, by simp⟩, fun _ _ => ⟨0, by simp⟩, ⟨0, by simp⟩⟩
  add_mem' := by
    rintro v w ⟨hv1, hv2, ⟨sv, hsv⟩⟩ ⟨hw1, hw2, ⟨sw, hsw⟩⟩
    refine ⟨fun i => ?_, fun i j => ?_, ⟨sv + sw, ?_⟩⟩
    · obtain ⟨nv, hnv⟩ := hv1 i
      obtain ⟨nw, hnw⟩ := hw1 i
      exact ⟨nv + nw, by simp [PiLp.add_apply]; linarith⟩
    · obtain ⟨mv, hmv⟩ := hv2 i j
      obtain ⟨mw, hmw⟩ := hw2 i j
      exact ⟨mv + mw, by simp [PiLp.add_apply]; linarith⟩
    · simp only [PiLp.add_apply, Finset.sum_add_distrib, hsv, hsw]
      push_cast; ring
  smul_mem' := by
    rintro k v ⟨hv1, hv2, ⟨sv, hsv⟩⟩
    refine ⟨fun i => ?_, fun i j => ?_, ⟨k * sv, ?_⟩⟩
    · obtain ⟨nv, hnv⟩ := hv1 i
      refine ⟨k * nv, ?_⟩
      simp only [PiLp.smul_apply, zsmul_eq_mul, Int.cast_mul]
      linear_combination (k : ℝ) * hnv
    · obtain ⟨mv, hmv⟩ := hv2 i j
      refine ⟨k * mv, ?_⟩
      simp only [PiLp.smul_apply, zsmul_eq_mul, Int.cast_mul]
      linear_combination (k : ℝ) * hmv
    · simp only [PiLp.smul_apply, zsmul_eq_mul, ← Finset.mul_sum, hsv]
      push_cast; ring

/-- Dichotomy for elements of `E₈`: every `v ∈ E₈` is either all-integer with even sum,
or all-half-integer with even sum. -/
lemma mem_E8Lattice_iff (v : EuclideanSpace ℝ (Fin 8)) :
    v ∈ E8Lattice ↔
      (∃ c : Fin 8 → ℤ, (∀ i, v i = (c i : ℝ)) ∧ Even (∑ i : Fin 8, c i)) ∨
      (∃ c : Fin 8 → ℤ, (∀ i, v i = (c i : ℝ) + 1 / 2) ∧ Even (∑ i : Fin 8, c i)) := by
  constructor
  · rintro ⟨h1, h2, ⟨s, hs⟩⟩
    obtain ⟨n0, hn0⟩ := h1 0
    rcases Int.even_or_odd n0 with ⟨k0, hk0⟩ | ⟨k0, hk0⟩
    · left
      have hv0 : v 0 = (k0 : ℝ) := by
        have : (n0 : ℝ) = 2 * (k0 : ℝ) := by exact_mod_cast (by omega : n0 = 2 * k0)
        linarith
      let c : Fin 8 → ℤ := fun i => k0 + Classical.choose (h2 i 0)
      have hc : ∀ i, v i = (c i : ℝ) := fun i => by
        have hspec := Classical.choose_spec (h2 i 0)
        dsimp only [c]; push_cast; linarith
      refine ⟨c, hc, ⟨s, ?_⟩⟩
      have hsum : ((∑ i : Fin 8, c i : ℤ) : ℝ) = ((2 * s : ℤ) : ℝ) := by
        push_cast; simpa [hc] using hs
      have hsumZ : ∑ i : Fin 8, c i = 2 * s := by exact_mod_cast hsum
      omega
    · right
      have hv0 : v 0 = (k0 : ℝ) + 1 / 2 := by
        have : (n0 : ℝ) = 2 * (k0 : ℝ) + 1 := by exact_mod_cast (by omega : n0 = 2 * k0 + 1)
        linarith
      let c : Fin 8 → ℤ := fun i => k0 + Classical.choose (h2 i 0)
      have hc : ∀ i, v i = (c i : ℝ) + 1 / 2 := fun i => by
        have hspec := Classical.choose_spec (h2 i 0)
        dsimp only [c]; push_cast; linarith
      refine ⟨c, hc, ⟨s - 2, ?_⟩⟩
      have hsum : ((∑ i : Fin 8, c i : ℤ) : ℝ) + 4 = ((2 * s : ℤ) : ℝ) := by
        have h1' : ∑ i : Fin 8, ((c i : ℝ) + 1 / 2) = (∑ i : Fin 8, (c i : ℝ)) + 4 := by
          rw [Finset.sum_add_distrib]
          norm_num
        push_cast; linarith [h1', show ∑ i : Fin 8, v i = ∑ i : Fin 8, ((c i : ℝ) + 1 / 2) from
          Finset.sum_congr rfl fun i _ => hc i]
      have hsumZ : ∑ i : Fin 8, c i + 4 = 2 * s := by exact_mod_cast hsum
      omega
  · rintro (⟨c, hc, ⟨s, hs⟩⟩ | ⟨c, hc, ⟨s, hs⟩⟩)
    · refine ⟨fun i => ⟨2 * c i, by rw [hc i]; push_cast; ring⟩,
        fun i j => ⟨c i - c j, by rw [hc i, hc j]; push_cast; ring⟩,
        ⟨s, ?_⟩⟩
      simp_rw [hc]
      have : ∑ i : Fin 8, c i = 2 * s := by omega
      exact_mod_cast this
    · refine ⟨fun i => ⟨2 * c i + 1, by rw [hc i]; push_cast; ring⟩,
        fun i j => ⟨c i - c j, by rw [hc i, hc j]; push_cast; ring⟩,
        ⟨s + 2, ?_⟩⟩
      simp_rw [hc, Finset.sum_add_distrib]
      have hsum : (∑ i : Fin 8, (c i : ℝ)) = 2 * (s : ℝ) := by
        exact_mod_cast (by omega : ∑ i : Fin 8, c i = 2 * s)
      rw [hsum]; push_cast; ring

/-- `E₈` is discrete (`DiscreteTopology E8Lattice`). -/
instance discreteTopology_E8Lattice : DiscreteTopology E8Lattice := by
  let f : E8Lattice → (Fin 8 → ℤ) := fun v i => Classical.choose (v.2.1 i)
  have hf_val : ∀ v : E8Lattice, ∀ i : Fin 8,
      ((f v i : ℤ) : ℝ) = 2 * (v : EuclideanSpace ℝ (Fin 8)) i :=
    fun v i => (Classical.choose_spec (v.2.1 i)).symm
  have hf_inj : Function.Injective f := by
    intro v w h
    apply Subtype.ext
    ext i
    have hi : ((f v i : ℤ) : ℝ) = ((f w i : ℤ) : ℝ) := by rw [congrFun h i]
    rw [hf_val, hf_val] at hi
    linarith
  have hf_cont : Continuous f := by
    refine continuous_pi fun i => ?_
    have hR : Continuous (fun v : E8Lattice => ((f v i : ℤ) : ℝ)) := by
      simp_rw [hf_val]
      exact continuous_const.mul ((EuclideanSpace.proj i).continuous.comp continuous_subtype_val)
    exact Int.isClosedEmbedding_coe_real.isInducing.continuous_iff.mpr hR
  exact DiscreteTopology.of_continuous_injective hf_cont hf_inj

/-- **`E₈` is an Even Lattice**: `∀ v ∈ E₈, ∃ m : ℤ, ‖v‖² = 2 m`. -/
theorem isEvenLattice_E8Lattice : IsEvenLattice E8Lattice := by
  intro v hv
  have hnorm : ‖v‖ ^ 2 = ∑ i : Fin 8, (v i) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    refine Finset.sum_congr rfl fun i _ => by simp [Real.norm_eq_abs]
  rw [hnorm]
  rcases (mem_E8Lattice_iff v).mp hv with ⟨c, hc, ⟨s, hs⟩⟩ | ⟨c, hc, ⟨s, hs⟩⟩
  · have heven : Even (∑ i : Fin 8, (c i) ^ 2) := by
      have hdiff : Even ((∑ i : Fin 8, (c i) ^ 2) - (∑ i : Fin 8, c i)) := by
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_induction (fun i : Fin 8 => c i ^ 2 - c i) Even
          (fun _ _ => Even.add) Even.zero fun i _ => ?_
        rcases Int.even_or_odd (c i) with ⟨k, hk⟩ | ⟨k, hk⟩
        · exact ⟨2 * k ^ 2 - k, by rw [hk]; ring⟩
        · exact ⟨2 * k ^ 2 + k, by rw [hk]; ring⟩
      obtain ⟨t, ht⟩ := hdiff
      exact ⟨t + s, by omega⟩
    obtain ⟨m, hm⟩ := heven
    refine ⟨m, ?_⟩
    simp_rw [hc]
    exact_mod_cast (by omega : ∑ i : Fin 8, c i ^ 2 = 2 * m)
  · have hpair : ∀ i : Fin 8, Even (c i ^ 2 + c i) := fun i => by
      rcases Int.even_or_odd (c i) with ⟨k, hk⟩ | ⟨k, hk⟩
      · exact ⟨2 * k ^ 2 + k, by rw [hk]; ring⟩
      · exact ⟨2 * k ^ 2 + 3 * k + 1, by rw [hk]; ring⟩
    obtain ⟨t, ht⟩ := Finset.sum_induction (s := (Finset.univ : Finset (Fin 8)))
      (fun i : Fin 8 => c i ^ 2 + c i) Even (fun _ _ => Even.add) Even.zero (fun i _ => hpair i)
    refine ⟨t + 1, ?_⟩
    have hexp : ∑ i : Fin 8, (v i) ^ 2 =
        (∑ i : Fin 8, ((c i : ℝ) ^ 2 + (c i : ℝ))) + 2 := by
      calc ∑ i : Fin 8, (v i) ^ 2
          = ∑ i : Fin 8, (((c i : ℝ) ^ 2 + (c i : ℝ)) + 1 / 4) := by
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [hc i]; ring
        _ = (∑ i : Fin 8, ((c i : ℝ) ^ 2 + (c i : ℝ))) + 2 := by
              rw [Finset.sum_add_distrib]; norm_num
    rw [hexp]
    have htR : (∑ i : Fin 8, ((c i : ℝ) ^ 2 + (c i : ℝ))) = 2 * (t : ℝ) := by
      exact_mod_cast (by omega : ∑ i : Fin 8, (c i ^ 2 + c i) = 2 * t)
    rw [htR]; push_cast; ring

lemma ofLp_sum_finset {ι : Type*} (s : Finset ι) (f : ι → EuclideanSpace ℝ (Fin 8)) (j : Fin 8) :
    (∑ i ∈ s, f i : EuclideanSpace ℝ (Fin 8)) j = ∑ i ∈ s, (f i) j := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih => simp [PiLp.add_apply, ih]

lemma ofLp_sum_fin {n : ℕ} (f : Fin n → EuclideanSpace ℝ (Fin 8)) (j : Fin 8) :
    (∑ i : Fin n, f i : EuclideanSpace ℝ (Fin 8)) j = ∑ i : Fin n, (f i) j :=
  ofLp_sum_finset Finset.univ f j

/-- **`E₈` is Self-Dual (`dualLattice E8Lattice = E8Lattice`)**! -/
theorem dualLattice_E8Lattice : dualLattice E8Lattice = E8Lattice := by
  have hinner : ∀ u w : EuclideanSpace ℝ (Fin 8), inner ℝ u w = ∑ i : Fin 8, u i * w i := by
    intro u w
    rw [PiLp.inner_apply]
    refine Finset.sum_congr rfl fun i _ => by simp [mul_comm]
  have hspan_top : Submodule.span ℝ (E8Lattice : Set (EuclideanSpace ℝ (Fin 8))) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have h2e : ∀ i : Fin 8, (2 : ℝ) • EuclideanSpace.single i (1 : ℝ) ∈ E8Lattice := by
      intro i
      rw [mem_E8Lattice_iff]
      left
      refine ⟨fun j => if j = i then 2 else 0, fun j => ?_, ⟨1, ?_⟩⟩
      · by_cases hji : j = i
        · subst hji; simp
        · simp [hji]
      · simp
    have hx : x = ∑ i : Fin 8, (x i / 2) • ((2 : ℝ) • EuclideanSpace.single i (1 : ℝ)) := by
      ext j
      rw [ofLp_sum_fin]
      rw [Finset.sum_eq_single j]
      · simp
      · intro i _ hij
        simp [PiLp.smul_apply, Ne.symm hij]
      · intro h; exact absurd (Finset.mem_univ j) h
    rw [hx]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span (h2e i))
  apply le_antisymm
  · rintro w ⟨_, hw⟩
    have hpair_mem : ∀ i j : Fin 8, i ≠ j →
        EuclideanSpace.single i (1 : ℝ) + EuclideanSpace.single j (1 : ℝ) ∈ E8Lattice ∧
        EuclideanSpace.single i (1 : ℝ) - EuclideanSpace.single j (1 : ℝ) ∈ E8Lattice := by
      intro i j hij
      constructor
      · rw [mem_E8Lattice_iff]; left
        refine ⟨fun k => (if k = i then 1 else 0) + (if k = j then 1 else 0), fun k => ?_,
          ⟨1, ?_⟩⟩
        · simp [PiLp.add_apply, eq_comm]
        · simp [Finset.sum_add_distrib]
      · rw [mem_E8Lattice_iff]; left
        refine ⟨fun k => (if k = i then 1 else 0) - (if k = j then 1 else 0), fun k => ?_,
          ⟨0, ?_⟩⟩
        · simp [PiLp.sub_apply, eq_comm]
        · simp [Finset.sum_sub_distrib]
    have hhalf_mem : (WithLp.toLp 2 (fun _ : Fin 8 => (1 / 2 : ℝ)) : EuclideanSpace ℝ (Fin 8)) ∈
        E8Lattice := by
      rw [mem_E8Lattice_iff]; right
      exact ⟨fun _ => 0, fun _ => by simp, ⟨0, by simp⟩⟩
    have hdiff_int : ∀ i j : Fin 8, ∃ m : ℤ, w i - w j = (m : ℝ) := by
      intro i j
      by_cases hij : i = j
      · subst hij; exact ⟨0, by simp⟩
      · obtain ⟨m, hm⟩ := hw _ (hpair_mem i j hij).2
        refine ⟨m, ?_⟩
        rw [hinner] at hm
        have heval : ∑ k : Fin 8, w k *
            (EuclideanSpace.single i (1 : ℝ) - EuclideanSpace.single j (1 : ℝ)) k = w i - w j := by
          simp only [PiLp.sub_apply, PiLp.single_apply, mul_sub, Finset.sum_sub_distrib]
          simp [eq_comm]
        linarith
    have h2_int : ∀ i : Fin 8, ∃ n : ℤ, 2 * w i = (n : ℝ) := by
      intro i
      let j : Fin 8 := if i = 0 then 1 else 0
      have hij : i ≠ j := by
        dsimp only [j]; split_ifs with h0
        · rw [h0]; decide
        · exact h0
      obtain ⟨m₁, hm₁⟩ := hw _ (hpair_mem i j hij).1
      obtain ⟨m₂, hm₂⟩ := hw _ (hpair_mem i j hij).2
      rw [hinner] at hm₁ hm₂
      have he1 : ∑ k : Fin 8, w k *
          (EuclideanSpace.single i (1 : ℝ) + EuclideanSpace.single j (1 : ℝ)) k = w i + w j := by
        simp only [PiLp.add_apply, PiLp.single_apply, mul_add, Finset.sum_add_distrib]
        simp [eq_comm]
      have he2 : ∑ k : Fin 8, w k *
          (EuclideanSpace.single i (1 : ℝ) - EuclideanSpace.single j (1 : ℝ)) k = w i - w j := by
        simp only [PiLp.sub_apply, PiLp.single_apply, mul_sub, Finset.sum_sub_distrib]
        simp [eq_comm]
      exact ⟨m₁ + m₂, by push_cast; linarith⟩
    have hsum_even : ∃ s : ℤ, ∑ i : Fin 8, w i = 2 * (s : ℝ) := by
      obtain ⟨s, hs⟩ := hw _ hhalf_mem
      rw [hinner] at hs
      have he : ∑ i : Fin 8, w i * (1 / 2 : ℝ) = (∑ i : Fin 8, w i) / 2 := by
        rw [← Finset.sum_mul]; ring
      exact ⟨s, by
        have h1 : ∑ i : Fin 8, w i *
            (WithLp.toLp 2 (fun _ : Fin 8 => (1 / 2 : ℝ)) : EuclideanSpace ℝ (Fin 8)) i =
            (∑ i : Fin 8, w i) / 2 := he
        linarith⟩
    exact ⟨h2_int, hdiff_int, hsum_even⟩
  · intro w hw
    refine ⟨by rw [hspan_top]; trivial, fun v hv => ?_⟩
    rw [hinner]
    rcases (mem_E8Lattice_iff w).mp hw with ⟨cw, hcw, ⟨sw, hsw⟩⟩ | ⟨cw, hcw, ⟨sw, hsw⟩⟩
    · rcases (mem_E8Lattice_iff v).mp hv with ⟨cv, hcv, _⟩ | ⟨cv, hcv, _⟩
      · refine ⟨∑ i : Fin 8, cw i * cv i, ?_⟩
        push_cast; refine Finset.sum_congr rfl fun i _ => by rw [hcw i, hcv i]
      · refine ⟨(∑ i : Fin 8, cw i * cv i) + sw, ?_⟩
        have hswR : ∑ i : Fin 8, (cw i : ℝ) = 2 * (sw : ℝ) := by
          exact_mod_cast (by omega : ∑ i : Fin 8, cw i = 2 * sw)
        calc ∑ i : Fin 8, w i * v i
            = ∑ i : Fin 8, ((cw i : ℝ) * (cv i : ℝ) + (cw i : ℝ) * (1 / 2)) := by
                refine Finset.sum_congr rfl fun i _ => by rw [hcw i, hcv i]; ring
          _ = (∑ i : Fin 8, (cw i : ℝ) * (cv i : ℝ)) + (∑ i : Fin 8, (cw i : ℝ)) * (1 / 2) := by
                rw [Finset.sum_add_distrib, ← Finset.sum_mul]
          _ = (((∑ i : Fin 8, cw i * cv i) + sw : ℤ) : ℝ) := by
                rw [hswR]; push_cast; ring
    · rcases (mem_E8Lattice_iff v).mp hv with ⟨cv, hcv, ⟨sv, hsv⟩⟩ | ⟨cv, hcv, ⟨sv, hsv⟩⟩
      · refine ⟨(∑ i : Fin 8, cw i * cv i) + sv, ?_⟩
        have hsvR : ∑ i : Fin 8, (cv i : ℝ) = 2 * (sv : ℝ) := by
          exact_mod_cast (by omega : ∑ i : Fin 8, cv i = 2 * sv)
        calc ∑ i : Fin 8, w i * v i
            = ∑ i : Fin 8, ((cw i : ℝ) * (cv i : ℝ) + (cv i : ℝ) * (1 / 2)) := by
                refine Finset.sum_congr rfl fun i _ => by rw [hcw i, hcv i]; ring
          _ = (∑ i : Fin 8, (cw i : ℝ) * (cv i : ℝ)) + (∑ i : Fin 8, (cv i : ℝ)) * (1 / 2) := by
                rw [Finset.sum_add_distrib, ← Finset.sum_mul]
          _ = (((∑ i : Fin 8, cw i * cv i) + sv : ℤ) : ℝ) := by
                rw [hsvR]; push_cast; ring
      · refine ⟨(∑ i : Fin 8, cw i * cv i) + sw + sv + 2, ?_⟩
        have hswR : ∑ i : Fin 8, (cw i : ℝ) = 2 * (sw : ℝ) := by
          exact_mod_cast (by omega : ∑ i : Fin 8, cw i = 2 * sw)
        have hsvR : ∑ i : Fin 8, (cv i : ℝ) = 2 * (sv : ℝ) := by
          exact_mod_cast (by omega : ∑ i : Fin 8, cv i = 2 * sv)
        calc ∑ i : Fin 8, w i * v i
            = ∑ i : Fin 8, ((cw i : ℝ) * (cv i : ℝ) + (cw i : ℝ) * (1 / 2) +
                (cv i : ℝ) * (1 / 2) + 1 / 4) := by
                refine Finset.sum_congr rfl fun i _ => by rw [hcw i, hcv i]; ring
          _ = (∑ i : Fin 8, (cw i : ℝ) * (cv i : ℝ)) + (∑ i : Fin 8, (cw i : ℝ)) * (1 / 2) +
                (∑ i : Fin 8, (cv i : ℝ)) * (1 / 2) + 2 := by
                simp only [Finset.sum_add_distrib, ← Finset.sum_mul]; norm_num
          _ = (((∑ i : Fin 8, cw i * cv i) + sw + sv + 2 : ℤ) : ℝ) := by
                rw [hswR, hsvR]; push_cast; ring

/-- Explicit upper-triangular `ℤ`-basis vectors of `E₈`:
- column `0`: `2 e₀`,
- column `k` (`1 ≤ k ≤ 6`): `e_k - e₀`,
- column `7`: `(1/2, ..., 1/2)`.
Its determinant is `2 * 1^6 * (1/2) = 1`! -/
def E8BasisVec (k : Fin 8) : EuclideanSpace ℝ (Fin 8) :=
  WithLp.toLp 2 fun i : Fin 8 =>
    if k = 0 then (if i = 0 then (2 : ℝ) else 0)
    else if k = 7 then (1 / 2 : ℝ)
    else (if i = k then (1 : ℝ) else 0) - (if i = 0 then 1 else 0)

@[simp]
lemma E8BasisVec_apply (k i : Fin 8) :
    E8BasisVec k i =
      if k = 0 then (if i = 0 then (2 : ℝ) else 0)
      else if k = 7 then (1 / 2 : ℝ)
      else (if i = k then (1 : ℝ) else 0) - (if i = 0 then 1 else 0) := rfl

lemma E8BasisVec_mem (k : Fin 8) : E8BasisVec k ∈ E8Lattice := by
  by_cases h0 : k = 0
  · subst h0
    rw [mem_E8Lattice_iff]; left
    refine ⟨fun i => if i = 0 then 2 else 0, fun i => ?_, ⟨1, by simp⟩⟩
    by_cases hi : i = 0 <;> simp [hi]
  · by_cases h7 : k = 7
    · subst h7
      rw [mem_E8Lattice_iff]; right
      exact ⟨fun _ => 0, fun _ => by simp, ⟨0, by simp⟩⟩
    · rw [mem_E8Lattice_iff]; left
      refine ⟨fun i => (if i = k then 1 else 0) - (if i = 0 then 1 else 0), fun i => ?_,
        ⟨0, by simp [Finset.sum_sub_distrib]⟩⟩
      simp [h0, h7]

/-- Explicit `ℤ`-basis `E8Basis : Basis (Fin 8) ℤ E8Lattice` of `E₈`! -/
def E8Basis : Basis (Fin 8) ℤ E8Lattice :=
  Basis.mk
    (v := fun k => ⟨E8BasisVec k, E8BasisVec_mem k⟩)
    (by
      rw [Fintype.linearIndependent_iff]
      intro c hc
      have hval : ∀ i : Fin 8, (∑ k : Fin 8, (c k : ℝ) * E8BasisVec k i) = 0 := by
        intro i
        have h0 := congrArg (fun y : E8Lattice => (y : EuclideanSpace ℝ (Fin 8)) i) hc
        simp only [Submodule.coe_sum, Submodule.coe_smul, ZeroMemClass.coe_zero,
          PiLp.zero_apply] at h0
        rw [ofLp_sum_fin] at h0
        simpa only [PiLp.smul_apply, zsmul_eq_mul] using h0
      have hc7 : c 7 = 0 := by
        have h7 := hval 7
        have hsum7 : ∑ k : Fin 8, (c k : ℝ) * E8BasisVec k 7 = (c 7 : ℝ) * (1 / 2) := by
          rw [Finset.sum_eq_single (7 : Fin 8)]
          · simp
          · intro k _ hk
            have h0 : E8BasisVec k 7 = 0 := by
              rw [E8BasisVec_apply]
              by_cases hk0 : k = 0
              · simp [hk0]
              · simp [hk0, hk, hk.symm]
            rw [h0, mul_zero]
          · intro h; exact absurd (Finset.mem_univ _) h
        rw [hsum7] at h7
        have h7R : (c 7 : ℝ) = 0 := by linarith
        exact_mod_cast h7R
      have hcmid : ∀ k : Fin 8, k ≠ 0 → k ≠ 7 → c k = 0 := by
        intro k hk0 hk7
        have hk := hval k
        have hsumk : ∑ j : Fin 8, (c j : ℝ) * E8BasisVec j k = (c k : ℝ) := by
          rw [Finset.sum_eq_single k]
          · simp [hk0, hk7]
          · intro j _ hjk
            by_cases hj7 : j = 7
            · subst hj7; simp [hc7]
            · have h0 : E8BasisVec j k = 0 := by
                rw [E8BasisVec_apply]
                by_cases hj0 : j = 0
                · simp [hj0, hk0]
                · simp [hj0, hj7, hk0, hjk.symm]
              rw [h0, mul_zero]
          · intro h; exact absurd (Finset.mem_univ _) h
        rw [hsumk] at hk
        exact_mod_cast hk
      have hc0 : c 0 = 0 := by
        have h0 := hval 0
        have hsum0 : ∑ j : Fin 8, (c j : ℝ) * E8BasisVec j 0 = 2 * (c 0 : ℝ) := by
          rw [Finset.sum_eq_single (0 : Fin 8)]
          · simp; ring
          · intro j _ hj0
            by_cases hj7 : j = 7
            · subst hj7; simp [hc7]
            · simp [hcmid j hj0 hj7]
          · intro h; exact absurd (Finset.mem_univ _) h
        rw [hsum0] at h0
        have h0R : (c 0 : ℝ) = 0 := by linarith
        exact_mod_cast h0R
      intro k
      by_cases hk0 : k = 0
      · subst hk0; exact hc0
      · by_cases hk7 : k = 7
        · subst hk7; exact hc7
        · exact hcmid k hk0 hk7)
    (by
      intro v _
      obtain ⟨c7, hc7⟩ := v.2.1 7
      let w : EuclideanSpace ℝ (Fin 8) := (v : EuclideanSpace ℝ (Fin 8)) - c7 • E8BasisVec 7
      have hw_mem : w ∈ E8Lattice :=
        E8Lattice.sub_mem v.2 (E8Lattice.smul_mem c7 (E8BasisVec_mem 7))
      have hw7 : w 7 = 0 := by
        have h77 : E8BasisVec 7 7 = 1 / 2 := by
          rw [E8BasisVec_apply]; simp
        dsimp only [w]
        rw [PiLp.sub_apply, PiLp.smul_apply, zsmul_eq_mul, h77]
        linarith
      have hw_int : ∃ a : Fin 8 → ℤ, (∀ i, w i = (a i : ℝ)) ∧ Even (∑ i : Fin 8, a i) := by
        rcases (mem_E8Lattice_iff w).mp hw_mem with h | ⟨a, ha, _⟩
        · exact h
        · exfalso
          have h7 := ha 7
          rw [hw7] at h7
          have h2 : (2 * a 7 + 1 : ℤ) = 0 := by
            have : ((2 * a 7 + 1 : ℤ) : ℝ) = 0 := by push_cast; linarith
            exact_mod_cast this
          omega
      obtain ⟨a, ha, ⟨s, hs⟩⟩ := hw_int
      have ha7 : a 7 = 0 := by
        have h1 : (a 7 : ℝ) = 0 := (ha 7).symm.trans hw7
        exact_mod_cast h1
      let coeff : Fin 8 → ℤ := fun k =>
        if k = 0 then s else if k = 7 then c7 else a k
      have hsum_eq : v = ∑ k : Fin 8, coeff k • (⟨E8BasisVec k, E8BasisVec_mem k⟩ : E8Lattice) := by
        apply Subtype.ext
        ext i
        simp only [Submodule.coe_sum, Submodule.coe_smul]
        rw [ofLp_sum_fin]
        simp only [PiLp.smul_apply, zsmul_eq_mul]
        have hdecomp : (v : EuclideanSpace ℝ (Fin 8)) i = w i + (c7 : ℝ) * E8BasisVec 7 i := by
          dsimp only [w]; simp [PiLp.sub_apply, PiLp.smul_apply, zsmul_eq_mul]
        rw [hdecomp, ha i]
        by_cases hi7 : i = 7
        · subst hi7
          rw [ha7, Int.cast_zero, zero_add]
          rw [Finset.sum_eq_single (7 : Fin 8)]
          · simp [coeff]
          · intro k _ hk7
            have h0 : E8BasisVec k 7 = 0 := by
              rw [E8BasisVec_apply]
              by_cases hk0 : k = 0
              · simp [hk0]
              · simp [hk0, hk7, hk7.symm]
            rw [h0, mul_zero]
          · intro h; exact absurd (Finset.mem_univ _) h
        · by_cases hi0 : i = 0
          · subst hi0
            have hmid : ∑ k : Fin 8, (coeff k : ℝ) * E8BasisVec k 0 =
                2 * (s : ℝ) + (c7 : ℝ) * E8BasisVec 7 0 -
                  ∑ k ∈ (Finset.univ.erase (0 : Fin 8)).erase (7 : Fin 8), (a k : ℝ) := by
              rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Fin 8))]
              have h7in : (7 : Fin 8) ∈ Finset.univ.erase (0 : Fin 8) := by decide
              rw [← Finset.add_sum_erase _ _ h7in]
              have ht0 : (coeff 0 : ℝ) * E8BasisVec 0 0 = 2 * (s : ℝ) := by
                simp [coeff]; ring
              have ht7 : (coeff 7 : ℝ) * E8BasisVec 7 0 = (c7 : ℝ) * E8BasisVec 7 0 := by
                simp [coeff]
              have hrem : ∑ k ∈ (Finset.univ.erase (0 : Fin 8)).erase (7 : Fin 8),
                  (coeff k : ℝ) * E8BasisVec k 0 =
                  -(∑ k ∈ (Finset.univ.erase (0 : Fin 8)).erase (7 : Fin 8), (a k : ℝ)) := by
                rw [← Finset.sum_neg_distrib]
                refine Finset.sum_congr rfl fun k hk => ?_
                have hk7' : k ≠ 7 := (Finset.mem_erase.mp hk).1
                have hk0' : k ≠ 0 := (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1
                simp [coeff, hk0', hk7', hk0'.symm]
              rw [ht0, ht7, hrem]; ring
            rw [hmid]
            have hsum_a : ∑ k : Fin 8, (a k : ℝ) =
                (a 0 : ℝ) + (a 7 : ℝ) +
                  ∑ k ∈ (Finset.univ.erase (0 : Fin 8)).erase (7 : Fin 8), (a k : ℝ) := by
              rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Fin 8))]
              have h7in : (7 : Fin 8) ∈ Finset.univ.erase (0 : Fin 8) := by decide
              rw [← Finset.add_sum_erase _ _ h7in]; ring
            have hsR : ∑ k : Fin 8, (a k : ℝ) = 2 * (s : ℝ) := by
              exact_mod_cast (by omega : ∑ k : Fin 8, a k = 2 * s)
            rw [ha7, Int.cast_zero] at hsum_a
            linarith
          · have hsplit : ∑ k : Fin 8, (coeff k : ℝ) * E8BasisVec k i =
                (a i : ℝ) + (c7 : ℝ) * E8BasisVec 7 i := by
              rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
              have h7in : (7 : Fin 8) ∈ Finset.univ.erase i :=
                Finset.mem_erase.mpr ⟨Ne.symm hi7, Finset.mem_univ _⟩
              rw [← Finset.add_sum_erase _ _ h7in]
              have hti : (coeff i : ℝ) * E8BasisVec i i = (a i : ℝ) := by
                simp [coeff, hi0, hi7]
              have ht7 : (coeff 7 : ℝ) * E8BasisVec 7 i = (c7 : ℝ) * E8BasisVec 7 i := by
                simp [coeff]
              have hrest : ∑ k ∈ (Finset.univ.erase i).erase (7 : Fin 8),
                  (coeff k : ℝ) * E8BasisVec k i = 0 := by
                refine Finset.sum_eq_zero fun k hk => ?_
                have hk7' : k ≠ 7 := (Finset.mem_erase.mp hk).1
                have hki' : k ≠ i := (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1
                have hzero : E8BasisVec k i = 0 := by
                  rw [E8BasisVec_apply]
                  by_cases hk0 : k = 0
                  · simp [hk0, hi0]
                  · simp [hk0, hk7', hi0, hki'.symm]
                rw [hzero, mul_zero]
              rw [hti, ht7, hrest, add_zero]
            exact hsplit.symm
      rw [hsum_eq]
      exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩))

/-- `rk E8Lattice = 8`. -/
theorem rk_E8Lattice : rk E8Lattice = 8 := by
  unfold rk
  simpa using Module.finrank_eq_card_basis E8Basis

/-- **`E₈` is Unimodular (`covol E8Lattice = 1`)**! -/
theorem covol_E8Lattice : covol E8Lattice = 1 := by
  rw [covol_eq_sqrt_det_gram E8Lattice E8Basis]
  let M : Matrix (Fin 8) (Fin 8) ℝ := Matrix.of fun i j => E8BasisVec j i
  have hgram : Matrix.gram ℝ (fun j => ((E8Basis j : E8Lattice) : EuclideanSpace ℝ (Fin 8))) =
      M.transpose * M := by
    ext j k
    simp only [Matrix.gram_apply, Matrix.mul_apply, Matrix.transpose_apply, M, Matrix.of_apply,
      E8Basis, Basis.mk_apply, PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
    refine Finset.sum_congr rfl fun i _ => mul_comm _ _
  have htri : M.BlockTriangular id := by
    intro i j hij
    dsimp only [M, Matrix.of_apply]
    rw [E8BasisVec_apply]
    have hj7 : j ≠ 7 := by
      intro h; subst h; exact not_lt_of_ge (Fin.le_last i) hij
    by_cases hj0 : j = 0
    · subst hj0
      have hi0 : i ≠ 0 := ne_of_gt hij
      simp [hi0]
    · have hi0 : i ≠ 0 := ne_of_gt (lt_of_le_of_lt (Fin.zero_le j) hij)
      have hij' : i ≠ j := ne_of_gt hij
      simp [hj0, hj7, hi0, hij']
  have hdetM : M.det = 1 := by
    rw [Matrix.det_of_isUpperTriangular htri]
    rw [Fin.prod_univ_eight]
    have h0 : M 0 0 = 2 := by simp [M]
    have h1 : M 1 1 = 1 := by simp [M]
    have h2 : M 2 2 = 1 := by simp [M]
    have h3 : M 3 3 = 1 := by simp [M]
    have h4 : M 4 4 = 1 := by simp [M]
    have h5 : M 5 5 = 1 := by simp [M]
    have h6 : M 6 6 = 1 := by simp [M]
    have h7 : M 7 7 = 1 / 2 := by simp [M]
    rw [h0, h1, h2, h3, h4, h5, h6, h7]
    norm_num
  rw [hgram, Matrix.det_mul, Matrix.det_transpose, hdetM]
  norm_num

lemma prod_zpow_finset {ι : Type*} (s : Finset ι) {a : ℂ} (ha : a ≠ 0) (c : ι → ℤ) :
    ∏ i ∈ s, a ^ c i = a ^ (∑ i ∈ s, c i) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons x s hx ih =>
    rw [Finset.prod_cons, Finset.sum_cons, zpow_add₀ ha, ih]

/-- Helper: even-sum integer `ℤ⁸` theta sum equals `(1/2)(θ₃(τ)⁸ + θ₄(τ)⁸)`. -/
lemma tsum_E8_intPart (τ : UpperHalfPlane) :
    (∑' c : { c : Fin 8 → ℤ // Even (∑ i : Fin 8, c i) },
      Complex.exp ((Real.pi : ℂ) * Complex.I * (τ : ℂ) *
        ((∑ i : Fin 8, (c.1 i : ℝ) ^ 2 : ℝ) : ℂ))) =
      (1 / 2 : ℂ) * (theta3 (τ : ℂ) ^ 8 + theta4 (τ : ℂ) ^ 8) := by
  let g3 : Fin 8 → ℤ → ℂ := fun _ n =>
    Complex.exp ((Real.pi : ℂ) * Complex.I * (n : ℂ) ^ 2 * (τ : ℂ))
  let g4 : Fin 8 → ℤ → ℂ := fun _ n =>
    (-1 : ℂ) ^ n * Complex.exp ((Real.pi : ℂ) * Complex.I * (n : ℂ) ^ 2 * (τ : ℂ))
  have ⟨hs3, hprod3⟩ := summable_norm_and_tsum_pi_fin_prod_complex g3
    (fun _ => summable_norm_theta3 τ.im_pos)
  have ⟨hs4, hprod4⟩ := summable_norm_and_tsum_pi_fin_prod_complex g4
    (fun _ => summable_norm_theta4 τ.im_pos)
  have hprod_g3 : ∀ c : Fin 8 → ℤ,
      ∏ i : Fin 8, g3 i (c i) =
        Complex.exp ((Real.pi : ℂ) * Complex.I * (τ : ℂ) *
          ((∑ i : Fin 8, (c i : ℝ) ^ 2 : ℝ) : ℂ)) := by
    intro c
    dsimp only [g3]
    rw [← Complex.exp_sum, Complex.ofReal_sum, Finset.mul_sum]
    congr 1; refine Finset.sum_congr rfl fun i _ => by push_cast; ring
  have hprod_g4 : ∀ c : Fin 8 → ℤ,
      ∏ i : Fin 8, g4 i (c i) =
        (-1 : ℂ) ^ (∑ i : Fin 8, c i) * ∏ i : Fin 8, g3 i (c i) := by
    intro c
    dsimp only [g4, g3]
    rw [Finset.prod_mul_distrib, prod_zpow_finset Finset.univ (by norm_num : (-1 : ℂ) ≠ 0)]
  have hparity : ∀ n : ℤ, (1 / 2 : ℂ) * (1 + (-1 : ℂ) ^ n) = if Even n then 1 else 0 := by
    intro n
    rcases Int.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
    · rw [if_pos ⟨k, hk⟩, show n = 2 * k by omega, zpow_mul]; norm_num
    · have hnot : ¬ Even n := by rintro ⟨m, hm⟩; omega
      rw [if_neg hnot, show n = 2 * k + 1 by omega,
        zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), zpow_mul, zpow_one]
      norm_num
  have hsub : (∑' c : { c : Fin 8 → ℤ // Even (∑ i : Fin 8, c i) },
      Complex.exp ((Real.pi : ℂ) * Complex.I * (τ : ℂ) *
        ((∑ i : Fin 8, (c.1 i : ℝ) ^ 2 : ℝ) : ℂ))) =
      ∑' c : Fin 8 → ℤ, if Even (∑ i : Fin 8, c i) then ∏ i : Fin 8, g3 i (c i) else 0 := by
    calc (∑' c : { c : Fin 8 → ℤ // Even (∑ i : Fin 8, c i) },
          Complex.exp ((Real.pi : ℂ) * Complex.I * (τ : ℂ) *
            ((∑ i : Fin 8, (c.1 i : ℝ) ^ 2 : ℝ) : ℂ)))
        = ∑' c : { c : Fin 8 → ℤ // Even (∑ i : Fin 8, c i) }, ∏ i : Fin 8, g3 i (c.1 i) :=
            tsum_congr fun c => (hprod_g3 c.1).symm
      _ = ∑' c : Fin 8 → ℤ,
            ({ c : Fin 8 → ℤ | Even (∑ i : Fin 8, c i) }).indicator
              (fun c => ∏ i : Fin 8, g3 i (c i)) c :=
            tsum_subtype { c : Fin 8 → ℤ | Even (∑ i : Fin 8, c i) } (fun c => ∏ i : Fin 8, g3 i (c i))
      _ = ∑' c : Fin 8 → ℤ, if Even (∑ i : Fin 8, c i) then ∏ i : Fin 8, g3 i (c i) else 0 :=
            tsum_congr fun c => by simp [Set.indicator]
  rw [hsub]
  have hite : ∀ c : Fin 8 → ℤ,
      (if Even (∑ i : Fin 8, c i) then ∏ i : Fin 8, g3 i (c i) else 0) =
        (1 / 2 : ℂ) * (∏ i : Fin 8, g3 i (c i) + ∏ i : Fin 8, g4 i (c i)) := by
    intro c
    rw [hprod_g4, show (1 / 2 : ℂ) * (∏ i : Fin 8, g3 i (c i) +
        (-1 : ℂ) ^ (∑ i : Fin 8, c i) * ∏ i : Fin 8, g3 i (c i)) =
        ((1 / 2 : ℂ) * (1 + (-1 : ℂ) ^ (∑ i : Fin 8, c i))) * ∏ i : Fin 8, g3 i (c i) by ring,
      hparity]
    split_ifs <;> simp
  simp_rw [hite, tsum_mul_left]
  rw [hs3.of_norm.tsum_add hs4.of_norm, hprod3, hprod4]
  simp [g3, g4, theta3, theta4]

/-- Helper: even-sum half-integer `(ℤ + 1/2)⁸` theta sum equals `(1/2) θ₂(τ)⁸`. -/
lemma tsum_E8_halfPart (τ : UpperHalfPlane) :
    (∑' c : { c : Fin 8 → ℤ // Even (∑ i : Fin 8, c i) },
      Complex.exp ((Real.pi : ℂ) * Complex.I * (τ : ℂ) *
        ((∑ i : Fin 8, ((c.1 i : ℝ) + 1 / 2) ^ 2 : ℝ) : ℂ))) =
      (1 / 2 : ℂ) * theta2 (τ : ℂ) ^ 8 := by
  let g2 : Fin 8 → ℤ → ℂ := fun _ n =>
    Complex.exp ((Real.pi : ℂ) * Complex.I * ((n : ℂ) + 1 / 2) ^ 2 * (τ : ℂ))
  let g2alt : Fin 8 → ℤ → ℂ := fun _ n =>
    (-1 : ℂ) ^ n * Complex.exp ((Real.pi : ℂ) * Complex.I * ((n : ℂ) + 1 / 2) ^ 2 * (τ : ℂ))
  have ⟨hs2, hprod2⟩ := summable_norm_and_tsum_pi_fin_prod_complex g2
    (fun _ => summable_norm_theta2 τ.im_pos)
  have ⟨hs2a, hprod2a⟩ := summable_norm_and_tsum_pi_fin_prod_complex g2alt
    (fun _ => (summable_norm_theta2 τ.im_pos).congr fun n => by
      simp [g2alt, norm_zpow])
  have hprod_g2 : ∀ c : Fin 8 → ℤ,
      ∏ i : Fin 8, g2 i (c i) =
        Complex.exp ((Real.pi : ℂ) * Complex.I * (τ : ℂ) *
          ((∑ i : Fin 8, ((c i : ℝ) + 1 / 2) ^ 2 : ℝ) : ℂ)) := by
    intro c
    dsimp only [g2]
    rw [← Complex.exp_sum, Complex.ofReal_sum, Finset.mul_sum]
    congr 1; refine Finset.sum_congr rfl fun i _ => by push_cast; ring
  have hprod_g2a : ∀ c : Fin 8 → ℤ,
      ∏ i : Fin 8, g2alt i (c i) =
        (-1 : ℂ) ^ (∑ i : Fin 8, c i) * ∏ i : Fin 8, g2 i (c i) := by
    intro c
    dsimp only [g2alt, g2]
    rw [Finset.prod_mul_distrib, prod_zpow_finset Finset.univ (by norm_num : (-1 : ℂ) ≠ 0)]
  have hparity : ∀ n : ℤ, (1 / 2 : ℂ) * (1 + (-1 : ℂ) ^ n) = if Even n then 1 else 0 := by
    intro n
    rcases Int.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
    · rw [if_pos ⟨k, hk⟩, show n = 2 * k by omega, zpow_mul]; norm_num
    · have hnot : ¬ Even n := by rintro ⟨m, hm⟩; omega
      rw [if_neg hnot, show n = 2 * k + 1 by omega,
        zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), zpow_mul, zpow_one]
      norm_num
  have hsub : (∑' c : { c : Fin 8 → ℤ // Even (∑ i : Fin 8, c i) },
      Complex.exp ((Real.pi : ℂ) * Complex.I * (τ : ℂ) *
        ((∑ i : Fin 8, ((c.1 i : ℝ) + 1 / 2) ^ 2 : ℝ) : ℂ))) =
      ∑' c : Fin 8 → ℤ, if Even (∑ i : Fin 8, c i) then ∏ i : Fin 8, g2 i (c i) else 0 := by
    calc (∑' c : { c : Fin 8 → ℤ // Even (∑ i : Fin 8, c i) },
          Complex.exp ((Real.pi : ℂ) * Complex.I * (τ : ℂ) *
            ((∑ i : Fin 8, ((c.1 i : ℝ) + 1 / 2) ^ 2 : ℝ) : ℂ)))
        = ∑' c : { c : Fin 8 → ℤ // Even (∑ i : Fin 8, c i) }, ∏ i : Fin 8, g2 i (c.1 i) :=
            tsum_congr fun c => (hprod_g2 c.1).symm
      _ = ∑' c : Fin 8 → ℤ,
            ({ c : Fin 8 → ℤ | Even (∑ i : Fin 8, c i) }).indicator
              (fun c => ∏ i : Fin 8, g2 i (c i)) c :=
            tsum_subtype { c : Fin 8 → ℤ | Even (∑ i : Fin 8, c i) } (fun c => ∏ i : Fin 8, g2 i (c i))
      _ = ∑' c : Fin 8 → ℤ, if Even (∑ i : Fin 8, c i) then ∏ i : Fin 8, g2 i (c i) else 0 :=
            tsum_congr fun c => by simp [Set.indicator]
  rw [hsub]
  have hite : ∀ c : Fin 8 → ℤ,
      (if Even (∑ i : Fin 8, c i) then ∏ i : Fin 8, g2 i (c i) else 0) =
        (1 / 2 : ℂ) * (∏ i : Fin 8, g2 i (c i) + ∏ i : Fin 8, g2alt i (c i)) := by
    intro c
    rw [hprod_g2a, show (1 / 2 : ℂ) * (∏ i : Fin 8, g2 i (c i) +
        (-1 : ℂ) ^ (∑ i : Fin 8, c i) * ∏ i : Fin 8, g2 i (c i)) =
        ((1 / 2 : ℂ) * (1 + (-1 : ℂ) ^ (∑ i : Fin 8, c i))) * ∏ i : Fin 8, g2 i (c i) by ring,
      hparity]
    split_ifs <;> simp
  simp_rw [hite, tsum_mul_left]
  rw [hs2.of_norm.tsum_add hs2a.of_norm, hprod2, hprod2a]
  have hzero : ∏ i : Fin 8, ∑' n : ℤ, g2alt i n = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ (0 : Fin 8)) tsum_neg_one_pow_theta2_eq_zero
  rw [hzero, add_zero]
  simp [g2, theta2]

/-- Canonical equivalence between `E₈` and two copies of even-sum integer 8-tuples
(integer points `D₈` and half-integer coset `D₈ + (1/2, ..., 1/2)`). -/
def E8EquivSum :
    ({ c : Fin 8 → ℤ // Even (∑ i : Fin 8, c i) } ⊕
      { c : Fin 8 → ℤ // Even (∑ i : Fin 8, c i) }) ≃ E8Lattice :=
  Equiv.ofBijective
    (fun x => match x with
      | Sum.inl c => ⟨WithLp.toLp 2 (fun i => (c.1 i : ℝ)),
          (mem_E8Lattice_iff _).mpr (Or.inl ⟨c.1, fun _ => rfl, c.2⟩)⟩
      | Sum.inr c => ⟨WithLp.toLp 2 (fun i => (c.1 i : ℝ) + 1 / 2),
          (mem_E8Lattice_iff _).mpr (Or.inr ⟨c.1, fun _ => rfl, c.2⟩)⟩)
    (by
      constructor
      · intro x y hxy
        rcases x with ⟨cx, hcx⟩ | ⟨cx, hcx⟩ <;> rcases y with ⟨cy, hcy⟩ | ⟨cy, hcy⟩
        · congr 1; apply Subtype.ext; funext i
          have hi : (cx i : ℝ) = (cy i : ℝ) :=
            congrArg (fun v : E8Lattice => (v : EuclideanSpace ℝ (Fin 8)) i) hxy
          exact_mod_cast hi
        · exfalso
          have hi : (cx 0 : ℝ) = (cy 0 : ℝ) + 1 / 2 :=
            congrArg (fun v : E8Lattice => (v : EuclideanSpace ℝ (Fin 8)) 0) hxy
          have h2 : (2 * cx 0 : ℤ) = 2 * cy 0 + 1 := by
            have : ((2 * cx 0 : ℤ) : ℝ) = ((2 * cy 0 + 1 : ℤ) : ℝ) := by push_cast; linarith
            exact_mod_cast this
          omega
        · exfalso
          have hi : (cx 0 : ℝ) + 1 / 2 = (cy 0 : ℝ) :=
            congrArg (fun v : E8Lattice => (v : EuclideanSpace ℝ (Fin 8)) 0) hxy
          have h2 : (2 * cx 0 + 1 : ℤ) = 2 * cy 0 := by
            have : ((2 * cx 0 + 1 : ℤ) : ℝ) = ((2 * cy 0 : ℤ) : ℝ) := by push_cast; linarith
            exact_mod_cast this
          omega
        · congr 1; apply Subtype.ext; funext i
          have hi : (cx i : ℝ) + 1 / 2 = (cy i : ℝ) + 1 / 2 :=
            congrArg (fun v : E8Lattice => (v : EuclideanSpace ℝ (Fin 8)) i) hxy
          have hi' : (cx i : ℝ) = (cy i : ℝ) := by linarith
          exact_mod_cast hi'
      · intro v
        rcases (mem_E8Lattice_iff (v : EuclideanSpace ℝ (Fin 8))).mp v.2 with
          ⟨c, hc, hev⟩ | ⟨c, hc, hev⟩
        · refine ⟨Sum.inl ⟨c, hev⟩, Subtype.ext ?_⟩
          ext i; exact (hc i).symm
        · refine ⟨Sum.inr ⟨c, hev⟩, Subtype.ext ?_⟩
          ext i; exact (hc i).symm)

/-- **EXACT JACOBI THETA DECOMPOSITION OF `Θ_{E₈}(τ)`**:
for every `τ : UpperHalfPlane`,
$$\Theta_{E_8}(\tau) = \frac{1}{2}\left(\theta_3(\tau)^8 + \theta_4(\tau)^8 + \theta_2(\tau)^8\right).$$ -/
theorem complexLatticeTheta_E8Lattice (τ : UpperHalfPlane) :
    complexLatticeTheta E8Lattice τ =
      (1 / 2 : ℂ) * (theta3 (τ : ℂ) ^ 8 + theta4 (τ : ℂ) ^ 8 + theta2 (τ : ℂ) ^ 8) := by
  let F : ({ c : Fin 8 → ℤ // Even (∑ i : Fin 8, c i) } ⊕
      { c : Fin 8 → ℤ // Even (∑ i : Fin 8, c i) }) → ℂ :=
    fun x => complexGaussianTerm (τ : ℂ) ((E8EquivSum x : E8Lattice) : EuclideanSpace ℝ (Fin 8))
  have hsum_all : Summable F :=
    (Equiv.summable_iff E8EquivSum).mpr (summable_complexGaussianTerm E8Lattice τ.im_pos)
  have hsum_l : Summable (fun c => F (Sum.inl c)) := hsum_all.comp_injective Sum.inl_injective
  have hsum_r : Summable (fun c => F (Sum.inr c)) := hsum_all.comp_injective Sum.inr_injective
  have hL : (∑' c, F (Sum.inl c)) = (1 / 2 : ℂ) * (theta3 (τ : ℂ) ^ 8 + theta4 (τ : ℂ) ^ 8) := by
    rw [← tsum_E8_intPart τ]
    refine tsum_congr fun c => ?_
    dsimp only [F, complexGaussianTerm]
    congr 2
    have hcoe : ((E8EquivSum (Sum.inl c) : E8Lattice) : EuclideanSpace ℝ (Fin 8)) =
        WithLp.toLp 2 (fun i => (c.1 i : ℝ)) := rfl
    rw [hcoe, EuclideanSpace.norm_sq_eq]
    congr 1
    refine Finset.sum_congr rfl fun i _ => by simp [Real.norm_eq_abs]
  have hR : (∑' c, F (Sum.inr c)) = (1 / 2 : ℂ) * theta2 (τ : ℂ) ^ 8 := by
    rw [← tsum_E8_halfPart τ]
    refine tsum_congr fun c => ?_
    dsimp only [F, complexGaussianTerm]
    congr 2
    have hcoe : ((E8EquivSum (Sum.inr c) : E8Lattice) : EuclideanSpace ℝ (Fin 8)) =
        WithLp.toLp 2 (fun i => (c.1 i : ℝ) + 1 / 2) := rfl
    rw [hcoe, EuclideanSpace.norm_sq_eq]
    congr 1
    refine Finset.sum_congr rfl fun i _ => by simp [Real.norm_eq_abs]
  calc complexLatticeTheta E8Lattice τ
      = ∑' x, F x := by
          unfold complexLatticeTheta complexLatticeThetaFun
          exact (E8EquivSum.tsum_eq _).symm
    _ = (∑' c, F (Sum.inl c)) + (∑' c, F (Sum.inr c)) := hsum_l.tsum_sum hsum_r
    _ = (1 / 2 : ℂ) * (theta3 (τ : ℂ) ^ 8 + theta4 (τ : ℂ) ^ 8) +
          (1 / 2 : ℂ) * theta2 (τ : ℂ) ^ 8 := by rw [hL, hR]
    _ = (1 / 2 : ℂ) * (theta3 (τ : ℂ) ^ 8 + theta4 (τ : ℂ) ^ 8 + theta2 (τ : ℂ) ^ 8) := by ring

/-- **EXACT `S`-MODULAR TRANSFORMATION OF `Θ_{E₈}(τ)`**:
`Θ_{E₈}(S • τ) = τ^4 · Θ_{E₈}(τ)`! -/
theorem complexLatticeTheta_E8Lattice_S_smul (τ : UpperHalfPlane) :
    complexLatticeTheta E8Lattice (ModularGroup.S • τ) =
      (τ : ℂ) ^ 4 * complexLatticeTheta E8Lattice τ := by
  rw [complexLatticeTheta_E8Lattice, complexLatticeTheta_E8Lattice,
    theta3_S_smul, theta4_S_smul, theta2_S_smul]
  have hpow8 : ((-Complex.I * (τ : ℂ)) ^ ((1 : ℂ) / 2)) ^ 8 = (τ : ℂ) ^ 4 := by
    rw [← Complex.cpow_nat_mul]
    have h1 := neg_I_mul_cpow_four_mul 1 τ
    simpa [div_eq_mul_inv] using h1
  simp only [mul_pow, hpow8]
  ring

/-- **EXACT `T`-PERIODICITY OF `Θ_{E₈}(τ)`**: `Θ_{E₈}(T • τ) = Θ_{E₈}(τ)`! -/
theorem complexLatticeTheta_E8Lattice_T_smul (τ : UpperHalfPlane) :
    complexLatticeTheta E8Lattice (ModularGroup.T • τ) = complexLatticeTheta E8Lattice τ :=
  complexLatticeTheta_T_smul_of_even isEvenLattice_E8Lattice τ

/-- **FULL `SL₂(ℤ)` WEIGHT-`4` SLASH-INVARIANCE OF `Θ_{E₈}`**:
for EVERY `γ ∈ SL₂(ℤ)`, `(Θ_{E₈} |_4 γ) = Θ_{E₈}`! -/
theorem E8Lattice_slash_SL2Z_invariant (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    SlashAction.map (4 : ℤ) (sl2ZToGL2R γ) (complexLatticeTheta E8Lattice) =
      complexLatticeTheta E8Lattice :=
  slash_SL2Z_invariant_of_S_T 4 (complexLatticeTheta E8Lattice)
    (fun τ => by simpa using complexLatticeTheta_E8Lattice_S_smul τ)
    complexLatticeTheta_E8Lattice_T_smul γ

/-- Real-axis functional equation of `E₈`: `Θ_{E₈}(t) = t^{-4} Θ_{E₈}(t⁻¹)` for all `t > 0`! -/
theorem latticeTheta_E8Lattice_functional_eq {t : ℝ} (ht : 0 < t) :
    latticeTheta E8Lattice t = t ^ (-4 : ℝ) * latticeTheta E8Lattice t⁻¹ := by
  have hinv_pos : 0 < t⁻¹ := inv_pos.mpr ht
  let τ : UpperHalfPlane := ⟨Complex.I * ((t⁻¹ : ℝ) : ℂ), by simp [hinv_pos]⟩
  have hS := complexLatticeTheta_E8Lattice_S_smul τ
  have hS_coe : ((ModularGroup.S • τ : UpperHalfPlane) : ℂ) = Complex.I * (t : ℂ) := by
    rw [UpperHalfPlane.modular_S_smul]
    dsimp only [τ]
    rw [Complex.ofReal_inv, inv_neg, mul_inv, Complex.inv_I, inv_inv]
    ring
  have hτ_pow : (τ : ℂ) ^ 4 = ((t ^ (-4 : ℝ) : ℝ) : ℂ) := by
    dsimp only [τ]
    rw [mul_pow, show Complex.I ^ 4 = 1 by
      calc Complex.I ^ 4 = (Complex.I ^ 2) ^ 2 := by ring
        _ = (-1 : ℂ) ^ 2 := by rw [Complex.I_sq]
        _ = 1 := by norm_num, one_mul]
    rw [← Complex.ofReal_pow, Real.rpow_neg ht.le, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast, inv_pow]
  have hlhs : complexLatticeTheta E8Lattice (ModularGroup.S • τ) = (latticeTheta E8Lattice t : ℂ) := by
    unfold complexLatticeTheta
    rw [hS_coe, complexLatticeThetaFun_imaginary_axis]
  have hrhs : complexLatticeTheta E8Lattice τ = (latticeTheta E8Lattice t⁻¹ : ℂ) :=
    complexLatticeTheta_imaginary_axis E8Lattice hinv_pos
  rw [hlhs, hrhs, hτ_pow, ← Complex.ofReal_mul] at hS
  exact Complex.ofReal_injective hS

/-- **Concrete `k`-Fold Direct-Sum Even Unimodular Lattice `E₈^k ⊂ ℝ^{k × 8}`** of rank `8k`! -/
def E8PowLattice (k : ℕ) : Submodule ℤ (EuclideanSpace ℝ (Fin k × Fin 8)) where
  carrier := { v | ∀ j : Fin k, WithLp.toLp 2 (fun i : Fin 8 => v (j, i)) ∈ E8Lattice }
  zero_mem' := fun _ => E8Lattice.zero_mem
  add_mem' := fun hv hw j => E8Lattice.add_mem (hv j) (hw j)
  smul_mem' := fun m _ hv j => E8Lattice.smul_mem m (hv j)

/-- `E₈^k` is discrete (`DiscreteTopology (E8PowLattice k)`). -/
instance discreteTopology_E8PowLattice (k : ℕ) : DiscreteTopology (E8PowLattice k) := by
  let f : E8PowLattice k → (Fin k → E8Lattice) := fun v j =>
    ⟨WithLp.toLp 2 (fun i : Fin 8 => (v : EuclideanSpace ℝ (Fin k × Fin 8)) (j, i)), v.2 j⟩
  have hf_inj : Function.Injective f := by
    intro v w h
    apply Subtype.ext
    ext ⟨j, i⟩
    exact congrArg (fun u : E8Lattice => (u : EuclideanSpace ℝ (Fin 8)) i) (congrFun h j)
  have hf_cont : Continuous f := by
    refine continuous_pi fun j => Continuous.subtype_mk ?_ _
    refine (PiLp.continuous_toLp 2 (fun _ : Fin 8 => ℝ)).comp ?_
    refine continuous_pi fun i => ?_
    exact (EuclideanSpace.proj (j, i)).continuous.comp continuous_subtype_val
  exact DiscreteTopology.of_continuous_injective hf_cont hf_inj

/-- **`E₈^k` is an Even Lattice** for every `k : ℕ`! -/
theorem isEvenLattice_E8PowLattice (k : ℕ) : IsEvenLattice (E8PowLattice k) := by
  intro v hv
  have hnorm : ‖v‖ ^ 2 = ∑ j : Fin k, ‖WithLp.toLp 2 (fun i : Fin 8 => v (j, i))‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [EuclideanSpace.norm_sq_eq]
  have hchoose : ∀ j : Fin k, ∃ m : ℤ,
      ‖WithLp.toLp 2 (fun i : Fin 8 => v (j, i))‖ ^ 2 = 2 * (m : ℝ) :=
    fun j => isEvenLattice_E8Lattice _ (hv j)
  refine ⟨∑ j : Fin k, Classical.choose (hchoose j), ?_⟩
  rw [hnorm]
  push_cast
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => Classical.choose_spec (hchoose j)

/-- Exact product factorization of `Θ_{E₈^k}(τ) = Θ_{E₈}(τ)^k`! -/
theorem complexLatticeTheta_E8PowLattice (k : ℕ) (τ : UpperHalfPlane) :
    complexLatticeTheta (E8PowLattice k) τ = (complexLatticeTheta E8Lattice τ) ^ k := by
  induction k with
  | zero =>
    unfold complexLatticeTheta complexLatticeThetaFun
    rw [pow_zero, tsum_eq_single (0 : E8PowLattice 0)]
    · simp
    · intro v hv
      exfalso; apply hv; apply Subtype.ext; ext ⟨j, _⟩; exact j.elim0
  | succ k ih =>
    let e : (E8Lattice × E8PowLattice k) ≃ E8PowLattice (k + 1) :=
      { toFun := fun p =>
          ⟨WithLp.toLp 2 (fun ji : Fin (k + 1) × Fin 8 =>
            Fin.cases ((p.1 : EuclideanSpace ℝ (Fin 8)) ji.2)
              (fun j' => (p.2 : EuclideanSpace ℝ (Fin k × Fin 8)) (j', ji.2)) ji.1),
            fun j => Fin.cases p.1.2 (fun j' => p.2.2 j') j⟩
        invFun := fun v =>
          (⟨WithLp.toLp 2 (fun i => (v : EuclideanSpace ℝ (Fin (k + 1) × Fin 8)) (0, i)), v.2 0⟩,
           ⟨WithLp.toLp 2 (fun ji => (v : EuclideanSpace ℝ (Fin (k + 1) × Fin 8)) (ji.1.succ, ji.2)),
            fun j' => v.2 j'.succ⟩)
        left_inv := fun p => by
          apply Prod.ext <;> apply Subtype.ext <;> ext x <;> rfl
        right_inv := fun v => by
          apply Subtype.ext; ext ⟨j, i⟩
          refine Fin.cases rfl (fun _ => rfl) j }
    have hsplit : ∀ p : E8Lattice × E8PowLattice k,
        complexGaussianTerm (τ : ℂ) ((e p : E8PowLattice (k + 1)) : EuclideanSpace ℝ (Fin (k + 1) × Fin 8)) =
          complexGaussianTerm (τ : ℂ) (p.1 : EuclideanSpace ℝ (Fin 8)) *
          complexGaussianTerm (τ : ℂ) (p.2 : EuclideanSpace ℝ (Fin k × Fin 8)) := by
      intro p
      unfold complexGaussianTerm
      rw [← Complex.exp_add]
      congr 1
      have hnorm : ‖((e p : E8PowLattice (k + 1)) : EuclideanSpace ℝ (Fin (k + 1) × Fin 8))‖ ^ 2 =
          ‖(p.1 : EuclideanSpace ℝ (Fin 8))‖ ^ 2 + ‖(p.2 : EuclideanSpace ℝ (Fin k × Fin 8))‖ ^ 2 := by
        rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
          Fintype.sum_prod_type, Fintype.sum_prod_type, Fin.sum_univ_succ]
        rfl
      rw [hnorm]; push_cast; ring
    have hsum1 := summable_norm_complexGaussianTerm E8Lattice τ.im_pos
    have hsum2 := summable_norm_complexGaussianTerm (E8PowLattice k) τ.im_pos
    have hprod_sum : Summable (fun p : E8Lattice × E8PowLattice k =>
        complexGaussianTerm (τ : ℂ) (p.1 : EuclideanSpace ℝ (Fin 8)) *
        complexGaussianTerm (τ : ℂ) (p.2 : EuclideanSpace ℝ (Fin k × Fin 8))) :=
      ((Summable.mul_of_nonneg hsum1 hsum2 (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)).congr
        fun p => (norm_mul _ _).symm).of_norm
    calc complexLatticeTheta (E8PowLattice (k + 1)) τ
        = ∑' p : E8Lattice × E8PowLattice k,
            complexGaussianTerm (τ : ℂ) ((e p : E8PowLattice (k + 1)) : EuclideanSpace ℝ (Fin (k + 1) × Fin 8)) := by
            unfold complexLatticeTheta complexLatticeThetaFun
            exact (e.tsum_eq _).symm
      _ = ∑' p : E8Lattice × E8PowLattice k,
            complexGaussianTerm (τ : ℂ) (p.1 : EuclideanSpace ℝ (Fin 8)) *
            complexGaussianTerm (τ : ℂ) (p.2 : EuclideanSpace ℝ (Fin k × Fin 8)) :=
            tsum_congr hsplit
      _ = complexLatticeTheta E8Lattice τ * complexLatticeTheta (E8PowLattice k) τ :=
            (hsum1.of_norm.tsum_mul_tsum hsum2.of_norm hprod_sum).symm
      _ = complexLatticeTheta E8Lattice τ * (complexLatticeTheta E8Lattice τ) ^ k := by rw [ih]
      _ = (complexLatticeTheta E8Lattice τ) ^ (k + 1) := (pow_succ' _ _).symm

/-- **CONCRETE WEIGHT-`4k` `SL₂(ℤ)` SLASH-INVARIANCE FOR `Θ_{E₈^k}` (EVERY `k : ℕ`)**:
`Θ_{E₈^k}(S • τ) = τ^{4k} · Θ_{E₈^k}(τ)`. -/
theorem complexLatticeTheta_E8PowLattice_S_smul (k : ℕ) (τ : UpperHalfPlane) :
    complexLatticeTheta (E8PowLattice k) (ModularGroup.S • τ) =
      (τ : ℂ) ^ (4 * k) * complexLatticeTheta (E8PowLattice k) τ := by
  rw [complexLatticeTheta_E8PowLattice, complexLatticeTheta_E8PowLattice,
    complexLatticeTheta_E8Lattice_S_smul, mul_pow, ← pow_mul]

/-- `Θ_{E₈^k}(T • τ) = Θ_{E₈^k}(τ)`. -/
theorem complexLatticeTheta_E8PowLattice_T_smul (k : ℕ) (τ : UpperHalfPlane) :
    complexLatticeTheta (E8PowLattice k) (ModularGroup.T • τ) =
      complexLatticeTheta (E8PowLattice k) τ :=
  complexLatticeTheta_T_smul_of_even (isEvenLattice_E8PowLattice k) τ

/-- **Full `SL₂(ℤ)` Weight-`4k` Slash-Invariance of `Θ_{E₈^k}` for EVERY `k : ℕ` and `γ ∈ SL₂(ℤ)`**! -/
theorem E8PowLattice_slash_SL2Z_invariant (k : ℕ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    SlashAction.map ((4 * k : ℕ) : ℤ) (sl2ZToGL2R γ) (complexLatticeTheta (E8PowLattice k)) =
      complexLatticeTheta (E8PowLattice k) :=
  slash_SL2Z_invariant_of_S_T ((4 * k : ℕ) : ℤ) (complexLatticeTheta (E8PowLattice k))
    (fun τ => by
      rw [complexLatticeTheta_E8PowLattice_S_smul k τ, zpow_natCast])
    (complexLatticeTheta_E8PowLattice_T_smul k) γ

end ComplexModularInversion

/-! ## Section 3: Concrete Mellin Transform of `Θ_L(i t) - 1`, Completed Epstein Zeta Function `Λ_L(s)` & Global Functional Equation -/

section MellinEpsteinZeta

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Epstein Zeta Function** of a lattice `L ⊂ E`:
`Z_L(s) = ∑'_{v ∈ L \ {0}} ‖v‖^{-s}`. -/
def epsteinZeta (L : Submodule ℤ E) (s : ℂ) : ℂ :=
  ∑' v : {v : L // (v : E) ≠ 0}, ((‖(v : E)‖ : ℝ) : ℂ) ^ (-s)

/-- **Completed Epstein Zeta Function** of a lattice `L ⊂ E`:
`Λ_L(s) = π^{-s/2} Γ(s/2) Z_L(s)`. -/
def completedEpsteinZeta (L : Submodule ℤ E) (s : ℂ) : ℂ :=
  (Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2) * epsteinZeta L s

/-- **Upper Mellin Integral** `I_L(s) = ∫_{1}^{∞} (Θ_L(t) - 1) t^{s/2 - 1} dt`
(entire on all of `ℂ` by super-polynomial decay of `Θ_L(t) - 1`). -/
def upperMellinTheta (L : Submodule ℤ E) (s : ℂ) : ℂ :=
  ∫ t in Set.Ioi (1 : ℝ), ((latticeTheta L t - 1 : ℝ) : ℂ) * (t : ℂ) ^ (s / 2 - 1)

/-- **Global Meromorphic Continuation of the Completed Epstein Zeta Function `Λ_L(s)`**:
$$\Lambda_L^{\mathrm{ext}}(s) = \int_1^\infty (\Theta_L(t) - 1)\, t^{s/2 - 1}\, dt
  + \operatorname{covol}(L)^{-1} \int_1^\infty (\Theta_{L^*}(t) - 1)\, t^{(r - s)/2 - 1}\, dt
  + \frac{2 \operatorname{covol}(L)^{-1}}{s - r} - \frac{2}{s}.$$ -/
def completedEpsteinZetaExt (L : Submodule ℤ E) (s : ℂ) : ℂ :=
  upperMellinTheta L s +
    ((covol L : ℝ) : ℂ)⁻¹ * upperMellinTheta (dualLattice L) ((rk L : ℂ) - s) +
    2 * ((covol L : ℝ) : ℂ)⁻¹ / (s - (rk L : ℂ)) -
    2 / s

/-- Every discrete `ℤ`-lattice `L ⊂ E` is countable (via `Module.finBasis ℤ L`). -/
lemma countable_of_discreteTopology (L : Submodule ℤ E) [DiscreteTopology L] :
    Countable L := by
  let f : L → (Fin (Module.finrank ℤ L) → ℤ) := fun v i => (Module.finBasis ℤ L).repr v i
  have hf : Function.Injective f := fun v w h =>
    (Module.finBasis ℤ L).repr.injective (Finsupp.ext (congrFun h))
  exact Function.Injective.countable hf

/-- Splitting out the `v = 0` term from `latticeTheta L t`:
for `t > 0`, `Θ_L(t) - 1 = ∑'_{v ∈ L \ {0}} exp(-π t ‖v‖²)`. -/
lemma latticeTheta_sub_one_eq_tsum_ne_zero (L : Submodule ℤ E) [DiscreteTopology L]
    {t : ℝ} (ht : 0 < t) :
    latticeTheta L t - 1 =
      ∑' v : {v : L // (v : E) ≠ 0}, gaussianTerm t (v : E) := by
  classical
  have hsum := summable_gaussianTerm L ht
  have h1 := hsum.tsum_eq_add_tsum_ite (0 : L)
  unfold latticeTheta
  rw [h1, ZeroMemClass.coe_zero, gaussianTerm_zero, add_sub_cancel_left]
  let S : Set L := {v : L | (v : E) ≠ 0}
  have hind : (fun v : L => if v = 0 then (0 : ℝ) else gaussianTerm t (v : E)) =
      S.indicator (fun v : L => gaussianTerm t (v : E)) := by
    funext v
    by_cases hv : v = 0
    · subst hv
      have hnot : (0 : L) ∉ S := by simp [S]
      rw [if_pos rfl, Set.indicator_of_notMem hnot]
    · have hmem : v ∈ S := by
        change (v : E) ≠ 0
        intro h; exact hv (Subtype.ext h)
      rw [if_neg hv, Set.indicator_of_mem hmem]
  rw [hind, ← tsum_subtype S (fun v : L => gaussianTerm t (v : E))]
  rfl

/-- Single-term complex Mellin integral of `exp(-a t)`:
for `a > 0` and `0 < w.re`,
`∫ t in Ioi 0, exp(-a t) * t^{w - 1} = a^{-w} * Γ(w)`. -/
lemma mellin_exp_neg_mul {a : ℝ} (ha : 0 < a) {w : ℂ} (hw : 0 < w.re) :
    ∫ t in Set.Ioi (0 : ℝ), ((Real.exp (-(a * t)) : ℝ) : ℂ) * (t : ℂ) ^ (w - 1) =
      (a : ℂ) ^ (-w) * Complex.Gamma w := by
  have hG : mellin (fun t : ℝ => (Real.exp (-t) : ℂ)) w = Complex.Gamma w := by
    rw [Complex.Gamma_eq_integral hw]
    unfold mellin Complex.GammaIntegral
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    simp [mul_comm]
  have hscale := mellin_comp_mul_left (fun t : ℝ => (Real.exp (-t) : ℂ)) w ha
  rw [hG, smul_eq_mul] at hscale
  rw [← hscale]
  unfold mellin
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  simp [mul_comm]

lemma continuousAt_ofReal_cpow_const {t : ℝ} (ht : 0 < t) (c : ℂ) :
    ContinuousAt (fun x : ℝ => (x : ℂ) ^ c) t :=
  ((differentiableAt_id (x := (t : ℂ))).cpow_const (Or.inl (by simpa using ht))).continuousAt.comp
    Complex.continuous_ofReal.continuousAt

/-- Single-term real Mellin integral of `exp(-a t)`:
for `a > 0` and `σ > 0`,
`∫ t in Ioi 0, exp(-a t) * t^{σ - 1} = a^{-σ} * Real.Gamma σ`. -/
lemma real_mellin_exp_neg_mul {a σ : ℝ} (ha : 0 < a) (hσ : 0 < σ) :
    ∫ t in Set.Ioi (0 : ℝ), Real.exp (-(a * t)) * t ^ (σ - 1) =
      a ^ (-σ) * Real.Gamma σ := by
  have hC := mellin_exp_neg_mul ha (w := (σ : ℂ)) (by simpa using hσ)
  have hlhs : ∫ t in Set.Ioi (0 : ℝ), ((Real.exp (-(a * t)) : ℝ) : ℂ) * (t : ℂ) ^ ((σ : ℂ) - 1) =
      ((∫ t in Set.Ioi (0 : ℝ), Real.exp (-(a * t)) * t ^ (σ - 1) : ℝ) : ℂ) := by
    calc ∫ t in Set.Ioi (0 : ℝ), ((Real.exp (-(a * t)) : ℝ) : ℂ) * (t : ℂ) ^ ((σ : ℂ) - 1)
        = ∫ t in Set.Ioi (0 : ℝ), ((Real.exp (-(a * t)) * t ^ (σ - 1) : ℝ) : ℂ) := by
            refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
            have ht0 : 0 < t := ht
            rw [Complex.ofReal_mul, Complex.ofReal_cpow ht0.le, Complex.ofReal_sub,
              Complex.ofReal_one]
      _ = ((∫ t in Set.Ioi (0 : ℝ), Real.exp (-(a * t)) * t ^ (σ - 1) : ℝ) : ℂ) :=
            integral_ofReal
  have hrhs : (a : ℂ) ^ (-(σ : ℂ)) * Complex.Gamma (σ : ℂ) =
      ((a ^ (-σ) * Real.Gamma σ : ℝ) : ℂ) := by
    rw [Complex.ofReal_mul, Complex.Gamma_ofReal, Complex.ofReal_cpow ha.le, Complex.ofReal_neg]
  rw [hlhs, hrhs] at hC
  exact Complex.ofReal_injective hC

/-- Integrability of `t ↦ exp(-a t) * t^{σ - 1}` on `Ioi 0` for `a > 0, σ > 0`. -/
lemma integrableOn_exp_neg_mul_rpow {a σ : ℝ} (ha : 0 < a) (hσ : 0 < σ) :
    IntegrableOn (fun t : ℝ => Real.exp (-(a * t)) * t ^ (σ - 1)) (Set.Ioi 0) volume := by
  have hG := Complex.GammaIntegral_convergent (s := (σ : ℂ)) (by simpa using hσ)
  have hreal : IntegrableOn (fun t : ℝ => Real.exp (-t) * t ^ (σ - 1)) (Set.Ioi 0) volume := by
    have h1 : IntegrableOn (fun x : ℝ => (((Real.exp (-x) : ℝ) : ℂ) * (x : ℂ) ^ ((σ : ℂ) - 1)).re)
        (Set.Ioi 0) volume := hG.re
    refine IntegrableOn.congr_fun h1 (fun t ht => ?_) measurableSet_Ioi
    have ht0 : 0 < t := ht
    have hcoe : ((Real.exp (-t) : ℝ) : ℂ) * (t : ℂ) ^ ((σ : ℂ) - 1) =
        ((Real.exp (-t) * t ^ (σ - 1) : ℝ) : ℂ) := by
      rw [Complex.ofReal_mul, Complex.ofReal_cpow ht0.le, Complex.ofReal_sub, Complex.ofReal_one]
    rw [hcoe, Complex.ofReal_re]
  have hcomp : IntegrableOn (fun t : ℝ => Real.exp (-(a * t)) * (a * t) ^ (σ - 1))
      (Set.Ioi 0) volume := by
    have hmul := MeasureTheory.integrableOn_Ioi_comp_mul_left_iff
      (f := fun u : ℝ => Real.exp (-u) * u ^ (σ - 1)) (a := a) (c := 0) ha
    rw [mul_zero] at hmul
    exact hmul.mpr hreal
  have hscaled : IntegrableOn
      (fun t : ℝ => (a ^ (-(σ - 1))) * (Real.exp (-(a * t)) * (a * t) ^ (σ - 1)))
      (Set.Ioi 0) volume := hcomp.const_mul (a ^ (-(σ - 1)))
  refine IntegrableOn.congr_fun hscaled (fun t ht => ?_) measurableSet_Ioi
  have ht0 : 0 < t := ht
  rw [Real.mul_rpow ha.le ht0.le]
  have hc : a ^ (-(σ - 1)) * a ^ (σ - 1) = 1 := by
    rw [← Real.rpow_add ha, neg_add_cancel, Real.rpow_zero]
  calc a ^ (-(σ - 1)) * (Real.exp (-(a * t)) * (a ^ (σ - 1) * t ^ (σ - 1)))
      = (a ^ (-(σ - 1)) * a ^ (σ - 1)) * (Real.exp (-(a * t)) * t ^ (σ - 1)) := by ring
    _ = Real.exp (-(a * t)) * t ^ (σ - 1) := by rw [hc, one_mul]

/-- Super-polynomial decay in `IsBigO` form at `atTop`:
for every discrete lattice `L` and EVERY `a : ℝ`, `Θ_L(t) - 1 = O(t^{-a})` as `t → ∞`. -/
lemma isBigO_latticeTheta_sub_one_atTop (L : Submodule ℤ E) [DiscreteTopology L] (a : ℝ) :
    (fun t : ℝ => ((latticeTheta L t - 1 : ℝ) : ℂ)) =O[atTop] fun t : ℝ => t ^ (-a) := by
  let m : ℕ := ⌈max a 0⌉₊
  have hm_ge : a ≤ (m : ℝ) := (le_max_left a 0).trans (Nat.le_ceil (max a 0))
  have hdec := latticeTheta_rapid_decay L m
  have hev : ∀ᶠ t : ℝ in atTop, ‖t ^ m * (latticeTheta L t - 1)‖ ≤ 1 := by
    have h1 := hdec.eventually (Metric.ball_mem_nhds (0 : ℝ) zero_lt_one)
    filter_upwards [h1] with t ht
    simpa [Metric.mem_ball, dist_zero_right] using ht.le
  rw [Asymptotics.isBigO_iff]
  refine ⟨1, ?_⟩
  filter_upwards [hev, eventually_ge_atTop (1 : ℝ)] with t ht ht1
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht1
  have hnn : 0 ≤ latticeTheta L t - 1 := sub_nonneg.mpr (one_le_latticeTheta L ht0)
  have htm_pos : 0 < t ^ m := pow_pos ht0 m
  have hbound : latticeTheta L t - 1 ≤ t ^ (-(m : ℝ)) := by
    rw [Real.norm_of_nonneg (mul_nonneg htm_pos.le hnn)] at ht
    rw [Real.rpow_neg ht0.le, Real.rpow_natCast, ← one_div, le_div_iff₀' htm_pos]
    exact ht
  have hrpow_le : t ^ (-(m : ℝ)) ≤ t ^ (-a) :=
    Real.rpow_le_rpow_of_exponent_le ht1 (neg_le_neg hm_ge)
  rw [Complex.norm_real, Real.norm_of_nonneg hnn, Real.norm_of_nonneg (Real.rpow_nonneg ht0.le _),
    one_mul]
  exact hbound.trans hrpow_le

/-- Dyadic-shell upper bound in `IsBigO` form near `0⁺`:
for every discrete lattice `L`, `Θ_L(t) - 1 = O(t^{-rk L / 2})` as `t → 0⁺`. -/
lemma isBigO_latticeTheta_sub_one_zero (L : Submodule ℤ E) [DiscreteTopology L] :
    (fun t : ℝ => ((latticeTheta L t - 1 : ℝ) : ℂ)) =O[nhdsWithin 0 (Set.Ioi 0)]
      fun t : ℝ => t ^ (-((rk L : ℝ) / 2)) := by
  by_cases hL0 : L = ⊥
  · subst hL0
    have hzero : (fun t : ℝ => ((latticeTheta (⊥ : Submodule ℤ E) t - 1 : ℝ) : ℂ)) = 0 := by
      funext t; simp [latticeTheta_bot]
    rw [hzero]
    exact Asymptotics.isBigO_zero _ _
  · let r := rk L
    let lam := RHDirect.Stage2SiegelReduction.lambda1 L
    have hlam : 0 < lam := RHDirect.Stage2SiegelReduction.lambda1_pos L hL0
    let C : ℝ := thetaConst r * (1 + lam ^ (-(r : ℝ)))
    rw [Asymptotics.isBigO_iff]
    refine ⟨C, ?_⟩
    have hmem : Set.Ioo (0 : ℝ) 1 ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) :=
      Ioo_mem_nhdsGT zero_lt_one
    filter_upwards [hmem] with t ht
    have ht0 : 0 < t := ht.1
    have ht1 : t ≤ 1 := ht.2.le
    have hnn : 0 ≤ latticeTheta L t - 1 := sub_nonneg.mpr (one_le_latticeTheta L ht0)
    have hdyad := latticeTheta_le_dyadic_bound L hL0 ht0
    have hexp1 : Real.exp (-(Real.pi / 2) * t * lam ^ 2) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by
        have h1 : 0 ≤ (Real.pi / 2) * t * lam ^ 2 := by positivity
        linarith)
    have htr_ge : 1 ≤ t ^ (-((r : ℝ) / 2)) := by
      rw [Real.rpow_neg ht0.le, one_le_inv₀ (Real.rpow_pos_of_pos ht0 _)]
      exact Real.rpow_le_one ht0.le ht1 (by positivity)
    have hsplit : (Real.sqrt t * lam) ^ (-(r : ℝ)) = lam ^ (-(r : ℝ)) * t ^ (-((r : ℝ) / 2)) := by
      rw [Real.mul_rpow (Real.sqrt_nonneg t) hlam.le, Real.sqrt_eq_rpow,
        ← Real.rpow_mul ht0.le, mul_comm]
      congr 2; ring
    have hinner : 1 + (Real.sqrt t * lam) ^ (-(r : ℝ)) ≤
        (1 + lam ^ (-(r : ℝ))) * t ^ (-((r : ℝ) / 2)) := by
      rw [hsplit]
      have hlam_nn : 0 ≤ lam ^ (-(r : ℝ)) := Real.rpow_nonneg hlam.le _
      nlinarith
    have hfac_nn : 0 ≤ thetaConst r * (1 + (Real.sqrt t * lam) ^ (-(r : ℝ))) :=
      mul_nonneg (thetaConst_pos r).le (add_nonneg zero_le_one (Real.rpow_nonneg (by positivity) _))
    have hbound : latticeTheta L t - 1 ≤ C * t ^ (-((r : ℝ) / 2)) := by
      calc latticeTheta L t - 1
          ≤ thetaConst r * (1 + (Real.sqrt t * lam) ^ (-(r : ℝ))) *
              Real.exp (-(Real.pi / 2) * t * lam ^ 2) := by linarith
        _ ≤ thetaConst r * (1 + (Real.sqrt t * lam) ^ (-(r : ℝ))) * 1 :=
              mul_le_mul_of_nonneg_left hexp1 hfac_nn
        _ = thetaConst r * (1 + (Real.sqrt t * lam) ^ (-(r : ℝ))) := mul_one _
        _ ≤ thetaConst r * ((1 + lam ^ (-(r : ℝ))) * t ^ (-((r : ℝ) / 2))) :=
              mul_le_mul_of_nonneg_left hinner (thetaConst_pos r).le
        _ = C * t ^ (-((r : ℝ) / 2)) := by dsimp only [C]; ring
    rw [Complex.norm_real, Real.norm_of_nonneg hnn,
      Real.norm_of_nonneg (Real.rpow_nonneg ht0.le _)]
    exact hbound

/-- Mellin convergence of `Θ_L(t) - 1` at `s / 2` for every discrete lattice `L` and `Re(s) > rk L`. -/
theorem mellinConvergent_latticeTheta_sub_one (L : Submodule ℤ E) [DiscreteTopology L]
    {s : ℂ} (hs : (rk L : ℝ) < s.re) :
    MellinConvergent (fun t : ℝ => ((latticeTheta L t - 1 : ℝ) : ℂ)) (s / 2) := by
  have hloc : LocallyIntegrableOn (fun t : ℝ => ((latticeTheta L t - 1 : ℝ) : ℂ))
      (Set.Ioi 0) volume := by
    have hcont : ContinuousOn (fun t : ℝ => ((latticeTheta L t - 1 : ℝ) : ℂ)) (Set.Ioi 0) :=
      Complex.continuous_ofReal.comp_continuousOn ((continuousOn_latticeTheta L).sub continuousOn_const)
    exact hcont.locallyIntegrableOn measurableSet_Ioi
  refine mellinConvergent_of_isBigO_rpow hloc
    (isBigO_latticeTheta_sub_one_atTop L (s.re / 2 + 1)) ?_
    (isBigO_latticeTheta_sub_one_zero L) ?_
  · have hre : (s / 2).re = s.re / 2 := by simp
    linarith
  · have hre : (s / 2).re = s.re / 2 := by simp
    linarith

/-- Real integrability of `(Θ_L(t) - 1) * t^{σ/2 - 1}` on `Ioi 0` for `σ > rk L`. -/
lemma integrableOn_latticeTheta_sub_one_real (L : Submodule ℤ E) [DiscreteTopology L]
    {σ : ℝ} (hσ : (rk L : ℝ) < σ) :
    IntegrableOn (fun t : ℝ => (latticeTheta L t - 1) * t ^ (σ / 2 - 1)) (Set.Ioi 0) volume := by
  have hC : IntegrableOn
      (fun t : ℝ => ((t : ℂ) ^ ((σ : ℂ) / 2 - 1) * ((latticeTheta L t - 1 : ℝ) : ℂ)).re)
      (Set.Ioi 0) volume :=
    (mellinConvergent_latticeTheta_sub_one L (s := (σ : ℂ)) (by simpa using hσ)).re
  refine IntegrableOn.congr_fun hC (fun t ht => ?_) measurableSet_Ioi
  have ht0 : 0 < t := ht
  have hpow : (t : ℂ) ^ ((σ : ℂ) / 2 - 1) = ((t ^ (σ / 2 - 1) : ℝ) : ℂ) := by
    rw [show ((σ : ℂ) / 2 - 1) = ((σ / 2 - 1 : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cpow ht0.le]
  rw [hpow, ← Complex.ofReal_mul, Complex.ofReal_re, mul_comm]

/-- Key Tonelli lintegral finiteness lemma:
for every discrete lattice `L` and `s` with `(rk L : ℝ) < s.re`,
`∑'_{v ≠ 0} ∫⁻_{t ∈ Ioi 0} ‖exp(-π t ‖v‖²) * t^{s/2 - 1}‖ₑ dt < ⊤`,
and each term equals `ENNReal.ofReal (π^{-s.re/2} Γ(s.re/2) ‖v‖^{-s.re})`. -/
lemma tsum_lintegral_epstein_ne_top (L : Submodule ℤ E) [DiscreteTopology L]
    {s : ℂ} (hs : (rk L : ℝ) < s.re) :
    (∑' v : {v : L // (v : E) ≠ 0},
      ∫⁻ t in Set.Ioi (0 : ℝ),
        ‖((gaussianTerm t (v : E) : ℝ) : ℂ) * (t : ℂ) ^ (s / 2 - 1)‖ₑ) ≠ ⊤ ∧
    (∀ v : {v : L // (v : E) ≠ 0},
      (∫⁻ t in Set.Ioi (0 : ℝ),
        ‖((gaussianTerm t (v : E) : ℝ) : ℂ) * (t : ℂ) ^ (s / 2 - 1)‖ₑ) =
      ENNReal.ofReal (Real.pi ^ (-s.re / 2) * Real.Gamma (s.re / 2) * ‖(v : E)‖ ^ (-s.re))) := by
  have : Countable L := countable_of_discreteTopology L
  have : Countable {v : L // (v : E) ≠ 0} := inferInstance
  have hs_pos : 0 < s.re := lt_of_le_of_lt (Nat.cast_nonneg (rk L)) hs
  have hs2_pos : 0 < s.re / 2 := half_pos hs_pos
  have hterm_eq : ∀ v : {v : L // (v : E) ≠ 0},
      (∫⁻ t in Set.Ioi (0 : ℝ),
        ‖((gaussianTerm t (v : E) : ℝ) : ℂ) * (t : ℂ) ^ (s / 2 - 1)‖ₑ) =
      ENNReal.ofReal (Real.pi ^ (-s.re / 2) * Real.Gamma (s.re / 2) * ‖(v : E)‖ ^ (-s.re)) := by
    intro v
    have hv_pos : 0 < ‖(v : E)‖ := norm_pos_iff.mpr v.2
    have ha_pos : 0 < Real.pi * ‖(v : E)‖ ^ 2 := mul_pos Real.pi_pos (sq_pos_of_pos hv_pos)
    have hlhs_congr : (∫⁻ t in Set.Ioi (0 : ℝ),
        ‖((gaussianTerm t (v : E) : ℝ) : ℂ) * (t : ℂ) ^ (s / 2 - 1)‖ₑ) =
        ∫⁻ t in Set.Ioi (0 : ℝ),
          ENNReal.ofReal (Real.exp (-(Real.pi * ‖(v : E)‖ ^ 2 * t)) * t ^ (s.re / 2 - 1)) := by
      refine setLIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
      have ht0 : 0 < t := ht
      rw [enorm_eq_nnnorm, ENNReal.ofReal_eq_coe_nnreal (by positivity)]
      congr 1
      apply Subtype.ext
      change ‖((gaussianTerm t (v : E) : ℝ) : ℂ) * (t : ℂ) ^ (s / 2 - 1)‖ = _
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (gaussianTerm_nonneg t (v : E)),
        Complex.norm_cpow_eq_rpow_re_of_pos ht0]
      have hre : (s / 2 - 1).re = s.re / 2 - 1 := by simp
      rw [hre]
      unfold gaussianTerm
      congr 2; ring
    rw [hlhs_congr]
    have hint := integrableOn_exp_neg_mul_rpow ha_pos hs2_pos
    have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioi (0 : ℝ))]
        fun t : ℝ => Real.exp (-(Real.pi * ‖(v : E)‖ ^ 2 * t)) * t ^ (s.re / 2 - 1) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht0 : 0 < t := ht
      exact mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg ht0.le _)
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint hnn,
      real_mellin_exp_neg_mul ha_pos hs2_pos]
    congr 1
    rw [Real.mul_rpow Real.pi_pos.le (sq_nonneg _), ← Real.rpow_natCast ‖(v : E)‖ 2,
      ← Real.rpow_mul hv_pos.le]
    have hexp : ((2 : ℕ) : ℝ) * -(s.re / 2) = -s.re := by push_cast; ring
    rw [hexp]
    have hneg : -(s.re / 2) = -s.re / 2 := by ring
    rw [hneg]; ring
  refine ⟨?_, hterm_eq⟩
  have hmeas : ∀ v : {v : L // (v : E) ≠ 0},
      AEMeasurable (fun t : ℝ =>
        ‖((gaussianTerm t (v : E) : ℝ) : ℂ) * (t : ℂ) ^ (s / 2 - 1)‖ₑ)
        (volume.restrict (Set.Ioi (0 : ℝ))) := by
    intro v
    refine ContinuousOn.aemeasurable ?_ measurableSet_Ioi
    refine Continuous.comp_continuousOn continuous_enorm ?_
    refine ContinuousOn.mul ?_ ?_
    · refine Complex.continuous_ofReal.comp_continuousOn ?_
      unfold gaussianTerm
      exact (Real.continuous_exp.comp (by fun_prop)).continuousOn
    · intro t ht
      have ht0 : 0 < t := ht
      exact (continuousAt_ofReal_cpow_const ht0 (s / 2 - 1)).continuousWithinAt
  rw [← MeasureTheory.lintegral_tsum hmeas]
  have hsum_eq : (∫⁻ t in Set.Ioi (0 : ℝ),
      ∑' v : {v : L // (v : E) ≠ 0},
        ‖((gaussianTerm t (v : E) : ℝ) : ℂ) * (t : ℂ) ^ (s / 2 - 1)‖ₑ) =
      ∫⁻ t in Set.Ioi (0 : ℝ),
        ENNReal.ofReal ((latticeTheta L t - 1) * t ^ (s.re / 2 - 1)) := by
    refine setLIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht0 : 0 < t := ht
    have hre : (s / 2 - 1).re = s.re / 2 - 1 := by simp
    have hterm_enorm : ∀ v : {v : L // (v : E) ≠ 0},
        ‖((gaussianTerm t (v : E) : ℝ) : ℂ) * (t : ℂ) ^ (s / 2 - 1)‖ₑ =
          ENNReal.ofReal (gaussianTerm t (v : E) * t ^ (s.re / 2 - 1)) := by
      intro v
      have hnn_v : 0 ≤ gaussianTerm t (v : E) * t ^ (s.re / 2 - 1) :=
        mul_nonneg (gaussianTerm_nonneg t _) (Real.rpow_nonneg ht0.le _)
      rw [enorm_eq_nnnorm, ENNReal.ofReal_eq_coe_nnreal hnn_v]
      congr 1; apply Subtype.ext
      change ‖((gaussianTerm t (v : E) : ℝ) : ℂ) * (t : ℂ) ^ (s / 2 - 1)‖ = _
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (gaussianTerm_nonneg t (v : E)),
        Complex.norm_cpow_eq_rpow_re_of_pos ht0, hre]
      rfl
    simp_rw [hterm_enorm]
    have hsum_ne : Summable (fun v : {v : L // (v : E) ≠ 0} =>
        gaussianTerm t (v : E) * t ^ (s.re / 2 - 1)) :=
      ((summable_gaussianTerm L ht0).subtype _).mul_right _
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun v => mul_nonneg (gaussianTerm_nonneg t _)
      (Real.rpow_nonneg ht0.le _)) hsum_ne, tsum_mul_right,
      ← latticeTheta_sub_one_eq_tsum_ne_zero L ht0]
  rw [hsum_eq]
  have hint := integrableOn_latticeTheta_sub_one_real L hs
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioi (0 : ℝ))]
      fun t : ℝ => (latticeTheta L t - 1) * t ^ (s.re / 2 - 1) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := ht
    exact mul_nonneg (sub_nonneg.mpr (one_le_latticeTheta L ht0)) (Real.rpow_nonneg ht0.le _)
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint hnn]
  exact ENNReal.ofReal_ne_top

/-- **Unconditional Absolute Summability of the Epstein Zeta Series on `Re(s) > rk L`**:
for every discrete `ℤ`-lattice `L ⊂ E` and every `s : ℂ` with `(rk L : ℝ) < s.re`,
`v ↦ ‖(‖v‖ : ℂ)^(-s)‖` is summable over `L \ {0}`! -/
theorem summable_norm_epsteinZeta (L : Submodule ℤ E) [DiscreteTopology L]
    {s : ℂ} (hs : (rk L : ℝ) < s.re) :
    Summable (fun v : {v : L // (v : E) ≠ 0} => ‖((‖(v : E)‖ : ℝ) : ℂ) ^ (-s)‖) := by
  obtain ⟨hne_top, hterm⟩ := tsum_lintegral_epstein_ne_top L hs
  simp_rw [hterm] at hne_top
  have hsum_scaled := ENNReal.summable_toReal hne_top
  have hs_pos : 0 < s.re := lt_of_le_of_lt (Nat.cast_nonneg (rk L)) hs
  have hs2_pos : 0 < s.re / 2 := half_pos hs_pos
  have hc_pos : 0 < Real.pi ^ (-s.re / 2) * Real.Gamma (s.re / 2) :=
    mul_pos (Real.rpow_pos_of_pos Real.pi_pos _) (Real.Gamma_pos_of_pos hs2_pos)
  have hsum_scaled' : Summable (fun v : {v : L // (v : E) ≠ 0} =>
      (Real.pi ^ (-s.re / 2) * Real.Gamma (s.re / 2)) * ‖(v : E)‖ ^ (-s.re)) := by
    refine hsum_scaled.congr fun v => ?_
    exact ENNReal.toReal_ofReal (mul_nonneg hc_pos.le (Real.rpow_nonneg (norm_nonneg _) _))
  have hsum_rpow : Summable (fun v : {v : L // (v : E) ≠ 0} => ‖(v : E)‖ ^ (-s.re)) := by
    have h := hsum_scaled'.mul_left (Real.pi ^ (-s.re / 2) * Real.Gamma (s.re / 2))⁻¹
    refine h.congr fun v => ?_
    rw [← mul_assoc, inv_mul_cancel₀ hc_pos.ne', one_mul]
  refine hsum_rpow.congr fun v => ?_
  have hv_pos : 0 < ‖(v : E)‖ := norm_pos_iff.mpr v.2
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hv_pos, Complex.neg_re]

/-- **Unconditional Summability of the Epstein Zeta Function `epsteinZeta L s` on `Re(s) > rk L`**. -/
theorem summable_epsteinZeta (L : Submodule ℤ E) [DiscreteTopology L]
    {s : ℂ} (hs : (rk L : ℝ) < s.re) :
    Summable (fun v : {v : L // (v : E) ≠ 0} => ((‖(v : E)‖ : ℝ) : ℂ) ^ (-s)) :=
  (summable_norm_epsteinZeta L hs).of_norm

/-- **EXACT MELLIN INTEGRAL IDENTITY ON `Re(s) > rk L`**:
for EVERY discrete `ℤ`-lattice `L ⊂ E` and EVERY `s : ℂ` with `(rk L : ℝ) < s.re`,
$$\int_0^\infty (\Theta_L(t) - 1)\, t^{s/2 - 1}\, dt = \pi^{-s/2} \Gamma(s/2) Z_L(s) = \Lambda_L(s).$$ -/
theorem mellin_latticeTheta_sub_one_eq_completedEpsteinZeta (L : Submodule ℤ E) [DiscreteTopology L]
    {s : ℂ} (hs : (rk L : ℝ) < s.re) :
    ∫ t in Set.Ioi (0 : ℝ), ((latticeTheta L t - 1 : ℝ) : ℂ) * (t : ℂ) ^ (s / 2 - 1) =
      completedEpsteinZeta L s := by
  have : Countable L := countable_of_discreteTopology L
  have : Countable {v : L // (v : E) ≠ 0} := inferInstance
  have hs_pos : 0 < s.re := lt_of_le_of_lt (Nat.cast_nonneg (rk L)) hs
  have hs2_pos : 0 < (s / 2).re := by simp [half_pos hs_pos]
  obtain ⟨hne_top, _⟩ := tsum_lintegral_epstein_ne_top L hs
  have haes : ∀ v : {v : L // (v : E) ≠ 0},
      AEStronglyMeasurable
        (fun t : ℝ => ((gaussianTerm t (v : E) : ℝ) : ℂ) * (t : ℂ) ^ (s / 2 - 1))
        (volume.restrict (Set.Ioi (0 : ℝ))) := by
    intro v
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    refine ContinuousOn.mul ?_ ?_
    · refine Complex.continuous_ofReal.comp_continuousOn ?_
      unfold gaussianTerm
      exact (Real.continuous_exp.comp (by fun_prop)).continuousOn
    · intro t ht
      have ht0 : 0 < t := ht
      exact (continuousAt_ofReal_cpow_const ht0 (s / 2 - 1)).continuousWithinAt
  have hcongr : (∫ t in Set.Ioi (0 : ℝ),
      ((latticeTheta L t - 1 : ℝ) : ℂ) * (t : ℂ) ^ (s / 2 - 1)) =
      ∫ t in Set.Ioi (0 : ℝ),
        ∑' v : {v : L // (v : E) ≠ 0},
          ((gaussianTerm t (v : E) : ℝ) : ℂ) * (t : ℂ) ^ (s / 2 - 1) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht0 : 0 < t := ht
    rw [latticeTheta_sub_one_eq_tsum_ne_zero L ht0, Complex.ofReal_tsum, tsum_mul_right]
  rw [hcongr, MeasureTheory.integral_tsum haes hne_top]
  have hterm : ∀ v : {v : L // (v : E) ≠ 0},
      (∫ t in Set.Ioi (0 : ℝ),
        ((gaussianTerm t (v : E) : ℝ) : ℂ) * (t : ℂ) ^ (s / 2 - 1)) =
        (Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2) * ((‖(v : E)‖ : ℝ) : ℂ) ^ (-s) := by
    intro v
    have hv_pos : 0 < ‖(v : E)‖ := norm_pos_iff.mpr v.2
    have ha_pos : 0 < Real.pi * ‖(v : E)‖ ^ 2 := mul_pos Real.pi_pos (sq_pos_of_pos hv_pos)
    have hfun : (fun t : ℝ => ((gaussianTerm t (v : E) : ℝ) : ℂ) * (t : ℂ) ^ (s / 2 - 1)) =
        fun t : ℝ => ((Real.exp (-(Real.pi * ‖(v : E)‖ ^ 2 * t)) : ℝ) : ℂ) * (t : ℂ) ^ (s / 2 - 1) := by
      funext t; unfold gaussianTerm; congr 3; ring
    rw [hfun, mellin_exp_neg_mul ha_pos hs2_pos]
    have hsplit : ((Real.pi * ‖(v : E)‖ ^ 2 : ℝ) : ℂ) ^ (-(s / 2)) =
        (Real.pi : ℂ) ^ (-s / 2) * ((‖(v : E)‖ : ℝ) : ℂ) ^ (-s) := by
      rw [Complex.ofReal_mul, cpow_mul_ofReal_pos (by simpa using Real.pi_pos) (sq_pos_of_pos hv_pos)]
      have hneg : -(s / 2) = -s / 2 := by ring
      rw [hneg]
      congr 1
      rw [Complex.ofReal_pow, ← Complex.cpow_natCast ((‖(v : E)‖ : ℝ) : ℂ) 2,
        ← Complex.cpow_mul (x := ((‖(v : E)‖ : ℝ) : ℂ)) (y := ((2 : ℕ) : ℂ)) (z := -s / 2)]
      · congr 1; push_cast; ring
      · rw [← Complex.ofReal_log hv_pos.le]
        simp [Real.pi_pos]
      · rw [← Complex.ofReal_log hv_pos.le]
        simp [Real.pi_pos.le]
    rw [hsplit]; ring
  simp_rw [hterm]
  rw [tsum_mul_left]
  rfl

/-- **Entirety of the Upper Mellin Transform `upperMellinTheta L`**:
for every discrete lattice `L ⊂ E`, `s ↦ ∫_{1}^{∞} (Θ_L(t) - 1) t^{s/2 - 1} dt`
is **entire** (`Differentiable ℂ`) on all of `ℂ`! -/
theorem differentiable_upperMellinTheta (L : Submodule ℤ E) [DiscreteTopology L] :
    Differentiable ℂ (upperMellinTheta L) := by
  let f : ℝ → ℂ := (Set.Ioi (1 : ℝ)).indicator (fun t => ((latticeTheta L t - 1 : ℝ) : ℂ))
  have hmellin_eq : upperMellinTheta L = fun s : ℂ => mellin f (s / 2) := by
    funext s
    unfold upperMellinTheta mellin
    have hind : (fun t : ℝ => (t : ℂ) ^ (s / 2 - 1) • f t) =
        (Set.Ioi (1 : ℝ)).indicator (fun t => ((latticeTheta L t - 1 : ℝ) : ℂ) * (t : ℂ) ^ (s / 2 - 1)) := by
      funext t
      by_cases ht : t ∈ Set.Ioi (1 : ℝ)
      · dsimp only [f]
        rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht, smul_eq_mul, mul_comm]
      · dsimp only [f]
        rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht, smul_zero]
    rw [hind, MeasureTheory.setIntegral_indicator measurableSet_Ioi,
      Set.inter_eq_right.mpr (Set.Ioi_subset_Ioi zero_le_one)]
  rw [hmellin_eq]
  have hloc : LocallyIntegrableOn f (Set.Ioi 0) volume := by
    have hcont : ContinuousOn (fun t : ℝ => ((latticeTheta L t - 1 : ℝ) : ℂ)) (Set.Ioi 0) :=
      Complex.continuous_ofReal.comp_continuousOn ((continuousOn_latticeTheta L).sub continuousOn_const)
    have hloc_g : LocallyIntegrableOn (fun t : ℝ => ((latticeTheta L t - 1 : ℝ) : ℂ))
        (Set.Ioi 0) volume := hcont.locallyIntegrableOn measurableSet_Ioi
    intro x hx
    obtain ⟨u, hu, hint⟩ := hloc_g x hx
    exact ⟨u, hu, hint.indicator measurableSet_Ioi⟩
  intro s
  have hdiff_mellin : DifferentiableAt ℂ (mellin f) (s / 2) := by
    refine mellin_differentiableAt_of_isBigO_rpow hloc (a := s.re / 2 + 1) (b := s.re / 2 - 1) ?_ ?_ ?_ ?_
    · have htop := isBigO_latticeTheta_sub_one_atTop L (s.re / 2 + 1)
      refine htop.congr' ?_ EventuallyEq.rfl
      filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
      have hmem : t ∈ Set.Ioi (1 : ℝ) := ht
      exact (Set.indicator_of_mem hmem (fun u : ℝ => ((latticeTheta L u - 1 : ℝ) : ℂ))).symm
    · have hre : (s / 2).re = s.re / 2 := by simp
      linarith
    · refine (Asymptotics.isBigO_zero (fun t : ℝ => t ^ (-(s.re / 2 - 1)))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))).congr' ?_ EventuallyEq.rfl
      filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with t ht
      have hnot : t ∉ Set.Ioi (1 : ℝ) := not_lt.mpr ht.2.le
      change (0 : ℂ) = (Set.Ioi (1 : ℝ)).indicator (fun t => ((latticeTheta L t - 1 : ℝ) : ℂ)) t
      exact (Set.indicator_of_notMem hnot _).symm
    · have hre : (s / 2).re = s.re / 2 := by simp
      linarith
  have hdiv : DifferentiableAt ℂ (fun z : ℂ => z / 2) s := differentiableAt_id.div_const (2 : ℂ)
  exact DifferentiableAt.comp (f := fun z : ℂ => z / 2) (g := mellin f) s hdiff_mellin hdiv

/-- **Holomorphicity of `completedEpsteinZetaExt L` on `ℂ \ {0, rk L}`**:
for any discrete lattice `L` whose dual `L*` is also discrete, `completedEpsteinZetaExt L`
is holomorphic at every `s ≠ 0` and `s ≠ rk L`. -/
theorem differentiableAt_completedEpsteinZetaExt (L : Submodule ℤ E) [DiscreteTopology L]
    [DiscreteTopology (dualLattice L)] {s : ℂ} (hs0 : s ≠ 0) (hsr : s ≠ (rk L : ℂ)) :
    DifferentiableAt ℂ (completedEpsteinZetaExt L) s := by
  unfold completedEpsteinZetaExt
  have h1 : DifferentiableAt ℂ (upperMellinTheta L) s :=
    differentiable_upperMellinTheta L s
  have h2 : DifferentiableAt ℂ
      (fun z : ℂ => ((covol L : ℝ) : ℂ)⁻¹ * upperMellinTheta (dualLattice L) ((rk L : ℂ) - z)) s :=
    (differentiableAt_const _).mul
      ((differentiable_upperMellinTheta (dualLattice L) _).comp s
        ((differentiableAt_const _).sub differentiableAt_id))
  have h3 : DifferentiableAt ℂ (fun z : ℂ => 2 * ((covol L : ℝ) : ℂ)⁻¹ / (z - (rk L : ℂ))) s :=
    (differentiableAt_const _).div (differentiableAt_id.sub (differentiableAt_const _))
      (sub_ne_zero.mpr hsr)
  have h4 : DifferentiableAt ℂ (fun z : ℂ => (2 : ℂ) / z) s :=
    (differentiableAt_const _).div differentiableAt_id hs0
  exact ((h1.add h2).add h3).sub h4

/-- `completedEpsteinZetaExt L` is holomorphic on `ℂ \ {0, rk L}`. -/
theorem differentiableOn_completedEpsteinZetaExt (L : Submodule ℤ E) [DiscreteTopology L]
    [DiscreteTopology (dualLattice L)] :
    DifferentiableOn ℂ (completedEpsteinZetaExt L) ({(0 : ℂ), (rk L : ℂ)}ᶜ) := by
  intro s hs
  have hs0 : s ≠ 0 := fun h => hs (by simp [h])
  have hsr : s ≠ (rk L : ℂ) := fun h => hs (by simp [h])
  exact (differentiableAt_completedEpsteinZetaExt L hs0 hsr).differentiableWithinAt

/-- **Exact Simple Pole Residue `-2` at `s = 0`** for every nonzero lattice `L ≠ ⊥`:
`lim_{s → 0, s ≠ 0} s * completedEpsteinZetaExt L s = -2`. -/
theorem completedEpsteinZetaExt_residue_zero (L : Submodule ℤ E) [DiscreteTopology L]
    [DiscreteTopology (dualLattice L)] (hL0 : L ≠ ⊥) :
    Tendsto (fun s : ℂ => s * completedEpsteinZetaExt L s)
      (nhdsWithin 0 {(0 : ℂ)}ᶜ) (nhds (-2)) := by
  have hr_pos : 0 < rk L := rk_pos_of_ne_bot L hL0
  have hr_ne : (0 : ℂ) - (rk L : ℂ) ≠ 0 := by
    simp [Nat.cast_ne_zero.mpr hr_pos.ne']
  let g : ℂ → ℂ := fun s =>
    s * (upperMellinTheta L s +
      ((covol L : ℝ) : ℂ)⁻¹ * upperMellinTheta (dualLattice L) ((rk L : ℂ) - s) +
      2 * ((covol L : ℝ) : ℂ)⁻¹ / (s - (rk L : ℂ))) - 2
  have hg_cont : ContinuousAt g 0 := by
    have h1 : ContinuousAt (upperMellinTheta L) 0 := (differentiable_upperMellinTheta L 0).continuousAt
    have h2 : ContinuousAt (fun z : ℂ =>
        ((covol L : ℝ) : ℂ)⁻¹ * upperMellinTheta (dualLattice L) ((rk L : ℂ) - z)) 0 :=
      continuousAt_const.mul
        ((differentiable_upperMellinTheta (dualLattice L) _).continuousAt.comp
          (continuousAt_const.sub continuousAt_id))
    have h3 : ContinuousAt (fun z : ℂ => 2 * ((covol L : ℝ) : ℂ)⁻¹ / (z - (rk L : ℂ))) 0 :=
      continuousAt_const.div (continuousAt_id.sub continuousAt_const) hr_ne
    exact (continuousAt_id.mul ((h1.add h2).add h3)).sub continuousAt_const
  have hg0 : g 0 = -2 := by simp [g]
  have hlim : Tendsto g (nhdsWithin 0 {(0 : ℂ)}ᶜ) (nhds (-2)) := by
    rw [← hg0]
    exact hg_cont.tendsto.mono_left nhdsWithin_le_nhds
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs0 : s ≠ 0 := hs
  dsimp only [g, completedEpsteinZetaExt]
  field_simp [hs0]

/-- **Exact Simple Pole Residue `+2 covol(L)⁻¹` at `s = rk L`** for every nonzero lattice `L ≠ ⊥`:
`lim_{s → rk L, s ≠ rk L} (s - rk L) * completedEpsteinZetaExt L s = 2 * covol(L)⁻¹`. -/
theorem completedEpsteinZetaExt_residue_rk (L : Submodule ℤ E) [DiscreteTopology L]
    [DiscreteTopology (dualLattice L)] (hL0 : L ≠ ⊥) :
    Tendsto (fun s : ℂ => (s - (rk L : ℂ)) * completedEpsteinZetaExt L s)
      (nhdsWithin (rk L : ℂ) {(rk L : ℂ)}ᶜ) (nhds (2 * ((covol L : ℝ) : ℂ)⁻¹)) := by
  have hr_pos : 0 < rk L := rk_pos_of_ne_bot L hL0
  have hr_ne : (rk L : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hr_pos.ne'
  let g : ℂ → ℂ := fun s =>
    (s - (rk L : ℂ)) * (upperMellinTheta L s +
      ((covol L : ℝ) : ℂ)⁻¹ * upperMellinTheta (dualLattice L) ((rk L : ℂ) - s) -
      2 / s) + 2 * ((covol L : ℝ) : ℂ)⁻¹
  have hg_cont : ContinuousAt g (rk L : ℂ) := by
    have h1 : ContinuousAt (upperMellinTheta L) (rk L : ℂ) :=
      (differentiable_upperMellinTheta L _).continuousAt
    have h2 : ContinuousAt (fun z : ℂ =>
        ((covol L : ℝ) : ℂ)⁻¹ * upperMellinTheta (dualLattice L) ((rk L : ℂ) - z)) (rk L : ℂ) :=
      continuousAt_const.mul
        ((differentiable_upperMellinTheta (dualLattice L) _).continuousAt.comp
          (continuousAt_const.sub continuousAt_id))
    have h3 : ContinuousAt (fun z : ℂ => (2 : ℂ) / z) (rk L : ℂ) :=
      continuousAt_const.div continuousAt_id hr_ne
    exact ((continuousAt_id.sub continuousAt_const).mul ((h1.add h2).sub h3)).add continuousAt_const
  have hgr : g (rk L : ℂ) = 2 * ((covol L : ℝ) : ℂ)⁻¹ := by simp [g]
  have hlim : Tendsto g (nhdsWithin (rk L : ℂ) {(rk L : ℂ)}ᶜ)
      (nhds (2 * ((covol L : ℝ) : ℂ)⁻¹)) := by
    rw [← hgr]
    exact hg_cont.tendsto.mono_left nhdsWithin_le_nhds
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hsr : s - (rk L : ℂ) ≠ 0 := sub_ne_zero.mpr hs
  dsimp only [g, completedEpsteinZetaExt]
  field_simp [hsr]
  ring

/-- Elementary Mellin power integral on `(0, 1)`:
for every `w : ℂ` with `0 < w.re`, `∫ t in Ioo 0 1, (t : ℂ)^{w - 1} = 1 / w`. -/
lemma integral_Ioo_zero_one_cpow {w : ℂ} (hw : 0 < w.re) :
    ∫ t in Set.Ioo (0 : ℝ) 1, (t : ℂ) ^ (w - 1) = 1 / w := by
  have hw_ne : w ≠ 0 := fun h => by rw [h] at hw; simp at hw
  let h : ℝ → ℂ := (Set.Ioo (0 : ℝ) 1).indicator (fun _ => (1 : ℂ))
  have hinv : mellin h w = mellin (fun t => h t⁻¹) (-w) := by
    have h1 := mellin_comp_inv h (-w)
    rw [neg_neg] at h1
    exact h1.symm
  have hlhs : mellin h w = ∫ t in Set.Ioo (0 : ℝ) 1, (t : ℂ) ^ (w - 1) := by
    unfold mellin
    have heq : (fun t : ℝ => (t : ℂ) ^ (w - 1) • h t) =
        (Set.Ioo (0 : ℝ) 1).indicator (fun t : ℝ => (t : ℂ) ^ (w - 1)) := by
      funext t
      by_cases ht : t ∈ Set.Ioo (0 : ℝ) 1
      · dsimp only [h]; rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht, smul_eq_mul, mul_one]
      · dsimp only [h]; rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht, smul_zero]
    rw [heq, MeasureTheory.setIntegral_indicator measurableSet_Ioo,
      Set.inter_eq_right.mpr Set.Ioo_subset_Ioi_self]
  have hrhs : mellin (fun t => h t⁻¹) (-w) = ∫ t in Set.Ioi (1 : ℝ), (t : ℂ) ^ (-w - 1) := by
    unfold mellin
    have heq : Set.EqOn (fun t : ℝ => (t : ℂ) ^ (-w - 1) • h t⁻¹)
        ((Set.Ioi (1 : ℝ)).indicator (fun t : ℝ => (t : ℂ) ^ (-w - 1))) (Set.Ioi 0) := by
      intro t ht
      have ht0 : 0 < t := ht
      by_cases ht1 : t ∈ Set.Ioi (1 : ℝ)
      · have hmem : t⁻¹ ∈ Set.Ioo (0 : ℝ) 1 := ⟨inv_pos.mpr ht0, inv_lt_one_of_one_lt₀ ht1⟩
        dsimp only [h]
        rw [Set.indicator_of_mem hmem, Set.indicator_of_mem ht1, smul_eq_mul, mul_one]
      · have hnot : t⁻¹ ∉ Set.Ioo (0 : ℝ) 1 := by
          intro hc
          have h1 : 1 < t := (inv_lt_one_iff₀.mp hc.2).resolve_left (not_le.mpr ht0)
          exact ht1 h1
        dsimp only [h]
        rw [Set.indicator_of_notMem hnot, Set.indicator_of_notMem ht1, smul_zero]
    rw [setIntegral_congr_fun measurableSet_Ioi heq,
      MeasureTheory.setIntegral_indicator measurableSet_Ioi,
      Set.inter_eq_right.mpr (Set.Ioi_subset_Ioi zero_le_one)]
  rw [← hlhs, hinv, hrhs]
  let F : ℝ → ℂ := fun t => -((t : ℂ) ^ (-w)) / w
  have hcont : ContinuousWithinAt F (Set.Ici 1) 1 :=
    (((continuousAt_ofReal_cpow_const zero_lt_one (-w)).neg).div_const w).continuousWithinAt
  have hderiv : ∀ x ∈ Set.Ioi (1 : ℝ), HasDerivAt F ((x : ℂ) ^ (-w - 1)) x := by
    intro x hx
    have hx0 : 0 < x := lt_trans zero_lt_one hx
    have hslit : (x : ℂ) ∈ Complex.slitPlane := Or.inl (by simpa using hx0)
    have h1 : HasDerivAt (fun t : ℝ => (t : ℂ) ^ (-w)) (-w * (x : ℂ) ^ (-w - 1)) x := by
      have hc := (HasDerivAt.cpow_const (hasDerivAt_id (x : ℂ)) (c := -w) hslit).comp_ofReal
      simpa [mul_comm] using hc
    have h2 := (h1.neg).div_const w
    have hval : -(-w * (x : ℂ) ^ (-w - 1)) / w = (x : ℂ) ^ (-w - 1) := by
      rw [neg_mul, neg_neg, mul_div_cancel_left₀ _ hw_ne]
    rwa [hval] at h2
  have hint : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (-w - 1)) (Set.Ioi 1) volume := by
    have hintR : IntegrableOn (fun t : ℝ => t ^ (-w.re - 1)) (Set.Ioi 1) volume :=
      integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one
    refine hintR.mono' ?_ ?_
    · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
      intro t ht
      have ht0 : 0 < t := lt_trans zero_lt_one ht
      exact (continuousAt_ofReal_cpow_const ht0 (-w - 1)).continuousWithinAt
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht0 : 0 < t := lt_trans zero_lt_one ht
      rw [Complex.norm_cpow_eq_rpow_re_of_pos ht0]
      simp
  have htend : Tendsto F atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hrpow : Tendsto (fun t : ℝ => t ^ (-w.re)) atTop (nhds 0) :=
      tendsto_rpow_neg_atTop hw
    have hscaled : Tendsto (fun t : ℝ => t ^ (-w.re) / ‖w‖) atTop (nhds 0) := by
      simpa using hrpow.div_const ‖w‖
    refine hscaled.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    dsimp only [F]
    rw [norm_div, norm_neg, Complex.norm_cpow_eq_rpow_re_of_pos ht, Complex.neg_re]
  rw [MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hint htend]
  dsimp only [F]
  simp [neg_div]

/-- Integrability of `t ↦ (t : ℂ) ^ (w - 1)` on `Ioo 0 1` for `0 < w.re`. -/
lemma integrableOn_Ioo_zero_one_cpow {w : ℂ} (hw : 0 < w.re) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (w - 1)) (Set.Ioo 0 1) volume := by
  have hintR : IntegrableOn (fun t : ℝ => t ^ (w.re - 1)) (Set.Ioo 0 1) volume := by
    rw [← integrableOn_Ioc_iff_integrableOn_Ioo]
    exact intervalIntegral.intervalIntegrable_rpow' (by linarith) |>.1
  refine hintR.mono' ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioo
    intro t ht
    exact (continuousAt_ofReal_cpow_const ht.1 (w - 1)).continuousWithinAt
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    rw [Complex.norm_cpow_eq_rpow_re_of_pos ht.1]
    simp

/-- **General Agreement Theorem `completedEpsteinZetaExt L s = completedEpsteinZeta L s` on `Re(s) > rk L`**:
holds for ANY discrete lattice `L` satisfying the real-axis theta functional equation
`Θ_L(t) = t^{-rk L / 2} · covol(L)⁻¹ · Θ_{L*}(t⁻¹)` (including ALL orthogonal lattices AND `E₈`!). -/
theorem completedEpsteinZetaExt_eq_completedEpsteinZeta_of_theta_functional_eq
    (L : Submodule ℤ E) [DiscreteTopology L] [DiscreteTopology (dualLattice L)]
    (htheta : ∀ t : ℝ, 0 < t →
      latticeTheta L t = t ^ (-((rk L : ℝ) / 2)) * (covol L)⁻¹ * latticeTheta (dualLattice L) t⁻¹)
    {s : ℂ} (hs : (rk L : ℝ) < s.re) :
    completedEpsteinZetaExt L s = completedEpsteinZeta L s := by
  rw [← mellin_latticeTheta_sub_one_eq_completedEpsteinZeta L hs]
  have hs_pos : 0 < s.re := lt_of_le_of_lt (Nat.cast_nonneg (rk L)) hs
  have hs2_pos : 0 < (s / 2).re := by simp [half_pos hs_pos]
  have hsr2_pos : 0 < ((s - (rk L : ℂ)) / 2).re := by
    have : ((s - (rk L : ℂ)) / 2).re = (s.re - (rk L : ℝ)) / 2 := by simp
    linarith
  have hint_full : IntegrableOn
      (fun t : ℝ => ((latticeTheta L t - 1 : ℝ) : ℂ) * (t : ℂ) ^ (s / 2 - 1))
      (Set.Ioi 0) volume := by
    refine (mellinConvergent_latticeTheta_sub_one L hs).congr_fun (fun t _ => ?_) measurableSet_Ioi
    simp [mul_comm]
  have hsplit : (∫ t in Set.Ioi (0 : ℝ),
      ((latticeTheta L t - 1 : ℝ) : ℂ) * (t : ℂ) ^ (s / 2 - 1)) =
      (∫ t in Set.Ioo (0 : ℝ) 1,
        ((latticeTheta L t - 1 : ℝ) : ℂ) * (t : ℂ) ^ (s / 2 - 1)) +
      upperMellinTheta L s := by
    have hunion : Set.Ioc (0 : ℝ) 1 ∪ Set.Ioi (1 : ℝ) = Set.Ioi (0 : ℝ) :=
      Set.Ioc_union_Ioi_eq_Ioi zero_le_one
    have hdisj : Disjoint (Set.Ioc (0 : ℝ) 1) (Set.Ioi (1 : ℝ)) :=
      Set.Ioc_disjoint_Ioi_same
    have hint1 : IntegrableOn
        (fun t : ℝ => ((latticeTheta L t - 1 : ℝ) : ℂ) * (t : ℂ) ^ (s / 2 - 1))
        (Set.Ioc 0 1) volume :=
      hint_full.mono_set Set.Ioc_subset_Ioi_self
    have hint2 : IntegrableOn
        (fun t : ℝ => ((latticeTheta L t - 1 : ℝ) : ℂ) * (t : ℂ) ^ (s / 2 - 1))
        (Set.Ioi 1) volume :=
      hint_full.mono_set (Set.Ioi_subset_Ioi zero_le_one)
    rw [← hunion, MeasureTheory.setIntegral_union hdisj measurableSet_Ioi hint1 hint2,
      MeasureTheory.integral_Ioc_eq_integral_Ioo]
    rfl
  rw [hsplit]
  -- Evaluate the (0, 1) integral using the theta functional equation
  let f1 : ℝ → ℂ := fun t =>
    ((covol L : ℝ) : ℂ)⁻¹ * (((latticeTheta (dualLattice L) t⁻¹ - 1 : ℝ) : ℂ) *
      (t : ℂ) ^ ((s - (rk L : ℂ)) / 2 - 1))
  let f2 : ℝ → ℂ := fun t => ((covol L : ℝ) : ℂ)⁻¹ * (t : ℂ) ^ ((s - (rk L : ℂ)) / 2 - 1)
  let f3 : ℝ → ℂ := fun t => (t : ℂ) ^ (s / 2 - 1)
  have hpointwise : Set.EqOn
      (fun t : ℝ => ((latticeTheta L t - 1 : ℝ) : ℂ) * (t : ℂ) ^ (s / 2 - 1))
      (fun t : ℝ => f1 t + f2 t - f3 t) (Set.Ioo 0 1) := by
    intro t ht
    have ht0 : 0 < t := ht.1
    have htC : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht0.ne'
    have hpow_mul : ((t ^ (-((rk L : ℝ) / 2)) : ℝ) : ℂ) * (t : ℂ) ^ (s / 2 - 1) =
        (t : ℂ) ^ ((s - (rk L : ℂ)) / 2 - 1) := by
      rw [Complex.ofReal_cpow ht0.le, ← Complex.cpow_add _ _ htC]
      congr 1; push_cast; ring
    have hth := congrArg (fun x : ℝ => (x : ℂ)) (htheta t ht0)
    simp only [Complex.ofReal_mul, Complex.ofReal_inv] at hth
    dsimp only [f1, f2, f3]
    push_cast
    rw [hth]
    calc (((t ^ (-((rk L : ℝ) / 2)) : ℝ) : ℂ) * ((covol L : ℝ) : ℂ)⁻¹ *
            (latticeTheta (dualLattice L) t⁻¹ : ℂ) - 1) * (t : ℂ) ^ (s / 2 - 1)
        = ((covol L : ℝ) : ℂ)⁻¹ * ((latticeTheta (dualLattice L) t⁻¹ : ℂ) - 1) *
            (((t ^ (-((rk L : ℝ) / 2)) : ℝ) : ℂ) * (t : ℂ) ^ (s / 2 - 1)) +
          ((covol L : ℝ) : ℂ)⁻¹ *
            (((t ^ (-((rk L : ℝ) / 2)) : ℝ) : ℂ) * (t : ℂ) ^ (s / 2 - 1)) -
          (t : ℂ) ^ (s / 2 - 1) := by ring
      _ = _ := by rw [hpow_mul]; ring
  have hint_f2 : IntegrableOn f2 (Set.Ioo 0 1) volume :=
    (integrableOn_Ioo_zero_one_cpow hsr2_pos).const_mul _
  have hint_f3 : IntegrableOn f3 (Set.Ioo 0 1) volume :=
    integrableOn_Ioo_zero_one_cpow hs2_pos
  have hint_lhs : IntegrableOn
      (fun t : ℝ => ((latticeTheta L t - 1 : ℝ) : ℂ) * (t : ℂ) ^ (s / 2 - 1))
      (Set.Ioo 0 1) volume :=
    hint_full.mono_set Set.Ioo_subset_Ioi_self
  have hint_f1 : IntegrableOn f1 (Set.Ioo 0 1) volume := by
    have hsum : IntegrableOn (fun t => f1 t + f2 t - f3 t) (Set.Ioo 0 1) volume :=
      IntegrableOn.congr_fun hint_lhs hpointwise measurableSet_Ioo
    have h1 : IntegrableOn (fun t => (f1 t + f2 t - f3 t) + f3 t - f2 t) (Set.Ioo 0 1) volume :=
      (hsum.add hint_f3).sub hint_f2
    refine IntegrableOn.congr_fun h1 (fun t _ => by ring) measurableSet_Ioo
  have hI1 : ∫ t in Set.Ioo (0 : ℝ) 1, f1 t =
      ((covol L : ℝ) : ℂ)⁻¹ * upperMellinTheta (dualLattice L) ((rk L : ℂ) - s) := by
    dsimp only [f1]
    rw [MeasureTheory.integral_const_mul]
    congr 1
    let g : ℝ → ℂ := (Set.Ioi (1 : ℝ)).indicator (fun u => ((latticeTheta (dualLattice L) u - 1 : ℝ) : ℂ))
    have hcomp := mellin_comp_inv g ((s - (rk L : ℂ)) / 2)
    have hlhs_g : mellin (fun t => g t⁻¹) ((s - (rk L : ℂ)) / 2) =
        ∫ t in Set.Ioo (0 : ℝ) 1,
          ((latticeTheta (dualLattice L) t⁻¹ - 1 : ℝ) : ℂ) *
            (t : ℂ) ^ ((s - (rk L : ℂ)) / 2 - 1) := by
      unfold mellin
      have heq : Set.EqOn (fun t : ℝ => (t : ℂ) ^ ((s - (rk L : ℂ)) / 2 - 1) • g t⁻¹)
          ((Set.Ioo (0 : ℝ) 1).indicator (fun t : ℝ =>
            ((latticeTheta (dualLattice L) t⁻¹ - 1 : ℝ) : ℂ) *
              (t : ℂ) ^ ((s - (rk L : ℂ)) / 2 - 1))) (Set.Ioi 0) := by
        intro t ht
        have ht0 : 0 < t := ht
        by_cases ht1 : t < 1
        · have hmem : t ∈ Set.Ioo (0 : ℝ) 1 := ⟨ht0, ht1⟩
          have hinv1 : t⁻¹ ∈ Set.Ioi (1 : ℝ) := (one_lt_inv₀ ht0).mpr ht1
          dsimp only [g]
          rw [Set.indicator_of_mem hinv1, Set.indicator_of_mem hmem, smul_eq_mul, mul_comm]
        · have hnot : t ∉ Set.Ioo (0 : ℝ) 1 := fun hc => ht1 hc.2
          have hnot1 : t⁻¹ ∉ Set.Ioi (1 : ℝ) := by
            intro hc
            exact ht1 ((one_lt_inv₀ ht0).mp hc)
          dsimp only [g]
          rw [Set.indicator_of_notMem hnot1, Set.indicator_of_notMem hnot, smul_zero]
      rw [setIntegral_congr_fun measurableSet_Ioi heq,
        MeasureTheory.setIntegral_indicator measurableSet_Ioo,
        Set.inter_eq_right.mpr Set.Ioo_subset_Ioi_self]
    have hrhs_g : mellin g (-((s - (rk L : ℂ)) / 2)) =
        upperMellinTheta (dualLattice L) ((rk L : ℂ) - s) := by
      unfold mellin upperMellinTheta
      have hexp : -((s - (rk L : ℂ)) / 2) = ((rk L : ℂ) - s) / 2 := by ring
      rw [hexp]
      have heq : (fun t : ℝ => (t : ℂ) ^ (((rk L : ℂ) - s) / 2 - 1) • g t) =
          (Set.Ioi (1 : ℝ)).indicator (fun t =>
            ((latticeTheta (dualLattice L) t - 1 : ℝ) : ℂ) *
              (t : ℂ) ^ (((rk L : ℂ) - s) / 2 - 1)) := by
        funext t
        by_cases ht : t ∈ Set.Ioi (1 : ℝ)
        · dsimp only [g]
          rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht, smul_eq_mul, mul_comm]
        · dsimp only [g]
          rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht, smul_zero]
      rw [heq, MeasureTheory.setIntegral_indicator measurableSet_Ioi,
        Set.inter_eq_right.mpr (Set.Ioi_subset_Ioi zero_le_one)]
    rw [← hlhs_g, hcomp, hrhs_g]
  have hI2 : ∫ t in Set.Ioo (0 : ℝ) 1, f2 t =
      2 * ((covol L : ℝ) : ℂ)⁻¹ / (s - (rk L : ℂ)) := by
    dsimp only [f2]
    rw [MeasureTheory.integral_const_mul, integral_Ioo_zero_one_cpow hsr2_pos, one_div_div]
    ring
  have hI3 : ∫ t in Set.Ioo (0 : ℝ) 1, f3 t = 2 / s := by
    dsimp only [f3]
    rw [integral_Ioo_zero_one_cpow hs2_pos, one_div_div]
  have hI01 : ∫ t in Set.Ioo (0 : ℝ) 1,
      ((latticeTheta L t - 1 : ℝ) : ℂ) * (t : ℂ) ^ (s / 2 - 1) =
      ((covol L : ℝ) : ℂ)⁻¹ * upperMellinTheta (dualLattice L) ((rk L : ℂ) - s) +
        2 * ((covol L : ℝ) : ℂ)⁻¹ / (s - (rk L : ℂ)) - 2 / s := by
    rw [setIntegral_congr_fun measurableSet_Ioo hpointwise]
    have hsub : ∫ x in Set.Ioo (0 : ℝ) 1, (f1 x + f2 x - f3 x) =
        (∫ x in Set.Ioo (0 : ℝ) 1, (f1 x + f2 x)) - ∫ x in Set.Ioo (0 : ℝ) 1, f3 x :=
      MeasureTheory.integral_sub (hint_f1.add hint_f2) hint_f3
    have hadd : ∫ x in Set.Ioo (0 : ℝ) 1, (f1 x + f2 x) =
        (∫ x in Set.Ioo (0 : ℝ) 1, f1 x) + ∫ x in Set.Ioo (0 : ℝ) 1, f2 x :=
      MeasureTheory.integral_add hint_f1 hint_f2
    rw [hsub, hadd, hI1, hI2, hI3]
  rw [hI01]
  unfold completedEpsteinZetaExt
  ring

/-- **Agreement of `completedEpsteinZetaExt` with `completedEpsteinZeta` on `Re(s) > r`**
for EVERY discrete orthogonal lattice `L ⊂ E` of rank `r`! -/
theorem completedEpsteinZetaExt_eq_completedEpsteinZeta_orthogonal
    {L : Submodule ℤ E} [DiscreteTopology L] {r : ℕ}
    (b : Basis (Fin r) ℤ L) (hb : IsOrthogonalBasis b)
    {s : ℂ} (hs : (r : ℝ) < s.re) :
    completedEpsteinZetaExt L s = completedEpsteinZeta L s := by
  have : DiscreteTopology (dualLattice L) := discreteTopology_dualLattice_of_orthogonal b hb
  have hrk : rk L = r := by
    unfold rk; simpa using Module.finrank_eq_card_basis b
  refine completedEpsteinZetaExt_eq_completedEpsteinZeta_of_theta_functional_eq L ?_ (by rwa [hrk])
  intro t ht
  rw [hrk]
  exact latticeTheta_functional_eq_orthogonal b hb ht

/-- **EXACT GLOBAL FUNCTIONAL EQUATION OF THE COMPLETED EPSTEIN ZETA FUNCTION (ARBITRARY RANK `r`)**:
for EVERY discrete orthogonal `ℤ`-lattice `L ⊂ E` of rank `r` and EVERY `s : ℂ`,
$$\Lambda_L^{\mathrm{ext}}(r - s) = \operatorname{covol}(L)^{-1} \cdot \Lambda_{L^*}^{\mathrm{ext}}(s),$$
generalizing Mathlib's `completedRiemannZeta_one_sub` to arbitrary-rank `r`-dimensional lattices! -/
theorem completedEpsteinZetaExt_functional_eq_orthogonal
    {L : Submodule ℤ E} [DiscreteTopology L] {r : ℕ}
    (b : Basis (Fin r) ℤ L) (hb : IsOrthogonalBasis b) (s : ℂ) :
    completedEpsteinZetaExt L ((r : ℂ) - s) =
      ((covol L : ℝ) : ℂ)⁻¹ * completedEpsteinZetaExt (dualLattice L) s := by
  have : DiscreteTopology (dualLattice L) := discreteTopology_dualLattice_of_orthogonal b hb
  have hrkL : rk L = r := by unfold rk; simpa using Module.finrank_eq_card_basis b
  have hrkDual : rk (dualLattice L) = r := by
    unfold rk; simpa using Module.finrank_eq_card_basis (dualBasis b hb)
  have hcov_pos : 0 < covol L := covol_pos L
  have hcov_ne : ((covol L : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hcov_pos.ne'
  have hcov_dual : covol (dualLattice L) = (covol L)⁻¹ :=
    covol_dualLattice_of_orthogonalBasis b hb
  have hbidual : dualLattice (dualLattice L) = L :=
    dualLattice_dualLattice_of_orthogonal b hb
  unfold completedEpsteinZetaExt
  rw [hrkL, hrkDual, hcov_dual, hbidual, Complex.ofReal_inv, inv_inv]
  have hsub1 : (r : ℂ) - ((r : ℂ) - s) = s := by ring
  have hsub2 : (r : ℂ) - s - (r : ℂ) = -s := by ring
  rw [hsub1, hsub2]
  have hdiv1 : 2 * ((covol L : ℝ) : ℂ)⁻¹ / (-s) =
      -((covol L : ℝ) : ℂ)⁻¹ * (2 / s) := by ring
  have hdiv2 : -(2 / ((r : ℂ) - s)) =
      ((covol L : ℝ) : ℂ)⁻¹ * (2 * ((covol L : ℝ) : ℂ) / (s - (r : ℂ))) := by
    have hneg : ((r : ℂ) - s) = -(s - (r : ℂ)) := by ring
    rw [hneg, div_neg, neg_neg]
    calc 2 / (s - (r : ℂ))
        = (((covol L : ℝ) : ℂ)⁻¹ * ((covol L : ℝ) : ℂ)) * (2 / (s - (r : ℂ))) := by
            rw [inv_mul_cancel₀ hcov_ne, one_mul]
      _ = ((covol L : ℝ) : ℂ)⁻¹ * (2 * ((covol L : ℝ) : ℂ) / (s - (r : ℂ))) := by ring
  have hmul : ((covol L : ℝ) : ℂ)⁻¹ * (((covol L : ℝ) : ℂ) * upperMellinTheta L ((r : ℂ) - s)) =
      upperMellinTheta L ((r : ℂ) - s) := by
    rw [← mul_assoc, inv_mul_cancel₀ hcov_ne, one_mul]
  calc upperMellinTheta L ((r : ℂ) - s) +
        ((covol L : ℝ) : ℂ)⁻¹ * upperMellinTheta (dualLattice L) s +
        2 * ((covol L : ℝ) : ℂ)⁻¹ / -s - 2 / ((r : ℂ) - s)
      = ((covol L : ℝ) : ℂ)⁻¹ * upperMellinTheta (dualLattice L) s +
          upperMellinTheta L ((r : ℂ) - s) +
          (-(2 / ((r : ℂ) - s))) + 2 * ((covol L : ℝ) : ℂ)⁻¹ / -s := by ring
    _ = ((covol L : ℝ) : ℂ)⁻¹ * upperMellinTheta (dualLattice L) s +
          ((covol L : ℝ) : ℂ)⁻¹ * (((covol L : ℝ) : ℂ) * upperMellinTheta L ((r : ℂ) - s)) +
          ((covol L : ℝ) : ℂ)⁻¹ * (2 * ((covol L : ℝ) : ℂ) / (s - (r : ℂ))) -
          ((covol L : ℝ) : ℂ)⁻¹ * (2 / s) := by
            rw [hmul, hdiv2, hdiv1]; ring
    _ = ((covol L : ℝ) : ℂ)⁻¹ *
          (upperMellinTheta (dualLattice L) s +
            ((covol L : ℝ) : ℂ) * upperMellinTheta L ((r : ℂ) - s) +
            2 * ((covol L : ℝ) : ℂ) / (s - (r : ℂ)) - 2 / s) := by ring

/-- Rank-indexed form of the Global Functional Equation:
`completedEpsteinZetaExt L (rk L - s) = (covol L)⁻¹ * completedEpsteinZetaExt (dualLattice L) s`. -/
theorem completedEpsteinZetaExt_rk_sub_orthogonal
    {L : Submodule ℤ E} [DiscreteTopology L] {r : ℕ}
    (b : Basis (Fin r) ℤ L) (hb : IsOrthogonalBasis b) (s : ℂ) :
    completedEpsteinZetaExt L ((rk L : ℂ) - s) =
      ((covol L : ℝ) : ℂ)⁻¹ * completedEpsteinZetaExt (dualLattice L) s := by
  have hrk : rk L = r := by unfold rk; simpa using Module.finrank_eq_card_basis b
  rw [hrk]
  exact completedEpsteinZetaExt_functional_eq_orthogonal b hb s

/-! ### Non-Orthogonal Even Unimodular `E₈` & Rank-1 Riemann Zeta Instantiations -/

/-- **Completed Epstein Zeta Agreement for `E₈` on `Re(s) > 8`** (non-orthogonal even unimodular!):
`completedEpsteinZetaExt E8Lattice s = completedEpsteinZeta E8Lattice s`. -/
theorem completedEpsteinZetaExt_E8Lattice_eq_completedEpsteinZeta
    {s : ℂ} (hs : (8 : ℝ) < s.re) :
    completedEpsteinZetaExt E8Lattice s = completedEpsteinZeta E8Lattice s := by
  have hdual_disc : DiscreteTopology (dualLattice E8Lattice) := by
    rw [dualLattice_E8Lattice]; infer_instance
  refine completedEpsteinZetaExt_eq_completedEpsteinZeta_of_theta_functional_eq E8Lattice ?_
    (by simpa [rk_E8Lattice] using hs)
  intro t ht
  rw [rk_E8Lattice, covol_E8Lattice, dualLattice_E8Lattice, inv_one, mul_one]
  simpa [show -((8 : ℝ) / 2) = -4 by norm_num] using latticeTheta_E8Lattice_functional_eq ht

/-- **EXACT SELF-DUAL GLOBAL FUNCTIONAL EQUATION FOR `E₈` (ALL `s : ℂ`)**:
$$\Lambda_{E_8}^{\mathrm{ext}}(8 - s) = \Lambda_{E_8}^{\mathrm{ext}}(s).$$ -/
theorem completedEpsteinZetaExt_E8Lattice_functional_eq (s : ℂ) :
    completedEpsteinZetaExt E8Lattice (8 - s) = completedEpsteinZetaExt E8Lattice s := by
  unfold completedEpsteinZetaExt
  rw [rk_E8Lattice, covol_E8Lattice, dualLattice_E8Lattice]
  push_cast
  have hsub1 : (8 : ℂ) - (8 - s) = s := by ring
  have hsub2 : (8 : ℂ) - s - 8 = -s := by ring
  rw [hsub1, hsub2]
  have h1 : (2 : ℂ) / (-s) = -(2 / s) := div_neg (2 : ℂ)
  have h2 : -(2 / ((8 : ℂ) - s)) = 2 / (s - 8) := by
    rw [show (8 : ℂ) - s = -(s - 8) by ring, div_neg, neg_neg]
  simp only [inv_one, one_mul, mul_one]
  linear_combination h1 + h2

omit [FiniteDimensional ℝ E] in
/-- **Rank-1 Specialization to Riemann's `riemannZeta` and `completedRiemannZeta`**:
for any unit vector `e : E` (`‖e‖ = 1`) and `L = ℤ · e`, on `1 < s.re`:
`epsteinZeta L s = 2 * riemannZeta s` and `completedEpsteinZeta L s = 2 * completedRiemannZeta s`! -/
theorem epsteinZeta_unit_rank1_eq_two_mul_riemannZeta {e : E} (he : ‖e‖ = 1)
    {s : ℂ} (hs : 1 < s.re) :
    epsteinZeta (Submodule.span ℤ ({e} : Set E)) s = 2 * riemannZeta s := by
  let L : Submodule ℤ E := Submodule.span ℤ ({e} : Set E)
  have he0 : e ≠ 0 := by
    intro h; rw [h, norm_zero] at he; norm_num at he
  let toL : (ℕ ⊕ ℕ) → {v : L // (v : E) ≠ 0}
    | Sum.inl n => ⟨⟨((n + 1 : ℕ) : ℤ) • e, Submodule.smul_mem _ _ (Submodule.subset_span rfl)⟩, by
        change (((n + 1 : ℕ) : ℤ) • e) ≠ 0
        rw [← Int.cast_smul_eq_zsmul ℝ]
        exact smul_ne_zero (by positivity) he0⟩
    | Sum.inr n => ⟨⟨(-((n + 1 : ℕ) : ℤ)) • e, Submodule.smul_mem _ _ (Submodule.subset_span rfl)⟩, by
        change ((-((n + 1 : ℕ) : ℤ)) • e) ≠ 0
        rw [← Int.cast_smul_eq_zsmul ℝ]
        refine smul_ne_zero ?_ he0
        push_cast; linarith⟩
  have hbij : Function.Bijective toL := by
    constructor
    · intro x y hxy
      have hval : ((toL x : L) : E) = ((toL y : L) : E) := congrArg (fun u => (u.1 : E)) hxy
      rcases x with nx | nx <;> rcases y with ny | ny
      · congr 1
        change (((nx + 1 : ℕ) : ℤ) • e) = (((ny + 1 : ℕ) : ℤ) • e) at hval
        rw [← Int.cast_smul_eq_zsmul ℝ, ← Int.cast_smul_eq_zsmul ℝ] at hval
        have h0 := smul_left_injective ℝ he0 hval
        push_cast at h0
        exact_mod_cast (by linarith : (nx : ℝ) = (ny : ℝ))
      · exfalso
        change (((nx + 1 : ℕ) : ℤ) • e) = ((-((ny + 1 : ℕ) : ℤ)) • e) at hval
        rw [← Int.cast_smul_eq_zsmul ℝ, ← Int.cast_smul_eq_zsmul ℝ] at hval
        have h0 := smul_left_injective ℝ he0 hval
        push_cast at h0; linarith
      · exfalso
        change ((-((nx + 1 : ℕ) : ℤ)) • e) = (((ny + 1 : ℕ) : ℤ) • e) at hval
        rw [← Int.cast_smul_eq_zsmul ℝ, ← Int.cast_smul_eq_zsmul ℝ] at hval
        have h0 := smul_left_injective ℝ he0 hval
        push_cast at h0; linarith
      · congr 1
        change ((-((nx + 1 : ℕ) : ℤ)) • e) = ((-((ny + 1 : ℕ) : ℤ)) • e) at hval
        rw [← Int.cast_smul_eq_zsmul ℝ, ← Int.cast_smul_eq_zsmul ℝ] at hval
        have h0 := smul_left_injective ℝ he0 hval
        push_cast at h0
        exact_mod_cast (by linarith : (nx : ℝ) = (ny : ℝ))
    · rintro ⟨⟨v, hv⟩, hv0⟩
      obtain ⟨k, hk⟩ := Submodule.mem_span_singleton.mp hv
      have hk0 : k ≠ 0 := by
        intro h; subst h; simp at hk; exact hv0 hk.symm
      rcases lt_or_gt_of_ne hk0 with hneg | hpos
      · refine ⟨Sum.inr ((-k - 1).toNat), Subtype.ext (Subtype.ext ?_)⟩
        dsimp only [toL]
        have hcast : (-(((-k - 1).toNat + 1 : ℕ) : ℤ)) = k := by omega
        rw [hcast, hk]
      · refine ⟨Sum.inl ((k - 1).toNat), Subtype.ext (Subtype.ext ?_)⟩
        dsimp only [toL]
        have hcast : (((k - 1).toNat + 1 : ℕ) : ℤ) = k := by omega
        rw [hcast, hk]
  let eqv := Equiv.ofBijective toL hbij
  have hzeta : riemannZeta s = ∑' n : ℕ, (((n + 1 : ℕ) : ℂ)) ^ (-s) := by
    rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs]
    refine tsum_congr fun n => ?_
    rw [one_div, Complex.cpow_neg]
    push_cast; rfl
  have hsum_nat : Summable (fun n : ℕ => (((n + 1 : ℕ) : ℂ)) ^ (-s)) := by
    have hreal : Summable (fun n : ℕ => (((n + 1 : ℕ) : ℝ) ^ s.re)⁻¹) :=
      (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow_inv.mpr hs)
    refine Summable.of_norm (hreal.congr fun n => ?_)
    have hpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    rw [show (((n + 1 : ℕ) : ℂ)) = ((((n + 1 : ℕ) : ℝ)) : ℂ) by push_cast; rfl,
      Complex.norm_cpow_eq_rpow_re_of_pos hpos, Complex.neg_re, Real.rpow_neg hpos.le]
  have hnorm_l : ∀ n : ℕ, ‖((toL (Sum.inl n) : L) : E)‖ = (n + 1 : ℝ) := fun n => by
    simp only [toL, ← Int.cast_smul_eq_zsmul ℝ, norm_smul, he, mul_one, Real.norm_eq_abs]
    push_cast
    exact abs_of_pos (by positivity)
  have hnorm_r : ∀ n : ℕ, ‖((toL (Sum.inr n) : L) : E)‖ = (n + 1 : ℝ) := fun n => by
    simp only [toL, ← Int.cast_smul_eq_zsmul ℝ, norm_smul, he, mul_one, Real.norm_eq_abs]
    push_cast
    rw [abs_neg]
    exact abs_of_pos (by positivity)
  unfold epsteinZeta
  rw [← eqv.tsum_eq]
  have hL_eq : (fun n : ℕ => ((‖((eqv (Sum.inl n) : L) : E)‖ : ℝ) : ℂ) ^ (-s)) =
      fun n : ℕ => (((n + 1 : ℕ) : ℂ)) ^ (-s) := by
    funext n
    change ((‖((toL (Sum.inl n) : L) : E)‖ : ℝ) : ℂ) ^ (-s) = _
    rw [hnorm_l n]; push_cast; rfl
  have hR_eq : (fun n : ℕ => ((‖((eqv (Sum.inr n) : L) : E)‖ : ℝ) : ℂ) ^ (-s)) =
      fun n : ℕ => (((n + 1 : ℕ) : ℂ)) ^ (-s) := by
    funext n
    change ((‖((toL (Sum.inr n) : L) : E)‖ : ℝ) : ℂ) ^ (-s) = _
    rw [hnorm_r n]; push_cast; rfl
  have hsumL : Summable (fun n : ℕ => ((‖((eqv (Sum.inl n) : L) : E)‖ : ℝ) : ℂ) ^ (-s)) := by
    rw [hL_eq]; exact hsum_nat
  have hsumR : Summable (fun n : ℕ => ((‖((eqv (Sum.inr n) : L) : E)‖ : ℝ) : ℂ) ^ (-s)) := by
    rw [hR_eq]; exact hsum_nat
  rw [hsumL.tsum_sum hsumR, hL_eq, hR_eq, hzeta]
  ring

omit [FiniteDimensional ℝ E] in
/-- **Exact Recovery of `2 * completedRiemannZeta s` in Rank 1**:
for any unit vector `e : E` (`‖e‖ = 1`) and `1 < s.re`,
`completedEpsteinZeta (ℤ · e) s = 2 * completedRiemannZeta s`! -/
theorem completedEpsteinZeta_unit_rank1_eq_two_mul_completedRiemannZeta {e : E} (he : ‖e‖ = 1)
    {s : ℂ} (hs : 1 < s.re) :
    completedEpsteinZeta (Submodule.span ℤ ({e} : Set E)) s = 2 * completedRiemannZeta s := by
  unfold completedEpsteinZeta
  rw [epsteinZeta_unit_rank1_eq_two_mul_riemannZeta he hs]
  have hs0 : s ≠ 0 := fun h => by rw [h, Complex.zero_re] at hs; linarith
  rw [riemannZeta_def_of_ne_zero hs0, Complex.Gammaℝ_def]
  have hpi : (Real.pi : ℂ) ^ (-s / 2) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'))
  have hgam : Complex.Gamma (s / 2) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by simp; linarith)
  field_simp [hpi, hgam]

end MellinEpsteinZeta

end
end RHDirect.Stage5ThetaModular

