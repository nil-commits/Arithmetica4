import RHDirect.Interfaces
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# RHDirect.HermitianCurvatureCore

Compact, direct, 0-`sorry`, 0-`axiom` formalization of the **Hermitian Curvature, Bergman Metric,
Chern–Weil Degree Comparison & Moriwaki / Arithmetic Hilbert–Samuel Volume-to-Height Core**,
distilling the genuinely necessary analytic and geometric estimates from:
- `Formalism/HermitianCurvature/` (`1,922` files / `460,802` lines, incl. `Statement.lean`,
  `StatementH.lean`, `OmNorm`, `HerglotzFejerZd`, `RecursionSharp`),
- `GroundTheory/HeightsAndTheta/Heights/` (`RegularizedCurvature.lean`, `PCurvature.lean`,
  `StatementsBergman.lean`, `L1Convergence`, `MoriwakiBig.lean`),
- `ReciprocityTheory/.../MoriwakiSt.lean` & `TopCovolSlim2Use.lean` / `TopCovolG.lean`.

## Contents

1. **Hermitian Forms, Orthogonal Projection & Positive-Definite Fejér Kernels**:
   - `hermitian_orth_proj_norm` (exact `OmNorm` identity for negative-definite projections),
   - `hermitian_posSemidef_lerp` & `hermitian_quad_le_of_posSemidef_sub`,
   - `herglotz_fejer_nonneg` (exact multi-dimensional Fejér positivity `HerglotzFejerZd`).
2. **Complex Hessian (Levi Form), Plurisubharmonicity & Regularized Curvature Barriers**:
   - `leviForm`, linearity, convex interpolation (`leviForm_lerp_nonneg`),
   - `sndDeriv_nonneg_of_isLocalMin`, `leviForm_le_of_le` (plurisubharmonic curvature comparison),
   - `curvX`, `curvEta`, `curvK`, `thetaCoeff`, `gradBound`, `gradSq`,
     `thetaCoeff_pos`, `gradBound_lt_one`, `gradSq_le_gradBound`, `exp_div_ge_of_one_le`.
3. **Bergman Kernel, Extremal Bound, Gaussian Submean-Value Monotonicity & `L¹` Convergence**:
   - `ptNormSq`, `l2NormSq`, `bergmanKernel`, `bergmanKernel_nonneg`,
   - `integral_bergmanKernel_eq_rank`, `bergman_extremal_bound`, `sup_norm_le_sqrt_bergman_mul_L2`,
   - `gaussDiscMass`, `gaussDiscMass_pos`, `gaussDiscMass_antitone`,
     `bergman_upper_of_polydisc_submean`,
   - `tendsto_L1_of_limsup_le_and_integral_ge` (exact proof of `L1Convergence.Statement`).
4. **Chern–Weil Metric-Change Degree Comparison & Plurisubharmonic Volume-Integral Monotonicity**:
   - `ptNormSq_antitone_weight`, `l2NormSq_le_of_weight_sub_ge`, `l2NormSq_ge_of_weight_sub_le`,
   - `plurisubharmonic_volume_integral_antitone`,
   - `chernWeilChange`, `chernWeilChange_mono`, `chernWeilChange_bounds`,
   - `chi_metric_change_bounds`.
5. **Sharp Iterated Curvature / Norm Recursion (`RecursionSharp`)**:
   - `recursion_sharp_bound` (explicit constant `C = 55`, matching `Formalism.FourierDecayAlt.RecursionSharp`).
6. **Moriwaki Bigness, Arithmetic Hilbert–Samuel Volume-to-Height Bound & `BostSlopeFiber` Bridge**:
   - `arithVolNorm`, `sup_to_L2_volume_error_tendsto_zero`,
   - `moriwaki_big_of_ahs`, `exists_exp_many_small_sections_of_pos_selfInt`,
   - `normalizedHeight`, `height_lower_bound_of_ahs`, `height_upper_bound_of_small_section_bound`,
   - `bost_slope_from_curvature_volume_bound` (feeding `ArakelovCovolume.lean`).

Zero `sorry`, zero custom `axiom`s.
-/

open scoped BigOperators ComplexConjugate ComplexOrder
open Real Finset MeasureTheory Filter Topology

namespace RHDirect.HermitianCurvatureCore

noncomputable section

/-! ## Section 1: Hermitian Forms, Orthogonal Projection (`OmNorm`) & Fejér Kernels -/

/-- Exact Hermitian orthogonal-projection norm identity for a negative-definite vector `z`
(`ip z z = -T` with `T > 0`), matching `Formalism.HermitianCurvature.Statement.OmNorm`. -/
theorem hermitian_orth_proj_norm
    {V : Type*} [AddCommGroup V] [Module ℂ V] (ip : V → V → ℂ)
    (hadd : ∀ x y w, ip (x + y) w = ip x w + ip y w)
    (hsmul : ∀ (s : ℂ) x y, ip (s • x) y = s * ip x y)
    (hsym : ∀ x y, ip y x = conj (ip x y))
    (z x : V) (T T' : ℝ) (Dr : ℂ) (hT : 0 < T)
    (hzz : ip z z = -(T : ℂ)) (hxx : ip x x = -(T' : ℂ)) :
    ip (Dr • (x + (ip x z / (T : ℂ)) • z)) z = 0 ∧
    ip (Dr • (x + (ip x z / (T : ℂ)) • z)) (Dr • (x + (ip x z / (T : ℂ)) • z)) =
      (((Complex.normSq (Dr * ip x z) - T * T' * Complex.normSq Dr) / T : ℝ) : ℂ) := by
  have hTne : (T : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hT.ne'
  have hadd_r : ∀ a b c, ip a (b + c) = ip a b + ip a c := fun a b c => by
    rw [hsym, hadd, map_add, ← hsym, ← hsym]
  have hsmul_r : ∀ (s : ℂ) a b, ip a (s • b) = conj s * ip a b := fun s a b => by
    rw [hsym, hsmul, map_mul, ← hsym]
  have hproj_z : ip (x + (ip x z / (T : ℂ)) • z) z = 0 := by
    rw [hadd, hsmul, hzz]
    field_simp [hTne]
    ring
  refine ⟨?_, ?_⟩
  · rw [hsmul, hproj_z, mul_zero]
  · set w : V := x + (ip x z / (T : ℂ)) • z
    have hww : ip w w = ip w x := by
      calc ip w w
          = ip w x + conj (ip x z / (T : ℂ)) * ip w z := by
            rw [hadd_r, hsmul_r]
        _ = ip w x := by rw [hproj_z, mul_zero, add_zero]
    have hwx : ip w x = -(T' : ℂ) + (ip x z * conj (ip x z)) / (T : ℂ) := by
      calc ip w x
          = ip x x + (ip x z / (T : ℂ)) * ip z x := by rw [hadd, hsmul]
        _ = -(T' : ℂ) + (ip x z / (T : ℂ)) * conj (ip x z) := by rw [hxx, hsym x z]
        _ = -(T' : ℂ) + (ip x z * conj (ip x z)) / (T : ℂ) := by ring
    have hDr : ip (Dr • w) (Dr • w) = (Dr * conj Dr) * ip w w := by
      rw [hsmul, hsmul_r]
      ring
    rw [hDr, hww, hwx]
    have h1 : Dr * conj Dr = (Complex.normSq Dr : ℂ) := Complex.mul_conj Dr
    have h2 : ip x z * conj (ip x z) = (Complex.normSq (ip x z) : ℂ) := Complex.mul_conj (ip x z)
    rw [h1, h2]
    push_cast
    rw [Complex.normSq_mul]
    push_cast
    field_simp [hTne]
    ring

/-- Convex combinations of positive semidefinite Hermitian matrices remain positive semidefinite
(used for linear interpolation `φ_t = (1 - t) φ₀ + t φ₁` of Hermitian metrics). -/
theorem hermitian_posSemidef_lerp {n : Type*} [Fintype n] [DecidableEq n]
    {H₀ H₁ : Matrix n n ℂ} (h₀ : H₀.PosSemidef) (h₁ : H₁.PosSemidef)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ((1 - t) • H₀ + t • H₁).PosSemidef := by
  have h1 : ((1 - t) • H₀).PosSemidef := h₀.smul (sub_nonneg.mpr ht1)
  have h2 : (t • H₁).PosSemidef := h₁.smul ht0
  exact h1.add h2

/-- Hermitian metric positivity comparison: if `H₁ - H₀` is positive semidefinite, then the
associated quadratic form of `H₀` is dominated by that of `H₁`. -/
theorem hermitian_quad_le_of_posSemidef_sub {n : Type*} [Fintype n] [DecidableEq n]
    {H₀ H₁ : Matrix n n ℂ} (hsub : (H₁ - H₀).PosSemidef) (v : n → ℂ) :
    (star v ⬝ᵥ H₀.mulVec v).re ≤ (star v ⬝ᵥ H₁.mulVec v).re := by
  have h0 : 0 ≤ (star v ⬝ᵥ (H₁ - H₀).mulVec v).re := hsub.re_dotProduct_nonneg v
  have heq : star v ⬝ᵥ (H₁ - H₀).mulVec v = star v ⬝ᵥ H₁.mulVec v - star v ⬝ᵥ H₀.mulVec v := by
    rw [Matrix.sub_mulVec, dotProduct_sub]
  rw [heq, Complex.sub_re] at h0
  linarith

/-- One-dimensional Fejér counting identity on `[0, N]`: the number of pairs `(u, v) ∈ [0, N]²`
with `u - v = σ` equals `N + 1 - |σ|` for `|σ| ≤ N`. -/
private lemma card_sub_eq_fejer (N : ℕ) (σ : ℤ) (hσ : σ ∈ Finset.Icc (-(N : ℤ)) N) :
    (((Finset.Icc (0 : ℤ) N ×ˢ Finset.Icc (0 : ℤ) N).filter (fun p => p.1 - p.2 = σ)).card : ℝ) =
      ((N : ℝ) + 1) * (1 - |(σ : ℝ)| / ((N : ℝ) + 1)) := by
  have hN1 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  simp only [Finset.mem_Icc] at hσ
  have hcard :
      ((Finset.Icc (0 : ℤ) N ×ˢ Finset.Icc (0 : ℤ) N).filter (fun p => p.1 - p.2 = σ)).card =
        (Finset.Icc (max (0 : ℤ) (-σ)) (min (N : ℤ) (N - σ))).card := by
    refine Finset.card_bij (fun p _ => p.2) ?_ ?_ ?_
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp ⊢
      omega
    · intro p₁ hp₁ p₂ hp₂ h
      simp only [Finset.mem_filter] at hp₁ hp₂
      ext
      · omega
      · exact h
    · intro b hb
      simp only [Finset.mem_Icc] at hb
      refine ⟨(b + σ, b), ?_, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
      omega
  rw [hcard, Int.card_Icc]
  have hlen : (min (N : ℤ) (N - σ) + 1 - max (0 : ℤ) (-σ)) = (N : ℤ) + 1 - |σ| := by
    rcases le_total 0 σ with h0 | h0
    · rw [abs_of_nonneg h0, min_eq_right (by omega), max_eq_left (by omega)]
      omega
    · rw [abs_of_nonpos h0, min_eq_left (by omega), max_eq_right (by omega)]
  rw [hlen]
  have hnonneg : (0 : ℤ) ≤ (N : ℤ) + 1 - |σ| := by
    rcases le_total 0 σ with h0 | h0
    · rw [abs_of_nonneg h0]; omega
    · rw [abs_of_nonpos h0]; omega
  have htoNat : (((N : ℤ) + 1 - |σ|).toNat : ℝ) = ((N : ℝ) + 1) - |(σ : ℝ)| := by
    have h1 : (((((N : ℤ) + 1 - |σ|).toNat : ℤ)) : ℝ) = (((N : ℤ) + 1 - |σ| : ℤ) : ℝ) := by
      rw [Int.toNat_of_nonneg hnonneg]
    push_cast at h1
    exact h1
  rw [htoNat]
  field_simp [hN1.ne']

/-- **Multi-dimensional Herglotz–Fejér Positivity (`HerglotzFejerZd`)**:
For every positive-definite kernel `A : (Fin d → ℤ) → ℂ`, the Fejér-weighted trigonometric
polynomial on `[-N, N]^d` is everywhere non-negative (matching
`Formalism.HermitianCurvature.StatementH.HerglotzFejerZd`). -/
theorem herglotz_fejer_nonneg (d : ℕ) (A : (Fin d → ℤ) → ℂ)
    (hPD : ∀ (S : Finset (Fin d → ℤ)) (c : (Fin d → ℤ) → ℂ),
      0 ≤ (∑ σ ∈ S, ∑ σ' ∈ S, A (σ - σ') * c σ * conj (c σ')).re)
    (N : ℕ) (x : Fin d → ℝ) :
    0 ≤ (∑ σ ∈ Fintype.piFinset (fun _ : Fin d => Finset.Icc (-(N : ℤ)) N),
      (((∏ j, (1 - |((σ j : ℤ) : ℝ)| / ((N : ℝ) + 1))) : ℝ) : ℂ) * A σ *
        Complex.exp (2 * π * Complex.I * ∑ j, ((σ j : ℝ) : ℂ) * (x j : ℂ))).re := by
  let Q : Finset (Fin d → ℤ) := Fintype.piFinset (fun _ : Fin d => Finset.Icc (0 : ℤ) N)
  let B : Finset (Fin d → ℤ) := Fintype.piFinset (fun _ : Fin d => Finset.Icc (-(N : ℤ)) N)
  let c : (Fin d → ℤ) → ℂ := fun u =>
    Complex.exp (2 * π * Complex.I * ∑ j, ((u j : ℝ) : ℂ) * (x j : ℂ))
  have hQ : 0 ≤ (∑ u ∈ Q, ∑ v ∈ Q, A (u - v) * c u * conj (c v)).re := hPD Q c
  have hconj : ∀ u v : Fin d → ℤ,
      c u * conj (c v) =
        Complex.exp (2 * π * Complex.I * ∑ j, (((u - v) j : ℝ) : ℂ) * (x j : ℂ)) := by
    intro u v
    have hrv : conj (c v) =
        Complex.exp (-(2 * π * Complex.I * ∑ j, ((v j : ℝ) : ℂ) * (x j : ℂ))) := by
      dsimp only [c]
      rw [← Complex.exp_conj]
      congr 1
      simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I, map_sum]
      ring
    rw [hrv]
    dsimp only [c]
    rw [← Complex.exp_add]
    congr 1
    simp only [Pi.sub_apply, Int.cast_sub, Complex.ofReal_sub, sub_mul, Finset.sum_sub_distrib]
    ring
  have hcard_prod : ∀ σ ∈ B,
      (((Q ×ˢ Q).filter (fun p => p.1 - p.2 = σ)).card : ℝ) =
        ((N : ℝ) + 1) ^ d * ∏ j : Fin d, (1 - |((σ j : ℤ) : ℝ)| / ((N : ℝ) + 1)) := by
    intro σ hσ
    have hσj : ∀ j, σ j ∈ Finset.Icc (-(N : ℤ)) N := by
      simpa [B, Fintype.mem_piFinset] using hσ
    have hbij :
        ((Q ×ˢ Q).filter (fun p => p.1 - p.2 = σ)).card =
          (Fintype.piFinset (fun j : Fin d =>
            (Finset.Icc (0 : ℤ) N ×ˢ Finset.Icc (0 : ℤ) N).filter
              (fun p => p.1 - p.2 = σ j))).card := by
      refine Finset.card_bij (fun p _ j => (p.1 j, p.2 j)) ?_ ?_ ?_
      · intro p hp
        simp only [Finset.mem_filter, Finset.mem_product, Q, Fintype.mem_piFinset] at hp ⊢
        intro j
        refine ⟨⟨hp.1.1 j, hp.1.2 j⟩, ?_⟩
        exact congr_fun hp.2 j
      · intro p₁ _ p₂ _ h
        ext j
        · exact congr_arg Prod.fst (congr_fun h j)
        · exact congr_arg Prod.snd (congr_fun h j)
      · intro f hf
        simp only [Fintype.mem_piFinset, Finset.mem_filter, Finset.mem_product] at hf
        refine ⟨(fun j => (f j).1, fun j => (f j).2), ?_, by ext j <;> rfl⟩
        simp only [Finset.mem_filter, Finset.mem_product, Q, Fintype.mem_piFinset]
        refine ⟨⟨fun j => (hf j).1.1, fun j => (hf j).1.2⟩, ?_⟩
        ext j
        exact (hf j).2
    rw [hbij, Fintype.card_piFinset, Nat.cast_prod]
    calc ∏ j : Fin d, (((Finset.Icc (0 : ℤ) N ×ˢ Finset.Icc (0 : ℤ) N).filter
            (fun p => p.1 - p.2 = σ j)).card : ℝ)
        = ∏ j : Fin d, (((N : ℝ) + 1) * (1 - |((σ j : ℤ) : ℝ)| / ((N : ℝ) + 1))) := by
          refine Finset.prod_congr rfl fun j _ => card_sub_eq_fejer N (σ j) (hσj j)
      _ = ((N : ℝ) + 1) ^ d * ∏ j : Fin d, (1 - |((σ j : ℤ) : ℝ)| / ((N : ℝ) + 1)) := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hsum_eq :
      ∑ u ∈ Q, ∑ v ∈ Q, A (u - v) * c u * conj (c v) =
        ((((N : ℝ) + 1) ^ d : ℝ) : ℂ) *
          ∑ σ ∈ B,
            (((∏ j, (1 - |((σ j : ℤ) : ℝ)| / ((N : ℝ) + 1))) : ℝ) : ℂ) * A σ *
              Complex.exp (2 * π * Complex.I * ∑ j, ((σ j : ℝ) : ℂ) * (x j : ℂ)) := by
    rw [← Finset.sum_product']
    have hmap : ∀ p ∈ Q ×ˢ Q, p.1 - p.2 ∈ B := by
      intro p hp
      simp only [Finset.mem_product, Q, B, Fintype.mem_piFinset, Finset.mem_Icc, Pi.sub_apply] at hp ⊢
      intro j
      have h1 := hp.1 j
      have h2 := hp.2 j
      omega
    have hfib := Finset.sum_fiberwise_of_maps_to (s := Q ×ˢ Q) (t := B) (g := fun p => p.1 - p.2)
      hmap (fun p => A (p.1 - p.2) * c p.1 * conj (c p.2))
    rw [← hfib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ hσ => ?_
    have hconst : ∀ p ∈ (Q ×ˢ Q).filter (fun p => p.1 - p.2 = σ),
        A (p.1 - p.2) * c p.1 * conj (c p.2) =
          A σ * Complex.exp (2 * π * Complex.I * ∑ j, ((σ j : ℝ) : ℂ) * (x j : ℂ)) := by
      intro p hp
      have heq : p.1 - p.2 = σ := (Finset.mem_filter.mp hp).2
      rw [mul_assoc, hconj, heq]
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
    have hc : (((((Q ×ˢ Q).filter (fun p => p.1 - p.2 = σ)).card : ℝ)) : ℂ) =
        ((((N : ℝ) + 1) ^ d : ℝ) : ℂ) *
          (((∏ j : Fin d, (1 - |((σ j : ℤ) : ℝ)| / ((N : ℝ) + 1))) : ℝ) : ℂ) := by
      exact_mod_cast hcard_prod σ hσ
    rw [show (((Q ×ˢ Q).filter (fun p => p.1 - p.2 = σ)).card : ℂ) =
        (((((Q ×ˢ Q).filter (fun p => p.1 - p.2 = σ)).card : ℝ)) : ℂ) by norm_cast, hc]
    ring
  rw [hsum_eq, Complex.re_ofReal_mul] at hQ
  have hpos : (0 : ℝ) < ((N : ℝ) + 1) ^ d := by positivity
  exact nonneg_of_mul_nonneg_right hQ hpos

/-! ## Section 2: Complex Hessian (Levi Form), Plurisubharmonicity & Regularized Curvature -/

/-- Complex Hessian / Levi curvature form `(∂²φ/∂z∂z̄)(w, w) = (D²φ(w, w) + D²φ(i w, i w)) / 4`
of a real-valued Hermitian metric weight `φ : (J → ℂ) → ℝ` at `z` in tangent direction `w`. -/
def leviForm {J : Type*} [Fintype J] (φ : (J → ℂ) → ℝ) (z w : J → ℂ) : ℝ :=
  (fderiv ℝ (fderiv ℝ φ) z w w + fderiv ℝ (fderiv ℝ φ) z (Complex.I • w) (Complex.I • w)) / 4

/-- A `C²` metric weight `φ` is plurisubharmonic (semipositive curvature) on `U` if its Levi form
is non-negative at every point of `U` in every tangent direction. -/
def IsPlurisubharmonicOn {J : Type*} [Fintype J] (φ : (J → ℂ) → ℝ) (U : Set (J → ℂ)) : Prop :=
  ∀ z ∈ U, ContDiffAt ℝ 2 φ z ∧ ∀ w : J → ℂ, 0 ≤ leviForm φ z w

/-- Second derivative test for a real local minimum at `0`. -/
theorem deriv_deriv_nonneg_of_isLocalMin {g : ℝ → ℝ} (hg : IsLocalMin g 0) (hc : ContinuousAt g 0) :
    0 ≤ deriv (deriv g) 0 := by
  by_contra hneg
  push Not at hneg
  have hmax := isLocalMax_of_deriv_deriv_neg hneg hg.deriv_eq_zero hc
  have hev : g =ᶠ[𝓝 0] fun _ => g 0 := by
    filter_upwards [hg, hmax] with s h1 h2
    exact le_antisymm h2 h1
  have h2 : deriv (deriv g) 0 = 0 := by
    rw [hev.deriv.deriv_eq]
    simp
  linarith

/-- Directional second derivative along a real line `s ↦ z + s • e` equals the Fréchet Hessian. -/
theorem deriv_deriv_line {J : Type*} [Fintype J] {f : (J → ℂ) → ℝ} {z : J → ℂ}
    (hf : ContDiffAt ℝ 2 f z) (e : J → ℂ) :
    deriv (deriv fun s : ℝ => f (z + s • e)) 0 = fderiv ℝ (fderiv ℝ f) z e e := by
  have hline : ∀ s : ℝ, HasDerivAt (fun s : ℝ => z + s • e) e s := fun s =>
    (((hasDerivAt_id s).smul_const e).const_add z).congr_deriv (one_smul ℝ e)
  have hz0 : z + (0 : ℝ) • e = z := by rw [zero_smul, add_zero]
  have hcont : Tendsto (fun s : ℝ => z + s • e) (𝓝 0) (𝓝 z) := by
    have h := (hline 0).continuousAt.tendsto
    rwa [hz0] at h
  have hfe : ∀ᶠ y in 𝓝 z, ContDiffAt ℝ 2 f y := hf.eventually (by simp)
  have hev : deriv (fun s : ℝ => f (z + s • e)) =ᶠ[𝓝 0] fun s => fderiv ℝ f (z + s • e) e := by
    filter_upwards [hcont.eventually hfe] with s hs
    have h := (hs.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt s (hline s)
    exact h.deriv
  have hH : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) z) z :=
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have hA : HasFDerivAt (fun y => fderiv ℝ f y e) ((fderiv ℝ (fderiv ℝ f) z).flip e) z := by
    have h := hH.clm_apply (hasFDerivAt_const e z)
    simpa using h
  have hd : HasDerivAt (fun s : ℝ => fderiv ℝ f (z + s • e) e) (fderiv ℝ (fderiv ℝ f) z e e) 0 :=
    hA.comp_hasDerivAt_of_eq (0 : ℝ) (hline 0) hz0.symm
  rw [hev.deriv_eq]
  exact hd.deriv

/-- At a local minimum of a `C²` function, the Fréchet Hessian is positive semidefinite. -/
theorem sndDeriv_nonneg_of_isLocalMin {J : Type*} [Fintype J] {f : (J → ℂ) → ℝ} {z : J → ℂ}
    (hf : ContDiffAt ℝ 2 f z) (hmin : IsLocalMin f z) (e : J → ℂ) :
    0 ≤ fderiv ℝ (fderiv ℝ f) z e e := by
  rw [← deriv_deriv_line hf e]
  have hc : Continuous fun s : ℝ => z + s • e :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hz : z + (0 : ℝ) • e = z := by simp
  refine deriv_deriv_nonneg_of_isLocalMin ?_ ?_
  · have h : IsLocalMin f (z + (0 : ℝ) • e) := by rw [hz]; exact hmin
    exact IsLocalMin.comp_continuous (g := fun s : ℝ => z + s • e) (b := 0) h hc.continuousAt
  · exact ContinuousAt.comp_of_eq hf.continuousAt hc.continuousAt hz

/-- A constant metric weight has identically vanishing Levi curvature form. -/
theorem leviForm_const {J : Type*} [Fintype J] (c : ℝ) (z w : J → ℂ) :
    leviForm (fun _ : J → ℂ => c) z w = 0 := by
  unfold leviForm
  have h1 : fderiv ℝ (fun _ : J → ℂ => c) = 0 := by
    ext y v
    simp
  rw [h1]
  simp

/-- Linearity of the Levi curvature form under real linear combinations of `C²` metric weights. -/
theorem leviForm_add_smul {J : Type*} [Fintype J] (a b : ℝ) {φ ψ : (J → ℂ) → ℝ} {z : J → ℂ}
    (hφ : ContDiffAt ℝ 2 φ z) (hψ : ContDiffAt ℝ 2 ψ z) (w : J → ℂ) :
    leviForm (fun y => a * φ y + b * ψ y) z w = a * leviForm φ z w + b * leviForm ψ z w := by
  have hφe : ∀ᶠ y in 𝓝 z, ContDiffAt ℝ 2 φ y := hφ.eventually (by simp)
  have hψe : ∀ᶠ y in 𝓝 z, ContDiffAt ℝ 2 ψ y := hψ.eventually (by simp)
  have hf1 : fderiv ℝ (fun y => a * φ y + b * ψ y) =ᶠ[𝓝 z]
      fun y => a • fderiv ℝ φ y + b • fderiv ℝ ψ y := by
    filter_upwards [hφe, hψe] with y hφy hψy
    have dφ := hφy.differentiableAt (by norm_num)
    have dψ := hψy.differentiableAt (by norm_num)
    exact ((dφ.hasFDerivAt.const_smul a).add (dψ.hasFDerivAt.const_smul b)).fderiv
  have hdφ : DifferentiableAt ℝ (fderiv ℝ φ) z :=
    (hφ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hdψ : DifferentiableAt ℝ (fderiv ℝ ψ) z :=
    (hψ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hf2 : fderiv ℝ (fderiv ℝ (fun y => a * φ y + b * ψ y)) z =
      a • fderiv ℝ (fderiv ℝ φ) z + b • fderiv ℝ (fderiv ℝ ψ) z := by
    rw [hf1.fderiv_eq]
    exact ((hdφ.hasFDerivAt.const_smul a).add (hdψ.hasFDerivAt.const_smul b)).fderiv
  unfold leviForm
  rw [hf2]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

/-- Convex interpolation `φ_t = (1 - t) φ₀ + t φ₁` of semipositive Hermitian metric weights
is again semipositive (`IsPlurisubharmonicOn` is convex). -/
theorem leviForm_lerp_nonneg {J : Type*} [Fintype J] {φ₀ φ₁ : (J → ℂ) → ℝ} {z : J → ℂ}
    (hφ₀ : ContDiffAt ℝ 2 φ₀ z) (hφ₁ : ContDiffAt ℝ 2 φ₁ z)
    (hp₀ : ∀ w, 0 ≤ leviForm φ₀ z w) (hp₁ : ∀ w, 0 ≤ leviForm φ₁ z w)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (w : J → ℂ) :
    0 ≤ leviForm (fun y => (1 - t) * φ₀ y + t * φ₁ y) z w := by
  rw [leviForm_add_smul (1 - t) t hφ₀ hφ₁ w]
  exact add_nonneg (mul_nonneg (sub_nonneg.mpr ht1) (hp₀ w)) (mul_nonneg ht0 (hp₁ w))

/-- **Plurisubharmonic Curvature Comparison Principle (`leviForm_le_of_le`)**:
If two `C²` Hermitian weights touch from below at `z` (`ψ ≤ φ` near `z` and `ψ z = φ z`),
then the Levi curvature form of `ψ` at `z` is dominated by that of `φ`. -/
theorem leviForm_le_of_le {J : Type*} [Fintype J] {φ ψ : (J → ℂ) → ℝ} {z : J → ℂ}
    (hφ : ContDiffAt ℝ 2 φ z) (hψ : ContDiffAt ℝ 2 ψ z)
    (hle : ∀ᶠ y in 𝓝 z, ψ y ≤ φ y) (heq : ψ z = φ z) (w : J → ℂ) :
    leviForm ψ z w ≤ leviForm φ z w := by
  have hf : ContDiffAt ℝ 2 (fun y => 1 * φ y + (-1) * ψ y) z :=
    (contDiffAt_const.mul hφ).add (contDiffAt_const.mul hψ)
  have hmin : IsLocalMin (fun y => 1 * φ y + (-1) * ψ y) z := by
    filter_upwards [hle] with y hy
    simp only [heq]
    linarith
  have h1 := sndDeriv_nonneg_of_isLocalMin hf hmin w
  have h2 := sndDeriv_nonneg_of_isLocalMin hf hmin (Complex.I • w)
  have h3 : 0 ≤ leviForm (fun y => 1 * φ y + (-1) * ψ y) z w :=
    div_nonneg (add_nonneg h1 h2) (by norm_num)
  rw [leviForm_add_smul 1 (-1) hφ hψ w] at h3
  linarith

/-- Curvature form upper bound via a touching barrier function `ψ`. -/
theorem leviForm_upper_bound_of_barrier {J : Type*} [Fintype J] {φ ψ : (J → ℂ) → ℝ} {z : J → ℂ}
    {C : ℝ} (hφ : ContDiffAt ℝ 2 φ z) (hψ : ContDiffAt ℝ 2 ψ z)
    (hle : ∀ᶠ y in 𝓝 z, φ y ≤ ψ y) (heq : φ z = ψ z)
    (hC : ∀ w, leviForm ψ z w ≤ C * ‖w‖ ^ 2) (w : J → ℂ) :
    leviForm φ z w ≤ C * ‖w‖ ^ 2 :=
  le_trans (leviForm_le_of_le hψ hφ hle heq w) (hC w)

/-! ### Explicit Regularized Poincaré / Effective Hilbert–Samuel Curvature Barrier -/

/-- Regularized radial log-barrier coordinate `x(ε, v) = 1 + log(1 + ε²) - log(e^v + ε²)`. -/
def curvX (ε v : ℝ) : ℝ := 1 + log (1 + ε ^ 2) - log (exp v + ε ^ 2)

/-- Auxiliary Poincaré entropy function `η(x) = x + log x`. -/
def curvEta (x : ℝ) : ℝ := x + log x

/-- Derivative ratio `K(x) = 1 + 1 / x`. -/
def curvK (x : ℝ) : ℝ := 1 + 1 / x

/-- Regularized curvature potential `Φ(x) = -log(x + log x)`. -/
def curvPhi (x : ℝ) : ℝ := -log (curvEta x)

/-- Upper bound `(x + 1)² / ((x + 1)² + η(x)) < 1` on the gradient-to-curvature ratio. -/
def gradBound (x : ℝ) : ℝ := (x + 1) ^ 2 / ((x + 1) ^ 2 + curvEta x)

/-- Curvature lower-bound coefficient `θ(ε, v)` for the regularized Poincaré metric. -/
def thetaCoeff (ε v : ℝ) : ℝ :=
  curvK (curvX ε v) * ε ^ 2 / (curvEta (curvX ε v) * exp v)
    + 1 / (curvX ε v ^ 2 * curvEta (curvX ε v))
    + (curvK (curvX ε v) / curvEta (curvX ε v)) ^ 2

/-- Gradient-squared-to-curvature ratio `|∇Φ|² / θ(ε, v)`. -/
def gradSq (ε v : ℝ) : ℝ :=
  (curvK (curvX ε v) / curvEta (curvX ε v)) ^ 2 / thetaCoeff ε v

theorem le_curvEta {x : ℝ} (hx : 1 ≤ x) : x ≤ curvEta x := by
  have := log_nonneg hx
  unfold curvEta
  linarith

theorem curvX_ge_one {ε v : ℝ} (hv : v ≤ 0) : 1 ≤ curvX ε v := by
  unfold curvX
  have hexp : exp v ≤ 1 := exp_le_one_iff.mpr hv
  have hle : exp v + ε ^ 2 ≤ 1 + ε ^ 2 := by linarith
  have hpos : 0 < exp v + ε ^ 2 := by positivity
  have hlog : log (exp v + ε ^ 2) ≤ log (1 + ε ^ 2) := log_le_log hpos hle
  linarith

theorem sq_add_four_mul_le_two_exp {x : ℝ} (hx : 1 ≤ x) : x ^ 2 + 4 * x ≤ 2 * exp x := by
  set t := x - 1 with ht
  have ht0 : 0 ≤ t := by linarith
  have hxt : x = 1 + t := by linarith
  have he : exp x = exp 1 * exp t := by rw [← exp_add, hxt]
  have hq : 1 + t + t ^ 2 / 2 ≤ exp t := quadratic_le_exp_of_nonneg ht0
  have he1 : (2.7 : ℝ) < exp 1 := lt_trans (by norm_num) exp_one_gt_d9
  have hp : 0 < 1 + t + t ^ 2 / 2 := by positivity
  have h1 : exp 1 * (1 + t + t ^ 2 / 2) ≤ exp 1 * exp t :=
    mul_le_mul_of_nonneg_left hq (exp_pos 1).le
  have h2 : 2.7 * (1 + t + t ^ 2 / 2) ≤ exp 1 * (1 + t + t ^ 2 / 2) :=
    mul_le_mul_of_nonneg_right he1.le hp.le
  rw [he, hxt]
  nlinarith [sq_nonneg (t - 3 / 17)]

/-- Effective Hilbert–Samuel exponential curvature barrier lower bound
(matching `EffectiveHilbertSamuel/PCurvature.lean`). -/
theorem exp_div_ge_of_one_le {x D : ℝ} (hx : 1 ≤ x) (hD : 1 ≤ D) :
    exp (D - 1) / 2 ≤ exp (D * x) / ((x + 1) ^ 2 + curvEta x) := by
  have hlog : log x ≤ x - 1 := log_le_sub_one_of_pos (by linarith)
  have hη : 1 ≤ curvEta x := le_trans hx (le_curvEta hx)
  have hden : 0 < (x + 1) ^ 2 + curvEta x := by positivity
  have hden' : (x + 1) ^ 2 + curvEta x ≤ 2 * exp x := by
    have := sq_add_four_mul_le_two_exp hx
    unfold curvEta
    nlinarith
  have hexp : exp (D - 1) * exp x ≤ exp (D * x) := by
    rw [← exp_add, exp_le_exp]
    nlinarith
  rw [le_div_iff₀ hden]
  calc exp (D - 1) / 2 * ((x + 1) ^ 2 + curvEta x)
      ≤ exp (D - 1) / 2 * (2 * exp x) := mul_le_mul_of_nonneg_left hden' (by positivity)
    _ = exp (D - 1) * exp x := by ring
    _ ≤ exp (D * x) := hexp

/-- Strict positivity of the regularized curvature coefficient `thetaCoeff ε v` for `v ≤ 0`. -/
theorem thetaCoeff_pos {ε v : ℝ} (hv : v ≤ 0) : 0 < thetaCoeff ε v := by
  have hx : 1 ≤ curvX ε v := curvX_ge_one hv
  have hη : 0 < curvEta (curvX ε v) := lt_of_lt_of_le zero_lt_one (le_trans hx (le_curvEta hx))
  have hK : 0 < curvK (curvX ε v) := by unfold curvK; positivity
  unfold thetaCoeff
  have t1 : 0 ≤ curvK (curvX ε v) * ε ^ 2 / (curvEta (curvX ε v) * exp v) := by positivity
  have t2 : 0 < 1 / (curvX ε v ^ 2 * curvEta (curvX ε v)) := by positivity
  have t3 : 0 ≤ (curvK (curvX ε v) / curvEta (curvX ε v)) ^ 2 := sq_nonneg _
  linarith

/-- The regularized curvature gradient bound is strictly below `1` for all `x ≥ 1`. -/
theorem gradBound_lt_one {x : ℝ} (hx : 1 ≤ x) : gradBound x < 1 := by
  have hη : 0 < curvEta x := lt_of_lt_of_le zero_lt_one (le_trans hx (le_curvEta hx))
  unfold gradBound
  rw [div_lt_one (by positivity)]
  linarith

/-- Sharp gradient-to-curvature upper bound `gradSq ε v ≤ gradBound (curvX ε v) < 1`. -/
theorem gradSq_le_gradBound {ε v : ℝ} (hv : v ≤ 0) : gradSq ε v ≤ gradBound (curvX ε v) := by
  set x := curvX ε v
  have hx : 1 ≤ x := curvX_ge_one hv
  have hxpos : 0 < x := by linarith
  have hη : 0 < curvEta x := lt_of_lt_of_le zero_lt_one (le_trans hx (le_curvEta hx))
  have hK : 0 < curvK x := by unfold curvK; positivity
  have hθ : 0 < thetaCoeff ε v := thetaCoeff_pos hv
  have hden : 0 < (x + 1) ^ 2 + curvEta x := by positivity
  unfold gradSq gradBound
  rw [div_le_div_iff₀ hθ hden]
  have hKeq : curvK x = (x + 1) / x := by
    unfold curvK
    field_simp [hxpos.ne']
  have hdrop :
      1 / (x ^ 2 * curvEta x) + (curvK x / curvEta x) ^ 2 ≤ thetaCoeff ε v := by
    unfold thetaCoeff
    have h1 : 0 ≤ curvK x * ε ^ 2 / (curvEta x * exp v) := by positivity
    linarith
  have hid :
      (curvK x / curvEta x) ^ 2 * ((x + 1) ^ 2 + curvEta x) =
        (x + 1) ^ 2 * (1 / (x ^ 2 * curvEta x) + (curvK x / curvEta x) ^ 2) := by
    rw [hKeq]
    field_simp [hxpos.ne', hη.ne']
    ring
  rw [hid]
  exact mul_le_mul_of_nonneg_left hdrop (sq_nonneg _)

/-! ## Section 3: Bergman Kernel, Extremal Property, Gaussian Submean & `L¹` Convergence -/

/-- Pointwise Hermitian metric norm-squared `‖s(x)‖² e^{-n φ(x)}` of a section `s` of `L^{⊗ n}`. -/
def ptNormSq {X : Type*} (φ : X → ℝ) (n : ℕ) (s : X → ℂ) (x : X) : ℝ :=
  ‖s x‖ ^ 2 * exp (-(n : ℝ) * φ x)

/-- Global `L²` Hermitian norm-squared `∫ ‖s(x)‖² e^{-n φ(x)} dμ`. -/
def l2NormSq {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (φ : X → ℝ) (n : ℕ) (s : X → ℂ) : ℝ :=
  ∫ x, ptNormSq φ n s x ∂μ

/-- Finite-rank Bergman kernel `B_n(x) = ∑ᵢ ‖eᵢ(x)‖² e^{-n φ(x)}` attached to an orthonormal
basis `e : Fin d → X → ℂ`. -/
def bergmanKernel {X : Type*} {d : ℕ} (φ : X → ℝ) (n : ℕ) (e : Fin d → X → ℂ) (x : X) : ℝ :=
  ∑ i : Fin d, ptNormSq φ n (e i) x

theorem ptNormSq_nonneg {X : Type*} (φ : X → ℝ) (n : ℕ) (s : X → ℂ) (x : X) :
    0 ≤ ptNormSq φ n s x :=
  mul_nonneg (sq_nonneg _) (exp_pos _).le

theorem bergmanKernel_nonneg {X : Type*} {d : ℕ} (φ : X → ℝ) (n : ℕ) (e : Fin d → X → ℂ) (x : X) :
    0 ≤ bergmanKernel φ n e x :=
  Finset.sum_nonneg fun i _ => ptNormSq_nonneg φ n (e i) x

/-- **Bergman Trace Identity (`IntegralOfBergman`)**:
Integrating the Bergman kernel of an `L²`-unit-norm basis over `(X, μ)` recovers the exact rank `d`. -/
theorem integral_bergmanKernel_eq_rank {X : Type*} [MeasurableSpace X] (μ : Measure X) {d : ℕ}
    (φ : X → ℝ) (n : ℕ) (e : Fin d → X → ℂ)
    (hint : ∀ i : Fin d, Integrable (ptNormSq φ n (e i)) μ)
    (hunit : ∀ i : Fin d, l2NormSq μ φ n (e i) = 1) :
    ∫ x, bergmanKernel φ n e x ∂μ = (d : ℝ) := by
  unfold bergmanKernel
  rw [MeasureTheory.integral_finsetSum Finset.univ (fun i _ => hint i)]
  have hsum : ∑ i : Fin d, ∫ x, ptNormSq φ n (e i) x ∂μ = ∑ _i : Fin d, (1 : ℝ) :=
    Finset.sum_congr rfl fun i _ => hunit i
  rw [hsum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]

/-- **Bergman Extremal Inequality**:
For any section `s = ∑ᵢ cᵢ eᵢ`, `‖s(x)‖² e^{-n φ(x)} ≤ B_n(x) · ∑ᵢ ‖cᵢ‖²`. -/
theorem bergman_extremal_bound {X : Type*} {d : ℕ} (φ : X → ℝ) (n : ℕ)
    (e : Fin d → X → ℂ) (c : Fin d → ℂ) (x : X) :
    ptNormSq φ n (fun y => ∑ i : Fin d, c i * e i y) x ≤
      bergmanKernel φ n e x * (∑ i : Fin d, ‖c i‖ ^ 2) := by
  simp only [ptNormSq, bergmanKernel]
  have hcs : ‖∑ i : Fin d, c i * e i x‖ ^ 2 ≤
      (∑ i : Fin d, ‖e i x‖ ^ 2) * (∑ i : Fin d, ‖c i‖ ^ 2) := by
    have htri : ‖∑ i : Fin d, c i * e i x‖ ≤ ∑ i : Fin d, ‖e i x‖ * ‖c i‖ := by
      refine le_trans (norm_sum_le _ _) ?_
      refine Finset.sum_le_sum fun i _ => ?_
      rw [norm_mul, mul_comm]
    have hsq := sq_le_sq' (by linarith [norm_nonneg (∑ i : Fin d, c i * e i x)]) htri
    exact le_trans hsq (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => ‖e i x‖) (fun i => ‖c i‖))
  have hfac : ∑ i : Fin d, ‖e i x‖ ^ 2 * exp (-(n : ℝ) * φ x) =
      (∑ i : Fin d, ‖e i x‖ ^ 2) * exp (-(n : ℝ) * φ x) :=
    (Finset.sum_mul Finset.univ (fun i => ‖e i x‖ ^ 2) _).symm
  rw [hfac]
  calc ‖∑ i : Fin d, c i * e i x‖ ^ 2 * exp (-(n : ℝ) * φ x)
      ≤ ((∑ i : Fin d, ‖e i x‖ ^ 2) * (∑ i : Fin d, ‖c i‖ ^ 2)) * exp (-(n : ℝ) * φ x) :=
        mul_le_mul_of_nonneg_right hcs (exp_pos _).le
    _ = (∑ i : Fin d, ‖e i x‖ ^ 2) * exp (-(n : ℝ) * φ x) * (∑ i : Fin d, ‖c i‖ ^ 2) := by ring

/-- **Sup-Norm vs. `L²`-Norm Comparison (`SupNormAgainstL2`)**:
A uniform Bergman bound `B_n(x) ≤ C n^D` directly yields `‖s(x)‖_{φ, n} ≤ √C · n^{D/2} · ‖s‖_{L²}`. -/
theorem sup_norm_le_sqrt_bergman_mul_L2 {X : Type*} {d D : ℕ} (φ : X → ℝ) (n : ℕ)
    (e : Fin d → X → ℂ) (c : Fin d → ℂ) {C : ℝ} (hC : 0 ≤ C)
    (hB : ∀ x, bergmanKernel φ n e x ≤ C * (n : ℝ) ^ D) (x : X) :
    Real.sqrt (ptNormSq φ n (fun y => ∑ i : Fin d, c i * e i y) x) ≤
      Real.sqrt C * Real.sqrt ((n : ℝ) ^ D) * Real.sqrt (∑ i : Fin d, ‖c i‖ ^ 2) := by
  have h1 : ptNormSq φ n (fun y => ∑ i : Fin d, c i * e i y) x ≤
      C * (n : ℝ) ^ D * (∑ i : Fin d, ‖c i‖ ^ 2) :=
    le_trans (bergman_extremal_bound φ n e c x)
      (mul_le_mul_of_nonneg_right (hB x) (Finset.sum_nonneg fun i _ => sq_nonneg _))
  calc Real.sqrt (ptNormSq φ n (fun y => ∑ i : Fin d, c i * e i y) x)
      ≤ Real.sqrt (C * (n : ℝ) ^ D * (∑ i : Fin d, ‖c i‖ ^ 2)) := Real.sqrt_le_sqrt h1
    _ = Real.sqrt (C * (n : ℝ) ^ D) * Real.sqrt (∑ i : Fin d, ‖c i‖ ^ 2) :=
        Real.sqrt_mul (mul_nonneg hC (pow_nonneg (Nat.cast_nonneg n) D)) _
    _ = Real.sqrt C * Real.sqrt ((n : ℝ) ^ D) * Real.sqrt (∑ i : Fin d, ‖c i‖ ^ 2) := by
        rw [Real.sqrt_mul hC]

/-- One-dimensional Gaussian disc mass `∫_{|z| ≤ R} e^{-λ |z|²} dA(z) = π (1 - e^{-λ R²}) / λ`
(continuously extended to `π R²` at `λ = 0`), matching `StatementsBergman.lean`. -/
def gaussDiscMass (lam R : ℝ) : ℝ :=
  if lam = 0 then π * R ^ 2 else π * (1 - exp (-lam * R ^ 2)) / lam

theorem gaussDiscMass_pos {lam R : ℝ} (hlam : 0 ≤ lam) (hR : 0 < R) :
    0 < gaussDiscMass lam R := by
  unfold gaussDiscMass
  split_ifs with h0
  · positivity
  · have hpos : 0 < lam := lt_of_le_of_ne hlam (Ne.symm h0)
    have hexp : exp (-lam * R ^ 2) < 1 := exp_lt_one_iff.mpr (by nlinarith [sq_pos_of_pos hR])
    have hnum : 0 < 1 - exp (-lam * R ^ 2) := sub_pos.mpr hexp
    positivity

theorem gaussDiscMass_le_pi_mul_sq {lam R : ℝ} (hlam : 0 ≤ lam) :
    gaussDiscMass lam R ≤ π * R ^ 2 := by
  unfold gaussDiscMass
  split_ifs with h0
  · exact le_rfl
  · have hpos : 0 < lam := lt_of_le_of_ne hlam (Ne.symm h0)
    rw [div_le_iff₀ hpos]
    have h1 : 1 - lam * R ^ 2 ≤ exp (-lam * R ^ 2) := by
      have := add_one_le_exp (-lam * R ^ 2)
      linarith
    have h2 : 1 - exp (-lam * R ^ 2) ≤ lam * R ^ 2 := by linarith
    have hpi : 0 ≤ π := pi_pos.le
    nlinarith

theorem gaussDiscMass_le_pi_div {lam R : ℝ} (hlam : 0 < lam) :
    gaussDiscMass lam R ≤ π / lam := by
  unfold gaussDiscMass
  rw [if_neg hlam.ne']
  refine div_le_div_of_nonneg_right ?_ hlam.le
  have h1 : 1 - exp (-lam * R ^ 2) ≤ 1 := by linarith [exp_pos (-lam * R ^ 2)]
  nlinarith [pi_pos]

/-- Auxiliary monotonicity of `t ↦ (1 - e^{-t}) / t` for `t > 0`. -/
private lemma one_sub_exp_neg_div_antitone {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (1 - exp (-b)) / b ≤ (1 - exp (-a)) / a := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  rw [div_le_div_iff₀ hb ha]
  have h1 : 0 ≤ b - a := sub_nonneg.mpr hab
  have h2 : 1 + a ≤ exp a := by linarith [add_one_le_exp a]
  have h3 : 1 + b ≤ exp b := by linarith [add_one_le_exp b]
  -- Directly verify `a (1 - e^{-b}) ≤ b (1 - e^{-a})` via `b e^{-a} - a e^{-b} ≤ b - a`.
  -- Multiply by `e^{a + b} > 0`: equivalent to `b e^b - a e^a ≤ (b - a) e^{a+b}`,
  -- i.e. `b e^b (1 - e^a) + a e^a (e^b - 1) ≤ 0`... wait, check the convex slope directly:
  -- For `g(t) = (1 - e^{-t}) / t`, `g(b) ≤ g(a)` follows from concavity of `f(t) = 1 - e^{-t}`
  -- with `f(0) = 0`: `a * (1 - e^{-b}) ≤ b * (1 - e^{-a})`.
  have hconc : a * (1 - exp (-b)) ≤ b * (1 - exp (-a)) := by
    set θ := a / b
    have hθ0 : 0 ≤ θ := div_nonneg ha.le hb.le
    have hθ1 : θ ≤ 1 := (div_le_one hb).mpr hab
    have h1θ : 0 ≤ 1 - θ := sub_nonneg.mpr hθ1
    have hconv : exp (-(θ * b + (1 - θ) * 0)) ≤ θ * exp (-b) + (1 - θ) * exp 0 := by
      have h := convexOn_exp.2 (Set.mem_univ (-b)) (Set.mem_univ (0 : ℝ)) hθ0 h1θ (by ring)
      simpa [smul_eq_mul, mul_neg] using h
    have hθb : θ * b = a := div_mul_cancel₀ a hb.ne'
    rw [hθb, mul_zero, add_zero, exp_zero, mul_one] at hconv
    have hmul := mul_le_mul_of_nonneg_left hconv hb.le
    have hleft : b * (θ * exp (-b) + (1 - θ)) = a * exp (-b) + (b - a) := by
      dsimp only [θ]
      field_simp [hb.ne']
    rw [hleft] at hmul
    linarith
  linarith [hconc]

/-- **Curvature Monotonicity of Gaussian Polydisc Mass**:
Larger curvature `λ₁ ≤ λ₂` shrinks the local Gaussian disc mass `gaussDiscMass λ₂ R ≤ gaussDiscMass λ₁ R`. -/
theorem gaussDiscMass_antitone {R lam₁ lam₂ : ℝ} (hR : 0 < R) (h1 : 0 ≤ lam₁) (hle : lam₁ ≤ lam₂) :
    gaussDiscMass lam₂ R ≤ gaussDiscMass lam₁ R := by
  by_cases h10 : lam₁ = 0
  · subst h10
    have h2 : 0 ≤ lam₂ := hle
    simpa [gaussDiscMass] using gaussDiscMass_le_pi_mul_sq (R := R) h2
  · have h1pos : 0 < lam₁ := lt_of_le_of_ne h1 (Ne.symm h10)
    have h2pos : 0 < lam₂ := lt_of_lt_of_le h1pos hle
    unfold gaussDiscMass
    rw [if_neg h2pos.ne', if_neg h1pos.ne']
    have hR2 : 0 < R ^ 2 := sq_pos_of_pos hR
    have hanti := one_sub_exp_neg_div_antitone (mul_pos h1pos hR2)
      (mul_le_mul_of_nonneg_right hle hR2.le)
    have hpi : 0 ≤ π * R ^ 2 := by positivity
    have hmul := mul_le_mul_of_nonneg_left hanti hpi
    have hL : π * R ^ 2 * ((1 - exp (-(lam₂ * R ^ 2))) / (lam₂ * R ^ 2)) =
        π * (1 - exp (-lam₂ * R ^ 2)) / lam₂ := by
      rw [neg_mul]
      field_simp [h2pos.ne', hR2.ne']
    have hR' : π * R ^ 2 * ((1 - exp (-(lam₁ * R ^ 2))) / (lam₁ * R ^ 2)) =
        π * (1 - exp (-lam₁ * R ^ 2)) / lam₁ := by
      rw [neg_mul]
      field_simp [h1pos.ne', hR2.ne']
    linarith

/-- Local Bergman upper bound deduced directly from a polydisc submean-value inequality. -/
theorem bergman_upper_of_polydisc_submean {D n : ℕ} {lam : Fin D → ℝ} {R f0Sq l2Sq : ℝ}
    (hn : 0 < n) (hR : 0 < R) (hlam : ∀ j, 0 ≤ lam j)
    (hsub : f0Sq * ((n : ℝ) ^ D)⁻¹ * (∏ j, gaussDiscMass (lam j) R) ≤ l2Sq) :
    f0Sq ≤ (∏ j, (gaussDiscMass (lam j) R)⁻¹) * (n : ℝ) ^ D * l2Sq := by
  have hprod_pos : 0 < ∏ j, gaussDiscMass (lam j) R :=
    Finset.prod_pos fun j _ => gaussDiscMass_pos (hlam j) hR
  have hn_pos : (0 : ℝ) < (n : ℝ) ^ D := pow_pos (Nat.cast_pos.mpr hn) D
  have hfac_pos : 0 < ((n : ℝ) ^ D)⁻¹ * ∏ j, gaussDiscMass (lam j) R := by positivity
  have h1 : f0Sq ≤ l2Sq / (((n : ℝ) ^ D)⁻¹ * ∏ j, gaussDiscMass (lam j) R) := by
    rw [le_div_iff₀ hfac_pos]
    linarith
  have hinv : (∏ j, (gaussDiscMass (lam j) R)⁻¹) * (n : ℝ) ^ D * l2Sq =
      l2Sq / (((n : ℝ) ^ D)⁻¹ * ∏ j, gaussDiscMass (lam j) R) := by
    rw [Finset.prod_inv_distrib]
    field_simp [hprod_pos.ne', hn_pos.ne']
  linarith

/-- **Dominated Bergman `L¹` Convergence Theorem (`L1Convergence.Statement`)**:
If `0 ≤ g n ≤ C` are integrable on a finite measure space `(Ω, μ)`, `limsup g n ≤ b` pointwise,
and `liminf ∫ g n ≥ ∫ b`, then `∫ |g n - b| dμ → 0`.
(Directly proves `GroundTheory.Heights₂.Heights.HilbertSamuel.L1Convergence.Statement`!) -/
theorem tendsto_L1_of_limsup_le_and_integral_ge
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (g : ℕ → Ω → ℝ) (b : Ω → ℝ) (C : ℝ)
    (hg_int : ∀ n, Integrable (g n) μ) (hb_int : Integrable b μ)
    (hg_bnd : ∀ n x, 0 ≤ g n x ∧ g n x ≤ C)
    (hupper : ∀ (x : Ω) (ε : ℝ), 0 < ε → ∀ᶠ n in atTop, g n x ≤ b x + ε)
    (hlower : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∫ x, b x ∂μ - ε ≤ ∫ x, g n x ∂μ) :
    Tendsto (fun n => ∫ x, |g n x - b x| ∂μ) atTop (𝓝 0) := by
  let posPart : ℕ → Ω → ℝ := fun n x => max (g n x - b x) 0
  have hpos_int : ∀ n, Integrable (posPart n) μ := fun n =>
    ((hg_int n).sub hb_int).sup (integrable_const (0 : ℝ))
  by_cases hΩ : Nonempty Ω
  · obtain ⟨x₀⟩ := hΩ
    have hC_nonneg : 0 ≤ C := le_trans (hg_bnd 0 x₀).1 (hg_bnd 0 x₀).2
    have hpos_lim : ∀ x : Ω, Tendsto (fun n => posPart n x) atTop (𝓝 0) := by
      intro x
      rw [Metric.tendsto_atTop]
      intro ε hε
      obtain ⟨N, hN⟩ := eventually_atTop.mp (hupper x (ε / 2) (half_pos hε))
      refine ⟨N, fun n hn => ?_⟩
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (le_max_right _ _)]
      have hgn := hN n hn
      exact lt_of_le_of_lt (max_le (by linarith) (by positivity)) (half_lt_self hε)
    have hbound_int : Integrable (fun x => C + |b x|) μ :=
      (integrable_const C).add hb_int.abs
    have hpos_dom : ∀ n, ∀ᵐ x ∂μ, ‖posPart n x‖ ≤ C + |b x| := by
      intro n
      refine ae_of_all μ fun x => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
      refine max_le ?_ (by positivity)
      have h1 : g n x ≤ C := (hg_bnd n x).2
      have h2 : -b x ≤ |b x| := neg_le_abs (b x)
      linarith
    have hpos_int_lim : Tendsto (fun n => ∫ x, posPart n x ∂μ) atTop (𝓝 0) := by
      have h := MeasureTheory.tendsto_integral_of_dominated_convergence (fun x => C + |b x|)
        (fun n => (hpos_int n).aestronglyMeasurable) hbound_int hpos_dom
        (ae_of_all μ hpos_lim)
      simpa using h
    have habs_eq : ∀ n x, |g n x - b x| = (b x - g n x) + 2 * posPart n x := by
      intro n x
      dsimp only [posPart]
      rcases le_total (g n x - b x) 0 with h | h
      · rw [abs_of_nonpos h, max_eq_right h]; ring
      · rw [abs_of_nonneg h, max_eq_left h]; ring
    have hint_eq : ∀ n, ∫ x, |g n x - b x| ∂μ =
        (∫ x, b x ∂μ - ∫ x, g n x ∂μ) + 2 * ∫ x, posPart n x ∂μ := by
      intro n
      calc ∫ x, |g n x - b x| ∂μ
          = ∫ x, ((b x - g n x) + 2 * posPart n x) ∂μ :=
            MeasureTheory.integral_congr_ae (ae_of_all μ (habs_eq n))
        _ = (∫ x, (b x - g n x) ∂μ) + ∫ x, (2 * posPart n x) ∂μ :=
            MeasureTheory.integral_add (hb_int.sub (hg_int n)) ((hpos_int n).const_mul 2)
        _ = (∫ x, b x ∂μ - ∫ x, g n x ∂μ) + 2 * ∫ x, posPart n x ∂μ := by
            rw [MeasureTheory.integral_sub hb_int (hg_int n), MeasureTheory.integral_const_mul]
    rw [Metric.tendsto_atTop]
    intro ε hε
    have h1 := hlower (ε / 2) (half_pos hε)
    have h2 : ∀ᶠ n in atTop, ∫ x, posPart n x ∂μ < ε / 4 := by
      have h := (Metric.tendsto_atTop.mp hpos_int_lim) (ε / 4) (by linarith)
      obtain ⟨N, hN⟩ := h
      exact eventually_atTop.mpr ⟨N, fun n hn => by
        have hlt := hN n hn
        rw [Real.dist_eq, sub_zero] at hlt
        exact lt_of_le_of_lt (le_abs_self _) hlt⟩
    obtain ⟨N, hN⟩ := eventually_atTop.mp (h1.and h2)
    refine ⟨N, fun n hn => ?_⟩
    obtain ⟨hlow, hpos⟩ := hN n hn
    have hnonneg : 0 ≤ ∫ x, |g n x - b x| ∂μ :=
      MeasureTheory.integral_nonneg fun x => abs_nonneg _
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg, hint_eq n]
    linarith
  · rw [not_nonempty_iff] at hΩ
    have hz : ∀ n, ∫ x, |g n x - b x| ∂μ = 0 := fun n =>
      MeasureTheory.integral_eq_zero_of_ae (ae_of_all μ fun x => isEmptyElim x)
    simp [hz]

/-! ## Section 4: Chern–Weil Metric-Change Degree Comparison & Volume-Integral Monotonicity -/

/-- Monotonicity of pointwise Hermitian norms under metric weight increase (`φ₁ ≤ φ₂`). -/
theorem ptNormSq_antitone_weight {X : Type*} {φ₁ φ₂ : X → ℝ} (n : ℕ) (s : X → ℂ)
    (hφ : ∀ x, φ₁ x ≤ φ₂ x) (x : X) :
    ptNormSq φ₂ n s x ≤ ptNormSq φ₁ n s x := by
  unfold ptNormSq
  refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
  exact exp_le_exp.mpr (by nlinarith [hφ x])

/-- **Plurisubharmonic / Subharmonic Volume-Integral Monotonicity**:
For any non-negative density `ρ ≥ 0`, increasing the potential `φ₁ ≤ φ₂` decreases the
weighted volume integral `∫ ρ(x) e^{-n φ(x)} dμ`. -/
theorem plurisubharmonic_volume_integral_antitone {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {ρ φ₁ φ₂ : X → ℝ} (n : ℕ) (hρ : ∀ x, 0 ≤ ρ x) (hφ : ∀ x, φ₁ x ≤ φ₂ x)
    (h1 : Integrable (fun x => ρ x * exp (-(n : ℝ) * φ₁ x)) μ)
    (h2 : Integrable (fun x => ρ x * exp (-(n : ℝ) * φ₂ x)) μ) :
    ∫ x, ρ x * exp (-(n : ℝ) * φ₂ x) ∂μ ≤ ∫ x, ρ x * exp (-(n : ℝ) * φ₁ x) ∂μ := by
  refine MeasureTheory.integral_mono h2 h1 fun x => ?_
  refine mul_le_mul_of_nonneg_left ?_ (hρ x)
  exact exp_le_exp.mpr (by nlinarith [hφ x])

/-- Upper comparison of global `L²` norms when `φ₁ - φ₀ ≥ uMin`. -/
theorem l2NormSq_le_of_weight_sub_ge {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {φ₀ φ₁ : X → ℝ} (n : ℕ) (s : X → ℂ) {uMin : ℝ}
    (hu : ∀ x, uMin ≤ φ₁ x - φ₀ x)
    (h0 : Integrable (ptNormSq φ₀ n s) μ) (h1 : Integrable (ptNormSq φ₁ n s) μ) :
    l2NormSq μ φ₁ n s ≤ exp (-(n : ℝ) * uMin) * l2NormSq μ φ₀ n s := by
  unfold l2NormSq
  rw [← MeasureTheory.integral_const_mul]
  refine MeasureTheory.integral_mono h1 (h0.const_mul _) fun x => ?_
  unfold ptNormSq
  have hexp : exp (-(n : ℝ) * φ₁ x) ≤ exp (-(n : ℝ) * uMin) * exp (-(n : ℝ) * φ₀ x) := by
    rw [← exp_add]
    exact exp_le_exp.mpr (by nlinarith [hu x])
  have hmul := mul_le_mul_of_nonneg_left hexp (sq_nonneg ‖s x‖)
  linarith

/-- Lower comparison of global `L²` norms when `φ₁ - φ₀ ≤ uMax`. -/
theorem l2NormSq_ge_of_weight_sub_le {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {φ₀ φ₁ : X → ℝ} (n : ℕ) (s : X → ℂ) {uMax : ℝ}
    (hu : ∀ x, φ₁ x - φ₀ x ≤ uMax)
    (h0 : Integrable (ptNormSq φ₀ n s) μ) (h1 : Integrable (ptNormSq φ₁ n s) μ) :
    exp (-(n : ℝ) * uMax) * l2NormSq μ φ₀ n s ≤ l2NormSq μ φ₁ n s := by
  unfold l2NormSq
  rw [← MeasureTheory.integral_const_mul]
  refine MeasureTheory.integral_mono (h0.const_mul _) h1 fun x => ?_
  unfold ptNormSq
  have hexp : exp (-(n : ℝ) * uMax) * exp (-(n : ℝ) * φ₀ x) ≤ exp (-(n : ℝ) * φ₁ x) := by
    rw [← exp_add]
    exact exp_le_exp.mpr (by nlinarith [hu x])
  have hmul := mul_le_mul_of_nonneg_left hexp (sq_nonneg ‖s x‖)
  linarith

/-- Bott–Chern / Chern–Weil metric-change integral
`∫₀¹ ∫_X u(x) · dens(t, x) dμ dt` interpolating between two Hermitian metrics `φ₀` and `φ₁`
with difference `u = φ₁ - φ₀`. -/
def chernWeilChange {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (u : X → ℝ) (dens : ℝ → X → ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..1, ∫ x, u x * dens t x ∂μ

/-- Monotonicity of the Chern–Weil metric-change functional in the potential shift `u`. -/
theorem chernWeilChange_mono {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {u₁ u₂ : X → ℝ} {dens : ℝ → X → ℝ}
    (hu : ∀ x, u₁ x ≤ u₂ x) (hd : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x, 0 ≤ dens t x)
    (hint₁ : ∀ t ∈ Set.Icc (0 : ℝ) 1, Integrable (fun x => u₁ x * dens t x) μ)
    (hint₂ : ∀ t ∈ Set.Icc (0 : ℝ) 1, Integrable (fun x => u₂ x * dens t x) μ)
    (hI₁ : IntervalIntegrable (fun t => ∫ x, u₁ x * dens t x ∂μ) volume 0 1)
    (hI₂ : IntervalIntegrable (fun t => ∫ x, u₂ x * dens t x ∂μ) volume 0 1) :
    chernWeilChange μ u₁ dens ≤ chernWeilChange μ u₂ dens := by
  unfold chernWeilChange
  refine intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1) hI₁ hI₂ fun t ht => ?_
  exact MeasureTheory.integral_mono (hint₁ t ht) (hint₂ t ht) fun x =>
    mul_le_mul_of_nonneg_right (hu x) (hd t ht x)

/-- **Chern–Weil Degree Comparison Bracket**:
If `uMin ≤ u(x) ≤ uMax` and the interpolated curvature density integrates to total volume `vol`
at every `t ∈ [0, 1]`, then `uMin * vol ≤ chernWeilChange μ u dens ≤ uMax * vol`. -/
theorem chernWeilChange_bounds {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {u : X → ℝ} {dens : ℝ → X → ℝ} {uMin uMax vol : ℝ}
    (huMin : ∀ x, uMin ≤ u x) (huMax : ∀ x, u x ≤ uMax)
    (hd : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x, 0 ≤ dens t x)
    (hd_int : ∀ t ∈ Set.Icc (0 : ℝ) 1, Integrable (dens t) μ)
    (hu_int : ∀ t ∈ Set.Icc (0 : ℝ) 1, Integrable (fun x => u x * dens t x) μ)
    (hvol : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∫ x, dens t x ∂μ = vol)
    (hI : IntervalIntegrable (fun t => ∫ x, u x * dens t x ∂μ) volume 0 1) :
    uMin * vol ≤ chernWeilChange μ u dens ∧ chernWeilChange μ u dens ≤ uMax * vol := by
  have hconst_int : ∀ c : ℝ, IntervalIntegrable (fun _ : ℝ => c * vol) volume 0 1 := fun _ =>
    intervalIntegrable_const
  have hconst_eval : ∀ c : ℝ, ∫ _t in (0 : ℝ)..1, c * vol = c * vol := fun c => by
    simp
  refine ⟨?_, ?_⟩
  · rw [← hconst_eval uMin]
    unfold chernWeilChange
    refine intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1)
      (hconst_int uMin) hI fun t ht => ?_
    rw [← hvol t ht, ← MeasureTheory.integral_const_mul]
    exact MeasureTheory.integral_mono ((hd_int t ht).const_mul uMin) (hu_int t ht) fun x =>
      mul_le_mul_of_nonneg_right (huMin x) (hd t ht x)
  · rw [← hconst_eval uMax]
    unfold chernWeilChange
    refine intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1)
      hI (hconst_int uMax) fun t ht => ?_
    rw [← hvol t ht, ← MeasureTheory.integral_const_mul]
    exact MeasureTheory.integral_mono (hu_int t ht) ((hd_int t ht).const_mul uMax) fun x =>
      mul_le_mul_of_nonneg_right (huMax x) (hd t ht x)

/-- Arithmetic Euler characteristic metric-change comparison (matching `MetricChange.Statement`):
bounding `χ(W₁) - χ(W₀)` directly in terms of `chernWeilChange` and the Bergman volume `vol`. -/
theorem chi_metric_change_bounds {D n : ℕ} {chi₀ chi₁ cw uMin uMax vol ε : ℝ}
    (hM : |chi₁ - chi₀ - (n : ℝ) ^ (D + 1) / 2 * cw| ≤ ε * (n : ℝ) ^ (D + 1))
    (hcw : uMin * vol ≤ cw ∧ cw ≤ uMax * vol) :
    ((uMin * vol / 2) - ε) * (n : ℝ) ^ (D + 1) ≤ chi₁ - chi₀ ∧
      chi₁ - chi₀ ≤ ((uMax * vol / 2) + ε) * (n : ℝ) ^ (D + 1) := by
  have hn : 0 ≤ (n : ℝ) ^ (D + 1) := pow_nonneg (Nat.cast_nonneg n) (D + 1)
  have habs := abs_le.mp hM
  constructor <;> nlinarith [hcw.1, hcw.2, habs.1, habs.2]

/-! ## Section 5: Sharp Iterated Curvature / Norm Recursion (`RecursionSharp`) -/

/-- Auxiliary convexity bound on `[0, 1]`: `exp (4 x) ≤ 1 + 55 * x`. -/
private lemma exp_four_mul_le_one_add_55 {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    exp (4 * x) ≤ 1 + 55 * x := by
  have hconv : exp (x * 4 + (1 - x) * 0) ≤ x * exp 4 + (1 - x) * exp 0 := by
    have h := convexOn_exp.2 (Set.mem_univ (4 : ℝ)) (Set.mem_univ (0 : ℝ)) hx0 (sub_nonneg.mpr hx1)
      (by ring)
    simpa [smul_eq_mul] using h
  rw [mul_zero, add_zero, exp_zero, mul_one, mul_comm x 4] at hconv
  have he1 : exp 1 < 2.72 := lt_trans exp_one_lt_d9 (by norm_num)
  have he4 : exp 4 < 56 := by
    have h4 : exp 4 = (exp 1) ^ 4 := by rw [← exp_nat_mul]; norm_num
    rw [h4]
    have h1 : (exp 1) ^ 4 < (2.72 : ℝ) ^ 4 :=
      pow_lt_pow_left₀ he1 (exp_pos 1).le (by norm_num)
    linarith [show (2.72 : ℝ) ^ 4 < 56 by norm_num]
  nlinarith

/-- **Sharp Iterated Curvature / Norm Recursion (`Formalism.HermitianCurvature.Statement.RecursionSharp`)**:
Direct inductive proof with explicit constant `C = 55` (replacing multi-file recursion wrappers). -/
theorem recursion_sharp_bound :
    ∀ (r : ℕ) (a ε : ℝ) (e σ : ℕ → ℝ),
      0 ≤ a → a ≤ 1 / 2 → 0 ≤ ε → ((r : ℝ) + 1) * (ε + a) ≤ 1 →
      (∀ i, 0 ≤ e i) → (∀ i, 0 ≤ σ i) →
      (∀ i, 1 ≤ i → i ≤ r + 1 →
        σ i ≤ (1 + ε) * √(1 + e i) * σ (i - 1) + ∑ t ∈ Icc 2 i, a ^ (t - 1) * σ (i - t)) →
      σ (r + 1) ^ 2 ≤
        (1 + 55 * ((r : ℝ) + 1) * (ε + a)) * (∏ i ∈ Icc 1 (r + 1), (1 + e i)) * σ 0 ^ 2 := by
  intro r a ε e σ ha ha2 hε hsmall he hσ hrec
  let P : ℕ → ℝ := fun k => ∏ j ∈ Icc 1 k, √(1 + e j)
  have hP_pos : ∀ k, 0 < P k := fun k =>
    Finset.prod_pos fun j _ => Real.sqrt_pos.mpr (by linarith [he j])
  have hP_succ : ∀ k, P (k + 1) = P k * √(1 + e (k + 1)) := by
    intro k
    dsimp only [P]
    have hmem : k + 1 ∉ Icc 1 k := by simp
    have hinsert : Icc 1 (k + 1) = insert (k + 1) (Icc 1 k) := by
      ext m
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    rw [hinsert, Finset.prod_insert hmem, mul_comm]
  have hP_mono : ∀ {j k}, j ≤ k → P j ≤ P k := by
    intro j k hjk
    induction k with
    | zero =>
      have hj0 : j = 0 := Nat.le_zero.mp hjk
      subst hj0; exact le_rfl
    | succ k ih =>
      rcases Nat.lt_or_eq_of_le hjk with hlt | rfl
      · have h1 : P j ≤ P k := ih (Nat.lt_succ_iff.mp hlt)
        have hsqrt : 1 ≤ √(1 + e (k + 1)) := Real.one_le_sqrt.mpr (by linarith [he (k + 1)])
        rw [hP_succ k]
        nlinarith [hP_pos k]
      · exact le_rfl
  let τ : ℕ → ℝ := fun k => σ k / P k
  have hτ_nonneg : ∀ k, 0 ≤ τ k := fun k => div_nonneg (hσ k) (hP_pos k).le
  have hτ0 : τ 0 = σ 0 := by simp [τ, P]
  let q : ℝ := 1 + ε + 2 * a
  have hq_ge_one : 1 ≤ q := by dsimp only [q]; linarith
  have hstep : ∀ k, k ≤ r + 1 → ∀ j ≤ k, τ j ≤ q ^ k * σ 0 := by
    intro k hk
    induction k with
    | zero =>
      intro j hj
      have hj0 : j = 0 := Nat.le_zero.mp hj
      subst hj0
      simp [hτ0]
    | succ k ih =>
      intro j hj
      have hk' : k ≤ r + 1 := Nat.le_of_succ_le hk
      rcases Nat.lt_or_eq_of_le hj with hlt | rfl
      · have hjle : j ≤ k := Nat.lt_succ_iff.mp hlt
        calc τ j
            ≤ q ^ k * σ 0 := ih hk' j hjle
          _ ≤ q ^ (k + 1) * σ 0 := by
              rw [pow_succ]
              have hqk : 0 ≤ q ^ k := pow_nonneg (by linarith) k
              exact mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hqk hq_ge_one) (hσ 0)
      · have hrec_k := hrec (k + 1) (Nat.succ_le_succ (Nat.zero_le k)) hk
        have hPpos := hP_pos (k + 1)
        have hdiv : τ (k + 1) ≤ (1 + ε) * τ k + ∑ t ∈ Icc 2 (k + 1), a ^ (t - 1) * τ (k + 1 - t) := by
          dsimp only [τ]
          rw [div_le_iff₀ hPpos]
          calc σ (k + 1)
              ≤ (1 + ε) * √(1 + e (k + 1)) * σ k +
                  ∑ t ∈ Icc 2 (k + 1), a ^ (t - 1) * σ (k + 1 - t) := by
                simpa using hrec_k
            _ ≤ (1 + ε) * (σ k / P k) * P (k + 1) +
                  (∑ t ∈ Icc 2 (k + 1), a ^ (t - 1) * (σ (k + 1 - t) / P (k + 1 - t))) *
                    P (k + 1) := by
                refine add_le_add ?_ ?_
                · rw [hP_succ k]
                  have hPk := (hP_pos k).ne'
                  have h1 : (1 + ε) * (σ k / P k) * (P k * √(1 + e (k + 1))) =
                      (1 + ε) * √(1 + e (k + 1)) * σ k := by
                    field_simp [hPk]
                  linarith
                · rw [Finset.sum_mul]
                  refine Finset.sum_le_sum fun t ht => ?_
                  have hleP : P (k + 1 - t) ≤ P (k + 1) := hP_mono (Nat.sub_le (k + 1) t)
                  have hPt := hP_pos (k + 1 - t)
                  have h1 : σ (k + 1 - t) ≤ σ (k + 1 - t) / P (k + 1 - t) * P (k + 1) := by
                    rw [div_mul_eq_mul_div, le_div_iff₀ hPt]
                    exact mul_le_mul_of_nonneg_left hleP (hσ _)
                  have ha_pow : 0 ≤ a ^ (t - 1) := pow_nonneg ha _
                  nlinarith
            _ = ((1 + ε) * (σ k / P k) +
                  ∑ t ∈ Icc 2 (k + 1), a ^ (t - 1) * (σ (k + 1 - t) / P (k + 1 - t))) *
                    P (k + 1) := by ring
        have hgeom : ∑ t ∈ Icc 2 (k + 1), a ^ (t - 1) ≤ 2 * a := by
          have hsub : ∀ t ∈ Icc 2 (k + 1), a ^ (t - 1) ≤ a * (1 / 2 : ℝ) ^ (t - 2) := by
            intro t ht
            simp only [Finset.mem_Icc] at ht
            have ht1 : t - 1 = (t - 2) + 1 := by omega
            rw [ht1, pow_succ, mul_comm]
            exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha ha2 (t - 2)) ha
          calc ∑ t ∈ Icc 2 (k + 1), a ^ (t - 1)
              ≤ ∑ t ∈ Icc 2 (k + 1), a * (1 / 2 : ℝ) ^ (t - 2) := Finset.sum_le_sum hsub
            _ = a * ∑ t ∈ Icc 2 (k + 1), (1 / 2 : ℝ) ^ (t - 2) := (Finset.mul_sum _ _ _).symm
            _ ≤ a * 2 := by
                refine mul_le_mul_of_nonneg_left ?_ ha
                have hshift : ∑ t ∈ Icc 2 (k + 1), (1 / 2 : ℝ) ^ (t - 2) =
                    ∑ m ∈ Finset.range k, (1 / 2 : ℝ) ^ m := by
                  refine Finset.sum_bij (fun t _ => t - 2) ?_ ?_ ?_ ?_
                  · intro t ht; simp only [Finset.mem_Icc, Finset.mem_range] at ht ⊢; omega
                  · intro t₁ ht₁ t₂ ht₂ h
                    simp only [Finset.mem_Icc] at ht₁ ht₂; omega
                  · intro m hm
                    simp only [Finset.mem_range] at hm
                    refine ⟨m + 2, by simp only [Finset.mem_Icc]; omega, by omega⟩
                  · intro t _; rfl
                rw [hshift, geom_sum_eq (by norm_num : (1 / 2 : ℝ) ≠ 1)]
                have hpow : 0 ≤ (1 / 2 : ℝ) ^ k := by positivity
                have hgeo : ((1 / 2 : ℝ) ^ k - 1) / (1 / 2 - 1) = 2 - 2 * (1 / 2 : ℝ) ^ k := by
                  ring
                linarith
            _ = 2 * a := by ring
        have hsum_le : ∑ t ∈ Icc 2 (k + 1), a ^ (t - 1) * τ (k + 1 - t) ≤
            (∑ t ∈ Icc 2 (k + 1), a ^ (t - 1)) * (q ^ k * σ 0) := by
          rw [Finset.sum_mul]
          refine Finset.sum_le_sum fun t ht => ?_
          simp only [Finset.mem_Icc] at ht
          have hle_k : k + 1 - t ≤ k := by omega
          exact mul_le_mul_of_nonneg_left (ih hk' (k + 1 - t) hle_k) (pow_nonneg ha _)
        have hτk : τ k ≤ q ^ k * σ 0 := ih hk' k le_rfl
        have hqkσ : 0 ≤ q ^ k * σ 0 := mul_nonneg (pow_nonneg (by linarith) k) (hσ 0)
        calc τ (k + 1)
            ≤ (1 + ε) * τ k + ∑ t ∈ Icc 2 (k + 1), a ^ (t - 1) * τ (k + 1 - t) := hdiv
          _ ≤ (1 + ε) * (q ^ k * σ 0) + (2 * a) * (q ^ k * σ 0) := by
              nlinarith [hsum_le, hgeom]
          _ = q ^ (k + 1) * σ 0 := by
              dsimp only [q]
              rw [pow_succ]
              ring
  have hτ_final : τ (r + 1) ≤ q ^ (r + 1) * σ 0 := hstep (r + 1) le_rfl (r + 1) le_rfl
  have hσ_final : σ (r + 1) ≤ q ^ (r + 1) * σ 0 * P (r + 1) := by
    have h := (div_le_iff₀ (hP_pos (r + 1))).mp hτ_final
    exact h
  have hsq : σ (r + 1) ^ 2 ≤ (q ^ (r + 1)) ^ 2 * P (r + 1) ^ 2 * σ 0 ^ 2 := by
    have h1 := pow_le_pow_left₀ (hσ (r + 1)) hσ_final 2
    nlinarith [h1]
  have hP_sq : P (r + 1) ^ 2 = ∏ i ∈ Icc 1 (r + 1), (1 + e i) := by
    dsimp only [P]
    rw [← Finset.prod_pow]
    refine Finset.prod_congr rfl fun i _ => Real.sq_sqrt (by linarith [he i])
  have hq_exp : (q ^ (r + 1)) ^ 2 ≤ 1 + 55 * ((r : ℝ) + 1) * (ε + a) := by
    have h1 : q ≤ exp (ε + 2 * a) := by
      dsimp only [q]
      linarith [add_one_le_exp (ε + 2 * a)]
    have h2 : (q ^ (r + 1)) ^ 2 ≤ exp (2 * ((r : ℝ) + 1) * (ε + 2 * a)) := by
      calc (q ^ (r + 1)) ^ 2
          = q ^ (2 * (r + 1)) := by rw [← pow_mul, mul_comm]
        _ ≤ (exp (ε + 2 * a)) ^ (2 * (r + 1)) := pow_le_pow_left₀ (by linarith) h1 _
        _ = exp ((2 * (r + 1) : ℕ) * (ε + 2 * a)) := (exp_nat_mul _ _).symm
        _ = exp (2 * ((r : ℝ) + 1) * (ε + 2 * a)) := by push_cast; ring_nf
    have h3 : 2 * ((r : ℝ) + 1) * (ε + 2 * a) ≤ 4 * (((r : ℝ) + 1) * (ε + a)) := by
      have hr : (0 : ℝ) ≤ (r : ℝ) + 1 := by positivity
      nlinarith
    have h4 : exp (4 * (((r : ℝ) + 1) * (ε + a))) ≤ 1 + 55 * (((r : ℝ) + 1) * (ε + a)) :=
      exp_four_mul_le_one_add_55 (by positivity) hsmall
    calc (q ^ (r + 1)) ^ 2
        ≤ exp (2 * ((r : ℝ) + 1) * (ε + 2 * a)) := h2
      _ ≤ exp (4 * (((r : ℝ) + 1) * (ε + a))) := exp_le_exp.mpr h3
      _ ≤ 1 + 55 * (((r : ℝ) + 1) * (ε + a)) := h4
      _ = 1 + 55 * ((r : ℝ) + 1) * (ε + a) := by ring
  rw [hP_sq] at hsq
  have hP_prod_nonneg : 0 ≤ (∏ i ∈ Icc 1 (r + 1), (1 + e i)) * σ 0 ^ 2 := by
    refine mul_nonneg ?_ (sq_nonneg _)
    exact Finset.prod_nonneg fun i _ => by linarith [he i]
  have hmul := mul_le_mul_of_nonneg_right hq_exp hP_prod_nonneg
  linarith

/-! ## Section 6: Moriwaki Bigness, Arithmetic Hilbert–Samuel & `BostSlopeFiber` Bridge -/

/-- Exact Moriwaki / arithmetic Hilbert–Samuel volume normalization `n^(D+1) / (D+1)!`
(matching `ReciprocityTheory/.../MoriwakiSt.lean`). -/
def arithVolNorm (D n : ℕ) : ℝ :=
  (n : ℝ) ^ (D + 1) / (((D + 1).factorial : ℕ) : ℝ)

theorem arithVolNorm_pos (D : ℕ) {n : ℕ} (hn : 0 < n) : 0 < arithVolNorm D n := by
  unfold arithVolNorm
  have h1 : (0 : ℝ) < (n : ℝ) ^ (D + 1) := pow_pos (Nat.cast_pos.mpr hn) (D + 1)
  have h2 : (0 : ℝ) < (((D + 1).factorial : ℕ) : ℝ) :=
    Nat.cast_pos.mpr (Nat.factorial_pos (D + 1))
  exact div_pos h1 h2

/-- **Sup-Norm vs. `L²`-Norm Asymptotic Volume Invariance**:
With `rank(n) ≤ C₁ n^D` and Bergman sup-to-`L²` comparison factor `C₂ n^{D/2}`, the
log-distortion `rank(n) * log(C₂ n^{D/2}) / (n^{D+1} / (D+1)!)` vanishes as `n → ∞`. -/
theorem sup_to_L2_volume_error_tendsto_zero (D : ℕ) (rank : ℕ → ℕ) {C₁ C₂ : ℝ}
    (hC₁ : 0 ≤ C₁) (hC₂ : 1 ≤ C₂) (hrank : ∀ n : ℕ, (rank n : ℝ) ≤ C₁ * (n : ℝ) ^ D) :
    Tendsto (fun n : ℕ =>
        ((rank n : ℝ) * log (C₂ * (n : ℝ) ^ ((D : ℝ) / 2))) / arithVolNorm D n)
      atTop (𝓝 0) := by
  have hlog_div : Tendsto (fun x : ℝ => log x / x) atTop (𝓝 0) := by
    have h := Real.tendsto_pow_log_div_mul_add_atTop (1 : ℝ) (0 : ℝ) 1 one_ne_zero
    simpa [pow_one, one_mul, add_zero] using h
  have hlog_nat : Tendsto (fun n : ℕ => log (n : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
    hlog_div.comp tendsto_natCast_atTop_atTop
  have hinv_nat : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  set K : ℝ := C₁ * (((D + 1).factorial : ℕ) : ℝ)
  have hK : 0 ≤ K := by positivity
  have hupper_lim :
      Tendsto (fun n : ℕ => K * (log C₂ * (n : ℝ)⁻¹ + ((D : ℝ) / 2) * (log (n : ℝ) / (n : ℝ))))
        atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => log C₂ * (n : ℝ)⁻¹) atTop (𝓝 (log C₂ * 0)) :=
      hinv_nat.const_mul (log C₂)
    have h2 : Tendsto (fun n : ℕ => ((D : ℝ) / 2) * (log (n : ℝ) / (n : ℝ))) atTop
        (𝓝 (((D : ℝ) / 2) * 0)) := hlog_nat.const_mul ((D : ℝ) / 2)
    simpa using (h1.add h2).const_mul K
  refine squeeze_zero' ?_ ?_ hupper_lim
  · refine eventually_atTop.mpr ⟨1, fun n hn => ?_⟩
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have harg : 1 ≤ C₂ * (n : ℝ) ^ ((D : ℝ) / 2) := by
      have hpow : (1 : ℝ) ≤ (n : ℝ) ^ ((D : ℝ) / 2) := Real.one_le_rpow hn1 (by positivity)
      nlinarith
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (log_nonneg harg))
      (arithVolNorm_pos D hn).le
  · refine eventually_atTop.mpr ⟨1, fun n hn => ?_⟩
    have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hC2_pos : 0 < C₂ := by linarith
    have hpow_pos : 0 < (n : ℝ) ^ ((D : ℝ) / 2) := Real.rpow_pos_of_pos hn_pos _
    have hlog_eq : log (C₂ * (n : ℝ) ^ ((D : ℝ) / 2)) = log C₂ + ((D : ℝ) / 2) * log (n : ℝ) := by
      rw [log_mul hC2_pos.ne' hpow_pos.ne', Real.log_rpow hn_pos]
    have hlog_nn : 0 ≤ log (C₂ * (n : ℝ) ^ ((D : ℝ) / 2)) := by
      have h1 : 1 ≤ C₂ * (n : ℝ) ^ ((D : ℝ) / 2) := by
        have hpow : (1 : ℝ) ≤ (n : ℝ) ^ ((D : ℝ) / 2) := Real.one_le_rpow hn1 (by positivity)
        nlinarith
      exact log_nonneg h1
    have hvol_pos := arithVolNorm_pos D hn
    calc ((rank n : ℝ) * log (C₂ * (n : ℝ) ^ ((D : ℝ) / 2))) / arithVolNorm D n
        ≤ ((C₁ * (n : ℝ) ^ D) * log (C₂ * (n : ℝ) ^ ((D : ℝ) / 2))) / arithVolNorm D n := by
          refine div_le_div_of_nonneg_right ?_ hvol_pos.le
          exact mul_le_mul_of_nonneg_right (hrank n) hlog_nn
      _ = K * (log C₂ * (n : ℝ)⁻¹ + ((D : ℝ) / 2) * (log (n : ℝ) / (n : ℝ))) := by
          rw [hlog_eq]
          unfold arithVolNorm
          dsimp only [K]
          have hfact : ((((D + 1).factorial : ℕ) : ℝ)) ≠ 0 :=
            (Nat.cast_pos.mpr (Nat.factorial_pos (D + 1))).ne'
          rw [pow_succ]
          field_simp [hn_pos.ne', hfact]

/-- **Moriwaki Bigness from Arithmetic Hilbert–Samuel (`MoriwakiBigStatement` core)**:
Combining the arithmetic Hilbert–Samuel lower bound `liminf χ_n / arithVolNorm D n ≥ selfInt`
with Minkowski's lattice-point bound and sup-vs-`L²` Bergman distortion gives the exact
asymptotic volume lower bound `liminf logSmallCount(n) / arithVolNorm D n ≥ selfInt`. -/
theorem moriwaki_big_of_ahs (D : ℕ) (chiArith logSmallCount : ℕ → ℝ) (selfInt : ℝ)
    (hAHS : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, selfInt - ε ≤ chiArith n / arithVolNorm D n)
    (hMink : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      chiArith n - ε * arithVolNorm D n ≤ logSmallCount n) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, selfInt - ε ≤ logSmallCount n / arithVolNorm D n := by
  intro ε hε
  have h1 := hAHS (ε / 2) (half_pos hε)
  have h2 := hMink (ε / 2) (half_pos hε)
  have h3 : ∀ᶠ n : ℕ in atTop, 1 ≤ n := eventually_ge_atTop 1
  filter_upwards [h1, h2, h3] with n hn1 hn2 hn3
  have hvol : 0 < arithVolNorm D n := arithVolNorm_pos D hn3
  have hdiv : chiArith n / arithVolNorm D n - ε / 2 ≤ logSmallCount n / arithVolNorm D n := by
    rw [sub_le_iff_le_add]
    have h := div_le_div_of_nonneg_right hn2 hvol.le
    rw [sub_div, mul_div_cancel_right₀ _ hvol.ne'] at h
    linarith
  linarith

/-- **Exponential Small-Section Abundance (Moriwaki Bigness Criterion)**:
Whenever `0 < selfInt`, the Moriwaki lower bound produces exponentially many small sections
`exp((selfInt / 2) * n^{D+1} / (D+1)!) ≤ smallCount(n)` for all sufficiently large `n`. -/
theorem exists_exp_many_small_sections_of_pos_selfInt
    (D : ℕ) (chiArith logSmallCount : ℕ → ℝ) (selfInt : ℝ) (hpos : 0 < selfInt)
    (hAHS : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, selfInt - ε ≤ chiArith n / arithVolNorm D n)
    (hMink : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      chiArith n - ε * arithVolNorm D n ≤ logSmallCount n) :
    ∀ᶠ n in atTop, (selfInt / 2) * arithVolNorm D n ≤ logSmallCount n ∧ 0 < logSmallCount n := by
  have hbig := moriwaki_big_of_ahs D chiArith logSmallCount selfInt hAHS hMink (selfInt / 2)
    (half_pos hpos)
  have hge : ∀ᶠ n : ℕ in atTop, 1 ≤ n := eventually_ge_atTop 1
  filter_upwards [hbig, hge] with n hn hn1
  have hvol : 0 < arithVolNorm D n := arithVolNorm_pos D hn1
  have h1 : (selfInt / 2) * arithVolNorm D n ≤ logSmallCount n := by
    have h : selfInt / 2 ≤ logSmallCount n / arithVolNorm D n := by linarith
    exact (le_div_iff₀ hvol).mp h
  have h2 : 0 < logSmallCount n := lt_of_lt_of_le (mul_pos (half_pos hpos) hvol) h1
  exact ⟨h1, h2⟩

/-- Normalized Arakelov height `h_{\overline{L}}(X) = \widehat{c}_1(\overline{L})^{D+1} / ((D+1) \deg_L X)`. -/
def normalizedHeight (D : ℕ) (selfInt geomDeg : ℝ) : ℝ :=
  selfInt / (((D + 1 : ℕ) : ℝ) * geomDeg)

/-- **Volume-to-Height Lower Bound** (feeding `TopCovolG.lean` & `ArakelovCovolume.lean`):
A lower bound `volLower ≤ selfInt` yields an explicit lower bound on the normalized height. -/
theorem height_lower_bound_of_ahs (D : ℕ) {selfInt geomDeg volLower : ℝ}
    (hdeg : 0 < geomDeg) (hvol : volLower ≤ selfInt) :
    volLower / (((D + 1 : ℕ) : ℝ) * geomDeg) ≤ normalizedHeight D selfInt geomDeg := by
  unfold normalizedHeight
  have hden : 0 < ((D + 1 : ℕ) : ℝ) * geomDeg := by positivity
  exact div_le_div_of_nonneg_right hvol hden.le

/-- **Volume-to-Height Upper Bound from Asymptotic Small-Section Counts**:
If the arithmetic Hilbert–Samuel lower bound holds and small-section counts are asymptotically
bounded by `V * arithVolNorm D n`, then `selfInt ≤ V` and `h_{\overline{L}}(X) ≤ V / ((D+1) deg)`. -/
theorem height_upper_bound_of_small_section_bound
    (D : ℕ) (chiArith logSmallCount : ℕ → ℝ) {selfInt geomDeg V : ℝ}
    (hdeg : 0 < geomDeg)
    (hAHS : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, selfInt - ε ≤ chiArith n / arithVolNorm D n)
    (hMink : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      chiArith n - ε * arithVolNorm D n ≤ logSmallCount n)
    (hUpper : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      logSmallCount n / arithVolNorm D n ≤ V + ε) :
    selfInt ≤ V ∧ normalizedHeight D selfInt geomDeg ≤ V / (((D + 1 : ℕ) : ℝ) * geomDeg) := by
  have hself : selfInt ≤ V := by
    by_contra hgt
    push Not at hgt
    set δ := (selfInt - V) / 3
    have hδ : 0 < δ := by dsimp only [δ]; linarith
    have h1 := moriwaki_big_of_ahs D chiArith logSmallCount selfInt hAHS hMink δ hδ
    have h2 := hUpper δ hδ
    obtain ⟨n, hn1, hn2⟩ := (h1.and h2).exists
    dsimp only [δ] at hn1 hn2
    linarith
  refine ⟨hself, ?_⟩
  unfold normalizedHeight
  have hden : 0 < ((D + 1 : ℕ) : ℝ) * geomDeg := by positivity
  exact div_le_div_of_nonneg_right hself hden.le

/-- **Arithmetic Volume Shift under Metric Scaling**:
If changing the Hermitian metric shifts `logSmallCount` by at most `δ * n * rank(n)` with
`rank(n) ≤ deg * n^D / D!`, then the normalized arithmetic volume shifts by at most `(D+1) * δ * deg`. -/
theorem arith_volume_metric_shift_le (D n : ℕ) (hn : 0 < n) {rank : ℕ} {δ deg : ℝ}
    (hδ : 0 ≤ δ) (hrank : (rank : ℝ) ≤ deg * (n : ℝ) ^ D / ((D.factorial : ℕ) : ℝ)) :
    (δ * (n : ℝ) * (rank : ℝ)) / arithVolNorm D n ≤ ((D + 1 : ℕ) : ℝ) * δ * deg := by
  have hvol : 0 < arithVolNorm D n := arithVolNorm_pos D hn
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hDfact : (0 : ℝ) < ((D.factorial : ℕ) : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos D)
  have hD1fact : (((D + 1).factorial : ℕ) : ℝ) = ((D + 1 : ℕ) : ℝ) * ((D.factorial : ℕ) : ℝ) := by
    exact_mod_cast Nat.factorial_succ D
  calc (δ * (n : ℝ) * (rank : ℝ)) / arithVolNorm D n
      ≤ (δ * (n : ℝ) * (deg * (n : ℝ) ^ D / ((D.factorial : ℕ) : ℝ))) / arithVolNorm D n := by
        refine div_le_div_of_nonneg_right ?_ hvol.le
        exact mul_le_mul_of_nonneg_left hrank (by positivity)
    _ = ((D + 1 : ℕ) : ℝ) * δ * deg := by
        unfold arithVolNorm
        rw [hD1fact, pow_succ]
        have hD1ne : ((D + 1 : ℕ) : ℝ) ≠ 0 := by positivity
        field_simp [hn_pos.ne', hDfact.ne', hD1ne]

/-- **Direct Bridge to `ArakelovCovolume` (`RHDirect.BostSlopeFiber`)**:
Combining a Hermitian-curvature / Moriwaki volume upper bound `B.muCC ≤ muCap` with the Bost slope
inequality `B.SlopeIneq` yields an explicit lower bound on `log B.cardW` (equivalently an upper
bound on the slope excess `B.s - muCap`), directly feeding `ArakelovCovolume.lean`. -/
theorem bost_slope_from_curvature_volume_bound (B : RHDirect.BostSlopeFiber) {muCap : ℝ}
    (hSlope : B.SlopeIneq)
    (hdel0 : 0 ≤ B.del) (hdel1 : B.del < 1) (hη : 0 ≤ B.η)
    (he0 : 0 ≤ B.e) (he1 : B.e ≤ 1 / 4)
    (hHH : B.s - B.muMinCC ≤ B.HH) (hHH_pos : 0 < B.HH)
    (hCurvCap : B.muCC ≤ muCap) :
    B.s - muCap -
      (1 - B.del)⁻¹ * (4 * B.uF * Real.log (1 + B.HH / B.uF) +
        (B.η + 4 * Real.sqrt B.e) * B.HH) ≤ Real.log (B.cardW : ℝ) := by
  have h1 := hSlope hdel0 hdel1 hη he0 he1 hHH hHH_pos
  linarith

end

end RHDirect.HermitianCurvatureCore
